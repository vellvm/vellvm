(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

From Coq Require Import
     List String.

From ITree Require Import
     ITree.

From ExtLib Require Import 
     Structures.Monads
     Data.Map.FMapAList.

From Vellvm Require Import 
     LLVMEvents
     Denotation
     Local
     Memory
     Intrinsics
     LLVMAst
     Util.


Import MonadNotation.
Import ListNotations.

Module IO := LLVMEvents.Make(Memory.A).
Module L := LLVM_LOCAL(A)(IO).
Module M := Memory.Make(IO).
Module D := Denotation(Memory.A)(IO).
Module INT := Intrinsics.Make(Memory.A)(IO).

Import IO.
Export IO.DV.

Open Scope string_scope.

Definition allocate_globals (CFG: CFG.mcfg) (gs:list global) : LLVM _MCFG D.genv :=
  monad_fold_right
    (fun (m:D.genv) (g:global) =>
       vis (Alloca (D.eval_typ CFG (g_typ g))) (fun v => ret (D.ENV.add (g_ident g) v m))) gs (@D.ENV.empty _).


(* Who is in charge of allocating the addresses for external functions declared in this mcfg? *)
Definition register_declaration (g:D.genv) (d:declaration) : LLVM _MCFG D.genv :=
  (* TODO: map dc_name d to the returned address *)
    vis (Alloca DTYPE_Pointer) (fun v => ret (D.ENV.add (dc_name d) v g)).

(* SAZ: for "open" MCFGs we have
    - (m_declarations CFG) is the set of possible ExternalCalls 
    - (List.map df_prototype (m_definitions CFG)) is the set of possilbe Entry Functions  (also internal calls)
*)
Definition register_functions (CFG: CFG.mcfg) (g:D.genv) : LLVM _MCFG D.genv :=
  monad_fold_right register_declaration
                   ((m_declarations CFG) ++ (List.map df_prototype (m_definitions CFG)))
                   g.
  
Definition initialize_globals (CFG: CFG.mcfg) (gs:list global) (g:D.genv) : LLVM _MCFG unit :=
  monad_fold_right
    (fun (_:unit) (glb:global) =>
       let dt := D.eval_typ CFG (g_typ glb) in
       a <- lift_err ret (D.lookup_env g (g_ident glb)) ;;
       dv <-
           match (g_exp glb) with
           | None => ret DVALUE_Undef
           | Some e => D.denote_exp CFG g (Some dt) e
           end ;;
       vis (Store a dv) ret)
    gs tt.
  
Definition build_global_environment (CFG : CFG.mcfg) : LLVM _MCFG D.genv :=
  g <- allocate_globals CFG (m_globals CFG) ;;
  g2 <- register_functions CFG g ;;
  _ <- initialize_globals CFG (m_globals CFG) g2 ;;
  ret g2.

(* Local environment implementation *)
Definition local_env := FMapAList.alist raw_id dvalue.

Definition run_with_memory (prog: list (toplevel_entity (list block))) :
  option (LLVM _MCFG2 (M.memory * (@L.stack local_env * DV.dvalue))) :=
  let scfg := Vellvm.AstLib.modul_of_toplevel_entities prog in
  mcfg <- CFG.mcfg_of_modul scfg ;;       
       let core_trace :=
           glbls <- build_global_environment mcfg ;;
           D.denote_mcfg mcfg glbls DTYPE_Void (Name "main") [] in
       let mem_trace := @L.run_local local_env _ _ _ _ core_trace L.start_stack in
       let interpreted_Trace := M.run_memory mem_trace M.empty in
       ret interpreted_Trace.

