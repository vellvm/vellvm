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
     DynamicTypes
     LLVMEvents
     Denotation
     Local
     Memory
     Intrinsics
     LLVMAst
     Util
     Error.


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

Definition allocate_globals (CFG: CFG.mcfg) (gs:list global) : LLVM _CFG D.genv :=
  monad_fold_right
    (fun (m:D.genv) (g:global) =>
       vis (Alloca (D.eval_typ CFG (g_typ g))) (fun v => ret (D.ENV.add (g_ident g) v m))) gs (@D.ENV.empty _).


(* Who is in charge of allocating the addresses for external functions declared in this mcfg? *)
Definition register_declaration (g:D.genv) (d:declaration) : LLVM _CFG D.genv :=
  (* SAZ TODO:  Don't allocate pointers for LLVM intrinsics declarations *)
    vis (Alloca DTYPE_Pointer) (fun v => ret (D.ENV.add (dc_name d) v g)).


(* SAZ: for "open" MCFGs we have
    - (m_declarations CFG) is the set of possible ExternalCalls 
    - (List.map df_prototype (m_definitions CFG)) is the set of possilbe Entry Functions  (also internal calls)
 *)


Definition denote_function CFG (g:D.genv) (df:definition _) :
  err (dvalue * (list local_id * LLVM _CFG dvalue))  := 
  let d := (df_prototype df) in
  let fid := (dc_name d) in
  liftM (fun fv => (fv, (df_args df, D.denote_cfg CFG g (df_instrs df)))) (D.lookup_env g fid).

Definition initialize_globals (CFG: CFG.mcfg) (gs:list global) (g:D.genv) : LLVM _CFG unit :=
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
  
Definition build_global_environment (CFG : CFG.mcfg) : LLVM _CFG D.genv :=
  g <- allocate_globals CFG (m_globals CFG) ;;
  g1 <- monad_fold_right register_declaration
       ((m_declarations CFG) ++ (List.map df_prototype (m_definitions CFG))) g;;
  initialize_globals CFG (m_globals CFG) g1 ;;
  ret g1.

(* Local environment implementation *)
Definition local_env := FMapAList.alist raw_id dvalue.

(* (for now) assume that [main (i64 argc, i8** argv)] 
    pass in 0 and null as the arguments to main
   Note: this isn't compliant with standard C semantics
*)
Definition main_args := [DV.DVALUE_I64 (DynamicValues.Int64.zero);
                         DV.DVALUE_Addr (Memory.A.null)
                        ].

Definition run_with_memory (prog: list (toplevel_entity (list block))) :
  option (LLVM _MCFG2 (M.memory * (@L.stack local_env * DV.dvalue))) :=
  let scfg := Vellvm.AstLib.modul_of_toplevel_entities prog in
  mcfg <- CFG.mcfg_of_modul scfg ;;       
       let core_trace : LLVM _CFG dvalue :=
           'glbls <- build_global_environment mcfg ;;
           'defns <- lift_err ret (map_monad (denote_function mcfg glbls) (m_definitions mcfg)) ;;
           'addr <- lift_err ret (D.lookup_env glbls (Name "main")) ;;
           D.denote_mcfg defns DTYPE_Void addr main_args in
       let after_intrinsics_trace : LLVM _CFG dvalue := INT.interpret_intrinsics core_trace in
       let mem_trace := L.run_local after_intrinsics_trace L.start_stack in
       let interpreted_Trace := M.run_memory mem_trace M.empty in
       ret interpreted_Trace.

