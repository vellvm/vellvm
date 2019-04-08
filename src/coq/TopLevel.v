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
     Structures.Monads.

From Vellvm Require Import 
     LLVMEvents
     Denotation
     Memory
     Intrinsics
     LLVMAst
     Util.


Import MonadNotation.
Import ListNotations.

Module IO := LLVMEvents.Make(Memory.A).
Module M := Memory.Make(IO).
Module D := Denotation(Memory.A)(IO).
Module INT := Intrinsics.Make(Memory.A)(IO).


Import IO.
Export IO.DV.

Open Scope string_scope.

Definition allocate_globals (CFG: CFG.mcfg) (gs:list global) : LLVM_CFG D.genv :=
  monad_fold_right
    (fun (m:D.genv) (g:global) =>
       vis (Alloca (D.eval_typ CFG (g_typ g))) (fun v => ret (D.ENV.add (g_ident g) v m))) gs (@D.ENV.empty _).


(* Who is in charge of allocating the addresses for external functions declared in this mcfg? *)
Definition register_declaration (g:D.genv) (d:declaration) : LLVM_CFG D.genv :=
  (* TODO: map dc_name d to the returned address *)
    vis (Alloca DTYPE_Pointer) (fun v => ret (D.ENV.add (dc_name d) v g)).

(* SAZ: for "open" MCFGs we have
    - (m_declarations CFG) is the set of possible ExternalCalls 
    - (List.map df_prototype (m_definitions CFG)) is the set of possilbe Entry Functions  (also internal calls)
*)
Definition register_functions (CFG: CFG.mcfg) (g:D.genv) : LLVM_CFG D.genv :=
  monad_fold_right register_declaration
                   ((m_declarations CFG) ++ (List.map df_prototype (m_definitions CFG)))
                   g.
  
Definition initialize_globals (CFG: CFG.mcfg) (gs:list global) (g:D.genv) : LLVM_CFG unit :=
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
  
Definition build_global_environment (CFG : CFG.mcfg) : LLVM_CFG D.genv :=
  g <- allocate_globals CFG (m_globals CFG) ;;
  g2 <- register_functions CFG g ;;
  _ <- initialize_globals CFG (m_globals CFG) g2 ;;
  ret g2.

Definition run_with_memory prog : option (LLVM_MCFG2 (M.memory * DV.dvalue)) :=
  let scfg := Vellvm.AstLib.modul_of_toplevel_entities prog in
  mcfg <- CFG.mcfg_of_modul scfg ;;
  let core_trace :=
      build_global_environment mcfg ;;
      D.denote_mcfg mcfg
      s <- D.init_state mcfg "main" ;;
        D.step_sem mcfg (D.Step s)
  in
  let after_intrinsics_trace := INT.evaluate_with_defined_intrinsics core_trace in
  ret (M.memD M.empty after_intrinsics_trace).
