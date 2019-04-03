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
     Intrinsics.


Import MonadNotation.
Import ListNotations.

Module IO := LLVMIO.Make(Memory.A).
Module M := Memory.Make(IO).
Module SS := StepSemantics(Memory.A)(IO).
Module INT := Intrinsics.Make(Memory.A)(IO).


Import IO.
Export IO.DV.

Open Scope string_scope.

Definition run_with_memory prog : option (LLVM (failureE +' debugE) (M.memory * DV.dvalue)) :=
  let scfg := Vellvm.AstLib.modul_of_toplevel_entities prog in
  mcfg <- CFG.mcfg_of_modul scfg ;;
  let core_trace : LLVM (failureE +' debugE) dvalue :=
      s <- SS.init_state mcfg "main" ;;
        SS.step_sem mcfg (SS.Step s)
  in
  let after_intrinsics_trace := INT.evaluate_with_defined_intrinsics core_trace in
  ret (M.memD M.empty after_intrinsics_trace).
