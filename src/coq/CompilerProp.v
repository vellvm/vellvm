(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import ZArith String Omega List Equalities MSets.

(* Vellvm dependencies *)
Require Import Vellvm.Compiler Vellvm.Memory.

(* Logical Foundations dependencies *)
Require Import Imp Maps.

(*
Definition imp_compiler_correct (p:Imp.com) : bool :=
  let fvs := IDSet.elements (fv p) in
  match compile p with
  | inl e => false
  | inr ll_prog =>
    let cfg = (* create the cfg *) in
    let initial_state = (..pc.. entry_of "imp_command", [], []) in
    let semantics = StepSemantics.sem cfg initial_state in
    let final_state = Memory.MemDFin semantics [] 1000 in
    let imp_state = Imp.run p empty 1000 in
    let ans_state = List.map imp_state fvs in
    final_state == ans_state
  end.
*)

