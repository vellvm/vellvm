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
Require Import Vellvm.Ollvm_ast Vellvm.Compiler Vellvm.AstLib Vellvm.CFG Vellvm.StepSemantics Vellvm.Memory.

(* Logical Foundations dependencies *)
Require Import Vellvm.Imp Vellvm.Maps.
Import ListNotations.


(* Equality for the "final states".  This should probably be made more general *)

Definition dvalue_of_nat (n:nat) : value :=
  DV (VALUE_Integer (Z.of_nat n)).

Definition imp_val_eqb (v1 v2 : dvalue) : bool :=
  match v1, v2 with
  | (DV (VALUE_Integer z1)), (DV (VALUE_Integer z2)) => true
  | _, _ => false
  end.

Fixpoint imp_memory_eqb (m1 : list dvalue) (m2 : list dvalue) : bool :=
  match m1, m2 with
  | [], [] => true
  | x::xs, y::ys => if imp_val_eqb x y then imp_memory_eqb xs ys else false
  | _, _ => false 
  end.  

Definition imp_compiler_correct (p:Imp.com) : bool :=
  let fvs := IDSet.elements (fv p) in
  match compile p with
  | inl e => false
  | inr ll_prog =>
    let m := modul_of_toplevel_entities ll_prog in
    match mcfg_of_modul m with
    | None => false
    | Some mcfg =>
      match init_state mcfg "imp_command" with
      | inl e => false
      | inr initial_state =>
        let semantics := sem mcfg initial_state in
        match MemDFin [] semantics 1000 with
            | None => false
            | Some final_state => 
              let imp_state := (* Imp.run p empty 1000 *) fun _ => 0%nat in
              let ans_state := List.map (fun x => dvalue_of_nat (imp_state x)) fvs in
              imp_memory_eqb final_state ans_state
        end
      end
    end
  end.


