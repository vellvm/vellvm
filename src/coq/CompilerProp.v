(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import Vellvm.Maps Vellvm.Imp.

Require Import QuickChick.QuickChick. 
Import QcDefaultNotation. Open Scope qc_scope. 

Require Import List ZArith.
Import ListNotations.
Require Import String.


Require Import ZArith String Omega List Equalities MSets.

(* Vellvm dependencies *)
Require Import Vellvm.Ollvm_ast Vellvm.Compiler Vellvm.AstLib Vellvm.CFG Vellvm.StepSemantics Vellvm.Memory.

(* Logical Foundations dependencies *)
Require Import Vellvm.Imp Vellvm.Maps Vellvm.ImpCEvalFun.
Import ListNotations.


(* Equality for the imp final memory states. *)

(* These definitions should probably go in a library *)
Definition dvalue_of_nat (n:nat) : value :=
  DV (VALUE_Integer (Z.of_nat n)).

Definition imp_val_eqb (v1 v2 : dvalue) : bool :=
  match v1, v2 with
  | (DV (VALUE_Integer z1)), (DV (VALUE_Integer z2)) => Z.eqb z1 z2
  | _, _ => false
  end.

Fixpoint imp_memory_eqb (m1 : list dvalue) (m2 : list dvalue) : bool :=
  match m1, m2 with
  | [], [] => true
  | x::xs, y::ys => if imp_val_eqb x y then imp_memory_eqb xs ys else false
  | _, _ => false 
  end.  

(* The executable test function for compiler correctnes. *)

(* TODO: 
     Add a 'run' function to Imp to execute n steps of the
     Imp operational semantics starting from a given state.

     One possible testing issue: the Vellvm code of a given
     imp program will take many more steps.
 *)
Require Import List.


Definition state_to_string (st : state) (fv : list id) : string :=
  fold_left (fun acc x => (match x with
                        | Id ident => (ident ++ ": " ++ show (st x) ++ ", ")%string
                        end)) fv "".


Definition imp_compiler_correct_aux (p:Imp.com) :=
  let fvs := IDSet.elements (fv p) in
  match compile p with
  | inl e => whenFail "Compilation failed" false
  | inr ll_prog =>
    let m := modul_of_toplevel_entities ll_prog in
    match mcfg_of_modul m with
    | None => whenFail "Compilation failed" false
    | Some mcfg =>
      match init_state mcfg "imp_command" with
      | inl e => whenFail "init failed" false
      | inr initial_state =>
        let semantics := sem mcfg initial_state in
        let llvm_final_state := MemDFin [] semantics 10 in
        let imp_state := ceval_step empty_state p 10 in
        match (llvm_final_state, imp_state) with
        | (None, None) => whenFail "both out of gas" true
        | (Some llvm_st, None) => whenFail "imp out of gas" false
        | (None, Some imp_st) => whenFail "llvm out of gas" false
        | (Some llvm_st, Some imp_st) => 
          let ans_state := List.map (fun x => dvalue_of_nat (imp_st x)) fvs in
          checker (imp_memory_eqb llvm_st ans_state)
        end        
      end
    end
  end.


Definition another_imp_compiler_correct (p:Imp.com) : string * bool :=
  let fvs := IDSet.elements (fv p) in
  match compile p with
  | inl e => ("Compilation failed", false)
  | inr ll_prog =>
    let m := modul_of_toplevel_entities ll_prog in
    match mcfg_of_modul m with
    | None => ("Compilation failed", false)
    | Some mcfg =>
      match init_state mcfg "imp_command" with
      | inl e => ("init failed", false)
      | inr initial_state =>
        let semantics := sem mcfg initial_state in
        ("Success", true)
      end        
    end
  end.

Example prog1 := W ::= AId W.
Example prog2 := X ::= APlus (AId W) (AId W).

(*
Eval vm_compute in (compile prog2).
Eval vm_compute in (another_imp_compiler_correct prog1).
*)

