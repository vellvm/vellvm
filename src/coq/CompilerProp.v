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
Require Import Vellvm.Classes.

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
                        | Id ident => (ident ++ ": " ++ show_nat (st x) ++ ", ")%string
                        end)) fv "".

Check fold_left.
Check show_int.

Definition mem_to_string (mem : mtype) : string :=
  fold_left (fun s cell =>
               match cell with
               | DV (VALUE_Integer z) => (s ++ (string_of z) ++ "; ")%string
               | _ => (s ++ "~VALUE_Integer; ")%string
               end)
            mem "".

Definition elt_to_string (elem : IDSet.elt) :=
  match elem with
  | Id name => name
  end.

Definition elems_to_string (elements : list IDSet.elt) : string :=
  fold_left (fun s elem => (s ++ ", " ++ (elt_to_string elem)))%string
            elements
            "".

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
        let llvm_final_state := MemDFin [] semantics 1000 in
        let imp_state := ceval_step empty_state p 10000 in
        match (llvm_final_state, imp_state) with
        | (None, None) => whenFail "both out of gas" true
        | (Some llvm_st, None) => whenFail "imp out of gas" false
        | (None, Some imp_st) => whenFail "llvm out of gas" false
        | (Some llvm_st, Some imp_st) => 
          let ans_state := List.map (fun x => dvalue_of_nat (imp_st x)) fvs in
          whenFail ("not equal: llvm: "
                      ++ (mem_to_string llvm_st)
                      ++ "; imp: "
                      ++ (mem_to_string ans_state)
                      ++ "; free vars: "
                      ++ (elems_to_string fvs))
                   (checker (imp_memory_eqb llvm_st ans_state))
        end        
      end
    end
  end.

Example prog1 := W ::= AId W.
Example prog2 := X ::= APlus (AId W) (AId W).

Eval vm_compute in (compile prog2).




