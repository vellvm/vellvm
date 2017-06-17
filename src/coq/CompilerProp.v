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

Require Import ZArith String Omega List Equalities MSets.
Import ListNotations.

(* Vellvm dependencies *)
Require Import Vellvm.Ollvm_ast.
Require Import Vellvm.Compiler.
Require Import Vellvm.AstLib.
Require Import Vellvm.CFG.
Require Import Vellvm.StepSemantics.
Require Import Vellvm.Memory.
Require Import Vellvm.Classes.

(* Logical Foundations dependencies *)
Require Import Vellvm.Imp.
Require Import Vellvm.Maps.
Require Import Vellvm.ImpCEvalFun.
Import ListNotations.

Require Import Vellvm.ImpQuickChick.


Require Import compcert.lib.Integers.

(* Equality for the imp final memory states. *)

(* These definitions should probably go in a library *)

Definition dvalue_of_nat (n:nat) : dvalue :=
  DV (VALUE_Integer (Z.of_nat n)).

Definition dvalue_of_int64 (n:int64) : dvalue :=
  DV (VALUE_Integer (Int64.unsigned n)).

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


Fixpoint string_of_dvalue' (v : dvalue) :=
  match v with
  | DV expr =>
    match expr with
    | VALUE_Ident id => string_of id
    | VALUE_Integer x => string_of x
    | VALUE_Bool b => string_of b
    | VALUE_Null => "null"
    | VALUE_Zero_initializer => "zero initializer"
    | VALUE_Cstring s => s
    | VALUE_None => "none" 
    | VALUE_Undef => "undef" 
    | OP_IBinop iop t v1 v2 =>
      ((string_of iop) ++ " " ++ (string_of t)
                       ++ " " ++ (string_of_dvalue' v1)
                       ++ " " ++ (string_of_dvalue' v2))%string
    | OP_GetElementPtr t ptrval idxs =>
      "getelementptr"
    | _ => "string_of_dvalue' todo"
    end
  | DVALUE_CodePointer p => "string_of_dvalue' todo (code pointer)"
  | DVALUE_Addr a => "string_of_dvalue' todo (addr)"
  | _ => "string_of_dvalue' (todo)"
  end.

Instance string_of_value : StringOf dvalue := string_of_dvalue'.

Instance string_of_mem : StringOf memory :=
  fun mem => ("[" ++ show_nat (List.length mem) ++ "] " ++ string_of mem)%string.

Definition state_to_string (fv : list id) (st : state) : string :=
  fold_left (fun acc x => (match x with
                        | Id ident => (ident ++ ": " ++ show_int64 (st x) ++ ", ")%string
                        end)) fv "".

Instance string_of_IDSet_elt : StringOf IDSet.elt :=
  fun elem => 
    match elem with
    | Id name => name
    end.

Definition compile_and_execute (c : Imp.com) : err memory :=
  let fvs := IDSet.elements (fv c) in
  match compile c with
  | inl e => inl e
  | inr ll_prog =>
    let m := modul_of_toplevel_entities ll_prog in
    match mcfg_of_modul m with
    | None => inl "Compilation failed"
    | Some mcfg =>
      match init_state mcfg "imp_command" with
      | inl e => inl "init failed"
      | inr initial_state =>
        let semantics := sem mcfg initial_state in
        let llvm_final_state := MemDFin [] semantics 10000 in
        match llvm_final_state with
        | Some st => inr st
        | None => inl "out of gas"
        end
      end
    end
  end.

(*! Section CompilerProp *)

Definition imp_compiler_correct_aux (p:Imp.com) : Checker :=
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
        let llvm_final_state := MemDFin [] semantics 10000 in
        let imp_state := ceval_step empty_state p 100 in
        match (llvm_final_state, imp_state) with
        | (None, None) => whenFail "both out of gas" true
        | (Some llvm_st, None) => whenFail "imp out of gas" true
        | (None, Some imp_st) => whenFail "llvm out of gas" false 
        | (Some llvm_st, Some imp_st) => 
          let ans_state := List.map (fun x => dvalue_of_int64 (imp_st x)) fvs in
          checker (whenFail ("not equal: llvm: "
                               ++ (string_of llvm_st)
                               ++ "; imp: "
                               ++ (string_of ans_state)
                               ++ "; free vars: "
                               ++ (string_of fvs) (* (elems_to_string fvs) *)
                               ++ "; compiled code: "
                               ++ (string_of ll_prog))
                            (imp_memory_eqb (*!*) (List.rev llvm_st) (*! llvm_st *) ans_state))
        end        
      end
    end
  end.


Definition imp_compiler_correct_bool (p:Imp.com) : bool :=
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
        let llvm_final_state := MemDFin [] semantics 15000 in
        let imp_state := ceval_step empty_state p 100 in
        match (llvm_final_state, imp_state) with
        | (None, None) => true
        | (Some llvm_st, None) => true
        | (None, Some imp_st) => true
        | (Some llvm_st, Some imp_st) => 
          let ans_state := List.map (fun x => dvalue_of_int64 (imp_st x)) fvs in
          imp_memory_eqb (List.rev llvm_st) ans_state
        end        
      end
    end
  end.

Definition compile_aexp_correct_bool (a:aexp) : bool :=
  let p := (Id "fresh_var" ::= a) in
  imp_compiler_correct_bool p.  


Definition compile_bexp_correct_bool (b:bexp) : bool :=
  let p := (IFB b THEN idX ::= ANum (Int64.repr 1) ELSE idY ::= ANum (Int64.repr 2) FI) in
  imp_compiler_correct_bool p.  

Definition compile_aexp_correct (a:aexp) : Checker :=
  let p := (Id "fresh_var" ::= a) in
  imp_compiler_correct_aux p.  


Definition compile_bexp_correct (b:bexp) : Checker :=
  let p := (IFB b THEN idX ::= ANum (Int64.repr 1) ELSE idY ::= ANum (Int64.repr 2) FI) in
  imp_compiler_correct_aux p.  


Definition show_aexp_compilation_result (result : err (Ollvm_ast.value * list elt)) :=
  match result with
  | inl _ => "err" 
  | inr (_, elts) => string_of elts
  end.

Definition show_bexp_compilation_result (result : err (Ollvm_ast.value * list elt)) :=
  match result with
  | inl _ => "err"
  | inr (_ , elts) => string_of elts
  end.


Definition show_result (result : err (toplevel_entities (list block))) :=
  match result with
  | inl _ => "error"
  | inr l => fold_left (fun s tle_blk => (s ++ "; " ++ (string_of tle_blk))%string) l ""
  end.

(* Tests *)

Extract Constant Test.defNumTests => "100".

(*
Definition prog_unshrunk :=
  IFB (BLe (ANum (Int64.repr 0)) (ANum (Int64.repr 0))) THEN
    IFB (BLe (AId idW) (AId W)) THEN
      idX ::= (AMult (AId idY)
                     (APlus (AMult (ANum (Int64.repr 0)) (ANum (Int64.repr 1)))
                            (AId idY)))
    ELSE SKIP
    FI
  ELSE
    idX ::= (AMult (AMult (ANum (Int64.repr 9)) (ANum (Int64.repr 10)))
                   (AMult (AMult (ANum (Int64.repr (-2))) (ANum (Int64.repr 8)))
                          (AId idX)))
  FI.
*)

(*! Section TestSingleCom *)

Existing Instance gen_seq_and_assgn_com.
Existing Instance gen_bexp_with_small_aexp.
Existing Instance gen_adhoc_aexp.
Existing Instance gen_small_nonneg_i64.

(*! QuickChick (forAll (arbitrarySized 0) imp_compiler_correct_aux). *)
(* Shrinking is slow: 
   QuickChick (forAllShrink (arbitrarySized 0) shrink imp_compiler_correct_aux).
 *)

(* QuickChick (forAll (arbitrarySized 0) imp_compiler_correct_aux). *)

Example prog1 :=
  idW ::= (APlus (AMult (AId idX) (ANum (Int64.repr 2)))
                 (AMult (ANum (Int64.repr 1)) (AId idX))).

(* Compute (compile_and_execute prog1). *)

Remove Hints gen_seq_and_assgn_com : typeclass_instances.
Remove Hints gen_bexp_with_small_aexp : typeclass_instances.
Remove Hints gen_adhoc_aexp : typeclass_instances.
Remove Hints gen_small_nonneg_i64 : typeclass_instances.

(* End TestSingleCom !*)


(*! Section TestMultipleCom *)


(* End TestMultipleCom *)