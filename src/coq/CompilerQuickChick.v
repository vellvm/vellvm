
Require Import Vellvm.Maps Vellvm.Imp.
Require Import Vellvm.ImpQuickChick.

Require Import Vellvm.CompilerProp Vellvm.Compiler.

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Require Import List ZArith.
Import ListNotations.
Require Import String.

Require Import Vellvm.Classes Vellvm.Ollvm_ast.


Example empty_ctxt : ctxt := t_empty (None : option Ollvm_ast.value).
Example test_ctxt :=
  t_update (t_update empty_ctxt
                     idX (Some (Ollvm_ast.SV (Ollvm_ast.VALUE_Integer 2%Z))))
           idY (Some (Ollvm_ast.SV (Ollvm_ast.VALUE_Integer 3%Z))).

Check (compile_aexp empty_ctxt (ANum 2)).
Compute (compile_aexp empty_ctxt (ANum 2)).
Compute (compile_aexp empty_ctxt (AId idX)).

Definition test_state := (2, 3, ([]: list elt))%Z.
Definition test_instr : instr :=
  INSTR_Op (SV (OP_IBinop (Add false false)
                          i64
                          (SV (VALUE_Integer 2%Z))
                          (SV (VALUE_Integer 2%Z)))).

Definition test_compiled_aexp := compile_aexp test_ctxt (APlus (AId idX) (ANum 3)).

Check fold_left.

(* Fails compilation because of wrongly-correct monad_fold_left *)
Example prog1 := (idX ::= ANum 1).
Example prog2 := (idW ::= AId idW).

(* Fails compilation because of off-by-one in Alloca for MemDFin *)
Example prog3 := idX ::= ANum 1 ;; idY ::= ANum 2 ;; idZ ::= ANum 3 ;; idW ::= ANum 4.
Example prog4 := idX ::= AId idY.
Example prog5 := idX ::= APlus (AId idW) (AId idX).

(* Fails compilation because of memory allocation of free vars in reverse order
   during compilation *)
Example prog6 := idY ::= APlus (AId idZ) (ANum 4).

Example prog7 :=
  IFB (BEq (AMult (ANum 10) (AId idW)) (AMult (ANum 6) (ANum 5))) THEN
    X ::= (APlus (AId idY) (AMult (APlus (ANum 1) (ANum 5)) (APlus (ANum 1) (ANum 0))))
  ELSE Y ::= (APlus (AId idY) (APlus (AMinus (ANum 3) (ANum 4)) (ANum 2))) FI.
  

Eval vm_compute in (compile prog2).

Definition show_aexp_compilation_result (result : err (value * list elt)) :=
  match result with
  | inl _ => "err" 
  | inr (_, elts) => string_of elts
  end.

Definition show_bexp_compilation_result (result : err (value * list elt)) :=
  match result with
  | inl _ => "err"
  | inr (_ , elts) => string_of elts
  end.


Definition show_result (result : err (toplevel_entities (list block))) :=
  match result with
  | inl _ => "error"
  | inr l => fold_left (fun s tle_blk => (s ++ "; " ++ (string_of tle_blk))%string) l ""
  end.


Compute (show_aexp_compilation_result
           (compile_aexp_wrapper (AMult (AId idX) (APlus (ANum 1) (ANum 2))))).

Compute (show_bexp_compilation_result
           (compile_bexp_wrapper (BEq (ANum 5) (APlus (ANum 2) (ANum 3))))).

Compute (show_result (compile prog3)).
Compute (show_result (compile prog4)).
Compute (show_result (compile prog6)).

Compute (compile_and_execute prog3).
Compute (compile_and_execute prog4).
Compute (compile_and_execute prog5).
Compute (compile_and_execute prog7).

QuickChick (forAll arbitrary
                   imp_compiler_correct_aux).


Compute (imp_compiler_correct_aux prog1).



Definition result1 := imp_compiler_correct_aux prog1.
(* Recursive Extraction result1.  *)
(* Eval vm_compute in (imp_compiler_correct_aux prog1). *)