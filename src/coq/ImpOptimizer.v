Require Import Vellvm.Imp.
Require Import Vellvm.ImpQuickChick.
Require Import compcert.lib.Integers.

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

(*! Section ImpOptimizer *)

Fixpoint fold_adjacent_constants (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId x => AId x
  | APlus a1 a2 =>
    match fold_adjacent_constants a1, fold_adjacent_constants a2 with
    | ANum n1, ANum n2 => (*!*) ANum (Int64.add n1 n2) (*! ANum (Int64.add n1 n1) *)
    | a1', a2' => APlus a1' a2'
    end
  | AMinus a1 a2 =>
    match fold_adjacent_constants a1, fold_adjacent_constants a2 with
    | ANum n1, ANum n2 => ANum (Int64.sub n1 n2)
    | a1', a2' => AMinus a1' a2'
    end 
  | AMult a1 a2 =>
    match fold_adjacent_constants a1, fold_adjacent_constants a2 with
    | ANum n1, ANum n2 => ANum (Int64.mul n1 n2)
    | ANum n1, a2' => if Int64.eq n1 Int64.zero then ANum (Int64.zero) else AMult (ANum n1) a2'
    | a1', ANum n2 => if Int64.eq n2 Int64.zero then ANum (Int64.zero) else AMult a1' (ANum n2)
    | a1', a2' => AMult a1' a2'
    end
  end.

Fixpoint fold_constants_for_bool (b : bexp) :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 =>
    let a1' := fold_adjacent_constants a1 in
    let a2' := fold_adjacent_constants a2 in
    match a1', a2' with
    | ANum n1, ANum n2 => if Int64.eq n1 n2 then BTrue else BFalse
    | _, _ => BEq a1 a2
    end
  | BLe a1 a2 =>
    let a1' := fold_adjacent_constants a1 in
    let a2' := fold_adjacent_constants a2 in
    match a1', a2' with
    | ANum n1, ANum n2 => if negb (Int64.lt n2 n1) then BTrue else BFalse
    | _, _ => BLe a1 a2
    end
  | BNot b => let b' := fold_constants_for_bool b in
              match b' with
              | BTrue => BFalse
              | BFalse => BTrue
              | _ => b'
              end
  | BAnd b1 b2 =>
    let b1' := fold_constants_for_bool b1 in
    let b2' := fold_constants_for_bool b2 in
    match b1', b2' with
    | BTrue, BTrue => BTrue
    | _, BFalse | BFalse, _ => BFalse
    | _, _ => BAnd b1' b2'
    end
  end.

Definition fold_constants_checker (st : state) (a : aexp) : bool :=
  Int64.eq (aeval st a) (aeval st (fold_adjacent_constants a)).

Definition fold_constants_aexp_ok (a : aexp) :=
  fold_constants_checker test_state a.


(*! Section FoldConstantsAexp *) (*! extends ImpOptimizer *)
Existing Instance gen_small_nonneg_i64.
Existing Instance genSaexp.

(*! QuickChick (forAll arbitrary fold_constants_aexp_ok). *)

Remove Hints gen_small_nonneg_i64 : typeclass_instances.
Remove Hints genSaexp : typeclass_instances.

(* End FoldConstantsAexp *)


(*! Section FoldConstantsBexp *) (*! extends ImpOptimizer *)



(* End FoldConstantsBexp *)

