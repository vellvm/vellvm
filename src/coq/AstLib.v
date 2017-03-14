Require Import ZArith.ZArith List.
Require Import String Omega.
Require Import Vellvm.Ollvm_ast Vellvm.Classes.
Require Import Equalities.
Import ListNotations.

Module RawID <: UsualDecidableTypeFull.
  Definition t := raw_id.
  Include HasUsualEq.
  Include UsualIsEq.
  Include UsualIsEqOrig.
  
  Lemma eq_dec : forall (x y : raw_id), {x = y} + {x <> y}.
  Proof.
    intros x y.
    destruct x as [xn | xn]; destruct y as [yn | yn].
    - destruct (string_dec xn yn). subst. left. reflexivity.
      right. unfold not. intros. apply n. inversion H. auto.
    - right. unfold not. intros. inversion H.
    - right. unfold not. intros. inversion H.
    - destruct (positive_eq_dec xn yn).
      left. subst. reflexivity.
      right. unfold not. intros. apply n. inversion H. auto.
  Qed.

  Include HasEqDec2Bool.
  
End RawID.

Instance eq_dec_raw_id : eq_dec raw_id := RawID.eq_dec.


