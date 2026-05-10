Require Import ExtLib.Programming.Eqv.
Require Import ExtLib.Core.RelDec.
From Stdlib Require Import List.
Import ListNotations.

Section With_Eqv_Rel_Dec.

  Context {A B : Type}.
  Context {RD:RelDec (@eq A)} {RDC:RelDec_Correct RD}.

  Lemma eq_dec_eq: forall a,
    rel_dec a a = true.
  Proof using A RD RDC.
    intros.
    rewrite rel_dec_correct.
    reflexivity.
  Qed.

  Lemma eq_dec_neq: forall a b,
      a <> b ->
      rel_dec a b = false.
  Proof using A RD RDC.
    intros.
    rewrite <- neg_rel_dec_correct.
    apply H.
  Qed.

  Fixpoint assoc (a:A) (l:list (A * B)) : option B :=
    match l with
    | [] => None
    | (a',b)::l' => if rel_dec a a' then Some b else assoc a l'
    end.

End With_Eqv_Rel_Dec.
