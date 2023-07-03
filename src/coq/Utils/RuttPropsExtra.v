From Vellvm Require Import
  Semantics.LLVMEvents.

From ITree Require Import
  ITree
  Basics
  Basics.HeterogeneousRelations
  Eq.Rutt
  Eq.RuttFacts
  Eq.Eqit
  Eq.EqAxiom.

Require Import Paco.paco.

(* TODO: Should go in the library *)
Lemma rutt_weaken :
  forall {E1 E2} {R1 R2}
    (PRE1 PRE2 : prerel E1 E2)
    (POST1 POST2 : postrel E1 E2)
    (ResR1 ResR2 : R1 -> R2 -> Prop)
    t1 t2,
    rutt PRE1 POST1 ResR1 t1 t2 ->
    (forall {A B} e1 e2, (PRE1 A B e1 e2 -> PRE2 _ _ e1 e2)) ->
    (forall {A B} e1 r1 e2 r2, (POST2 A B e1 r1 e2 r2 -> POST1 _ _ e1 r1 e2 r2)) ->
    (forall r1 r2, (ResR1 r1 r2 -> ResR2 r1 r2)) ->
    rutt PRE2 POST2 ResR2 t1 t2.
Proof.
  intros E1 E2 R1 R2 PRE1 PRE2 POST1 POST2 ResR1 ResR2.

  Hint Resolve rutt_monot : paco.
  Hint Constructors ruttF : itree.
  Hint Unfold rutt_ : itree.
  Hint Unfold rutt : itree.

  pcofix CIH. pstep. intros t1 t2 RUTT. punfold RUTT.
  red in RUTT |- *. induction RUTT; pclearbot; eauto 7 with paco itree.

  intros H2 H3 H4.
  constructor; auto.
  intros a b H1.
  apply H3 in H1.
  apply H0 in H1.
  pclearbot.
  eauto with paco itree.
Qed.

(* TODO: generalize *)
Lemma rutt_raise :
  forall {E1 E2 : Type -> Type} {R1 R2 : Type} `{FailureE -< E1} `{FailureE -< E2}
    {PRE : prerel E1 E2} {POST : postrel E1 E2} {R1R2 : R1 -> R2 -> Prop}
    msg1 msg2,
    PRE void void (subevent void (Throw tt)) (subevent void (Throw tt)) ->
    rutt PRE POST R1R2 (LLVMEvents.raise msg1) (LLVMEvents.raise msg2).
Proof.
  intros E1 E2 R1 R2 FAIL1 FAIL2 PRE POST R1R2 msg1 msg2 PRETHROW.
  unfold LLVMEvents.raise.
  repeat rewrite bind_trigger.
  apply rutt_Vis; auto.
  intros [] [] _.
Qed.
