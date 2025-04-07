From Coq Require Import Morphisms.

From ITree Require Import
     Basics.HeterogeneousRelations
     Axioms
     ITree
     ITreeFacts
     EqAxiom
     Events.State
     Events.StateFacts.

From ITree.Extra Require Import
     Secure.SecureEqHalt
     Secure.SecureEqBind
     Secure.SecureEqEuttHalt
     Secure.StrongBisimProper
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Ltac use_simpobs :=
  repeat match goal with
         | H : TauF _ = observe ?t |- _ => apply simpobs in H
         | H : RetF _ = observe ?t |- _ => apply simpobs in H
         | H : VisF _ _ = observe ?t |- _ => apply simpobs in H
  end.

Section GeneralStateHandler.

Context (S : Type).
Context (RS : S -> S -> Prop).
Context (RS_Eq: Equivalence RS).

Context (E1 E2 : Type -> Type).

Context (handler : E1 ~> stateT S (itree E2) ).

Context (Label : Preorder).
Context (priv1 : forall A, E1 A -> L).
Context (priv2 : forall A, E2 A -> L).
Context (l : L).

Definition state_eqit_secure {R1 R2 : Type} (b1 b2 : bool) (RR : R1 -> R2 -> Prop)
           (m1 : stateT S (itree E2) R1) (m2 : stateT S (itree E2) R2) :=
  forall s1 s2, RS s1 s2 -> eqit_secure Label priv2 (prod_rel RS RR) b1 b2 l (m1 s1) (m2 s2).

Definition top2 {R1 R2} (r1 : R1) (r2 : R2) : Prop := True.


Definition secure_in_nonempty_context {R} (m : stateT S (itree E2) R) :=
   forall r' : R, state_eqit_secure true true top2 m (ret r').

Definition secure_in_empty_context  {R} (m : stateT S (itree E2) R) :=
   state_eqit_secure true true (@top2 R R) m (fun s => ITree.spin).

Inductive terminates (s1 : S) (P : forall A, E2 A -> Prop) : forall {A : Type}, itree E2 (S * A) -> Prop :=
| terminates_ret {R : Type} : forall (r : R) (s2 : S), RS s1 s2 -> terminates s1 P (Ret (s2, r))
| terminates_tau : forall A (t : itree E2 (S * A)) , terminates s1 P t -> terminates s1 P (Tau t)
| terminates_vis {A R : Type} : forall (e : E2 A) (k : A -> itree E2 (S * R)) , (forall v, terminates s1 P (k v)) -> P A e -> terminates s1 P (Vis e k)
.

Variant diverges_with' {E : Type -> Type} (P : forall A, E A -> Prop) (A : Type) (F : itree E A -> Prop) : itree' E A -> Prop :=
  | diverges_tau (t : itree E A): F t -> diverges_with' P A F (TauF t)
  | diverges_vis {B : Type} (e : E B) (k : B -> itree E A) : (forall a, F (k a)) -> P _ e -> diverges_with' P A F (VisF e k).

Definition diverges_with_  {E} (P : forall A, E A -> Prop) {A : Type} (F : itree E A -> Prop) :  itree E A -> Prop :=
  fun t => diverges_with' P A F (observe t).

Definition diverges_with {E} (P : forall A, E A -> Prop) {A : Type} : itree E A -> Prop := paco1 (@diverges_with_ E P A) bot1.

Hint Constructors diverges_with' : itree.
Hint Unfold diverges_with_ : itree.

Lemma mono_diverges_with (E : Type -> Type) P A : monotone1 (@diverges_with_ E P A).
Proof.
  red. intros. red. inversion IN; auto with itree.
Qed.

Hint Resolve mono_diverges_with : paco.

#[global] Instance proper_diverges_with {E A} {P : forall A, E A -> Prop} : Proper (eq_itree eq ==> iff ) (@diverges_with E P A).
Proof.
  do 2 red. intros t1 t2 Heq. apply EqAxiom.bisimulation_is_eq in Heq. subst; tauto.
Qed.

#[global] Instance proper_diverges_with_r  {E A r} {P : forall A, E A -> Prop} : Proper (eq_itree eq ==> iff ) (paco1 (@diverges_with_ E P A) r ).
Proof.
  do 2 red. intros t1 t2 Heq. apply EqAxiom.bisimulation_is_eq in Heq. subst; tauto.
Qed.

#[global] Instance proper_terminate {R s} {P : forall A, E2 A -> Prop} : Proper (eq_itree (@eq (S *R )) ==> iff) (terminates s P).
Proof.
  red. intros t1 t2 Heq. apply EqAxiom.bisimulation_is_eq in Heq. subst; tauto.
Qed.


Lemma diverges_with_bind : forall E (P : forall A, E A -> Prop) (A B : Type) (k : A -> itree E B) (t : itree E A) ,
    diverges_with P t -> diverges_with P (ITree.bind t k).
Proof.
  intros P A B k. pcofix CIH. intros.
  pfold. red. unfold observe. cbn.
  pinversion H0; cbn.
  - constructor; eauto.
  - constructor; intros; eauto. right. eapply CIH; eauto. apply H1.
Qed.

Lemma diverges_with_halt : forall E (A B : Type) (e : E A) (k : A -> itree E B) (P : forall A, E A -> Prop),
    P A e -> empty A -> diverges_with P (Vis e k).
Proof.
  intros. pfold. constructor; auto. intros; contra_size.
Qed.

Lemma diverges_secure_equiv_halt_r : forall A R1 R2 RR (e : E1 A) (k : A -> itree E1 R1) (t : itree E1 R2),
    empty A ->
    ~ leq (priv1 _ e) l ->
    eqit_secure Label priv1 RR true true l (Vis e k) t ->
    diverges_with (fun _ e => ~ leq (priv1 _ e) l) t.
Proof.
  intros A R1 R2 RR e k t Hemp Hsec. revert t. pcofix CIH.
  intros. punfold H0. red in H0.
  cbn in *. remember (VisF e k) as ov. remember (observe t) as ot.
  hinduction H0 before r; intros; inv Heqov; subst; ddestruction; subst; try discriminate;  try contradiction;
    try contra_size; use_simpobs.
  - rewrite Heqot. pfold. constructor. left. eapply IHsecure_eqitF; eauto.
  - pclearbot. rewrite Heqot. pfold. constructor; eauto.
  - rewrite Heqot. pfold. constructor. right. pclearbot. eapply CIH; eauto.
  - pclearbot. rewrite Heqot. pfold. constructor; auto. right. eapply CIH; eauto. apply H.
  - rewrite Heqot. pfold. constructor; auto. right. eapply CIH; eauto. contra_size.
Qed.

Lemma diverges_secure_equiv_halt_l : forall A R1 R2 RR (e : E1 A) (k : A -> itree E1 R1) (t : itree E1 R2),
    empty A ->
    ~ leq (priv1 _ e) l ->
    eqit_secure Label priv1 RR true true l t (Vis e k) ->
    diverges_with (fun _ e => ~ leq (priv1 _ e) l) t.
Proof.
  intros A R1 R2 RR e k t Hemp Hsec. revert t. pcofix CIH.
  intros. punfold H0. red in H0.
  cbn in *. remember (VisF e k) as ov. remember (observe t) as ot.
  hinduction H0 before r; intros; inv Heqov; subst; ddestruction; subst; try discriminate;  try contradiction;
    try contra_size; use_simpobs.
  - rewrite Heqot. pfold. constructor. left. eapply IHsecure_eqitF; eauto.
  - pclearbot. rewrite Heqot. pfold. constructor; eauto.
  - rewrite Heqot. pfold. constructor. right. pclearbot. eapply CIH; eauto.
  - pclearbot. rewrite Heqot. pfold. constructor; auto. right. eapply CIH; eauto. contra_size.
  - pclearbot. rewrite Heqot. pfold. constructor; auto. right. eapply CIH; eauto. apply H.
Qed.

Lemma diverges_with_spin : forall E A P,
    diverges_with P (@ITree.spin E A).
Proof.
  intros. pcofix CIH. pfold. red. cbn. constructor.
  right; auto.
Qed.

Lemma eqit_secure_silent_diverge : forall A B RR (t1 : itree E2 A) (t2 : itree E2 B),
    diverges_with (fun _ e => ~ leq (priv2 _ e) l) t1 ->
    diverges_with (fun _ e => ~ leq (priv2 _ e) l) t2 ->
    eqit_secure Label priv2 RR true true l t1 t2.
Proof.
  intros A B RR. pcofix CIH. intros.
  punfold H0. red in H0. punfold H1. red in H1.
  inversion H0; inversion H1; use_simpobs; try rewrite H; try rewrite H3.
  - pfold. constructor. right. pclearbot. eapply CIH; eauto.
  - destruct (classic_empty B0).
    + pclearbot. pfold. constructor; auto. pstep_reverse. clear H. clear CIH.
      generalize dependent t. pcofix CIH. intros.
      pinversion H2; use_simpobs.
      * rewrite H. pfold. red. cbn. unpriv_halt.
      * rewrite H. pfold. red. cbn. unpriv_halt.
    + pfold. red. cbn. unpriv_co. right. pclearbot. eapply CIH; eauto. apply H4.
  - pclearbot. destruct (classic_empty B0).
    + pclearbot. clear H4. clear CIH.
      generalize dependent t2. pcofix CIH. intros.
      inversion H4; use_simpobs.
      * rewrite H1. pfold. red. cbn. pclearbot. unpriv_halt. right. eapply CIH; eauto. punfold H7.
      * rewrite H1. pfold. red. cbn. unpriv_halt. right. pclearbot. eapply CIH; eauto. pstep_reverse.
    + rewrite H4. pfold. red. cbn. unpriv_co. right. pclearbot. eapply CIH; eauto. apply H2.
  - pclearbot. rewrite H4.
    destruct (classic_empty B0); destruct (classic_empty B1).
    + pfold. red. cbn. unpriv_halt. contra_size.
    + assert (diverges_with (fun _ e => ~ leq (priv2 _ e) l) (Vis e0 k0)).
      { pfold. constructor; auto. }
      rewrite <- H4. rewrite <- H4 in H9. clear H4. clear H1 CIH. generalize dependent t2.
      pcofix CIH. intros. pinversion H9; use_simpobs.
      * rewrite H1. pfold. red. cbn. unpriv_halt.
      * rewrite H1. pfold. red. cbn. unpriv_halt. right. eapply CIH; eauto. apply H4.
    + assert (diverges_with (fun _ e => ~ leq (priv2 _ e) l) (Vis e k)).
      { pfold. constructor; auto. }
      rewrite <- H. rewrite <- H in H9. clear H. clear H0 CIH. generalize dependent t1.
      pcofix CIH. intros. pinversion H9; use_simpobs.
      * rewrite H. pfold. red. cbn. unpriv_halt.
      * rewrite H. pfold. red. cbn. unpriv_halt. right. eapply CIH; eauto. apply H0.
    + pfold. red. cbn. unpriv_co. right. eapply CIH; eauto. apply H2. apply H5.
Qed.

Lemma silent_diverges_eqit_secure_spin : forall A B (RR : A -> B -> Prop) (t : itree E2 A),
    diverges_with (fun _ e => ~ leq (priv2 _ e) l) t <-> eqit_secure Label priv2 RR true true l t (ITree.spin).
Proof.
  intros. split.
  { intros. eapply eqit_secure_silent_diverge; eauto. apply diverges_with_spin. }
  revert t. pcofix CIH.
  intros t Ht. punfold Ht. red in Ht. remember (observe t) as ot.
  remember (observe ITree.spin) as otspin.
  hinduction Ht before r; intros; subst; try discriminate; use_simpobs.
  - pclearbot. rewrite Heqot. pfold. constructor. right. eapply CIH; eauto. rewrite Heqotspin.
    pfold; constructor; auto. pstep_reverse.
  - rewrite Heqot. pfold; constructor. left. eapply IHHt; eauto.
  - eapply IHHt; eauto. assert (ITree.spin ≅ t2).
    { clear IHHt Ht. generalize dependent t2. pcofix CIH'.
      intros. punfold Heqotspin. red in Heqotspin.  cbn in *. inversion Heqotspin; try inv CHECK0.
      subst. pclearbot. eapply paco2_mon; eauto; intros; try contradiction. }
    apply EqAxiom.bisimulation_is_eq in H. subst; auto.
  - rewrite Heqot. pfold. constructor; auto. right. eapply CIH; eauto. pclearbot. rewrite Heqotspin.
    pfold; constructor; auto. pstep_reverse.
  - rewrite Heqot. pfold. constructor; auto. left. eapply H0; eauto.
  - rewrite Heqot. pclearbot. pfold; constructor; auto. right. eapply CIH; eauto.
    rewrite Heqotspin. pfold; constructor; auto. pstep_reverse.  eapply unpriv_e_eqit_secure; eauto.
Qed.


Lemma silent_terminates_eqit_secure_ret : forall R (m : stateT S (itree E2) R), nonempty R ->
      (forall s, terminates s (fun B e => ~ leq (priv2 _ e) l /\ nonempty B) (m s) ) <-> forall r' : R, state_eqit_secure true true top2 m (ret r').
Proof.
  split; intros.
  - red. intros. specialize (H0 s1).
    cbn. induction H0.
    + pfold; constructor. split; try constructor. cbn. etransitivity; eauto. symmetry. auto.
    + pfold; constructor; auto. pstep_reverse. eapply IHterminates; eauto.
    + destruct H3. pfold. red. cbn. timeout 10 setoid_rewrite itree_eta' at 2.  unpriv_ind.
      pstep_reverse. eapply H2; eauto.
  - cbn in *. red in H0. assert (RS s s). reflexivity.
    inv H.
    specialize (H0 a s s H1). remember (m s) as t. clear Heqt.
    punfold H0. red in H0. cbn in H0. remember (RetF (s,a) ) as oret. remember (observe t) as ot.
    hinduction H0 before E1; intros; try discriminate; use_simpobs.
    + rewrite Heqot. injection Heqoret; intros; subst. destruct r1, H. cbn in *.
      constructor. symmetry. auto.
    + rewrite Heqot. constructor. eapply IHsecure_eqitF; eauto.
    + rewrite Heqot. constructor; eauto.
Qed.

Variant handler_respects_priv (A : Type) (e : E1 A) : Prop :=
| respect_private (SECCHECK : ~ leq (priv1 _ e) l)
                  (FINCHECK : forall s, terminates s (fun _ e' => ~ leq (priv2 _ e') l) (handler A e s))
| respect_public (SECCHECK : leq (priv1 _ e) l)
                 (RESCHECK : state_eqit_secure true true eq (handler A e) (handler A e))
.

Variant handler_respects_priv' (A : Type) (e : E1 A) : Prop :=
| respect_private_ne (SECCHECK : ~ leq (priv1 _ e) l) (SIZECHECK : nonempty A)
                  (FINCHECK :  forall s, terminates s (fun B e' => ~ leq (priv2 _ e') l /\ nonempty B ) (handler A e s) )
| respect_private_e (SECCHECK : ~ leq (priv1 _ e) l) (SIZECHECK : empty A)
                  (DIVCHECK : forall s, diverges_with (fun _ e' => ~ leq (priv2 _ e') l ) (handler A e s) )
| respect_public' (SECCHECK : leq (priv1 _ e) l)
                 (RESCHECK : state_eqit_secure true true eq (handler A e) (handler A e))
.

Context (Hhandler : forall A (e : E1 A), handler_respects_priv' A e).

Lemma diverge_with_respectful_handler : forall (R : Type) (t : itree E1 R),
    diverges_with (fun _ e => ~ leq (priv1 _ e) l ) t ->
    forall s, diverges_with (fun _ e => ~ leq (priv2 _ e) l) (interp_state handler t s).
Proof.
  intro R. pcofix CIH. intros t Hdiv s. pinversion Hdiv; use_simpobs.
  - rewrite H. rewrite interp_state_tau. pfold. constructor. right. eapply CIH; eauto.
  - rewrite H. rewrite interp_state_vis.
    destruct (classic_empty B).
    + specialize (Hhandler _ e). destruct Hhandler; try contradiction; try contra_size.
      specialize (DIVCHECK s). eapply paco1_mon with (r:= bot1). eapply diverges_with_bind; eauto.
      intros; contradiction.
    + specialize (Hhandler _ e). destruct Hhandler; try contradiction; try contra_size.
      specialize (FINCHECK s). induction FINCHECK.
      * rewrite bind_ret_l. cbn. pfold. constructor. right. eapply CIH; eauto. apply H0.
      * rewrite bind_tau. pfold. constructor. left. eapply IHFINCHECK; eauto.
      * destruct H5. rewrite bind_vis. pfold. constructor; auto. left. eapply H4; eauto.
Qed.



Lemma interp_eqit_secure_state : forall (R1 R2 : Type) (RR : R1 -> R2 -> Prop) (t1 : itree E1 R1) (t2 : itree E1 R2),
    eqit_secure Label priv1 RR true true l t1 t2 ->
    state_eqit_secure true true RR (interp_state handler t1) (interp_state handler t2).
Proof.
  intros R1 R2 RR. pcofix CIH. intros t1 t2 Ht s1 s2 Hs. punfold Ht.
  red in Ht. remember (observe t1) as ot1. remember (observe t2) as ot2.
  hinduction Ht before r; intros; use_simpobs.
  - rewrite Heqot1. rewrite Heqot2. repeat rewrite interp_state_ret. pfold. constructor. auto.
  - rewrite Heqot1. rewrite Heqot2. repeat rewrite interp_state_tau. pfold. constructor.
    pclearbot. right. apply CIH; auto.
  - rewrite Heqot1. rewrite interp_state_tau. pfold. constructor; auto. pstep_reverse.
  - rewrite Heqot2. rewrite interp_state_tau. pfold. constructor; auto. pstep_reverse.
  - rewrite Heqot1. rewrite Heqot2. repeat rewrite interp_state_vis.
    specialize (Hhandler A e). pclearbot. repeat rewrite bind_tau.
    (* could use the bind closure here, but maybe we can do manually for now*)
    repeat setoid_rewrite <- interp_state_tau. inv Hhandler; try contradiction.
    specialize (RESCHECK s1 s2 Hs).
    eapply secure_eqit_bind'; eauto. intros [] [] []. simpl in *. subst.
    repeat rewrite interp_state_tau.
    pfold. constructor. right. eapply CIH; eauto. apply H.
  - pclearbot. rewrite Heqot1. rewrite Heqot2.
    rewrite interp_state_tau. rewrite interp_state_vis.
    specialize (Hhandler A e). inv Hhandler; try contradiction; try contra_size.
    specialize (FINCHECK s1). induction FINCHECK.
    + rewrite bind_ret_l. pstep. constructor. right.
      apply CIH. apply H. etransitivity; [symmetry |]; eauto.
    + rewrite bind_tau. pstep. constructor 3; auto. pstep_reverse.
    + rewrite bind_vis. pstep. destruct H2. constructor 9; auto. intros. pstep_reverse.
  - pclearbot. rewrite Heqot1. rewrite Heqot2.
    rewrite interp_state_tau. rewrite interp_state_vis.
    specialize (Hhandler A e). inv Hhandler; try contradiction; try contra_size.
    specialize (FINCHECK s2). induction FINCHECK.
    + rewrite bind_ret_l. pstep. constructor. right.
      apply CIH. apply H. etransitivity; eauto.
    + rewrite bind_tau. pstep. constructor 4; auto. pstep_reverse.
    + rewrite bind_vis. pstep. destruct H2. constructor 10; auto. intros. pstep_reverse.
  - pclearbot. rewrite Heqot1. rewrite Heqot2. repeat rewrite interp_state_vis.
    specialize (Hhandler _ e1) as He1. specialize (Hhandler _ e2) as He2.
    inv He1; inv He2; try contradiction; try contra_size.
    eapply secure_eqit_bind' with (RR := prod_rel RS (fun _ _ => True)).
    + intros [] [] ?. pstep. constructor. right.
      apply CIH. apply H. simpl. apply H0.
    + specialize (FINCHECK s1). specialize (FINCHECK0 s2).
      induction FINCHECK.
      * induction FINCHECK0.
        -- simpl. pstep. constructor. split; auto. simpl.
           transitivity s2; eauto. etransitivity; [symmetry |]; eauto.
        -- pstep. constructor; auto. pstep_reverse. eapply IHFINCHECK0; eauto.
        -- pstep. destruct H3. constructor; auto. intros. pstep_reverse. eapply H2; eauto.
      * pstep. constructor; auto. pstep_reverse. eapply IHFINCHECK; eauto.
      * pstep. destruct H2. constructor; auto. intros. pstep_reverse. eapply H1; eauto.
  - rewrite Heqot1. rewrite interp_state_vis. specialize (Hhandler _ e).
    inv Hhandler; try contradiction; try contra_size.
    specialize (FINCHECK s1). induction FINCHECK.
    + rewrite bind_ret_l. pstep. constructor; auto. pstep_reverse.
      eapply H0; eauto. simpl. etransitivity; [symmetry |]; eauto.
    + rewrite bind_tau. pstep. constructor 3; auto. pstep_reverse.
    + rewrite bind_vis. pstep. destruct H3. constructor 9; auto. intros. pstep_reverse.
  - rewrite Heqot2. rewrite interp_state_vis. specialize (Hhandler _ e).
    inv Hhandler; try contradiction; try contra_size.
    specialize (FINCHECK s2). induction FINCHECK.
    + rewrite bind_ret_l. pstep. constructor 4; auto. pstep_reverse.
      eapply H0; eauto. simpl. etransitivity; eauto.
    + rewrite bind_tau. pstep. constructor 4; auto. pstep_reverse.
    + rewrite bind_vis. pstep. destruct H3. constructor 10; auto. intros. pstep_reverse.
  - pclearbot.
    rewrite Heqot1. rewrite interp_state_vis.
    rewrite Heqot2. rewrite interp_state_tau.
    pose proof Hhandler as Hhandler'.
    specialize (Hhandler' _ e). inv Hhandler'; try contradiction; try contra_size.
    eapply paco2_mon with (r:= bot2); intros; try contradiction. eapply eqit_secure_silent_diverge.
    + eapply diverges_with_bind; eauto.
    + pfold. constructor. left. eapply diverge_with_respectful_handler; eauto.
      eapply diverges_secure_equiv_halt_r; eauto.
  - pclearbot.
    rewrite Heqot1. rewrite interp_state_tau.
    rewrite Heqot2. rewrite interp_state_vis.
    pose proof Hhandler as Hhandler'.
    specialize (Hhandler' _ e). inv Hhandler'; try contradiction; try contra_size.
    eapply paco2_mon with (r:= bot2); intros; try contradiction. eapply eqit_secure_silent_diverge.
    + pfold. constructor. left. eapply diverge_with_respectful_handler; eauto.
      eapply diverges_secure_equiv_halt_l; eauto.
    + eapply diverges_with_bind; eauto.
  - pclearbot. rewrite Heqot1. rewrite Heqot2. repeat rewrite interp_state_vis.
    pose proof Hhandler as Hhandler'.
    pose proof Hhandler as Hhandler''.
    specialize (Hhandler'' _ e2). inv Hhandler''; try contradiction; try contra_size.
    specialize (Hhandler' _ e1). inv Hhandler'; try contradiction; try contra_size.
    eapply paco2_mon with (r:= bot2); intros; try contradiction. eapply eqit_secure_silent_diverge.
    + eapply diverges_with_bind; eauto.
    + specialize (FINCHECK s2). induction FINCHECK.
      * rewrite bind_ret_l. pfold; constructor. left. cbn.
        eapply diverge_with_respectful_handler; eauto. eapply diverges_secure_equiv_halt_r; eauto.
        apply H.
      * rewrite bind_tau. pfold; constructor. left. eapply IHFINCHECK; eauto.
      * rewrite bind_vis. pfold. constructor. left. eapply H1; eauto. destruct H2; auto.
    + eapply paco2_mon with (r:= bot2); intros; try contradiction. eapply eqit_secure_silent_diverge.
      * apply diverges_with_bind. specialize (Hhandler _ e1). inv Hhandler; try contradiction; try contra_size; auto.
      * apply diverges_with_bind; auto.
  - pclearbot. rewrite Heqot1. rewrite Heqot2. repeat rewrite interp_state_vis.
    pose proof Hhandler as Hhandler'.
    pose proof Hhandler as Hhandler''.
    eapply paco2_mon with (r:= bot2); intros; try contradiction. eapply eqit_secure_silent_diverge.
    + specialize (Hhandler'' _ e1). inv Hhandler''; try contradiction; try contra_size.
      * specialize (FINCHECK s1). induction FINCHECK.
        ++ rewrite bind_ret_l. pfold; constructor. cbn. left.
           eapply diverge_with_respectful_handler. eapply diverges_secure_equiv_halt_l; eauto. apply H.
        ++ rewrite bind_tau. pfold. constructor. left. eapply IHFINCHECK; eauto.
        ++ destruct H2. rewrite bind_vis. pfold. constructor; auto. left. eapply H1; eauto.
      * apply diverges_with_bind; auto.
    + specialize (Hhandler'' _ e2). inv Hhandler''; try contradiction; try contra_size.
      apply diverges_with_bind; auto.
Qed.

End GeneralStateHandler.
