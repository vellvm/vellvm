(* begin hide *)
From Coq Require Import
     RelationClasses
     Morphisms
     Program.Equality.

From Paco Require Import paco.
From ITree Require Import
     ITree
     ITreeFacts
     Eq.Eqit.
Set Implicit Arguments.
Set Strict Implicit.
(* end hide *)

(** * NoEvent
    We develop in this file a theory to reason about absence of a given event signature
    in a tree, and how to use this absence to safely eliminate this signature from the tree.
 *)

(** * Signature vacuousness
  A simple way to assert the absence of a signature is based on the shape of the signature.
  We define straightforward non-recursive functors and take the cofixed points.
 *)

(* The left part of the signature is absent *)
Variant no_event_lF {E F X} (R: itree (E +' F) X -> Prop) : itree' (E +' F) X -> Prop :=
| no_event_l_ret: forall (x: X), no_event_lF R (RetF x)
| no_event_l_tau: forall t, R t -> no_event_lF R (TauF t)
| no_event_l_vis: forall {Y} (e: F Y) k, (forall x, R (k x)) -> no_event_lF R (VisF (inr1 e) k).
#[export] Hint Constructors no_event_lF : core.

Lemma no_event_lF_mono : forall {E F X} (R1 R2 : itree (E +' F) X -> Prop) (LE : R1 <1= R2),
    no_event_lF R1 <1= no_event_lF R2.
Proof using.
  intros.
  induction PR; auto.
Qed.

Definition no_event_lF_ {E F X} R (t : itree (E +' F) X) := no_event_lF R (observe t).
#[export] Hint Unfold no_event_lF_ : core.

Lemma no_event_lF__mono : forall E F X, (monotone1 (@no_event_lF_ E F X)).
Proof using.
  do 2 red.
  intros.
  eapply no_event_lF_mono; eauto.
Qed.

#[export] Hint Resolve no_event_lF_mono : paco.

Definition no_event_l {E F X} := paco1 (@no_event_lF_ E F X) bot1.

(* This exists in the stdlib as [ProofIrrelevance.inj_pair2], but we reprove
   it to not depend on proof irrelevance (we use axiom [JMeq.JMeq_eq] instead).
   The itree library now avoids as much as possible using this axiom, we may want
   to see if it's possible to do so here.
 *)
Lemma inj_pair2 :
  forall (U : Type) (P : U -> Type) (p : U) (x y : P p),
    existT P p x = existT P p y -> x = y.
  Proof using.
    intros. apply JMeq.JMeq_eq.
    refine (
        match H in _ = w return JMeq.JMeq x (projT2 w) with
        | eq_refl => JMeq.JMeq_refl
        end).
  Qed.

(* The right part of the signature is absent *)
Variant no_event_rF {E F X} (R: itree (E +' F) X -> Prop): itree' (E +' F) X -> Prop :=
| no_event_r_ret: forall (x: X), no_event_rF R (RetF x)
| no_event_r_tau: forall t, R t -> no_event_rF R (TauF t)
| no_event_r_vis: forall {Y} (e: E Y) k, (forall x, R (k x)) -> no_event_rF R (VisF (inl1 e) k).

#[export] Hint Constructors no_event_rF : core.

Lemma no_event_rF_mono : forall {E F X} (R1 R2 : itree (E +' F) X -> Prop) (LE : R1 <1= R2),
    no_event_rF R1 <1= no_event_rF R2.
Proof using.
  intros.
  induction PR; auto.
Qed.

Definition no_event_rF_ {E F X} R (t : itree (E +' F) X) := no_event_rF R (observe t).
#[export] Hint Unfold no_event_rF_ : core.

Lemma no_event_rF__mono : forall E F X, (monotone1 (@no_event_rF_ E F X)).
Proof using.
  do 2 red.
  intros.
  eapply no_event_rF_mono; eauto.
Qed.

#[export] Hint Resolve no_event_rF_mono : paco.

Definition no_event_r {E F X} := paco1 (@no_event_rF_ E F X) bot1.

(* The tree contains no event *)
Variant no_eventF {E X} (R: itree E X -> Prop): itree' E X -> Prop :=
| no_event_ret: forall (x: X), no_eventF R (RetF x)
| no_event_tau: forall t, R t -> no_eventF R (TauF t).

#[export] Hint Constructors no_eventF : core.

Lemma no_eventF_mono : forall {E X} (R1 R2 : itree E X -> Prop) (LE : R1 <1= R2),
    no_eventF R1 <1= no_eventF R2.
Proof using.
  intros.
  induction PR; auto.
Qed.

Definition no_eventF_ {E X} R (t : itree E X) := no_eventF R (observe t).
#[export] Hint Unfold no_eventF_ : core.

Lemma no_eventF__mono : forall E X, (monotone1 (@no_eventF_ E X)).
Proof using.
  do 2 red.
  intros.
  eapply no_eventF_mono; eauto.
Qed.

#[export] Hint Resolve no_eventF_mono : paco.

Definition no_event {E X} := paco1 (@no_eventF_ E X) bot1.

(** up-to eq_itree closure
  Coinductive proofs about no_event can be performed up-to `eq_itree`.

  Note that up-to eutt is not valid:
    Tau (Vis e k)
        |  no_eventF
        v
      Vis e k ~~ Tau (Vis e k)

  Up-to euttge is valid as well.
  *)
Section eqit_closure.

  Inductive eqit_clo {E R} (r : itree E R -> Prop)
    : itree E R -> Prop :=
  | eqit_clo_intro b t t' (EQVl: eqit eq b false t t') (REL: r t')
    : eqit_clo r t.
  Hint Constructors eqit_clo: core.

  Lemma eqit_clo_mon {E R} r1 r2 t
        (IN: eqit_clo r1 t)
        (LE: r1 <1= r2):
    @eqit_clo E R r2 t.
  Proof using.
    destruct IN. econstructor; eauto.
  Qed.

  Lemma no_event_eqit_clo_wcompat {E R} :
    wcompatible1 (@no_eventF_ E R) eqit_clo.
  Proof using.
    econstructor.
    pmonauto.
    intros.
    inv PR.
    punfold EQVl.
    unfold_eqit.
    unfold no_eventF_ in *.
    induction EQVl; auto.
    - inv REL.
      constructor.
      pclearbot.
      gclo; econstructor; cycle -1; eauto with paco.
    - inv REL.
    - constructor.
      gstep; auto.
    - congruence.
  Qed.

  #[global] Instance eq_itree_no_event_cong {E R} r rg :
    Proper ((eq_itree eq) ==> flip impl) (gpaco1 (@no_eventF_ E R) eqit_clo r rg).
  Proof using.
    repeat intro.
    gclo.
    econstructor; cycle -1; eauto.
  Qed.

  #[global] Instance euttge_no_event_cong {E R} r rg :
    Proper ((euttge eq) ==> flip impl) (gpaco1 (@no_eventF_ E R) eqit_clo r rg).
  Proof using.
    repeat intro.
    gclo.
    econstructor; cycle -1; eauto.
  Qed.

  Lemma no_event_r_eqit_clo_wcompat {E F R} :
    wcompatible1 (@no_event_rF_ E F R) eqit_clo.
  Proof using.
    econstructor.
    pmonauto.
    intros.
    inv PR.
    punfold EQVl.
    unfold_eqit.
    unfold no_event_rF_ in *.
    induction EQVl; auto.
    - inv REL.
      constructor.
      pclearbot.
      gclo; econstructor; cycle -1; eauto with paco.
    - destruct e.
      + constructor.
        dependent induction REL.
        pclearbot; intros; gclo; econstructor; cycle -1; eauto with paco.
        apply REL0.
      + inv REL.
    - constructor.
      gstep; auto.
    - congruence.
  Qed.

  #[global] Instance eq_itree_no_event_r_cong {E F R} r rg :
    Proper ((eq_itree eq) ==> flip impl) (gpaco1 (@no_event_rF_ E F R) eqit_clo r rg).
  Proof using.
    repeat intro.
    gclo.
    econstructor; cycle -1; eauto.
  Qed.

  #[global] Instance euttge_no_event_r_cong {E F R} r rg :
    Proper ((euttge eq) ==> flip impl) (gpaco1 (@no_event_rF_ E F R) eqit_clo r rg).
  Proof using.
    repeat intro.
    gclo.
    econstructor; cycle -1; eauto.
  Qed.

  Lemma no_event_l_eqit_clo_wcompat {E F R} :
    wcompatible1 (@no_event_lF_ E F R) eqit_clo.
  Proof using.
    econstructor.
    pmonauto.
    intros.
    inversion PR.
    punfold EQVl.
    unfold_eqit.
    unfold no_event_lF_ in *.
    induction EQVl; auto.
    - inversion REL.
      constructor.
      pclearbot.
      gclo; econstructor; cycle -1; eauto with paco.
    - destruct e.
      + inversion REL.
      + constructor.
        dependent induction REL.
        pclearbot; intros; gclo; econstructor; cycle -1; eauto with paco.
        apply REL0.
    - constructor.
      gstep; auto.
    - congruence.
  Qed.

  #[global] Instance eq_itree_no_event_l_cong {E F R} r rg :
    Proper ((eq_itree eq) ==> flip impl) (gpaco1 (@no_event_lF_ E F R) eqit_clo r rg).
  Proof using.
    repeat intro.
    gclo.
    econstructor; cycle -1; eauto.
  Qed.

  #[global] Instance euttge_no_event_l_cong {E F R} r rg :
    Proper ((euttge eq) ==> flip impl) (gpaco1 (@no_event_lF_ E F R) eqit_clo r rg).
  Proof using.
    repeat intro.
    gclo.
    econstructor; cycle -1; eauto.
  Qed.

End eqit_closure.
#[export] Hint Resolve eqit_clo_mon : paco.
#[export] Hint Constructors eqit_clo: core.
#[export] Hint Resolve no_event_eqit_clo_wcompat : paco.
#[export] Hint Resolve no_event_l_eqit_clo_wcompat : paco.
#[export] Hint Resolve no_event_r_eqit_clo_wcompat : paco.

(* In particular [eq_itree] is hence a congruence for [no_event] *)
#[global] Instance no_event_l_eq_itree {E F X} : Proper (eq_itree eq ==> iff) (@no_event_l E F X).
Proof using.
  repeat red. intros. split; intros.
  ginit. rewrite <- H. gfinal; auto.
  ginit. rewrite H. gfinal; auto.
Qed.

#[global] Instance no_event_r_eq_itree {E F X} : Proper (eq_itree eq ==> iff) (@no_event_r E F X).
Proof using.
  repeat red. intros. split; intros.
  ginit. rewrite <- H. gfinal; auto.
  ginit. rewrite H. gfinal; auto.
Qed.

#[global] Instance no_event_eq_itree {E X} : Proper (eq_itree eq ==> iff) (@no_event E X).
Proof using.
  repeat red. intros. split; intros.
  ginit. rewrite <- H. gfinal; auto.
  ginit. rewrite H. gfinal; auto.
Qed.

(* But although not a valid up-to, [eutt] is also a congruence for [no_event] *)
#[global] Instance no_event_l_eutt {E F X} : Proper (eutt eq ==> iff) (@no_event_l E F X).
Proof using.
  do 2 red.
  repeat red. intros. split; intros.
  - revert x y H H0.
    pcofix CIH.
    intros x y H0 H1.
    + punfold H0. red in H0.
      punfold H1. red in H1.
      genobs x ox.
      genobs y oy.
      pstep. red.
      revert x Heqox y Heqoy.
      induction H0; inversion H1; intros; subst.
      * rewrite <- Heqoy. econstructor.
      * rewrite <- Heqoy. econstructor. pclearbot. right. eapply CIH. 2:  { apply H0. }  apply REL.
      * rewrite <- Heqoy. destruct e. inversion H1. econstructor. intros.
        specialize (REL x0). red in REL. pclearbot. right. eapply CIH. apply REL.
        apply inj_pair2 in H3. rewrite <- H3. specialize (H0 x0). apply H0.
      * eapply IHeqitF. pclearbot. punfold H2. reflexivity. reflexivity.
      * rewrite <- Heqoy. econstructor. left.
        pstep. red. eapply IHeqitF. econstructor. apply Heqox. reflexivity.
      * rewrite <- Heqoy. econstructor. left.
        pstep. red. eapply IHeqitF. econstructor. assumption. apply Heqox. reflexivity.
      * rewrite <- Heqoy. econstructor. left.
        pstep. red. eapply IHeqitF. econstructor. intros. apply H. apply Heqox. reflexivity.
  - revert x y H H0.
    pcofix CIH.
    intros x y H0 H1.
    + punfold H0. red in H0.
      punfold H1. red in H1.
      genobs x ox.
      genobs y oy.
      pstep. red.
      revert x Heqox y Heqoy.
      induction H0; inversion H1; intros; subst.
      * rewrite <- Heqox. econstructor.
      * rewrite <- Heqox. econstructor. pclearbot. right. eapply CIH. 2:  { apply H0. }  apply REL.
      * rewrite <- Heqox. destruct e. inversion H1. econstructor. intros.
        specialize (REL x0). red in REL. pclearbot. right. eapply CIH. apply REL.
        apply inj_pair2 in H3. rewrite <- H3. specialize (H0 x0). apply H0.
      * rewrite <- Heqox. econstructor. left.
        pstep. red. eapply IHeqitF. econstructor. reflexivity. apply Heqoy.
      * rewrite <- Heqox. econstructor. left.
        pstep. red. eapply IHeqitF. econstructor. assumption. reflexivity. apply Heqoy.
      * rewrite <- Heqox. econstructor. left.
        pstep. red. eapply IHeqitF. econstructor. intros. apply H. reflexivity. apply Heqoy.
      * eapply IHeqitF. pclearbot. punfold H2. reflexivity. reflexivity.
Qed.

#[global] Instance no_event_r_eutt {E F X} : Proper (eutt eq ==> iff) (@no_event_r E F X).
Proof using.
  do 2 red.
  repeat red. intros. split; intros.
  - revert x y H H0.
    pcofix CIH.
    intros x y H0 H1.
    + punfold H0. red in H0.
      punfold H1. red in H1.
      genobs x ox.
      genobs y oy.
      pstep. red.
      revert x Heqox y Heqoy.
      induction H0; inversion H1; intros; subst.
      * rewrite <- Heqoy. econstructor.
      * rewrite <- Heqoy. econstructor. pclearbot. right. eapply CIH. 2:  { apply H0. }  apply REL.
      * rewrite <- Heqoy. destruct e. econstructor. intros.
        specialize (REL x0). red in REL. pclearbot. right. eapply CIH. apply REL.
        apply inj_pair2 in H3. rewrite <- H3. specialize (H0 x0). apply H0.
        inversion H1.
      * eapply IHeqitF. pclearbot. punfold H2. reflexivity. reflexivity.
      * rewrite <- Heqoy. econstructor. left.
        pstep. red. eapply IHeqitF. econstructor. apply Heqox. reflexivity.
      * rewrite <- Heqoy. econstructor. left.
        pstep. red. eapply IHeqitF. econstructor. assumption. apply Heqox. reflexivity.
      * rewrite <- Heqoy. econstructor. left.
        pstep. red. eapply IHeqitF. econstructor. intros. apply H. apply Heqox. reflexivity.
  - revert x y H H0.
    pcofix CIH.
    intros x y H0 H1.
    + punfold H0. red in H0.
      punfold H1. red in H1.
      genobs x ox.
      genobs y oy.
      pstep. red.
      revert x Heqox y Heqoy.
      induction H0; inversion H1; intros; subst.
      * rewrite <- Heqox. econstructor.
      * rewrite <- Heqox. econstructor. pclearbot. right. eapply CIH. 2:  { apply H0. }  apply REL.
      * rewrite <- Heqox. destruct e. econstructor. intros.
        specialize (REL x0). red in REL. pclearbot. right. eapply CIH. apply REL.
        apply inj_pair2 in H3. rewrite <- H3. specialize (H0 x0). apply H0.
        inversion H1.
      * rewrite <- Heqox. econstructor. left.
        pstep. red. eapply IHeqitF. econstructor. reflexivity. apply Heqoy.
      * rewrite <- Heqox. econstructor. left.
        pstep. red. eapply IHeqitF. econstructor. assumption. reflexivity. apply Heqoy.
      * rewrite <- Heqox. econstructor. left.
        pstep. red. eapply IHeqitF. econstructor. intros. apply H. reflexivity. apply Heqoy.
      * eapply IHeqitF. pclearbot. punfold H2. reflexivity. reflexivity.
Qed.

#[global] Instance no_event_eutt {E X} : Proper (eutt eq ==> iff) (@no_event E X).
Proof using.
  repeat red. intros. split; intros.
  - revert x y H H0.
    pcofix CIH.
    intros x y H0 H1.
    + punfold H0. red in H0.
      punfold H1. red in H1.
      genobs x ox.
      genobs y oy.
      pstep. red.
      revert x Heqox y Heqoy.
      induction H0; inversion H1; intros; subst.
      * rewrite <- Heqoy. econstructor.
      * rewrite <- Heqoy. econstructor. pclearbot. right. eapply CIH. 2:  { apply H0. }  apply REL.
      * eapply IHeqitF. pclearbot. punfold H2. reflexivity. reflexivity.
      * rewrite <- Heqoy. econstructor. left.
        pstep. red. eapply IHeqitF. econstructor. apply Heqox. reflexivity.
      * rewrite <- Heqoy. econstructor. left.
        pstep. red. eapply IHeqitF. econstructor. assumption. apply Heqox. reflexivity.
  - revert x y H H0.
    pcofix CIH.
    intros x y H0 H1.
    + punfold H0. red in H0.
      punfold H1. red in H1.
      genobs x ox.
      genobs y oy.
      pstep. red.
      revert x Heqox y Heqoy.
      induction H0; inversion H1; intros; subst.
      * rewrite <- Heqox. econstructor.
      * rewrite <- Heqox. econstructor. pclearbot. right. eapply CIH. 2:  { apply H0. }  apply REL.
      * rewrite <- Heqox. econstructor. left.
        pstep. red. eapply IHeqitF. econstructor. reflexivity. apply Heqoy.
      * rewrite <- Heqox. econstructor. left.
        pstep. red. eapply IHeqitF. econstructor. assumption. reflexivity. apply Heqoy.
      * eapply IHeqitF. pclearbot. punfold H2. reflexivity. reflexivity.
Qed.

(* Sanity check, trees with empty signature should have no event *)
Lemma no_event_empty {X} : forall (t: itree void1 X), no_event t.
Proof using.
  pcofix CIH.
  intros t.
  pstep.
  red.
  genobs t obt.
  destruct obt.
  - econstructor.
  - econstructor. right. apply CIH.
  - inversion e.
Qed.

Lemma no_event_l_empty {E X} : forall (t: itree (void1 +' E) X), no_event_l t.
Proof using.
  pcofix CIH.
  intros t.
  pstep.
  red.
  genobs t obt.
  destruct obt; auto.
  destruct e; auto.
  inversion v.
Qed.

Lemma no_event_r_empty {E X} : forall (t: itree (E +' void1) X), no_event_r t.
Proof using.
  pcofix CIH.
  intros t.
  pstep.
  red.
  genobs t obt.
  destruct obt; auto.
  destruct e; auto.
  inversion v.
Qed.

(** * Signature elimination
  In order to eliminate a signature from the type,
  we need to handle it into an itree over the remaining signature.
  Since the intent is to run these handlers over trees that do not
  contain such events, how we handle them should not matter, but
  the obvious solution is to interpret them into [spin]
 *)

Definition helim_l {E F}: E +' F ~> itree F :=
  fun _ e => match e with
          | inl1 _ => ITree.spin
          | inr1 e => trigger e
          end.

Definition helim_r {E F}: E +' F ~> itree E :=
  fun _ e => match e with
          | inr1 _ => ITree.spin
          | inl1 e => trigger e
          end.

Definition helim {E}: E ~> itree void1 :=
  fun _ _ => ITree.spin.

Definition elim_l {E F}: itree (E +' F) ~> itree F     := interp helim_l.
Definition elim_r {E F}: itree (E +' F) ~> itree E     := interp helim_r.
Definition elim   {E}  : itree E        ~> itree void1 := interp helim.

(** * Soundness
    The tricky part is now to figure out how to express the correctness of
    the elimination of vacuous signatures.
 *)

(** By asserting that handlers can't be distinguished: *)

Lemma no_event_elim_l :
  forall {E F X} (t : itree (E +' F) X),
    no_event_l t ->
    forall (h : E ~> itree F) , elim_l t  ≈ interp (case_ h (id_ F)) t.
Proof using.
  intros E F X.
  unfold elim_l.
  intros t H h.
  revert t H.
  einit.
  ecofix CIH.
  intros.
  rewrite (itree_eta t).
  pinversion H0.
  - rewrite interp_ret. rewrite interp_ret. reflexivity.
  - rewrite interp_tau. rewrite interp_tau. estep.
  - rewrite interp_vis. rewrite interp_vis. cbn.
    unfold id_. unfold Id_Handler, Handler.id_.
    ebind. econstructor. reflexivity.
    intros. subst. estep.
    ebase. right. eapply CIHL. apply H1.
Qed.

Lemma no_event_elim_r :
  forall {E F X} (t : itree (E +' F) X),
    no_event_r t ->
    forall (h : F ~> itree E), elim_r t ≈ interp (case_ (id_ E) h) t.
Proof using.
  intros E F X.
  unfold elim_r.
  intros t H h.
  revert t H.
  einit.
  ecofix CIH.
  intros.
  rewrite (itree_eta t).
  pinversion H0.
  - rewrite interp_ret. rewrite interp_ret. reflexivity.
  - rewrite interp_tau. rewrite interp_tau. estep.
  - rewrite interp_vis. rewrite interp_vis. cbn.
    unfold id_. unfold Id_Handler, Handler.id_.
    ebind. econstructor. reflexivity.
    intros. subst. estep.
    ebase. right. eapply CIHL. apply H1.
Qed.

Lemma no_event_elim :
  forall {E X} (t : itree E X),
    no_event t ->
    forall h, elim t ≈ interp h t.
Proof using.
  intros E X.
  unfold elim.
  intros t H h.
  revert t H.
  einit.
  ecofix CIH.
  intros.
  rewrite (itree_eta t).
  pinversion H0.
  - rewrite interp_ret. rewrite interp_ret. reflexivity.
  - rewrite interp_tau. rewrite interp_tau. estep.
Qed.

Lemma no_event_l_interp :
  forall {E F X} (t : itree (E +' F) X),
    no_event_l t ->
    forall (h : E ~> itree (E +' F)) ,
      t ≈ interp (case_ h inr_) t.
Proof using.
  intros E F X.
  intros t H h.
  revert t H.
  einit.
  ecofix CIH.
  intros.
  rewrite (itree_eta t).
  pinversion H0.
  - rewrite interp_ret. reflexivity.
  - rewrite interp_tau. estep.
  - clear - CIHH H0 H1 H.
    rewrite interp_vis. cbn.
    unfold inr_, Inr_sum1_Handler, Handler.inr_, Handler.htrigger.
    rewrite bind_trigger.
    estep; intros.
    rewrite tau_eutt.
    ebase. right. eapply CIHH. apply H1.
Qed.

Lemma no_event_r_interp :
  forall {E F X} (t : itree (E +' F) X),
    no_event_r t ->
    forall (h : F ~> itree (E +' F)), t ≈ interp (case_ inl_ h) t.
Proof using.
  intros E F X.
  intros t H h.
  revert t H.
  einit.
  ecofix CIH.
  intros.
  rewrite (itree_eta t).
  pinversion H0.
  - rewrite interp_ret. reflexivity.
  - rewrite interp_tau. estep.
  - clear - CIHH H0 H1 H.
    rewrite interp_vis. cbn.
    unfold inl_, Inl_sum1_Handler, Handler.inl_, Handler.htrigger.
    rewrite bind_trigger.
    estep; intros.
    rewrite tau_eutt.
    ebase. right. eapply CIHH. apply H1.
Qed.

Lemma no_event_interp :
  forall {E X} (t : itree E X),
    no_event t ->
    forall h, t ≈ interp h t.
Proof using.
  intros E X.
  intros t H h.
  revert t H.
  einit.
  ecofix CIH.
  intros.
  rewrite (itree_eta t).
  pinversion H0.
  - rewrite interp_ret. reflexivity.
  - rewrite interp_tau. estep.
Qed.

(** By expressing that [elim] is an inverse to the signature injection: *)

(* Injection to the left *)
Definition inject_l {E F}: itree F ~> itree (E +' F) :=
  translate inr_.

(* Injection to the right *)
Definition inject_r {E F}: itree E ~> itree (E +' F) :=
  translate inl_.

(* Injection *)
Definition inject {E}: itree void1 ~> itree E :=
  translate (fun _ (e : void1 _) => match e with end).

(* For some reason the new definition of [ecofix] in itrees loops here.
  We redefine the old one for now.
*)
Require Import Paco.pacotac_internal.

Tactic Notation "ecofix" ident(CIH) "with" ident(gL) ident(gH) :=
   repeat red;
   paco_pre2;
   eapply euttG_cofix;
   paco_post2 CIH with gL;
   paco_post2 CIH with gH.

Tactic Notation "ecofix" ident(CIH) := ecofix CIH with gL gH.

Lemma inject_no_event_l : forall {E F X} t,
  no_event_l (@inject_l E F X t).
Proof using.
  intros E F X.
  ginit; gcofix CIH; intros t.
  setoid_rewrite unfold_translate.
  gstep.
  destruct (observe t); cbn; constructor.
  - gbase; apply CIH.
  - intros ?; gbase; apply CIH.
Qed.

Lemma inject_no_event_r : forall {E F X} t,
  no_event_r (@inject_r E F X t).
Proof using.
  intros E F X.
  ginit; gcofix CIH; intros t.
  setoid_rewrite unfold_translate.
  gstep.
  destruct (observe t); cbn; constructor.
  - gbase; apply CIH.
  - intros ?; gbase; apply CIH.
Qed.

Lemma inject_no_event : forall {E X} t,
  no_event (@inject E X t).
Proof using.
  intros E X.
  ginit; gcofix CIH; intros t.
  unfold inject; setoid_rewrite unfold_translate.
  gstep.
  destruct (observe t); cbn; try constructor.
  - gbase; apply CIH.
  - inversion e.
Qed.

(* [elim_l] is _always_ a left inverse to [inject_l] *)
Lemma elim_inject_l :
  forall {E F X} (t : itree F X),
    elim_l (@inject_l E F _ t) ≈ t.
Proof using.
  einit.
  ecofix CIH.
  intros.
  rewrite (itree_eta t).
  unfold elim_l. unfold inject_l.
  destruct (observe t).
  - rewrite translate_ret. rewrite interp_ret.
    estep.
  - rewrite translate_tau. rewrite interp_tau.
    estep.
  - rewrite translate_vis. rewrite interp_vis. cbn.
    rewrite bind_trigger. estep.
    intros.
    rewrite tau_eutt. ebase.
Qed.

(* [inject_l] is a left inverse to [elim_l] when considering trees with [no_event_l] *)
Lemma inject_elim_l :
  forall {E F X} (t : itree (E +' F) X),
    no_event_l t ->
    inject_l (elim_l t) ≈ t.
Proof using.
  einit.
  ecofix CIH.
  intros.
  rewrite (itree_eta t).
  unfold elim_l in *.
  unfold inject_l in *.
  pinversion H0.
  - rewrite interp_ret. rewrite translate_ret. estep.
  - rewrite interp_tau. rewrite translate_tau. estep.
  - rewrite interp_vis. rewrite translate_bind.  cbn.
    unfold trigger.  rewrite translate_vis. rewrite bind_vis.
    estep. intros. rewrite translate_ret. rewrite bind_ret_l.
    rewrite translate_tau. rewrite tau_eutt. ebase.
    left. apply CIH0. apply H1.
Qed.

(* [elim_r] is _always_ a left inverse to [inject_r] *)
Lemma elim_inject_r :
  forall {E F X} (t : itree E X),
    elim_r (@inject_r E F _ t) ≈ t.
Proof using.
  einit.
  ecofix CIH.
  intros.
  rewrite (itree_eta t).
  unfold elim_r. unfold inject_r.
  destruct (observe t).
  - rewrite translate_ret. rewrite interp_ret. estep.
  - rewrite translate_tau. rewrite interp_tau. estep.
  - rewrite translate_vis. rewrite interp_vis. cbn.
    rewrite bind_trigger. estep.
    intros.
    rewrite tau_eutt. ebase.
Qed.

(* [inject_r] is a left inverse to [elim_r] when considering trees with [no_event_r] *)
Lemma inject_elim_r :
  forall {E F X} (t : itree (E +' F) X),
    no_event_r t ->
    inject_r (elim_r t) ≈ t.
Proof using.
  einit.
  ecofix CIH.
  intros.
  rewrite (itree_eta t).
  unfold elim_r in *.
  unfold inject_r in *.
  pinversion H0.
  - rewrite interp_ret. rewrite translate_ret. estep.
  - rewrite interp_tau. rewrite translate_tau. estep.
  - rewrite interp_vis. rewrite translate_bind.  cbn.
    unfold trigger.  rewrite translate_vis. rewrite bind_vis.
    estep. intros. rewrite translate_ret. rewrite bind_ret_l.
    rewrite translate_tau. rewrite tau_eutt. ebase.
    left. apply CIH0. apply H1.
Qed.


(* [elim] is _always_ a left inverse to [inject] *)
Lemma elim_inject :
  forall {E X} (t : itree void1 X),
    elim (@inject E _ t) ≈ t.
Proof using.
  einit.
  ecofix CIH.
  intros.
  rewrite (itree_eta t).
  unfold elim. unfold inject.
  destruct (observe t).
  - rewrite translate_ret. rewrite interp_ret. estep.
  - rewrite translate_tau. rewrite interp_tau. estep.
  - inversion e.
Qed.


(* [inject] is a left inverse to [elim] when considering trees with [no_event] *)
Lemma inject_elim :
  forall {E X} (t : itree E X),
    no_event t ->
    inject (elim t) ≈ t.
Proof using.
  einit.
  ecofix CIH.
  intros.
  rewrite (itree_eta t).
  unfold elim. unfold inject.
  pinversion H0.
  - rewrite interp_ret. rewrite translate_ret. estep.
  - rewrite interp_tau. rewrite translate_tau. estep.
Qed.

(** * Establishing [no_event]
    If two tree are similar after non-trivial injections, they have no events.
    The following probably needs to be refined.
 *)

(*  ------------------------------------------------------------------------- *)
(* TODO: Move these to the itrees library? *)

Lemma translate_ret_inv : forall E F A (h : E ~> F) (t : itree E A) a,
    translate h t ≅ ret a -> t ≅ ret a.
Proof using.
  intros.
  rewrite (itree_eta t) in *.
  pinversion H.
  destruct (observe t); cbn in *; inversion H1. subst. reflexivity.
  inversion CHECK.
Qed.

Lemma translate_tau_inv : forall E F A (h : E ~> F) (t : itree E A) u,
    translate h t ≅ Tau u -> exists u', t ≅ Tau u'.
Proof using.
  intros.
  setoid_rewrite (itree_eta t).
  rewrite (itree_eta t) in H.
  pinversion H; try inversion CHECK.
  destruct (observe t); cbn in *; inversion H1. subst. exists t0. reflexivity.
Qed.

Lemma translate_tau_vis : forall E F A B (h : E ~> F) (t : itree E B) f k,
    translate h t ≅ Vis f k -> exists e k', f = @h A e /\ t ≅ Vis e k'.
Proof using.
  intros.
  setoid_rewrite (itree_eta t).
  rewrite (itree_eta t) in H.
  pinversion H; try inversion CHECK.
  apply inj_pair2 in H3.
  apply inj_pair2 in H4.
  subst. destruct (observe t). cbn in *. inversion H1. inversion H1. cbn in *.
  inversion H. cbn in *.
  apply inj_pair2 in H3.
  apply inj_pair2 in H4.
  subst.
  apply inj_pair2 in H7.
  apply inj_pair2 in H6. subst.
  exists e0.
  exists k2. split; reflexivity.
Qed.
(*  ------------------------------------------------------------------------- *)


Lemma eutt_disjoint_no_event_l :
  forall {E F X Y} (R : X -> Y -> Prop) (t : itree E X) (s : itree F Y),
    eutt R (inject_r t) (@inject_l E F _ s) ->
    no_event t.
Proof using.
  intros E F X Y R.
  pcofix CIH.
  intros t s H0.
  rewrite (itree_eta t) in H0.
  rewrite (itree_eta s) in H0.
  repeat red in H0.
  punfold H0.
  red in H0.
  unfold inject_r, inject_l in H0.
  pstep. red.
  genobs t obt.
  genobs s obs.
  match goal with
  | [_ : eqitF _ _ _ _ _ ?X ?Y |- _] => remember X; remember Y
  end.
  revert t s obt Heqobt obs Heqobs Heqi Heqi0.
  induction H0; intros.
  - destruct obt; cbn in *; inversion Heqi. constructor.
  - destruct obt; cbn in *; inversion Heqi. constructor. destruct obs; cbn in *; inversion Heqi0. subst.
    right. eapply CIH. unfold inject_r. unfold inject_l. pclearbot. apply REL.
  - destruct obt; cbn in *; inversion Heqi. destruct obs; cbn in *; inversion Heqi0. subst.
    apply inj_pair2 in H4.
    apply inj_pair2 in H1. rewrite H4 in H1. inversion H1.
  - destruct obt; cbn in *; inversion Heqi. constructor. right. eapply CIH. unfold inject_r. rewrite <- H1.
    pstep. red. unfold inject_l. rewrite Heqi0 in H0. apply H0.
  - destruct obs; cbn in *; inversion Heqi0.
    eapply IHeqitF. apply Heqobt. 2 : { apply Heqi. } assert (observe t0 = observe t0) by reflexivity. apply H.
    rewrite H1. reflexivity.
Qed.


Lemma eutt_disjoint_no_event_r :
  forall {E F X Y} (R : X -> Y -> Prop) (t : itree E X) (s : itree F Y),
    eutt R (inject_r t) (@inject_l E F _ s) ->
    no_event s.
Proof using.
  intros E F X Y R.
  pcofix CIH.
  intros t s H0.
  rewrite (itree_eta t) in H0.
  rewrite (itree_eta s) in H0.
  repeat red in H0.
  punfold H0.
  red in H0.
  unfold inject_r, inject_l in H0.
  pstep. red.
  genobs t obt.
  genobs s obs.
  match goal with
  | [_ : eqitF _ _ _ _ _ ?X ?Y |- _] => remember X; remember Y
  end.
  revert t s obt Heqobt obs Heqobs Heqi Heqi0.
  induction H0; intros.
  - destruct obs; cbn in *; inversion Heqi0. constructor.
  - destruct obs; cbn in *; inversion Heqi0. constructor. destruct obt; cbn in *; inversion Heqi. subst.
    right. eapply CIH. unfold inject_r. unfold inject_l. pclearbot. apply REL.
  - destruct obs; cbn in *; inversion Heqi0. destruct obt; cbn in *; inversion Heqi. subst.
    apply inj_pair2 in H4.
    apply inj_pair2 in H1. rewrite H4 in H1. inversion H1.
  - destruct obt; cbn in *; inversion Heqi.
    eapply IHeqitF. assert (observe t0 = observe t0) by reflexivity. apply H. apply Heqobs.
    rewrite H1. reflexivity. assumption.
  - destruct obs; cbn in *; inversion Heqi0. constructor. right. eapply CIH. unfold inject_l. rewrite <- H1.
    pstep. red. unfold inject_r. rewrite Heqi in H0. apply H0.
Qed.

#[global] Instance Proper_inject_l {E F X} : Proper (eq_itree eq ==> eq_itree eq) (@inject_l E F X).
Proof using.
  do 3 red.
  intros x y EQ.
  rewrite EQ. reflexivity.
Qed.

Lemma no_event_translate :
  forall {E F X} (m : E ~> F) (t : itree E X), no_event t -> no_event (translate m t).
Proof using.
  ginit.
  intros E F X m t H.
  rewrite (itree_eta t).
  revert t H.
  gcofix CIH.
  intros * NEV.
  rewrite itree_eta in NEV.
  red in NEV.
  punfold NEV.
  inversion NEV.
  - rewrite translate_ret.
    gstep.
    constructor.
  - pclearbot.
    rewrite translate_tau.
    gstep.
    constructor.
    rewrite (itree_eta t0).
    gbase.
    eauto.
Qed.

(* And while we're at it, injection should not compromise [no_event] *)
Lemma no_event_inject_l :
  forall {E F X} (t : itree F X), no_event t -> no_event (@inject_l E F _ t).
Proof using.
  ginit.
  intros * H.
  rewrite (itree_eta t).
  revert t H.
  gcofix CIH.
  intros * NEV.
  rewrite itree_eta in NEV.
  red in NEV.
  punfold NEV.
  inversion NEV.
  - unfold inject_l; rewrite translate_ret.
    gstep.
    constructor.
  - pclearbot.
    unfold inject_l; rewrite translate_tau.
    gstep.
    constructor.
    rewrite (itree_eta t0).
    gbase.
    eauto.
Qed.

Lemma no_event_inject_r :
  forall {E F X} (t : itree E X),
    no_event t ->
    no_event (@inject_r E F _ t).
  ginit.
  intros * H.
  rewrite (itree_eta t).
  revert t H.
  gcofix CIH.
  intros * NEV.
  rewrite itree_eta in NEV.
  red in NEV.
  punfold NEV.
  inversion NEV.
  - unfold inject_r; rewrite translate_ret.
    gstep.
    constructor.
  - pclearbot.
    unfold inject_r; rewrite translate_tau.
    gstep.
    constructor.
    rewrite (itree_eta t0).
    gbase.
    eauto.
Qed.

(** * Other discussions  *)

(* YZ TODO: This file should not depend on VIR, this section should be eventually moved 
   somewhere in [Theory/]
*)
(* We want to express that a tree contains no [pickE] events,
   and that if so that entails that the interpretation by the pick handlers
   leads to the singleton predicate containing the elimination of the pick event.
   Something like:
   no_pick t ->
   forall t', model_pick t t' -> t' ≈ elim_pick t
 *)

From Vellvm Require Import
     Utils.Tactics
     Utils.Util
     Utils.PropT
     Utils.PostConditions
     Utils.NoFailure
     Syntax.Traversal
     Syntax.LLVMAst
     Syntax.AstLib
     Syntax.CFG
     Syntax.DynamicTypes
     Syntax.TypToDtyp
     Semantics.LLVMEvents
     Semantics.Denotation
     Semantics.InterpretationStack
     Semantics.TopLevel
     Handlers.Handlers
     Theory.InterpreterCFG
     Theory.InterpreterMCFG
     Theory.TopLevelRefinements
     Theory.DenotationTheory
     Theory.InstrLemmas.



Import MonadNotation.
Open Scope monad_scope.

Definition trigger_prop {E F} : F ~> PropT (E +' F) :=
  fun R e => fun t => t = r <- trigger e ;; ret r.

Definition trigger_prop' {F} : F ~> PropT F :=
  fun R e => fun t => t = r <- trigger e ;; ret r.

Definition is_singleton {E X} (ts : PropT E X) (t : itree E X) : Prop :=
  forall u, ts u -> u ≈ t.

(*
  Initially : E is UB (non det stuff)
              F is other effects.
we have E +' F
E gets interepreted into a non-deterministic computation : PropT ??
F gets "preserved" 
 *)

(* Lemma deterministic_is_singleton :  *)
(*   forall {E F X} (RX : relation X) *)
(*     (t : itree (E +' F) X) *)
(*     (h : E ~> PropT F), *)
(*     no_event_l t ->  *)
(*     is_singleton *)
(*       (interp_prop (case_ h trigger_prop') X RX t) *)
(*       (elim_l t). *)
(* Proof using. *)

(* Admitted. *)

(* t --pick> {t} --UB> {t} *)

(* Definition interp_from_prop {E F} T (RR: T -> T -> Prop) (h : E ~> PropT F) : PropT (E +' F) T -> PropT F T := *)
(*   fun Pt (t : itree F T) => *)
(*     exists (t' : itree (E +' F) T) , *)
(*       Pt t' /\ *)
(*       (interp_prop (case_ h trigger_prop') _ RR t' t). *)

Section DeterministicSingleton.

  (* Lemma deterministic_is_singleton' :  *)
  (*   forall {E F X} (RX : relation X) *)
  (*     (ts : PropT (E +' F) X) *)
  (*     (t : itree (E +' F) X) *)
  (*     (h : E ~> PropT F), *)
  (*     is_singleton ts t -> *)
  (*     no_event_l t ->  *)
  (*     is_singleton (interp_from_prop RX h ts) (elim_l t). *)
  (* Proof using. *)
  (* Admitted. *)

    (*
  (* Definition deterministic_vellvm *)
  Lemma deterministc_llvm_is_singleton : forall R RR t g sl mem,
      deterministic_vellvm t -> 
      is_singleton (interp_mcfg5 (R := R) RR t g sl mem) (remove_pick_ub (interp_mcfg3 (R := R) t g sl mem)).

  (*
    Then the same statement on llvm syntax by applying it with (t := denote_llvm p)
    Then on the helix side:
    - we know that there is (t: itree void1 X),
    "inject (ExternalCallE +' PickE +' UBE +' DebugE +' FailureE) t ≈ interp_mcfg3 (denote_llvm p)"
   *)
  Proof using. Admitted.
*)
End DeterministicSingleton.

Require Import Mem.MemoryAddress.
Require Import LLVM_Memory.Sizeof.

Module PICK_REMOVE (ADDR : ADDRESS) (IP : INTPTR) (SIZE : Sizeof) (Events : LLVM_INTERACTIONS ADDR IP SIZE).
  Import Events.

  Variable remove_pick_ub : itree (ExternalCallE +' PickUvalueE +' UBE +' DebugE +' FailureE) ~> itree (ExternalCallE +' DebugE +' FailureE).
  Variable deterministic_vellvm : forall R, itree L0 R -> Prop.
End PICK_REMOVE.
