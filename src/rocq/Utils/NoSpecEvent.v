(* begin hide *)
From Stdlib Require Import
     RelationClasses
     Morphisms
     Program.Equality.

From Paco Require Import paco.
From ITree Require Import
     ITree
     ITreeFacts
     Eq.Eqit.

From ITreeSpec Require Import
  ITreeSpecDefinition
  ITreeSpecFacts
  ITreeSpecCombinatorFacts.

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
Variant no_spec_event_F {E X} (R: itree (SpecEvent E) X -> Prop) : itree' (SpecEvent E) X -> Prop :=
| no_spec_event_ret: forall (x: X), no_spec_event_F R (RetF x)
| no_spec_event_tau: forall t, R t -> no_spec_event_F R (TauF t)
| no_spec_event_vis: forall {Y} (e: E Y) k, (forall x, R (k x)) -> no_spec_event_F R (VisF (Spec_vis e) k).
#[export] Hint Constructors no_spec_event_F : core.

Lemma no_spec_event_F_mono : forall {E X} (R1 R2 : itree (SpecEvent E) X -> Prop) (LE : R1 <1= R2),
    no_spec_event_F R1 <1= no_spec_event_F R2.
Proof using.
  intros.
  induction PR; auto.
Qed.

Definition no_spec_event_F_ {E X} R (t : itree (SpecEvent E) X) := no_spec_event_F R (observe t).
#[export] Hint Unfold no_spec_event_F_ : core.

Lemma no_event_lF__mono : forall E X, (monotone1 (@no_spec_event_F_ E X)).
Proof using.
  do 2 red.
  intros.
  eapply no_spec_event_F_mono; eauto.
Qed.

#[export] Hint Resolve no_spec_event_F_mono : paco.

Definition no_spec_event {E X} := paco1 (@no_spec_event_F_ E X) bot1.

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

(** up-to eq_itree closure
  Coinductive proofs about no_spec_event can be performed up-to `eq_itree`.

  Note that up-to eutt is not valid:
    Tau (Vis e k)
        |  no_spec_eventF
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

  Lemma no_spec_event_eqit_clo_wcompat {E R} :
    wcompatible1 (@no_spec_event_F_ E R) eqit_clo.
  Proof using.
    econstructor.
    pmonauto.
    intros.
    inversion PR.
    punfold EQVl.
    unfold_eqit.
    unfold no_spec_event_F_ in *.
    induction EQVl; auto.
    - inversion REL.
      constructor.
      pclearbot.
      gclo; econstructor; cycle -1; eauto with paco.
    - subst. destruct e.
      + constructor.
        dependent induction REL.
        pclearbot; intros; gclo; econstructor; cycle -1; eauto with paco.
        apply REL0.
      + inversion REL.
      + inversion REL.
    - constructor.
      gstep; auto.
    - congruence.
  Qed.

  #[global] Instance eq_itree_no_spec_event_l_cong {E R} r rg :
    Proper ((eq_itree eq) ==> flip impl) (gpaco1 (@no_spec_event_F_ E R) eqit_clo r rg).
  Proof using.
    repeat intro.
    gclo.
    econstructor; cycle -1; eauto.
  Qed.

  #[global] Instance euttge_no_spec_event_l_cong {E R} r rg :
    Proper ((euttge eq) ==> flip impl) (gpaco1 (@no_spec_event_F_ E R) eqit_clo r rg).
  Proof using.
    repeat intro.
    gclo.
    econstructor; cycle -1; eauto.
  Qed.

End eqit_closure.
#[export] Hint Resolve eqit_clo_mon : paco.
#[export] Hint Constructors eqit_clo: core.
#[export] Hint Resolve no_spec_event_eqit_clo_wcompat : paco.

(* In particular [eq_itree] is hence a congruence for [no_spec_event] *)
#[global] Instance no_spec_event_eq_itree {E X} : Proper (eq_itree eq ==> iff) (@no_spec_event E X).
Proof using.
  repeat red. intros. split; intros.
  ginit. rewrite <- H. gfinal; auto.
  ginit. rewrite H. gfinal; auto.
Qed.

(* But although not a valid up-to, [eutt] is also a congruence for [no_spec_event] *)
#[global] Instance no_spec_event_eutt {E X} : Proper (eutt eq ==> iff) (@no_spec_event E X).
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
      * rewrite <- Heqoy. destruct e.
        --  inversion H1. econstructor. intros.
            specialize (REL x0). red in REL. pclearbot. right. eapply CIH. apply REL.
            apply inj_pair2 in H3. rewrite <- H3. specialize (H0 x0). apply H0.
        --  inversion H1.
        --  inversion H1.
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
        -- specialize (REL x0). red in REL. pclearbot. right. eapply CIH. apply REL.
           apply inj_pair2 in H3. rewrite <- H3. specialize (H0 x0). apply H0.
        -- inv H1.
        -- inv H1.
      * rewrite <- Heqox. econstructor. left.
        pstep. red. eapply IHeqitF. econstructor. reflexivity. apply Heqoy.
      * rewrite <- Heqox. econstructor. left.
        pstep. red. eapply IHeqitF. econstructor. assumption. reflexivity. apply Heqoy.
      * rewrite <- Heqox. econstructor. left.
        pstep. red. eapply IHeqitF. econstructor. intros. apply H. reflexivity. apply Heqoy.
      * eapply IHeqitF. pclearbot. punfold H2. reflexivity. reflexivity.
Qed.

Lemma no_spec_event_to_itree_spec {E X} : forall (t: itree (SpecEvent E) X), no_spec_event (to_itree_spec t).
Proof using.
  intros t.
  setoid_rewrite (itree_eta t).
  genobs t ot. clear t Heqot.
  revert ot.
  pcofix CIH.
  intros ot.
  destruct ot; auto.
  - pstep; red; cbn.
    constructor.
  - pstep; red; cbn.
    constructor.
    right.
    unfold to_itree_spec in *.
    rewrite (EqAxiom.itree_eta_ t).
    apply CIH.
  - pstep; red; cbn.
    constructor.
    intros x.
    right.
    rewrite (EqAxiom.itree_eta_ (k x)).
    apply CIH.
Qed.

(** * Signature elimination
  In order to eliminate a signature from the type,
  we need to handle it into an itree over the remaining signature.
  Since the intent is to run these handlers over trees that do not
  contain such events, how we handle them should not matter, but
  the obvious solution is to interpret them into [spin]
 *)

Definition helim_spec {E}: SpecEvent E ~> itree E :=
  fun _ e => match e with
          | Spec_vis e => trigger e
          | Spec_forall _
          | Spec_exists _ => ITree.spin
          end.

Definition elim_spec {E}: itree (SpecEvent E) ~> itree E := interp helim_spec.

(** * Soundness
    The tricky part is now to figure out how to express the correctness of
    the elimination of vacuous signatures.
 *)

(** By asserting that handlers can't be distinguished: *)

(* Lemma no_spec_event_elim : *)
(*   forall {E X} (t : itree (SpecEvent E) X), *)
(*     no_spec_event t -> *)
(*     forall (h : E ~> itree E) , elim_spec t  ≈ interp (to_itree_spec_handler h) t. *)
(* Proof using. *)
(*   intros E F X. *)
(*   unfold elim_l. *)
(*   intros t H h. *)
(*   revert t H. *)
(*   einit. *)
(*   ecofix CIH. *)
(*   intros. *)
(*   rewrite (itree_eta t). *)
(*   pinversion H0. *)
(*   - rewrite interp_ret. rewrite interp_ret. reflexivity. *)
(*   - rewrite interp_tau. rewrite interp_tau. estep. *)
(*   - rewrite interp_vis. rewrite interp_vis. cbn. *)
(*     unfold id_. unfold Id_Handler, Handler.id_. *)
(*     ebind. econstructor. reflexivity. *)
(*     intros. subst. estep. *)
(*     ebase. right. eapply CIHL. apply H1. *)
(* Qed. *)

Lemma no_spec_event_interp :
  forall {E X} (t : itree (SpecEvent E) X),
    no_spec_event t ->
    forall (h : E ~> itree E) ,
      t ≈ interp (to_itree_spec_handler h) t.
Proof using.
  intros E X.
  einit.
  ecofix CIH.
  intros t H h.
  rewrite (itree_eta t).
  rewrite (itree_eta t) in H.
  genobs t ot.
  clear t Heqot.
  pinversion H; cbn in *; subst.
  - setoid_rewrite interp_ret. reflexivity.
  - setoid_rewrite interp_tau. estep.
  - setoid_rewrite interp_vis. cbn.
    unfold to_itree_spec.
    red in H.
    cbn in *.
Admitted.

(** By expressing that [elim] is an inverse to the signature injection: *)

(* Injection to the left *)
Definition inject_spec {E}: itree E ~> itree (SpecEvent E) :=
  translate (@to_SpecEvent _).

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

Lemma inject_no_spec_event : forall {E X} t,
  no_spec_event (@inject_spec E X t).
Proof using.
  intros E X.
  ginit; gcofix CIH; intros t.
  setoid_rewrite unfold_translate.
  gstep.
  destruct (observe t); cbn; constructor.
  - gbase; apply CIH.
  - intros ?; gbase; apply CIH.
Qed.

(* [elim_l] is _always_ a left inverse to [inject_l] *)
Lemma elim_inject_spec :
  forall {E X} (t : itree E X),
    elim_spec (@inject_spec E _ t) ≈ t.
Proof using.
  einit.
  ecofix CIH.
  intros.
  rewrite (itree_eta t).
  unfold elim_spec. unfold inject_spec.
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

(* [inject_l] is a left inverse to [elim_l] when considering trees with [no_spec_event_l] *)
Lemma inject_elim_spec :
  forall {E X} (t : itree (SpecEvent E) X),
    no_spec_event t ->
    inject_spec (elim_spec t) ≈ t.
Proof using.
  einit.
  ecofix CIH.
  intros.
  rewrite (itree_eta t).
  unfold elim_spec in *.
  unfold inject_spec in *.
  pinversion H0.
  - rewrite interp_ret. rewrite translate_ret. estep.
  - rewrite interp_tau. rewrite translate_tau. estep.
  - rewrite interp_vis. rewrite translate_bind.  cbn.
    unfold trigger.  rewrite translate_vis. rewrite bind_vis.
    estep. intros. rewrite translate_ret. rewrite bind_ret_l.
    rewrite translate_tau. rewrite tau_eutt. ebase.
    left. apply CIH0. apply H1.
Qed.

(** * Establishing [no_spec_event]
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

#[global] Instance Proper_inject_spec {E X} : Proper (eq_itree eq ==> eq_itree eq) (@inject_spec E X).
Proof using.
  do 3 red.
  intros x y EQ.
  rewrite EQ. reflexivity.
Qed.

(* TODO: Probably need to move this *)
Definition to_spec_handler {E F} (h : E ~> F) : SpecEvent E ~> SpecEvent F.
  intros T X.
  destruct X.
  - apply Spec_vis.
    apply h; auto.
  - apply Spec_forall.
  - apply Spec_exists.
Defined.

Lemma no_spec_event_translate :
  forall {E F X} (m : E ~> F) (t : itree (SpecEvent E) X), no_spec_event t -> no_spec_event (translate (to_spec_handler m) t).
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
  - pclearbot.
    rewrite translate_vis.
    gstep.
    red. cbn.
    constructor.
    intros x.
    rewrite (itree_eta (k x)).
    gbase.
    eapply CIH.
    apply H0.
Qed.

(* And while we're at it, injection should not compromise [no_spec_event] *)
Lemma no_spec_event_inject :
  forall {E X} (t : itree E X), no_spec_event (@inject_spec E _ t).
Proof using.
  ginit.
  intros *.
  rewrite (itree_eta t).
  genobs t ot.
  clear t Heqot.
  revert ot.
  unfold inject_spec.
  gcofix CIH.
  intros ot.
  hinduction ot before E; intros * CIH.
  - rewrite translate_ret.
    gstep.
    constructor.
  - rewrite translate_tau.
    rewrite (itree_eta t).
    gstep.
    constructor.
    gbase.
    eauto.
  - rewrite translate_vis.
    gstep; red; cbn; constructor.
    intros x.
    rewrite (itree_eta (k x)).
    gbase.
    apply CIH.
Qed.
