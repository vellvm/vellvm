(* begin hide *)
From Coq Require Import
     RelationClasses
     Morphisms.

From Paco Require Import paco.
From ITree Require Import
     ITree
     ITreeFacts
     Eq.Eq.
Set Implicit Arguments.
Set Strict Implicit.
(* end hide *)

(** * NoEvent
    We develop in this file a tiny theory to reason about absence of a given event signature
    in a tree, and how to use this absence to safely eliminate this signature from the tree.
 *)

(** * Signature vacuousness
  A simple way to assert the absence of a signature is based on the shape of the signature.
  We define straightforward non-recursive functors and take the cofixed points.
 *)

(* Note : Need to state/prove the monotony of the functors to reason about their paco *)

(* The left part of the signature is absent *)
Variant no_event_lF {E F X} (R: itree (E +' F) X -> Prop) : itree' (E +' F) X -> Prop :=
| no_event_l_ret: forall (x: X), no_event_lF R (RetF x)
| no_event_l_tau: forall t, R t -> no_event_lF R (TauF t)
| no_event_l_vis: forall {Y} (e: F Y) k, (forall x, R (k x)) -> no_event_lF R (VisF (inr1 e) k).
Hint Constructors no_event_lF : core.

Lemma no_event_lF_mono : forall {E F X} (R1 R2 : itree (E +' F) X -> Prop) (LE : R1 <1= R2),
    no_event_lF R1 <1= no_event_lF R2.
Proof.
  intros.
  induction PR; auto.
Qed.  

Definition no_event_lF_ {E F X} R (t : itree (E +' F) X) := no_event_lF R (observe t).
Hint Unfold no_event_lF_ : core.

Lemma no_event_lF__mono : forall E F X, (monotone1 (@no_event_lF_ E F X)).
Proof.
  do 2 red.
  intros.
  eapply no_event_lF_mono; eauto.
Qed.  

Hint Resolve no_event_lF_mono : paco.
  
Definition no_event_l {E F X} := paco1 (@no_event_lF_ E F X) bot1. 

Instance Proper_no_event_l {E F X} : Proper (eutt eq ==> iff) (@no_event_l E F X).
Proof.
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
  

(* The right part of the signature is absent *)
Variant no_event_rF {E F X} (R: itree (E +' F) X -> Prop): itree' (E +' F) X -> Prop :=
| no_event_r_ret: forall (x: X), no_event_rF R (RetF x)
| no_event_r_tau: forall t, R t -> no_event_rF R (TauF t)
| no_event_r_vis: forall {Y} (e: E Y) k, (forall x, R (k x)) -> no_event_rF R (VisF (inl1 e) k).

Hint Constructors no_event_rF : core.

Lemma no_event_rF_mono : forall {E F X} (R1 R2 : itree (E +' F) X -> Prop) (LE : R1 <1= R2),
    no_event_rF R1 <1= no_event_rF R2.
Proof.
  intros.
  induction PR; auto.
Qed.  

Definition no_event_rF_ {E F X} R (t : itree (E +' F) X) := no_event_rF R (observe t).
Hint Unfold no_event_rF_ : core.

Lemma no_event_rF__mono : forall E F X, (monotone1 (@no_event_rF_ E F X)).
Proof.
  do 2 red.
  intros.
  eapply no_event_rF_mono; eauto.
Qed.  

Hint Resolve no_event_rF_mono : paco.

Definition no_event_r {E F X} := paco1 (@no_event_rF_ E F X) bot1. 

Instance Proper_no_event_r {E F X} : Proper (eutt eq ==> iff) (@no_event_r E F X).
Proof.
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


(* The tree contains no event *)
Variant no_eventF {E X} (R: itree E X -> Prop): itree' E X -> Prop :=
| no_event_ret: forall (x: X), no_eventF R (RetF x)
| no_event_tau: forall t, R t -> no_eventF R (TauF t).

Hint Constructors no_eventF : core.

Lemma no_eventF_mono : forall {E X} (R1 R2 : itree E X -> Prop) (LE : R1 <1= R2),
    no_eventF R1 <1= no_eventF R2.
Proof.
  intros.
  induction PR; auto.
Qed.  

Definition no_eventF_ {E X} R (t : itree E X) := no_eventF R (observe t).
Hint Unfold no_eventF_ : core.

Lemma no_eventF__mono : forall E X, (monotone1 (@no_eventF_ E X)).
Proof.
  do 2 red.
  intros.
  eapply no_eventF_mono; eauto.
Qed.  

Hint Resolve no_eventF_mono : paco.

Definition no_event {E X} := paco1 (@no_eventF_ E X) bot1. 

Instance Proper_no_event {E X} : Proper (eutt eq ==> iff) (@no_event E X).
Proof.
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
Proof.
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
Proof.
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
    ebase. right. eapply CIH. apply H1.
Qed.

Lemma no_event_elim_r :
  forall {E F X} (t : itree (E +' F) X),
    no_event_r t ->
    forall (h : F ~> itree E), elim_r t ≈ interp (case_ (id_ E) h) t.
Proof.
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
    ebase. right. eapply CIH. apply H1.
Qed.

Lemma no_event_elim :
  forall {E X} (t : itree E X),
    no_event t ->
    forall h, elim t ≈ interp h t.
Proof.
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

(** By expressing that [elim] is an inverse to the signature injection: *)

(* Injection to the left *)
Definition inject_l {E F}: itree F ~> itree (E +' F) :=
  translate inr_.

(* [elim_l] is _always_ a left inverse to [inject_l] *)
Lemma elim_inject_l :
  forall {E F X} (t : itree F X),
    elim_l (@inject_l E F _ t) ≈ t.
Admitted.

(* [inject_l] is a left inverse to [elim_l] when considering trees with [no_event_l] *)
Lemma inject_elim_l :
  forall {E F X} (t : itree (E +' F) X),
    no_event_l t -> 
    inject_l (elim_l t) ≈ t.
Admitted.

(* Injection to the left *)
Definition inject_r {E F}: itree E ~> itree (E +' F) :=
  translate inl_.

(* [elim_r] is _always_ a left inverse to [inject_r] *)
Lemma elim_inject_r :
  forall {E F X} (t : itree E X),
    elim_r (@inject_r E F _ t) ≈ t.
Admitted.

(* [inject_r] is a left inverse to [elim_r] when considering trees with [no_event_r] *)
Lemma inject_elim_r :
  forall {E F X} (t : itree (E +' F) X),
    no_event_r t -> 
    inject_r (elim_r t) ≈ t.
Admitted.

(* Injection *)
Definition inject {E}: itree void1 ~> itree E :=
  translate (fun _ (e : void1 _) => match e with end).

(* [elim] is _always_ a left inverse to [inject] *)
Lemma elim_inject :
  forall {E X} (t : itree void1 X),
    elim (@inject E _ t) ≈ t.
Admitted.

(* [inject] is a left inverse to [elim] when considering trees with [no_event] *)
Lemma inject_elim :
  forall {E X} (t : itree E X),
    no_event t -> 
    inject (elim t) ≈ t.
Admitted.

(** * Establishing [no_event]
    If two tree are similar after non-trivial injections, they have no events.
    The following probably needs to be refined.
 *)

Lemma eutt_disjoint_no_event :
  forall {E F X Y} (R : X -> Y -> Prop) (t : itree E X) (s : itree F Y),
    eutt R (inject_r t) (@inject_l E F _ s) ->
    no_event t /\ no_event s.
Admitted.

(* And while we're at it, injection should not compromise [no_event] *)
Lemma no_event_inject_l :
  forall {E F X} (t : itree F X),
    no_event t ->
    no_event (@inject_l E F _ t).
Admitted.

Lemma no_event_inject_r :
  forall {E F X} (t : itree E X),
    no_event t ->
    no_event (@inject_r E F _ t).
Admitted.


(** * Other discussions  *)

(* We want to express that a tree contains no [pickE] events,
   and that if so that entails that the interpretation by the pick handlers
   leads to the singleton predicate containing the elimination of the pick event.
   Something like:
   no_pick t ->
   forall t', model_pick t t' -> t' ≈ elim_pick t
 *)
