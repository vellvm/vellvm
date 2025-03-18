From Stdlib Require Import
     Morphisms.

From Paco Require Import paco.

From ExtLib Require Import
  Structures.Monads
  Structures.Functor
  EitherMonad.

From ITree Require Import
     ITree
     Eq.Eqit
     InterpFacts.

From Vellvm Require Import
     Utils.Util
     Utils.Error.

Import ITree.Basics.Basics.Monads.

Set Implicit Arguments.
Set Contextual Implicit.

Import MonadNotation.
Open Scope monad.

Lemma eq1_unEitherT :
  forall
    V m R `{HM: Monad m} `{EQM: Monad.Eq1 m}
    (x y : eitherT V m R),
    Monad.eq1 x y <->
      Monad.eq1 (unEitherT x) (unEitherT y).
Proof.
  intros V m R HM EQM x y.
  split; intros EQ; auto.
Qed.

Definition interp_either {E M EXC}
  {FM : Functor M} {MM : Monad M}
  {IM : MonadIter M} (h : E ~> eitherT EXC M) :
  itree E ~> eitherT EXC M := interp h.

Definition _interp_either {E F V R}
  (f : E ~> eitherT V (itree F)) (ot : itreeF E R (itree E R))
  : eitherT V (itree F) R.
  refine (match ot with
    | RetF r => mkEitherT (ret (inr r))
    | TauF t => mkEitherT (Tau (unEitherT (interp_either f t)))
    | VisF _ e k => _
          end).
  - refine (f _ e >>= _).
    intros X.
    apply mkEitherT.
    refine (Tau _).
    apply (interp_either f (k X)).
Defined.


Lemma unfold_interp_either {E F V R} (h : E ~> eitherT V (itree F))
      (t : itree E R) :
    Monad.eq1
      (interp_either h t)
      (_interp_either h (observe t)).
Proof.
  unfold interp_either, interp, Basics.iter, MonadIter_eitherT, Basics.iter, MonadIter_itree; cbn.
  red; red; cbn.
  rewrite unfold_iter; cbn.
  destruct observe; cbn.
  - rewrite 2 bind_ret_l. reflexivity.
  - rewrite 2 bind_ret_l.
    reflexivity.
  - setoid_rewrite bind_map.
    setoid_rewrite bind_bind; cbn.
    apply eqit_bind; try reflexivity.
    repeat red.
    intros a.
    destruct a.
    rewrite bind_ret_l.
    apply Reflexive_eqit; eauto.
    rewrite bind_ret_l.
    apply Reflexive_eqit; eauto.
Qed.

Lemma unfold_interp_either' {E F V R} (h : E ~> eitherT V (itree F))
      (t : itree E R) :
    Monad.eq1
      (unEitherT (interp_either h t))
      (unEitherT (_interp_either h (observe t))).
Proof.
  apply unfold_interp_either.
Qed.

Lemma unfold_interp_either'' {E F V R} (h : E ~> eitherT V (itree F))
      (t : itree E R) :
      (unEitherT (interp_either h t)) ≅
      (unEitherT (_interp_either h (observe t))).
Proof.
  unfold interp_either, interp, Basics.iter, MonadIter_eitherT, Basics.iter, MonadIter_itree; cbn.
  red; red; cbn.
  rewrite unfold_iter; cbn.
  destruct observe; cbn.
  - rewrite 2 bind_ret_l.
    apply Reflexive_eqit_eq.
  - rewrite 2 bind_ret_l.
    apply Reflexive_eqit_eq.
  - setoid_rewrite bind_map.
    setoid_rewrite bind_bind; cbn.
    apply eqit_bind; try reflexivity.
    repeat red.
    intros a.
    destruct a.
    rewrite bind_ret_l.
    apply Reflexive_eqit; eauto.
    rewrite bind_ret_l.
    apply Reflexive_eqit; eauto.
Qed.

#[global] Opaque interp_either.

#[global]
Instance eq1_interp_either {E F V R} (h : E ~> eitherT V (itree F)) :
  Proper (Monad.eq1 ==> Monad.eq1)
    (@interp_either _ _ _ _ _ _ h R).
Proof.
  einit. ecofix CIH. intros.
  rewrite !unfold_interp_either''.
  punfold H0; red in H0.
  induction H0; intros; subst; simpl; pclearbot.
  - eret.
  - etau.    
  - ebind. econstructor; [reflexivity|].
    intros; subst.
    destruct u2.
    eret.
    etau. ebase.
    right.
    apply CIHL.
    apply REL.
  - rewrite tau_euttge. eauto.
    rewrite unfold_interp_either''. eauto.
  - rewrite tau_euttge. eauto.
    rewrite unfold_interp_either''. eauto.
Qed.

Definition eq_either_itree {F V R} (t1 t2 : eitherT V (itree F) R)
  := unEitherT t1 ≅ unEitherT t2.

#[global] Instance Reflexive_eq_either_itree {F V R} : Reflexive (@eq_either_itree F V R).
intros x.
red.
reflexivity.
Qed.

#[global] Instance Symmetric_eq_either_itree {F V R} : Symmetric (@eq_either_itree F V R).
intros x y EQ.
red; red in EQ.
symmetry.
apply EQ.
Qed.

#[global] Instance Transitive_eq_either_itree {F V R} : Transitive (@eq_either_itree F V R).
intros x y z XY YZ.
red; red in XY, YZ.
rewrite XY, YZ.
reflexivity.
Qed.

#[global] Instance Equivalence_eq_either_itree {F V R} : Equivalence (@eq_either_itree F V R).
split; try typeclasses eauto.
Qed.

#[global]
Instance eq_interp_either {E F V R} (h : E ~> eitherT V (itree F)) :
  Proper (eq_itree eq ==> eq_either_itree)
    (@interp_either _ _ _ _ _ _ h R).
Proof.
  ginit. gcofix CIH. intros.
  rewrite !unfold_interp_either''.
  punfold H0; red in H0.
  induction H0; intros; subst; simpl; pclearbot.
  - gstep; red; constructor; auto.
  - gstep; red; constructor; auto.
    gbase.
    apply CIH; eauto.
  - guclo eqit_clo_bind.
    eapply pbc_intro_h with (RU:=eq).
    reflexivity.

    intros u1 u2 H; subst.
    destruct u2.
    + gstep; red; cbn; constructor; auto.
    + gstep; red; cbn; constructor; auto.
      gbase.
      apply CIH.
      apply REL.
  - inversion CHECK.
  - inversion CHECK.
Qed.

#[global]
Instance eq_either_itree_eq1 {E V R} :
  Proper (@eq_either_itree E V R ==> @eq_either_itree E V R ==> iff) Monad.eq1.
Proof.
  repeat red.
  intros x y H x0 y0 H0.
  red in H, H0.
  split; intros;
    do 4 red;
    do 4 red in H1.
  - rewrite H, H0 in H1.
    auto.
  - rewrite <- H, <- H0 in H1.
    auto.
Qed.

Lemma interp_either_vis {E F : Type -> Type} {V T R : Type}
  (f : forall T, E T -> eitherT V (itree F) T)
  (e : E T)
  (k : T -> itree E R) :
  Monad.eq1 (interp_either f (Vis e k)) (f T e >>= fun x => interp_either f (k x)).
Proof.
  rewrite unfold_interp_either.
  cbn.
  do 4 red.
  cbn.
  eapply eutt_clo_bind.
  reflexivity.
  intros ? ? ?; subst.
  destruct u2; try reflexivity.
  rewrite tau_eutt.
  reflexivity.
Qed.

Lemma interp_either_tau {E F} {V R : Type}
  (f : forall T, E T -> eitherT V (itree F) T)
  (t : itree E R) :
  Monad.eq1 (interp_either f (Tau t)) (interp_either f t).
Proof.
  apply eq1_unEitherT; try typeclasses eauto.
  unfold Monad.eq1.
  red.
  rewrite unfold_interp_either'.
  cbn.
  rewrite tau_eutt.
  reflexivity.
Qed.

Lemma interp_either_tau' {E F} {V R : Type}
  (f : forall T, E T -> eitherT V (itree F) T)
  (t : itree E R) :
  unEitherT (interp_either f (Tau t)) ≅ Tau (unEitherT (interp_either f t)).
Proof.
  red.
  rewrite unfold_interp_either''.
  cbn.
  reflexivity.
Qed.

Lemma interp_either_vis' {E F : Type -> Type} {V T R : Type}
  (f : forall T, E T -> eitherT V (itree F) T)
  (e : E T)
  (k : T -> itree E R) :
  eq_either_itree (interp_either f (Vis e k)) (f T e >>= fun x => interp_either f (Tau (k x))).
Proof.
  red.
  rewrite unfold_interp_either''.
  cbn.
  eapply eq_itree_clo_bind.
  reflexivity.
  intros ? ? ?; subst.
  destruct u2; try reflexivity.
  rewrite interp_either_tau'.
  reflexivity.
Qed.

Lemma interp_either_ret {E F} {V R : Type}
  (f : forall T, E T -> eitherT V (itree F) T)
  (r : R) :
  Monad.eq1 (interp_either f (Ret r)) (ret r).
Proof.
  apply eq1_unEitherT; try typeclasses eauto.
  setoid_rewrite itree_eta. reflexivity.
Qed.

Lemma interp_either_ret' {E F} {V R : Type}
  (f : forall T, E T -> eitherT V (itree F) T)
  (r : R) :
  unEitherT (interp_either f (Ret r)) ≅ unEitherT (ret r).
Proof.
  setoid_rewrite itree_eta. reflexivity.
Qed.


Lemma interp_either_bind :
  forall {E F : Type -> Type} {V R S : Type}
    (f : forall T : Type, E T -> eitherT V (itree F) T) 
    (t : itree E R) (k : R -> itree E S),
    Monad.eq1 (interp_either f (bind t k)) (bind (interp_either f t) (fun r : R => interp_either f (k r))).
Proof.
  intros E F V R S f t k.
  revert t k.
  ginit. gcofix CIH.
  intros t k.
  cbn.
  rewrite !unfold_interp_either''.
  epose proof unfold_bind.
  specialize (H t k).
  apply EqAxiom.bisimulation_is_eq in H.
  rewrite H.
  destruct (observe t).
  - cbn. rewrite !bind_ret_l. cbn.
    rewrite !unfold_interp_either''.
    apply reflexivity.
  - cbn. rewrite !bind_tau.
    gstep. econstructor. gbase. apply CIH.
  - cbn.
    rewrite bind_bind.
    guclo eqit_clo_bind. econstructor.
    + reflexivity.
    + intros ? ? ?; subst.
      destruct u2.
      -- rewrite bind_ret_l.
         gstep; red; constructor; auto.
      -- rewrite bind_tau.
         gstep; constructor.
         gbase.
         apply CIH.
Qed.

Lemma interp_either_trigger_eqit {E F : Type -> Type} {V T : Type}
      (e : E T) (f : E ~> eitherT V (itree F))
  : eq_either_itree (interp_either f (ITree.trigger e))
      (@bind (eitherT V (itree F)) _ _ _ (f _ e) (fun x => interp_either f (Tau (Ret x)))).
Proof.
  unfold ITree.trigger. rewrite interp_either_vis'.
  reflexivity.
Qed.

Lemma interp_either_trigger {E F : Type -> Type} {V R : Type}
      (e : E R) (f : E ~> eitherT V (itree F))
  : Monad.eq1 (interp_either f (ITree.trigger e)) (f _ e).
Proof.
  unfold ITree.trigger. rewrite interp_either_vis.
  do 4 red.
  cbn.
  rewrite <- (bind_ret_r (unEitherT (f R e))) at 2.
  eapply eqit_bind; try reflexivity.
  intros []; try reflexivity.
  rewrite unfold_interp_either'.
  cbn.
  reflexivity.
Qed.
