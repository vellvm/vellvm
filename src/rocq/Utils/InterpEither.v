Unset Universe Checking.
From Stdlib Require Import
     Morphisms.

From Paco Require Import paco.

From ExtLib Require Import
  Structures.Monads
  Structures.Functor
  EitherMonad.

From CTree Require Import
     CTree
     Eq
     Fold.

From Vellvm Require Import
     Utils.Util
     Utils.Error
     Utils.CTreeUtils.

(* Import ITree.Basics.Basics.Monads. *)

Set Implicit Arguments.
(* Set Contextual Implicit. *)

Import MonadNotation.

Open Scope monad.

#[global] Instance MonadStepEither {S M} `{HM : Monad M} `{MS : MonadStep M} : MonadStep (eitherT S M).
red.
constructor.
eapply bind.
apply mstep.
intros.
apply (ret (inr H)).
Defined.

#[global] Instance MonadStuckEither {S M} `{HM : Monad M} `{MS : MonadStuck M} : MonadStuck (eitherT S M).
red.
intros X.
constructor.
apply mstuck.
Defined.

#[global] Instance MonadBrEither {B S M} `{HM : Monad M} `{MB : MonadBr B M} : MonadBr B (eitherT S M).
red.
intros.
apply mbr in b.
constructor.
eapply fmap; cycle 1; eauto.
Defined.

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

Definition interp_either {E M EXC} {BR}
  `{FM : Functor M} `{MM : Monad M}
  `{MonadStuck M}
  `{MonadStep M}
  `{MonadBr BR M}
  `{IM : MonadIter M} (h : E ~> eitherT EXC M) :
  ctree E BR ~> eitherT EXC M := interp h.

Definition _interp_either {E F V R} {BR}
  (f : E ~> eitherT V (ctree F BR)) 
  (ot : ctreeF E BR R (ctree E BR R))
  : eitherT V (ctree F BR) R.
  refine (match ot with
    | RetF r => mkEitherT (ret (inr r))
    | StuckF => _
    | StepF t => _
    | GuardF t => mkEitherT (Guard (unEitherT (interp_either f t)))
    | VisF _ e k => _
    | BrF _ b k => _
          end).
  - apply mkEitherT.
    apply mstuck.
  - apply mkEitherT.
  eapply bind.
  apply (mstep).
  intros.
    pose proof (Guard (unEitherT (interp_either f t))).
    auto.
  - refine (f _ e >>= _).
    intros X.
    apply mkEitherT.
    apply (Guard (unEitherT (interp_either f (k X)))).
  - refine (mbr _ b >>= _).
    intros X.
    apply mkEitherT.
    apply (Guard (unEitherT (interp_either f (k X)))).
Defined.


Lemma unfold_interp_either {E F V R BR} (h : E ~> eitherT V (ctree F BR))
      (t : ctree E BR R) :
    Monad.eq1
      (interp_either h t)
      (_interp_either h (observe t)).
Proof.
  unfold interp_either, interp, Basics.iter, MonadIter_eitherT, Basics.iter, MonadIter_ctree; cbn.
  red; red; cbn.
  rewrite unfold_iter; cbn.
  destruct observe; cbn.
  - rewrite 2 bind_ret_l. reflexivity.
  - rewrite bind_bind.
   setoid_rewrite bind_ret_l.
   unfold mstuck, MonadStuck_ctree.
   rewrite bind_stuck.
   reflexivity.
  - rewrite 3 bind_bind.
    setoid_rewrite bind_ret_l.
    setoid_rewrite bind_ret_l.
    setoid_rewrite bind_ret_l.
    setoid_rewrite bind_step.
    setoid_rewrite bind_ret_l.
    unfold Monad.eq1.
    red.
    apply sb_step.
    reflexivity.
  - setoid_rewrite bind_map.
    setoid_rewrite bind_ret_l.
    reflexivity.
  - setoid_rewrite bind_bind; cbn.
    setoid_rewrite bind_bind; cbn.
    setoid_rewrite bind_ret_l.
    apply sbisim_clo_bind_eq.
    reflexivity.
    intros.
    destruct x.
    + rewrite bind_ret_l.
      reflexivity.
    + rewrite bind_ret_l.
      reflexivity. 
  - repeat rewrite bind_bind.
    setoid_rewrite bind_ret_l.
    apply sbisim_clo_bind_eq.
    reflexivity.
    intros.
    rewrite bind_ret_l.
    rewrite bind_ret_l.
    reflexivity.
Qed.

Lemma unfold_interp_either' {E F V R BR} (h : E ~> eitherT V (ctree F BR))
      (t : ctree E BR R) :
    Monad.eq1
      (unEitherT (interp_either h t))
      (unEitherT (_interp_either h (observe t))).
Proof.
  apply unfold_interp_either.
Qed.

Lemma unfold_interp_either'' {E F V R BR} (h : E ~> eitherT V (ctree F BR))
      (t : ctree E BR R) :
      (unEitherT (interp_either h t)) ≅
      (unEitherT (_interp_either h (observe t))).
Proof.
  unfold interp_either, interp, Basics.iter, MonadIter_eitherT, Basics.iter, MonadIter_ctree; cbn.
  rewrite unfold_iter.
  rewrite bind_bind.
  setoid_rewrite bind_ret_l.
  destruct observe; cbn.
  - rewrite bind_ret_l.
    reflexivity.
  - rewrite bind_stuck.
  reflexivity.
  - setoid_rewrite bind_map.
    setoid_rewrite bind_bind; cbn.
    setoid_rewrite bind_ret_l.
    apply equ_clo_bind_eq.
    intros.
    reflexivity.
  - rewrite bind_ret_l.
    reflexivity.
  - rewrite bind_bind; cbn.
    apply equ_clo_bind_eq.
    intros.
    destruct x.
    + rewrite bind_ret_l.
      reflexivity.
    + rewrite bind_ret_l.
    reflexivity.
  - repeat rewrite bind_bind; cbn.
    apply equ_clo_bind_eq.
    intros.
    rewrite bind_ret_l.
    rewrite bind_ret_l.
    rewrite bind_ret_l.
    reflexivity.  
Qed.
#[global] Opaque interp_either.
Check @equ.
#[global]
Instance eq1_interp_either {E F V R} {BR}
 (h : E ~> eitherT V (ctree F BR)) :
  Proper ((@Monad.eq1 (ctree E BR) _ _) ==> (@Monad.eq1 (eitherT V (ctree F BR)) _ _))
  (* Proper ((@equ _ BR _ _ eq)  ==> (@Monad.eq1 (eitherT V (ctree F BR)) _ _)) *)
    (@interp_either E (ctree F BR) V _ _ _ _ _ _ _ h R).
Proof.
  cbn.
  (* coinduction R CIH.
  intros.
  x
  einit. ecofix CIH. intros.
  rewrite !unfold_interp_either''.
  punfold H0; red in H0.
  induction H0; intros; subst; simpl; pclearbot.
  - eret.
  - eguard.    
  - ebind. econstructor; [reflexivity|].
    intros; subst.
    destruct u2.
    eret.
    eguard. ebase.
    right.
    apply CIHL.
    apply REL.
  - rewrite guard_euttge. eauto.
    rewrite unfold_interp_either''. eauto.
  - rewrite guard_euttge. eauto.
    rewrite unfold_interp_either''. eauto. *)
Admitted.

Definition eq_either_ctree {F V R BR} (t1 t2 : eitherT V (ctree F BR) R)
  := unEitherT t1 ≅ unEitherT t2.

#[global] Instance Reflexive_eq_either_ctree {F V R BR} : Reflexive (@eq_either_ctree F V R BR).
intros x.
red.
reflexivity.
Qed.

#[global] Instance Symmetric_eq_either_ctree {F V R BR} : Symmetric (@eq_either_ctree F V R BR).
intros x y EQ.
red; red in EQ.
symmetry.
apply EQ.
Qed.

#[global] Instance Transitive_eq_either_ctree {F V R BR} : Transitive (@eq_either_ctree F V R BR).
intros x y z XY YZ.
red; red in XY, YZ.
rewrite XY, YZ.
reflexivity.
Qed.

#[global] Instance Equivalence_eq_either_ctree {F V R BR} : Equivalence (@eq_either_ctree F V R BR).
split; try typeclasses eauto.
Qed.
#[global]
Instance eq_interp_either {E F V R BR} (h : E ~> eitherT V (ctree F BR)) :
  Proper ((@equ _ BR _ _ eq) ==> eq_either_ctree)
    (@interp_either _ _ _ _ _ _ _ _ _ _ h R).
Proof.
  cbn.
  unfold eq_either_ctree.
  coinduction r CIH.
  intros * EQ1 *.
  rewrite !unfold_interp_either''.
  unfold _interp_either.
  step in EQ1; inv EQ1; auto.
  - constructor; auto. 
  - cbn. upto_bind_eq.
    intros.
    constructor.
    auto.
  - cbn; upto_bind_eq.
    intros.
    destruct x0.
    constructor.
    auto.
    constructor.
    auto.
  - cbn; upto_bind_eq.
    intros.
    destruct x0; constructor; auto.
Qed.  

#[global]
Instance eq_either_ctree_eq1 {E V R BR} :
  Proper (@eq_either_ctree E V R BR ==> @eq_either_ctree E V R BR ==> iff) Monad.eq1.
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

Lemma interp_either_vis {E F BR: Type -> Type} {V T R : Type}
  (f : forall T, E T -> eitherT V (ctree F BR) T)
  (e : E T)
  (k : T -> ctree E BR R) :
  Monad.eq1 (interp_either f (Vis e k)) (f T e >>= fun x => interp_either f (k x)).
Proof.
  rewrite unfold_interp_either.
  cbn.
  do 4 red.
  cbn.
  eapply sbisim_clo_bind_eq.
  reflexivity.
  intros ?; subst.
  destruct x; try reflexivity.
  rewrite sb_guard.
  reflexivity.
Qed.

Lemma interp_either_guard {E F BR} {V R : Type}
  (f : forall T, E T -> eitherT V (ctree F BR) T)
  (t : ctree E BR R) :
  Monad.eq1 (interp_either f (Guard t)) (interp_either f t).
Proof.
  apply eq1_unEitherT; try typeclasses eauto.
  unfold Monad.eq1.
  red.
  rewrite unfold_interp_either'.
  cbn.
  rewrite sb_guard.
  reflexivity.
Qed.

Lemma interp_either_guard' {E F BR} {V R : Type}
  (f : forall T, E T -> eitherT V (ctree F BR) T)
  (t : ctree E BR R) :
  unEitherT (interp_either f (Guard t)) ≅ Guard (unEitherT (interp_either f t)).
Proof.
  red.
  rewrite unfold_interp_either''.
  cbn.
  reflexivity.
Qed.

Lemma interp_either_vis' {E F BR: Type -> Type} {V T R : Type}
  (f : forall T, E T -> eitherT V (ctree F BR) T)
  (e : E T)
  (k : T -> ctree E BR R) :
  eq_either_ctree (interp_either f (Vis e k)) (f T e >>= fun x => interp_either f (Guard (k x))).
Proof.
  red.
  rewrite unfold_interp_either''.
  cbn.
  eapply equ_clo_bind.
  reflexivity.
  intros ? ? ?; subst.
  destruct x2; try reflexivity.
  rewrite interp_either_guard'.
  reflexivity.
Qed.

Lemma interp_either_ret {E F BR} {V R : Type}
  (f : forall T, E T -> eitherT V (ctree F BR) T)
  (r : R) :
  Monad.eq1 (interp_either f (Ret r: ctree E BR R)) (ret r).
Proof.
  apply eq1_unEitherT; try typeclasses eauto.
  setoid_rewrite ctree_eta. reflexivity.
Qed.

Lemma interp_either_ret' {E F BR} {V R : Type}
  (f : forall T, E T -> eitherT V (ctree F BR) T)
  (r : R) :
  unEitherT (interp_either f (Ret r: ctree E BR R)) ≅ unEitherT (ret r).
Proof.
  setoid_rewrite ctree_eta. reflexivity.
Qed.


Lemma interp_either_bind :
  forall {E F BR: Type -> Type} {V R S : Type}
    (f : forall T : Type, E T -> eitherT V (ctree F BR) T) 
    (t : ctree E BR R) (k : R -> ctree E BR S),
    Monad.eq1 (interp_either f (bind t k)) (bind (interp_either f t) (fun r : R => interp_either f (k r))).
Proof.
  intros E F V R S f t k.
  revert t k.
  admit.
  (* ginit. gcofix CIH.
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
  - cbn. rewrite !bind_guard.
    gstep. econstructor. gbase. apply CIH.
  - cbn.
    rewrite bind_bind.
    guclo eqit_clo_bind. econstructor.
    + reflexivity.
    + intros ? ? ?; subst.
      destruct u2.
      -- rewrite bind_ret_l.
         gstep; red; constructor; auto.
      -- rewrite bind_guard.
         gstep; constructor.
         gbase.
         apply CIH. *)
Admitted.

Lemma interp_either_trigger_equ {E F BR: Type -> Type} {V T : Type}
      (e : E T) (f : E ~> eitherT V (ctree F BR))
  : eq_either_ctree (interp_either f (CTree.trigger e: ctree E BR T))
      (@bind (eitherT V (ctree F BR)) _ _ _ (f _ e) (fun x => interp_either f (Guard (Ret x: ctree E BR T)))).
Proof.
  unfold CTree.trigger. rewrite interp_either_vis'.
  reflexivity.
Qed.

Lemma interp_either_trigger {E F BR: Type -> Type} {V R : Type}
      (e : E R) (f : E ~> eitherT V (ctree F BR))
  : Monad.eq1 (interp_either f (CTree.trigger e: ctree E BR R)) (f _ e).
Proof.
  unfold CTree.trigger. rewrite interp_either_vis.
  do 4 red.
  cbn.
  rewrite <- (bind_ret_r (unEitherT (f R e))) at 2.
  upto_bind_eq.
  intros ?; subst.
  destruct x.
  reflexivity.
  rewrite unfold_interp_either'.
  cbn.
  reflexivity.
Qed.
