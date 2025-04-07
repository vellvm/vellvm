(** * [IForest]: Sets of itrees *)

(** A monad-like structure.

[[
  iforest E X := (itree E X -> Prop)
]]

   Its [bind] is not associative. It only satisfies an "associativity to the right"
   inequality ([bind_bind_iforest]).

   TODO: There may be a better definition of [bind]. *)

(* begin hide *)
From ITree Require Import
     Axioms
     ITree
     ITreeFacts
     Props.Leaf
     Basics.HeterogeneousRelations.

From Paco Require Import paco.

From ExtLib Require Import
     Structures.Functor.

From Coq Require Import
     Relations
     Morphisms.

Import ITree.Basics.Basics.Monads.

Import MonadNotation.
Import CatNotations.
Local Open Scope monad_scope.
Local Open Scope cat_scope.
(* end hide *)

(** The [iforest] "monad", consisting of sets of [itree]. *)

Definition iforest (E: Type -> Type) (X: Type): Type :=
  itree E X -> Prop.

(** TODO: There may be a generalization to a kind of monad transformer
    [PropT M X := M X -> Prop]. *)

(** [iforest] are expected to be compatible with the [eutt] relation in the following sense: *)
Notation eutt_closed := (Proper (eutt eq ==> iff)) (only parsing).

#[global] Polymorphic Instance Eq1_iforest {E} : Eq1 (iforest E) :=
  fun a PA PA' =>
    (forall x y, x ≈ y -> (PA x <-> PA' y)) /\
    eutt_closed PA /\ eutt_closed PA'.

#[global] Instance Functor_iforest {E}
  : Functor (iforest E) :=
  {| fmap := fun A B f PA b => exists (a: itree E A), PA a /\ b = fmap f a |}.

Definition subtree {E} {A B} (ta : itree E A) (tb : itree E B) : Prop :=
  exists (k : A -> itree E B), tb ≈ bind ta k.

(* Definition 5.1 *)
Definition bind_iforest {E}
  : forall A B, iforest E A -> (A -> iforest E B) -> iforest E B :=
  fun A B (specA : iforest E A) (K: A -> iforest E B) (tb: itree E B) =>
    exists (ta: itree E A) (k: A -> itree E B),
      specA ta /\
      tb ≈ bind ta k /\
      (forall a, Leaf a ta -> K a (k a)).

Definition bind_iforest_stronger {E}
  : forall A B, iforest E A -> (A -> iforest E B) -> iforest E B :=
  fun A B (PA: iforest E A) (K: A -> iforest E B) (tb: itree E B) =>
    exists (ta: itree E A) (k: A -> itree E B),
      PA ta /\
      tb ≈ bind ta k /\
      (forall a, Leaf a ta -> K a (k a)).

(** Alternate, logically equivalent version of [bind_iforest].
  It should not matter which one we use. Since [bind_iforest] has fewer cases, we should
  stick to it.*)
Definition bind_iforest' {E}
  : forall A B, iforest E A -> (A -> iforest E B) -> iforest E B :=
  fun A B (PA: iforest E A) (K: A -> iforest E B) (tb: itree E B) =>
    exists (ta: itree E A),  PA ta /\
                        ((exists (k: A -> itree E B),
                             (forall a, Leaf a ta -> K a (k a))
                             /\ tb ≈ bind ta k)
                         \/ (forall k, (forall a, K a (k a)) /\ tb ≈ bind ta k)).

Lemma bind_iforest_bind_iforest' {E}:
  forall A B PA K (tb : itree E B), bind_iforest A B PA K tb <-> bind_iforest' A B PA K tb.
Proof.
  intros. split.
  intros.
  - red. red in H.
    destruct H as (ta & ka & HPA & eq & HR).
    exists ta. split; auto.
    left.  exists ka. split; auto.
  - intros.
    red. red in H.
    destruct H as  (ta & EQ1 & [(k & KA & EQ2) | HX]).
    + exists ta. exists k. auto.
    + exists ta. exists (fun _ => ITree.spin).
      split; auto.
      specialize (HX (fun _ => ITree.spin)).
      destruct HX as (HA & H).
      split; auto.
Qed.


(* Definition 5.1 *)
#[global] Instance Monad_iforest {E} : Monad (iforest E) :=
  {|
    ret := fun _ x y => y ≈ ret x
    ; bind := bind_iforest
  |}.

(* Definition 5.3: Handler Correctness *)
Definition handler_correct {E F} (h_spec: E ~> iforest F) (h: E ~> itree F) : Prop :=
  (forall T e, h_spec T e (h T e)).

Inductive interp_iforestF {E F} (h_spec : forall T, E T -> itree F T -> Prop)
          {R : Type} (RR : relation R) (sim : itree E R -> itree F R -> Prop)
          : itree' E R -> itree F R -> Prop :=
| Interp_iforest_Ret : forall r1 r2 (REL: RR r1 r2)
                   (t2 : itree F R)
                   (eq2 : t2 ≈ (Ret r2)),
    interp_iforestF h_spec RR sim (RetF r1) t2

| Interp_iforest_Tau : forall t1 t2 (HS: sim t1 t2), interp_iforestF h_spec RR sim (TauF t1) t2

| Interp_iforest_Vis : forall A (e : E A) (k1 : A -> itree E R)
                       (t2 : itree F R)
                       (ta :itree F A)  (k2 : A -> itree F R) (HTA: h_spec A e ta)
                       (eq2 : t2 ≈ (bind ta k2))
                       (HK : forall (a : A), Leaf a ta ->  sim (k1 a) (k2 a)),
    interp_iforestF h_spec RR sim (VisF e k1) t2.

#[global] Hint Constructors interp_iforestF : itree.

Lemma interp_iforestF_mono E F h_spec R RR  (t0 : itree' E R) (t1 : itree F R) sim sim'
      (IN : interp_iforestF h_spec RR sim t0 t1)
      (LE : sim <2= sim') :
  (interp_iforestF h_spec RR sim' t0 t1).
Proof.
  induction IN; eauto with itree.
Qed.

#[global] Hint Resolve interp_iforestF_mono : paco.

Definition interp_iforest_ E F h_spec R RR sim (t0 : itree E R) (t1 : itree F R) : Prop :=
  interp_iforestF h_spec RR sim (observe t0) t1.
#[global] Hint Unfold interp_iforest_ : itree.

Lemma interp_iforest__mono E F h_spec R RR : monotone2 (interp_iforest_ E F h_spec R RR).
Proof.
  do 2 red. intros. eapply interp_iforestF_mono; eauto.
Qed.
#[global] Hint Resolve interp_iforest__mono : paco.

(* Definition 5.2 *)
Definition interp_iforest {E F} (h_spec : E ~> iforest F) :
  forall R (RR: relation R), itree E R -> iforest F R :=
    fun R (RR: relation R) =>  paco2 (interp_iforest_ E F h_spec R RR) bot2.

(* Figure 7: Interpreter law for Ret *)
Lemma interp_iforest_ret :
  forall R E F (h_spec : E ~> iforest F)
    (r : R)
  , Eq1_iforest _ (interp_iforest h_spec R eq (ret r)) (ret r).
Proof.
  intros.
  repeat red.
  split; [| split].
  - intros. split; intros.
    + unfold interp_iforest in H0.
      pinversion H0. subst.
      cbn. rewrite <- H. assumption.
    + pstep. econstructor. reflexivity. rewrite H. cbn in H0. assumption.
  - do 3 red.
    intros t1 t2 eq; split; intros H; pinversion H; subst.
    + red. pstep. econstructor. reflexivity. rewrite <- eq. assumption.
    + red. pstep. econstructor. reflexivity. rewrite eq. assumption.
 - do 3 red. intros. split; intros; cbn in *. rewrite <- H. assumption. rewrite H; assumption.
Qed.

#[global] Instance interp_iforestF_Proper
       {E F} (h_spec : E ~> iforest F) R RR (t : itree' E R)
       (sim : itree E R -> itree F R -> Prop)
       (HS: forall t, Proper(eutt eq ==> flip impl) (sim t))
  :
  Proper(eutt eq ==> iff) (interp_iforestF h_spec RR sim t).
Proof.
  do 2 red.
  intros.
  split; intros.
  - inversion H0; subst; econstructor; eauto.
    + rewrite <- H. assumption.
    + specialize (HS t1). rewrite <- H. assumption.
    + rewrite <- H. assumption.

  - inversion H0; subst; econstructor; eauto.
    rewrite H. assumption. specialize (HS t1). rewrite H. assumption.
    rewrite H. assumption.
Qed.

#[global] Instance interp_iforest_Proper
       {E F} (h_spec : E ~> iforest F) R RR (t : itree E R) :
  Proper(eq_itree Logic.eq ==> iff) (interp_iforest h_spec R RR t).
Proof.
  do 2 red.
  intros.
  split.
  - revert t x y H.
    pcofix CIH.
    intros t x y eq HI.
    red in HI. punfold HI. red in HI.
    pstep. red. genobs t ot.
    inversion HI; subst; econstructor; eauto.
    + rewrite <- eq. assumption.
    + pclearbot. right. eapply CIH; eauto.
    + rewrite <- eq. apply eq2.
    + intros. specialize (HK a H0). pclearbot. right. eapply CIH. 2 : { apply HK. } reflexivity.
  - revert t x y H.
    pcofix CIH.
    intros t x y eq HI.
    red in HI. punfold HI. red in HI.
    pstep. red. genobs t ot.
    inversion HI; subst; econstructor; eauto.
    + rewrite eq. assumption.
    + pclearbot. right. eapply CIH; eauto.
    + rewrite eq. apply eq2.
    + intros. specialize (HK a H0). pclearbot. right. eapply CIH. 2 : { apply HK. } reflexivity.
Qed.

#[global] Instance interp_iforest_Proper2
       {E F} (h_spec : E ~> iforest F) R RR (t : itree E R) :
  Proper(eutt Logic.eq ==> iff) (interp_iforest h_spec R RR t).
Proof.
  do 2 red.
  intros.
  split.
  - revert t x y H.
    pcofix CIH.
    intros t x y eq HI.
    red in HI. punfold HI. red in HI.
    pstep. red. genobs t ot.
    inversion HI; subst; econstructor; eauto.
    + rewrite <- eq. assumption.
    + pclearbot. right. eapply CIH; eauto.
    + rewrite <- eq. apply eq2.
    + intros. specialize (HK a H0). pclearbot. right. eapply CIH. 2 : { apply HK. } reflexivity.
  - revert t x y H.
    pcofix CIH.
    intros t x y eq HI.
    red in HI. punfold HI. red in HI.
    pstep. red. genobs t ot.
    inversion HI; subst; econstructor; eauto.
    + rewrite eq. assumption.
    + pclearbot. right. eapply CIH; eauto.
    + rewrite eq. apply eq2.
    + intros. specialize (HK a H0). pclearbot. right. eapply CIH. 2 : { apply HK. } reflexivity.
Qed.

(* This exists in the stdlib as [ProofIrrelevance.inj_pair2], but we reprove
 it to not depend on proof irrelevance (we use axiom [JMeq.JMeq_eq] instead).
 The itree library now avoids as much as possible using this axiom, we may want
 to see if it's possible to do so here.
 *)
Lemma inj_pair2 :
  forall (U : Type) (P : U -> Type) (p : U) (x y : P p),
    existT P p x = existT P p y -> x = y.
Proof.
  intros. apply JMeq.JMeq_eq.
  refine (
      match H in _ = w return JMeq.JMeq x (projT2 w) with
      | eq_refl => JMeq.JMeq_refl
      end).
Qed.

#[global] Instance interp_iforest_Proper3
       {E F} (h_spec : E ~> iforest F) R RR :
  Proper(eq_itree eq ==> eq  ==> iff) (interp_iforest h_spec R RR).
Proof.
  do 4 red.
  intros; split.
  - subst.
    revert x y H y0.
    pcofix CIH.
    intros x y eq t H.
    pstep; red.
    punfold H. red in H.

    punfold eq. red in eq.
    genobs x obsx.
    genobs y obsy.
    revert x y Heqobsx Heqobsy t H.

    induction eq; intros x y Heqobsx Heqobsy t H; inversion H; subst; pclearbot.
    + econstructor; eauto.
    + econstructor. right. eapply CIH. apply REL. apply HS.
    + apply inj_pair2 in H2.
      apply inj_pair2 in H3. subst.
      econstructor; eauto. intros X HX. specialize (REL X). specialize (HK X HX). pclearbot.
      right. eapply CIH; eauto.
    + eapply IHeq.  reflexivity. reflexivity.
      punfold HS.
    + econstructor. left. pstep. eapply IHeq. reflexivity. reflexivity. assumption.
    + econstructor. left.  pstep. eapply IHeq. reflexivity. reflexivity. assumption.
    + econstructor. left.  pstep. eapply IHeq. reflexivity. reflexivity. assumption.

 - subst.
    revert x y H y0.
    pcofix CIH.
    intros x y eq t H.
    pstep; red.
    punfold H. red in H.

    punfold eq. red in eq.
    genobs x obsx.
    genobs y obsy.
    revert x y Heqobsx Heqobsy t H.

    induction eq; intros x y Heqobsx Heqobsy t H; inversion H; subst; pclearbot.
    + econstructor; eauto.
    + econstructor. right. eapply CIH. apply REL. apply HS.
    + apply inj_pair2 in H2.
      apply inj_pair2 in H3. subst.
      econstructor; eauto. intros X HX. specialize (REL X). specialize (HK X HX). pclearbot.
      right. eapply CIH; eauto.
    + econstructor. left. pstep. eapply IHeq. reflexivity. reflexivity. assumption.
    + econstructor. left. pstep. eapply IHeq. reflexivity. reflexivity. assumption.
    + econstructor. left. pstep. eapply IHeq. reflexivity. reflexivity. assumption.
    + eapply IHeq. reflexivity. reflexivity.   punfold HS.
Qed.

(* Lemma 5.4: interp_iforest_correct - note that the paper presents a slightly simpler formulation where t = t' *)
Lemma interp_iforest_correct_exec:
  forall {E F} (h_spec: E ~> iforest F) (h: E ~> itree F),
    handler_correct h_spec h ->
    forall R RR `{Reflexive _ RR} t t', t ≈ t' -> interp_iforest h_spec R RR t (interp h t').
Proof.
  intros.
  revert t t' H1.
  pcofix CIH.
  intros t t' eq.
  pstep.
  red.
  unfold interp, Basics.iter, MonadIter_itree.
  rewrite (itree_eta t) in eq.
  destruct (observe t).
  - econstructor. reflexivity. rewrite <- eq. rewrite unfold_iter. cbn.
    rewrite Eqit.bind_ret_l. cbn.  reflexivity.
  - econstructor. right.
    eapply CIH. rewrite tau_eutt in eq. rewrite eq. reflexivity.
  - econstructor.
    2 : { rewrite <- eq. rewrite unfold_iter. cbn.
          unfold ITree.map. rewrite Eqit.bind_bind.
          setoid_rewrite Eqit.bind_ret_l at 1. cbn. setoid_rewrite tau_eutt.
          reflexivity. }
    apply H.
    intros a. cbn.
    right.
    unfold interp, Basics.iter, MonadIter_itree in CIH. unfold fmap, Functor_itree, ITree.map in CIH.
    specialize (CIH (k a) (k a)).
    apply CIH.
    reflexivity.
Qed.

(* Lemma 5.5 - note that the paper presents this lemma after unfolding the definition of Proper.
 *)
#[global] Instance interp_iforest_Proper_eq :
  forall R (RR : relation R) (HR: Reflexive RR) (HT : Transitive RR) E F (h_spec : E ~> iforest F),
    Proper (@eutt _ _ _ RR ==> eq ==> flip Basics.impl) (@interp_iforest E _ h_spec R RR).
Proof.
  intros.

  do 5 red.
  intros t1 t2 eqt s' s eqs HI.
  subst.

  revert t1 t2 eqt s HI.

  pcofix CIH.

  intros.

  pstep. red.
  punfold HI. red in HI.

  punfold eqt. red in eqt.
  genobs t1 obst1.
  genobs t2 obst2.
  revert t1 t2 Heqobst1 Heqobst2 s HI.

  induction eqt; intros.
  - inversion HI; subst.
    econstructor. etransitivity; eauto. assumption.
  - inversion HI; subst.
    econstructor. pclearbot. right.  eapply CIH; eauto.
  - inversion HI.
    subst.
    apply inj_pair2 in H1.
    apply inj_pair2 in H2.
    subst.
    econstructor.
    apply HTA.
    apply eq2.
    intros a Ha. specialize (REL a). specialize (HK a Ha). red in REL. pclearbot.
    right. eapply CIH. apply REL. apply HK.
  - econstructor.
    left. pstep. red. eapply IHeqt. reflexivity. eassumption. assumption.
  - inversion HI; subst.
    pclearbot.
    eapply IHeqt. reflexivity. reflexivity.
    pinversion HS.
Qed.

Lemma Leaf_Vis_sub :  forall {E} {R} X (e : E X) (k : X -> itree E R) u x, Leaf u (k x) -> Leaf u (Vis e k).
Proof.
  intros.
  eapply LeafVis. reflexivity. apply H.
Qed.

Lemma eutt_Leaf_ : forall {E} {R} (RR : R -> Prop) (ta : itree E R)
   (IN: forall (a : R), Leaf a ta -> RR a), eutt (fun u1 u2 => u1 = u2 /\ RR u1) ta ta.
Proof.
  intros E R.
  ginit.
  gcofix CIH; intros.

  setoid_rewrite (itree_eta ta) in IN.

  gstep. red.

  destruct (observe ta).
  - econstructor.  split; auto. apply IN. econstructor. reflexivity.
  - econstructor. gfinal. left. apply CIH. intros. eapply IN. rewrite tau_eutt. assumption.
  - econstructor. intros. red.
    gfinal. left. apply CIH. intros. eapply IN. eapply Leaf_Vis_sub. apply H.
Qed.

Lemma eutt_Leaf : forall E R (ta : itree E R), eutt (fun u1 u2 => u1 = u2 /\ Leaf u1 ta) ta ta.
Proof.
  intros.
  apply eutt_Leaf_. auto.
Qed.

(* Figure 7: interp Trigger law *)
(* morally, we should only work with "proper" triggers everywhere *)
Lemma interp_iforest_trigger :
  forall E F (h_spec : E ~> iforest F) R (e : E R)
    (HP : forall T, Proper (eq ==> Eq1_iforest T) (h_spec T))
  , Eq1_iforest _ (interp_iforest h_spec R eq (trigger e)) (h_spec R e).
Proof.
  intros.
  red.
  split; [| split].
  - intros; split; intros.
    + unfold trigger in H0. red in H0.
      pinversion H0; subst.
      apply inj_pair2 in H3. apply inj_pair2 in H4.
      subst.
      unfold subevent, resum, ReSum_id, Id_IFun, id_ in HTA.
      rewrite eq2 in H.
      assert (x <- ta ;; k2 x ≈ ta).
      { rewrite <- (Eqit.bind_ret_r ta).
        apply eutt_clo_bind with (UU := fun u1 u2 => u1 = u2 /\ Leaf u1 ta).
        rewrite Eqit.bind_ret_r. apply eutt_Leaf.
        intros. destruct H1. subst. specialize (HK u2 H2). pclearbot. pinversion HK. subst. assumption.
      }
      rewrite H1 in H.
      specialize (HP R e e eq_refl).  unfold Eq1_iforest in HP. destruct HP as (P & _ & _).
      rewrite P. apply HTA. symmetry. assumption.
    + unfold trigger, subevent, resum, ReSum_id, Id_IFun, id_.
      red. pstep. eapply Interp_iforest_Vis with (k2 := (fun x : R => Ret x)).
      * apply H0.
      * unfold bind, Monad_itree. rewrite Eqit.bind_ret_r. assumption.
      * intros a. left. pstep. red. econstructor. reflexivity.  reflexivity.
  - hnf. intros; split; intros.
    rewrite <- H. assumption.
    rewrite H. assumption.
  - hnf.
    intros; split; intros.
    specialize (HP R e e eq_refl). destruct HP as (P & _ & _).
    rewrite P; eauto. symmetry. assumption.
    specialize (HP R e e eq_refl). destruct HP as (P & _ & _).
    rewrite P; eauto.
Qed.

(*  Interesting observations about interp_iforest:

    Suppose h_spec : E ~> Prop T F
    then (interp_iforest h_spec _ eq spin) : iforest F
    which itrees should be accepted by that predicate?

    - we know by interp_iforest_correct_exe that if there is an h such that handler_correct h_spec h then spin is accepted.
      (I believe we could eliminate the requirement that there is such an h)
    - what other trees are accepted?

    Answer: all of them!
 *)
Lemma interp_iforest_spin_accepts_anything :
  forall E F (h_spec : E ~> iforest F) R RR (t : itree F R),
    interp_iforest h_spec R RR ITree.spin t.
Proof.
  intros.
  pcofix CIH.
  pstep. red. cbn. econstructor. right. apply CIH.
Qed.

(* Figure 7: Structural law for tau *)
Lemma interp_iforest_tau :
  forall E F (h_spec : E ~> iforest F) R RR
    (t_spec : itree E R),
    Eq1_iforest _ (interp_iforest h_spec R RR t_spec) (interp_iforest h_spec R RR (Tau t_spec)).
Proof.
  intros.
  split; [| split].
  - intros; split; intros.
    + rewrite <- H.
      pstep. red. econstructor. left. apply H0.
    + rewrite H.
      pinversion H0. subst.
      apply HS.
  - typeclasses eauto.
  - typeclasses eauto.
Qed.

Lemma interp_iforest_ret_inv :
  forall E F (h_spec : E ~> iforest F) R RR
    (r1 : R)
    (t : itree F R)
    (H : interp_iforest h_spec R RR (ret r1) t),
     exists  r2, RR r1 r2 /\ t ≈ ret r2.
Proof.
  intros.
  punfold H.
  red in H. inversion H; subst.
  exists r2; eauto.
Qed.

Lemma interp_iforest_vis_inv :
  forall E F (h_spec : E ~> iforest F) R RR S
    (e : E S)
    (k : S -> itree E R)
    (t : itree F R)
    (H : interp_iforest h_spec R RR (vis e k) t),
  exists  ms, exists (ks : S -> itree F R),
      h_spec S e ms /\ t ≈ (bind ms ks).
Proof.
  intros.
  punfold H.
  red in H. inversion H; subst.
  apply inj_pair2 in H2.
  apply inj_pair2 in H3.
  subst.
  exists ta. exists k2. split; auto.
Qed.

Lemma interp_iforest_tau_inv :
  forall E F (h_spec : E ~> iforest F) R RR
    (s : itree E R)
    (t : itree F R)
    (H : interp_iforest h_spec R RR (Tau s) t),
    interp_iforest h_spec R RR s t.
Proof.
  intros.
  punfold H.
  red in H. inversion H; subst.
  pclearbot.
  apply HS.
Qed.

Lemma case_iforest_handler_correct:
  forall {E1 E2 F}
    (h1_spec: E1 ~> iforest F)
    (h2_spec: E2 ~> iforest F)
    (h1: E1 ~> itree F)
    (h2: E2 ~> itree F)
    (C1: handler_correct h1_spec h1)
    (C2: handler_correct h2_spec h2),
    handler_correct (case_ h1_spec h2_spec) (case_ h1 h2).
Proof.
  intros E1 E2 F h1_spec h2_spec h1 h2 C1 C2.
  unfold handler_correct in *.
  intros T e.
  destruct e. apply C1. apply C2.
Qed.

Definition iforest_compose {F G : Type -> Type} {T : Type} (TT : relation T)
    (g_spec : F ~> iforest G) (PF: iforest F T) : iforest G T :=
  fun (g:itree G T) =>
    exists f : itree F T, PF f /\ (interp_iforest g_spec) T TT f g.

Definition handler_correct_iforest
           {E F G}
           (h_spec: E ~> iforest F) (h: E ~> itree F)
           (g_spec: F ~> iforest G) (g: F ~> itree G)
  :=
    (forall T TT e,
        (iforest_compose TT g_spec (h_spec T e))
          (interp g (h T e))).


Definition singletonT {E}: itree E ~> iforest E :=
  fun R t t' => t' ≈ t.

Definition iter_cont {I E R} (step' : I -> itree E (I + R)) :
  I + R -> itree E R :=
  fun lr => ITree.on_left lr l (Tau (ITree.iter step' l)).

#[global] Polymorphic Instance MonadIter_iforest {E} : MonadIter (iforest E) :=
  fun R I (step : I -> iforest E (I + R)) i =>
    fun (r : itree E R) =>
      (exists (step' : I -> (itree E (I + R)%type)),
              ITree.bind (step' i) (@iter_cont I E R step') ≈ r /\
              (forall j, step j (step' j))).

Section LeafBind.

  Context {E : Type -> Type} {R S : Type}.

  Import ITreeNotations.
  Local Open Scope itree.

  Inductive eqit_Leaf_bind_clo b1 b2 (r : itree E R -> itree E S -> Prop) :
    itree E R -> itree E S -> Prop :=
  | pbc_intro_h U (t1 t2: itree E U) (k1 : U -> itree E R) (k2 : U -> itree E S)
                (EQV: eqit eq b1 b2 t1 t2)
                (REL: forall u, Leaf u t1 -> r (k1 u) (k2 u))
    : eqit_Leaf_bind_clo b1 b2 r (ITree.bind t1 k1) (ITree.bind t2 k2)
  .
  Hint Constructors eqit_Leaf_bind_clo: itree.

  Lemma eqit_Leaf_clo_bind  (RS : R -> S -> Prop) b1 b2 vclo
        (MON: monotone2 vclo)
        (CMP: compose (eqitC RS b1 b2) vclo <3= compose vclo (eqitC RS b1 b2))
        (ID: id <3= vclo):
    eqit_Leaf_bind_clo b1 b2 <3= gupaco2 (eqit_ RS b1 b2 vclo) (eqitC RS b1 b2).
  Proof.
    gcofix CIH. intros. destruct PR.
    guclo eqit_clo_trans.
    econstructor; auto_ctrans_eq; try (rewrite (itree_eta (x <- _;; _ x)), unfold_bind; reflexivity).
    punfold EQV. unfold_eqit.
    genobs t1 ot1.
    genobs t2 ot2.
    hinduction EQV before CIH; intros; pclearbot.
    - guclo eqit_clo_trans.
      econstructor; auto_ctrans_eq; try (rewrite <- !itree_eta; reflexivity).
      gbase; cbn.
      apply REL0.
      rewrite itree_eta, <- Heqot1; constructor; reflexivity.
    - gstep. econstructor.
      gbase.
      apply CIH.
      constructor; auto.
      intros u HR.
      apply REL0.
      rewrite itree_eta,  <- Heqot1.  econstructor 2. reflexivity. assumption.
    - gstep. econstructor.
      intros; apply ID; unfold id.
      gbase.
      apply CIH.
      constructor; auto. eapply REL.
      intros ? HR; apply REL0.
      rewrite itree_eta, <- Heqot1.
      econstructor 3; eauto; reflexivity.
    - destruct b1; try discriminate.
      guclo eqit_clo_trans.
      econstructor.
      3:{ eapply IHEQV; eauto.
          intros ? HR; apply REL.
          rewrite itree_eta, <- Heqot1; econstructor 2. reflexivity. eauto.
      }
      3,4:auto_ctrans_eq.
      2: reflexivity.
      eapply eqit_Tau_l. rewrite unfold_bind, <-itree_eta. reflexivity.
    - destruct b2; try discriminate.
      guclo eqit_clo_trans.
      econstructor; auto_ctrans_eq; cycle -1; eauto; try reflexivity.
      eapply eqit_Tau_l. rewrite unfold_bind, <-itree_eta. reflexivity.
  Qed.

End LeafBind.

Lemma eqit_Leaf_bind' {E} {R} {T} b1 b2
    (t1 t2: itree E T) (k1 k2: T -> itree E R) :
    eqit eq b1 b2 t1 t2 ->
    (forall r, Leaf r t1 -> eqit eq b1 b2 (k1 r) (k2 r)) ->
  @eqit E _ _ eq b1 b2 (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros. ginit. guclo (@eqit_Leaf_clo_bind E R R eq). unfold eqit in *.
  econstructor; eauto with paco.
Qed.

Lemma eqit_Leaf_bind'' {E} {R S} {T} (RS : R -> S -> Prop) b1 b2
    (t1 t2: itree E T) (k1: T -> itree E R) (k2 : T -> itree E S) :
    eqit eq b1 b2 t1 t2 ->
    (forall r, Leaf r t1 -> eqit RS b1 b2 (k1 r) (k2 r)) ->
  @eqit E _ _ RS b1 b2 (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros. ginit. guclo (@eqit_Leaf_clo_bind E R S RS). unfold eqit in *.
  econstructor; eauto with paco.
Qed.

Lemma eutt_ret_vis_abs: forall {X Y E} (x: X) (e: E Y) k, Ret x ≈ Vis e k -> False.
Proof.
  intros.
  punfold H; inv H.
Qed.

Ltac simpl_iter :=
    unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree.

Definition g {a b : Type} {E} (x0 : a * nat -> itree E (a + b)) (a1 : a)
  := (fun '(x, k) =>
          bind (x0 (x, k))
              (fun ir : a + b =>
                  match ir with
                  | inl i0 => ret (inl (i0, k))
                  | inr r0 => ret (inr r0)
                  end)).

Definition f {a b : Type} {E} : a * nat  -> itree E (a * nat + b) :=
  fun '(x, k) => ret (inl ((x, S k))).

Lemma iter_succ_dinatural:
  forall {a b : Type} {E} (x0 : a * nat -> itree E (a + b)) (a1 : a),
    iter (C := Kleisli (itree E)) (bif := sum)
         (f >>> case_ (g x0 a1) inr_)
     ⩯
     f >>> case_ (iter (C := Kleisli (itree E)) (bif := sum) ((g x0 a1) >>> (case_ f inr_))) (id_ _).
Proof.
  intros. rewrite iter_dinatural. reflexivity.
Qed.

Lemma iter_eq_start_index:
  forall (a b : Type) (E : Type -> Type) (x0 : a * nat -> itree E (a + b)) (a1 : a),
    iter (C := Kleisli (itree E)) (bif := sum)
      (fun '(x, k) =>
          bind (x0 (x, S k))
              (fun ir : a + b =>
                  match ir with
                  | inl i0 => ret (inl (i0, S k))
                  | inr r0 => ret (inr r0)
                  end)) (a1, 0)
      ≈ iter (C := Kleisli (itree E)) (bif := sum)
      (fun '(x', k) =>
          bind (x0 (x', k))
              (fun ir : a + b =>
                  match ir with
                  | inl i0 => ret (inl (i0, S k))
                  | inr r0 => ret (inr r0)
                  end)) (a1, 1).
Proof.
  intros a b m x0 a1.
  pose proof (iter_succ_dinatural x0 a1) as H0.
  specialize (H0 (a1, 0)).
  unfold f at 1, g at 1 in H0.
  unfold cat at 1, Cat_Kleisli at 1 in H0.
  match goal with
  | H : (?body1 ≈ _)%monad |- ?body2 ≈ _ =>
   remember body1 as s1;
   remember body2 as s2
  end.
 assert (s1 ≈ s2). {
    subst.
    match goal with
    | |- iter ?body1 _ ≈ iter ?body2 _ => remember body1 as k1;
                                          remember body2 as k2
    end.
    assert (iter k1 ⩯ iter k2). {
      eapply iterative_proper_iter.
      subst. do 3 red. intros.
      destruct a0; rewrite Monad.bind_ret_l; cbn.
      reflexivity.
    }
    do 3 red in H.
    apply H.
  }
  rewrite <- H. subst. clear H. rewrite H0.
  unfold f, g.
  unfold cat, Cat_Kleisli. rewrite Monad.bind_ret_l.
  cbn.
  match goal with
  | |- iter ?body1 _ ≈ iter ?body2 _ => remember body1 as i1; remember body2 as i2
   end.
  assert (iter i1 ⩯ iter i2). {
    eapply iterative_proper_iter.
    subst.
    do 3 red. intros.
    destruct a0. rewrite Eqit.bind_bind.
    eapply eutt_clo_bind. reflexivity.
    intros. rewrite H. destruct u2;
    rewrite Eqit.bind_ret_l; cbn; reflexivity.
  }
  do 3 red in H.
  apply H.
Qed.


Definition Eq1_iforest' {E} : Eq1 (iforest E) :=
  fun a PA PA' =>
    (forall x, (PA x -> exists y, x ≈ y /\ PA' y)) /\
    (forall y, (PA' y -> exists x, x ≈ y /\ PA x)) /\
    eutt_closed PA /\ eutt_closed PA'.

Lemma Eq1_iforest'_Eq1_iforest : forall E a PA PA', @Eq1_iforest E a PA PA' -> Eq1_iforest' a PA PA'.
Proof.
  intros.
  red.
  red in H.
  destruct H as (HXY & EPA & EPA').
  split.
  intros.
  exists x. split; [reflexivity|]. specialize (HXY x x).  apply HXY. reflexivity. assumption.
  split; try tauto.
  intros.
  exists y. split; [reflexivity|]. specialize (HXY y y).  apply HXY. reflexivity. assumption.
Qed.


(* Figure 7: ret_bind law for iforest  - first law *)
Lemma ret_bind: forall {E} (a b : Type) (f : a -> iforest E b) (x : a),
    eutt_closed (f x) ->
    eq1 (bind (ret x) f) (f x).
Proof.
  intros.
  split; [| split].
  - intros t t' eq; split; intros eqtt'.
    * cbn in *.
      repeat red in eqtt'.
      destruct eqtt' as (ta & k & EQ1 & EQ2 & KA).
    + unfold bind, Monad_itree in EQ2. rewrite EQ1, Eqit.bind_ret_l, eq in EQ2.
      eapply H; [apply EQ2 | apply KA].
      rewrite EQ1. constructor; eauto.
   * cbn.
     exists (Ret x), (fun _ => t); split; [reflexivity|]; split.
      + unfold bind, Monad_itree. rewrite Eqit.bind_ret_l; reflexivity.
      + intros. apply Leaf_Ret_inv in H0; subst. revert eqtt'; apply H. auto.
  - intros t t' EQ; cbn; split; intros HX.
    * destruct HX as (ta & k & EQ1 & EQ2 & KA).
      exists (Ret x), (fun _ => t); split; [reflexivity |]; split.
      -- unfold bind, Monad_itree. rewrite Eqit.bind_ret_l. symmetry. assumption.
      -- intros ? RET. apply Leaf_Ret_inv in RET; subst. rewrite EQ2, EQ1.
         cbn. rewrite bind_ret_l. apply KA. rewrite EQ1. constructor; auto.
    * destruct HX as (ta & k & EQ1 & EQ2 & KA).
      exists (Ret x), (fun _ => t); split; [reflexivity |]; split.
      -- unfold bind, Monad_itree. rewrite Eqit.bind_ret_l. reflexivity.
      -- intros ? RET. apply Leaf_Ret_inv in RET; subst. rewrite EQ, EQ2, EQ1.
         cbn. rewrite bind_ret_l. apply KA. rewrite EQ1. constructor; auto.
  - assumption.
Qed.

#[global] Instance bind_iforest_Proper {E} {A B} :
  Proper (eq1 ==> (eq ==> eq1) ==> eutt eq ==> iff) (@bind_iforest E A B).
Proof.
  repeat red; intros PA1 PA2 EQP K1 K2 EQK t1 t2 EQt; split; intros H.
  - destruct H as (ta & k & HA & eq & HK).
    red.
    exists ta, k. split.
    + destruct EQP. apply (H ta ta). reflexivity. assumption.
    + split. rewrite <- EQt. assumption. intros.
      repeat red in EQK.  specialize (EQK a a eq_refl). destruct EQK.
      rewrite <- H0. apply HK. assumption. reflexivity.
 -  destruct H as (ta & k & HA & eq & HK).
    red.
    exists ta, k. split.
    + destruct EQP. apply (H ta ta). reflexivity. assumption.
    + split. rewrite EQt. assumption. intros.
      repeat red in EQK.  specialize (EQK a a eq_refl). destruct EQK.
      rewrite H0. apply HK. assumption. reflexivity.
Qed.

#[global] Instance bind_Propt_Proper2 {E} {A B} (PA : iforest E A) (K : A -> iforest E B) :
  Proper (eutt eq ==> flip impl) (bind PA K).
Proof.
  repeat red.
  intros.
  repeat red in H0.
  destruct H0 as (ta & k & HA & eq & HK).
  exists ta, k. split; auto. split. rewrite H; auto. assumption.
Qed.

#[local]
Notation agrees_itree := (eutt (fun a p => p a)) (only parsing).

Definition bind_stronger {E A B}
  (PA: iforest E A) (K: A -> iforest E B) : iforest E B :=
  fun (tb: itree E B) =>
    exists (ta: itree E A), PA ta /\
    exists (k: A -> itree E B), (agrees_itree (fmap k ta) (fmap K ta) /\ tb ≈ bind ta k).

Lemma agree_itree_Leaf E A B (ta : itree E A) (K : A -> iforest E B) (k : A -> itree E B)
  : (forall a, Leaf a ta -> K a (k a)) <-> (agrees_itree (fmap k ta) (fmap K ta)).
Proof.
  split; intros.
  - cbn. red.
    unfold ITree.map.
    eapply eqit_Leaf_bind''.
    + reflexivity.
    + intros. apply eqit_Ret. apply H. assumption.
  - revert H.
    induction H0; cbn; unfold ITree.map; rewrite 2 unfold_bind, H.
    + intros H'; apply eqit_inv_Ret in H'. auto.
    + rewrite 2 tau_eutt; apply IHLeaf.
    + intros H'; eapply eqit_inv_Vis in H'. eauto.
Qed.

Lemma distinguish_bind {E} {A B}
      (a : A)
      (ma : itree E A)
      (k1 k2 : A -> itree E B)
      (HRET : Leaf a ma)
      (NEQ: ~((k1 a) ≈ (k2 a))) :
  not ((ITree.bind ma k1) ≈ (ITree.bind ma k2)).
Proof.
  intros HI; eapply eqit_bind_Leaf_inv in HI; eauto.
Qed.

Lemma not_Leaf {E} {A B} : inhabited B ->
  forall (ta: itree E A), (exists tb, forall (k : A -> itree E B), tb ≈ bind ta k) -> forall (a:A), ~ Leaf a ta.
Proof.
  intros [b] ta [tb HK] a HRet. revert tb HK; induction HRet; intros tb HK.
  - setoid_rewrite unfold_bind in HK. setoid_rewrite H in HK.
    generalize (HK (fun _ => ITree.spin)). rewrite (HK (fun _ => ret b)).
    apply eutt_Ret_spin_abs.
  - eapply (IHHRet tb). intros k; specialize (HK k).
    cbn in HK. rewrite unfold_bind, H in HK. rewrite tau_eutt in HK. auto.
  - setoid_rewrite unfold_bind in HK. setoid_rewrite H in HK; clear H t.
    assert (t2 := HK (fun _ => ITree.spin)).
    apply (IHHRet (ITree.bind (k x) (fun _ => ITree.spin))).
    intros k'; rewrite (HK k') in t2.
    eapply eqit_inv_Vis in t2; symmetry; eauto.
Qed.

(* Figure 7: bind_ret - second monad law for iforest *)
Lemma bind_ret: forall {E} (A : Type) (PA : iforest E A),
    eutt_closed PA ->
    eq1 (bind PA (fun x => ret x)) PA.
Proof.
  intros.
  split; [| split].
  + intros t t' eq; split; intros eqtt'.
    * cbn in *.
      destruct eqtt' as (ta & k & HPA & EQ & HRET).
      eapply H; [symmetry; eauto | clear eq t'].
      eapply H; [eauto | clear EQ t].
      eapply H; eauto.
      rewrite <- (Monad.bind_ret_r _ ta) at 2.
      apply eqit_Leaf_bind'; [reflexivity |].
        intros.
        rewrite (HRET r); auto.
        reflexivity.

    * cbn.
      exists t', (fun x => Ret x); split; [auto|]; split.
      unfold bind, Monad_itree. rewrite Eqit.bind_ret_r; auto.
      intros; reflexivity.

  + intros x y EQ; split; intros eqtt'.
    * cbn in *.
      destruct eqtt' as (ta & k & HPA & EQ' & HRET).
      exists ta, k; split; [auto|]; split; auto.
      rewrite <- EQ; auto.

    * cbn in *.
      destruct eqtt' as (ta & k & HPA & EQ' & HRET).
      exists ta, k; split; [auto|]; split; auto.
      rewrite EQ; auto.
  + auto.
Qed.

Definition EQ_REL {E A} (ta : itree E A) : A -> A -> Prop :=
  fun a b => a = b /\ Leaf a ta.

Lemma Symmteric_EQ_REL {E A} (ta : itree E A) : Symmetric (EQ_REL ta).
Proof.
  repeat red.
  intros a b (EQ & H).
  split.
  - symmetry. assumption.
  - subst; auto.
Qed.

Lemma Transitive_EQ_REL {E A} (ta : itree E A) : Transitive (EQ_REL ta).
Proof.
  repeat red.
  intros a b c (EQ1 & H1) (EQ2 & H2).
  split.
  - rewrite EQ1. assumption.
  - assumption.
Qed.

#[global] Instance EQ_REL_Proper {E A} : Proper (eutt eq ==> eq ==> eq ==> iff) (@EQ_REL E A).
Proof.
  repeat red.
  intros. subst.
  split; intros; unfold EQ_REL in *.
  - split. destruct H0. assumption. destruct H0.
    intros. rewrite <- H. assumption.
  - destruct H0.
    split. assumption.
    intros. rewrite H. assumption.
Qed.

Definition eq_relation {A} (R S : A -> A -> Prop) :=
  R <2= S /\ S <2= R.

#[global] Instance eutt_EQ_REL_Proper {E} {A} :
  Proper (eq_relation ==> eutt eq ==> @eutt E A A eq ==> iff) (eutt).
Proof.
  repeat red.
  intros; split; intros.
  -  rewrite <- H0. rewrite <- H1.
     clear H0 H1.
     destruct H.
     eapply eqit_mon; eauto.
  - rewrite H0, H1.
    destruct H.
    eapply eqit_mon; eauto.
Qed.

Lemma eutt_EQ_REL_Reflexive_ {E} {A} (ta : itree E A) :
  forall R, (EQ_REL ta) <2= R ->
  eutt R ta ta.
Proof.
  revert ta.
  ginit. gcofix CIH. intros ta HEQ.
  gstep. red.
  genobs ta obs.
  destruct obs.
  - econstructor. apply HEQ. red. split; auto. rewrite itree_eta. rewrite <- Heqobs. constructor 1. reflexivity.
  - econstructor. gbase. apply CIH.
    setoid_rewrite itree_eta in HEQ.
    destruct (observe ta); inversion Heqobs. subst.
    assert (Tau t0 ≈ t0) by apply tau_eutt.
    setoid_rewrite H in HEQ.
    auto.
  - econstructor.  intros. red. gbase. apply CIH.
    intros. apply HEQ.
    rewrite itree_eta. rewrite <- Heqobs.
    red in PR. destruct PR.
    red. split; auto.
    econstructor 3. reflexivity. apply H0.
Qed.

Lemma eutt_EQ_REL_Reflexive {E} {A} (ta : itree E A) : eutt (EQ_REL ta) ta ta.
Proof.
  apply eutt_EQ_REL_Reflexive_.
  auto.
Qed.

Definition RET_EQ {E} {A} (ta : itree E A) : A -> A -> Prop :=
  fun x y => Leaf x ta /\ Leaf y ta.

(* Figure 7: 3rd monad law, one direction bind associativity *)
Lemma bind_bind_iforest
  : forall {E} (A B C : Type) (PA : iforest E A)
      (KB : A -> iforest E B) (KC : B -> iforest E C)
      (PQOK : eutt_closed PA)
      (KBP : Proper (eq ==> eq1) KB)
      (KCP : Proper (eq ==> eq1) KC)
      (t : itree E C),
      (bind (bind PA KB) KC) t -> (bind PA (fun a => bind (KB a) KC)) t.
Proof.
  (* PA ~a> KB a ~b> KC b *)
  intros E A B C PA KB KC PQOK KBP KCP t eqtt'.
      red in eqtt'.
      destruct eqtt' as (tb & kbc & (HBC & EQc & HRkbc)).
      destruct HBC as (ta & kab & HTA & EQb & HRkab).
      red. exists ta. exists (fun a => ITree.bind (kab a) kbc).
      split; [auto|]; split.
      * setoid_rewrite EQc; clear EQc.
        setoid_rewrite EQb. setoid_rewrite EQb in HRkbc; clear EQb tb.
        unfold bind, Monad_itree.
        rewrite Eqit.bind_bind. reflexivity.
      * intros a HRet.
        exists (kab a), kbc.
        split; [auto|];split.
        -- reflexivity.
        -- intros b HRET. apply HRkbc. rewrite EQb. eapply Leaf_bind; eauto.
Qed.

Module BIND_BIND_COUNTEREXAMPLE.

  Inductive ND : Type -> Prop :=
  | Pick : ND bool.

  Definition PA : iforest ND bool := fun (ta : itree ND bool) => ta ≈ trigger Pick.

  Definition KB : bool -> iforest ND bool :=
    fun b => PA.

  Definition KC : bool -> iforest ND bool :=
    fun b => if b then (fun tc : itree ND bool => (tc ≈ ret true) \/ (tc ≈ ret false)) else (fun tc : itree ND bool => tc ≈ ITree.spin).

  Definition t : itree ND bool :=
    bind (trigger Pick) (fun (b:bool) => if b
                               then bind (trigger Pick) (fun (x:bool) => if x then ret true else ITree.spin)
                               else bind (trigger Pick) (fun (x:bool)  => if x then ret false else ITree.spin)).

  Lemma bind_right_assoc : bind PA (fun a => bind (KB a) KC) t.
  Proof.
    repeat red.
    exists (trigger Pick).
    exists (fun (b:bool) => if b
             then (bind (trigger Pick) (fun (x:bool) => if x then ret true else ITree.spin))
             else (bind (trigger Pick) (fun (x:bool) => if x then ret false else ITree.spin))).
    split; auto.
    red. reflexivity.
    split. reflexivity.
    intros. repeat red. exists (trigger Pick).
    exists (fun (x:bool) => if a
                 then (if x then ret true else ITree.spin)
                 else (if x then ret false else ITree.spin)).
    split.
    red. red.  reflexivity.
    split.
    destruct a.
    - reflexivity.
    - reflexivity.
    - intros.
      destruct a0.
      destruct a.
      red. left. reflexivity.
      red. right. reflexivity.
      destruct a.
      red. reflexivity. red.  reflexivity.
  Qed.

  Lemma not_bind_left_assoc : ~ (bind (bind PA KB) KC t).
  Proof.
    intro H.
    repeat red in H.
    destruct H as (ta & k & HB & HEQ & HRET).
    destruct HB as (tb & kb & HX & HEQ' & HRET').
    red in HX.
    rewrite HX in *.
    setoid_rewrite HX in HRET'.
    clear tb HX.
    rewrite HEQ' in HEQ.
    unfold t in HEQ.
    unfold bind, Monad_itree in HEQ.
    rewrite Eqit.bind_bind in HEQ.
    assert (forall r, Leaf r (ITree.trigger Pick) -> eutt eq ((fun b : bool =>
           if b
           then ITree.bind (trigger Pick) (fun x : bool => if x then ret true else ITree.spin)
           else ITree.bind (trigger Pick) (fun x : bool => if x then ret false else ITree.spin)) r) ((fun r : bool => ITree.bind (kb r) k) r)).
    apply eqit_bind_Leaf_inv. apply HEQ.
    assert (Leaf true (ITree.trigger Pick)).
    { unfold trigger. econstructor 3. reflexivity. constructor 1. reflexivity. }
    assert (Leaf false (ITree.trigger Pick)).
    { unfold trigger. econstructor 3. reflexivity. constructor 1. reflexivity. }
    assert (Leaf true (ITree.trigger Pick)).
    { unfold trigger. econstructor 3. reflexivity. constructor 1. reflexivity. }
    assert (Leaf false (ITree.trigger Pick)).
    { unfold trigger. econstructor 3. reflexivity. constructor 1. reflexivity. }
    apply H in H0.
    apply H in H1.
    apply HRET' in H2.
    apply HRET' in H3.
    red in H2. red in H3. red in H2. red in H3.
    rewrite H2 in H0.
    rewrite H3 in H1.
    rewrite <- H0 in H1.
    apply eqit_bind_Leaf_inv with (r := true) in H1 .
    apply eqit_inv_Ret in H1. inversion H1.
    { unfold trigger. econstructor 3. reflexivity. constructor 1. reflexivity. }
Qed.

Lemma bind_bind_counterexample:
    exists t, bind PA (fun a => bind (KB a) KC) t /\ ~ (bind (bind PA KB) KC t).
Proof.
  exists t.
  split.
  apply bind_right_assoc.
  apply not_bind_left_assoc.
Qed.

End BIND_BIND_COUNTEREXAMPLE.
