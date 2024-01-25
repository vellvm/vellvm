From ITree Require Import
  Basics.HeterogeneousRelations.

From Coq Require Import
  Lia
  RelationClasses
  Relation_Definitions
  Relations
  Relations.Relation_Operators
  Program.Equality.

Infix"×" := prod_rel (at level 90, left associativity).

Definition TT {A} : relation A := fun _ _ => True.

#[global] Instance TT_Reflexive {A} : Reflexive (@TT A).
Proof.
  intro.
  reflexivity.
Qed.

#[global] Instance TT_Transitive {A} : Transitive (@TT A).
Proof.
  intro.
  auto.
Qed.

#[global] Instance TT_Symmetric {A} : Symmetric (@TT A).
Proof.
  intro.
  auto.
Qed.

#[global] Instance TT_Equivalence {A} : Equivalence (@TT A).
Proof.
  split; typeclasses eauto.
Qed.

Lemma clos_t_rt :
  forall {A: Type} {R : relation A}
    {x y : A},
    clos_trans A R x y ->
    clos_refl_trans A R x y.
Proof.
  intros A R x y H.
  induction H.
  - apply rt_step; auto.
  - eapply rt_trans; eauto.
Qed.

Lemma clos_t_rt_t :
  forall {A: Type} {R : relation A}
    {x y z : A},
    clos_trans A R x y ->
    clos_refl_trans A R y z ->
    clos_trans A R x z.
Proof.
  intros A R x y z T RT.
  induction RT; subst; auto.
  eapply t_trans; eauto.
  apply t_step; auto.
Qed.

Lemma clos_t_rt_inv :
  forall {A : Type} {R : relation A} {x y : A},
    clos_trans A R x y ->
    exists z, R z y /\ clos_refl_trans A R x z.
Proof.
  intros A R x y SUB.
  dependent induction SUB.
  - exists x.
    split; eauto.
    apply rt_refl.
  - clear IHSUB1.
    destruct IHSUB2 as (?&?&?).
    exists x0.
    split; auto.
    eapply rt_trans.
    apply clos_t_rt; eauto.
    eauto.
Qed.

Lemma clos_rt_t_inv :
  forall {A : Type} {R : relation A} {x y : A},
    clos_refl_trans A R x y ->
    x=y \/ R x y \/ clos_trans A R x y.
Proof.
  intros A R x y RT.
  dependent induction RT; auto.

  destruct IHRT1 as [? | [? | ?]]; subst; auto;
    destruct IHRT2 as [? | [? | ?]]; subst; auto;
    right; right;
    eapply t_trans; eauto;
    apply t_step; eauto.
Qed.

Lemma clos_rt_inv :
  forall {A : Type} {R : relation A} {x y : A},
    clos_refl_trans A R x y ->
    x=y \/ exists z, R z y /\ clos_refl_trans A R x z.
Proof.
  intros A R x y SUB.
  eapply clos_rt_t_inv in SUB.
  destruct SUB as [? | [? | ?]]; subst; auto.
  - right.
    exists x; split; eauto.
    apply rt_refl.
  - apply clos_t_rt_inv in H.
    auto.
Qed.

Lemma clos_trans_measure :
  forall {A} {R : relation A} m,
    (forall a b, R a b -> (m a < m b)%nat) ->
    (forall a b, @clos_trans A R a b -> (m a < m b)%nat).
Proof.
  intros A R m MR a b MT.
  eapply clos_trans_t1n_iff in MT.
  dependent induction MT; eauto.
  enough (m x < m y)%nat by lia; eauto.
Qed.

Lemma clos_trans_not_refl :
  forall {A} {R : relation A} m,
    (forall a b, R a b -> (m a < m b)%nat) ->
    (forall a, ~ @clos_trans A R a a).
Proof.
  intros A R m NSYM a CONTRA.
  eapply clos_trans_measure in CONTRA; eauto.
  lia.
Qed.

Lemma clos_trans_not_sym :
  forall {A} {R : relation A} m,
    (forall a b, R a b -> (m a < m b)%nat) ->
    (forall a b, @clos_trans A R a b -> ~ @clos_trans A R b a).
Proof.
  intros A R m NSYM a b M CONTRA.
  eapply clos_trans_measure in CONTRA; eauto.
  eapply clos_trans_measure in M; eauto.
  lia.
Qed.

Lemma clos_refl_trans_antisymmetric :
  forall {A} {R : relation A} m,
    (forall a b, R a b -> (m a < m b)%nat) ->
    forall a b,
      @clos_refl_trans A R a b ->
      @clos_refl_trans A R b a ->
      a = b.
Proof.
  intros A R m M a b AB BA.
  eapply clos_rt_t_inv in AB.
  destruct AB as [AB | [AB | AB]]; auto.
  - eapply clos_rt_t_inv in BA.
    destruct BA as [BA | [BA | BA]]; subst; auto; exfalso.
    + apply M in AB, BA; lia.
    + apply t_step in AB.
      eapply clos_trans_not_sym; eauto.
  - eapply clos_rt_t_inv in BA.
    destruct BA as [BA | [BA | BA]]; subst; auto; exfalso.
    + apply t_step in BA; auto.
      eapply clos_trans_not_sym; eauto.
    + eapply clos_trans_not_sym; eauto.
Qed.
