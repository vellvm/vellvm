From Vellvm.Utils Require Import
     Monads.

From ExtLib Require Import
     Structures.Monads.

From Coq Require Import
     Relations
     RelationClasses
     Morphisms.

Import Monad.
Import MonadNotation.
Open Scope monad_scope.

(* Whether a monadic computation M contains something in B *)
Class Within {M : Type -> Type} `{EQM : Eq1 M} (B : Type -> Type) (PreState PostState : Type) : Type :=
  { within {A} (m : M A) (pre : PreState) (b : B A) (post : PostState) : Prop;
    within_eq1_Proper {A} :>
      Proper (@eq1 M EQM A ==> eq ==> eq ==> eq ==> iff) within;
  }.

Notation "b ∈ m" := (exists pre post, within m pre b post) (at level 99).
Notation "b ∉ m" := (~ (exists pre post, within m pre b post)) (at level 99).
Notation "b ⦉ pre ⦊ ∈ ⦉ post ⦊ m" := (within m pre b post) (at level 99).
Notation "b ⦉ pre ⦊ ∉ ⦉ post ⦊ m" := (~ (within m pre b post)) (at level 99).
Notation "b {{ pre }} ∈ {{ post }} m" := (within m pre b post) (at level 99).
Notation "b {{ pre }} ∉ {{ post }} m" := (~ (within m pre b post)) (at level 99).    

Section Laws.
  Variable M : Type -> Type.
  Variable B : Type -> Type.
  Variable Pre Post : Type.
  Context `{HM : Monad M}.
  Context `{HMB : Monad B}.
  Context `{EQM : Eq1 M}.
  Context `{WM : @Within M EQM B Pre Post}.
  Variable MSG : Type.
  Variable rw_raise : forall {X}, MSG -> M X.

  Class RaiseWithin :=
    { rw_ret_nin_raise :
      forall X (msg : MSG) (x : X),
        @ret B HMB X x ∉ @rw_raise X msg;
    }.

End Laws.

Section Laws.
  Variable M : Type -> Type.
  Variable B : Type -> Type.
  Variable Pre Post : Type.
  Context `{HM : Monad M}.
  Context `{HMB : Monad B}.
  Context `{EQM : Eq1 M}.
  Context `{WM : @Within M EQM B Pre Post}.
  Variable MSG : Type.
  Variable rw_raise : forall {X}, MSG -> B X.

  Class RetWithin :=
    { rw_raise_nin_ret :
      forall X (msg : MSG) (x : X),
        @rw_raise X msg ∉ ret x;
    }.

End Laws.

Section Laws.
  Variable M : Type -> Type.
  Variable B : Type -> Type.
  Variable Pre Post : Type.
  Context `{HM : Monad M}.
  Context `{HMB : Monad B}.
  Context `{EQM : Eq1 M}.
  Context `{WM : @Within M EQM B Pre Post}.
  Variable MSG : Type.
  Variable raise1 : forall {X}, MSG -> B X.
  Variable raise2 : forall {X}, MSG -> M X.

  Class DisjointRaiseWithin :=
    { disjoint_raise_within :
      forall X (msg1 msg2 : MSG),
        @raise1 X msg1 ∉ @raise2 X msg2;
    }.

End Laws.

Section Laws.
  Variable M : Type -> Type.
  Variable B : Type -> Type.
  Variable Pre Post : Type.
  Context `{HM : Monad M}.
  Context `{HMB : Monad B}.
  Context `{EQM : Eq1 M}.
  Context `{WM : @Within M EQM B Pre Post}.

  Class Within_ret_inv : Prop :=
    { within_ret_ret : forall {A} (x y : A), ret x ∈ ret y -> x = y;
      within_ret_refl : forall {A} (x : A), ret x ∈ ret x;
    }.
End Laws.

Definition transitive_within {Pre Post} {M1 M2 M3} `{EQM2 : Eq1 M2} `{EQM3 : Eq1 M3} `{WM1M2 : @Within M2 EQM2 M1 Pre Post} `{WM2M3 : @Within M3 EQM3 M2 Pre Post}
  {A} (m3 : M3 A) (pre : Pre) (m1 : M1 A) (post : Post) : Prop :=
  exists (m2 : M2 A),
    (m1 {{pre}} ∈ {{post}} m2) /\
      (m2 {{pre}} ∈ {{post}} m3).

Definition transitive_within_eq1_Proper {Pre Post} {M1 M2 M3} `{EQM2 : Eq1 M2} `{EQM3 : Eq1 M3} `{WM1M2 : @Within M2 EQM2 M1 Pre Post} `{WM2M3 : @Within M3 EQM3 M2 Pre Post} {A} :
  Proper (eq1 ==> eq ==> eq ==> eq ==> iff) (transitive_within (A:=A)).
Proof.
  unfold Proper, respectful.
  intros x y H x0 y0 H0 x1 y1 H1 x2 y2 H2.
  subst.
  unfold transitive_within.
  split; intros [m2 [INM2 INM3]].
  - rewrite H in INM3.
    exists m2; split; auto.
  - rewrite <- H in INM3.
    exists m2; split; auto.
Defined.

#[global] Instance Transitive_Within {Pre Post} {M1 M2 M3} `{EQM2 : Eq1 M2} `{EQM3 : Eq1 M3} `{WM1M2 : @Within M2 EQM2 M1 Pre Post} `{WM2M3 : @Within M3 EQM3 M2 Pre Post} : @Within M3 EQM3 M1 Pre Post.
Proof.
  esplit.
  intros A.
  unfold Proper, respectful.
  intros x y H x0 y0 H0 x1 y1 H1 x2 y2 H2.
  eapply transitive_within_eq1_Proper; eauto.
Defined.

Definition reflexive_within {Pre Post} {M} `{EQM : Eq1 M}
  {A} (m : M A) (pre : Pre) (m' : M A) (post : Post) : Prop :=
  m ≈ m'.

Definition reflexive_within_eq1_Proper {Pre Post} {M} `{MM : Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M MM EQM} {A} :
  Proper (eq1 ==> eq ==> eq ==> eq ==> iff) (reflexive_within (Pre:=Pre) (Post:=Post) (A:=A)).
Proof.
  unfold Proper, respectful.
  intros x y H x0 y0 H0 x1 y1 H1 x2 y2 H2.
  subst.
  unfold reflexive_within.
  split; intros EQ.
  - rewrite <- H.
    auto.
  - rewrite H.
    auto.
Defined.

#[global] Instance Reflexive_Within {Pre Post} {M} `{MM : Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M MM EQM} : @Within M EQM M Pre Post.
Proof.
  esplit.
  intros A.
  unfold Proper, respectful.
  intros x y H x0 y0 H0 x1 y1 H1 x2 y2 H2.
  eapply reflexive_within_eq1_Proper; eauto.
Defined.
