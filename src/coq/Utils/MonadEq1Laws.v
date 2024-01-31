From Coq Require Import
     Morphisms.

From ITree Require Import
     Basics.Basics
     Basics.Monad
     ITree.

From ExtLib Require Import
     Data.Monads.IdentityMonad.

From Vellvm.Utils Require Import Monads MonadExcLaws.

Section Laws.

  Context (M : Type -> Type).
  Context {Eq1 : @Eq1 M}.
  Context {Monad : Monad M}.

  Local Open Scope monad_scope.

  Class Eq1_ret_inv : Prop :=
    { eq1_ret_ret : forall {A} (x y : A), ret x ≈ ret y -> x = y }.

End Laws.

Open Scope monad_scope.

Section Ident.
  Lemma eq1_ret_ret_ident :
    forall {A} (x y : A), (ret x : ident A) ≈ ret y -> x = y.
  Proof using.
    intros A x y EQ.
    unfold Monad.eq1, Eq1_either in EQ.
    inversion EQ.
    reflexivity.
  Qed.

  Global Instance Eq1_ret_inv_ident : Eq1_ret_inv ident :=
    { eq1_ret_ret := fun a => eq1_ret_ret_ident }.

End Ident.

Section Either.
  Variable E : Type.

  Lemma eq1_ret_ret_either:
    forall {A} (x y : A), (ret x : sum E A) ≈ ret y -> x = y.
  Proof using.
    intros A x y EQ.
    unfold Monad.eq1, Eq1_either in EQ.
    inversion EQ.
    reflexivity.
  Qed.

  Global Instance Eq1_ret_inv_either : Eq1_ret_inv (sum E) :=
    { eq1_ret_ret := fun a => eq1_ret_ret_either }.

End Either.

Section EitherT.
  Variable E : Type.
  Variable M : Type -> Type.
  Context {HM : Monad M}.
  Context {EQM : Eq1 M}.
  Context {RINV : @Eq1_ret_inv M EQM HM}.

  Import EitherMonad.

  Lemma eq1_ret_ret_eitherT:
    forall {A} (x y : A), (ret x : eitherT E M A) ≈ ret y -> x = y.
  Proof using All.
    intros A x y EQ.
    unfold Monad.eq1, Eq1_eitherT in EQ.
    destruct RINV.
    specialize (eq1_ret_ret0 _ _ _ EQ).
    inversion eq1_ret_ret0.
    reflexivity.
  Qed.

  Global Instance Eq1_ret_inv_eitherT : Eq1_ret_inv (eitherT E M) :=
    { eq1_ret_ret := fun a => eq1_ret_ret_eitherT }.

End EitherT.

Section ITree.
  Variable E : Type -> Type.
  Require Import ITree.Core.ITreeMonad.

  Lemma eq1_ret_ret_itree :
    forall {A} (x y : A), (ret x : itree E A) ≈ ret y -> x = y.
  Proof using.
    intros A x y EQ.
    eapply Eqit.eutt_inv_Ret.
    cbn in EQ.
    eapply EQ.
  Qed.

  Global Instance Eq1_ret_inv_itree : Eq1_ret_inv (itree E) :=
    { eq1_ret_ret := fun a => eq1_ret_ret_itree }.
End ITree.
