From Coq Require Import
     String
     Morphisms.

From ExtLib Require Import
     Structures.Monads.

From ITree Require Import
     Basics.Basics
     Basics.Monad
     Eq
     ITree.

From Vellvm Require Import 
     Semantics.LLVMEvents
     Utils.MonadRefactored
     Utils.MonadRefactoredTheory.

Require Import Paco.paco.

Section Laws.
  Variable M : Type -> Type.
  Context `{HM : Monad M}.
  Context `{EQM : Eq1 M}.
  Variable MSG : Type.
  Variable rbm_raise : forall {X}, MSG -> M X.

  Class RaiseBindM :=
    { rbm_raise_bind :
      forall A B (f : A -> M B) (x : MSG),
        eq1 (bind (rbm_raise x) f) (rbm_raise x);
      rbm_raise_ret_inv :
      forall A (x : MSG) (y : A),
        ~ eq1 (rbm_raise x) (ret y);
    }.
End Laws.

Section Failure.
  Variable E : Type -> Type.
  Context {FAIL : FailureE -< E}.

  Lemma raise_bind_itree :
    forall A B (f : A -> itree E B) x,
      bind (raise x) f ≈ raise x.
  Proof.
    intros A B f x.
    unfold raise.
    cbn.
    rewrite bind_bind.
    eapply eutt_clo_bind.
    reflexivity.
    intros u1 u2 H.
    destruct u1.
  Qed.

  Lemma raise_map_itree :
    forall A B (f : A -> B) x,
      ITree.map f (raise x) ≈ raise x.
  Proof.
    intros A B f x.
    unfold raise.
    rewrite map_bind.
    eapply eutt_clo_bind.
    reflexivity.
    intros [].
  Qed.

  Lemma raise_ret_inv_itree :
      forall A x (y : A),
        ~ (raise x) ≈ (ret y).
  Proof.
    intros A x y.
    intros CONTRA.
    cbn in CONTRA.
    pinversion CONTRA.
  Qed.

  #[global] Instance RaiseBindM_Fail : RaiseBindM (itree E) string (fun T => raise) :=
    { rbm_raise_bind := raise_bind_itree;
      rbm_raise_ret_inv := raise_ret_inv_itree;
    }.
End Failure.

Section OOM.
  Variable E : Type -> Type.
  Context {OOM : OOME -< E}.

  Lemma raiseOOM_bind_itree :
    forall A B (f : A -> itree E B) x,
      bind (raiseOOM x) f ≈ raiseOOM x.
  Proof.
    intros A B f x.
    unfold raiseOOM.
    cbn.
    rewrite bind_bind.
    eapply eutt_clo_bind.
    reflexivity.
    intros u1 u2 H.
    destruct u1.
  Qed.

  Lemma raiseOOM_map_itree :
    forall A B (f : A -> B) x,
      ITree.map f (raiseOOM x) ≈ raiseOOM x.
  Proof.
    intros A B f x.
    unfold raiseOOM, raise.
    rewrite map_bind.
    eapply eutt_clo_bind.
    reflexivity.
    intros [].
  Qed.

  Lemma raiseOOM_ret_inv_itree :
      forall A x (y : A),
        ~ (raiseOOM x) ≈ (ret y).
  Proof.
    intros A x y.
    intros CONTRA.
    cbn in CONTRA.
    pinversion CONTRA.
  Qed.

  #[global] Instance RaiseBindM_OOM : RaiseBindM (itree E) string (fun T => raiseOOM) :=
    { rbm_raise_bind := raiseOOM_bind_itree;
      rbm_raise_ret_inv := raiseOOM_ret_inv_itree;
    }.
End OOM.

Section UB.
  Variable E : Type -> Type.
  Context {UB : UBE -< E}.

  Lemma raiseUB_bind_itree :
    forall A B (f : A -> itree E B) x,
      bind (raiseUB x) f ≈ raiseUB x.
  Proof.
    intros A B f x.
    unfold raiseUB.
    cbn.
    rewrite bind_bind.
    eapply eutt_clo_bind.
    reflexivity.
    intros u1 u2 H.
    destruct u1.
  Qed.

  Lemma raiseUB_map_itree :
    forall A B (f : A -> B) x,
      ITree.map f (raiseUB x) ≈ raiseUB x.
  Proof.
    intros A B f x.
    unfold raiseUB, raise.
    rewrite map_bind.
    eapply eutt_clo_bind.
    reflexivity.
    intros [].
  Qed.

  Lemma raiseUB_ret_inv_itree :
      forall A x (y : A),
        ~ (raiseUB x) ≈ (ret y).
  Proof.
    intros A x y.
    intros CONTRA.
    cbn in CONTRA.
    pinversion CONTRA.
  Qed.

  #[global] Instance RaiseBindM_UB : RaiseBindM (itree E) string (fun T => raiseUB) :=
    { rbm_raise_bind := raiseUB_bind_itree;
      rbm_raise_ret_inv := raiseUB_ret_inv_itree;
    }.
End UB.
