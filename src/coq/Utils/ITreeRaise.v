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
     Semantics.LLVMEvents.

Section Laws.
  Variable E : Type -> Type.
  Variable MSG : Type.

  Class RaiseBindItree :=
    { rbi_raise : forall {X}, MSG -> itree E X;
      rbi_raise_bind :
      forall A B (f : A -> itree E B) (x : MSG),
        bind (rbi_raise x) f ≈ rbi_raise x      
    }.
End Laws.

Section Failure.
  Variable E : Type -> Type.
  Context {FAIL : FailureE -< E}.

  Lemma raise_bind_itree :
    forall A B (f : A -> itree E B) x,
      bind (raise x) f ≈ raise x.
  Proof using.
    intros A B f x.
    unfold raise.
    cbn.
    rewrite bind_bind.
    eapply eutt_clo_bind.
    reflexivity.
    intros u1 u2 H.
    destruct u1.
  Qed.

  Global Instance RaiseBindItree_Fail : RaiseBindItree E string :=
    { rbi_raise := fun X => raise;
      rbi_raise_bind := raise_bind_itree
    }.
End Failure.

Section OOM.
  Variable E : Type -> Type.
  Context {OOM : OOME -< E}.

  Lemma raiseOOM_bind_itree :
    forall A B (f : A -> itree E B) x,
      bind (raiseOOM x) f ≈ raiseOOM x.
  Proof using.
    intros A B f x.
    unfold raiseOOM.
    cbn.
    rewrite bind_bind.
    eapply eutt_clo_bind.
    reflexivity.
    intros u1 u2 H.
    destruct u1.
  Qed.

  Global Instance RaiseBindItree_OOM : RaiseBindItree E string :=
    { rbi_raise := fun X => raiseOOM;
      rbi_raise_bind := raiseOOM_bind_itree
    }.
End OOM.

Section UB.
  Variable E : Type -> Type.
  Context {UB : UBE -< E}.

  Lemma raiseUB_bind_itree :
    forall A B (f : A -> itree E B) x,
      bind (raiseUB x) f ≈ raiseUB x.
  Proof using.
    intros A B f x.
    unfold raiseUB.
    cbn.
    rewrite bind_bind.
    eapply eutt_clo_bind.
    reflexivity.
    intros u1 u2 H.
    destruct u1.
  Qed.

  Global Instance RaiseBindItree_UB : RaiseBindItree E string :=
    { rbi_raise := fun X => raiseUB;
      rbi_raise_bind := raiseUB_bind_itree
    }.
End UB.

