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


Section Itree.
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
End Itree.
