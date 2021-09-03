From ITree Require Import
     Basics.Monad.

From ExtLib Require Import
     Structures.Monads.

(* (* Canonical equivalence relation for a unary type family. *) *)
(* Class Eq1 (M : Type -> Type) : Type := *)
(*   eq1 : forall A, M A -> M A -> Prop. *)

(* (* Proof that [eq1] is an equivalence relation. *) *)
(* Class Eq1Equidedvalence (M : Type -> Type) `{Monad M} `{Eq1 M} := *)
(*   eq1_equiv :> forall A, Equivalence (eq1 A). *)

(* Arguments eq1 {M _ _}. *)
(* Infix "≈" := eq1 (at level 70) : monad_scope. *)

Section Laws.

  Context (M : Type -> Type).
  Context {Eq1 : @Eq1 M}.
  Context {Monad : Monad M}.
  Variable E : Type.
  Context {MonadExc : MonadExc E M}.

  Local Open Scope monad_scope.

  Class MonadExcLaws : Prop :=
    { raise_bind : forall A B (f : A -> M B) (x : E), bind (raise x) f ≈ raise x;
      raise_catch : forall A (handler : E -> M A) (x : E) , catch (raise x) handler ≈ handler x
    }.

End Laws.

Arguments raise_bind {M _ _ _ _ _}.
Arguments raise_catch {M _ _ _ _ _}.

(* Separate file? *)

Section Either.
  Variable T : Type.
  Variable E : Type.

  Import Monad.
  Global Instance Eq1_either : Eq1 (sum E) :=
    { eq1 := fun a => Logic.eq }.

  Arguments eq1 {M _ _}.
  Infix "≈" := eq1 (at level 70) : monad_scope.

  Open Scope monad_scope.

  Import EitherMonad.
  Lemma raise_bind_either :
    forall A B (f : A -> sum E B) (x : E),
      bind (raise x) f ≈ raise x.
  Proof.
    intros A B f x.
    cbn.
    reflexivity.
  Qed.

  Lemma raise_catch_either :
    forall A (handler : E -> sum E A) (x : E) , catch (raise x) handler ≈ handler x.
  Proof.
    intros A handler x.
    reflexivity.
  Qed.

  Global Instance MonadExcLaws_either : MonadExcLaws (sum E) E :=
    { raise_bind := raise_bind_either;
      raise_catch := raise_catch_either;
    }.

End Either.
