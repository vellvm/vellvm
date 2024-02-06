From Coq Require Import
     Morphisms.

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

  Class RaiseBind : Prop :=
    { raise_bind : forall A B (f : A -> M B) (x : E), bind (raise x) f ≈ raise x }.

  Class RaiseCatch : Prop :=
    { raise_catch : forall A (handler : E -> M A) (x : E) , catch (raise x) handler ≈ handler x }.

  Class MonadExcLaws `{RB : RaiseBind} `{RC : RaiseCatch} : Prop.
  Global Instance MonadExcLaws_rb_rc `{RB : RaiseBind} `{RC : RaiseCatch} : MonadExcLaws.
  Defined.
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
  Proof using.
    intros A B f x.
    cbn.
    reflexivity.
  Qed.

  Lemma raise_catch_either :
    forall A (handler : E -> sum E A) (x : E) , catch (raise x) handler ≈ handler x.
  Proof using.
    intros A handler x.
    reflexivity.
  Qed.

  Global Instance RaiseBind_either : RaiseBind (sum E) E :=
    { raise_bind := raise_bind_either }.

  Global Instance RaiseCatch_either : RaiseCatch (sum E) E :=
    { raise_catch := raise_catch_either }.

End Either.

Section EitherT.
  Variable T : Type.
  Variable E : Type.
  Variable M : Type -> Type.
  Context {HM : Monad M}.
  Context {EQM : Eq1 M}.
  Context {EQE : Eq1Equivalence M}.
  Context {MLAWS : MonadLawsE M}.

  Import EitherMonad.

  Global Instance Eq1_eitherT `{Eq1 M} : Eq1 (eitherT E M) :=
    { eq1 :=
        fun a x y =>
          eq1 (unEitherT x) (unEitherT y)
    }.

  Arguments eq1 {M _ _}.
  Infix "≈" := eq1 (at level 70) : monad_scope.

  Context {proper_eq1_mkEitherT : forall {A}, Proper (@eq1 M EQM (E + A) ==> @eq1 (eitherT E M) _ A) mkEitherT}.

  Open Scope monad_scope.



  (* Instance proper_eq1_mkEitherT : forall {A}, Proper (@eq1 M EQM (E + A) ==> @eq1 (eitherT E M) _ A) mkEitherT. *)
  (* Proof using. *)
  (*   intros A. *)
  (*   unfold Proper. *)
  (*   unfold respectful. *)
  (*   unfold eq1. *)
  (*   unfold Eq1_eitherT. *)
  (*   intros x y H. *)
  (* Admitted. *)



  Lemma raise_bind_eitherT :
    forall A B (f : A -> eitherT E M B) (x : E),
      bind (raise x) f ≈ raise x.
  Proof using E EQM HM M MLAWS proper_eq1_mkEitherT.
    intros A B f x.
    cbn.
    destruct MLAWS.
    unfold Proper, respectful in proper_eq1_mkEitherT.
    pose proof bind_ret_l _ _ (fun xM : E + A => match xM with
                                                   | inl x0 => ret (inl x0)
                                                   | inr x0 => unEitherT (f x0)
                                              end) (inl x).

    epose proof (proper_eq1_mkEitherT _ _ _ H).
    apply H0.
  Qed.

  Lemma raise_catch_eitherT :
    forall A (handler : E -> eitherT E M A) (x : E) , catch (raise x) handler ≈ handler x.
  Proof using E EQM HM M MLAWS proper_eq1_mkEitherT.
    intros A handler x.
    cbn.
    unfold Proper, respectful in proper_eq1_mkEitherT.
    pose proof bind_ret_l _ _ (fun xM : E + A => match xM with
                                                   | inl x0 => unEitherT (handler x0)
                                                   | inr x0 => ret (inr x0)
                                              end) (inl x).

    epose proof (proper_eq1_mkEitherT _ _ _ H).

    apply H0.
  Qed.

  Global Instance RaiseBind_eitherT : RaiseBind (eitherT E M) E :=
    { raise_bind := raise_bind_eitherT }.

  Global Instance RaiseCatch_eitherT : RaiseCatch (eitherT E M) E :=
    { raise_catch := raise_catch_eitherT }.

End EitherT.
