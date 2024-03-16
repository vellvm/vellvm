From Vellvm.Utils Require Import
  Monads.

Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Traversable.
Import MonadNotation.
Import ApplicativeNotation.
Import FunctorNotation.

Record Const (a b : Type) : Type := mkConst { getConst : a }.
Arguments mkConst {_ _}.
Arguments getConst {_ _}.

Instance Const_Functor {a} : Functor (Const a).
split.
intros A B X X0.
destruct X0.
apply (mkConst getConst0).
Defined.

Definition ASetter s t a b := (a -> IdentityMonad.ident b) -> s -> IdentityMonad.ident t.
Definition ASetter' s a := (a -> IdentityMonad.ident a) -> s -> IdentityMonad.ident s.
Definition LensLike (f : Type -> Type) s t a b := (a -> f b) -> s -> f t.
Definition Lens s t a b := forall {f} `{F: Functor f}, (a -> f b) -> s -> f t.
Definition Lens' s a := forall {f} `{F: Functor f}, (a -> f a) -> s -> f s.
Definition Traversal s t a b := forall {f} `{F: Applicative f}, (a -> f b) -> s -> f t.

Definition lift_Lens' {a b} (l : Lens' a b) : Lens a a b b := l.

Definition view {s t a b : Type} (l : Lens s t a b) (w : s) : a
  := (getConst (l _ _ mkConst w)).

Definition over {s t a b : Type} (l : ASetter s t a b) (f : a -> b) (w : s) : t
  := IdentityMonad.unIdent (l (fun x => IdentityMonad.mkIdent (f x)) w).

Definition setl {s t a b : Type} (l : ASetter s t a b) (v : b) (w : s) : t
  := IdentityMonad.unIdent (l (fun _ => IdentityMonad.mkIdent v) w).

Definition assign {m : Type -> Type} {s a b : Type} `{HM : Monad m} `{ST : @MonadState s m}
  (l : ASetter s s a b) (v : b) : m s
  := modify (setl l v).

Definition modifying {m : Type -> Type} {s a b : Type} `{HM : Monad m} `{ST : @MonadState s m}
  (l : ASetter s s a b) (f : a -> b) : m s
  := modify (over l f).

Definition use {m : Type -> Type} {s a : Type} `{HM : Monad m} `{ST : @MonadState s m}
  (l : Lens' s a) : m a
  := gets (view l).

Definition comp' {a b c} (l1 : Lens' a b) (l2 : Lens' b c) : Lens' a c.
  red in l1, l2.
  red.
  intros f F afa x.
  specialize (l1 f F).
  specialize (l2 f F).
  apply l1.
  - apply l2.
    apply afa.
  - apply x.
Defined.

Definition traversal {f s t a b} (tr : (a -> f b) -> s -> f t) : LensLike f s t a b
  := tr.

Definition lens_to_asetter {s t a b} : Lens s t a b -> ASetter s t a b.
  intros l.
  specialize (l IdentityMonad.ident _).
  red. apply l.
Defined.

Definition lens'_to_lens {s a} : Lens' s a -> Lens s s a a.
  intros l.
  apply l.
Defined.

#[global] Coercion lens_to_asetter : Lens >-> ASetter.
#[global] Coercion lens'_to_lens : Lens' >-> Lens.

Module LensNotations.
  Declare Scope lens_scope.
  Delimit Scope lens_scope with lens.
  Bind Scope lens_scope with Lens.

  Notation "X -l> Y" := (Lens X X Y Y)
    (at level 99, Y at level 200, right associativity) : type_scope.
  Notation "a & b" := (b a) (at level 50, only parsing, left associativity) : lens_scope.
  Notation "a %~ f" := (Lens.over a f) (at level 49, left associativity) : lens_scope.
  Notation "a .~ b" := (Lens.setl a b) (at level 49, left associativity) : lens_scope.
  Notation "a %= f" := (Lens.modifying a f) (at level 49, left associativity) : lens_scope.
  Notation "a .= b" := (Lens.assign a b) (at level 49, left associativity) : lens_scope.
  Notation "a .^ f" := (Lens.view f a) (at level 45, left associativity) : lens_scope.
  (* level 19 to be compatible with Iris .@ *)
  Notation "a .@ b" := (comp' a b) (at level 19, left associativity) : lens_scope.
End LensNotations.
