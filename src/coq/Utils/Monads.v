From Coq Require Import
     List.

From ExtLib Require Import
     Structures.Monads.

Import MonadNotation.
Import ListNotations.

Open Scope monad.

Fixpoint foldM {a b} {M} `{Monad M} (f : b -> a -> M b ) (acc : b) (l : list a) : M b
  := match l with
     | [] => ret acc
     | (x :: xs) =>
       b <- f acc x;;
       foldM f b xs
     end.

Lemma map_monad_In {m : Type -> Type} {H : Monad m} {A B} (l : list A) (f: forall (x : A), In x l -> m B) : m (list B).
Proof.
  induction l.
  - exact (ret []).
  - refine (b <- f a _;; bs <- IHl _;; ret (b::bs)).
    + cbn; auto.
    + intros x Hin.
      apply (f x).
      cbn; auto.
Defined.
