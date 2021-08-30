From Coq Require Import
     List.

From ExtLib Require Import
     Structures.Monads.

From ITree Require Import
     Basics.Monad. 

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

Lemma map_monad_In_unfold :
  forall {A B M} `{Monad M} (x : A) (xs : list A) (f : forall (elt:A), In elt (x::xs) -> M B),
    map_monad_In (x::xs) f = b <- f x (or_introl eq_refl);;
                            bs <- map_monad_In xs (fun x HIn => f x (or_intror HIn));;
                            ret (b :: bs).
Proof.
  intros A B M H x xs f.
  induction xs; cbn; auto.
Qed.
