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
