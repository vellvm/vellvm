From ExtLib Require Import
     Structures.Monads
     Structures.Functor.

From ITree Require Import
     ITree.

Import Basics.Basics.Monads.

From Vellvm Require Import Utils.Monads.

Import MonadNotation.

(* TODO: move this? *)
Definition runStateT {S M A} `{Monad M} (m: stateT S M A) (s : S) : M (A * S)%type
  := '(s', a) <- m s;;
     ret (a, s').

Definition evalStateT {S M A} `{Monad M} (m: stateT S M A) (s : S) : M A
  := fmap fst (runStateT m s).

Global Instance MonadT_stateT_itree {S : Type} {M : Type -> Type} `{Monad M} : MonadT (stateT S M) M
  := {| lift := fun (t : Type) (c : M t) => fun s => t0 <- c;; ret (s, t0) |}.

Global Instance MonadState_stateT_itree {S : Type} {M : Type -> Type} `{Monad M} : MonadState S (stateT S M)
  := {| MonadState.get := fun s => ret (s, s);
        MonadState.put := fun x s => ret (x, tt);
     |}.

