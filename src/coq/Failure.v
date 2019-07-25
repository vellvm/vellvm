From Coq Require Import
     String.

From Vellvm Require Import
     Error.

From ITree Require Import
     ITree
     Events.Exception.

(* Failures carry string *)
Definition FailureE := exceptE string.

Definition raise {E} {A} `{FailureE -< E} (msg : string) : itree E A :=
  throw msg.

Definition lift_err {A B} {E} `{FailureE -< E} (f : A -> itree E B) (m:err A) : itree E B :=
  match m with
  | inl x => throw x
  | inr x => f x
  end.


(*
Notation "'do' x <- m ;; f" := (lift_err (fun x => f) m)
                                (at level 100, x ident, m at next level, right associativity).


Definition raise_FailureE {E} `{failureE -< E} := @throw _ E _.
(*
CoFixpoint catch_FailureE {E F X} `{E -< F} `{failureE -< F}
           (f:string -> itree F X)
           (t : itree (failureE +' E) X) : itree F X :=
  match (observe t) with
  | RetF x => Ret x
  | TauF t => Tau (catch_FailureE f t)
  | VisF _ (inl1 (Throw s)) k => f s
  | VisF _ (inr1 e) k => vis e (fun x => catch_FailureE f (k x))
  end.

(* CB TODO: Can we have 1 instance of MonadExc? *)
Global Instance monad_exc_FailureE {E} : (MonadExc string (itree (failureE +' E))) := {
  raise := raise_FailureE ;
  catch := fun T m f => catch_FailureE f m ;
}.
 *)

CoFixpoint catch_FailureE1E2 {E1 E2 F X} `{E1 -< F} `{E2 -< F} `{failureE -< F}
           (f:string -> itree F X)
           (t : itree (E1 +' failureE +' E2) X) : itree F X :=
  match (observe t) with
  | RetF x => Ret x
  | TauF t => Tau (catch_FailureE1E2 f t)
  | VisF _ (inr1 (inl1 (Throw s))) k => f s
  | VisF _ e k => vis e (fun x => catch_FailureE1E2 f (k x))
  end.


(* CB TODO: Can we have 1 instance of MonadExc? *)
Global Instance monad_exc_FailureE1E2 {E1 E2} : (MonadExc string (itree (E1 +' failureE +' E2))) := {
  raise := raise_FailureE ;
  catch := fun T m f => catch_FailureE1E2 f m ;
}.

*)
