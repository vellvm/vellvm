(** 
    Taken from vzaliva github.com/vzaliva/helix/Util/ErrorWithState

*)

Require Import Coq.Strings.String.

From ExtLib Require Import
     Structures.Monads
     Structures.Monad
     Structures.MonadExc
     Structures.MonadState
     Data.Monads.EitherMonad.

Require Import Vellvm.Error.

Import MonadNotation.
Open Scope monad_scope.
Open Scope type_scope.

(** Define various bits and bobs of monadic boilerplate for the ensuing plumbing *)
Section boilerplates.
  Variable S : Type.
  (** Error with state ... 
      Either you get a state OR you get an error (with a message) 
   *)
  Definition errS A := S -> string+(S*A). 

  Global Instance Monad_errS: Monad errS :=
    {
    ret := fun _ x => fun s => inr (s, x) ;
    bind := fun _ _ m f => fun s => match m s with
                                    | inl v => inl v
                                    | inr (s', x) => f x s'
                                    end
    }.

  Global Instance Exception_errS : MonadExc string errS :=
    { raise := fun _ v => fun s => inl v;
      catch := fun _ c h => fun s => match c s with
                                     | inl v => h v s
                                     | inr x => inr x
                                     end
    }.

  Global Instance State_errS : MonadState S errS :=
    { get := fun s => inr (s, s);
      put := fun t s => inr (t, tt)
    }.

  (** Running the monad *)

  Definition evalErrS {A: Type} (c: errS A) (initial: S) : err A :=
    match c initial with
    | inl msg => raise msg
    | inr (s, v) => ret v
    end.

  Definition execErrS {A:Type} (c: errS A) (initial: S) : err S :=
    match c initial with
    | inl msg => raise msg
    | inr (s, v) => ret s
    end.


  (* Lifting errors *)
  Definition err2errS {A: Type} : err A -> errS A
    := fun e => match e with
                | inl msg => raise msg
                | inr v => ret v
                end.

  (* Lifting option *)

  Definition option2errS {A:Type} (msg:string) (o:option A) : errS A
    := match o with
       | Some v => ret v
       | None => raise msg
       end.

End boilerplates.

Arguments option2errS {S} {A} (_) (_).
Arguments err2errS {S} {A} (_).
Arguments evalErrS {S} {A} (_) (_).
Arguments execErrS {S} {A} (_) (_).
  

