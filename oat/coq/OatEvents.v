From Coq Require Import
     ZArith
     List
     String
     Setoid
     Morphisms
     Omega
     Classes.RelationClasses.

From ExtLib Require Import
     Core.RelDec
     Programming.Eqv
     Structures.Monads.

From ITree Require Import
     ITree
     Events.Exception.

From Vellvm Require Import
     Error.

Require Import Oat.AST.
Require Import Oat.DynamicValues.

Open Scope list_scope.
Open Scope string_scope.
(************************************ Oat Events ********************************)
(**
   Oat semantics are designed to map cleanly to LLVM's memory / semantics ...
   We'll try to preserve many of the same notions, in order to simplify future
   proofs.
   
   The hope here is that we can define all the effectful ways in which Oat programs behave,
   e.g. Function Calls, Variable Mutations, Failure and Exceptions, to simplify writing
   down our denotational semantics.

   These are the events we'll use:
   * Function calls [CallE]
   * Interactions with the Local Environment [LocalE]
   *
*)
Set Implicit Arguments.
Set Contextual Implicit.

Definition value := ovalue.

(* We need some way of manipulating local variable values *)
Variant OLocalE : Type -> Type :=
| OLocalRead (id: var) : OLocalE value
| OLocalWrite (id: var) (v: value) : OLocalE unit.

(* We need some way of performing function calls *)
Variant OCallE : Type -> Type :=
  (* A function call to id that returns *)
  | OCallRet (id: var) (args: list value) : OCallE value
  | OCallVoid (id: var) (args: list value) : OCallE unit.

(* We need a notion of failure *)
Definition FailureE := exceptE string.
Definition raise {E} {A} `{FailureE -< E} (msg: string) : itree E A :=
  throw msg.

Definition lift_err {A B} {E} `{FailureE -< E} (f : A -> itree E B) (m : err A) : itree E B :=
  match m with
  | inl x => throw x
  | inr x => f x
  end.

(** 
    Finally, we can string these together - an OatEvent is just any one of these events.
    The only difference is that these effects have kind Type -> Type, so we need a variant
    of the sum type, called sum1.
 *)

Definition OatE := OLocalE +' OCallE +' FailureE. 
