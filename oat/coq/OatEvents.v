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
     Utils.Error.

Require Import Oat.Ast.
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

Definition value := ovalue.
Definition var := Ast.id.
(* We need some way of manipulating local variable values *)
Variant OLocalE : Type -> Type :=
| OLocalRead (id: var) : OLocalE value
| OLocalWrite (id: var) (v: value) : OLocalE unit.

(* We need some way of performing function calls *)
Variant OCallE : Type -> Type :=
  (* A function call to id that returns *)
  | OCall (id: var) (args: list value) : OCallE value.

(* We need some way of representing call stacks *)
Variant OStackE : Type -> Type :=
| OStackPush (args: list (id * ovalue)) : OStackE unit
| OStackPop (args: list (id * ovalue)) : OStackE unit.

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

Definition OatE :=  OCallE +' OLocalE +' OStackE +' FailureE. 

(* This version of an oat event has no call events - these are interpreted away *)
Definition OatE' := OLocalE +' OStackE +' FailureE.

(** Note that just having these events is not enough to extract an interpreter.
    We'll need to define how to interpret these concretely. We'll do this in levels,
    interpreting the semantics of each event (what data structures / operations), 
    until we have an itree over void events. 
*)

Definition Oat0 := OatE'.
Definition Oat1 := OStackE +' FailureE.
Definition Oat2 := FailureE.
                     

