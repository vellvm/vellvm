Require Import String ZArith.
Require Import Oat.AST.
Require Import List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.


(* Following the Imp.v example, I'm trying to write the semantics for OAT *)
(*
  VV: First pass
  An OAT Environment is a mapping of a variable to an exp 
  Defintion var : Set := string.
  Definition value : Type := nat 

  Variant OatState : Type -> Type :=
  | GetVar (x: var) : OatState value
  | SetVar (x: var) (v: value) : OatState unit
  | GetArr ... what should this be?
  | SetArr ... also not really easy to express here

  IMP only uses int variables so maybe not ?
 *)


Check Oat.AST.exp.
(* Maybe refine the var defintion *)
Definition var : Set := string.
Definition value : Set := Oat.AST.ty.
(* Definition value : Set := Cbool \/ CInt \/ CStr *)

Variant OatValue : Type := 
   | OBool : Bool -> OatValue Oat.AST.TBool 
   | OInt : Z -> OatValue Oat.AST.TInt

(* 
  Second pass
  Defintion var : Set := string.

  OatValues can be more diverse ...
  Variant OatValue : Type -> Type := 
   | OBool : Bool -> OatValue Oat.AST.TBool 
   | OInt : Z -> OatValue Oat.AST.TInt
   | ONull : ty -> OatValue ty 
   (* We can add more types here for the possible oat values *)

   Definition value : Type := OatValue 
  
  Variant OatState : Type -> Type :=
  | GetVar (x: var) : OatState value 
  | SetVar (x: var) (v: value) : OatState unit
*)
