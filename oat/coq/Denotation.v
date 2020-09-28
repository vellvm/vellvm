Require Import Oat.AST.
Require Import List.

From Coq Require Import
     ZArith
     List
     String
     Setoid
     Morphisms
     Omega
     Classes.RelationClasses
     Init.Datatypes
.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts
     Events.Exception
.

From ExtLib Require Import
     Core.RelDec
     Programming.Eqv
     Structures.Monads.

From Vellvm Require Import Error.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

(* ======================================================================================== *)
(** ** Oat Events & values*)
(* We can manipulate Oat state via get and set events *)
Definition var : Set := string.
Variant OatValue : Type := 
| OBool (b: bool)
| OInt (i: Z)
.
Definition value : Set := OatValue.
Variant OatVarE : Type -> Type :=
| GetVar (x: var) : OatVarE value 
| SetVar (x: var) (v: value) : OatVarE unit
.

(* Oat programs may also yield undefined behaviour! *)
Variant UBE : Type -> Type :=
  | ThrowUB : string -> UBE void. 


(* We can make UBE an action without a return type *)
Definition raiseUB { E : Type -> Type} `{UBE -< E} {X}
           (e : string)
  : itree E X
          := vis (ThrowUB e) (fun v : void => match v with end).

Definition FailureE := exceptE string.


Definition raise {E} {A} `{FailureE -< E} (msg: string) : itree E A :=
  throw msg.
About throw.


(* VV: define lifters here - you'll probably need them soon?' *)
About inl.
Definition lift_err {A B} {E} `{FailureE -< E} (f : A -> itree E B) (m : err A) : itree E B :=
  match m with
  | inl x => throw x
  | inr x => f x
  end.

(* Core effects *)
Definition expE := OatVarE +' UBE +' FailureE.
Definition expr := Oat.AST.exp.
Definition binop := Oat.AST.binop.
Context { eff : Type -> Type }.
Context {HasImpState : OatVarE -< eff}.


Locate "<-". 

Fixpoint denote_bop (op: binop) (v1 v2 : value) : itree expE value :=
  match op, v1, v2 with
  | Oat.AST.Add, OInt l, OInt r => ret (OInt (l + r))
  | Mul, OInt l, OInt r => ret (OInt (l * r))
  | Sub, OInt l, OInt r => ret (OInt (l - r))
  | Oat.AST.Eq, OInt l, OInt r => ret (OBool (Z.eqb l r))
  | Oat.AST.Eq, OBool l, OBool r => ret (OBool (Bool.eqb l r))
  | Oat.AST.Neq, OInt l, OInt r => ret (OBool (negb (Z.eqb l r)))
  | Oat.AST.Neq, OBool l, OBool r => ret (OBool (negb (Bool.eqb l r)))
  | _, _, _ => raise "type error"
 end.


Fixpoint denote_expr (e: expr) : itree expE value :=
  match e with
  | CBool b => ret (OBool b)
  | CInt i => ret (OInt i)
  | Id i => trigger (GetVar i)
 (* Boring boilerplate here *)
  | Bop op l_exp r_exp =>
    let l := elt_of l_exp in
    let r := elt_of r_exp in
    l' <- denote_expr l;;
    r' <- denote_expr r;;
    denote_bop op l' r' 
  | Uop op ex =>
    let e' := elt_of ex in
    raise "todo : fill in"
  (* Boilerplate fin *)
  | _ => raise "undefined"
 end.

