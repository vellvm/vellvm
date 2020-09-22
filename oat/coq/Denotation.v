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
(* Pass at denote_expr  *)

(* ======================================================================================== *)
(** ** Semantics *)

Definition var : Set := string.

Variant OatValue : Type := 
| OBool (b: bool)
| OInt (i: Z)
.

Definition value : Set := OatValue.
Variant OatState : Type -> Type :=
| GetVar (x: var) : OatState value 
| SetVar (x: var) (v: value) : OatState unit
.
Context { eff : Type -> Type }.
Context {HasOatState : OatState -< eff }.

i
Definition expr := Oat.AST.exp.
Definition bop := Oat.AST.binop.

(* (e)xpr (i)n (n)ode *)

Fixpoint eval_Oatval (o: oatval)
Fixpoint denote_expr (e: expr) : itree eff value :=
  match e with
  | Id i => trigger (GetVar i)
  | CBool b => ret (OBool b)
  | CInt i => ret (OInt i)
  | Bop Add l r => l' <- denote_expr (elt_of l) ;; r' <- denote_expr (elt_of r) ;; ret (OInt(l' + r'))  
  | _ => ret (OBool true)
  end.

                           

        
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
