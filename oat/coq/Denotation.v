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
Require Import Integers.
Require Import Oat.AST.
Require Import Oat.DynamicValues.
Require Import Oat.OatEvents.

Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.
Module Int64 := Integers.Int64.
Definition int64 := Int64.int.

(******************************* Oat Semantics *******************************)
(**
   We'll finally start writing down how OAT should work! To begin, we'll
   write down OAT semantics in terms of itrees / how an OAT program should
   be interpreted.
*)

Set Implicit Arguments.
Set Contextual Implicit.
Definition expr := Oat.AST.exp.
Definition stmt := Oat.AST.stmt.
Definition binop := Oat.AST.binop.

(* Denote the semantics for binary operations *)

About value.
Search value.
About raise.
About Int64.

(* TODO: these definitions might cause some problems? *)
Definition neq (x y : int64) : bool :=
  negb (Int64.eq x y).

Definition lte (x y : int64) : bool :=
  Int64.eq x y || Int64.lt x y.

Definition gt (x y : int64) : bool :=
  negb (lte x y).

Definition gte (x y : int64) : bool :=
  negb (Int64.lt x y).

Fixpoint denote_bop (op: binop) (v1 v2 : ovalue) : itree OatE ovalue :=
  match op, v1, v2 with
  (* Integer arithmetic *)
  | Oat.AST.Add, OVALUE_Int l, OVALUE_Int r => ret (OVALUE_Int (Int64.add l r))
  | Sub, OVALUE_Int l, OVALUE_Int r => ret (OVALUE_Int(Int64.sub l r))
  | Mul, OVALUE_Int l, OVALUE_Int r => ret (OVALUE_Int(Int64.mul l r))
  (* Integer comparison *)
  | Eq, OVALUE_Int l, OVALUE_Int r => ret (OVALUE_Bool (Int64.eq l r))
  | Neq, OVALUE_Int l, OVALUE_Int r => ret (OVALUE_Bool (neq l r))
  | Lt, OVALUE_Int l, OVALUE_Int r => ret (OVALUE_Bool (Int64.lt l r))
  | Lte, OVALUE_Int l, OVALUE_Int r => ret (OVALUE_Bool (lte l r))
  | Gt, OVALUE_Int l, OVALUE_Int r => ret (OVALUE_Bool (gt l r))
  | Gte, OVALUE_Int l, OVALUE_Int r => ret (OVALUE_Bool (gte l r))
  (* Integer bitwise arithmetic *)
  | IAnd, OVALUE_Int l, OVALUE_Int r => ret (OVALUE_Int (Int64.and l r))
  | IOr, OVALUE_Int l, OVALUE_Int r => ret (OVALUE_Int (Int64.or l r))
  | Shl, OVALUE_Int l, OVALUE_Int r => ret (OVALUE_Int (Int64.shl l r))
  | Shr, OVALUE_Int l, OVALUE_Int r => ret (OVALUE_Int (Int64.shru l r))
  | Sar, OVALUE_Int l, OVALUE_Int r => ret (OVALUE_Int (Int64.shr l r))
  (* Boolean operations *)
  | And, OVALUE_Bool l, OVALUE_Bool r => ret (OVALUE_Bool (l && r))
  | Or, OVALUE_Bool l, OVALUE_Bool r => ret (OVALUE_Bool (l || r))
  | _, _, _ => raise "err: incompatible types for binary operand"
 end.

(*
(* TODO: Denote uop *)

Fixpoint denote_expr (e: expr) : itree expE value :=
  match e with
  | CBool b => ret (OBool b)
  | CInt i => ret (OInt i)
  | Id i => trigger (GetVar i)
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


(* cast bools to true *)
Definition is_true (v: OatValue) : bool :=
  match v with
  | OBool b => b
  (* Should this case even happen? Maybe we raise ub before *)
  | OInt i => negb (Z.eqb i 0)
  end.

Definition while (step : itree expE (unit + unit)) : itree expE unit :=
  iter (C := Kleisli _) (fun _ => step) tt.
    
Fixpoint denote_stmt (s : stmt) : itree expE unit :=
  match s with
  | Assn target source =>
    let tgt := elt_of target in
    let src := elt_of source in
    match tgt with
    | Id i =>
      v <- denote_expr src ;;
      trigger (SetVar i v)
    | _ => raiseUB "Non variable target?"
    end

  | While cond stmts =>
    let e_cond := elt_of cond in
    let e_stmts := List.map (elt_of) stmts in
(*    while (v <- denote_expr e_cond ;;
           if is_true v
                      then 
          )
*)
    raise "unimplemented"
  | Decl (id, node) =>
    (* Default initialization with helper *)
    (* int x; / bool x; *)
    let src := elt_of target in
    v <- denote_expr src ;;
    trigger (SetVar id v)
  | _ => raise "unimplemented"
  end.

(* Write down some proofs for the typesystem ... *)
*)
