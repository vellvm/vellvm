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
     Program.Basics
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

From Vellvm Require Import Util Error.
Require Import Integers.
Require Import Oat.AST.
Require Import Oat.DynamicValues.
Require Import Oat.OatEvents.

Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.
Local Open Scope program_scope.
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
Definition unop := Oat.AST.unop.
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


Fixpoint denote_uop (u: unop) (v: ovalue) : itree OatE ovalue :=
  match u,v with
  | Neg,    OVALUE_Int i => ret (OVALUE_Int (Int64.neg i))
  | Lognot, OVALUE_Bool b => ret (OVALUE_Bool (negb b))
  | Bitnot, OVALUE_Int i => ret (OVALUE_Int (Int64.not i))
  | _, _ => raise "err: incompatible types for unary operand"
  end.


(* Denote basic bop and uop *)
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

Definition fcall_return_or_fail (id: expr) (args: list ovalue) : itree OatE ovalue :=
  match id with
  | Id i => trigger (OCallRet i args)
  | _ => raise "err: can't call a thing that's not a func!"
  end.

    

(* Now we can give an ITree semantics for the expressions in oat *)
Fixpoint denote_expr (e: expr) : itree OatE ovalue :=
  match e with
  | CBool b => ret (OVALUE_Bool b)
  | CInt i => ret (OVALUE_Int i)
  | Id i => trigger (OLocalRead i) 
  | CStr s => ret (OVALUE_Str s)
  | Uop op n =>
    let e' := elt_of n in
    v <- denote_expr e' ;;
    denote_uop op v
  | Bop op l_exp r_exp =>
    let l := elt_of l_exp in
    let r := elt_of r_exp in
    l' <- denote_expr l;;
    r' <- denote_expr r;;
    denote_bop op l' r' 
  | Call f args =>
    let f_id := elt expr f in
    args' <- map_monad ( fun e => denote_expr (elt expr e)) args ;;
    f_ret <- fcall_return_or_fail f_id args';;
    ret f_ret
  end.

(** 
    Before we move onto statements, we have to sort out a few things first.
    1) How are we going to handle if statements
    2) How are we going to represent function calls 
    3) How are we going to represent various loops
    4) Sequencing
*)
Definition seq (l : list (node stmt)) (f : stmt -> itree OatE unit) : itree OatE unit :=
  List.fold_left ( fun acc hd => f (elt stmt hd) ;; acc) (l) (ret tt).

Definition while (step : itree OatE (unit + unit)) : itree OatE unit :=
  iter (C := Kleisli _) (fun _ => step) tt.


Definition fcall_noret_or_fail (id: expr) (args: list ovalue) : itree OatE unit :=
  match id with
  | Id i => trigger (OCallVoid i args)
  | _ => raise "err: can't call a thing that's not a func!"
  end.

(** Finally, we can start to denote the meaning of Oat statements *)
 Fixpoint denote_stmt (s : stmt) : itree OatE unit :=
  match s with
  | Assn target source =>
    let tgt := elt_of target in
    let src := elt_of source in
    match tgt with
    | Id i =>
      v <- denote_expr src ;;
      trigger (OLocalWrite i v)
    | _ => raise "err: assignment to a non variable target"
    end
  | Decl (id, node) =>
    let src := elt_of node in
    v <- denote_expr src ;;
    trigger (OLocalWrite id v)
  | If cond p f =>
    (* Local function  *)
    let e_cond := elt expr cond in
    exp <- denote_expr e_cond ;;
    match exp with
      | OVALUE_Bool bv => 
    if bv then seq p denote_stmt else seq f denote_stmt
      | _ => raise "err"
    end
  | While cond stmts =>
    let e_cond := elt expr cond in
    while ( exp <- denote_expr e_cond ;;
            (match exp with
            | OVALUE_Bool bv =>
              if bv then (seq stmts denote_stmt) ;; ret (inl tt)
              else ret (inr tt)
            | _ => raise "err"
            end)
      )
  | SCall f args =>
    let f_id := elt expr f in
    args' <- map_monad ( fun e => denote_expr (elt expr e)) args ;;
    _ <- fcall_noret_or_fail f_id args';;
    ret tt
  | _ => raise "unimplemented"
  end.



(*
(* Write down some proofs for the typesystem ... *)
*)
