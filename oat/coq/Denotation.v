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
     Interp.Recursion
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

About translate.
About mrec.
Search mrec.
About iter.
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
Definition vdecl := Oat.AST.vdecl.

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


Definition denote_uop (u: unop) (v: ovalue) : itree OatE ovalue :=
  match u,v with
  | Neg,    OVALUE_Int i => ret (OVALUE_Int (Int64.neg i))
  | Lognot, OVALUE_Bool b => ret (OVALUE_Bool (negb b))
  | Bitnot, OVALUE_Int i => ret (OVALUE_Int (Int64.not i))
  | _, _ => raise "err: incompatible types for unary operand"
  end.


(* Denote basic bop and uop *)
Definition denote_bop (op: binop) (v1 v2 : ovalue) : itree OatE ovalue :=
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

(** I'll define some convenient helpers for common things like looping and sequencing here *)
Definition seq {T : Type } (l : list (node stmt)) (f : stmt -> itree OatE (unit + T)) : itree OatE (unit + T) :=
  let base : itree OatE (unit + T) := ret (inl tt) in
  let combine : itree OatE (unit + T)
                -> node stmt
                -> itree OatE (unit + T)
      := fun acc hd =>
           v <- f (elt stmt hd) ;;
           ( match v with | inl _ => acc | inr v => ret (inr v) end )
  in 
  List.fold_left (combine) (l) (base).

Definition stmt_t : Type := unit + ovalue.
Definition cont_stmt : Type := unit + stmt_t.

Definition while (step : itree OatE (unit + stmt_t)) : itree OatE stmt_t :=
  iter (C := Kleisli _) (fun _ => step) (tt).

(* while combinator: inl unit *)

Definition end_loop : itree OatE (unit + stmt_t) := ret (inr (inl tt)).
Definition cont_loop_silent : itree OatE (unit + stmt_t) := ret (inl tt). 
Definition cont_loop_end : ovalue -> itree OatE (unit + stmt_t)
  := fun v => ret (inr (inr v)).

Definition fcall_noret_or_fail (id: expr) (args: list ovalue) : itree OatE unit :=
  match id with
  | Id i => trigger (OCallVoid i args)
  | _ => raise "err: can't call a thing that's not a func!"
  end.


 Definition for_loop_pre (decl: list vdecl) : itree OatE unit :=
  _ <- (map_monad (fun vdec =>
                     let e := denote_expr (elt expr (snd vdec)) in
                     v <- e ;;
                     trigger (OLocalWrite (fst vdec) v) ) decl) ;;
  ret tt.

(** Finally, we can start to denote the meaning of Oat statements *)
About inl.
Definition lift_eff {T} (t: itree OatE T) : itree OatE (unit + T) :=
 t' <- t ;; ret (inr t').   

Definition fcall (invoke: node exp) (args : list (node exp))  : itree OatE stmt_t :=
    let f_id := elt expr invoke in
    args' <- map_monad ( fun e => denote_expr (elt expr e)) args ;;
    _ <- fcall_noret_or_fail f_id args';;
    ret (inl tt).
  

Fixpoint denote_stmt (s : stmt) : itree OatE (unit + ovalue) :=
  match s with
  | Assn target source =>
    let tgt := elt_of target in
    let src := elt_of source in
    match tgt with
    | Id i =>
      v <- denote_expr src ;;
      trigger (OLocalWrite i v) ;;
      ret (inl tt)
    | _ => raise "err: assignment to a non variable target"
    end
  | Decl (id, node) =>
    let src := elt_of node in
    v <- denote_expr src ;;
    trigger (OLocalWrite id v) ;;
    ret (inl tt)
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
    while (
        x <- denote_expr (elt expr cond) ;;
        match x with
        | OVALUE_Bool bv =>
          if bv then lift_eff (seq stmts denote_stmt) else end_loop
        | _ => raise "err"
        end)
  | SCall f args => fcall f args
  | _ => raise "unimplemented"
  end.
Print  fdecl.

Definition fdecl_denotation : Type :=
  list ovalue -> itree OatE stmt_t. 

Definition denote_fdecl (df : fdecl ) : 

(*
  (* For loop stuff *)
  (* for (vdecl ; cond ; post )  { body } *)
  | For vdecl (Some cond) (Some post) body =>
    for_loop_pre vdecl ;;
    while (
        (cond' <- denote_expr (elt expr cond) ;; 
          match cond' with
          | OVALUE_Bool bv => if bv then
                              seq body denote_stmt ;;
                              denote_stmt (elt stmt post) ;;
                              ret (inl tt)
                              else
                                ret (inr tt)
          | _ => raise "err"
          end)
      )
          
  | For vdecl (Some cond) None body =>
    for_loop_pre vdecl ;;
    while (
        (cond' <- denote_expr (elt expr cond) ;; 
          match cond' with
          | OVALUE_Bool bv => if bv then
                              seq body denote_stmt ;;
                              ret (inl tt)
                              else
                                ret (inr tt)
          | _ => raise "err"
          end)
      )
  (* for (vdecl ; cond? ; post? )  { body } - infinite loop *)
  | For vdecl None (Some post) body =>
    for_loop_pre vdecl ;;
    while (
        seq body denote_stmt ;;
        denote_stmt (elt stmt post) ;;
        ret (inl tt)
      )
  | For vdecl None None body =>
    for_loop_pre vdecl ;;
    while (
        seq body denote_stmt ;;
        ret (inl tt)
      )
  | _ => raise "unimplemented"
  end.
*)
 
(*
  lookups for fname

*)
About AST.fdecl.

Fixpoint lookup (id: id) (fdecls: list AST.fdecl) : option AST.fdecl :=
  match fdecls with
  | nil => None
  | h :: t => if eqb (fname h) (id) then Some h else lookup id t
  end.
  
Definition denote_fdecl (fdecls : list fdecl) : _ :=
  @mrec OCallE (OatE')
        (fun T call =>
           match call with
             | OCallRet id args => 
               dargs <- map_monad (fun e => denote_expr (elt expr e)) args ;; 
        ).

About denote_fdecl.
