From Coq Require Import List String Init.Datatypes Program.Basics.
Local Open Scope string_scope.
Local Open Scope program_scope.
Local Open Scope list_scope.
From Vellvm Require Import LLVMAst Util.
Require Import AST. 
Import ListNotations.
Set Implicit Arguments.
Set Strict Implicit.
From Coq Require Import FSets.FMapList.
Require Import FunInd FMapInterface.

Require Import Integers.
Require Import Integers String ZArith.
Require Import Plumbing.
Module Int64 := Integers.Int64. 
Definition int64 := Int64.int. 


From ExtLib Require Import
     Structures.Monads
     Structures.Monad
     Structures.MonadExc
     Structures.MonadState
     Data.Monads.EitherMonad.
Import MonadNotation.
Open Scope monad_scope.

Variant operand : Type :=
| Null
| Const (i: int64)
| Gid (id: ident)
| Lid (id: ident).

Local Definition t : Type :=  (AST.id * (operand * typ))%type.
Local Definition ctxt : Type := list t.
Record vellvmState := mkVellumState {
                          block_id: nat;
                          local_id: nat;
                          void_id : nat;
                          Δ : ctxt
                        }.

Definition cerr := errS vellvmState.

(** Fill these in as part of the compiler *)
Fixpoint cmp_ty (ty:  AST.ty) : LLVMAst.typ
(* TODO *). Admitted.

Definition typ_of_binop (op : AST.binop) : (AST.ty * AST.ty * AST.ty)
(* TODO *). Admitted.

Definition typ_of_unop (op: AST.unop) : (AST.ty * AST.ty * AST.ty)
(* TODO *). Admitted.


Fixpoint cmp_exp (exp: node AST.exp)
  : cerr (LLVMAst.typ * operand * code typ)
(* TODO *). Admitted.

Fixpoint cmp_stmt
         (rt : LLVMAst.typ)
         (stmt: node AST.stmt) : cerr ( LLVMAst.block typ ) 
(* TODO *). Admitted.
(** 
with cmp_block (rt : LLVMAst.typ) (stmts: AST.block) : cerr (code typ)
(* TODO *). Admitted.
*)                                   

(** Initialize a function context, compiler the given prog
    and run the state ... - work out what the nicest 
*)

Definition Populate_function_ctxt (c: ctxt) (p: AST.prog) : ctxt 
(* TODO *). Admitted.

(* TODO - add this once globals are supported in OAT *)
Fixpoint Populate_global_ctxt (c: ctxt) (p: AST.prog) : ctxt
(* TODO *). Admitted.

Definition cfg : Set := LLVMAst.block typ * list (LLVMAst.block typ).

Definition cmp_fdecl (f: node AST.fdecl)
  : cerr ( toplevel_entity typ cfg)
(* TODO *). Admitted.

Definition cmp_prog (p: AST.prog) : cerr ( toplevel_entities typ cfg) 
(* TODO *). Admitted.



