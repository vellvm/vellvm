
From Coq Require Import List String Init.Datatypes Program.Basics.
Local Open Scope string_scope.
Local Open Scope program_scope.
Local Open Scope list_scope.
From Vellvm Require Import LLVMAst Util.
Require Import Ast. 
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

Definition tctxt (T: Type) := list (Ast.id * T).
Definition t_global := Ast.ty.
Definition t_local := Ast.ty.
Definition t_fun := list Ast.ty * Ast.ret_ty.

Definition t_gctxt : Type := tctxt t_global.
Definition t_lctxt : Type := tctxt t_local.
Definition t_fctxt : Type := tctxt t_fun.
Definition t_sctxt : Type := tctxt (list Ast.id).

Definition tc_ctxt : Type := mkTypingContext {
                                 Γ : t_gctxt; (* Global variable typing context *)
                                 Λ : t_lctxt; (* Local variable typing context *)
                                 Φ : t_fctxt; (* Function typing context *)
                                 Σ : t_sctxt (* Struct typing context *)
                               }.

Definition tcerr := errS tc_ctxt.
