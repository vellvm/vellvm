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


Definition ctxt (T: Type) := list (Ast.id * T). 

(* Type of OAT maps *)
(* TODO: Find a better name for this than t_rhs >:( *)
Definition t_rhs : Type := (LLVMAst.ident * typ)%type. 
Definition global : Type := t_rhs.
Definition local : Type := t_rhs.
(* TODO: Figure out if a function type should be passed to the INSTR_Call ty or just the return type ... *)
Definition fxn : Type := t_rhs. 
Definition gctxt : Type := ctxt global.
Definition lctxt : Type := ctxt local.
Definition fctxt : Type := ctxt fxn.

Record cmpState := mkCmpState {
                            block_id: nat; (* most recently used block_id *)
                            local_id: nat; (* most recently used local variable id - named var *)
                            void_id : nat; (* here for compatibility ? - last used void terminator id *)
                            Γ : gctxt; (* Global variable context *)
                            Λ: lctxt; (* Local variable context *)
                            Φ : fctxt (* Function reference context *)
                          }.

Definition cerr := errS cmpState .



(** Lookup functions for various bits and pieces of state *)
Fixpoint find_id  (i: Ast.id) (ctxt: ctxt t_rhs) : cerr t_rhs :=
  match ctxt with
  | nil => option2errS "did not find id" None
  | h :: t =>
    let '(id, res) := h in
    if String.eqb id i then option2errS "found id" (Some res) else find_id i t
  end.

About map_monad.
Definition find_global (i: Ast.id) (st: cmpState) : cerr global := find_id i (Γ st).
Definition find_local  (i: Ast.id) (st: cmpState) : cerr local := find_id i (Λ st).
Definition find_func   (i: Ast.id) (st: cmpState) : cerr fxn := find_id i (Φ st).

(** Functions to edit state *)

(* increment state but return prev value *)
Definition inc_tmp : cerr (raw_id) :=
  x <- get ;;
  let v : nat := local_id x in
  put {|
      block_id := block_id x;
      local_id := S v;
      void_id  := void_id x;
      Γ        := Γ x;
      Λ        := Λ x;
      Φ        := Φ x
    |} ;;
  ret (Anon (Z_of_nat v)).

Definition inc_block: cerr nat :=
  x <- get ;;
  let v : nat := block_id x in
  put {|
      block_id := S v;
      local_id := local_id x;
      void_id  := void_id x;
      Γ        := Γ x;
      Λ        := Λ x;
      Φ        := Φ x
    |} ;;
  ret v.

Definition inc_void : cerr nat :=
  x <- get ;;
  let v : nat := void_id x in
  put {|
      block_id := block_id x;
      local_id := local_id x;
      void_id  := S v;
      Γ        := Γ x;
      Λ        := Λ x;
      Φ        := Φ x
    |} ;;
  ret v.

(* State modification *)
(* Might alias, but will always pick the most recent (allowing for shadowing :( ) *)
(* TODO: maybe rule this out as an invariant of oat programs - i think so *)
Definition safe_put (i: Ast.id) (ty: LLVMAst.typ) (id: LLVMAst.ident) (ctx: list (Ast.id * t_rhs)) : list (Ast.id * t_rhs) :=
  let to_add := (i, (id, ty)) in
  to_add :: ctx.

(* Will mutate every element with identifier i *)
Fixpoint unsafe_put (i: Ast.id) (ty: LLVMAst.typ) (id': ident) (ctx: ctxt t_rhs) : ctxt t_rhs :=
  match ctx with
  | nil => [(i, (id', ty))]
  | h :: t =>
    let '(id, rhs) := h in
    if String.eqb id i then
      (i, (id', ty)) :: unsafe_put i ty id' t
    else
      h :: unsafe_put i ty id' t
  end.

(* Safe puts *)
Definition put_global (id: Ast.id) (ty: LLVMAst.typ) (rid: ident) : cerr unit :=
  x <- get ;;
  put {|
      block_id := block_id x;
      local_id := local_id x;
      void_id  := void_id x; 
      Γ        := safe_put id ty rid (Γ x);
      Λ        := Λ x;
      Φ        := Φ x
    |}.

Definition put_local (id: Ast.id) (ty: LLVMAst.typ) (rid: ident) : cerr unit :=
  x <- get ;;
  put {|
      block_id := block_id x;
      local_id := local_id x;
      void_id  := void_id x; 
      Γ        := Γ x;
      Λ        := safe_put id ty rid (Λ x);
      Φ        := Φ x
    |}.

Definition put_fxn (id: Ast.id) (ty: LLVMAst.typ) (rid: ident) : cerr unit :=
  x <- get ;;
  put {|
      block_id := block_id x;
      local_id := local_id x;
      void_id  := void_id x; 
      Γ        := Γ x;
      Λ        := Λ x;
      Φ        := safe_put id ty rid (Φ x)
    |}.

(* Unsafe puts *)
Definition unsafe_put_global (id: Ast.id) (ty: LLVMAst.typ) (rid: ident) : cerr unit :=
  x <- get ;;
  put {|
      block_id := block_id x;
      local_id := local_id x;
      void_id  := void_id x; 
      Γ        := unsafe_put id ty rid (Γ x);
      Λ        := Λ x;
      Φ        := Φ x
    |}.

Definition unsafe_put_local (id: Ast.id) (ty: LLVMAst.typ) (rid: ident) : cerr unit :=
  x <- get ;;
  put {|
      block_id := block_id x;
      local_id := local_id x;
      void_id  := void_id x; 
      Γ        := Γ x;
      Λ        := unsafe_put id ty rid (Λ x);
      Φ        := Φ x
    |}.

Definition unsafe_put_fxn (id: Ast.id) (ty: LLVMAst.typ) (rid: ident) : cerr unit :=
  x <- get ;;
  put {|
      block_id := block_id x;
      local_id := local_id x;
      void_id  := void_id x; 
      Γ        := Γ x;
      Λ        := Λ x;
      Φ        := unsafe_put id ty rid (Φ x)
    |}.

(* Lookup an identifier in all contexts -
   if it's not locally defined, try the globals
*)

Definition find_ident (id : Ast.id) : cerr ( t_rhs ) :=
  st <- get ;;
  catch ( find_local id st) (fun _ => find_global id st).


