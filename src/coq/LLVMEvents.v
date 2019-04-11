(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

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
     Programming.Show
     Structures.Monads.

From ITree Require Import
     ITree
     Events.Exception.

From Vellvm Require Import
     Util
     LLVMAst
     MemoryAddress
     DynamicValues
     Error.

From Paco Require Import
     paco.

Set Implicit Arguments.
Set Contextual Implicit.

Inductive dtyp : Set :=
| DTYPE_I (sz:Z)
| DTYPE_Pointer
| DTYPE_Void
| DTYPE_Half
| DTYPE_Float
| DTYPE_Double
| DTYPE_X86_fp80
| DTYPE_Fp128
| DTYPE_Ppc_fp128
| DTYPE_Metadata
| DTYPE_X86_mmx
| DTYPE_Array (sz:Z) (t:dtyp)
| DTYPE_Struct (fields:list dtyp)
| DTYPE_Packed_struct (fields:list dtyp)
| DTYPE_Opaque
| DTYPE_Vector (sz:Z) (t:dtyp)     (* t must be integer, floating point, or pointer type *)
.

Section hiding_notation.
  Import ShowNotation.
  Local Open Scope show_scope.

  Fixpoint show_dtyp' (dt:dtyp) :=
    match dt with
    | DTYPE_I sz     => ("i" << show sz)
    | DTYPE_Pointer  => "ptr"
    | DTYPE_Void     => "dvoid"
    | DTYPE_Half     => "half"
    | DTYPE_Float    => "float"
    | DTYPE_Double   => "double"
    | DTYPE_X86_fp80 => "x86_fp80"
    | DTYPE_Fp128    => "fp128"
    | DTYPE_Ppc_fp128 => "ppc_fp128"
    | DTYPE_Metadata  => "metadata"
    | DTYPE_X86_mmx   => "x86_mmx"
    | DTYPE_Array sz t
      => ("[" << show sz << " x " << (show_dtyp' t) << "]")
    | DTYPE_Struct fields
      => ("{" << iter_show (List.map (fun x => (show_dtyp' x) << ",") fields) << "}")
    | DTYPE_Packed_struct fields
      => ("packed{" << iter_show (List.map (fun x => (show_dtyp' x) << ",") fields) << "}")
    | DTYPE_Opaque => "opaque"
    | DTYPE_Vector sz t
      => ("<" << show sz << " x " << (show_dtyp' t) << ">")  (* TODO: right notation? *)
    end%string.

  Global Instance show_dtyp : Show dtyp := show_dtyp'.
End hiding_notation.


Module Type LLVM_INTERACTIONS (ADDR : MemoryAddress.ADDRESS).

  Global Instance eq_dec_addr : RelDec (@eq ADDR.addr) := RelDec_from_dec _ ADDR.addr_dec.
  Global Instance Eqv_addr : Eqv ADDR.addr := (@eq ADDR.addr).

  (* The set of dynamic types manipulated by an LLVM program.  Mostly
   isomorphic to LLVMAst.typ but
     - pointers have no further detail
     - identified types are not allowed
   Questions:
     - What to do with Opaque?
   *)

  Module DV := DynamicValues.DVALUE(ADDR).
  Export DV.

  (*
Module LCLS := LocalEnvironment.LLVM_LOCALS(ADDR).
Export LCLS.
   *)

  (****************************** LLVM Events *******************************)
  (**
   We define the denotation of an LLVM program as computation emitting several families of events.
   These events are then concretely interpreted as a succesion of handler.
   In the current approach, we fix at the top level both the universe of events, and the order in which
   they get handled. More specifically:
   * a single CFG is an [itree (CallE +' LocalE +' MemoryE +' +' IntrinsicE +' MemoryIntrinsicE +' FailureE +' DebugE)]
   * [denote_mcfg] ties the functional knot, interpreting away [CallE]
   * [Local] interprets away [LocalE]
   * [Memory] interprets away [MemoryE]
   * Both kind of intrinsics admit handlers that do not interpret away their respective universe of events, since there might remain some of them

YZ NOTE: It makes sense for [MemoryIntrinsicE] to actually live in [MemoryE]. However, that means that [Memory] cannot interpret away [MemoryE] anymore.
   *)

  (* Generic calls, refined by [denote_mcfg] *)
  Variant CallE : Type -> Type :=
  | Call        : forall (t:dtyp) (f:dvalue) (args:list dvalue), CallE dvalue.

  (* Call to an intrinsic whose implementation do not rely on the implementation of the memory model *)
  Variant IntrinsicE : Type -> Type :=
  | Intrinsic : forall (t:dtyp) (f:string) (args:list dvalue), IntrinsicE dvalue.


  (* Interactions with local variables for the LLVM IR *)
  (* YZ NOTE: We here conflate two concepts: [LocalWrite] and [LocalRead] are events about a single local
   environment, while [LocalPush] and [LocalPop] are events about the stack dynamic required to handle
   call frames.
   Shall we split them?
   *)
  Variant LocalE : Type -> Type :=
  | LocalPush: LocalE unit (* Pushes a fresh environment during a call *)
  | LocalPop : LocalE unit (* Pops it back during a ret *)
  | LocalWrite (id: raw_id) (dv: dvalue): LocalE unit
  | LocalRead  (id: raw_id): LocalE dvalue.

  (* SAZ: TODO: add Push / Pop to memory events to properly handle Alloca scoping *)
  (* Interactions with the memory for the LLVM IR *)
  Variant MemoryE : Type -> Type :=
  | Alloca : forall (t:dtyp),                             (MemoryE dvalue)
  | Load   : forall (t:dtyp) (a:dvalue),                  (MemoryE dvalue)
  | Store  : forall (a:dvalue) (v:dvalue),                (MemoryE unit)
  | GEP    : forall (t:dtyp) (v:dvalue) (vs:list dvalue), (MemoryE dvalue)
  | ItoP   : forall (i:dvalue),                           (MemoryE dvalue)
  | PtoI   : forall (a:dvalue),                           (MemoryE dvalue)
  (* | MemoryIntrinsic : forall (t:dtyp) (f:function_id) (args:list dvalue), MemoryE dvalue *)
  .

  (* Debug is identical to the "Trace" effect from the itrees library,
   but debug is probably a less confusing name for us. *)
  Variant DebugE : Type -> Type :=
  | Debug : string -> DebugE unit.

  (* Failures carry string *)
  Definition FailureE := exceptE string.

  (* The signatures for computations that we will use during the successive stages of the interpretation of LLVM programs *)

  Definition LLVM X := itree X.

  
  (* Core effects - no distinction between "internal" and "external" calls. *)
  Definition _CFG := CallE +' IntrinsicE +' LocalE +' MemoryE +' DebugE +' FailureE.

  (* Distinction made between internal and external calls -- intermediate step in denote_mcfg.
     Note that [CallE] appears _twice_ in the [_CFG_INTERNAL] type.  The left one is 
     meant to be the "internal" call event and the right one is the "external" call event.
     The [denote_mcfg] function, which uses [mrec] to tie the recursive knot distinguishes
     the two.  It re-triggers an unknown [Call] event as an [ExternalCall] (which is just
     an injection into the right-hand side.
  *)
  Definition _CFG_INTERNAL := CallE +' _CFG.
  Definition ExternalCall t f args : _CFG_INTERNAL dvalue := (inr1 (inl1 (Call t f args))).
  
  (* For multiple CFG, after interpreting [LocalE] *)
  Definition _MCFG1 := CallE +' IntrinsicE +' MemoryE +' DebugE +' FailureE.

  (* For multiple CFG, after interpreting [LocalE] and [MemoryE] and [IntrinsicE] that are memory intrinsics *)
  Definition _MCFG2 := CallE +' DebugE +' FailureE.
  Hint Unfold LLVM _CFG _MCFG1 _MCFG2.

  (* This inclusion "assumes" that all call events are internal.  The 
     dispatch in denote_mcfg then interprets some of the calls directly,
     if their definitions are known, or it "externalizes" the calls
     whose definitions are not known.
  *)
  Definition _CFG_to_CFG_INTERNAL : _CFG ~> _CFG_INTERNAL :=
    fun R e =>
      match e with
      | inl1 e' =>
        match e' with
        | Call dt fv args => inl1 (Call dt fv args)
        end
      | inr1 e' => inr1 (inr1 e')
      end.

  
  
  (* Utilities to conveniently trigger debug and failure events *)

  Definition lift_err {A B} {E} `{FailureE -< E} (f : A -> itree E B) (m:err A) : itree E B :=
    match m with
    | inl x => throw x
    | inr x => f x
    end.

  Definition debug {E} `{DebugE -< E} (msg : string) : itree E unit :=
    trigger (Debug msg).

  Definition raise {E} {A} `{FailureE -< E} (msg : string) : itree E A :=
    throw msg.

End LLVM_INTERACTIONS.


Module Make(ADDR : MemoryAddress.ADDRESS) <: LLVM_INTERACTIONS(ADDR).
Include LLVM_INTERACTIONS(ADDR).
End Make.
