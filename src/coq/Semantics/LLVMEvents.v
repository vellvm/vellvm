(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

(* begin hide *)
From Coq Require Import
     ZArith
     List
     String
     Setoid
     Morphisms
     Classes.RelationClasses.

From ExtLib Require Import
     Core.RelDec
     Programming.Eqv
     Structures.Monads
     Data.Monads.EitherMonad
     Data.Monads.IdentityMonad.

From ITree Require Import
     ITree
     Events.Exception.

From Mem Require Import
  Addresses.MemoryAddress.

From LLVM_Memory Require Import
  Sizeof
  Intptr.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics.DynamicValues
     Semantics.VellvmIntegers.

Import ITreeNotations.
(* end hide *)

(****************************** LLVM Events *******************************)
(**
   Vellvm's semantics relies on _Interaction Trees_, a generic data-structure allowing to model
   effectful computations.
   This file defined the interface provided to the interaction trees, that is the set of
   events that a LLVM program can trigger.
   These events are then concretely interpreted as a succession of handler, as defined in the
   _Handlers_ folder.
   The possible events are:
   * Function calls                                                          [CallE]
   * External function calls                                                 [ExternalCallE]
   * Calls to intrinsics whose implementation _do not_ depends on the memory [IntrinsicE]
   * Interactions with the global environment                                [GlobalE]
   * Interactions with the local environment                                 [LocalE]
   * Manipulation of the frame stack for local environments                  [StackE]
   * Interactions with the memory                                            [MemoryE]
   * Concretization of a under-defined value                                 [PickE]
   * Undefined behaviour                                                     [UBE]
   * Failure                                                                 [FailureE]
   * Debugging messages                                                      [DebugE]
*)

Set Implicit Arguments.
Set Contextual Implicit.

 (* Interactions with global variables for the LLVM IR *)
 (* Note: Globals are read-only, except for the initialization. We could want to reflect this in the events themselves. *)
  Variant GlobalE (k v:Type) : Type -> Type :=
  | GlobalWrite (id: k) (dv: v): GlobalE k v unit
  | GlobalRead  (id: k): GlobalE k v v.

  (* Interactions with local variables for the LLVM IR *)
  Variant LocalE (k v:Type) : Type -> Type :=
  | LocalWrite (id: k) (dv: v): LocalE k v unit
  | LocalRead  (id: k): LocalE k v v.

  Variant StackE (k v:Type) : Type -> Type :=
  | StackPush (args: list (k * v)) : StackE k v unit (* Pushes a fresh environment during a call *)
  | StackPop : StackE k v unit. (* Pops it back during a ret *)

  (* This function can be replaced with print_string during extraction
     to print the error messages of Throw and (indirectly) ThrowUB. *)
  Definition print_msg (msg : string) : unit := tt.

  (* Undefined behaviour carries a string. *)
  Variant UBE : Type -> Type :=
  | ThrowUB : unit -> UBE void.

  (** Since the output type of [ThrowUB] is [void], we can make it an action
    with any return type. *)
  Definition raiseUB {E : Type -> Type} `{UBE -< E} {X}
             (e : string)
    : itree E X
    := v <- trigger (ThrowUB (print_msg e));; match v: void with end.

  #[global] Instance RAISE_UB_ITREE_UB {E : Type -> Type} `{UBE -< E} : RAISE_UB (itree E) :=
  { raise_ub := fun A e => raiseUB e
  }.

  (* Out of memory / abort. Carries a string for a message. *)
  Variant OOME : Type -> Type :=
  | ThrowOOM : unit -> OOME void.

  (** Since the output type of [ThrowUB] is [void], we can make it an action
    with any return type. *)
  Definition raiseOOM {E : Type -> Type} `{OOME -< E} {X}
             (e : string)
    : itree E X
    := v <- trigger (ThrowOOM (print_msg e));; match v: void with end.

  #[global] Instance RAISE_OOM_ITREE_OOME {E : Type -> Type} `{OOME -< E} : RAISE_OOM (itree E) :=
  { raise_oom := fun A => raiseOOM
  }.

  (* Debug is identical to the "Trace" effect from the itrees library,
   but debug is probably a less confusing name for us. *)
  Variant DebugE : Type -> Type :=
  | Debug : unit -> DebugE unit.

  (* Utilities to conveniently trigger debug events *)
  Definition debug {E} `{DebugE -< E} (msg : string) : itree E unit :=
    trigger (Debug (print_msg msg)).

  (* Failure. Carries a string for a message. *)
  Variant FailureE : Type -> Type :=
  | Throw : unit -> FailureE void.

  Definition raise {E} {A} `{FailureE -< E} (msg : string) : itree E A :=
    v <- trigger (Throw (print_msg msg));; match v: void with end.

  #[global] Instance RAISE_ERR_ITREE_FAILUREE {E : Type -> Type} `{FailureE -< E} : RAISE_ERROR (itree E) :=
  { raise_error := fun A e => raise e
  }.

  Definition lift_err {A B} {E} `{FailureE -< E} (f : A -> itree E B) (m:err A) : itree E B :=
    match m with
    | inl x => raise x
    | inr x => f x
    end.

  Definition lift_pure_err {A} {E} `{FailureE -< E} (m:err A) : itree E A :=
    lift_err ret m.

  Definition lift_err_ub_oom {A B} {E} `{FailureE -< E} `{UBE -< E} `{OOME -< E} (f : A -> itree E B) (m:err_ub_oom A) : itree E B :=
    match m with
    | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
        match m with
        | inl (OOM_message x) => raiseOOM x
        | inr (inl (UB_message x)) => raiseUB x
        | inr (inr (inl (ERR_message x))) => raise x
        | inr (inr (inr x)) => f x
      end
    end.


(* TODO: decouple these definitions from the instance of DVALUE and DTYP by using polymorphism not functors. *)
Module Type LLVM_INTERACTIONS (ADDR : ADDRESS) (IP:INTPTR) (SIZEOF : Sizeof).

  #[global] Instance eq_dec_addr : RelDec (@eq ADDR.addr) := RelDec_from_dec _ ADDR.eq_dec.
  #[global] Instance Eqv_addr : Eqv ADDR.addr := (@eq ADDR.addr).

  Module DV := DynamicValues.DVALUE(ADDR)(IP)(SIZEOF).
  Export DV.

  Section Events.
    Variable memory : Type.

    (* Generic calls, refined by [denote_mcfg] *)
    Variant CallE : Type -> Type :=
    | Call        : forall (t:dtyp) (f:uvalue) (args:list uvalue), CallE uvalue.

    (* ExternalCallE values are the "observable" events by which one should compare the 
       equivalence of two LLVM IR programs.  These should never be interpreted away
       by the Coq semantics. However, for practicality, we _do_ interpet some calls that
       generate outputs to [stdout] (SAZ: and eventuall[stderr]).  The stream of bytes
       visible in [IO_stdout] events is the data printed to [stdout].

       - [ExternalCall] represents interactions with the OS
       - [IO_stdout] represents bytes sent to [stdout]
       - [IO_stderr] represents bytes sent to [stderr]

       The latter two are actually printed to the console by [interpreter.ml]
     *)
    Variant ExternalCallE : Type -> Type :=
      | ExternalCall        : forall (t:dtyp) (f:uvalue) (args:list dvalue), ExternalCallE dvalue

      (* This event corresponds to writing to the [stdout] channel. ] *)                              
      | IO_stdout : forall (str : list int8), ExternalCallE unit
      (* This event corresponds to writing to the [stderr] channel. ] *)                              
      | IO_stderr : forall (str : list int8), ExternalCallE unit.

    (* Call to an intrinsic whose implementation do not rely on the implementation of the memory model *)
    Variant IntrinsicE : Type -> Type :=
    | Intrinsic : forall (t:dtyp) (f:string) (args:list dvalue), IntrinsicE dvalue.

    (* Interactions with the memory *)
    Variant MemoryE : Type -> Type :=
    | MemPush : MemoryE unit
    | MemPop  : MemoryE unit
    | Alloca  : forall (t:dtyp) (num_elements : N) (align : option Z),  (MemoryE dvalue)
    (* Load address should also be unique *)
    | Load    : forall (t:dtyp) (a:dvalue),                    (MemoryE uvalue)
    (* Store address should be unique... *)
    | Store   : forall (t:dtyp) (a:dvalue) (v:uvalue),         (MemoryE unit).

  (* An event resolving the non-determinism induced by undef. The argument _P_
   is intended to be a predicate over the set of dvalues _u_ can take such that
   if it is not satisfied, the only possible execution is to raise _UB_.
   *)
  Variant PickE {X Y} {Post : X -> Y -> Prop} : Type -> Type :=
    | pickUnique (x : X) : PickE ({y : Y | Post x y})
    | pickNonPoison (x : X) : PickE ({y : Y | Post x y})
    | pick (x : X) : PickE ({y : Y | Post x y}).

  Definition PickUvalueE := @PickE uvalue dvalue (fun _ _ => True).

  (* MOVE THIS *)
  Class RAISE_PICK {X Y Post} (M : Type -> Type) : Type :=
    { raise_pick : @PickE X Y Post ~> M }.

  (* The signatures for computations that we will use during the successive stages of the interpretation of LLVM programs *)
  (* TODO: The events and handlers are parameterized by the types of key and value.
     It's weird for it to be the case if the events are concretely instantiated right here.
     At least TODO: remove these prefixes that are inconsistent with other names.
   *)
  Definition LLVMGEnvE := (GlobalE raw_id dvalue).
  Definition LLVMEnvE := (LocalE raw_id uvalue).
  Definition LLVMStackE := (StackE raw_id uvalue).

  Definition conv_E := MemoryE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE.
  Definition lookup_E := LLVMGEnvE +' LLVMEnvE.
  Definition exp_E := LLVMGEnvE +' LLVMEnvE +' MemoryE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE.

  Definition LU_to_exp : lookup_E ~> exp_E :=
    fun T e =>
      match e with
      | inl1 e => inl1 e
      | inr1 e => inr1 (inl1 e)
      end.

  Definition conv_to_exp : conv_E ~> exp_E :=
    fun T e => inr1 (inr1 e).

  Definition instr_E := CallE +' IntrinsicE +' exp_E.
  Definition exp_to_instr : exp_E ~> instr_E :=
    fun T e => inr1 (inr1 e).

  (* Core effects. *)
  Definition L0' := CallE +' ExternalCallE +' IntrinsicE +' LLVMGEnvE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE.

  Definition instr_to_L0' : instr_E ~> L0' :=
    fun T e =>
      match e with
      | inl1 e => inl1 e
      | inr1 (inl1 e) => inr1 (inr1 (inl1 e))
      | inr1 (inr1 (inl1 e)) => inr1 (inr1 (inr1 (inl1 e)))
      | inr1 (inr1 (inr1 (inl1 e))) => inr1 (inr1 (inr1 (inr1 (inl1 (inl1 e)))))
      | inr1 (inr1 (inr1 (inr1 e))) => inr1 (inr1 (inr1 (inr1 (inr1 e))))
      end.

  Definition exp_to_L0' : exp_E ~> L0' :=
    fun T e => instr_to_L0' (exp_to_instr e).

  Definition FUB_to_exp : (FailureE +' UBE) ~> exp_E :=
    fun T e =>
      match e with
      | inl1 x => inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 x))))))
      | inr1 x => inr1 (inr1 (inr1 (inr1 (inr1 (inl1 x)))))
      end.

  Definition FUBO_to_exp : (FailureE +' UBE +' OOME) ~> exp_E :=
    fun T e =>
      match e with
      | inl1 x => inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 x))))))
      | inr1 (inl1 x) => inr1 (inr1 (inr1 (inr1 (inr1 (inl1 x)))))
      | inr1 (inr1 x) => inr1 (inr1 (inr1 (inr1 (inl1 x))))
      end.

  Definition L0 := ExternalCallE +' IntrinsicE +' LLVMGEnvE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE.

  Definition exp_to_L0 : exp_E ~> L0 :=
    fun T e =>
      match e with
      | inl1 e => inr1 (inr1 (inl1 e))
      | inr1 (inl1 e) => inr1 (inr1 (inr1 (inl1 (inl1 e))))
      | inr1 (inr1 e) => inr1 (inr1 (inr1 (inr1 e)))
      end.

  (* For multiple CFG, after interpreting [GlobalE] *)
  Definition L1 := ExternalCallE +' IntrinsicE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE.

  (* For multiple CFG, after interpreting [LocalE] *)
  Definition L2 := ExternalCallE +' IntrinsicE +' MemoryE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE.

  (* For multiple CFG, after interpreting [LocalE] and [MemoryE] and [IntrinsicE] that are memory intrinsics *)
  Definition L3 := ExternalCallE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE.

  (* For multiple CFG, after interpreting [LocalE] and [MemoryE] and [IntrinsicE] that are memory intrinsics and [PickUvalueE]*)
  (* Interprets [Pick] events: forcing evaluation of [uvalue]s, [UBE] has no semantic meaning *)
  Definition L4 := ExternalCallE +' OOME +' UBE +' DebugE +' FailureE.

  (* [UBE] is still present in tree to identify failure, but the [model_UB] semantics allows [UB] to subsume all behavior *)
  Definition L5 := ExternalCallE +' OOME +' UBE +' DebugE +' FailureE.

  (* [OOM] semantics is introduced through [interp_prop], so the semantic change is not apparent in the event signature *)
  Definition L6 := ExternalCallE +' OOME +' UBE +' DebugE +' FailureE.

  Definition FUBO_to_L4 : (FailureE +' UBE +' OOME) ~> L4:=
    fun T e =>
      match e with
      | inl1 x => inr1 (inr1 (inr1 (inr1 x)))
      | inr1 (inl1 x) => inr1 (inr1 (inl1 x))
      | inr1 (inr1 x) => inr1 (inl1 x)
      end
    .

  End Events.

  #[export] Hint Unfold L0 L0' L1 L2 L3 L4 L5 L6 : core.

End LLVM_INTERACTIONS.

Module Make(ADDR : ADDRESS)(IP:INTPTR)(SIZEOF : Sizeof) <: LLVM_INTERACTIONS(ADDR)(IP)(SIZEOF).
Include LLVM_INTERACTIONS(ADDR)(IP)(SIZEOF).
End Make.
