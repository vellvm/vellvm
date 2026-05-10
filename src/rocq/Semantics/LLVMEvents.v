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
From Stdlib Require Import
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

From Vellvm Require Import
     Utilities
     Syntax
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

  Variant StackE (k v exc:Type) : Type -> Type :=
  | StackPush (args: list (k * v)) : StackE k v exc unit (* Pushes a fresh environment during a call *)
  | StackPop : StackE k v exc unit (* Pops it back during a ret *)
  | StackSetHandler : option block_id -> StackE k v exc unit (* Insert / remove landingpad for exception *)
  | StackHandler : StackE k v exc (option block_id) (* Get exception handler for current frame *)
  | StackRaise : exc -> StackE k v exc unit (* Place exception onto the stack, does not pop *)
  | StackGetExc : StackE k v exc (option exc). (* Fetches the currently raised exception if there is one *)

  (* LLVM exceptions *)
  Variant LLVMExcE (EXC : Type) : Type -> Type :=
    | LLVMExc : EXC -> LLVMExcE EXC void.

  Definition raiseLLVM {E EXC} {A} `{LLVMExcE EXC -< E} (e : EXC) : itree E A :=
    v <- trigger (LLVMExc e);; match v: void with end.

  (* See src/ml/Extract.v for the special handling of these operation. *)
  (* This function can be replaced with print operations  during extraction
     to print the error messages of Throw and (indirectly) ThrowUB.
      - set_loc imperatively sets a string that will be prefixed onto the msg
        it returns the empty string, but we need to use its result to
        force extraction 
      - print_msg call `print_string`
   *)
  Record printer := mk_printer {
      printer_set_loc : string -> string ;
      printer_print_msg : string -> unit ;
      printer_get_loc : unit -> string ;
    }.
  
  Definition printer_object : printer :=
    mk_printer (fun (_:string) => "") (fun (_:string) => tt) (fun (_:unit) => "").
  
  Definition set_loc : string -> string := printer_object.(printer_set_loc).
  Definition print_msg : string -> unit := printer_object.(printer_print_msg).
  Definition get_loc : unit -> string := printer_object.(printer_get_loc).

  (* Undefined behaviour carries a string. *)
  Variant UBE : Type -> Type :=
  | ThrowUB : unit -> UBE void.

  (** Since the output type of [ThrowUB] is [void], we can make it an action
    with any return type. *)
  Definition raiseUB {E : Type -> Type} `{UBE -< E} {X}
             (e : string)
    : itree E X
    := v <- trigger (ThrowUB (print_msg e));; match v: void with end.

  (* Out of memory / abort. Carries a string for a message. *)
  Variant OOME : Type -> Type :=
  | ThrowOOM : unit -> OOME void.

  (** Since the output type of [ThrowOOM] is [void], we can make it an action
    with any return type. *)
  Definition raiseOOM {E : Type -> Type} `{OOME -< E} {X}
             (e : string)
    : itree E X
    := v <- trigger (ThrowOOM (print_msg e));; match v: void with end.

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

(* REFACTOR: This should not be a module type.  DynamicValues should not be instantiated here.   *)
(* TODO: decouple these definitions from the instance of DVALUE and DTYP by using polymorphism not functors. *)
  Section Events.
    Variable dvalue : Set.
    
    (* Generic calls, refined by [denote_mcfg] *)
    (* TODO: reincorporate exceptions *)
    Variant CallE : Type -> Type :=
    | Call        : forall (t:dtyp) (f:dvalue) (args:list dvalue), CallE dvalue.

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
      | ExternalCall        : forall (t:dtyp) (f:dvalue) (args:list dvalue), ExternalCallE dvalue

      (* This event corresponds to writing to the [stdout] channel. ] *)                              
      | IO_stdout : forall (str : list int8), ExternalCallE unit
      (* This event corresponds to writing to the [stderr] channel. ] *)                              
      | IO_stderr : forall (str : list int8), ExternalCallE unit.

    (* Call to an intrinsic whose implementation do not rely on the implementation of the memory model *)
    (* Intrinsics may raise an exception by returning inl *)
    (* TODO: reincorporate exceptions *)
    Variant IntrinsicE : Type -> Type :=
    | Intrinsic : forall (t:dtyp) (f:string) (args:list dvalue), IntrinsicE dvalue.

    (* Interactions with the memory *)
    Variant MemoryE : Type -> Type :=
    | MemPush : MemoryE unit
    | MemPop  : MemoryE unit
    | Alloca  : forall (t:dtyp) (num_elements : N) (align : option Z),  (MemoryE dvalue)
    (* Load address should also be unique *)
    | Load    : forall (t:dtyp) (a:dvalue),                    (MemoryE dvalue)
    (* Store address should be unique... *)
    | Store   : forall (t:dtyp) (a:dvalue) (v:dvalue),         (MemoryE unit).

  (* An event resolving the non-determinism induced by undef. The argument _P_
   is intended to be a predicate over the set of dvalues _u_ can take such that
   if it is not satisfied, the only possible execution is to raise _UB_.
   *)
    Variant DrawE : Type -> Type :=
      | draw (dt : dtyp) : DrawE dvalue.
    
  (* Variant PickE {X Y} {Post : X -> Y -> Prop} : Type -> Type := *)
  (*   | pickUnique (x : X) : PickE ({y : Y | Post x y}) *)
  (*   | pickNonPoison (x : X) : PickE ({y : Y | Post x y}) *)
  (*   | pick (x : X) : PickE ({y : Y | Post x y}). *)

  (* Definition PickDvalueE := @PickE dvalue dvalue (fun _ _ => True). *)

  (* (* MOVE THIS *) *)
  (* Class RAISE_PICK {X Y Post} (M : Type -> Type) : Type := *)
  (*   { raise_pick : @PickE X Y Post ~> M }. *)

  (* The signatures for computations that we will use during the successive stages of the interpretation of LLVM programs *)
  (* TODO: The events and handlers are parameterized by the types of key and value.
     It's weird for it to be the case if the events are concretely instantiated right here.
     At least TODO: remove these prefixes that are inconsistent with other names.
   *)
  Definition LLVMGEnvE := (GlobalE raw_id dvalue).
  Definition LLVMEnvE := (LocalE raw_id dvalue).
  Definition LLVMStackE := (StackE raw_id dvalue dvalue).

  Definition conv_E := MemoryE +' DrawE +' OOME +' LLVMExcE dvalue +' UBE +' DebugE +' FailureE.
  Definition lookup_E := LLVMGEnvE +' LLVMEnvE.
  Definition exp_E := LLVMGEnvE +' LLVMEnvE +' MemoryE +' DrawE +' OOME +' LLVMExcE dvalue +' UBE +' DebugE +' FailureE.

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
    fun T e => subevent _ e.

  (* Core effects. *)
  Definition L0' := CallE +' ExternalCallE +' IntrinsicE +' LLVMGEnvE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' DrawE +' OOME +' LLVMExcE dvalue +' UBE +' DebugE +' FailureE.

  Definition instr_to_L0' : instr_E ~> L0' := subevent.

  Definition exp_to_L0' : exp_E ~> L0' := subevent.

  Definition FUB_to_exp : (FailureE +' UBE) ~> exp_E := subevent.

  Definition FUBO_to_exp : (FailureE +' UBE +' OOME) ~> exp_E := subevent.

  Definition L0 := ExternalCallE +' IntrinsicE +' LLVMGEnvE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' DrawE +' OOME +' LLVMExcE dvalue +' UBE +' DebugE +' FailureE.

  Definition exp_to_L0 : exp_E ~> L0 := subevent.

  (* For multiple CFG, after interpreting [GlobalE] *)
  Definition L1 := ExternalCallE +' IntrinsicE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' DrawE +' OOME +' LLVMExcE dvalue +' UBE +' DebugE +' FailureE.

  (* For multiple CFG, after interpreting [LocalE] *)
  Definition L2 := ExternalCallE +' IntrinsicE +' MemoryE +' DrawE +' OOME +' LLVMExcE dvalue +' UBE +' DebugE +' FailureE.

  (* For multiple CFG, after interpreting [LocalE] and [MemoryE] and [IntrinsicE] that are memory intrinsics *)
  Definition L3 := ExternalCallE +' DrawE +' OOME +' LLVMExcE dvalue +' UBE +' DebugE +' FailureE.

  (* For multiple CFG, after interpreting [LocalE] and [MemoryE] and [IntrinsicE] that are memory intrinsics and [DrawE]*)
  (* Interprets [Pick] events: forcing evaluation of [dvalue]s, [UBE] has no semantic meaning *)
  Definition L4 := ExternalCallE +' OOME +' LLVMExcE dvalue +' UBE +' DebugE +' FailureE.

  (* [UBE] is still present in tree to identify failure, but the [model_UB] semantics allows [UB] to subsume all behavior *)
  Definition L5 := ExternalCallE +' OOME +' LLVMExcE dvalue +' UBE +' DebugE +' FailureE.

  (* [OOM] semantics is introduced through [interp_prop], so the semantic change is not apparent in the event signature *)
  Definition L6 := ExternalCallE +' OOME +' LLVMExcE dvalue +' UBE +' DebugE +' FailureE.

  Definition FUBO_to_L4 : (FailureE +' UBE +' OOME) ~> L4:= subevent.


  
  (* Event Inclusions -------------------------------- *)

  #[global]
    Instance Global_lookup : GlobalE raw_id dvalue -< lookup_E :=
    inl1.

  #[global]
    Instance Local_lookup : LocalE raw_id dvalue -< lookup_E :=
    inr1.

  
  (* expE *)
  (*   Definition exp_E := LLVMGEnvE +' LLVMEnvE +' MemoryE +' DrawE +' OOME +' LLVMExcE dvalue +' UBE +' DebugE +' FailureE. *)
  #[global]
    Instance Failure_expE : `{FailureE -< exp_E} := 
    fun T e => (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e)))))))).

  #[global]
    Instance DebugE_expE : `{DebugE -< exp_E} := 
    fun T e => (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e)))))))).

  #[global]
    Instance UBE_expE : `{UBE -< exp_E} := 
    fun T e => (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e))))))).

  #[global]
    Instance LLVMExcE_expE : `{LLVMExcE dvalue -< exp_E} := 
    fun T e => (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e)))))).
  
  #[global]
    Instance OOME_expE : `{OOME -< exp_E} := 
    fun T e => (inr1 (inr1 (inr1 (inr1 (inl1 e))))).

  #[global]
    Instance PickE_expE : `{DrawE -< exp_E} := 
    fun T e => (inr1 (inr1 (inr1 (inl1 e)))).

  #[global]
    Instance MemoryE_expE : `{MemoryE -< exp_E} := 
    fun T e => (inr1 (inr1 (inl1 e))).

  #[global]
    Instance LLVMEnvE_expE : `{LLVMEnvE -< exp_E} := 
    fun T e => (inr1 (inl1 e)).

  #[global]
    Instance LLVMGEnvE_expE : `{LLVMGEnvE -< exp_E} := 
    fun T e => (inl1 e).

  (* instr_E *)
  
  #[global]
    Instance Failure_instrE : `{FailureE -< instr_E} := 
    fun T e => (inr1 (inr1 (Failure_expE e))).

  #[global]
    Instance DebugE_instrE : `{DebugE -< instr_E} := 
    fun T e => (inr1 (inr1 (DebugE_expE e))).
  
  #[global]
    Instance UBE_instrE : `{UBE -< instr_E} := 
    fun T e => (inr1 (inr1 (UBE_expE e))).

  #[global]
    Instance LLVMExcE_instrE : `{LLVMExcE dvalue -< instr_E } := 
    fun T e => (inr1 (inr1 (LLVMExcE_expE e))).
  
  #[global]
    Instance OOME_instrE : `{OOME -< instr_E} := 
    fun T e => (inr1 (inr1 (OOME_expE e))).

  #[global]
    Instance PickE_instrE : `{DrawE -< instr_E} := 
    fun T e => (inr1 (inr1 (PickE_expE e))).

  #[global]
    Instance MemoryE_instrE : `{MemoryE -< instr_E} := 
    fun T e => (inr1 (inr1 (MemoryE_expE e))).

  #[global]
    Instance LLVMEnvE_instrE : `{LLVMEnvE -< instr_E } := 
    fun T e => (inr1 (inr1 (LLVMEnvE_expE e))).
  
  #[global]
    Instance LLVMGEnvE_instrE : `{LLVMGEnvE -< instr_E } := 
    fun T e => (inr1 (inr1 (LLVMGEnvE_expE e))).

  #[global]
    Instance IntrinsicE_instrE : `{IntrinsicE -< instr_E } := 
    fun T e => (inr1 (inl1 e)).

  #[global]
    Instance CallE_instrE : `{CallE -< instr_E} := 
    fun T e => (inl1 e).

  (* L0' *)
  (*   Definition L0' := CallE +' ExternalCallE +' IntrinsicE +' LLVMGEnvE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' DrawE +' OOME +' LLVMExcE dvalue +' UBE +' DebugE +' FailureE. *)

  #[global]
    Instance FailureE_L0' : `{FailureE -< L0'} := 
    fun T e => inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e)))))))))).

  #[global]
    Instance DebugE_L0' : `{DebugE -< L0'} := 
    fun T e => inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e)))))))))).
  
  #[global]
    Instance UBE_L0' : UBE -< L0' :=
    fun T e => (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e)))))))))).

  #[global]
    Instance LLVMExcE_L0' : LLVMExcE dvalue -< L0' :=
    fun T e => (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e))))))))).
  
  #[global]
    Instance OOME_L0' : OOME -< L0' :=
    fun T e => (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e)))))))).

  #[global]
    Instance DrawE_L0' : DrawE -< L0' :=
    fun T e => (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e))))))).
  
    #[global]
    Instance MemoryE_L0' : `{MemoryE -< L0'} := 
    fun T e => (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e)))))).

  #[global]
    Instance LLVMEnvE_L0' : `{LLVMEnvE  -< L0'} := 
    fun T e => inr1 (inr1 (inr1 (inr1 (inl1 (inl1 e))))).

  #[global]
    Instance StackE_L0' : `{StackE local_id dvalue _  -< L0'} := 
    fun T e => inr1 (inr1 (inr1 (inr1 (inl1 (inr1 e))))).

  #[global]
    Instance GEnvE_L0' : `{LLVMGEnvE  -< L0'} := 
    fun T e => (inr1 (inr1 (inr1 (inl1 e)))).

  #[global]
    Instance IntrinsicE_L0' : `{IntrinsicE  -< L0'} := 
    fun T e => (inr1 (inr1 (inl1 e))).

  #[global]
    Instance ExternalCallE_L0' : `{ExternalCallE  -< L0'} := 
    fun T e => (inr1 (inl1 e)).

  #[global]
    Instance CallE_L0' : `{CallE  -< L0'} := 
    fun T e => (inl1 e).

  (* L0 *)
  (*   Definition L0 := ExternalCallE +' IntrinsicE +' LLVMGEnvE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' DrawE +' OOME +' LLVMExcE dvalue +' UBE +' DebugE +' FailureE. *)

  #[global]
    Instance FailureE_L0 : FailureE -< L0 :=
    fun T e => (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e)))))))))).

  #[global]
    Instance DebugE_L0 : DebugE -< L0 :=
    fun T e => (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e)))))))))).

  #[global]
    Instance UBE_L0 : UBE -< L0 :=
    fun T e => (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e))))))))).

  #[global]
    Instance LLVMExcE_L0 : LLVMExcE dvalue -< L0 :=
    fun T e => (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e)))))))).
  
  #[global]
    Instance OOME_L0 : OOME -< L0  :=
    fun T e => inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e)))))).

  #[global]
    Instance DrawE_L0 : DrawE -< L0 :=
    fun T e => inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e))))).
  
  #[global]
    Instance MemoryE_L0 : MemoryE  -< L0 :=
    fun T e => inr1 (inr1 (inr1 (inr1 (inl1 e)))).

  #[global]
    Instance LocalE_expE_L0 : LocalE raw_id dvalue -< L0 :=
    fun T e => inr1 (inr1 (inr1 (inl1 (inl1 e)))).

  #[global]
    Instance StackE_expE_L0 : StackE raw_id dvalue dvalue -< L0 :=
    fun T e => inr1 (inr1 (inr1 (inl1 (inr1 e)))).
  
  #[global]
    Instance GlobalE_L0 : GlobalE raw_id dvalue -< L0 :=
    fun T e => (inr1 (inr1 (inl1 e))).

  #[global]
    Instance IntrinsincE_L0 : IntrinsicE -< L0 :=
    fun T e => (inr1 (inl1 e)).

  #[global]
    Instance ExternalCallE_L0 : ExternalCallE -< L0 :=
    fun T e => (inl1 e).


  #[global]
    Instance IntrinsiceE_expE_L0 : IntrinsicE  +' exp_E -< L0  :=
    fun T e =>
      match e with
      | inl1 e => inr1 (inl1 e)
      | inr1 e => exp_to_L0 e
      end.


  (* L1 *)
  (*     Definition L1 := ExternalCallE +' IntrinsicE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' DrawE +' OOME +' LLVMExcE dvalue +' UBE +' DebugE +' FailureE. *)

  #[global]
    Instance FailureE_L1 : FailureE -< L1 :=
    fun T e => (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e))))))))).

  #[global]
    Instance DebugE_L1 : DebugE -< L1 :=
    fun T e => (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e))))))))).

  #[global]
    Instance UBE_L1 : UBE -< L1 :=
    fun T e => (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e)))))))).

  #[global]
    Instance LLVMExcE_L1 : LLVMExcE dvalue -< L1 :=
    fun T e => (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e))))))).
  
  #[global]
    Instance OOME_L1 : OOME -< L1  :=
    fun T e => (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e)))))).

  #[global]
    Instance DrawE_L1 : DrawE -< L1 :=
    fun T e => (inr1 (inr1 (inr1 (inr1 (inl1 e))))).
  
  #[global]
    Instance MemoryE_L1 : MemoryE  -< L1 :=
    fun T e => (inr1 (inr1 (inr1 (inl1 e)))).

  #[global]
    Instance LocalE_expE_L1 : LocalE raw_id dvalue -< L1 :=
    fun T e => (inr1 (inr1 (inl1 (inl1 e)))).

  #[global]
    Instance StackE_expE_L1 : StackE raw_id dvalue dvalue -< L1 :=
    fun T e =>  (inr1 (inr1 (inl1 (inr1 e)))).
  
  #[global]
    Instance IntrinsincE_L1 : IntrinsicE -< L1 :=
    fun T e => (inr1 (inl1 e)).

  #[global]
    Instance ExternalCallE_L1 : ExternalCallE -< L1 :=
    fun T e => (inl1 e).

  (* L2 *)
  (* ExternalCallE +' IntrinsicE +' MemoryE +' DrawE +' OOME +' LLVMExcE dvalue +' UBE +' DebugE +' FailureE.    *)

  #[global]
    Instance FailureE_L2 : FailureE -< L2 :=
    fun T e => (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e)))))))).

  #[global]
    Instance DebugE_L2 : DebugE -< L2 :=
    fun T e => (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e)))))))).

  #[global]
    Instance UBE_L2 : UBE -< L2 :=
    fun T e => (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e))))))).

  #[global]
    Instance LLVMExcE_L2 : LLVMExcE dvalue -< L2 :=
    fun T e => (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e)))))).
  
  #[global]
    Instance OOME_L2 : OOME -< L2  :=
    fun T e => (inr1 (inr1 (inr1 (inr1 (inl1 e))))).

  #[global]
    Instance DrawE_L2 : DrawE -< L2 :=
    fun T e => (inr1 (inr1 (inr1 (inl1 e)))).
  
  #[global]
    Instance MemoryE_L2 : MemoryE  -< L2 :=
    fun T e => (inr1 (inr1 (inl1 e))).

  #[global]
    Instance IntrinsincE_L2 : IntrinsicE -< L2 :=
    fun T e => (inr1 (inl1 e)).

  #[global]
    Instance ExternalCallE_L2 : ExternalCallE -< L2 :=
    fun T e => (inl1 e).


    (* L3 *)
  (* ExternalCallE +' DrawE +' OOME +' LLVMExcE dvalue +' UBE +' DebugE +' FailureE. *)

  #[global]
    Instance FailureE_L3 : FailureE -< L3 :=
    fun T e => (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e)))))).

  #[global]
    Instance DebugE_L3 : DebugE -< L3 :=
    fun T e =>  (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e)))))).

  #[global]
    Instance UBE_L3 : UBE -< L3 :=
    fun T e =>  (inr1 (inr1 (inr1 (inr1 (inl1 e))))).

  #[global]
    Instance LLVMExcE_L3 : LLVMExcE dvalue -< L3 :=
    fun T e =>  (inr1 (inr1 (inr1 (inl1 e)))).
  
  #[global]
    Instance OOME_L3 : OOME -< L3  :=
    fun T e =>  (inr1 (inr1 (inl1 e))).

  #[global]
    Instance DrawE_L3 : DrawE -< L3 :=
    fun T e =>  (inr1 (inl1 e)).
  
  #[global]
    Instance ExternalCallE_L3 : ExternalCallE -< L3 :=
    fun T e => (inl1 e).

    (* L4 *)
  (* ExternalCallE +' OOME +' LLVMExcE dvalue +' UBE +' DebugE +' FailureE. *)

  #[global]
    Instance FailureE_L4 : FailureE -< (ExternalCallE +' OOME +' LLVMExcE dvalue +' UBE +' DebugE +' FailureE) :=
    fun T e => (inr1 (inr1 (inr1 (inr1 (inr1 e))))).

  #[global]
    Instance DebugE_L4 : DebugE -< (ExternalCallE +' OOME +' LLVMExcE dvalue +' UBE +' DebugE +' FailureE) :=
    fun T e =>  (inr1 (inr1 (inr1 (inr1 (inl1 e))))).

  #[global]
    Instance UBE_L4 : UBE -< (ExternalCallE +' OOME +' LLVMExcE dvalue +' UBE +' DebugE +' FailureE) :=
    fun T e =>  (inr1 (inr1 (inr1 (inl1 e)))).

  #[global]
    Instance LLVMExcE_L4 : LLVMExcE dvalue -< (ExternalCallE +' OOME +' LLVMExcE dvalue +' UBE +' DebugE +' FailureE) :=
    fun T e =>  (inr1 (inr1 (inl1 e))).
  
  #[global]
    Instance OOME_L4 : OOME -< (ExternalCallE +' OOME +' LLVMExcE dvalue +' UBE +' DebugE +' FailureE) :=
    fun T e =>  (inr1 (inl1 e)).

  #[global]
    Instance ExternalCallE_L4 : ExternalCallE -< (ExternalCallE +' OOME +' LLVMExcE dvalue +' UBE +' DebugE +' FailureE) :=
    fun T e => (inl1 e).
  
  End Events.

  Arguments DrawE {_} _.

  #[export] Hint Unfold L0 L0' L1 L2 L4 L4 L5 L6 : core.

  
(*
Module Make(ADDR : MemoryAddress.ADDRESS)(IP:MemoryAddress.INTPTR)(SIZEOF : Sizeof) <: LLVM_INTERACTIONS(ADDR)(IP)(SIZEOF).
Include LLVM_INTERACTIONS(ADDR)(IP)(SIZEOF).
End Make.
*)
