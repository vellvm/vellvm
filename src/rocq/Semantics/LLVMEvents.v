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
     Utils
     Syntax
     Params
     DynamicValues
     EOU
     VellvmIntegers.

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

Section withParams.
  Context {Pa : Params}.

  (* Exceptions are carried around as [dvalue]s *)
  Definition exc := dvalue.
  
  (* Interactions with global variables for the LLVM IR *)
  (* Note: Globals are read-only, except for the initialization. We could want to reflect this in the events themselves. *)
  Variant GlobalE : Type -> Type :=
    | GlobalWrite (id: raw_id) (dv: dvalue) : GlobalE unit
    | GlobalRead  (id: raw_id)              : GlobalE dvalue.
  Definition gwrite {E} `{GlobalE -< E} id dv : itree E _ := trigger (GlobalWrite id dv).
  Definition gread  {E} `{GlobalE -< E} id    : itree E _ := trigger (GlobalRead id).
  
  (* Interactions with local variables for the LLVM IR *)
  Variant LocalE : Type -> Type :=
    | LocalWrite (id: raw_id) (dv: dvalue) : LocalE unit
    | LocalRead  (id: raw_id)              : LocalE dvalue.
  Definition lwrite {E} `{LocalE -< E} id dv : itree E _ := trigger (LocalWrite id dv).
  Definition lread  {E} `{LocalE -< E} id    : itree E _ := trigger (LocalRead id).

  Variant StackE : Type -> Type :=
    | StackPush (args : list (raw_id * dvalue))
                      : StackE unit                   (* Pushes a fresh environment during a call *)
    | StackPop        : StackE unit                   (* Pops it back during a ret *)
    | StackRaise      : exc -> StackE unit             (* Place exception onto the stack, does not pop *)
    | StackGetExc     : StackE (option exc).          (* Fetches and clears the currently raised exception if there is one *)
  Definition stack_push        {E} `{StackE -< E} args : itree E _ := trigger (StackPush args).
  Definition stack_pop         {E} `{StackE -< E}      : itree E _ := trigger StackPop.
  Definition stack_raise       {E} `{StackE -< E} e    : itree E _ := trigger (StackRaise e).
  Definition stack_get_exc     {E} `{StackE -< E}      : itree E _ := trigger StackGetExc.

  (* Interactions with the memory *)
  Variant MemoryE : Type -> Type :=
    | MemPush : MemoryE unit
    | MemPop  : MemoryE unit
    | Alloca  (t : dtyp) (num_elements : N) (align : option N) :  MemoryE dvalue
    | Load   (t : dtyp) (a : dvalue) : MemoryE dvalue
    | Store (t : dtyp) (a : dvalue) (v : dvalue) : MemoryE unit
    | Conv (cv : impure_conversion) (t_from : dtyp) (v : dvalue) (t_to : dtyp) : MemoryE dvalue
  .
  
  Definition mem_push {E} `{MemoryE -< E}                      : itree E _ := trigger MemPush.
  Definition mem_pop  {E} `{MemoryE -< E}                      : itree E _ := trigger MemPop.
  Definition alloca   {E} `{MemoryE -< E} t num_elements align : itree E _ := trigger (Alloca t num_elements align).
  Definition load     {E} `{MemoryE -< E} t a                  : itree E _ := trigger (Load t a).
  Definition store    {E} `{MemoryE -< E} t a v                : itree E _ := trigger (Store t a v).
  Definition conv  {E} `{MemoryE -< E} cv t_from v t_to     : itree E _ := trigger (Conv cv t_from v t_to).
  
  (* An event resolving the non-determinism induced by undef. The argument _P_
   is intended to be a predicate over the set of dvalues _u_ can take such that
   if it is not satisfied, the only possible execution is to raise _UB_. *)
  Variant DrawE : Type -> Type :=
    | Draw (dt : dtyp) : DrawE dvalue.
  Definition draw {E} `{DrawE -< E} dt : itree E _ := trigger (Draw dt).

    (* Generic calls, refined by [denote_mcfg] *)
  Variant CallE : Type -> Type :=
    | Call        : forall (t:dtyp) (f:dvalue) (args:list dvalue), CallE (exc + dvalue).
  Definition call {E} `{CallE -< E} t f args : itree E _ := trigger (Call t f args).

  (* ExternalCallE values are the "observable" events by which one should compare the 
       equivalence of two LLVM IR programs.  These should never be interpreted away
       by the rocq semantics. However, for practicality, we _do_ interpet some calls that
       generate outputs to [stdout] (SAZ: and eventuall[stderr]).  The stream of bytes
       visible in [IO_stdout] events is the data printed to [stdout].

       - [ExternalCall] represents interactions with the OS
       - [IO_stdout] represents bytes sent to [stdout]
       - [IO_stderr] represents bytes sent to [stderr]

       The latter two are actually printed to the console by [interpreter.ml]
   *)
  Variant ExternalCallE : Type -> Type :=
    | ExternalCall (t : dtyp) (f : dvalue) (args : list dvalue) :
      ExternalCallE dvalue
    (* This event corresponds to writing to the [stdout] channel. ] *)                              
    | IO_stdout (str : list int8) :
      ExternalCallE unit
    (* This event corresponds to writing to the [stderr] channel. ] *)
    | IO_stderr (str : list int8) :
      ExternalCallE unit.
  Definition external_call {E} `{ExternalCallE -< E} t f args : itree E _ := trigger (ExternalCall t f args).
  Definition io_stdout     {E} `{ExternalCallE -< E} str      : itree E _ := trigger (IO_stdout str).
  Definition io_stderr     {E} `{ExternalCallE -< E} str      : itree E _ := trigger (IO_stderr str).

  (* Call to an intrinsic whose implementation do not rely on the implementation of the memory model *)
  (* Intrinsics may raise an exception by returning inl *)
  Variant IntrinsicE : Type -> Type :=
    | Intrinsic (t : dtyp) (f : string) (args : list dvalue) (vararg : option ptr) :
      IntrinsicE (exc + dvalue).
  Definition intrinsic {E} `{IntrinsicE -< E} t f args vararg : itree E _ := trigger (Intrinsic t f args vararg).
  
  (* LLVM exceptions *)
  Variant LLVMExcE : Type -> Type :=
    | LLVMExc : exc -> LLVMExcE void.

  Definition raiseLLVM {E} {A} `{LLVMExcE -< E} (e : exc) : itree E A :=
    trigger_cast (LLVMExc e).

  (* See src/ml/Extract.v for the special handling of these operation. *)
  (* This function can be replaced with print operations  during extraction
     to print the error messages of Throw and (indirectly) ThrowUB.
      - set_loc imperatively records the current source location; it takes
        the raw [file_info] (not a formatted string) so that the hot path
        pays one pointer write — [get_loc] formats on demand
        ([AstLib.location_string]). It returns the empty string, but we
        need to use its result to force extraction
      - print_msg call `print_string`
   *)
  Record printer :=
    mk_printer {
        printer_set_loc : option file_info -> string ;
        printer_print_msg : string -> unit ;
        printer_get_loc : unit -> string ;
      }.

  Definition printer_object : printer :=
    mk_printer (fun (_:option file_info) => "") (fun (_:string) => tt) (fun (_:unit) => "").

  Definition set_loc : option file_info -> string := printer_object.(printer_set_loc).
  Definition print_msg : string -> unit := printer_object.(printer_print_msg).
  Definition get_loc : unit -> string := printer_object.(printer_get_loc).
 
  (* Undefined behaviour carries a string. *)
  Variant UBE : Type -> Type :=
    | ThrowUB : unit -> UBE void.

  (** Since the output type of [ThrowUB] is [void], we can make it an action
    with any return type. *)
  Definition raiseUB {E : Type -> Type} `{UBE -< E} {X}
    (msg : string) : itree E X :=
    trigger_cast (ThrowUB (print_msg msg)).

  (* Failure. Carries a string for a message. *)
  Variant FailureE : Type -> Type :=
    | Throw : unit -> FailureE void.

  Definition raise {E} {A} `{FailureE -< E} (msg : string) : itree E A :=
    trigger_cast (Throw (print_msg msg)).

  (* Out of memory / abort. Carries a string for a message. *)
  Variant OOME : Type -> Type :=
    | ThrowOOM : unit -> OOME void.

  (** Since the output type of [ThrowOOM] is [void], we can make it an action
    with any return type. *)
  Definition raiseOOM {E : Type -> Type} `{OOME -< E} {X}
    (msg : string) : itree E X :=
    trigger_cast (ThrowOOM (print_msg msg)).

  (* Debug is identical to the "Trace" effect from the itrees library,
   but debug is probably a less confusing name for us. *)
  Variant DebugE : Type -> Type :=
    | Debug : unit -> DebugE unit.

  (* Utilities to conveniently trigger debug events *)
  Definition debug {E} `{DebugE -< E} (msg : string) : itree E unit :=
    trigger (Debug (print_msg msg)).

  (* Core effects. *)
  Definition CFGEtop  := CallE +' ExternalCallE +' IntrinsicE +' GlobalE +' (LocalE +' StackE) +' MemoryE +' DrawE +' OOME +' LLVMExcE +' UBE +' DebugE +' FailureE.
  Definition MCFGEtop :=          ExternalCallE +' IntrinsicE +' GlobalE +' (LocalE +' StackE) +' MemoryE +' DrawE +' OOME +' LLVMExcE +' UBE +' DebugE +' FailureE.
  Definition CFGtop   := itree CFGEtop.
  Definition MCFGtop  := itree MCFGEtop.
  Definition withCall : MCFGtop ~> CFGtop := translate inr1.
  
  (* For multiple CFG, after interpreting [LocalE] and [MemoryE] and [IntrinsicE] that are memory intrinsics and [DrawE]*)
  Definition MCFGEbot := ExternalCallE +' OOME +' LLVMExcE +' UBE +' DebugE +' FailureE.
  Definition MCFGbot  := itree MCFGEbot.

End withParams.

Arguments DrawE {_} _.

#[export] Hint Unfold CFGEtop CFGtop MCFGEtop MCFGtop MCFGEbot MCFGbot : core.

Definition EOU_to_itree {E} `{FailureE -< E} `{OOME -< E} `{UBE -< E} :
  EOU ~> itree E :=
  fun _ x => match x with
          | raise_error s => raise s
          | raise_oom   s => raiseOOM s
          | raise_ub    s => raiseUB s
          | raise_ret   v => ret v
          end.

