(** * Handlers for VIR's events *)

(**
   Reexport the handlers implementing the effects of the VIR's events for:
   * manipulating the global environment;
   * manipulating the local environment;
   * manipulating a stack of local environment;
   * manipulating the memory;
   * calling intrinsics;
   * collecting the set semantics of symbolic expressions denoting [uvalue]s;
   * interpreting undefined behaviors according to the "anything can happen"
   (without time traveling) policy.

   In the case of the non-deterministic handlers (for [pickE] and [UBE]), two
   handlers are provided: a propositional model, and an executable interpreter.

   For each handler, up-to-tau equations are provided to commute them with [Ret],
   [bind], [vis] and [trigger], as well as the proof that they respect [eutt].
 *)

From Vellvm.Handlers Require Export
     Global
     Local
     Stack
     Intrinsics
     FiniteMemory
     FiniteMemoryTheory
     Pick
     OOM
     Serialization.

From Vellvm.Semantics Require Import Memory.Sizeof Memory.MemBytes GepM.

(* Handlers get instantiated over the domain of addresses provided by the memory model *)
Module LLVMEvents64 := LLVMEvents.Make(FiniteMemory.Addr)(FiniteMemory.IP64Bit)(FiniteMemory.FinSizeof).
Module Global64 := Global.Make FiniteMemory.Addr FiniteMemory.IP64Bit FiniteMemory.FinSizeof LLVMEvents64.
Module Local64  := Local.Make  FiniteMemory.Addr FiniteMemory.IP64Bit FiniteMemory.FinSizeof LLVMEvents64.
Module Stack64  := Stack.Make  FiniteMemory.Addr FiniteMemory.IP64Bit FiniteMemory.FinSizeof LLVMEvents64.

Module LLVMEvents := LLVMEvents.Make(FiniteMemory.Addr)(FiniteMemory.BigIP)(FiniteMemory.FinSizeof).
Module Global := Global.Make FiniteMemory.Addr FiniteMemory.BigIP FiniteMemory.FinSizeof LLVMEvents.
Module Local  := Local.Make  FiniteMemory.Addr FiniteMemory.BigIP FiniteMemory.FinSizeof LLVMEvents.
Module Stack  := Stack.Make  FiniteMemory.Addr FiniteMemory.BigIP FiniteMemory.FinSizeof LLVMEvents.

Require Import List ZArith String.
Import ListNotations.

From Vellvm Require Import
     Utils.Error
     Semantics.MemoryAddress
     Semantics.LLVMEvents
     DynamicTypes.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

Import MonadNotation.

(* Module GEP := GepM.Make FiniteMemory.Addr FiniteMemory.BigIP FiniteMemory.FinSizeof LLVMEvents FiniteMemory.FinPTOI FiniteMemory.FinPROV FiniteMemory.FinITOP. *)
(* Module GEP64 := GepM.Make FiniteMemory.Addr FiniteMemory.IP64Bit FiniteMemory.FinSizeof LLVMEvents64 FiniteMemory.FinPTOI FiniteMemory.FinPROV FiniteMemory.FinITOP. *)

(* Module Intrinsics64 := Intrinsics.Make FiniteMemory.Addr FiniteMemory.IP64Bit FiniteMemory.FinSizeof LLVMEvents64. *)
(* Module Intrinsics := Intrinsics.Make FiniteMemory.Addr FiniteMemory.BigIP FiniteMemory.FinSizeof LLVMEvents. *)

(* Module Byte := FinByte FiniteMemory.Addr FiniteMemory.BigIP FiniteMemory.FinSizeof LLVMEvents. *)
(* Module Byte64 := FinByte FiniteMemory.Addr FiniteMemory.IP64Bit FiniteMemory.FinSizeof LLVMEvents64. *)

(* Module SER := Serialization.Make(FiniteMemory.Addr)(FiniteMemory.BigIP)(FiniteMemory.FinSizeof)(LLVMEvents)(FiniteMemory.FinPTOI)(FiniteMemory.FinPROV)(FiniteMemory.FinITOP)(GEP)(Byte). *)
(* Module SER64 := Serialization.Make(FiniteMemory.Addr)(FiniteMemory.IP64Bit)(FiniteMemory.FinSizeof)(LLVMEvents64)(FiniteMemory.FinPTOI)(FiniteMemory.FinPROV)(FiniteMemory.FinITOP)(GEP64)(Byte64). *)

(* Module MEM := FiniteMemory.Make(FiniteMemory.Addr)(FiniteMemory.BigIP)(FiniteMemory.FinSizeof)(LLVMEvents)(FiniteMemory.FinPTOI)(FiniteMemory.FinPROV)(FiniteMemory.FinITOP)(GEP)(Byte). *)
(* Module MEM64 := FiniteMemory.Make(FiniteMemory.Addr)(FiniteMemory.IP64Bit)(FiniteMemory.FinSizeof)(LLVMEvents64)(FiniteMemory.FinPTOI)(FiniteMemory.FinPROV)(FiniteMemory.FinITOP)(GEP64)(Byte64). *)

(* Module MEMORY_THEORY := FiniteMemoryTheory.Make(FiniteMemory.Addr)(FiniteMemory.BigIP)(FiniteMemory.FinSizeof)(LLVMEvents)(FiniteMemory.FinPTOI)(FiniteMemory.FinPROV)(FiniteMemory.FinITOP)(GEP)(Byte). *)
(* Module MEMORY_THEORY64 := FiniteMemoryTheory.Make(FiniteMemory.Addr)(FiniteMemory.IP64Bit)(FiniteMemory.FinSizeof)(LLVMEvents64)(FiniteMemory.FinPTOI)(FiniteMemory.FinPROV)(FiniteMemory.FinITOP)(GEP64)(Byte64). *)

(* Module Pick64 := Pick.Make FiniteMemory.Addr FiniteMemory.IP64Bit FinSizeof LLVMEvents64 FinPTOI FinPROV FinITOP GEP64 Byte64. *)
(* Module Pick := Pick.Make FiniteMemory.Addr FiniteMemory.BigIP FinSizeof LLVMEvents FinPTOI FinPROV FinITOP GEP Byte. *)

(* Export LLVMEvents LLVMEvents.DV Global Local Stack Pick Intrinsics *)
(*        MEM MEMORY_THEORY UndefinedBehaviour. *)
