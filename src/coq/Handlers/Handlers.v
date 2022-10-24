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
     Pick
     UndefinedBehaviour
     MemoryModelImplementation
     OOM
     Concretization.

From Vellvm.Semantics Require Import Memory.Sizeof Memory.MemBytes GepM.

(* Handlers get instantiated over the domain of addresses provided by the memory model *)
Module LLVMEvents64 := LLVMEvents.Make(MemoryModelImplementation.Addr)(MemoryModelImplementation.IP64Bit)(MemoryModelImplementation.FinSizeof).
Module Global64 := Global.Make MemoryModelImplementation.Addr MemoryModelImplementation.IP64Bit MemoryModelImplementation.FinSizeof LLVMEvents64.
Module Local64  := Local.Make  MemoryModelImplementation.Addr MemoryModelImplementation.IP64Bit MemoryModelImplementation.FinSizeof LLVMEvents64.
Module Stack64  := Stack.Make  MemoryModelImplementation.Addr MemoryModelImplementation.IP64Bit MemoryModelImplementation.FinSizeof LLVMEvents64.

Module LLVMEvents := LLVMEvents.Make(MemoryModelImplementation.Addr)(MemoryModelImplementation.BigIP)(MemoryModelImplementation.FinSizeof).
Module Global := Global.Make MemoryModelImplementation.Addr MemoryModelImplementation.BigIP MemoryModelImplementation.FinSizeof LLVMEvents.
Module Local  := Local.Make  MemoryModelImplementation.Addr MemoryModelImplementation.BigIP MemoryModelImplementation.FinSizeof LLVMEvents.
Module Stack  := Stack.Make  MemoryModelImplementation.Addr MemoryModelImplementation.BigIP MemoryModelImplementation.FinSizeof LLVMEvents.

Require Import List.

Import ListNotations.

From Vellvm Require Import
     Utils.Error
     Semantics.MemoryAddress
     Semantics.LLVMEvents
     DynamicTypes.

From ExtLib Require Import
     Structures.Monad.

Import MonadNotation.

(* Module GEP := GepM.Make MemoryModelImplementation.Addr MemoryModelImplementation.BigIP MemoryModelImplementation.FinSizeof LLVMEvents MemoryModelImplementation.FinPTOI MemoryModelImplementation.FinPROV MemoryModelImplementation.FinITOP. *)
(* Module GEP64 := GepM.Make MemoryModelImplementation.Addr MemoryModelImplementation.IP64Bit MemoryModelImplementation.FinSizeof LLVMEvents64 MemoryModelImplementation.FinPTOI MemoryModelImplementation.FinPROV MemoryModelImplementation.FinITOP. *)

(* Module Intrinsics64 := Intrinsics.Make MemoryModelImplementation.Addr MemoryModelImplementation.IP64Bit MemoryModelImplementation.FinSizeof LLVMEvents64. *)
(* Module Intrinsics := Intrinsics.Make MemoryModelImplementation.Addr MemoryModelImplementation.BigIP MemoryModelImplementation.FinSizeof LLVMEvents. *)

(* Module Byte := FinByte MemoryModelImplementation.Addr MemoryModelImplementation.BigIP MemoryModelImplementation.FinSizeof LLVMEvents. *)
(* Module Byte64 := FinByte MemoryModelImplementation.Addr MemoryModelImplementation.IP64Bit MemoryModelImplementation.FinSizeof LLVMEvents64. *)

(* Module SER := Serialization.Make(MemoryModelImplementation.Addr)(MemoryModelImplementation.BigIP)(MemoryModelImplementation.FinSizeof)(LLVMEvents)(MemoryModelImplementation.FinPTOI)(MemoryModelImplementation.FinPROV)(MemoryModelImplementation.FinITOP)(GEP)(Byte). *)
(* Module SER64 := Serialization.Make(MemoryModelImplementation.Addr)(MemoryModelImplementation.IP64Bit)(MemoryModelImplementation.FinSizeof)(LLVMEvents64)(MemoryModelImplementation.FinPTOI)(MemoryModelImplementation.FinPROV)(MemoryModelImplementation.FinITOP)(GEP64)(Byte64). *)

(* Module MEM := MemoryModelImplementation.Make(MemoryModelImplementation.Addr)(MemoryModelImplementation.BigIP)(MemoryModelImplementation.FinSizeof)(LLVMEvents)(MemoryModelImplementation.FinPTOI)(MemoryModelImplementation.FinPROV)(MemoryModelImplementation.FinITOP)(GEP)(Byte). *)
(* Module MEM64 := MemoryModelImplementation.Make(MemoryModelImplementation.Addr)(MemoryModelImplementation.IP64Bit)(MemoryModelImplementation.FinSizeof)(LLVMEvents64)(MemoryModelImplementation.FinPTOI)(MemoryModelImplementation.FinPROV)(MemoryModelImplementation.FinITOP)(GEP64)(Byte64). *)

(* Module MEMORY_THEORY := MemoryModelImplementationTheory.Make(MemoryModelImplementation.Addr)(MemoryModelImplementation.BigIP)(MemoryModelImplementation.FinSizeof)(LLVMEvents)(MemoryModelImplementation.FinPTOI)(MemoryModelImplementation.FinPROV)(MemoryModelImplementation.FinITOP)(GEP)(Byte). *)
(* Module MEMORY_THEORY64 := MemoryModelImplementationTheory.Make(MemoryModelImplementation.Addr)(MemoryModelImplementation.IP64Bit)(MemoryModelImplementation.FinSizeof)(LLVMEvents64)(MemoryModelImplementation.FinPTOI)(MemoryModelImplementation.FinPROV)(MemoryModelImplementation.FinITOP)(GEP64)(Byte64). *)

(* Module Pick64 := Pick.Make MemoryModelImplementation.Addr MemoryModelImplementation.IP64Bit FinSizeof LLVMEvents64 FinPTOI FinPROV FinITOP GEP64 Byte64. *)
(* Module Pick := Pick.Make MemoryModelImplementation.Addr MemoryModelImplementation.BigIP FinSizeof LLVMEvents FinPTOI FinPROV FinITOP GEP Byte. *)

(* Export LLVMEvents LLVMEvents.DV Global Local Stack Pick Intrinsics *)
(*        MEM MEMORY_THEORY UndefinedBehaviour. *)
