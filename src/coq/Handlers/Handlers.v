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
     Memory
     MemoryTheory
     Pick
.

(* Handlers get instantiated over the domain of addresses provided by the memory model *)
Module LLVMEvents := LLVMEvents.Make(Memory.Addr).
Module Global := Global.Make Memory.Addr LLVMEvents.
Module Local  := Local.Make  Memory.Addr LLVMEvents.
Module Stack  := Stack.Make  Memory.Addr LLVMEvents.
Module Intrinsics := Intrinsics.Make Memory.Addr LLVMEvents.
Module MemTheory := MemoryTheory.Make(LLVMEvents).
Module Pick := Pick.Make Memory.Addr LLVMEvents.

Export LLVMEvents LLVMEvents.DV Global Local Stack MemTheory MemTheory.Mem Pick Intrinsics.
