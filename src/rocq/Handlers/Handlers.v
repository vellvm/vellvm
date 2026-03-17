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
     OOM
     Concretization
     MemoryModelImplementation.



From Vellvm.Semantics Require Import Memory.Sizeof Memory.MemBytes GepM.

(* Handlers get instantiated over the domain of addresses provided by the memory model *)

Module Global64 := Global.Make MemoryModelImplementation.LLVMParams64BitIntptr.
Module Local64  := Local.Make MemoryModelImplementation.LLVMParams64BitIntptr.
Module Stack64  := Stack.Make MemoryModelImplementation.LLVMParams64BitIntptr.

Module Global := Global.Make MemoryModelImplementation.LLVMParamsBigIntptr.
Module Local  := Local.Make MemoryModelImplementation.LLVMParamsBigIntptr.
Module Stack  := Stack.Make MemoryModelImplementation.LLVMParamsBigIntptr.
