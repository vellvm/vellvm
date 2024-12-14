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
     Concretization.

From LLVM_Memory Require Import
  GepM
  Sizeof
  MemBytes
  FiniteIntptr
  FiniteSizeof.

From Mem Require Import
  FiniteAddresses
  InfiniteAddresses.

(* Handlers get instantiated over the domain of addresses provided by the memory model *)
Module LLVMEvents64 := LLVMEvents.Make(FinAddr)(IP64Bit)(FinSizeof).
Module Global64 := Global.Make FinAddr IP64Bit FinSizeof LLVMEvents64.
Module Local64  := Local.Make FinAddr IP64Bit FinSizeof LLVMEvents64.
Module Stack64  := Stack.Make FinAddr IP64Bit FinSizeof LLVMEvents64.

Module LLVMEvents := LLVMEvents.Make(InfAddr)(BigIP)(FinSizeof).
Module Global := Global.Make InfAddr BigIP FinSizeof LLVMEvents.
Module Local  := Local.Make InfAddr BigIP FinSizeof LLVMEvents.
Module Stack  := Stack.Make InfAddr BigIP FinSizeof LLVMEvents.
