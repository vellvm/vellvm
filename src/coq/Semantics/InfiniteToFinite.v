From Vellvm Require Import
     Semantics.InterpretationStack
     Semantics.LLVMEvents
     Semantics.Denotation
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Semantics.Lang
     Semantics.InterpretationStack.

Module Type InfiniteToFinite (LLVM1 : InterpreterStack) (LLVM2 : InterpreterStack).
  (* Parameter oom_refine : LLVM1. *)
End InfiniteToFinite.
