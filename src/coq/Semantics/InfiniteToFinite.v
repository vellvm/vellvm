From Vellvm Require Import
     Semantics.InterpretationStack
     Semantics.LLVMEvents
     Semantics.Denotation
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Semantics.Lang
     Semantics.InterpretationStack
     Semantics.TopLevel.

Module InfiniteToFinite (IS1 : InterpreterStack) (IS2 : InterpreterStack) (LLVM1 : LLVMTopLevel IS1) (LLVM2 : LLVMTopLevel IS2).
  (* Parameter oom_refine : LLVM1. *)
End InfiniteToFinite.
