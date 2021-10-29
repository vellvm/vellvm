From Vellvm Require Import
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Semantics.Lang
     Semantics.InterpretationStack.

Module Type LLVMInstance (ADDR : ADDRESS) (IP : INTPTR) (SIZEOF : Sizeof) (PTOI : PTOI ADDR) (PROV : PROVENANCE ADDR) (ITOP : ITOP ADDR PROV).
  Declare Module L : Lang ADDR IP SIZEOF PTOI PROV ITOP.
  Declare Module IS : InterpreterStack ADDR IP SIZEOF PTOI PROV ITOP L.
End LLVMInstance.

Module Make (ADDR : ADDRESS) (IP : INTPTR) (SIZEOF : Sizeof) (PTOI : PTOI ADDR) (PROV : PROVENANCE ADDR) (ITOP : ITOP ADDR PROV) : LLVMInstance ADDR IP SIZEOF PTOI PROV ITOP.
  Module L := Lang.Make ADDR IP SIZEOF PTOI PROV ITOP.
  Module IS := InterpretationStack.Make ADDR IP SIZEOF PTOI PROV ITOP L.
End Make.

Module LLVM_BigIntptr := Make FiniteMemory.Addr FiniteMemory.BigIP FiniteMemory.FinSizeof FiniteMemory.FinPTOI FiniteMemory.FinPROV FiniteMemory.FinITOP.

Module LLVM_64BitIntptr := Make FiniteMemory.Addr FiniteMemory.IP64Bit FiniteMemory.FinSizeof FiniteMemory.FinPTOI FiniteMemory.FinPROV FiniteMemory.FinITOP.
