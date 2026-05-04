From Vellvm Require Import
     Semantics.LLVMParams
     Semantics.GepM
     Semantics.Memory.MemoryBytes.

Module Type MEMORY_PARAMS (LP : LLVMParams).
  Declare Module GEP : GEPM LP.
  Declare Module MBYTES : MemoryByte LP.
End MEMORY_PARAMS.

Module Make (LP : LLVMParams) : MEMORY_PARAMS LP.
  Module GEP := GepM.Make LP.
  Module MBYTES := MemoryBytes.Make LP.
End Make.
