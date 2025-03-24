From Vellvm Require Import
     Semantics.LLVMParams
     Semantics.MemoryParams
     Semantics.Memory.MemBytes
     Handlers.Concretization.

Module Type ConcretizationParams (LP : LLVMParams) (MP : MemoryParams LP) (Byte : ByteModule LP.ADDR LP.IP LP.SIZEOF LP.Events MP.BYTE_IMPL).
  Module CONCBASE := Concretization.MakeBase LP MP Byte.
  Module CONC := Concretization.Make LP MP Byte CONCBASE.
End ConcretizationParams.

Module Make (LP' : LLVMParams) (MP' : MemoryParams LP') (Byte' : ByteModule LP'.ADDR LP'.IP LP'.SIZEOF LP'.Events MP'.BYTE_IMPL) : ConcretizationParams LP' MP' Byte'.
  Include ConcretizationParams LP' MP' Byte'.
End Make.
