From Vellvm Require Import
     Semantics.LLVMParams
     Semantics.MemoryParams
     Semantics.Memory.MemBytes
     Handlers.Concretization.

Module Type ConcretizationParams (LP : LLVMParams) (MP : MemoryParams LP) (ByteMod : ByteModule LP.ADDR LP.IP LP.SIZEOF LP.Events MP.BYTE_IMPL).
  Module CONCBASE := Concretization.MakeBase LP MP ByteMod.
  Module CONC := Concretization.Make LP MP ByteMod CONCBASE.
End ConcretizationParams.

Module Make (LP' : LLVMParams) (MP' : MemoryParams LP') (ByteMod' : ByteModule LP'.ADDR LP'.IP LP'.SIZEOF LP'.Events MP'.BYTE_IMPL) : ConcretizationParams LP' MP' ByteMod'.
  Include ConcretizationParams LP' MP' ByteMod'.
End Make.
