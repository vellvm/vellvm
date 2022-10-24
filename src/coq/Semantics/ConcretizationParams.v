From Vellvm Require Import
     Semantics.LLVMParams
     Semantics.MemoryParams
     Handlers.Concretization.

Module Type ConcretizationParams (LP : LLVMParams) (MP : MemoryParams LP).
  Module CONCBASE := Concretization.MakeBase LP MP.
  Module CONC := Concretization.Make LP MP CONCBASE.
End ConcretizationParams.

Module Make (LP' : LLVMParams) (MP' : MemoryParams LP') : ConcretizationParams LP' MP'.
  Include ConcretizationParams LP' MP'.
End Make.
