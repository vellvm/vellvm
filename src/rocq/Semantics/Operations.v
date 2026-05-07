From Vellvm Require Import
  Semantics.LLVMParams
  Semantics.Gep
  Semantics.Select
  Semantics.Compare
  Semantics.Conversion
  Semantics.Memory.MemoryBytes.

Module Operations (LP : LLVMParams).
  Module GEP     := Gep.GEP LP.
  Module SELECT  := Select.SELECT LP.
  Module COMPARE := Compare.COMPARE LP.
  Module MBYTES  := MemoryBytes.Make LP.
  Module CONVERT := Conversion.CONVERT LP MBYTES.
End Operations.
