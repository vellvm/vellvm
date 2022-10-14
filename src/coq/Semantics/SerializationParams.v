From Vellvm Require Import
     Semantics.LLVMParams
     Semantics.MemoryParams
     Handlers.Serialization.

Module Type SerializationParams (LP : LLVMParams) (MP : MemoryParams LP).
  Module SERBASE := Serialization.MakeBase LP MP.
  Module SER := Serialization.Make LP MP SERBASE.
End SerializationParams.

Module Make (LP' : LLVMParams) (MP' : MemoryParams LP') : SerializationParams LP' MP'.
  Include SerializationParams LP' MP'.
End Make.
