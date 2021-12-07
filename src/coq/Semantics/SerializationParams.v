From Vellvm Require Import
     Semantics.LLVMEvents
     Semantics.LLVMParams
     Semantics.GepM
     Semantics.Memory.MemBytes
     Semantics.MemoryParams
     Handlers.Serialization.

Module Type SerializationParams (LP : LLVMParams) (Events : LLVM_INTERACTIONS LP.ADDR LP.IP LP.SIZEOF) (MP : MemoryParams LP Events).
  Module SERBASE := Serialization.MakeBase LP Events MP.
  Module SER := Serialization.Make LP Events MP SERBASE.
End SerializationParams.

Module Make (LP' : LLVMParams) (Events : LLVM_INTERACTIONS LP'.ADDR LP'.IP LP'.SIZEOF) (MP' : MemoryParams LP' Events) : SerializationParams LP' Events MP'.
  Include SerializationParams LP' Events MP'.
End Make.
