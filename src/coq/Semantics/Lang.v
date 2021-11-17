From Vellvm Require Import
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Semantics.Memory.MemBytes
     Semantics.LLVMParams
     Semantics.GepM
     Semantics.LLVMEvents
     Semantics.Denotation
     Semantics.MemoryParams
     Semantics.SerializationParams

     Handlers.Global
     Handlers.Local
     Handlers.Stack
     Handlers.Intrinsics
     Handlers.Pick
     Handlers.FiniteMemory
     Handlers.FiniteMemoryTheory.

Module Type Lang (LP: LLVMParams).
  Import LP.

  (* Events *)
  Module Events := LLVMEvents.Make ADDR IP SIZEOF.

  (* Handlers *)
  Module Global     := Global.Make ADDR IP SIZEOF Events.
  Module Local      := Local.Make ADDR IP SIZEOF Events.
  Module Stack      := Stack.Make ADDR IP SIZEOF Events.
  Module Intrinsics := Intrinsics.Make ADDR IP SIZEOF Events.

  (* Memory *)
  Module GEP  := GepM.Make ADDR IP SIZEOF Events PTOI PROV ITOP.
  Module Byte := FiniteMemory.FinByte ADDR IP SIZEOF Events.

  Module MP := MemoryParams.Make LP Events GEP Byte.

  Module MEM  := FiniteMemory.Make LP Events MP.

  (* Serialization *)
  Module SP := SerializationParams.Make LP Events MP.
  
  Module MEMORY_THEORY := FiniteMemoryTheory.Make LP Events MP SP MEM.

  (* Pick handler (depends on memory / serialization) *)
  Module Pick := Pick.Make LP Events MP SP.

  (* Denotation *)
  Module D := Denotation LP Events MP SP.

  Export Events Events.DV Global Local Stack Pick Intrinsics
         MEM MEMORY_THEORY SP.SER D.
End Lang.

Module Make (LP : LLVMParams) <: Lang LP.
  Include Lang LP.
End Make.
