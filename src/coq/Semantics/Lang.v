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
     Handlers.MemoryModel
     Handlers.MemoryInterpreters
     Handlers.MemoryModelTheory.

Module Type Lang (LP: LLVMParams).
  Export LP.

  (* Handlers *)
  Module Global     := Global.Make ADDR IP SIZEOF LP.Events.
  Module Local      := Local.Make ADDR IP SIZEOF LP.Events.
  Module Stack      := Stack.Make ADDR IP SIZEOF LP.Events.
  Module Intrinsics := Intrinsics.Make ADDR IP SIZEOF LP.Events.

  (* Memory *)
  Declare Module GEP  : GEPM ADDR IP SIZEOF LP.Events.
  Declare Module Byte : ByteImpl ADDR IP SIZEOF LP.Events.

  Module MP := MemoryParams.Make LP GEP Byte.

  Declare Module MEM : MemoryModel LP MP.
  Module MEMINTERP := MemoryInterpreters.Make LP MP MEM.

  (* Serialization *)
  Module SP := SerializationParams.Make LP MP.
  
  Declare Module MEMORY_THEORY : MemoryModelTheory LP MP SP MEM MEMINTERP.

  (* Pick handler (depends on memory / serialization) *)
  Module Pick := Pick.Make LP MP SP.

  (* Denotation *)
  Module D := Denotation LP MP SP.

  Export Events Events.DV Global Local Stack Pick Intrinsics
         MEM MEMORY_THEORY SP.SER D.
End Lang.

Module Make (LP : LLVMParams) <: Lang LP.
  Include Lang LP.
End Make.
