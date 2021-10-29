From Vellvm Require Import
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Semantics.Memory.MemBytes
     Semantics.GepM
     Semantics.LLVMEvents
     Semantics.Denotation

     Handlers.Global
     Handlers.Local
     Handlers.Stack
     Handlers.Intrinsics
     Handlers.Pick
     Handlers.UndefinedBehaviour
     Handlers.FiniteMemory
     Handlers.FiniteMemoryTheory.

Module Type Lang (ADDR : ADDRESS) (IP : INTPTR) (SIZEOF : Sizeof) (PTOI : PTOI ADDR) (PROV : PROVENANCE ADDR) (ITOP : ITOP ADDR PROV).
  (* Events *)
  Declare Module Events : LLVMEvents.LLVM_INTERACTIONS ADDR IP SIZEOF.

  (* Handlers *)
  Module Global     := Global.Make ADDR IP SIZEOF Events.
  Module Local      := Local.Make ADDR IP SIZEOF Events.
  Module Stack      := Stack.Make ADDR IP SIZEOF Events.
  Module Intrinsics := Intrinsics.Make ADDR IP SIZEOF Events.

  (* Memory *)
  Module GEP  := GepM.Make ADDR IP SIZEOF Events PTOI PROV ITOP.
  Declare Module Byte : ByteImpl ADDR IP SIZEOF Events.

  (* Pick handler (depends on memory) *)
  Module Pick := Pick.Make ADDR IP SIZEOF Events PTOI PROV ITOP GEP Byte.

  Module MEM  := FiniteMemory.Make ADDR IP SIZEOF Events PTOI PROV ITOP GEP Byte.
  Declare Module MEMORY_THEORY : FiniteMemoryTheory.MEMORY_THEORY ADDR IP SIZEOF Events PTOI PROV ITOP GEP Byte.

  (* Serialization *)
  Module SER := Serialization.Make ADDR IP SIZEOF Events PTOI PROV ITOP GEP Byte.

  (* Denotation *)
  Module D := Denotation ADDR IP SIZEOF Events PTOI PROV ITOP GEP Byte.

  Export Events Events.DV Global Local Stack Pick Intrinsics
         MEM MEMORY_THEORY UndefinedBehaviour SER D.
End Lang.

Module Make (ADDR : ADDRESS) (IP : INTPTR) (SIZEOF : Sizeof) (PTOI : PTOI ADDR) (PROV : PROVENANCE ADDR) (ITOP : ITOP ADDR PROV) <: Lang ADDR IP SIZEOF PTOI PROV ITOP.
  (* Events *)
  Module Events := LLVMEvents.Make ADDR IP SIZEOF.

  (* Handlers *)
  Module Global     := Global.Make ADDR IP SIZEOF Events.
  Module Local      := Local.Make ADDR IP SIZEOF Events.
  Module Stack      := Stack.Make ADDR IP SIZEOF Events.
  Module Intrinsics := Intrinsics.Make ADDR IP SIZEOF Events.

  (* Memory *)
  Module GEP  := GepM.Make ADDR IP SIZEOF Events PTOI PROV ITOP.
  Module Byte := FinByte ADDR IP SIZEOF Events.

  (* Pick handler (depends on memory) *)
  Module Pick := Pick.Make ADDR IP SIZEOF Events PTOI PROV ITOP GEP Byte.

  Module MEM  := FiniteMemory.Make ADDR IP SIZEOF Events PTOI PROV ITOP GEP Byte.
  Module MEMORY_THEORY := FiniteMemoryTheory.Make ADDR IP SIZEOF Events PTOI PROV ITOP GEP Byte.

  (* Serialization *)
  Module SER := Serialization.Make ADDR IP SIZEOF Events PTOI PROV ITOP GEP Byte.

  (* Denotation *)
  Module D := Denotation ADDR IP SIZEOF Events PTOI PROV ITOP GEP Byte.

  Export Events Events.DV Global Local Stack Pick Intrinsics
         MEM MEMORY_THEORY UndefinedBehaviour SER D.
End Make.

