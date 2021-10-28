From Vellvm Require Import
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Semantics.GepM
     Semantics.LLVMEvents

     Handlers.Global
     Handlers.Local
     Handlers.Stack
     Handlers.Intrinsics
     Handlers.Pick
     Handlers.UndefinedBehaviour
     Handlers.FiniteMemory
     Handlers.FiniteMemoryTheory.

Module Lang (ADDR : ADDRESS) (IP : INTPTR) (SIZEOF : Sizeof) (PTOI : PTOI ADDR) (PROV : PROVENANCE ADDR) (ITOP : ITOP ADDR PROV).
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

  Export Events Events.DV Global Local Stack Pick Intrinsics
         MEM MEMORY_THEORY UndefinedBehaviour.
End Lang.
