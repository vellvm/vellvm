From Vellvm Require Import
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Semantics.Memory.MemBytes
     Semantics.LLVMParams
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

Module FMP (LP' : LLVMParams) (Events' : LLVM_INTERACTIONS LP'.ADDR LP'.IP LP'.SIZEOF) (GEP' : GEPM LP'.ADDR LP'.IP LP'.SIZEOF Events') (BYTE' : ByteImpl LP'.ADDR LP'.IP LP'.SIZEOF Events') : FinMemoryParams LP' Events'.
  Module LP := LP'.
  Module Events := Events'.
  Module GEP := GEP'.
  Module BYTE_IMPL := BYTE'.
End FMP.

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

  Module FMP := FMP LP Events GEP Byte.

  (* Pick handler (depends on memory) *)
  Module Pick := Pick.Make ADDR IP SIZEOF Events PTOI PROV ITOP GEP Byte.

  Module MEM  := FiniteMemory.Make LP Events FMP.
  Module MEMORY_THEORY := FiniteMemoryTheory.Make LP Events FMP MEM.

  (* Serialization *)
  Module SER := Serialization.Make ADDR IP SIZEOF Events PTOI PROV ITOP GEP Byte.

  (* Denotation *)
  Module D := Denotation ADDR IP SIZEOF Events PTOI PROV ITOP GEP Byte.

  Export Events Events.DV Global Local Stack Pick Intrinsics
         MEM MEMORY_THEORY UndefinedBehaviour SER D.
End Lang.

Module Make (LP : LLVMParams) <: Lang LP.
  Include Lang LP.
End Make.
