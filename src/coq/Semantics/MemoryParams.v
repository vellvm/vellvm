From Vellvm Require Import
     Semantics.LLVMEvents
     Semantics.LLVMParams
     Semantics.GepM
     Semantics.Memory.MemBytes.

Module Type MemoryParams (LP : LLVMParams).
  Declare Module GEP : GEPM LP.ADDR LP.PTOI LP.PROV LP.ITOP LP.IP LP.SIZEOF LP.Events.
  Declare Module BYTE_IMPL : ByteImpl LP.ADDR LP.IP LP.SIZEOF LP.Events.
End MemoryParams.

Module Make (LP' : LLVMParams) (GEP' : GEPM LP'.ADDR LP'.PTOI LP'.PROV LP'.ITOP LP'.IP LP'.SIZEOF LP'.Events) (BYTE_IMPL' : ByteImpl LP'.ADDR LP'.IP LP'.SIZEOF LP'.Events) : MemoryParams LP'.
  Module GEP := GEP'.
  Module BYTE_IMPL := BYTE_IMPL'.
End Make.
