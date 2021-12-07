From Vellvm Require Import
     Semantics.LLVMEvents
     Semantics.LLVMParams
     Semantics.GepM
     Semantics.Memory.MemBytes.

Module Type MemoryParams (LP : LLVMParams) (Events : LLVM_INTERACTIONS LP.ADDR LP.IP LP.SIZEOF).
  Declare Module GEP : GEPM LP.ADDR LP.IP LP.SIZEOF Events.
  Declare Module BYTE_IMPL : ByteImpl LP.ADDR LP.IP LP.SIZEOF Events.
End MemoryParams.

Module Make (LP' : LLVMParams) (Events' : LLVM_INTERACTIONS LP'.ADDR LP'.IP LP'.SIZEOF) (GEP' : GEPM LP'.ADDR LP'.IP LP'.SIZEOF Events') (BYTE_IMPL' : ByteImpl LP'.ADDR LP'.IP LP'.SIZEOF Events') : MemoryParams LP' Events'.
  Module GEP := GEP'.
  Module BYTE_IMPL := BYTE_IMPL'.
End Make.
