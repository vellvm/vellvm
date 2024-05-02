From Vellvm Require Import
  Semantics.LLVMParams.

From LLVM_Memory Require Import
  GepM
  MemBytes
  DvalueBytes.

Module Type MemoryParams (LP : LLVMParams).
  Declare Module GEP : GEPM LP.ADDR LP.PTOI LP.PROV LP.ITOP LP.IP LP.SIZEOF LP.Events.
  Declare Module BYTE_IMPL : ByteImpl LP.ADDR LP.IP LP.SIZEOF LP.Events.
  Declare Module DVALUE_BYTES : DvalueByte LP.
End MemoryParams.

Module Make (LP' : LLVMParams) (GEP' : GEPM LP'.ADDR LP'.PTOI LP'.PROV LP'.ITOP LP'.IP LP'.SIZEOF LP'.Events) (BYTE_IMPL' : ByteImpl LP'.ADDR LP'.IP LP'.SIZEOF LP'.Events) (DVALUE_BYTES' : DvalueByte LP') : MemoryParams LP'
with Module GEP := GEP'
with Module BYTE_IMPL := BYTE_IMPL'
with Module DVALUE_BYTES := DVALUE_BYTES'.
  Module GEP := GEP'.
  Module BYTE_IMPL := BYTE_IMPL'.
  Module DVALUE_BYTES := DVALUE_BYTES'.
End Make.
