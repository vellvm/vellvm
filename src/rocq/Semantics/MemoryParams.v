From Vellvm Require Import
     Semantics.LLVMParams
     Semantics.GepM
     Semantics.Memory.MemBytes
     Semantics.Memory.DvalueBytes.

Module Type MEMORY_PARAMS (LP : LLVMParams).
  Declare Module GEP : GEPM LP.
  Declare Module BYTE_IMPL : ByteImpl LP.
  Declare Module DVALUE_BYTES : DvalueByte LP.
End MEMORY_PARAMS.

Module Make (LP : LLVMParams) (GEP' : GEPM LP) (BYTE_IMPL' : ByteImpl LP) (DVALUE_BYTES' : DvalueByte LP) : MEMORY_PARAMS LP
with Module GEP := GEP'
with Module BYTE_IMPL := BYTE_IMPL'
with Module DVALUE_BYTES := DVALUE_BYTES'.
  Module GEP := GEP'.
  Module BYTE_IMPL := BYTE_IMPL'.
  Module DVALUE_BYTES := DVALUE_BYTES'.
End Make.
