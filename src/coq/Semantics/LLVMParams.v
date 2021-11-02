From Vellvm Require Import
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof.

(** Parameters for LLVM instances. *)
Module Type LLVMParams.
  Declare Module ADDR : ADDRESS.
  Declare Module IP : INTPTR.
  Declare Module SIZEOF : Sizeof.
  Declare Module PTOI : PTOI ADDR.
  Declare Module PROV : PROVENANCE ADDR.
  Declare Module ITOP : ITOP ADDR PROV.
End LLVMParams.

Module Make (ADDR' : ADDRESS) (IP' : INTPTR) (SIZEOF' : Sizeof) (PTOI' : PTOI ADDR') (PROV' : PROVENANCE ADDR') (ITOP' : ITOP ADDR' PROV') : LLVMParams.
  Module ADDR := ADDR'.
  Module IP := IP'.
  Module SIZEOF := SIZEOF'.
  Module PTOI := PTOI'.
  Module PROV := PROV'.
  Module ITOP := ITOP'.
End Make.

(*
Module LLVMParamsBigIntptr := Make FiniteMemory.Addr FiniteMemory.BigIP FiniteMemory.FinSizeof FiniteMemory.FinPTOI FiniteMemory.FinPROV FiniteMemory.FinITOP.

Module LLVMParams64BitIntptr := Make FiniteMemory.Addr FiniteMemory.IP64Bit FiniteMemory.FinSizeof FiniteMemory.FinPTOI FiniteMemory.FinPROV FiniteMemory.FinITOP.
*)
