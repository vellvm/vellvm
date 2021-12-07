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

Module Type LLVMParamsBig <: LLVMParams.
  Declare Module ADDR : ADDRESS.
  Declare Module IP : INTPTR.
  Declare Module SIZEOF : Sizeof.
  Declare Module PTOI : PTOI ADDR.
  Declare Module PROV : PROVENANCE ADDR.
  Declare Module ITOP : ITOP ADDR PROV.

  (* Additional module *)
  Declare Module IP_BIG : INTPTR_BIG IP.
End LLVMParamsBig.  

Module Make (ADDR' : ADDRESS) (IP' : INTPTR) (SIZEOF' : Sizeof) (PTOI' : PTOI ADDR') (PROV' : PROVENANCE ADDR') (ITOP' : ITOP ADDR' PROV') : LLVMParams.
  Module ADDR := ADDR'.
  Module IP := IP'.
  Module SIZEOF := SIZEOF'.
  Module PTOI := PTOI'.
  Module PROV := PROV'.
  Module ITOP := ITOP'.
End Make.

Module MakeBig (ADDR' : ADDRESS) (IP' : INTPTR) (SIZEOF' : Sizeof) (PTOI' : PTOI ADDR') (PROV' : PROVENANCE ADDR') (ITOP' : ITOP ADDR' PROV') (IP_BIG' : INTPTR_BIG IP') : LLVMParamsBig.
  Module ADDR := ADDR'.
  Module IP := IP'.
  Module SIZEOF := SIZEOF'.
  Module PTOI := PTOI'.
  Module PROV := PROV'.
  Module ITOP := ITOP'.
  Module IP_BIG := IP_BIG'.
End MakeBig.
