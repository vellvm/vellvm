From Vellvm Require Import
     Semantics.LLVMEvents
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof.

(** Parameters for LLVM instances. *)
Module Type LLVMParams.
  Declare Module ADDR : ADDRESS.
  Declare Module IP : INTPTR.
  Declare Module SIZEOF : Sizeof.
  Declare Module PTOI : PTOI ADDR.
  Declare Module PROV : PROVENANCE ADDR.
  Declare Module ITOP : ITOP ADDR PROV PTOI.
  
  Module Events := LLVMEvents.Make ADDR IP SIZEOF.
End LLVMParams.

Module Type LLVMParamsBig <: LLVMParams.
  Include LLVMParams.

  (* Additional module *)
  Declare Module IP_BIG : INTPTR_BIG IP.
End LLVMParamsBig.  

Module Make (ADDR' : ADDRESS) (IP' : INTPTR) (SIZEOF' : Sizeof) (PTOI' : PTOI ADDR') (PROV' : PROVENANCE ADDR') (ITOP' : ITOP ADDR' PROV' PTOI') : LLVMParams with Module ADDR := ADDR'.
  Module ADDR := ADDR'.
  Module IP := IP'.
  Module SIZEOF := SIZEOF'.
  Module PTOI := PTOI'.
  Module PROV := PROV'.
  Module ITOP := ITOP'.
  Module Events := LLVMEvents.Make ADDR IP SIZEOF.
End Make.

Module MakeBig (ADDR' : ADDRESS) (IP' : INTPTR) (SIZEOF' : Sizeof) (PTOI' : PTOI ADDR') (PROV' : PROVENANCE ADDR') (ITOP' : ITOP ADDR' PROV' PTOI') (IP_BIG' : INTPTR_BIG IP') : LLVMParamsBig with Module ADDR := ADDR'.
  Module ADDR := ADDR'.
  Module IP := IP'.
  Module SIZEOF := SIZEOF'.
  Module PTOI := PTOI'.
  Module PROV := PROV'.
  Module ITOP := ITOP'.
  Module Events := LLVMEvents.Make ADDR IP SIZEOF.
  Module IP_BIG := IP_BIG'.
End MakeBig.
