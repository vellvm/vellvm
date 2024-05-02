From Vellvm Require Import
     Semantics.LLVMEvents.

From Mem Require Import
  Addresses.MemoryAddress.

From LLVM_Memory Require Import
  Sizeof
  Intptr.

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
  Declare Module I2P_BIG : ITOP_BIG ADDR PROV PTOI ITOP.
End LLVMParamsBig.

Module Make (ADDR' : ADDRESS) (IP' : INTPTR) (SIZEOF' : Sizeof) (PTOI' : PTOI ADDR') (PROV' : PROVENANCE ADDR') (ITOP' : ITOP ADDR' PROV' PTOI') : LLVMParams
with Module ADDR := ADDR'
with Module IP := IP'
with Module SIZEOF := SIZEOF'
with Module PTOI := PTOI'
with Module PROV := PROV'
with Module ITOP := ITOP'.
  Module ADDR := ADDR'.
  Module IP := IP'.
  Module SIZEOF := SIZEOF'.
  Module PTOI := PTOI'.
  Module PROV := PROV'.
  Module ITOP := ITOP'.
  Module Events := LLVMEvents.Make ADDR IP SIZEOF.
End Make.

Module MakeBig (ADDR' : ADDRESS) (IP' : INTPTR) (SIZEOF' : Sizeof) (PTOI' : PTOI ADDR') (PROV' : PROVENANCE ADDR') (ITOP' : ITOP ADDR' PROV' PTOI') (IP_BIG' : INTPTR_BIG IP') (I2P_BIG' : ITOP_BIG ADDR' PROV' PTOI' ITOP') : LLVMParamsBig
with Module ADDR := ADDR'
with Module IP := IP'
with Module SIZEOF := SIZEOF'
with Module PTOI := PTOI'
with Module PROV := PROV'
with Module ITOP := ITOP'
with Module IP_BIG := IP_BIG'
with Module I2P_BIG := I2P_BIG'.
  Module ADDR := ADDR'.
  Module IP := IP'.
  Module SIZEOF := SIZEOF'.
  Module PTOI := PTOI'.
  Module PROV := PROV'.
  Module ITOP := ITOP'.
  Module Events := LLVMEvents.Make ADDR IP SIZEOF.
  Module IP_BIG := IP_BIG'.
  Module I2P_BIG := I2P_BIG'.
End MakeBig.
