From Coq Require Import
  Equalities.

From Vellvm Require Import
     Semantics.LLVMEvents.

From Mem Require Import
  Addresses.Provenance
  Addresses.MemoryAddress.

From LLVM_Memory Require Import
  Sizeof
  Intptr.

(** Parameters for LLVM instances. *)
Module Type LLVMParams.
  Declare Module ADDR_MD : Typ.
  Declare Module PS : PROV_SET.
  Declare Module ADDR : ADDRESS ADDR_MD PS.
  Declare Module IP : INTPTR.
  Declare Module SIZEOF : Sizeof.

  Module Events := LLVMEvents.Make ADDR_MD PS ADDR IP SIZEOF.
End LLVMParams.

Module Type LLVMParamsBig <: LLVMParams.
  Declare Module ADDR_MD : Typ.
  Declare Module PS : PROV_SET.
  Declare Module ADDR : INFINITE_ADDRESS ADDR_MD PS.
  Declare Module IP : INTPTR_BIG.
  Declare Module SIZEOF : Sizeof.

  Module Events := LLVMEvents.Make ADDR_MD PS ADDR IP SIZEOF.

  (* Additional module *)
  Declare Module IP_BIG : INTPTR_BIG IP.
  Declare Module I2P_BIG : ITOP_BIG ADDR_MD ADDR ADDR ADDR.
End LLVMParamsBig.

Module Make (ADDR_MD' : Typ) (PS' : PROV_SET) (ADDR' : ADDRESS ADDR_MD' PS') (IP' : INTPTR) (SIZEOF' : Sizeof) : LLVMParams
with Module ADDR_MD := ADDR_MD'
with Module PS := PS'
with Module ADDR := ADDR'
with Module IP := IP'
with Module SIZEOF := SIZEOF'.
  Module ADDR_MD := ADDR_MD'.
  Module PS := PS'.
  Module ADDR := ADDR'.
  Module IP := IP'.
  Module SIZEOF := SIZEOF'.

  Module Events := LLVMEvents.Make ADDR_MD PS ADDR IP SIZEOF.
End Make.

Module MakeBig (ADDR_MD' : Typ) (PS' : PROV_SET) (ADDR' : ADDRESS ADDR_MD' PS') (IP' : INTPTR) (SIZEOF' : Sizeof) (IP_BIG' : INTPTR_BIG IP') : LLVMParamsBig
with Module ADDR_MD := ADDR_MD'
with Module PS := PS'
with Module ADDR := ADDR'
with Module IP := IP'
with Module SIZEOF := SIZEOF'
with Module IP_BIG := IP_BIG'.
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
