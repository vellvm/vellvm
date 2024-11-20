From Stdlib Require Import
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
  Declare Module PS : FULL_PROV_SET.
  Declare Module ADDR : ADDRESS ADDR_MD PS.
  Declare Module IP : INTPTR.
  Declare Module SIZEOF : Sizeof.

  Module Events := LLVMEvents.Make ADDR IP SIZEOF.
End LLVMParams.

Module Type LLVMParamsBig <: LLVMParams.
  Declare Module ADDR_MD : Typ.
  Declare Module PS : FULL_PROV_SET.
  Declare Module ADDR : INFINITE_ADDRESS ADDR_MD PS.
  Declare Module IP : INTPTR_BIG.
  Declare Module SIZEOF : Sizeof.

  Module Events := LLVMEvents.Make ADDR IP SIZEOF.
End LLVMParamsBig.

Module Make (ADDR_MD' : Typ) (PS' : FULL_PROV_SET) (ADDR' : ADDRESS ADDR_MD' PS') (IP' : INTPTR) (SIZEOF' : Sizeof) : LLVMParams
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

  Module Events := LLVMEvents.Make ADDR IP SIZEOF.
End Make.

Module MakeBig (ADDR_MD' : Typ) (PS' : FULL_PROV_SET) (ADDR' : INFINITE_ADDRESS ADDR_MD' PS') (IP' : INTPTR_BIG) (SIZEOF' : Sizeof) : LLVMParamsBig
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

  Module Events := LLVMEvents.Make ADDR IP SIZEOF.
End MakeBig.
