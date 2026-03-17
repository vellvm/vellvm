From Vellvm Require Import
     Semantics.LLVMEvents
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Semantics.DynamicValues.

From ExtLib Require Import
  Core.RelDec
  Programming.Eqv.  


(** Parameters for LLVM instances. *)
Module Type LLVMParams.
  Declare Module ADDR : ADDRESS.
  Declare Module IP : INTPTR.
  Declare Module SZ : SIZEOF.
  Declare Module PTOI : PTOI ADDR.
  Declare Module PROV : PROVENANCE ADDR.
  Declare Module ITOP : ITOP ADDR PROV PTOI.

  #[global] Instance eq_dec_addr : RelDec (@eq ADDR.addr) := RelDec_from_dec _ ADDR.eq_dec.
  #[global] Instance Eqv_addr : Eqv ADDR.addr := (@eq ADDR.addr).

  Module DV := DynamicValues.DVALUE(ADDR)(IP)(SZ).
End LLVMParams.

Module Type LLVMParamsBig <: LLVMParams.
  Include LLVMParams.

  (* Additional module *)
  Declare Module IP_BIG : INTPTR_BIG IP.
  Declare Module I2P_BIG : ITOP_BIG ADDR PROV PTOI ITOP.
End LLVMParamsBig.

Module Make (ADDR' : ADDRESS) (IP' : INTPTR) (SZ' : SIZEOF) (PTOI' : PTOI ADDR') (PROV' : PROVENANCE ADDR') (ITOP' : ITOP ADDR' PROV' PTOI') : LLVMParams
with Module ADDR := ADDR'
with Module IP := IP'
with Module SZ := SZ'
with Module PTOI := PTOI'
with Module PROV := PROV'
with Module ITOP := ITOP'.
  Module ADDR := ADDR'.
  Module IP := IP'.
  Module SZ := SZ'.
  Module PTOI := PTOI'.
  Module PROV := PROV'.
  Module ITOP := ITOP'.
  #[global] Instance eq_dec_addr : RelDec (@eq ADDR.addr) := RelDec_from_dec _ ADDR.eq_dec.
  #[global] Instance Eqv_addr : Eqv ADDR.addr := (@eq ADDR.addr).

  Module DV := DynamicValues.DVALUE(ADDR)(IP)(SZ).

End Make.

Module MakeBig (ADDR' : ADDRESS) (IP' : INTPTR) (SZ' : SIZEOF) (PTOI' : PTOI ADDR') (PROV' : PROVENANCE ADDR') (ITOP' : ITOP ADDR' PROV' PTOI') (IP_BIG' : INTPTR_BIG IP') (I2P_BIG' : ITOP_BIG ADDR' PROV' PTOI' ITOP') : LLVMParamsBig
with Module ADDR := ADDR'
with Module IP := IP'
with Module SZ := SZ'
with Module PTOI := PTOI'
with Module PROV := PROV'
with Module ITOP := ITOP'
with Module IP_BIG := IP_BIG'
with Module I2P_BIG := I2P_BIG'.
  Module ADDR := ADDR'.
  Module IP := IP'.
  Module SZ := SZ'.
  Module PTOI := PTOI'.
  Module PROV := PROV'.
  Module ITOP := ITOP'.

  #[global] Instance eq_dec_addr : RelDec (@eq ADDR.addr) := RelDec_from_dec _ ADDR.eq_dec.
  #[global] Instance Eqv_addr : Eqv ADDR.addr := (@eq ADDR.addr).

  Module DV := DynamicValues.DVALUE(ADDR)(IP)(SZ).
  Module IP_BIG := IP_BIG'.
  Module I2P_BIG := I2P_BIG'.
End MakeBig.
