From ExtLib Require Import
     Core.RelDec
     Programming.Eqv.

From Vellvm Require Import
            Semantics.IntPtr
            Semantics.MemoryAddress
            Semantics.Memory.Overlaps
            Semantics.Memory.Sizeof
            Semantics.DynamicValues.

(** Parameters for LLVM instances. *)
Module Type LLVM_PARAMS.
  Declare Module Addr : ADDRESS_OVERLAPS.
  Declare Module IP : INTPTR.
  Declare Module Sizeof : SIZEOF.

  #[global] Instance eq_dec_addr : RelDec (@eq Addr.addr) := RelDec_from_dec _ Addr.eq_dec.
  #[global] Instance Eqv_addr : Eqv Addr.addr := (@eq Addr.addr).

  Module DV := DynamicValues.DVALUE(Addr)(IP)(Sizeof).
  Module OVER := OverlapHelpers Addr Sizeof.
End LLVM_PARAMS.


Module Type LLVM_PARAMS_BIG <: LLVM_PARAMS.
  Declare Module Addr : ADDRESS_OVERLAPS_BIG.
  Declare Module IP : INTPTR_BIG.
  
  Declare Module Sizeof : SIZEOF.

  #[global] Instance eq_dec_addr : RelDec (@eq Addr.addr) := RelDec_from_dec _ Addr.eq_dec.
  #[global] Instance Eqv_addr : Eqv Addr.addr := (@eq Addr.addr).

  Module DV := DynamicValues.DVALUE(Addr)(IP)(Sizeof).
  Module OVER := OverlapHelpers Addr Sizeof.  
End LLVM_PARAMS_BIG.

Module Make (Addr' : ADDRESS_OVERLAPS) (IP' : INTPTR) (Sizeof' : SIZEOF) <: LLVM_PARAMS
with Module Addr := Addr'
with Module IP := IP'
with Module Sizeof := Sizeof'.
  Module Addr := Addr'.
  Module IP := IP'.
  Module Sizeof := Sizeof'.

  #[global] Instance eq_dec_addr : RelDec (@eq Addr.addr) := RelDec_from_dec _ Addr.eq_dec.
  #[global] Instance Eqv_addr : Eqv Addr.addr := (@eq Addr.addr).

  Module DV := DynamicValues.DVALUE(Addr)(IP)(Sizeof).
  Module OVER := OverlapHelpers Addr Sizeof.  
End Make.

Module MakeParamsBig (Addr' : ADDRESS_OVERLAPS_BIG) (IP' : INTPTR_BIG) (Sizeof' : SIZEOF) <: LLVM_PARAMS_BIG
with Module Addr := Addr'
with Module IP := IP'
with Module Sizeof := Sizeof'.
  Module Addr := Addr'.
  Module IP := IP'.
  Module Sizeof := Sizeof'.

  #[global] Instance eq_dec_addr : RelDec (@eq Addr.addr) := RelDec_from_dec _ Addr.eq_dec.
  #[global] Instance Eqv_addr : Eqv Addr.addr := (@eq Addr.addr).

  Module DV := DynamicValues.DVALUE(Addr)(IP)(Sizeof).
  Module OVER := OverlapHelpers Addr Sizeof.  
End MakeParamsBig.

