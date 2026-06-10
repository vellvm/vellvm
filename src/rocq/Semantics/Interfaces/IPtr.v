(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

(* begin hide *)
From Vellvm Require Import
  Utilities
  Syntax
  EOU
  VellvmIntegers.
(* end hide *)

Class IPtr : Type :=
  {
    iptr : Set;
    zero_iptr : iptr;

    VMemInt_iptr : VMemInt iptr;

    eq_dec_iptr : forall (a b : iptr), {a = b} + {a <> b};
    eqb_iptr : forall (a b : iptr), bool;

    to_Z : forall (a : iptr), Z;
    to_unsigned : forall (a : iptr), Z;
    from_Z : Z -> EOU iptr;

    show_iptr : iptr -> string;
    
  }.

Class IPtrTheory {IP : IPtr} :=
  {
    from_Z_to_Z :
    forall (z : Z) (i : iptr),
      from_Z z = ret i ->
      to_Z i = z;

    from_Z_injective :
    forall (z1 z2 : Z) (i : iptr),
      from_Z z1 = ret i ->
      from_Z z2 = ret i ->
      z1 = z2;

    to_Z_from_Z :
    forall (i : iptr),
      from_Z (to_Z i) = ret i;

    from_Z_0 :
    from_Z 0 = ret zero_iptr;

    to_Z_0 :
    to_Z zero_iptr = 0%Z;

    to_Z_inj :
    forall x y,
      to_Z x = to_Z y ->
      x = y;

    VMemInt_iptr_dtyp :
    @mdtyp_of_int iptr VMemInt_iptr = DTYPE_IPTR;

    VMemInt_iptr_mrepr_from_Z :
    forall x,
      @mrepr iptr VMemInt_iptr x = from_Z x;

    to_Z_to_unsigned :
    forall x,
      to_Z x = to_unsigned x;
    
  }.

Definition intptr_seq {IP : IPtr} (start : Z) (len : nat) : EOU (list iptr)
  := map_monad from_Z (Zseq start len).

