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
  Syntax.DynamicTypes
  Semantics.VellvmIntegers.
(* end hide *)

Module Type IPTR.
  Parameter intptr : Type.
  Parameter zero : intptr.

  Parameter VMemInt_intptr : VMemInt intptr.

  Parameter eq_dec : forall (a b : intptr), {a = b} + {a <> b}.
  Parameter eqb : forall (a b : intptr), bool.

  Parameter to_Z : forall (a : intptr), Z.
  Parameter to_unsigned : forall (a : intptr), Z.
  Parameter from_Z : Z -> EOB intptr.

  Parameter show_intptr : intptr -> string.
  
  Parameter from_Z_to_Z :
    forall (z : Z) (i : intptr),
      from_Z z = ret i ->
      to_Z i = z.

  Parameter from_Z_injective :
    forall (z1 z2 : Z) (i : intptr),
      from_Z z1 = ret i ->
      from_Z z2 = ret i ->
      z1 = z2.

  Parameter to_Z_from_Z :
    forall (i : intptr),
      from_Z (to_Z i) = ret i.

  Parameter from_Z_0 :
    from_Z 0 = ret zero.

  Parameter to_Z_0 :
    to_Z zero = 0%Z.

  Parameter to_Z_inj :
    forall x y,
      to_Z x = to_Z y ->
      x = y.

  Parameter VMemInt_intptr_dtyp :
    @mdtyp_of_int intptr VMemInt_intptr = DTYPE_IPTR.

  Parameter VMemInt_intptr_mrepr_from_Z :
    forall x,
      @mrepr intptr VMemInt_intptr x = from_Z x.

  Parameter to_Z_to_unsigned :
    forall x,
      to_Z x = to_unsigned x.
End IPTR.

