From Coq Require Import
  ZArith.

From Vellvm Require Import
  Semantics.VellvmIntegers
  Utils.Error
  DynamicTypes.

Module Type INTPTR.
  Parameter intptr : Set.
  Parameter zero : intptr.

  Parameter VMemInt_intptr : VMemInt intptr.

  Parameter eq_dec : forall (a b : intptr), {a = b} + {a <> b}.
  Parameter eqb : forall (a b : intptr), bool.

  Parameter to_Z : forall (a : intptr), Z.
  Parameter to_unsigned : forall (a : intptr), Z.
  Parameter from_Z : Z -> OOM intptr.

  Parameter from_Z_to_Z :
    forall (z : Z) (i : intptr),
      from_Z z = NoOom i ->
      to_Z i = z.

  Parameter from_Z_injective :
    forall (z1 z2 : Z) (i : intptr),
      from_Z z1 = NoOom i ->
      from_Z z2 = NoOom i ->
      z1 = z2.

  Parameter to_Z_from_Z :
    forall (i : intptr),
      from_Z (to_Z i) = NoOom i.

  Parameter from_Z_0 :
    from_Z 0 = NoOom zero.

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
End INTPTR.

Module Type INTPTR_BIG (IP : INTPTR).
  Import IP.

  Parameter from_Z_safe :
    forall z,
      match from_Z z with
      | NoOom _ => True
      | Oom _ => False
      end.
End INTPTR_BIG.
