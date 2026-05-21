From Vellvm Require Import
  Utilities
  Syntax.

From Vellvm Require Import
  IPtr
  Integers
  VellvmIntegers.

From QuickChick Require Import Show.

#[local]Instance IPZ : IPtr :=
  {|
    iptr := Z;
    zero_iptr := 0%Z;

    eq_dec_iptr := Z.eq_dec;
    eqb_iptr := Z.eqb;
    to_Z x := x;

    VMemInt_iptr := VMemInt_Z;

    (* TODO: negatives;;;; ???? *)
    to_unsigned p := p;
    from_Z (x : Z) := ret x;

    show_iptr p := show p;
  |}.

#[local]Instance IPZTheory : IPtrTheory.
Proof.
  constructor; cbn; auto.
  - intros z i FROM; inversion FROM; auto.
  - intros z1 z2 i Z1 Z2; inversion Z1; inversion Z2; subst; auto.
Qed.
