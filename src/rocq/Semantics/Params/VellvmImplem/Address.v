From Vellvm Require Import
  Utilities
  Syntax.

From Vellvm Require Import
  Rocqlib
  Params.IPtr
  Params.Address
  Params.Provenance
  VellvmImplem.Provenance
  VellvmIntegers.

From QuickChick Require Import Show.

(* TODO: move this *)
Instance showIptr {IP : IPtr} : Show iptr := {| show := show_iptr |}.

#[refine] Instance AddressV {IP : IPtr} : @Address ProvenanceV :=
  {|
    addr := (iptr * prov);
    null := (zero_iptr, nil_prov)%Z;
    address_provenance := snd;
    show_addr a := show a;
  |}.
Proof.
intros [a1 a2] [b1 b2].
destruct (eq_dec_iptr a1 b1); destruct (option_eq (list_eq_dec N.eq_dec) a2 b2); subst.
- left; reflexivity.
- right. intros H. inversion H; subst. apply n. reflexivity.
- right. intros H. inversion H; subst. apply n. reflexivity.
- right. intros H. inversion H; subst. apply n. reflexivity.
Defined.
