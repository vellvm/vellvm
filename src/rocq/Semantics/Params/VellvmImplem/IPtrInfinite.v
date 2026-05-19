From Vellvm Require Import
  Utilities
  Syntax.

From Vellvm Require Import
  IPtr
  Integers
  VellvmIntegers.

From QuickChick Require Import Show.

Module IPZ : IPTR.
 
  Definition intptr := Z.
  Definition zero := 0%Z.

  Definition eq_dec := Z.eq_dec.
  Definition eqb := Z.eqb.

  Definition to_Z (x : intptr) := x.

  Definition VMemInt_intptr := VMemInt_Z.

  (* TODO: negatives.... ???? *)
  Definition to_unsigned := to_Z.
  Definition from_Z (x : Z) : EOB intptr := ret x.

  Definition show_intptr (p : intptr) : string := show p.
  
  Lemma from_Z_to_Z :
    forall (z : Z) (i : intptr),
      from_Z z = ret i ->
      to_Z i = z.
  Proof.
    intros z i FROM.
    inversion FROM; auto.
  Qed.

  Lemma from_Z_injective :
    forall (z1 z2 : Z) (i : intptr),
      from_Z z1 = ret i ->
      from_Z z2 = ret i ->
      z1 = z2.
  Proof.
    intros z1 z2 i Z1 Z2.
    inversion Z1; inversion Z2; subst; auto.
  Qed.

  Lemma to_Z_from_Z :
    forall (i : intptr),
      from_Z (to_Z i) = ret i.
  Proof.
    intros i.
    cbn.
    unfold to_Z.
    reflexivity.
  Qed.

  Lemma from_Z_0 :
    from_Z 0 = ret zero.
  Proof.
    auto.
  Qed.

  Lemma to_Z_0 :
    to_Z zero = 0%Z.
  Proof.
    auto.
  Qed.

  Lemma to_Z_inj :
    forall x y,
      to_Z x = to_Z y ->
      x = y.
  Proof.
    intros x y.
    unfold to_Z; auto.
  Qed.

  Definition mequ_Z (x y : Z) : bool :=
    Z.eqb x y.

  Definition mcmp_Z (c : comparison) (x y : Z) : bool :=
    match c with
    | Ceq => Z.eqb x y
    | Cne => negb (Z.eqb x y)
    | Clt => Z.ltb x y
    | Cle => Z.leb x y
    | Cgt => Z.gtb x y
    | Cge => Z.geb x y
    end.

  Definition mcmpu_Z (c : comparison) (x y : Z) : bool :=
    match c with
    | Ceq => Z.eqb x y
    | Cne => negb (Z.eqb x y)
    | Clt => Z.ltb x y
    | Cle => Z.leb x y
    | Cgt => Z.gtb x y
    | Cge => Z.geb x y
    end.

  Lemma VMemInt_intptr_dtyp :
    @mdtyp_of_int intptr VMemInt_intptr = DTYPE_IPTR.
  Proof.
    cbn. reflexivity.
  Qed.

  Lemma VMemInt_intptr_mrepr_from_Z :
    forall x,
      @mrepr intptr VMemInt_intptr x = from_Z x.
  Proof.
    reflexivity.
  Qed.

  Lemma to_Z_to_unsigned :
    forall x,
      to_Z x = to_unsigned x.
  Proof.
    intros x.
    reflexivity.
  Qed.

End IPZ.

