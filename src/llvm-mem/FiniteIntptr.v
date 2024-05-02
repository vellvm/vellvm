From Coq Require Import
     ZArith
     List
     Lia.

From Vellvm.Numeric Require Import
     Coqlib
     Integers.

From Vellvm.Utils Require Import
     Error
     Tactics.

From Vellvm.Syntax Require Import
     DynamicTypes.

From Vellvm.Semantics Require Import
     DynamicValues
     VellvmIntegers.

From Mem Require Import
     Addresses.MemoryAddress
     Memory.Provenance.

From LLVM_Memory Require Import
  Intptr.

From ExtLib Require Import
     Structures.Monads.

Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.

#[local] Open Scope Z_scope.


Module BigIP : INTPTR with
Definition intptr := Z with
  Definition zero := 0%Z with
Definition from_Z := (fun (x : Z) => ret x : OOM Z) with
Definition to_Z := fun (x : Z) => x with
Definition VMemInt_intptr := VMemInt_Z.
  Definition intptr := Z.
  Definition zero := 0%Z.

  Definition eq_dec := Z.eq_dec.
  Definition eqb := Z.eqb.

  Definition to_Z (x : intptr) := x.

  Definition VMemInt_intptr := VMemInt_Z.

  (* TODO: negatives.... ???? *)
  Definition to_unsigned := to_Z.
  Definition from_Z (x : Z) : OOM intptr := ret x.

  Lemma from_Z_to_Z :
    forall (z : Z) (i : intptr),
      from_Z z = NoOom i ->
      to_Z i = z.
  Proof.
    intros z i FROM.
    inversion FROM; auto.
  Qed.

  Lemma from_Z_injective :
    forall (z1 z2 : Z) (i : intptr),
      from_Z z1 = NoOom i ->
      from_Z z2 = NoOom i ->
      z1 = z2.
  Proof.
    intros z1 z2 i Z1 Z2.
    inversion Z1; inversion Z2; subst; auto.
  Qed.

  Lemma to_Z_from_Z :
    forall (i : intptr),
      from_Z (to_Z i) = NoOom i.
  Proof.
    intros i.
    cbn.
    unfold to_Z.
    reflexivity.
  Qed.

  Lemma from_Z_0 :
    from_Z 0 = NoOom zero.
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
    | Cne => Zneq_bool x y
    | Clt => Z.ltb x y
    | Cle => Z.leb x y
    | Cgt => Z.gtb x y
    | Cge => Z.geb x y
    end.

  Definition mcmpu_Z (c : comparison) (x y : Z) : bool :=
    match c with
    | Ceq => Z.eqb x y
    | Cne => Zneq_bool x y
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

End BigIP.

Module BigIP_BIG : INTPTR_BIG BigIP.
  Import BigIP.

  Lemma from_Z_safe :
    forall z,
      match from_Z z with
      | NoOom _ => True
      | Oom _ => False
      end.
  Proof.
    intros z.
    unfold from_Z.
    reflexivity.
  Qed.
End BigIP_BIG.

Definition from_Z_bits {sz : positive} : Z -> OOM (@int sz) := (fun (x : Z) =>
    if (x <=? @Integers.max_unsigned sz)%Z && (x >=? 0)%Z
    then ret (@Integers.repr sz x)
    else Oom "IPBit from_Z oom.").

Instance VMemInt_intptr_ix {sz : positive} : VMemInt (@int sz)
  :=
  { (* Comparisons *)
    mequ := @Integers.eq sz;
    mcmp := @Integers.cmp sz;
    mcmpu := @Integers.cmpu sz;

    (* Constants *)
    mbitwidth := Some sz;
    mzero := @Integers.zero sz;
    mone := @Integers.one sz;

    (* Arithmetic *)
    madd := fun x y =>
              if (Integers.eq (Integers.add_carry x y (@Integers.zero sz)) (@Integers.one sz))
              then Oom "IPBit addition overflow."
              else ret (Integers.add x y);
    madd_carry := fun x y c => (@Integers.zero sz);
    madd_overflow := fun x y c => (@Integers.zero sz);

    msub := fun x y =>
              if (@Integers.unsigned sz y >? @Integers.unsigned sz x)%Z
              then Oom "IPBit subtraction underflow."
              else ret (@Integers.sub sz x y);
    msub_borrow := fun x y c => (@Integers.zero sz);
    msub_overflow := fun x y c => (@Integers.zero sz);

    mmul :=
      fun x y =>
        let res := ((Integers.unsigned x) * (Integers.unsigned y))%Z in
        if (res >? @Integers.max_unsigned 64)
        then Oom "IPBit multiplication overflow."
        else ret (@Integers.repr sz res);

    mdivu := @Integers.divu sz;
    mdivs := fun _ _ => Oom "IPBit signed division.";

    mmodu := @Integers.modu sz;
    mmods := fun _ _ => Oom "IPBit signed modulo.";

    mshl :=
      fun x y =>
        let res_Z := Z.shiftl (@Integers.unsigned sz x) (@Integers.unsigned sz y) in
        if res_Z >? @Integers.max_unsigned sz
        then Oom "IP64Bit left shift overflow."
        else ret (@Integers.repr sz res_Z);
    mshr := @Integers.shr sz;
    mshru := @Integers.shru sz;

    mnegative := fun _ => Oom "IP64Bit taking negative of a number.";

    (* Logic *)
    mand := @Integers.and sz;
    mor := @Integers.or sz;
    mxor := @Integers.xor sz;

    (* Bounds *)
    mmin_signed := ret (@Integers.min_signed sz);
    mmax_signed := ret (@Integers.max_signed sz);
    mmax_unsigned := ret (@Integers.max_unsigned sz);

    (* Conversion *)
    munsigned := @Integers.unsigned sz;
    msigned := @Integers.signed sz;

    mrepr := @from_Z_bits sz;

    mdtyp_of_int := DTYPE_IPTR
  }.

Module IP64Bit : INTPTR with
Definition intptr := int64 with
Definition zero := (@Integers.zero 64) with
Definition from_Z := @from_Z_bits 64 with
Definition to_Z := @Integers.unsigned 64 with
Definition VMemInt_intptr := @VMemInt_intptr_ix 64.

  Definition intptr := int64.
  Definition zero := (@Integers.zero 64).

  Definition eq_dec := @Integers.eq_dec 64.
  Definition eqb := @Integers.eq 64.

  Definition to_Z (x : intptr) := Integers.unsigned x.

  Definition VMemInt_intptr := @VMemInt_intptr_ix 64.

  (* TODO: negatives.... ???? *)
  Definition to_unsigned := to_Z.
  Definition from_Z (x : Z) : OOM intptr := @from_Z_bits 64 x.

  Lemma from_Z_to_Z :
    forall (z : Z) (i : intptr),
      from_Z z = NoOom i ->
      to_Z i = z.
  Proof.
    intros z i FROM.
    unfold from_Z, from_Z_bits in FROM.
    break_match_hyp; inversion FROM.
    unfold to_Z.
    apply Integers.unsigned_repr.
    lia.
  Qed.

  Lemma from_Z_injective :
    forall (z1 z2 : Z) (i : intptr),
      from_Z z1 = NoOom i ->
      from_Z z2 = NoOom i ->
      z1 = z2.
  Proof.
    intros z1 z2 i Z1 Z2.
    unfold from_Z, from_Z_bits in *.
    break_match_hyp; inversion Z2.
    break_match_hyp; inversion Z1.
    pose proof (@Integers.unsigned_repr 64 z1).
    pose proof (@Integers.unsigned_repr 64 z2).
    forward H; try lia.
    forward H2; try lia.
    congruence.
  Qed.

  Lemma to_Z_from_Z :
    forall (i : intptr),
      from_Z (to_Z i) = NoOom i.
  Proof.
    intros i.
    unfold from_Z, from_Z_bits, to_Z.
    break_match.
    - rewrite Integers.repr_unsigned; auto.
    - unfold intptr in *.
      pose proof Integers.unsigned_range i.
      unfold Integers.max_unsigned in *.
      lia.
  Qed.

  Lemma from_Z_0 :
    from_Z 0 = NoOom zero.
  Proof.
    auto.
  Qed.

  Lemma to_Z_0 :
    to_Z zero = 0%Z.
  Proof.
    auto.
  Qed.

  Require Import ProofIrrelevance.

  Lemma to_Z_inj :
    forall x y,
      to_Z x = to_Z y ->
      x = y.
  Proof.
    intros x y EQ.
    unfold to_Z in *.
    destruct x, y.
    unfold Integers.unsigned in *.
    cbn in *; subst.
    rewrite (proof_irrelevance _ intrange intrange0); auto.
  Qed.

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

End IP64Bit.
