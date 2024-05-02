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

Definition from_Z_64 := (fun (x : Z) =>
    if (x <=? Int64.max_unsigned)%Z && (x >=? 0)%Z
    then ret (Int64.repr x)
    else Oom "IP64Bit from_Z oom.").

Instance VMemInt_intptr_i64 : VMemInt int64
  :=
  { (* Comparisons *)
    mequ := Int64.eq;
    mcmp := Int64.cmp;
    mcmpu := Int64.cmpu;

    (* Constants *)
    mbitwidth := Some 64%nat;
    mzero := Int64.zero;
    mone := Int64.one;

    (* Arithmetic *)
    madd := fun x y =>
              if (Int64.eq (Int64.add_carry x y Int64.zero) Int64.one)
              then Oom "IP64Bit addition overflow."
              else ret (Int64.add x y);
    madd_carry := fun x y c => Int64.zero;
    madd_overflow := fun x y c => Int64.zero;

    msub := fun x y =>
              if (Int64.unsigned y >? Int64.unsigned x)%Z
              then Oom "IP64Bit subtraction underflow."
              else ret (Int64.sub x y);
    msub_borrow := fun x y c => Int64.zero;
    msub_overflow := fun x y c => Int64.zero;

    mmul :=
      fun x y =>
        let res := ((Int64.unsigned x) * (Int64.unsigned y))%Z in
        if (res >? Int64.max_unsigned)
        then Oom "IP64Bit multiplication overflow."
        else ret (Int64.repr res);

    mdivu := Int64.divu;
    mdivs := fun _ _ => Oom "IP64Bit signed division.";

    mmodu := Int64.modu;
    mmods := fun _ _ => Oom "IP64Bit signed modulo.";

    mshl :=
      fun x y =>
        let res_Z := Z.shiftl (Int64.unsigned x) (Int64.unsigned y) in
        if res_Z >? Int64.max_unsigned
        then Oom "IP64Bit left shift overflow."
        else ret (Int64.repr res_Z);
    mshr := Int64.shr;
    mshru := Int64.shru;

    mnegative := fun _ => Oom "IP64Bit taking negative of a number.";

    (* Logic *)
    mand := Int64.and;
    mor := Int64.or;
    mxor := Int64.xor;

    (* Bounds *)
    mmin_signed := ret Int64.min_signed;
    mmax_signed := ret Int64.max_signed;
    mmax_unsigned := ret Int64.max_unsigned;

    (* Conversion *)
    munsigned := Int64.unsigned;
    msigned := Int64.signed;

    mrepr := from_Z_64;

    mdtyp_of_int := DTYPE_IPTR
  }.

Module IP64Bit : INTPTR with
Definition intptr := int64 with
Definition zero := Int64.zero with
Definition from_Z := from_Z_64 with
Definition to_Z := Int64.unsigned with
Definition VMemInt_intptr := VMemInt_intptr_i64.

  Definition intptr := int64.
  Definition zero := Int64.zero.

  Definition eq_dec := Int64.eq_dec.
  Definition eqb := Int64.eq.

  Definition to_Z (x : intptr) := Int64.unsigned x.

  Definition VMemInt_intptr := VMemInt_intptr_i64.

  (* TODO: negatives.... ???? *)
  Definition to_unsigned := to_Z.
  Definition from_Z (x : Z) : OOM intptr := from_Z_64 x.

  Lemma from_Z_to_Z :
    forall (z : Z) (i : intptr),
      from_Z z = NoOom i ->
      to_Z i = z.
  Proof.
    intros z i FROM.
    unfold from_Z, from_Z_64 in FROM.
    break_match_hyp; inversion FROM.
    unfold to_Z.
    apply Integers.Int64.unsigned_repr.
    lia.
  Qed.

  Lemma from_Z_injective :
    forall (z1 z2 : Z) (i : intptr),
      from_Z z1 = NoOom i ->
      from_Z z2 = NoOom i ->
      z1 = z2.
  Proof.
    intros z1 z2 i Z1 Z2.
    unfold from_Z, from_Z_64 in *.
    break_match_hyp; inversion Z2.
    break_match_hyp; inversion Z1.
    pose proof Integers.Int64.unsigned_repr z1.
    pose proof Integers.Int64.unsigned_repr z2.
    forward H; try lia.
    forward H2; try lia.
    congruence.
  Qed.

  Lemma to_Z_from_Z :
    forall (i : intptr),
      from_Z (to_Z i) = NoOom i.
  Proof.
    intros i.
    unfold from_Z, from_Z_64, to_Z.
    break_match.
    - rewrite Int64.repr_unsigned; auto.
    - unfold intptr in *.
      pose proof Int64.unsigned_range i.
      unfold Int64.max_unsigned in *.
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
    unfold Int64.unsigned in *.
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
