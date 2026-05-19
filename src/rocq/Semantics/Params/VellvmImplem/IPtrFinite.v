(* Used in [to_Z_inj] *)
From Stdlib Require Import ProofIrrelevance.

From Vellvm Require Import
  Utilities
  Syntax.

From Vellvm Require Import
  IPtr
  Integers
  VellvmIntegers.

From QuickChick Require Import Show.

Module IP64Bit : IPTR.
(*   with *)
(* Definition intptr := int64 with *)
(* Definition zero := (@Integers.zero 64) with *)
(* Definition from_Z := @from_Z_bits 64 with *)
(* Definition to_Z := @Integers.unsigned 64 with *)
(* Definition VMemInt_intptr := @VMemInt_intptr_ix 64. *)

  Definition from_Z_bits {sz : positive} : Z -> EOB (@bit_int sz) :=
    (fun (x : Z) =>
       if (x <=? @Integers.max_unsigned sz)%Z && (x >=? 0)%Z
       then ret (@Integers.repr sz x)
       else raise_oom "IPBit from_Z oom.").

  Instance VMemInt_intptr_ix {sz : positive} : VMemInt (@bit_int sz)
    :=
    { (* Comparisons *)
      mequ := @Integers.eq sz;
      mcmp := @Integers.cmp sz;
      mcmpu := @Integers.cmpu sz;
      msamesign := fun _ _ => true;
      
      (* Constants *)
      mbitwidth := Some sz;
      mzero := @Integers.zero sz;
      mone := @Integers.one sz;

      (* Arithmetic *)
      madd := fun x y =>
                if (Integers.eq (Integers.add_carry x y (@Integers.zero sz)) (@Integers.one sz))
                then raise_oom "IPBit addition overflow."
                else ret (Integers.add x y);
      madd_carry := fun x y c => (@Integers.zero sz);
      madd_overflow := fun x y c => (@Integers.zero sz);

      msub := fun x y =>
                if (@Integers.unsigned sz y >? @Integers.unsigned sz x)%Z
                then raise_oom "IPBit subtraction underflow."
                else ret (@Integers.sub sz x y);
      msub_borrow := fun x y c => (@Integers.zero sz);
      msub_overflow := fun x y c => (@Integers.zero sz);

      mmul :=
        fun x y =>
          let res := ((Integers.unsigned x) * (Integers.unsigned y))%Z in
          if (res >? @Integers.max_unsigned 64)
          then raise_oom "IPBit multiplication overflow."
          else ret (@Integers.repr sz res);

      mdivu := @Integers.divu sz;
      mdivs := fun _ _ => raise_oom "IPBit signed division.";

      mmodu := @Integers.modu sz;
      mmods := fun _ _ => raise_oom "IPBit signed modulo.";

      mshl :=
        fun x y =>
          let res_Z := Z.shiftl (@Integers.unsigned sz x) (@Integers.unsigned sz y) in
          if res_Z >? @Integers.max_unsigned sz
          then raise_oom "IP64Bit left shift overflow."
          else ret (@Integers.repr sz res_Z);
      mshr := @Integers.shr sz;
      mshru := @Integers.shru sz;

      mnegative := fun _ => raise_oom "IP64Bit taking negative of a number.";

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

  Definition intptr := int64.
  Definition zero := (@Integers.zero 64).

  Definition eq_dec := @Integers.eq_dec 64.
  Definition eqb := @Integers.eq 64.

  Definition to_Z (x : intptr) := Integers.unsigned x.

  Definition VMemInt_intptr := @VMemInt_intptr_ix 64.

  (* TODO: negatives.... ???? *)
  Definition to_unsigned := to_Z.
  Definition from_Z (x : Z) : EOB intptr := @from_Z_bits 64 x.

  Definition show_intptr (p : intptr) : string := show (unsigned p).
    
  Lemma from_Z_to_Z :
    forall (z : Z) (i : intptr),
      from_Z z = ret i ->
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
      from_Z z1 = ret i ->
      from_Z z2 = ret i ->
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
      from_Z (to_Z i) = ret i.
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
    from_Z 0 = ret zero.
  Proof.
    auto.
  Qed.

  Lemma to_Z_0 :
    to_Z zero = 0%Z.
  Proof.
    auto.
  Qed.

  (* TODO : do we need this? Should we assume and leverage it more broadly? *)
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

