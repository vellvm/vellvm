(* Used in [to_Z_inj] *)
From Stdlib Require Import ProofIrrelevance.

From Vellvm Require Import
  Utilities
  Syntax
  EOU
  IPtr
  Integers
  VellvmIntegers.

Definition from_Z_bits {sz : positive} : Z -> EOU (@bit_int sz) :=
  (fun (x : Z) =>
     if (x <=? @Integers.max_unsigned sz)%Z && (x >=? 0)%Z
     then ret (@Integers.repr sz x)
     else raise_oom "IPBit from_Z oom.").

#[local]Instance VMemInt_intptr_ix {sz : positive} : VMemInt (@bit_int sz)
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

    mdtyp_of_int := DTYPE_Iptr
  }.

#[local]Instance IP64Bit : IPtr :=
  {|
    iptr := int64;
    zero_iptr := @Integers.zero 64;

    eq_dec_iptr := @Integers.eq_dec 64;
    eqb_iptr := @Integers.eq 64;

    to_Z := Integers.unsigned;

    VMemInt_iptr := @VMemInt_intptr_ix 64;

    (* TODO: negatives;;;; ???? *)
    to_unsigned := Integers.unsigned;
    from_Z (x : Z)  := @from_Z_bits 64 x;

    show_iptr p := show (unsigned p);

  |}.

#[local]Instance IP64BitTheory : IPtrTheory.
Proof.
  constructor; auto.
  - intros z i FROM.
    cbn in FROM; unfold from_Z_bits in FROM.
    break_match_hyp; inversion FROM.
    cbn; apply Integers.unsigned_repr;
    lia.
  - intros z1 z2 i Z1 Z2.
    cbn in *; unfold from_Z, from_Z_bits in *.
    break_match_hyp; inversion Z2.
    break_match_hyp; inversion Z1.
    pose proof (@Integers.unsigned_repr 64 z1);
    pose proof (@Integers.unsigned_repr 64 z2);
    forward H; try lia;
    forward H2; try lia;
    congruence.
  - intros i;
    cbn; unfold from_Z, from_Z_bits, to_Z;
    break_match.
    + rewrite Integers.repr_unsigned; auto.
    + pose proof Integers.unsigned_range i;
      unfold Integers.max_unsigned in *;
      lia.
  - intros x y EQ;
    cbn in *; unfold to_Z in *.
    destruct x, y;
    unfold Integers.unsigned in *;
    cbn in *; subst.
  (* TODO : do we need this? Should we assume and leverage it more broadly? *)
    rewrite (proof_irrelevance _ intrange intrange0); auto.
Qed.

