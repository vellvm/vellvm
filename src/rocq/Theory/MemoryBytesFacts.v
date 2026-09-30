(** * Facts about [Semantics/MemoryBytes.v]

    The theory of the byte-level serializer ([dvalue_to_memory_bytes]) and
    deserializer ([memory_bytes_to_dvalue]): sizes, round trips, what the
    reader can produce, well-formedness of what the writer produces, and
    exactness at byte types.  The definitions themselves live in
    [Semantics/MemoryBytes.v]. *)

From Vellvm Require Import
  Utils
  Numeric
  Syntax
  Params
  DynamicValues
  EOU
  VellvmIntegers.

From Vellvm.Semantics Require Import
  MemoryBytes.

From ExtLib Require Import
  Data.Monads.EitherMonad.
#[local] Open Scope N_scope.

Definition extract_bit_N (x:N) (idx : N) : N :=
  (N.shiftr x idx) mod 2.

(** ** Bit-level facts for the integer round trip

    [concat_bytes_Z_extract] is the arithmetic core: concatenating the bytes
    of a value reassembles it modulo the number of bytes taken.
    [extract_byte_vint_spec] says the writer's byte extraction really is
    "shift right and take the low 8 bits" -- which at exactly 8 bits holds
    for a different reason, since [repr 256] is then [0] and Rocq's
    [_ mod 0] is the identity. *)
Lemma concat_bytes_Z_extract : forall k v j,
    concat_bytes_Z (List.map (fun i => ((v / 2 ^ (8 * Z.of_N i)) mod 256)%Z) (Nseq j k))
    = ((v / 2 ^ (8 * Z.of_N j)) mod 2 ^ (8 * Z.of_nat k))%Z.
Proof.
  induction k as [| k IH]; intros v j; cbn [Nseq List.map concat_bytes_Z].
  - cbn; rewrite Z.mod_1_r; reflexivity.
  - rewrite IH.
    rewrite Z.shiftl_mul_pow2 by lia.
    rewrite N2Z.inj_succ.
    replace (8 * Z.succ (Z.of_N j))%Z with (8 * Z.of_N j + 8)%Z by lia.
    rewrite Z.pow_add_r by lia.
    rewrite <- Z.div_div by (try lia; apply Z.pow_pos_nonneg; lia).
    replace (Z.of_nat (S k)) with (Z.of_nat k + 1)%Z by lia.
    replace (8 * (Z.of_nat k + 1))%Z with (8 * Z.of_nat k + 8)%Z by lia.
    rewrite Z.pow_add_r by lia.
    replace (2 ^ 8)%Z with 256%Z by reflexivity.
    rewrite (Z.mul_comm (2 ^ (8 * Z.of_nat k))%Z 256%Z).
    rewrite (Z.rem_mul_r _ 256 (2 ^ (8 * Z.of_nat k)))
      by (try lia; apply Z.pow_pos_nonneg; lia).
    lia.
Qed.

Lemma extract_byte_vint_spec : forall sz (x : @bit_int sz) idx,
    (8 * (Z.of_N idx + 1) <= Z.pos sz)%Z ->
    extract_byte_vint x idx = ((unsigned x / 2 ^ (8 * Z.of_N idx)) mod 256)%Z.
Proof.
  intros sz x idx H.
  pose proof (unsigned_range x) as [Hlo Hhi].
  assert (Hm : (@modulus sz = 2 ^ Z.pos sz)%Z)
    by (rewrite modulus_def; apply two_power_pos_eq).
  assert (Hpow : (Z.pos sz < 2 ^ Z.pos sz)%Z) by (apply Z.pow_gt_lin_r; lia).
  unfold extract_byte_vint.
  cbn [modu shru unsigned repr VInt_Bounded].
  unfold Integers.modu, Integers.shru.
  rewrite !unsigned_repr_eq.
  rewrite (Z.mod_small (Z.of_N idx * 8)) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (Z.of_N idx * 8)%Z with (8 * Z.of_N idx)%Z by lia.
  rewrite (Z.mod_small (Integers.unsigned x / 2 ^ (8 * Z.of_N idx))).
  2:{ assert (Hp : (0 < 2 ^ (8 * Z.of_N idx))%Z) by (apply Z.pow_pos_nonneg; lia).
      assert (Hge1 : (1 <= 2 ^ (8 * Z.of_N idx))%Z)
        by (replace 1%Z with (2 ^ 0)%Z by reflexivity;
            apply Z.pow_le_mono_r; lia).
      split.
      - apply Z.div_pos; lia.
      - apply Z.le_lt_trans with (Integers.unsigned x); [| lia].
        apply Z.div_le_upper_bound; [lia | nia]. }
  destruct (Z.eq_dec (Z.pos sz) 8) as [E8 | E8].
  - (* exactly one byte wide: [repr 256] is 0 and [_ mod 0] is the identity *)
    assert (idx = 0%N) by lia; subst.
    rewrite E8 in Hm; cbn in Hm.
    rewrite Hm, Z.mod_same by lia.
    rewrite Zmod_0_r; reflexivity.
  - (* wider: [repr 256] is 256 and the outer [mod] is the identity *)
    assert (H256 : (256 < 2 ^ Z.pos sz)%Z).
    { apply Z.lt_le_trans with (2 ^ 9)%Z; [cbn; lia |].
      apply Z.pow_le_mono_r; lia. }
    rewrite Hm, (Z.mod_small 256) by lia.
    rewrite Z.mod_small; [reflexivity |].
    split; [apply Z.mod_pos_bound; lia |].
    eapply Z.lt_trans; [apply Z.mod_pos_bound; lia | lia].
Qed.

(** The same, for any byte that *starts* inside [x] -- in particular the
    last byte of an integer whose width is not a multiple of 8, whose
    missing top bits are the zeros of a zero extension. *)
Lemma extract_byte_vint_spec_lt : forall sz (x : @bit_int sz) idx,
    (8 * Z.of_N idx < Z.pos sz)%Z ->
    extract_byte_vint x idx = ((unsigned x / 2 ^ (8 * Z.of_N idx)) mod 256)%Z.
Proof.
  intros sz x idx H.
  destruct (Z_le_gt_dec (8 * (Z.of_N idx + 1)) (Z.pos sz)) as [Hin | Hout];
    [now apply extract_byte_vint_spec |].
  pose proof (unsigned_range x) as [Hlo Hhi].
  assert (Hm : (@modulus sz = 2 ^ Z.pos sz)%Z)
    by (rewrite modulus_def; apply two_power_pos_eq).
  assert (Hpow : (Z.pos sz < 2 ^ Z.pos sz)%Z) by (apply Z.pow_gt_lin_r; lia).
  assert (Hp : (0 < 2 ^ (8 * Z.of_N idx))%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (Hq : (0 <= Integers.unsigned x / 2 ^ (8 * Z.of_N idx) < 256)%Z).
  { split; [apply Z.div_pos; lia |].
    apply Z.div_lt_upper_bound; [lia |].
    replace 256%Z with (2 ^ 8)%Z by reflexivity.
    rewrite <- Z.pow_add_r by lia.
    rewrite Hm in Hhi.
    eapply Z.lt_le_trans; [exact Hhi | apply Z.pow_le_mono_r; lia]. }
  unfold extract_byte_vint.
  cbn [modu shru unsigned repr VInt_Bounded].
  unfold Integers.modu, Integers.shru.
  rewrite !unsigned_repr_eq.
  rewrite (Z.mod_small (Z.of_N idx * 8)) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (Z.of_N idx * 8)%Z with (8 * Z.of_N idx)%Z by lia.
  rewrite (Z.mod_small (Integers.unsigned x / 2 ^ (8 * Z.of_N idx))).
  2:{ split; [lia |].
      apply Z.le_lt_trans with (Integers.unsigned x); [| lia].
      apply Z.div_le_upper_bound; [lia | nia]. }
  rewrite (Z.mod_small (Integers.unsigned x / 2 ^ (8 * Z.of_N idx)) 256) by lia.
  rewrite Hm.
  destruct (Z_le_gt_dec (Z.pos sz) 8) as [Hle | Hgt].
  - (* at most one byte wide: [repr 256] is 0 and [_ mod 0] is the identity *)
    assert (H0 : (256 mod 2 ^ Z.pos sz = 0)%Z).
    { replace 256%Z with (2 ^ (8 - Z.pos sz) * 2 ^ Z.pos sz)%Z.
      - apply Z.mod_mul; apply Z.pow_nonzero; lia.
      - rewrite <- Z.pow_add_r by lia.
        replace (8 - Z.pos sz + Z.pos sz)%Z with 8%Z by lia; reflexivity. }
    rewrite H0, Zmod_0_r.
    apply Z.mod_small; split; [lia |].
    apply Z.le_lt_trans with (Integers.unsigned x); [| lia].
    apply Z.div_le_upper_bound; [lia | nia].
  - (* wider: [repr 256] is 256 *)
    assert (H256 : (256 < 2 ^ Z.pos sz)%Z).
    { apply Z.lt_le_trans with (2 ^ 9)%Z; [cbn; lia |].
      apply Z.pow_le_mono_r; lia. }
    rewrite (Z.mod_small 256) by lia.
    rewrite (Z.mod_small (Integers.unsigned x / 2 ^ (8 * Z.of_N idx))) by lia.
    apply Z.mod_small; lia.
Qed.

(** Bit-level analogues of [extract_byte_vint_spec] / [concat_bytes_Z_extract],
    for the last byte of an integer whose width is not a multiple of 8: the
    writer stores [sz mod 8] real bits there and pads the rest with poison. *)
Lemma extract_bit_N_spec : forall v i, (0 <= v)%Z ->
    Z.of_N (extract_bit_N (Z.to_N v) i) = ((v / 2 ^ Z.of_N i) mod 2)%Z.
Proof.
  intros v i Hv; unfold extract_bit_N.
  rewrite N.shiftr_div_pow2, N2Z.inj_mod, N2Z.inj_div, N2Z.inj_pow, Z2N.id by lia.
  reflexivity.
Qed.

Lemma concat_bits_Z_extract : forall n v j,
    concat_bits_Z (List.map (fun i => ((v / 2 ^ Z.of_N i) mod 2)%Z) (Nseq j n))
    = ((v / 2 ^ Z.of_N j) mod 2 ^ Z.of_nat n)%Z.
Proof.
  induction n as [| n IH]; intros v j; cbn [Nseq List.map concat_bits_Z].
  - cbn; rewrite Z.mod_1_r; reflexivity.
  - rewrite IH.
    rewrite Z.shiftl_mul_pow2 by lia.
    rewrite N2Z.inj_succ.
    replace (Z.succ (Z.of_N j)) with (Z.of_N j + 1)%Z by lia.
    rewrite Z.pow_add_r by lia.
    rewrite <- Z.div_div by (try lia; apply Z.pow_pos_nonneg; lia).
    replace (Z.of_nat (S n)) with (Z.of_nat n + 1)%Z by lia.
    rewrite Z.pow_add_r by lia.
    replace (2 ^ 1)%Z with 2%Z by reflexivity.
    rewrite (Z.mul_comm (2 ^ Z.of_nat n)%Z 2%Z).
    rewrite (Z.rem_mul_r _ 2 (2 ^ Z.of_nat n)) by (try lia; apply Z.pow_pos_nonneg; lia).
    lia.
Qed.

(** For [DTYPE_Iptr] and the floats the writer uses [extract_byte_Z], the
    plain-[Z] sibling of [extract_byte_vint], and the reader recombines with
    [concat_bytes_Z_vint].  These two lemmas say each is what it looks like. *)
Lemma extract_byte_Z_spec : forall v idx,
    extract_byte_Z v idx = ((v / 2 ^ (8 * Z.of_N idx)) mod 256)%Z.
Proof.
  intros v idx; unfold extract_byte_Z.
  rewrite Z.shiftr_div_pow2 by (pose proof (N2Z.is_nonneg idx); lia).
  replace (Z.of_N idx * 8)%Z with (8 * Z.of_N idx)%Z by lia.
  reflexivity.
Qed.

(* the vint-level fold agrees with the Z-level one, modulo the width *)
Lemma concat_bytes_vint_Z : forall (w : positive) (zs : list Z),
    (8 < @Integers.modulus w)%Z ->
    @concat_bytes_vint _ (VInt_Bounded w) (List.map (@Integers.repr w) zs)
    = Integers.repr (concat_bytes_Z zs).
Proof.
  intros w zs H; induction zs as [| z zs IH]; [reflexivity |].
  cbn [List.map concat_bytes_vint concat_bytes_Z].
  rewrite IH.
  cbn [add shl repr unsigned VInt_Bounded].
  unfold Integers.add, Integers.shl.
  rewrite (Integers.unsigned_repr_eq 8), (Z.mod_small 8) by lia.
  apply Integers.eqm_samerepr.
  apply Integers.eqm_add; [apply Integers.eqm_sym, Integers.eqm_unsigned_repr |].
  eapply Integers.eqm_trans;
    [apply Integers.eqm_sym, Integers.eqm_unsigned_repr |].
  rewrite !Z.shiftl_mul_pow2 by lia.
  apply Integers.eqm_mult; [| apply Integers.eqm_refl].
  apply Integers.eqm_sym, Integers.eqm_unsigned_repr.
Qed.

Section MemoryByteFacts.
  Context {Pa : Params}.


  (* Sanity check for the layout model above: proved as
     [dvalue_to_memory_bytes_sizeof] at the end of this section. *)
  (** [tapad ta x] is [x] rounded up to [a] when the caller asked for a
      trailing alignment, and [x] otherwise. *)
  Definition tapad (ta : option N) (x : N) : N :=
    match ta with
    | None => x
    | Some a => pad_to a x
    end.

  (** The byte-accumulating primitives all satisfy the same invariant: the
      offset advances by exactly the number of bytes appended to [acc]. *)

  Lemma accumulate_poison_bytes_length : forall n acc,
      length (accumulate_poison_bytes n acc) = (N.to_nat n + length acc)%nat.
  Proof.
    intros n acc; unfold accumulate_poison_bytes, accumulate_memory_bytes.
    apply rev_loop_acc_length.
  Qed.

  Lemma accumulate_padding_spec : forall offset ta acc,
      fst (accumulate_padding offset ta acc) = tapad ta offset
      /\ N.of_nat (length (snd (accumulate_padding offset ta acc)))
         = (N.of_nat (length acc) + (tapad ta offset - offset))%N.
  Proof.
    intros offset [a|] acc; cbn; [| split; [reflexivity | lia]].
    unfold pad_to; split; [reflexivity |].
    rewrite accumulate_poison_bytes_length; lia.
  Qed.

  Lemma accumulate_padding_bytes_spec : forall offset n acc,
      fst (accumulate_padding_bytes offset n acc) = (offset + n)%N
      /\ N.of_nat (length (snd (accumulate_padding_bytes offset n acc)))
         = (N.of_nat (length acc) + n)%N.
  Proof.
    intros offset n acc; unfold accumulate_padding_bytes; cbn.
    rewrite accumulate_poison_bytes_length; split; [reflexivity | lia].
  Qed.

  Lemma acc_memory_bytes_of_dvalue_base_spec : forall dtb dv offset acc,
      fst (acc_memory_bytes_of_dvalue_base dtb dv offset acc)
      = (store_size_dtyp (DTYPE_Base dtb) + offset)%N
      /\ N.of_nat (length (snd (acc_memory_bytes_of_dvalue_base dtb dv offset acc)))
         = (N.of_nat (length acc) + store_size_dtyp (DTYPE_Base dtb))%N.
  Proof.
    intros dtb dv offset acc; unfold acc_memory_bytes_of_dvalue_base; cbn.
    rewrite rev_loop_acc_length; split; [reflexivity | lia].
  Qed.

  (** Unfolding equations for the non-loop branches of the serializer.  Used
      instead of [cbn], which reduces the helpers away and leaves a goal that
      no longer mentions them. *)
  (* Top-level copies of the two loops that [acc_dvalue_to_memory_bytes_h]
     defines locally, abstracted over the recursive call [ser] so that they
     can be reasoned about by induction.  Everything the local loops capture
     ([tail_align], [pad], the element type and its padding) is a section
     variable, so each [Fixpoint] elaborates to a [fix] over exactly the
     arguments the local one takes -- which is what makes the [ser_*_unfold]
     equations below hold by [reflexivity]. *)
  Section SerStructLoop.
    Variable ser : dtyp -> dvalue -> N -> option N -> list memory_byte ->
                   EOU (N * list memory_byte).
    Variable tail_align : option N.
    Variable pad : option N.

    Fixpoint struct_bytes_loop (fields : list dvalue) (types : list dtyp)
      (offset : N) (acc : list memory_byte) {struct fields}
      : EOU (N * list memory_byte) :=
      match fields, types with
      | [], [] =>
          let '(offset, acc) := accumulate_padding offset pad acc in
          ret (accumulate_padding offset tail_align acc)
      | f::fs, dt::dts =>
          let a := preferred_alignment (dtyp_alignment dt) in
          let ssz := store_size_dtyp dt in
          let asz := alloc_size_dtyp dt in
          let '(offset, acc) :=
            accumulate_padding offset (if pad then Some a else None) acc in
          '(coff, bs) <- ser dt f 0%N None acc ;;
          let '(offset'', bs') :=
            accumulate_padding_bytes (offset + coff)%N (asz - ssz) bs in
          struct_bytes_loop fs dts offset'' bs'
      | _, _ => raise_error "type-mismatch: structs / fields have different lengths"
      end.
  End SerStructLoop.

  Section SerArrayLoop.
    Variable ser : dtyp -> dvalue -> N -> option N -> list memory_byte ->
                   EOU (N * list memory_byte).
    Variable tail_align : option N.
    Variable dt : dtyp.
    Variable elt_pad : N.

    Fixpoint array_bytes_loop (elts : list dvalue) (offset : N)
      (acc : list memory_byte) {struct elts} : EOU (N * list memory_byte) :=
      match elts with
      | [] => ret (accumulate_padding offset tail_align acc)
      | e::es =>
          '(coff, bs) <- ser dt e 0%N None acc ;;
          let '(offset'', bs') :=
            accumulate_padding_bytes (offset + coff)%N elt_pad bs in
          array_bytes_loop es offset'' bs'
      end.
  End SerArrayLoop.

  Lemma ser_struct_unfold : forall packed dts p fields offset ta acc,
      acc_dvalue_to_memory_bytes_h (DTYPE_Struct packed dts)
        (DVALUE_Struct p fields) offset ta acc =
        struct_bytes_loop acc_dvalue_to_memory_bytes_h ta
          (if packed then None else Some (max_preferred_dtyp_alignment dts))
          fields dts offset acc.
  Proof. reflexivity. Qed.

  Lemma ser_array_unfold : forall vec sz t p elts offset ta acc,
      acc_dvalue_to_memory_bytes_h (DTYPE_Array vec sz t)
        (DVALUE_Array p elts) offset ta acc =
        array_bytes_loop acc_dvalue_to_memory_bytes_h ta t
          (if vec then 0%N else (alloc_size_dtyp t - store_size_dtyp t)%N)
          elts offset acc.
  Proof. reflexivity. Qed.

  Lemma ser_base_unfold : forall dtb dv offset ta acc,
      acc_dvalue_to_memory_bytes_h (DTYPE_Base dtb) (DVALUE_Base dv) offset ta acc =
        let '(offset', bs) := acc_memory_bytes_of_dvalue_base dtb dv offset acc in
        ret (accumulate_padding offset' ta bs).
  Proof. reflexivity. Qed.

  Lemma ser_struct_poison_unfold : forall packed dts offset ta acc,
      acc_dvalue_to_memory_bytes_h (DTYPE_Struct packed dts)
        (DVALUE_Base DVALUE_Poison) offset ta acc =
        let '(offset', bs) :=
          accumulate_padding_bytes offset (store_size_dtyp (DTYPE_Struct packed dts)) acc in
        ret (accumulate_padding offset' ta bs).
  Proof. reflexivity. Qed.

  Lemma ser_array_poison_unfold : forall vec sz t offset ta acc,
      acc_dvalue_to_memory_bytes_h (DTYPE_Array vec sz t)
        (DVALUE_Base DVALUE_Poison) offset ta acc =
        let '(offset', bs) :=
          accumulate_padding_bytes offset (store_size_dtyp (DTYPE_Array vec sz t)) acc in
        ret (accumulate_padding offset' ta bs).
  Proof. reflexivity. Qed.

  (* Shape of the accumulator invariant: the returned offset says how many
     bytes were appended to [acc]. *)
  Definition acc_ok (offset : N) (acc : list memory_byte)
                    (r : N * list memory_byte) : Prop :=
    N.of_nat (length (snd r)) = (N.of_nat (length acc) + (fst r - offset))%N
    /\ (offset <= fst r)%N.

  Lemma tapad_ge : forall ta x, (x <= tapad ta x)%N.
  Proof. intros [a|] x; cbn; unfold pad_to; lia. Qed.

  (** The offset a struct's field loop reaches after one field: align (unpacked
      only), then advance by the field's *alloc* size.  [fold_left sfe_step]
      from 0 is [struct_fields_extent] on the nose. *)
  Definition sfe_step (pad : option N) : N -> dtyp -> N :=
    fun a t =>
      (tapad (if pad then Some (preferred_alignment (dtyp_alignment t)) else None) a
       + alloc_size_dtyp t)%N.

  Lemma struct_bytes_loop_nil : forall ser ta pad offset acc,
      struct_bytes_loop ser ta pad [] [] offset acc =
        let '(offset, acc) := accumulate_padding offset pad acc in
        ret (accumulate_padding offset ta acc).
  Proof. reflexivity. Qed.

  Lemma struct_bytes_loop_cons : forall ser ta pad f fs dt dts offset acc,
      struct_bytes_loop ser ta pad (f::fs) (dt::dts) offset acc =
        let '(offset, acc) :=
          accumulate_padding offset
            (if pad then Some (preferred_alignment (dtyp_alignment dt)) else None) acc in
        '(coff, bs) <- ser dt f 0%N None acc ;;
        let '(offset'', bs') :=
          accumulate_padding_bytes (offset + coff)%N
            (alloc_size_dtyp dt - store_size_dtyp dt)%N bs in
        struct_bytes_loop ser ta pad fs dts offset'' bs'.
  Proof. reflexivity. Qed.

  Lemma array_bytes_loop_nil : forall ser ta dt ep offset acc,
      array_bytes_loop ser ta dt ep [] offset acc =
        ret (accumulate_padding offset ta acc).
  Proof. reflexivity. Qed.

  Lemma array_bytes_loop_cons : forall ser ta dt ep e es offset acc,
      array_bytes_loop ser ta dt ep (e::es) offset acc =
        '(coff, bs) <- ser dt e 0%N None acc ;;
        let '(offset'', bs') := accumulate_padding_bytes (offset + coff)%N ep bs in
        array_bytes_loop ser ta dt ep es offset'' bs'.
  Proof. reflexivity. Qed.

  (** The property proved by [acc_dvalue_to_memory_bytes_h_spec], named so that
      the two loop lemmas can take the induction hypothesis as [Forall ser_spec]. *)
  Definition ser_spec (dv : dvalue) : Prop :=
    forall dt, dvalue_has_dtyp dv dt ->
    forall ta acc offset' bs,
      acc_dvalue_to_memory_bytes_h dt dv 0%N ta acc = raise_ret (offset', bs) ->
      offset' = tapad ta (store_size_dtyp dt)
      /\ N.of_nat (length bs) = (N.of_nat (length acc) + offset')%N.

  Ltac cbn_ser H :=
    cbn -[acc_dvalue_to_memory_bytes_h accumulate_padding accumulate_padding_bytes
          struct_bytes_loop array_bytes_loop store_size_dtyp alloc_size_dtyp
          pad_to_align dtyp_alignment preferred_alignment
          max_preferred_dtyp_alignment] in H.

  Lemma struct_bytes_loop_spec :
    forall fs ts, Forall2 dvalue_has_dtyp fs ts ->
      Forall ser_spec fs ->
      forall pad ta offset acc offset' bs,
        struct_bytes_loop acc_dvalue_to_memory_bytes_h ta pad fs ts offset acc
          = raise_ret (offset', bs) ->
        offset' = tapad ta (tapad pad (fold_left (sfe_step pad) ts offset))
        /\ N.of_nat (length bs) = (N.of_nat (length acc) + (offset' - offset))%N
        /\ (offset <= offset')%N.
  Proof.
    intros fs ts HF2; induction HF2 as [| f t fs ts Hft HF2 IHl];
      intros HS pad ta offset acc offset' bs Heq.
    - rewrite struct_bytes_loop_nil in Heq.
      destruct (accumulate_padding_spec offset pad acc) as [P1 P2].
      destruct (accumulate_padding offset pad acc) as [o1 a1]; cbn in P1, P2; subst o1.
      destruct (accumulate_padding_spec (tapad pad offset) ta a1) as [Q1 Q2].
      destruct (accumulate_padding (tapad pad offset) ta a1) as [o2 a2];
        cbn in Q1, Q2; subst o2.
      cbn_ser Heq; inversion Heq; subst; clear Heq.
      pose proof (tapad_ge pad offset) as G1.
      pose proof (tapad_ge ta (tapad pad offset)) as G2.
      cbn [fold_left]; split; [reflexivity | split; lia].
    - inversion HS as [| ? ? Hhd Htl]; subst; clear HS.
      rewrite struct_bytes_loop_cons in Heq.
      (* leading alignment of the field *)
      destruct (accumulate_padding_spec offset
                  (if pad then Some (preferred_alignment (dtyp_alignment t)) else None) acc)
        as [P1 P2].
      destruct (accumulate_padding offset
                  (if pad then Some (preferred_alignment (dtyp_alignment t)) else None) acc)
        as [o1' a1]; cbn in P1, P2; subst o1'.
      pose proof (tapad_ge
                    (if pad then Some (preferred_alignment (dtyp_alignment t)) else None)
                    offset) as G1.
      remember (tapad (if pad then Some (preferred_alignment (dtyp_alignment t)) else None)
                  offset) as o1 eqn:Ho1.
      (* the field itself, laid out from 0 *)
      cbn_ser Heq.
      destruct (acc_dvalue_to_memory_bytes_h t f 0%N None a1)
        as [ | | | [coff cbs] ] eqn:EF; cbn_ser Heq; try discriminate.
      destruct (Hhd _ Hft None a1 _ _ EF) as [Ec Elc]; cbn [tapad] in Ec; subst coff.
      (* pad the field out to its alloc size *)
      destruct (accumulate_padding_bytes_spec (o1 + store_size_dtyp t)%N
                  (alloc_size_dtyp t - store_size_dtyp t)%N cbs) as [R1 R2].
      destruct (accumulate_padding_bytes (o1 + store_size_dtyp t)%N
                  (alloc_size_dtyp t - store_size_dtyp t)%N cbs) as [o2 a2];
        cbn in R1, R2; subst o2.
      pose proof (store_le_alloc t) as SA.
      assert (EQ : (o1 + store_size_dtyp t + (alloc_size_dtyp t - store_size_dtyp t))%N
                   = sfe_step pad offset t).
      { unfold sfe_step; rewrite <- Ho1; lia. }
      rewrite EQ in Heq.
      destruct (IHl Htl pad ta _ a2 _ _ Heq) as [Eo [Elen Ele]].
      cbn [fold_left]; split; [exact Eo | split ].
      + rewrite Elen, R2, Elc, P2; lia.
      + lia.
  Qed.

  Lemma array_bytes_loop_spec :
    forall elts t, Forall (fun x => dvalue_has_dtyp x t) elts ->
      Forall ser_spec elts ->
      forall ta ep offset acc offset' bs,
        array_bytes_loop acc_dvalue_to_memory_bytes_h ta t ep elts offset acc
          = raise_ret (offset', bs) ->
        offset' = tapad ta (offset + N.of_nat (length elts) * (store_size_dtyp t + ep))%N
        /\ N.of_nat (length bs) = (N.of_nat (length acc) + (offset' - offset))%N
        /\ (offset <= offset')%N.
  Proof.
    intros elts t HT; induction elts as [| e es IHl];
      intros HS ta ep offset acc offset' bs Heq.
    - rewrite array_bytes_loop_nil in Heq.
      destruct (accumulate_padding_spec offset ta acc) as [Q1 Q2].
      destruct (accumulate_padding offset ta acc) as [o2 a2]; cbn in Q1, Q2; subst o2.
      cbn_ser Heq; inversion Heq; subst; clear Heq.
      pose proof (tapad_ge ta offset) as G.
      split; [f_equal; cbn [length]; lia | split; lia].
    - inversion HT as [| ? ? Hhd HTtl]; subst; clear HT.
      inversion HS as [| ? ? Shd Stl]; subst; clear HS.
      rewrite array_bytes_loop_cons in Heq.
      cbn_ser Heq.
      destruct (acc_dvalue_to_memory_bytes_h t e 0%N None acc)
        as [ | | | [coff cbs] ] eqn:EF; cbn_ser Heq; try discriminate.
      destruct (Shd _ Hhd None acc _ _ EF) as [Ec Elc]; cbn [tapad] in Ec; subst coff.
      destruct (accumulate_padding_bytes_spec (offset + store_size_dtyp t)%N ep cbs)
        as [R1 R2].
      destruct (accumulate_padding_bytes (offset + store_size_dtyp t)%N ep cbs)
        as [o2 a2]; cbn in R1, R2; subst o2.
      destruct (IHl HTtl Stl ta ep _ a2 _ _ Heq) as [Eo [Elen Ele]].
      split; [| split].
      + rewrite Eo; f_equal; cbn [length]; lia.
      + rewrite Elen, R2, Elc; lia.
      + lia.
  Qed.

  Lemma acc_dvalue_to_memory_bytes_h_spec :
    forall dv dt, dvalue_has_dtyp dv dt ->
    forall ta acc offset' bs,
      acc_dvalue_to_memory_bytes_h dt dv 0%N ta acc = raise_ret (offset', bs) ->
      offset' = tapad ta (store_size_dtyp dt)
      /\ N.of_nat (length bs) = (N.of_nat (length acc) + offset')%N.
  Proof.
    intros dv; induction dv using dvalue_ind;
      intros dt HT ta acc offset' bs Heq.
    - (* DVALUE_Base: the value's own bytes (or the type's worth of poison
         bytes at an aggregate type), then the caller's trailing pad. *)
      assert (POIS : forall n,
                 let '(o1, a1) := accumulate_padding_bytes 0%N n acc in
                 let '(o2, a2) := accumulate_padding o1 ta a1 in
                 o2 = tapad ta n
                 /\ N.of_nat (length a2) = (N.of_nat (length acc) + o2)%N).
      { intros n.
        pose proof (accumulate_padding_bytes_spec 0%N n acc) as [E1 L1].
        destruct (accumulate_padding_bytes 0%N n acc) as [o1 a1]; cbn in E1, L1.
        pose proof (accumulate_padding_spec o1 ta a1) as [E2 L2].
        destruct (accumulate_padding o1 ta a1) as [o2 a2]; cbn in E2, L2.
        subst o1 o2; split; [reflexivity |].
        rewrite L2, L1; destruct ta as [a|]; cbn; unfold pad_to; lia. }
      destruct dt as [dtb | packed dts | vec sz t].
      + rewrite ser_base_unfold in Heq.
        pose proof (acc_memory_bytes_of_dvalue_base_spec dtb dv 0%N acc) as [E1 L1].
        destruct (acc_memory_bytes_of_dvalue_base dtb dv 0%N acc) as [o1 a1];
          cbn in E1, L1.
        pose proof (accumulate_padding_spec o1 ta a1) as [E2 L2].
        destruct (accumulate_padding o1 ta a1) as [o2 a2]; cbn in E2, L2, Heq.
        inversion Heq; subst.
        rewrite ?N.add_0_r in *.
        split; [first [assumption | reflexivity] |].
        rewrite L2, L1; destruct ta as [a|]; cbn; unfold pad_to; lia.
      + (* a base value at an aggregate type must be poison
           ([DVALUE_Poison_typ_agg] is the only applicable constructor) *)
        inversion HT; subst.
        rewrite ser_struct_poison_unfold in Heq.
        specialize (POIS (store_size_dtyp (DTYPE_Struct packed dts))).
        destruct (accumulate_padding_bytes 0%N
                    (store_size_dtyp (DTYPE_Struct packed dts)) acc) as [o1 a1].
        destruct (accumulate_padding o1 ta a1) as [o2 a2]; cbn in Heq.
        inversion Heq; subst; exact POIS.
      + inversion HT; subst.
        rewrite ser_array_poison_unfold in Heq.
        specialize (POIS (store_size_dtyp (DTYPE_Array vec sz t))).
        destruct (accumulate_padding_bytes 0%N
                    (store_size_dtyp (DTYPE_Array vec sz t)) acc) as [o1 a1].
        destruct (accumulate_padding o1 ta a1) as [o2 a2]; cbn in Heq.
        inversion Heq; subst; exact POIS.
    - (* DVALUE_Struct *)
      inversion HT as [| | pp ffs ddts HNP HF2 |]; subst.
      rewrite ser_struct_unfold in Heq.
      destruct (struct_bytes_loop_spec HF2 IH _ _ _ _ Heq) as [Eo [Elen Ele]].
      split.
      + rewrite Eo; f_equal.
        destruct p.
        * rewrite store_size_dtyp_Packed_struct; reflexivity.
        * rewrite store_size_dtyp_Struct; reflexivity.
      + rewrite Elen; lia.
    - (* DVALUE_Array *)
      inversion HT as [| | | vv ees ssz eet HNV HNP HFA HLen]; subst.
      rewrite ser_array_unfold in Heq.
      destruct (array_bytes_loop_spec HFA IH _ _ _ _ Heq) as [Eo [Elen Ele]].
      split.
      + rewrite Eo; f_equal.
        rewrite HLen, Nnat.N2Nat.id.
        destruct v.
        * rewrite store_size_dtyp_vector; cbv beta iota; lia.
        * rewrite store_size_dtyp_array; cbv beta iota.
          replace (store_size_dtyp eet + (alloc_size_dtyp eet - store_size_dtyp eet))%N
            with (alloc_size_dtyp eet)
            by (pose proof (store_le_alloc eet); lia).
          reflexivity.
      + rewrite Elen; lia.
  Qed.

  Lemma dvalue_to_memory_bytes_sizeof :
    forall dt dv tail_align bytes,
      dvalue_has_dtyp dv dt ->
      dvalue_to_memory_bytes dt dv tail_align = raise_ret bytes ->
      (N.of_nat (List.length bytes)) =
        match tail_align with
        | None => store_size_dtyp dt
        | Some a => pad_to a (store_size_dtyp dt)
        end.
  Proof.
    intros dt dv ta bytes HT.
    unfold dvalue_to_memory_bytes.
    destruct (acc_dvalue_to_memory_bytes_h dt dv 0%N ta (@nil memory_byte))
      as [ | | | [off bs] ] eqn:E;
      cbn; try discriminate.
    intros EQ; inversion EQ; subst; clear EQ.
    destruct (acc_dvalue_to_memory_bytes_h_spec HT ta (@nil memory_byte) E) as [Eo Elen].
    rewrite rev_append_rev, app_nil_r, length_rev, Elen; cbn.
    subst off; destruct ta; reflexivity.
  Qed.
  
  (* one-step unfolding for the recursive case; [cbn] would splice the
     recursive call in too, leaving no [concat_bytes_Z_mixed] for an
     induction hypothesis to apply to *)
  Lemma concat_bytes_Z_mixed_cons2 : forall extra b d rest,
      concat_bytes_Z_mixed extra (b :: d :: rest) =
        z <- memory_byte_to_Z b ;;
        r <- concat_bytes_Z_mixed extra (d :: rest) ;;
        ret (z + Z.shiftl r 8)%Z.
  Proof. intros extra b d rest; destruct b; reflexivity. Qed.

  (** ** Round trip: deserializing a serialization

      Two side conditions, both necessary (each has a checked counterexample):

      - [tail_align] must be [None].  With [Some a] the writer appends poison
        out to [pad_to a (store_size_dtyp dt)], but the reader is never told
        [a].  Aggregates ignore trailing bytes (each loop consumes only what
        its type needs) but base types do not: an [i32] written with [Some 8]
        reads back as [DVALUE_Poison], because the integer read consumes the
        four padding bytes too.

      - [dt] must be [serializable].  [memory_bytes_to_dvalue_base] is partial:
        it raises an error on [DTYPE_Void] and on the floating-point and opaque
        types it does not implement.  Since poison inhabits *every* type
        ([DVALUE_Poison_typ_agg]), each of those types has well-typed values -
        e.g. poison at [DTYPE_FP FP_half], or [DVALUE_None] at [DTYPE_Void] -
        that the reader cannot produce. *)

  (* [DTYPE_Iptr] is deliberately excluded: it is not an LLVM IR type, and it
     does not round-trip under the infinite-pointer instance, where [to_Z] is
     unbounded but the type still occupies only [ptr_size] bytes -- so any
     value of at least [2 ^ (8 * ptr_size)] is truncated by the writer. *)
  Definition serializable_base (dt : dtyp_base) : Prop :=
    match dt with
    | DTYPE_I _ | DTYPE_Pointer | DTYPE_B _ => True
    | DTYPE_FP FP_float | DTYPE_FP FP_double => True
    | _ => False
    end.

  Fixpoint serializable (dt : dtyp) : Prop :=
    match dt with
    | DTYPE_Base dt => serializable_base dt
    | DTYPE_Struct _ dts => FORALL serializable dts
    | DTYPE_Array _ _ t => serializable t
    end.

  Lemma serializable_NO_VOID : forall dt, serializable dt -> NO_VOID dt.
  Proof.
    induction dt as [db | pk dts IH | vv sz t IHt];
      cbn [serializable NO_VOID].
    - destruct db; cbn; auto; destruct f; cbn; auto.
    - unfold FORALL; revert IH; induction dts as [| t ts IHts]; cbn; auto.
      intros IH [Ht Hts]; split.
      + apply (IH t (or_introl eq_refl)), Ht.
      + apply IHts; [intros u INu; apply IH; now right | exact Hts].
    - auto.
  Qed.

  (** How [poison_split] -- the reader's all-poison fast path -- reacts to
      extra bytes after the value.  Either the value already has a non-poison
      byte, in which case the split index is unchanged and the extra bytes
      just ride along on the tail; or it does not, in which case the scan runs
      on into the extra bytes.  Together these say the fast path is taken on
      [w ++ extra] exactly when it is taken on both parts. *)
  (** The byte generator [acc_memory_bytes_of_dvalue_base] uses, lifted out of
      its [let] so that proofs can name it.  [acc_base_unfold] says the lift is
      exact. *)
  Definition base_byte_gen (dv : dvalue_base) : N -> memory_byte :=
    match dv with
    | DVALUE_I sz x => memory_byte_of_dvalue_bv (BYTE_I x)
    | DVALUE_Iptr x => fun idx => BYTE_I (repr (extract_byte_Z (to_Z x) idx))
    | DVALUE_Pointer ptr => BYTE_Pointer 8 ptr
    | DVALUE_Float f => fun idx => BYTE_I (repr (extract_byte_Z (unsigned (Float32.to_bits f)) idx))
    | DVALUE_Double d => fun idx => BYTE_I (repr (extract_byte_Z (unsigned (Float.to_bits d)) idx))
    | DVALUE_Poison => fun idx => poison_memory_byte
    | DVALUE_None => fun idx => poison_memory_byte
    | DVALUE_B sz bits => memory_byte_of_dvalue_bv bits
    end.

  Lemma acc_base_unfold : forall dtb dv offset acc,
      acc_memory_bytes_of_dvalue_base dtb dv offset acc
      = ((store_size_dtyp (DTYPE_Base dtb) + offset)%N,
         N.rev_loop_acc (base_byte_gen dv) (store_size_dtyp (DTYPE_Base dtb)) 0 acc).
  Proof. intros dtb dv offset acc; destruct dv; reflexivity. Qed.

  (** The forward-order block the writer lays down for a base value is
      [List.map (base_byte_gen dv) (Nseq 0 (N.to_nat (store_size_dtyp _)))];
      it is spelled out rather than named so that it matches the goal the
      writer's unfolding produces. *)
  Lemma base_block_length : forall dtb dv,
      N.of_nat (length (List.map (base_byte_gen dv)
                          (Nseq 0 (N.to_nat (store_size_dtyp (DTYPE_Base dtb))))))
      = store_size_dtyp (DTYPE_Base dtb).
  Proof.
    intros dtb dv; rewrite length_map, Nseq_length; apply Nnat.N2Nat.id.
  Qed.

  (** ** All-poison blocks

      The writer emits padding, and a poison value at an aggregate type, as a
      run of [poison_memory_byte]; the reader answers any such run with
      [DVALUE_Poison].  These lemmas turn both sides into [List.repeat]. *)

  Lemma accumulate_poison_bytes_app : forall n acc,
      accumulate_poison_bytes n acc
      = List.repeat poison_memory_byte (N.to_nat n) ++ acc.
  Proof.
    intros n acc; unfold accumulate_poison_bytes, accumulate_memory_bytes.
    apply rev_loop_acc_const.
  Qed.

  Lemma is_all_poison_memory_byte : is_all_poison_byte poison_memory_byte = true.
  Proof. reflexivity. Qed.

  Lemma poison_split_repeat : forall k,
      poison_split (List.repeat poison_memory_byte k) = (N.of_nat k, []).
  Proof.
    induction k; [reflexivity |].
    cbn [List.repeat poison_split].
    rewrite is_all_poison_memory_byte, IHk; cbv beta iota.
    replace (N.of_nat (S k)) with (1 + N.of_nat k)%N by lia; reflexivity.
  Qed.

  (* an all-poison buffer reads as [DVALUE_Poison] at any aggregate type *)
  Lemma read_repeat_poison_agg : forall dt L,
      match dt with DTYPE_Base _ => False | _ => True end ->
      memory_bytes_to_dvalue (List.repeat poison_memory_byte L) dt
      = ret (DVALUE_Base DVALUE_Poison).
  Proof.
    intros dt L H; destruct dt as [db | pk dts | vv sz t]; [contradiction | |];
      cbn [memory_bytes_to_dvalue]; rewrite poison_split_repeat;
      cbv beta iota; reflexivity.
  Qed.

  (** ** The poison and pointer blocks

      Poison is uniform across every serializable base type: the writer emits
      a run of [poison_memory_byte] and each arm of the reader absorbs it.
      A pointer is laid down as the run [BYTE_Pointer 8 p 0 .. 8 p (k-1)],
      which is exactly what [valid_pointer_bytes] walks. *)

  Lemma serializable_base_pos : forall dtb,
      serializable_base dtb -> (0 < store_size_dtyp (DTYPE_Base dtb))%N.
  Proof.
    intros dtb H; destruct dtb as [sz | | | | fp | | | | | | sz];
      cbn in H; try contradiction.
    - rewrite store_size_dtyp_int; apply N.div_str_pos; lia.
    - exact store_size_dtyp_ptr_pos.
    - destruct fp; cbn in H; try contradiction.
      + rewrite store_size_dtyp_float; lia.
      + rewrite store_size_dtyp_double; lia.
    - rewrite store_size_dtyp_bytes; apply N.div_str_pos; lia.
  Qed.

  Lemma memory_byte_to_Z_poison : memory_byte_to_Z poison_memory_byte = raise_ret Pois.
  Proof. reflexivity. Qed.

  Lemma memory_bits_to_Z_poison_cons : forall rest,
      memory_bits_to_Z (Bit_psn :: rest) = raise_ret Pois.
  Proof.
    intros rest; unfold memory_bits_to_Z.
    rewrite (map_monad_EOUP_pois_head memory_bit_to_bit Bit_psn rest eq_refl).
    reflexivity.
  Qed.

  Lemma map_monad_byte_to_Z_poison : forall k, (0 < k)%nat ->
      map_monad memory_byte_to_Z (List.repeat poison_memory_byte k) = raise_ret Pois.
  Proof.
    intros [| k'] H; [lia |]; cbn [List.repeat].
    apply map_monad_EOUP_pois_head, memory_byte_to_Z_poison.
  Qed.

  Lemma concat_bytes_Z_mixed_poison : forall extra k,
      (0 < extra)%N -> (0 < k)%nat ->
      concat_bytes_Z_mixed extra (List.repeat poison_memory_byte k)
      = raise_ret Pois.
  Proof.
    intros extra [| [| k'']] Hx Hk; [lia | |].
    - (* exactly one byte: the last-byte-mixed path *)
      cbn [List.repeat]; unfold poison_memory_byte;
        cbn [concat_bytes_Z_mixed memory_byte_to_memory_bits].
      destruct (@take_repeat_cons _ Bit_psn extra 8 Hx ltac:(lia)) as [r Hr].
      rewrite Hr, memory_bits_to_Z_poison_cons; reflexivity.
    - (* two or more: the first byte already poisons the fold *)
      cbn [List.repeat concat_bytes_Z_mixed].
      rewrite memory_byte_to_Z_poison; reflexivity.
  Qed.

  Lemma memory_bytes_to_int_poison : forall sz k,
      (0 < k)%nat ->
      memory_bytes_to_int sz (List.repeat poison_memory_byte k) = raise_ret Pois.
  Proof.
    intros sz k H; unfold memory_bytes_to_int.
    destruct (N.eqb_spec (N.modulo (Npos sz) 8) 0) as [E | E]; cbn [negb].
    - rewrite map_monad_byte_to_Z_poison by exact H; reflexivity.
    - (* [lia] does not know [N.modulo]; abstract it first *)
      assert (Hx : (0 < N.pos sz mod 8)%N)
        by (revert E; generalize (N.pos sz mod 8)%N; intros m Hm; lia).
      apply concat_bytes_Z_mixed_poison; [exact Hx | exact H].
  Qed.

  Lemma memory_bytes_to_pointer_poison : forall k, (0 < k)%nat ->
      memory_bytes_to_pointer (List.repeat poison_memory_byte k) = raise_ret Pois.
  Proof.
    intros [| k'] H; [lia |].
    cbn [List.repeat]; unfold poison_memory_byte, memory_bytes_to_pointer;
      cbn [List.repeat]; reflexivity.
  Qed.

  Lemma all_poison_bytes_repeat : forall k,
      all_poison_bytes (List.repeat poison_memory_byte k) = true.
  Proof.
    intros k; unfold all_poison_bytes; rewrite poison_split_repeat; reflexivity.
  Qed.

  Lemma read_base_block_poison : forall dtb,
      serializable_base dtb ->
      memory_bytes_to_dvalue_base
        (List.repeat poison_memory_byte
           (N.to_nat (store_size_dtyp (DTYPE_Base dtb)))) dtb
      = ret DVALUE_Poison.
  Proof.
    intros dtb H.
    assert (Hk : (0 < N.to_nat (store_size_dtyp (DTYPE_Base dtb)))%nat)
      by (pose proof (serializable_base_pos dtb H); lia).
    destruct dtb as [sz | | | | fp | | | | | | sz];
      cbn in H; try contradiction; cbn [memory_bytes_to_dvalue_base].
    - rewrite memory_bytes_to_int_poison by exact Hk; reflexivity.
    - rewrite memory_bytes_to_pointer_poison by exact Hk; reflexivity.
    - destruct fp; cbn in H; try contradiction;
        rewrite map_monad_byte_to_Z_poison by exact Hk; reflexivity.
    - rewrite all_poison_bytes_repeat; reflexivity.
  Qed.

  (** The writer lays a pointer down as the run
      [BYTE_Pointer 8 p 0, BYTE_Pointer 8 p 1, ...], which is exactly the
      shape [valid_pointer_bytes] walks; its terminator compares the index
      reached against [store_size_dtyp (DTYPE_Base DTYPE_Pointer)], which is
      how many bytes the writer emitted. *)
  Lemma valid_pointer_bytes_run : forall p n i,
      valid_pointer_bytes p i (List.map (BYTE_Pointer 8 p) (Nseq i n))
      = ret (N.eqb (i + N.of_nat n) (store_size_dtyp (DTYPE_Base DTYPE_Pointer))).
  Proof.
    intros p; induction n as [| n IH]; intros i;
      cbn [Nseq List.map valid_pointer_bytes].
    - replace (i + N.of_nat 0)%N with i by lia; reflexivity.
    - unfold valid_pointer_byte.
      destruct (eq_dec_ptr p p) as [_ | NE]; [| now contradiction NE].
      rewrite N.eqb_refl; cbv beta iota.
      replace (N.succ i) with (1 + i)%N by lia.
      rewrite IH.
      replace (1 + i + N.of_nat n)%N with (i + N.of_nat (S n))%N by lia.
      reflexivity.
  Qed.

  Lemma memory_bytes_to_pointer_run : forall p n,
      (0 < n)%nat ->
      N.of_nat n = store_size_dtyp (DTYPE_Base DTYPE_Pointer) ->
      memory_bytes_to_pointer (List.map (BYTE_Pointer 8 p) (Nseq 0 n))
      = raise_ret (NoPois p).
  Proof.
    intros p [| n'] Hn Hsz; [lia |].
    unfold memory_bytes_to_pointer.
    cbn [Nseq List.map]; cbv beta iota.
    change (BYTE_Pointer 8 p 0 :: List.map (BYTE_Pointer 8 p) (Nseq (N.succ 0) n'))
      with (List.map (BYTE_Pointer 8 p) (Nseq 0 (S n'))).
    rewrite valid_pointer_bytes_run.
    replace (0 + N.of_nat (S n'))%N
      with (store_size_dtyp (DTYPE_Base DTYPE_Pointer)) by lia.
    rewrite N.eqb_refl; reflexivity.
  Qed.

  Lemma read_base_block_pointer : forall p,
      memory_bytes_to_dvalue_base
        (List.map (base_byte_gen (DVALUE_Pointer p))
                  (Nseq 0 (N.to_nat (store_size_dtyp (DTYPE_Base DTYPE_Pointer)))))
        DTYPE_Pointer
      = ret (DVALUE_Pointer p).
  Proof.
    intros p; pose proof store_size_dtyp_ptr_pos as Hp.
    cbn [memory_bytes_to_dvalue_base base_byte_gen].
    rewrite memory_bytes_to_pointer_run by lia.
    reflexivity.
  Qed.

  (** ** Integers of a whole number of bytes

      When the width is a multiple of 8 the writer emits plain [BYTE_I]s and
      the reader's [memory_bytes_to_int] takes its non-mixed branch, so the
      round trip is [concat_bytes_Z_extract] plus [extract_byte_vint_spec]
      and some plumbing. *)

  Lemma map_monad_byte_to_Z_BYTE_I : forall (f : N -> @bit_int 8) l,
      map_monad memory_byte_to_Z (List.map (fun i => @BYTE_I Pa 8 (f i)) l)
      = raise_ret (NoPois (List.map (fun i => Integers.unsigned (f i)) l)).
  Proof.
    intros f; induction l as [| a l IH]; [reflexivity |].
    cbn [List.map]; cbn [map_monad].
    rewrite IH; reflexivity.
  Qed.

  Lemma read_int_block_mult8 : forall sz (x : @bit_int sz),
      (Npos sz mod 8 = 0)%N ->
      memory_bytes_to_dvalue_base
        (List.map (memory_byte_of_dvalue_bv (BYTE_I x))
                  (Nseq 0 (N.to_nat (store_size_dtyp (DTYPE_Base (DTYPE_I sz))))))
        (DTYPE_I sz)
      = ret (DVALUE_I sz x).
  Proof.
    intros sz x H8.
    pose proof (@store_size_int_mult8 _ _ sz H8) as Hk.
    pose proof (Integers.unsigned_range x) as [Hlo Hhi].
    assert (Hm : (@Integers.modulus sz = 2 ^ Z.pos sz)%Z)
      by (rewrite Integers.modulus_def; apply two_power_pos_eq).
    (* the generator takes the non-mixed branch *)
    assert (Hgen : forall idx, memory_byte_of_dvalue_bv (BYTE_I x) idx
                               = BYTE_I (repr (extract_byte_vint x idx))).
    { intros idx; reflexivity. }
    cbn [memory_bytes_to_dvalue_base].
    unfold memory_bytes_to_int; rewrite H8; cbn [N.eqb negb].
    erewrite map_ext by exact Hgen.
    rewrite map_monad_byte_to_Z_BYTE_I.
    cbn -[store_size_dtyp Nseq concat_bytes_Z Integers.unsigned
          Z.pow Z.div Z.modulo List.map extract_byte_vint Integers.repr].
    do 2 f_equal.
    erewrite map_ext_in with
      (g := fun i => ((Integers.unsigned x / 2 ^ (8 * Z.of_N i)) mod 256)%Z).
    2:{ intros i Hi; apply In_Nseq in Hi.
        cbn [repr unsigned VInt_Bounded].
        rewrite Integers.unsigned_repr_eq.
        rewrite extract_byte_vint_spec by lia.
        replace (@Integers.modulus 8) with 256%Z by reflexivity.
        rewrite Z.mod_mod by lia; reflexivity. }
    rewrite concat_bytes_Z_extract.
    replace (8 * Z.of_N 0)%Z with 0%Z by lia.
    rewrite Z.pow_0_r, Z.div_1_r.
    replace (8 * Z.of_nat (N.to_nat (store_size_dtyp (DTYPE_Base (DTYPE_I sz)))))%Z
      with (Z.pos sz) by lia.
    rewrite <- Hm, Z.mod_small by lia.
    apply Integers.repr_unsigned.
  Qed.

  (** ** Integers whose width is not a whole number of bytes

      The writer zero-extends: the last byte holds the top [sz mod 8] bits of
      the value and zeros above them.  The reader takes
      [concat_bytes_Z_mixed], which weights each full byte by its position
      and keeps only the low [sz mod 8] bits of the last one. *)

  (* the last byte's real bits, read back *)
  Lemma memory_bits_to_Z_of_bits : forall zs,
      memory_bits_to_Z (List.map Z_to_memory_bit zs)
      = raise_ret (NoPois (concat_bits_Z (List.map (fun z => (z mod 2)%Z) zs))).
  Proof.
    assert (M : forall zs, map_monad memory_bit_to_bit (List.map Z_to_memory_bit zs)
                = raise_ret (NoPois (List.map (fun z => (z mod 2)%Z) zs))).
    { induction zs as [| z zs IH]; [reflexivity |].
      cbn [List.map].
      rewrite map_monad_cons_EOUP, IH.
      unfold Z_to_memory_bit, memory_bit_to_bit.
      cbn [unsigned repr VInt_Bounded].
      rewrite Integers.unsigned_repr_eq.
      replace (@Integers.modulus 1) with 2%Z by reflexivity.
      reflexivity. }
    intros zs; unfold memory_bits_to_Z; rewrite M; reflexivity.
  Qed.

  (* [concat_bytes_Z_mixed_cons2] needs two visible elements; here the tail is
     [map _ ys ++ [lastb]], which is a cons for either shape of [ys] *)
  Lemma concat_bytes_Z_mixed_cons_app : forall extra b ys lastb,
      concat_bytes_Z_mixed extra
        (b :: (List.map (fun z => @BYTE_I Pa 8 z) ys ++ [lastb]))
      = (z <- memory_byte_to_Z b ;;
         r <- concat_bytes_Z_mixed extra
                (List.map (fun z => @BYTE_I Pa 8 z) ys ++ [lastb]) ;;
         ret (z + Z.shiftl r 8)%Z).
  Proof. intros extra b [| y ys] lastb; destruct b; reflexivity. Qed.

  (* a run of plain bytes followed by the (truncated) last one.  [lastb] is
     typed as [List.map]'s output ([dvalue_bv 8]) rather than [memory_byte],
     so that [[lastb]] matches the goals syntactically. *)
  Lemma concat_bytes_Z_mixed_app_ret : forall extra ys (lastb : @dvalue_bv Pa 8) v,
      concat_bytes_Z_mixed extra [lastb] = raise_ret (NoPois v) ->
      concat_bytes_Z_mixed extra
        (List.map (fun y => @BYTE_I Pa 8 y) ys ++ [lastb])
      = raise_ret (NoPois (concat_bytes_Z (List.map Integers.unsigned ys)
                           + v * 2 ^ (8 * Z.of_nat (length ys)))%Z).
  Proof.
    intros extra ys lastb v Hv; induction ys as [| y ys IH].
    - cbn [List.map app length].
      rewrite Hv.
      cbn [concat_bytes_Z]; repeat f_equal; lia.
    - cbn [List.map app].
      rewrite concat_bytes_Z_mixed_cons_app, IH.
      cbn [memory_byte_to_Z concat_bytes_Z List.map Datatypes.length].
      cbn -[concat_bytes_Z List.map Z.pow Z.of_nat Integers.unsigned
            Datatypes.length Z.shiftl Z.mul Z.add].
      rewrite !Z.shiftl_mul_pow2 by lia.
      replace (8 * Z.of_nat (S (Datatypes.length ys)))%Z
         with (8 * Z.of_nat (Datatypes.length ys) + 8)%Z by lia.
      rewrite Z.pow_add_r by lia.
      do 2 f_equal; ring.
  Qed.
  (* the writer's generator: every byte, the last included, is plain *)
  Lemma gen_plain : forall sz (x : @bit_int sz) idx,
      memory_byte_of_dvalue_bv (BYTE_I x) idx
      = BYTE_I (repr (extract_byte_vint x idx)).
  Proof. reflexivity. Qed.

  Lemma read_int_block_mixed : forall sz (x : @bit_int sz),
      (Npos sz mod 8 <> 0)%N ->
      memory_bytes_to_dvalue_base
        (List.map (memory_byte_of_dvalue_bv (BYTE_I x))
                  (Nseq 0 (N.to_nat (store_size_dtyp (DTYPE_Base (DTYPE_I sz))))))
        (DTYPE_I sz)
      = ret (DVALUE_I sz x).
  Proof.
    intros sz x H8.
    destruct (@store_size_int_mixed _ _ sz H8) as [Hk1 Hk2].
    pose proof (Integers.unsigned_range x) as [Hlo Hhi].
    pose proof (N.mod_upper_bound (Npos sz) 8 ltac:(lia)) as Hub.
    assert (Hm : (@Integers.modulus sz = 2 ^ Z.pos sz)%Z)
      by (rewrite Integers.modulus_def; apply two_power_pos_eq).
    destruct (N.to_nat (store_size_dtyp (DTYPE_Base (DTYPE_I sz)))) as [| m] eqn:EK;
      [lia |].
    assert (HK : (store_size_dtyp (DTYPE_Base (DTYPE_I sz)) = N.of_nat (S m))%N)
      by (rewrite <- EK; symmetry; apply Nnat.N2Nat.id).
    assert (HK1 : (store_size_dtyp (DTYPE_Base (DTYPE_I sz)) - 1 = N.of_nat m)%N)
      by (rewrite HK, Nnat.Nat2N.inj_succ; lia).
    rewrite HK1 in Hk2.
    assert (Hmm : (8 * N.of_nat m + Npos sz mod 8 = Npos sz)%N) by exact Hk2.
    assert (He1 : (1 <= Npos sz mod 8)%N)
      by (revert H8; generalize (Npos sz mod 8)%N; intros e He; lia).
    (* every byte is a plain [BYTE_I] *)
    erewrite map_ext with
      (g := fun i => @BYTE_I Pa 8 (repr (extract_byte_vint x i)))
      by (intros i; apply gen_plain).
    rewrite Nseq_snoc, List.map_app.
    rewrite <- (map_map (fun i => repr (extract_byte_vint x i))
                        (fun z => @BYTE_I Pa 8 z)).
    cbn [List.map].
    (* the last byte contributes its low [sz mod 8] bits *)
    assert (HV : concat_bytes_Z_mixed (Npos sz mod 8)
                   [@BYTE_I Pa 8 (repr (extract_byte_vint x (0 + N.of_nat m)))]
                 = raise_ret (NoPois
                     ((Integers.unsigned x / 2 ^ (8 * Z.of_nat m))
                      mod 2 ^ Z.of_N (Npos sz mod 8))%Z)).
    { cbn [concat_bytes_Z_mixed ret EOUP_Monad EOU_monad]; do 2 f_equal.
      rewrite extract_byte_vint_spec_lt by lia.
      replace (Z.of_N (0 + N.of_nat m)) with (Z.of_nat m) by lia.
      cbn [repr unsigned VInt_Bounded].
      rewrite Integers.unsigned_repr_eq.
      replace (@Integers.modulus 8) with 256%Z by reflexivity.
      rewrite Z.mod_mod by lia.
      (* [2 ^ (sz mod 8)] divides 256 *)
      symmetry; apply Znumtheory.Zmod_div_mod;
        [apply Z.pow_pos_nonneg; lia | lia |].
      exists (2 ^ (8 - Z.of_N (Npos sz mod 8)))%Z.
      rewrite <- Z.pow_add_r by lia.
      replace (8 - Z.of_N (Npos sz mod 8) + Z.of_N (Npos sz mod 8))%Z with 8%Z by lia.
      reflexivity. }
    cbn [memory_bytes_to_dvalue_base].
    unfold memory_bytes_to_int.
    destruct (N.eqb_spec (Npos sz mod 8) 0); [lia |]; cbn [negb].
    rewrite (concat_bytes_Z_mixed_app_ret _ _ _ HV).
    cbn -[concat_bytes_Z List.map Z.pow Z.of_nat Integers.unsigned
          Datatypes.length Z.mul Z.add Nseq extract_byte_vint Integers.repr].
    do 2 f_equal.
    (* the leading bytes reassemble the low part *)
    rewrite map_map.
    erewrite map_ext_in with
      (g := fun i => ((Integers.unsigned x / 2 ^ (8 * Z.of_N i)) mod 256)%Z).
    2:{ intros i Hi; apply In_Nseq in Hi.
        cbn [repr unsigned VInt_Bounded].
        rewrite Integers.unsigned_repr_eq.
        rewrite extract_byte_vint_spec by lia.
        replace (@Integers.modulus 8) with 256%Z by reflexivity.
        rewrite Z.mod_mod by lia; reflexivity. }
    rewrite concat_bytes_Z_extract, length_map, Nseq_length.
    replace (8 * Z.of_N 0)%Z with 0%Z by lia.
    rewrite Z.pow_0_r, Z.div_1_r.
    (* combine low part and the top bits *)
    rewrite (Z.mul_comm ((Integers.unsigned x / 2 ^ (8 * Z.of_nat m))
                          mod 2 ^ Z.of_N (N.pos sz mod 8))%Z
                        (2 ^ (8 * Z.of_nat m))%Z).
    rewrite <- (Z.rem_mul_r (Integers.unsigned x) (2 ^ (8 * Z.of_nat m))
                            (2 ^ Z.of_N (Npos sz mod 8)))
      by (try (apply Z.pow_nonzero; lia); apply Z.pow_pos_nonneg; lia).
    rewrite <- Z.pow_add_r by lia.
    replace (8 * Z.of_nat m + Z.of_N (Npos sz mod 8))%Z with (Z.pos sz) by lia.
    rewrite <- Hm, Z.mod_small by lia.
    apply Integers.repr_unsigned.
  Qed.

  (** ** Floating point

      Both float types are fixed width and the writer captures every byte, so
      the round trip is [concat_bytes_Z_extract] plus [concat_bytes_vint_Z] to
      cross from the reader's [vint]-level fold, then [of_to_bits]. *)

  Lemma read_base_block_double : forall d,
      memory_bytes_to_dvalue_base
        (List.map (base_byte_gen (DVALUE_Double d))
           (Nseq 0 (N.to_nat (store_size_dtyp (DTYPE_Base (DTYPE_FP FP_double))))))
        (DTYPE_FP FP_double)
      = ret (DVALUE_Double d).
  Proof.
    intros d.
    pose proof (Integers.unsigned_range (Float.to_bits d)) as [Hlo Hhi].
    assert (Hm : (@Integers.modulus 64 = 2 ^ 64)%Z) by reflexivity.
    cbn [base_byte_gen].
    rewrite store_size_dtyp_double.
    cbn [memory_bytes_to_dvalue_base].
    match goal with
    | |- context [map_monad memory_byte_to_Z ?L] =>
        replace (map_monad memory_byte_to_Z L)
          with (raise_ret (NoPois (List.map
                  (fun i => @Integers.unsigned 8
                     (repr (extract_byte_Z (unsigned (Float.to_bits d)) i)))
                  (Nseq 0 (N.to_nat 8)))))
          by (symmetry; apply map_monad_byte_to_Z_BYTE_I)
    end.
    cbn -[concat_bytes_Z_vint List.map Nseq Integers.unsigned Z.pow Z.of_nat
          Integers.repr extract_byte_Z].
    do 2 f_equal.
    unfold concat_bytes_Z_vint.
    cbn [repr VInt_Bounded].
    rewrite concat_bytes_vint_Z by (rewrite Hm; lia).
    erewrite map_ext with
      (g := fun i => ((Integers.unsigned (Float.to_bits d) / 2 ^ (8 * Z.of_N i))
                      mod 256)%Z).
    2:{ intros i; cbn [repr unsigned VInt_Bounded].
        rewrite Integers.unsigned_repr_eq.
        replace (@Integers.modulus 8) with 256%Z by reflexivity.
        rewrite extract_byte_Z_spec, Z.mod_mod by lia; reflexivity. }
    rewrite concat_bytes_Z_extract.
    replace (8 * Z.of_N 0)%Z with 0%Z by lia.
    rewrite Z.pow_0_r, Z.div_1_r.
    match goal with
    | |- context [(2 ^ ?E)%Z] => replace (2 ^ E)%Z with (2 ^ 64)%Z by (f_equal; lia)
    end.
    rewrite <- Hm, Z.mod_small by lia.
    rewrite Integers.repr_unsigned.
    apply Float.of_to_bits.
  Qed.
  Lemma read_base_block_float : forall d,
      memory_bytes_to_dvalue_base
        (List.map (base_byte_gen (DVALUE_Float d))
           (Nseq 0 (N.to_nat (store_size_dtyp (DTYPE_Base (DTYPE_FP FP_float))))))
        (DTYPE_FP FP_float)
      = ret (DVALUE_Float d).
  Proof.
    intros d.
    pose proof (Integers.unsigned_range (Float32.to_bits d)) as [Hlo Hhi].
    assert (Hm : (@Integers.modulus 32 = 2 ^ 32)%Z) by reflexivity.
    cbn [base_byte_gen].
    rewrite store_size_dtyp_float.
    cbn [memory_bytes_to_dvalue_base].
    match goal with
    | |- context [map_monad memory_byte_to_Z ?L] =>
        replace (map_monad memory_byte_to_Z L)
          with (raise_ret (NoPois (List.map
                  (fun i => @Integers.unsigned 8
                     (repr (extract_byte_Z (unsigned (Float32.to_bits d)) i)))
                  (Nseq 0 (N.to_nat 4)))))
          by (symmetry; apply map_monad_byte_to_Z_BYTE_I)
    end.
    cbn -[concat_bytes_Z_vint List.map Nseq Integers.unsigned Z.pow Z.of_nat
          Integers.repr extract_byte_Z].
    do 2 f_equal.
    unfold concat_bytes_Z_vint.
    cbn [repr VInt_Bounded].
    rewrite concat_bytes_vint_Z by (rewrite Hm; lia).
    erewrite map_ext with
      (g := fun i => ((Integers.unsigned (Float32.to_bits d) / 2 ^ (8 * Z.of_N i))
                      mod 256)%Z).
    2:{ intros i; cbn [repr unsigned VInt_Bounded].
        rewrite Integers.unsigned_repr_eq.
        replace (@Integers.modulus 8) with 256%Z by reflexivity.
        rewrite extract_byte_Z_spec, Z.mod_mod by lia; reflexivity. }
    rewrite concat_bytes_Z_extract.
    replace (8 * Z.of_N 0)%Z with 0%Z by lia.
    rewrite Z.pow_0_r, Z.div_1_r.
    match goal with
    | |- context [(2 ^ ?E)%Z] => replace (2 ^ E)%Z with (2 ^ 32)%Z by (f_equal; lia)
    end.
    rewrite <- Hm, Z.mod_small by lia.
    rewrite Integers.repr_unsigned.
    apply Float32.of_to_bits.
  Qed.

  (** ** Byte-vector values

      [DTYPE_B] reads through [memory_bytes_to_byte_value], which prefers a
      pointer slice, then an integer, then a raw bit list -- so each
      constructor of a canonical [dvalue_bv] has to be shown to come back down
      the branch it came from. *)

  Lemma memory_bytes_to_int_of_read : forall sz (x : @bit_int sz) dbs,
      memory_bytes_to_dvalue_base dbs (DTYPE_I sz) = ret (DVALUE_I sz x) ->
      exists v, memory_bytes_to_int sz dbs = raise_ret (NoPois v) /\ repr v = x.
  Proof.
    intros sz x dbs H; cbn [memory_bytes_to_dvalue_base] in H.
    unfold absorb_pois, catch_pois in H.
    destruct (memory_bytes_to_int sz dbs) as [ | | | [ v | ] ] eqn:E;
      cbn in H; try discriminate.
    exists v; split; [reflexivity |]. inversion H; reflexivity.
  Qed.

  Lemma pointer_slice_from_run : forall p n i,
      pointer_slice_from p i (List.map (fun j => @BYTE_Pointer Pa 8 p j) (Nseq i n))
      = true.
  Proof.
    intros p; induction n as [| n IH]; intros i; cbn [Nseq List.map pointer_slice_from];
      [reflexivity |].
    unfold pointer_byte_at, valid_pointer_byte.
    destruct (eq_dec_ptr p p) as [_ | NE]; [| now contradiction NE].
    rewrite N.eqb_refl; cbn [andb].
    replace (N.succ i) with (1 + i)%N by lia.
    apply IH.
  Qed.

  Lemma BYTE_I_byte0 : forall sz (x : @bit_int sz),
      memory_byte_of_dvalue_bv (BYTE_I x) 0
      = BYTE_I (repr (extract_byte_vint x 0))
      \/ exists b bs, memory_byte_of_dvalue_bv (BYTE_I x) 0
                      = @BYTE_Mixed Pa 8 (Bit_bit b :: bs).
  Proof.
    intros sz x; now left.
  Qed.

  Lemma all_poison_BYTE_I_block : forall sz (x : @bit_int sz) K,
      (0 < K)%nat ->
      all_poison_bytes
        (List.map (memory_byte_of_dvalue_bv (BYTE_I x)) (Nseq 0 K)) = false.
  Proof.
    intros sz x [| K] H; [lia |].
    cbn [Nseq List.map]; unfold all_poison_bytes; cbn [poison_split].
    destruct (BYTE_I_byte0 x) as [E | (b & bs & E)]; rewrite E;
      cbn [is_all_poison_byte all_poison_bits forallb is_poison_bit]; reflexivity.
  Qed.

  Lemma pointer_slice_BYTE_I_block : forall sz (x : @bit_int sz) K,
      (0 < K)%nat ->
      memory_bytes_to_pointer_slice
        (List.map (memory_byte_of_dvalue_bv (BYTE_I x)) (Nseq 0 K)) = None.
  Proof.
    intros sz x [| K] H; [lia |].
    cbn [Nseq List.map]; unfold memory_bytes_to_pointer_slice.
    destruct (BYTE_I_byte0 x) as [E | (b & bs & E)]; rewrite E; reflexivity.
  Qed.

  (** The reader takes the [BYTE_I] branch only when no extracted bit is a
      pointer bit.  Every bit [get_bits_of_memory_byte_list] returns comes
      from its accumulator, from one of the bytes, or is poison padding. *)
  Lemma In_get_bits : forall dbs n acc b,
      In b (get_bits_of_memory_byte_list n dbs acc) ->
      In b acc \/ b = Bit_psn \/
        exists d, In d dbs /\ In b (memory_byte_to_memory_bits d).
  Proof.
    induction dbs as [| d dbs IH]; intros n acc b H;
      cbn [get_bits_of_memory_byte_list] in H.
    - destruct (N.eqb n 0); [now left |].
      apply In_rev_loop_acc in H as [H | (j & ->)]; [now left | now (right; left)].
    - destruct (N.ltb n 8).
      + rewrite rev_append_rev in H; apply in_app_or in H as [H | H]; [| now left].
        apply in_rev in H.
        right; right; exists d; split; [now left |].
        rewrite <- (@take_drop_app _ n (memory_byte_to_memory_bits d)).
        apply in_or_app; now left.
      + apply IH in H as [H | [H | (d' & Hd' & H)]].
        * rewrite rev_append_rev in H; apply in_app_or in H as [H | H]; [| now left].
          apply in_rev in H; right; right; exists d; split; [now left | exact H].
        * now (right; left).
        * right; right; exists d'; split; [now right | exact H].
  Qed.

  (* With enough bytes there is no poison padding: every bit comes from the
     accumulator or from a byte. *)
  Lemma In_get_bits_full : forall dbs n acc b,
      (n <= 8 * N.of_nat (List.length dbs))%N ->
      In b (get_bits_of_memory_byte_list n dbs acc) ->
      In b acc \/ exists d, In d dbs /\ In b (memory_byte_to_memory_bits d).
  Proof.
    induction dbs as [| d dbs IH]; intros n acc b Hn H;
      cbn [get_bits_of_memory_byte_list] in H.
    - cbn [List.length] in Hn.
      destruct (N.eqb_spec n 0); [now left | lia].
    - destruct (N.ltb n 8).
      + rewrite rev_append_rev in H; apply in_app_or in H as [H | H]; [| now left].
        apply in_rev in H.
        right; exists d; split; [now left |].
        rewrite <- (@take_drop_app _ n (memory_byte_to_memory_bits d)).
        apply in_or_app; now left.
      + apply IH in H as [H | (d' & Hd' & H)].
        * rewrite rev_append_rev in H; apply in_app_or in H as [H | H]; [| now left].
          apply in_rev in H; right; exists d; split; [now left | exact H].
        * right; exists d'; split; [now right | exact H].
        * cbn [List.length] in Hn; lia.
  Qed.

  Lemma BYTE_I_byte_no_ptr : forall sz (x : @bit_int sz) idx b,
      In b (memory_byte_to_memory_bits (memory_byte_of_dvalue_bv (BYTE_I x) idx)) ->
      is_ptr_bit b = false.
  Proof.
    intros sz x idx b H;
      cbn [memory_byte_of_dvalue_bv memory_byte_to_memory_bits] in H.
    rewrite rev_append_rev, app_nil_r in H; apply in_rev in H.
    apply In_rev_loop_acc in H as [[] | (j & ->)]; reflexivity.
  Qed.

  Lemma no_ptr_bits_BYTE_I_block : forall sz (x : @bit_int sz) K,
      existsb is_ptr_bit
        (rev_append (get_bits_of_memory_byte_list (Npos sz)
           (List.map (memory_byte_of_dvalue_bv (BYTE_I x)) (Nseq 0 K)) []) [])
      = false.
  Proof.
    intros sz x K.
    apply not_true_iff_false; intros H.
    apply existsb_exists in H as (b & Hin & Hb).
    rewrite rev_append_rev, app_nil_r in Hin; apply in_rev in Hin.
    apply In_get_bits in Hin as [[] | [-> | (d & Hd & Hin)]]; [discriminate |].
    apply in_map_iff in Hd as (idx & <- & _).
    rewrite (BYTE_I_byte_no_ptr Hin) in Hb; discriminate.
  Qed.

  Lemma BYTE_I_byte_no_psn : forall sz (x : @bit_int sz) idx b,
      In b (memory_byte_to_memory_bits (memory_byte_of_dvalue_bv (BYTE_I x) idx)) ->
      is_poison_bit b = false.
  Proof.
    intros sz x idx b H;
      cbn [memory_byte_of_dvalue_bv memory_byte_to_memory_bits] in H.
    rewrite rev_append_rev, app_nil_r in H; apply in_rev in H.
    apply In_rev_loop_acc in H as [[] | (j & ->)]; reflexivity.
  Qed.

  (* the writer lays down enough bytes that none of the bits is padding *)
  Lemma no_psn_bits_BYTE_I_block : forall sz (x : @bit_int sz) K,
      (Npos sz <= 8 * N.of_nat K)%N ->
      existsb is_poison_bit
        (rev_append (get_bits_of_memory_byte_list (Npos sz)
           (List.map (memory_byte_of_dvalue_bv (BYTE_I x)) (Nseq 0 K)) []) [])
      = false.
  Proof.
    intros sz x K HK.
    apply not_true_iff_false; intros H.
    apply existsb_exists in H as (b & Hin & Hb).
    rewrite rev_append_rev, app_nil_r in Hin; apply in_rev in Hin.
    apply In_get_bits_full in Hin as [[] | (d & Hd & Hin)];
      [| rewrite length_map, Nseq_length; exact HK].
    apply in_map_iff in Hd as (idx & <- & _).
    rewrite (BYTE_I_byte_no_psn Hin) in Hb; discriminate.
  Qed.

  (* a canonical [BYTE_Mixed] with no pointer bits must contain poison *)
  Lemma not_all_int_no_ptr_pois : forall bits,
      negb (forallb is_int_bit bits) = true ->
      existsb is_ptr_bit bits = false ->
      existsb is_poison_bit bits = true.
  Proof.
    induction bits as [| b bits IH]; intros H1 H2; cbn in *; [discriminate |].
    destruct b; cbn in *; [discriminate | reflexivity | auto].
  Qed.

  Lemma read_base_block_BYTE_I : forall sz (x : @bit_int sz),
      memory_bytes_to_dvalue_base
        (List.map (memory_byte_of_dvalue_bv (BYTE_I x))
                  (Nseq 0 (N.to_nat (store_size_dtyp (DTYPE_Base (DTYPE_B sz))))))
        (DTYPE_B sz)
      = ret (@DVALUE_B Pa sz (BYTE_I x)).
  Proof.
    intros sz x.
    rewrite store_size_B_I.
    assert (HK : (0 < N.to_nat (store_size_dtyp (DTYPE_Base (DTYPE_I sz))))%nat).
    { pose proof (serializable_base_pos (DTYPE_I sz) I); lia. }
    assert (HR : memory_bytes_to_dvalue_base
                   (List.map (memory_byte_of_dvalue_bv (BYTE_I x))
                      (Nseq 0 (N.to_nat (store_size_dtyp (DTYPE_Base (DTYPE_I sz))))))
                   (DTYPE_I sz) = ret (DVALUE_I sz x)).
    { destruct (N.eqb_spec (Npos sz mod 8) 0) as [E8 | E8];
        [apply read_int_block_mult8 | apply read_int_block_mixed]; exact E8. }
    destruct (memory_bytes_to_int_of_read _ HR) as [v [Ev Hv]].
    cbn [memory_bytes_to_dvalue_base].
    rewrite all_poison_BYTE_I_block by exact HK.
    unfold memory_bytes_to_byte_value.
    rewrite pointer_slice_BYTE_I_block by exact HK.
    unfold memory_bytes_to_bits_value; cbv zeta.
    rewrite no_ptr_bits_BYTE_I_block, no_psn_bits_BYTE_I_block
      by apply store_size_int_bits.
    cbn [orb]; rewrite Ev.
    rewrite Hv; cbn; reflexivity.
  Qed.


  Lemma all_poison_pointer_run : forall p i n,
      all_poison_bytes
        (List.map (fun j => @BYTE_Pointer Pa 8 p j) (Nseq i (S n))) = false.
  Proof.
    intros p i n; cbn [Nseq List.map].
    unfold all_poison_bytes; cbn [poison_split is_all_poison_byte]; reflexivity.
  Qed.

  Lemma memory_bytes_to_pointer_slice_run : forall p i n,
      memory_bytes_to_pointer_slice
        (List.map (fun j => @BYTE_Pointer Pa 8 p j) (Nseq i (S n))) = Some (p, i).
  Proof.
    intros p i n.
    pose proof (pointer_slice_from_run p (S n) i) as HR.
    cbn [Nseq List.map] in *.
    unfold memory_bytes_to_pointer_slice.
    rewrite HR; reflexivity.
  Qed.

  Lemma read_base_block_BYTE_Pointer : forall sz p k,
      (Npos sz mod 8 = 0)%N ->
      memory_bytes_to_dvalue_base
        (List.map (memory_byte_of_dvalue_bv (@BYTE_Pointer Pa sz p k))
                  (Nseq 0 (N.to_nat (store_size_dtyp (DTYPE_Base (DTYPE_B sz))))))
        (DTYPE_B sz)
      = ret (@DVALUE_B Pa sz (BYTE_Pointer sz p k)).
  Proof.
    intros sz p k H8.
    pose proof (serializable_base_pos (DTYPE_B sz) I) as HKpos.
    remember (N.to_nat (store_size_dtyp (DTYPE_Base (DTYPE_B sz)))) as K eqn:EK.
    destruct K as [| K']; [lia |].
    erewrite map_ext with
      (g := fun idx => @BYTE_Pointer Pa 8 p ((Npos sz * k / 8) + idx)%N)
      by (intros idx; reflexivity).
    rewrite (map_Nseq_shift (fun j => @BYTE_Pointer Pa 8 p j) (S K') 0
                            (Npos sz * k / 8)%N).
    rewrite N.add_0_r.
    remember (Npos sz / 8)%N as q eqn:Eq.
    assert (Hq : (Npos sz = 8 * q)%N)
      by (subst q; apply N.Div0.div_exact; exact H8).
    assert (Hqnz : (q <> 0)%N) by lia.
    assert (Harith : ((Npos sz * k / 8) * 8 / Npos sz = k)%N).
    { rewrite Hq.
      replace (8 * q * k)%N with (q * k * 8)%N by lia.
      rewrite N.div_mul by lia.
      replace (q * k * 8)%N with (k * (8 * q))%N by lia.
      rewrite N.div_mul by lia.
      reflexivity. }
    (* the writer's chunk starts on a chunk boundary *)
    assert (Hal : pointer_chunk_aligned sz (Npos sz * k / 8) = true).
    { unfold pointer_chunk_aligned; rewrite H8, N.eqb_refl; cbn [andb].
      apply N.eqb_eq; rewrite Hq.
      replace (8 * q * k)%N with (q * k * 8)%N by lia.
      rewrite N.div_mul by lia.
      replace (q * k * 8)%N with (k * (8 * q))%N by lia.
      apply N.Div0.mod_mul. }
    cbn [memory_bytes_to_dvalue_base].
    rewrite all_poison_pointer_run.
    unfold memory_bytes_to_byte_value.
    rewrite memory_bytes_to_pointer_slice_run.
    cbv beta iota.
    rewrite Hal, Harith; cbn; reflexivity.
  Qed.

  (** The reader's [get_bits_of_memory_byte_list] inverts the writer's
      per-byte [take 8 (drop (8*idx) _)] splitting: it recovers exactly the
      original bit list. *)

  Definition mixed_byte (bits : list memory_bit) (idx : N) : memory_byte :=
    let m := take 8 (drop (8 * idx) bits) in
    @BYTE_Mixed Pa 8
      (m ++ (if negb (N.of_nat (List.length m) =? 8)%N then
               repeat Bit_psn (8 - List.length m) else [])).

  Lemma writer_mixed_byte : forall sz bits idx,
      memory_byte_of_dvalue_bv (@BYTE_Mixed Pa sz bits) idx = mixed_byte bits idx.
  Proof. reflexivity. Qed.

  Lemma mixed_byte_shift : forall bits j,
      mixed_byte bits (1 + j) = mixed_byte (drop 8 bits) j.
  Proof.
    intros bits j; unfold mixed_byte.
    replace (8 * (1 + j))%N with (8 + 8 * j)%N by lia.
    rewrite <- (drop_drop (8 * j)%N 8 bits); reflexivity.
  Qed.

  Lemma memory_byte_to_memory_bits_mixed : forall bits idx,
      memory_byte_to_memory_bits (mixed_byte bits idx)
      = (let m := take 8 (drop (8 * idx) bits) in
         m ++ (if negb (N.of_nat (List.length m) =? 8)%N then
                 repeat Bit_psn (8 - List.length m) else [])).
  Proof. reflexivity. Qed.

  Lemma get_bits_writer : forall n bits acc,
      (N.of_nat (List.length bits) <= 8 * N.of_nat n)%N ->
      get_bits_of_memory_byte_list (N.of_nat (List.length bits))
        (List.map (mixed_byte bits) (Nseq 0 n)) acc
      = rev_append bits acc.
  Proof.
    induction n as [| n IH]; intros bits acc Hlen.
    - cbn [Nseq List.map get_bits_of_memory_byte_list].
      destruct bits; [reflexivity | cbn in Hlen; lia].
    - cbn [Nseq List.map get_bits_of_memory_byte_list].
      rewrite !memory_byte_to_memory_bits_mixed; cbv beta zeta.
      rewrite N.mul_0_r, drop_nil.
      destruct (N.ltb_spec (N.of_nat (List.length bits)) 8) as [Hlt | Hge].
      + (* the only byte: take just the real bits *)
        rewrite (@take_all _ bits 8) by lia.
        replace (if negb (N.of_nat (List.length bits) =? 8)%N then
                   repeat Bit_psn (8 - List.length bits) else [])
          with (repeat (@Bit_psn Pa) (8 - List.length bits))
          by (destruct (N.eqb_spec (N.of_nat (List.length bits)) 8); [lia | reflexivity]).
        rewrite take_app_exact by reflexivity; reflexivity.
      + (* a full byte: recurse on the rest *)
        assert (H8 : N.of_nat (List.length (take 8 bits)) = 8%N)
          by (apply take_length_exact; lia).
        rewrite H8; cbn [negb N.eqb]; rewrite app_nil_r.
        replace (N.succ 0)%N with (1 + 0)%N by lia.
        rewrite <- (map_Nseq_shift (mixed_byte bits) n 0 1).
        erewrite map_ext by (intros j; apply mixed_byte_shift).
        replace (N.of_nat (List.length bits) - 8)%N
          with (N.of_nat (List.length (drop 8 bits)))
          by (rewrite length_drop_N; lia).
        rewrite IH by (rewrite length_drop_N; lia).
        rewrite <- (@take_drop_app _ 8 bits) at 3.
        rewrite rev_append_rev, rev_append_rev, rev_append_rev, rev_app_distr.
        rewrite <- app_assoc; reflexivity.
  Qed.
  (** Bridges from a property of the bit list to the corresponding property of
      the bytes the writer lays down. *)

  Lemma all_poison_bytes_forallb : forall l,
      all_poison_bytes l = forallb is_all_poison_byte l.
  Proof.
    induction l as [| b l IH]; [reflexivity |].
    unfold all_poison_bytes in *; cbn [poison_split forallb].
    destruct (is_all_poison_byte b); cbn [andb].
    - destruct (poison_split l) as [k tl]; cbn in *; exact IH.
    - reflexivity.
  Qed.

  (* if every byte of the block is all-poison then so is every bit *)
  Lemma mixed_all_poison : forall n bits,
      (N.of_nat (List.length bits) <= 8 * N.of_nat n)%N ->
      forallb is_all_poison_byte (List.map (mixed_byte bits) (Nseq 0 n)) = true ->
      forallb is_poison_bit bits = true.
  Proof.
    induction n as [| n IH]; intros bits Hlen H.
    - destruct bits; [reflexivity | cbn in Hlen; lia].
    - cbn [Nseq List.map forallb] in H.
      apply andb_true_iff in H as [H0 Hrest].
      unfold mixed_byte, is_all_poison_byte, all_poison_bits in H0.
      rewrite N.mul_0_r, drop_nil in H0.
      rewrite forallb_app in H0; apply andb_true_iff in H0 as [Htake _].
      replace (N.succ 0)%N with (1 + 0)%N in Hrest by lia.
      rewrite <- (map_Nseq_shift (mixed_byte bits) n 0 1) in Hrest.
      erewrite map_ext in Hrest by (intros j; apply mixed_byte_shift).
      specialize (IH (drop 8 bits) ltac:(rewrite length_drop_N; lia) Hrest).
      rewrite <- (@take_drop_app _ 8 bits), forallb_app, Htake, IH; reflexivity.
  Qed.

  Lemma map_monad_bit_pois : forall l,
      existsb is_poison_bit l = true ->
      map_monad memory_bit_to_bit l = raise_ret (@Pois (list Z)).
  Proof.
    induction l as [| b l IH]; [discriminate |].
    cbn [existsb]; intros H.
    rewrite map_monad_cons_EOUP.
    destruct b; cbn [is_poison_bit] in H; cbn [memory_bit_to_bit].
    - rewrite IH by exact H; reflexivity.
    - reflexivity.
    - rewrite IH by exact H; reflexivity.
  Qed.

  Lemma memory_bits_to_Z_pois : forall l,
      existsb is_poison_bit l = true -> memory_bits_to_Z l = raise_ret (@Pois Z).
  Proof.
    intros l H; unfold memory_bits_to_Z.
    rewrite map_monad_bit_pois by exact H; reflexivity.
  Qed.

  Lemma memory_byte_to_Z_mixed_pois : forall bits idx,
      existsb is_poison_bit (take 8 (drop (8 * idx) bits)) = true ->
      memory_byte_to_Z (mixed_byte bits idx) = raise_ret (@Pois Z).
  Proof.
    intros bits idx H.
    unfold mixed_byte; cbn [memory_byte_to_Z].
    apply memory_bits_to_Z_pois.
    rewrite existsb_app, H; reflexivity.
  Qed.

  Lemma map_monad_bit_ret : forall l,
      exists r, map_monad memory_bit_to_bit l = raise_ret r.
  Proof.
    induction l as [| b l [r IH]]; [eexists; reflexivity |].
    rewrite map_monad_cons_EOUP, IH.
    destruct b; cbn [memory_bit_to_bit]; destruct r; eexists; reflexivity.
  Qed.

  Lemma memory_byte_to_Z_mixed_ret : forall bits idx,
      exists r, memory_byte_to_Z (mixed_byte bits idx) = raise_ret r.
  Proof.
    intros bits idx; unfold mixed_byte; cbn [memory_byte_to_Z].
    unfold memory_bits_to_Z.
    destruct (map_monad_bit_ret
                (take 8 (drop (8 * idx) bits) ++
                 (if negb (N.of_nat (List.length (take 8 (drop (8 * idx) bits))) =? 8)%N
                  then repeat Bit_psn (8 - List.length (take 8 (drop (8 * idx) bits)))
                  else []))) as [r Er].
    rewrite Er; destruct r; eexists; reflexivity.
  Qed.

  (* the whole-byte read poisons as soon as any bit does *)
  Lemma map_monad_byte_mixed_pois : forall n bits,
      (N.of_nat (List.length bits) <= 8 * N.of_nat n)%N ->
      existsb is_poison_bit bits = true ->
      map_monad memory_byte_to_Z (List.map (mixed_byte bits) (Nseq 0 n))
      = raise_ret (@Pois (list Z)).
  Proof.
    induction n as [| n IH]; intros bits Hlen H.
    - destruct bits; [discriminate | cbn in Hlen; lia].
    - cbn [Nseq List.map].
      rewrite map_monad_cons_EOUP.
      rewrite <- (@take_drop_app _ 8 bits), existsb_app in H.
      apply orb_true_iff in H as [Hhd | Htl].
      + rewrite memory_byte_to_Z_mixed_pois; [reflexivity |].
        rewrite N.mul_0_r, drop_nil; exact Hhd.
      + replace (N.succ 0)%N with (1 + 0)%N by lia.
        rewrite <- (map_Nseq_shift (mixed_byte bits) n 0 1).
        erewrite map_ext by (intros j; apply mixed_byte_shift).
        rewrite IH by (first [rewrite length_drop_N; lia | exact Htl]).
        destruct (memory_byte_to_Z_mixed_ret bits 0) as [r Er].
        rewrite Er; destruct r; reflexivity.
  Qed.

  Lemma cbmix_cons : forall extra b f a n,
      concat_bytes_Z_mixed extra (b :: List.map f (Nseq a (S n)))
      = (z <- memory_byte_to_Z b ;;
         r <- concat_bytes_Z_mixed extra (List.map f (Nseq a (S n))) ;;
         ret (z + Z.shiftl r 8)%Z).
  Proof.
    intros extra b f a n; cbn [Nseq List.map]; apply concat_bytes_Z_mixed_cons2.
  Qed.

  Lemma concat_bytes_Z_mixed_mixed_pois : forall n extra bits,
      (0 < extra <= 8)%N ->
      (N.of_nat (List.length bits) = 8 * N.of_nat n + extra)%N ->
      existsb is_poison_bit bits = true ->
      concat_bytes_Z_mixed extra (List.map (mixed_byte bits) (Nseq 0 (S n)))
      = raise_ret (@Pois Z).
  Proof.
    induction n as [| n IH]; intros extra bits Hx Hlen H.
    - (* a single, partial byte *)
      cbn [Nseq List.map concat_bytes_Z_mixed].
      unfold mixed_byte; cbn [memory_byte_to_memory_bits].
      rewrite N.mul_0_r, drop_nil, (@take_all _ bits 8) by lia.
      rewrite take_app_exact by lia.
      apply memory_bits_to_Z_pois; exact H.
    - (* at least one full byte first *)
      rewrite <- (@take_drop_app _ 8 bits), existsb_app in H.
      apply orb_true_iff in H as [Hhd | Htl].
      + change (List.map (mixed_byte bits) (Nseq 0 (S (S n))))
          with (mixed_byte bits 0
                :: List.map (mixed_byte bits) (Nseq (N.succ 0) (S n))).
        rewrite cbmix_cons.
        rewrite memory_byte_to_Z_mixed_pois; [reflexivity |].
        rewrite N.mul_0_r, drop_nil; exact Hhd.
      + assert (Hshift : List.map (mixed_byte bits) (Nseq (N.succ 0) (S n))
                         = List.map (mixed_byte (drop 8 bits)) (Nseq 0 (S n))).
        { replace (N.succ 0)%N with (1 + 0)%N by lia.
          rewrite <- (map_Nseq_shift (mixed_byte bits) (S n) 0 1).
          apply map_ext; intros j; apply mixed_byte_shift. }
        change (List.map (mixed_byte bits) (Nseq 0 (S (S n))))
          with (mixed_byte bits 0
                :: List.map (mixed_byte bits) (Nseq (N.succ 0) (S n))).
        rewrite Hshift, cbmix_cons.
        rewrite IH by (first [lia | rewrite length_drop_N; lia | exact Htl]).
        destruct (memory_byte_to_Z_mixed_ret bits 0) as [r Er].
        rewrite Er; destruct r; reflexivity.
  Qed.

  (** Relating the bit-level pointer-run test [all_pointer_bits_from] that
      [dvalue_bv_canonical] uses to the byte-level [pointer_slice_from] the
      reader runs. *)

  Lemma all_pointer_bits_from_app : forall l1 p j l2,
      all_pointer_bits_from p j (l1 ++ l2)
      = all_pointer_bits_from p j l1
        && all_pointer_bits_from p (j + N.of_nat (List.length l1))%N l2.
  Proof.
    induction l1 as [| b l1 IH]; intros p j l2; cbn [app all_pointer_bits_from
                                                     Datatypes.length].
    - rewrite N.add_0_r; reflexivity.
    - destruct b; cbn [andb]; [| reflexivity | reflexivity].
      destruct (eq_dec_ptr p p0); cbn [andb]; [| reflexivity].
      destruct (N.eqb_spec idx j); cbn [andb]; [| reflexivity].
      rewrite IH.
      replace (1 + j + N.of_nat (List.length l1))%N
        with (j + N.of_nat (S (List.length l1)))%N by lia.
      reflexivity.
  Qed.

  Lemma all_pointer_bits_from_repeat_psn : forall m p j,
      all_pointer_bits_from p j (repeat (@Bit_psn Pa) m) = true -> m = 0%nat.
  Proof. intros [| m] p j H; [reflexivity | cbn in H; discriminate]. Qed.

  Lemma valid_pointer_bits_implies : forall l p base offset,
      valid_pointer_bits p base offset l = raise_ret (NoPois true) ->
      all_pointer_bits_from p (base + offset)%N l = true.
  Proof.
    induction l as [| b l IH]; intros p base offset H; [reflexivity |].
    cbn [valid_pointer_bits] in H; cbn [all_pointer_bits_from].
    destruct b; [| discriminate | discriminate].
    destruct (eq_dec_ptr p p0) as [Ep | ]; [| discriminate].
    destruct (N.eqb_spec idx (base + offset)) as [Eidx | ]; [| discriminate].
    cbn [andb].
    replace (1 + (base + offset))%N with (base + (1 + offset))%N by lia.
    apply IH; exact H.
  Qed.
  Lemma pointer_slice_implies_bits : forall n bits p k,
      (N.of_nat (List.length bits) <= 8 * N.of_nat n)%N ->
      pointer_slice_from p k (List.map (mixed_byte bits) (Nseq 0 n)) = true ->
      all_pointer_bits_from p (8 * k)%N bits = true.
  Proof.
    induction n as [| n IH]; intros bits p k Hlen H.
    - destruct bits; [reflexivity | cbn in Hlen; lia].
    - cbn [Nseq List.map pointer_slice_from] in H.
      apply andb_true_iff in H as [Hhd Htl].
      (* the head byte is eight consecutive pointer bits, so no padding *)
      unfold pointer_byte_at, valid_pointer_byte, mixed_byte in Hhd.
      rewrite N.mul_0_r, drop_nil in Hhd.
      destruct (valid_pointer_bits p (k * 8) 0
                  (take 8 bits ++ _)) as [ | | | [ b | ] ] eqn:Ev in Hhd;
        try discriminate.
      subst b.
      apply valid_pointer_bits_implies in Ev.
      rewrite N.add_0_r, all_pointer_bits_from_app in Ev.
      apply andb_true_iff in Ev as [Etake Epad].
      assert (Hfull : N.of_nat (List.length (take 8 bits)) = 8%N).
      { destruct (N.eqb_spec (N.of_nat (List.length (take 8 bits))) 8) as [E | E];
          [exact E |].
        cbn [negb] in Epad.
        apply all_pointer_bits_from_repeat_psn in Epad.
        pose proof (take_length_le bits 8); lia. }
      (* recurse on the remaining bits *)
      replace (N.succ 0)%N with (1 + 0)%N in Htl by lia.
      rewrite <- (map_Nseq_shift (mixed_byte bits) n 0 1) in Htl.
      erewrite map_ext in Htl by (intros j; apply mixed_byte_shift).
      specialize (IH (drop 8 bits) p (1 + k)%N
                    ltac:(rewrite length_drop_N; lia) Htl).
      rewrite <- (@take_drop_app _ 8 bits), all_pointer_bits_from_app.
      replace (8 * k)%N with (k * 8)%N by lia.
      rewrite Etake, Hfull; cbn [andb].
      replace (k * 8 + 8)%N with (8 * (1 + k))%N by lia.
      rewrite IH; reflexivity.
  Qed.

  Lemma mixed_block_head : forall bits n,
      List.map (mixed_byte bits) (Nseq 0 (S n))
      = mixed_byte bits 0 :: List.map (mixed_byte bits) (Nseq (N.succ 0) n).
  Proof. reflexivity. Qed.

  Lemma mixed_byte_0 : forall bits,
      mixed_byte bits 0
      = @BYTE_Mixed Pa 8 (take 8 bits ++
          (if negb (N.of_nat (List.length (take 8 bits)) =? 8)%N
           then repeat Bit_psn (8 - List.length (take 8 bits)) else [])).
  Proof. intros bits; unfold mixed_byte; rewrite N.mul_0_r, drop_nil; reflexivity. Qed.


  Lemma pointer_slice_head : forall bits n,
      match bits with
      | Bit_ptr q j :: _ =>
          memory_bytes_to_pointer_slice (List.map (mixed_byte bits) (Nseq 0 (S n)))
          = (if pointer_slice_from q (j / 8)%N
                  (List.map (mixed_byte bits) (Nseq 0 (S n)))
             then Some (q, (j / 8)%N) else None)
      | _ =>
          memory_bytes_to_pointer_slice (List.map (mixed_byte bits) (Nseq 0 (S n)))
          = None
      end.
  Proof. intros [| [q j | | ] bits'] n; reflexivity. Qed.
  (* A pointer slice in the writer's rendering of a canonical [BYTE_Mixed]
     is not a whole aligned chunk -- else [is_pointer_chunk] would hold. *)
  Lemma pointer_slice_mixed_unaligned : forall sz n bits p k,
      (N.of_nat (List.length bits) <= 8 * N.of_nat (S n))%N ->
      negb (is_pointer_chunk sz bits) = true ->
      memory_bytes_to_pointer_slice (List.map (mixed_byte bits) (Nseq 0 (S n)))
      = Some (p, k) ->
      pointer_chunk_aligned sz k = false.
  Proof.
    intros sz n bits p k Hlen H Hs.
    pose proof (pointer_slice_head bits n) as HP.
    destruct bits as [| [q j | | ] bits']; rewrite HP in Hs; try discriminate.
    destruct (pointer_slice_from q (j / 8)%N
                (List.map (mixed_byte (Bit_ptr q j :: bits')) (Nseq 0 (S n))))
      eqn:E; [| discriminate].
    inversion Hs; subst p k; clear Hs.
    assert (Hall : all_pointer_bits_from q (8 * (j / 8))%N (Bit_ptr q j :: bits')
                   = true)
      by (apply (pointer_slice_implies_bits (S n)); [exact Hlen | exact E]).
    assert (Ej : j = (8 * (j / 8))%N).
    { cbn [all_pointer_bits_from] in Hall.
      destruct (eq_dec_ptr q q) as [_ | NE]; [| now contradiction NE].
      cbn [andb] in Hall.
      destruct (N.eqb_spec j (8 * (j / 8))%N) as [Ej | ]; [exact Ej | discriminate]. }
    unfold pointer_chunk_aligned.
    destruct (N.eqb_spec (Npos sz mod 8) 0) as [H8 | ]; [| reflexivity].
    destruct (N.eqb_spec ((j / 8) * 8 mod Npos sz) 0) as [Hj | ]; [| reflexivity].
    exfalso.
    unfold is_pointer_chunk in H.
    replace ((j / 8) * 8)%N with j in Hj by lia.
    rewrite H8, Hj, N.eqb_refl in H; cbn [andb] in H.
    rewrite <- Ej in Hall.
    rewrite Hall in H; discriminate.
  Qed.

  Lemma read_base_block_BYTE_Mixed : forall sz bits,
      (N.of_nat (List.length bits) = Npos sz)%N ->
      negb (is_pointer_chunk sz bits) = true ->
      negb (forallb is_int_bit bits) = true ->
      negb (forallb is_poison_bit bits) = true ->
      memory_bytes_to_dvalue_base
        (List.map (memory_byte_of_dvalue_bv (@BYTE_Mixed Pa sz bits))
                  (Nseq 0 (N.to_nat (store_size_dtyp (DTYPE_Base (DTYPE_B sz))))))
        (DTYPE_B sz)
      = ret (@DVALUE_B Pa sz (BYTE_Mixed sz bits)).
  Proof.
    intros sz bits Hlen Hptr Hnint Hnall.
    erewrite map_ext with (g := mixed_byte bits)
      by (intros idx; apply writer_mixed_byte).
    pose proof (serializable_base_pos (DTYPE_B sz) I) as HKpos.
    assert (Hb : (Npos sz <= 8 * store_size_dtyp (DTYPE_Base (DTYPE_B sz)))%N).
    { rewrite store_size_dtyp_bytes.
      pose proof (N.div_mod (Npos sz + 7) 8 ltac:(lia)) as D.
      pose proof (N.mod_upper_bound (Npos sz + 7) 8 ltac:(lia)) as U.
      lia. }
    remember (N.to_nat (store_size_dtyp (DTYPE_Base (DTYPE_B sz)))) as K eqn:EK.
    assert (HKb : (N.of_nat (List.length bits) <= 8 * N.of_nat K)%N) by lia.
    destruct K as [| n]; [lia |].
    cbn [memory_bytes_to_dvalue_base].
    (* not all poison *)
    assert (Hap : all_poison_bytes (List.map (mixed_byte bits) (Nseq 0 (S n)))
                  = false).
    { destruct (all_poison_bytes (List.map (mixed_byte bits) (Nseq 0 (S n))))
        eqn:Eap; [| reflexivity].
      rewrite all_poison_bytes_forallb in Eap.
      apply mixed_all_poison in Eap; [| exact HKb].
      rewrite Eap in Hnall; discriminate. }
    rewrite Hap.
    (* a pointer slice, if there is one, is not a whole aligned chunk: the
       bytes are read as bits *)
    assert (Hfb : memory_bytes_to_byte_value sz (List.map (mixed_byte bits) (Nseq 0 (S n)))
                  = ret (memory_bytes_to_bits_value sz
                           (List.map (mixed_byte bits) (Nseq 0 (S n))))).
    { unfold memory_bytes_to_byte_value.
      destruct (memory_bytes_to_pointer_slice (List.map (mixed_byte bits) (Nseq 0 (S n))))
        as [[p k] |] eqn:Es; [| reflexivity].
      rewrite (pointer_slice_mixed_unaligned _ _ HKb Hptr Es); reflexivity. }
    rewrite Hfb; cbn [bind ret EOU_monad].
    (* the bits come back unchanged *)
    unfold memory_bytes_to_bits_value; cbv zeta.
    rewrite <- Hlen, get_bits_writer by exact HKb.
    rewrite rev_append_rev, app_nil_r, rev_append_rev, app_nil_r, rev_involutive.
    (* a pointer or poison bit sends the read to [BYTE_Mixed] *)
    assert (Hmix : (existsb is_ptr_bit bits || existsb is_poison_bit bits)%bool = true).
    { destruct (existsb is_ptr_bit bits) eqn:Eptr; [reflexivity |].
      cbn [orb]; apply not_all_int_no_ptr_pois; assumption. }
    rewrite Hmix; cbn [dvalue_bv_all_poison].
    apply negb_true_iff in Hnall; rewrite Hnall; reflexivity.
  Qed.


  (** The one remaining bit-level obligation of the round trip: the reader
      inverts the writer at each supported base type.  Per [dtyp_base] this
      needs a [concat_bytes_Z]-after-[extract_byte_vint] lemma for [DTYPE_I]
      (and the float types), that [valid_pointer_bytes] accepts what the
      writer laid down for [DTYPE_Pointer], and that [dvalue_bv_canonical]
      forces [memory_bytes_to_byte_value] down the branch the value came
      from for [DTYPE_B].  Poison is uniform: the writer emits poison bytes
      and every arm absorbs them. *)
  Lemma read_base_block : forall dtb dv,
      serializable_base dtb ->
      dvalue_base_has_dtyp_base dv dtb = true ->
      dvalue_base_canonical dv = true ->
      memory_bytes_to_dvalue_base
        (List.map (base_byte_gen dv)
                  (Nseq 0 (N.to_nat (store_size_dtyp (DTYPE_Base dtb))))) dtb
      = ret dv.
  Proof.
    intros dtb dv HS HB HC;
      destruct dv as [p | vsz x | ip | d | fl | | | bsz bv].
    - (* [DVALUE_Pointer]: only well-typed at [DTYPE_Pointer] *)
      destruct dtb; cbn in HB; try discriminate.
      apply read_base_block_pointer.
    - (* [DVALUE_I]: only well-typed at [DTYPE_I] of the same width *)
      destruct dtb as [tsz | | | | fp | | | | | | tsz];
        cbn in HB; try discriminate.
      apply Pos.eqb_eq in HB; subst tsz.
      cbn [base_byte_gen].
      destruct (N.eqb_spec (Npos vsz mod 8) 0) as [E8 | E8].
      + (* a whole number of bytes *)
        apply read_int_block_mult8; exact E8.
      + (* the last byte holds [sz mod 8] real bits plus poison padding *)
        apply read_int_block_mixed; exact E8.
    - (* [DVALUE_Iptr]: well-typed only at [DTYPE_Iptr], which is not
         [serializable_base] *)
      destruct dtb; cbn in HB, HS; try discriminate; contradiction.
    - (* [DVALUE_Double]: only well-typed at [DTYPE_FP FP_double] *)
      destruct dtb as [tsz | | | | fp | | | | | | tsz]; cbn in HB; try discriminate.
      destruct fp; cbn in HB; try discriminate.
      apply read_base_block_double.
    - (* [DVALUE_Float]: only well-typed at [DTYPE_FP FP_float] *)
      destruct dtb as [tsz | | | | fp | | | | | | tsz]; cbn in HB; try discriminate.
      destruct fp; cbn in HB; try discriminate.
      apply read_base_block_float.
    - (* [DVALUE_Poison]: the block is a run of [poison_memory_byte], which
         every arm of the reader absorbs *)
      cbn [base_byte_gen]; rewrite map_const_Nseq.
      apply read_base_block_poison; exact HS.
    - (* [DVALUE_None]: well-typed only at [DTYPE_Void], which is not
         [serializable_base] *)
      destruct dtb; cbn in HB, HS; try discriminate; contradiction.
    - (* [DVALUE_B]: each constructor of a canonical [dvalue_bv] must come back
         down the branch of [memory_bytes_to_byte_value] it came from *)
      destruct dtb as [tsz | | | | fp | | | | | | tsz]; cbn in HB; try discriminate.
      apply Pos.eqb_eq in HB; subst tsz.
      cbn [base_byte_gen].
      destruct bv as [p k | x | bits].
      + (* [BYTE_Pointer]: canonical only at a whole number of bytes *)
        apply read_base_block_BYTE_Pointer.
        cbn in HC; apply N.eqb_eq in HC; exact HC.
      + (* [BYTE_I] *) apply read_base_block_BYTE_I.
      + (* [BYTE_Mixed] *)
        cbn in HC.
        apply andb_true_iff in HC as [HC3 HC4].
        apply andb_true_iff in HC3 as [HC2 HC3].
        apply andb_true_iff in HC2 as [HC1 HC2].
        apply N.eqb_eq in HC1.
        apply read_base_block_BYTE_Mixed; assumption.
  Qed.


  (* both aggregate arms of the writer share this body for a poison value *)
  Lemma poison_block_shape : forall n ta acc,
      (let '(o, bs) := accumulate_padding_bytes 0%N n acc in
       ret (accumulate_padding o ta bs) : EOU (N * list memory_byte))
      = raise_ret (tapad ta n,
                   List.repeat poison_memory_byte (N.to_nat (tapad ta n)) ++ acc).
  Proof.
    intros n ta acc; unfold accumulate_padding_bytes; cbv beta iota.
    replace (0 + n)%N with n by lia.
    destruct ta as [a |]; cbn [accumulate_padding tapad].
    - rewrite 2 accumulate_poison_bytes_app, app_assoc, <- repeat_app.
      unfold pad_to.
      replace (N.to_nat (pad_amount a n) + N.to_nat n)%nat
         with (N.to_nat (n + pad_amount a n)) by lia.
      reflexivity.
    - rewrite accumulate_poison_bytes_app; reflexivity.
  Qed.

  Lemma ser_poison_agg : forall dt ta acc,
      match dt with DTYPE_Base _ => False | _ => True end ->
      acc_dvalue_to_memory_bytes_h dt (DVALUE_Base DVALUE_Poison) 0%N ta acc
      = raise_ret (tapad ta (store_size_dtyp dt),
                   List.repeat poison_memory_byte
                     (N.to_nat (tapad ta (store_size_dtyp dt))) ++ acc).
  Proof.
    intros dt ta acc H; destruct dt as [db | pk dts | vv sz t]; [contradiction | |].
    - rewrite ser_struct_poison_unfold; apply poison_block_shape.
    - rewrite ser_array_poison_unfold; apply poison_block_shape.
  Qed.

  Lemma poison_split_app_live : forall w extra,
      snd (poison_split w) <> [] ->
      poison_split (w ++ extra)
      = (fst (poison_split w), snd (poison_split w) ++ extra).
  Proof.
    induction w as [| b w IH]; intros extra H.
    - exfalso; apply H; reflexivity.
    - specialize (IH extra).
      cbn [poison_split app] in *.
      destruct (is_all_poison_byte b).
      + destruct (poison_split w) as [k tl]; cbv beta iota in *.
        rewrite IH by assumption; reflexivity.
      + reflexivity.
  Qed.

  Lemma poison_split_app_poison : forall w extra,
      snd (poison_split w) = [] ->
      poison_split (w ++ extra)
      = ((fst (poison_split w) + fst (poison_split extra))%N,
         snd (poison_split extra)).
  Proof.
    induction w as [| b w IH]; intros extra H.
    - cbn [poison_split app].
      destruct (poison_split extra) as [ke te]; cbn [fst snd].
      rewrite N.add_0_l; reflexivity.
    - specialize (IH extra).
      cbn [poison_split app] in *.
      destruct (is_all_poison_byte b).
      + destruct (poison_split w) as [k tl]; cbv beta iota in *.
        rewrite IH by assumption.
        destruct (poison_split extra) as [ke te]; cbn [fst snd] in *.
        cbv beta iota.
        replace (1 + (k + ke))%N with (1 + k + ke)%N by lia; reflexivity.
      + cbv beta iota in H; discriminate.
  Qed.

  (** A base read consumes exactly [store_size_dtyp], so anything after the
      value is invisible to it.  This is what makes the [tail_align] padding
      harmless, and it is the base case of the same property for aggregates. *)
  Lemma read_base_trailing : forall dtb w extra,
      (store_size_dtyp (DTYPE_Base dtb) <= N.of_nat (length w))%N ->
      memory_bytes_to_dvalue (w ++ extra) (DTYPE_Base dtb)
      = memory_bytes_to_dvalue w (DTYPE_Base dtb).
  Proof.
    intros dtb w extra H; cbn [memory_bytes_to_dvalue].
    now rewrite take_app_le by exact H.
  Qed.

  (** The reader's struct loop, lifted out of [memory_bytes_to_dvalue] the same
      way the writer's loops were, so it can be reasoned about by induction.
      [read_struct_unfold] says the lift is exact. *)
  Section ReadStructLoop.
    Variable rd : list memory_byte -> dtyp -> EOU dvalue.
    Variable np : N.
    Variable pad : option N.

    Fixpoint read_struct_loop (offset : N) (dts : list dtyp)
      (dbs : list memory_byte) {struct dts} : EOU (list dvalue) :=
      match dts with
      | [] => ret []
      | (dt::dts) =>
          let padding :=
            if pad
            then pad_amount (preferred_alignment (dtyp_alignment dt)) offset
            else 0%N
          in
          let dbs' := drop padding dbs in
          let start := (offset + padding)%N in
          let ssz := store_size_dtyp dt in
          let asz := alloc_size_dtyp dt in
          let rest_bytes := drop asz dbs' in
          f <- (if N.leb (start + ssz) np
                then ret (DVALUE_Base DVALUE_Poison)
                else rd (take ssz dbs') dt) ;;
          rest <- read_struct_loop (start + asz) dts rest_bytes ;;
          ret (f :: rest)
      end.
  End ReadStructLoop.

  Lemma read_struct_unfold : forall packed dts dbs,
      memory_bytes_to_dvalue dbs (DTYPE_Struct packed dts)
      = let '(np, rest) := poison_split dbs in
        match rest with
        | [] => ret (DVALUE_Base DVALUE_Poison)
        | _ :: _ =>
            (canonicalize_agg (DVALUE_Struct packed))
              <$> (read_struct_loop memory_bytes_to_dvalue np
                     (if packed then None
                      else Some (max_preferred_dtyp_alignment dts))
                     0%N dts dbs)
        end.
  Proof. reflexivity. Qed.

  (* [poison_split] hands back a genuinely all-poison prefix *)
  Lemma poison_split_prefix : forall l,
      forallb is_all_poison_byte (take (fst (poison_split l)) l) = true.
  Proof.
    induction l as [| b l IH]; [reflexivity |].
    cbn [poison_split].
    destruct (is_all_poison_byte b) eqn:Eb.
    - destruct (poison_split l) as [k tl] eqn:E; cbn [fst] in *.
      cbn [take]; rewrite N.eqb_sym.
      destruct (N.eqb_spec (1 + k) 0)%N; [lia |].
      cbn [forallb]; rewrite Eb, N.pred_sub.
      replace (1 + k - 1)%N with k by lia; exact IH.
    - cbn [take fst]; reflexivity.
  Qed.

  (** A non-poison base value always lays down at least one non-poison byte.
      This is what lets the aggregate cases justify the reader's [np] skipping:
      a field lying entirely below the first non-poison byte must itself have
      been poison. *)

  Lemma forallb_head_false : forall (b : memory_byte) l,
      is_all_poison_byte b = false -> forallb is_all_poison_byte (b :: l) = false.
  Proof. intros b l H; cbn [forallb]; rewrite H; reflexivity. Qed.

  Lemma base_block_not_all_poison : forall dtb dv,
      serializable_base dtb ->
      dvalue_base_has_dtyp_base dv dtb = true ->
      dvalue_base_canonical dv = true ->
      dv <> DVALUE_Poison ->
      forallb is_all_poison_byte
        (List.map (base_byte_gen dv)
                  (Nseq 0 (N.to_nat (store_size_dtyp (DTYPE_Base dtb))))) = false.
  Proof.
    intros dtb dv HS HB HC HNP.
    assert (HK : (0 < N.to_nat (store_size_dtyp (DTYPE_Base dtb)))%nat)
      by (pose proof (serializable_base_pos dtb HS); lia).
    destruct (N.to_nat (store_size_dtyp (DTYPE_Base dtb))) as [| K] eqn:EK;
      [lia |].
    destruct dv as [p | vsz x | ip | d | fl | | | bsz bv].
    - (* pointer *) cbn [Nseq List.map base_byte_gen]; reflexivity.
    - (* integer: reuse the [BYTE_I] block fact *)
      cbn [base_byte_gen].
      rewrite <- all_poison_bytes_forallb.
      apply all_poison_BYTE_I_block; lia.
    - (* iptr is not serializable *)
      destruct dtb; cbn in HB, HS; try discriminate; contradiction.
    - (* double *) cbn [Nseq List.map base_byte_gen]; reflexivity.
    - (* float *) cbn [Nseq List.map base_byte_gen]; reflexivity.
    - (* poison, excluded *) contradiction.
    - (* none is only well-typed at void *)
      destruct dtb; cbn in HB, HS; try discriminate; contradiction.
    - (* byte vector *)
      destruct dtb as [tsz | | | | fp | | | | | | tsz]; cbn in HB; try discriminate.
      apply Pos.eqb_eq in HB; subst tsz.
      cbn [base_byte_gen].
      assert (Hb : (Npos bsz <= 8 * store_size_dtyp (DTYPE_Base (DTYPE_B bsz)))%N).
      { rewrite store_size_dtyp_bytes.
        pose proof (N.div_mod (Npos bsz + 7) 8 ltac:(lia)).
        pose proof (N.mod_upper_bound (Npos bsz + 7) 8 ltac:(lia)); lia. }
      destruct bv as [q k | x | bits].
      + cbn [Nseq List.map memory_byte_of_dvalue_bv]; reflexivity.
      + rewrite <- all_poison_bytes_forallb.
        apply all_poison_BYTE_I_block; lia.
      + cbn in HC.
        apply andb_true_iff in HC as [HC3 HC4].
        apply andb_true_iff in HC3 as [HC2 _].
        apply andb_true_iff in HC2 as [HC1 _].
        apply N.eqb_eq in HC1.
        destruct (forallb is_all_poison_byte
                    (List.map (memory_byte_of_dvalue_bv (BYTE_Mixed bsz bits))
                       (Nseq 0 (S K)))) eqn:E; [| reflexivity].
        exfalso.
        erewrite map_ext in E by (intros idx; apply writer_mixed_byte).
        apply mixed_all_poison in E; [rewrite E in HC4; discriminate | lia].
  Qed.

  (** The property [round_trip_h] proves, named so that the aggregate loop
      lemmas can take the induction hypothesis as [Forall rt_spec]. *)
  Definition rt_spec (dv : dvalue) : Prop :=
    forall dt, dvalue_has_dtyp dv dt ->
    serializable dt ->
    forall ta acc offset' bs,
      acc_dvalue_to_memory_bytes_h dt dv 0%N ta acc = raise_ret (offset', bs) ->
      exists w, bs = w ++ acc
             /\ N.of_nat (length w) = tapad ta (store_size_dtyp dt)
             /\ memory_bytes_to_dvalue (rev w) dt = ret dv
             /\ (dv <> DVALUE_Base DVALUE_Poison ->
                 forallb is_all_poison_byte (rev w) = false).

  (** The reader's array/vector loop, lifted the same way. *)
  Section ReadArrayLoop.
    Variable rd : list memory_byte -> dtyp -> EOU dvalue.
    Variable np : N.
    Variable stride : N.
    Variable t : dtyp.

    Fixpoint read_array_loop (n : nat) (offset : N) (dbs : list memory_byte)
      {struct n} : EOU (list dvalue) :=
      match n with
      | O => ret []
      | S n' =>
          e <- (if N.leb (offset + store_size_dtyp t) np
                then ret (DVALUE_Base DVALUE_Poison)
                else rd (take (store_size_dtyp t) dbs) t) ;;
          rest <- read_array_loop n' (offset + stride)%N (drop stride dbs) ;;
          ret (e :: rest)
      end.
  End ReadArrayLoop.

  Lemma read_array_unfold : forall vec sz t dbs,
      memory_bytes_to_dvalue dbs (DTYPE_Array vec sz t)
      = let '(np, rest) := poison_split dbs in
        match rest with
        | [] => ret (DVALUE_Base DVALUE_Poison)
        | _ :: _ =>
            elts <- read_array_loop memory_bytes_to_dvalue np
                      (if vec then store_size_dtyp t else alloc_size_dtyp t) t
                      (N.to_nat sz) 0%N dbs ;;
            ret (canonicalize_agg (DVALUE_Array vec) elts)
        end.
  Proof. reflexivity. Qed.

  Lemma read_array_loop_cons : forall rd np stride t n offset dbs,
      read_array_loop rd np stride t (S n) offset dbs
      = (e <- (if N.leb (offset + store_size_dtyp t) np
               then ret (DVALUE_Base DVALUE_Poison)
               else rd (take (store_size_dtyp t) dbs) t) ;;
         rest <- read_array_loop rd np stride t n (offset + stride)%N
                   (drop stride dbs) ;;
         ret (e :: rest)).
  Proof. reflexivity. Qed.

  (** Shapes of the two padding primitives, and a sublist fact for the
      reader's poison prefix. *)

  Lemma accumulate_padding_shape : forall offset q acc,
      accumulate_padding offset q acc
      = (tapad q offset,
         List.repeat poison_memory_byte (N.to_nat (tapad q offset - offset)) ++ acc).
  Proof.
    intros offset [a |] acc; cbn [accumulate_padding tapad].
    - rewrite accumulate_poison_bytes_app.
      unfold pad_to.
      replace (offset + pad_amount a offset - offset)%N
        with (pad_amount a offset) by lia.
      reflexivity.
    - replace (offset - offset)%N with 0%N by lia; reflexivity.
  Qed.

  Lemma accumulate_padding_bytes_shape : forall offset n acc,
      accumulate_padding_bytes offset n acc
      = ((offset + n)%N, List.repeat poison_memory_byte (N.to_nat n) ++ acc).
  Proof.
    intros offset n acc; unfold accumulate_padding_bytes.
    rewrite accumulate_poison_bytes_app; reflexivity.
  Qed.

  Lemma forallb_poison_repeat : forall k,
      forallb is_all_poison_byte (List.repeat poison_memory_byte k) = true.
  Proof. induction k as [| k IH]; cbn; [reflexivity | exact IH]. Qed.
  Lemma forallb_sub : forall (l : list memory_byte) n i m,
      (i + m <= n)%N ->
      forallb is_all_poison_byte (take n l) = true ->
      forallb is_all_poison_byte (take m (drop i l)) = true.
  Proof.
    intros l n i m Hle H.
    rewrite <- (@take_take_le _ (drop i l) m (n - i)) by lia.
    rewrite <- drop_take.
    apply forallb_take_pres, forallb_drop_pres; exact H.
  Qed.


  Lemma read_struct_loop_cons : forall rd np pad offset dt dts dbs,
      read_struct_loop rd np pad offset (dt::dts) dbs
      = (let padding := if pad
                        then pad_amount (preferred_alignment (dtyp_alignment dt)) offset
                        else 0%N in
         let dbs' := drop padding dbs in
         let start := (offset + padding)%N in
         f <- (if N.leb (start + store_size_dtyp dt) np
               then ret (DVALUE_Base DVALUE_Poison)
               else rd (take (store_size_dtyp dt) dbs') dt) ;;
         rest <- read_struct_loop rd np pad (start + alloc_size_dtyp dt) dts
                   (drop (alloc_size_dtyp dt) dbs') ;;
         ret (f :: rest)).
  Proof. reflexivity. Qed.

  (** The struct loops, writer against reader.  The writer emits, per field,
      [[leading padding][child block][pad to alloc size]]; the reader does
      [drop padding], [take ssz], [drop asz].  The last clause is the reader
      side: given that the block's first [np - offset] bytes are poison (which
      is what [poison_split] reports), the reader's loop rebuilds [fields].
      A field the reader skips lies wholly inside that poison prefix, so by
      the fourth clause of [rt_spec] it must have been poison -- which is what
      the reader answers. *)
  Lemma struct_loop_read : forall fields dts,
      Forall2 dvalue_has_dtyp fields dts ->
      Forall rt_spec fields ->
      FORALL serializable dts ->
      forall ta pad offset acc offset' bs,
        struct_bytes_loop acc_dvalue_to_memory_bytes_h ta pad fields dts offset acc
          = raise_ret (offset', bs) ->
        exists w, bs = w ++ acc
               /\ N.of_nat (length w) = (offset' - offset)%N
               /\ (offset <= offset')%N
               /\ (forallb dvalue_is_poison fields = false ->
                   forallb is_all_poison_byte (rev w) = false)
               /\ (forall np extra,
                     forallb is_all_poison_byte
                       (take (np - offset) (rev w ++ extra)) = true ->
                     read_struct_loop memory_bytes_to_dvalue np pad offset dts
                       (rev w ++ extra) = ret fields).
  Proof.
    intros fields dts HF2; induction HF2 as [| f dt fs dts Hfdt HF2 IHl];
      intros HR HSer ta pad offset acc offset' bs Heq.
    - (* no fields: just the struct's tail padding and the caller's *)
      rewrite struct_bytes_loop_nil, accumulate_padding_shape in Heq.
      cbv beta iota in Heq.
      rewrite accumulate_padding_shape in Heq.
      inversion Heq; subst; clear Heq.
      pose proof (tapad_ge pad offset) as G1.
      pose proof (tapad_ge ta (tapad pad offset)) as G2.
      exists (List.repeat poison_memory_byte
                (N.to_nat (tapad ta (tapad pad offset) - tapad pad offset))
              ++ List.repeat poison_memory_byte
                   (N.to_nat (tapad pad offset - offset))).
      split; [now rewrite <- app_assoc | split; [| split; [| split]]].
      + rewrite length_app, !repeat_length; lia.
      + lia.
      + cbn [forallb]; discriminate.
      + intros np extra Hpre; reflexivity.
    - (* one field, then the rest *)
      inversion HR as [| ? ? Hrt HRtl]; subst; clear HR.
      destruct HSer as [HSdt HSdts].
      rewrite struct_bytes_loop_cons, accumulate_padding_shape in Heq.
      cbv beta iota in Heq.
      set (q := if pad then Some (preferred_alignment (dtyp_alignment dt)) else None)
        in Heq |- *.
      set (o1 := tapad q offset) in Heq |- *.
      set (p1 := List.repeat poison_memory_byte (N.to_nat (o1 - offset)))
        in Heq |- *.
      destruct (acc_dvalue_to_memory_bytes_h dt f 0%N None (p1 ++ acc))
        as [ | | | [coff cbs] ] eqn:EF;
        cbn -[acc_dvalue_to_memory_bytes_h accumulate_padding
              accumulate_padding_bytes struct_bytes_loop store_size_dtyp
              alloc_size_dtyp pad_to_align dtyp_alignment preferred_alignment
              max_preferred_dtyp_alignment] in Heq;
        try discriminate.
      destruct (Hrt dt Hfdt HSdt None (p1 ++ acc) coff cbs EF)
        as (wf & Ecbs & Lwf & Hrdf & Hlivef).
      destruct (acc_dvalue_to_memory_bytes_h_spec Hfdt None (p1 ++ acc) EF)
        as [Ecoff _].
      cbn [tapad] in Ecoff, Lwf; subst coff.
      rewrite accumulate_padding_bytes_shape in Heq; cbv beta iota in Heq.
      set (p2 := List.repeat poison_memory_byte
                   (N.to_nat (alloc_size_dtyp dt - store_size_dtyp dt)))
        in Heq |- *.
      destruct (IHl HRtl HSdts ta pad _ _ _ _ Heq)
        as (wr & Ebs & Lwr & Hler & Hliver & Hreadr).
      pose proof (store_le_alloc dt) as SA.
      replace (o1 + store_size_dtyp dt
               + (alloc_size_dtyp dt - store_size_dtyp dt))%N
        with (o1 + alloc_size_dtyp dt)%N in Hreadr, Lwr, Hler by lia.
      pose proof (tapad_ge q offset) as G1.
      assert (Lp1 : N.of_nat (length p1) = (o1 - offset)%N)
        by (subst p1; rewrite repeat_length; lia).
      assert (Lp2 : N.of_nat (length p2)
                    = (alloc_size_dtyp dt - store_size_dtyp dt)%N)
        by (subst p2; rewrite repeat_length; lia).
      exists (wr ++ p2 ++ wf ++ p1).
      assert (Erev : rev (wr ++ p2 ++ wf ++ p1)
                     = p1 ++ rev wf ++ p2 ++ rev wr).
      { rewrite !rev_app_distr, !app_assoc.
        subst p1 p2; rewrite !rev_repeat; reflexivity. }
      split; [rewrite Ebs, Ecbs; rewrite <- !app_assoc; reflexivity | split; [| split; [| split]]].
      + rewrite !length_app; lia.
      + lia.
      + intros Hnp; rewrite Erev, !forallb_app.
        cbn [forallb] in Hnp; apply andb_false_iff in Hnp as [Hf | Hfs].
        * rewrite (Hlivef (dvalue_is_poison_false Hf)).
          rewrite andb_false_l, andb_false_r; reflexivity.
        * rewrite (Hliver Hfs), !andb_false_r; reflexivity.
      + intros np extra Hpre.
        rewrite Erev in Hpre |- *.
        rewrite <- !app_assoc in Hpre |- *.
        rewrite read_struct_loop_cons; cbv beta zeta.
        assert (Epad : (if pad
                        then pad_amount (preferred_alignment (dtyp_alignment dt)) offset
                        else 0%N) = (o1 - offset)%N).
        { subst o1 q; destruct pad; cbn [tapad]; unfold pad_to; lia. }
        rewrite Epad.
        assert (Lwf' : N.of_nat (length (rev wf)) = store_size_dtyp dt)
          by (rewrite length_rev; exact Lwf).
        assert (Lwfp2 : N.of_nat (length (rev wf ++ p2)) = alloc_size_dtyp dt)
          by (rewrite length_app, length_rev; lia).
        rewrite (drop_app_exact p1 Lp1).
        replace (offset + (o1 - offset))%N with o1 by lia.
        rewrite (@take_app_exact _ (rev wf) (p2 ++ rev wr ++ extra)
                   (store_size_dtyp dt) Lwf').
        rewrite (app_assoc (rev wf) p2).
        rewrite (drop_app_exact (rev wf ++ p2) Lwfp2).
        (* the tail's poison prefix *)
        assert (Edrop : drop (o1 + alloc_size_dtyp dt - offset)%N
                          (p1 ++ rev wf ++ p2 ++ rev wr ++ extra)
                        = rev wr ++ extra).
        { rewrite (app_assoc p1), (app_assoc (p1 ++ rev wf)).
          apply drop_app_exact.
          rewrite !length_app, length_rev; lia. }
        assert (Hr : forallb is_all_poison_byte
                       (take (np - (o1 + alloc_size_dtyp dt))
                          (rev wr ++ extra)) = true).
        { destruct (N.leb_spec np (o1 + alloc_size_dtyp dt)) as [Hle2 | Hgt].
          - replace (np - (o1 + alloc_size_dtyp dt))%N with 0%N by lia.
            rewrite take_nil; reflexivity.
          - rewrite <- Edrop.
            apply forallb_sub with (n := (np - offset)%N); [lia | exact Hpre]. }
        rewrite (Hreadr np extra Hr).
        (* the field itself: read, or skipped because it is poison *)
        destruct (N.leb_spec (o1 + store_size_dtyp dt) np) as [Hskip | Hread].
        * assert (Hwf : forallb is_all_poison_byte (rev wf) = true).
          { assert (Etake : take (store_size_dtyp dt)
                              (drop (o1 - offset)%N
                                 (p1 ++ rev wf ++ p2 ++ rev wr ++ extra))
                            = rev wf).
            { rewrite (drop_app_exact p1 Lp1).
              apply (@take_app_exact _ (rev wf) (p2 ++ rev wr ++ extra)
                       (store_size_dtyp dt) Lwf'). }
            rewrite <- Etake.
            apply forallb_sub with (n := (np - offset)%N); [lia | exact Hpre]. }
          assert (Hfp : f = DVALUE_Base DVALUE_Poison).
          { destruct (dvalue_eq_dec f (DVALUE_Base DVALUE_Poison)) as [E | NE];
              [exact E |].
            exfalso; rewrite (Hlivef NE) in Hwf; discriminate. }
          rewrite Hfp; reflexivity.
        * rewrite Hrdf; reflexivity.
  Qed.

  Lemma array_loop_read : forall elts t,
      Forall (fun x => dvalue_has_dtyp x t) elts ->
      Forall rt_spec elts ->
      serializable t ->
      forall ta ep offset acc offset' bs,
        array_bytes_loop acc_dvalue_to_memory_bytes_h ta t ep elts offset acc
          = raise_ret (offset', bs) ->
        exists w, bs = w ++ acc
               /\ N.of_nat (length w) = (offset' - offset)%N
               /\ (offset <= offset')%N
               /\ (forallb dvalue_is_poison elts = false ->
                   forallb is_all_poison_byte (rev w) = false)
               /\ (forall np extra,
                     forallb is_all_poison_byte
                       (take (np - offset) (rev w ++ extra)) = true ->
                     read_array_loop memory_bytes_to_dvalue np
                       (store_size_dtyp t + ep)%N t (length elts) offset
                       (rev w ++ extra) = ret elts).
  Proof.
    intros elts t HT; induction HT as [| e es Het HT IHl];
      intros HR HSt ta ep offset acc offset' bs Heq.
    - (* no elements: only the caller's padding *)
      rewrite array_bytes_loop_nil, accumulate_padding_shape in Heq.
      inversion Heq; subst; clear Heq.
      pose proof (tapad_ge ta offset) as G.
      exists (List.repeat poison_memory_byte (N.to_nat (tapad ta offset - offset))).
      split; [reflexivity | split; [| split; [| split]]].
      + rewrite repeat_length; lia.
      + lia.
      + cbn [forallb]; discriminate.
      + intros np extra Hpre; reflexivity.
    - (* one element, then the rest *)
      inversion HR as [| ? ? Hrt HRtl]; subst; clear HR.
      rewrite array_bytes_loop_cons in Heq.
      destruct (acc_dvalue_to_memory_bytes_h t e 0%N None acc)
        as [ | | | [coff cbs] ] eqn:EF;
        cbn -[acc_dvalue_to_memory_bytes_h accumulate_padding_bytes
              array_bytes_loop store_size_dtyp alloc_size_dtyp] in Heq;
        try discriminate.
      destruct (Hrt t Het HSt None acc coff cbs EF)
        as (we & Ecbs & Lwe & Hrde & Hlivee).
      destruct (acc_dvalue_to_memory_bytes_h_spec Het None acc EF) as [Ecoff _].
      cbn [tapad] in Ecoff, Lwe; subst coff.
      rewrite accumulate_padding_bytes_shape in Heq; cbv beta iota in Heq.
      set (pe := List.repeat poison_memory_byte (N.to_nat ep)) in Heq |- *.
      destruct (IHl HRtl HSt ta ep _ _ _ _ Heq)
        as (wr & Ebs & Lwr & Hler & Hliver & Hreadr).
      assert (Lpe : N.of_nat (length pe) = ep)
        by (subst pe; rewrite repeat_length; lia).
      exists (wr ++ pe ++ we).
      assert (Erev : rev (wr ++ pe ++ we) = rev we ++ pe ++ rev wr).
      { rewrite !rev_app_distr, !app_assoc; subst pe; rewrite rev_repeat; reflexivity. }
      assert (Lwe' : N.of_nat (length (rev we)) = store_size_dtyp t)
        by (rewrite length_rev; exact Lwe).
      assert (Lwepe : N.of_nat (length (rev we ++ pe)) = (store_size_dtyp t + ep)%N)
        by (rewrite length_app, length_rev; lia).
      split; [rewrite Ebs, Ecbs; rewrite <- !app_assoc; reflexivity
             | split; [| split; [| split]]].
      + rewrite !length_app; lia.
      + lia.
      + intros Hnp; rewrite Erev, !forallb_app.
        cbn [forallb] in Hnp; apply andb_false_iff in Hnp as [He | Hes].
        * rewrite (Hlivee (dvalue_is_poison_false He)); reflexivity.
        * rewrite (Hliver Hes), !andb_false_r; reflexivity.
      + intros np extra Hpre.
        rewrite Erev in Hpre |- *.
        rewrite <- !app_assoc in Hpre |- *.
        cbn [length]; rewrite read_array_loop_cons.
        rewrite (@take_app_exact _ (rev we) (pe ++ rev wr ++ extra)
                   (store_size_dtyp t) Lwe').
        rewrite (app_assoc (rev we) pe).
        rewrite (drop_app_exact (rev we ++ pe) Lwepe).
        replace (offset + (store_size_dtyp t + ep))%N
          with (offset + store_size_dtyp t + ep)%N by lia.
        assert (Edrop : drop (offset + store_size_dtyp t + ep - offset)%N
                          (rev we ++ pe ++ rev wr ++ extra) = rev wr ++ extra).
        { rewrite (app_assoc (rev we) pe).
          apply drop_app_exact; rewrite length_app, length_rev; lia. }
        assert (Hr : forallb is_all_poison_byte
                       (take (np - (offset + store_size_dtyp t + ep))
                          (rev wr ++ extra)) = true).
        { destruct (N.leb_spec np (offset + store_size_dtyp t + ep)) as [Hle2 | Hgt].
          - replace (np - (offset + store_size_dtyp t + ep))%N with 0%N by lia.
            rewrite take_nil; reflexivity.
          - rewrite <- Edrop.
            apply forallb_sub with (n := (np - offset)%N); [lia | exact Hpre]. }
        rewrite (Hreadr np extra Hr).
        destruct (N.leb_spec (offset + store_size_dtyp t) np) as [Hskip | Hread].
        * assert (Hwe : forallb is_all_poison_byte (rev we) = true).
          { assert (Etake : take (store_size_dtyp t)
                              (drop 0%N (rev we ++ pe ++ rev wr ++ extra))
                            = rev we).
            { rewrite drop_nil.
              apply (@take_app_exact _ (rev we) (pe ++ rev wr ++ extra)
                       (store_size_dtyp t) Lwe'). }
            rewrite <- Etake.
            apply forallb_sub with (n := (np - offset)%N); [lia | exact Hpre]. }
          assert (Hep : e = DVALUE_Base DVALUE_Poison).
          { destruct (dvalue_eq_dec e (DVALUE_Base DVALUE_Poison)) as [E | NE];
              [exact E |].
            exfalso; rewrite (Hlivee NE) in Hwe; discriminate. }
          rewrite Hep; reflexivity.
        * rewrite Hrde; reflexivity.
  Qed.

  (** The invariant the round trip is proved by.  The writer accumulates in
      reverse on top of [acc], so it contributes a block [w] that [acc] is
      appended to; [w] has the type's store size, and reading [rev w] back
      gives [dv]. *)
  Lemma round_trip_h : forall dv dt, dvalue_has_dtyp dv dt ->
    serializable dt ->
    forall ta acc offset' bs,
      acc_dvalue_to_memory_bytes_h dt dv 0%N ta acc = raise_ret (offset', bs) ->
      exists w, bs = w ++ acc
             /\ N.of_nat (length w) = tapad ta (store_size_dtyp dt)
             /\ memory_bytes_to_dvalue (rev w) dt = ret dv
             (* carried along for the aggregate cases: a live value always
                leaves a live byte, which is what justifies the reader
                skipping fields that fall below its [np] *)
             /\ (dv <> DVALUE_Base DVALUE_Poison ->
                 forallb is_all_poison_byte (rev w) = false).
  Proof.
    intros dv; induction dv using dvalue_ind; intros dt HT HS ta acc offset' bs Heq.
    - (* [DVALUE_Base]: either a genuine base type, or poison at an aggregate
         one ([DVALUE_Poison_typ_agg] is the only constructor that applies
         there, so the value must be poison). *)
      destruct dt as [dtb | pk dts | vv sz t].
      + (* a genuine base type: the writer lays down [base_block], then [ta]'s
           padding; the reader trims back to exactly the block *)
        assert (HB : dvalue_base_has_dtyp_base dv dtb = true
                     /\ dvalue_base_canonical dv = true)
          by (inversion HT; subst; split; cbn; auto).
        destruct HB as [HB HC].
        rewrite ser_base_unfold, acc_base_unfold, rev_loop_acc_app in Heq.
        cbv beta iota in Heq; rewrite N.add_0_r in Heq.
        pose proof (base_block_length dtb dv) as Lblk.
        destruct ta as [a |]; cbn [accumulate_padding tapad] in Heq |- *.
        * rewrite accumulate_poison_bytes_app in Heq.
          inversion Heq; subst; clear Heq.
          eexists; split; [now rewrite <- app_assoc | split; [| split]].
          -- rewrite length_app, repeat_length, length_rev, length_map, Nseq_length.
             unfold pad_to; lia.
          -- rewrite rev_app_distr, rev_involutive, rev_repeat.
             cbn [memory_bytes_to_dvalue].
             rewrite take_app_exact by exact Lblk.
             rewrite read_base_block by assumption; reflexivity.
          -- intros Hne.
             rewrite rev_app_distr, rev_involutive, rev_repeat, forallb_app.
             rewrite base_block_not_all_poison
               by (first [exact HS | exact HB | exact HC
                         | intros C; apply Hne; f_equal; exact C]).
             reflexivity.
        * inversion Heq; subst; clear Heq.
          eexists; split; [reflexivity | split; [| split]].
          -- rewrite length_rev; exact Lblk.
          -- rewrite rev_involutive.
             cbn [memory_bytes_to_dvalue].
             rewrite take_all by lia.
             rewrite read_base_block by assumption; reflexivity.
          -- intros Hne; rewrite rev_involutive.
             apply base_block_not_all_poison;
               first [exact HS | exact HB | exact HC
                     | intros C; apply Hne; f_equal; exact C].
      + (* poison at a struct type *)
        inversion HT; subst.
        rewrite ser_poison_agg in Heq by exact I.
        inversion Heq; subst; clear Heq.
        eexists; split; [reflexivity | split; [| split]].
        * rewrite repeat_length, Nnat.N2Nat.id; reflexivity.
        * rewrite rev_repeat; apply read_repeat_poison_agg; exact I.
        * intros C; exfalso; apply C; reflexivity.
      + (* poison at an array/vector type *)
        inversion HT; subst.
        rewrite ser_poison_agg in Heq by exact I.
        inversion Heq; subst; clear Heq.
        eexists; split; [reflexivity | split; [| split]].
        * rewrite repeat_length, Nnat.N2Nat.id; reflexivity.
        * rewrite rev_repeat; apply read_repeat_poison_agg; exact I.
        * intros C; exfalso; apply C; reflexivity.
    - (* [DVALUE_Struct]: the loop lemma does the work; here we only have to
         get past [poison_split]'s fast path and [canonicalize_agg]. *)
      pose proof Heq as Heq0.
      inversion HT as [| | pp ffs ddts HNP HF2 |]; subst.
      rewrite ser_struct_unfold in Heq.
      destruct (struct_loop_read HF2 IH HS _ _ _ _ Heq)
        as (w & Ebs & Hlen & Hle & Hlive & Hread).
      destruct (acc_dvalue_to_memory_bytes_h_spec HT ta acc Heq0) as [Eo _].
      exists w; split; [exact Ebs | split; [| split]].
      + rewrite Hlen, Eo; lia.
      + rewrite read_struct_unfold.
        destruct (poison_split (rev w)) as [np rest] eqn:Eps.
        destruct rest as [| b rest].
        * (* the block cannot be all poison: some field is live *)
          exfalso.
          assert (Hap : all_poison_bytes (rev w) = true)
            by (unfold all_poison_bytes; rewrite Eps; reflexivity).
          rewrite all_poison_bytes_forallb, (Hlive HNP) in Hap; discriminate.
        * assert (HPre : forallb is_all_poison_byte
                           (take (np - 0) (rev w ++ [])) = true).
          { rewrite app_nil_r, N.sub_0_r.
            pose proof (poison_split_prefix (rev w)) as HP.
            rewrite Eps in HP; cbn [fst] in HP; exact HP. }
          specialize (Hread np [] HPre); rewrite app_nil_r in Hread.
          rewrite Hread; cbn.
          unfold canonicalize_agg; rewrite HNP; reflexivity.
      + intros _; apply Hlive; exact HNP.
    - (* [DVALUE_Array]: same shape as the struct, with a uniform stride *)
      pose proof Heq as Heq0.
      inversion HT as [| | | vv ees sz0 eet HNV HNP HFA HLen]; subst.
      rewrite ser_array_unfold in Heq.
      destruct (array_loop_read HFA IH HS _ _ _ _ Heq)
        as (w & Ebs & Hlen & Hle & Hlive & Hread).
      destruct (acc_dvalue_to_memory_bytes_h_spec HT ta acc Heq0) as [Eo _].
      exists w; split; [exact Ebs | split; [| split]].
      + rewrite Hlen, Eo; lia.
      + rewrite read_array_unfold.
        destruct (poison_split (rev w)) as [np rest] eqn:Eps.
        destruct rest as [| b rest].
        * exfalso.
          assert (Hap : all_poison_bytes (rev w) = true)
            by (unfold all_poison_bytes; rewrite Eps; reflexivity).
          rewrite all_poison_bytes_forallb, (Hlive HNP) in Hap; discriminate.
        * assert (HPre : forallb is_all_poison_byte
                           (take (np - 0) (rev w ++ [])) = true).
          { rewrite app_nil_r, N.sub_0_r.
            pose proof (poison_split_prefix (rev w)) as HP.
            rewrite Eps in HP; cbn [fst] in HP; exact HP. }
          specialize (Hread np [] HPre); rewrite app_nil_r, HLen in Hread.
          replace (if v then store_size_dtyp eet else alloc_size_dtyp eet)
            with (store_size_dtyp eet
                  + (if v then 0
                     else alloc_size_dtyp eet - store_size_dtyp eet))%N
            by (pose proof (store_le_alloc eet); destruct v; lia).
          rewrite Hread; cbn.
          unfold canonicalize_agg; rewrite HNP; reflexivity.
      + intros _; apply Hlive; exact HNP.
  Qed.

  Lemma memory_bytes_round_trip1 :
    forall dt dv ta mb,
      serializable dt ->
      dvalue_has_dtyp dv dt ->
      dvalue_to_memory_bytes dt dv ta = ret mb ->
      memory_bytes_to_dvalue mb dt = ret dv.
  Proof.
    intros dt dv ta mb HS HT HW.
    unfold dvalue_to_memory_bytes in HW.
    destruct (acc_dvalue_to_memory_bytes_h dt dv 0%N ta [])
      as [ | | | [off bs] ] eqn:E; cbn in HW; try discriminate.
    inversion HW; subst; clear HW.
    destruct (round_trip_h HT HS _ _ E) as (w & Ebs & _ & HR & _).
    rewrite Ebs, app_nil_r, rev_append_rev, app_nil_r.
    exact HR.
  Qed.

  (** ** The reader produces well-typed, canonical values

      [memory_bytes_to_dvalue] answers only with a value of the type it was
      asked for, in canonical form ([memory_bytes_to_dvalue_has_dtyp]).
      Together with [memory_bytes_round_trip1] this makes reading
      idempotent: writing back a value that was read, and reading again,
      gives the same value.

      The bytes must be well formed: a [BYTE_Mixed] byte has exactly 8
      bits.  The writer only produces such bytes. *)
  Definition memory_byte_wf (mb : memory_byte) : Prop :=
    match mb with
    | BYTE_Mixed bits => List.length bits = 8%nat
    | _ => True
    end.

  Lemma memory_byte_bits_length : forall mb,
      memory_byte_wf mb -> List.length (memory_byte_to_memory_bits mb) = 8%nat.
  Proof.
    intros [p i | x | bits] H; cbn [memory_byte_to_memory_bits memory_byte_wf] in *;
      try exact H;
      rewrite rev_append_rev, app_nil_r, length_rev, rev_loop_acc_length; reflexivity.
  Qed.

  (** The reader's bit list, in forward order. *)
  Fixpoint get_bits_fwd (n : N) (dbs : list memory_byte) : list memory_bit :=
    match dbs with
    | [] => List.repeat Bit_psn (N.to_nat n)
    | b :: bs =>
        if N.ltb n 8 then take n (memory_byte_to_memory_bits b)
        else memory_byte_to_memory_bits b ++ get_bits_fwd (n - 8) bs
    end.

  Lemma get_bits_fwd_spec : forall dbs n acc,
      get_bits_of_memory_byte_list n dbs acc = rev_append (get_bits_fwd n dbs) acc.
  Proof.
    induction dbs as [| b bs IH]; intros n acc;
      cbn [get_bits_of_memory_byte_list get_bits_fwd].
    - destruct (N.eqb_spec n 0).
      + subst; reflexivity.
      + rewrite rev_loop_acc_const, rev_append_rev, rev_repeat; reflexivity.
    - destruct (N.ltb n 8); [reflexivity |].
      rewrite IH, !rev_append_rev, rev_app_distr, <- app_assoc; reflexivity.
  Qed.

  Lemma reader_bits_fwd : forall n dbs,
      rev_append (get_bits_of_memory_byte_list n dbs []) [] = get_bits_fwd n dbs.
  Proof.
    intros n dbs; rewrite get_bits_fwd_spec, !rev_append_rev, !app_nil_r, rev_involutive.
    reflexivity.
  Qed.

  Lemma get_bits_fwd_length : forall dbs n,
      Forall memory_byte_wf dbs ->
      N.of_nat (List.length (get_bits_fwd n dbs)) = n.
  Proof.
    induction dbs as [| b bs IH]; intros n HW; cbn [get_bits_fwd].
    - rewrite repeat_length, Nnat.N2Nat.id; reflexivity.
    - inversion HW as [| ? ? Hb Hbs]; subst.
      pose proof (memory_byte_bits_length _ Hb) as HL.
      destruct (N.ltb_spec n 8).
      + apply take_length_exact; rewrite HL; lia.
      + rewrite length_app, Nnat.Nat2N.inj_add, HL, IH by exact Hbs; lia.
  Qed.

  (** A whole aligned pointer chunk among the bits is a pointer slice among
      the bytes, and the reader finds it. *)
  Lemma valid_pointer_bits_of_run : forall bits p base off,
      all_pointer_bits_from p (base + off) bits = true ->
      (N.of_nat (List.length bits) + off = 8)%N ->
      valid_pointer_bits p base off bits = ret true.
  Proof.
    induction bits as [| b bits IH]; intros p base off H HL; cbn [valid_pointer_bits].
    - cbn [List.length] in HL; replace off with 8%N by lia; reflexivity.
    - destruct b as [q i | | x]; cbn [all_pointer_bits_from] in H; try discriminate.
      destruct (eq_dec_ptr p q) as [E | NE]; cbn [andb] in H; [| discriminate].
      destruct (N.eqb_spec i (base + off)) as [Ei | NE]; cbn [andb] in H; [| discriminate].
      apply IH.
      + replace (base + (1 + off))%N with (1 + (base + off))%N by lia; exact H.
      + cbn [List.length] in HL; lia.
  Qed.

  Lemma BYTE_Pointer_bits : forall p k,
      memory_byte_to_memory_bits (@BYTE_Pointer Pa 8 p k)
      = List.map (fun t => Bit_ptr p t) (Nseq (8 * k) 8).
  Proof.
    intros p k; cbn [memory_byte_to_memory_bits].
    rewrite rev_loop_acc_app, !rev_append_rev, !app_nil_r, rev_involutive.
    reflexivity.
  Qed.

  Lemma pointer_byte_at_run : forall b p i,
      memory_byte_wf b ->
      all_pointer_bits_from p (8 * i) (memory_byte_to_memory_bits b) = true ->
      pointer_byte_at p i b = true.
  Proof.
    intros [q k | x | bits] p i Hb H; unfold pointer_byte_at, valid_pointer_byte.
    - rewrite BYTE_Pointer_bits in H; cbn [Nseq List.map all_pointer_bits_from] in H.
      destruct (eq_dec_ptr p q) as [E | NE]; cbn [andb] in H; [| discriminate].
      destruct (N.eqb_spec (8 * k) (8 * i)); cbn [andb] in H; [| discriminate].
      cbn; apply N.eqb_eq; lia.
    - cbn [memory_byte_to_memory_bits] in H.
      rewrite rev_loop_acc_app in H; cbn in H; discriminate.
    - cbn [memory_byte_to_memory_bits memory_byte_wf] in H, Hb.
      rewrite (valid_pointer_bits_of_run bits p (i * 8) 0);
        [reflexivity | rewrite N.add_0_r, N.mul_comm; exact H | rewrite Hb; reflexivity].
  Qed.

  Lemma pointer_slice_from_chunk : forall dbs p i n,
      Forall memory_byte_wf dbs ->
      (8 * N.of_nat (List.length dbs) <= n)%N ->
      all_pointer_bits_from p (8 * i) (get_bits_fwd n dbs) = true ->
      pointer_slice_from p i dbs = true.
  Proof.
    induction dbs as [| b bs IH]; intros p i n HW Hn H; [reflexivity |].
    inversion HW as [| ? ? Hb Hbs]; subst.
    cbn [List.length] in Hn; cbn [get_bits_fwd] in H.
    destruct (N.ltb_spec n 8); [lia |].
    rewrite all_pointer_bits_from_app in H; apply andb_true_iff in H as [H1 H2].
    rewrite (memory_byte_bits_length _ Hb) in H2.
    cbn [pointer_slice_from]; rewrite (pointer_byte_at_run _ _ _ Hb H1); cbn [andb].
    apply (IH p (1 + i) (n - 8)); [exact Hbs | lia |].
    replace (8 * (1 + i))%N with (8 * i + N.of_nat 8)%N by lia; exact H2.
  Qed.

  Lemma pointer_slice_of_chunk : forall sz dbs,
      Forall memory_byte_wf dbs ->
      (8 * N.of_nat (List.length dbs) <= Npos sz)%N ->
      is_pointer_chunk sz (get_bits_fwd (Npos sz) dbs) = true ->
      exists p k, memory_bytes_to_pointer_slice dbs = Some (p, k)
                  /\ pointer_chunk_aligned sz k = true.
  Proof.
    intros sz dbs HW Hn H.
    unfold is_pointer_chunk in H.
    destruct (get_bits_fwd (Npos sz) dbs) as [| [p j | | x] tl] eqn:Ef; try discriminate.
    apply andb_true_iff in H as [H Hall]; apply andb_true_iff in H as [H8 Hj].
    apply N.eqb_eq in H8, Hj.
    (* the run starts at byte [j / 8] *)
    assert (Ej : j = (8 * (j / 8))%N).
    { pose proof (N.div_mod j (Npos sz) ltac:(lia)) as Dj.
      pose proof (N.div_mod (Npos sz) 8 ltac:(lia)) as Ds.
      rewrite Hj, N.add_0_r in Dj; rewrite H8, N.add_0_r in Ds.
      rewrite Dj at 2; rewrite Ds at 1.
      replace (8 * (Npos sz / 8) * (j / Npos sz))%N
        with ((Npos sz / 8 * (j / Npos sz)) * 8)%N by lia.
      rewrite N.div_mul by lia; lia. }
    assert (Hsl : pointer_slice_from p (j / 8) dbs = true).
    { eapply pointer_slice_from_chunk; [exact HW | exact Hn |].
      rewrite Ef, <- Ej; exact Hall. }
    assert (Hal : pointer_chunk_aligned sz (j / 8) = true).
    { unfold pointer_chunk_aligned; rewrite H8, N.eqb_refl; cbn [andb].
      apply N.eqb_eq; rewrite N.mul_comm, <- Ej; exact Hj. }
    (* the first byte starts the run *)
    destruct dbs as [| b bs]; cbn [get_bits_fwd] in Ef.
    { destruct (Pos2Nat.is_succ sz) as [m Em].
      cbn [N.to_nat] in Ef; rewrite Em in Ef; discriminate. }
    inversion HW as [| ? ? Hb Hbs]; subst.
    destruct (N.ltb_spec (Npos sz) 8).
    { exfalso; pose proof (N.mod_small (Npos sz) 8 ltac:(lia)); lia. }
    destruct b as [q k | y | bits].
    - rewrite BYTE_Pointer_bits in Ef; cbn [Nseq List.map app] in Ef.
      injection Ef as Eq Ejk _; subst q.
      assert (E8k : (8 * k = j)%N) by (rewrite <- Ejk; reflexivity).
      assert (Hk : (j / 8 = k)%N)
        by (rewrite <- E8k, N.mul_comm, N.div_mul; lia).
      rewrite Hk in Hsl, Hal.
      exists p, k; cbn [memory_bytes_to_pointer_slice].
      rewrite Hsl; split; [reflexivity | exact Hal].
    - cbn [memory_byte_to_memory_bits] in Ef; rewrite rev_loop_acc_app in Ef.
      cbn in Ef; discriminate.
    - cbn [memory_byte_to_memory_bits memory_byte_wf] in Ef, Hb.
      destruct bits as [| b0 bits]; [discriminate |].
      cbn [app] in Ef; inversion Ef; subst b0.
      exists p, (j / 8)%N; cbn [memory_bytes_to_pointer_slice].
      rewrite Hsl; split; [reflexivity | exact Hal].
  Qed.

  Lemma mix_not_all_int : forall l : list memory_bit,
      (existsb is_ptr_bit l || existsb is_poison_bit l)%bool = true ->
      forallb is_int_bit l = false.
  Proof.
    induction l as [| b l IH]; cbn; [discriminate |].
    destruct b; cbn; auto.
  Qed.

  (* the bits read as bits are canonical, unless they are a whole aligned
     pointer chunk -- which the reader will have recognised first *)
  Lemma memory_bytes_to_bits_value_canonical : forall sz dbs,
      Forall memory_byte_wf dbs ->
      (N.of_nat (List.length dbs) <= store_size_dtyp (DTYPE_Base (DTYPE_B sz)))%N ->
      (forall p k, memory_bytes_to_pointer_slice dbs = Some (p, k) ->
                   pointer_chunk_aligned sz k = false) ->
      dvalue_bv_all_poison (memory_bytes_to_bits_value sz dbs) = false ->
      dvalue_bv_canonical (memory_bytes_to_bits_value sz dbs) = true.
  Proof.
    intros sz dbs HW HL NA HNP.
    unfold memory_bytes_to_bits_value in *; cbv zeta in *.
    rewrite reader_bits_fwd in *.
    destruct (existsb is_ptr_bit (get_bits_fwd (Npos sz) dbs)
              || existsb is_poison_bit (get_bits_fwd (Npos sz) dbs))%bool eqn:Emix.
    2:{ destruct (memory_bytes_to_int sz dbs) as [| | | [x |]]; reflexivity. }
    cbn [dvalue_bv_canonical dvalue_bv_all_poison] in *.
    rewrite (get_bits_fwd_length _ HW), N.eqb_refl, HNP, (mix_not_all_int _ Emix).
    destruct (is_pointer_chunk sz (get_bits_fwd (Npos sz) dbs)) eqn:Ec; [| reflexivity].
    exfalso.
    assert (H8 : (Npos sz mod 8 = 0)%N).
    { unfold is_pointer_chunk in Ec.
      destruct (get_bits_fwd (Npos sz) dbs) as [| [p j | |] tl]; try discriminate.
      apply andb_true_iff in Ec as [Ec _]; apply andb_true_iff in Ec as [Ec _].
      apply N.eqb_eq; exact Ec. }
    assert (Hn : (8 * N.of_nat (List.length dbs) <= Npos sz)%N)
      by (rewrite <- (@store_size_B_bytes _ _ sz H8); lia).
    destruct (@pointer_slice_of_chunk sz dbs HW Hn Ec) as (p & k & Es & Ea).
    rewrite (NA p k Es) in Ea; discriminate.
  Qed.

  Lemma memory_bytes_to_byte_value_canonical : forall sz dbs bv,
      Forall memory_byte_wf dbs ->
      (N.of_nat (List.length dbs) <= store_size_dtyp (DTYPE_Base (DTYPE_B sz)))%N ->
      memory_bytes_to_byte_value sz dbs = ret bv ->
      dvalue_bv_all_poison bv = false ->
      dvalue_bv_canonical bv = true.
  Proof.
    intros sz dbs bv HW HL H HNP.
    unfold memory_bytes_to_byte_value in H.
    destruct (memory_bytes_to_pointer_slice dbs) as [[p k] |] eqn:Es.
    - destruct (pointer_chunk_aligned sz k) eqn:Ea; cbn in H; inversion H; subst bv.
      + unfold pointer_chunk_aligned in Ea; apply andb_true_iff in Ea as [Ea _].
        exact Ea.
      + apply memory_bytes_to_bits_value_canonical; auto.
        intros p' k' Es'; rewrite Es in Es'; inversion Es'; subst; exact Ea.
    - cbn in H; inversion H; subst bv.
      apply memory_bytes_to_bits_value_canonical; auto.
      intros p' k' Es'; rewrite Es in Es'; discriminate.
  Qed.

  (** Base types. *)
  Lemma memory_bytes_to_dvalue_base_has_dtyp : forall dt dbs v,
      serializable_base dt ->
      Forall memory_byte_wf dbs ->
      (N.of_nat (List.length dbs) <= store_size_dtyp (DTYPE_Base dt))%N ->
      memory_bytes_to_dvalue_base dbs dt = ret v ->
      dvalue_has_dtyp (DVALUE_Base v) (DTYPE_Base dt).
  Proof.
    intros dt dbs v HS HW HL H.
    destruct dt as [sz | | | | fp | | | | | | sz]; cbn in HS; try contradiction;
      cbn [memory_bytes_to_dvalue_base] in H.
    - (* [DTYPE_I] *)
      unfold absorb_pois, catch_pois in H.
      destruct (memory_bytes_to_int sz dbs) as [| | | [x |]]; cbn in H;
        inversion H; subst; [| apply DVALUE_Poison_typ_agg].
      constructor; [apply Pos.eqb_refl | reflexivity].
    - (* [DTYPE_Pointer] *)
      unfold absorb_pois, catch_pois in H.
      destruct (memory_bytes_to_pointer dbs) as [| | | [p |]]; cbn in H;
        inversion H; subst; [| apply DVALUE_Poison_typ_agg].
      constructor; reflexivity.
    - (* [DTYPE_FP] *)
      destruct fp; cbn in HS; try contradiction;
        unfold absorb_pois, catch_pois in H;
        destruct (map_monad memory_byte_to_Z dbs) as [| | | [zs |]]; cbn in H;
        inversion H; subst; try apply DVALUE_Poison_typ_agg;
        constructor; reflexivity.
    - (* [DTYPE_B] *)
      destruct (all_poison_bytes dbs).
      { cbn in H; inversion H; subst; apply DVALUE_Poison_typ_agg. }
      destruct (memory_bytes_to_byte_value sz dbs) as [| | | bv] eqn:Eb;
        cbn in H; try discriminate.
      destruct (dvalue_bv_all_poison bv) eqn:Ep; inversion H; subst;
        [apply DVALUE_Poison_typ_agg |].
      constructor; [apply Pos.eqb_refl |].
      cbn [dvalue_base_canonical].
      eapply memory_bytes_to_byte_value_canonical; eauto.
  Qed.

  (** Aggregates: each field or element is a read of a sub-block, or
      poison. *)
  Lemma read_struct_loop_has_dtyp : forall rd np pad dts offset dbs vs,
      (forall t, In t dts -> forall mb v, Forall memory_byte_wf mb ->
                 rd mb t = ret v -> dvalue_has_dtyp v t) ->
      Forall memory_byte_wf dbs ->
      read_struct_loop rd np pad offset dts dbs = ret vs ->
      Forall2 dvalue_has_dtyp vs dts.
  Proof.
    intros rd np pad; induction dts as [| t ts IH]; intros offset dbs vs HR HW H.
    - cbn in H; inversion H; constructor.
    - cbn [read_struct_loop] in H; cbv zeta in H.
      apply EOU_bind_ret_inv in H as (f & Ef & H).
      apply EOU_bind_ret_inv in H as (rest & Er & H).
      cbn in H; inversion H; subst vs; clear H.
      constructor.
      + match type of Ef with
        | (if ?c then _ else _) = _ => destruct c
        end.
        * cbn in Ef; inversion Ef; apply DVALUE_Poison_typ_agg.
        * eapply HR; [now left | | exact Ef].
          apply Forall_take_N, Forall_drop_N, HW.
      + eapply IH; [intros u Hu; apply HR; now right | | exact Er].
        apply Forall_drop_N, Forall_drop_N, HW.
  Qed.

  Lemma read_array_loop_has_dtyp : forall rd np stride t n offset dbs vs,
      (forall mb v, Forall memory_byte_wf mb -> rd mb t = ret v -> dvalue_has_dtyp v t) ->
      Forall memory_byte_wf dbs ->
      read_array_loop rd np stride t n offset dbs = ret vs ->
      Forall (fun v => dvalue_has_dtyp v t) vs /\ List.length vs = n.
  Proof.
    intros rd np stride t; induction n as [| n IH]; intros offset dbs vs HR HW H.
    - cbn in H; inversion H; split; [constructor | reflexivity].
    - rewrite read_array_loop_cons in H.
      apply EOU_bind_ret_inv in H as (e & Ee & H).
      apply EOU_bind_ret_inv in H as (rest & Er & H).
      cbn in H; inversion H; subst vs; clear H.
      destruct (IH _ _ _ HR (Forall_drop_N _ HW) Er) as [HF HL].
      split; [constructor; [| exact HF] | cbn; rewrite HL; reflexivity].
      match type of Ee with
      | (if ?c then _ else _) = _ => destruct c
      end.
      + cbn in Ee; inversion Ee; apply DVALUE_Poison_typ_agg.
      + eapply HR; [apply Forall_take_N, HW | exact Ee].
  Qed.

  Lemma memory_bytes_to_dvalue_has_dtyp : forall dt mb dv,
      serializable dt ->
      Forall memory_byte_wf mb ->
      memory_bytes_to_dvalue mb dt = ret dv ->
      dvalue_has_dtyp dv dt.
  Proof.
    induction dt as [db | pk dts IH | vv sz t IHt]; intros mb dv HS HW H.
    - (* base: the reader trims to the store size *)
      cbn [memory_bytes_to_dvalue] in H.
      destruct (memory_bytes_to_dvalue_base (take (store_size_dtyp (DTYPE_Base db)) mb) db)
        as [| | | v] eqn:E; cbn in H; try discriminate.
      inversion H; subst dv.
      eapply memory_bytes_to_dvalue_base_has_dtyp;
        [exact HS | apply Forall_take_N, HW | apply take_length_le | exact E].
    - (* struct *)
      rewrite read_struct_unfold in H.
      destruct (poison_split mb) as [np rest]; destruct rest as [| b rest].
      { cbn in H; inversion H; apply DVALUE_Poison_typ_agg. }
      destruct (read_struct_loop memory_bytes_to_dvalue np
                  (if pk then None else Some (max_preferred_dtyp_alignment dts)) 0%N dts mb)
        as [| | | vs] eqn:Ev; cbn in H; try discriminate.
      inversion H; subst dv; clear H.
      unfold canonicalize_agg.
      destruct (forallb dvalue_is_poison vs) eqn:Ep; [apply DVALUE_Poison_typ_agg |].
      apply DVALUE_Struct_typ; [exact Ep |].
      eapply read_struct_loop_has_dtyp; [| exact HW | exact Ev].
      intros u Hu mb' v' HW' H'.
      apply FORALL_forall in HS.
      eapply IH; [exact Hu | eapply Forall_forall; [exact HS | exact Hu] | exact HW' | exact H'].
    - (* array / vector *)
      rewrite read_array_unfold in H.
      destruct (poison_split mb) as [np rest]; destruct rest as [| b rest].
      { cbn in H; inversion H; apply DVALUE_Poison_typ_agg. }
      apply EOU_bind_ret_inv in H as (elts & Ee & H).
      cbn in H; inversion H; subst dv; clear H.
      assert (HR : forall mb' v', Forall memory_byte_wf mb' ->
                     memory_bytes_to_dvalue mb' t = ret v' -> dvalue_has_dtyp v' t)
        by (intros mb' v' HW' H'; eapply IHt; eauto).
      destruct (@read_array_loop_has_dtyp memory_bytes_to_dvalue _ _ t _ _ mb elts HR HW Ee)
        as [HF HL].
      unfold canonicalize_agg.
      destruct (forallb dvalue_is_poison elts) eqn:Ep; [apply DVALUE_Poison_typ_agg |].
      apply DVALUE_Array_typ; [apply serializable_NO_VOID, HS | exact Ep | exact HF | exact HL].
  Qed.

  (** Reading is idempotent: what one read loses (poison bits that poison a
      whole value, padding, provenance read at an integer type, ...) stays
      lost, and nothing more is lost by writing the value back and reading
      it again. *)
  Lemma memory_bytes_to_dvalue_idempotent :
    forall dt dv mb1 mb2,
      serializable dt ->
      Forall memory_byte_wf mb1 ->
      memory_bytes_to_dvalue mb1 dt = ret dv ->
      dvalue_to_memory_bytes dt dv None = ret mb2 ->
      memory_bytes_to_dvalue mb2 dt = ret dv.
  Proof.
    intros dt dv mb1 mb2 HS HW H1 H2.
    eapply memory_bytes_round_trip1;
      [exact HS | eapply memory_bytes_to_dvalue_has_dtyp; eauto | exact H2].
  Qed.

  (** ** The writer produces well-formed bytes

      Every byte [dvalue_to_memory_bytes] emits is a [BYTE_I], a
      [BYTE_Pointer], or an 8-bit [BYTE_Mixed] -- a poison byte, or one byte
      of a [BYTE_Mixed] value, padded out to 8 bits -- so written memory
      meets the [memory_byte_wf] precondition of
      [memory_bytes_to_dvalue_idempotent].  No typing hypothesis is
      needed. *)
  Lemma memory_byte_of_dvalue_bv_wf : forall sz (bv : @dvalue_bv Pa sz) idx,
      memory_byte_wf (memory_byte_of_dvalue_bv bv idx).
  Proof.
    intros sz [p k | x | bits] idx; cbn [memory_byte_of_dvalue_bv memory_byte_wf];
      try exact I.
    cbv zeta; rewrite length_app.
    pose proof (take_length_le (drop (8 * idx) bits) 8) as HL.
    destruct (N.eqb_spec (N.of_nat (List.length (take 8 (drop (8 * idx) bits)))) 8)
      as [E | NE]; cbn [negb].
    - cbn [List.length]; lia.
    - rewrite repeat_length; lia.
  Qed.

  Lemma poison_memory_byte_wf : memory_byte_wf poison_memory_byte.
  Proof. reflexivity. Qed.

  Lemma Forall_wf_poison_app : forall k acc,
      Forall memory_byte_wf acc ->
      Forall memory_byte_wf (List.repeat poison_memory_byte k ++ acc).
  Proof.
    intros k acc H; apply Forall_app; split; [| exact H].
    apply Forall_forall; intros x Hx; apply repeat_spec in Hx; subst x.
    exact poison_memory_byte_wf.
  Qed.

  Lemma accumulate_padding_wf : forall o q acc,
      Forall memory_byte_wf acc ->
      Forall memory_byte_wf (snd (accumulate_padding o q acc)).
  Proof.
    intros o q acc H; rewrite accumulate_padding_shape; apply Forall_wf_poison_app, H.
  Qed.

  Lemma accumulate_padding_bytes_wf : forall o n acc,
      Forall memory_byte_wf acc ->
      Forall memory_byte_wf (snd (accumulate_padding_bytes o n acc)).
  Proof.
    intros o n acc H; rewrite accumulate_padding_bytes_shape; apply Forall_wf_poison_app, H.
  Qed.

  Lemma acc_memory_bytes_of_dvalue_base_wf : forall dtb dv offset acc,
      Forall memory_byte_wf acc ->
      Forall memory_byte_wf (snd (acc_memory_bytes_of_dvalue_base dtb dv offset acc)).
  Proof.
    intros dtb dv offset acc H; unfold acc_memory_bytes_of_dvalue_base; cbv zeta;
      cbn [snd].
    rewrite rev_loop_acc_app; apply Forall_app; split; [| exact H].
    apply Forall_rev, Forall_forall; intros b Hb; apply in_map_iff in Hb as (i & <- & _).
    destruct dv;
      first [apply memory_byte_of_dvalue_bv_wf | exact I | exact poison_memory_byte_wf].
  Qed.

  (* the two aggregate loops, given that each field / element writes
     well-formed bytes *)
  Lemma struct_bytes_loop_wf : forall ser ta pad fields types offset acc r,
      (forall f, In f fields -> forall dt o ta' acc' r',
          Forall memory_byte_wf acc' -> ser dt f o ta' acc' = ret r' ->
          Forall memory_byte_wf (snd r')) ->
      Forall memory_byte_wf acc ->
      struct_bytes_loop ser ta pad fields types offset acc = ret r ->
      Forall memory_byte_wf (snd r).
  Proof.
    intros ser ta pad; induction fields as [| f fs IH];
      intros types offset acc r HS HW H;
      destruct types as [| t ts]; cbn [struct_bytes_loop] in H; try discriminate.
    - destruct (accumulate_padding offset pad acc) as [o1 a1] eqn:E1.
      inversion H; subst r.
      apply accumulate_padding_wf.
      change a1 with (snd (o1, a1)); rewrite <- E1; apply accumulate_padding_wf, HW.
    - cbv zeta in H.
      match type of H with
      | context [accumulate_padding ?o ?q ?a] =>
          destruct (accumulate_padding o q a) as [o1 a1] eqn:E1
      end.
      apply EOU_bind_ret_inv in H as ([coff bs] & Es & H).
      match type of H with
      | context [accumulate_padding_bytes ?o ?n ?a] =>
          destruct (accumulate_padding_bytes o n a) as [o2 a2] eqn:E2
      end.
      eapply IH; [intros; eapply HS; [right; eassumption | eassumption | eassumption]
                 | | exact H].
      change a2 with (snd (o2, a2)); rewrite <- E2; apply accumulate_padding_bytes_wf.
      change bs with (snd (coff, bs)).
      eapply (HS f (or_introl eq_refl)); [| exact Es].
      change a1 with (snd (o1, a1)); rewrite <- E1; apply accumulate_padding_wf, HW.
  Qed.

  Lemma array_bytes_loop_wf : forall ser ta dt elt_pad elts offset acc r,
      (forall e, In e elts -> forall o ta' acc' r',
          Forall memory_byte_wf acc' -> ser dt e o ta' acc' = ret r' ->
          Forall memory_byte_wf (snd r')) ->
      Forall memory_byte_wf acc ->
      array_bytes_loop ser ta dt elt_pad elts offset acc = ret r ->
      Forall memory_byte_wf (snd r).
  Proof.
    intros ser ta dt elt_pad; induction elts as [| e es IH];
      intros offset acc r HS HW H; cbn [array_bytes_loop] in H.
    - inversion H; subst r; apply accumulate_padding_wf, HW.
    - apply EOU_bind_ret_inv in H as ([coff bs] & Es & H).
      match type of H with
      | context [accumulate_padding_bytes ?o ?n ?a] =>
          destruct (accumulate_padding_bytes o n a) as [o2 a2] eqn:E2
      end.
      eapply IH; [intros; eapply HS; [right; eassumption | eassumption | eassumption]
                 | | exact H].
      change a2 with (snd (o2, a2)); rewrite <- E2; apply accumulate_padding_bytes_wf.
      change bs with (snd (coff, bs)).
      eapply (HS e (or_introl eq_refl)); [exact HW | exact Es].
  Qed.

  Lemma acc_dvalue_to_memory_bytes_h_wf : forall dv dt offset ta acc r,
      Forall memory_byte_wf acc ->
      acc_dvalue_to_memory_bytes_h dt dv offset ta acc = ret r ->
      Forall memory_byte_wf (snd r).
  Proof.
    intros dv; induction dv as [db | p fields IH | v elts IH] using dvalue_ind;
      intros dt offset ta acc r HW H.
    - (* [DVALUE_Base]: the value's bytes, or poison at an aggregate type *)
      destruct dt as [dtb | packed dts | vec sz t].
      + rewrite ser_base_unfold in H.
        destruct (acc_memory_bytes_of_dvalue_base dtb db offset acc) as [o1 a1] eqn:E1.
        inversion H; subst r; apply accumulate_padding_wf.
        change a1 with (snd (o1, a1)); rewrite <- E1.
        apply acc_memory_bytes_of_dvalue_base_wf, HW.
      + destruct db; cbn [acc_dvalue_to_memory_bytes_h] in H; try discriminate.
        destruct (accumulate_padding_bytes offset _ acc) as [o1 a1] eqn:E1.
        inversion H; subst r; apply accumulate_padding_wf.
        change a1 with (snd (o1, a1)); rewrite <- E1.
        apply accumulate_padding_bytes_wf, HW.
      + destruct db; cbn [acc_dvalue_to_memory_bytes_h] in H; try discriminate.
        destruct (accumulate_padding_bytes offset _ acc) as [o1 a1] eqn:E1.
        inversion H; subst r; apply accumulate_padding_wf.
        change a1 with (snd (o1, a1)); rewrite <- E1.
        apply accumulate_padding_bytes_wf, HW.
    - (* [DVALUE_Struct] *)
      destruct dt as [dtb | packed dts | vec sz t];
        [cbn [acc_dvalue_to_memory_bytes_h] in H; discriminate | |
         cbn [acc_dvalue_to_memory_bytes_h] in H; discriminate].
      rewrite ser_struct_unfold in H.
      eapply struct_bytes_loop_wf; [| exact HW | exact H].
      intros f Hf dt' o ta' acc' r' HW' H'.
      eapply (proj1 (Forall_forall _ _) IH f Hf); eauto.
    - (* [DVALUE_Array] *)
      destruct dt as [dtb | packed dts | vec sz t];
        [cbn [acc_dvalue_to_memory_bytes_h] in H; discriminate
        | cbn [acc_dvalue_to_memory_bytes_h] in H; discriminate |].
      rewrite ser_array_unfold in H.
      eapply array_bytes_loop_wf; [| exact HW | exact H].
      intros e He o ta' acc' r' HW' H'.
      eapply (proj1 (Forall_forall _ _) IH e He); eauto.
  Qed.

  Lemma dvalue_to_memory_bytes_wf : forall dt dv ta mb,
      dvalue_to_memory_bytes dt dv ta = ret mb -> Forall memory_byte_wf mb.
  Proof.
    intros dt dv ta mb H; unfold dvalue_to_memory_bytes in H.
    apply EOU_bind_ret_inv in H as ([o bs] & E & H).
    inversion H; subst mb.
    rewrite rev_append_rev, app_nil_r; apply Forall_rev.
    change bs with (snd (o, bs)).
    eapply acc_dvalue_to_memory_bytes_h_wf; [constructor | exact E].
  Qed.

  (** So for memory the writer produced, reading is idempotent outright. *)
  Corollary memory_bytes_to_dvalue_idempotent_written :
    forall dt dv0 ta dv mb1 mb2,
      serializable dt ->
      dvalue_to_memory_bytes dt dv0 ta = ret mb1 ->
      memory_bytes_to_dvalue mb1 dt = ret dv ->
      dvalue_to_memory_bytes dt dv None = ret mb2 ->
      memory_bytes_to_dvalue mb2 dt = ret dv.
  Proof.
    intros dt dv0 ta dv mb1 mb2 HS HW1 H1 H2.
    eapply memory_bytes_to_dvalue_idempotent;
      [exact HS | eapply dvalue_to_memory_bytes_wf; exact HW1 | exact H1 | exact H2].
  Qed.

  (** ** Exactness at byte types

      The byte type exists so that memory can be copied through SSA values
      without losing anything: reading bytes at a byte type and writing the
      value back reproduces them -- pointer bits with their provenance, and
      poison bits -- as long as the type has no padding, which the writer
      fills with poison and the reader skips.

      [byte_layout] is the padding-free byte types: whole-byte [bN]s, vectors
      of them, and arrays and packed structs of them whose elements occupy
      exactly their store size.  (Packed structs, like arrays, advance by the
      *alloc* size, which for e.g. [b24] is 4 bytes.)

      The bytes come back with the same bits, not necessarily the same
      representation: eight integer bits stored as a [BYTE_Mixed] are
      written back as a [BYTE_I], and a pointer's byte stored as eight
      [Bit_ptr]s as a [BYTE_Pointer]. *)
  Fixpoint byte_layout (dt : dtyp) : Prop :=
    match dt with
    | DTYPE_Base (DTYPE_B sz) => (Npos sz mod 8 = 0)%N
    | DTYPE_Base _ => False
    | DTYPE_Array true _ t => byte_layout t
    | DTYPE_Array false _ t => byte_layout t /\ alloc_size_dtyp t = store_size_dtyp t
    | DTYPE_Struct true dts =>
        FORALL (fun t => byte_layout t /\ alloc_size_dtyp t = store_size_dtyp t) dts
    | DTYPE_Struct false _ => False
    end.

  Definition same_bits (b b' : memory_byte) : Prop :=
    memory_byte_to_memory_bits b = memory_byte_to_memory_bits b'.

  (** *** Poison *)

  Lemma forallb_psn_repeat : forall l : list (@memory_bit Pa),
      forallb is_poison_bit l = true -> l = List.repeat Bit_psn (List.length l).
  Proof.
    induction l as [| b l IH]; intros H; [reflexivity |].
    destruct b; cbn in H; try discriminate.
    cbn [List.length List.repeat]; f_equal; auto.
  Qed.

  Lemma same_bits_poison : forall b,
      memory_byte_wf b -> is_all_poison_byte b = true -> same_bits b poison_memory_byte.
  Proof.
    intros [p i | x | bits] Hw H; cbn in H; try discriminate.
    unfold same_bits, poison_memory_byte; cbn [memory_byte_to_memory_bits].
    cbn [memory_byte_wf] in Hw; unfold all_poison_bits in H.
    rewrite (forallb_psn_repeat _ H), Hw; reflexivity.
  Qed.

  Lemma same_bits_all_poison : forall dbs,
      Forall memory_byte_wf dbs -> forallb is_all_poison_byte dbs = true ->
      Forall2 same_bits dbs (List.repeat poison_memory_byte (List.length dbs)).
  Proof.
    induction dbs as [| b bs IH]; intros HW H; cbn [List.length List.repeat];
      [constructor |].
    inversion HW as [| ? ? Hb Hbs]; subst.
    cbn [forallb] in H; apply andb_true_iff in H as [Hh Ht].
    constructor; [apply same_bits_poison; assumption | apply IH; assumption].
  Qed.

  (** *** The writer's output *)

  Lemma write_base_block : forall dtb v acc o bs,
      acc_dvalue_to_memory_bytes_h (DTYPE_Base dtb) (DVALUE_Base v) 0%N None acc
      = ret (o, bs) ->
      bs = rev (List.map (base_byte_gen v)
                  (Nseq 0 (N.to_nat (store_size_dtyp (DTYPE_Base dtb))))) ++ acc.
  Proof.
    intros dtb v acc o bs H.
    rewrite ser_base_unfold, acc_base_unfold in H; cbn [accumulate_padding] in H.
    inversion H; subst; apply rev_loop_acc_app.
  Qed.

  Lemma write_poison_layout : forall dt acc o bs,
      byte_layout dt ->
      acc_dvalue_to_memory_bytes_h dt (DVALUE_Base DVALUE_Poison) 0%N None acc
      = ret (o, bs) ->
      bs = List.repeat poison_memory_byte (N.to_nat (store_size_dtyp dt)) ++ acc.
  Proof.
    intros [db | pk dts | vv sz t] acc o bs HL H.
    - apply write_base_block in H; rewrite H; cbn [base_byte_gen].
      rewrite map_const_Nseq, rev_repeat; reflexivity.
    - rewrite ser_poison_agg in H by exact I; inversion H; reflexivity.
    - rewrite ser_poison_agg in H by exact I; inversion H; reflexivity.
  Qed.

  (** *** Digit arithmetic

      [concat_bits_Z] and [concat_bytes_Z] are both little-endian
      concatenations of digits, of 1 and 8 bits: instances of
      [concat_digits] (Utils/ZUtil.v). *)
  Lemma concat_bits_Z_digits : forall l, concat_bits_Z l = concat_digits 1 l.
  Proof. induction l as [| z l IH]; cbn; [reflexivity | now rewrite IH]. Qed.

  Lemma concat_bytes_Z_digits : forall l, concat_bytes_Z l = concat_digits 8 l.
  Proof. induction l as [| z l IH]; cbn; [reflexivity | now rewrite IH]. Qed.

  Lemma extract_bit_vint_8 : forall (y : @bit_int 8) i,
      (i < 8)%N -> extract_bit_vint y i = ((unsigned y / 2 ^ Z.of_N i) mod 2)%Z.
  Proof.
    intros y i Hi.
    pose proof (unsigned_range y) as [Hlo Hhi].
    assert (Hm : (@modulus 8 = 256)%Z) by reflexivity.
    assert (Hp : (0 < 2 ^ Z.of_N i)%Z) by (apply Z.pow_pos_nonneg; lia).
    unfold extract_bit_vint.
    cbn [modu shru unsigned repr VInt_Bounded].
    unfold Integers.modu, Integers.shru.
    rewrite !unsigned_repr_eq, Hm.
    rewrite Hm in Hhi.
    rewrite (Z.mod_small (Z.of_N i)) by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    rewrite (Z.mod_small (Integers.unsigned y / 2 ^ Z.of_N i)).
    2:{ split; [apply Z.div_pos; lia |].
        apply Z.le_lt_trans with (Integers.unsigned y); [| lia].
        apply Z.div_le_upper_bound; [lia | nia]. }
    rewrite (Z.mod_small 2) by lia.
    apply Z.mod_small.
    pose proof (Z.mod_pos_bound (Integers.unsigned y / 2 ^ Z.of_N i) 2 ltac:(lia)); lia.
  Qed.

  Lemma BYTE_I_bits : forall (y : @bit_int 8),
      memory_byte_to_memory_bits (@BYTE_I Pa 8 y)
      = List.map (fun i => Bit_bit (repr (extract_bit_vint y i))) (Nseq 0 8).
  Proof.
    intros y; cbn [memory_byte_to_memory_bits].
    rewrite rev_loop_acc_app, !rev_append_rev, !app_nil_r, rev_involutive.
    reflexivity.
  Qed.

  (** *** The reader's bits at a whole-byte width

      Exactly [8 * length dbs] bits: the bytes' bits, concatenated. *)
  Lemma get_bits_fwd_concat : forall dbs n,
      Forall memory_byte_wf dbs ->
      (8 * N.of_nat (List.length dbs) = n)%N ->
      get_bits_fwd n dbs = List.concat (List.map memory_byte_to_memory_bits dbs).
  Proof.
    induction dbs as [| b bs IH]; intros n HW Hn; cbn [get_bits_fwd List.map List.concat].
    - cbn [List.length] in Hn; subst n; reflexivity.
    - apply Forall_cons_iff in HW as [Hb Hbs].
      cbn [List.length] in Hn.
      destruct (N.ltb_spec n 8); [lia |].
      rewrite (IH (n - 8)%N Hbs) by lia; reflexivity.
  Qed.


  (** *** Pointer bytes *)

  Lemma all_pointer_bits_from_map : forall p l s,
      all_pointer_bits_from p s l = true ->
      l = List.map (fun t => Bit_ptr p t) (Nseq s (List.length l)).
  Proof.
    intros p; induction l as [| b l IH]; intros s H; [reflexivity |].
    destruct b as [q i | | x]; cbn [all_pointer_bits_from] in H; try discriminate.
    destruct (eq_dec_ptr p q) as [E | NE]; cbn [andb] in H; [subst q | discriminate].
    destruct (N.eqb_spec i s) as [Ei | NE]; cbn [andb] in H; [subst i | discriminate].
    cbn [List.length Nseq List.map]; f_equal.
    replace (N.succ s) with (1 + s)%N by lia; apply IH; exact H.
  Qed.

  Lemma same_bits_pointer_byte : forall b p j,
      memory_byte_wf b -> pointer_byte_at p j b = true ->
      same_bits b (@BYTE_Pointer Pa 8 p j).
  Proof.
    intros [q i | x | bits] p j Hw H; unfold pointer_byte_at, valid_pointer_byte in H.
    - destruct (eq_dec_ptr p q) as [E | NE]; [subst q | cbn in H; discriminate].
      cbn in H; apply N.eqb_eq in H; subst i; reflexivity.
    - cbn in H; discriminate.
    - destruct (valid_pointer_bits p (j * 8) 0 bits) as [| | | [[|] |]] eqn:Ev;
        try discriminate.
      apply valid_pointer_bits_implies in Ev; rewrite N.add_0_r in Ev.
      apply all_pointer_bits_from_map in Ev.
      cbn [memory_byte_wf] in Hw; rewrite Hw in Ev.
      unfold same_bits; rewrite BYTE_Pointer_bits; cbn [memory_byte_to_memory_bits].
      rewrite Ev; replace (j * 8)%N with (8 * j)%N by lia; reflexivity.
  Qed.

  Lemma pointer_slice_from_same_bits : forall p dbs k,
      Forall memory_byte_wf dbs -> pointer_slice_from p k dbs = true ->
      Forall2 same_bits dbs (List.map (@BYTE_Pointer Pa 8 p) (Nseq k (List.length dbs))).
  Proof.
    intros p; induction dbs as [| b bs IH]; intros k HW H; [constructor |].
    apply Forall_cons_iff in HW as [Hb Hbs].
    cbn [pointer_slice_from] in H; apply andb_true_iff in H as [H1 H2].
    cbn [List.length Nseq List.map]; constructor.
    - apply same_bits_pointer_byte; assumption.
    - replace (N.succ k) with (1 + k)%N by lia; apply IH; assumption.
  Qed.

  Lemma pointer_slice_some : forall dbs p k,
      memory_bytes_to_pointer_slice dbs = Some (p, k) -> pointer_slice_from p k dbs = true.
  Proof.
    intros dbs p k H; unfold memory_bytes_to_pointer_slice in H; cbv zeta in H.
    destruct dbs as [| b bs]; [discriminate |].
    destruct b as [q i | x | [| [q j | | y] bits]]; try discriminate;
      match type of H with
      | (if ?c then _ else _) = _ => destruct c eqn:E
      end; inversion H; subst; exact E.
  Qed.

  (** *** Mixed bits *)

  Lemma take_drop_concat_bytes : forall dbs i,
      Forall memory_byte_wf dbs -> (i < List.length dbs)%nat ->
      take 8 (drop (8 * N.of_nat i) (List.concat (List.map memory_byte_to_memory_bits dbs)))
      = memory_byte_to_memory_bits (nth i dbs poison_memory_byte).
  Proof.
    induction dbs as [| b bs IH]; intros i HW Hi; cbn [List.length] in Hi; [lia |].
    apply Forall_cons_iff in HW as [Hb Hbs].
    pose proof (memory_byte_bits_length _ Hb) as HL.
    cbn [List.map List.concat].
    destruct i as [| i].
    - cbn [nth]; rewrite N.mul_0_r, drop_nil; apply take_app_exact; rewrite HL; reflexivity.
    - cbn [nth].
      replace (8 * N.of_nat (S i))%N with (8 + 8 * N.of_nat i)%N by lia.
      rewrite <- drop_drop, drop_app_exact by (rewrite HL; reflexivity).
      apply IH; [exact Hbs | lia].
  Qed.

  Lemma mixed_bytes_same_bits : forall dbs,
      Forall memory_byte_wf dbs ->
      Forall2 same_bits dbs
        (List.map (mixed_byte (List.concat (List.map memory_byte_to_memory_bits dbs)))
                  (Nseq 0 (List.length dbs))).
  Proof.
    intros dbs HW.
    apply (@Forall2_nth_Nseq _ _ same_bits _ poison_memory_byte); intros i Hi.
    rewrite N.add_0_l; unfold same_bits; rewrite memory_byte_to_memory_bits_mixed; cbv zeta.
    rewrite take_drop_concat_bytes by assumption.
    rewrite (memory_byte_bits_length _ (proj1 (Forall_forall _ _) HW _ (nth_In _ _ Hi))).
    replace (negb (N.of_nat 8 =? 8)%N) with false by reflexivity.
    rewrite app_nil_r; reflexivity.
  Qed.

  (** *** Integer bits *)

  Lemma no_ptr_psn_bits : forall l : list (@memory_bit Pa),
      existsb is_ptr_bit l = false -> existsb is_poison_bit l = false ->
      exists bis, l = List.map Bit_bit bis.
  Proof.
    induction l as [| b l IH]; intros H1 H2; [exists []; reflexivity |].
    destruct b as [p i | | x]; cbn in H1, H2; try discriminate.
    destruct (IH H1 H2) as [bis ->]; exists (x :: bis); reflexivity.
  Qed.

  Lemma memory_bits_to_Z_ints : forall bis : list (@bit_int 1),
      memory_bits_to_Z (List.map (@Bit_bit Pa) bis)
      = raise_ret (NoPois (concat_bits_Z (List.map unsigned bis))).
  Proof.
    intros bis; unfold memory_bits_to_Z.
    assert (M : map_monad memory_bit_to_bit (List.map (@Bit_bit Pa) bis)
                = raise_ret (NoPois (List.map unsigned bis))).
    { induction bis as [| b bis IH]; [reflexivity |].
      cbn [List.map]; rewrite map_monad_cons_EOUP, IH; reflexivity. }
    rewrite M; reflexivity.
  Qed.

  Lemma bit_unsigned_range : forall b : @bit_int 1, (0 <= unsigned b < 2 ^ 1)%Z.
  Proof.
    intros b; pose proof (unsigned_range b) as H.
    replace (2 ^ 1)%Z with (@modulus 1) by reflexivity; exact H.
  Qed.

  Lemma same_bits_int_byte : forall b z,
      memory_byte_wf b ->
      existsb is_ptr_bit (memory_byte_to_memory_bits b) = false ->
      existsb is_poison_bit (memory_byte_to_memory_bits b) = false ->
      memory_byte_to_Z b = raise_ret (NoPois z) ->
      same_bits b (@BYTE_I Pa 8 (repr z)).
  Proof.
    intros [p i | y | bits] z Hw H1 H2 Hz.
    - rewrite BYTE_Pointer_bits in H1; cbn in H1; discriminate.
    - cbn [memory_byte_to_Z] in Hz; inversion Hz; subst z.
      cbn [repr unsigned VInt_Bounded]; rewrite Integers.repr_unsigned; reflexivity.
    - cbn [memory_byte_to_memory_bits memory_byte_wf] in Hw, H1, H2.
      destruct (no_ptr_psn_bits _ H1 H2) as [bis ->].
      cbn [memory_byte_to_Z] in Hz; rewrite memory_bits_to_Z_ints in Hz.
      inversion Hz; subst z; clear Hz.
      rewrite length_map in Hw.
      assert (HF : Forall (fun u => 0 <= u < 2 ^ 1)%Z (List.map unsigned bis)).
      { apply Forall_forall; intros u Hu; apply in_map_iff in Hu as (b & <- & _).
        apply bit_unsigned_range. }
      pose proof (@concat_digits_range 1%Z _ ltac:(lia) HF) as [Hlo Hhi].
      rewrite length_map, Hw in Hhi.
      rewrite <- concat_bits_Z_digits in Hlo, Hhi.
      remember (concat_bits_Z (List.map unsigned bis)) as z eqn:Ez.
      unfold same_bits; rewrite BYTE_I_bits; cbn [memory_byte_to_memory_bits].
      symmetry.
      transitivity (List.map Bit_bit (List.map (fun i => nth (N.to_nat (i - 0)) bis (repr 0))
                                               (Nseq 0 (List.length bis)))).
      2:{ rewrite map_Nseq_nth; reflexivity. }
      rewrite Hw, map_map.
      apply map_ext_in; intros i Hi; apply In_Nseq in Hi; f_equal.
      rewrite extract_bit_vint_8 by lia.
      (* bit [i] of [z] is the [i]th bit *)
      pose proof (@concat_digits_nth 1%Z (List.map unsigned bis) (N.to_nat i)
                    ltac:(lia) HF ltac:(rewrite length_map, Hw; lia)) as Hn.
      rewrite <- concat_bits_Z_digits, <- Ez, Z.pow_1_r in Hn.
      replace (1 * Z.of_nat (N.to_nat i))%Z with (Z.of_N i) in Hn by lia.
      cbn [repr unsigned VInt_Bounded] in *.
      rewrite Integers.unsigned_repr_eq.
      replace (@Integers.modulus 8) with 256%Z by reflexivity.
      subst z.
      rewrite (Z.mod_small (concat_bits_Z _)) by (cbn in Hhi; lia).
      rewrite Hn, N.sub_0_r.
      replace (nth (N.to_nat i) (List.map Integers.unsigned bis) 0%Z)
        with (Integers.unsigned (nth (N.to_nat i) bis (Integers.repr 0)))
        by (rewrite <- (map_nth Integers.unsigned); reflexivity).
      apply Integers.repr_unsigned.
  Qed.

  (** *** A whole integer's bytes *)

  (* the value of a byte that has no poison bits *)
  Definition byte_val (b : memory_byte) : Z :=
    match memory_byte_to_Z b with
    | raise_ret (NoPois z) => z
    | _ => 0%Z
    end.

  Lemma memory_byte_to_Z_no_psn : forall b,
      existsb is_poison_bit (memory_byte_to_memory_bits b) = false ->
      memory_byte_to_Z b = raise_ret (NoPois (byte_val b)).
  Proof.
    intros b H; unfold byte_val.
    destruct b as [p i | y | bits]; cbn [memory_byte_to_Z]; try reflexivity.
    cbn [memory_byte_to_memory_bits] in H.
    unfold memory_bits_to_Z.
    assert (M : exists zs, map_monad memory_bit_to_bit bits = raise_ret (NoPois zs)).
    { induction bits as [| c bits IH]; [eexists; reflexivity |].
      cbn [existsb] in H; apply orb_false_iff in H as [Hc Hr].
      destruct (IH Hr) as [zs Ezs].
      rewrite map_monad_cons_EOUP, Ezs.
      destruct c; cbn in Hc; try discriminate; cbn; eexists; reflexivity. }
    destruct M as [zs ->]; reflexivity.
  Qed.

  Lemma byte_val_range : forall b,
      memory_byte_wf b ->
      existsb is_ptr_bit (memory_byte_to_memory_bits b) = false ->
      existsb is_poison_bit (memory_byte_to_memory_bits b) = false ->
      (0 <= byte_val b < 256)%Z.
  Proof.
    intros [p i | y | bits] Hw H1 H2.
    - rewrite BYTE_Pointer_bits in H1; cbn in H1; discriminate.
    - unfold byte_val; cbn [memory_byte_to_Z].
      pose proof (unsigned_range y) as H; exact H.
    - cbn [memory_byte_to_memory_bits memory_byte_wf] in Hw, H1, H2.
      destruct (no_ptr_psn_bits _ H1 H2) as [bis ->].
      unfold byte_val; cbn [memory_byte_to_Z]; rewrite memory_bits_to_Z_ints.
      rewrite length_map in Hw.
      assert (HF : Forall (fun u => 0 <= u < 2 ^ 1)%Z (List.map unsigned bis)).
      { apply Forall_forall; intros u Hu; apply in_map_iff in Hu as (b & <- & _).
        apply bit_unsigned_range. }
      pose proof (@concat_digits_range 1%Z _ ltac:(lia) HF) as [Hlo Hhi].
      rewrite length_map, Hw in Hhi; cbv beta iota; rewrite concat_bits_Z_digits.
      cbn in Hhi; cbn [unsigned VInt_Bounded] in *; lia.
  Qed.

  Lemma map_monad_byte_to_Z_no_psn : forall dbs,
      (forall b, In b dbs -> existsb is_poison_bit (memory_byte_to_memory_bits b) = false) ->
      map_monad memory_byte_to_Z dbs = raise_ret (NoPois (List.map byte_val dbs)).
  Proof.
    induction dbs as [| b bs IH]; intros H; [reflexivity |].
    rewrite map_monad_cons_EOUP, memory_byte_to_Z_no_psn by (apply H; now left).
    rewrite IH by (intros; apply H; now right); reflexivity.
  Qed.

  Lemma extract_byte_vint_concat : forall sz zs i,
      (8 * Z.of_nat (List.length zs) = Z.pos sz)%Z ->
      Forall (fun z => 0 <= z < 256)%Z zs ->
      (i < List.length zs)%nat ->
      extract_byte_vint (repr (concat_bytes_Z zs) : @bit_int sz) (N.of_nat i)
      = nth i zs 0%Z.
  Proof.
    intros sz zs i Hlen HF Hi.
    assert (HF' : Forall (fun z => 0 <= z < 2 ^ 8)%Z zs)
      by (eapply Forall_impl; [| exact HF]; cbn; lia).
    pose proof (@concat_digits_range 8%Z zs ltac:(lia) HF') as [Hlo Hhi].
    rewrite <- concat_bytes_Z_digits, Hlen in Hhi.
    rewrite <- concat_bytes_Z_digits in Hlo.
    rewrite extract_byte_vint_spec by (rewrite nat_N_Z; lia).
    assert (Hm : (@Integers.modulus sz = 2 ^ Z.pos sz)%Z)
      by (rewrite Integers.modulus_def; apply two_power_pos_eq).
    cbn [unsigned repr VInt_Bounded]; rewrite Integers.unsigned_repr_eq, Hm.
    rewrite (Z.mod_small (concat_bytes_Z zs)) by lia.
    rewrite concat_bytes_Z_digits.
    rewrite nat_N_Z.
    replace 256%Z with (2 ^ 8)%Z by reflexivity.
    apply concat_digits_nth; [lia | exact HF' | exact Hi].
  Qed.

  Lemma int_bytes_same_bits : forall sz dbs,
      Forall memory_byte_wf dbs ->
      (8 * N.of_nat (List.length dbs) = Npos sz)%N ->
      existsb is_ptr_bit (List.concat (List.map memory_byte_to_memory_bits dbs)) = false ->
      existsb is_poison_bit (List.concat (List.map memory_byte_to_memory_bits dbs)) = false ->
      Forall2 same_bits dbs
        (List.map (memory_byte_of_dvalue_bv
                     (BYTE_I (repr (concat_bytes_Z (List.map byte_val dbs)) : @bit_int sz)))
                  (Nseq 0 (List.length dbs))).
  Proof.
    intros sz dbs HW Hlen Hp Hs.
    assert (Hin : forall b, In b dbs ->
                  memory_byte_wf b
                  /\ existsb is_ptr_bit (memory_byte_to_memory_bits b) = false
                  /\ existsb is_poison_bit (memory_byte_to_memory_bits b) = false).
    { intros b Hb; split; [eapply Forall_forall; eauto |].
      split; eapply existsb_concat_map; eauto. }
    assert (HR : Forall (fun z => 0 <= z < 256)%Z (List.map byte_val dbs)).
    { apply Forall_forall; intros z Hz; apply in_map_iff in Hz as (b & <- & Hb).
      destruct (Hin b Hb) as (Hw & H1 & H2); apply byte_val_range; assumption. }
    apply (@Forall2_nth_Nseq _ _ same_bits _ poison_memory_byte); intros i Hi.
    rewrite N.add_0_l.
    cbn [memory_byte_of_dvalue_bv].
    rewrite extract_byte_vint_concat;
      [| rewrite length_map; lia | exact HR | rewrite length_map; exact Hi].
    change 0%Z with (byte_val poison_memory_byte) at 1.
    rewrite map_nth.
    destruct (Hin _ (nth_In _ poison_memory_byte Hi)) as (Hw & H1 & H2).
    apply same_bits_int_byte; try assumption.
    apply memory_byte_to_Z_no_psn; exact H2.
  Qed.

  (** *** The bit-level reading at a whole-byte width *)

  Lemma bits_value_same_bits : forall sz dbs,
      Forall memory_byte_wf dbs ->
      (8 * N.of_nat (List.length dbs) = Npos sz)%N ->
      Forall2 same_bits dbs
        (List.map (memory_byte_of_dvalue_bv (memory_bytes_to_bits_value sz dbs))
                  (Nseq 0 (List.length dbs))).
  Proof.
    intros sz dbs HW Hlen.
    assert (H8 : (Npos sz mod 8 = 0)%N)
      by (rewrite <- Hlen, N.mul_comm; apply N.Div0.mod_mul).
    unfold memory_bytes_to_bits_value; cbv zeta.
    rewrite reader_bits_fwd, (get_bits_fwd_concat HW Hlen).
    destruct (existsb is_ptr_bit (List.concat (List.map memory_byte_to_memory_bits dbs))
              || existsb is_poison_bit (List.concat (List.map memory_byte_to_memory_bits dbs)))%bool
      eqn:Emix.
    - erewrite map_ext by (intros idx; apply writer_mixed_byte).
      apply mixed_bytes_same_bits; exact HW.
    - apply orb_false_iff in Emix as [Hp Hs].
      assert (Hint : memory_bytes_to_int sz dbs
                     = raise_ret (NoPois (concat_bytes_Z (List.map byte_val dbs)))).
      { unfold memory_bytes_to_int; cbv zeta; rewrite H8; cbn [negb N.eqb].
        rewrite map_monad_byte_to_Z_no_psn; [reflexivity |].
        intros b Hb; eapply existsb_concat_map; eauto. }
      rewrite Hint.
      apply int_bytes_same_bits; assumption.
  Qed.

  Lemma bits_value_all_poison : forall sz dbs,
      Forall memory_byte_wf dbs ->
      (8 * N.of_nat (List.length dbs) = Npos sz)%N ->
      dvalue_bv_all_poison (memory_bytes_to_bits_value sz dbs) = true ->
      forallb is_all_poison_byte dbs = true.
  Proof.
    intros sz dbs HW Hlen H.
    unfold memory_bytes_to_bits_value in H; cbv zeta in H.
    rewrite reader_bits_fwd, (get_bits_fwd_concat HW Hlen) in H.
    destruct (existsb is_ptr_bit (List.concat (List.map memory_byte_to_memory_bits dbs))
              || existsb is_poison_bit (List.concat (List.map memory_byte_to_memory_bits dbs)))%bool;
      [| destruct (memory_bytes_to_int sz dbs) as [| | | [x |]]; discriminate].
    cbn [dvalue_bv_all_poison] in H.
    apply forallb_forall; intros b Hb.
    pose proof (forallb_concat_map _ _ _ _ H Hb) as Hbits.
    destruct b as [p i | y | bits]; cbn [is_all_poison_byte].
    - rewrite BYTE_Pointer_bits in Hbits; cbn in Hbits; discriminate.
    - rewrite BYTE_I_bits in Hbits; cbn in Hbits; discriminate.
    - cbn [memory_byte_to_memory_bits] in Hbits; exact Hbits.
  Qed.

  (** *** The round trip at one type

      [rt_bytes dt mb dv]: if [dv] (read from [mb]) is poison then [mb] was
      all poison, and writing [dv] back reproduces [mb]'s bits.  The first
      half is what an aggregate needs when [canonicalize_agg] turns a value
      of all-poison elements into [DVALUE_Poison]. *)
  Definition rt_bytes (dt : dtyp) (mb : list memory_byte) (dv : dvalue) : Prop :=
    (dv = DVALUE_Base DVALUE_Poison -> forallb is_all_poison_byte mb = true) /\
    (forall acc o bs,
        acc_dvalue_to_memory_bytes_h dt dv 0%N None acc = ret (o, bs) ->
        exists w, bs = w ++ acc /\ Forall2 same_bits mb (rev w)).

  Lemma rt_bytes_poison : forall dt mb,
      byte_layout dt -> Forall memory_byte_wf mb ->
      N.of_nat (List.length mb) = store_size_dtyp dt ->
      forallb is_all_poison_byte mb = true ->
      rt_bytes dt mb (DVALUE_Base DVALUE_Poison).
  Proof.
    intros dt mb HL HW Hlen HP; split; [intros _; exact HP |].
    intros acc o bs H; apply write_poison_layout in H; [| exact HL].
    eexists; split; [exact H |].
    rewrite rev_repeat, <- Hlen, Nnat.Nat2N.id.
    apply same_bits_all_poison; assumption.
  Qed.

  Lemma rt_bytes_B : forall sz mb dv,
      (Npos sz mod 8 = 0)%N -> Forall memory_byte_wf mb ->
      N.of_nat (List.length mb) = store_size_dtyp (DTYPE_Base (DTYPE_B sz)) ->
      memory_bytes_to_dvalue mb (DTYPE_Base (DTYPE_B sz)) = ret dv ->
      rt_bytes (DTYPE_Base (DTYPE_B sz)) mb dv.
  Proof.
    intros sz mb dv H8 HW Hlen H.
    assert (Hlen8 : (8 * N.of_nat (List.length mb) = Npos sz)%N)
      by (rewrite Hlen; apply store_size_B_bytes; exact H8).
    cbn [memory_bytes_to_dvalue] in H.
    rewrite take_all in H by lia.
    cbn [memory_bytes_to_dvalue_base] in H.
    destruct (all_poison_bytes mb) eqn:Eap.
    { cbn in H; inversion H; subst dv.
      apply rt_bytes_poison; [exact H8 | exact HW | exact Hlen |].
      rewrite <- all_poison_bytes_forallb; exact Eap. }
    destruct (memory_bytes_to_byte_value sz mb) as [| | | bv] eqn:Eb; cbn in H;
      try discriminate.
    destruct (dvalue_bv_all_poison bv) eqn:Ep; cbn in H; inversion H; subst dv; clear H.
    - (* all the value's bits are poison: so are all its bytes *)
      apply rt_bytes_poison; [exact H8 | exact HW | exact Hlen |].
      unfold memory_bytes_to_byte_value in Eb.
      destruct (memory_bytes_to_pointer_slice mb) as [[p k] |] eqn:Es;
        [destruct (pointer_chunk_aligned sz k) |]; cbn in Eb; inversion Eb; subst bv;
        [discriminate | |]; eapply bits_value_all_poison; eauto.
    - split; [discriminate |].
      intros acc o bs Hw; apply write_base_block in Hw.
      eexists; split; [exact Hw |].
      rewrite rev_involutive; cbn [base_byte_gen].
      rewrite <- Hlen, Nnat.Nat2N.id.
      unfold memory_bytes_to_byte_value in Eb.
      destruct (memory_bytes_to_pointer_slice mb) as [[p k] |] eqn:Es.
      + destruct (pointer_chunk_aligned sz k) eqn:Ea; cbn in Eb; inversion Eb; subst bv.
        * (* a whole aligned chunk of [p], starting at byte [k] *)
          unfold pointer_chunk_aligned in Ea; apply andb_true_iff in Ea as [_ Ea].
          apply N.eqb_eq in Ea.
          assert (Hk : (Npos sz * ((k * 8) / Npos sz) / 8 = k)%N).
          { pose proof (proj2 (N.Div0.div_exact (k * 8) (Npos sz)) Ea) as E.
            rewrite <- E; apply N.div_mul; lia. }
          erewrite map_ext with (g := fun idx => @BYTE_Pointer Pa 8 p (k + idx)%N)
            by (intros idx; cbn [memory_byte_of_dvalue_bv]; rewrite Hk; reflexivity).
          rewrite (map_Nseq_shift (@BYTE_Pointer Pa 8 p) _ 0 k), N.add_0_r.
          apply pointer_slice_from_same_bits; [exact HW | apply pointer_slice_some; exact Es].
        * apply bits_value_same_bits; assumption.
      + cbn in Eb; inversion Eb; subst bv; apply bits_value_same_bits; assumption.
  Qed.

  (** *** Aggregates *)

  (* the reader's element loop against the writer's, with no padding: each
     element reads its own [store_size] chunk and writes it back *)
  Lemma read_array_loop_bytes : forall t np n offset dbs elts,
      byte_layout t ->
      (forall chunk v, Forall memory_byte_wf chunk ->
          N.of_nat (List.length chunk) = store_size_dtyp t ->
          memory_bytes_to_dvalue chunk t = ret v -> rt_bytes t chunk v) ->
      Forall memory_byte_wf dbs ->
      N.of_nat (List.length dbs) = (N.of_nat n * store_size_dtyp t)%N ->
      forallb is_all_poison_byte (take (np - offset) dbs) = true ->
      read_array_loop memory_bytes_to_dvalue np (store_size_dtyp t) t n offset dbs
      = ret elts ->
      (forallb dvalue_is_poison elts = true -> forallb is_all_poison_byte dbs = true) /\
      (forall offset' acc o bs,
          array_bytes_loop acc_dvalue_to_memory_bytes_h None t 0%N elts offset' acc
          = ret (o, bs) ->
          exists w, bs = w ++ acc /\ Forall2 same_bits dbs (rev w)).
  Proof.
    intros t np; induction n as [| n IH]; intros offset dbs elts HL Hel HW Hlen Hpre H.
    - cbn in H; inversion H; subst elts; clear H.
      destruct dbs as [| b dbs]; [| cbn [List.length] in Hlen; lia].
      split; [reflexivity |].
      intros offset' acc o bs Hw; rewrite array_bytes_loop_nil in Hw;
        cbn [accumulate_padding] in Hw.
      inversion Hw; subst; exists []; split; [reflexivity | constructor].
    - rewrite read_array_loop_cons in H.
      apply EOU_bind_ret_inv in H as (e & Ee & H).
      apply EOU_bind_ret_inv in H as (rest & Er & H).
      cbn in H; inversion H; subst elts; clear H.
      set (ssz := store_size_dtyp t) in *.
      assert (Hcl : N.of_nat (List.length (take ssz dbs)) = ssz)
        by (apply take_length_exact; lia).
      assert (Htl : N.of_nat (List.length (drop ssz dbs)) = (N.of_nat n * ssz)%N)
        by (rewrite length_drop_N; lia).
      assert (HWc : Forall memory_byte_wf (take ssz dbs)) by (apply Forall_take_N, HW).
      assert (HWt : Forall memory_byte_wf (drop ssz dbs)) by (apply Forall_drop_N, HW).
      (* the element: read, or skipped as lying in the poison prefix *)
      assert (He : rt_bytes t (take ssz dbs) e).
      { destruct (N.leb_spec (offset + ssz) np) as [Hle | Hgt].
        - cbn in Ee; inversion Ee; subst e.
          apply rt_bytes_poison; [exact HL | exact HWc | exact Hcl |].
          rewrite <- (@drop_nil _ dbs) at 1.
          apply forallb_sub with (n := (np - offset)%N); [lia | exact Hpre].
        - apply Hel; assumption. }
      (* the rest *)
      assert (Hpre' : forallb is_all_poison_byte (take (np - (offset + ssz)) (drop ssz dbs))
                      = true).
      { destruct (N.leb_spec (offset + ssz) np).
        - apply forallb_sub with (n := (np - offset)%N); [lia | exact Hpre].
        - replace (np - (offset + ssz))%N with 0%N by lia; rewrite take_nil; reflexivity. }
      destruct (IH (offset + ssz)%N (drop ssz dbs) rest HL Hel HWt Htl Hpre' Er)
        as [IH1 IH2].
      split.
      + cbn [forallb]; intros Hp; apply andb_true_iff in Hp as [Hp1 Hp2].
        rewrite <- (@take_drop_app _ ssz dbs), forallb_app.
        apply andb_true_iff; split;
          [apply (proj1 He), dvalue_is_poison_true, Hp1 | apply IH1, Hp2].
      + intros offset' acc o bs Hw.
        rewrite array_bytes_loop_cons in Hw.
        apply EOU_bind_ret_inv in Hw as ([coff cbs] & Ec & Hw).
        destruct (proj2 He _ _ _ Ec) as (w1 & -> & Hs1).
        rewrite accumulate_padding_bytes_shape in Hw; cbn [N.to_nat List.repeat app] in Hw.
        destruct (IH2 _ _ _ _ Hw) as (w2 & -> & Hs2).
        exists (w2 ++ w1); split; [rewrite app_assoc; reflexivity |].
        rewrite rev_app_distr, <- (@take_drop_app _ ssz dbs).
        apply Forall2_app; assumption.
  Qed.

  (* the same for a packed struct, whose fields take no padding when their
     alloc and store sizes agree *)
  Lemma read_struct_loop_bytes : forall np dts offset dbs vs,
      FORALL (fun t => byte_layout t /\ alloc_size_dtyp t = store_size_dtyp t) dts ->
      (forall t, In t dts -> forall chunk v, Forall memory_byte_wf chunk ->
          N.of_nat (List.length chunk) = store_size_dtyp t ->
          memory_bytes_to_dvalue chunk t = ret v -> rt_bytes t chunk v) ->
      Forall memory_byte_wf dbs ->
      N.of_nat (List.length dbs)
      = fold_right (fun t acc => (store_size_dtyp t + acc)%N) 0%N dts ->
      forallb is_all_poison_byte (take (np - offset) dbs) = true ->
      read_struct_loop memory_bytes_to_dvalue np None offset dts dbs = ret vs ->
      (forallb dvalue_is_poison vs = true -> forallb is_all_poison_byte dbs = true) /\
      (forall offset' acc o bs,
          struct_bytes_loop acc_dvalue_to_memory_bytes_h None None vs dts offset' acc
          = ret (o, bs) ->
          exists w, bs = w ++ acc /\ Forall2 same_bits dbs (rev w)).
  Proof.
    intros np; induction dts as [| t ts IH]; intros offset dbs vs HL Hel HW Hlen Hpre H.
    - cbn in H; inversion H; subst vs; clear H.
      destruct dbs as [| b dbs]; [| cbn [List.length fold_right] in Hlen; lia].
      split; [reflexivity |].
      intros offset' acc o bs Hw; rewrite struct_bytes_loop_nil in Hw;
        cbn [accumulate_padding] in Hw.
      inversion Hw; subst; exists []; split; [reflexivity | constructor].
    - cbn [FORALL fold_right] in HL, Hlen; destruct HL as [[HLt Htight] HLs].
      rewrite read_struct_loop_cons in H; cbv zeta in H.
      rewrite drop_nil, N.add_0_r, Htight in H.
      apply EOU_bind_ret_inv in H as (f & Ef & H).
      apply EOU_bind_ret_inv in H as (rest & Er & H).
      cbn in H; inversion H; subst vs; clear H.
      set (ssz := store_size_dtyp t) in *.
      assert (Hcl : N.of_nat (List.length (take ssz dbs)) = ssz)
        by (apply take_length_exact; lia).
      assert (Htl : N.of_nat (List.length (drop ssz dbs))
                    = fold_right (fun t acc => (store_size_dtyp t + acc)%N) 0%N ts)
        by (rewrite length_drop_N; lia).
      assert (HWc : Forall memory_byte_wf (take ssz dbs)) by (apply Forall_take_N, HW).
      assert (HWt : Forall memory_byte_wf (drop ssz dbs)) by (apply Forall_drop_N, HW).
      assert (Hf : rt_bytes t (take ssz dbs) f).
      { destruct (N.leb_spec (offset + ssz) np) as [Hle | Hgt].
        - cbn in Ef; inversion Ef; subst f.
          apply rt_bytes_poison; [exact HLt | exact HWc | exact Hcl |].
          rewrite <- (@drop_nil _ dbs) at 1.
          apply forallb_sub with (n := (np - offset)%N); [lia | exact Hpre].
        - apply (Hel t (or_introl eq_refl)); assumption. }
      assert (Hpre' : forallb is_all_poison_byte (take (np - (offset + ssz)) (drop ssz dbs))
                      = true).
      { destruct (N.leb_spec (offset + ssz) np).
        - apply forallb_sub with (n := (np - offset)%N); [lia | exact Hpre].
        - replace (np - (offset + ssz))%N with 0%N by lia; rewrite take_nil; reflexivity. }
      destruct (IH (offset + ssz)%N (drop ssz dbs) rest HLs
                  (fun u Hu => Hel u (or_intror Hu)) HWt Htl Hpre' Er) as [IH1 IH2].
      split.
      + cbn [forallb]; intros Hp; apply andb_true_iff in Hp as [Hp1 Hp2].
        rewrite <- (@take_drop_app _ ssz dbs), forallb_app.
        apply andb_true_iff; split;
          [apply (proj1 Hf), dvalue_is_poison_true, Hp1 | apply IH1, Hp2].
      + intros offset' acc o bs Hw.
        rewrite struct_bytes_loop_cons in Hw; cbn [accumulate_padding] in Hw.
        apply EOU_bind_ret_inv in Hw as ([coff cbs] & Ec & Hw).
        destruct (proj2 Hf _ _ _ Ec) as (w1 & -> & Hs1).
        rewrite Htight, N.sub_diag, accumulate_padding_bytes_shape in Hw;
          cbn [N.to_nat List.repeat app] in Hw.
        destruct (IH2 _ _ _ _ Hw) as (w2 & -> & Hs2).
        exists (w2 ++ w1); split; [rewrite app_assoc; reflexivity |].
        rewrite rev_app_distr, <- (@take_drop_app _ ssz dbs).
        apply Forall2_app; assumption.
  Qed.

  Lemma packed_extent_store : forall dts,
      FORALL (fun t => byte_layout t /\ alloc_size_dtyp t = store_size_dtyp t) dts ->
      struct_fields_extent true dts
      = fold_right (fun t acc => (store_size_dtyp t + acc)%N) 0%N dts.
  Proof.
    intros dts H; unfold struct_fields_extent; cbv beta iota.
    rewrite fold_left_add_right, N.add_0_l.
    induction dts as [| t ts IH]; [reflexivity |].
    cbn [FORALL fold_right] in H |- *; destruct H as [[_ Ht] Hs].
    rewrite Ht, IH by exact Hs; reflexivity.
  Qed.

  (** *** The theorem *)
  Lemma bytes_round_trip_h : forall dt,
      byte_layout dt ->
      forall mb dv, Forall memory_byte_wf mb ->
      N.of_nat (List.length mb) = store_size_dtyp dt ->
      memory_bytes_to_dvalue mb dt = ret dv ->
      rt_bytes dt mb dv.
  Proof.
    induction dt as [db | pk dts IH | vv sz t IHt]; intros HL mb dv HW Hlen H.
    - destruct db; cbn in HL; try contradiction.
      apply rt_bytes_B; assumption.
    - destruct pk; cbn in HL; [| contradiction].
      rewrite read_struct_unfold in H.
      pose proof (poison_split_prefix mb) as Hpre.
      destruct (poison_split mb) as [np rest] eqn:Eps; cbn [fst] in Hpre.
      destruct rest as [| b rest].
      { cbn in H; inversion H; subst dv.
        apply rt_bytes_poison; [exact HL | exact HW | exact Hlen |].
        rewrite <- all_poison_bytes_forallb; unfold all_poison_bytes; rewrite Eps; reflexivity. }
      destruct (read_struct_loop memory_bytes_to_dvalue np None 0%N dts mb)
        as [| | | vs] eqn:Ev; cbn in H; try discriminate.
      inversion H; subst dv; clear H.
      assert (Hel : forall t, In t dts -> forall chunk v, Forall memory_byte_wf chunk ->
                  N.of_nat (List.length chunk) = store_size_dtyp t ->
                  memory_bytes_to_dvalue chunk t = ret v -> rt_bytes t chunk v).
      { intros t Ht chunk v HWc Hc Hv.
        apply FORALL_forall in HL.
        apply (IH t Ht); [apply (proj1 (Forall_forall _ _) HL t Ht) | | |]; assumption. }
      assert (Hlen' : N.of_nat (List.length mb)
                      = fold_right (fun t acc => (store_size_dtyp t + acc)%N) 0%N dts)
        by (rewrite Hlen, store_size_dtyp_Packed_struct; apply packed_extent_store, HL).
      destruct (@read_struct_loop_bytes np dts 0%N mb vs HL Hel HW Hlen'
                  ltac:(rewrite N.sub_0_r; exact Hpre) Ev) as [L1 L2].
      unfold canonicalize_agg.
      destruct (forallb dvalue_is_poison vs) eqn:Ep.
      + apply rt_bytes_poison; [exact HL | exact HW | exact Hlen | apply L1; reflexivity].
      + split; [discriminate |].
        intros acc o bs Hw; rewrite ser_struct_unfold in Hw.
        exact (L2 0%N acc o bs Hw).
    - assert (HLt : byte_layout t) by (destruct vv; cbn in HL; tauto).
      assert (Hstride : (if vv then store_size_dtyp t else alloc_size_dtyp t)
                        = store_size_dtyp t)
        by (destruct vv; cbn in HL; [reflexivity | tauto]).
      assert (Hpad : (if vv then 0%N else (alloc_size_dtyp t - store_size_dtyp t)%N) = 0%N)
        by (destruct vv; cbn in HL; [reflexivity | destruct HL as [_ ->]; lia]).
      assert (Hlen' : N.of_nat (List.length mb) = (N.of_nat (N.to_nat sz) * store_size_dtyp t)%N).
      { rewrite Nnat.N2Nat.id, Hlen.
        destruct vv; [apply store_size_dtyp_vector |].
        rewrite store_size_dtyp_array; cbn in HL; destruct HL as [_ ->]; reflexivity. }
      rewrite read_array_unfold, Hstride in H.
      pose proof (poison_split_prefix mb) as Hpre.
      destruct (poison_split mb) as [np rest] eqn:Eps; cbn [fst] in Hpre.
      destruct rest as [| b rest].
      { cbn in H; inversion H; subst dv.
        apply rt_bytes_poison; [exact HL | exact HW | exact Hlen |].
        rewrite <- all_poison_bytes_forallb; unfold all_poison_bytes; rewrite Eps; reflexivity. }
      apply EOU_bind_ret_inv in H as (elts & Ee & H).
      cbn in H; inversion H; subst dv; clear H.
      assert (Hel : forall chunk v, Forall memory_byte_wf chunk ->
                  N.of_nat (List.length chunk) = store_size_dtyp t ->
                  memory_bytes_to_dvalue chunk t = ret v -> rt_bytes t chunk v)
        by (intros chunk v HWc Hc Hv; apply IHt; assumption).
      destruct (@read_array_loop_bytes t np (N.to_nat sz) 0%N mb elts HLt Hel HW Hlen'
                  ltac:(rewrite N.sub_0_r; exact Hpre) Ee) as [L1 L2].
      unfold canonicalize_agg.
      destruct (forallb dvalue_is_poison elts) eqn:Ep.
      + apply rt_bytes_poison; [exact HL | exact HW | exact Hlen | apply L1; reflexivity].
      + split; [discriminate |].
        intros acc o bs Hw; rewrite ser_array_unfold, Hpad in Hw.
        exact (L2 0%N acc o bs Hw).
  Qed.

  (** Reading bytes at a padding-free byte type and writing the value back
      reproduces them, bit for bit: pointer bits with their provenance, and
      poison bits. *)
  Theorem memory_bytes_round_trip_bytes : forall dt mb dv mb',
      byte_layout dt ->
      Forall memory_byte_wf mb ->
      N.of_nat (List.length mb) = store_size_dtyp dt ->
      memory_bytes_to_dvalue mb dt = ret dv ->
      dvalue_to_memory_bytes dt dv None = ret mb' ->
      Forall2 same_bits mb mb'.
  Proof.
    intros dt mb dv mb' HL HW Hlen H1 H2.
    unfold dvalue_to_memory_bytes in H2.
    apply EOU_bind_ret_inv in H2 as ([o bs] & E & H2).
    cbn in H2; inversion H2; subst mb'; clear H2.
    destruct (proj2 (@bytes_round_trip_h dt HL mb dv HW Hlen H1) _ _ _ E) as (w & -> & Hs).
    rewrite app_nil_r, rev_append_rev, app_nil_r; exact Hs.
  Qed.

End MemoryByteFacts.
