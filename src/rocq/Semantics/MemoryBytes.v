From Vellvm Require Import
  Utils
  Numeric
  Syntax
  Params
  DynamicValues
  EOU
  VellvmIntegers.

From ExtLib Require Import
  Data.Monads.EitherMonad.
Open Scope N_scope.


(* TODO: Make these take endianess into account.

         Can probably use bitwidth from VInt to do big-endian...
 *)
Definition extract_bit_vint {I} `{VInt I} (i : I) (idx : N) : Z
  := unsigned (modu (shru i (repr (Z.of_N idx))) (repr 2)).

Fixpoint concat_bits_vint {I} `{VInt I} (bits : list I) : I
  := match bits with
     | [] => repr 0
     | (bit::bits) =>
         add bit (shl (concat_bits_vint bits) (repr 1))
     end.

Definition extract_byte_vint {I} `{VInt I} (i : I) (idx : N) : Z
  := unsigned (modu (shru i (repr ((Z.of_N idx) * 8))) (repr 256)).

Fixpoint concat_bytes_vint {I} `{VInt I} (bytes : list I) : I
  := match bytes with
     | [] => repr 0
     | (byte::bytes) =>
         add byte (shl (concat_bytes_vint bytes) (repr 8))
     end.

(* TODO: Endianess *)
Definition extract_bit_Z (x:Z) (idx : N) : Z :=
  (Z.shiftr x (Z.of_N idx)) mod 2.

Definition extract_bit_N (x:N) (idx : N) : N :=
  (N.shiftr x idx) mod 2.

(* TODO: Endianess *)
Definition concat_bits_Z_vint {I} `{VInt I} (bits : list Z) : I
  := concat_bits_vint (map repr bits).

(* TODO: does this work correctly with negative x? *)
Definition extract_byte_Z (x : Z) (idx : N) : Z
  := (Z.shiftr x ((Z.of_N idx) * 8)) mod 256.

(* TODO: Endianess *)
Definition concat_bytes_Z_vint {I} `{VInt I} (bytes : list Z) : I
  := concat_bytes_vint (map repr bytes).

Fixpoint concat_bits_Z (bits : list Z) : Z
  := match bits with
     | [] => 0
     | (bit::bits) =>
         bit + (Z.shiftl (concat_bits_Z bits) 1)
     end.

(* TODO: Endianess *)
Fixpoint concat_bytes_Z (bytes : list Z) : Z
  := match bytes with
     | [] => 0
     | (byte::bytes) =>
         byte + (Z.shiftl (concat_bytes_Z bytes) 8)
     end.

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

Lemma two_power_pos_eq : forall p, two_power_pos p = (2 ^ Z.pos p)%Z.
Proof. intros p; rewrite two_power_pos_equiv; reflexivity. Qed.

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

Section MemoryByte.
  Context {Pa : Params}.

  (* Memory bytes are dvalue_bv values of 8 memory_bits.

     BYTE_Pointer p i -  represents i'th byte of pointer p, no poison bits
     BYTE_I x - is an 8-bit integral value, no poison bits
     BYTE_Mixed 8 bits -
        bits is a length 8 list that represents a combination of bits,
        pointers, poison
        Note that, unlike in the LLVM Side, it is valid to have all of
        the bits be poison.
   *)
  Definition memory_byte : Type := @dvalue_bv Pa 8.

  (* A byte of poison in the memory model *)
  Definition poison_memory_byte : memory_byte :=
    BYTE_Mixed 8 (repeat Bit_psn 8).

  (* Accumulates num_bytes copies of mb.*)
  Definition accumulate_memory_bytes (mb:memory_byte) (num_bytes : N) : list memory_byte -> list memory_byte :=
    N.rev_loop_acc (fun _ => mb) num_bytes 0.

  Definition accumulate_poison_bytes (num_bytes : N) :=
    accumulate_memory_bytes poison_memory_byte num_bytes.

  (* Emit exactly [n] poison padding bytes.  Distinct from
     [accumulate_padding], which aligns an absolute offset: a field must be
     padded out to its *alloc size* by a fixed number of bytes, which is only
     the same thing when the field happens to start aligned (it does not, in a
     packed struct). *)
  Definition accumulate_padding_bytes (offset : N) (n : N) (acc : list memory_byte)
    : N * (list memory_byte) :=
    ((offset + n)%N, accumulate_poison_bytes n acc).

  (* Align an absolute offset: emit [pad_amount] poison bytes so that the
     offset becomes [pad_to align offset].  [None] means "no alignment
     requested" and is the identity. *)
  Definition accumulate_padding (offset : N) (opt_align : option N) (acc : list memory_byte)
    : N * (list memory_byte) :=
    match opt_align with
    | None => (offset, acc)
    | Some align =>
        let n := pad_amount align offset in
        ((offset + n)%N, accumulate_poison_bytes n acc)
    end.

  (* Given a type, there is a "bijection" between lists of memory bytes (of the
  right length) and dynamic values. *)

  (* Returns a memory byte at index 0 <= idx < (max 1 (bit_sz / 8)).
     If bit_sz is not divisible by 8, returns a BYTE_Mixed value with poison as the pad bits.
   *) 
  Definition memory_byte_of_dvalue_bv
    (bit_sz : positive) (bv : dvalue_bv bit_sz) (idx : N)
    : memory_byte :=
    
    match bv with
    (* num_chunks := (8 * pointer_size / bit_sz)

       0 <= idx' < num_chunks and chunk_size = bit_sz
       bits in this chunk are numbered, so they are at offset (bit_sz * idx'):
         bit_sz * idx' + [0, ..., bit_sz-1]

       Need to extract the byte numbered of these bits:
       0 <= idx < (bit_sz / 8)

       8 * idx + [0, ..., 7]

       Assuming bit_sz >= 8 (so there is at least one bytes' worth of data)
       0 <= 8 * idx < bit_sz
       we want to "drop" 8 * idx bits and "take" the next 8
       This amounts to rescaling the first  bit_sz * idx' idx

       For example if [bit_sz] = 32 (so this is a 32-bit chunk of aligned pointer data)
       and this is the chunk at idx' = 1, then it can broken into 4 sub-pointer bytes)

       "raw" pointer bytes: [p0,p1,p2,p3,p4,p5,p6,p7,p8] = DVALUE_Pointer p
       At type dvalue_bv 32:   BYTE_pointer p 0 = [p0,p1,p2,p3] i.e., bits 32 * 0 + [0,1,2,...,31]
       At type dvalue_bv 32:   BYTE_pointer p 1 = [p4,p5,p6,p7] i.e., bits 32 * 1 + [0,1,2,...,31]
       To re-index to dvalue_bv 8:
           memory_byte_of_dvalue 32 (BYTE_pointer p 0) 0 = (BYTE_Pointer p 0) 
                                                       1 = (BYTE_Pointer p 1)

           memory_byte_of_dvalue 32 (BYTE_pointer p 1) 0 = (BYTE_Pointer p 4)
           memory_byte_of_dvalue 32 (BYTE_pointer p 1) 1 = (BYTE_Pointer p 5)

       bit_sz / 8 = 4        (bit_sz * idx' )/ 8 + idx
     *)
    | BYTE_Pointer p idx' =>
        (* TODO: Case when pointer bit_sz is not a mulutiple of 8 ? *)
        BYTE_Pointer 8 p (((Npos bit_sz) * idx' / 8) + idx)
    | BYTE_I x =>
        (* LangRef ('store'): a value whose width is not a whole number of
           bytes "will be zero extended to the next larger multiple of the
           byte size" -- so the last byte is just the top bits of [x], which
           [extract_byte_vint] already fills with zeros. *)
        BYTE_I (repr (extract_byte_vint x idx))
    | BYTE_Mixed bits =>
        (* byte [idx] is bits [8*idx .. 8*idx+7]; the old [8 * N.pred idx] made
           bytes 0 and 1 identical *)
        let mbits := take 8 (drop (8 * idx) bits) in
        let pad := if negb (N.of_nat (List.length mbits) =? 8) then
                     repeat Bit_psn (8 - (List.length mbits)) else
                     []
        in
        BYTE_Mixed 8 (mbits ++ pad)
    end.

  
  (* Computes the memory byte at index [idx] of the dvalue_base.
     Only valid if 0 <= [idx] < size_of_dv_base dvalue_base.

     TODO: 
     If the size of the dv in bits is not a multiple of 8, i.e. is such that
        n = [(bit_size dv) mod 8 <> 0]
     Then the last memory_byte should be of the form
        BYTE_Mixed [Bit_bit x1, .. , Bit_bit xn, Bit_psn, .. Bit_psn]
     where 
   *)
  Definition acc_memory_bytes_of_dvalue_base (dt:dtyp_base)
    (dv:dvalue_base) (offset : N) (acc : list memory_byte)
    : N * (list memory_byte)  :=
    let byte_size := store_size_dtyp dt in
    let byte_gen := 
      match dv with
      | DVALUE_I sz x => memory_byte_of_dvalue_bv (BYTE_I x)
      | DVALUE_Iptr x => fun idx => BYTE_I (repr (extract_byte_Z (to_Z x) idx))
      | DVALUE_Pointer ptr => BYTE_Pointer 8 ptr
      | DVALUE_Float f =>  fun idx => BYTE_I (repr (extract_byte_Z (unsigned (Float32.to_bits f)) idx))
      | DVALUE_Double d => fun idx => BYTE_I (repr (extract_byte_Z (unsigned (Float.to_bits d)) idx))
      | DVALUE_Poison => fun idx => poison_memory_byte
      | DVALUE_None => fun idx => poison_memory_byte
                        (* was: raise_error "dvalue_extract_byte on DVALUE_None" *)
      | DVALUE_B sz bits => memory_byte_of_dvalue_bv bits
      end in
    (byte_size + offset, N.rev_loop_acc byte_gen byte_size 0 acc).
  
    
  (* Invariants:
     [acc] the accumulated list of memory_bytes so far is in _reverse_ order.
     [offset] is the offset in bytes of the next byte to be accumulated
         it is used to decide when to accumulate padding
     [pad_to] gives an (option) target that determines the amount of padding
         added to the end of the dvalue.



            (* Handle padding at the end of the structure *)
            let padding :=
              match pad with
              | Some max_pad
                => Sizeof.pad_amount max_pad offset
              | None =>
                  0%N
              end
            in
            if N.ltb  padding
            then
              (* Indexing into padding bytes *)
              (* TODO: currently we pad with poison bytes. *)
              ret poison_memory_byte
            else
              raise_error "No fields left for byte-indexing..."

   *)
  Fixpoint acc_dvalue_to_memory_bytes_h
    (dt:dtyp)
    (dv : dvalue) (offset : N)
    (tail_align : option N) (acc : list memory_byte)
    {struct dv}
    : EOU (N * (list memory_byte)) :=
    (* [pad] is [Some a] for an unpacked struct (a = its own alignment) and
       [None] for a packed one.  Each field is laid out as LLVM's
       [StructLayout] does: align the offset (unpacked only), emit the field,
       then pad it out to its *alloc* size.  The [], [] case emits the
       struct's own tail padding, which is part of its store size. *)
    let accumulate_struct_bytes (pad : option N) : list dvalue -> list dtyp -> N -> list memory_byte -> EOU (N * list memory_byte) :=
      fix loop fields types (offset : N) (acc : list memory_byte) {struct fields} : EOU (N * list memory_byte) :=
        match fields, types with
        | [], [] =>
            let '(offset, acc) := accumulate_padding offset pad acc in
            ret (accumulate_padding offset tail_align acc)
        | f::fs, dt::dts =>
            let a := preferred_alignment (dtyp_alignment dt) in
            (* [alloc_size_dtyp] recomputes [store_size_dtyp] internally, so
               bind both once per field *)
            let ssz := store_size_dtyp dt in
            let asz := alloc_size_dtyp dt in
            let '(offset, acc) :=
              accumulate_padding offset (if pad then Some a else None) acc in
            (* The field is laid out relative to *its own* start, so the
               recursive call begins at 0 and the parent adds the field's
               extent.  Passing the absolute [offset] down would make a
               nested unpacked aggregate pad itself against the enclosing
               offset, which disagrees with [store_size_dtyp] (and with LLVM,
               and with the reader) whenever that offset is not a multiple of
               the field's alignment -- as inside a packed struct. *)
            '(coff, bs) <- acc_dvalue_to_memory_bytes_h dt f 0%N None acc ;;
            let '(offset'', bs') :=
              accumulate_padding_bytes (offset + coff)%N (asz - ssz) bs in
            loop fs dts offset'' bs'
        | _, _ => raise_error "type-mismatch: structs / fields have different lengths"
        end
    in
    (* Array elements sit at their alloc size; vector elements are contiguous
       at their store size. *)
    let dvalue_extract_array_bytes (vector : bool) dt :=
      (* [dt] is fixed for the whole loop, so the per-element tail padding is
         computed once here rather than at every element (mirrors the reader's
         [array_elts_to_dvalue]) *)
      let elt_pad :=
        if vector then 0%N else (alloc_size_dtyp dt - store_size_dtyp dt)%N in
      fix loop (elts : list dvalue) offset (acc : list memory_byte) {struct elts}  :=
        match elts with
        | [] => ret (accumulate_padding offset tail_align acc)
        | e::es =>
            (* as in the struct loop: the element is laid out from 0 *)
            '(coff, bs) <- acc_dvalue_to_memory_bytes_h dt e 0%N None acc ;;
            let '(offset'', bs') :=
              accumulate_padding_bytes (offset + coff)%N elt_pad bs in
            loop es offset'' bs'
        end
    in
    match dt with
    | DTYPE_Base dtb =>
        match dv with
        | DVALUE_Base dv =>
            let '(offset', bs) := acc_memory_bytes_of_dvalue_base dtb dv offset acc in
            ret (accumulate_padding offset' tail_align bs)
        | _ => raise_error "acc_dvalue_to_memory_bytes_h: type-mismatch non-base value"
        end
    | DTYPE_Struct packed dts =>
        match dv with
          (* TODO: could check that the type and dvalue packed flag agree *)
        | DVALUE_Struct _ fields =>
            (* A *packed* struct gets no inter-field padding; an unpacked one
               lays its fields out at their preferred alignments. This matches
               [sizeof_dtyp_Packed_struct] / [sizeof_dtyp_Struct] and the
               [DTYPE_Struct true/false] cases of [handle_gep_h]. *)
            let pad := if packed then None else Some (max_preferred_dtyp_alignment dts) in
            accumulate_struct_bytes pad fields dts offset acc
        | DVALUE_Base DVALUE_Poison =>
            (* Poison inhabits every type ([DVALUE_Poison_typ_agg]), so a
               poison at aggregate type is well-typed: it serializes to the
               type's worth of poison bytes. *)
            let '(offset', bs) := accumulate_padding_bytes offset (store_size_dtyp dt) acc in
            ret (accumulate_padding offset' tail_align bs)
        | _ => raise_error "acc_dvalue_to_memory_bytes_h: type-mismatch non-struct value"
        end
    | DTYPE_Array _vector sz elt_t =>
        match dv with
        | DVALUE_Array v elts =>
            dvalue_extract_array_bytes _vector elt_t elts offset acc
        | DVALUE_Base DVALUE_Poison =>
            (* Poison inhabits every type ([DVALUE_Poison_typ_agg]), so a
               poison at aggregate type is well-typed: it serializes to the
               type's worth of poison bytes. *)
            let '(offset', bs) := accumulate_padding_bytes offset (store_size_dtyp dt) acc in
            ret (accumulate_padding offset' tail_align bs)
        | _ => raise_error ("acc_dvalue_to_memory_bytes_h: type-mismatch non-array value: "  ++ (show dv))
        end
    end.
  

  (** ** Serializing a [dvalue]: the layout model

      [dvalue_to_memory_bytes dt dv tail_align] lays [dv] out as the bytes of a
      value of type [dt], as they would appear in memory.

      *** Why the type is needed
      The value alone does not determine the layout: [DVALUE_Poison] inhabits
      every type ([DVALUE_Poison_typ_agg]), so its width comes from [dt], and
      so does every padding decision inside an aggregate.

      *** The layout law
      Writing [|bs|] for the number of bytes produced, the intended invariant is

        dvalue_has_dtyp dv dt ->
        dvalue_to_memory_bytes dt dv None = ret bs ->
        |bs| = store_size_dtyp dt

      (and [pad_to a (store_size_dtyp dt)] for [tail_align = Some a]).  This is
      [dvalue_to_memory_bytes_sizeof] below.  Case by case, matching
      [SizeofTheory]:

      - [DTYPE_Base dtb] emits [store_size_dtyp dtb] bytes, no padding.

      - [DTYPE_Struct true dts] (*packed*) emits the fields back to back with no
        padding anywhere -- [sizeof_dtyp_Packed_struct].

      - [DTYPE_Struct false dts] (unpacked) emits, for each field of type [t],
        *leading* padding up to [preferred_alignment (dtyp_alignment t)] and
        then [store_size_dtyp t] bytes; after the last field, *trailing* padding up
        to [max_preferred_dtyp_alignment dts].  That is exactly
        [sizeof_dtyp_Struct]:
          pad_to (max_preferred_dtyp_alignment dts)
                 (fold_left (fun acc t => pad_to_align (dtyp_alignment t) acc
                                          + store_size_dtyp t) dts 0)
        The trailing padding is *intrinsic* to the struct -- it is part of its
        [store_size_dtyp] -- so it must be emitted whatever the caller asks for.
        It is NOT the same thing as [tail_align].

      - [DTYPE_Array _ sz t] emits [sz] elements of [store_size_dtyp t] bytes each
        with no padding between them -- [sizeof_dtyp_array].  An element's own
        trailing padding is already inside [store_size_dtyp t], which is what makes
        a contiguous layout correct.

      *** Preconditions
      - [dvalue_has_dtyp dv dt].  The element-count part matters: the array case
        loops over the elements it is given and ignores [sz], so a short array
        value serializes without complaint and yields too few bytes.
      - Bytes are laid out relative to offset [0] and are assumed to be written
        at an address that is a multiple of
        [preferred_alignment (dtyp_alignment dt)].  All padding is computed from
        the offset *within* the value, so this assumption is what makes the
        result correctly aligned once in memory.

      *** [tail_align]
      [Some a] asks for extra padding so the value occupies a multiple of [a]
      bytes; [None] asks for none.  It is a request from the caller, and is
      independent of whether the value is a packed struct.  Both callers in the
      development ([write_dvalue] and the bitcast case of [convert]) pass
      [None], so the [Some] case is currently unexercised.
      (Previously named [pad_to], which collides with [Sizeof.pad_to].)
   *)
  Definition dvalue_to_memory_bytes (dt:dtyp) (dv : dvalue) (tail_align : option N)
    : EOU (list memory_byte) :=
    '(offset, bytes) <- acc_dvalue_to_memory_bytes_h dt dv 0 tail_align [] ;;
    (* reverse the list *)
    ret (rev_append bytes []).


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

  Lemma store_le_alloc : forall t, (store_size_dtyp t <= alloc_size_dtyp t)%N.
  Proof. intros t; unfold alloc_size_dtyp, pad_to_align, pad_to; lia. Qed.

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

  Definition memory_bit_to_bit (mb : memory_bit) : EOUP Z :=
    match mb with
    | Bit_ptr p i  => ret (extract_bit_Z (ptr_to_int p) i)
    | Bit_psn => ret Pois
    | Bit_bit b => ret (unsigned b)
    end.


  (* Extract the bits from (non-poison) memory_bits or raise poison otherwise. *)
  Definition memory_bits_to_Z (bits : list memory_bit) : EOUP Z :=
    bits <- map_monad memory_bit_to_bit bits ;;
    ret (concat_bits_Z bits).

  Definition memory_byte_to_Z (mb : memory_byte) : EOUP Z :=
    match mb with
    | BYTE_Pointer p i => ret (extract_byte_Z (ptr_to_int p) i)
    | BYTE_I x => ret (unsigned x)
    | BYTE_Mixed bits =>
        memory_bits_to_Z bits
    end.
    
  
  
  (* Gets an integral byte value from a list of memory bits, stripping away provenance:
       given [b0; b1; ... ; bn]
       extracts bits numbered [idx*8 + 0; idx*8 + 1; ... idx*8 + 7]
       if none of them are poison, return the byte obtained by concatenating them
       if any are poison, raise poison
        
   *)
  Definition extract_byte_mixed_bits (bits : list memory_bit) (idx : N) : EOUP Z :=
    let suffix := if N.eqb idx 0 then bits else drop (8 * (N.pred idx)) bits in
    let mbits := take 8 suffix in
    if negb (N.of_nat (List.length mbits) =? 8) then
      raise_ub "extract_byte_mixed_bits: not enough bits"
    else
      vs <- map_monad memory_bit_to_bit mbits ;;
      ret (concat_bits_Z vs).
  

  #[local] Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia].

  Definition absorb_pois {A} (c : EOUP A) (k : A -> EOU dvalue_base) : EOU dvalue_base :=
    catch_pois DVALUE_Poison c k.
  
  (* Recover a pointer from a byte representation for pointer p.
     The byte at index 0 <= i < pointer_size must be of the form:

     BYTE_Pointer 8 p i
     BYTE_Mixed 8 [Bit_ptr p (8*i)+0;
                   Bit_ptr p (8*i)+1;
                   ...
                   Bit_ptr p (8*i)+7]

   *)
  Fixpoint valid_pointer_bits p base offset bits : EOUP bool :=
    match bits with
    | [] => ret (N.eqb offset 8)
    | (Bit_ptr q j) :: rest  =>
        if eq_dec_ptr p q then
          if N.eqb j (base + offset) then
            valid_pointer_bits p base (1+offset) rest 
          else
            ret false
        else
          ret false
    | Bit_bit _ :: _ => ret false  (* an integer bit: not this pointer *)
    | Bit_psn :: _ => ret Pois
    end.
  
  Definition valid_pointer_byte (p:ptr) (idx:N) (mb:memory_byte) : EOUP bool :=
    match mb with
    | BYTE_Pointer q i =>
        if eq_dec_ptr p q then ret (N.eqb idx i) else ret false 
    | BYTE_Mixed bits =>
        valid_pointer_bits p (idx * 8) 0 bits 
    | BYTE_I _ => ret false
    end.

  Fixpoint valid_pointer_bytes (p:ptr) (idx:N) (bytes : list memory_byte) : EOUP bool :=
    match bytes with
    | [] => ret (N.eqb idx (store_size_dtyp (DTYPE_Base DTYPE_Pointer)))
    | b::rest =>
        v <- valid_pointer_byte p idx b ;;
        if v then valid_pointer_bytes p (1+idx) rest else ret false
    end.
  
  (* LangRef ('bitcast', a byte value to a pointer type): if no bit is
     poison but the bits are not all those of one pointer, correctly
     ordered, the result is a pointer with the address given by the integer
     value of the bits, and without provenance.  (A load at pointer type
     follows the same rules.)  Any poison byte makes it poison. *)
  Definition memory_bytes_to_address_ptr (dbs : list memory_byte) : EOUP ptr :=
    zs <- map_monad memory_byte_to_Z dbs ;;
    NoPois <$> int_to_ptr (concat_bytes_Z zs) nil_prov.

  Definition memory_bytes_to_pointer (dbs : list memory_byte) : EOUP ptr :=
    match dbs with
    | ((BYTE_Pointer p _) :: _)
    | ((BYTE_Mixed ((Bit_ptr p _)::_)) :: _) =>
        v <- valid_pointer_bytes p 0 dbs ;;
        if v then ret p else memory_bytes_to_address_ptr dbs
    | _ => memory_bytes_to_address_ptr dbs
    end.

  Definition memory_byte_to_memory_bits (mb : memory_byte) : list memory_bit :=
    match mb with
    | BYTE_Pointer p idx => rev_append (N.rev_loop_acc (fun i => Bit_ptr p i) 8 (8 * idx) []) []
    | BYTE_I x  => rev_append (N.rev_loop_acc (fun i => Bit_bit (repr (extract_bit_vint x i))) 8 0 []) []
    | BYTE_Mixed bits => bits
    end.

  (* A version of concat_bytes that trims extra bits from the last byte. *)
  (* Like [concat_bytes_Z], but only the low [extra] bits of the last byte
     belong to the value; the rest is padding.  Each byte has to
     be weighted by its position, exactly as [concat_bytes_Z] does -- an
     unweighted running sum reads [i12 4000] back as 175. *)
  Fixpoint concat_bytes_Z_mixed (extra:N) (dbs : list memory_byte) : EOUP Z :=
    match dbs with
    | [] => ret 0%Z
    (* only the low [extra] bits of the last byte belong to the value,
       whatever wrote it *)
    | (BYTE_I y)::[] => ret (unsigned y mod 2 ^ Z.of_N extra)%Z
    | b::[] => memory_bits_to_Z (take extra (memory_byte_to_memory_bits b))
    | b::rest =>
        z <- memory_byte_to_Z b ;;
        r <- concat_bytes_Z_mixed extra rest ;;
        ret (z + Z.shiftl r 8)%Z
    end.
  
  (* one-step unfolding for the recursive case; [cbn] would splice the
     recursive call in too, leaving no [concat_bytes_Z_mixed] for an
     induction hypothesis to apply to *)
  Lemma concat_bytes_Z_mixed_cons2 : forall extra b d rest,
      concat_bytes_Z_mixed extra (b :: d :: rest) =
        z <- memory_byte_to_Z b ;;
        r <- concat_bytes_Z_mixed extra (d :: rest) ;;
        ret (z + Z.shiftl r 8)%Z.
  Proof. intros extra b d rest; destruct b; reflexivity. Qed.

  Definition memory_bytes_to_int (bit_sz : positive) (dbs : list memory_byte) : EOUP Z :=
    let extra_bits := N.modulo (Npos bit_sz) 8 in
    if negb (N.eqb extra_bits 0) then
      (* we need to deal with padding *)
      concat_bytes_Z_mixed extra_bits dbs 
    else
      v <- map_monad (m := EOUP) (memory_byte_to_Z) dbs ;;
      ret (concat_bytes_Z v).


  Fixpoint get_bits_of_memory_byte_list (bit_sz : N) (dbs : list memory_byte) acc : list memory_bit :=
    match dbs with
    | [] => if (N.eqb bit_sz 0) then
             acc
           else
             (* still need poison bits as padding *)
             N.rev_loop_acc (fun _ => Bit_psn) bit_sz 0 acc 
    | b::bs =>
        let bits := memory_byte_to_memory_bits b in
        if (N.ltb bit_sz 8) then
          rev_append (take bit_sz bits) acc
        else
          get_bits_of_memory_byte_list (bit_sz - 8) bs (rev_append bits acc)
        
    end.
  
  (* Is [mb] byte number [idx] of pointer [p]?  This is just [valid_pointer_byte]
     read as a plain predicate: it answers [NoPois] on every byte shape, so the
     other outcomes can only be [Pois], which is "no". *)
  Definition pointer_byte_at (p : ptr) (idx : N) (mb : memory_byte) : bool :=
    match valid_pointer_byte p idx mb with
    | raise_ret (NoPois b) => b
    | _ => false
    end.

  Fixpoint pointer_slice_from (p : ptr) (idx : N) (dbs : list memory_byte) : bool :=
    match dbs with
    | [] => true
    | b :: rest => pointer_byte_at p idx b && pointer_slice_from p (1+idx) rest
    end.

  (** Recognise a contiguous run of bytes of a *single* pointer, starting at
      whatever index the run happens to begin at:

        [BYTE_Pointer 8 p k; BYTE_Pointer 8 p (k+1); ...]

      This is deliberately weaker than [memory_bytes_to_pointer], which
      reconstructs a *whole* pointer (it requires the run to start at index 0
      and to span the full pointer width) because that is what a
      [DTYPE_Pointer] read needs.  A [DTYPE_B] read has the opposite job: it
      must preserve the byte-level representation, provenance and byte index
      included, so that storing [p] and reading it back as, say,
      [<8 x DTYPE_B 8>] yields bytes [0..7] of [p] rather than eight
      provenance-free integers.  A sub-word slice is representable: bytes
      [k..k+n-1] read at [DTYPE_B (8*n)] give [BYTE_Pointer (8*n) p k]. *)
  Definition memory_bytes_to_pointer_slice (dbs : list memory_byte) : option (ptr * N) :=
    match dbs with
    | (BYTE_Pointer p k) :: _ =>
        if pointer_slice_from p k dbs then Some (p, k) else None
    | (BYTE_Mixed ((Bit_ptr p j) :: _)) :: _ =>
        let k := (j / 8)%N in
        if pointer_slice_from p k dbs then Some (p, k) else None
    | _ => None
    end.

  Definition memory_bytes_to_byte_value (bit_sz : positive) (dbs : list memory_byte) : EOU (@dvalue_bv _ bit_sz) :=
    match memory_bytes_to_pointer_slice dbs with
    (* First try to retain a slice of a pointer, provenance and index intact.
       This must come before the integer attempt: [memory_byte_to_Z] answers
       pointer bytes with a concrete address rather than poison, so an
       integer-first order would strip provenance from every pointer byte. *)
    | Some (p, k) =>
        (* [k] is a *byte* index, but [BYTE_Pointer]'s index counts chunks of
           [bit_sz] bits -- [memory_byte_of_dvalue_bv] writes chunk [i] of a
           [BYTE_Pointer _ i] starting at byte [(bit_sz * i) / 8].  Invert
           that here, so reading bytes 4..7 of [p] at [DTYPE_B 32] gives
           [BYTE_Pointer 32 p 1] rather than [BYTE_Pointer 32 p 4]. *)
        ret (BYTE_Pointer bit_sz p ((k * 8) / Npos bit_sz))
    | None =>
        let bits := rev_append (get_bits_of_memory_byte_list (Npos bit_sz) dbs []) [] in
        (* Then as a plain integer, but only when no bit belongs to a
           pointer: [memory_byte_to_Z] answers pointer bits with their
           address, so a pointer bit mixed with integer bits would otherwise
           lose its provenance.  With no pointer bits, the integer read
           succeeds exactly when no bit is poison, i.e. when every bit is an
           integer bit -- the condition under which [dvalue_bv_canonical]
           takes [BYTE_I]. *)
        if existsb is_ptr_bit bits then ret (BYTE_Mixed bit_sz bits)
        else
          match memory_bytes_to_int bit_sz dbs with
          | raise_ret (NoPois x) => ret (BYTE_I (repr x))
          | _ => (* otherwise retain as just a list of mixed bits *)
              ret (BYTE_Mixed bit_sz bits)
          end
    end.

  (* [is_poison_bit] is defined in DynamicValues.v, next to [dvalue_bv_canonical]. *)
  
  Definition all_poison_bits (bits : list memory_bit) : bool :=
    List.forallb is_poison_bit bits.

  Definition is_all_poison_byte (mb : memory_byte) : bool :=
    match mb with
    | BYTE_Mixed bits => all_poison_bits bits
    | _ => false
    end.
  
  (** [poison_split dbs = (k, rest)] splits [dbs] at its first non-poison
      byte: [k] is the number of leading all-poison bytes and [rest] is what
      follows, so [rest = []] exactly when every byte is poison.  Like
      [forallb] it stops as soon as it sees a non-poison byte.

      This replaces a boolean [all_poison_bytes] test in the deserializer.
      The same scan then does two jobs: it selects the all-poison fast path,
      and its index [k] says which fields / array elements lie entirely
      before the first non-poison byte, so those can be answered with
      [DVALUE_Poison] by arithmetic instead of being re-scanned. *)
  Fixpoint poison_split (dbs : list memory_byte) : N * list memory_byte :=
    match dbs with
    | [] => (0%N, [])
    | b :: rest =>
        if is_all_poison_byte b
        then let '(k, tl) := poison_split rest in ((1 + k)%N, tl)
        else (0%N, b :: rest)
    end.

  Definition all_poison_bytes (bytes : list memory_byte) : bool :=
    match snd (poison_split bytes) with
    | [] => true
    | _ :: _ => false
    end.
  
  Definition memory_bytes_to_dvalue_base (dbs : list memory_byte) (dt : dtyp_base) : EOU dvalue_base :=
    match dt with
    | DTYPE_I sz =>
        absorb_pois 
          (memory_bytes_to_int sz dbs)
          (fun v => ret (DVALUE_I sz (repr v)))

    | DTYPE_Iptr =>
        absorb_pois 
          (map_monad memory_byte_to_Z dbs)
          (fun zs => DVALUE_Iptr <$> from_Z (concat_bytes_Z zs))

    | DTYPE_Pointer =>
        absorb_pois (memory_bytes_to_pointer dbs)
                    (fun p => ret (DVALUE_Pointer p))
    | DTYPE_Void =>
        raise_error "memory_bytes_to_dvalue on void type."
    | DTYPE_FP FP_half =>
        raise_error "memory_bytes_to_dvalue: unsupported half."
    | DTYPE_FP FP_bfloat =>
        raise_error "memory_bytes_to_dvalue: unsupported bfloat"
    | DTYPE_FP FP_float =>
        absorb_pois (map_monad memory_byte_to_Z dbs)
          (fun zs => ret (DVALUE_Float (Float32.of_bits (concat_bytes_Z_vint zs))))
    | DTYPE_FP FP_double => 
        absorb_pois  (map_monad memory_byte_to_Z dbs)
          (fun zs => ret (DVALUE_Double (Float.of_bits (concat_bytes_Z_vint zs))))
    | DTYPE_FP FP_x86_fp80 =>
        raise_error "memory_bytes_to_dvalue: unsupported X86_fp80."
    | DTYPE_FP FP_fp128 =>
        raise_error "memory_bytes_to_dvalue: unsupported fp128."
    | DTYPE_FP FP_ppc_fp128 =>
        raise_error "memory_bytes_to_dvalue: unsupported ppc_fp128."
    | DTYPE_Label =>
        raise_error "memory_bytes_to_dvalue: unsupported DTYPE_Label."
    | DTYPE_Token =>
        raise_error "memory_bytes_to_dvalue: unsupported DTYPE_Token."
    | DTYPE_Metadata =>
        raise_error "memory_bytes_to_dvalue: unsupported DTYPE_Metadata."
    | DTYPE_X86_mmx =>
        raise_error "memory_bytes_to_dvalue: unsupported DTYPE_X86_mmx."
    | DTYPE_Opaque =>
        raise_error "memory_bytes_to_dvalue: unsupported DTYPE_Opaque."
    | DTYPE_B sz =>
        (* If all the bits are poison then create the poison value *)
        (* Question: do we have to check the length too *)
        if all_poison_bytes dbs then
          ret DVALUE_Poison
        else
        (* otherwise at least one is non-poison *)
        dv <- memory_bytes_to_byte_value sz dbs ;;
        ret (@DVALUE_B _ sz dv)
    end.

  
  (** ** Deserializing: [memory_bytes_to_dvalue dbs dt]

      The inverse of [dvalue_to_memory_bytes], and it has to agree with it byte
      for byte.  Where the writer *emits* padding, the reader *skips* it.

      *** Precondition
      [dbs] is expected to be exactly [store_size_dtyp dt] bytes, which is what
      [read_dvalue] supplies ([read_bytes p (store_size_dtyp dt)]).  The array case
      depends on it: [split_every_nil (store_size_dtyp t) dbs] chops *all* of [dbs],
      so a longer [dbs] yields more than [sz] elements rather than an error.

      *** Where the padding goes
      - Structs: [list_memory_bytes_to_dvalue] drops
        [pad_amount (preferred_alignment (dtyp_alignment t)) offset] bytes
        before each field and then consumes [store_size_dtyp t] -- the exact mirror
        of the writer's *leading* padding.  It is called with
        [Some (max_preferred_dtyp_alignment fields)] for an unpacked struct and
        [None] for a packed one, so the packed/unpacked decision is taken from
        the type on both sides.
      - Arrays: no padding between elements; the split is at [store_size_dtyp t].
      - Trailing padding is *ignored*: the [[]] case of the field loop returns
        without inspecting what is left, so surplus bytes at the end are
        dropped.  This is why a writer that omits a struct's trailing padding
        still round-trips at the top level, and why the bug is only visible in
        fields that follow a misaligned one.

      *** Round trip
      The intended statement is

        dvalue_has_dtyp dv dt ->
        dvalue_to_memory_bytes dt dv None = ret bs ->
        exists dv', memory_bytes_to_dvalue bs dt = ret dv' /\ <dv' agrees with dv>

      It is deliberately not the identity.  Padding bytes are written as poison
      and are not recorded in the dvalue, and deserialization is lossy in two
      further ways: a field whose bytes are all poison comes back as
      [DVALUE_Poison] rather than as the original shape
      (see [all_poison_bytes]), and [memory_bytes_to_byte_value] re-canonicalises
      a byte sequence (integer, then pointer, then mixed bits), so a value may
      come back under a different [dvalue_bv] constructor than it went in.
      Pinning down "<dv' agrees with dv>" is the open part of this model.
   *)
  (* Canonicalising constructor for aggregates: an aggregate all of whose
     immediate children are poison *is* poison, per [dvalue_has_dtyp].

     The [poison_split] fast path in [memory_bytes_to_dvalue] catches the
     common case -- every byte poison -- without rebuilding the value, but it
     is not sufficient on its own.  A single non-poison byte lying in padding,
     or in the tail of an array slot, leaves [rest] non-empty while every
     field still reads back as poison; e.g. reading [{i8, i32}] from
     [[psn; X; psn; psn; psn; psn; psn; psn]] would otherwise yield
     [DVALUE_Struct false [Poison; Poison]].  Children are canonical by
     induction, so the shallow [dvalue_is_poison] test is enough here.

     Note this also sends an empty aggregate to poison, which is what the
     [forallb ... = false] premises of [DVALUE_Struct_typ] / [DVALUE_Array_typ]
     require. *)
  Definition canonicalize_agg (mk : list dvalue -> dvalue) (vs : list dvalue) : dvalue :=
    if forallb dvalue_is_poison vs then DVALUE_Base DVALUE_Poison else mk vs.

  Fixpoint memory_bytes_to_dvalue (dbs : list memory_byte) (dt : dtyp) : EOU dvalue :=
    (* [np] is the index of the first non-poison byte of the *whole* aggregate.
       A field or element lying entirely below it is poison, so it is answered
       directly rather than reconstructed. *)
    let list_memory_bytes_to_dvalue (np : N) (pad : option N) :=
      fix go (offset : N) dts dbs :=
        match dts with
        | [] =>
            (* TODO: should we check that we have the appropriate number of extra padding bytes here? *)
            (* Long term we'll have to include padding bytes in the dvalue *)
            ret []
        | (dt::dts) =>
            (* mirror of the writer: skip the field's leading padding, read its
               store-size bytes, then advance by its alloc size *)
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
                  else memory_bytes_to_dvalue (take ssz dbs') dt) ;;
            rest <- go (start + asz) dts rest_bytes ;;
            ret (f :: rest)
        end
    in
    (* Array/vector elements: stride is the alloc size for arrays and the store
       size for vectors; in both cases only the first [store_size_dtyp t] bytes
       of each slot carry the value. *)
    let array_elts_to_dvalue (np : N) (stride : N) (t : dtyp) :=
      let ssz := store_size_dtyp t in
      fix go (n : nat) (offset : N) (dbs : list memory_byte) : EOU (list dvalue) :=
        match n with
        | O => ret []
        | S n' =>
            e <- (if N.leb (offset + ssz) np
                  then ret (DVALUE_Base DVALUE_Poison)
                  else memory_bytes_to_dvalue (take ssz dbs) t) ;;
            rest <- go n' (offset + stride)%N (drop stride dbs) ;;
            ret (e :: rest)
        end
    in
    match dt with
    | DTYPE_Base dt =>
        (* Trim to the type's store size, mirroring the [take ssz _] the
           aggregate loops below already hand their children.  Each arm of
           [memory_bytes_to_dvalue_base] consumes its whole input, so without
           this a base read is the only part of the reader that cannot
           tolerate a longer buffer: a value written with a [tail_align] would
           have its trailing padding folded into the value and read back as
           [DVALUE_Poison].  On an exactly-sized buffer this is the identity. *)
        DVALUE_Base <$> (memory_bytes_to_dvalue_base
                           (take (store_size_dtyp (DTYPE_Base dt)) dbs) dt)

    | DTYPE_Array vector sz t =>
        (* An all-poison aggregate canonicalises to [DVALUE_Poison] rather than
           to an aggregate of poisons -- the same treatment [DTYPE_B] already
           gets in [memory_bytes_to_dvalue_base]. *)
        let '(np, rest) := poison_split dbs in
        match rest with
        | [] => ret (DVALUE_Base DVALUE_Poison)
        | _ :: _ =>
            let stride := if vector then store_size_dtyp t else alloc_size_dtyp t in
            elts <- array_elts_to_dvalue np stride t (N.to_nat sz) 0%N dbs ;;
            ret (canonicalize_agg (DVALUE_Array vector) elts)
        end

    | DTYPE_Struct packed fields =>
        let '(np, rest) := poison_split dbs in
        match rest with
        | [] => ret (DVALUE_Base DVALUE_Poison)
        | _ :: _ =>
            let pad := if packed then None else Some (max_preferred_dtyp_alignment fields) in
            (canonicalize_agg (DVALUE_Struct packed))
              <$> (list_memory_bytes_to_dvalue np pad 0%N fields dbs)
        end
    end.

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

  Lemma map_monad_EOUP_pois_head : forall {A B} (f : A -> EOUP B) x rest,
      f x = raise_ret Pois -> map_monad f (x :: rest) = raise_ret Pois.
  Proof. intros A B f x rest H; cbn; rewrite H; reflexivity. Qed.

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

  Lemma take_repeat_cons : forall {A} (x : A) n k,
      (0 < n)%N -> (0 < k)%nat -> exists r, take n (List.repeat x k) = x :: r.
  Proof.
    intros A x n [| k'] Hn Hk; [lia |].
    cbn [List.repeat take].
    destruct (N.eqb_spec 0 n); [lia |].
    eexists; reflexivity.
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

  (* a multiple-of-8 width occupies exactly [sz/8] bytes *)
  Lemma store_size_int_mult8 : forall sz,
      (Npos sz mod 8 = 0)%N ->
      (8 * store_size_dtyp (DTYPE_Base (DTYPE_I sz)) = Npos sz)%N.
  Proof.
    intros sz H; rewrite store_size_dtyp_int.
    assert (Hq : (Npos sz = 8 * (Npos sz / 8))%N)
      by (apply N.div_exact; [lia | exact H]).
    remember (Npos sz / 8)%N as q.
    rewrite Hq.
    replace (8 * q + 7)%N with (7 + q * 8)%N by lia.
    rewrite N.div_add by lia.
    replace (7 / 8)%N with 0%N by reflexivity.
    lia.
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
    pose proof (store_size_int_mult8 sz H8) as Hk.
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

  Lemma map_monad_cons_EOUP : forall {A B} (f : A -> EOUP B) x xs,
      map_monad f (x :: xs) = (y <- f x ;; ys <- map_monad f xs ;; ret (y :: ys)).
  Proof. reflexivity. Qed.

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
  Lemma store_size_int_mixed : forall sz,
      (Npos sz mod 8 <> 0)%N ->
      (1 <= store_size_dtyp (DTYPE_Base (DTYPE_I sz))
       /\ 8 * (store_size_dtyp (DTYPE_Base (DTYPE_I sz)) - 1) + Npos sz mod 8
          = Npos sz)%N.
  Proof.
    intros sz H; rewrite store_size_dtyp_int.
    pose proof (N.div_mod (Npos sz) 8 ltac:(lia)) as D.
    pose proof (N.mod_upper_bound (Npos sz) 8 ltac:(lia)) as U.
    remember (Npos sz / 8)%N as q; remember (Npos sz mod 8)%N as e.
    replace (Npos sz + 7)%N with (7 + e + q * 8)%N by lia.
    rewrite N.div_add by lia.
    assert (Hd : ((7 + e) / 8 = 1)%N).
    { replace (7 + e)%N with (1 * 8 + (e - 1))%N by lia.
      rewrite N.div_add_l by lia.
      rewrite (N.div_small (e - 1) 8) by lia; lia. }
    rewrite Hd; lia.
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
    destruct (store_size_int_mixed sz H8) as [Hk1 Hk2].
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

  Lemma store_size_B_I : forall sz,
      store_size_dtyp (DTYPE_Base (DTYPE_B sz))
      = store_size_dtyp (DTYPE_Base (DTYPE_I sz)).
  Proof. intros sz; rewrite store_size_dtyp_bytes, store_size_dtyp_int; reflexivity. Qed.

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
  Lemma In_rev_loop_acc : forall {A} (f : N -> A) n i acc b,
      In b (N.rev_loop_acc f n i acc) -> In b acc \/ exists j, b = f j.
  Proof.
    intros A f n i acc b H.
    rewrite rev_loop_acc_app in H.
    apply in_app_or in H as [H | H]; [| now left].
    apply in_rev, in_map_iff in H as (j & <- & _); eauto.
  Qed.

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
    cbv zeta; rewrite no_ptr_bits_BYTE_I_block.
    rewrite Ev; cbv beta iota.
    rewrite Hv; cbn; reflexivity.
  Qed.

  Lemma map_Nseq_shift : forall {A} (f : N -> A) n a s,
      List.map (fun i => f (s + i)%N) (Nseq a n) = List.map f (Nseq (s + a)%N n).
  Proof.
    intros A f; induction n as [| n IH]; intros a s; cbn [Nseq List.map];
      [reflexivity |].
    f_equal.
    rewrite (IH (N.succ a) s).
    do 2 f_equal; lia.
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
      by (subst q; apply N.div_exact; [lia | exact H8]).
    assert (Hqnz : (q <> 0)%N) by lia.
    assert (Harith : ((Npos sz * k / 8) * 8 / Npos sz = k)%N).
    { rewrite Hq.
      replace (8 * q * k)%N with (q * k * 8)%N by lia.
      rewrite N.div_mul by lia.
      replace (q * k * 8)%N with (k * (8 * q))%N by lia.
      rewrite N.div_mul by lia.
      reflexivity. }
    cbn [memory_bytes_to_dvalue_base].
    rewrite all_poison_pointer_run.
    unfold memory_bytes_to_byte_value.
    rewrite memory_bytes_to_pointer_slice_run.
    cbv beta iota.
    rewrite Harith; cbn; reflexivity.
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
  Lemma pointer_slice_mixed_none : forall n bits,
      (N.of_nat (List.length bits) <= 8 * N.of_nat (S n))%N ->
      negb (is_pointer_bits bits) = true ->
      memory_bytes_to_pointer_slice (List.map (mixed_byte bits) (Nseq 0 (S n)))
      = None.
  Proof.
    intros n bits Hlen H.
    pose proof (pointer_slice_head bits n) as HP.
    destruct bits as [| [q j | | ] bits']; try exact HP.
    rewrite HP.
    destruct (pointer_slice_from q (j / 8)%N
                (List.map (mixed_byte (Bit_ptr q j :: bits')) (Nseq 0 (S n))))
      eqn:E; [| reflexivity].
    exfalso.
    assert (Hall : all_pointer_bits_from q (8 * (j / 8))%N (Bit_ptr q j :: bits')
                   = true)
      by (apply (pointer_slice_implies_bits (S n)); [exact Hlen | exact E]).
    assert (Ej : j = (8 * (j / 8))%N).
    { cbn [all_pointer_bits_from] in Hall.
      destruct (eq_dec_ptr q q) as [_ | NE]; [| now contradiction NE].
      cbn [andb] in Hall.
      destruct (N.eqb_spec j (8 * (j / 8))%N) as [Ej | ]; [exact Ej | discriminate]. }
    assert (Hmod : (j mod 8 = 0)%N).
    { rewrite Ej at 1; rewrite N.mul_comm, N.mod_mul; lia. }
    unfold is_pointer_bits in H.
    rewrite Hmod, N.eqb_refl in H; cbn [andb] in H.
    rewrite <- Ej in Hall.
    rewrite Hall in H; discriminate.
  Qed.

  Lemma read_base_block_BYTE_Mixed : forall sz bits,
      (N.of_nat (List.length bits) = Npos sz)%N ->
      negb (is_pointer_bits bits) = true ->
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
    unfold memory_bytes_to_byte_value.
    (* not a pointer slice *)
    rewrite pointer_slice_mixed_none by (first [exact HKb | exact Hptr]).
    (* the bits come back unchanged *)
    cbv zeta.
    rewrite <- Hlen, get_bits_writer by exact HKb.
    rewrite rev_append_rev, app_nil_r, rev_append_rev, app_nil_r, rev_involutive.
    (* a pointer bit sends the read straight to [BYTE_Mixed] *)
    destruct (existsb is_ptr_bit bits) eqn:Eptr; [reflexivity |].
    (* otherwise some bit is poison, and the integer read poisons *)
    assert (Hex : existsb is_poison_bit bits = true)
      by (apply not_all_int_no_ptr_pois; assumption).
    assert (Hint : memory_bytes_to_int sz (List.map (mixed_byte bits) (Nseq 0 (S n)))
                   = raise_ret (@Pois Z)).
    { unfold memory_bytes_to_int.
      destruct (N.eqb_spec (Npos sz mod 8) 0) as [E8 | E8]; cbn [negb].
      - rewrite map_monad_byte_mixed_pois by (first [exact HKb | exact Hex]);
          reflexivity.
      - rewrite store_size_B_I in EK.
        destruct (store_size_int_mixed sz E8) as [_ Hk2].
        assert (HK : (store_size_dtyp (DTYPE_Base (DTYPE_I sz))
                      = N.of_nat (S n))%N)
          by (rewrite EK; symmetry; apply Nnat.N2Nat.id).
        assert (Hx : (0 < Npos sz mod 8 <= 8)%N).
        { pose proof (N.mod_upper_bound (Npos sz) 8 ltac:(lia)) as U.
          revert E8 U; generalize (Npos sz mod 8)%N; intros m HA HB; lia. }
        apply concat_bytes_Z_mixed_mixed_pois; [exact Hx | lia | exact Hex]. }
    rewrite Hint; reflexivity.
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

  Lemma dvalue_is_poison_false : forall d,
      dvalue_is_poison d = false -> d <> DVALUE_Base DVALUE_Poison.
  Proof. intros d H C; subst; discriminate. Qed.

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

End MemoryByte.

