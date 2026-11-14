From Vellvm Require Import
  Utils
  Syntax
  VellvmIntegers
  EOU
  DynamicValues
  Params.
Open Scope Z.

Section GEP.
  Context {Pa : Params}.

  (** ** Get Element Pointer

      [getelementptr t, ptr a, i_1, ..., i_n] computes an address from [a] by
      a sequence of steps, one per index.  [gep_steps] lists them: for each
      index, its value and what it is scaled by.  The first index steps over
      whole objects of type [t]; each later one selects an element of the
      current aggregate type: an array or vector element (the index times
      the element stride, see [sequential_stride]), or a struct field (its
      byte offset, scaled by 1).
      The address is [a] plus the sum of the steps ([gep_offset]), and the
      no-wrap flags are rules about the steps (see [gep_flags_violated]).
      A poison index makes the whole result poison.
   *)
  (* Indexing into [t] is allowed unless [t] is a vector whose elements are
     not byte-addressable, i.e. whose bit size is not their store size in
     bits (<N x i1>, <N x i12>, ...).  Such an element has no address of its
     own -- the vector is bit-packed -- and LLVM's verifier rejects the GEP
     ("GEP into vector with non-byte-addressable element type", mirroring
     [DataLayout::typeSizeEqualsStoreSize]).  No well-formed program
     performs one, so the semantics may treat it as undefined behavior. *)
  Definition gep_indexable (t : dtyp) : bool :=
    match t with
    | DTYPE_Array true _ ta => N.eqb (bit_sizeof_dtyp ta) (8 * store_size_dtyp ta)
    | _ => true
    end.

  (* The distance between consecutive elements when indexing into an array
     ([vector = false]) or a vector ([vector = true]).  Array elements sit at
     their alloc size, but a vector is bit-packed, so its elements are
     contiguous at their *store* size -- e.g. element 2 of <3 x i24> is at
     byte 6, of [3 x i24] at byte 8.  The two differ for over-aligned element
     types such as [i24].  LangRef does not say this; it is LLVM's
     [generic_gep_type_iterator::getSequentialElementStride]
     (GetElementPtrTypeIterator.h, llvm-project PR #75448).  [gep_indexable]
     guarantees the vector's elements are byte-addressable, so the store
     size is exactly where the next element's bits begin. *)
  Definition sequential_stride (vector : bool) (ta : dtyp) : N :=
    if vector then store_size_dtyp ta else alloc_size_dtyp ta.

  (** ** Indices

      LangRef (getelementptr): "When indexing into a (optionally packed)
      structure, only i32 integer constants are allowed ... When indexing
      into an array, pointer or vector, integers of any width are allowed,
      and they are not required to be constant.  These integers are treated
      as signed values where relevant."  And: "If the offsets have a
      different width from the pointer's index type, they are sign-extended
      or truncated to the width of the pointer's index type." *)

  (* The width of the pointer index type, in bits.  Vellvm's index type is
     the pointer size, also under the infinite-pointer parameters. *)
  Definition gep_index_bits : Z := 8 * Z.of_N pointer_size.

  (* The signed value of the low [gep_index_bits] bits of [k]. *)
  Definition trunc_to_index (k : Z) : Z :=
    let half := 2 ^ (gep_index_bits - 1) in
    (k + half) mod (2 * half) - half.

  (* The value of an index of an array, vector, or pointer step, as it
     enters the address computation.  An [iN] index of any width N is read
     as signed, which sign-extends a narrow one, and one wider than the
     index type is truncated to it.  An [iptr] is the index type itself
     (unbounded under the infinite-pointer parameters). *)
  Definition gep_index (v : dvalue) : option Z :=
    match v with
    | DVALUE_Base (DVALUE_I sz i) =>
        Some (if Zpos sz <=? gep_index_bits then signed i else trunc_to_index (signed i))
    | DVALUE_Base (DVALUE_Iptr i) => Some (to_Z i)
    | _ => None
    end.

  (* The byte offset of field [n] of a struct with fields [ts], and the
     field's type. *)
  Definition gep_struct_field (packed : bool) (ts : list dtyp) (n : nat) : option (N * dtyp) :=
    match nth_error ts n with
    | None => None
    | Some t' =>
        let before := firstn n ts in
        Some (if packed
              then fold_left (fun acc t => acc + alloc_size_dtyp t)%N before 0%N
              else pad_to_align (dtyp_alignment t')
                     (fold_left (fun acc t => pad_to_align (dtyp_alignment t) acc + alloc_size_dtyp t)%N before 0%N),
              t')
    end.

  Fixpoint gep_steps_h (t:dtyp) (vs:list dvalue): EOUP (list (Z * Z)) :=
    match vs with
    | v :: vs' =>
        if negb (gep_indexable t)
        then raise_ub "getelementptr into a vector with non-byte-addressable element type"
        else
        match v, t with
        | DVALUE_Base DVALUE_Poison, _ => ret Pois
        | _, DTYPE_Array vec _ ta =>
            match gep_index v with
            | Some k => cons (k, Z.of_N (sequential_stride vec ta)) <$> gep_steps_h ta vs'
            | None => raise_error "gep_steps_h: index is not an integer"
            end
        | DVALUE_Base (DVALUE_I 32 i), DTYPE_Struct packed ts =>
            match gep_struct_field packed ts (BinIntDef.Z.to_nat (unsigned i)) with
            | Some (offset, t') => cons (Z.of_N offset, 1) <$> gep_steps_h t' vs'
            | None => raise_error "gep_steps_h: no such struct field"
            end
        | _, DTYPE_Struct _ _ => raise_error "gep_steps_h: a struct index must be an i32"
        | _, _ => raise_error "gep_steps_h: indexing into a non-aggregate type"
        end
    | [] => ret (NoPois [])
    end.

  Definition gep_steps (t:dtyp) (vs:list dvalue) : EOUP (list (Z * Z)) :=
    match vs with
    | [] => raise_error "gep_steps: no indices"
    | DVALUE_Base DVALUE_Poison :: _ => ret Pois
    | v :: vs' =>
        match gep_index v with
        | Some k => cons (k, Z.of_N (alloc_size_dtyp t)) <$> gep_steps_h t vs'
        | None => raise_error "gep_steps: index is not an integer"
        end
    end.

  Definition gep_offset (steps : list (Z * Z)) : Z :=
    fold_left (fun off '(k, size) => off + k * size) steps 0.

  (** ** The no-wrap flags

      LangRef (getelementptr): with [nusw], [nuw], or [inbounds], "If any of
      the rules are violated, the result value is a poison value". *)

  Definition in_signed_index_range (x : Z) : bool :=
    (- 2 ^ (gep_index_bits - 1) <=? x) && (x <? 2 ^ (gep_index_bits - 1)).

  Definition in_unsigned_index_range (x : Z) : bool :=
    (0 <=? x) && (x <? 2 ^ gep_index_bits).

  (* LangRef [nusw]: the index fits the index type (trunc nsw); each
     index * size does not wrap (mul nsw); nor does each partial sum of the
     offsets (add nsw); nor does adding that sum to the address, truncated to
     the index type and read as unsigned.  [addr] is that truncated address
     and [off] the offset so far. *)
  Fixpoint gep_nusw_ok (addr off : Z) (steps : list (Z * Z)) : bool :=
    match steps with
    | [] => true
    | (k, size) :: steps' =>
        let o := k * size in
        let off' := off + o in
        in_signed_index_range k && in_signed_index_range o
        && in_signed_index_range off' && in_unsigned_index_range (addr + off')
        && gep_nusw_ok addr off' steps'
    end.

  (* LangRef [nuw]: the same rules with every index and offset read as
     unsigned. *)
  Fixpoint gep_nuw_ok (addr off : Z) (steps : list (Z * Z)) : bool :=
    match steps with
    | [] => true
    | (k, size) :: steps' =>
        let o := (k mod 2 ^ gep_index_bits) * size in
        let off' := off + o in
        in_unsigned_index_range o && in_unsigned_index_range off'
        && in_unsigned_index_range (addr + off')
        && gep_nuw_ok addr off' steps'
    end.

  (* The part of LangRef [inbounds] that does not need the bounds of an
     allocated object: nothing is allocated at address 0, and "the only
     pointer in bounds of the null pointer ... is the null pointer itself", so
     from a null base every step must stay at offset 0.  Being in bounds of
     a real allocated object is not checked. *)
  Fixpoint gep_inbounds_null_ok (off : Z) (steps : list (Z * Z)) : bool :=
    match steps with
    | [] => true
    | (k, size) :: steps' =>
        let off' := off + k * size in
        (off' =? 0) && gep_inbounds_null_ok off' steps'
    end.

  (* The rules about truncating an index wider than the index type, which
     [gep_steps] has already done.  LangRef [nusw]: "the truncation to the
     pointer index type preserves the signed value (trunc nsw)"; [nuw]: "the
     truncation to the pointer index type preserves the unsigned value
     (trunc nuw)".  An index no wider than the index type is not truncated. *)
  Definition gep_index_trunc_ok (unsigned_rule : bool) (v : dvalue) : bool :=
    match v with
    | DVALUE_Base (DVALUE_I sz i) =>
        (Zpos sz <=? gep_index_bits)
        || (if unsigned_rule
            then in_unsigned_index_range (unsigned i)
            else in_signed_index_range (signed i))
    | _ => true
    end.

  Definition gep_trunc_violated (flags : gep_flags) (vs : list dvalue) : bool :=
    ((gep_inbounds flags || gep_nusw flags) && negb (forallb (gep_index_trunc_ok false) vs))
    || (gep_nuw flags && negb (forallb (gep_index_trunc_ok true) vs)).

  (* Whether the flags make the result poison.  [inbounds] implies [nusw]. *)
  Definition gep_flags_violated (flags : gep_flags) (addr : Z) (steps : list (Z * Z)) : bool :=
    let a := addr mod 2 ^ gep_index_bits in
    ((gep_inbounds flags || gep_nusw flags) && negb (gep_nusw_ok a 0 steps))
    || (gep_nuw flags && negb (gep_nuw_ok a 0 steps))
    || (gep_inbounds flags && (addr =? 0) && negb (gep_inbounds_null_ok 0 steps)).

  (* At the toplevel, GEP takes a [dvalue] as an argument that must contain a
     pointer, but no other pointer can be recursively followed.  The pointer
     sets the block into which we look, and the initial offset. *)
  (* TODO: This should take into account padding too... May break get_consecutive_ptrs and friends. *)
  Definition handle_gep_ptr (flags : gep_flags) (t:dtyp) (a:ptr) (vs:list dvalue) : EOUP ptr :=
    let ptr := ptr_to_int a in
    steps <- gep_steps t vs ;;
    if gep_flags_violated flags ptr steps || gep_trunc_violated flags vs
    then raise_ret Pois
    else NoPois <$> (int_to_ptr (ptr + gep_offset steps) (ptr_provenance a)).

  Lemma handle_gep_ptr_0 :
    forall (dt : dtyp) (p : ptr),
      handle_gep_ptr gep_no_flags dt p [DVALUE_Base (DVALUE_Iptr zero_iptr)] = ret p.
  Proof.
    intros dt p.
    unfold handle_gep_ptr; cbn.
    rewrite to_Z_0.
    replace (ptr_to_int p + 0 * Z.of_N (alloc_size_dtyp dt))%Z with (ptr_to_int p) by ring.
    rewrite int_to_ptr_ptr_to_int; auto.
  Qed.

  Lemma handle_gep_ptr_nil :
    forall flags (dt : dtyp) (p : ptr),
      handle_gep_ptr flags dt p [] = raise_error "gep_steps: no indices"%string.
  Proof.
    intros flags dt p.
    unfold handle_gep_ptr; cbn; auto.
  Qed.

  Lemma handle_gep_ptr_ix :
    forall (dt : dtyp) (p p' : ptr) ix,
      handle_gep_ptr gep_no_flags dt p [DVALUE_Base (DVALUE_Iptr ix)] = ret p' ->
      ptr_to_int p' = (ptr_to_int p + Z.of_N (alloc_size_dtyp dt) * to_Z ix)%Z.
  Proof.
    intros dt p p' ix GEP.
    unfold handle_gep_ptr in *; cbn in *.
    break_match_hyp; inv GEP.
    match goal with
    | H : _ = raise_ret p' |- _ => apply ptr_to_int_int_to_ptr in H; rewrite H
    end.
    ring.
  Qed.

  Lemma handle_gep_ptr_ix_OOM :
    forall (dt : dtyp) (p p' : ptr) ix msg,
      handle_gep_ptr gep_no_flags dt p [DVALUE_Base (DVALUE_Iptr ix)] = raise_oom msg ->
      exists msg',
        int_to_ptr (ptr_to_int p + Z.of_N (alloc_size_dtyp dt) * to_Z ix)%Z (ptr_provenance p) = raise_oom msg'.
  Proof.
    intros dt p p' ix msg GEP.
    unfold handle_gep_ptr in *; cbn in *.
    exists msg.
    replace (ptr_to_int p + Z.of_N (alloc_size_dtyp dt) * to_Z ix)%Z
      with (ptr_to_int p + to_Z ix * Z.of_N (alloc_size_dtyp dt))%Z by ring.
    break_match_hyp; inv GEP.
    auto.
  Qed.

  Lemma handle_gep_ptr_ix' :
    forall (dt : dtyp) (p p' : ptr) ix,
      ret p' = int_to_ptr (ptr_to_int p + Z.of_N (alloc_size_dtyp dt) * to_Z ix)%Z (ptr_provenance p) ->
      handle_gep_ptr gep_no_flags dt p [DVALUE_Base (DVALUE_Iptr ix)] = ret p'.
  Proof.
    intros dt p p' ix IX.
    unfold handle_gep_ptr in *; cbn in *.
    replace (ptr_to_int p + to_Z ix * Z.of_N (alloc_size_dtyp dt))%Z
      with (ptr_to_int p + Z.of_N (alloc_size_dtyp dt) * to_Z ix)%Z by ring.
    rewrite <- IX.
    reflexivity.
  Qed.

  Lemma handle_gep_ptr_ix'_OOM :
    forall (dt : dtyp) (p p' : ptr) ix msg,
      int_to_ptr (ptr_to_int p + Z.of_N (alloc_size_dtyp dt) * to_Z ix)%Z (ptr_provenance p) = raise_oom msg ->
      exists msg', handle_gep_ptr gep_no_flags dt p [DVALUE_Base (DVALUE_Iptr ix)] = raise_oom msg'.
  Proof.
    intros dt p p' ix msg IX.
    unfold handle_gep_ptr in *; cbn in *.
    exists msg.
    replace (ptr_to_int p + to_Z ix * Z.of_N (alloc_size_dtyp dt))%Z
      with (ptr_to_int p + Z.of_N (alloc_size_dtyp dt) * to_Z ix)%Z by ring.
    rewrite IX.
    auto.
  Qed.

  Lemma handle_gep_ptr_preserves_provenance :
    forall flags (dt : dtyp) ixs (p p' : ptr),
      handle_gep_ptr flags dt p ixs = ret p' ->
      ptr_provenance p = ptr_provenance p'.
  Proof.
    intros flags dt ixs p p' GEP.
    unfold handle_gep_ptr in GEP; cbn in GEP.
    repeat break_match_hyp_inv;
      cbn in *;
      symmetry;
      eapply int_to_ptr_provenance; eauto.
  Qed.

  Definition eval_gep (flags : gep_flags) (t:dtyp) (dv:dvalue) (vs:list dvalue) : EOU dvalue :=
    match dv with
    | DVALUE_Base (DVALUE_Pointer a) =>
        catch_pois (DVALUE_Base DVALUE_Poison)
          ((fun x => DVALUE_Base (DVALUE_Pointer x)) <$> handle_gep_ptr flags t a vs)
          ret
    | DVALUE_Base DVALUE_Poison => ret (DVALUE_Base DVALUE_Poison)
    | _ => raise_error "non-ptr"%string
    end.
End GEP.
