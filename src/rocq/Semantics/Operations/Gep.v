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
      the element size), or a struct field (its byte offset, scaled by 1).
      The address is [a] plus the sum of the steps ([gep_offset]), and the
      no-wrap flags are rules about the steps (see [gep_flags_violated]).
      A poison index makes the whole result poison.
   *)
  Fixpoint gep_steps_h (t:dtyp) (vs:list dvalue): EOUP (list (Z * Z)) :=
    match vs with
    | v :: vs' =>
        match v with
        | DVALUE_Base (DVALUE_I 8 i) =>
            match t with
            | DTYPE_Array _ _ ta =>
                cons (signed i, Z.of_N (alloc_size_dtyp ta)) <$> gep_steps_h ta vs'
            | _ => raise_error ("non-i8-indexable type")
            end
        | DVALUE_Base (DVALUE_I 32 i) =>
            let n := BinIntDef.Z.to_nat (unsigned i) in
            match t with
            | DTYPE_Array _ _ ta =>
                cons (signed i, Z.of_N (alloc_size_dtyp ta)) <$> gep_steps_h ta vs'
            | DTYPE_Struct false ts =>
                match nth_error ts n with
                | None => raise_error "overflow"
                | Some t' =>
                    let end_of_prev_field := fold_left (fun acc t => pad_to_align (dtyp_alignment t) acc + alloc_size_dtyp t)%N (firstn n ts) 0%N in
                    let offset := pad_to_align (dtyp_alignment t') end_of_prev_field in
                    cons (Z.of_N offset, 1) <$> gep_steps_h t' vs'
                end
            | DTYPE_Struct true ts =>
                let offset := fold_left (fun acc t => acc + alloc_size_dtyp t)%N
                                (firstn n ts) 0%N in
                match nth_error ts n with
                | None => raise_error "overflow"
                | Some t' =>
                    cons (Z.of_N offset, 1) <$> gep_steps_h t' vs'
                end
            | _ => raise_error ("non-i32-indexable type")
            end
        | DVALUE_Base (DVALUE_I 64 i) =>
            match t with
            | DTYPE_Array _ _ ta =>
                cons (signed i, Z.of_N (alloc_size_dtyp ta)) <$> gep_steps_h ta vs'
            | _ => raise_error ("non-i64-indexable type")
            end
        | DVALUE_Base (DVALUE_Iptr i) =>
            match t with
            | DTYPE_Array _ _ ta =>
                cons (to_Z i, Z.of_N (alloc_size_dtyp ta)) <$> gep_steps_h ta vs'
            | _ => raise_error ("non-iptr-indexable type")
            end
        | DVALUE_Base (DVALUE_Poison) =>
            ret Pois
        | _ => raise_error "gep_steps_h: unsupported index type"
        end
    | [] => ret (NoPois [])
    end.

  Definition gep_steps (t:dtyp) (vs:list dvalue) : EOUP (list (Z * Z)) :=
    let first k vs' := cons (k, Z.of_N (alloc_size_dtyp t)) <$> gep_steps_h t vs' in
    match vs with
    | DVALUE_Base (DVALUE_I 8 i) :: vs' => first (signed i) vs'
    | DVALUE_Base (DVALUE_I 32 i) :: vs' => first (signed i) vs'
    | DVALUE_Base (DVALUE_I 64 i) :: vs' => first (signed i) vs'
    | DVALUE_Base (DVALUE_Iptr i) :: vs' => first (to_Z i) vs'
    | DVALUE_Base (DVALUE_Poison)::_ => ret Pois
    | [] => raise_error "gep_steps: no indices"
    | _ => raise_error "gep_steps: unsupported index type"
    end.

  Definition gep_offset (steps : list (Z * Z)) : Z :=
    fold_left (fun off '(k, size) => off + k * size) steps 0.

  (** ** The no-wrap flags

      LangRef (getelementptr): with [nusw], [nuw], or [inbounds], "If any of
      the rules are violated, the result value is a poison value". *)

  (* The width of the pointer index type, in bits.  Vellvm's index type is
     the pointer size, also under the infinite-pointer parameters. *)
  Definition gep_index_bits : Z := 8 * Z.of_N pointer_size.

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
    if gep_flags_violated flags ptr steps
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
