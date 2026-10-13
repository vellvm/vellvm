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
      Retrieve the address of a subelement of an indexable (i.e. aggregate) [dtyp] [t] (i.e. vector, array, struct, packed struct).
      The [off]set parameter contains the current entry address of the aggregate structure being analyzed, while the list
      of [dvalue] [vs] describes the indexes of interest used to access the subelement.
      The interpretation of these values slightly depends on the type considered.
      But essentially, for instance in a vector or an array, the head value should be an [i32] describing the index of interest.
      The offset is therefore incremented by this index times the size of the type of elements stored. Finally, a recursive call
      at this new offset allows for deeper unbundling of a nested structure.
   *)
  Fixpoint handle_gep_h (t:dtyp) (off:Z) (vs:list dvalue): EOUP Z :=
    match vs with
    | v :: vs' =>
        match v with
        | DVALUE_Base (DVALUE_I 8 i) =>
            let k := signed i in
            match t with
            | DTYPE_Array v _ ta =>
                handle_gep_h ta (off + k * (Z.of_N (alloc_size_dtyp ta))) vs'                
            | _ => raise_error ("non-i8-indexable type")
            end
        | DVALUE_Base (DVALUE_I 32 i) =>
            let k := unsigned i in
            let ks := signed i in
            let n := BinIntDef.Z.to_nat k in
            match t with
            | DTYPE_Array v _ ta =>
                handle_gep_h ta (off + ks * (Z.of_N (alloc_size_dtyp ta))) vs'                          
            | DTYPE_Struct false ts =>
                match nth_error ts n with
                | None => raise_error "overflow"
                | Some t' =>
                    let end_of_prev_field := fold_left (fun acc t => pad_to_align (dtyp_alignment t) acc + alloc_size_dtyp t)%N (firstn n ts) 0%N in
                    let offset := pad_to_align (dtyp_alignment t') end_of_prev_field in
                    handle_gep_h t' (off + Z.of_N offset) vs'
                end
            | DTYPE_Struct true ts =>
                let offset := fold_left (fun acc t => acc + alloc_size_dtyp t)%N
                                (firstn n ts) 0%N in
                match nth_error ts n with
                | None => raise_error "overflow"
                | Some t' =>
                    handle_gep_h t' (off + Z.of_N offset) vs'
                end

            | _ => raise_error ("non-i32-indexable type")
            end
              
        | DVALUE_Base (DVALUE_I 64 i) =>
            let k := signed i in
            match t with
            | DTYPE_Array false _ ta =>
                handle_gep_h ta (off + k * (Z.of_N (alloc_size_dtyp ta))) vs'
            | DTYPE_Array true _ ta =>
                handle_gep_h ta (off + k * (Z.of_N (alloc_size_dtyp ta))) vs'
            | _ => raise_error ("non-i64-indexable type")
            end
        | DVALUE_Base (DVALUE_Iptr i) =>
            let k := to_Z i in
            match t with
            | DTYPE_Array v  _ ta =>
                handle_gep_h ta (off + k * (Z.of_N (alloc_size_dtyp ta))) vs'                
            | _ => raise_error ("non-iptr-indexable type")
            end
        | DVALUE_Base (DVALUE_Poison) =>
            ret Pois 
        | _ => raise_error "handle_gep_h: unsupported index type"
        end
    | [] => ret off
    end.

  (* At the toplevel, GEP takes a [dvalue] as an argument that must contain a pointer, but no other pointer can be recursively followed.
     The pointer set the block into which we look, and the initial offset. The first index value add to the initial offset passed to [handle_gep_h] for the actual access to structured data.
   *)
  (* TODO: This should take into account padding too... May break get_consecutive_ptrs and friends. *)
  Definition handle_gep_ptr (t:dtyp) (a:ptr) (vs:list dvalue) : EOUP ptr :=
    let ptr := ptr_to_int a in
    let prov := ptr_provenance a in
    match vs with
    | DVALUE_Base (DVALUE_I 8 i) :: vs' =>
        ptr' <- handle_gep_h t (ptr + Z.of_N (alloc_size_dtyp t) * (signed i)) vs' ;;
        NoPois <$> (int_to_ptr ptr' prov)
    | DVALUE_Base (DVALUE_I 32 i) :: vs' =>
        ptr' <- handle_gep_h t (ptr + Z.of_N (alloc_size_dtyp t) * (signed i)) vs' ;;
        NoPois <$> (int_to_ptr ptr' prov)
    | DVALUE_Base (DVALUE_I 64 i) :: vs' =>
        ptr' <- handle_gep_h t (ptr + Z.of_N (alloc_size_dtyp t) * (signed i)) vs' ;;
        NoPois <$> (int_to_ptr ptr' prov)
    | DVALUE_Base (DVALUE_Iptr i) :: vs' =>
        ptr' <- handle_gep_h t (ptr + Z.of_N (alloc_size_dtyp t) * (to_Z i)) vs' ;;
        NoPois <$> (int_to_ptr ptr' prov)
    | DVALUE_Base (DVALUE_Poison)::_ =>
        ret Pois
    | [] => raise_error "handle_gep_ptr: no indices"
    | _ => raise_error "handle_gep_ptr: unsupported index type"
    end.

  Lemma handle_gep_ptr_0 :
    forall (dt : dtyp) (p : ptr),
      handle_gep_ptr dt p [DVALUE_Base (DVALUE_Iptr zero_iptr)] = ret p.
  Proof.
    intros dt p.
    cbn.
    rewrite to_Z_0.
    replace (ptr_to_int p + Z.of_N (alloc_size_dtyp dt) * 0)%Z with (ptr_to_int p) by lia.
    rewrite int_to_ptr_ptr_to_int; auto.
  Qed.

  Lemma handle_gep_ptr_nil :
    forall (dt : dtyp) (p : ptr),
      handle_gep_ptr dt p [] = raise_error "handle_gep_ptr: no indices"%string.
  Proof.
    intros dt p.
    cbn; auto.
  Qed.

  Lemma handle_gep_ptr_ix :
    forall (dt : dtyp) (p p' : ptr) ix,
      handle_gep_ptr dt p [DVALUE_Base (DVALUE_Iptr ix)] = ret p' ->
      ptr_to_int p' = (ptr_to_int p + Z.of_N (alloc_size_dtyp dt) * to_Z ix)%Z.
  Proof.
    intros dt p p' ix GEP.
    cbn in *.
    break_match_hyp; inv GEP.
    erewrite ptr_to_int_int_to_ptr; eauto.
  Qed.

  Lemma handle_gep_ptr_ix_OOM :
    forall (dt : dtyp) (p p' : ptr) ix msg,
      handle_gep_ptr dt p [DVALUE_Base (DVALUE_Iptr ix)] = raise_oom msg ->
      exists msg',
        int_to_ptr (ptr_to_int p + Z.of_N (alloc_size_dtyp dt) * to_Z ix)%Z (ptr_provenance p) = raise_oom msg'.
  Proof.
    intros dt p p' ix msg GEP.
    cbn in *.
    exists msg.
    break_match_hyp; inv GEP.    
    auto.
  Qed.

  Lemma handle_gep_ptr_ix' :
    forall (dt : dtyp) (p p' : ptr) ix,
      ret p' = int_to_ptr (ptr_to_int p + Z.of_N (alloc_size_dtyp dt) * to_Z ix)%Z (ptr_provenance p) ->
      handle_gep_ptr dt p [DVALUE_Base (DVALUE_Iptr ix)] = ret p'.
  Proof.
    intros dt p p' ix IX.
    cbn in *.
    inv IX.
    reflexivity.
  Qed.

  Lemma handle_gep_ptr_ix'_OOM :
    forall (dt : dtyp) (p p' : ptr) ix msg,
      int_to_ptr (ptr_to_int p + Z.of_N (alloc_size_dtyp dt) * to_Z ix)%Z (ptr_provenance p) = raise_oom msg ->
      exists msg', handle_gep_ptr dt p [DVALUE_Base (DVALUE_Iptr ix)] = raise_oom msg'.
  Proof.
    intros dt p p' ix msg IX.
    cbn in *.
    exists msg.
    rewrite IX.
    auto.
  Qed.

  Lemma handle_gep_ptr_preserves_provenance :
    forall (dt : dtyp) ixs (p p' : ptr),
      handle_gep_ptr dt p ixs = ret p' ->
      ptr_provenance p = ptr_provenance p'.
  Proof.
    intros dt ixs.
    induction ixs;
      intros p p' GEP;
      [inversion GEP|].

    cbn in GEP.
    repeat break_match_hyp_inv;
      cbn in *;
      symmetry;
      eapply int_to_ptr_provenance; eauto.
  Qed.

  (** ** The no-wrap flags

      LangRef (getelementptr): with [nusw], [nuw], or [inbounds], "If any of
      the rules are violated, the result value is a poison value".  The rules
      are stated over the steps of the address computation, so [gep_steps]
      lists them: for each index, its value (sign-extended) and what it is
      scaled by.  A struct field contributes its byte offset, scaled by 1.
      [None] means a poison or unsupported index, which [handle_gep_ptr]
      deals with.  The type dispatch mirrors [handle_gep_h]. *)
  Fixpoint gep_steps_h (t:dtyp) (vs:list dvalue) : option (list (Z * Z)) :=
    match vs with
    | [] => Some []
    | v :: vs' =>
        let array_step k :=
          match t with
          | DTYPE_Array _ _ ta =>
              option_map (cons (k, Z.of_N (alloc_size_dtyp ta))) (gep_steps_h ta vs')
          | _ => None
          end in
        match v with
        | DVALUE_Base (DVALUE_I 8 i) => array_step (signed i)
        | DVALUE_Base (DVALUE_I 64 i) => array_step (signed i)
        | DVALUE_Base (DVALUE_Iptr i) => array_step (to_Z i)
        | DVALUE_Base (DVALUE_I 32 i) =>
            let n := Z.to_nat (unsigned i) in
            match t with
            | DTYPE_Struct false ts =>
                match nth_error ts n with
                | None => None
                | Some t' =>
                    let end_of_prev_field := fold_left (fun acc t => pad_to_align (dtyp_alignment t) acc + alloc_size_dtyp t)%N (firstn n ts) 0%N in
                    let offset := pad_to_align (dtyp_alignment t') end_of_prev_field in
                    option_map (cons (Z.of_N offset, 1)) (gep_steps_h t' vs')
                end
            | DTYPE_Struct true ts =>
                match nth_error ts n with
                | None => None
                | Some t' =>
                    let offset := fold_left (fun acc t => acc + alloc_size_dtyp t)%N (firstn n ts) 0%N in
                    option_map (cons (Z.of_N offset, 1)) (gep_steps_h t' vs')
                end
            | _ => array_step (signed i)
            end
        | _ => None
        end
    end.

  (* The first index steps over whole objects of type [t]. *)
  Definition gep_steps (t:dtyp) (vs:list dvalue) : option (list (Z * Z)) :=
    let first vs' k := option_map (cons (k, Z.of_N (alloc_size_dtyp t))) (gep_steps_h t vs') in
    match vs with
    | DVALUE_Base (DVALUE_I 8 i) :: vs' => first vs' (signed i)
    | DVALUE_Base (DVALUE_I 32 i) :: vs' => first vs' (signed i)
    | DVALUE_Base (DVALUE_I 64 i) :: vs' => first vs' (signed i)
    | DVALUE_Base (DVALUE_Iptr i) :: vs' => first vs' (to_Z i)
    | _ => None
    end.

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
  Definition gep_flags_violated (flags : gep_flags) (t:dtyp) (addr : Z) (vs:list dvalue) : bool :=
    match gep_steps t vs with
    | None => false
    | Some steps =>
        let a := addr mod 2 ^ gep_index_bits in
        ((gep_inbounds flags || gep_nusw flags) && negb (gep_nusw_ok a 0 steps))
        || (gep_nuw flags && negb (gep_nuw_ok a 0 steps))
        || (gep_inbounds flags && (addr =? 0) && negb (gep_inbounds_null_ok 0 steps))
    end.

  Definition eval_gep (flags : gep_flags) (t:dtyp) (dv:dvalue) (vs:list dvalue) : EOU dvalue :=
    match dv with
    | DVALUE_Base (DVALUE_Pointer a) =>
        if gep_flags_violated flags t (ptr_to_int a) vs
        then ret (DVALUE_Base DVALUE_Poison)
        else
          catch_pois (DVALUE_Base DVALUE_Poison)
            ((fun x => DVALUE_Base (DVALUE_Pointer x)) <$> handle_gep_ptr t a vs)
            ret
    | DVALUE_Base DVALUE_Poison => ret (DVALUE_Base DVALUE_Poison)
    | _ => raise_error "non-ptr"%string
    end.
End GEP.
