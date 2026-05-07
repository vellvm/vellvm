From Vellvm Require Import
  Utilities
  Syntax
  VellvmIntegers
  Semantics.LLVMParams
  Semantics.MemoryAddress
  Semantics.Memory.Sizeof.

Module Type GEPM (LP:LLVMParams).
  Import LP.DV.
  Import LP.PROV.
  Import LP.ADDR.
  Import LP.PTOI.
  Import LP.ITOP.
  Import LP.IP.
  Import LP.SZ.

  (** ** Get Element Pointer
      Retrieve the address of a subelement of an indexable (i.e. aggregate) [dtyp] [t] (i.e. vector, array, struct, packed struct).
      The [off]set parameter contains the current entry address of the aggregate structure being analyzed, while the list
      of [dvalue] [vs] describes the indexes of interest used to access the subelement.
      The interpretation of these values slightly depends on the type considered.
      But essentially, for instance in a vector or an array, the head value should be an [i32] describing the index of interest.
      The offset is therefore incremented by this index times the size of the type of elements stored. Finally, a recursive call
      at this new offset allows for deeper unbundling of a nested structure.
   *)
  Fixpoint handle_gep_h (t:dtyp) (off:Z) (vs:list dvalue): EOB Z :=
    match vs with
    | v :: vs' =>
      match v with
      | @DVALUE_I 8 i =>
        let k := signed i in
        let n := BinIntDef.Z.to_nat k in
        match t with
        | DTYPE_Array _ ta
        | DTYPE_Vector _ ta =>
            handle_gep_h ta (off + k * (Z.of_N (sizeof_dtyp ta))) vs'
        | _ => raise_error ("non-i8-indexable type")
        end
      | @DVALUE_I 32 i =>
        let k := unsigned i in
        let ks := signed i in
        let n := BinIntDef.Z.to_nat k in
        match t with
        | DTYPE_Array _ ta
        | DTYPE_Vector _ ta =>
            handle_gep_h ta (off + ks * (Z.of_N (sizeof_dtyp ta))) vs'
        | DTYPE_Struct ts =>
            let offset := fold_left (fun acc t => pad_to_align (dtyp_alignment t) acc + sizeof_dtyp t)%N
                            (firstn n ts) 0%N in
            match nth_error ts n with
            | None => raise_error "overflow"
            | Some t' =>
                handle_gep_h t' (off + Z.of_N offset) vs'
            end
        | DTYPE_Packed_struct ts =>
          let offset := fold_left (fun acc t => acc + sizeof_dtyp t)%N
                                  (firstn n ts) 0%N in
          match nth_error ts n with
          | None => raise_error "overflow"
          | Some t' =>
            handle_gep_h t' (off + Z.of_N offset) vs'
          end
        | _ => raise_error ("non-i32-indexable type")
        end
      | @DVALUE_I 64 i =>
        let k := signed i in
        let n := BinIntDef.Z.to_nat k in
        match t with
        | DTYPE_Array _ ta
        | DTYPE_Vector _ ta =>
            handle_gep_h ta (off + k * (Z.of_N (sizeof_dtyp ta))) vs'
        | _ => raise_error ("non-i64-indexable type")
        end
      | DVALUE_IPTR i =>
        let k := to_Z i in
        let n := BinIntDef.Z.to_nat k in
        match t with
        | DTYPE_Array _ ta
        | DTYPE_Vector _ ta =>
            handle_gep_h ta (off + k * (Z.of_N (sizeof_dtyp ta))) vs'
        | _ => raise_error ("non-iptr-indexable type")
        end
      | _ => raise_error "handle_gep_h: unsupported index type"
      end
    | [] => ret off
    end.

  (* At the toplevel, GEP takes a [dvalue] as an argument that must contain a pointer, but no other pointer can be recursively followed.
     The pointer set the block into which we look, and the initial offset. The first index value add to the initial offset passed to [handle_gep_h] for the actual access to structured data.
   *)
  (* TODO: This should take into account padding too... May break get_consecutive_ptrs and friends. *)
  Definition handle_gep_addr {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_OOM M} (t:dtyp) (a:addr) (vs:list dvalue) : M addr :=
    let ptr := ptr_to_int a in
    let prov := address_provenance a in
    match vs with
    | @DVALUE_I 8 i :: vs' =>
      ptr' <- handle_gep_h t (ptr + Z.of_N (sizeof_dtyp t) * (signed i)) vs' ;;
      ret (int_to_ptr ptr' prov)
    | @DVALUE_I 32 i :: vs' =>
      ptr' <- handle_gep_h t (ptr + Z.of_N (sizeof_dtyp t) * (signed i)) vs' ;;
      ret (int_to_ptr ptr' prov)
    | @DVALUE_I 64 i :: vs' =>
      ptr' <- handle_gep_h t (ptr + Z.of_N (sizeof_dtyp t) * (signed i)) vs' ;;
      ret (int_to_ptr ptr' prov)
    | DVALUE_IPTR i :: vs' =>
      ptr' <- handle_gep_h t (ptr + Z.of_N (sizeof_dtyp t) * (to_Z i)) vs' ;;
      ret (int_to_ptr ptr' prov)
    | [] => failwith "handle_gep_addr: no indices"
    | _ => failwith "handle_gep_addr: unsupported index type"
    end.

  Lemma handle_gep_addr_0 :
    forall (dt : dtyp) (p : addr),
      handle_gep_addr dt p [DVALUE_IPTR zero] = inr (ret p).
  Proof.
    intros dt p.
    cbn.
    rewrite to_Z_0.
    replace (ptr_to_int p + Z.of_N (sizeof_dtyp dt) * 0)%Z with (ptr_to_int p) by lia.
    rewrite int_to_ptr_ptr_to_int; auto.
  Qed.

  Lemma handle_gep_addr_nil :
    forall (dt : dtyp) (p : addr),
      handle_gep_addr dt p [] = inl "handle_gep_addr: no indices"%string.
  Proof.
    intros dt p.
    cbn; auto.
  Qed.

  Lemma handle_gep_addr_ix :
    forall (dt : dtyp) (p p' : addr) ix,
      handle_gep_addr dt p [DVALUE_IPTR ix] = inr (ret p') ->
      ptr_to_int p' = (ptr_to_int p + Z.of_N (sizeof_dtyp dt) * to_Z ix)%Z.
  Proof.
    intros dt p p' ix GEP.
    cbn in *.
    inv GEP.
    erewrite ptr_to_int_int_to_ptr; eauto.
  Qed.

  Lemma handle_gep_addr_ix_OOM :
    forall (dt : dtyp) (p p' : addr) ix msg,
      handle_gep_addr dt p [DVALUE_IPTR ix] = inr (Oom msg) ->
      exists msg',
        int_to_ptr (ptr_to_int p + Z.of_N (sizeof_dtyp dt) * to_Z ix)%Z (address_provenance p) = Oom msg'.
  Proof.
    intros dt p p' ix msg GEP.
    cbn in *.
    exists msg.
    inv GEP.
    auto.
  Qed.

  Lemma handle_gep_addr_ix' :
    forall (dt : dtyp) (p p' : addr) ix,
      ret p' = int_to_ptr (ptr_to_int p + Z.of_N (sizeof_dtyp dt) * to_Z ix)%Z (address_provenance p) ->
      handle_gep_addr dt p [DVALUE_IPTR ix] = inr (ret p').
  Proof.
    intros dt p p' ix IX.
    cbn in *.
    inv IX.
    reflexivity.
  Qed.

  Lemma handle_gep_addr_ix'_OOM :
    forall (dt : dtyp) (p p' : addr) ix msg,
      int_to_ptr (ptr_to_int p + Z.of_N (sizeof_dtyp dt) * to_Z ix)%Z (address_provenance p) = Oom msg ->
      exists msg', handle_gep_addr dt p [DVALUE_IPTR ix] = inr (Oom msg').
  Proof.
    intros dt p p' ix msg IX.
    cbn in *.
    exists msg.
    inv IX.
    auto.
  Qed.

  Lemma handle_gep_addr_preserves_provenance :
    forall (dt : dtyp) ixs (p p' : addr),
      handle_gep_addr dt p ixs = inr (ret p') ->
      address_provenance p = address_provenance p'.
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

  Definition handle_gep (t:dtyp) (dv:dvalue) (vs:list dvalue) : err (OOM dvalue) :=
    match dv with
    | DVALUE_Addr a => fmap (F:=err) (fmap DVALUE_Addr) (handle_gep_addr t a vs)
    | _ => inl "non-address"%string
    end.
End GEPM.

Module Make (LP:LLVMParams) <: GEPM(LP).
  Include GEPM LP.
End Make.
