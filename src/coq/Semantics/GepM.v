Require Import ZArith String List Lia.

From ExtLib Require Import
     Structures.Monad
     Structures.Functor.

From Vellvm Require Import
     DynamicTypes
     LLVMEvents
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Utils.Error
     Utils.Monads
     Utils.Tactics.

Import ListNotations.
Import MonadNotation.

Module Type GEPM (Addr:ADDRESS) (PTOI : PTOI Addr) (PROV : PROVENANCE Addr) (ITOP : ITOP Addr PROV PTOI) (IP:INTPTR) (SIZEOF:Sizeof) (LLVMEvents:LLVM_INTERACTIONS(Addr)(IP)(SIZEOF)).
  Import LLVMEvents.
  Import DV.
  Import PROV.
  Import Addr.
  Import PTOI.
  Import ITOP.
  Import IP.
  Import SIZEOF.

  (* TODO: should this be here? *)
  Parameter handle_gep_h : dtyp -> Z -> list dvalue -> err Z.

  Parameter handle_gep_addr : dtyp -> addr -> list dvalue -> err addr.

  Parameter handle_gep_addr_0 :
    forall (dt : dtyp) (p : addr),
      handle_gep_addr dt p [DVALUE_IPTR IP.zero] = inr p.

  Parameter handle_gep_addr_ix :
    forall (dt : dtyp) (p p' : addr) ix,
      handle_gep_addr dt p [DVALUE_IPTR ix] = inr p' ->
      ptr_to_int p' = (ptr_to_int p + Z.of_N (sizeof_dtyp dt) * IP.to_Z ix)%Z.

  Parameter handle_gep_addr_ix' :
    forall (dt : dtyp) (p p' : addr) ix,
      p' = int_to_ptr (ptr_to_int p + Z.of_N (sizeof_dtyp dt) * IP.to_Z ix)%Z (address_provenance p) ->
      handle_gep_addr dt p [DVALUE_IPTR ix] = inr p'.

  Parameter handle_gep_addr_preserves_provenance :
    forall (dt : dtyp) ixs (p p' : addr),
      handle_gep_addr dt p ixs = inr p' ->
      address_provenance p = address_provenance p'.

  Definition handle_gep (t:dtyp) (dv:dvalue) (vs:list dvalue) : err dvalue :=
    match dv with
    | DVALUE_Addr a => fmap DVALUE_Addr (handle_gep_addr t a vs)
    | _ => failwith "non-address"
    end.
End GEPM.

Module Make (ADDR : ADDRESS) (IP : INTPTR) (SIZE : Sizeof) (Events : LLVM_INTERACTIONS(ADDR)(IP)(SIZE)) (PTOI : PTOI ADDR) (PROV : PROVENANCE ADDR) (ITOP : ITOP ADDR PROV PTOI) <: GEPM(ADDR)(PTOI)(PROV)(ITOP)(IP)(SIZE)(Events).
  Import ADDR.
  Import Events.
  Import DV.
  Import SIZE.
  Import PTOI.
  Import ITOP.
  Import PROV.

  (** ** Get Element Pointer
      Retrieve the address of a subelement of an indexable (i.e. aggregate) [dtyp] [t] (i.e. vector, array, struct, packed struct).
      The [off]set parameter contains the current entry address of the aggregate structure being analyzed, while the list
      of [dvalue] [vs] describes the indexes of interest used to access the subelement.
      The interpretation of these values slightly depends on the type considered.
      But essentially, for instance in a vector or an array, the head value should be an [i32] describing the index of interest.
      The offset is therefore incremented by this index times the size of the type of elements stored. Finally, a recursive call
      at this new offset allows for deeper unbundling of a nested structure.
   *)
  Fixpoint handle_gep_h (t:dtyp) (off:Z) (vs:list dvalue): err Z :=
    match vs with
    | v :: vs' =>
      match v with
      | DVALUE_I32 i =>
        let k := unsigned i in
        let n := BinIntDef.Z.to_nat k in
        match t with
        | DTYPE_Vector _ ta
        | DTYPE_Array _ ta =>
          handle_gep_h ta (off + k * (Z.of_N (sizeof_dtyp ta))) vs'
        | DTYPE_Struct ts
        | DTYPE_Packed_struct ts => (* Handle these differently in future *)
          let offset := fold_left (fun acc t => (acc + (Z.of_N (sizeof_dtyp t))))%Z
                                  (firstn n ts) 0%Z in
          match nth_error ts n with
          | None => failwith "overflow"
          | Some t' =>
            handle_gep_h t' (off + offset) vs'
          end
        | _ => failwith ("non-i32-indexable type")
        end
      | DVALUE_I8 i =>
        let k := unsigned i in
        let n := BinIntDef.Z.to_nat k in
        match t with
        | DTYPE_Vector _ ta
        | DTYPE_Array _ ta =>
          handle_gep_h ta (off + k * (Z.of_N (sizeof_dtyp ta))) vs'
        | _ => failwith ("non-i8-indexable type")
        end
      | DVALUE_I64 i =>
        let k := unsigned i in
        let n := BinIntDef.Z.to_nat k in
        match t with
        | DTYPE_Vector _ ta
        | DTYPE_Array _ ta =>
          handle_gep_h ta (off + k * (Z.of_N (sizeof_dtyp ta))) vs'
        | _ => failwith ("non-i64-indexable type")
        end
      | _ => failwith "non-I32 index"
      end
    | [] => ret off
    end.

  (* At the toplevel, GEP takes a [dvalue] as an argument that must contain a pointer, but no other pointer can be recursively followed.
     The pointer set the block into which we look, and the initial offset. The first index value add to the initial offset passed to [handle_gep_h] for the actual access to structured data.
   *)
  Definition handle_gep_addr (t:dtyp) (a:addr) (vs:list dvalue) : err addr :=
    let ptr := ptr_to_int a in
    let prov := address_provenance a in
    match vs with
    | DVALUE_I32 i :: vs' => (* TODO: Handle non i32 / i64 indices *)
      ptr' <- handle_gep_h t (ptr + Z.of_N (sizeof_dtyp t) * (unsigned i)) vs' ;;
      ret (int_to_ptr ptr' prov)
    | DVALUE_I64 i :: vs' =>
      ptr' <- handle_gep_h t (ptr + Z.of_N (sizeof_dtyp t) * (unsigned i)) vs' ;;
      ret (int_to_ptr ptr' prov)
    | DVALUE_IPTR i :: vs' =>
      ptr' <- handle_gep_h t (ptr + Z.of_N (sizeof_dtyp t) * (IP.to_Z i)) vs' ;;
      ret (int_to_ptr ptr' prov)
    | _ => failwith "non-I32 index"
    end.

  Lemma handle_gep_addr_0 :
    forall (dt : dtyp) (p : addr),
      handle_gep_addr dt p [DVALUE_IPTR IP.zero] = inr p.
  Proof.
    intros dt p.
    cbn.
    rewrite IP.to_Z_0.
    replace (ptr_to_int p + Z.of_N (sizeof_dtyp dt) * 0)%Z with (ptr_to_int p) by lia.
    rewrite int_to_ptr_ptr_to_int; auto.
  Qed.

  Lemma handle_gep_addr_ix :
    forall (dt : dtyp) (p p' : addr) ix,
      handle_gep_addr dt p [DVALUE_IPTR ix] = inr p' ->
      ptr_to_int p' = (ptr_to_int p + Z.of_N (sizeof_dtyp dt) * IP.to_Z ix)%Z.
  Proof.
    intros dt p p' ix GEP.
    cbn in *.
    inv GEP.
    rewrite ptr_to_int_int_to_ptr.
    reflexivity.
  Qed.

  Lemma handle_gep_addr_ix' :
    forall (dt : dtyp) (p p' : addr) ix,
      p' = int_to_ptr (ptr_to_int p + Z.of_N (sizeof_dtyp dt) * IP.to_Z ix)%Z (address_provenance p) ->
      handle_gep_addr dt p [DVALUE_IPTR ix] = inr p'.
  Proof.
    intros dt p p' ix IX.
    cbn.
    subst.
    reflexivity.
  Qed.

  Lemma handle_gep_addr_preserves_provenance :
    forall (dt : dtyp) ixs (p p' : addr),
      handle_gep_addr dt p ixs = inr p' ->
      address_provenance p = address_provenance p'.
  Proof.
    intros dt ixs.
    induction ixs;
      intros p p' GEP;
      [inversion GEP|].

    cbn in GEP.
    destruct a; inversion GEP.
    - break_match_hyp; inv GEP.
      rewrite int_to_ptr_provenance.
      reflexivity.
    - break_match_hyp; inv GEP.
      rewrite int_to_ptr_provenance.
      reflexivity.
    - break_match_hyp; inv GEP.
      rewrite int_to_ptr_provenance.
      reflexivity.
  Qed.

  Definition handle_gep (t:dtyp) (dv:dvalue) (vs:list dvalue) : err dvalue :=
    match dv with
    | DVALUE_Addr a => fmap DVALUE_Addr (handle_gep_addr t a vs)
    | _ => failwith "non-address"
    end.
End Make.
