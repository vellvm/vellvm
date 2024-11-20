From Stdlib Require Import ZArith String List Lia.

From Stdlib Require Import
  Structures.Equalities.

From ExtLib Require Import
     Structures.Monad
     Structures.Functor.

From Vellvm Require Import
  DynamicTypes
  VellvmIntegers
  LLVMEvents
  Utils.Error
  Utils.Tactics.

From Mem Require Import
  Addresses.MemoryAddress
  Addresses.Provenance.

From LLVM_Memory Require Import
  Sizeof
  Intptr.

Import ListNotations.
Import MonadNotation.

Module Type GEPM (Addr : BASIC_ADDRESS) (IP : INTPTR) (SIZEOF : Sizeof) (LLVM_Events : LLVM_INTERACTIONS Addr IP SIZEOF).
  Import Addr.
  Import SIZEOF.
  Import LLVM_Events.

  (** ** Get Element Pointer
      Retrieve the address of a subelement of an indexable (i.e. aggregate) [dtyp] [t] (i.e. vector, array, struct, packed struct).
      The [off]set parameter contains the current entry address of the aggregate structure being analyzed, while the list
      of [dvalue] [vs] describes the indexes of interest used to access the subelement.
      The interpretation of these values slightly depends on the type considered.
      But essentially, for instance in a vector or an array, the head value should be an [i32] describing the index of interest.
      The offset is therefore incremented by this index times the size of the type of elements stored. Finally, a recursive call
      at this new offset allows for deeper unbundling of a nested structure.
   *)
  Fixpoint calculate_gep_offset (t:dtyp) (off:Z) (vs:list dvalue): err Z :=
    match vs with
    | v :: vs' =>
      match v with
      | @DVALUE_I 8 i =>
        let k := signed i in
        let n := BinIntDef.Z.to_nat k in
        match t with
        | DTYPE_Array _ ta
        | DTYPE_Vector _ ta =>
            calculate_gep_offset ta (off + k * (Z.of_N (sizeof_dtyp ta))) vs'
        | _ => failwith ("non-i8-indexable type")
        end
      | @DVALUE_I 32 i =>
        let k := unsigned i in
        let ks := signed i in
        let n := BinIntDef.Z.to_nat k in
        match t with
        | DTYPE_Array _ ta
        | DTYPE_Vector _ ta =>
            calculate_gep_offset ta (off + ks * (Z.of_N (sizeof_dtyp ta))) vs'
        | DTYPE_Struct ts =>
            let offset := fold_left (fun acc t => pad_to_align (dtyp_alignment t) acc + sizeof_dtyp t)%N
                            (firstn n ts) 0%N in
            match nth_error ts n with
            | None => failwith "overflow"
            | Some t' =>
                calculate_gep_offset t' (off + Z.of_N offset) vs'
            end
        | DTYPE_Packed_struct ts =>
          let offset := fold_left (fun acc t => acc + sizeof_dtyp t)%N
                                  (firstn n ts) 0%N in
          match nth_error ts n with
          | None => failwith "overflow"
          | Some t' =>
            calculate_gep_offset t' (off + Z.of_N offset) vs'
          end
        | _ => failwith ("non-i32-indexable type")
        end
      | @DVALUE_I 64 i =>
        let k := signed i in
        let n := BinIntDef.Z.to_nat k in
        match t with
        | DTYPE_Array _ ta
        | DTYPE_Vector _ ta =>
            calculate_gep_offset ta (off + k * (Z.of_N (sizeof_dtyp ta))) vs'
        | _ => failwith ("non-i64-indexable type")
        end
      | DVALUE_IPTR i =>
        let k := IP.to_Z i in
        let n := BinIntDef.Z.to_nat k in
        match t with
        | DTYPE_Array _ ta
        | DTYPE_Vector _ ta =>
            calculate_gep_offset ta (off + k * (Z.of_N (sizeof_dtyp ta))) vs'
        | _ => failwith ("non-iptr-indexable type")
        end
      | _ => failwith "calculate_gep_offset: unsupported index type"
      end
    | [] => ret off
    end.

  (* Calculate GEP offsets directly with pointer type. May not need this *)
  Fixpoint handle_gep_ptr_h (t:dtyp) (ptr:addr) (vs:list dvalue): err addr :=
    match vs with
    | v :: vs' =>
      match v with
      | @DVALUE_I 8 i =>
        let k := signed i in
        let n := BinIntDef.Z.to_nat k in
        match t with
        | DTYPE_Array _ ta
        | DTYPE_Vector _ ta =>
            ptr' <- ptr_add ptr (k * (Z.of_N (sizeof_dtyp ta)));;
            handle_gep_ptr_h ta ptr' vs'
        | _ => failwith ("non-i8-indexable type")
        end
      | @DVALUE_I 32 i =>
        let k := unsigned i in
        let ks := signed i in
        let n := BinIntDef.Z.to_nat k in
        match t with
        | DTYPE_Array _ ta
        | DTYPE_Vector _ ta =>
            ptr' <- ptr_add ptr (ks * (Z.of_N (sizeof_dtyp ta)));;
            handle_gep_ptr_h ta ptr' vs'
        | DTYPE_Struct ts =>
            let offset := fold_left (fun acc t => pad_to_align (dtyp_alignment t) acc + sizeof_dtyp t)%N
                            (firstn n ts) 0%N in
            match nth_error ts n with
            | None => failwith "overflow"
            | Some t' =>
                ptr' <- ptr_add ptr (Z.of_N offset);;
                handle_gep_ptr_h t' ptr' vs'
            end
        | DTYPE_Packed_struct ts =>
          let offset := fold_left (fun acc t => acc + sizeof_dtyp t)%N
                                  (firstn n ts) 0%N in
          match nth_error ts n with
          | None => failwith "overflow"
          | Some t' =>
              ptr' <- ptr_add ptr (Z.of_N offset);;
              handle_gep_ptr_h t' ptr' vs'
          end
        | _ => failwith ("non-i32-indexable type")
        end
      | @DVALUE_I 64 i =>
        let k := signed i in
        let n := BinIntDef.Z.to_nat k in
        match t with
        | DTYPE_Array _ ta
        | DTYPE_Vector _ ta =>
            ptr' <- ptr_add ptr (k * (Z.of_N (sizeof_dtyp ta)));;
            handle_gep_ptr_h ta ptr' vs'
        | _ => failwith ("non-i64-indexable type")
        end
      | DVALUE_IPTR i =>
        let k := IP.to_Z i in
        let n := BinIntDef.Z.to_nat k in
        match t with
        | DTYPE_Array _ ta
        | DTYPE_Vector _ ta =>
            ptr' <- ptr_add ptr (k * (Z.of_N (sizeof_dtyp ta)));;
            handle_gep_ptr_h ta ptr' vs'
        | _ => failwith ("non-iptr-indexable type")
        end
      | _ => failwith "handle_gep_ptr_h: unsupported index type"
      end
    | [] => ret ptr
    end.

  (* TODO: Should probably move / abstract this *)
  Definition ptr_add_oom (a : addr) (off : Z) : OOM addr :=
    match ptr_add a off with
    | inl msg => Oom msg
    | inr ptr => NoOom ptr
    end.                  

  (* At the toplevel, GEP takes a [dvalue] as an argument that must contain a pointer, but no other pointer can be recursively followed.
     The pointer set the block into which we look, and the initial offset. The first index value add to the initial offset passed to [handle_gep_h] for the actual access to structured data.
   *)
  (* TODO: This should take into account padding too... May break get_consecutive_ptrs and friends. *)
  Definition handle_gep_addr (t:dtyp) (a:addr) (vs:list dvalue) : err (OOM addr) :=
    match vs with
    | @DVALUE_I 8 i :: vs' =>
        off <- calculate_gep_offset t (Z.of_N (sizeof_dtyp t) * (signed i)) vs';;
        ret (ptr_add_oom a off)
    | @DVALUE_I 32 i :: vs' =>
        off <- calculate_gep_offset t (Z.of_N (sizeof_dtyp t) * (signed i)) vs';;
        ret (ptr_add_oom a off)
    | @DVALUE_I 64 i :: vs' =>
        off <- calculate_gep_offset t (Z.of_N (sizeof_dtyp t) * (signed i)) vs';;
        ret (ptr_add_oom a off)
    | DVALUE_IPTR i :: vs' =>
        off <- calculate_gep_offset t (Z.of_N (sizeof_dtyp t) * (IP.to_Z i)) vs';;
        ret (ptr_add_oom a off)
    | [] => failwith "handle_gep_addr: no indices"
    | _ => failwith "handle_gep_addr: unsupported index type"
    end.

  Lemma handle_gep_addr_0 :
    forall (dt : dtyp) (p : addr),
      handle_gep_addr dt p [DVALUE_IPTR IP.zero] = inr (ret p).
  Proof.
    intros dt p.
    cbn.
    rewrite IP.to_Z_0.
    unfold ptr_add_oom.
    replace (Z.of_N (sizeof_dtyp dt) * 0)%Z with 0%Z by lia.
    rewrite ptr_add_0; auto.
  Qed.

  Lemma handle_gep_addr_nil :
    forall (dt : dtyp) (p : addr),
      handle_gep_addr dt p [] = inl "handle_gep_addr: no indices"%string.
  Proof.
    intros dt p.
    cbn; auto.
  Qed.

  Lemma handle_gep_addr_ptr_add_ix :
    forall (dt : dtyp) (p p' : addr) ix,
      handle_gep_addr dt p [DVALUE_IPTR ix] = inr (ret p') ->
      ptr_add p (Z.of_N (sizeof_dtyp dt) * IP.to_Z ix) = inr p'.
  Proof.
    intros dt p p' ix GEP.
    cbn in *.
    inv GEP.
    unfold ptr_add_oom in H0.
    break_match_hyp_inv; auto.
  Qed.

  Lemma handle_gep_addr_ix :
    forall (dt : dtyp) (p p' : addr) ix,
      handle_gep_addr dt p [DVALUE_IPTR ix] = inr (ret p') ->
      ptr_to_int p' = (ptr_to_int p + Z.of_N (sizeof_dtyp dt) * IP.to_Z ix)%Z.
  Proof.
    intros dt p p' ix GEP.
    apply handle_gep_addr_ptr_add_ix in GEP.
    erewrite <- ptr_to_int_ptr_add; eauto.
  Qed.

  Lemma handle_gep_addr_ptr_add_ix_OOM :
    forall (dt : dtyp) (p p' : addr) ix msg,
      handle_gep_addr dt p [DVALUE_IPTR ix] = inr (Oom msg) ->
      ptr_add p (Z.of_N (sizeof_dtyp dt) * IP.to_Z ix) = inl msg.
  Proof.
    intros dt p p' ix msg GEP.
    cbn in *.
    unfold ptr_add_oom in GEP.
    break_match_hyp_inv; auto.
  Qed.

  Lemma handle_gep_addr_ptr_add_ix' :
    forall (dt : dtyp) (p p' : addr) ix,
      ptr_add p (Z.of_N (sizeof_dtyp dt) * IP.to_Z ix) = ret p' ->
      handle_gep_addr dt p [DVALUE_IPTR ix] = inr (ret p').
  Proof.
    intros dt p p' ix IX.
    cbn in *.
    unfold ptr_add_oom.
    rewrite IX.
    reflexivity.
  Qed.

  Lemma handle_gep_addr_ptr_add_ix'_OOM :
    forall (dt : dtyp) (p p' : addr) ix msg,
      ptr_add p (Z.of_N (sizeof_dtyp dt) * IP.to_Z ix) = inl msg ->
      handle_gep_addr dt p [DVALUE_IPTR ix] = inr (Oom msg).
  Proof.
    intros dt p p' ix msg IX.
    cbn in *.
    unfold ptr_add_oom.
    rewrite IX.
    reflexivity.
  Qed.

  (* Lemma handle_gep_addr_ix' : *)
  (*   forall (dt : dtyp) (p p' : addr) ix, *)
  (*     ret p' = int_to_ptr (ptr_to_int p + Z.of_N (sizeof_dtyp dt) * IP.to_Z ix)%Z (extract_metadata p) -> *)
  (*     handle_gep_addr dt p [DVALUE_IPTR ix] = inr (ret p'). *)
  (* Proof. *)
  (*   intros dt p p' ix IX. *)
  (*   apply handle_gep_addr_ptr_add_ix'. *)
  (*   erewrite ptr_to_int_ptr_add in IX; eauto. *)
    
  (*   cbn in *. *)
  (*   inv IX. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Lemma handle_gep_addr_ix'_OOM : *)
  (*   forall (dt : dtyp) (p p' : addr) ix msg, *)
  (*     int_to_ptr (ptr_to_int p + Z.of_N (sizeof_dtyp dt) * IP.to_Z ix)%Z (address_provenance p) = Oom msg -> *)
  (*     exists msg', handle_gep_addr dt p [DVALUE_IPTR ix] = inr (Oom msg'). *)
  (* Proof. *)
  (*   intros dt p p' ix msg IX. *)
  (*   cbn in *. *)
  (*   exists msg. *)
  (*   inv IX. *)
  (*   auto. *)
  (* Qed. *)

  (* Lemma handle_gep_addr_cons_inv : *)
  (*   forall t base_addr idx idxs final_addr, *)
  (*     handle_gep_addr t base_addr (idx :: idxs) = inr (ret final_addr) -> *)
  (*     exists res_addr, *)
  (*       handle_gep_addr t base_addr [idx] = inr (ret res_addr) /\ *)
  (*         handle_gep_addr t res_addr idxs = inr (ret res_addr). *)
  (* Proof. *)
  (*   intros t base_addr idx idxs final_addr H. *)
  (*   cbn in H. *)
  (*   break_match_hyp_inv. *)
  (*   - break_match_hyp_inv. *)
  (*     exists final_addr. *)


  (*     remember (int_to_ptr (ptr_to_int base_addr + Z.of_N (sizeof_dtyp t) * DynamicValues.Int8.unsigned x) (address_provenance base_addr)). *)
  (*     pose proof int_to_ptr_ptr_to_int_exists. *)
  (*     exists (int_to_ptr (ptr_to_int base_addr + Z.of_N (sizeof_dtyp t) * DynamicValues.Int8.unsigned x) (address_provenance base_addr)). *)

  (* Qed. *)

  (* Lemma handle_gep_h_cons : *)
  (*   forall idxs idx t base_addr res_addr final_addr, *)
  (*     handle_gep_h t base_addr [idx] = inr res_addr -> *)
  (*     handle_gep_h t res_addr idxs = inr final_addr -> *)
  (*     handle_gep_h t base_addr (idx :: idxs) = inr final_addr. *)
  (* Proof. *)
  (*   intros idxs. *)
  (*   induction idxs; intros idx t base_addr res_addr final_addr GEP_START GEP_REST. *)
  (*   - cbn in GEP_REST. inv GEP_REST; auto. *)
  (*   - specialize  *)
  (*     cbn in GEP_REST. *)
  (*     break_match_hyp_inv. *)
  (*     + break_match_hyp_inv. *)
  (*       specialize x (res_addr + DynamicValues.Int8.unsigned x * Z.of_N (sizeof_dtyp d)) *)
  (*       * cbn in H1. *)

  (*     specialize (IHidxs a t res_addr). *)
      
      
  (*   cbn; cbn in GEP_START. *)
  (*   break_match_hyp_inv. *)
  (*   - break_match_hyp_inv. *)
  (*     + generalize dependent final_addr. *)
  (*       generalize dependent base_addr. *)
  (*       induction idxs; intros base_addr final_addr GEP_REST. *)
  (*       * cbn in *; auto. *)
  (*       * cbn in *. *)
  (*         break_match_hyp_inv. *)
  (*         --  *)
  (* Qed. *)

  (* Lemma handle_gep_addr_cons : *)
  (*   forall idx idxs t base_addr res_addr final_addr, *)
  (*     handle_gep_addr t base_addr [idx] = inr (ret res_addr) -> *)
  (*     handle_gep_addr t res_addr idxs = inr (ret final_addr) -> *)
  (*     handle_gep_addr t base_addr (idx :: idxs) = inr (ret final_addr). *)
  (* Proof. *)
  (*   intros idx. *)
  (*   induction idxs; intros t base_addr res_addr final_addr GEP_START GEP_REST. *)
  (*   - cbn in GEP_REST. inv GEP_REST. *)
  (*   - cbn in GEP_START. *)
  (*     cbn. *)
  (*     break_match_hyp_inv. *)
  (*     + cbn in GEP_REST. *)
  (*       break_match_hyp_inv. *)
  (*       * break_match_hyp_inv. *)
  (*         break_match_goal. *)
  (*         admit. *)

  (*         break_match_hyp_inv. *)
          
      

  (*   intros t base_addr idx idxs res_addr final_addr GEP_START GEP_REST. *)
  (*   cbn. *)
  (*   cbn in GEP_START. *)
  (*   break_match_hyp_inv. *)
  (*   - unfold handle_gep_addr in GEP_REST. *)
  (*     induction idxs; inv GEP_REST. *)
  (*     forward IHidxs. *)
      
      
  (*     generalize dependent res_addr. *)
  (*     induction idxs; intros res_addr GEP_REST H0. *)
  (*     + inv GEP_REST. *)
  (*     + cbn. *)
  (*       setoid_rewrite GEP_REST. *)
  (*     break_match_goal. *)
  (*     + unfold handle_gep_addr in GEP_REST. *)
  (*       break_match_hyp_inv. *)
  (*       break_match_hyp_inv. *)
  (*       cbn in *. *)
  (*       break_match_hyp_inv. *)
  (*       break_match_hyp_inv. *)

                             
        
  (*   reflexivity. *)
  (* Qed. *)

  Definition handle_gep (t:dtyp) (dv:dvalue) (vs:list dvalue) : err (OOM dvalue) :=
    match dv with
    | DVALUE_Addr a => fmap (F:=err) (fmap DVALUE_Addr) (handle_gep_addr t a vs)
    | _ => inl "non-address"%string
    end.
End GEPM.

(* Module Type GEPM_EXTRA (MD : Typ) (PS : PROV_SET) (Addr : ADDRESS MD PS) (IP : INTPTR) (SIZEOF : Sizeof) (LLVM_Events : LLVM_INTERACTIONS Addr IP SIZEOF) <: GEPM. *)
(*   Include (GEPM Addr IP SIZEOF LLVM_Events). *)
(*   Import Addr. *)

(*   Lemma handle_gep_addr_preserves_metadata : *)
(*     forall (dt : dtyp) ixs (p p' : addr), *)
(*       handle_gep_addr dt p ixs = inr (ret p') -> *)
(*       extract_metadata p = extract_metadata p'. *)
(*   Proof. *)
(*     intros dt ixs. *)
(*     induction ixs; *)
(*       intros p p' GEP; *)
(*       [inversion GEP|]. *)

(*     cbn in GEP. *)
(*     repeat break_match_hyp_inv; *)
(*       cbn in *; *)
(*       symmetry. *)
(*       eapply int_to_ptr_provenance; eauto. *)
(*   Qed. *)

(*   Lemma handle_gep_addr_preserves_provenance : *)
(*     forall (dt : dtyp) ixs (p p' : addr), *)
(*       handle_gep_addr dt p ixs = inr (ret p') -> *)
(*       address_provenance p = address_provenance p'. *)
(*   Proof. *)
(*     intros dt ixs. *)
(*     induction ixs; *)
(*       intros p p' GEP; *)
(*       [inversion GEP|]. *)

(*     cbn in GEP. *)
(*     repeat break_match_hyp_inv; *)
(*       cbn in *; *)
(*       symmetry; *)
(*       eapply int_to_ptr_provenance; eauto. *)
(*   Qed. *)
(* End GEPM_EXTRA. *)

Module Make (ADDR : BASIC_ADDRESS) (IP : INTPTR) (SIZE : Sizeof) (Events : LLVM_INTERACTIONS(ADDR)(IP)(SIZE)) <: GEPM ADDR IP SIZE Events.
  Include (GEPM ADDR IP SIZE Events).
End Make.
