From Vellvm.Syntax Require Import
     DataLayout
     DynamicTypes.

From Vellvm.Semantics Require Import
     MemoryAddress
     MemoryParams
     Memory.Overlaps
     LLVMParams
     LLVMEvents
     ItreeRaiseMReturns.

Require Import MemBytes.

From Vellvm.Handlers Require Import
     MemPropT.

From Vellvm.Utils Require Import
     Error
     PropT
     Util
     NMaps
     Tactics
     Raise
     MonadReturnsLaws
     MonadEq1Laws
     MonadExcLaws.

From Vellvm.Numeric Require Import
     Integers.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor.

From ITree Require Import
     ITree
     Basics.Basics
     Events.Exception
     Eq.Eq
     Events.StateFacts
     Events.State.

From Coq Require Import
     ZArith
     Strings.String
     List
     Lia
     Relations
     RelationClasses
     Wellfounded.

Require Import Morphisms.

Import ListNotations.
Import ListUtil.
Import Utils.Monads.

Import Basics.Basics.Monads.
Import MonadNotation.
Open Scope monad_scope.


Module Type MemoryModelSpecPrimitives (LP : LLVMParams) (MP : MemoryParams LP).
  Import LP.Events.
  Import LP.ADDR.
  Import LP.SIZEOF.
  Import LP.PROV.

  Import MemBytes.
  Module MemByte := Byte LP.ADDR LP.IP LP.SIZEOF LP.Events MP.BYTE_IMPL.
  Import MemByte.
  Import LP.SIZEOF.

  (*** Internal state of memory *)
  Parameter MemState : Type.
  Parameter memory_stack : Type.
  Parameter MemState_get_memory : MemState -> memory_stack.
  Parameter MemState_get_provenance : MemState -> Provenance.
  Parameter MemState_put_memory : memory_stack -> MemState -> MemState.

  (* Type for frames and frame stacks *)
  Parameter Frame : Type.
  Parameter FrameStack : Type.

  (* Heaps *)
  Parameter Heap : Type.

  (* TODO: Should DataLayout be here?

     It might make sense to move DataLayout to another module, some of
     the parameters in the DataLayout may be relevant to other
     modules, and we could enforce that everything agrees.

     For instance alignment may impact Sizeof, and there's also some
     stuff about pointer sizes in the DataLayout structure.
   *)
  (* Parameter datalayout : DataLayout. *)

  (*** Primitives on memory *)

  (** Reads *)
  Parameter read_byte_MemPropT : addr -> MemPropT memory_stack SByte.

  (** Allocations *)
  (* Returns true if a byte is allocated with a given AllocationId? *)
  Parameter addr_allocated_prop : addr -> AllocationId -> MemPropT memory_stack bool.

  (** Frame stacks *)
  (* Check if an address is allocated in a frame *)
  Parameter ptr_in_frame_prop : Frame -> addr -> Prop.

  (* Check for the current frame *)
  Parameter peek_frame_stack_prop : FrameStack -> Frame -> Prop.
  Parameter pop_frame_stack_prop : FrameStack -> FrameStack -> Prop.

  Parameter memory_stack_frame_stack_prop : memory_stack -> FrameStack -> Prop.

  Definition frame_eqv (f f' : Frame) : Prop :=
    forall ptr, ptr_in_frame_prop f ptr <-> ptr_in_frame_prop f' ptr.

  #[global] Instance frame_eqv_Equivalence : Equivalence frame_eqv.
  Proof.
    split.
    - intros f ptr.
      reflexivity.
    - intros f1 f2 EQV.
      unfold frame_eqv in *.
      firstorder.
    - intros x y z XY YZ.
      firstorder.
  Qed.

  Parameter frame_stack_eqv : FrameStack -> FrameStack -> Prop.
  #[global] Parameter frame_stack_eqv_Equivalence : Equivalence frame_stack_eqv.

  (** Heaps *)

  Parameter root_in_heap_prop : Heap -> addr -> Prop.

  (* 1) heap
     2) root pointer
     3) pointer

     The root pointer is the reference to a block that will be freed.
   *)
  Parameter ptr_in_heap_prop : Heap -> addr -> addr -> Prop.

  (* Memory stack's heap *)
  Parameter memory_stack_heap_prop : memory_stack -> Heap -> Prop.

  Record heap_eqv (h h' : Heap) : Prop :=
    {
      heap_roots_eqv : forall root, root_in_heap_prop h root <-> root_in_heap_prop h' root;
      heap_ptrs_eqv : forall root ptr, ptr_in_heap_prop h root ptr <-> ptr_in_heap_prop h' root ptr;
    }.

  #[global] Instance root_in_heap_prop_Proper :
    Proper (heap_eqv ==> eq ==> iff) root_in_heap_prop.
  Proof.
    intros h h' HEAPEQ ptr ptr' PTREQ; subst.
    inv HEAPEQ.
    eauto.
  Qed.

  #[global] Instance ptr_in_heap_prop_Proper :
    Proper (heap_eqv ==> eq ==> eq ==> iff) ptr_in_heap_prop.
  Proof.
    intros h h' HEAPEQ root root' ROOTEQ ptr ptr' PTREQ; subst.
    inv HEAPEQ.
    eauto.
  Qed.

  #[global] Instance heap_Equivalence : Equivalence heap_eqv.
  Proof.
    split.
    - intros h; split.
      + intros root.
        reflexivity.
      + intros root ptr.
        reflexivity.
    - intros h1 h2 EQV.
      firstorder.
    - intros x y z XY YZ.
      split.
      + intros root.
        rewrite XY, YZ.
        reflexivity.
      + intros root ptr.
        rewrite XY, YZ.
        reflexivity.
  Qed.

  (** Provenances *)
  Parameter used_provenance_prop : MemState -> Provenance -> Prop. (* Has a provenance *ever* been used. *)

  (* Allocate a new fresh provenance *)
  Parameter mem_state_fresh_provenance : MemState -> (Provenance * MemState)%type.
  Parameter mem_state_fresh_provenance_fresh :
    forall (ms ms' : MemState) (pr : Provenance),
      mem_state_fresh_provenance ms = (pr, ms') ->
      MemState_get_memory ms = MemState_get_memory ms' /\
        (forall pr, used_provenance_prop ms pr -> used_provenance_prop ms' pr) /\
      ~ used_provenance_prop ms pr /\ used_provenance_prop ms' pr.

  (** Lemmas about MemState *)
  Parameter MemState_get_put_memory :
    forall ms mem,
      MemState_get_memory (MemState_put_memory mem ms) = mem.

  #[global] Instance MemState_memory_MemStateMem : MemStateMem MemState memory_stack :=
    {| ms_get_memory := MemState_get_memory;
      ms_put_memory := MemState_put_memory;
      ms_get_put_memory := MemState_get_put_memory;
    |}.

End MemoryModelSpecPrimitives.

Module MemoryHelpers (LP : LLVMParams) (MP : MemoryParams LP) (Byte : ByteModule LP.ADDR LP.IP LP.SIZEOF LP.Events MP.BYTE_IMPL).
  (*** Other helpers *)
  Import MP.GEP.
  Import MP.BYTE_IMPL.
  Import LP.
  Import LP.ADDR.
  Import LP.Events.
  Import LP.SIZEOF.
  Import Byte.

  (* TODO: Move this? *)
  Definition intptr_seq (start : Z) (len : nat) : OOM (list IP.intptr)
    := Util.map_monad (IP.from_Z) (Zseq start len).

  (* TODO: Move this? *)
  Lemma intptr_seq_succ :
    forall off n,
      intptr_seq off (S n) =
        hd <- IP.from_Z off;;
        tail <- intptr_seq (Z.succ off) n;;
        ret (hd :: tail).
  Proof.
    intros off n.
    cbn.
    reflexivity.
  Qed.

  Lemma intptr_seq_nth :
    forall start len seq ix ixip,
      intptr_seq start len = NoOom seq ->
      Util.Nth seq ix ixip ->
      IP.from_Z (start + (Z.of_nat ix)) = NoOom ixip.
  Proof.
    intros start len seq. revert start len.
    induction seq; intros start len ix ixip SEQ NTH.
    - cbn in NTH.
      destruct ix; inv NTH.
    - cbn in *.
      destruct ix.
      + cbn in *; inv NTH.
        destruct len; cbn in SEQ; inv SEQ.
        break_match_hyp; inv H0.
        replace (start + 0)%Z with start by lia.
        break_match_hyp; cbn in *; inv H1; auto.
      + cbn in *; inv NTH.
        destruct len as [ | len']; cbn in SEQ; inv SEQ.
        break_match_hyp; inv H1.
        break_match_hyp; cbn in *; inv H2; auto.

        replace (start + Z.pos (Pos.of_succ_nat ix))%Z with
          (Z.succ start + Z.of_nat ix)%Z by lia.

        eapply IHseq with (start := Z.succ start) (len := len'); eauto.
  Qed.

  Lemma intptr_seq_ge :
    forall start len seq x,
      intptr_seq start len = NoOom seq ->
      In x seq ->
      (IP.to_Z x >= start)%Z.
  Proof.
    intros start len seq x SEQ IN.
    apply In_nth_error in IN.
    destruct IN as [n IN].

    pose proof (intptr_seq_nth start len seq n x SEQ IN) as IX.
    erewrite IP.from_Z_to_Z; eauto.
    lia.
  Qed.

  Lemma in_intptr_seq :
    forall len start n seq,
      intptr_seq start len = NoOom seq ->
      In n seq <-> (start <= IP.to_Z n < start + Z.of_nat len)%Z.
  Proof.
  intros len start.
  revert start. induction len as [|len IHlen]; simpl; intros start n seq SEQ.
  - cbn in SEQ; inv SEQ.
    split.
    + intros IN; inv IN.
    + lia.
  - cbn in SEQ.
    break_match_hyp; [|inv SEQ].
    break_match_hyp; inv SEQ.
    split.
    + intros [IN | IN].
      * subst.
        apply IP.from_Z_to_Z in Heqo; subst.
        lia.
      * pose proof (IHlen (Z.succ start) n l Heqo0) as [A B].
        specialize (A IN).
        cbn.
        lia.
    + intros BOUND.
      cbn.
      destruct (IP.eq_dec i n) as [EQ | NEQ]; auto.
      right.

      pose proof (IHlen (Z.succ start) n l Heqo0) as [A B].
      apply IP.from_Z_to_Z in Heqo; subst.
      assert (IP.to_Z i <> IP.to_Z n).
      { intros EQ.
        apply IP.to_Z_inj in EQ; auto.
      }

      assert ((Z.succ (IP.to_Z i) <= IP.to_Z n < Z.succ (IP.to_Z i) + Z.of_nat len)%Z) as BOUND' by lia.
      specialize (B BOUND').
      auto.
  Qed.

  Lemma intptr_seq_from_Z :
    forall start len seq,
      intptr_seq start len = NoOom seq ->
      (forall x,
          (start <= x < start + Z.of_nat len)%Z ->
          exists ipx, IP.from_Z x = NoOom ipx /\ In ipx seq).
  Proof.
    intros start len; revert start;
      induction len;
      intros start seq SEQ x BOUND.

    - lia.
    - rewrite intptr_seq_succ in SEQ.
      cbn in SEQ.
      break_match_hyp.
      + destruct (Z.eq_dec x start); subst.
        * exists i.
          split; auto.
          break_match_hyp; inv SEQ; cbn; auto.
        * break_match_hyp; inv SEQ.
          eapply IHlen with (x := x) in Heqo0 as (ipx & FROMZ & IN).
          exists ipx; split; cbn; auto.
          lia.
      + inv SEQ.
  Qed.

  Lemma intptr_seq_len :
    forall len start seq,
      intptr_seq start len = NoOom seq ->
      length seq = len.
  Proof.
    induction len;
      intros start seq SEQ.
    - inv SEQ. reflexivity.
    - rewrite intptr_seq_succ in SEQ.
      cbn in SEQ.
      break_match_hyp; [break_match_hyp|]; inv SEQ.
      cbn.
      apply IHlen in Heqo0; subst.
      reflexivity.
  Qed.

  Definition get_consecutive_ptrs {M} `{Monad M} `{RAISE_OOM M} `{RAISE_ERROR M} (ptr : addr) (len : nat) : M (list addr) :=
    ixs <- lift_OOM (intptr_seq 0 len);;
    lift_err_RAISE_ERROR
      (Util.map_monad
         (fun ix => handle_gep_addr (DTYPE_I 8) ptr [DVALUE_IPTR ix])
         ixs).

  Import Monad.
  Lemma get_consecutive_ptrs_length : 
    forall {M} `{HM : Monad M} `{EQM : Monad.Eq1 M}
      `{EQV : @Eq1Equivalence M HM EQM}
      `{EQRET : @Eq1_ret_inv M EQM HM}
      `{MLAWS : @MonadLawsE M EQM HM}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{RAISE : @RaiseBindM M HM EQM string (fun T msg => raise_oom msg)}
      (ptr : addr) (len : nat) (ptrs : list addr),
      (get_consecutive_ptrs ptr len ≈ ret ptrs)%monad ->
      len = length ptrs.
  Proof.
    intros M HM EQM EQV EQRET MLAWS OOM ERR RAISE ptr len ptrs CONSEC.
    unfold get_consecutive_ptrs in CONSEC.
    cbn in *.
    destruct (intptr_seq 0 len) eqn:SEQ.
    - (* No OOM *)
      cbn in *.
      rewrite bind_ret_l in CONSEC.
      destruct (map_monad (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) ptr [DVALUE_IPTR ix]) l) eqn:HMAPM.
      + (* Error: should be a contradiction *)
        (* TODO: need inversion lemma. *)
        cbn in CONSEC.
        admit.
      + cbn in CONSEC.
        apply eq1_ret_ret in CONSEC; auto.
        assert (MReturns l0 (map_monad (fun ix : IP.intptr => handle_gep_addr (DTYPE_I 8) ptr [DVALUE_IPTR ix]) l)) as RETS.
        { auto. }

        epose proof MapMonadExtra.map_monad_length l _ _ RETS as LEN.
        apply intptr_seq_len in SEQ.
        subst.
        auto.
    - (* OOM: CONSEC equivalent to ret is a contradiction. *)
      (* TODO: need inversion lemma *)
      admit.
  Admitted.

  Definition generate_num_undef_bytes (num : N) (dt : dtyp) (sid : store_id) : OOM (list SByte) :=
    N.recursion
      (fun (x : N) => ret [])
      (fun n mf x =>
         rest_bytes <- mf (N.succ x);;
         x' <- IP.from_Z (Z.of_N x);;
         let byte := uvalue_sbyte (UVALUE_Undef dt) dt (UVALUE_IPTR x') sid in
         ret (byte :: rest_bytes))
      num 0%N.

  Definition generate_undef_bytes (dt : dtyp) (sid : store_id) : OOM (list SByte) :=
    generate_num_undef_bytes (sizeof_dtyp dt) dt sid.

  Section Serialization.
    (** ** Serialization *)
  (*      Conversion back and forth between values and their byte representation *)
  (*    *)
    (* Given a little endian list of bytes, match the endianess of `e` *)
    Definition correct_endianess {BYTES : Type} (e : Endianess) (bytes : list BYTES)
      := match e with
         | ENDIAN_BIG => rev bytes
         | ENDIAN_LITTLE => bytes
         end.

    (* Converts an integer [x] to its byte representation over [n] bytes. *)
  (*    The representation is little endian. In particular, if [n] is too small, *)
  (*    only the least significant bytes are returned. *)
  (*    *)
    Fixpoint bytes_of_int_little_endian (n: nat) (x: Z) {struct n}: list byte :=
      match n with
      | O => nil
      | S m => Byte.repr x :: bytes_of_int_little_endian m (x / 256)
      end.

    Definition bytes_of_int (e : Endianess) (n : nat) (x : Z) : list byte :=
      correct_endianess e (bytes_of_int_little_endian n x).

    (* *)
  (* Definition sbytes_of_int (e : Endianess) (count:nat) (z:Z) : list SByte := *)
  (*   List.map Byte (bytes_of_int e count z). *)

    Definition uvalue_bytes_little_endian (uv :  uvalue) (dt : dtyp) (sid : store_id) : OOM (list uvalue)
      := map_monad (fun n => n' <- IP.from_Z (Z.of_N n);;
                          ret (UVALUE_ExtractByte uv dt (UVALUE_IPTR n') sid)) (Nseq 0 (N.to_nat (sizeof_dtyp DTYPE_Pointer))).

    Definition uvalue_bytes (e : Endianess) (uv :  uvalue) (dt : dtyp) (sid : store_id) : OOM (list uvalue)
      := fmap (correct_endianess e) (uvalue_bytes_little_endian uv dt sid).

    (* TODO: move this *)
    Definition dtyp_eqb (dt1 dt2 : dtyp) : bool
      := match @dtyp_eq_dec dt1 dt2 with
         | left x => true
         | right x => false
         end.

    (* TODO: revive this *)
    (* Definition fp_alignment (bits : N) : option Alignment := *)
    (*   let fp_map := dl_floating_point_alignments datalayout *)
    (*   in NM.find bits fp_map. *)

    (*  TODO: revive this *)
    (* Definition int_alignment (bits : N) : option Alignment := *)
    (*   let int_map := dl_integer_alignments datalayout *)
    (*   in match NM.find bits int_map with *)
    (*      | Some align => Some align *)
    (*      | None => *)
    (*        let keys  := map fst (NM.elements int_map) in *)
    (*        let bits' := nextOrMaximumOpt N.leb bits keys  *)
    (*        in match bits' with *)
    (*           | Some bits => NM.find bits int_map *)
    (*           | None => None *)
    (*           end *)
    (*      end. *)

    (* TODO: Finish this function *)
    (* Fixpoint dtyp_alignment (dt : dtyp) : option Alignment := *)
    (*   match dt with *)
    (*   | DTYPE_I sz => *)
    (*     int_alignment sz *)
    (*   | DTYPE_IPTR => *)
    (*     (* TODO: should these have the same alignments as pointers? *) *)
    (*     int_alignment (N.of_nat ptr_size * 4)%N *)
    (*   | DTYPE_Pointer => *)
    (*     (* TODO: address spaces? *) *)
    (*     Some (ps_alignment (head (dl_pointer_alignments datalayout))) *)
    (*   | DTYPE_Void => *)
    (*     None *)
    (*   | DTYPE_Half => *)
    (*     fp_alignment 16 *)
    (*   | DTYPE_Float => *)
    (*     fp_alignment 32 *)
    (*   | DTYPE_Double => *)
    (*     fp_alignment 64 *)
    (*   | DTYPE_X86_fp80 => *)
    (*     fp_alignment 80 *)
    (*   | DTYPE_Fp128 => *)
    (*     fp_alignment 128 *)
    (*   | DTYPE_Ppc_fp128 => *)
    (*     fp_alignment 128 *)
    (*   | DTYPE_Metadata => *)
    (*     None *)
    (*   | DTYPE_X86_mmx => _ *)
    (*   | DTYPE_Array sz t => *)
    (*     dtyp_alignment t *)
    (*   | DTYPE_Struct fields => _ *)
    (*   | DTYPE_Packed_struct fields => _ *)
    (*   | DTYPE_Opaque => _ *)
    (*   | DTYPE_Vector sz t => _ *)
    (*   end. *)

    Definition dtyp_extract_fields (dt : dtyp) : err (list dtyp)
      := match dt with
         | DTYPE_Struct fields
         | DTYPE_Packed_struct fields =>
             ret fields
         | DTYPE_Array sz t
         | DTYPE_Vector sz t =>
             ret (repeat t (N.to_nat sz))
         | _ => inl "No fields."%string
         end.

    Definition extract_byte_to_sbyte (uv : uvalue) : ERR SByte
      := match uv with
         | UVALUE_ExtractByte uv dt idx sid =>
             ret (uvalue_sbyte uv dt idx sid)
         | _ => inl (ERR_message "extract_byte_to_ubyte invalid conversion.")
         end.

    Definition sbyte_sid_match (a b : SByte) : bool
      := match sbyte_to_extractbyte a, sbyte_to_extractbyte b with
         | UVALUE_ExtractByte uv dt idx sid, UVALUE_ExtractByte uv' dt' idx' sid' =>
             N.eqb sid sid'
         | _, _ => false
         end.

    Definition replace_sid (sid : store_id) (ub : SByte) : SByte
      := match sbyte_to_extractbyte ub with
         | UVALUE_ExtractByte uv dt idx sid_old =>
             uvalue_sbyte uv dt idx sid
         | _ =>
             ub (* Should not happen... *)
         end.

    Definition filter_sid_matches (byte : SByte) (sbytes : list (N * SByte)) : (list (N * SByte) * list (N * SByte))
      := filter_split (fun '(n, uv) => sbyte_sid_match byte uv) sbytes.

    (* TODO: should I move this? *)
    (* Assign fresh sids to ubytes while preserving entanglement *)
    Program Fixpoint re_sid_ubytes_helper {M} `{Monad M} `{MonadStoreId M} `{RAISE_ERROR M}
            (bytes : list (N * SByte)) (acc : NMap SByte) {measure (length bytes)} : M (NMap SByte)
      := match bytes with
         | [] => ret acc
         | ((n, x)::xs) =>
             match sbyte_to_extractbyte x with
             | UVALUE_ExtractByte uv dt idx sid =>
                 let '(ins, outs) := filter_sid_matches x xs in
                 nsid <- fresh_sid;;
                 let acc := @NM.add _ n (replace_sid nsid x) acc in
                 (* Assign new sid to entangled bytes *)
                 let acc := fold_left (fun acc '(n, ub) => @NM.add _ n (replace_sid nsid ub) acc) ins acc in
                 re_sid_ubytes_helper outs acc
             | _ => raise_error "re_sid_ubytes_helper: sbyte_to_extractbyte did not yield UVALUE_ExtractByte"
             end
         end.
    Next Obligation.
      cbn.
      symmetry in Heq_anonymous.
      apply filter_split_out_length in Heq_anonymous.
      lia.
    Defined.

    Lemma re_sid_ubytes_helper_equation {M} `{Monad M} `{MonadStoreId M} `{RAISE_ERROR M}
          (bytes : list (N * SByte)) (acc : NMap SByte) :
      re_sid_ubytes_helper bytes acc =
        match bytes with
        | [] => ret acc
        | ((n, x)::xs) =>
            match sbyte_to_extractbyte x with
            | UVALUE_ExtractByte uv dt idx sid =>
                let '(ins, outs) := filter_sid_matches x xs in
                nsid <- fresh_sid;;
                let acc := @NM.add _ n (replace_sid nsid x) acc in
                (* Assign new sid to entangled bytes *)
                let acc := fold_left (fun acc '(n, ub) => @NM.add _ n (replace_sid nsid ub) acc) ins acc in
                re_sid_ubytes_helper outs acc
            | _ => raise_error "re_sid_ubytes_helper: sbyte_to_extractbyte did not yield UVALUE_ExtractByte"
            end
        end.
    Proof.
      unfold re_sid_ubytes_helper.
      unfold re_sid_ubytes_helper_func at 1.
      rewrite Wf.WfExtensionality.fix_sub_eq_ext.
      destruct bytes.
      reflexivity.
      cbn.
      break_match; break_match; try reflexivity.
      break_match.
      break_match; subst.
      - assert
          (forall nsid acc,
              (fold_left
                 (fun (acc0 : NM.t SByte) (pat : NM.key * SByte) =>
                    (let '(n0, ub) as anonymous' := pat return (anonymous' = pat -> NM.t SByte) in fun _ : (n0, ub) = pat => NM.add n0 (replace_sid nsid ub) acc0)
                      eq_refl) l acc) =
                (fold_left (fun (acc0 : NM.t SByte) '(n0, ub) => NM.add n0 (replace_sid nsid ub) acc0) l acc)) as FOLD.
        { clear Heqp1 acc.
          induction l; intros nsid acc.
          - reflexivity.
          - cbn.
            rewrite <- IHl.
            destruct a.
            reflexivity.
        }

        apply f_equal.
        Require Import FunctionalExtensionality.
        apply functional_extensionality.
        intros nsid.
        rewrite FOLD.
        reflexivity.
      - apply f_equal.
        apply functional_extensionality.
        intros nsid.
        break_match.
        break_match.
        all: try reflexivity.
        cbn.
    Admitted.

    Definition re_sid_ubytes {M} `{Monad M} `{MonadStoreId M} `{RAISE_ERROR M}
               (bytes : list SByte) : M (list SByte)
      := let len := length bytes in
         byte_map <- re_sid_ubytes_helper (zip (Nseq 0 len) bytes) (@NM.empty _);;
         trywith_error "re_sid_ubytes: missing indices." (NM_find_many (Nseq 0 len) byte_map).

    Definition sigT_of_prod {A B : Type} (p : A * B) : {_ : A & B} :=
      let (a, b) := p in existT (fun _ : A => B) a b.

    Definition uvalue_measure_rel (uv1 uv2 : uvalue) : Prop :=
      (uvalue_measure uv1 < uvalue_measure uv2)%nat.

    Lemma wf_uvalue_measure_rel :
      @well_founded uvalue uvalue_measure_rel.
    Proof.
      unfold uvalue_measure_rel.
      apply wf_inverse_image.
      apply Wf_nat.lt_wf.
    Defined.

    Definition lt_uvalue_dtyp (uvdt1 uvdt2 : (uvalue * dtyp)) : Prop :=
      lexprod uvalue (fun uv => dtyp) uvalue_measure_rel (fun uv dt1f dt2f => dtyp_measure dt1f < dtyp_measure dt2f)%nat (sigT_of_prod uvdt1) (sigT_of_prod uvdt2).

    Lemma wf_lt_uvalue_dtyp : well_founded lt_uvalue_dtyp.
    Proof.
      unfold lt_uvalue_dtyp.
      apply wf_inverse_image.
      apply wf_lexprod.
      - unfold well_founded; intros a.
        apply wf_uvalue_measure_rel.
      - intros uv.
        apply wf_inverse_image.
        apply Wf_nat.lt_wf.
    Defined.

    Definition lex_nats (ns1 ns2 : (nat * nat)) : Prop :=
      lexprod nat (fun n => nat) lt (fun _ => lt) (sigT_of_prod ns1) (sigT_of_prod ns2).

    Lemma well_founded_lex_nats :
      well_founded lex_nats.
    Proof.
      unfold lex_nats.
      apply wf_inverse_image.
      apply wf_lexprod; intros;
        apply Wf_nat.lt_wf.
    Qed.

    (* This is mostly to_ubytes, except it will also unwrap concatbytes *)
    Obligation Tactic := try Tactics.program_simpl; try solve [solve_uvalue_dtyp_measure
                                                              | intuition;
                                                               match goal with
                                                               | H: _ |- _ =>
                                                                   try solve [inversion H]
                                                               end
                                                    ].

    Program Fixpoint serialize_sbytes
            {M} `{Monad M} `{MonadStoreId M} `{RAISE_ERROR M} `{RAISE_OOM M}
            (uv : uvalue) (dt : dtyp) {measure (uvalue_measure uv, dtyp_measure dt) lex_nats} : M (list SByte)
      :=
      match uv with
      (* Base types *)
      | UVALUE_Addr _
      | UVALUE_I1 _
      | UVALUE_I8 _
      | UVALUE_I32 _
      | UVALUE_I64 _
      | UVALUE_IPTR _
      | UVALUE_Float _
      | UVALUE_Double _

      (* Expressions *)
      | UVALUE_IBinop _ _ _
      | UVALUE_ICmp _ _ _
      | UVALUE_FBinop _ _ _ _
      | UVALUE_FCmp _ _ _
      | UVALUE_Conversion _ _ _ _
      | UVALUE_GetElementPtr _ _ _
      | UVALUE_ExtractElement _ _ _
      | UVALUE_InsertElement _ _ _ _
      | UVALUE_ShuffleVector _ _ _
      | UVALUE_ExtractValue _ _ _
      | UVALUE_InsertValue _ _ _ _
      | UVALUE_Select _ _ _ =>
          sid <- fresh_sid;;
          lift_OOM (to_ubytes uv dt sid)

      (* Undef values, these can possibly be aggregates *)
      | UVALUE_Undef _ =>
          match dt with
          | DTYPE_Struct [] =>
              ret []
          | DTYPE_Struct (t::ts) =>
              f_bytes <- serialize_sbytes (UVALUE_Undef t) t;; (* How do I know this is smaller? *)
              fields_bytes <- serialize_sbytes (UVALUE_Undef (DTYPE_Struct ts)) (DTYPE_Struct ts);;
              ret (f_bytes ++ fields_bytes)

          | DTYPE_Packed_struct [] =>
              ret []
          | DTYPE_Packed_struct (t::ts) =>
              f_bytes <- serialize_sbytes (UVALUE_Undef t) t;; (* How do I know this is smaller? *)
              fields_bytes <- serialize_sbytes (UVALUE_Undef (DTYPE_Packed_struct ts)) (DTYPE_Packed_struct ts);;
              ret (f_bytes ++ fields_bytes)

          | DTYPE_Array sz t =>
              field_bytes <- map_monad_In (repeatN sz (UVALUE_Undef t)) (fun elt Hin => serialize_sbytes elt t);;
              ret (concat field_bytes)

          | DTYPE_Vector sz t =>
              field_bytes <- map_monad_In (repeatN sz (UVALUE_Undef t)) (fun elt Hin => serialize_sbytes elt t);;
              ret (concat field_bytes)
          | _ =>
              sid <- fresh_sid;;
              lift_OOM (to_ubytes uv dt sid)
          end

      (* Poison values, possibly aggregates *)
      | UVALUE_Poison _ =>
          match dt with
          | DTYPE_Struct [] =>
              ret []
          | DTYPE_Struct (t::ts) =>
              f_bytes <- serialize_sbytes (UVALUE_Poison t) t;; (* How do I know this is smaller? *)
              fields_bytes <- serialize_sbytes (UVALUE_Poison (DTYPE_Struct ts)) (DTYPE_Struct ts);;
              ret (f_bytes ++ fields_bytes)

          | DTYPE_Packed_struct [] =>
              ret []
          | DTYPE_Packed_struct (t::ts) =>
              f_bytes <- serialize_sbytes (UVALUE_Poison t) t;; (* How do I know this is smaller? *)
              fields_bytes <- serialize_sbytes (UVALUE_Poison (DTYPE_Packed_struct ts)) (DTYPE_Packed_struct ts);;
              ret (f_bytes ++ fields_bytes)

          | DTYPE_Array sz t =>
              field_bytes <- map_monad_In (repeatN sz (UVALUE_Poison t)) (fun elt Hin => serialize_sbytes elt t);;
              ret (concat field_bytes)

          | DTYPE_Vector sz t =>
              field_bytes <- map_monad_In (repeatN sz (UVALUE_Poison t)) (fun elt Hin => serialize_sbytes elt t);;
              ret (concat field_bytes)
          | _ =>
              sid <- fresh_sid;;
              lift_OOM (to_ubytes uv dt sid)
          end

      (* TODO: each field gets a separate store id... Is that sensible? *)
      (* Padded aggregate types *)
      | UVALUE_Struct [] =>
          ret []
      | UVALUE_Struct (f::fields) =>
          (* TODO: take padding into account *)
          match dt with
          | DTYPE_Struct (t::ts) =>
              f_bytes <- serialize_sbytes f t;;
              fields_bytes <- serialize_sbytes (UVALUE_Struct fields) (DTYPE_Struct ts);;
              ret (f_bytes ++ fields_bytes)
          | _ =>
              raise_error "serialize_sbytes: UVALUE_Struct field / type mismatch."
          end

      (* Packed aggregate types *)
      | UVALUE_Packed_struct [] =>
          ret []
      | UVALUE_Packed_struct (f::fields) =>
          (* TODO: take padding into account *)
          match dt with
          | DTYPE_Packed_struct (t::ts) =>
              f_bytes <- serialize_sbytes f t;;
              fields_bytes <- serialize_sbytes (UVALUE_Packed_struct fields) (DTYPE_Packed_struct ts);;
              ret (f_bytes ++ fields_bytes)
          | _ =>
              raise_error "serialize_sbytes: UVALUE_Packed_struct field / type mismatch."
          end

      | UVALUE_Array elts =>
          match dt with
          | DTYPE_Array sz t =>
              field_bytes <- map_monad_In elts (fun elt Hin => serialize_sbytes elt t);;
              ret (concat field_bytes)
          | _ =>
              raise_error "serialize_sbytes: UVALUE_Array with incorrect type."
          end
      | UVALUE_Vector elts =>
          match dt with
          | DTYPE_Vector sz t =>
              field_bytes <- map_monad_In elts (fun elt Hin => serialize_sbytes elt t);;
              ret (concat field_bytes)
          | _ =>
              raise_error "serialize_sbytes: UVALUE_Array with incorrect type."
          end

      | UVALUE_None => ret nil

      (* Byte manipulation. *)
      | UVALUE_ExtractByte uv dt' idx sid =>
          raise_error "serialize_sbytes: UVALUE_ExtractByte not guarded by UVALUE_ConcatBytes."

      | UVALUE_ConcatBytes bytes t =>
          (* TODO: should provide *new* sids... May need to make this function in a fresh sid monad *)
          bytes' <- lift_ERR_RAISE_ERROR (map_monad extract_byte_to_sbyte bytes);;
          re_sid_ubytes bytes'
      end.
    Next Obligation.
      unfold Wf.MR.
      unfold lex_nats.
      apply wf_inverse_image.
      apply wf_lexprod; intros;
        apply Wf_nat.lt_wf.
    Qed.

    Lemma serialize_sbytes_equation {M} `{Monad M} `{MonadStoreId M} `{RAISE_ERROR M} `{RAISE_OOM M} : forall (uv : uvalue) (dt : dtyp),
        @serialize_sbytes M _ _ _ _ uv dt =
          match uv with
          (* Base types *)
          | UVALUE_Addr _
          | UVALUE_I1 _
          | UVALUE_I8 _
          | UVALUE_I32 _
          | UVALUE_I64 _
          | UVALUE_IPTR _
          | UVALUE_Float _
          | UVALUE_Double _

          (* Expressions *)
          | UVALUE_IBinop _ _ _
          | UVALUE_ICmp _ _ _
          | UVALUE_FBinop _ _ _ _
          | UVALUE_FCmp _ _ _
          | UVALUE_Conversion _ _ _ _
          | UVALUE_GetElementPtr _ _ _
          | UVALUE_ExtractElement _ _ _
          | UVALUE_InsertElement _ _ _ _
          | UVALUE_ShuffleVector _ _ _
          | UVALUE_ExtractValue _ _ _
          | UVALUE_InsertValue _ _ _ _
          | UVALUE_Select _ _ _ =>
              sid <- fresh_sid;;
              lift_OOM (to_ubytes uv dt sid)

          (* Undef values, these can possibly be aggregates *)
          | UVALUE_Undef _ =>
              match dt with
              | DTYPE_Struct [] =>
                  ret []
              | DTYPE_Struct (t::ts) =>
                  f_bytes <- serialize_sbytes (UVALUE_Undef t) t;; (* How do I know this is smaller? *)
                  fields_bytes <- serialize_sbytes (UVALUE_Undef (DTYPE_Struct ts)) (DTYPE_Struct ts);;
                  ret (f_bytes ++ fields_bytes)

              | DTYPE_Packed_struct [] =>
                  ret []
              | DTYPE_Packed_struct (t::ts) =>
                  f_bytes <- serialize_sbytes (UVALUE_Undef t) t;; (* How do I know this is smaller? *)
                  fields_bytes <- serialize_sbytes (UVALUE_Undef (DTYPE_Packed_struct ts)) (DTYPE_Packed_struct ts);;
                  ret (f_bytes ++ fields_bytes)

              | DTYPE_Array sz t =>
                  field_bytes <- map_monad_In (repeatN sz (UVALUE_Undef t)) (fun elt Hin => serialize_sbytes elt t);;
                  ret (concat field_bytes)

              | DTYPE_Vector sz t =>
                  field_bytes <- map_monad_In (repeatN sz (UVALUE_Undef t)) (fun elt Hin => serialize_sbytes elt t);;
                  ret (concat field_bytes)
              | _ =>
                  sid <- fresh_sid;;
                  lift_OOM (to_ubytes uv dt sid)
              end

          (* Poison values, possibly aggregates *)
          | UVALUE_Poison _ =>
              match dt with
              | DTYPE_Struct [] =>
                  ret []
              | DTYPE_Struct (t::ts) =>
                  f_bytes <- serialize_sbytes (UVALUE_Poison t) t;; (* How do I know this is smaller? *)
                  fields_bytes <- serialize_sbytes (UVALUE_Poison (DTYPE_Struct ts)) (DTYPE_Struct ts);;
                  ret (f_bytes ++ fields_bytes)

              | DTYPE_Packed_struct [] =>
                  ret []
              | DTYPE_Packed_struct (t::ts) =>
                  f_bytes <- serialize_sbytes (UVALUE_Poison t) t;; (* How do I know this is smaller? *)
                  fields_bytes <- serialize_sbytes (UVALUE_Poison (DTYPE_Packed_struct ts)) (DTYPE_Packed_struct ts);;
                  ret (f_bytes ++ fields_bytes)

              | DTYPE_Array sz t =>
                  field_bytes <- map_monad_In (repeatN sz (UVALUE_Poison t)) (fun elt Hin => serialize_sbytes elt t);;
                  ret (concat field_bytes)

              | DTYPE_Vector sz t =>
                  field_bytes <- map_monad_In (repeatN sz (UVALUE_Poison t)) (fun elt Hin => serialize_sbytes elt t);;
                  ret (concat field_bytes)
              | _ =>
                  sid <- fresh_sid;;
                  lift_OOM (to_ubytes uv dt sid)
              end

          (* TODO: each field gets a separate store id... Is that sensible? *)
          (* Padded aggregate types *)
          | UVALUE_Struct [] =>
              ret []
          | UVALUE_Struct (f::fields) =>
              (* TODO: take padding into account *)
              match dt with
              | DTYPE_Struct (t::ts) =>
                  f_bytes <- serialize_sbytes f t;;
                  fields_bytes <- serialize_sbytes (UVALUE_Struct fields) (DTYPE_Struct ts);;
                  ret (f_bytes ++ fields_bytes)
              | _ =>
                  raise_error "serialize_sbytes: UVALUE_Struct field / type mismatch."
              end

          (* Packed aggregate types *)
          | UVALUE_Packed_struct [] =>
              ret []
          | UVALUE_Packed_struct (f::fields) =>
              (* TODO: take padding into account *)
              match dt with
              | DTYPE_Packed_struct (t::ts) =>
                  f_bytes <- serialize_sbytes f t;;
                  fields_bytes <- serialize_sbytes (UVALUE_Packed_struct fields) (DTYPE_Packed_struct ts);;
                  ret (f_bytes ++ fields_bytes)
              | _ =>
                  raise_error "serialize_sbytes: UVALUE_Packed_struct field / type mismatch."
              end

          | UVALUE_Array elts =>
              match dt with
              | DTYPE_Array sz t =>
                  field_bytes <- map_monad_In elts (fun elt Hin => serialize_sbytes elt t);;
                  ret (concat field_bytes)
              | _ =>
                  raise_error "serialize_sbytes: UVALUE_Array with incorrect type."
              end
          | UVALUE_Vector elts =>
              match dt with
              | DTYPE_Vector sz t =>
                  field_bytes <- map_monad_In elts (fun elt Hin => serialize_sbytes elt t);;
                  ret (concat field_bytes)
              | _ =>
                  raise_error "serialize_sbytes: UVALUE_Array with incorrect type."
              end

          | UVALUE_None => ret nil

          (* Byte manipulation. *)
          | UVALUE_ExtractByte uv dt' idx sid =>
              raise_error "serialize_sbytes: UVALUE_ExtractByte not guarded by UVALUE_ConcatBytes."

          | UVALUE_ConcatBytes bytes t =>
              (* TODO: should provide *new* sids... May need to make this function in a fresh sid monad *)
              bytes' <- lift_ERR_RAISE_ERROR (map_monad extract_byte_to_sbyte bytes);;
              re_sid_ubytes bytes'
          end.
    Proof.
      (* intros uv dt. *)
      (* unfold serialize_sbytes. *)
      (* unfold serialize_sbytes_func at 1. *)
      (* rewrite Wf.WfExtensionality.fix_sub_eq_ext. *)
      (* destruct uv. *)
      (* all: try reflexivity. *)
      (* all: cbn. *)
      (* - destruct dt; try reflexivity. *)
      (*   destruct (Datatypes.length fields0 =? Datatypes.length fields)%nat eqn:Hlen. *)
      (*   + cbn. *)
      (*     reflexivity. *)
      (*   + *)


      (* destruct uv; try reflexivity. simpl. *)
      (* destruct dt; try reflexivity. simpl. *)
      (* break_match. *)
      (*  destruct (find (fun a : ident * typ => Ident.eq_dec id (fst a)) env). *)
      (* destruct p; simpl; eauto. *)
      (* reflexivity. *)
    Admitted.

    (* deserialize_sbytes takes a list of SBytes and turns them into a uvalue. *)

  (*    This relies on the similar, but different, from_ubytes function *)
  (*    which given a set of bytes checks if all of the bytes are from *)
  (*    the same uvalue, and if so returns the original uvalue, and *)
  (*    otherwise returns a UVALUE_ConcatBytes value instead. *)

  (*    The reason we also have deserialize_sbytes is in order to deal *)
  (*    with aggregate data types. *)
  (*    *)
    Obligation Tactic := try Tactics.program_simpl; try solve [solve_dtyp_measure].
    Program Fixpoint deserialize_sbytes (bytes : list SByte) (dt : dtyp) {measure (dtyp_measure dt)} : err uvalue
      :=
      match dt with
      (* TODO: should we bother with this? *)
      (* Array and vector types *)
      | DTYPE_Array sz t =>
          let size := sizeof_dtyp t in
          let size_nat := N.to_nat size in
          fields <- monad_fold_right (fun acc idx => uv <- deserialize_sbytes (between (idx*size) ((idx+1) * size) bytes) t;; ret (uv::acc)) (Nseq 0 size_nat) [];;
          ret (UVALUE_Array fields)

      | DTYPE_Vector sz t =>
          let size := sizeof_dtyp t in
          let size_nat := N.to_nat size in
          fields <- monad_fold_right (fun acc idx => uv <- deserialize_sbytes (between (idx*size) ((idx+1) * size) bytes) t;; ret (uv::acc)) (Nseq 0 size_nat) [];;
          ret (UVALUE_Vector fields)

      (* Padded aggregate types *)
      | DTYPE_Struct fields =>
          (* TODO: Add padding *)
          match fields with
          | [] => ret (UVALUE_Struct []) (* TODO: Not 100% sure about this. *)
          | (dt::dts) =>
              let sz := sizeof_dtyp dt in
              let init_bytes := take sz bytes in
              let rest_bytes := drop sz bytes in
              f <- deserialize_sbytes init_bytes dt;;
              rest <- deserialize_sbytes rest_bytes (DTYPE_Struct dts);;
              match rest with
              | UVALUE_Struct fs =>
                  ret (UVALUE_Struct (f::fs))
              | _ =>
                  inl "deserialize_sbytes: DTYPE_Struct recursive call did not return a struct."%string
              end
          end

      (* Structures with no padding *)
      | DTYPE_Packed_struct fields =>
          match fields with
          | [] => ret (UVALUE_Packed_struct []) (* TODO: Not 100% sure about this. *)
          | (dt::dts) =>
              let sz := sizeof_dtyp dt in
              let init_bytes := take sz bytes in
              let rest_bytes := drop sz bytes in
              f <- deserialize_sbytes init_bytes dt;;
              rest <- deserialize_sbytes rest_bytes (DTYPE_Packed_struct dts);;
              match rest with
              | UVALUE_Packed_struct fs =>
                  ret (UVALUE_Packed_struct (f::fs))
              | _ =>
                  inl "deserialize_sbytes: DTYPE_Struct recursive call did not return a struct."%string
              end
          end

      (* Base types *)
      | DTYPE_I _
      | DTYPE_IPTR
      | DTYPE_Pointer
      | DTYPE_Half
      | DTYPE_Float
      | DTYPE_Double
      | DTYPE_X86_fp80
      | DTYPE_Fp128
      | DTYPE_Ppc_fp128
      | DTYPE_X86_mmx
      | DTYPE_Opaque
      | DTYPE_Metadata =>
          ret (from_ubytes bytes dt)

      | DTYPE_Void =>
          inl "deserialize_sbytes: Attempt to deserialize void."%string
      end.

    (* Serialize a uvalue into bytes and combine them into UVALUE_ConcatBytes. Useful for bitcasts.

       dt should be the type of the thing you are casting to in the case of bitcasts.
     *)
    Definition uvalue_to_concatbytes
               {M} `{Monad M} `{MonadStoreId M} `{RAISE_ERROR M} `{RAISE_OOM M}
               (uv : uvalue) (dt : dtyp) : M uvalue :=
      bytes <- serialize_sbytes uv dt;;
      ret (UVALUE_ConcatBytes (map sbyte_to_extractbyte bytes) dt).

  (* (* TODO: *) *)

  (*  (*   What is the difference between a pointer and an integer...? *) *)

  (*  (*   Primarily, it's that pointers have provenance and integers don't? *) *)

  (*  (*   So, if we do PVI is there really any difference between an address *) *)
  (*  (*   and an integer, and should we actually distinguish between them? *) *)

  (*  (*   Provenance in UVALUE_IPTR probably means we need provenance in *all* *) *)
  (*  (*   data types... i1, i8, i32, etc, and even doubles and floats... *) *)
  (*  (*  *) *)

  (* (* TODO: *) *)

  (*  (*    Should uvalue have something like... UVALUE_ExtractByte which *) *)
  (*  (*    extracts a certain byte out of a uvalue? *) *)

  (*  (*    Will probably need an equivalence relation on UVALUEs, likely won't *) *)
  (*  (*    end up with a round-trip property with regular equality... *) *)
  (*  (* *) *)

  End Serialization.
End MemoryHelpers.

Module Type MemoryModelSpec (LP : LLVMParams) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP).
  Import LP.
  Import LP.Events.
  Import LP.ADDR.
  Import LP.SIZEOF.
  Import LP.PROV.
  Import LP.PTOI.
  Import MMSP.

  Module OVER := PTOIOverlaps ADDR PTOI SIZEOF.
  Import OVER.
  Module OVER_H := OverlapHelpers ADDR SIZEOF OVER.
  Import OVER_H.

  Import MemByte.

  Module MemHelpers := MemoryHelpers LP MP MemByte.
  Import MemHelpers.

  Definition read_byte_prop (ms : MemState) (ptr : addr) (byte : SByte) : Prop
    := read_byte_MemPropT ptr (MemState_get_memory ms) (ret ((MemState_get_memory ms), byte)).

  Definition lift_memory_MemPropT {X} (m : MemPropT memory_stack X) : MemPropT MemState X :=
    fun ms res =>
      m (MemState_get_memory ms) (fmap (fun '(ms, x) => (MemState_get_memory ms, x)) res) /\
        (* Provenance should be preserved as memory operation shouldn't touch rest of MemState *)
        forall ms' x, res = ret (ms', x) -> MemState_get_provenance ms = MemState_get_provenance ms'.

  Definition byte_allocated_MemPropT (ptr : addr) (aid : AllocationId) : MemPropT MemState unit :=
    b <- lift_memory_MemPropT (addr_allocated_prop ptr aid);;
    MemPropT_assert (b = true).

  Definition byte_allocated (ms : MemState) (ptr : addr) (aid : AllocationId) : Prop
    := byte_allocated_MemPropT ptr aid ms (ret (ms, tt)).

  Definition byte_not_allocated (ms : MemState) (ptr : addr) : Prop
    := forall (aid : AllocationId), ~ byte_allocated ms ptr aid.

  (** Addresses *)
  Definition disjoint_ptr_byte (a b : addr) :=
    ptr_to_int a <> ptr_to_int b.

  (*** Predicates *)

  (** Reads *)
  Definition read_byte_allowed (ms : MemState) (ptr : addr) : Prop :=
    exists aid, byte_allocated ms ptr aid /\ access_allowed (address_provenance ptr) aid = true.

  Definition read_byte_allowed_all_preserved (m1 m2 : MemState) : Prop :=
    forall ptr,
      read_byte_allowed m1 ptr <-> read_byte_allowed m2 ptr.

  Definition read_byte_prop_all_preserved (m1 m2 : MemState) : Prop :=
    forall ptr byte,
      read_byte_prop m1 ptr byte <-> read_byte_prop m2 ptr byte.

  Definition read_byte_preserved (m1 m2 : MemState) : Prop :=
    read_byte_allowed_all_preserved m1 m2 /\ read_byte_prop_all_preserved m1 m2.

  (** Writes *)
  Definition write_byte_allowed (ms : MemState) (ptr : addr) : Prop :=
    exists aid, byte_allocated ms ptr aid /\ access_allowed (address_provenance ptr) aid = true.

  Definition write_byte_allowed_all_preserved (m1 m2 : MemState) : Prop :=
    forall ptr,
      write_byte_allowed m1 ptr <-> write_byte_allowed m2 ptr.

  (** Allocations *)
  Definition allocations_preserved (m1 m2 : MemState) : Prop :=
    forall ptr aid, byte_allocated m1 ptr aid <-> byte_allocated m2 ptr aid.

  (** Provenances / allocation ids *)
  Definition extend_provenance (ms : MemState) (new_pr : Provenance) (ms' : MemState) : Prop
    := (forall pr, used_provenance_prop ms pr -> used_provenance_prop ms' pr) /\
         ~ used_provenance_prop ms new_pr /\
         used_provenance_prop ms' new_pr.

  Definition preserve_allocation_ids (ms ms' : MemState) : Prop
    := forall p, used_provenance_prop ms p <-> used_provenance_prop ms' p.

  (** Store ids *)
  Definition used_store_id_prop (ms : MemState) (sid : store_id) : Prop
    := exists ptr byte, read_byte_prop ms ptr byte /\ sbyte_sid byte = inr sid.

  Definition fresh_store_id (ms : MemState) (new_sid : store_id) : Prop
    := ~ used_store_id_prop ms new_sid.

  (** Frame stack *)
  Definition frame_stack_preserved (m1 m2 : MemState) : Prop
    := forall fs,
      memory_stack_frame_stack_prop (MemState_get_memory m1) fs <-> memory_stack_frame_stack_prop (MemState_get_memory m2) fs.

  (** Heap *)
  Definition heap_preserved (m1 m2 : MemState) : Prop
    := forall h,
      memory_stack_heap_prop (MemState_get_memory m1) h <-> memory_stack_heap_prop (MemState_get_memory m2) h.

  (*** Provenance operations *)
  #[global] Instance MemPropT_MonadProvenance : MonadProvenance Provenance (MemPropT MemState).
  Proof.
    (* Need to be careful with allocation ids / provenances (more so than store ids)

       They can never be reused. E.g., if you have a pointer `p` with
       allocation id `aid`, and that block is freed, you can't reuse
       `aid` without causing problems. If you allocate a new block
       with `aid` again, then `p` may still be around and may be able
       to access the block.

       Therefore the MemState has to have some idea of what allocation
       ids have been used in the past, not just the allocation ids
       that are *currently* in use.
    *)
    split.
    - (* fresh_provenance *)
      unfold MemPropT.
      intros ms [[[[[[[oom_res] | [[ub_res] | [[err_res] | [ms' new_pr]]]]]]]]].
      + exact True.
      + exact False.
      + exact True.
      + exact
          ( extend_provenance ms new_pr ms' /\
              read_byte_preserved ms ms' /\
              write_byte_allowed_all_preserved ms ms' /\
              allocations_preserved ms ms' /\
              frame_stack_preserved ms ms' /\
              heap_preserved ms ms'
          ).
  Defined.

  (*** Store id operations *)
  #[global] Instance MemPropT_MonadStoreID : MonadStoreId (MemPropT MemState).
  Proof.
    split.
    - (* fresh_sid *)
      unfold MemPropT.
      intros ms [[[[[[[oom_res] | [[ub_res] | [[err_res] | [ms' new_sid]]]]]]]]].
      + exact True.
      + exact False.
      + exact True.
      + exact
          ( fresh_store_id ms' new_sid /\
              preserve_allocation_ids ms ms' /\
              read_byte_preserved ms ms' /\
              write_byte_allowed_all_preserved ms ms' /\
              allocations_preserved ms ms' /\
              frame_stack_preserved ms ms' /\
              heap_preserved ms ms'
          ).
  Defined.

  (*** Reading from memory *)
  Record read_byte_spec (ms : MemState) (ptr : addr) (byte : SByte) : Prop :=
    { read_byte_allowed_spec : read_byte_allowed ms ptr;
      read_byte_value : read_byte_prop ms ptr byte;
    }.

  Definition read_byte_spec_MemPropT (ptr : addr) : MemPropT MemState SByte :=
    fun m1 res =>
      match run_err_ub_oom res with
      | inl (OOM_message x) =>
          True
      | inr (inl (UB_message x)) =>
          forall byte, ~ read_byte_spec m1 ptr byte
      | inr (inr (inl (ERR_message x))) =>
          True
      | inr (inr (inr (m2, byte))) =>
          m1 = m2 /\ read_byte_spec m1 ptr byte
      end.

  (*** Framestack operations *)
  Definition empty_frame (f : Frame) : Prop :=
    forall ptr, ~ ptr_in_frame_prop f ptr.

  Record add_ptr_to_frame (f1 : Frame) (ptr : addr) (f2 : Frame) : Prop :=
    {
      old_frame_lu : forall ptr', disjoint_ptr_byte ptr ptr' ->
                             ptr_in_frame_prop f1 ptr' <-> ptr_in_frame_prop f2 ptr';
      new_frame_lu : ptr_in_frame_prop f2 ptr;
    }.

  Record empty_frame_stack (fs : FrameStack) : Prop :=
    {
      no_pop : (forall f, ~ pop_frame_stack_prop fs f);
      empty_fs_empty_frame : forall f, peek_frame_stack_prop fs f -> empty_frame f;
    }.

  Record push_frame_stack_spec (fs1 : FrameStack) (f : Frame) (fs2 : FrameStack) : Prop :=
    {
      can_pop : pop_frame_stack_prop fs2 fs1;
      new_frame : peek_frame_stack_prop fs2 f;
    }.

  Definition ptr_in_current_frame (ms : MemState) (ptr : addr) : Prop
    := forall fs, memory_stack_frame_stack_prop (MemState_get_memory ms) fs ->
             forall f, peek_frame_stack_prop fs f ->
                  ptr_in_frame_prop f ptr.

  (** mempush *)
  Record mempush_operation_invariants (m1 : MemState) (m2 : MemState) :=
    {
      mempush_op_reads : read_byte_preserved m1 m2;
      mempush_op_write_allowed : write_byte_allowed_all_preserved m1 m2;
      mempush_op_allocations : allocations_preserved m1 m2;
      mempush_op_allocation_ids : preserve_allocation_ids m1 m2;
      mempush_heap_preserved : heap_preserved m1 m2;
    }.

  Record mempush_spec (m1 : MemState) (m2 : MemState) : Prop :=
    {
      fresh_frame :
      forall fs1 fs2 f,
        memory_stack_frame_stack_prop (MemState_get_memory m1) fs1 ->
        empty_frame f ->
        push_frame_stack_spec fs1 f fs2 ->
        memory_stack_frame_stack_prop (MemState_get_memory m2) fs2;

      mempush_invariants :
      mempush_operation_invariants m1 m2;
    }.

  Definition mempush_spec_MemPropT : MemPropT MemState unit :=
    fun m1 res =>
      match run_err_ub_oom res with
      | inl (OOM_message x) =>
          True
      | inr (inl (UB_message x)) =>
          forall m2, ~ mempush_spec m1 m2
      | inr (inr (inl (ERR_message x))) =>
          True
      | inr (inr (inr (m2, tt))) =>
          mempush_spec m1 m2
      end.

  (** mempop *)
  Record mempop_operation_invariants (m1 : MemState) (m2 : MemState) :=
    {
      mempop_op_allocation_ids : preserve_allocation_ids m1 m2;
      mempop_heap_preserved : heap_preserved m1 m2;
    }.

  Record mempop_spec (m1 : MemState) (m2 : MemState) : Prop :=
    {
      (* all bytes in popped frame are freed. *)
      bytes_freed :
      forall ptr,
        ptr_in_current_frame m1 ptr ->
        byte_not_allocated m2 ptr;

      (* Bytes not allocated in the popped frame have the same allocation status as before *)
      non_frame_bytes_preserved :
      forall ptr aid,
        (~ ptr_in_current_frame m1 ptr) ->
        byte_allocated m1 ptr aid <-> byte_allocated m2 ptr aid;

      (* Bytes not allocated in the popped frame are the same when read *)
      non_frame_bytes_read :
      forall ptr byte,
        (~ ptr_in_current_frame m1 ptr) ->
        read_byte_spec m1 ptr byte <-> read_byte_spec m2 ptr byte;

      (* Set new framestack *)
      pop_frame :
      forall fs1 fs2,
        memory_stack_frame_stack_prop (MemState_get_memory m1) fs1 ->
        pop_frame_stack_prop fs1 fs2 ->
        memory_stack_frame_stack_prop (MemState_get_memory m2) fs2;

      (* Invariants *)
      mempop_invariants : mempop_operation_invariants m1 m2;
    }.

  Definition mempop_spec_MemPropT : MemPropT MemState unit :=
    fun m1 res =>
      match run_err_ub_oom res with
      | inl (OOM_message x) =>
          True
      | inr (inl (UB_message x)) =>
          forall m2, ~ mempop_spec m1 m2
      | inr (inr (inl (ERR_message x))) =>
          True
      | inr (inr (inr (m2, tt))) =>
          mempop_spec m1 m2
      end.

  (* Add a pointer onto the current frame in the frame stack *)
  Definition add_ptr_to_frame_stack (fs1 : FrameStack) (ptr : addr) (fs2 : FrameStack) : Prop :=
    forall f,
      peek_frame_stack_prop fs1 f ->
      exists f', add_ptr_to_frame f ptr f' /\
              peek_frame_stack_prop fs2 f' /\
              (forall fs1_pop, pop_frame_stack_prop fs1 fs1_pop <-> pop_frame_stack_prop fs2 fs1_pop).

  Fixpoint add_ptrs_to_frame_stack (fs1 : FrameStack) (ptrs : list addr) (fs2 : FrameStack) : Prop :=
    match ptrs with
    | nil => frame_stack_eqv fs1 fs2
    | (ptr :: ptrs) =>
        exists fs',
          add_ptrs_to_frame_stack fs1 ptrs fs' /\
            add_ptr_to_frame_stack fs' ptr fs2
    end.

  (*** Heap operations *)
  Record empty_heap (h : Heap) : Prop :=
    {
      empty_heap_no_roots : forall root,
        ~ root_in_heap_prop h root;

      empty_heap_no_ptrs : forall root ptr,
        ~ ptr_in_heap_prop h root ptr;
    }.

  Definition root_in_memstate_heap (ms : MemState) (root : addr) : Prop
    := forall h, memory_stack_heap_prop (MemState_get_memory ms) h ->
            root_in_heap_prop h root.

  Definition ptr_in_memstate_heap (ms : MemState) (root : addr) (ptr : addr) : Prop
    := forall h, memory_stack_heap_prop (MemState_get_memory ms) h ->
            ptr_in_heap_prop h root ptr.

  Record add_ptr_to_heap (h1 : Heap) (root : addr) (ptr : addr) (h2 : Heap) : Prop :=
    {
      old_heap_lu : forall ptr', 
        disjoint_ptr_byte ptr ptr' ->
        forall root, ptr_in_heap_prop h1 root ptr' <-> ptr_in_heap_prop h2 root ptr';

      old_heap_lu_different_root : forall root', 
        disjoint_ptr_byte root root' ->
        forall ptr', ptr_in_heap_prop h1 root' ptr' <-> ptr_in_heap_prop h2 root' ptr';

      old_heap_roots : forall root',
        disjoint_ptr_byte root root' ->
        root_in_heap_prop h1 root' <-> root_in_heap_prop h2 root';

      new_heap_lu :
      ptr_in_heap_prop h2 root ptr;

      new_heap_root :
      root_in_heap_prop h2 root;
    }.

  Fixpoint add_ptrs_to_heap' (h1 : Heap) (root : addr) (ptrs : list addr) (h2 : Heap) : Prop :=
    match ptrs with
    | nil => heap_eqv h1 h2
    | (ptr :: ptrs) =>
        exists h',
        add_ptrs_to_heap' h1 root ptrs h' /\
          add_ptr_to_heap h' root ptr h2
    end.

  Definition add_ptrs_to_heap (h1 : Heap) (ptrs : list addr) (h2 : Heap) : Prop :=
    match ptrs with
    | nil => heap_eqv h1 h2
    | (ptr :: _) =>
        add_ptrs_to_heap' h1 ptr ptrs h2
    end.

  (*** Writing to memory *)
  Record set_byte_memory (m1 : MemState) (ptr : addr) (byte : SByte) (m2 : MemState) : Prop :=
    {
      new_lu : read_byte_spec m2 ptr byte;
      old_lu : forall ptr' byte',
        disjoint_ptr_byte ptr ptr' ->
        (read_byte_spec m1 ptr' byte' <-> read_byte_spec m2 ptr' byte');
    }.

  Record write_byte_operation_invariants (m1 m2 : MemState) : Prop :=
    {
      write_byte_op_preserves_allocations : allocations_preserved m1 m2;
      write_byte_op_preserves_frame_stack : frame_stack_preserved m1 m2;
      write_byte_op_preserves_heap : heap_preserved m1 m2;
      write_byte_op_read_allowed : read_byte_allowed_all_preserved m1 m2;
      write_byte_op_write_allowed : write_byte_allowed_all_preserved m1 m2;
      write_byte_op_allocation_ids : preserve_allocation_ids m1 m2;
    }.

  Record write_byte_spec (m1 : MemState) (ptr : addr) (byte : SByte) (m2 : MemState) : Prop :=
    {
      byte_write_succeeds : write_byte_allowed m1 ptr;
      byte_written : set_byte_memory m1 ptr byte m2;

      write_byte_invariants : write_byte_operation_invariants m1 m2;
    }.

  Definition write_byte_spec_MemPropT (ptr : addr) (byte : SByte) : MemPropT MemState unit
    := fun m1 res =>
         match run_err_ub_oom res with
         | inl (OOM_message x) =>
             True
         | inr (inl (UB_message x)) =>
             forall m2, ~ write_byte_spec m1 ptr byte m2
         | inr (inr (inl (ERR_message x))) =>
             True
         | inr (inr (inr (m2, tt))) =>
             write_byte_spec m1 ptr byte m2
         end.

  (*** Allocating bytes on the stack *)
  Record allocate_bytes_succeeds_spec (m1 : MemState) (t : dtyp) (init_bytes : list SByte) (pr : Provenance) (m2 : MemState) (ptr : addr) (ptrs : list addr) : Prop :=
    { (* The allocated pointers are consecutive in memory. *)
      (* m1 doesn't really matter here. *)
      allocate_bytes_consecutive : get_consecutive_ptrs ptr (length init_bytes) m1 (ret (m1, ptrs));

      (* Provenance *)
      allocate_bytes_address_provenance : address_provenance ptr = allocation_id_to_prov (provenance_to_allocation_id pr); (* Need this case if `ptrs` is empty (allocating 0 bytes) *)
      allocate_bytes_addresses_provenance : forall ptr, In ptr ptrs -> address_provenance ptr = allocation_id_to_prov (provenance_to_allocation_id pr);
      allocate_bytes_provenances_preserved :
      forall pr',
        (used_provenance_prop m1 pr' <-> used_provenance_prop m2 pr');

      (* byte_allocated *)
      allocate_bytes_was_fresh_byte : forall ptr, In ptr ptrs -> byte_not_allocated m1 ptr;
      allocate_bytes_now_byte_allocated : forall ptr, In ptr ptrs -> byte_allocated m2 ptr (provenance_to_allocation_id pr);
      allocate_bytes_preserves_old_allocations :
      forall ptr aid,
        (forall p, In p ptrs -> disjoint_ptr_byte p ptr) ->
        (byte_allocated m1 ptr aid <-> byte_allocated m2 ptr aid);

      (* read permissions *)
      alloc_bytes_new_reads_allowed :
      forall p, In p ptrs ->
           read_byte_allowed m2 p;

      alloc_bytes_old_reads_allowed :
      forall ptr',
        (forall p, In p ptrs -> disjoint_ptr_byte p ptr') ->
        read_byte_allowed m1 ptr' <-> read_byte_allowed m2 ptr';

      (* reads *)
      alloc_bytes_new_reads :
      forall p ix byte,
        Util.Nth ptrs ix p ->
        Util.Nth init_bytes ix byte ->
        read_byte_prop m2 p byte;

      alloc_bytes_old_reads :
      forall ptr' byte,
        (forall p, In p ptrs -> disjoint_ptr_byte p ptr') ->
        read_byte_prop m1 ptr' byte <-> read_byte_prop m2 ptr' byte;

      (* write permissions *)
      alloc_bytes_new_writes_allowed :
      forall p, In p ptrs ->
           write_byte_allowed m2 p;

      alloc_bytes_old_writes_allowed :
      forall ptr',
        (forall p, In p ptrs -> disjoint_ptr_byte p ptr') ->
        write_byte_allowed m1 ptr' <-> write_byte_allowed m2 ptr';

      (* Add allocated bytes onto the stack frame *)
      allocate_bytes_add_to_frame :
      forall fs1 fs2,
        memory_stack_frame_stack_prop (MemState_get_memory m1) fs1 ->
        add_ptrs_to_frame_stack fs1 ptrs fs2 ->
        memory_stack_frame_stack_prop (MemState_get_memory m2) fs2;

      (* Heap preserved *)
      allocate_bytes_heap_preserved :
      heap_preserved m1 m2;

      (* Type is valid *)
      allocate_bytes_typ :
      t <> DTYPE_Void;

      allocate_bytes_typ_size :
      sizeof_dtyp t = N.of_nat (length init_bytes);
    }.

  Definition allocate_bytes_spec_MemPropT' (t : dtyp) (init_bytes : list SByte) (prov : Provenance)
    : MemPropT MemState (addr * list addr)
    := fun m1 res =>
         match run_err_ub_oom res with
         | inl (OOM_message x) =>
             True
         | inr (inl (UB_message x)) =>
             forall m2 ptr ptrs, ~ allocate_bytes_succeeds_spec m1 t init_bytes prov m2 ptr ptrs
         | inr (inr (inl (ERR_message x))) =>
             True
         | inr (inr (inr (m2, (ptr, ptrs)))) =>
             allocate_bytes_succeeds_spec m1 t init_bytes prov m2 ptr ptrs
         end.

  Definition allocate_bytes_spec_MemPropT (t : dtyp) (init_bytes : list SByte)
    : MemPropT MemState addr
    := prov <- fresh_provenance;;
       '(ptr, _) <- allocate_bytes_spec_MemPropT' t init_bytes prov;;
       ret ptr.

  (*** Allocating bytes in the heap *)
  Record malloc_bytes_succeeds_spec (m1 : MemState) (init_bytes : list SByte) (pr : Provenance) (m2 : MemState) (ptr : addr) (ptrs : list addr) : Prop :=
    {
      (* The allocated pointers are consecutive in memory. *)
      (* m1 doesn't really matter here. *)
      malloc_bytes_consecutive : get_consecutive_ptrs ptr (length init_bytes) m1 (ret (m1, ptrs));

      (* Provenance *)
      malloc_bytes_address_provenance : address_provenance ptr = allocation_id_to_prov (provenance_to_allocation_id pr); (* Need this case if `ptrs` is empty (allocating 0 bytes) *)
      malloc_bytes_addresses_provenance : forall ptr, In ptr ptrs -> address_provenance ptr = allocation_id_to_prov (provenance_to_allocation_id pr);
      malloc_bytes_provenances_preserved :
      forall pr',
        (used_provenance_prop m1 pr' <-> used_provenance_prop m2 pr');

      (* byte_allocated *)
      malloc_bytes_was_fresh_byte : forall ptr, In ptr ptrs -> byte_not_allocated m1 ptr;
      malloc_bytes_now_byte_allocated : forall ptr, In ptr ptrs -> byte_allocated m2 ptr (provenance_to_allocation_id pr);
      malloc_bytes_preserves_old_allocations :
      forall ptr aid,
        (forall p, In p ptrs -> disjoint_ptr_byte p ptr) ->
        (byte_allocated m1 ptr aid <-> byte_allocated m2 ptr aid);

      (* read permissions *)
      malloc_bytes_new_reads_allowed :
      forall p, In p ptrs ->
           read_byte_allowed m2 p;

      malloc_bytes_old_reads_allowed :
      forall ptr',
        (forall p, In p ptrs -> disjoint_ptr_byte p ptr') ->
        read_byte_allowed m1 ptr' <-> read_byte_allowed m2 ptr';

      (* reads *)
      malloc_bytes_new_reads :
      forall p ix byte,
        Util.Nth ptrs ix p ->
        Util.Nth init_bytes ix byte ->
        read_byte_prop m2 p byte;

      malloc_bytes_old_reads :
      forall ptr' byte,
        (forall p, In p ptrs -> disjoint_ptr_byte p ptr') ->
        read_byte_prop m1 ptr' byte <-> read_byte_prop m2 ptr' byte;

      (* write permissions *)
      malloc_bytes_new_writes_allowed :
      forall p, In p ptrs ->
           write_byte_allowed m2 p;

      malloc_bytes_old_writes_allowed :
      forall ptr',
        (forall p, In p ptrs -> disjoint_ptr_byte p ptr') ->
        write_byte_allowed m1 ptr' <-> write_byte_allowed m2 ptr';

      (* Framestack preserved *)
      malloc_bytes_frame_stack_preserved : frame_stack_preserved m1 m2;

      (* Heap extended *)
      malloc_bytes_add_to_frame :
      forall h1 h2,
        memory_stack_heap_prop (MemState_get_memory m1) h1 ->
        add_ptrs_to_heap h1 ptrs h2 ->
        memory_stack_heap_prop (MemState_get_memory m2) h2;
    }.

  Definition malloc_bytes_spec_MemPropT' (init_bytes : list SByte) (prov : Provenance)
    : MemPropT MemState (addr * list addr)
    := fun m1 res =>
         match run_err_ub_oom res with
         | inl (OOM_message x) =>
             True
         | inr (inl (UB_message x)) =>
             forall m2 ptr ptrs, ~ malloc_bytes_succeeds_spec m1 init_bytes prov m2 ptr ptrs
         | inr (inr (inl (ERR_message x))) =>
             True
         | inr (inr (inr (m2, (ptr, ptrs)))) =>
             malloc_bytes_succeeds_spec m1 init_bytes prov m2 ptr ptrs
         end.

  Definition malloc_bytes_spec_MemPropT (init_bytes : list SByte)
    : MemPropT MemState addr
    := prov <- fresh_provenance;;
       '(ptr, _) <- malloc_bytes_spec_MemPropT' init_bytes prov;;
       ret ptr.

  (*** Freeing heap allocations *)
  Record free_operation_invariants (m1 : MemState) (m2 : MemState) :=
    {
      free_op_allocation_ids : preserve_allocation_ids m1 m2;
      free_frame_stack_preserved : frame_stack_preserved m1 m2;
    }.

  Record free_block_prop (h1 : Heap) (root : addr) (h2 : Heap) : Prop :=
    { free_block_ptrs_freed :
      forall ptr,
        ptr_in_heap_prop h1 root ptr ->
        ~ ptr_in_heap_prop h2 root ptr;

      free_block_root_freed :
      ~ root_in_heap_prop h2 root;

      (* TODO: make sure there's no weirdness about multiple roots *)
      free_block_disjoint_preserved :
      forall ptr root',
        disjoint_ptr_byte root root' ->
        ptr_in_heap_prop h1 root' ptr <-> ptr_in_heap_prop h2 root' ptr;

      free_block_disjoint_roots :
      forall root',
        disjoint_ptr_byte root root' ->
        root_in_heap_prop h1 root' <-> root_in_heap_prop h2 root';
    }.

  Record free_spec (m1 : MemState) (root : addr) (m2 : MemState) : Prop :=
    { (* ptr being freed was a root *)
      free_was_root :
      root_in_memstate_heap m1 root;

      (* all bytes in block are freed. *)
      free_bytes_freed :
      forall ptr,
        ptr_in_memstate_heap m1 root ptr ->
        byte_not_allocated m2 ptr;

      (* Bytes not allocated in the block have the same allocation status as before *)
      free_non_block_bytes_preserved :
      forall ptr aid,
        (~ ptr_in_memstate_heap m1 root ptr) ->
        byte_allocated m1 ptr aid <-> byte_allocated m2 ptr aid;

      (* Bytes not allocated in the freed block are the same when read *)
      free_non_frame_bytes_read :
      forall ptr byte,
        (~ ptr_in_memstate_heap m1 root ptr) ->
        read_byte_spec m1 ptr byte <-> read_byte_spec m2 ptr byte;

      (* Set new heap *)
      free_block :
      forall h1 h2,
        memory_stack_heap_prop (MemState_get_memory m1) h1 ->
        memory_stack_heap_prop (MemState_get_memory m2) h2 ->
        free_block_prop h1 root h2;

      (* Invariants *)
      free_invariants : free_operation_invariants m1 m2;
    }.

  Definition free_spec_MemPropT (root : addr) : MemPropT MemState unit :=
    fun m1 res =>
      match run_err_ub_oom res with
      | inl (OOM_message x) =>
          True
      | inr (inl (UB_message x)) =>
          forall m2, ~ free_spec m1 root m2
      | inr (inr (inl (ERR_message x))) =>
          True
      | inr (inr (inr (m2, tt))) =>
          free_spec m1 root m2
      end.

  (*** Aggregate things *)

  (** Reading uvalues *)
  Definition read_bytes_spec (ptr : addr) (len : nat) : MemPropT MemState (list SByte) :=
    (* TODO: should this OOM, or should this count as walking outside of memory and be UB? *)
    ptrs <- get_consecutive_ptrs ptr len;;

    (* Actually perform reads *)
    Util.map_monad (fun ptr => read_byte_spec_MemPropT ptr) ptrs.

  Definition read_uvalue_spec (dt : dtyp) (ptr : addr) : MemPropT MemState uvalue :=
    bytes <- read_bytes_spec ptr (N.to_nat (sizeof_dtyp dt));;
    lift_err_RAISE_ERROR (deserialize_sbytes bytes dt).

  (** Writing uvalues *)
  Definition write_bytes_spec (ptr : addr) (bytes : list SByte) : MemPropT MemState unit :=
    ptrs <- get_consecutive_ptrs ptr (length bytes);;
    let ptr_bytes := zip ptrs bytes in

    (* TODO: double check that this is correct... Should we check if all writes are allowed first? *)
    (* Actually perform writes *)
    Util.map_monad_ (fun '(ptr, byte) => write_byte_spec_MemPropT ptr byte) ptr_bytes.

  Definition write_uvalue_spec (dt : dtyp) (ptr : addr) (uv : uvalue) : MemPropT MemState unit :=
    bytes <- serialize_sbytes uv dt;;
    write_bytes_spec ptr bytes.

  (** Allocating dtyps *)
  (* Need to make sure MemPropT has provenance and sids to generate the bytes. *)
  Definition allocate_dtyp_spec (dt : dtyp) : MemPropT MemState addr :=
    sid <- fresh_sid;;
    bytes <- lift_OOM (generate_undef_bytes dt sid);;
    allocate_bytes_spec_MemPropT dt bytes.

  (** memcpy spec *)
  Definition memcpy_spec (src dst : addr) (len : Z) (align : N) (volatile : bool) : MemPropT MemState unit :=
    if Z.ltb len 0
    then
      raise_ub "memcpy given negative length."
    else
      (* From LangRef: The ‘llvm.memcpy.*’ intrinsics copy a block of
       memory from the source location to the destination location, which
       must either be equal or non-overlapping.
       *)
      if orb (no_overlap dst len src len)
             (Z.eqb (ptr_to_int src) (ptr_to_int dst))
      then
        src_bytes <- read_bytes_spec src (Z.to_nat len);;

        (* TODO: Double check that this is correct... Should we check if all writes are allowed first? *)
        write_bytes_spec dst src_bytes
      else
        raise_ub "memcpy with overlapping or non-equal src and dst memory locations.".

  (*** Handling memory events *)
  Section Handlers.
    Definition handle_memory_prop : MemoryE ~> MemPropT MemState
      := fun T m =>
           match m with
           (* Unimplemented *)
           | MemPush =>
               mempush_spec_MemPropT
           | MemPop =>
               mempop_spec_MemPropT
           | Alloca t =>
               addr <- allocate_dtyp_spec t;;
               ret (DVALUE_Addr addr)
           | Load t a =>
               match a with
               | DVALUE_Addr a =>
                   read_uvalue_spec t a
               | _ => raise_ub "Loading from something that isn't an address."
               end
           | Store t a v =>
               match a with
               | DVALUE_Addr a =>
                   write_uvalue_spec t a v
               | _ => raise_ub "Writing something to somewhere that isn't an address."
               end
           end.

    Definition handle_memcpy_prop (args : list dvalue) : MemPropT MemState unit :=
      match args with
      | DVALUE_Addr dst ::
                    DVALUE_Addr src ::
                    DVALUE_I32 len ::
                    DVALUE_I32 align :: (* alignment ignored *)
                    DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          memcpy_spec src dst (unsigned len) (Z.to_N (unsigned align)) (equ volatile one)
      | DVALUE_Addr dst ::
                    DVALUE_Addr src ::
                    DVALUE_I64 len ::
                    DVALUE_I64 align :: (* alignment ignored *)
                    DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          memcpy_spec src dst (unsigned len) (Z.to_N (unsigned align)) (equ volatile one)
      | DVALUE_Addr dst ::
                    DVALUE_Addr src ::
                    DVALUE_IPTR len ::
                    DVALUE_IPTR align :: (* alignment ignored *)
                    DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          memcpy_spec src dst (IP.to_Z len) (Z.to_N (IP.to_Z align)) (equ volatile one)
      | _ => raise_error "Unsupported arguments to memcpy."
      end.

    Definition handle_malloc_prop (args : list dvalue) : MemPropT MemState addr :=
      match args with
      | [DVALUE_I1 sz]
      | [DVALUE_I8 sz]
      | [DVALUE_I32 sz]
      | [DVALUE_I64 sz] =>
          sid <- fresh_sid;;
          bytes <- lift_OOM (generate_num_undef_bytes (Z.to_N (unsigned sz)) (DTYPE_I 8) sid);;
          malloc_bytes_spec_MemPropT bytes
      | [DVALUE_IPTR sz] =>
          sid <- fresh_sid;;
          bytes <- lift_OOM (generate_num_undef_bytes (Z.to_N (IP.to_unsigned sz)) (DTYPE_I 8) sid);;
          malloc_bytes_spec_MemPropT bytes
      | _ => raise_error "Malloc: invalid arguments."
      end.

    Definition handle_free_prop (args : list dvalue) : MemPropT MemState unit :=
      match args with
      | [DVALUE_Addr ptr] =>
          free_spec_MemPropT ptr
      | _ => raise_error "Free: invalid arguments."
      end.

    Definition handle_intrinsic_prop : IntrinsicE ~> MemPropT MemState
      := fun T e =>
           match e with
           | Intrinsic t name args =>
               (* Pick all arguments, they should all be unique. *)
               (* TODO: add more variants to memcpy *)
               (* FIXME: use reldec typeclass? *)
               if orb (Coqlib.proj_sumbool (string_dec name "llvm.memcpy.p0i8.p0i8.i32"))
                      (Coqlib.proj_sumbool (string_dec name "llvm.memcpy.p0i8.p0i8.i64"))
               then
                 handle_memcpy_prop args;;
                 ret DVALUE_None
               else
                 if (Coqlib.proj_sumbool (string_dec name "malloc"))
                 then
                   addr <- handle_malloc_prop args;;
                   ret (DVALUE_Addr addr)
                 else
                   if (Coqlib.proj_sumbool (string_dec name "free"))
                   then
                        handle_free_prop args;;
                        ret DVALUE_None
                   else
                     raise_error ("Unknown intrinsic: " ++ name)
           end.

  End Handlers.
End MemoryModelSpec.

Module MakeMemoryModelSpec (LP : LLVMParams) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) <: MemoryModelSpec LP MP MMSP.
  Include MemoryModelSpec LP MP MMSP.
End MakeMemoryModelSpec.

Module Type MemoryExecMonad (LP : LLVMParams) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MMS : MemoryModelSpec LP MP MMSP).
  (* TODO: move these imports *)
  Import EitherMonad.
  Import Monad.
  Require Import Morphisms.
  From Vellvm Require Import
       MonadEq1Laws
       Raise.

  Import LP.
  Import PROV.
  Import MMSP.
  Import MMS.

  Class MemMonad (ExtraState : Type) (M : Type -> Type) (RunM : Type -> Type)
        `{MM : Monad M} `{MRun: Monad RunM}
        `{MPROV : MonadProvenance Provenance M} `{MSID : MonadStoreId M} `{MMS: MonadMemState MemState M}
        `{MERR : RAISE_ERROR M} `{MUB : RAISE_UB M} `{MOOM :RAISE_OOM M}
        `{RunERR : RAISE_ERROR RunM} `{RunUB : RAISE_UB RunM} `{RunOOM :RAISE_OOM RunM}
    : Type
    :=
    { MemMonad_eq1_runm :> Eq1 RunM;
      MemMonad_runm_monadlaws :> MonadLawsE RunM;
      MemMonad_eq1_runm_equiv {A} :> Equivalence (@eq1 _ MemMonad_eq1_runm A);
      MemMonad_eq1_runm_eq1laws :> Eq1_ret_inv RunM;
      MemMonad_raisebindm_ub :> RaiseBindM RunM string (@raise_ub RunM RunUB);
      MemMonad_raisebindm_oom :> RaiseBindM RunM string (@raise_oom RunM RunOOM);
      MemMonad_raisebindm_err :> RaiseBindM RunM string (@raise_error RunM RunERR);

      MemMonad_eq1_runm_proper :>
                               (forall A, Proper ((@eq1 _ MemMonad_eq1_runm) A ==> (@eq1 _ MemMonad_eq1_runm) A ==> iff) ((@eq1 _ MemMonad_eq1_runm) A));

      MemMonad_run {A} (ma : M A) (ms : MemState) (st : ExtraState)
      : RunM (ExtraState * (MemState * A))%type;

      (** Whether a piece of extra state is valid for a given execution *)
      MemMonad_valid_state : MemState -> ExtraState -> Prop;

    (** Run bind / ret laws *)
    MemMonad_run_bind
      {A B} (ma : M A) (k : A -> M B) (ms : MemState) (st : ExtraState):
    eq1 (MemMonad_run (x <- ma;; k x) ms st)
        ('(st', (ms', x)) <- MemMonad_run ma ms st;; MemMonad_run (k x) ms' st');

    MemMonad_run_ret
      {A} (x : A) (ms : MemState) st:
    eq1 (MemMonad_run (ret x) ms st) (ret (st, (ms, x)));

    (** MonadMemState properties *)
    MemMonad_get_mem_state
      (ms : MemState) st :
    eq1 (MemMonad_run (get_mem_state) ms st) (ret (st, (ms, ms)));

    MemMonad_put_mem_state
      (ms ms' : MemState) st :
    eq1 (MemMonad_run (put_mem_state ms') ms st) (ret (st, (ms', tt)));

    (** Fresh store id property *)
    MemMonad_run_fresh_sid
      (ms : MemState) st (VALID : MemMonad_valid_state ms st):
    exists st' sid',
      eq1 (MemMonad_run (fresh_sid) ms st) (ret (st', (ms, sid'))) /\
        MemMonad_valid_state ms st' /\
        ~ used_store_id_prop ms sid';

    (** Fresh provenance property *)
    (* TODO: unclear if this should exist, must change ms. *)
    MemMonad_run_fresh_provenance
      (ms : MemState) st (VALID : MemMonad_valid_state ms st):
    exists ms' pr',
      eq1 (MemMonad_run (fresh_provenance) ms st) (ret (st, (ms', pr'))) /\
        MemMonad_valid_state ms' st /\
        ms_get_memory ms = ms_get_memory ms' /\
        (* Analogous to extend_provenance *)
        (forall pr, used_provenance_prop ms pr -> used_provenance_prop ms' pr) /\
        ~ used_provenance_prop ms pr' /\
        used_provenance_prop ms' pr';

    (** Exceptions *)
    MemMonad_run_raise_oom :
    forall {A} ms oom_msg st,
      eq1 (MemMonad_run (@raise_oom _ _ A oom_msg) ms st) (raise_oom oom_msg);

    MemMonad_eq1_raise_oom_inv :
    forall {A} x oom_msg,
      ~ ((@eq1 _ MemMonad_eq1_runm) A (ret x) (raise_oom oom_msg));

    MemMonad_run_raise_ub :
    forall {A} ms ub_msg st,
      eq1 (MemMonad_run (@raise_ub _ _ A ub_msg) ms st) (raise_ub ub_msg);

    MemMonad_run_raise_error :
    forall {A} ms error_msg st,
      eq1 (MemMonad_run (@raise_error _ _ A error_msg) ms st) (raise_error error_msg);

    MemMonad_eq1_raise_error_inv :
    forall {A} x error_msg,
      ~ ((@eq1 _ MemMonad_eq1_runm) A (ret x) (raise_error error_msg));
  }.

    (*** Correctness *)
    Definition exec_correct {MemM Eff ExtraState} `{MM: MemMonad ExtraState MemM (itree Eff)} {X} (exec : MemM X) (spec : MemPropT MemState X) : Prop :=
      forall ms st,
        (@MemMonad_valid_state ExtraState MemM (itree Eff) _ _ _ _ _ _ _ _ _ _ _ _ ms st) ->
        let t := MemMonad_run exec ms st in
        let eqi := (@eq1 _ (@MemMonad_eq1_runm _ _ _ _ _ _ _ _ _ _ _ _ _ _ MM)) in
        (* UB *)
        (exists msg_spec,
            spec ms (raise_ub msg_spec)) \/
          (* Error *)
          ((exists msg msg_spec,
               eqi _ t (raise_error msg) ->
               spec ms (raise_error msg_spec))) /\
          (* OOM *)
          (exists msg msg_spec,
              eqi _ t (raise_oom msg) ->
              spec ms (raise_oom msg_spec)) /\
          (* Success *)
          (forall st' ms' x,
              eqi _ t (ret (st', (ms', x))) ->
              spec ms (ret (ms', x))).

    Definition exec_correct_memory {MemM Eff ExtraState} `{MM: MemMonad ExtraState MemM (itree Eff)} {X} (exec : MemM X) (spec : MemPropT memory_stack X) : Prop :=
      exec_correct exec (lift_memory_MemPropT spec).

    Lemma exec_correct_lift_memory :
      forall {MemM Eff ExtraState} `{MemMonad ExtraState MemM (itree Eff)}
        {X} (exec : MemM X)  (spec : MemPropT memory_stack X),
        exec_correct_memory exec spec ->
        exec_correct exec (lift_memory_MemPropT spec).
    Proof.
      intros * EXEC.
      unfold exec_correct_memory in EXEC.
      auto.
    Qed.
End MemoryExecMonad.

Module MakeMemoryExecMonad (LP : LLVMParams) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MMS : MemoryModelSpec LP MP MMSP) <: MemoryExecMonad LP MP MMSP MMS.
  Include MemoryExecMonad LP MP MMSP MMS.
End MakeMemoryExecMonad.

Module Type MemoryModelExecPrimitives (LP : LLVMParams) (MP : MemoryParams LP).
  Import LP.
  Import LP.ADDR.
  Import LP.SIZEOF.
  Import LP.PROV.
  Import MP.

  (** Specification of the memory model *)
  Declare Module MMSP : MemoryModelSpecPrimitives LP MP.
  Import MMSP.
  Import MMSP.MemByte.

  Module MemSpec := MakeMemoryModelSpec LP MP MMSP.
  Import MemSpec.

  Module MemExecM := MakeMemoryExecMonad LP MP MMSP MemSpec.
  Import MemExecM.

  Section MemoryPrimitives.
    Context {MemM : Type -> Type}.
    Context {Eff : Type -> Type}.
    Context {ExtraState : Type}.
    Context `{MM : MemMonad ExtraState MemM (itree Eff)}.

    (*** Data types *)
    Parameter initial_memory_state : MemState.
    Parameter initial_frame : Frame.
    Parameter initial_heap : Heap.

    (*** Primitives on memory *)
    (** Reads *)
    Parameter read_byte :
      forall `{MemMonad ExtraState MemM (itree Eff)}, addr -> MemM SByte.

    (** Writes *)
    Parameter write_byte :
      forall `{MemMonad ExtraState MemM (itree Eff)}, addr -> SByte -> MemM unit.

    (** Stack allocations *)
    Parameter allocate_bytes :
      forall `{MemMonad ExtraState MemM (itree Eff)}, dtyp -> list SByte -> MemM addr.

    (** Frame stacks *)
    Parameter mempush : forall `{MemMonad ExtraState MemM (itree Eff)}, MemM unit.
    Parameter mempop : forall `{MemMonad ExtraState MemM (itree Eff)}, MemM unit.

    (** Heap operations *)
    Parameter malloc_bytes :
      forall `{MemMonad ExtraState MemM (itree Eff)}, list SByte -> MemM addr.

    Parameter free :
      forall `{MemMonad ExtraState MemM (itree Eff)}, addr -> MemM unit.

    (*** Correctness *)

    (** Correctness of the main operations on memory *)
    Parameter read_byte_correct :
      forall ptr, exec_correct (read_byte ptr) (read_byte_spec_MemPropT ptr).

    Parameter write_byte_correct :
      forall ptr byte, exec_correct (write_byte ptr byte) (write_byte_spec_MemPropT ptr byte).

    Parameter allocate_bytes_correct :
      forall dt init_bytes, exec_correct (allocate_bytes dt init_bytes) (allocate_bytes_spec_MemPropT dt init_bytes).

    (** Correctness of frame stack operations *)
    Parameter mempush_correct :
      exec_correct mempush mempush_spec_MemPropT.

    Parameter mempop_correct :
      exec_correct mempop mempop_spec_MemPropT.

    Parameter malloc_bytes_correct :
      forall init_bytes,
        exec_correct (malloc_bytes init_bytes) (malloc_bytes_spec_MemPropT init_bytes).

    Parameter free_correct :
      forall ptr,
        exec_correct (free ptr) (free_spec_MemPropT ptr).

    (*** Initial memory state *)
    Record initial_memory_state_prop : Prop :=
      {
        initial_memory_no_allocations :
        forall ptr aid,
          ~ byte_allocated initial_memory_state ptr aid;

        initial_memory_frame_stack :
        forall fs,
          memory_stack_frame_stack_prop (MemState_get_memory initial_memory_state) fs ->
          empty_frame_stack fs;

        initial_memory_heap :
        forall h,
          memory_stack_heap_prop (MemState_get_memory initial_memory_state) h ->
          empty_heap h;

        initial_memory_read_ub :
        forall ptr byte,
          read_byte_prop initial_memory_state ptr byte
      }.

    Record initial_frame_prop : Prop :=
      {
        initial_frame_is_empty : empty_frame initial_frame;
      }.

    Record initial_heap_prop : Prop :=
      {
        initial_heap_is_empty : empty_heap initial_heap;
      }.

    Parameter initial_memory_state_correct : initial_memory_state_prop.
    Parameter initial_frame_correct : initial_frame_prop.
    Parameter initial_heap_correct : initial_heap_prop.
  End MemoryPrimitives.
End MemoryModelExecPrimitives.

Module Type MemoryModelExec (LP : LLVMParams) (MP : MemoryParams LP) (MMEP : MemoryModelExecPrimitives LP MP).
  Import LP.
  Import LP.ADDR.
  Import LP.SIZEOF.
  Import LP.PROV.
  Import LP.PTOI.
  Import LP.Events.
  Import MP.
  Import MMEP.
  Import MemExecM.
  Import MMSP.
  Import MMSP.MemByte.
  Import MMEP.MemSpec.
  Import MemHelpers.

  Module OVER := PTOIOverlaps ADDR PTOI SIZEOF.
  Import OVER.
  Module OVER_H := OverlapHelpers ADDR SIZEOF OVER.
  Import OVER_H.

  (*** Handling memory events *)
  Section Handlers.
    Context {MemM : Type -> Type}.
    Context {Eff : Type -> Type}.
    Context {ExtraState : Type}.
    Context `{MM : MemMonad ExtraState MemM (itree Eff)}.

    (** Reading uvalues *)
    Definition read_bytes `{MemMonad ExtraState MemM (itree Eff)} (ptr : addr) (len : nat) : MemM (list SByte) :=
      (* TODO: this should maybe be UB and not OOM??? *)
      ptrs <- get_consecutive_ptrs ptr len;;

      (* Actually perform reads *)
      Util.map_monad (fun ptr => read_byte ptr) ptrs.

    Definition read_uvalue `{MemMonad ExtraState MemM (itree Eff)} (dt : dtyp) (ptr : addr) : MemM uvalue :=
      bytes <- read_bytes ptr (N.to_nat (sizeof_dtyp dt));;
      lift_err_RAISE_ERROR (deserialize_sbytes bytes dt).

    (** Writing uvalues *)
    Definition write_bytes `{MemMonad ExtraState MemM (itree Eff)} (ptr : addr) (bytes : list SByte) : MemM unit :=
      (* TODO: Should this be UB instead of OOM? *)
      ptrs <- get_consecutive_ptrs ptr (length bytes);;
      let ptr_bytes := zip ptrs bytes in

      (* Actually perform writes *)
      Util.map_monad_ (fun '(ptr, byte) => write_byte ptr byte) ptr_bytes.

    Definition write_uvalue `{MemMonad ExtraState MemM (itree Eff)} (dt : dtyp) (ptr : addr) (uv : uvalue) : MemM unit :=
      bytes <- serialize_sbytes uv dt;;
      write_bytes ptr bytes.

    (** Allocating dtyps *)
    (* Need to make sure MemPropT has provenance and sids to generate the bytes. *)
    Definition allocate_dtyp `{MemMonad ExtraState MemM (itree Eff)} (dt : dtyp) : MemM addr :=
      sid <- fresh_sid;;
      bytes <- lift_OOM (generate_undef_bytes dt sid);;
      allocate_bytes dt bytes.

    (** Handle memcpy *)
    Definition memcpy `{MemMonad ExtraState MemM (itree Eff)} (src dst : addr) (len : Z) (align : N) (volatile : bool) : MemM unit :=
      if Z.ltb len 0
      then
        raise_ub "memcpy given negative length."
      else
        (* From LangRef: The ‘llvm.memcpy.*’ intrinsics copy a block of
       memory from the source location to the destination location, which
       must either be equal or non-overlapping.
         *)
        if orb (no_overlap dst len src len)
               (Z.eqb (ptr_to_int src) (ptr_to_int dst))
        then
          src_bytes <- read_bytes src (Z.to_nat len);;

          (* TODO: Double check that this is correct... Should we check if all writes are allowed first? *)
          write_bytes dst src_bytes
        else
          raise_ub "memcpy with overlapping or non-equal src and dst memory locations.".

    Definition handle_memory `{MemMonad ExtraState MemM (itree Eff)} : MemoryE ~> MemM
      := fun T m =>
           match m with
           (* Unimplemented *)
           | MemPush =>
               mempush
           | MemPop =>
               mempop
           | Alloca t =>
               addr <- allocate_dtyp t;;
               ret (DVALUE_Addr addr)
           | Load t a =>
               match a with
               | DVALUE_Addr a =>
                   read_uvalue t a
               | _ =>
                   raise_ub "Loading from something that is not an address."
               end
           | Store t a v =>
               match a with
               | DVALUE_Addr a =>
                   write_uvalue t a v
               | _ =>
                   raise_ub "Store to somewhere that is not an address."
               end
           end.

    Definition handle_memcpy `{MemMonad ExtraState MemM (itree Eff)} (args : list dvalue) : MemM unit :=
      match args with
      | DVALUE_Addr dst ::
                    DVALUE_Addr src ::
                    DVALUE_I32 len ::
                    DVALUE_I32 align :: (* alignment ignored *)
                    DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          memcpy src dst (unsigned len) (Z.to_N (unsigned align)) (equ volatile one)
      | DVALUE_Addr dst ::
                    DVALUE_Addr src ::
                    DVALUE_I64 len ::
                    DVALUE_I64 align :: (* alignment ignored *)
                    DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          memcpy src dst (unsigned len) (Z.to_N (unsigned align)) (equ volatile one)
      | DVALUE_Addr dst ::
                    DVALUE_Addr src ::
                    DVALUE_IPTR len ::
                    DVALUE_IPTR align :: (* alignment ignored *)
                    DVALUE_I1 volatile :: [] (* volatile ignored *)  =>
          memcpy src dst (IP.to_Z len) (Z.to_N (IP.to_Z align)) (equ volatile one)
      | _ => raise_error "Unsupported arguments to memcpy."
      end.

    Definition handle_malloc `{MemMonad ExtraState MemM (itree Eff)} (args : list dvalue) : MemM addr :=
      match args with
      | [DVALUE_I1 sz]
      | [DVALUE_I8 sz]
      | [DVALUE_I32 sz]
      | [DVALUE_I64 sz] =>
          sid <- fresh_sid;;
          bytes <- lift_OOM (generate_num_undef_bytes (Z.to_N (unsigned sz)) (DTYPE_I 8) sid);;
          malloc_bytes bytes
      | [DVALUE_IPTR sz] =>
          sid <- fresh_sid;;
          bytes <- lift_OOM (generate_num_undef_bytes (Z.to_N (IP.to_unsigned sz)) (DTYPE_I 8) sid);;
          malloc_bytes bytes
      | _ => raise_error "Malloc: invalid arguments."
      end.

    Definition handle_free `{MemMonad ExtraState MemM (itree Eff)} (args : list dvalue) : MemM unit :=
      match args with
      | [DVALUE_Addr ptr] =>
          free ptr
      | _ => raise_error "Free: invalid arguments."
      end.

    Definition handle_intrinsic `{MemMonad ExtraState MemM (itree Eff)} : IntrinsicE ~> MemM
      := fun T e =>
           match e with
           | Intrinsic t name args =>
               (* Pick all arguments, they should all be unique. *)
               (* TODO: add more variants to memcpy *)
               (* FIXME: use reldec typeclass? *)
               if orb (Coqlib.proj_sumbool (string_dec name "llvm.memcpy.p0i8.p0i8.i32"))
                      (Coqlib.proj_sumbool (string_dec name "llvm.memcpy.p0i8.p0i8.i64"))
               then
                 handle_memcpy args;;
                 ret DVALUE_None
               else
                 if (Coqlib.proj_sumbool (string_dec name "malloc"))
                 then
                   addr <- handle_malloc args;;
                   ret (DVALUE_Addr addr)
                 else
                   if (Coqlib.proj_sumbool (string_dec name "free"))
                   then
                     handle_free args;;
                     ret DVALUE_None
                   else
                     raise_error ("Unknown intrinsic: " ++ name)
           end.

  End Handlers.
End MemoryModelExec.

Module MakeMemoryModelExec (LP : LLVMParams) (MP : MemoryParams LP) (MMEP : MemoryModelExecPrimitives LP MP) <: MemoryModelExec LP MP MMEP.
  Include MemoryModelExec LP MP MMEP.
End MakeMemoryModelExec.

Module MemoryModelTheory (LP : LLVMParams) (MP : MemoryParams LP) (MMEP : MemoryModelExecPrimitives LP MP) (MME : MemoryModelExec LP MP MMEP).
  Import MMEP.
  Import MME.
  Import MemSpec.
  Import MMSP.
  Import MemExecM.
  Import MemHelpers.
  Import LP.Events.

  Section Correctness.
    Context {MemM : Type -> Type}.
    Context {Eff : Type -> Type}.
    Context {ExtraState : Type}.
    Context `{MM : MemMonad ExtraState MemM (itree Eff)}.

    Import Monad.

    Lemma exec_correct_bind :
      forall {A B}
        (m_exec : MemM A) (k_exec : A -> MemM B)
        (m_spec : MemPropT MemState A) (k_spec : A -> MemPropT MemState B),
        exec_correct m_exec m_spec ->
        (forall a, exec_correct (k_exec a) (k_spec a)) ->
        exec_correct (a <- m_exec;; k_exec a) (a <- m_spec;; k_spec a).
    Proof.
      intros A B m_exec k_exec m_spec k_spec HM HK.
      unfold exec_correct in *.
      intros ms st VALID.

      pose proof (HM ms st VALID) as [[ubm UBM] | NUBM].
      { (* m raised UB *)
        left.
        exists ubm.
        repeat eexists; cbn; eauto.
      }

      (* m did not raise UB *)
      destruct NUBM as [ERROR [OOM SUCC]].
      right.

      split; [|split].
      { (* Error *)
        do 2 eexists; intros RUN.

        rewrite MemMonad_run_bind in RUN.
        (* I think I need some kind of inversion lemma about this *)
        (* What about divergence? *)
        (* Oh, it can't diverge because it's eutt error *)
        epose proof MReturns_bind_inv.
        assert (FailureE -< Eff) by admit.
        epose proof (@MFails_bind_inv (itree Eff) _ _ ITreeErrorMonadReturns (ExtraState * (MemState * A)) (ExtraState * (MemState * B)) (MemMonad_run m_exec ms st) (fun x0 => (let (st', y) := x0 in let (ms', x) := y in MemMonad_run (k_exec x) ms' st'))) as FAILINV.

        unfold MFails in FAILINV.
        forward FAILINV.
        admit.

        destruct FAILINV.
        + admit.
        + 

        admit.
      }
      admit.
      admit.
    Admitted.

    Lemma exec_correct_ret :
      forall {X} (x : X),
        exec_correct (ret x) (ret x).
    Proof.
      intros X x.
      cbn; red; cbn.
      intros ms st VALID.
      right.
      setoid_rewrite MemMonad_run_ret.
      split; [|split].
      + (* Error *)
        cbn. repeat eexists.
        exact ""%string.
        intros CONTRA.
        apply MemMonad_eq1_raise_error_inv in CONTRA; auto.
      + (* OOM *)
        cbn. repeat eexists.
        exact ""%string.
        intros CONTRA.
        apply MemMonad_eq1_raise_oom_inv in CONTRA; auto.
      + (* Success *)
        intros st' ms' x' RUN.
        apply eq1_ret_ret in RUN; [|typeclasses eauto].
        inv RUN; cbn; auto.

        Unshelve.
        all: exact ""%string.
    Qed.
        
    Lemma exec_correct_map_monad :
      forall {A B}
        xs
        (m_exec : A -> MemM B) (m_spec : A -> MemPropT MemState B),
        (forall a, exec_correct (m_exec a) (m_spec a)) ->
        exec_correct (map_monad m_exec xs) (map_monad m_spec xs).
    Proof.
      induction xs;
        intros m_exec m_spec HM.

      - unfold map_monad.
        apply exec_correct_ret.
      - rewrite map_monad_unfold.
        rewrite map_monad_unfold.

        eapply exec_correct_bind; eauto.
        intros a0.

        eapply exec_correct_bind; eauto.
        intros a1.

        apply exec_correct_ret.
    Qed.

    Lemma exec_correct_map_monad_ :
      forall {A B}
        (xs : list A)
        (m_exec : A -> MemM B) (m_spec : A -> MemPropT MemState B),
        (forall a, exec_correct (m_exec a) (m_spec a)) ->
        exec_correct (map_monad_ m_exec xs) (map_monad_ m_spec xs).
    Proof.
      intros A B xs m_exec m_spec H.
      apply exec_correct_bind.
      eapply exec_correct_map_monad; auto.
      intros a.
      apply exec_correct_ret.
    Qed.

    Lemma exec_correct_map_monad_In :
      forall {A B}
        (xs : list A)
        (m_exec : forall (x : A), In x xs -> MemM B) (m_spec : forall (x : A), In x xs -> MemPropT MemState B),
      (forall a (IN : In a xs), exec_correct (m_exec a IN) (m_spec a IN)) ->
      exec_correct (map_monad_In xs m_exec) (map_monad_In xs m_spec).
    Proof.
      induction xs; intros m_exec m_spec HM.
      - unfold map_monad_In.
        apply exec_correct_ret.
      - rewrite map_monad_In_unfold.
        rewrite map_monad_In_unfold.

        eapply exec_correct_bind; eauto.
        intros a0.

        eapply exec_correct_bind; eauto.
        intros a1.

        apply exec_correct_ret.
    Qed.

    Lemma exec_correct_raise_oom :
      forall {A} (msg : string),
        exec_correct (raise_oom msg) (raise_oom msg : MemPropT MemState A).
    Proof.
      intros A msg.
      cbn.
      red.
      intros ms st VALID.
      cbn. right.
      split; [|split].
      { (* Error Case *)
        do 2 eexists.
        exact ""%string.
        intros RUN.
        admit. (* Need inversion property. *)
      }
      { (* OOM case *)
        exists msg.
        exists msg.
        intros; auto.
      }
      { (* Success *)
        intros st' ms' x H.
        symmetry in H.
        rewrite MemMonad_run_raise_oom in H.
        apply MemMonad_eq1_raise_oom_inv in H.
        auto.
      }
    Admitted.

    Lemma exec_correct_raise_error :
      forall {A} (msg1 msg2 : string),
        exec_correct (raise_error msg1) (raise_error msg2 : MemPropT MemState A).
    Proof.
      intros A msg1 msg2.
      cbn.
      red.
      intros ms st VALID.
      cbn. right.
      split; [|split].
      { (* Error Case *)
        exists msg1.
        exists msg2.
        intros; auto.
      }
      { (* OOM case *)
        do 2 eexists.
        exact ""%string.
        intros RUN.
        rewrite MemMonad_run_raise_error in RUN.
        admit. (* Need inversion property. *)
      }
      { (* Success *)
        intros st' ms' x H.
        symmetry in H.
        rewrite MemMonad_run_raise_error in H.
        apply MemMonad_eq1_raise_error_inv in H.
        auto.
      }
    Admitted.

    Lemma exec_correct_raise_ub :
      forall {A} (msg1 msg2 : string),
        exec_correct (raise_ub msg1) (raise_ub msg2 : MemPropT MemState A).
    Proof.
      intros A msg.
      cbn.
      red.
      intros ms st VALID.
      cbn.
      left.
      exists ""%string.
      auto.
    Qed.
      
    Lemma exec_correct_lift_OOM :
      forall {A} (m : OOM A),
        exec_correct (lift_OOM m) (lift_OOM m).
    Proof.
      intros A [NOOM | OOM].
      - apply exec_correct_ret.
      - apply exec_correct_raise_oom.
    Qed.

    Lemma exec_correct_lift_err_RAISE_ERROR :
      forall {A} (m : err A),
        exec_correct (lift_err_RAISE_ERROR m) (lift_err_RAISE_ERROR m).
    Proof.
      intros A [ERR | NOERR].
      - apply exec_correct_raise_error.
      - apply exec_correct_ret.
    Qed.

    Lemma exec_correct_lift_ERR_RAISE_ERROR :
      forall {A} (m : ERR A),
        exec_correct (lift_ERR_RAISE_ERROR m) (lift_ERR_RAISE_ERROR m).
    Proof.
      intros A [[ERR] | NOERR].
      - apply exec_correct_raise_error.
      - apply exec_correct_ret.
    Qed.

    Lemma exec_correct_get_consecutive_pointers :
      forall len ptr,
        exec_correct (get_consecutive_ptrs ptr len) (get_consecutive_ptrs ptr len).
    Proof.
      intros len ptr.
      unfold get_consecutive_ptrs.
      eapply exec_correct_bind.
      apply exec_correct_lift_OOM.

      intros a.
      apply exec_correct_lift_err_RAISE_ERROR.
    Qed.

    Lemma exec_correct_fresh_sid :
      exec_correct fresh_sid fresh_sid.
    Proof.
      red.
      intros ms st H.
      right.
      eapply MemMonad_run_fresh_sid in H as [st' [sid [EUTT [VALID FRESH]]]].
      split; [| split].
      { do 2 eexists.
        intros ERR.
        exfalso.
        rewrite EUTT in ERR.
        apply MemMonad_eq1_raise_error_inv in ERR; auto.
      }
      { do 2 eexists.
        intros OOM.
        exfalso.
        rewrite EUTT in OOM.
        apply MemMonad_eq1_raise_oom_inv in OOM; auto.
      }
      { intros st'0 ms' x H.
        rewrite EUTT in H.
        apply eq1_ret_ret in H; try typeclasses eauto.
        inv H.
        cbn.
        split; [| split; [| split; [| split; [| split; [| split]]]]];
          try solve [red; reflexivity].
        - unfold fresh_store_id. auto.
        - unfold read_byte_preserved.
          split; red; reflexivity.
      }
      Unshelve.
      all: exact ""%string.
    Qed.

    (* TODO: move this? *)
    Lemma byte_allocated_mem_eq :
      forall ms ms' ptr aid,
        byte_allocated ms ptr aid ->
        MemState_get_memory ms = MemState_get_memory ms' ->
        byte_allocated ms' ptr aid.
    Proof.
      intros ms ms' ptr aid ALLOC EQ.
      unfold byte_allocated, byte_allocated_MemPropT in *.
      cbn in *.
      unfold lift_memory_MemPropT in *.
      cbn in *.
      destruct ALLOC as [sab [ab [[ALLOC PROV] [EQ1 EQ2]]]].
      subst.
      repeat eexists.
      rewrite <- EQ.
      auto.
      intros ms'0 x EQ'; inv EQ'.
      reflexivity.
    Qed.

    (* TODO: move this? *)
    Lemma read_byte_allowed_mem_eq :
      forall ms ms' ptr,
        read_byte_allowed ms ptr ->
        MemState_get_memory ms = MemState_get_memory ms' ->
        read_byte_allowed ms' ptr.
    Proof.
      intros ms ms' ptr READ EQ.
      unfold read_byte_allowed in *.
      destruct READ as [aid [ALLOC ACCESS]].
      exists aid; split; auto.
      eapply byte_allocated_mem_eq; eauto.
    Qed.

    Lemma write_byte_allowed_mem_eq :
      forall ms ms' ptr,
        write_byte_allowed ms ptr ->
        MemState_get_memory ms = MemState_get_memory ms' ->
        write_byte_allowed ms' ptr.
    Proof.
      intros ms ms' ptr WRITE EQ.
      unfold write_byte_allowed in *.
      destruct WRITE as [aid [ALLOC ACCESS]].
      exists aid; split; auto.
      eapply byte_allocated_mem_eq; eauto.
    Qed.

    (* TODO: move this? *)
    Lemma read_byte_prop_mem_eq :
      forall ms ms' ptr byte,
        read_byte_prop ms ptr byte ->
        MemState_get_memory ms = MemState_get_memory ms' ->
        read_byte_prop ms' ptr byte.
    Proof.
      intros ms ms' ptr byte READ EQ.
      unfold read_byte_prop.
      rewrite <- EQ.
      auto.
    Qed.

    Lemma read_byte_preserved_mem_eq :
      forall ms ms',
        MemState_get_memory ms = MemState_get_memory ms' ->
        read_byte_preserved ms ms'.
    Proof.
      unfold read_byte_preserved.
      split; red.
      + intros ptr; split; intros READ_ALLOWED;
          eapply read_byte_allowed_mem_eq; eauto.
      + intros ptr byte; split; intros READ_ALLOWED;
          eapply read_byte_prop_mem_eq; eauto.
    Qed.

    Lemma write_byte_allowed_all_preserved_mem_eq :
      forall ms ms',
        MemState_get_memory ms = MemState_get_memory ms' ->
        write_byte_allowed_all_preserved ms ms'.
    Proof.
      intros ms ms' EQ.
      unfold write_byte_allowed_all_preserved.
      intros ptr.
      split; red;
        intros WRITE_ALLOWED;
        eapply write_byte_allowed_mem_eq; eauto.
    Qed.

    Lemma allocations_preserved_mem_eq :
      forall ms ms',
        MemState_get_memory ms = MemState_get_memory ms' ->
        allocations_preserved ms ms'.
    Proof.
      intros ms ms' EQ.
      unfold write_byte_allowed_all_preserved.
      intros ptr aid.
      split; intros ALLOC; eapply byte_allocated_mem_eq; eauto.
    Qed.

    Lemma frame_stack_preserved_mem_eq :
      forall ms ms',
        MemState_get_memory ms = MemState_get_memory ms' ->
        frame_stack_preserved ms ms'.
    Proof.
      intros ms ms' EQ.
      unfold frame_stack_preserved.
      intros fs.
      split; intros FS; [rewrite <- EQ | rewrite EQ]; eauto.
    Qed.

    Lemma exec_correct_fresh_provenance :
      exec_correct fresh_provenance fresh_provenance.
    Proof.
      red.
      intros ms st H.
      right.
      eapply MemMonad_run_fresh_provenance in H as [st' [sid [EUTT [VALID [MEM FRESH]]]]].
      split; [| split].
      { do 2 eexists.
        intros ERR.
        exfalso.
        rewrite EUTT in ERR.
        apply MemMonad_eq1_raise_error_inv in ERR; auto.
      }
      { do 2 eexists.
        intros OOM.
        exfalso.
        rewrite EUTT in OOM.
        apply MemMonad_eq1_raise_oom_inv in OOM; auto.
      }
      { intros st'0 ms' x H.
        rewrite EUTT in H.
        apply eq1_ret_ret in H; try typeclasses eauto.
        inv H.
        cbn.
        split; [| split; [| split; [| split; [| split; [| split]]]]];
          try solve [red; reflexivity].
        - unfold extend_provenance. tauto.
        - eapply read_byte_preserved_mem_eq; eauto.
        - eapply write_byte_allowed_all_preserved_mem_eq; eauto.
        - eapply allocations_preserved_mem_eq; eauto.
        - eapply frame_stack_preserved_mem_eq; eauto.
        - unfold ms_get_memory in MEM; cbn in MEM. rewrite MEM.
          auto.
        - unfold ms_get_memory in MEM; cbn in MEM. rewrite MEM.
          auto.
      }
      Unshelve.
      all: exact ""%string.
    Qed.

    Hint Resolve exec_correct_ret : EXEC_CORRECT.
    Hint Resolve exec_correct_bind : EXEC_CORRECT.
    Hint Resolve exec_correct_fresh_sid : EXEC_CORRECT.
    Hint Resolve exec_correct_lift_err_RAISE_ERROR : EXEC_CORRECT.
    Hint Resolve exec_correct_lift_ERR_RAISE_ERROR : EXEC_CORRECT.
    Hint Resolve exec_correct_lift_OOM : EXEC_CORRECT.
    Hint Resolve exec_correct_raise_error : EXEC_CORRECT.
    Hint Resolve exec_correct_raise_oom : EXEC_CORRECT.
    Hint Resolve exec_correct_raise_ub : EXEC_CORRECT.
    Hint Resolve exec_correct_map_monad : EXEC_CORRECT.
    Hint Resolve exec_correct_map_monad_ : EXEC_CORRECT.
    Hint Resolve exec_correct_map_monad_In : EXEC_CORRECT.
    Hint Resolve malloc_bytes_correct : EXEC_CORRECT.

    (* TODO: move this *)
    Lemma zip_cons :
      forall {A B} (x : A) (y : B) xs ys,
        zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys.
    Proof.
      reflexivity.
    Qed.
        
    Lemma exec_correct_re_sid_ubytes_helper :
      forall bytes,
        exec_correct
          (re_sid_ubytes_helper bytes (NM.empty MP.BYTE_IMPL.SByte))
          (re_sid_ubytes_helper bytes (NM.empty MP.BYTE_IMPL.SByte)).
    Proof.
      induction bytes.
      - apply exec_correct_ret.
      - repeat rewrite re_sid_ubytes_helper_equation.
        break_match; auto with EXEC_CORRECT.
        break_match; auto with EXEC_CORRECT.
        break_match; auto with EXEC_CORRECT.
        apply exec_correct_bind; auto with EXEC_CORRECT.
        intros a0.
        (* Fiddly reasoning because it's not structural... we update
           all of the sids that match the current one at once, and
           then recursively call the function on the unmatched
           bytes...
        *)
    Admitted.

    Hint Resolve exec_correct_re_sid_ubytes_helper : EXEC_CORRECT.

    Lemma exec_correct_trywith_error :
      forall {A} msg1 msg2 (ma : option A),
        exec_correct
          (trywith_error msg1 ma)
          (trywith_error msg2 ma).
    Proof.
      intros A msg1 msg2 [a |];
        unfold trywith_error;
        auto with EXEC_CORRECT.
    Qed.

    Hint Resolve exec_correct_trywith_error : EXEC_CORRECT.

    Lemma exec_correct_re_sid_ubytes :
      forall bytes,
        exec_correct (re_sid_ubytes bytes) (re_sid_ubytes bytes).
    Proof.
      intros bytes.
      apply exec_correct_bind; auto with EXEC_CORRECT.
    Qed.
    
    Hint Resolve exec_correct_re_sid_ubytes : EXEC_CORRECT.

    Lemma exec_correct_serialize_sbytes :
      forall uv dt,
        exec_correct (serialize_sbytes uv dt) (serialize_sbytes uv dt).
    Proof.
      induction uv using uvalue_ind''; intros dt';
        do 2 rewrite serialize_sbytes_equation;
        auto with EXEC_CORRECT.

      (* - (* Undef *) *)
      (*   break_match; auto with EXEC_CORRECT. *)
      (*   { apply exec_correct_bind; auto with EXEC_CORRECT. *)
      (*     apply exec_correct_map_monad_In. *)
      (*     intros a IN. *)
      (*     apply In_repeatN in IN; subst. *)
      (*     admit. *)
      (*   } *)
      (*   admit. *)
      (* - (* Poison *) *)
      (*   admit. *)
      (* - (* Structs *) *)
      (*   break_match; auto with EXEC_CORRECT. *)
      (*   break_match; auto with EXEC_CORRECT. *)
      (* - (* Packed structs *) *)
      (*   break_match; auto with EXEC_CORRECT. *)
      (*   break_match; auto with EXEC_CORRECT. *)
      (* - (* Arrays *) *)
      (*   break_match; auto with EXEC_CORRECT. *)
      (* - (* Vectors *) *)
      (*   break_match; auto with EXEC_CORRECT. *)
    Admitted.

    Lemma read_bytes_correct :
      forall len ptr,
        exec_correct (read_bytes ptr len) (read_bytes_spec ptr len).
    Proof.
      unfold read_bytes.
      unfold read_bytes_spec.
      intros len ptr.
      eapply exec_correct_bind.
      apply exec_correct_get_consecutive_pointers.

      intros a.
      eapply exec_correct_map_monad.
      intros ptr'.
      apply read_byte_correct.
    Qed.


    Lemma read_uvalue_correct :
      forall dt ptr,
        exec_correct (read_uvalue dt ptr) (read_uvalue_spec dt ptr).
    Proof.
      intros dt ptr.
      eapply exec_correct_bind.
      apply read_bytes_correct.
      intros a.
      apply exec_correct_lift_err_RAISE_ERROR.
    Qed.

    Lemma write_bytes_correct :
      forall ptr bytes,
        exec_correct (write_bytes ptr bytes) (write_bytes_spec ptr bytes).
    Proof.
      intros ptr bytes.
      apply exec_correct_bind.
      apply exec_correct_get_consecutive_pointers.
      intros a.
      apply exec_correct_map_monad_.
      intros [a' b].
      apply write_byte_correct.
    Qed.

    Lemma write_uvalue_correct :
      forall dt ptr uv,
        exec_correct (write_uvalue dt ptr uv) (write_uvalue_spec dt ptr uv).
    Proof.
      intros dt ptr uv.
      apply exec_correct_bind.
      apply exec_correct_serialize_sbytes.
      intros a.
      apply write_bytes_correct.
    Qed.

    Lemma allocate_dtyp_correct :
      forall dt,
        exec_correct (allocate_dtyp dt) (allocate_dtyp_spec dt).
    Proof.
      intros dt.
      apply exec_correct_bind.
      apply exec_correct_fresh_sid.
      intros a.
      apply exec_correct_bind.
      apply exec_correct_lift_OOM.
      intros a0.
      apply allocate_bytes_correct.
    Qed.

    Lemma memcpy_correct :
      forall src dst len align volatile,
        exec_correct (memcpy src dst len align volatile) (memcpy_spec src dst len align volatile).
    Proof.
      intros src dst len align volatile.
      unfold memcpy, memcpy_spec.
      break_match; [apply exec_correct_raise_ub|].
      unfold MME.OVER_H.no_overlap, MME.OVER.overlaps.
      unfold OVER_H.no_overlap, OVER.overlaps.
      break_match; [|apply exec_correct_raise_ub].

      apply exec_correct_bind.
      apply read_bytes_correct.
      intros a.
      apply write_bytes_correct.
    Qed.

    Lemma handle_memory_correct :
      forall T (m : MemoryE T),
        exec_correct (handle_memory T m) (handle_memory_prop T m).
    Proof.
      intros T m.
      destruct m.
      - (* MemPush *)
        cbn.
        apply mempush_correct.
      - (* MemPop *)
        cbn.
        apply mempop_correct.
      - (* Alloca *)
        unfold handle_memory.
        unfold handle_memory_prop.
        apply exec_correct_bind.
        apply allocate_dtyp_correct.
        intros a.
        apply exec_correct_ret.
      - (* Load *)
        unfold handle_memory, handle_memory_prop.
        destruct a; try apply exec_correct_raise_ub.
        apply read_uvalue_correct.
      - (* Store *)
        unfold handle_memory, handle_memory_prop.
        destruct a; try apply exec_correct_raise_ub.
        apply write_uvalue_correct.
    Qed.

    Lemma handle_memcpy_correct:
      forall args,
        exec_correct (handle_memcpy args) (handle_memcpy_prop args).
    Proof.
      intros args.
      unfold handle_memcpy, handle_memcpy_prop.
      repeat (break_match; try apply exec_correct_raise_error).
      all: apply memcpy_correct.
    Qed.

    Lemma handle_malloc_correct:
      forall args,
        exec_correct (handle_malloc args) (handle_malloc_prop args).
    Proof.
      intros args.
      unfold handle_malloc, handle_malloc_prop.
      repeat (break_match; try apply exec_correct_raise_error).
      all: eauto with EXEC_CORRECT.
    Qed.

    Lemma handle_free_correct:
      forall args,
        exec_correct (handle_free args) (handle_free_prop args).
    Proof.
      intros args.
      unfold handle_free, handle_free_prop.
      repeat (break_match; try apply exec_correct_raise_error).
      all: apply free_correct.
    Qed.

    Lemma handle_intrinsic_correct:
      forall T (e : IntrinsicE T),
        exec_correct (handle_intrinsic T e) (handle_intrinsic_prop T e).
    Proof.
      intros T e.
      unfold handle_intrinsic, handle_intrinsic_prop.
      break_match.
      break_match.
      { (* Memcpy *)
        apply exec_correct_bind.
        apply handle_memcpy_correct.
        intros a.
        apply exec_correct_ret.
      }

      break_match.
      { (* Malloc *)
        apply exec_correct_bind.
        apply handle_malloc_correct.
        eauto with EXEC_CORRECT.
      }

      break_match.
      { (* Free *)
        apply exec_correct_bind.
        apply handle_free_correct.
        eauto with EXEC_CORRECT.
      }

      apply exec_correct_raise_error.
    Qed.
  End Correctness.
End MemoryModelTheory.

Module MemStateInfiniteHelpers (LP : LLVMParamsBig) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MMS : MemoryModelSpec LP MP MMSP).
  (* Intptrs are "big" *)
  Import LP.Events.
  Import LP.ITOP.
  Import LP.PTOI.
  Import LP.IP_BIG.
  Import LP.IP.
  Import LP.ADDR.
  Import LP.PROV.
  Import LP.SIZEOF.

  Import MMSP.
  Import MMS.
  Import MemHelpers.

  Import Monad.
  Import MapMonadExtra.
  Import MP.GEP.
  Import MP.BYTE_IMPL.

  Import Util.

  (*
    Things that must succeed:

    - get_consecutive_ptrs: May need something in GepM for this.
    - byte_allocated: for all of the consecutive pointers

   *)

  (* TODO: Move to something like IP_BIG? *)
  Lemma big_intptr_seq_succeeds :
    forall start len,
    exists ips, intptr_seq start len = NoOom ips.
  Proof.
    intros start len.
    unfold intptr_seq.
    induction (Zseq start len).
    - cbn. exists []. reflexivity.
    - rewrite map_monad_unfold.
      cbn.
      break_match.
      2: {
        pose proof (from_Z_safe a) as CONTRA.
        rewrite Heqo in CONTRA.
        contradiction.
      }

      destruct IHl as (ips & IHl).
      exists (i :: ips).
      Require Import FunctionalExtensionality.
      setoid_rewrite functional_extensionality.
      rewrite IHl.
      reflexivity.
      reflexivity.
  Qed.

  #[global] Instance lift_err_RAISE_ERROR_Proper {A M} `{HM: Monad M} `{RAISE: RAISE_ERROR M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM} :
    Proper (eq ==> eq1) (@lift_err_RAISE_ERROR A M HM RAISE).
  Proof.
    unfold Proper, respectful.
    intros x y H; subst.
    reflexivity.
  Defined.

  Lemma get_consecutive_ptrs_succeeds :
    forall {M : Type -> Type}
      `{HM: Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM}
      `{EQRET : @Eq1_ret_inv M EQM HM}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{LAWS: @MonadLawsE M EQM HM}
      ptr len,
    exists ptrs, (get_consecutive_ptrs ptr len ≈ ret ptrs)%monad.
  Proof.
    intros M HM EQM EQV EQRET OOM ERR LAWS ptr len.

    unfold get_consecutive_ptrs.
    pose proof big_intptr_seq_succeeds 0 len as (ips & SEQ).
    rewrite SEQ.
    cbn.

    pose proof map_monad_err_succeeds
         (fun ix : intptr =>
            handle_gep_addr (DTYPE_I 8) ptr [LP.Events.DV.DVALUE_IPTR ix])
         ips as HMAPM.

    forward HMAPM.
    { intros a IN.
      eexists.
      eapply handle_gep_addr_ix'.
      reflexivity.
    }

    destruct HMAPM as (res & HMAPM).
    exists res.
    rewrite bind_ret_l.
    rewrite HMAPM.
    cbn.
    reflexivity.
  Qed.

  (* TODO: this can probably more somewhere else *)
  Lemma get_consecutive_ptrs_cons :
    forall {M : Type -> Type}
      `{HM: Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM}
      `{EQRET : @Eq1_ret_inv M EQM HM}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{LAWS: @MonadLawsE M EQM HM}
      ptr len p ptrs,
      (get_consecutive_ptrs ptr len ≈ ret (p :: ptrs))%monad ->
      p = ptr /\ (exists ptr' len', len = S len' /\ (get_consecutive_ptrs ptr' len' ≈ ret ptrs)%monad).
  Proof.
    intros M HM EQM EQRET EQV OOM ERR LAWS ptr len p ptrs CONSEC.

    unfold get_consecutive_ptrs in *.
    pose proof big_intptr_seq_succeeds 0 len as (ips & SEQ).
    rewrite SEQ in *.
    cbn in *.

    rewrite bind_ret_l in CONSEC.
    generalize dependent len.
    induction len; intros SEQ.
    - cbn in SEQ.
      inv SEQ.
      cbn in CONSEC.
      eapply eq1_ret_ret in CONSEC; [|typeclasses eauto].
      inv CONSEC.
    - clear IHlen.

      cbn in *.
      rewrite from_Z_0 in *.
      break_match_hyp; inv SEQ.

      cbn in *.
      rewrite handle_gep_addr_0 in *.

      break_match_hyp.
      (* TODO: Need some kind of inversion lemma for raise_error and ret *)
      cbn in *.
      admit.

      cbn in *.
      eapply eq1_ret_ret in CONSEC; [|typeclasses eauto].
      inv CONSEC.

      split; auto.
      destruct (from_Z 1) as [ix_one | ix_one] eqn:ONE.
      2: {
        pose proof from_Z_safe 1 as CONTRA.
        rewrite ONE in CONTRA.
        contradiction.
      }

      destruct (handle_gep_addr (DTYPE_I 8) p [LP.Events.DV.DVALUE_IPTR ix_one]) as [ptr_one | ptr_one] eqn:PTRONE.
      { erewrite handle_gep_addr_ix' in PTRONE.
        inv PTRONE.
        reflexivity.
      }

      induction len.
  Admitted.

  (* TODO: this can probably more somewhere else *)
  Lemma get_consecutive_ptrs_ge :
    forall {M : Type -> Type}
      `{HM: Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM}
      `{EQRET : @Eq1_ret_inv M EQM HM}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{LAWS: @MonadLawsE M EQM HM}
      ptr len ptrs,
      (get_consecutive_ptrs ptr len ≈ ret ptrs)%monad ->
      (forall p,
          In p ptrs ->
          (ptr_to_int ptr <= ptr_to_int p)%Z).
  Proof.
    intros M HM EQM EQV EQRET OOM ERR LAWS ptr len ptrs.
    revert ptr len.
    induction ptrs; intros ptr len CONSEC p IN.
    - inv IN.
    - destruct IN as [IN | IN].
      + subst.
        apply get_consecutive_ptrs_cons in CONSEC as (START & CONSEC).
        subst.
        lia.
      + pose proof CONSEC as CONSEC'.
        apply get_consecutive_ptrs_cons in CONSEC as (START & ptr' & len' & LENEQ & CONSEC).
        subst.
        pose proof IHptrs as IHptrs'.
        specialize (IHptrs' _ _ CONSEC _ IN).

        (* `ptr'` is in `ptrs`, and everything in `ptrs >= ptr'`

           So, I know `ptr' <= p`

           I should know that `ptr < ptr'`...
         *)

        (* Could take get_consecutive_ptrs in CONSEC and CONSEC' and compare...

           What if ptrs = [ ]?

           I.e., len = 1... Then ptrs is nil and IN is a contradiction.
        *)

        destruct ptrs as [| ptr'0 ptrs].
        inv IN.

        (* Need to show that ptr'0 = ptr' *)
        pose proof CONSEC as CONSEC''.
        apply get_consecutive_ptrs_cons in CONSEC as (ptreq & ptr'' & len'' & LENEQ & CONSEC).
        subst.

        assert (ptr_to_int ptr < ptr_to_int ptr')%Z by admit.
        lia.
  Admitted.

  (* TODO: can probably move out of infinite stuff *)
  Lemma get_consecutive_ptrs_range :
    forall {M : Type -> Type}
      `{HM: Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM}
      `{EQRET : @Eq1_ret_inv M EQM HM}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{LAWS: @MonadLawsE M EQM HM}
      ptr len ptrs,
      (get_consecutive_ptrs ptr len ≈ ret ptrs)%monad ->
      (forall p,
          In p ptrs ->
          (ptr_to_int ptr <= ptr_to_int p < ptr_to_int ptr + (Z.of_nat len))%Z).
  Proof.
    intros M HM EQM EQV EQRET OOM ERR LAWS ptr len ptrs.
    revert ptr len.
    induction ptrs; intros ptr len CONSEC p IN.
    - inv IN.
    - induction IN as [IN | IN].
      + subst.
        apply get_consecutive_ptrs_cons in CONSEC as (START & ptr' & len' & LENEQ & CONSEC).
        subst.
        lia.
      + pose proof CONSEC as CONSEC'.
        apply get_consecutive_ptrs_cons in CONSEC as (START & ptr' & len' & LENEQ & CONSEC).
        subst.
        pose proof IHptrs as IHptrs'.
        specialize (IHptrs' _ _ CONSEC _ IN).

        (* `ptr'` is in `ptrs`, and everything in `ptrs >= ptr'`

           So, I know `ptr' <= p`

           I should know that `ptr < ptr'`...
         *)

        (* Could take get_consecutive_ptrs in CONSEC and CONSEC' and compare...

           What if ptrs = [ ]?

           I.e., len = 1... Then ptrs is nil and IN is a contradiction.
        *)

        destruct ptrs as [| ptr'0 ptrs].
        inv IN.

        (* Need to show that ptr'0 = ptr' *)
        pose proof CONSEC as CONSEC''.
        apply get_consecutive_ptrs_cons in CONSEC as (ptreq & ptr'' & len'' & LENEQ & CONSEC).
        subst.

        assert (Z.succ (ptr_to_int ptr) = ptr_to_int ptr')%Z.
        { unfold get_consecutive_ptrs in CONSEC'.
          cbn in CONSEC'.
          break_match_hyp.
          2: { cbn in CONSEC'. rewrite rbm_raise_bind in CONSEC'.
               (* TODO: inversion lemma *)
               admit.
               admit.
          }

          break_match_hyp.
          2: { cbn in CONSEC'. rewrite rbm_raise_bind in CONSEC'.
               (* TODO: inversion lemma *)
               admit.
               admit.
          }

          cbn in CONSEC'.
          rewrite bind_ret_l in CONSEC'.
          destruct (map_monad (fun ix : intptr => handle_gep_addr (DTYPE_I 8) ptr [DVALUE_IPTR ix])
                              (i :: l)) eqn:HMAPM.
          { cbn in CONSEC'.
            (* TODO: inversion lemma *)
            admit.
          }

          cbn in CONSEC'.
          apply eq1_ret_ret in CONSEC'; eauto.
          inv CONSEC'.
          apply map_monad_err_In with (x := ptr') in HMAPM; [| intuition].

          admit.
        }
        lia.        
  Admitted.

  Lemma get_consecutive_ptrs_nth :
    forall {M : Type -> Type}
      `{HM: Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM}
      `{EQRET : @Eq1_ret_inv M EQM HM}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{LAWS: @MonadLawsE M EQM HM}
      ptr len ptrs,
      (get_consecutive_ptrs ptr len ≈ ret ptrs)%monad ->
      (forall p ix_nat,
          Nth ptrs ix_nat p ->
          exists ix,
            NoOom ix = from_Z (Z.of_nat ix_nat) /\
            handle_gep_addr (DTYPE_I 8) ptr [DVALUE_IPTR ix] = inr p).
  Proof.
    intros M HM EQM EQV EQRET OOM ERR LAWS ptr len ptrs CONSEC p ix_nat NTH.
    pose proof from_Z_safe (Z.of_nat ix_nat) as IX.
    break_match_hyp; inv IX.
    rename i into ix.
    exists ix.
    split; auto.

    pose proof big_intptr_seq_succeeds 0 len as (ixs & SEQ).
    unfold get_consecutive_ptrs in *.
    rewrite SEQ in CONSEC.
    cbn in CONSEC.
    rewrite bind_ret_l in CONSEC.
    cbn in CONSEC.
    cbn in *.

    pose proof
         (map_monad_err_Nth
            (fun ix : intptr => handle_gep_addr (DTYPE_I 8) ptr [DVALUE_IPTR ix])
            ixs
            ptrs
            p
            ix_nat
         ) as MAPNTH.

    forward MAPNTH.
    { destruct (map_monad (fun ix : intptr => handle_gep_addr (DTYPE_I 8) ptr [DVALUE_IPTR ix]) ixs).
      cbn in CONSEC.
      (* TODO: Need raise_error inversion lemma *)
      admit.
      cbn in CONSEC.
      eapply eq1_ret_ret in CONSEC; try typeclasses eauto.
      subst; auto.
    }

    specialize (MAPNTH NTH).
    destruct MAPNTH as (ix' & GEP & NTH').
    cbn in GEP.

    eapply intptr_seq_nth in SEQ; eauto.
    assert (ix = ix').
    { cbn in SEQ.
      rewrite Heqo in SEQ.
      inv SEQ.
      auto.
    }

    subst; auto.
  Admitted.

  Lemma get_consecutive_ptrs_prov :
    forall {M : Type -> Type}
      `{HM: Monad M} `{EQM : Eq1 M} `{EQV : @Eq1Equivalence M HM EQM}
      `{EQRET : @Eq1_ret_inv M EQM HM}
      `{OOM: RAISE_OOM M} `{ERR: RAISE_ERROR M}
      `{LAWS: @MonadLawsE M EQM HM}
      ptr len ptrs,
      (get_consecutive_ptrs ptr len ≈ ret ptrs)%monad ->
      forall p, In p ptrs -> address_provenance p = address_provenance ptr.
  Proof.
    intros M HM EQM EQV EQRET OOM ERR LAWS ptr len ptrs CONSEC p IN.

    apply In_nth_error in IN as (ix_nat & NTH).
    pose proof CONSEC as GEP.
    eapply get_consecutive_ptrs_nth in GEP; eauto.
    destruct GEP as (ix & IX & GEP).

    apply handle_gep_addr_preserves_provenance in GEP.
    auto.
  Qed.

End MemStateInfiniteHelpers.

Module Type MemoryModelInfiniteSpec (LP : LLVMParamsBig) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MMS : MemoryModelSpec LP MP MMSP).
  (* Intptrs are "big" *)
  Import LP.Events.
  Import LP.ITOP.
  Import LP.PTOI.
  Import LP.IP_BIG.
  Import LP.IP.
  Import LP.ADDR.
  Import LP.PROV.
  Import LP.SIZEOF.

  Import MMSP.
  Import MMS.
  Import MemHelpers.

  Import Monad.
  Import MapMonadExtra.
  Import MP.GEP.
  Import MP.BYTE_IMPL.

  Parameter allocate_can_always_succeed :
    forall (ms_init ms_fresh_pr : MemState) (t : dtyp) (init_bytes : list SByte) (pr : Provenance)
      (FRESH_PR : (fresh_provenance ms_init (ret (ms_fresh_pr, pr))))
      (BYTES_SIZE : sizeof_dtyp t = N.of_nat (length init_bytes))
      (NON_VOID : t <> DTYPE_Void),
    exists ms_final ptr ptrs,
      allocate_bytes_succeeds_spec ms_fresh_pr t init_bytes pr ms_final ptr ptrs.

End MemoryModelInfiniteSpec.

Module MemoryModelInfiniteSpecHelpers (LP : LLVMParamsBig) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MMS : MemoryModelSpec LP MP MMSP) (MMIS : MemoryModelInfiniteSpec LP MP MMSP MMS).
  Import LP.Events.
  Import LP.ITOP.
  Import LP.PTOI.
  Import LP.IP_BIG.
  Import LP.IP.
  Import LP.ADDR.
  Import LP.PROV.
  Import LP.SIZEOF.

  Import MMSP.
  Import MMS.
  Import MemHelpers.

  Import Monad.
  Import MapMonadExtra.
  Import MP.GEP.
  Import MP.BYTE_IMPL.

  Import MMIS.
  
  Lemma allocate_bytes_spec_MemPropT_can_always_succeed :
    forall (ms_init ms_fresh_pr : MemState)
      dt bytes
      (pr : Provenance)
      (FRESH_PR : (fresh_provenance ms_init (ret (ms_fresh_pr, pr))))
      (BYTES_SIZE : sizeof_dtyp dt = N.of_nat (length bytes))
      (NON_VOID : dt <> DTYPE_Void),
    exists ms_final ptr,
      allocate_bytes_spec_MemPropT dt bytes ms_init (ret (ms_final, ptr)).
  Proof.
    intros ms_init ms_fresh_pr dt bytes pr FRESH_PR BYTES_SIZE NON_VOID.
    unfold allocate_bytes_spec_MemPropT, allocate_bytes_spec_MemPropT'.

    pose proof allocate_can_always_succeed
         ms_init ms_fresh_pr dt bytes pr FRESH_PR BYTES_SIZE NON_VOID
      as (ms_final & ptr & ptrs & ALLOC_SUCCESS).

    exists ms_final, ptr.

    (* Fresh provenance *)
    cbn.
    exists ms_fresh_pr. exists pr.
    split; auto.

    exists ms_final, (ptr, ptrs).
    tauto.
  Qed.

  (* TODO: should this be here? *)
  Lemma generate_num_undef_bytes_succeeds :
    forall dt sid,
    exists bytes : list SByte, generate_num_undef_bytes (sizeof_dtyp dt) dt sid = ret bytes.
  Proof.
    intros dt sid.
    eexists. (* Going to need to fill this in manually. *)

    induction (sizeof_dtyp dt) using N.peano_ind.
    - cbn.
      admit.
    - unfold generate_num_undef_bytes in *.
      match goal with
      | H: _ |- N.recursion ?a ?f  _ _ = ret _ =>
          pose proof
               (@N.recursion_succ (N -> OOM (list SByte)) eq
                                  a
                                  f
               )
      end.

      forward H.
      reflexivity.
      forward H.
      { unfold Proper, respectful.
        intros x y H0 x0 y0 H1; subst.
        reflexivity.
      }

      specialize (H n).
      rewrite H.
  Admitted.

  (* TODO: should this be here? *)
  Lemma generate_undef_bytes_succeeds :
    forall dt sid,
    exists bytes, generate_undef_bytes dt sid = ret bytes.
  Proof.
    intros dt sid.
    unfold generate_undef_bytes.
    apply generate_num_undef_bytes_succeeds.
  Qed.

  (* TODO: Move this *)
  Lemma generate_undef_bytes_length :
    forall dt sid bytes,
      generate_undef_bytes dt sid = ret bytes ->
      sizeof_dtyp dt = N.of_nat (length bytes).
  Proof.
  Admitted.

  Lemma allocate_dtyp_spec_can_always_succeed :
    forall (ms_init ms_fresh_sid ms_fresh_pr : MemState) dt pr sid
      (FRESH_SID : (fresh_sid ms_init (ret (ms_fresh_sid, sid))))
      (FRESH_PR : (fresh_provenance ms_fresh_sid (ret (ms_fresh_pr, pr))))
      (NON_VOID : dt <> DTYPE_Void),
    exists ms_final ptr,
      allocate_dtyp_spec dt ms_init (ret (ms_final, ptr)).
  Proof.
    intros ms_init ms_fresh_sid ms_fresh_pr dt pr sid FRESH_SID FRESH_PR NON_VOID.

    unfold allocate_dtyp_spec.

    pose proof generate_undef_bytes_succeeds dt sid as (bytes & UNDEF_BYTES).
    pose proof generate_undef_bytes_length dt sid bytes UNDEF_BYTES as BYTES_SIZE.

    pose proof allocate_bytes_spec_MemPropT_can_always_succeed
         ms_fresh_sid ms_fresh_pr dt bytes pr FRESH_PR BYTES_SIZE NON_VOID
      as (ms_final & ptr & ALLOC_SUCCESS).

    exists ms_final, ptr.
    exists ms_fresh_sid, sid; split; auto.

    rewrite UNDEF_BYTES.
    Opaque allocate_bytes_spec_MemPropT.
    cbn.
    Transparent allocate_bytes_spec_MemPropT.

    exists ms_fresh_sid, bytes.
    tauto.
  Qed.
End MemoryModelInfiniteSpecHelpers.
