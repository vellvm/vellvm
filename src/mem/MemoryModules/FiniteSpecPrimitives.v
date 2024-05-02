From Coq Require Import
     ZArith
     Strings.String
     List
     Lia
     Relations
     RelationClasses
     Morphisms.

From Vellvm Require Import
     Numeric.Coqlib
     Numeric.Integers.

From Vellvm.Semantics Require Import
     MemoryAddress
     MemoryParams
     LLVMParams
     LLVMEvents
     Lang
     Memory.FiniteProvenance
     Memory.Sizeof
     Memory.MemBytes
     Memory.ErrSID
     GepM
     VellvmIntegers
     StoreId.

From Vellvm.Utils Require Import
     Error
     IntMaps
     Tactics
     Inhabited.

From Vellvm.Handlers Require Import
     MemPropT
     MemoryModel
     MemoryInterpreters.

From Vellvm.Handlers.MemoryModules Require Import
     FiniteAddresses.

From ExtLib Require Import
     Structures.Monads.

Import ListNotations.

Import MonadNotation.
Open Scope monad_scope.

#[local] Open Scope Z_scope.

Module FiniteMemoryModelSpecPrimitives (LP : LLVMParams) (MP : MemoryParams LP) <: MemoryModelSpecPrimitives LP MP.
  Import LP.
  Import LP.Events.
  Import LP.ADDR.
  Import LP.SIZEOF.
  Import LP.PROV.
  Import PTOI.
  Import ITOP.
  Import MP.
  Import GEP.

  Import MemBytes.
  Module MemByte := Byte LP.ADDR LP.IP LP.SIZEOF LP.Events MP.BYTE_IMPL.
  Import MemByte.
  Import LP.SIZEOF.


  Section Datatype_Definition.

    (* Memory consists of bytes which have a provenance associated with them. *)
    Definition mem_byte := (SByte * AllocationId)%type.

    (** ** Memory
        Memory is just a map of mem_bytes.
     *)
    Definition memory := IntMap mem_byte.

    (** ** Stack frames
      A frame contains the list of block ids that need to be freed when popped,
      i.e. when the function returns.
      A [frame_stack] is a list of such frames.
     *)
    Definition Frame := list addr.
    Inductive FrameStack' : Type :=
    | Singleton (f : Frame)
    | Snoc (s : FrameStack') (f : Frame).

    (* The kernel does not recognize yet that a parameter can be
       instantiated by an inductive type. Hint: you can rename the
       inductive type and give a definition to map the old name to the new
       name. *)
    Definition FrameStack := FrameStack'.

    (** Heaps *)
    Definition Block := list addr.
    Definition Heap := IntMap Block.

    (** ** Memory stack
      The full notion of state manipulated by the monad is a pair of a [memory] and a [mem_stack].
     *)
    Record memory_stack' : Type :=
      mkMemoryStack
        { memory_stack_memory : memory;
          memory_stack_frame_stack : FrameStack;
          memory_stack_heap : Heap;
        }.

    Definition memory_stack := memory_stack'.

    (** Some operations on memory *)
    Definition set_byte_raw (mem : memory) (phys_addr : Z) (byte : mem_byte) : memory :=
      IM.add phys_addr byte mem.

    Definition read_byte_raw (mem : memory) (phys_addr : Z) : option mem_byte :=
      IM.find phys_addr mem.

    Lemma set_byte_raw_eq :
      forall (mem : memory) (byte : mem_byte) (x y : Z),
        x = y ->
        read_byte_raw (set_byte_raw mem x byte) y = Some byte.
    Proof using.
      intros mem byte x y XY.
      apply IP.F.add_eq_o; auto.
    Qed.

    Lemma set_byte_raw_neq :
      forall (mem : memory) (byte : mem_byte) (x y : Z),
        x <> y ->
        read_byte_raw (set_byte_raw mem x byte) y = read_byte_raw mem y.
    Proof using.
      intros mem byte x y XY.
      apply IP.F.add_neq_o; auto.
    Qed.

    Lemma read_byte_raw_add_all_index_out :
      forall (mem : memory) l z p,
        p < z \/ p >= z + Zlength l ->
        read_byte_raw (add_all_index l z mem) p = read_byte_raw mem p.
    Proof using.
      intros mem l z p BOUNDS.
      unfold read_byte_raw.
      eapply lookup_add_all_index_out; eauto.
    Qed.

    Lemma read_byte_raw_add_all_index_in :
      forall (mem : memory) l z p v,
        z <= p <= z + Zlength l - 1 ->
        list_nth_z l (p - z) = Some v ->
        read_byte_raw (add_all_index l z mem) p = Some v.
    Proof using.
      intros mem l z p v BOUNDS IN.
      unfold read_byte_raw.
      eapply lookup_add_all_index_in; eauto.
    Qed.

    Lemma read_byte_raw_add_all_index_in_exists :
      forall (mem : memory) l z p,
        z <= p <= z + Zlength l - 1 ->
        exists v, list_nth_z l (p - z) = Some v /\
               read_byte_raw (add_all_index l z mem) p = Some v.
    Proof using.
      intros mem l z p IN.
      pose proof range_list_nth_z l (p - z) as H.
      forward H.
      lia.
      destruct H as [v NTH].
      exists v.

      split; auto.
      unfold read_byte_raw.
      eapply lookup_add_all_index_in; eauto.
    Qed.

    Lemma InA_In :
      forall mem ix e,
        SetoidList.InA (IM.eq_key_elt (elt:=mem_byte)) (ix, e) (IM.elements (elt:=mem_byte) mem) ->
        In (ix, e) (IM.elements (elt:=mem_byte) mem).
    Proof using.
      intros mem.
      induction (IM.elements (elt:=mem_byte) mem);
        intros ix e INS.

      - exfalso. apply SetoidList.InA_nil in INS; auto.
      - apply SetoidList.InA_cons in INS.
        destruct INS as [INS | INS]; firstorder.
        cbn in *; subst.
        left; destruct a; reflexivity.
    Qed.

    Lemma In_InA :
      forall mem ix e,
        In (ix, e) (IM.elements (elt:=mem_byte) mem) ->
        SetoidList.InA (IM.eq_key_elt (elt:=mem_byte)) (ix, e) (IM.elements (elt:=mem_byte) mem).
    Proof using.
      intros mem.
      induction (IM.elements (elt:=mem_byte) mem);
        intros ix e INS.

      - cbn in INS; contradiction.
      - apply SetoidList.InA_cons.
        destruct INS as [INS | INS]; firstorder.
        left; subst; eauto.
        repeat red; eauto.
    Qed.

    Lemma read_byte_raw_next_memory_key :
      forall (mem : memory) ix,
        ix >= next_key mem ->
        read_byte_raw mem ix = None.
    Proof using.
      intros mem ix H.
      unfold read_byte_raw.
      apply IP.F.not_find_in_iff.
      unfold next_key in *.
      intros IN.
      apply IP.F.elements_in_iff in IN.
      destruct IN as [e IN].

      pose proof (maximumBy_Z_correct (-1) (map fst (IM.elements (elt:=mem_byte) mem)) ix) as LE.
      forward LE.
      { apply InA_In in IN.
        replace ix with (fst (ix, e)) by auto.
        apply in_map; auto.
      }
      apply Zle_bool_imp_le in LE.
      lia.
    Qed.

    Lemma read_byte_raw_lt_next_memory_key :
      forall (mem : memory) ix v,
        read_byte_raw mem ix = Some v ->
        ix < next_key mem.
    Proof using.
      intros mem ix H.
      intros FIND.
      pose proof (Z_lt_le_dec ix (next_key mem)) as [LT | GE]; auto.
      assert (read_byte_raw mem ix = None) as NONE.
      { apply read_byte_raw_next_memory_key.
        lia.
      }
      rewrite FIND in NONE.
      inv NONE.
    Qed.

  End Datatype_Definition.

  (* Convenient to make these opaque so they don't get unfolded *)
  #[global] Opaque set_byte_raw.
  #[global] Opaque read_byte_raw.


  Record MemState' :=
    mkMemState
      { ms_memory_stack : memory_stack;
        (* Used to keep track of allocation ids in use *)
        ms_provenance : Provenance;
      }.

  (* The kernel does not recognize yet that a parameter can be
  instantiated by an inductive type. Hint: you can rename the
  inductive type and give a definition to map the old name to the new
  name.
  *)
  Definition MemState := MemState'.

  Definition memory_empty : memory := IntMaps.empty.
  Definition frame_empty : FrameStack := Singleton [].
  Definition heap_empty : Heap := IntMaps.empty.

  Definition empty_memory_stack : memory_stack :=
    mkMemoryStack memory_empty frame_empty heap_empty.

  Definition initial_memory_state : MemState :=
    mkMemState empty_memory_stack initial_provenance.

  Definition mem_state_memory_stack (ms : MemState) : memory_stack
    := ms.(ms_memory_stack).

  Definition MemState_get_memory := mem_state_memory_stack.
  Definition MemState_put_memory (mem' : memory_stack) (ms : MemState) : MemState :=
    let '(mkMemState mem prov) := ms in
    (mkMemState mem' prov).

  Definition mem_state_memory (ms : MemState) : memory
    := memory_stack_memory (MemState_get_memory ms).

  Definition mem_state_provenance (ms : MemState) : Provenance
    := ms.(ms_provenance).

  Definition MemState_get_provenance := mem_state_provenance.

  Definition mem_state_frame_stack (ms : MemState) : FrameStack
    := memory_stack_frame_stack ms.(ms_memory_stack).

  Definition mem_state_heap (ms : MemState) : Heap
    := memory_stack_heap ms.(ms_memory_stack).

  Definition read_byte_prop_memory (ptr : addr) (mem_stack : memory_stack) (byte : SByte) : Prop :=
    let addr := ptr_to_int ptr in
    let pr := address_provenance ptr in
    let mem := memory_stack_memory mem_stack in
    match read_byte_raw mem addr with
    | None => False
    | Some mbyte =>
        let aid := snd mbyte in
        if access_allowed pr aid
        then byte = fst mbyte
        else
          False
    end.

  Definition addr_allocated_prop_memory (ptr : addr) (aid : AllocationId) (mem_stack : memory_stack) : Prop :=
    let mem := memory_stack_memory mem_stack in
    match read_byte_raw mem (ptr_to_int ptr) with
    | None => False
    | Some (byte, aid') =>
        aid_eq_dec aid aid'
    end.

  Definition ptr_in_frame_prop (f : Frame) (ptr : addr) : Prop :=
    In (ptr_to_int ptr) (map ptr_to_int f).

  Definition frame_eqv (f f' : Frame) : Prop :=
    forall ptr, ptr_in_frame_prop f ptr <-> ptr_in_frame_prop f' ptr.

  #[global] Instance frame_eqv_Equivalence : Equivalence frame_eqv.
  Proof using.
    split.
    - intros f ptr.
      reflexivity.
    - intros f1 f2 EQV.
      unfold frame_eqv in *.
      firstorder.
    - intros x y z XY YZ.
      firstorder.
  Qed.

  Fixpoint FSIn (f : Frame) (fs : FrameStack) : Prop :=
    match fs with
    | Singleton f' => f' = f
    | Snoc fs f' => f' = f \/ FSIn f fs
    end.

  Fixpoint FSIn_eqv (f : Frame) (fs : FrameStack) : Prop :=
    match fs with
    | Singleton f' => frame_eqv f' f
    | Snoc fs f' => frame_eqv f' f \/ FSIn_eqv f fs
    end.

  Fixpoint FSNth_rel (R : relation Frame) (fs : FrameStack) (n : nat) (f : Frame) : Prop :=
    match n with
    | 0%nat =>
        match fs with
        | Singleton f' => R f' f
        | Snoc fs f' => R f' f
        end
    | S n =>
        match fs with
        | Singleton f' => False
        | Snoc fs f' => FSNth_rel R fs n f
        end
    end.

  Definition FSNth_eqv := FSNth_rel frame_eqv.

  Definition frame_stack_eqv (fs fs' : FrameStack) : Prop :=
    forall f n, FSNth_eqv fs n f <-> FSNth_eqv fs' n f.

  #[global] Instance frame_stack_eqv_Equivalence : Equivalence frame_stack_eqv.
  Proof using.
    split; try firstorder.
    - intros x y z XY YZ.
      unfold frame_stack_eqv in *.
      intros f n.
      split; intros NTH.
      + apply YZ; apply XY; auto.
      + apply XY; apply YZ; auto.
  Qed.

  (* Check for the current frame *)
  Definition peek_frame_stack_prop (fs : FrameStack) (f : Frame) : Prop :=
    match fs with
    | Singleton f' => frame_eqv f f'
    | Snoc s f' => frame_eqv f f'
    end.

  Definition pop_frame_stack_prop (fs fs' : FrameStack) : Prop :=
    match fs with
    | Singleton f => False
    | Snoc s f => frame_stack_eqv s fs'
    end.

  Definition memory_stack_frame_stack_prop (mem : memory_stack) (fs : FrameStack) : Prop :=
    frame_stack_eqv (memory_stack_frame_stack mem) fs.

  Definition mem_state_frame_stack_prop (ms : MemState) (fs : FrameStack) : Prop :=
    memory_stack_frame_stack_prop (MemState_get_memory ms) fs.

  (** Heap *)
  Definition ptr_in_heap_prop (h : Heap) (root ptr : addr) : Prop
    := match IM.find (ptr_to_int root) h with
       | None => False
       | Some ptrs => In (ptr_to_int ptr) (map ptr_to_int ptrs)
       end.

  Definition root_in_heap_prop (h : Heap) (root : addr) : Prop
    := member (ptr_to_int root) h.

  Record heap_eqv (h h' : Heap) : Prop :=
    {
      heap_roots_eqv : forall root, root_in_heap_prop h root <-> root_in_heap_prop h' root;
      heap_ptrs_eqv : forall root ptr, ptr_in_heap_prop h root ptr <-> ptr_in_heap_prop h' root ptr;
    }.

  #[global] Instance root_in_heap_prop_Proper :
    Proper (heap_eqv ==> eq ==> iff) root_in_heap_prop.
  Proof using.
    intros h h' HEAPEQ ptr ptr' PTREQ; subst.
    inv HEAPEQ.
    eauto.
  Qed.

  #[global] Instance ptr_in_heap_prop_Proper :
    Proper (heap_eqv ==> eq ==> eq ==> iff) ptr_in_heap_prop.
  Proof using.
    intros h h' HEAPEQ root root' ROOTEQ ptr ptr' PTREQ; subst.
    inv HEAPEQ.
    eauto.
  Qed.

  #[global] Instance heap_Equivalence : Equivalence heap_eqv.
  Proof using.
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

  (* Memory stack's heap *)
  Definition memory_stack_heap_prop (ms : memory_stack) (h : Heap) : Prop
    := heap_eqv (memory_stack_heap ms) h.

  Definition mem_state_heap_prop (ms : MemState) (h : Heap) : Prop :=
    memory_stack_heap_prop (MemState_get_memory ms) h.

  (** Provenance / store ids *)
  Definition used_provenance_prop (ms : MemState) (pr : Provenance) : Prop :=
    provenance_lt pr (next_provenance (mem_state_provenance ms)).

  Definition get_fresh_provenance (ms : MemState) : Provenance :=
    let pr := mem_state_provenance ms in
    next_provenance pr.

  Lemma get_fresh_provenance_fresh :
    forall (ms : MemState),
      ~ used_provenance_prop ms (get_fresh_provenance ms).
  Proof using.
    intros ms.
    unfold used_provenance_prop.
    destruct ms.
    cbn.
    unfold get_fresh_provenance.
    cbn.
    apply provenance_lt_nrefl.
  Qed.

  Definition mem_state_fresh_provenance (ms : MemState) : (Provenance * MemState)%type :=
    match ms with
    | mkMemState mem_stack pr =>
        let pr' := next_provenance pr in
        (pr', mkMemState mem_stack pr')
    end.

  Definition used_store_id_prop (ms : MemState) (sid : store_id) : Prop :=
    exists ptr byte aid,
      let mem := mem_state_memory ms in
      read_byte_raw mem ptr = Some (byte, aid) /\
        sbyte_sid byte = inr sid.

  Lemma mem_state_fresh_provenance_fresh :
    forall (ms ms' : MemState) (pr : Provenance),
      mem_state_fresh_provenance ms = (pr, ms') ->
      MemState_get_memory ms = MemState_get_memory ms' /\
        (forall pr, used_provenance_prop ms pr -> used_provenance_prop ms' pr) /\
      ~ used_provenance_prop ms pr /\ used_provenance_prop ms' pr.
  Proof using.
    intros ms ms' pr MSFP.
    unfold mem_state_fresh_provenance in *.
    destruct ms; cbn in *; inv MSFP.
    split; [|split; [|split]].
    - reflexivity.
    - intros pr H.
      unfold used_provenance_prop in *.
      cbn in *.
      eapply provenance_lt_trans.
      apply H.
      apply provenance_lt_next_provenance.
    - intros CONTRA;
      unfold used_provenance_prop in *.
      cbn in CONTRA.
      eapply provenance_lt_nrefl; eauto.
    - unfold used_provenance_prop in *.
      cbn.
      apply provenance_lt_next_provenance.
  Qed.

  (** Extra frame stack lemmas *)
  Lemma frame_stack_eqv_snoc_sing_inv :
    forall fs f1 f2,
      frame_stack_eqv (Snoc fs f1) (Singleton f2) -> False.
  Proof using.
    intros fs f1 f2 EQV.
    destruct fs.
    - unfold frame_stack_eqv in *.
      specialize (EQV f 1%nat).
      destruct EQV as [NTH1 NTH2].
      cbn in *.
      apply NTH1.
      reflexivity.
    - unfold frame_stack_eqv in *.
      specialize (EQV f 1%nat).
      destruct EQV as [NTH1 NTH2].
      cbn in *.
      apply NTH1.
      reflexivity.
  Qed.

  Lemma frame_stack_eqv_sing_snoc_inv :
    forall fs f1 f2,
      frame_stack_eqv (Singleton f2) (Snoc fs f1) -> False.
  Proof using.
    intros fs f1 f2 EQV.
    destruct fs.
    - unfold frame_stack_eqv in *.
      specialize (EQV f 1%nat).
      destruct EQV as [NTH1 NTH2].
      cbn in *.
      apply NTH2.
      reflexivity.
    - unfold frame_stack_eqv in *.
      specialize (EQV f 1%nat).
      destruct EQV as [NTH1 NTH2].
      cbn in *.
      apply NTH2.
      reflexivity.
  Qed.

  Lemma FSNTH_rel_snoc :
    forall R fs f n x,
      FSNth_rel R (Snoc fs f) (S n) x =
        FSNth_rel R fs n x.
  Proof using.
    intros R fs f n x.
    cbn. reflexivity.
  Qed.

  Lemma frame_stack_snoc_inv_fs :
    forall fs1 fs2 f1 f2,
      frame_stack_eqv (Snoc fs1 f1) (Snoc fs2 f2) ->
      frame_stack_eqv fs1 fs2.
  Proof using.
    intros fs1 fs2 f1 f2 EQV.
    unfold frame_stack_eqv in *.
    intros f n.
    specialize (EQV f (S n)).
    setoid_rewrite FSNTH_rel_snoc in EQV.
    apply EQV.
  Qed.

  Lemma frame_stack_snoc_inv_f :
    forall fs1 fs2 f1 f2,
      frame_stack_eqv (Snoc fs1 f1) (Snoc fs2 f2) ->
      frame_eqv f1 f2.
  Proof using.
    intros fs1 fs2 f1 f2 EQV.
    unfold frame_stack_eqv in *.
    specialize (EQV f2 0%nat).
    cbn in *.
    apply EQV.
    reflexivity.
  Qed.

  Lemma frame_stack_inv :
    forall fs1 fs2,
      frame_stack_eqv fs1 fs2 ->
      (exists fs1' fs2' f1 f2,
          fs1 = (Snoc fs1' f1) /\ fs2 = (Snoc fs2' f2) /\
            frame_stack_eqv fs1' fs2' /\
            frame_eqv f1 f2) \/
        (exists f1 f2,
            fs1 = Singleton f1 /\ fs2 = Singleton f2 /\
              frame_eqv f1 f2).
  Proof using.
    intros fs1 fs2 EQV.
    destruct fs1, fs2.
    - right.
      do 2 eexists.
      split; eauto.
      split; eauto.
      specialize (EQV f 0%nat).
      cbn in EQV.
      symmetry.
      apply EQV.
      reflexivity.
    - exfalso; eapply frame_stack_eqv_sing_snoc_inv; eauto.
    - exfalso; eapply frame_stack_eqv_snoc_sing_inv; eauto.
    - left.
      do 4 eexists.
      split; eauto.
      split; eauto.

      split.
      + eapply frame_stack_snoc_inv_fs; eauto.
      + eapply frame_stack_snoc_inv_f; eauto.
  Qed.

  #[global] Instance peek_frame_stack_prop_Proper :
    Proper (frame_stack_eqv ==> frame_eqv ==> iff) peek_frame_stack_prop.
  Proof using.
    unfold Proper, respectful.
    intros xs ys XSYS x y XY.
    eapply frame_stack_inv in XSYS as [XSYS | XSYS].
    - (* Singleton framestacks *)
      destruct XSYS as [fs1' [fs2' [f1 [f2 [X [Y [EQFS EQF]]]]]]].
      subst.
      cbn in *.
      rewrite EQF.
      rewrite XY.
      reflexivity.
    - (* Snoc framestacks *)
      destruct XSYS as [f1 [f2 [X [Y EQF]]]].
      subst.
      cbn in *.
      rewrite EQF.
      rewrite XY.
      reflexivity.
  Qed.

  #[global] Instance peek_frame_stack_prop_impl_Proper :
    Proper (frame_stack_eqv ==> frame_eqv ==> Basics.impl ) peek_frame_stack_prop.
  Proof using.
    unfold Proper, respectful.
    intros xs ys XSYS x y XY.
    rewrite XY.
    rewrite XSYS.
    intros H; auto.
  Qed.

  #[global] Instance pop_frame_stack_prop_Proper :
    Proper (frame_stack_eqv ==> frame_stack_eqv ==> iff) pop_frame_stack_prop.
  Proof using.
    unfold Proper, respectful.
    intros x y XY a b AB.
    eapply frame_stack_inv in XY as [XY | XY].
    - (* Singleton framestacks *)
      destruct XY as [fs1' [fs2' [f1 [f2 [X [Y [EQFS EQF]]]]]]].
      subst.
      cbn in *.
      rewrite EQFS.
      rewrite AB.
      reflexivity.
    - (* Snoc framestacks *)
      destruct XY as [f1 [f2 [X [Y EQF]]]].
      subst.
      cbn in *.
      reflexivity.
  Qed.

  #[global] Instance frame_eqv_cons_Proper :
    Proper (eq ==> frame_eqv ==> frame_eqv) cons.
  Proof using.
    unfold Proper, respectful.
    intros ptr ptr' EQ f1 f2 EQV; subst.
    unfold frame_eqv in *.
    cbn in *; intros ptr; split; firstorder.
  Qed.

  (* TODO: move this *)
  #[global] Instance ptr_in_frame_prop_int_Proper :
    Proper (frame_eqv ==> (fun a b => ptr_to_int a = ptr_to_int b) ==> iff) ptr_in_frame_prop.
  Proof using.
    unfold Proper, respectful.
    intros x y XY a b AB.
    unfold frame_eqv in *.
    unfold ptr_in_frame_prop in *.
    rewrite AB; auto.
  Qed.

  #[global] Instance ptr_in_frame_prop_Proper :
    Proper (frame_eqv ==> eq ==> iff) ptr_in_frame_prop.
  Proof using.
    unfold Proper, respectful.
    intros x y XY a b AB; subst.
    unfold frame_eqv in *.
    auto.
  Qed.

  (* TODO: Move this *)
  Lemma FSNth_frame_eqv :
    forall n fs f1 f2,
      frame_eqv f1 f2 ->
      FSNth_eqv fs n f1 ->
      FSNth_eqv fs n f2.
  Proof using.
    induction n;
      intros fs f1 f2 EQV NTHEQV.
    - destruct fs; cbn in *;
        rewrite NTHEQV; auto.
    - destruct fs; cbn in *; eauto.
  Qed.

  (* TODO: Move this *)
  #[global] Instance FSNth_eqv_Proper :
    Proper (frame_stack_eqv ==> eq ==> frame_eqv ==> iff) FSNth_eqv.
  Proof using.
    unfold Proper, respectful.
    intros x y H' x0 y0 H0 x1 y1 H1; subst.
    split; intros NTH.
    - red in H'.
      apply H'.
      eapply FSNth_frame_eqv; eauto.
    - red in H'.
      apply H'.
      eapply FSNth_frame_eqv; eauto.
      symmetry; auto.
  Qed.

  #[global] Instance frame_stack_eqv_Singleton_Proper :
    Proper (frame_eqv ==> frame_stack_eqv) Singleton.
  Proof using.
    intros fs' fs FS.
    split; intros NTH.
    - cbn in *.
      break_match_hyp; auto.
      rewrite <- FS; auto.
    - cbn in *.
      break_match_hyp; auto.
      rewrite FS; auto.
  Qed.

  #[global] Instance frame_stack_eqv_Snoc_Proper :
    Proper (frame_stack_eqv ==> frame_eqv ==> frame_stack_eqv) Snoc.
  Proof using.
    unfold Proper, respectful.
    intros x y H x0 y0 H0.
    split.
    - intros H1.
      revert x0 y0 x y f H1 H H0.
      induction n; intros x0 y0 x y f H1 H H0; cbn in *.
      + rewrite <- H0; auto.
      + destruct n.
        * rewrite <- H; auto.
        * rewrite <- H; eauto.
    - intros H1.
      revert x0 y0 x y f H1 H H0.
      induction n; intros x0 y0 x y f H1 H H0; cbn in *.
      + rewrite H0; auto.
      + destruct n.
        * rewrite H; auto.
        * rewrite H; eauto.
  Qed.

  Lemma MemState_get_put_memory :
    forall ms mem,
      MemState_get_memory (MemState_put_memory mem ms) = mem.
  Proof using.
    intros ms mem.
    destruct ms.
    cbn.
    reflexivity.
  Qed.

  Lemma memory_stack_memory_mem_state_memory :
    forall m,
      memory_stack_memory (MemState_get_memory m) = mem_state_memory m.
  Proof using.
    intros m.
    destruct m.
    cbn.
    destruct ms_memory_stack0.
    cbn.
    auto.
  Qed.

  #[global] Instance MemState_memory_MemStateMem : MemStateMem MemState memory_stack :=
    {| ms_get_memory := MemState_get_memory;
      ms_put_memory := MemState_put_memory;
      ms_get_put_memory := MemState_get_put_memory;
    |}.

  #[global] Instance Inhabited_MemState : Inhabited MemState :=
    { inhabitant := initial_memory_state
    }.

End FiniteMemoryModelSpecPrimitives.
