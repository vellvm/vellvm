(*** Memory model implementations using intmaps *)
From Stdlib Require Import
  ZArith
  String
  Lia
  Structures.Equalities.

From Mem Require Import
  MemoryModel
  MemoryModelHelpers
  Addresses.MemoryAddress
  Addresses.Provenance
  SByte
  StoreId
  FiniteMaps
  Tactics
  Heaps
  StackFrames
  Utils.

From Stdlib Require Import
  List.

From Vellvm Require Import Error.

From ExtLib Require Import Structures.Monads.
Import MonadNotation.
Open Scope monad.

Notation err := (sum string).

(** Memory models based on integer maps *)
Module INTMAP_MEMORY_MODEL_BASE (ADDR : CORE_ADDRESS) (PTOI : HAS_PTOI ADDR) (SB : SBYTE) <: MEMORY_MODEL_BASE ADDR SB.
  Import ADDR.
  Import SB.

  Definition Memory := IM.t SByte.
  Definition initial_memory := @IM.empty SByte.
End INTMAP_MEMORY_MODEL_BASE.

Module Type CORE_CORRECT_MEMORY_MODEL_HELPER (ADDR : CORE_ADDRESS) (SB : SBYTE) := MEMORY_MODEL_BASE ADDR SB <+ CORE_CORRECT_MEMORY_MODEL ADDR SB.

Module INTMAP_MEMORY_MODEL_CORE (ADDR : CORE_ADDRESS) (PTOI : HAS_PTOI ADDR) (SB : SBYTE) <: CORE_CORRECT_MEMORY_MODEL_HELPER ADDR SB.
  Import ADDR.
  Import SB.

  Include (INTMAP_MEMORY_MODEL_BASE ADDR PTOI SB).

  Definition read_byte (m : Memory) (ptr : addr) (b : SByte) : Prop :=
    match IM.find (PTOI.ptr_to_int ptr) m with
    | None => False
    | Some b' => b = b'
    end.

  Definition read_byte_exec (m : Memory) (ptr : addr) : err SByte :=
    match IM.find (PTOI.ptr_to_int ptr) m with
    | None => inl "read_byte_exec: byte doesn't exist in memory"%string
    | Some b => inr b
    end.

  Lemma read_byte_correct :
    forall m ptr sb,
      read_byte_exec m ptr = inr sb ->
      read_byte m ptr sb.
  Proof.
    intros m ptr sb READ.
    unfold read_byte, read_byte_exec in *.
    repeat break_match_hyp_inv; auto.
  Qed.

  Lemma read_byte_correct_err :
    forall m ptr sb str,
      read_byte_exec m ptr = inl str ->
      ~ read_byte m ptr sb.
  Proof.
    intros m ptr sb str READ.
    unfold read_byte, read_byte_exec in *.
    repeat break_match_hyp_inv; auto.
  Qed.
End INTMAP_MEMORY_MODEL_CORE.

(** Memory models based on integer maps with allocation ids *)
Module INTMAP_AID_MEMORY_MODEL
  (MD : Typ)
  (PS : PROV_SET)
  (Import ADDR : ADDRESS MD PS)
  (Import AID : ALLOCATION_ID)
  (Import A : AID_PROVENANCE PS AID)
  (Import SB : SBYTE) <: CORRECT_ALLOCATABLE_MEMORY_FRESH ADDR SB AID.

  Record Memory' :=
    MkMemory {
      Memory_aid_counter : AllocationId;
      Memory_sid_counter : store_id;
      Memory_byte_map : IM.t (SByte * AllocationId)%type;
    }.

  Definition Memory := Memory'.
  Definition initial_memory : Memory := MkMemory initial_aid 0%N (@IM.empty (SByte * AllocationId))%type.

  (*** MEMORY_ALLOCATED_CORE *)
  (** Whether an address is allocated with a given AllocationId *)
  Definition addr_allocated (m : Memory) (ptr : addr) (aid : AllocationId) : Prop :=
    match IM.find (ptr_to_int ptr) (Memory_byte_map m) with
    | None => False
    | Some (_, aid') => AID.eq aid aid'
    end.

  Definition addr_not_allocated (m : Memory) (ptr : addr) :=
    forall aid, ~ addr_allocated m ptr aid.

  (*** READABLE_MEMORY *)
  Definition read_byte_allowed (m : Memory) (ptr : addr) : Prop :=
    exists aid, addr_allocated m ptr aid /\ access_allowed (address_provenance ptr) aid = true.

  Definition read_byte (m : Memory) (ptr : addr) (b : SByte) : Prop :=
    match IM.find (ptr_to_int ptr) (Memory_byte_map m) with
    | None => False
    | Some (b', aid) => b = b' /\ access_allowed (address_provenance ptr) aid = true
    end.

  Definition read_byte_exec (m : Memory) (ptr : addr) : err SByte :=
    match IM.find (ptr_to_int ptr) (Memory_byte_map m) with
    | None => inl "read_byte_exec: byte not in memory."%string
    | Some (b', aid) =>
        if access_allowed (address_provenance ptr) aid
        then inr b'
        else inl "ready_byte_exec: invalid provenance."%string
    end.

  Lemma read_byte_correct :
    forall m ptr sb,
      read_byte_exec m ptr = inr sb ->
      read_byte m ptr sb.
  Proof.
    intros m ptr sb READ.
    unfold read_byte, read_byte_exec in *.
    repeat break_match_hyp_inv; auto.
  Qed.

  Lemma read_byte_correct_err :
    forall m ptr sb str,
      read_byte_exec m ptr = inl str ->
      ~ read_byte m ptr sb.
  Proof.
    intros m ptr sb str READ.
    unfold read_byte, read_byte_exec in *.
    repeat break_match_hyp_inv; auto.
    intros (_&CONTRA); inv CONTRA.
  Qed.

  Lemma read_byte_allowed_spec :
    forall (m : Memory) (ptr : addr),
      ~ read_byte_allowed m ptr ->
      forall b, ~ read_byte m ptr b.
  Proof.
    intros m ptr NRBA b RB.
    apply NRBA.
    red; red in RB.
    break_match_hyp; [|contradiction].
    destruct p, RB; subst.
    exists t0.
    split; auto.
    red.
    rewrite Heqo.
    reflexivity.
  Qed.

  (*** WRITEABLE_MEMORY *)
  Definition disjoint_ptr_byte (a b : addr) :=
    ptr_to_int a <> ptr_to_int b.

  Definition write_byte_allowed (m : Memory) (ptr : addr) : Prop :=
    exists aid, addr_allocated m ptr aid /\ access_allowed (address_provenance ptr) aid = true.

  Definition write_byte (m1 : Memory) (ptr : addr) (b : SByte) (m2 : Memory) : Prop :=
    let phys_addr := ptr_to_int ptr in
    let pr := address_provenance ptr in
    match IM.find phys_addr (Memory_byte_map m1) with
    | None => False (* "Writing to unallocated memory" *)
    | Some (_, aid) =>
        if access_allowed pr aid
        then m2 = MkMemory (Memory_aid_counter m1) (Memory_sid_counter m1) (IM.add phys_addr (b, aid) (Memory_byte_map m1))
        else False (* Invalid access *)
    end.

  Definition write_byte_exec (m1 : Memory) (ptr : addr) (b : SByte) : err Memory :=
    let phys_addr := ptr_to_int ptr in
    let pr := address_provenance ptr in
    match IM.find phys_addr (Memory_byte_map m1) with
    | None => inl "write_byte_exec: trying to write to unallocated memory."%string
    | Some (_, aid) =>
        if access_allowed pr aid
        then inr (MkMemory (Memory_aid_counter m1) (Memory_sid_counter m1) (IM.add phys_addr (b, aid) (Memory_byte_map m1)))
        else inl "write_byte_exec: provenance mismatch."%string
    end.

  #[global] Hint Unfold write_byte write_byte_exec : MEM.

  Lemma write_byte_correct :
    forall m1 ptr b m2,
      write_byte_exec m1 ptr b = inr m2 ->
      write_byte m1 ptr b m2.
  Proof.
    intros m1 ptr b m2 WRITE.
    autounfold with MEM in *.
    repeat break_match_hyp_inv; auto.
  Qed.

  Lemma write_byte_correct_err :
    forall m1 ptr b m2 str,
      write_byte_exec m1 ptr b = inl str ->
      ~ write_byte m1 ptr b m2.
  Proof.
    intros m1 ptr b m2 str WRITE.
    autounfold with MEM in *.
    repeat break_match_hyp_inv; auto.
  Qed.

  (** We can look up a new value after writing it to memory *)
  Lemma write_byte_new_lu :
    forall (m1 : Memory) (ptr : addr) (byte : SByte) (m2 : Memory),
      write_byte m1 ptr byte m2 ->
      read_byte m2 ptr byte.
  Proof.
    intros m1 ptr byte m2 WB.
    red in WB; red.
    repeat (break_match_hyp; try contradiction); subst.
    unfold Memory_byte_map.
    rewrite find_add_eq; auto.
  Qed.

  (** We can look up old values after writing to a disjoint location in memory *)
  Lemma write_byte_old_lu :
    forall (m1 : Memory) (ptr : addr) (byte : SByte) (m2 : Memory),
      write_byte m1 ptr byte m2 ->
      forall ptr',
        disjoint_ptr_byte ptr ptr' ->
        (forall byte', read_byte m1 ptr' byte' <-> read_byte m2 ptr' byte').
  Proof.
    intros m1 ptr byte m2 WB ptr' DISJOINT byte'.
    red in WB.
    repeat (break_match_hyp; try contradiction); subst.
    split; intros RB; red; red in RB;
      repeat (break_match_hyp; try contradiction); destruct RB; subst;
      unfold Memory_byte_map in *.
    { erewrite find_add_neq; eauto.
      cbn; auto.
    }
    { rewrite IP.F.add_neq_o in Heqo0; auto.
      rewrite Heqo0; auto.
    }
  Qed.

  Lemma write_byte_allowed_spec :
    forall (m : Memory) (ptr : addr),
      ~ write_byte_allowed m ptr ->
      forall b m2, ~ write_byte m ptr b m2.
  Proof.
    intros m ptr NWBA b m2 WB.
    apply NWBA.
    red; red in WB.
    repeat break_match_hyp; try contradiction; subst.
    exists t0.
    split; auto.
    red.
    rewrite Heqo.
    reflexivity.
  Qed.

  Definition read_byte_allowed_preserved
    (m1 m2 : Memory) : Prop
    := forall ptr,
      read_byte_allowed m1 ptr <-> read_byte_allowed m2 ptr.

  Lemma write_byte_preserves_read_byte_allowed :
    forall m1 ptr b m2,
      write_byte m1 ptr b m2 ->
      read_byte_allowed_preserved m1 m2.
  Proof.
    intros m1 ptr b m2 WB.
    red; red in WB.
    repeat break_match_hyp; try contradiction; subst.
    intros ptr'.
    pose proof (Z.eq_dec (ptr_to_int ptr) (ptr_to_int ptr')) as [EQ | NEQ].

    { (* Pointers overlap *)
      split; intros RBA; red; red in RBA;
        destruct RBA as (aid & ALLOCATED & ACCESS);
        exists aid; cbn; split; auto.
      - red. unfold Memory_byte_map. rewrite IP.F.add_eq_o; auto.
        red in ALLOCATED.
        rewrite EQ in Heqo.
        rewrite Heqo in ALLOCATED; auto.
      - red; red in ALLOCATED.
        rewrite EQ in Heqo.
        rewrite Heqo.
        unfold Memory_byte_map in ALLOCATED.
        rewrite IP.F.add_eq_o in ALLOCATED; auto.
    }

    { (* Pointers don't overlap *)
      split; intros RBA; red; red in RBA;
        destruct RBA as (aid & ALLOCATED & ACCESS);
        exists aid; cbn; split; auto.
      - red. unfold Memory_byte_map. rewrite IP.F.add_neq_o; auto.
      - red in ALLOCATED; red. unfold Memory_byte_map in *. rewrite IP.F.add_neq_o in ALLOCATED; auto.
    }
  Qed.

  Definition write_byte_allowed_preserved
    (m1 m2 : Memory) : Prop
    := forall ptr,
      write_byte_allowed m1 ptr <-> write_byte_allowed m2 ptr.

  Lemma write_byte_preserves_write_byte_allowed :
    forall m1 ptr b m2,
      write_byte m1 ptr b m2 ->
      write_byte_allowed_preserved m1 m2.
  Proof.
    apply write_byte_preserves_read_byte_allowed.
  Qed.

  Lemma read_byte_allocated_spec :
    forall (m : Memory) (ptr : addr),
      addr_not_allocated m ptr ->
      forall b, ~ read_byte m ptr b.
  Proof.
    intros m ptr NALLOC b READ.
    red in NALLOC, READ.
    repeat (break_match_hyp; try contradiction);
      subst.
    destruct READ; subst.
    apply (NALLOC t0).
    red.
    rewrite Heqo.
    reflexivity.
  Qed.

  Include (ALL_ALLOCATED_PRESERVED ADDR SB AID).

  Lemma write_byte_preserves_allocated :
    forall m1 ptr b m2,
      write_byte m1 ptr b m2 ->
      all_allocated_preserved m1 m2.
  Proof.
    intros m1 ptr b m2 WB.
    red; red in WB.
    repeat break_match_hyp; try contradiction; subst.
    intros ptr' aid'.
    unfold addr_allocated.
    pose proof (Z.eq_dec (ptr_to_int ptr) (ptr_to_int ptr')) as [EQ | NEQ].

    { (* Pointers overlap *)
      rewrite <- EQ.
      rewrite Heqo.
      unfold Memory_byte_map.
      rewrite IP.F.add_eq_o; auto.
      reflexivity.
    }

    { (* Pointers don't overlap *)
      unfold Memory_byte_map.
      rewrite IP.F.add_neq_o; auto.
      reflexivity.
    }
  Qed.

  Definition Memory_aid_modify (m : Memory) (f : AllocationId -> AllocationId) : Memory :=
    MkMemory (f (Memory_aid_counter m)) (Memory_sid_counter m) (Memory_byte_map m).

  Lemma Memory_aid_modify_spec :
    forall (m1 m2 : Memory) (f : AllocationId -> AllocationId) (aid1 aid2 : AllocationId),
      aid1 = Memory_aid_counter m1 ->
      m2 = Memory_aid_modify m1 f ->
      aid2 = Memory_aid_counter m2 ->
      aid2 = f aid1.
  Proof.
    intros m1 m2 f aid1 aid2 H H0 H1.
    subst.
    unfold Memory_aid_counter, Memory_aid_modify.
    destruct m1; cbn.
    reflexivity.
  Qed.

  Definition Memory_fresh_aid (m : Memory) : (AllocationId * Memory)%type
    := let aid := Memory_aid_counter m in
       let aid' := next_aid aid in
       (aid', Memory_aid_modify m (fun _ => aid')).

  Definition Memory_sid_modify (m : Memory) (f : store_id -> store_id) : Memory :=
    MkMemory (Memory_aid_counter m) (f (Memory_sid_counter m)) (Memory_byte_map m).

  Lemma Memory_sid_modify_spec :
    forall (m1 m2 : Memory) (f : store_id -> store_id) (sid1 sid2 : store_id),
      sid1 = Memory_sid_counter m1 ->
      m2 = Memory_sid_modify m1 f ->
      sid2 = Memory_sid_counter m2 ->
      sid2 = f sid1.
  Proof.
    intros m1 m2 f sid1 sid2 H H0 H1.
    subst.
    unfold Memory_sid_counter, Memory_sid_modify.
    destruct m1; cbn.
    reflexivity.
  Qed.

  Definition Memory_fresh_sid (m : Memory) : (store_id * Memory)%type
    := let sid := Memory_sid_counter m in
       let sid' := N.succ sid in
       (sid', Memory_sid_modify m (fun _ => sid')).

  (** FIND_FREE *)
  Include (MEMORY_FIND_FREE_SPEC_IMPL ADDR SB AID).

  (** MEMORY_ALLOCATE *)
  Include (MEMORY_ALLOCATE_SPEC_IMPL ADDR SB AID).

  Definition find_free_block_exec
    (m : Memory) (len : nat) (aid : AllocationId) : OOM (addr * list addr)%type :=
    let mem_map := Memory_byte_map m in
    let addr := next_key mem_map in
    let pr := aid_to_prov aid in
    let md := metadata_set_provenance default_metadata pr in
    ptr <- int_to_ptr addr md;;
    match get_consecutive_ptrs ptr len with
    | inl msg => Oom msg
    | inr ptrs => ret (ptr, ptrs)
    end.

  #[global] Hint Unfold find_free_block_exec find_free_block : MEM.

  Lemma find_free_block_correct :
    forall m len aid ptrs,
      find_free_block_exec m len aid = NoOom ptrs ->
      find_free_block m len ptrs.
  Proof.
    intros m len aid ptrs FIND_FREE.
    autounfold with MEM in *.
    cbn in *.
    repeat break_match_hyp_inv.
    split;
      eauto with MEM.
    - (* New block was free *)
      (* Should follow from next_key *)
      cbn.
      apply Forall_forall.
      intros x IN aid' ALLOC.
      red in ALLOC.
      break_match_hyp; auto.
      destruct p as (b, baid).
      pose proof next_key_correct (Memory_byte_map m) (ptr_to_int x) as NEXT.
      forward NEXT.
      apply IP.F.find_mapsto_iff in Heqo0.
      eexists; apply Heqo0.
      eapply get_consecutive_ptrs_gt in Heqs; eauto.
      erewrite ptr_to_int_int_to_ptr with (a:=t0) in Heqs; eauto.
    - (* Block head *)
      intros ptr' ptrs' HEAD.
      cbn in *.
      subst; eauto with MEM.
    - (* Nothing is NULL *)
      apply Forall_forall.
      intros x IN.
      cbn in *.
      assert (ptr_to_int x > 0)%Z.
      {
        eapply get_consecutive_ptrs_gt in Heqs; eauto.
        erewrite ptr_to_int_int_to_ptr with (a:=t0) in Heqs; eauto.
        pose proof next_key_gt_0 (Memory_byte_map m).
        lia.
      }

      assert (ptr_to_int x <> 0)%Z by lia.
      destruct is_null eqn:NULL; auto.
      apply is_null_is_zero in NULL; contradiction.
    - (* New allocation is not null *)
      cbn.
      clear Heqs.
      assert (ptr_to_int t0 > 0)%Z.
      {
        erewrite ptr_to_int_int_to_ptr with (a:=t0); eauto.
        apply next_key_gt_0.
      }

      assert (ptr_to_int t0 <> 0)%Z by lia.
      destruct is_null eqn:NULL; auto.
      apply is_null_is_zero in NULL; contradiction.
  Qed.

  #[global] Hint Resolve find_free_block_correct : MEM.

  Lemma find_free_block_exec_aids :
    forall m len aid ptrs,
      find_free_block_exec m len aid = NoOom ptrs ->
      Forall (fun p => address_provenance p = aid_to_prov aid) (snd ptrs).
  Proof.
    intros m len aid ptrs FREE.
    unfold find_free_block_exec in FREE.
    cbn in *.
    repeat break_match_hyp_inv.
    cbn.
    eapply get_consecutive_ptrs_metadata in Heqs.
    apply Forall_forall.
    intros x IN.
    eapply Forall_forall in Heqs; eauto.
    unfold address_provenance.
    apply int_to_ptr_metadata in Heqo as H.
    rewrite Heqs.
    rewrite H.
    eauto with MEM.
  Qed.

  Lemma find_free_block_exec_access_allowed :
    forall m len aid ptrs,
      find_free_block_exec m len aid = NoOom ptrs ->
      Forall (fun p => access_allowed (address_provenance p) aid) (snd ptrs).
  Proof.
    intros m len aid ptrs FREE.
    apply find_free_block_exec_aids in FREE.
    apply Forall_forall.
    intros x H.
    eapply Forall_forall in FREE; eauto.
    rewrite FREE.
    apply access_allowed_refl.
  Qed.

  Fixpoint add_ptrs_to_byte_map (mem_byte : SByte * AllocationId) (ptrs : list addr) (mem : IM.t (SByte * AllocationId)) : IM.t (SByte * AllocationId)
    := match ptrs with
       | nil => mem
       | cons ptr ptrs => add_ptrs_to_byte_map mem_byte ptrs (IM.add (ptr_to_int ptr) mem_byte mem)
       end.

  Definition allocate_block_exec
    (m : Memory) (bytes : list SByte) (aid : AllocationId) : OOM (Memory * (addr * list addr))%type :=
    ptrs <- find_free_block_exec m (length bytes) aid;;
    let ptr_bytes := combine (map ptr_to_int (snd ptrs)) (map (fun b => (b, aid)) bytes) in
    (* Actually allocate pointers *)
    let m' := MkMemory (Memory_aid_counter m) (Memory_sid_counter m) (add_all ptr_bytes (Memory_byte_map m)) in
    ret (m', ptrs).

  #[global] Hint Unfold allocate_block allocate_block_exec : ALLOCATE_BLOCK.

  Lemma allocate_block_correct :
    forall m1 bytes aid m2 ptrs,
      allocate_block_exec m1 bytes aid = NoOom (m2, ptrs) ->
      allocate_block m1 bytes aid m2 ptrs.
  Proof.
    intros m1 bytes aid m2 ptrs ALLOC.
    autounfold with ALLOCATE_BLOCK in *.
    destruct (find_free_block_exec m1 (Datatypes.length bytes) aid) eqn:FIND_FREE;
      cbn in ALLOC; inv ALLOC.
    assert (find_free_block m1 (Datatypes.length bytes) ptrs) as FREE_SPEC; eauto with MEM.
    split;
      eauto with MEM.
    - (* New reads *)
      apply Forall2_forall.
      split; eauto with MEM.
      intros i a b H H0.
      red; cbn.
      erewrite find_in_add_all with (i:=i) (v:=(a, aid)).
      split; auto.
      3: {
        assert (list_values_injective (map ptr_to_int (snd ptrs))) by eauto with MEM.
        intros i' j' x NTH1 NTH2.
        apply nth_map_inv in NTH1, NTH2.
        destruct NTH1 as (?&?&?).
        destruct NTH2 as (?&?&?).
        destruct x0, x1; inv H3; inv H5.
        cbn in *; subst.
        apply nth_combine in H2, H4.
        destruct H2 as (?&?).
        destruct H4 as (?&?).
        eauto.
      }

      2: {
        apply nth_combine; split.
        - apply map_nth_error; auto.
        - change (a, aid) with ((fun b0 : SByte => (b0, aid)) a).
          apply map_nth_error; auto.
      }

      apply find_free_block_exec_access_allowed in FIND_FREE.
      eapply Forall_Nth in FIND_FREE; eauto.
    - (* Old reads *)
      intros b ptr H.
      red; cbn.
      (* The read should be disjoint from find_free_block_is_free *)
      erewrite find_nin_add_all.
      unfold read_byte in H; apply H.

      apply Forall_forall.
      intros [k v] IN.

      cbn in FIND_FREE.
      repeat break_match_hyp_inv.
      unfold read_byte in H.
      break_match_hyp; auto.
      destruct p.
      destruct H; subst.

      assert (IM.In (elt:=SByte * AllocationId) (ptr_to_int ptr) (Memory_byte_map m1)) as INM.
      { apply IP.F.find_mapsto_iff in Heqo0; eexists; eauto.
      }
      apply next_key_correct in INM.

      assert (k >= next_key (Memory_byte_map m1))%Z.
      { apply in_combine_l in IN; cbn in *.
        apply in_map_iff in IN as (?&?&?); subst.
        eapply get_consecutive_ptrs_gt in Heqs; eauto.
        erewrite ptr_to_int_int_to_ptr with (a:=t0) in Heqs; eauto.
      }
      lia.
    - (* Allocated *)
      apply Forall_forall.
      intros x IN.
      red; cbn.
      apply in_nth_error in IN as (n&NTH).
      assert (exists b, nth_error bytes n = Some b) as (b & NTHB).
      { assert (Datatypes.length bytes = Datatypes.length (snd ptrs)) as LEN by eauto with MEM.
        eapply nth_error_succeeds.
        apply nth_error_in in NTH.
        lia.
      }

      erewrite find_in_add_all with (i:=n) (v:=(b, aid)).
      + reflexivity.
      + apply nth_combine.
        split.
        * apply map_nth_error; auto.
        * change (b, aid) with ((fun b0 : SByte => (b0, aid)) b).
          apply map_nth_error; auto.
      + red.
        intros i j x0 H H0.
        apply nth_map_inv in H, H0.
        destruct H as (?&?&?).
        destruct H0 as (?&?&?).
        destruct x1, x2; cbn in *; subst.
        apply nth_combine in H, H0.
        destruct H as (?&?).
        destruct H0 as (?&?).
        repeat break_match_hyp_inv.
        eapply get_consecutive_ptrs_ptoi_injective; eauto.
    - (* Old allocated *)
      intros ptr ALLOC.
      { red; cbn.
        (* The read should be disjoint from find_free_block_is_free *)
        erewrite find_nin_add_all.
        unfold addr_allocated in ALLOC; auto.

        apply Forall_forall.
        intros [k v] IN.

        cbn in FIND_FREE.
        repeat break_match_hyp_inv.
        unfold addr_allocated in ALLOC.
        break_match_hyp; auto.
        destruct p.

        assert (IM.In (elt:=SByte * AllocationId) (ptr_to_int ptr) (Memory_byte_map m1)) as INM.
        { apply IP.F.find_mapsto_iff in Heqo0; eexists; eauto.
        }
        apply next_key_correct in INM.

        assert (k >= next_key (Memory_byte_map m1))%Z.
        { apply in_combine_l in IN; cbn in *.
          apply in_map_iff in IN as (?&?&?); subst.
          eapply get_consecutive_ptrs_gt in Heqs; eauto.
          erewrite ptr_to_int_int_to_ptr with (a:=t0) in Heqs; eauto.
        }
        lia.
      }
  Qed.

End INTMAP_AID_MEMORY_MODEL.

Module INTMAP_AID_FULL_MEMORY
  (MD : Typ)
  (PS : PROV_SET)
  (ADDR : ADDRESS MD PS)
  (AID : ALLOCATION_ID)
  (A : AID_PROVENANCE PS AID)
  (SB : SBYTE)
  (H : HEAP ADDR)
  (F : FRAME ADDR)
  (FS : FRAME_STACK ADDR F) <: FULL_MEMORY_MODEL ADDR SB AID H F FS.
  Module MEM := INTMAP_AID_MEMORY_MODEL MD PS ADDR AID A SB.
  Include (ALLOCATABLE_MEMORY_FRESH_TO_FULL_MEMORY_MODEL ADDR SB AID H F FS MEM).
End INTMAP_AID_FULL_MEMORY.

(* Module NAT_SBYTE <: SBYTE. *)
(*   Definition SByte := (nat * N)%type. *)
(*   Definition sbyte_sid (b : SByte) := snd b. *)
(* End NAT_SBYTE. *)

(* Module Z_ADDR <: CORE_ADDRESS. *)
(*   Include BinInt.Z. *)
(*   Notation addr := t. *)
(* End Z_ADDR. *)

(* Module CORE_INT_MEM <: CORE_MEMORY_MODEL Z_ADDR NAT_SBYTE. *)
(*   Import Z_ADDR. *)
(*   Import NAT_SBYTE. *)
(*   Require Import IntMaps. *)
(*   Definition Memory := IntMap SByte. *)
(*   Definition initial_memory := @IM.empty SByte. *)

(*   Definition read_byte {M} `{HM : Monad M} `{SM : SpecM M} *)
(*     (m : Memory) (ptr : addr) : M SByte := *)
(*     match IM.find ptr m with *)
(*     | None => empty_spec *)
(*     | Some b => ret b *)
(*     end. *)
(* End CORE_INT_MEM. *)
