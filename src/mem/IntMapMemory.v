(*** Memory model implementations using intmaps *)
From Coq Require Import
  ZArith
  String
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

From Coq Require Import
  List.

Notation err := (sum string).

(** Memory models based on integer maps *)
Module INTMAP_MEMORY_MODEL_BASE (ADDR : CORE_ADDRESS) (PTOI : HAS_PTOI ADDR) (SB : SBYTE) <: MEMORY_MODEL_BASE ADDR SB.
  Import ADDR.
  Import SB.

  Definition Memory := IM.t SByte.
  Definition initial_memory := @IM.empty SByte.
End INTMAP_MEMORY_MODEL_BASE.

Module INTMAP_MEMORY_MODEL_CORE (ADDR : CORE_ADDRESS) (PTOI : HAS_PTOI ADDR) (SB : SBYTE) <: CORE_MEMORY_MODEL ADDR SB.
  Import ADDR.
  Import SB.

  Include (INTMAP_MEMORY_MODEL_BASE ADDR PTOI SB).

  Definition read_byte (m : Memory) (ptr : addr) (b : SByte) : Prop :=
    match IM.find (PTOI.ptr_to_int ptr) m with
    | None => False
    | Some b' => b = b'
    end.

  Definition read_byte_exec (m : Memory) (ptr : addr) : option SByte :=
    IM.find (PTOI.ptr_to_int ptr) m.
End INTMAP_MEMORY_MODEL_CORE.

(** Memory models based on integer maps with allocation ids *)
Module INTMAP_AID_MEMORY_MODEL
  (MD : Typ)
  (PS : PROV_SET)
  (Import ADDR : PROVENANCE_ADDRESS MD PS)
  (Import AID : ALLOCATION_ID)
  (Import A : ACCESS PS AID)
  (Import SB : SBYTE) <: ALLOCATABLE_MEMORY_FRESH ADDR SB AID.

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

  (** FIND_FREE *)
  Include (MEMORY_FIND_FREE ADDR SB AID).

  (** MEMORY_ALLOCATE *)
  Include (MEMORY_ALLOCATE ADDR SB AID).

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
End INTMAP_AID_MEMORY_MODEL.

Module INTMAP_AID_FULL_MEMORY
  (MD : Typ)
  (PS : PROV_SET)
  (ADDR : PROVENANCE_ADDRESS MD PS)
  (AID : ALLOCATION_ID)
  (A : ACCESS PS AID)
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

