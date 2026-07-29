(** * I2F invariant for the memory model, restricted to the memM monad *)

From Equations Require Import Equations.

From Stdlib Require Import
  ZArith
  Strings.String
  List
  Morphisms.
Import ListNotations.

From ITree Require Import Basics.HeterogeneousRelations.

From Vellvm Require Import
  Utils
  Syntax
  Semantics
  VellvmIntegers
  Integers
  Interfaces.IPtr
  Interfaces.Params
  Interfaces.Pointer
  Implementations.Pointer
  Implementations.Provenance
  Implementations.IPtrInfinite
  Implementations.IPtrFinite
  Implementations.Memory
  Implementations.ParamsV
  Interfaces.Memory.

From Vellvm Require Import
  Handlers.Memory.

From Vellvm Require Import
  Theory.I2F.Refinement
  Theory.I2F.I2F_exp
  Theory.I2F.I2F_memS.

Existing Instance MemoryModelStateV.
Existing Instance MemoryModelPrimitivesV.

(** * Relating [ptr]/[EOU] operations underlying the memory model

    Pure facts about pointers and [EOU]-valued primitives (address
    creation, sequences of intptrs, integer coercions) that the state-ful
    lemmas below build on. *)

Lemma I2F_Addr_ptr_to_int : forall (p : @ptr (@PROV PInf) (@PTR PInf)) (p' : @ptr (@PROV PFin) (@PTR PFin)),
    I2F_Addr p p' -> @ptr_to_int _ _ (@P2I PInf) p = @ptr_to_int _ _ (@P2I PFin) p'.
Proof.
  intros [z pr] [i pr'] [HI ->]; cbn; red in HI; auto.
Qed.

Lemma I2F_from_Z : forall z, I2F_EOU I2F_Iptr (@from_Z IPZ z) (@from_Z IP64Bit z).
Proof.
  intros z; cbn; unfold from_Z_bits.
  destruct ((z <=? @Integers.max_unsigned 64) && (z >=? 0))%Z eqn:RANGE.
  - constructor.
    red.
    apply andb_prop in RANGE as [LE GE].
    apply Z.leb_le in LE; apply Z.geb_le in GE.
    symmetry; apply Integers.unsigned_repr.
    unfold Integers.max_unsigned in *; lia.
  - constructor.
Qed.

Lemma I2F_int_to_ptr : forall z pr,
    I2F_EOU I2F_Addr (@int_to_ptr _ _ (@PIV IPZ) z pr) (@int_to_ptr _ _ (@PIV IP64Bit) z pr).
Proof.
  intros z pr.
  eapply I2F_EOU_bind; [apply I2F_from_Z |].
  intros a1 a2 Ha; constructor; auto.
Qed.

(** [intptr_seq] traverses the SAME (Params-independent) index list on
    both sides: a single-list [map_monad] compatibility suffices. *)
Lemma I2F_intptr_seq : forall start size,
    I2F_EOU (Forall2 I2F_Iptr) (@intptr_seq IPZ start size) (@intptr_seq IP64Bit start size).
Proof.
  intros start size; unfold intptr_seq.
  rewrite 2 seq_map_monad_acc_eq.
  apply I2F_EOU_map_monad.
  intros a _; apply I2F_from_Z.
Qed.

Lemma I2F_get_consecutive_ptrs : forall p p',
    I2F_Addr p p' ->
    forall n,
      I2F_EOU (Forall2 I2F_Addr)
        (@get_consecutive_ptrs PInf p n)
        (@get_consecutive_ptrs PFin p' n).
Proof.
  intros p p' Hp n; unfold get_consecutive_ptrs.
  eapply I2F_EOU_bind; [apply I2F_intptr_seq |].
  intros ixs1 ixs2 HIXS.
  eapply I2F_EOU_map_monad_acc2; eauto.
  intros ix1 ix2 Hix.
  apply I2F_handle_gep_ptr; auto.
Qed.

Lemma I2F_coerce_integer_to_int : forall b z,
    I2F_EOU I2F_dvalue_base (@coerce_integer_to_int PInf b z) (@coerce_integer_to_int PFin b z).
Proof.
  intros [sz|] z; unfold coerce_integer_to_int.
  - repeat constructor.
  - eapply I2F_EOU_bind; [apply I2F_from_Z |].
    intros i1 i2 Hi; repeat constructor; auto.
Qed.

Lemma I2F_no_overlap : forall (a1 a2 : @ptr (@PROV PInf) (@PTR PInf)) sz1
                              (a1' a2' : @ptr (@PROV PFin) (@PTR PFin)) sz2,
    I2F_Addr a1 a1' -> I2F_Addr a2 a2' ->
    @no_overlap _ _ (@overlaps_ptoi _ _ (@P2I PInf)) a1 sz1 a2 sz2 =
    @no_overlap _ _ (@overlaps_ptoi _ _ (@P2I PFin)) a1' sz1 a2' sz2.
Proof.
  intros [z1 pr1] [z2 pr2] sz1 [i1 pr1'] [i2 pr2'] sz2 [HI1 ->] [HI2 ->].
  red in HI1, HI2; subst.
  reflexivity.
Qed.

Lemma I2F_mbyte_MByte : forall dv dv' dt idx,
    I2F_dvalue dv dv' -> I2F_mbyte (MByte dv dt idx) (MByte dv' dt idx).
Proof.
  intros dv dv' dt idx H; red; cbn.
  now apply I2F_dvalue_extract_byte.
Qed.

Lemma generate_num_poison_bytes_h_0 {Pa : Params} (dt : dtyp) (start : N) :
  generate_num_poison_bytes_h start 0 dt = [].
Proof. reflexivity. Qed.

Lemma generate_num_poison_bytes_h_succ {Pa : Params} (dt : dtyp) (start num : N) :
  generate_num_poison_bytes_h start (N.succ num) dt =
  MByte (DVALUE_Poison dt) dt start :: generate_num_poison_bytes_h (N.succ start) num dt.
Proof.
  unfold generate_num_poison_bytes_h.
  rewrite !seq_map_acc_eq, !N_to_nat_safe_eq, Nnat.N2Nat.inj_succ.
  cbn [Nseq map]; reflexivity.
Qed.

Lemma I2F_generate_num_poison_bytes_h : forall start num dt,
    Forall2 I2F_mbyte
      (@generate_num_poison_bytes_h PInf start num dt)
      (@generate_num_poison_bytes_h PFin start num dt).
Proof.
  intros start num; revert start; induction num using N.peano_ind; intros start dt.
  - rewrite 2 generate_num_poison_bytes_h_0; constructor.
  - rewrite 2 generate_num_poison_bytes_h_succ.
    constructor; auto.
    apply I2F_mbyte_MByte; repeat constructor.
Qed.

Lemma I2F_generate_num_poison_bytes : forall num dt,
    Forall2 I2F_mbyte
      (@generate_num_poison_bytes PInf num dt)
      (@generate_num_poison_bytes PFin num dt).
Proof.
  intros; apply I2F_generate_num_poison_bytes_h.
Qed.

Lemma I2F_generate_poison_bytes : forall dt,
    Forall2 I2F_mbyte
      (@generate_poison_bytes PInf dt)
      (@generate_poison_bytes PFin dt).
Proof.
  intros; unfold generate_poison_bytes.
  rewrite I2F_sizeof_dtyp.
  apply I2F_generate_num_poison_bytes.
Qed.

(** * State relation

    Componentwise relation on the concrete implementation's memory
    state: memories are related as [IM_Refine]-related maps of
    [I2F_byte]-related bytes, framestacks structurally, heaps as
    [IM_Refine]-related maps of [I2F_Addr]-related pointer lists,
    and provenances equal. *)

Definition I2F_byte (b : @byte PInf) (b' : @byte PFin) : Prop :=
  let '(mb, aid) := b in
  let '(mb', aid') := b' in
  I2F_mbyte mb mb' /\ aid = aid'.

Definition I2F_memory : @memory PInf -> @memory PFin -> Prop := IM_Refine I2F_byte.

Definition I2F_Frame : @Frame PInf -> @Frame PFin -> Prop := Forall2 I2F_Addr.

Inductive I2F_Framestack : @Framestack PInf -> @Framestack PFin -> Prop :=
| I2F_FS_Singleton f f' : I2F_Frame f f' -> I2F_Framestack (Singleton f) (Singleton f')
| I2F_FS_Snoc s s' f f' :
  I2F_Framestack s s' -> I2F_Frame f f' -> I2F_Framestack (Snoc s f) (Snoc s' f')
.

Definition I2F_Heap : @Heap PInf -> @Heap PFin -> Prop := IM_Refine (Forall2 I2F_Addr).

Record I2F_Memory_stack (ms : @Memory_stack PInf) (ms' : @Memory_stack PFin) : Prop :=
  { i2f_ms_memory : I2F_memory (Memory_stack_memory ms) (Memory_stack_memory ms');
    i2f_ms_fs     : I2F_Framestack (Memory_stack_frame_stack ms) (Memory_stack_frame_stack ms');
    i2f_ms_heap   : I2F_Heap (Memory_stack_heap ms) (Memory_stack_heap ms')
  }.

Record I2F_State (σ : @State PInf) (σ' : @State PFin) : Prop :=
  { i2f_st_ms   : I2F_Memory_stack (state_memory_stack σ) (state_memory_stack σ');
    i2f_st_prov : state_provenance σ = state_provenance σ'
  }.

(** ** [IM_Refine]/map-operation corollaries *)

Lemma I2F_next_key_with_alignment : forall m1 m2,
    I2F_memory m1 m2 ->
    forall align, next_key_with_alignment m1 align = next_key_with_alignment m2 align.
Proof.
  intros m1 m2 [DOM _] align.
  unfold next_key_with_alignment.
  rewrite (IM_greatest_key_morph _ _ DOM).
  reflexivity.
Qed.

Lemma I2F_free_frame_memory : forall f f',
    I2F_Frame f f' ->
    forall m1 m2, I2F_memory m1 m2 ->
    I2F_memory (@free_frame_memory PInf f m1) (@free_frame_memory PFin f' m2).
Proof.
  intros f f' HF; induction HF as [| [z pr] [i pr'] fs fs' [HI ->] HF' IH];
    intros m1 m2 Hm; [cbn; auto|].
  red in HI; subst.
  cbn [free_frame_memory fold_left free_byte] in *.
  apply IH.
  apply IM_Refine_remove; auto.
Qed.

Lemma I2F_free_block_memory : forall b b',
    Forall2 I2F_Addr b b' ->
    forall m1 m2, I2F_memory m1 m2 ->
    I2F_memory (@free_block_memory PInf b m1) (@free_block_memory PFin b' m2).
Proof.
  intros b b' HB; induction HB as [| [z pr] [i pr'] bs bs' [HI ->] HB' IH];
    intros m1 m2 Hm; [cbn; auto|].
  red in HI; subst.
  cbn [free_block_memory fold_left free_byte] in *.
  apply IH.
  apply IM_Refine_remove; auto.
Qed.

Lemma I2F_add_to_frame : forall ms1 ms2,
    I2F_Memory_stack ms1 ms2 ->
    forall (k1 : @ptr (@PROV PInf) (@PTR PInf)) (k2 : @ptr (@PROV PFin) (@PTR PFin)),
      I2F_Addr k1 k2 ->
    I2F_Memory_stack (@add_to_frame PInf ms1 k1) (@add_to_frame PFin ms2 k2).
Proof.
  intros [m1 s1 h1] [m2 s2 h2] [Hmem Hfs Hheap] k1 k2 Hk; cbn in *.
  destruct Hfs as [f f' Hf | s s' f f' Hs Hf].
  - constructor; cbn.
    + auto.
    + apply I2F_FS_Singleton; constructor; auto.
    + auto.
  - constructor; cbn.
    + auto.
    + apply I2F_FS_Snoc; auto; constructor; auto.
    + auto.
Qed.

Lemma I2F_add_all_to_frame : forall (ks1 : list (@ptr (@PROV PInf) (@PTR PInf)))
                                    (ks2 : list (@ptr (@PROV PFin) (@PTR PFin))),
    Forall2 I2F_Addr ks1 ks2 ->
    forall ms1 ms2, I2F_Memory_stack ms1 ms2 ->
    I2F_Memory_stack (@add_all_to_frame PInf ks1 ms1) (@add_all_to_frame PFin ks2 ms2).
Proof.
  intros ks1 ks2 HK; induction HK; intros ms1 ms2 Hms; cbn; auto.
  apply IHHK, I2F_add_to_frame; auto.
Qed.

Lemma I2F_add_to_heap : forall ms1 ms2,
    I2F_Memory_stack ms1 ms2 ->
    forall (root1 : @ptr (@PROV PInf) (@PTR PInf)) (root2 : @ptr (@PROV PFin) (@PTR PFin)),
      I2F_Addr root1 root2 ->
    forall (p1 : @ptr (@PROV PInf) (@PTR PInf)) (p2 : @ptr (@PROV PFin) (@PTR PFin)),
      I2F_Addr p1 p2 ->
    I2F_Memory_stack (@add_to_heap PInf ms1 root1 p1) (@add_to_heap PFin ms2 root2 p2).
Proof.
  intros [m1 s1 h1] [m2 s2 h2] [Hmem Hfs Hheap]
    [z pr] [i pr'] Hroot p1 p2 Hp; cbn in *.
  destruct Hroot as [HI ->]; red in HI; subst.
  unfold add_to_heap, add_with; cbn.
  constructor.
  - auto.
  - auto.
  - cbn.
    destruct Hheap as [DOM VAL].
    lazymatch goal with
    | |- I2F_Heap match ?e1 with Some _ => _ | None => _ end match ?e2 with Some _ => _ | None => _ end =>
        destruct e1 as [l1|] eqn:E1; destruct e2 as [l2|] eqn:E2
    end.
    + assert (HL : Forall2 I2F_Addr l1 l2) by (eapply VAL; eauto).
      apply IM_Refine_add; [exact (conj DOM VAL) | constructor; auto].
    + exfalso.
      apply lookup_member in E1; apply DOM in E1; apply member_lookup in E1 as [v Hv].
      assert (Hcontra : Some v = None)
        by (transitivity (lookup (unsigned i) h2); [symmetry; exact Hv | exact E2]).
      discriminate.
    + exfalso.
      apply lookup_member in E2; apply DOM in E2; apply member_lookup in E2 as [v Hv].
      assert (Hcontra : Some v = None)
        by (transitivity (lookup (unsigned i) h1); [symmetry; exact Hv | exact E1]).
      discriminate.
    + apply IM_Refine_add; [exact (conj DOM VAL) | constructor; auto].
Qed.

Lemma I2F_add_all_to_heap' : forall ms1 ms2,
    I2F_Memory_stack ms1 ms2 ->
    forall (root1 : @ptr (@PROV PInf) (@PTR PInf)) (root2 : @ptr (@PROV PFin) (@PTR PFin)),
      I2F_Addr root1 root2 ->
    forall (ks1 : list (@ptr (@PROV PInf) (@PTR PInf))) (ks2 : list (@ptr (@PROV PFin) (@PTR PFin))),
      Forall2 I2F_Addr ks1 ks2 ->
    I2F_Memory_stack (@add_all_to_heap' PInf ms1 root1 ks1) (@add_all_to_heap' PFin ms2 root2 ks2).
Proof.
  intros ms1 ms2 Hms root1 root2 Hroot ks1 ks2 HK; revert ms1 ms2 Hms.
  induction HK; intros ms1 ms2 Hms; cbn; auto.
  apply IHHK, I2F_add_to_heap; auto.
Qed.

Lemma I2F_add_all_to_heap : forall (ks1 : list (@ptr (@PROV PInf) (@PTR PInf)))
                                   (ks2 : list (@ptr (@PROV PFin) (@PTR PFin))),
    Forall2 I2F_Addr ks1 ks2 ->
    forall ms1 ms2, I2F_Memory_stack ms1 ms2 ->
    I2F_Memory_stack (@add_all_to_heap PInf ks1 ms1) (@add_all_to_heap PFin ks2 ms2).
Proof.
  intros ks1 ks2 HK; destruct HK as [| k1 k2 ks1 ks2 Hk HK]; intros ms1 ms2 Hms;
    cbn [add_all_to_heap].
  - auto.
  - apply I2F_add_all_to_heap'; auto.
Qed.

(** ** Accessor pack *)

Lemma I2F_get_mem : I2F_memS I2F_State I2F_memory get_mem get_mem.
Proof.
  unfold get_mem.
  eapply I2F_memS_bind; [apply I2F_memS_get |].
  intros σ1 σ2 [[Hmem Hfs Hheap] Hprov]; cbn.
  constructor; exact Hmem.
Qed.

Lemma I2F_get_frame_stack : I2F_memS I2F_State I2F_Framestack get_frame_stack get_frame_stack.
Proof.
  unfold get_frame_stack.
  eapply I2F_memS_bind; [apply I2F_memS_get |].
  intros σ1 σ2 [[Hmem Hfs Hheap] Hprov]; cbn.
  constructor; exact Hfs.
Qed.

Lemma I2F_get_framestack : I2F_memS I2F_State I2F_Framestack get_framestack get_framestack.
Proof.
  unfold get_framestack.
  eapply I2F_memS_bind; [apply I2F_memS_get |].
  intros σ1 σ2 [[Hmem Hfs Hheap] Hprov]; cbn.
  constructor; exact Hfs.
Qed.

Lemma I2F_get_frame : I2F_memS I2F_State I2F_Frame get_frame get_frame.
Proof.
  unfold get_frame.
  eapply I2F_memS_bind; [apply I2F_get_frame_stack |].
  intros fs1 fs2 Hfs.
  destruct Hfs as [f f' Hf | s s' f f' Hs Hf]; constructor; auto.
Qed.

Lemma I2F_get_heap : I2F_memS I2F_State I2F_Heap get_heap get_heap.
Proof.
  unfold get_heap.
  eapply I2F_memS_bind; [apply I2F_memS_get |].
  intros σ1 σ2 [[Hmem Hfs Hheap] Hprov]; cbn.
  constructor; exact Hheap.
Qed.

Lemma I2F_app_mem_stack : forall f1 f2,
    (forall ms1 ms2, I2F_Memory_stack ms1 ms2 -> I2F_Memory_stack (f1 ms1) (f2 ms2)) ->
    I2F_memS I2F_State (fun (_ _ : unit) => True) (app_mem_stack f1) (app_mem_stack f2).
Proof.
  intros f1 f2 Hf; unfold app_mem_stack.
  eapply I2F_memS_bind; [apply I2F_memS_get |].
  intros [ms1 pv1] [ms2 pv2] [Hms Hprov]; cbn in *.
  apply I2F_memS_put; auto.
  constructor; cbn; auto.
Qed.

Lemma I2F_app_mem : forall f1 f2,
    (forall m1 m2, I2F_memory m1 m2 -> I2F_memory (f1 m1) (f2 m2)) ->
    I2F_memS I2F_State (fun (_ _ : unit) => True) (app_mem f1) (app_mem f2).
Proof.
  intros f1 f2 Hf; unfold app_mem.
  eapply I2F_memS_bind; [apply I2F_memS_get |].
  intros [[m1 s1 h1] pv1] [[m2 s2 h2] pv2] [[Hmem Hfs Hheap] Hprov]; cbn in *.
  apply I2F_memS_put.
  constructor; cbn.
  - constructor; cbn; auto.
  - auto.
Qed.

Lemma I2F_app_heap : forall f1 f2,
    (forall h1 h2, I2F_Heap h1 h2 -> I2F_Heap (f1 h1) (f2 h2)) ->
    I2F_memS I2F_State (fun (_ _ : unit) => True) (app_heap f1) (app_heap f2).
Proof.
  intros f1 f2 Hf; unfold app_heap.
  eapply I2F_memS_bind; [apply I2F_memS_get |].
  intros [[m1 s1 h1] pv1] [[m2 s2 h2] pv2] [[Hmem Hfs Hheap] Hprov]; cbn in *.
  apply I2F_memS_put.
  constructor; cbn.
  - constructor; cbn; auto.
  - auto.
Qed.

Lemma I2F_app_frame_stack : forall f1 f2,
    (forall fs1 fs2, I2F_Framestack fs1 fs2 -> I2F_Framestack (f1 fs1) (f2 fs2)) ->
    I2F_memS I2F_State (fun (_ _ : unit) => True) (app_frame_stack f1) (app_frame_stack f2).
Proof.
  intros f1 f2 Hf; unfold app_frame_stack.
  eapply I2F_memS_bind; [apply I2F_memS_get |].
  intros [[m1 s1 h1] pv1] [[m2 s2 h2] pv2] [[Hmem Hfs Hheap] Hprov]; cbn in *.
  apply I2F_memS_put.
  constructor; cbn.
  - constructor; cbn; auto.
  - auto.
Qed.

Lemma I2F_upd_mem : forall m1 m2,
    I2F_memory m1 m2 ->
    I2F_memS I2F_State (fun (_ _ : unit) => True) (upd_mem m1) (upd_mem m2).
Proof. intros; apply I2F_app_mem; auto. Qed.

Lemma I2F_upd_heap : forall h1 h2,
    I2F_Heap h1 h2 ->
    I2F_memS I2F_State (fun (_ _ : unit) => True) (upd_heap h1) (upd_heap h2).
Proof. intros; apply I2F_app_heap; auto. Qed.

Lemma I2F_upd_frame_stack : forall fs1 fs2,
    I2F_Framestack fs1 fs2 ->
    I2F_memS I2F_State (fun (_ _ : unit) => True) (upd_frame_stack fs1) (upd_frame_stack fs2).
Proof. intros; apply I2F_app_frame_stack; auto. Qed.

Lemma I2F_pop_frame_stack : forall fs1 fs2,
    I2F_Framestack fs1 fs2 ->
    I2F_EOU I2F_Framestack (pop_frame_stack fs1) (pop_frame_stack fs2).
Proof.
  intros fs1 fs2 Hfs; destruct Hfs as [f f' Hf | s s' f f' Hs Hf]; cbn.
  - constructor.
  - constructor; auto.
Qed.

Lemma I2F_app_frame_stack_eob : I2F_memS I2F_State (fun (_ _ : unit) => True)
    (app_frame_stack_eob pop_frame_stack) (app_frame_stack_eob pop_frame_stack).
Proof.
  unfold app_frame_stack_eob.
  eapply I2F_memS_bind; [apply I2F_get_framestack |].
  intros fs1 fs2 Hfs.
  eapply I2F_memS_bind; [apply I2F_memS_lift, I2F_pop_frame_stack; auto |].
  intros fs1' fs2' Hfs'.
  apply I2F_upd_frame_stack; auto.
Qed.

(** ** Primitives *)

Lemma I2F_read_byte_raw : forall msg addr,
    I2F_memS I2F_State I2F_byte
      (read_byte_raw msg addr)
      (read_byte_raw msg addr).
Proof.
  intros msg addr; unfold read_byte_raw, read_byte_raw_mem.
  eapply I2F_memS_bind; [apply I2F_memS_get |].
  intros [[m1 s1 h1] pv1] [[m2 s2 h2] pv2] [[Hmem Hfs Hheap] Hprov]; cbn in *.
  lazymatch goal with
  | |- I2F_memS I2F_State I2F_byte
        match ?e1 with Some _ => _ | None => _ end
        match ?e2 with Some _ => _ | None => _ end =>
      destruct e1 as [b1|] eqn:E1; destruct e2 as [b2|] eqn:E2
  end.
  - constructor; eapply Hmem; eauto.
  - exfalso.
    destruct Hmem as [DOM VAL].
    apply lookup_member in E1; apply DOM in E1; apply member_lookup in E1 as [v Hv].
    assert (Hcontra : Some v = None)
      by (transitivity (lookup addr m2); [symmetry; exact Hv | exact E2]).
    discriminate.
  - exfalso.
    destruct Hmem as [DOM VAL].
    apply lookup_member in E2; apply DOM in E2; apply member_lookup in E2 as [v Hv].
    assert (Hcontra : Some v = None)
      by (transitivity (lookup addr m1); [symmetry; exact Hv | exact E1]).
    discriminate.
  - constructor.
Qed.

Lemma I2F_set_byte_raw : forall addr b1 b2,
    I2F_byte b1 b2 ->
    I2F_memS I2F_State (fun (_ _ : unit) => True) (set_byte_raw addr b1) (set_byte_raw addr b2).
Proof.
  intros addr b1 b2 Hb; unfold set_byte_raw.
  eapply I2F_memS_bind; [apply I2F_get_mem |].
  intros m1 m2 Hm.
  apply I2F_upd_mem.
  unfold set_byte_raw_mem.
  apply IM_Refine_add; auto.
Qed.

Lemma I2F_Read_byte : forall (p1 : @ptr (@PROV PInf) (@PTR PInf)) (p2 : @ptr (@PROV PFin) (@PTR PFin)),
    I2F_Addr p1 p2 ->
    I2F_memS I2F_State I2F_mbyte (Read_byte p1) (Read_byte p2).
Proof.
  intros [z1 pr1] [z2 pr2] Hp; unfold Read_byte.
  destruct Hp as [HI ->]; red in HI; subst.
  eapply I2F_memS_bind; [apply I2F_read_byte_raw |].
  intros [b1 aid1] [b2 aid2] [Hb Haid]; cbn.
  rewrite Haid.
  lazymatch goal with
  | |- I2F_memS _ _ (if ?c then _ else _) (if ?c then _ else _) => destruct c
  end.
  - constructor; auto.
  - constructor.
Qed.

Lemma I2F_Write_byte : forall (p1 : @ptr (@PROV PInf) (@PTR PInf)) (p2 : @ptr (@PROV PFin) (@PTR PFin)),
    I2F_Addr p1 p2 ->
    forall b1 b2, I2F_mbyte b1 b2 ->
    I2F_memS I2F_State (fun (_ _ : unit) => True) (Write_byte p1 b1) (Write_byte p2 b2).
Proof.
  intros [z1 pr1] [z2 pr2] Hp b1 b2 Hb; unfold Write_byte.
  destruct Hp as [HI ->]; red in HI; subst.
  eapply I2F_memS_bind; [apply I2F_read_byte_raw |].
  intros [b1' aid1] [b2' aid2] [Hb' Haid]; cbn.
  rewrite Haid.
  lazymatch goal with
  | |- I2F_memS _ _ (if ?c then _ else _) (if ?c then _ else _) => destruct c
  end.
  - apply I2F_set_byte_raw; split; auto.
  - constructor.
Qed.

Lemma I2F_get_free_block : forall size align pr,
    I2F_memS I2F_State (prod_rel I2F_Addr (Forall2 I2F_Addr))
      (@get_free_block PInf size align pr) (@get_free_block PFin size align pr).
Proof.
  intros size align pr; unfold get_free_block.
  eapply I2F_memS_bind; [apply I2F_memS_next_key |].
  intros addr1 addr2 ->.
  eapply I2F_memS_bind; [apply I2F_memS_lift, I2F_int_to_ptr |].
  intros ptr1 ptr2 Hptr.
  eapply I2F_memS_bind; [apply I2F_memS_lift, I2F_get_consecutive_ptrs; auto |].
  intros ptrs1 ptrs2 Hptrs.
  constructor; constructor; auto.
Qed.

Lemma I2F_memory_bytes_to_bytes : forall aid
    (bytes1 : list (@memory_byte PInf)) (bytes2 : list (@memory_byte PFin)),
    Forall2 I2F_mbyte bytes1 bytes2 ->
    Forall2 I2F_byte (@memory_bytes_to_bytes PInf aid bytes1) (@memory_bytes_to_bytes PFin aid bytes2).
Proof.
  intros aid bytes1 bytes2 H; unfold memory_bytes_to_bytes; rewrite !map_acc_eq.
  induction H; cbn; constructor; auto.
  split; auto.
Qed.

Lemma I2F_add_block : forall aid (p1 : @ptr (@PROV PInf) (@PTR PInf)) (p2 : @ptr (@PROV PFin) (@PTR PFin)),
    I2F_Addr p1 p2 ->
    forall (ptrs1 : list (@ptr (@PROV PInf) (@PTR PInf))) (ptrs2 : list (@ptr (@PROV PFin) (@PTR PFin)))
           (bytes1 : list (@memory_byte PInf)) (bytes2 : list (@memory_byte PFin)),
      Forall2 I2F_mbyte bytes1 bytes2 ->
    I2F_memS I2F_State (fun (_ _ : unit) => True)
      (@add_block PInf aid p1 ptrs1 bytes1) (@add_block PFin aid p2 ptrs2 bytes2).
Proof.
  intros aid p1 p2 Hp ptrs1 ptrs2 bytes1 bytes2 Hbytes; unfold add_block.
  destruct p1 as [z1 pr1]; destruct p2 as [z2 pr2].
  destruct Hp as [HI ->]; red in HI; subst.
  eapply I2F_memS_bind; [apply I2F_get_mem |].
  intros m1 m2 Hm.
  apply I2F_upd_mem.
  apply IM_Refine_add_all_index_acc; auto.
  apply I2F_memory_bytes_to_bytes; auto.
Qed.

Lemma I2F_add_ptrs_to_frame :
    forall (ptrs1 : list (@ptr (@PROV PInf) (@PTR PInf))) (ptrs2 : list (@ptr (@PROV PFin) (@PTR PFin))),
    Forall2 I2F_Addr ptrs1 ptrs2 ->
    I2F_memS I2F_State (fun (_ _ : unit) => True)
      (@add_ptrs_to_frame PInf ptrs1) (@add_ptrs_to_frame PFin ptrs2).
Proof.
  intros ptrs1 ptrs2 Hptrs; unfold add_ptrs_to_frame.
  apply I2F_app_mem_stack.
  intros ms1 ms2 Hms; apply I2F_add_all_to_frame; auto.
Qed.

Lemma I2F_add_ptrs_to_heap :
    forall (ptrs1 : list (@ptr (@PROV PInf) (@PTR PInf))) (ptrs2 : list (@ptr (@PROV PFin) (@PTR PFin))),
    Forall2 I2F_Addr ptrs1 ptrs2 ->
    I2F_memS I2F_State (fun (_ _ : unit) => True)
      (@add_ptrs_to_heap PInf ptrs1) (@add_ptrs_to_heap PFin ptrs2).
Proof.
  intros ptrs1 ptrs2 Hptrs; unfold add_ptrs_to_heap.
  apply I2F_app_mem_stack.
  intros ms1 ms2 Hms; apply I2F_add_all_to_heap; auto.
Qed.

Lemma I2F_add_block_to_stack : forall aid (p1 : @ptr (@PROV PInf) (@PTR PInf)) (p2 : @ptr (@PROV PFin) (@PTR PFin)),
    I2F_Addr p1 p2 ->
    forall (ptrs1 : list (@ptr (@PROV PInf) (@PTR PInf))) (ptrs2 : list (@ptr (@PROV PFin) (@PTR PFin))),
      Forall2 I2F_Addr ptrs1 ptrs2 ->
    forall (bytes1 : list (@memory_byte PInf)) (bytes2 : list (@memory_byte PFin)),
      Forall2 I2F_mbyte bytes1 bytes2 ->
    I2F_memS I2F_State (fun (_ _ : unit) => True)
      (@add_block_to_stack PInf aid p1 ptrs1 bytes1) (@add_block_to_stack PFin aid p2 ptrs2 bytes2).
Proof.
  intros aid p1 p2 Hp ptrs1 ptrs2 Hptrs bytes1 bytes2 Hbytes; unfold add_block_to_stack.
  eapply I2F_memS_bind; [apply I2F_add_block; auto |].
  intros _ _ _; apply I2F_add_ptrs_to_frame; auto.
Qed.

Lemma I2F_add_block_to_heap : forall aid (p1 : @ptr (@PROV PInf) (@PTR PInf)) (p2 : @ptr (@PROV PFin) (@PTR PFin)),
    I2F_Addr p1 p2 ->
    forall (ptrs1 : list (@ptr (@PROV PInf) (@PTR PInf))) (ptrs2 : list (@ptr (@PROV PFin) (@PTR PFin))),
      Forall2 I2F_Addr ptrs1 ptrs2 ->
    forall (bytes1 : list (@memory_byte PInf)) (bytes2 : list (@memory_byte PFin)),
      Forall2 I2F_mbyte bytes1 bytes2 ->
    I2F_memS I2F_State (fun (_ _ : unit) => True)
      (@add_block_to_heap PInf aid p1 ptrs1 bytes1) (@add_block_to_heap PFin aid p2 ptrs2 bytes2).
Proof.
  intros aid p1 p2 Hp ptrs1 ptrs2 Hptrs bytes1 bytes2 Hbytes; unfold add_block_to_heap.
  eapply I2F_memS_bind; [apply I2F_add_block; auto |].
  intros _ _ _; apply I2F_add_ptrs_to_heap; auto.
Qed.

Lemma I2F_Allocate_bytes_with_pr : forall
    (init_bytes1 : list (@memory_byte PInf)) (init_bytes2 : list (@memory_byte PFin)),
    Forall2 I2F_mbyte init_bytes1 init_bytes2 ->
    forall align pr,
    I2F_memS I2F_State I2F_Addr
      (@Allocate_bytes_with_pr PInf init_bytes1 align pr)
      (@Allocate_bytes_with_pr PFin init_bytes2 align pr).
Proof.
  intros init_bytes1 init_bytes2 Hbytes align pr; unfold Allocate_bytes_with_pr.
  rewrite !N_length_eq, (Forall2_length_N Hbytes).
  eapply I2F_memS_bind; [apply I2F_get_free_block |].
  intros [ptr1 ptrs1] [ptr2 ptrs2] [Hptr Hptrs]; cbn in Hptr, Hptrs.
  eapply I2F_memS_bind; [apply I2F_add_block_to_stack; auto |].
  intros _ _ _; constructor; auto.
Qed.

Lemma I2F_Malloc_bytes_with_pr : forall
    (init_bytes1 : list (@memory_byte PInf)) (init_bytes2 : list (@memory_byte PFin)),
    Forall2 I2F_mbyte init_bytes1 init_bytes2 ->
    forall align pr,
    I2F_memS I2F_State I2F_Addr
      (@Malloc_bytes_with_pr PInf init_bytes1 align pr)
      (@Malloc_bytes_with_pr PFin init_bytes2 align pr).
Proof.
  intros init_bytes1 init_bytes2 Hbytes align pr; unfold Malloc_bytes_with_pr.
  rewrite !N_length_eq, (Forall2_length_N Hbytes).
  eapply I2F_memS_bind; [apply I2F_get_free_block |].
  intros [ptr1 ptrs1] [ptr2 ptrs2] [Hptr Hptrs]; cbn in Hptr, Hptrs.
  eapply I2F_memS_bind; [apply I2F_add_block_to_heap; auto |].
  intros _ _ _; constructor; auto.
Qed.

Lemma I2F_push_frame_stack :
    forall (f1 : @Frame PInf) (f2 : @Frame PFin), I2F_Frame f1 f2 ->
    forall fs1 fs2, I2F_Framestack fs1 fs2 ->
    I2F_Framestack (push_frame_stack f1 fs1) (push_frame_stack f2 fs2).
Proof. intros f1 f2 Hf fs1 fs2 Hfs; constructor; auto. Qed.

Lemma I2F_Mempush : I2F_memS I2F_State (fun (_ _ : unit) => True) Mempush Mempush.
Proof.
  unfold Mempush.
  apply I2F_app_frame_stack.
  intros fs1 fs2 Hfs; apply I2F_push_frame_stack; auto.
  constructor.
Qed.

Lemma I2F_Mempop : I2F_memS I2F_State (fun (_ _ : unit) => True) Mempop Mempop.
Proof.
  unfold Mempop.
  eapply I2F_memS_bind; [apply I2F_get_frame |].
  intros f1 f2 Hf.
  eapply I2F_memS_bind; [apply I2F_app_frame_stack_eob |].
  intros _ _ _.
  apply I2F_app_mem.
  intros m1 m2 Hm; apply I2F_free_frame_memory; auto.
Qed.

Lemma I2F_Free : forall (p1 : @ptr (@PROV PInf) (@PTR PInf)) (p2 : @ptr (@PROV PFin) (@PTR PFin)),
    I2F_Addr p1 p2 ->
    I2F_memS I2F_State (fun (_ _ : unit) => True) (Free p1) (Free p2).
Proof.
  intros [z1 pr1] [z2 pr2] Hp; unfold Free.
  destruct Hp as [HI ->]; red in HI; subst.
  eapply I2F_memS_bind; [apply I2F_get_heap |].
  intros h1 h2 Hh.
  destruct Hh as [DOM VAL].
  lazymatch goal with
  | |- I2F_memS _ _
        match ?e1 with Some _ => _ | None => _ end
        match ?e2 with Some _ => _ | None => _ end =>
      destruct e1 as [b1|] eqn:E1; destruct e2 as [b2|] eqn:E2
  end.
  - assert (HB : Forall2 I2F_Addr b1 b2) by (eapply VAL; eauto).
    eapply I2F_memS_bind.
    { apply I2F_app_mem; intros m1 m2 Hm; apply I2F_free_block_memory; auto. }
    intros _ _ _; apply I2F_upd_heap.
    apply IM_Refine_remove; exact (conj DOM VAL).
  - exfalso.
    apply lookup_member in E1; apply DOM in E1; apply member_lookup in E1 as [v Hv].
    assert (Hcontra : Some v = None)
      by (transitivity (lookup (unsigned z2) h2); [symmetry; exact Hv | exact E2]).
    discriminate.
  - exfalso.
    apply lookup_member in E2; apply DOM in E2; apply member_lookup in E2 as [v Hv].
    assert (Hcontra : Some v = None)
      by (transitivity (lookup (unsigned z2) h1); [symmetry; exact Hv | exact E1]).
    discriminate.
  - constructor.
Qed.

(** ** Derived operations *)

Lemma I2F_read_bytes : forall (p1 : @ptr (@PROV PInf) (@PTR PInf)) (p2 : @ptr (@PROV PFin) (@PTR PFin)),
    I2F_Addr p1 p2 -> forall size,
    I2F_memS I2F_State (Forall2 I2F_mbyte) (read_bytes p1 size) (read_bytes p2 size).
Proof.
  intros p1 p2 Hp size; unfold read_bytes.
  eapply I2F_memS_bind; [apply I2F_memS_lift, I2F_get_consecutive_ptrs; auto |].
  intros ptrs1 ptrs2 Hptrs.
  eapply I2F_memS_map_monad_acc2.
  - exact Hptrs.
  - intros; apply I2F_Read_byte; auto.
Qed.

Lemma I2F_read_dvalue : forall (p1 : @ptr (@PROV PInf) (@PTR PInf)) (p2 : @ptr (@PROV PFin) (@PTR PFin)),
    I2F_Addr p1 p2 -> forall dt,
    I2F_memS I2F_State I2F_dvalue (read_dvalue dt p1) (read_dvalue dt p2).
Proof.
  intros p1 p2 Hp dt; unfold read_dvalue.
  eapply I2F_memS_bind; [apply I2F_read_bytes; auto |].
  intros bytes1 bytes2 Hbytes.
  apply I2F_memS_lift.
  apply I2F_memory_bytes_to_dvalue; auto.
Qed.

Lemma I2F_write_bytes : forall (p1 : @ptr (@PROV PInf) (@PTR PInf)) (p2 : @ptr (@PROV PFin) (@PTR PFin)),
    I2F_Addr p1 p2 ->
    forall (bytes1 : list (@memory_byte PInf)) (bytes2 : list (@memory_byte PFin)),
      Forall2 I2F_mbyte bytes1 bytes2 ->
    I2F_memS I2F_State (fun (_ _ : unit) => True) (write_bytes p1 bytes1) (write_bytes p2 bytes2).
Proof.
  intros p1 p2 Hp bytes1 bytes2 Hbytes; unfold write_bytes.
  rewrite !N_length_eq, (Forall2_length_N Hbytes).
  eapply I2F_memS_bind; [apply I2F_memS_lift, I2F_get_consecutive_ptrs; auto |].
  intros ptrs1 ptrs2 Hptrs.
  rewrite !zip_acc_eq.
  eapply I2F_memS_loop_monad2.
  - eapply Forall2_zip; eauto.
  - intros [pa ba] [pb bb] [Hpp Hbb]; cbn; apply I2F_Write_byte; auto.
Qed.

Lemma I2F_write_dvalue : forall (p1 : @ptr (@PROV PInf) (@PTR PInf)) (p2 : @ptr (@PROV PFin) (@PTR PFin)),
    I2F_Addr p1 p2 ->
    forall dt v1 v2, I2F_dvalue v1 v2 ->
    I2F_memS I2F_State (fun (_ _ : unit) => True) (write_dvalue dt p1 v1) (write_dvalue dt p2 v2).
Proof.
  intros p1 p2 Hp dt v1 v2 Hv; unfold write_dvalue.
  apply I2F_write_bytes; auto.
  apply I2F_dvalue_to_memory_bytes; auto.
Qed.

Lemma I2F_allocate_bytes : forall
    (init_bytes1 : list (@memory_byte PInf)) (init_bytes2 : list (@memory_byte PFin)),
    Forall2 I2F_mbyte init_bytes1 init_bytes2 ->
    forall align,
    I2F_memS I2F_State I2F_Addr
      (@allocate_bytes PInf _ init_bytes1 align) (@allocate_bytes PFin _ init_bytes2 align).
Proof.
  intros init_bytes1 init_bytes2 Hbytes align; unfold allocate_bytes.
  eapply I2F_memS_bind; [apply I2F_memS_fresh_prov |].
  intros pr1 pr2 ->.
  apply I2F_Allocate_bytes_with_pr; auto.
Qed.

Lemma I2F_allocate_dtyp : forall dt num_elements align,
    I2F_memS I2F_State I2F_Addr
      (@allocate_dtyp PInf _ dt num_elements align) (@allocate_dtyp PFin _ dt num_elements align).
Proof.
  intros dt num_elements align; unfold allocate_dtyp.
  destruct (dtyp_eqb dt DTYPE_Void).
  - constructor.
  - apply I2F_allocate_bytes.
    rewrite !concat_acc_eq.
    apply Forall2_concat.
    apply Forall2_repeatN.
    apply I2F_generate_poison_bytes.
Qed.

(** ** [convert_impure]: impure type conversions *)

Lemma I2F_assert_inttoptr_types_ok : forall t_from t_to,
    I2F_memS I2F_State (fun (_ _ : unit) => True)
      (@assert_inttoptr_types_ok PInf _ t_from t_to) (@assert_inttoptr_types_ok PFin _ t_from t_to).
Proof.
  intros t_from t_to; unfold assert_inttoptr_types_ok.
  destruct t_from, t_to; constructor; auto.
Qed.

Lemma I2F_convert_impure_base : forall conv t_from t_to v1 v2,
    I2F_dvalue_base v1 v2 ->
    I2F_memS I2F_State I2F_dvalue_base
      (@convert_impure_base PInf _ conv t_from v1 t_to) (@convert_impure_base PFin _ conv t_from v2 t_to).
Proof.
  intros conv t_from t_to v1 v2 Hv; unfold convert_impure_base.
  destruct conv.
  - eapply I2F_memS_bind; [apply I2F_assert_inttoptr_types_ok |].
    intros _ _ _.
    apply I2F_memS_lift.
    rewrite (I2F_dvalue_base_int_unsigned Hv).
    eapply I2F_EOU_bind; [apply I2F_int_to_ptr |].
    intros a1 a2 Ha; repeat constructor; auto.
  - destruct Hv as [[z1 pr1] [z2 pr2] HI | | | | | | | ]; [ | constructor .. ].
    destruct HI as [HI ->]; red in HI; subst.
    destruct t_to;
      [ apply I2F_memS_lift; apply I2F_coerce_integer_to_int
      | apply I2F_memS_lift; apply I2F_coerce_integer_to_int
      | constructor .. ].
  - destruct Hv as [[z1 pr1] [z2 pr2] HI | | | | | | | ]; [ | constructor .. ].
    destruct HI as [HI ->]; red in HI; subst.
    destruct t_to;
      [ apply I2F_memS_lift; apply I2F_coerce_integer_to_int
      | apply I2F_memS_lift; apply I2F_coerce_integer_to_int
      | constructor .. ].
  - constructor.
Qed.

Lemma I2F_convert_impure : forall conv t_from t_to v1 v2,
    I2F_dvalue v1 v2 ->
    I2F_memS I2F_State I2F_dvalue
      (@convert_impure PInf _ conv t_from v1 t_to) (@convert_impure PFin _ conv t_from v2 t_to).
Proof.
  intros conv t_from t_to v1 v2 Hv; unfold convert_impure.
  destruct Hv as [b1 b2 Hb | p s1 s2 Hs | v τ s1 s2 Hs].
  - destruct (get_base_conversion_type t_from t_to) as [[tf' tt']|]; cbn; [| apply I2F_Merr].
    eapply I2F_memS_bind; [apply I2F_convert_impure_base; auto |].
    intros b1' b2' Hb'; apply I2F_Mret; constructor; auto.
  - cbn; apply I2F_Merr.
  - destruct v; cbn; [| apply I2F_Merr ..].
    destruct τ as [ | | vector sz τ]; cbn; [ apply I2F_Merr | apply I2F_Merr | ].
    destruct vector; cbn; [ | apply I2F_Merr ].
    destruct (get_vector_conversion_type t_from t_to) as [[tf' tt']|]; cbn; [| apply I2F_Merr].
    eapply I2F_memS_bind.
    { apply I2F_memS_lift, I2F_EOU_map_monad2 with (RA := I2F_dvalue); auto.
      intros a1 a2 Ha; apply I2F_dvalue_to_dvalue_base; auto. }
    intros elts1' elts2' Helts.
    eapply I2F_memS_bind.
    { eapply I2F_memS_map_monad2; eauto.
      intros x1 x2 Hx; apply I2F_convert_impure_base; auto. }
    intros val1 val2 Hval.
    apply I2F_Mret, I2F_dvalue_Array.
    induction Hval; cbn; constructor; auto.
Qed.

(** ** [handle_memoryM] *)

Theorem I2F_handle_memoryM :
  forall T1 T2 (e1 : @MemoryE PInf T1) (e2 : @MemoryE PFin T2),
    I2FE_Memory e1 e2 ->
    I2F_memS I2F_State (fun a b => I2FA_Memory e1 a e2 b)
      (@handle_memoryM PInf _ T1 e1) (@handle_memoryM PFin _ T2 e2).
Proof.
  intros T1 T2 e1 e2 H.
  destruct e1 as [ | | t1 n1 align1 | t1 a1 | t1 a1 v1 | cv1 tf1 v1 tt1];
    destruct e2 as [ | | t2 n2 align2 | t2 a2 | t2 a2 v2 | cv2 tf2 v2 tt2];
    simp I2FE_Memory in H; cbn in H; try contradiction; unfold handle_memoryM.
  - (* MemPush *)
    eapply I2F_memS_mono; [ | apply I2F_Mempush].
    intros; simp I2FA_Memory; auto.
  - (* MemPop *)
    eapply I2F_memS_mono; [ | apply I2F_Mempop].
    intros; simp I2FA_Memory; auto.
  - (* Alloca *)
    destruct H as [Ht [Hn Halign]]; subst.
    destruct align2 as [align|]; cbn.
    all: eapply I2F_memS_bind; [apply I2F_allocate_dtyp |];
      intros ptr1 ptr2 Hptr;
      apply I2F_Mret;
      simp I2FA_Memory;
      repeat constructor; auto.
  - (* Load *)
    destruct H as [Ht Ha]; subst.
    destruct Ha as [b1 b2 Hb | p1 s1 s2 Hs | v1 τ1 s1 s2 Hs].
    + destruct Hb as [p1 p2 Hp | | | | | | | ]; [ | apply I2F_Mub_l ..].
      eapply I2F_memS_mono; [ | apply I2F_read_dvalue; auto].
      intros; simp I2FA_Memory; auto.
    + apply I2F_Mub_l.
    + apply I2F_Mub_l.
  - (* Store *)
    destruct H as [Ht [Ha Hv]]; subst.
    destruct Ha as [b1 b2 Hb | p1 s1 s2 Hs | v1' τ1 s1 s2 Hs].
    + destruct Hb as [p1 p2 Hp | | | | | | | ]; [ | apply I2F_Mub_l ..].
      eapply I2F_memS_mono; [ | apply I2F_write_dvalue; auto].
      intros; simp I2FA_Memory; auto.
    + apply I2F_Mub_l.
    + apply I2F_Mub_l.
  - (* Conv *)
    destruct H as [Hcv [Htf [Hv Htt]]]; subst.
    eapply I2F_memS_mono; [ | apply I2F_convert_impure; auto].
    intros; simp I2FA_Memory; auto.
Qed.

(** ** [handle_intrinsicM] (memcpy/memset/malloc/free) *)

Lemma I2F_memcpy : forall (src1 dst1 : @ptr (@PROV PInf) (@PTR PInf))
                          (src2 dst2 : @ptr (@PROV PFin) (@PTR PFin)),
    I2F_Addr src1 src2 -> I2F_Addr dst1 dst2 ->
    forall size volatile,
    I2F_memS I2F_State (fun (_ _ : unit) => True)
      (memcpy src1 dst1 size volatile) (memcpy src2 dst2 size volatile).
Proof.
  intros src1 dst1 src2 dst2 Hsrc Hdst size volatile.
  unfold memcpy.
  rewrite <- (I2F_no_overlap dst1 src1 size dst2 src2 size Hdst Hsrc).
  rewrite <- (I2F_Addr_ptr_to_int _ _ Hsrc).
  rewrite <- (I2F_Addr_ptr_to_int _ _ Hdst).
  destruct (orb (no_overlap dst1 size src1 size) (Z.eqb (ptr_to_int src1) (ptr_to_int dst1))).
  - eapply I2F_memS_bind; [apply I2F_read_bytes; auto |].
    intros bytes1 bytes2 Hbytes.
    apply I2F_write_bytes; auto.
  - apply I2F_Mub_l.
Qed.

Lemma I2F_memset : forall (dst1 : @ptr (@PROV PInf) (@PTR PInf)) (dst2 : @ptr (@PROV PFin) (@PTR PFin)),
    I2F_Addr dst1 dst2 ->
    forall val len volatile,
    I2F_memS I2F_State (fun (_ _ : unit) => True)
      (memset dst1 val len volatile) (memset dst2 val len volatile).
Proof.
  intros dst1 dst2 Hdst val len volatile; unfold memset.
  destruct (Z.ltb len 0); [constructor |].
  apply I2F_write_bytes; auto.
  apply Forall2_repeatN.
  apply I2F_mbyte_MByte; repeat constructor.
Qed.

Lemma I2F_malloc_bytes : forall
    (init_bytes1 : list (@memory_byte PInf)) (init_bytes2 : list (@memory_byte PFin)),
    Forall2 I2F_mbyte init_bytes1 init_bytes2 ->
    forall align,
    I2F_memS I2F_State I2F_Addr (malloc_bytes init_bytes1 align) (malloc_bytes init_bytes2 align).
Proof.
  intros init_bytes1 init_bytes2 Hbytes align; unfold malloc_bytes.
  eapply I2F_memS_bind; [apply I2F_memS_fresh_prov |].
  intros pr1 pr2 ->.
  apply I2F_Malloc_bytes_with_pr; auto.
Qed.

Lemma I2F_handle_memcpy : forall (args1 : list (@dvalue_base PInf)) (args2 : list (@dvalue_base PFin)),
    Forall2 I2F_dvalue_base args1 args2 ->
    I2F_memS I2F_State (fun (_ _ : unit) => True) (handle_memcpy args1) (handle_memcpy args2).
Proof.
  intros args1 args2 Hargs; unfold handle_memcpy.
  destruct Hargs as [ | dst1 dst2 l1 l2 Hdst Hargs]; [apply I2F_Merr |].
  destruct Hdst as [pdst1 pdst2 Hpdst | | | | | | | ]; try apply I2F_Merr.
  destruct Hargs as [ | src1 src2 l1' l2' Hsrc Hargs]; [apply I2F_Merr |].
  destruct Hsrc as [psrc1 psrc2 Hpsrc | | | | | | | ]; try apply I2F_Merr.
  destruct Hargs as [ | sz1 sz2 l1'' l2'' Hsz Hargs]; [apply I2F_Merr |].
  destruct Hsz as [ | szv i1 | ip1 ip2 Hip | | | | | ]; try apply I2F_Merr.
  - destruct Hargs as [ | vol1 vol2 l1''' l2''' Hvol Hargs]; [apply I2F_Merr |].
    destruct Hvol as [ | szv2 vv1 | | | | | | ]; try apply I2F_Merr.
    destruct Hargs; [ | apply I2F_Merr].
    apply I2F_memcpy; auto.
  - destruct Hargs as [ | vol1 vol2 l1''' l2''' Hvol Hargs]; [apply I2F_Merr |].
    destruct Hvol as [ | szv2 vv1 | | | | | | ]; try apply I2F_Merr.
    destruct Hargs; [ | apply I2F_Merr].
    red in Hip; subst; cbn.
    apply I2F_memcpy; auto.
Qed.

Lemma I2F_handle_memset : forall (args1 : list (@dvalue_base PInf)) (args2 : list (@dvalue_base PFin)),
    Forall2 I2F_dvalue_base args1 args2 ->
    I2F_memS I2F_State (fun (_ _ : unit) => True) (handle_memset args1) (handle_memset args2).
Proof.
  intros args1 args2 Hargs; unfold handle_memset.
  destruct Hargs as [ | dst1 dst2 l1 l2 Hdst Hargs]; [apply I2F_Merr |].
  destruct Hdst as [pdst1 pdst2 Hpdst | | | | | | | ]; try apply I2F_Merr.
  destruct Hargs as [ | val1 val2 l1' l2' Hval Hargs]; [apply I2F_Merr |].
  destruct Hval as [ | szval v1 | | | | | | ]; try apply I2F_Merr.
  destruct Hargs as [ | len1 len2 l1'' l2'' Hlen Hargs]; [apply I2F_Merr |].
  destruct Hlen as [ | szlen ln1 | | | | | | ]; try apply I2F_Merr.
  destruct Hargs as [ | vol1 vol2 l1''' l2''' Hvol Hargs]; [apply I2F_Merr |].
  destruct Hvol as [ | szvol vv1 | | | | | | ]; try apply I2F_Merr.
  destruct Hargs; [ | apply I2F_Merr].
  destruct (Pos.eq_dec szval 8) as [e | ]; [ | apply I2F_Merr].
  subst; cbn.
  apply I2F_memset; auto.
Qed.

Lemma I2F_handle_malloc : forall (args1 : list (@dvalue_base PInf)) (args2 : list (@dvalue_base PFin)),
    Forall2 I2F_dvalue_base args1 args2 ->
    forall align,
    I2F_memS I2F_State I2F_Addr (handle_malloc args1 align) (handle_malloc args2 align).
Proof.
  intros args1 args2 Hargs align; unfold handle_malloc.
  destruct Hargs as [ | sz1 sz2 l1 l2 Hsz Hargs]; [apply I2F_Merr |].
  destruct Hsz as [ | szv i1 | ip1 ip2 Hip | | | | | ]; try (destruct Hargs; apply I2F_Merr).
  - destruct Hargs; [ | apply I2F_Merr].
    apply I2F_malloc_bytes, I2F_generate_num_poison_bytes.
  - destruct Hargs; [ | apply I2F_Merr].
    red in Hip; subst; cbn.
    apply I2F_malloc_bytes, I2F_generate_num_poison_bytes.
Qed.

Lemma I2F_handle_free : forall (args1 : list (@dvalue_base PInf)) (args2 : list (@dvalue_base PFin)),
    Forall2 I2F_dvalue_base args1 args2 ->
    I2F_memS I2F_State (fun (_ _ : unit) => True) (handle_free args1) (handle_free args2).
Proof.
  intros args1 args2 Hargs; unfold handle_free.
  destruct Hargs as [ | p1 p2 l1 l2 Hp Hargs]; [apply I2F_Merr |].
  destruct Hp as [pdst1 pdst2 Hpdst | | | | | | | ]; try apply I2F_Merr.
  destruct Hargs; [ | apply I2F_Merr].
  apply I2F_Free; auto.
Qed.

Theorem I2F_handle_intrinsicM :
  forall T1 T2 (e1 : @IntrinsicE PInf T1) (e2 : @IntrinsicE PFin T2),
    I2FE_Intrinsic e1 e2 ->
    I2F_memS I2F_State (fun a b => I2FA_Intrinsic e1 a e2 b)
      (@handle_intrinsicM PInf _ T1 e1) (@handle_intrinsicM PFin _ T2 e2).
Proof.
  intros T1 T2 e1 e2 H.
  destruct e1 as [t1 f1 args1 va1]; destruct e2 as [t2 f2 args2 va2].
  simp I2FE_Intrinsic in H; cbn in H.
  destruct H as [Ht [Hf [Hargs Hva]]]; subst.
  unfold handle_intrinsicM.
  eapply I2F_memS_bind.
  { apply I2F_memS_lift.
    eapply I2F_EOU_map_monad2; [exact Hargs |].
    intros a1 a2 Ha; apply I2F_dvalue_to_dvalue_base; auto. }
  intros args1' args2' Hargs'.
  destruct (orb (Rocqlib.proj_sumbool (string_dec f2 "llvm.memcpy.p0i8.p0i8.i32"))
              (Rocqlib.proj_sumbool (string_dec f2 "llvm.memcpy.p0i8.p0i8.i64"))).
  - eapply I2F_memS_bind; [apply I2F_handle_memcpy; auto |].
    intros _ _ _; apply I2F_Mret; simp I2FA_Intrinsic; repeat constructor.
  - destruct (orb (Rocqlib.proj_sumbool (string_dec f2 "llvm.memset.p0i8.i32"))
                (Rocqlib.proj_sumbool (string_dec f2 "llvm.memset.p0i8.i64"))).
    + eapply I2F_memS_bind; [apply I2F_handle_memset; auto |].
      intros _ _ _; apply I2F_Mret; simp I2FA_Intrinsic; repeat constructor.
    + destruct (Rocqlib.proj_sumbool (string_dec f2 "malloc")).
      * eapply I2F_memS_bind; [apply I2F_handle_malloc; auto |].
        intros ptr1 ptr2 Hptr; apply I2F_Mret; simp I2FA_Intrinsic; repeat constructor; auto.
      * destruct (Rocqlib.proj_sumbool (string_dec f2 "free")).
        -- eapply I2F_memS_bind; [apply I2F_handle_free; auto |].
           intros _ _ _; apply I2F_Mret; simp I2FA_Intrinsic; repeat constructor.
        -- apply I2F_Merr.
Qed.
