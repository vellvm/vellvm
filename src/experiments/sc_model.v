(* Extending the block model to concurrency. *)
Require Import Coqlib.
Require Import Util.
Require Import Arith.
Require Import block_model.
Import ListNotations.
Import Bool.
Import EquivDec.
Import CoqEqDec.

Local Close Scope Z.

Set Implicit Arguments.

Section Concurrency.
  Context `(ML : Memory_Layout) {thread : Type}.

  Definition ptr := ptr block.

  Inductive base_op : Type :=
  | Read : thread -> ptr -> val -> base_op
  | Write : thread -> ptr -> val -> base_op
  | ARW : thread -> ptr -> val -> val -> base_op
  | Alloc : thread -> block -> nat -> base_op
  | Free : thread -> block -> base_op.

  Definition to_seq c :=
    match c with
    | Read _ p v => [MRead p v]
    | Write _ p v => [MWrite p v]
    | ARW _ p v v' => [MRead p v; MWrite p v']
    | Alloc _ b n => [MAlloc b n]
    | Free _ b => [MFree b]
    end.

  Definition thread_of c :=
    match c with
    | Read t _ _ => t
    | Write t _ _ => t
    | ARW t _ _ _ => t
    | Alloc t _ _ => t
    | Free t _ => t
    end.

  Definition loc_of c :=
    match c with
    | Read _ p _ => Ptr p
    | Write _ p _ => Ptr p
    | ARW _ p _ _ => Ptr p
    | Alloc _ b _ => Block b
    | Free _ b => Block b
    end.

  Definition block_of c :=
    match c with
    | Read _ (b, _) _ => b
    | Write _ (b, _) _ => b
    | ARW _ (b, _) _ _ => b
    | Alloc _ b _ => b
    | Free _ b => b
    end.

  Lemma block_of_loc_spec : forall c, block_of_loc (loc_of c) = block_of c.
  Proof. destruct c; clarify. Qed.

  Section Sync.
 
    Inductive sync : Set := (* non-atomic? *)
      unordered | monotonic | acquire | release | acq_rel | seq_cst.
    Global Instance sync_eq : @EqDec sync eq eq_equivalence.
    Proof. eq_dec_inst. Qed.

    Inductive sync_le : sync -> sync -> Prop :=
    | sync_refl : forall s, sync_le s s
    | sync_trans : forall s1 s2 s3 (Hs1 : sync_le s1 s2) (Hs2 : sync_le s2 s3),
                     sync_le s1 s3
    | sync_u_m : sync_le unordered monotonic
    | sync_m_a : sync_le monotonic acquire
    | sync_m_r : sync_le monotonic release
    | sync_a_ar : sync_le acquire acq_rel
    | sync_r_ar : sync_le release acq_rel
    | sync_ar_sc : sync_le acq_rel seq_cst.
    Hint Constructors sync_le.

    Global Instance sync_le_trans : Transitive sync_le.
    Proof. eauto. Qed.

    Lemma sync_le_u_inv : forall s, sync_le s unordered -> s = unordered.
    Proof. remember unordered as s2; intros; induction H; clarify. Qed.

    Lemma sync_le_m_inv : forall s, sync_le s monotonic ->
                                    s = unordered \/ s = monotonic.
    Proof.
      remember monotonic as s2; intros; induction H; clarify.
      generalize (sync_le_u_inv H); auto.
    Qed.

    Lemma sync_le_sc_inv : forall s, sync_le seq_cst s -> s = seq_cst.
    Proof. remember seq_cst as s2; intros; induction H; clarify. Qed.

    Lemma sync_le_ar_inv : forall s, sync_le acq_rel s ->
                                     s = acq_rel \/ s = seq_cst.
    Proof.
      remember acq_rel as s2; intros; induction H; clarify.
      generalize (sync_le_sc_inv H0); auto.
    Qed.

    Lemma sync_le_a_inv : forall s, sync_le acquire s ->
                                    s = acquire \/ s = acq_rel \/ s = seq_cst.
    Proof.
      remember acquire as s2; intros; induction H; clarify.
      destruct IHsync_le1; subst; [generalize (sync_le_ar_inv H0) |
                                   generalize (sync_le_sc_inv H0)]; auto.
    Qed.
    
    Lemma sync_le_r_inv : forall s, sync_le release s ->
                                    s = release \/ s = acq_rel \/ s = seq_cst.
    Proof.
      remember release as s2; intros; induction H; clarify.
      destruct IHsync_le1; subst; [generalize (sync_le_ar_inv H0) |
                                   generalize (sync_le_sc_inv H0)]; auto.
    Qed.

    Ltac analyze_sync :=
      match goal with
        | H : sync_le _ unordered |- _ => generalize (sync_le_u_inv H); clarify
        | H : sync_le _ monotonic |- _ => generalize (sync_le_m_inv H); clarify
        | H : sync_le seq_cst _ |- _ => generalize (sync_le_sc_inv H); clarify
        | H : sync_le acq_rel _ |- _ => generalize (sync_le_ar_inv H); clarify
        | H : sync_le acquire _ |- _ => generalize (sync_le_a_inv H); clarify
        | H : sync_le release _ |- _ => generalize (sync_le_r_inv H); clarify
      end.
    
    Definition sync_leb s1 s2 :=
      if eq_dec s1 s2 then true else
        match s1, s2 with
          | unordered, _ => true
          | _, unordered => false
          | monotonic, _ => true
          | _, monotonic => false
          | acquire, acq_rel => true
          | release, acq_rel => true
          | _, seq_cst => true
          | _, _ => false
        end.

    Lemma sync_leb_spec : forall s1 s2, sync_leb s1 s2 = true <-> sync_le s1 s2.
    Proof.
      intros; unfold sync_leb; destruct (eq_dec s1 s2); clarify.
      - split; clarify.
      - destruct s1, s2; split; clarify; eauto 4; analyze_sync.
    Qed.

  End Sync.

  Definition conc_op := (base_op * sync)%type.
  Definition loc_of' (p : conc_op) := loc_of (fst p).
  Definition block_of' (p : conc_op) := block_of (fst p).
  Definition thread_of' (p : conc_op) := thread_of (fst p).
  Definition to_seq' (p : conc_op) := match p with (c, _) => to_seq c end.
  Lemma block_of_loc_spec' : forall c, block_of_loc (loc_of' c) = block_of' c.
  Proof. destruct c; apply block_of_loc_spec. Qed.
(*  Definition not_sync (c : conc_op) := 
    match c with (a, s) => ~sync_le acquire s /\ ~sync_le release s end.*)
  Definition mem := ilist conc_op.

  Definition touches_block op b := beq (block_of' op) b.
  Definition touches_other op b := negb (touches_block op b).
  Class MM_base := { synchronizes_with : conc_op -> conc_op -> Prop;
      touches_sync1 : forall a1 a2 b (Hsync : synchronizes_with a1 a2),
        touches_block a1 b = false -> touches_other a2 b = true;
      touches_sync2 : forall a1 a2 b (Hsync : synchronizes_with a1 a2),
        touches_block a2 b = false -> touches_other a1 b = true }.

  Section Mem.

  Context `{Mb : MM_base}.

  Section Happens_Before.

  Inductive happens_before (m : mem) i j : Prop :=
  | hb_prog (Hlt : i < j) a (Ha : inth m i = Some a) b (Hb : inth m j = Some b)
      (Hthread : thread_of' a = thread_of' b) : happens_before m i j
  | hb_sync (Hlt : i < j) a (Ha : inth m i = Some a) b (Hb : inth m j = Some b)
      (Hsync : synchronizes_with a b) : happens_before m i j
  | hb_trans k (Hi : happens_before m i k) (Hj : happens_before m k j) :
      happens_before m i j.

  Lemma hb_lt : forall m i j, happens_before m i j -> i < j.
  Proof. intros; induction H; clarify; abstract omega. Qed.
  Corollary hb_irrefl : forall m i, ~happens_before m i i.
  Proof. repeat intro; exploit hb_lt; eauto; abstract omega. Qed.
  Corollary hb_antisym : forall m i j, happens_before m i j ->
    ~happens_before m j i.
  Proof. intros ? ? ? H1 H2; generalize (hb_lt H1), (hb_lt H2); abstract omega. 
  Qed.

  Lemma hb_app : forall m1 m2 i j m2' (Hhb : happens_before (iapp m1 m2) i j)
    (Hi : i < length m1) (Hj : j < length m1), happens_before (iapp m1 m2') i j.
  Proof.
    intros; induction Hhb.
    - eapply hb_prog; eauto; rewrite iapp_nth in *; clarify.
    - eapply hb_sync; eauto; rewrite iapp_nth in *; clarify.
    - generalize (hb_lt Hhb2); intro.
      generalize (lt_trans _ _ _ H Hj); clarify.
      eapply hb_trans; eauto.
  Qed.
  
  Corollary hb_app_impl : forall m1 m2 i j
    (Hhb : happens_before (iapp m1 m2) i j)
    (Hi : i < length m1) (Hj : j < length m1), happens_before m1 i j.
  Proof.
    intros; exploit hb_app; eauto.
    rewrite iapp_nil_ilist; auto.
  Qed.

  Lemma hb_app' : forall m1 m2 i j m1' (Hhb : happens_before (iapp m1 m2) i j)
    (Hi : ~i < length m1) (Hj : ~j < length m1),
    happens_before (iapp m1' m2)
      (i - length m1 + length m1') (j - length m1 + length m1').
  Proof.
    intros; induction Hhb.
    - rewrite iapp_nth in *; clarify.
      eapply hb_prog; eauto; try rewrite iapp_nth.
      + abstract omega.
      + destruct (lt_dec (i - length m1 + length m1') (length m1')); [abstract omega|].
        rewrite NPeano.Nat.add_sub; auto.
      + destruct (lt_dec (j - length m1 + length m1') (length m1')); [abstract omega|].
        rewrite NPeano.Nat.add_sub; auto.
    - rewrite iapp_nth in *; clarify.
      eapply hb_sync; eauto; try rewrite iapp_nth.
      + abstract omega.
      + destruct (lt_dec (i - length m1 + length m1') (length m1')); [abstract omega|].
        rewrite NPeano.Nat.add_sub; auto.
      + destruct (lt_dec (j - length m1 + length m1') (length m1')); [abstract omega|].
        rewrite NPeano.Nat.add_sub; auto.
    - generalize (hb_lt Hhb1); intro.
      destruct (lt_dec k (length m1)); [abstract omega | clarify].
      eapply hb_trans; eauto.
  Qed.

  Definition hbe m i j := happens_before m i j \/ i = j.

  Lemma hbe_app : forall m1 m2 i j m2' (Hhb : hbe (iapp m1 m2) i j)
    (Hi : i < length m1) (Hj : j < length m1), hbe (iapp m1 m2') i j.
  Proof. unfold hbe; clarify; left; eapply hb_app; eauto. Qed.
  
  Lemma hb_next : forall m i j, happens_before m i j ->
    exists a, inth m i = Some a /\ exists k b, i < k /\ inth m k = Some b /\
      (thread_of' a = thread_of' b \/ synchronizes_with a b) /\ hbe m k j.
  Proof.
    unfold hbe; intros; induction H; clarify.
    - repeat eexists; eauto.
    - repeat eexists; eauto.
    - eexists; split; eauto.
      exists x3; repeat eexists; eauto.
      destruct IHhappens_before12222, IHhappens_before22222; clarify;
        left; eapply hb_trans; eauto.
  Qed.

  Lemma hb_prev : forall m i j, happens_before m i j ->
    exists b, inth m j = Some b /\ exists k a, k < j /\ inth m k = Some a /\
      (thread_of' a = thread_of' b \/ synchronizes_with a b) /\ hbe m i k.
  Proof.
    unfold hbe; intros; induction H; clarify.
    - repeat eexists; eauto.
    - repeat eexists; eauto.
    - eexists; split; eauto.
      exists x1; repeat eexists; eauto.
      destruct IHhappens_before22222; clarify.
      left; eapply hb_trans; eauto.
  Qed.

  Lemma hbe_trans : forall m i j k (Hhbe1 : hbe m i j) (Hhbe2 : hbe m j k),
    hbe m i k.
  Proof.
    unfold hbe; clarify.
    left; eapply hb_trans; eauto.
  Qed.

  Lemma hb_inv : forall m i j, happens_before m i j ->
    exists a b, inth m i = Some a /\ inth m j = Some b /\
      ((thread_of' a = thread_of' b) \/ synchronizes_with a b \/
      exists k c, inth m k = Some c /\ (*~not_sync c /\*)
                  happens_before m i k /\ happens_before m k j).
  Proof.
    intros; induction H; clarsimp; repeat eexists; eauto.
    destruct IHhappens_before122 as [? | [? | ?]]; clarify.
    - destruct IHhappens_before222 as [? | [? | ?]]; clarify.
      + clarsimp.
      + right; right; exists k; repeat eexists; eauto.
(*        intro Hsync; generalize (no_sync _ Hsync x0); clarify.*)
      + right; right; exists x2; repeat eexists; eauto.
        eapply hb_trans; eauto.
    - destruct IHhappens_before222 as [? | [? | ?]]; clarify.
      + right; right; exists k; repeat eexists; eauto.
(*        intro Hsync; generalize (no_sync _ Hsync x1); clarify.*)
      + right; right; exists k; repeat eexists; eauto.
(*        intro Hsync; generalize (no_sync _ Hsync x1); clarify.*)
      + right; right; exists x2; repeat eexists; eauto.
        eapply hb_trans; eauto.
    - right; right; exists x2; repeat eexists; eauto.
      eapply hb_trans; eauto.
  Qed.

(*  Lemma hb_across : forall m1 ops m2 i j (*(Hnot_sync : Forall not_sync ops)*)
    (Hi : i < length m1) (Hj : j >= length m1 + length ops)
    (Hhb : happens_before (iapp m1 (iapp ops m2)) i j),
    happens_before (iapp m1 m2) i (j - length ops).
  Proof.
    intros.
    remember (j - i) as diff; generalize dependent j; generalize dependent i.
    induction diff using lt_wf_ind; clarify.
    exploit hb_inv; eauto; intros [a [b [Ha [Hb Hk]]]].
    rewrite iapp_nth in *; clarify.
    destruct (lt_dec j (length m1)); [abstract omega|].
    rewrite iapp_nth in *; destruct (lt_dec (j - length m1) (length ops));
      [abstract omega|].
    assert (j - length m1 - length ops = j - length ops - length m1) as Heq
      by abstract omega; rewrite Heq in *; clear Heq.
    destruct Hk as [? | [? | Hk]].
    - eapply hb_prog; eauto; try abstract omega; rewrite iapp_nth; clarify; abstract omega.
    - eapply hb_sync; eauto; try abstract omega; rewrite iapp_nth; clarify; abstract omega.
    - clarify.
      destruct (lt_dec x (length m1));
        [|destruct (lt_dec x (length m1 + length ops))].
      + eapply hb_trans; [eapply hb_app; eauto|].
        eapply H; eauto.
        generalize (hb_lt Hk221); intro; abstract omega.
      + rewrite iapp_nth in Hk1; clarify.
        rewrite iapp_nth in Hk1; destruct (lt_dec (x - length m1) (length ops));
          [|abstract omega].
        exploit nth_error_in; eauto; intro Hin.
        rewrite Forall_forall in Hnot_sync; specialize (Hnot_sync _ Hin);
          clarify.
      + eapply hb_trans.
        * generalize (hb_lt Hk222); intro.
          eapply H; try (apply Hk221); eauto; abstract omega.
        * rewrite iapp_app in *.
          generalize (hb_app' _ _ m1 Hk222); rewrite app_length; intro Hhb';
            clarify.
          use Hhb'; [|abstract omega].
          assert (x - (length m1 + length ops) + length m1 = x - length ops)
            as Heq by abstract omega; rewrite Heq in Hhb'; clear Heq;
            assert (j - (length m1 + length ops) + length m1 = j - length ops)
            as Heq by abstract omega; rewrite Heq in Hhb'; auto.
  Qed.*)

  Lemma seq_hb : forall ops t (Ht : Forall (fun c => thread_of' c = t) ops)
    m1 m2 i j (Hlt : length m1 <= i < j) (Hlen : j < length m1 + length ops),
    happens_before (iapp m1 (iapp ops m2)) i j.
  Proof.
    intros.
    assert (j - length m1 < length ops) by abstract omega.
    exploit nth_error_succeeds; eauto; intros [b Hj]; clarify.
    assert (i - length m1 < length ops) by abstract omega.
    exploit nth_error_succeeds; eauto; intros [a Hi].
    generalize (nth_error_in _ _ Hi), (nth_error_in _ _ Hj); intros Ha Hb.
    rewrite Forall_forall in Ht; generalize (Ht _ Ha); specialize (Ht _ Hb);
      clarify.
    eapply hb_prog; eauto; rewrite iapp_inter; clarify; abstract omega.
  Qed.

  Corollary seq_hb_iff : forall ops t
    (Ht : Forall (fun c => thread_of' c = t) ops) m1 m2 i j
    (Hlt : length m1 <= i < j) (Hlen : j < length m1 + length ops),
    happens_before (iapp m1 (iapp ops m2)) i j <-> i < j.
  Proof. intros; split; intro; [eapply hb_lt | eapply seq_hb]; eauto. Qed.    

  Corollary seq_hbe : forall ops t (Ht : Forall (fun c => thread_of' c = t) ops)
    m1 m2 i j (Hlt : length m1 <= i <= j) (Hlen : j < length m1 + length ops),
    hbe (iapp m1 (iapp ops m2)) i j.
  Proof.
    intros; unfold hbe; destruct (eq_dec i j); auto.
    left; eapply seq_hb; eauto; omega.
  Qed.

  Definition adjust_range {A} (l1 l l' : list A) i :=
    if lt_dec i (length l1) then i else i - length l + length l'.

  Lemma adjust_range_nth : forall {A} i (m1 ops : list A) m2 ops'
    (Hrange : i < length m1 \/ i >= length m1 + length ops),
    inth (iapp m1 (iapp ops' m2)) (adjust_range m1 ops ops' i) =
    inth (iapp m1 (iapp ops m2)) i.
  Proof.
    intros; repeat rewrite iapp_nth.
    unfold adjust_range; destruct (lt_dec i (length m1)); clarify.
    destruct (lt_dec (i - length m1) (length ops)); [abstract omega|].
    destruct (lt_dec (i - length ops + length ops') (length m1)); [abstract omega|].
    destruct (lt_dec (i - length ops + length ops' - length m1) (length ops'));
      [abstract omega|].
    assert (i - length ops + length ops' - length m1 - length ops' =
      i - length m1 - length ops) as Heq; [|rewrite Heq; auto].
    rewrite NPeano.Nat.add_sub_swap; [rewrite NPeano.Nat.add_sub | abstract omega].
    repeat rewrite <- NPeano.Nat.sub_add_distr; rewrite plus_comm; auto.
  Qed.

  Lemma adjust_adjust : forall {A} (l1 l l' : list A) i
    (Hrange : i < length l1 \/ i >= length l1 + length l),
    adjust_range l1 l' l (adjust_range l1 l l' i) = i.
  Proof.
    unfold adjust_range; intros.
    destruct (lt_dec i (length l1)); clarify.
    destruct (lt_dec (i - length l + length l')); abstract omega.
  Qed.

  Lemma adjust_lt : forall {A} (l1 l l' : list A) i j
    (Hi : i < length l1 \/ i >= length l1 + length l)
    (Hj : j < length l1 \/ j >= length l1 + length l),
    adjust_range l1 l l' i < adjust_range l1 l l' j <-> i < j.
  Proof.
    unfold adjust_range; intros.
    destruct (lt_dec i (length l1)), (lt_dec j (length l1)); try abstract omega.
  Qed.

  Lemma hb_delay : forall m1 ops m2 i j
    (Hhb : happens_before (iapp m1 m2) i j),
    happens_before (iapp m1 (iapp ops m2))
      (adjust_range m1 [] ops i) (adjust_range m1 [] ops j).
  Proof.
    intros; induction Hhb.
    - eapply hb_prog; eauto.
      + apply adjust_lt; clarify; abstract omega.
      + rewrite adjust_range_nth; clarify; abstract omega.
      + rewrite adjust_range_nth; clarify; abstract omega.
    - eapply hb_sync; eauto.
      + apply adjust_lt; clarify; abstract omega.
      + rewrite adjust_range_nth; clarify; abstract omega.
      + rewrite adjust_range_nth; clarify; abstract omega.
    - eapply hb_trans; eauto.
  Qed.

(*  Lemma hb_not_sync : forall m1 ops m2
    (*(Hnot_sync : Forall not_sync ops)*) i j
    (Hi : i < length m1 \/ i >= length m1 + length ops)
    (Hj : j < length m1 \/ j >= length m1 + length ops)
    ops' (*(Hnot_sync' : Forall not_sync ops')*)
    (Hhb : happens_before (iapp m1 (iapp ops m2)) i j),
    happens_before (iapp m1 (iapp ops' m2))
      (adjust_range m1 ops ops' i) (adjust_range m1 ops ops' j).
  Proof.
    intros.
    generalize (hb_lt Hhb); intro; destruct Hi, Hj; try abstract omega.
    - unfold adjust_range; clarify; eapply hb_app; eauto.
    - exploit hb_across; try (apply Hhb); eauto; intro Hhb'.
      generalize (hb_delay _ ops' _ Hhb'); clarify.
      unfold adjust_range in *; clarify.
      destruct (lt_dec (j - length ops) (length m1)); [abstract omega|].
      destruct (lt_dec j (length m1)); [abstract omega|].
      rewrite NPeano.Nat.sub_0_r in *; auto.
    - unfold adjust_range; destruct (lt_dec i (length m1)); [abstract omega|].
      destruct (lt_dec j (length m1)); [abstract omega|].
      rewrite iapp_app in *.
      generalize (hb_app' _ _ (m1 ++ ops') Hhb); repeat rewrite app_length;
        intro Hhb'; clarify.
      repeat (use Hhb'; [|abstract omega]).
      assert (i - (length m1 + length ops) + (length m1 + length ops') =
        i - length ops + length ops') as Heq by abstract omega; rewrite Heq in Hhb';
        clear Heq; assert (j - (length m1 + length ops) +
        (length m1 + length ops') = j - length ops + length ops') as Heq
        by abstract omega; rewrite Heq in Hhb'; auto.
  Qed.
  Lemma hb_not_sync_iff : forall m1 ops m2
    (Hnot_sync : Forall not_sync ops) i j
    (Hi : i < length m1 \/ i >= length m1 + length ops)
    (Hj : j < length m1 \/ j >= length m1 + length ops)
    ops' (Hnot_sync' : Forall not_sync ops'),
    happens_before (iapp m1 (iapp ops' m2))
      (adjust_range m1 ops ops' i) (adjust_range m1 ops ops' j) <->
    happens_before (iapp m1 (iapp ops m2)) i j.
  Proof.
    intros; split; intro; [|apply hb_not_sync; auto].
    rewrite <- (adjust_adjust m1 ops ops' Hi);
        rewrite <- (adjust_adjust m1 ops ops' Hj); apply hb_not_sync; auto.
    { unfold adjust_range; clarify; abstract omega. }
    { unfold adjust_range; clarify; abstract omega. }
  Qed.*)

  Lemma hbe_le : forall m i j (Hhbe : hbe m i j), i <= j.
  Proof.
    unfold hbe; intros; destruct Hhbe; clarify.
    generalize (hb_lt H); abstract omega.
  Qed.

  Lemma hb_hbe_trans : forall m i j k, happens_before m i k -> hbe m k j ->
    happens_before m i j.
  Proof.
    intros ? ? ? ? ? Hhbe; unfold hbe in Hhbe; destruct Hhbe; clarify;
      eapply hb_trans; eauto.
  Qed.

  Lemma hbe_hb_trans : forall m i j k, hbe m i k -> happens_before m k j ->
    happens_before m i j.
  Proof.
    intros ? ? ? ? Hhbe; unfold hbe in Hhbe; destruct Hhbe; clarify;
      eapply hb_trans; eauto.
  Qed.

(*  Lemma hb_not_sync_lt : forall m1 ops m2 i j t
    (Hnot_sync : Forall not_sync ops)
    (Ht : Forall (fun op => thread_of op = t) ops)
    (Hhb : happens_before (iapp m1 (iapp ops m2)) i j)
    (Hi : i < length m1) (Hj : length m1 <= j < length m1 + length ops),
    exists k c, k < length m1 /\ hbe (iapp m1 (iapp ops m2)) i k /\
      nth_error m1 k = Some c /\ thread_of c = t.
  Proof.
    intros ? ? ? ? ?; remember (j - i) as d; revert i j Heqd;
      induction d using lt_wf_ind; clarify.
    generalize (hb_prev Hhb); clarify.
    exploit hbe_le; eauto; intro.
    rewrite iapp_inter in H01; auto.
    rewrite iapp_nth in *; clarify.
    exploit nth_error_in; eauto; intro Hin.
    rewrite Forall_forall in *; generalize (Hnot_sync _ Hin); intro Hnot.
    generalize (no_sync _ Hnot x1), (Ht _ Hin); clarify.
    destruct (lt_dec x0 (length m1)); [eexists; eexists; eauto|].
    specialize (H (x0 - i)); use H; [|abstract omega].
    specialize (H _ _ eq_refl (thread_of x));
      repeat rewrite Forall_forall in *; clarify.
    destruct (lt_dec (x0 - length m1) (length ops)); [clarify | abstract omega].
    unfold hbe in *; clarify.
    use H; [eauto | abstract omega].
  Qed.*)

(*  Corollary hb_before : forall m1 ops m2 i j t
    (Hnot_sync : Forall not_sync ops)
    (Ht : Forall (fun op => thread_of op = t) ops)
    (Hhb : happens_before (iapp m1 (iapp ops m2)) i j)
    (Hj : length m1 <= j < length m1 + length ops)
    k (Hk : length m1 <= k < length m1 + length ops) (Hlt : i < k),
    happens_before (iapp m1 (iapp ops m2)) i k.
  Proof.
    intros; generalize (hb_lt Hhb); intro.
    assert (exists c, nth_error ops (k - length m1) = Some c) as [c ?]
      by (apply nth_error_succeeds; abstract omega).
    exploit nth_error_in; eauto; intro Hin.
    destruct (lt_dec i (length m1)).
    - exploit hb_not_sync_lt; eauto; clarify.
      rewrite Forall_forall in Ht; specialize (Ht _ Hin).
      eapply hbe_hb_trans; eauto.
      symmetry in Ht; eapply hb_prog; eauto.
      + abstract omega.
      + rewrite iapp_nth; clarify.
      + rewrite iapp_inter; auto.
    - rewrite Forall_forall in Ht; generalize (Ht _ Hin); intro.
      assert (exists c, nth_error ops (i - length m1) = Some c) as [a ?]
        by (apply nth_error_succeeds; abstract omega).
      exploit nth_error_in; eauto; intro Hin'.
      specialize (Ht _ Hin'); clarify.
      symmetry in H1; eapply hb_prog; eauto.
      + rewrite iapp_inter; auto; abstract omega.
      + rewrite iapp_inter; auto.
  Qed.
  Lemma hb_not_sync_ge : forall m1 ops m2 i j t
    (Hnot_sync : Forall not_sync ops)
    (Ht : Forall (fun op => thread_of op = t) ops)
    (Hhb : happens_before (iapp m1 (iapp ops m2)) i j)
    (Hi : length m1 <= i < length m1 + length ops)
    (Hj : j >= length m1 + length ops),
    exists k c, hbe (iapp m1 (iapp ops m2)) (k + length m1 + length ops) j /\
      inth m2 k = Some c /\ thread_of c = t.
  Proof.
    intros ? ? ? ? ?; remember (j - i) as d; revert i j Heqd;
      induction d using lt_wf_ind; clarify.
    generalize (hb_next Hhb); clarify.
    exploit hbe_le; eauto; intro.
    rewrite iapp_inter in H01; auto.
    exploit nth_error_in; eauto; intro Hin.
    rewrite Forall_forall in *; generalize (Hnot_sync _ Hin); intro Hnot.
    generalize (no_sync _ Hnot x1), (Ht _ Hin); clarify.
    rewrite iapp_nth in *; destruct (lt_dec x0 (length m1)); [abstract omega|].
    rewrite iapp_nth in *; destruct (lt_dec (x0 - length m1) (length ops)).
    - specialize (H (j - x0)); use H; [|abstract omega].
      specialize (H _ _ eq_refl (thread_of x));
        repeat rewrite Forall_forall in *; clarify.
      unfold hbe in *; destruct H02222; [clarify | abstract omega].
      use H; [eauto | abstract omega].
    - eexists; eexists; split; [|split]; eauto.
      assert (x0 - length m1 - length ops + length m1 + length ops = x0)
        as Heq by abstract omega; rewrite Heq; auto.
  Qed.
  Corollary hb_after : forall m1 ops m2 i j t
    (Hnot_sync : Forall not_sync ops)
    (Ht : Forall (fun op => thread_of op = t) ops)
    (Hhb : happens_before (iapp m1 (iapp ops m2)) i j)
    (Hi : length m1 <= i < length m1 + length ops)
    k (Hk : length m1 <= k < length m1 + length ops) (Hlt : k < j),
    happens_before (iapp m1 (iapp ops m2)) k j.
  Proof.
    intros; generalize (hb_lt Hhb); intro.
    assert (exists c, nth_error ops (k - length m1) = Some c) as [c ?]
      by (apply nth_error_succeeds; abstract omega).
    exploit nth_error_in; eauto; intro Hin.
    destruct (lt_dec j (length m1 + length ops)).
    - rewrite Forall_forall in Ht; generalize (Ht _ Hin); intro.
      assert (exists c, nth_error ops (j - length m1) = Some c) as [a ?]
        by (apply nth_error_succeeds; abstract omega).
      exploit nth_error_in; eauto; intro Hin'.
      specialize (Ht _ Hin'); clarify.
      eapply hb_prog; eauto.
      + rewrite iapp_inter; auto.
      + rewrite iapp_inter; auto; abstract omega.
    - exploit hb_not_sync_ge; eauto; [abstract omega | clarify].
      rewrite Forall_forall in Ht; specialize (Ht _ Hin).
      eapply hb_hbe_trans; eauto.
      eapply hb_prog; eauto.
      + abstract omega.
      + rewrite iapp_inter; clarify.
      + rewrite iapp_nth;
          destruct (lt_dec (x + length m1 + length ops) (length m1)); [abstract omega|].
        rewrite iapp_nth; destruct (lt_dec (x + length m1 + length ops -
          length m1) (length ops)); [abstract omega|].
        assert (x + length m1 + length ops - length m1 - length ops = x)
          by abstract omega; clarsimp.
  Qed.*)

  Lemma hb_boundary : forall m1 m2 i j
    (Hhb : happens_before (iapp m1 m2) i j)
    (Hi : i < length m1) (Hj : length m1 <= j),
    exists k k', k < length m1 /\ length m1 <= k' /\
      hbe (iapp m1 m2) i k /\ hbe (iapp m1 m2) k' j /\
      exists a a', nth_error m1 k = Some a /\ inth m2 (k' - length m1) = Some a'
                   /\ (thread_of' a = thread_of' a' \/ synchronizes_with a a').
  Proof.
    intros; induction Hhb.
    - exists i, j; unfold hbe; clarify.
      rewrite iapp_nth in *; clarify.
      destruct (lt_dec j (length m1)); [abstract omega|].
      repeat eexists; eauto.
    - exists i, j; unfold hbe; clarify.
      rewrite iapp_nth in *; clarify.
      destruct (lt_dec j (length m1)); [abstract omega|].
      repeat eexists; eauto.
    - destruct (lt_dec k (length m1)); clarify.
      + exists x, x0; clarify.
        repeat split; eauto.
        eapply hbe_trans; eauto; unfold hbe; clarify.
      + use IHHhb1; [clarify | abstract omega].
        exists x, x0; clarify.
        repeat split; eauto.
        eapply hbe_trans; eauto; unfold hbe; clarify.
  Qed.

  Lemma hb_app'' : forall m1 ops m2 i j ops'
    (Hhb : happens_before (iapp m1 (iapp ops m2)) i j)
    (Hi : ~ i < length m1 + length ops) (Hj : ~ j < length m1 + length ops),
    happens_before (iapp m1 (iapp ops' m2)) (i - length ops + length ops')
         (j - length ops + length ops').
  Proof.
    intros; rewrite iapp_app in *; exploit hb_app'; eauto.
    - rewrite app_length; auto.
    - rewrite app_length; auto.
    - instantiate (1 := (m1 ++ ops')); repeat rewrite app_length.
      assert (i - (length m1 + length ops) + (length m1 + length ops') =
        i - length ops + length ops') as Heq1 by abstract omega; assert (j - (length m1 +
        length ops) + (length m1 + length ops') = j - length ops + length ops') 
        as Heq2 by abstract omega; rewrite Heq1, Heq2; auto.
  Qed.

  Corollary hbe_app'' : forall m1 ops m2 i j ops'
    (Hhb : hbe (iapp m1 (iapp ops m2)) i j)
    (Hi : ~ i < length m1 + length ops) (Hj : ~ j < length m1 + length ops),
    hbe (iapp m1 (iapp ops' m2)) (i - length ops + length ops')
         (j - length ops + length ops').
  Proof. unfold hbe; clarify; left; eapply hb_app''; eauto. Qed.

  Lemma filter_snoc_inv : forall A (f : A -> bool) l l' x
    (Hfilter : filter f l = l' ++ [x]),
    exists l1 l2, l = l1 ++ x :: l2 /\ filter f l1 = l' /\
      Forall (fun a => f a = false) l2.
  Proof.
    intros.
    assert (nth_error (filter f l) (length l') = Some x)
      by (rewrite Hfilter, nth_error_app; clarsimp).
    exploit nth_error_in; eauto; intro.
    rewrite filter_In in *; clarify.
    exploit nth_filter_split; eauto; intros [k1 [k2 Hk]]; clarify.
    symmetry in Hk21.
    rewrite filter_app in *; generalize (app_eq_inv _ _ _ _ Hk21 Hfilter);
      clarify.
    rewrite filter_none_iff in *; eauto.
  Qed.

  Lemma hb_into_inv1 : forall m1 ops m2 i j
    (Hi : i < length m1) (Hj : length m1 <= j < length m1 + length ops)
    (Hhb : happens_before (iapp m1 (iapp ops m2)) i j) ops'
    (Hlen : length ops > 0) (Hlen' : length ops' > 0)
    t (Ht : Forall (fun op => thread_of' op = t) ops)
    (Ht' : Forall (fun op => thread_of' op = t) ops')
    b (Hbefore : forall i op, nth_error m1 i = Some op ->
       touches_block op b = true ->
       happens_before (iapp m1 (iapp ops m2)) i (length m1) /\
       happens_before (iapp m1 (iapp ops' m2)) i (length m1)),
    happens_before (iapp m1 (iapp ops' m2)) i (length m1) \/
      exists k1 k2 a1 a2, hbe (iapp m1 (iapp ops' m2)) i k1 /\
        inth (iapp m1 (iapp ops' m2)) k1 = Some a1 /\ k1 < length m1 /\
        inth (iapp m1 (iapp ops m2)) k2 = Some a2 /\ length m1 <= k2 /\
        synchronizes_with a1 a2 /\ touches_other a2 b = true /\
        hbe (iapp m1 (iapp ops m2)) k2 j.
  Proof.
    intros.
    exploit hb_boundary; eauto; [omega|].
    intros [k1 [k2 [? [? [Hhbe1 [Hhbe2 [a1 [a2 Has]]]]]]]]; clarify.
    destruct (touches_block a1 b) eqn: Hblock.
    { left; eapply hbe_hb_trans; [eapply hbe_app; eauto|].
      eapply Hbefore; eauto. }
    destruct Has22.
    - left; eapply hbe_hb_trans; [eapply hbe_app; eauto|].
      exploit hbe_le; eauto; intro.
      rewrite iapp_nth in Has21; destruct (lt_dec (k2 - length m1)
                                                  (length ops)); [|omega].
      generalize (nth_error_in _ _ Has21); intro Hin.
      rewrite Forall_forall in Ht; specialize (Ht _ Hin).
      generalize (nth_error_succeeds _ Hlen'); intros [c ?].
      exploit nth_error_in; eauto; intro Hin'.
      rewrite Forall_forall in Ht'; specialize (Ht' _ Hin'); clarify.
      eapply hb_prog.
      + auto.
      + rewrite iapp_nth; clarify; eauto.
      + rewrite iapp_inter, minus_diag; eauto; abstract omega.
      + clarsimp.
    - right; repeat eexists; eauto.
      + eapply hbe_app; eauto.
      + rewrite iapp_nth; clarify.
      + rewrite iapp_nth; clarify; omega.
      + eapply touches_sync1; eauto.
  Qed.

  Definition map_index b ops ops' i :=
    find_match (fun op => touches_other op b) ops ops' i.

  Lemma touches_one : forall c b, touches_block c b = false ->
                                  touches_other c b = true.
  Proof. unfold touches_other, negb; clarify. Qed.

  Lemma hb_into1 : forall m1 ops m2 i j
    (Hi : i < length m1) (Hj : length m1 <= j < length m1 + length ops)
    (Hhb : happens_before (iapp m1 (iapp ops m2)) i j) ops'
    (Hlen : length ops > 0) (Hlen' : length ops' > 0)
    t (Ht : Forall (fun op => thread_of' op = t) ops)
    (Ht' : Forall (fun op => thread_of' op = t) ops')
    b (Hfilter : filter (fun op => touches_other op b) ops' =
                 filter (fun op => touches_other op b) ops)
    (Hbefore : forall i op, nth_error m1 i = Some op ->
       touches_block op b = true ->
       happens_before (iapp m1 (iapp ops m2)) i (length m1) /\
       happens_before (iapp m1 (iapp ops' m2)) i (length m1))
    c1 (Hc1 : nth_error m1 i = Some c1)
    c2 (Hc2 : nth_error ops (j - length m1) = Some c2)
    (Htouch : touches_other c1 b = touches_other c2 b),
    happens_before (iapp m1 (iapp ops' m2)) i (length m1) /\
      touches_other c2 b = false \/
    happens_before (iapp m1 (iapp ops' m2)) i
                   (length m1 + map_index b ops ops' (j - length m1)) /\
      touches_other c2 b = true.
  Proof.
    intros; exploit hb_into_inv1; try (apply Hbefore); eauto; intro Hhb'.
    destruct (touches_other c2 b) eqn: Hblock; [right | left]; clarify.
    - exploit find_match_valid; eauto; clarify.
      exploit nth_error_lt; eauto; intro.
      destruct Hhb'; clarify.
      + eapply hb_hbe_trans; eauto.
        unfold map_index; eapply seq_hbe; eauto; omega.
      + eapply hbe_hb_trans; [eapply hbe_app; eauto|].
        exploit hbe_le; eauto; intro.
        rewrite iapp_inter in H12221; [|omega].
        generalize (find_match_valid (fun op => touches_other op b) _ ops' _
          H12221); clarify.
        exploit nth_error_lt; eauto; intro.
        eapply hb_hbe_trans.
        * instantiate (1 := length m1 + map_index b ops ops' (x0 - length m1));
            eapply hb_sync; eauto.
          { omega. }
          { rewrite iapp_inter, minus_plus; auto; unfold map_index; omega. }
        * eapply seq_hbe; eauto; unfold map_index; [split|]; try omega.
          apply plus_le_compat_l.
          rewrite le_lt_or_eq_iff; rewrite <- find_match_mono; eauto.
          destruct (eq_dec x0 j); clarify; omega.
    - destruct (touches_block c1 b) eqn: Hblock'; [|exploit touches_one; eauto;
        clarify].
      specialize (Hbefore _ _ Hc1 Hblock'); clarify.
  Qed.
  
  Lemma hb_into_inv2 : forall m1 ops m2 i j
    (Hi : length m1 <= i < length m1 + length ops)
    (Hj : j >= length m1 + length ops)
    (Hhb : happens_before (iapp m1 (iapp ops m2)) i j) ops'
    (Hlen : length ops > 0) (Hlen' : length ops' > 0)
    t (Ht : Forall (fun op => thread_of' op = t) ops)
    (Ht' : Forall (fun op => thread_of' op = t) ops')
    b (Hafter : forall i op, inth m2 i = Some op -> touches_block op b = true ->
       happens_before (iapp m1 (iapp ops m2))
         (length m1 + length ops - 1) (i + length m1 + length ops) /\
       happens_before (iapp m1 (iapp ops' m2))
         (length m1 + length ops' - 1) (i + length m1 + length ops')),
    happens_before (iapp m1 (iapp ops' m2)) (length m1 + length ops' - 1)
      (j - length ops + length ops') \/
      exists k1 k2 a1 a2, hbe (iapp m1 (iapp ops m2)) i k1 /\
        inth (iapp m1 (iapp ops m2)) k1 = Some a1 /\ k1 < length m1 + length ops
        /\ inth (iapp m1 (iapp ops' m2)) (k2 - length ops + length ops') =
        Some a2 /\ k2 >= length m1 + length ops /\
        synchronizes_with a1 a2 /\ touches_other a1 b = true /\
        hbe (iapp m1 (iapp ops' m2)) (k2 - length ops + length ops')
            (j - length ops + length ops').
  Proof.
    intros.
    rewrite iapp_app in Hhb; exploit hb_boundary; eauto;
      try (rewrite app_length; omega).
    intros [k1 [k2 [? [? [Hhbe1 [Hhbe2 [a1 [a2 Has]]]]]]]];
      rewrite <- iapp_app, app_length in *; clarify.
    destruct (touches_block a2 b) eqn: Hblock.
    { left; eapply hb_hbe_trans; [|eapply hbe_app''; eauto; omega].
      specialize (Hafter _ _ Has21 Hblock); clarify.
      assert (k2 - (length m1 + length ops) + length m1 + length ops' =
        k2 - length ops + length ops') as Heq by omega; rewrite Heq in *;
      auto. }
    destruct Has22.
    - left; eapply hb_hbe_trans; [|eapply hbe_app''; eauto; omega].
      generalize (hbe_le Hhbe1); intro.
      rewrite nth_error_app in Has1; destruct (lt_dec k1 (length m1));
        [omega|].
      generalize (nth_error_in _ _ Has1); intro Hin.
      rewrite Forall_forall in Ht; specialize (Ht _ Hin).
      assert (length ops' - 1 < length ops') by omega.
      exploit nth_error_succeeds; eauto; intros [c ?].
      exploit nth_error_in; eauto; intro Hin'.
      rewrite Forall_forall in Ht'; specialize (Ht' _ Hin'); clarify.
      eapply hb_prog.
      + omega.
      + rewrite iapp_inter; eauto; [|omega].
        rewrite <- NPeano.Nat.add_sub_assoc, minus_plus; clarify; eauto.
      + rewrite iapp_app, iapp_nth, app_length; destruct (lt_dec (k2 -
          length ops + length ops') (length m1 + length ops')); [omega|].
        assert (k2 - length ops + length ops' - (length m1 + length ops') =
          k2 - (length m1 + length ops)) as Heq by omega; rewrite Heq; eauto.
      + clarsimp.
    - right; repeat eexists; eauto.
      + rewrite iapp_app, iapp_nth, app_length; clarify.
      + rewrite iapp_app, iapp_nth, app_length; destruct (lt_dec (k2 -
          length ops + length ops') (length m1 + length ops')); [omega|].
        assert (k2 - length ops + length ops' - (length m1 + length ops') =
          k2 - (length m1 + length ops)) as Heq by omega; rewrite Heq; eauto.
      + eapply touches_sync2; eauto.
      + eapply hbe_app''; eauto; omega.
  Qed.  

  Lemma hb_into2 : forall m1 ops m2 i j
    (Hi : length m1 <= i < length m1 + length ops)
    (Hj : j >= length m1 + length ops)
    (Hhb : happens_before (iapp m1 (iapp ops m2)) i j) ops'
    (Hlen : length ops > 0) (Hlen' : length ops' > 0)
    t (Ht : Forall (fun op => thread_of' op = t) ops)
    (Ht' : Forall (fun op => thread_of' op = t) ops')
    b (Hfilter : filter (fun op => touches_other op b) ops' =
                 filter (fun op => touches_other op b) ops)
    (Hafter : forall i op, inth m2 i = Some op -> touches_block op b = true ->
       happens_before (iapp m1 (iapp ops m2))
         (length m1 + length ops - 1) (i + length m1 + length ops) /\
       happens_before (iapp m1 (iapp ops' m2))
         (length m1 + length ops' - 1) (i + length m1 + length ops'))
    c1 (Hc1 : nth_error ops (i - length m1) = Some c1)
    c2 (Hc2 : inth m2 (j - length m1 - length ops) = Some c2)
    (Htouch : touches_other c1 b = touches_other c2 b),
    happens_before (iapp m1 (iapp ops' m2)) (length m1 + length ops' - 1)
      (j - length ops + length ops') /\ touches_other c2 b = false \/
    happens_before (iapp m1 (iapp ops' m2))
                   (length m1 + map_index b ops ops' (i - length m1))
                   (j - length ops + length ops') /\ touches_other c2 b = true.
  Proof.
    intros; exploit hb_into_inv2; try (apply Hafter); eauto; intro Hhb'.
    destruct (touches_other c2 b) eqn: Hblock; [right | left]; clarify.
    - exploit find_match_valid; eauto; clarify.
      exploit nth_error_lt; eauto; intro.
      destruct Hhb'; clarify.
      + eapply hbe_hb_trans; eauto.
        unfold map_index; eapply seq_hbe; eauto; omega.
      + eapply hb_hbe_trans; eauto.
        generalize (hbe_le H11); intro.
        rewrite iapp_inter in H121; [|omega].
        generalize (find_match_valid (fun op => touches_other op b) _ ops' _
          H121); clarify.
        exploit nth_error_lt; eauto; intro.
        eapply hbe_hb_trans.
        * instantiate (1 := length m1 + map_index b ops ops' (x - length m1));
            eapply seq_hbe; eauto; unfold map_index; [split|]; try omega.
          apply plus_le_compat_l.
          rewrite le_lt_or_eq_iff; rewrite <- find_match_mono; eauto.
          destruct (eq_dec i x); clarify; omega.
        * eapply hb_sync; eauto.
          { unfold map_index; omega. }
          { rewrite iapp_inter, minus_plus; auto; unfold map_index; omega. }
    - destruct (touches_block c2 b) eqn: Hblock'; [|exploit touches_one; eauto;
        clarify].
      specialize (Hafter _ _ Hc2 Hblock'); clarify.
      assert (j - length m1 - length ops + length m1 + length ops' =
        j - length ops + length ops') as Heq by omega; rewrite Heq in *; auto.
  Qed.

  Lemma hb_across : forall m1 ops m2 i j
    (Hi : i < length m1) (Hj : j >= length m1 + length ops)
    (Hhb : happens_before (iapp m1 (iapp ops m2)) i j) ops'
    (Hlen : length ops > 0) (Hlen' : length ops' > 0)
    t (Ht : Forall (fun op => thread_of' op = t) ops)
    (Ht' : Forall (fun op => thread_of' op = t) ops')
    b (Hfilter : filter (fun op => touches_other op b) ops' =
               filter (fun op => touches_other op b) ops)
    (Hbefore : forall i op, nth_error m1 i = Some op ->
       touches_block op b = true ->
       happens_before (iapp m1 (iapp ops m2)) i (length m1) /\
       happens_before (iapp m1 (iapp ops' m2)) i (length m1))
    (Hafter : forall i op, inth m2 i = Some op -> touches_block op b = true ->
       happens_before (iapp m1 (iapp ops m2))
         (length m1 + length ops - 1) (i + length m1 + length ops) /\
       happens_before (iapp m1 (iapp ops' m2))
         (length m1 + length ops' - 1) (i + length m1 + length ops')),
    happens_before (iapp m1 (iapp ops' m2)) i (adjust_range m1 ops ops' j).
  Proof.
    intros.
    exploit hb_boundary; eauto; [abstract omega|].
    intros [k1 [k2 [? [? [Hhbe1 [Hhbe2 [a1 [a2 Has]]]]]]]]; clarify.
    eapply hbe_hb_trans; [eapply hbe_app|]; eauto.
    unfold adjust_range; destruct (lt_dec j (length m1)); [abstract omega|].
    clear dependent i.
    rewrite iapp_nth in *; destruct (lt_dec (k2 - length m1) (length ops)).
    - destruct Hhbe2 as [Hhbe2 | ?]; [|subst; abstract omega].
      rewrite iapp_app in Hhbe2; exploit hb_boundary; eauto;
        try (rewrite app_length; abstract omega).
      intros [k1' [k2' [? [? [Hhbe1' [Hhbe2' [a1' [a2' Has']]]]]]]]; clarify.
      rewrite <- iapp_app, app_length in *.
      eapply hb_hbe_trans; [|eapply hbe_app'']; eauto; try abstract omega.
      clear dependent j.
      generalize (hbe_le Hhbe1'); intro.
      rewrite nth_error_app in *; destruct (lt_dec k1' (length m1));
        [abstract omega|].
      assert (happens_before (iapp m1 (iapp ops' m2)) k1 (length m1) \/
        synchronizes_with a1 a2 /\ touches_other a2 b = true) as Hhb1.
      { destruct (touches_block a1 b) eqn: Hblock.
        { left; eapply Hbefore; eauto. }
        destruct Has22.
        + left; generalize (nth_error_in _ _ Has21); intro Hin.
          rewrite Forall_forall in Ht; specialize (Ht _ Hin).
          generalize (nth_error_succeeds _ Hlen'); intros [c ?].
          exploit nth_error_in; eauto; intro Hin'.
          rewrite Forall_forall in Ht'; specialize (Ht' _ Hin'); clarify.
          eapply hb_prog.
          * auto.
          * rewrite iapp_nth; clarify; eauto.
          * rewrite iapp_inter, minus_diag; eauto; abstract omega.
          * clarsimp.
        + right; clarify.
          eapply touches_sync1; eauto. }
      clear Hbefore.
      assert (happens_before (iapp m1 (iapp ops' m2))
        (length m1 + length ops' - 1) (k2' - length ops + length ops') \/
        synchronizes_with a1' a2' /\ touches_other a1' b = true) as Hhb2.
      { destruct (touches_block a2' b) eqn: Hblock.
        { left; specialize (Hafter _ _ Has'21 Hblock); clarify.
          assert (k2' - (length m1 + length ops) + length m1 + length ops' =
                  k2' - length ops + length ops') as Heq by abstract omega;
            rewrite Heq in *; auto. }
        destruct Has'22.
        + left; generalize (nth_error_in _ _ Has'1); intro Hin.
          rewrite Forall_forall in Ht; specialize (Ht _ Hin).
          assert (length ops' - 1 < length ops') by abstract omega.
          exploit nth_error_succeeds; eauto; intros [c ?].
          exploit nth_error_in; eauto; intro Hin'.
          rewrite Forall_forall in Ht'; specialize (Ht' _ Hin'); clarify.
          eapply hb_prog.
          * abstract omega.
          * rewrite iapp_inter; [|abstract omega].
            rewrite <- NPeano.Nat.add_sub_assoc, minus_plus; clarify; eauto.
          * rewrite iapp_nth; destruct (lt_dec (k2' - length ops + length ops')
              (length m1)); [omega|].
            rewrite iapp_nth; destruct (lt_dec (k2' - length ops + length ops' -
              length m1) (length ops')); [omega|].
            rewrite NPeano.Nat.sub_add_distr in Has'21.
            rewrite plus_minus_comm, NPeano.Nat.add_sub, minus_comm; eauto;
              abstract omega.
          * clarsimp.
        + right; clarify.
          eapply touches_sync2; eauto. }
      clear Hafter.
      destruct Hhb1 as [Hhb1 | Hhb1]; [eapply hb_trans; eauto|];
        destruct Hhb2 as [Hhb2 | Hhb2].
      + eapply hbe_hb_trans; eauto.
        eapply seq_hbe; eauto; omega.
      + clarify.
        exploit find_match_valid; eauto; auto; intro.
        exploit nth_error_lt; eauto; intro.
        eapply hbe_hb_trans.
        * instantiate (1 := length m1 + map_index b ops ops' (k1' - length m1)).
          eapply seq_hbe; eauto; unfold map_index; omega.
        * eapply hb_sync; eauto.
          { unfold map_index; abstract omega. }
          { rewrite iapp_inter, minus_plus; auto; unfold map_index;
              abstract omega. }
          { rewrite iapp_app, iapp_nth, app_length;
              destruct (lt_dec (k2' - length ops + length ops')
                               (length m1 + length ops')); [abstract omega|].
            assert (k2' - length ops + length ops' - (length m1 + length ops') =
              k2' - (length m1 + length ops)) as Heq by abstract omega;
              rewrite Heq; auto. }
      + clarify.
        generalize (find_match_valid (fun op => touches_other op b) _ ops' _
          Has21); clarify.
        exploit nth_error_lt; eauto; intro.
        eapply hb_trans.
        * eapply hb_sync.
          { instantiate (1 := length m1 + map_index b ops ops'
              (k2 - length m1)); abstract omega. }
          { rewrite iapp_nth; clarify; eauto. }
          { rewrite iapp_inter, minus_plus; eauto; unfold map_index;
              abstract omega. }
          { auto. }
        * eapply hbe_hb_trans; eauto.
          eapply seq_hbe; eauto; unfold map_index; omega.
      + clarify.
        generalize (find_match_valid (fun op => touches_other op b) _ ops' _
          Has21); clarify.
        exploit nth_error_lt; eauto; intro.
        eapply hb_trans; [eapply hb_sync; try (apply Hhb11)|].
        { instantiate (1 := length m1 + map_index b ops ops' (k2 - length m1)); 
            unfold map_index; abstract omega. }
        { rewrite iapp_nth; clarify. }
        { rewrite iapp_inter, minus_plus; auto; unfold map_index;
            abstract omega. }
        generalize (find_match_valid (fun op => touches_other op b) _ ops' _
          Has'1); clarify.
        exploit nth_error_lt; eauto; intro.
        eapply hbe_hb_trans; [|eapply hb_sync; eauto].
        instantiate (1 := length m1 + map_index b ops ops' (k1' - length m1)).
        eapply seq_hbe; eauto; unfold map_index; [split|]; try (abstract omega).
        apply plus_le_compat_l.
        rewrite le_lt_or_eq_iff; rewrite <- find_match_mono; eauto.
        destruct (eq_dec k2 k1'); clarify; omega.
        { unfold map_index; abstract omega. }
        { rewrite iapp_inter, minus_plus; auto; unfold map_index;
            abstract omega. }
        { rewrite iapp_app, iapp_nth, app_length;
            destruct (lt_dec (k2' - length ops + length ops')
            (length m1 + length ops')); [abstract omega|].
          assert (k2' - length ops + length ops' - (length m1 + length ops') =
            k2' - (length m1 + length ops)) as Heq
            by (clear - H2; abstract omega); rewrite Heq; auto. }
    - eapply hb_hbe_trans; [|eapply hbe_app'']; eauto; try abstract omega.
      assert (inth (iapp m1 (iapp ops' m2)) k1 = Some a1)
        by (rewrite iapp_nth; clarify).
      assert (inth (iapp m1 (iapp ops' m2)) (k2 - length ops + length ops') =
        Some a2).
      { rewrite iapp_nth; destruct (lt_dec (k2 - length ops + length ops')
          (length m1)); [abstract omega|].
        rewrite iapp_nth; destruct (lt_dec (k2 - length ops + length ops' -
          length m1) (length ops')); [abstract omega|].
        rewrite plus_minus_comm; clarsimp; [|abstract omega].
        rewrite minus_comm; auto; abstract omega. }
      destruct Has22; [eapply hb_prog | eapply hb_sync]; eauto; abstract omega.
  Qed.

  Corollary hb_across' : forall m1 ops' m2 i j
    (Hi : i < length m1) (Hj : j >= length m1 + length ops')
    (Hhb : happens_before (iapp m1 (iapp ops' m2)) i j) ops
    (Hlen : length ops > 0) (Hlen' : length ops' > 0)
    t (Ht : Forall (fun op => thread_of' op = t) ops)
    (Ht' : Forall (fun op => thread_of' op = t) ops')
    b (Hfilter : filter (fun op => touches_other op b) ops' =
                 filter (fun op => touches_other op b) ops)
    (Hbefore : forall i op, nth_error m1 i = Some op ->
                            touches_block op b = true ->
       happens_before (iapp m1 (iapp ops m2)) i (length m1) /\
       happens_before (iapp m1 (iapp ops' m2)) i (length m1))
    (Hafter : forall i op, inth m2 i = Some op -> touches_block op b = true ->
       happens_before (iapp m1 (iapp ops m2))
         (length m1 + length ops - 1) (i + length m1 + length ops) /\
       happens_before (iapp m1 (iapp ops' m2))
         (length m1 + length ops' - 1) (i + length m1 + length ops')),
    happens_before (iapp m1 (iapp ops m2)) i (adjust_range m1 ops' ops j).
  Proof.
    intros; eapply hb_across; eauto.
    - intros; exploit Hbefore; eauto; clarify.
    - intros; exploit Hafter; eauto; clarify.
  Qed.

  Corollary hb_out : forall m1 ops m2 i j
    (Hi : i < length m1 \/ i >= length m1 + length ops)
    (Hj : j < length m1 \/ j >= length m1 + length ops)
    (Hhb : happens_before (iapp m1 (iapp ops m2)) i j) ops'
    (Hlen : length ops > 0) (Hlen' : length ops' > 0)
    t (Ht : Forall (fun op => thread_of' op = t) ops)
    (Ht' : Forall (fun op => thread_of' op = t) ops')
    b (Hfilter : filter (fun op => touches_other op b) ops' =
               filter (fun op => touches_other op b) ops)
    (Hbefore : forall i op, nth_error m1 i = Some op ->
                            touches_block op b = true ->
       happens_before (iapp m1 (iapp ops m2)) i (length m1) /\
       happens_before (iapp m1 (iapp ops' m2)) i (length m1))
    (Hafter : forall i op, inth m2 i = Some op -> touches_block op b = true ->
       happens_before (iapp m1 (iapp ops m2))
         (length m1 + length ops - 1) (i + length m1 + length ops) /\
       happens_before (iapp m1 (iapp ops' m2))
         (length m1 + length ops' - 1) (i + length m1 + length ops')),
    happens_before (iapp m1 (iapp ops' m2)) (adjust_range m1 ops ops' i)
                   (adjust_range m1 ops ops' j).
  Proof.
    intros; generalize (hb_lt Hhb); intro.
    destruct (lt_dec i (length m1)), (lt_dec j (length m1)).
    - unfold adjust_range; clarify.
      eapply hb_app; eauto.
    - unfold adjust_range at 1; clarify.
      eapply hb_across; eauto.
    - omega.
    - unfold adjust_range; clarify.
      eapply hb_app''; eauto; omega.
  Qed.

  Corollary hb_out' : forall m1 ops' m2 i j
    (Hi : i < length m1 \/ i >= length m1 + length ops')
    (Hj : j < length m1 \/ j >= length m1 + length ops')
    (Hhb : happens_before (iapp m1 (iapp ops' m2)) i j) ops
    (Hlen : length ops > 0) (Hlen' : length ops' > 0)
    t (Ht : Forall (fun op => thread_of' op = t) ops)
    (Ht' : Forall (fun op => thread_of' op = t) ops')
    b (Hfilter : filter (fun op => touches_other op b) ops' =
               filter (fun op => touches_other op b) ops)
    (Hbefore : forall i op, nth_error m1 i = Some op ->
                            touches_block op b = true ->
       happens_before (iapp m1 (iapp ops m2)) i (length m1) /\
       happens_before (iapp m1 (iapp ops' m2)) i (length m1))
    (Hafter : forall i op, inth m2 i = Some op -> touches_block op b = true ->
       happens_before (iapp m1 (iapp ops m2))
         (length m1 + length ops - 1) (i + length m1 + length ops) /\
       happens_before (iapp m1 (iapp ops' m2))
         (length m1 + length ops' - 1) (i + length m1 + length ops')),
    happens_before (iapp m1 (iapp ops m2)) (adjust_range m1 ops' ops i)
                   (adjust_range m1 ops' ops j).
  Proof.
    intros; eapply hb_out; eauto.
    - intros; exploit Hbefore; eauto; clarify.
    - intros; exploit Hafter; eauto; clarify.
  Qed.

  End Happens_Before.

  Definition not_read := @not_read block val.

  Require Import Sorting.Permutation.

  Inductive linearization (m m' : list _) : Prop :=
    linI p (Hp : Permutation (interval 0 (length m)) p)
    (Hlen : length m' = length m)
    (Hperm : forall i i', nth_error p i = Some i' ->
       nth_error m' i' = nth_error m i)
    (Hhb : forall i j i' j', nth_error p i = Some i' ->
       nth_error p j = Some j' ->
       (happens_before m i j <-> happens_before m' i' j')).

  Instance lin_refl : Reflexive linearization.
  Proof.
    intro; econstructor.
    - reflexivity.
    - auto.
    - intros; rewrite nth_error_interval in *; clarify.
    - intros; rewrite nth_error_interval in *; clarify; reflexivity.
  Qed.

  Definition read_loc (m : mem) i :=
    match inth m i with
    | Some (Read _ p _, _) => Some p
    | Some (ARW _ p _ _, _) => Some p
    | _ => None
    end.

  Definition read_val (m : mem) i :=
    match inth m i with
    | Some (Read _ _ v, _) => Some v
    | Some (ARW _ _ v _, _) => Some v
    | _ => None
    end.

  Definition write_loc (m : mem) i :=
    match inth m i with
    | Some (Write _ p _, _) => Some (Ptr p)
    | Some (ARW _ p _ _, _) => Some (Ptr p)
    | Some (Alloc _ b _, _) => Some (Block b)
    | Some (Free _ b, _) => Some (Block b)
    | _ => None
    end.

  Definition write_val (m : mem) i :=
    match inth m i with
    | Some (Write _ _ v, _) => Some v
    | Some (ARW _ _ _ v, _) => Some v
    | _ => None
    end.

  Definition can_read m r w := exists p p', read_loc m r = Some p /\
    write_loc m w = Some p' /\ ~independent p' (Ptr p) /\ r <> w /\
    ~(exists w2 p2, write_loc m w2 = Some p2 /\ ~independent p2 (Ptr p) /\
                    happens_before m w w2 /\ happens_before m w2 r) /\
    ~happens_before m r w.

  Definition read_result m r v :=
    exists w, can_read m r w /\ write_val m w = Some v.

  Fixpoint drop_b_reads b (l : list conc_op) :=
    match l with
    | [] => []
    | (Read t p v, s) :: l' =>
        if eq_dec (fst p) b then drop_b_reads b l'
        else (Read t p v, s) :: drop_b_reads b l'
    | (ARW t p v v', s) :: l' =>
        if eq_dec (fst p) b then (Write t p v', s) :: drop_b_reads b l'
        else (ARW t p v v', s) :: drop_b_reads b l'
    | c :: l' => c :: drop_b_reads b l'
    end.
 
  (* drop_b_reads should probably leave the first one. *)
  Definition drop_b_reads' b ops :=
    match ops with
    | [] => []
    | a :: rest => a :: drop_b_reads b rest
    end.

  Definition release_writes m := forall i c s, inth m i = Some (c, s) ->
    sync_le release s -> forall t p v, c <> Read t p v.
  
  Definition lower_con := @block_model.consistent _ _ _ ML.

  Definition consistent m := (forall (ops : list _), iprefix ops m ->
    write_alloc (flatten (map to_seq' ops)) /\
    lower_con (filter not_read (flatten (map to_seq' ops)))) /\
(*    release_writes m /\*)
    forall r v (Hread : read_val m r = Some v), read_result m r v.

  End Mem.

Context (b0 : block).

Section SC.

  (* This definition of sw gives no notion of races under SC.
     But maybe what we really care about are M-races in an SC execution? *)
  Instance SC_base : MM_base := 
    { synchronizes_with := fun _ _ => True }.
  admit.  admit. Defined.
  (* Admits some false properties of the HB relation, but we won't
    use SC's HB anyway. *)

  Lemma hb_list : forall (m : list _) i j (Hhb : happens_before m i j),
    j < length m.
  Proof.
    intros.
    exploit hb_inv; eauto; clarsimp.
    eapply nth_error_lt; eauto.
  Qed.

  Lemma hb_seq : forall m i j a (Hlt : i < j) (Hj : inth m j = Some a),
    happens_before m i j.
  Proof.
    intros.
    exploit inth_lt; eauto; clarify.
    intros; eapply hb_sync; eauto; clarify.
  Qed.

  Corollary hb_triv : forall (m : list _) i j, happens_before m i j <->
    i < j /\ j < length m.
  Proof.
    split; intro.
    - split; [eapply hb_lt | eapply hb_list]; eauto.
    - clarify; exploit nth_error_succeeds; eauto; clarify.
      eapply hb_seq; clarsimp.
  Qed.
      
  Lemma hb_prefix : forall (m1 : list _) m2 i j (Hhb : happens_before m1 i j),
    happens_before (iapp m1 m2) i j.
  Proof.
    intros.
    exploit hb_inv; eauto; clarsimp.
    exploit hb_list; eauto; exploit hb_lt; eauto; intros.
    eapply hb_app; auto.
    - rewrite iapp_nil_ilist; auto.
    - omega.
  Qed.

  Lemma SC_prefix : forall m1 m2 (Hcon : consistent (iapp m1 m2)),
    consistent m1.
  Proof.
    unfold consistent; split; clarify.
    - apply Hcon1.
      etransitivity; [eauto | apply iapp_prefix].
    - specialize (Hcon2 r v); unfold read_val in *; clarify.
      unfold read_result, can_read, read_loc in *.
      rewrite inth_nth_error in *; exploit nth_error_lt; eauto; intro.
      rewrite iapp_nth, Hread1 in *; use Hcon2; destruct Hcon2 as [w [Hcan Hw]].
      exists w; unfold write_val in *; clarify.
      destruct (lt_dec r w).
      { exploit hb_seq; eauto; clarify. }
      unfold write_loc in *; rewrite Hw1 in *.
      rewrite inth_nth_error, iapp_nth in *; destruct (lt_dec w (length m1));
        [clarify | omega].
      repeat eexists; eauto; intro; clarify.
      + contradiction Hcan22221.
        rewrite inth_nth_error in *; exploit nth_error_lt; eauto.
        exists x; rewrite iapp_nth; clarify.
        repeat eexists; eauto; apply hb_prefix; auto.
      + contradiction Hcan22222; apply hb_prefix; auto.
  Qed.

  Lemma can_read_alt : forall m r w, can_read m r w <->
    exists p p', read_loc m r = Some p /\ write_loc m w = Some p' /\
      ~independent p' (Ptr p) /\ w < r /\
      forall w2 p2, write_loc m w2 = Some p2 ->
        ~independent p2 (Ptr p) -> w2 <= w \/ w2 >= r.
  Proof.
    intros; unfold can_read.
    split; clarify; repeat eexists; eauto; try omega; clarify.
    - destruct (lt_dec w r); auto.
      assert (r < w) as Hlt by omega.
      unfold write_loc in *; clarify.
      exploit hb_seq; eauto; clarify.
    - destruct (le_dec w2 w); clarify.
      destruct (ge_dec w2 r); clarify.
      contradiction H22221.
      exists w2; repeat eexists; eauto; unfold read_loc, write_loc in *;
        clarify; eapply hb_seq; eauto; omega.
    - intro Hhb; clarify.
      generalize (hb_lt Hhb221), (hb_lt Hhb222).
      exploit H2222; eauto; omega.
    - intro; exploit hb_lt; eauto; omega.
  Qed.

  Context (val_eq : EqDec_eq val).

  Lemma to_seq_last : forall c,
    exists op, nth_error (to_seq' c) (length (to_seq' c) - 1) = Some op.
  Proof.
    destruct c as (c, ?); destruct c; clarify; eauto.
  Qed.

  Lemma lift_last_write : forall ops p v
    (Hlast : last_op (flatten (map to_seq' ops)) (Ptr p) (MWrite p v)),
    exists w, write_loc ops w = Some (Ptr p) /\ write_val ops w = Some v /\
      forall w2 l2, write_loc ops w2 = Some l2 -> ~independent l2 (Ptr p) ->
        w2 <= w.
  Proof.
    unfold last_op; intros; destruct Hlast as [i [Hlast_mod Hnth]].
    inversion Hlast_mod; rewrite Hnth in Hop1; clarify.
    rewrite inth_nth_error in Hnth; exploit nth_flatten_split; eauto;
      intros [? [opl [? [i' ?]]]]; clarify.
    exploit list_append_map_inv; eauto; intros [ops1 [ops2 ?]]; clarify.
    exists (length ops1); unfold write_loc, write_val.
    rewrite inth_nth_error, nth_error_app, lt_dec_eq, minus_diag.
    destruct ops2; clarify.
    exploit nth_error_in; eauto; intro.
    split; [destruct c as (c, ?); destruct c; clarify; inversion H; clarify|].
    split; [destruct c as (c, ?); destruct c; clarify; inversion H; clarify|].
    intros w2 l2; clarify.
    rewrite inth_nth_error, nth_error_app in *;
      destruct (lt_dec w2 (length ops1)); [omega|].
    destruct (w2 - length ops1) eqn: Hminus; [omega | clarify].
    exploit nth_error_split'; eauto; clarify.
    generalize (to_seq_last x); intros [op ?].
    specialize (Hlast (length (flatten (map to_seq' ops1)) +
      (length (to_seq' c) + (length (flatten (map to_seq' x0)) +
      (length (to_seq' x) - 1)))) op).
    rewrite inth_nth_error in Hlast; repeat rewrite map_app, flatten_app
      in Hlast; clarify.
    rewrite nth_error_app, lt_dec_plus_r, minus_plus in Hlast.
    rewrite nth_error_app, lt_dec_plus_r, minus_plus in Hlast.
    rewrite map_app, flatten_app in Hlast; clarify.
    rewrite nth_error_app, lt_dec_plus_r, minus_plus in Hlast.
    rewrite nth_error_app in Hlast; clarify.
    generalize (nth_error_lt _ _ H21); intro.
    destruct x as (c', ?); destruct c'; clarify; omega.
  Qed.

  Lemma lower_flatten : forall ops w c p
    (Hops : nth_error ops w = Some c) (Hloc : write_loc ops w = Some (Ptr p))
    (Hforall : forall w2 l2, write_loc ops w2 = Some l2 ->
       ~independent l2 (Ptr p) -> w2 <= w),
    last_mod_op (flatten (map to_seq' ops)) (Ptr p)
    (length (flatten (map to_seq' (firstn w ops))) + (length (to_seq' c) - 1)).
  Proof.
    intros.
    exploit nth_error_split'; eauto; intros [ops1 [ops2 ?]]; clarsimp.
    rewrite map_app, flatten_app; simpl.
    generalize (to_seq_last c); intros [op ?].
    econstructor.
    - rewrite inth_nth_error, nth_error_app; clarsimp.
      rewrite nth_error_app; clarsimp.
      destruct (to_seq' c); clarsimp; omega.
    - unfold write_loc in Hloc; rewrite inth_nth_error, nth_error_app in Hloc;
        clarsimp.
      destruct x as (c, ?); destruct c; clarify.
    - unfold write_loc in Hloc; rewrite inth_nth_error, nth_error_app in Hloc;
        clarsimp.
      destruct x as (c, ?); destruct c; clarify.
    - intros.
      rewrite inth_nth_error, nth_error_app in *.
      destruct (lt_dec j (length (flatten (map to_seq' ops1)))); [omega|].
      rewrite nth_error_app in *.
      destruct (lt_dec (j - length (flatten (map to_seq' ops1)))
        (length (to_seq' c))); [omega|].
      exploit nth_flatten_split; eauto; clarify.
      exploit list_append_map_inv; eauto; intros [ops1' [ops2' ?]]; clarify.
      destruct ops2'; clarify.
      specialize (Hforall (length ops1 + (S (length ops1')))
        (block_model.loc_of op2)); unfold write_loc in Hforall.
      rewrite inth_nth_error, nth_error_app, lt_dec_plus_r, minus_plus
        in Hforall; clarify.
      rewrite nth_error_app, lt_dec_eq, minus_diag in Hforall; clarify.
      exploit nth_error_in; eauto; intro.
      destruct c0 as (c', ?); destruct c'; clarify; omega.
  Qed.

  Lemma write_val_ptr : forall m w l v (Hloc : write_loc m w = Some l)
    (Hval : write_val m w = Some v), exists p, l = Ptr p.
  Proof.
    unfold write_loc, write_val; clarsimp.
    destruct x as (c, ?); destruct c; clarify; eauto.
  Qed.

  Lemma read_last : forall (m : list _) r v, read_result m r v <->
    exists p, read_loc m r = Some p /\
      last_op (flatten (map to_seq' (itake r m))) (Ptr p) (MWrite p v).
  Proof.
    unfold read_result; setoid_rewrite can_read_alt; split; clarify.
    - eexists; split; eauto.
      exploit write_val_ptr; eauto; clarify.
      unfold write_val in *; clarify; rewrite inth_nth_error in *.
      destruct (eq_dec x2 x0); clarify.
      exploit (lower_flatten (firstn r m)).
      { rewrite nth_error_firstn.
        instantiate (2 := x); clarify; eauto. }
      { unfold write_loc in *; rewrite inth_nth_error, H21 in *.
        rewrite nth_error_firstn; clarify; eauto. }
      { unfold write_loc; clarify.
        rewrite inth_nth_error, nth_error_firstn in *; clarify.
        specialize (H12222 w2); unfold write_loc in *.
        rewrite inth_nth_error, H1 in *; exploit H12222; eauto; omega. }
      clarsimp.
      eexists; split; eauto.
      rewrite <- (firstn_skipn x (firstn r m)) at 1.
      rewrite map_app, flatten_app, inth_nth_error, nth_error_app,
        lt_dec_plus_r, minus_plus.
      erewrite skipn_n; [|rewrite nth_error_firstn; clarify; eauto].
      unfold write_loc in *; rewrite inth_nth_error, H21 in *.
      destruct x1 as (c, ?); destruct c; clarify.
    - exploit lift_last_write; eauto; intros [w Hw].
      exists w; unfold write_val in *; clarify.
      unfold read_loc, write_loc in *; rewrite Hw211 in *.
      rewrite inth_nth_error, itake_firstn, nth_error_firstn in *; clarify.
      rewrite inth_nth_error; clarify.
      repeat eexists; eauto; clarify.
      specialize (Hw22 w2); rewrite inth_nth_error, nth_error_firstn in *.
      destruct (lt_dec w2 r); [|omega].
      left; eapply Hw22; eauto; clarify.
  Qed.      

  Lemma SC_lower : forall (m : list _)
    (Hread : read_init (flatten (map to_seq' m)))
    (Hwrite : write_alloc (flatten (map to_seq' m))),
    consistent m <-> lower_con (flatten (map to_seq' m)).
  Proof.
    induction m using rev_ind; split; clarify.
    - apply consistent_nil; auto.
    - unfold consistent, read_val; split; clarsimp.
      inversion H0; clarify.
      destruct ops; clarify.
    - rewrite map_app, flatten_app in *.
      generalize (read_init_app _ _ Hread); intro Hread'; clarsimp.
      generalize (write_alloc_app _ _ Hwrite); intro Hwrite'; clarify.
      rewrite to_ilist_app in H.
      exploit SC_prefix; eauto; intro Hcon'.
      rewrite IHm in Hcon'.
      unfold consistent in H; clarify.
      specialize (H1 (m ++ [x])); rewrite to_ilist_app in H1; clarify.
      specialize (H1 (iprefix_refl _)); clarify.
      rewrite map_app, flatten_app, filter_app in *; clarsimp.
      assert (Forall (fun op => block_model.block_of op = block_of' x)
        (to_seq' x)).
      { rewrite Forall_forall; destruct x as (c, ?); destruct c; clarify. }
      setoid_rewrite consistent_core_ops; eauto.
      setoid_rewrite consistent_proj_ops in H12; clarify.
      instantiate (1 := block_of' x) in H122.
      rewrite proj_filter_comm in H122.
      destruct x as (c, ?); destruct c; clarsimp.
      + specialize (H2 (length m)); unfold read_val in H2.
        rewrite iapp_nth, lt_dec_eq, minus_diag in H2; clarify.
        specialize (H2 _ eq_refl).
        generalize (read_last (m ++ [(Read t p v, s)])); rewrite to_ilist_app;
          simpl; intro Hiff; rewrite Hiff in *; clarify.
        rewrite iapp_take in H22; clarsimp.
        rewrite to_ilist_app; simpl; eapply read_consistent_op.
        { rewrite iapp_nil_ilist; auto. }
        unfold read_loc in *; clarify.
        rewrite iapp_nth, lt_dec_eq, minus_diag in *; clarify.
        rewrite last_op_filter.
        rewrite last_op_proj in H22; clarify.
      + specialize (H2 (length m)); unfold read_val in H2.
        rewrite iapp_nth, lt_dec_eq, minus_diag in H2; clarify.
        specialize (H2 _ eq_refl).
        generalize (read_last (m ++ [(ARW t p v v0, s)])); rewrite to_ilist_app;
          simpl; intro Hiff; rewrite Hiff in *; clarify.
        rewrite iapp_take in H22; clarsimp.
        rewrite to_ilist_app; simpl; eapply read_consistent_op.
        { rewrite to_ilist_app in *; auto. }
        unfold read_loc in *; clarify.
        rewrite iapp_nth, lt_dec_eq, minus_diag in *; clarify.
        rewrite last_op_filter.
        rewrite last_op_proj in H22; clarify.
      + apply Forall_filter; auto.
      + rewrite <- filter_app; apply read_init_none.
      + rewrite <- filter_app; apply write_alloc_filter; auto.
    - rewrite map_app, flatten_app in *.
      generalize (read_init_app _ _ Hread); intro Hread'; clarsimp.
      generalize (write_alloc_app _ _ Hwrite); intro Hwrite'; clarify.
      exploit consistent_app; eauto; intro Hcon'.
      rewrite <- IHm in Hcon'.
      unfold consistent in *; split; clarify.
      + exploit iprefix_list_inv'; eauto; intros [l Heq]; clarify.
        exploit to_ilist_inj; eauto; clarify.
        destruct (le_dec (length l) (length m)).
        { symmetry in Heq2; exploit app_eq_inv_ge; eauto; clarify.
          apply Hcon'1, app_prefix. }
        exploit app_eq_inv_ge; eauto; [omega | clarify].
        destruct x1; clarsimp; [apply Hcon'1, iprefix_refl|].
        destruct x1; clarify.
        generalize (consistent_filter _ H Hread Hwrite).
        rewrite map_app, flatten_app; clarsimp.
      + rewrite read_last.
        destruct (lt_dec r (length m)).
        { unfold read_val in *; clarify.
          rewrite inth_nth_error, nth_error_app in *; clarify.
          specialize (Hcon'2 r v); rewrite inth_nth_error, Hread01, read_last
            in Hcon'2; clarify.
          unfold read_loc in *; rewrite inth_nth_error, nth_error_app, Hread01
            in *; clarify.
          eexists; split; eauto; clarsimp.
          destruct (r - length m) eqn: Hminus; [clarsimp | omega]. }
        unfold read_val in *; clarify.
        rewrite inth_nth_error, nth_error_app in *; clarify.
        rewrite nth_error_single in Hread01; clarify.
        unfold read_loc; rewrite inth_nth_error, nth_error_app; clarify.
        rewrite nth_error_single; clarify.
        assert (r = length m) by omega.
        destruct x0 as (c, ?); destruct c; clarify.
        * eexists; split; eauto.
          rewrite to_ilist_app in H; clarify.
          exploit read_justified_op; eauto; clarsimp.
          { rewrite to_ilist_app in *; auto. }
        * eexists; split; eauto.
          rewrite to_ilist_app in H; clarify.
          exploit read_justified_op; eauto; clarsimp.
          { rewrite to_ilist_app in *; auto. }
  Qed.

End SC.

Section HB.

  Definition sw (c1 c2 : conc_op) :=
    match c1, c2 with
    | (a1, s1), (a2, s2) => ~independent (loc_of a1) (loc_of a2) /\
                            sync_le release s1 /\ sync_le acquire s2
    end.

  Instance LLVM_base : MM_base := { synchronizes_with := sw }.
  Proof.
    - unfold sw, touches_other, touches_block; destruct a1, a2; clarify.
      exploit dep_block; eauto; repeat rewrite block_of_loc_spec; clarify.
      unfold negb, beq, block_of' in *; clarify.
    - unfold sw, touches_other, touches_block; destruct a1, a2; clarify.
      exploit dep_block; eauto; repeat rewrite block_of_loc_spec; clarify.
      unfold negb, beq, block_of' in *; clarify.
  Defined.

End HB.

  Lemma private_seq : forall ops t (Ht : Forall (fun c => thread_of' c = t) ops)
    (Hlen : length ops > 0) m1 m2 b
    (Hbefore : forall i op, nth_error m1 i = Some op ->
                            mods_block op b = true ->
       happens_before (iapp m1 (iapp ops m2)) i (length m1))
    (Hafter : forall i op, inth m2 i = Some op -> mods_block op b = true ->
       happens_before (iapp m1 (iapp ops m2))
         (length m1 + length ops - 1) (i + length m1 + length ops))
    (Hread_init : read_init (filter (fun op =>
      if eq_dec (block_model.block_of op) b then not_read op else false)
      (flatten (map to_seq m1)) ++ proj_block (flatten (map to_seq ops)) b))
    (Hwrite_alloc : write_alloc (flatten (map to_seq (m1 ++ ops)))),
    consistent (iapp m1 (iapp ops m2)) <->
    consistent (iapp m1 (iapp (drop_b_reads b ops) m2)) /\
    well_formed (iapp m1 (iapp ops m2)) /\
    exists m1', linearization m1 m1' /\ seq_con (filter (fun op =>
      if eq_dec (block_model.block_of op) b then not_read op else false)
      (flatten (map to_seq m1')) ++ proj_block (flatten (map to_seq ops)) b).
  Admitted.

  Variable (val_eq : EqDec_eq val).

(* Well-synchronized programs *)
  Definition reads m r p v := exists a, inth m r = Some a /\
    In (MRead p v) (to_seq a).
  (* It is very important that a read not be able to justify itself! *)
  Hypothesis reads_safe : forall m r p v a i, reads m r p v ->
    inth m r = Some a -> nth_error (to_seq a) i = Some (MRead p v) ->
    forall j op, j < i -> nth_error (to_seq a) j = Some op ->
                 op_modifies _ op p = false.
  Definition writes m w p v := exists a, inth m w = Some a /\
    In (MWrite p v) (to_seq a).
  Hypothesis writes_safe : forall m w p v a, writes m w p v ->
    inth m w = Some a -> last_op (to_seq a) (Ptr p) (MWrite p v).
  Definition mods m i p := exists a op, inth m i = Some a /\ In op (to_seq a) /\
    op_modifies _ op p = true.

  Definition race_free m := forall i j (Hdiff : i <> j) a b
    (Ha : inth m i = Some a) (Hb : inth m j = Some b)
    (Hint : exists bl op1 op2 o, In op1 (to_seq a) /\ In op2 (to_seq b) /\
      op_modifies _ op1 (bl, o) = true /\ block_of op2 = bl),
    happens_before m i j \/ happens_before m j i.

  Lemma race_free_app : forall m1 m2, race_free (m1 ++ m2) -> race_free m1.
  Proof.
    unfold race_free; intros.
    specialize (H _ _ Hdiff).
    repeat rewrite inth_nth_error, nth_error_app in *.
    generalize (nth_error_lt _ _ Ha), (nth_error_lt _ _ Hb); clarify.
    rewrite to_ilist_app in H.
    exploit H; eauto; [repeat eexists; eauto|].
    intros [Hhb | Hhb]; [left | right]; eapply hb_app_impl;
      eauto.
  Qed.

  Hypothesis touches_block_min : forall a op, In op (to_seq a) ->
    touches_block a (block_of op) = true.

(*  Definition can_read m r w p v := reads m r p v /\ writes m w p v /\ r <> w /\
    (forall k, happens_before m w k -> happens_before m k r ->
       ~mods m k p) /\ ~happens_before m r w.*)
  (* Note that this condition is quite orthogonal to private_seq.
     What does that mean? Is there a similar simplification for private_seq? *)
(*  Hypothesis consistent_iff : forall (m : list _), consistent m <->
    seq_con (filter (@not_read _ _) (flatten (map to_seq m))) /\
      forall r p v, reads m r p v -> exists w, can_read m r w p v.*)

  (* up? *)
  Instance mem_op_eq : EqDec_eq (mem_op block val).
  Proof. eq_dec_inst. Qed.

  Hypothesis read_free : forall (m : list _), (forall r p v, ~reads m r p v) ->
    (consistent m <-> seq_con (flatten (map to_seq m))).

  Definition has_read (c : conc_op) :=
    existsb (fun op => negb (not_read op)) (to_seq c).

  (* We could let m be infinite and do "for all prefixes" instead if we want. *)
  Theorem race_free_SC : forall (b0 : block) (m : list _) (Hrf : race_free m)
    (Hread : read_init (flatten (map to_seq m)))
    (Hwrite : write_alloc (flatten (map to_seq m))) (Hwf : well_formed m),
    consistent m <-> seq_con (flatten (map to_seq m)).
  Proof.
    intros; split; intro Hcon.
    - remember (length (filter (fun op => negb (not_read op))
        (flatten (map to_seq m)))) as nreads; generalize dependent m;
        induction nreads using lt_wf_ind; intros.
      destruct nreads.
      { rewrite <- read_free; auto.
        repeat intro.
        unfold reads in *; clarify.
        destruct (filter (fun op => negb (not_read op))
          (flatten (map to_seq m))) eqn: Hfilter; clarify.
        rewrite filter_none_iff in Hfilter.
        rewrite Forall_forall in Hfilter.
        setoid_rewrite flatten_in in Hfilter.
        setoid_rewrite in_map_iff in Hfilter.
        rewrite inth_nth_error in *; exploit nth_error_in; eauto; intro.
        specialize (Hfilter (MRead p v)); use Hfilter; eauto; clarify. }
      destruct (find has_read (rev m)) eqn: Hfind.
      rewrite find_spec in Hfind; clarify.
      exploit nth_error_rev'; eauto; intro Hnth.
      unfold has_read in Hfind21; rewrite existsb_exists in Hfind21; clarify.
      destruct x0; clarify.
      exploit nth_error_split'; eauto; intros [m1 [m2 ?]]; clarify.
      rewrite split_app in Hcon; rewrite <- app_assoc in Hcon;
        repeat rewrite to_ilist_app in Hcon.
      erewrite private_seq in Hcon.
      instantiate (1 := fst p) in Hcon.
      repeat rewrite <- to_ilist_app in Hcon; clarify.
      specialize (H (length (filter (fun op => negb (not_read op)) (flatten
        (map to_seq (m1 ++ drop_b_reads (fst p) [c] ++ m2)))))).
      use H.
      specialize (H (m1 ++ drop_b_reads (fst p) [c] ++ m2)).
      use H. use H. use H. clarify.
      repeat rewrite map_app, flatten_app in H.
      (* From Hcon22 and H, we should be able to synthesize the result. *)
      admit.
      (* Provable conditions on drop_b_reads. *)
      admit.
      admit.
      admit.
      admit.
      rewrite Forall_forall; clarify.
      clarify.
      admit. (* by Hrf *)
      admit. (* by Hrf *)
      admit.
      admit.
      { rewrite find_fail, Forall_rev in Hfind.
        rewrite filter_none in Heqnreads; clarify.
        rewrite Forall_forall in *; intros ? Hin.
        rewrite flatten_in in Hin; clarify.
        rewrite in_map_iff in Hin2; clarify.
        specialize (Hfind _ Hin22); unfold has_read in *.
        destruct x; clarify.
        assert (existsb (fun op => negb (not_read op)) (to_seq x1) = true);
          clarify.
        rewrite existsb_exists; eauto. }
    - remember (length (filter (fun op => negb (not_read op))
        (flatten (map to_seq m)))) as nreads; generalize dependent m;
        induction nreads using lt_wf_ind; intros.
      destruct nreads.
      { rewrite read_free; auto.
        repeat intro.
        unfold reads in *; clarify.
        destruct (filter (fun op => negb (not_read op))
          (flatten (map to_seq m))) eqn: Hfilter; clarify.
        rewrite filter_none_iff in Hfilter.
        rewrite Forall_forall in Hfilter.
        setoid_rewrite flatten_in in Hfilter.
        setoid_rewrite in_map_iff in Hfilter.
        rewrite inth_nth_error in *; exploit nth_error_in; eauto; intro.
        specialize (Hfilter (MRead p v)); use Hfilter; eauto; clarify. }
      destruct (find has_read (rev m)) eqn: Hfind.
      rewrite find_spec in Hfind; clarify.
      exploit nth_error_rev'; eauto; intro Hnth.
      unfold has_read in Hfind21; rewrite existsb_exists in Hfind21; clarify.
      destruct x0; clarify.
      exploit nth_error_split'; eauto; intros [m1 [m2 ?]]; clarify.
      rewrite split_app; rewrite <- app_assoc; repeat rewrite to_ilist_app.
      erewrite private_seq.
      instantiate (1 := fst p).
      repeat rewrite <- to_ilist_app; clarify.
      split; [|split].
      + eapply H; try reflexivity.
        admit.
        admit.
        admit.
        admit.
        repeat rewrite to_ilist_app in *; apply drop_wf; auto.
        admit.
      + auto.
      + exists m1; split; [reflexivity|].
        admit.
      + rewrite Forall_forall; clarify.
      + clarify.
      + (* by Hrf *) admit.
      + (* by Hrf *) admit.
      + admit.
      + admit.
      + rewrite find_fail, Forall_rev in Hfind.
        rewrite filter_none in Heqnreads; clarify.
        rewrite Forall_forall in *; intros ? Hin.
        rewrite flatten_in in Hin; clarify.
        rewrite in_map_iff in Hin2; clarify.
        specialize (Hfind _ Hin22); unfold has_read in *.
        destruct x; clarify.
        assert (existsb (fun op => negb (not_read op)) (to_seq x1) = true);
          clarify.
        rewrite existsb_exists; eauto.
  Qed.

End Concurrency.