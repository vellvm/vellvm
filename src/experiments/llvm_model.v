(* A formalization of LLVM's concurrency model. *)
Require Import block_model.
Require Import conc_model.
Require Import Ensembles.
Require Import Util.
Require Import Relation_Operators.
Import EquivDec.
Import CoqEqDec.

Set Implicit Arguments.

Section LLVM_model.
  Context `(ML : Memory_Layout).
  Variable (thread : Type).

  Notation ptr := (ptr block).

  Inductive base_op : Type :=
  | Read : thread -> ptr -> val -> base_op
  | Write : thread -> ptr -> val -> base_op
  | ARW : thread -> ptr -> val -> val -> base_op
  | Alloc : thread -> block -> nat -> base_op
  | Free : thread -> block -> base_op
  | Noop : thread -> ptr -> base_op. (* for sync. Is this in LLVM? *)

  Definition to_seq c :=
    match c with
    | Read _ p v => [MRead p v]
    | Write _ p v => [MWrite p v]
    | ARW _ p v v' => [MRead p v; MWrite p v']
    | Alloc _ b n => [MAlloc b n]
    | Free _ b => [MFree b]
    | Noop _ _ => []
    end.

  Definition thread_of c :=
    match c with
    | Read t _ _ => t
    | Write t _ _ => t
    | ARW t _ _ _ => t
    | Alloc t _ _ => t
    | Free t _ => t
    | Noop t _ => t
    end.

  Definition loc_of c :=
    match c with
    | Read _ p _ => Ptr p
    | Write _ p _ => Ptr p
    | ARW _ p _ _ => Ptr p
    | Alloc _ b _ => Block b
    | Free _ b => Block b
    | Noop _ p => Ptr p
    end.

  Definition block_of c :=
    match c with
    | Read _ (b, _) _ => b
    | Write _ (b, _) _ => b
    | ARW _ (b, _) _ _ => b
    | Alloc _ b _ => b
    | Free _ b => b
    | Noop _ (b, _) => b
    end.

  Lemma block_of_loc_spec : forall c, block_of_loc (loc_of c) = block_of c.
  Proof. destruct c; clarify. Qed.

  Section Sync.
 
    Inductive sync : Set := (* Anything lower than monotonic doesn't give us
      a modification order, and so isn't sufficient for critical-section
      reasoning. *) monotonic | acquire | release | acq_rel | seq_cst.
    Global Instance sync_eq : @EqDec sync eq eq_equivalence.
    Proof. eq_dec_inst. Qed.

    Inductive sync_le : sync -> sync -> Prop :=
    | sync_refl : forall s, sync_le s s
    | sync_trans : forall s1 s2 s3 (Hs1 : sync_le s1 s2) (Hs2 : sync_le s2 s3),
                     sync_le s1 s3
    | sync_m_a : sync_le monotonic acquire
    | sync_m_r : sync_le monotonic release
    | sync_a_ar : sync_le acquire acq_rel
    | sync_r_ar : sync_le release acq_rel
    | sync_ar_sc : sync_le acq_rel seq_cst.
    Hint Constructors sync_le.

    Global Instance sync_le_trans : Transitive sync_le.
    Proof. eauto. Qed.

    Lemma sync_le_m_inv : forall s, sync_le s monotonic ->
                                    s = monotonic.
    Proof.
      remember monotonic as s2; intros; induction H; clarify.
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
        | H : sync_le _ monotonic |- _ => generalize (sync_le_m_inv H); clarify
        | H : sync_le seq_cst _ |- _ => generalize (sync_le_sc_inv H); clarify
        | H : sync_le acq_rel _ |- _ => generalize (sync_le_ar_inv H); clarify
        | H : sync_le acquire _ |- _ => generalize (sync_le_a_inv H); clarify
        | H : sync_le release _ |- _ => generalize (sync_le_r_inv H); clarify
      end.
    
    Definition sync_leb s1 s2 :=
      if eq_dec s1 s2 then true else
        match s1, s2 with
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

  (* This would need more for seq_cst. *)
  Definition synchronizes_with (c1 c2 : conc_op) :=
    match c1, c2 with
    | (a1, s1), (a2, s2) => ~independent (loc_of a1) (loc_of a2) /\
                            sync_le release s1 /\ sync_le acquire s2
    end.

  Definition mod_op (c : conc_op) :=
    match c with
    | (Read _ _ _, _) => false
    | _ => true
    end.
  
  Instance LLVM_base : MM_base conc_op :=
    { thread_of := thread_of'; to_seq := to_seq' }.
  Proof.
    - destruct c as (c, ?); destruct c; clarsimp.
      destruct i; clarsimp.
      destruct j; clarsimp.
    - destruct c as (c, ?); destruct c; clarsimp.
      destruct i; clarsimp.
      destruct j; clarsimp.
  Defined.

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

  Notation event := (event(conc_op := conc_op) nat).
  Notation execution := (execution(conc_op := conc_op) nat).

  Variable err : val.

  Definition wf_reads (E : execution) X := forall e (He : events E e) p v
    (Hread : reads (op e) p v), exists w a, w <> e /\ events E w /\
    rf X (id w) (id e) /\ last_op (to_seq' (op w)) (Ptr p) a /\
    match_op err a v /\ ~hb X (id e) (id w) /\
    forall w2, events E w2 -> mods (op w2) p ->
      hb X (id w) (id w2) -> hb X (id w2) (id e) -> False.

  Definition wf_rf (E : execution) X :=
    (forall i j (Hi : rf X i j) i' (Hi' : rf X i' j), i' = i) /\
    (forall i e (He : events E e) (Hi : rf X i (id e)),
      exists p v, reads (op e) p v).

(*  Notation seq_con := (seq_con ML err).*)
  Notation lower m := (flatten (map to_seq' (map (@op conc_op nat) m))).

  Definition wf_lin (E : execution) X := exists l, 
    linearization (events E) (full (events E) X) l /\
    forall i j a b, i < j -> nth_error l i = Some a -> nth_error l j = Some b ->
      synchronizes_with (op a) (op b) -> hb X (id a) (id b).

  Inductive good_mo (E : Ensemble event) X p R := good_moI
    (HR_total : total_on R (fun e => E e /\ mods (op e) p))
    (Hdom : forall i j, R i j -> exists e1 e2, E e1 /\ mods (op e1) p /\
       i = id e1 /\ E e2 /\ mods (op e2) p /\ j = id e2)
    (HcoWR : forall e (He : E e) v (Hp : reads (op e) p v) w (Hw : E w)
       (Hrf : rf X (id w) (id e)) w2 (Hw2 : E w2),
       R (id w) (id w2) -> ~hb X (id w2) (id e))
    (Hacyclic : forall e1 e2 (He1 : E e1) (He2 : E e2)
       (Hfull : full E X (id e1) (id e2)), ~R (id e2) (id e1))
    (Hirrefl : forall i, ~R i i).

  Definition has_mo (E : execution) X := forall p, exists R,
    good_mo (events E) X p R.

  Definition valid E X := wf_reads E X /\ wf_rf E X /\ wf_lin E X /\
    has_mo E X /\ contained (constraints E) (hb X) /\
    transitive_on (hb X) (events E).

  Lemma to_seq_last : forall c (Hc : forall t p, fst c <> Noop t p),
    exists op, nth_error (to_seq' c) (length (to_seq' c) - 1) = Some op.
  Proof.
    destruct c as (c, ?); destruct c; clarify; eauto.
    exploit Hc; eauto; clarify.
  Qed.

  Lemma lower_inv : forall ops i a, nth_error (lower ops) i = Some a ->
    exists i' a', nth_error ops i' = Some a' /\ In a (to_seq' (op a')).
  Proof.
    intros; exploit nth_lower_split; eauto; clarify.
    clear H; exploit nth_error_in; eauto; intro.
    do 2 eexists; rewrite nth_error_split; eauto.
  Qed.

(*  Lemma to_seq_read_inv : forall ops i p v,
    nth_error (lower ops) i = Some (MRead p v) ->
    exists i' op', nth_error ops i' = Some op' /\ read_loc ops i' = Some p /\
                   read_val ops i' = Some v /\
                   i = length (lower (firstn i' ops)).
  Proof.
    intros; exploit nth_lower_split; eauto; intros (? & c & ? & i' & ?);
      clarify.
    do 2 eexists; unfold read_loc, read_val.
    rewrite inth_nth_error, nth_error_split; clarsimp.
    clear H; exploit nth_error_in; eauto; intro.
    destruct c as (c, ?); destruct c; clarify; inversion H; clarify.
    - rewrite nth_error_single in *; clarify.
    - destruct i'; clarify; rewrite nth_error_single in *; clarify.
  Qed.*)

  Fixpoint drop_l_reads p (l : list event) :=
    match l with
    | [] => []
    | e :: l' =>
        match op e with
        | (Read t p' v, s) => 
            if eq_dec p' p then drop_l_reads p l'
            else e :: drop_l_reads p l'
        | (ARW t p' v v', s) =>
            if eq_dec p' p
            then {| op := (Write t p v', s); id := id e |} :: drop_l_reads p l'
            else e :: drop_l_reads p l'
        | _ => e :: drop_l_reads p l'
        end
    end.

  (* drop_b_reads should leave the first sync op intact. *)
  Definition drop_l_read p c :=
    match c with
    | Read t p' v => if eq_dec p' p then Noop t p else c
    | ARW t p' v v' => if eq_dec p' p then Write t p v' else c
    | _ => c
    end.

  Definition drop_l_reads' p ops :=
    match ops with
    | [] => []
    | {| op := (c, s); id := i |} :: l' =>
         {| op := (drop_l_read p c, s); id := i |} :: drop_l_reads p l'
    end.

(*  Definition release_writes (m : ilist event) := forall i c s j,
    inth m i = Some {| op := (c, s); id := j |} ->
    sync_le release s -> match c with Read _ _ _ => False | Noop _ _ => False
      | _ => True end.

  (* up *)
  Lemma adjust_add : forall A l (x : A) n, adjust_range l [] [x] n =
    add_index n (length l).
  Proof.
    intros; unfold adjust_range, add_index; clarify; omega.
  Qed.

  Lemma drop_add : forall n k, drop_index (add_index n k) k = n.
  Proof.
    intros; unfold drop_index, add_index; destruct (lt_dec n k); clarify.
    destruct (lt_dec (S n) k); omega.
  Qed.

  Lemma add_drop : forall n k (Hneq : n <> k), add_index (drop_index n k) k = n.
  Proof.
    intros; unfold drop_index, add_index; destruct (lt_dec n k); clarify.
    destruct (lt_dec (n - 1) k); omega.
  Qed.

  Lemma drop_reads_app : forall b l1 l2, drop_b_reads b (l1 ++ l2) =
    drop_b_reads b l1 ++ drop_b_reads b l2.
  Proof.
    induction l1; clarify.
    rewrite IHl1; destruct (op a) as (c, ?); destruct c; clarify.
  Qed.

  Corollary drop_reads_app' : forall b l1 l2 (Hnil : l1 <> []),
    drop_b_reads' b (l1 ++ l2) = drop_b_reads' b l1 ++ drop_b_reads b l2.
  Proof.
    destruct l1; clarify; rewrite drop_reads_app.
    destruct e as [? (c, ?)]; auto.
  Qed.

  Fixpoint drop_b_index b (l : list event) i :=
    match i with
    | 0 => 0
    | S i =>
        match l with
        | [] => S i
        | {| op := (Read t p v, s); id := _ |} :: l' =>
            if eq_dec (fst p) b then drop_b_index b l' i
            else S (drop_b_index b l' i)
        | c :: l' => S (drop_b_index b l' i)
        end
    end.

  Definition not_dropped b ops i := exists (e : event),
    nth_error ops i = Some e /\ forall t o v s, op e <> (Read t (b, o) v, s).

  Lemma b_index : forall b (ops : list _) i c s j
    (Hi : nth_error ops i = Some {| id := j; op := (c, s) |})
    (Hc : forall t o v, c <> Read t (b, o) v),
    nth_error (drop_b_reads b ops) (drop_b_index b ops i) =
      Some {| id := j; op := (drop_b_read b c, s) |}.
  Proof.
    induction ops; destruct i; clarify.
    - destruct c; clarify.
      destruct p; exploit Hc; eauto; clarify.
    - specialize (IHops _ _ _ _ Hi Hc).
      destruct a as [? (c', ?)]; destruct c'; clarify.
  Qed.

  Definition dropped_read b (m1 ops : list event) r :=
    if lt_dec r (length m1) then false
    else if lt_dec (r - length m1) (length ops) then
      match nth_error ops (r - length m1) with
      | Some {| op := (Read t p v, s); id := _ |} => beq (fst p) b
      | _ => false
      end
    else false.

  Lemma drop_drop_lt : forall b l i c (Hi : nth_error l i = Some c)
    (Hc : forall t o v s, op c <> (Read t (b, o) v, s)),
    drop_b_index b l i < length (drop_b_reads b l).
  Proof.
    induction l; clarsimp.
    destruct i; clarify.
    - destruct c as [? (c, ?)]; destruct c; clarify.
      destruct p; exploit Hc; eauto; clarify.
    - specialize (IHl _ _ Hi Hc).
      destruct a as [? (c', ?)]; destruct c'; clarify; omega.
  Qed.

  Fixpoint add_b_index b (l : list event) i :=
    match l with
    | [] => i
    | {| op := (Read t p v, s); id := _ |} :: l' =>
        if eq_dec (fst p) b then S (add_b_index b l' i)
        else match i with 0 => 0 | S i => S (add_b_index b l' i) end
    | c :: l' => match i with 0 => 0 | S i => S (add_b_index b l' i) end
    end.

  Lemma drop_inv : forall b l i c (Hi : nth_error l i = Some c)
    (Hc : forall t o v s, op c <> (Read t (b, o) v, s)),
    add_b_index b l (drop_b_index b l i) = i.
  Proof.
    induction l; destruct i; clarify.
    - destruct c as [? (c, ?)]; destruct c; clarify.
      destruct p; exploit Hc; eauto; clarify.
    - specialize (IHl _ _ Hi Hc).
      destruct a as [? (c', ?)]; destruct c'; clarify.
  Qed.

  Lemma drop_inv' : forall b l i, drop_b_index b l (add_b_index b l i) = i.
  Proof.
    induction l; destruct i; clarify.
    - destruct a as [? (c, ?)]; destruct c; clarify.
    - destruct a as [? (c, ?)]; destruct c; clarify.
  Qed.

  Lemma b_index' : forall b (ops : list _) i c
    (Hi : nth_error (drop_b_reads b ops) i = Some c),
    nth_error ops (add_b_index b ops i) = Some c \/
    exists t o v v' s j, c = {| op := (Write t (b, o) v', s); id := j |} /\
      nth_error ops (add_b_index b ops i) =
      Some {| op := (ARW t (b, o) v v', s); id := j |}.
  Proof.
    induction ops; clarify.
    destruct a as [? (c', ?)]; destruct c', i; clarify.
    destruct p; right; repeat eexists; eauto.
  Qed.

  Definition drop_b_index' b ops i :=
    match i with
    | 0 => 0
    | S i => S (drop_b_index b (tail ops) i)
    end.
  Definition add_b_index' b ops i :=
    match i with
    | 0 => 0
    | S i => S (add_b_index b (tail ops) i)
    end.

  Definition to_drop_index (m1 : list event) b ops i :=
    if lt_dec i (length m1) then i
    else if lt_dec (i - length m1) (length ops) then
      length m1 + drop_b_index' b ops (i - length m1)
    else i - length ops + length (drop_b_reads' b ops).
      
  Definition from_drop_index (m1 : list event) b ops i :=
    if lt_dec i (length m1) then i
    else if lt_dec (i - length m1) (length (drop_b_reads' b ops)) then
      length m1 + add_b_index' b ops (i - length m1)
    else i - length (drop_b_reads' b ops) + length ops.

*)  

  Lemma drop_l_reads_length : forall p l,
    length (drop_l_reads p l) <= length l.
  Proof.
    induction l; clarify.
    destruct a as [? (c, ?)]; destruct c; clarify; try omega.
    destruct (eq_dec p0 p); clarify; omega.
  Qed.

(*  Lemma add_drop_lt : forall b l i (Hlt : i < length (drop_l_reads b l)),
    add_b_index b l i < length l.
  Proof.
    induction l; clarify.
    destruct a as [? (c, ?)]; destruct c, i; clarify; apply lt_n_S, IHl;
      try omega.
    destruct (eq_dec (fst p) b); clarify; omega.
  Qed.

  Lemma from_drop_nth : forall m1 b ops m2 i,
    inth (iapp m1 (iapp (drop_l_reads' b ops) m2)) i =
    inth (iapp m1 (iapp ops m2)) (from_drop_index m1 b ops i) \/
    exists c s j, inth (iapp m1 (iapp (drop_l_reads' b ops) m2)) i =
      Some {| op := (drop_l_read b c, s); id := j |} /\
      inth (iapp m1 (iapp ops m2)) (from_drop_index m1 b ops i) =
      Some {| op := (c, s); id := j |}.
  Proof.
    intros; unfold from_drop_index.
    destruct (lt_dec i (length m1));
      [|destruct (lt_dec (i - length m1) (length (drop_l_reads' b ops)))];
      clarify.
    - repeat rewrite iapp_nth; clarify.
    - destruct ops; clarify.
      destruct e as [? (c, s)]; clarify.
      destruct (i - length m1) eqn: Hminus; setoid_rewrite Hminus;
        repeat rewrite iapp_nth; clarsimp.
      { right; eauto. }
      clear cond0; setoid_rewrite Hminus in l0;
        rewrite <- NPeano.Nat.succ_lt_mono in l0.
      rewrite iapp_nth; clarify.
      generalize (nth_error_succeeds _ l); clarsimp.
      generalize (add_drop_lt _ _ l); rewrite iapp_nth; clarify.
      exploit b_index'; eauto; intros [? | ?]; clarify.
      right; do 4 eexists; eauto; clarify.
    - repeat rewrite iapp_nth; clarify.
      assert (length m1 <= i) by (apply not_lt; auto).
      assert (i - length m1 >= length (drop_l_reads' b ops))
        by (apply not_lt; auto).
      destruct (lt_dec (i - length (drop_l_reads' b ops) + length ops)
                       (length m1)); [abstract omega|].
      destruct (lt_dec (i - length (drop_l_reads' b ops) + length ops -
                        length m1) (length ops)); [abstract omega|].
      rewrite plus_minus_comm; [|abstract omega].
      rewrite NPeano.Nat.add_sub.
      rewrite minus_comm; [auto | abstract omega].
  Qed.

  Lemma to_from : forall m1 b ops i,
    to_drop_index m1 b ops (from_drop_index m1 b ops i) = i.
  Proof.
    intros; unfold to_drop_index, from_drop_index.
    destruct (lt_dec i (length m1)); clarify.
    destruct (lt_dec (i - length m1) (length (drop_l_reads' b ops))); clarify.
    - rewrite lt_dec_plus_r, minus_plus.
      destruct ops, (i - length m1) eqn: Hminus; clarify; [omega|].
      destruct e as [? (?, ?)]; clarify.
      rewrite <- NPeano.Nat.succ_lt_mono in l; rewrite lt_dec_mono.
      generalize (add_drop_lt _ _ l); clarify.
      rewrite drop_inv'; omega.
    - destruct (lt_dec (i - length (drop_l_reads' b ops) + length ops)
        (length m1)); [omega|].
      destruct (lt_dec (i - length (drop_l_reads' b ops) + length ops -
        length m1) (length ops)); [omega|].
      rewrite NPeano.Nat.add_sub, NPeano.Nat.sub_add; [clarify | omega].
  Qed.
      
  Lemma from_to : forall m1 b ops i (Hdrop : dropped_read b m1 ops i = false),
    from_drop_index m1 b ops (to_drop_index m1 b ops i) = i.
  Proof.
    intros; unfold to_drop_index, from_drop_index.
    destruct (lt_dec i (length m1)); clarify.
    destruct (lt_dec (i - length m1) (length ops)); clarify.
    - rewrite lt_dec_plus_r, minus_plus.
      destruct ops; clarify; [omega|].
      destruct e as [? (?, ?)]; clarify.
      destruct (i - length m1) eqn: Hminus; clarsimp; try omega.
      rewrite <- NPeano.Nat.succ_lt_mono in l; rewrite lt_dec_mono.
      exploit nth_error_succeeds; eauto; clarify.
      unfold dropped_read in *; clarsimp.
      exploit drop_drop_lt; eauto.
      { instantiate (1 := b); repeat intro; unfold beq in *; destruct x;
          clarify. }
      intro; erewrite drop_inv; clarify; [omega | eauto|].
      { intro; unfold beq in *; destruct x; clarify. }
    - destruct (lt_dec (i - length ops + length (drop_l_reads' b ops))
        (length m1)); [omega|].
      destruct (lt_dec (i - length ops + length (drop_l_reads' b ops) -
        length m1) (length (drop_l_reads' b ops))); [omega|].
      rewrite NPeano.Nat.add_sub, NPeano.Nat.sub_add; [auto|].
      destruct (le_dec (length ops) i); [auto | omega].
  Qed.
      
  Lemma add_index_lt : forall b l i j,
    add_b_index b l i < add_b_index b l j <-> i < j.
  Proof.
    induction l; clarify; [reflexivity|].
    destruct a as [? (c, ?)]; destruct c, i, j; clarify; try omega;
      try (destruct (eq_dec (fst p) b));
      try (rewrite <- NPeano.Nat.succ_lt_mono, IHl); omega.
  Qed.

  Lemma add_index_le : forall b l i j,
    add_b_index b l i <= add_b_index b l j <-> i <= j.
  Proof.
    induction l; clarify; [reflexivity|].
    destruct a as [? (c, ?)]; destruct c, i, j; clarify; try omega;
      try (destruct (eq_dec (fst p) b));
      try (rewrite <- NPeano.Nat.succ_le_mono, IHl); omega.
  Qed.

  Lemma from_drop_lt : forall m1 b ops i j,
    from_drop_index m1 b ops i < from_drop_index m1 b ops j <-> i < j.
  Proof.
    unfold from_drop_index; intros.
    destruct (lt_dec j (length m1)), (lt_dec i (length m1)); try omega.
    { destruct (lt_dec (i - length m1) (length (drop_l_reads' b ops))); omega. }
    { destruct (lt_dec (j - length m1) (length (drop_l_reads' b ops))); omega. }
    destruct ops; clarify; [omega|].
    destruct e as [? (?, ?)]; clarify.
    destruct (i - length m1) eqn: Hi, (j - length m1) eqn: Hj; clarify;
      try omega; repeat rewrite lt_dec_mono;
      destruct (lt_dec n1 (length (drop_l_reads b ops)));
      try (destruct (lt_dec n2 (length (drop_l_reads b ops)))); clarify;
      try omega.
    - rewrite <- NPeano.Nat.add_lt_mono_l;
        rewrite <- NPeano.Nat.succ_lt_mono, add_index_lt; omega.
    - generalize (add_drop_lt _ _ l0); split; try omega.
      intro; eapply lt_le_trans; [apply plus_lt_compat_l, lt_n_S; eauto|].
      exploit NPeano.Nat.add_sub_eq_nz; try (apply Hj); clarify.
      transitivity (length m1 + S (length (drop_l_reads b ops)) -
        S (length (drop_l_reads b ops)) + S (length ops)); try omega.
      rewrite NPeano.Nat.add_sub; auto.
    - generalize (add_drop_lt _ _ l0); split; try omega.
      exploit NPeano.Nat.add_sub_eq_nz; try (apply Hi); clarify.
      exploit le_lt_trans; [| apply H1 |].
      { apply plus_le_compat_r.
        rewrite <- NPeano.Nat.add_sub_assoc; [|omega].
        apply plus_le_compat_l, le_0_n. }
      clarsimp.
      generalize (lt_asym _ _ H).
      rewrite <- NPeano.Nat.add_lt_mono_l in *;
        rewrite <- NPeano.Nat.succ_lt_mono in *; clarify.
  Qed.

  Lemma drop_l_thread : forall b c, thread_of (drop_l_read b c) = thread_of c.
  Proof.
    destruct c; clarify.
  Qed.

  Corollary drop_l_thread' : forall b c s, thread_of' (drop_l_read b c, s) =
    thread_of' (c, s).
  Proof. unfold thread_of'; clarify; apply drop_l_thread. Qed.
  Hint Rewrite drop_l_thread'.

  Lemma drop_l_loc : forall b c, loc_of (drop_l_read b c) = loc_of c.
  Proof.
    destruct c; clarify.
  Qed.
  Hint Rewrite drop_l_loc.

  Lemma drop_l_sync1 : forall b c s c',
    synchronizes_with (drop_l_read b c, s) c' <-> synchronizes_with (c, s) c'.
  Proof.
    destruct c'; clarsimp; reflexivity.
  Qed.

  Lemma drop_l_sync2 : forall b c s c',
    synchronizes_with c' (drop_l_read b c, s) <-> synchronizes_with c' (c, s).
  Proof.
    destruct c'; clarsimp; reflexivity.
  Qed.
  Hint Rewrite drop_l_sync1 drop_l_sync2.

  Lemma drop_thread : forall t b ops
    (Ht : Forall (fun e => thread_of' (op e) = t) ops),
    Forall (fun e => thread_of' (op e) = t) (drop_l_reads b ops).
  Proof.
    induction ops; clarify.
    inversion Ht; clarify.
    destruct a as [? (c, ?)]; destruct c; clarify.
  Qed.

  Corollary drop_thread' : forall t b ops
    (Ht : Forall (fun e => thread_of' (op e) = t) ops),
    Forall (fun e => thread_of' (op e) = t) (drop_l_reads' b ops).
  Proof.
    destruct ops; clarify.
    destruct e as [? (?, ?)]; clarify.
    inversion Ht; constructor; clarsimp.
    apply drop_thread; auto.
  Qed.

  Lemma from_drop_length : forall m1 b ops,
    from_drop_index m1 b ops (length m1) = length m1.
  Proof.
    unfold from_drop_index; clarsimp.
    destruct ops; clarsimp.
    destruct e as [? (?, ?)]; clarify.
  Qed.

  Lemma to_drop_length : forall m1 b ops,
    to_drop_index m1 b ops (length m1) = length m1.
  Proof.
    unfold to_drop_index; intros.
    rewrite lt_dec_eq, minus_diag.
    destruct ops; clarsimp.
  Qed.

  Lemma to_drop_nth : forall m1 b ops m2 i
    (Hdrop : dropped_read b m1 ops i = false),
    inth (iapp m1 (iapp ops m2)) i =
    inth (iapp m1 (iapp (drop_l_reads' b ops) m2)) (to_drop_index m1 b ops i) \/
    exists t o v v' s j, inth (iapp m1 (iapp (drop_l_reads' b ops) m2))
      (to_drop_index m1 b ops i) =
      Some {| op := (Write t (b, o) v', s); id := j |} /\
      inth (iapp m1 (iapp ops m2)) i =
      Some {| op := (ARW t (b, o) v v', s); id := j |}.
  Proof.
    unfold dropped_read, to_drop_index; intros; repeat rewrite iapp_nth.
    destruct (lt_dec i (length m1));
      [|destruct (lt_dec (i - length m1) (length ops))]; clarify.
    - rewrite lt_dec_plus_r, minus_plus.
      destruct ops; clarify; [omega|].
      destruct e as [? (?, ?)]; clarify.
      destruct (i - length m1); clarify.
      { destruct b0; clarify; unfold beq in *; clarify.
        destruct p; right; do 3 eexists; eauto. }
      rewrite <- NPeano.Nat.succ_lt_mono in l; rewrite lt_dec_mono.
      destruct (lt_dec (drop_l_index b ops n0)
        (length (drop_l_reads b ops))); clarify.
      generalize (nth_error_succeeds _ l); clarsimp.
      destruct x as [? (c, ?)]; erewrite b_index; eauto.
      + destruct c; unfold beq in *; clarify.
        destruct p; right; do 3 eexists; eauto.
      + destruct c; repeat intro; unfold beq in *; clarify.
        inversion H0; clarify.
      + generalize (nth_error_succeeds _ l); clarify.
        contradiction n2; eapply drop_drop_lt; eauto.
        repeat intro; destruct x as [? (c, ?)]; destruct c; unfold beq in *;
          clarsimp.
    - assert (length m1 <= i) by (apply not_lt; auto).
      assert (i - length m1 >= length ops) by (apply not_lt; auto).
      destruct (lt_dec (i - length ops + length (drop_l_reads' b ops))
                       (length m1)); [omega|].
      destruct (lt_dec (i - length ops + length (drop_l_reads' b ops) -
                        length m1) (length (drop_l_reads' b ops))); [omega|].
      rewrite plus_minus_comm; [|omega].
      rewrite NPeano.Nat.add_sub.
      rewrite minus_comm; [auto | omega].
  Qed.

  Lemma to_drop_nth' : forall m1 b ops m2 i
    (Hi : i < length m1 \/ i >= length m1 + length ops),
    inth (iapp m1 (iapp (drop_l_reads' b ops) m2)) (to_drop_index m1 b ops i) =
    inth (iapp m1 (iapp ops m2)) i.
  Proof.
    intros; unfold to_drop_index.
    destruct (lt_dec i (length m1)).
    - repeat rewrite iapp_nth; clarify.
    - destruct (lt_dec (i - length m1) (length ops)); [omega|].
      repeat rewrite iapp_nth; clarify.
      destruct (lt_dec (i - length ops + length (drop_l_reads' b ops))
        (length m1)); [omega|].
      destruct (lt_dec (i - length ops + length (drop_l_reads' b ops) -
        length m1) (length (drop_l_reads' b ops))); [omega | clarify].
      assert (i - length ops + length (drop_l_reads' b ops) - length m1 -
        length (drop_l_reads' b ops) = i - length m1 - length ops) as Heq;
        [|setoid_rewrite Heq; auto].
      rewrite <- minus_comm, NPeano.Nat.add_sub; [|omega].
      apply minus_comm; omega.
  Qed.
  
  Lemma drop_index_lt : forall b l i j (Hlt : i < j)
    (Hi : not_dropped b l i) (Hj : not_dropped b l j),
    drop_l_index b l i < drop_l_index b l j.
  Proof.
    induction l; destruct i, j; clarify; try omega.
    - destruct a as [? (c, ?)]; destruct c; clarify.
      unfold not_dropped in Hi; clarify.
      destruct p; exploit Hi2; eauto; clarify.
    - destruct a as [? (c, ?)]; destruct c; clarify;
        try (apply lt_n_S, IHl; auto; omega).
      destruct (eq_dec (fst p) b); clarify; [|apply lt_n_S]; apply IHl; auto;
        omega.
  Qed.

  Corollary drop_index_lt' : forall b l i j (Hlt : i < j)
    (Hi : not_dropped b l i) (Hj : not_dropped b l j),
    drop_l_index' b l i < drop_l_index' b l j.
  Proof.
    destruct l; unfold not_dropped; clarsimp.
    destruct i, j; clarify; try omega.
    rewrite <- NPeano.Nat.succ_lt_mono; apply drop_index_lt; try omega;
      unfold not_dropped; eauto.
  Qed.

  Lemma not_dropped_read : forall b m1 ops i
    (Hi : dropped_read b m1 ops i = false)
    (Hrange : length m1 <= i < length m1 + length ops),
    not_dropped b ops (i - length m1).
  Proof.
    unfold dropped_read, not_dropped; intros.
    destruct (lt_dec i (length m1)); [omega | clarify].
    destruct (lt_dec (i - length m1) (length ops)); [clarify | omega].
    generalize (nth_error_succeeds _ l); clarsimp.
    repeat eexists; eauto; repeat intro; unfold beq in *; destruct x; clarify.
  Qed.

  Lemma to_drop_lt : forall m1 b ops i j (Hlt : i < j)
    (Hi : dropped_read b m1 ops i = false)
    (Hj : dropped_read b m1 ops j = false),
    to_drop_index m1 b ops i < to_drop_index m1 b ops j.
  Proof.
    unfold to_drop_index; intros.
    destruct (lt_dec j (length m1)), (lt_dec i (length m1)); try omega.
    { destruct (lt_dec (j - length m1) (length ops)); omega. }
    destruct (lt_dec (j - length m1) (length ops)),
      (lt_dec (i - length m1) (length ops)); try omega.
    - rewrite <- NPeano.Nat.add_lt_mono_l; apply drop_index_lt'; try omega;
        apply not_dropped_read; auto; omega.
    - destruct ops; clarify; [omega|].
      destruct e as [? (?, ?)]; clarify.
      destruct (i - length m1) eqn: Hminus; clarify; try omega.
      rewrite <- NPeano.Nat.succ_lt_mono in l.
      generalize (nth_error_succeeds _ l); clarify.
      exploit drop_drop_lt; eauto.
      { unfold dropped_read in Hi; clarsimp.
        instantiate (1 := b); intro; unfold beq in *; destruct x; clarify. }
      intro; apply plus_le_lt_compat; try omega.
      apply lt_n_S; auto.
  Qed.
  
(*  Lemma adjust_to : forall m1 b ops i
    (Hi : i < length m1 \/ i >= length m1 + length ops),
    to_drop_index m1 b ops i = adjust_range m1 ops (drop_l_reads' b ops) i.
  Proof. intros; unfold to_drop_index, adjust_range; clarify; omega. Qed.*)

(*  Lemma adjust_from : forall m1 b ops i
    (Hi : i < length m1 \/ i >= length m1 + length (drop_l_reads' b ops)),
    from_drop_index m1 b ops i = adjust_range m1 (drop_l_reads' b ops) ops i.
  Proof. intros; unfold from_drop_index, adjust_range; clarify; omega. Qed.*)

  Definition dropped_read' b (m1 ops : list event) r :=
    if lt_dec r (length m1) then false
    else if lt_dec (r - length m1) (length ops) then
      match nth_error ops (r - length m1) with
      | Some {| op := (Read t p v, s); id := _ |} => beq (fst p) b
      | Some {| op := (ARW t p v v', s); id := _ |} => beq (fst p) b
      | _ => false
      end
    else false.

  Lemma to_drop_not : forall m1 b ops m2 i
    (Hi : dropped_read' b m1 ops i = false),
    inth (iapp m1 (iapp (drop_l_reads' b ops) m2)) (to_drop_index m1 b ops i) =
    inth (iapp m1 (iapp ops m2)) i.
  Proof.
    intros; unfold to_drop_index.
    destruct (lt_dec i (length m1));
      [|destruct (lt_dec (i - length m1) (length ops))].
    - repeat rewrite iapp_nth; clarify.
    - unfold dropped_read' in *; clarify.
      exploit nth_error_succeeds; eauto; clarify.
      repeat rewrite iapp_inter; try omega.
      rewrite minus_plus.
      destruct ops; clarify.
      destruct e as [? (?, ?)]; clarify.
      destruct (i - length m1) eqn: Hminus; clarify.
      { destruct b0; unfold beq in *; clarify. }
      destruct x as [? (c, ?)]; erewrite b_index; eauto.
      destruct c; unfold beq in *; clarsimp.
      { repeat intro; clarsimp; unfold beq in *; clarify. }
      { split; [apply le_plus_l|].
        apply plus_lt_compat_l.
        destruct ops; clarify.
        destruct e as [? (?, ?)]; clarify.
        destruct (i - length m1); clarify.
        exploit drop_drop_lt; eauto.
        repeat intro; unfold beq in *; destruct x; clarsimp. }
    - repeat rewrite iapp_nth; clarify.
      destruct (lt_dec (i - length ops + length (drop_l_reads' b ops))
        (length m1)); [omega|].
      destruct (lt_dec (i - length ops + length (drop_l_reads' b ops) -
        length m1) (length (drop_l_reads' b ops))); [omega|].
      assert (i - length ops + length (drop_l_reads' b ops) - length m1 -
        length (drop_l_reads' b ops) = i - length m1 - length ops) as Heq;
        [|rewrite Heq; auto].
      rewrite <- minus_comm, NPeano.Nat.add_sub; [|omega].
      apply minus_comm; omega.
  Qed.

  Lemma dropped' : forall b m1 ops i, dropped_read' b m1 ops i = false ->
    dropped_read b m1 ops i = false.
  Proof.
    unfold dropped_read', dropped_read; clarify.
    destruct (nth_error ops (i - length m1)); clarify.
    destruct e as [? (c, ?)]; destruct c; clarify.
  Qed.

*)

  Lemma drop_l_reads_spec : forall p ops, lower (drop_l_reads p ops) =
    filter (fun op => match op with MRead p' v => negb (beq p' p) | _ => true
                      end) (lower ops).
  Proof.
    induction ops; clarify.
    destruct a as [? (c, ?)]; destruct c; try setoid_rewrite lower_cons;
      clarsimp.
    - unfold negb, beq; destruct (eq_dec p0 p); clarsimp.
    - unfold negb, beq; destruct (eq_dec p0 p); clarsimp.
  Qed.

  Corollary drop_l_reads_spec' : forall p ops, lower (drop_l_reads' p ops) =
    filter (fun op => match op with MRead p' v => negb (beq p' p) | _ => true
                      end) (lower ops).
  Proof.
    destruct ops; clarify.
    destruct e as [? (c, ?)]; clarify.
    rewrite drop_l_reads_spec, filter_app.
    destruct c; clarify.
    - unfold negb, beq; destruct (eq_dec p0 p); clarify.
    - unfold negb, beq; destruct (eq_dec p0 p); clarify.
  Qed.

  Lemma drop_idem : forall b l, drop_l_reads b (drop_l_reads b l) =
    drop_l_reads b l.
  Proof.
    induction l; clarify.
    destruct a as [? (c, ?)]; destruct c; clarsimp.
    destruct (eq_dec p b); clarsimp.
  Qed.

  Corollary drop_idem' : forall b l, drop_l_reads' b (drop_l_reads' b l) =
    drop_l_reads' b l.
  Proof.
    destruct l; clarify.
    destruct e as [? (?, ?)]; clarify; rewrite drop_idem.
    destruct b0; clarify.
  Qed.

(*  Lemma drop_release : forall m1 ops m2 b
    (Hrelease : release_writes (iapp m1 (iapp ops m2))),
    release_writes (iapp m1 (iapp (drop_l_reads' b ops) m2)).
  Proof.
    repeat intro.
    specialize (Hrelease (from_drop_index m1 b ops i)).
    generalize (from_drop_nth m1 b ops m2 i); intros [Hi | Hi]; clarsimp.
    - exploit Hrelease; eauto.
    - destruct x; clarify; exploit Hrelease; eauto; clarify.
  Qed.*)

  Lemma to_seq_block : forall c,
    Forall (fun a => block_model.block_of a = block_of' c) (to_seq' c).
  Proof.
    destruct c as (c, ?); destruct c; clarify.
  Qed.

  Corollary to_seq_proj : forall c,
    proj_block (to_seq' c) (block_of' c) = to_seq' c.
  Proof.
    intro; apply filter_all; eapply Forall_impl; [|apply to_seq_block].
    unfold beq; clarify.
  Qed.

  Definition sync_dec a b : {synchronizes_with a b} + {~synchronizes_with a b}.
  Proof.
    destruct a as (c, ?), b as (d, ?); simpl.
    destruct (indep_dec _ (loc_of c) (loc_of d)); [right; intro; clarify|].
    destruct (sync_leb release s) eqn: Hs; 
      [|right; intro; clarify; rewrite <- sync_leb_spec in *; clarify].
    destruct (sync_leb acquire s0) eqn: Hs0; 
      [|right; intro; clarify; rewrite <- sync_leb_spec in *; clarify].
    left; rewrite sync_leb_spec in *; clarify.
  Defined.

  Variables (thread_eq : EqDec_eq thread) (val_eq : EqDec_eq val).

(*  Lemma to_seq_exclude : forall m b,
    lower (filter (fun op => negb (beq (block_of' op) b)) m) =
    exclude_block (lower m) b.
  Proof.
    induction m; clarify.
    unfold exclude_block; destruct (negb (beq (block_of' a) b)) eqn: Hblock;
      rewrite lower_cons; rewrite IHm; destruct a as (c, ?); destruct c;
      clarify.
  Qed.    *)

  Variable (b0 : block).

  Notation witness := (witness nat).

  Definition dropped p ops (e : event) := In e ops /\
    exists v, reads (op e) p v.

  Definition dlr p (E : execution) (Y : list event * witness) :=
    (drop_l_reads' p (fst Y), {| hb := hb (snd Y); rf := fun i j =>
       rf (snd Y) i j /\ forall e (He : events E e) (Hj : j = id e),
       ~dropped p (fst Y) e |}).

  Notation id := (@id conc_op nat).

  Lemma drop_ids : forall p ops e (Hin : In e (drop_l_reads p ops)),
    exists e', In e' ops /\ id e = id e'.
  Proof.
    induction ops; clarify.
    destruct a as [? (c, ?)]; destruct c; clarify.
    - destruct (eq_dec p0 p); clarify.
      + exploit IHops; eauto; clarify; eauto.
      + destruct Hin; clarify; eauto.
        exploit IHops; eauto; clarify; eauto.
    - destruct Hin; clarify; eauto.
      exploit IHops; eauto; clarify; eauto.
    - destruct (eq_dec p0 p); clarify.
      + destruct Hin; clarify; eauto.
        exploit IHops; eauto; clarify; eauto.
      + destruct Hin; clarify; eauto.
        exploit IHops; eauto; clarify; eauto.
    - destruct Hin; clarify; eauto.
      exploit IHops; eauto; clarify; eauto.
    - destruct Hin; clarify; eauto.
      exploit IHops; eauto; clarify; eauto.
    - destruct Hin; clarify; eauto.
      exploit IHops; eauto; clarify; eauto.
  Qed.

  Lemma drop_ids' : forall p ops e (Hin : In e (drop_l_reads' p ops)), 
    exists e', In e' ops /\ id e = id e'.
  Proof.
    destruct ops; clarify.
    destruct e as [? (c, ?)]; destruct c; clarify.
    - destruct (eq_dec p0 p); clarify.
      + destruct Hin; clarify; eauto.
        exploit drop_ids; eauto; clarify; eauto.
      + destruct Hin; clarify; eauto.
        exploit drop_ids; eauto; clarify; eauto.
    - destruct Hin; clarify; eauto.
      exploit drop_ids; eauto; clarify; eauto.
    - destruct (eq_dec p0 p); clarify.
      + destruct Hin; clarify; eauto.
        exploit drop_ids; eauto; clarify; eauto.
      + destruct Hin; clarify; eauto.
        exploit drop_ids; eauto; clarify; eauto.
    - destruct Hin; clarify; eauto.
      exploit drop_ids; eauto; clarify; eauto.
    - destruct Hin; clarify; eauto.
      exploit drop_ids; eauto; clarify; eauto.
    - destruct Hin; clarify; eauto.
      exploit drop_ids; eauto; clarify; eauto.
  Qed.

  Lemma drop_id_in : forall p ops,
    Included (set_of (map id (drop_l_reads p ops))) (set_of (map id ops)).
  Proof.
    induction ops; repeat intro; unfold Ensembles.In in *; clarify.
    destruct a as [? (c, ?)]; destruct c; clarify;
      try solve [right; apply IHops; auto].
    - destruct (eq_dec p0 p); clarify; right; apply IHops; auto.
    - destruct (eq_dec p0 p); clarify; right; apply IHops; auto.
  Qed.

  Lemma drop_NoDup : forall p ops (Hnodup : NoDup (map id ops)),
    NoDup (map id (drop_l_reads p ops)).
  Proof.
    induction ops; clarify.
    inversion Hnodup as [|?? Hout ?]; clarify.
    assert (~In (id a) (map id (drop_l_reads p ops))).
    { intro; contradiction Hout; eapply drop_id_in; eauto. }
    destruct a as [? (c, ?)]; destruct c; clarify; try (constructor; auto).
    destruct (eq_dec p0 p); constructor; auto.
  Qed.    

  Corollary drop_NoDup' : forall p ops (Hnodup : NoDup (map id ops)),
    NoDup (map id (drop_l_reads' p ops)).
  Proof.
    destruct ops; clarify.
    inversion Hnodup as [|?? Hout ?]; clarify.
    assert (~In (id e) (map id (drop_l_reads p ops))).
    { intro; contradiction Hout; eapply drop_id_in; eauto. }
    destruct e as [? (c, ?)]; destruct c; clarify;
      try (constructor; [|apply drop_NoDup]; auto).
  Qed.

  Lemma drop_read_touches : forall p c s b'
    (Hb : touches (drop_l_read p c, s) b'), touches (c, s) b'.
  Proof.
    destruct c; clarify; unfold touches in *; clarify; eauto.
  Qed.
    
  Lemma drop_read_mods : forall p c s p' (Hb : mods (drop_l_read p c, s) p'),
    mods (c, s) p'.
  Proof.
    destruct c; clarify; unfold mods in *; clarify; eauto.
    exists (MWrite p v0); clarify.
  Qed.
  
  Lemma drop_read : forall p ops e p' v (Hin : In e (drop_l_reads p ops))
    (Hreads : reads (op e) p' v), In e ops /\ p' <> p.
  Proof.
    induction ops; clarify.
    unfold reads in Hreads; destruct a as [? (c, ?)]; destruct c; clarify;
      try (destruct Hin; clarify); try solve [exploit IHops; eauto; clarify].
    - destruct (eq_dec p0 p); clarify.
      + exploit IHops; eauto; clarify.
      + destruct Hin; [|exploit IHops; eauto]; clarify.
        inversion H; clarify.
    - destruct (eq_dec p0 p); clarify.
      + destruct Hin; [|exploit IHops; eauto]; clarify.
      + destruct Hin; [|exploit IHops; eauto]; clarify.
        inversion Hreads; clarify.
  Qed.

  Corollary drop_read' : forall p ops e p' v (Hin : In e (drop_l_reads' p ops))
    (Hreads : reads (op e) p' v), In e ops /\ p' <> p.
  Proof.
    destruct ops; clarify.
    unfold reads in Hreads; destruct e as [? (c, ?)]; destruct c; clarify;
      try (destruct Hin; clarify);
      try solve [exploit drop_read; eauto; clarify].
    - inversion H; clarify.
    - destruct (eq_dec p0 p); clarify.
      inversion Hreads; clarify.
  Qed.

  Corollary drop_read_set : forall E e p ops p' v
    (Hin : forall e, In e ops -> events E e)
    (He : Union (Setminus (events E) (set_of ops))
      (set_of (drop_l_reads' p ops)) e) (Hreads : reads (op e) p' v),
    events E e.
  Proof.
    intros; rewrite Union_spec, Setminus_spec in *; clarify.
    apply Hin; eapply drop_read'; eauto.
  Qed.

  Lemma reads_p_dec : forall p a, (exists v, reads a p v) \/
    ~exists v, reads a p v.
  Proof.
    unfold reads; destruct a as (c, ?); destruct c; clarify;
      try solve [right; intro; clarify].
    - destruct (eq_dec p0 p); clarify; eauto.
      right; intro; clarify.
      inversion H; clarify.
    - destruct (eq_dec p0 p); clarify; eauto.
      right; intro; clarify.
      inversion H; clarify.
  Qed.

  Lemma in_ops_dec : forall E ops (e : event) (He : events E e)
    (Hin : Included (set_of ops) (events E))
    X l (Hlin : linearization (events E) (hb X) l), In e ops \/ ~In e ops.
  Proof.
    intros.
    destruct (find (fun e' => beq (id e') (id e)) ops) eqn: Hfind.
    - left; generalize (find_success _ _ Hfind); unfold beq; intros [He' Heid].
      specialize (Hin _ He').
      unfold linearization in Hlin; clarify.
      rewrite Hlin1 in He; setoid_rewrite Hlin1 in Hin.
      generalize (NoDup_id_inj _ _ _ Hlin21 Hin He); clarify.
    - right; rewrite find_fail in Hfind; intro.
      rewrite Forall_forall in Hfind; specialize (Hfind e); unfold beq in *;
        clarify.
  Qed.    

  Lemma dropped_dec : forall E p ops e (He : events E e)
    (Hin : Included (set_of ops) (events E))
    X l (Hlin : linearization (events E) (hb X) l),
    dropped p ops e \/ ~dropped p ops e.
  Proof.
    intros.
    destruct (in_ops_dec _ _ He Hin _ Hlin).
    - destruct (reads_p_dec p (op e)); unfold dropped; eauto.
      right; intros [? ?]; auto.
    - right; unfold dropped; intro; clarify.
  Qed.

  Lemma drop_not_dropped : forall p ops e (He : In e ops)
    (Hkeep : ~dropped p ops e), In e (drop_l_reads p ops).
  Proof.
    unfold dropped; induction ops; clarify.
    destruct a as [? (c, ?)]; destruct He; clarify.
    - destruct c; clarify.
      + contradiction Hkeep; unfold reads; clarify; eauto.
      + contradiction Hkeep; unfold reads; clarify; eauto.
    - specialize (IHops e); clarify.
      use IHops; [|intro; contradiction Hkeep; clarify; eauto].
      destruct c; clarify.
  Qed.

  Corollary drop_not_dropped' : forall p ops e (He : In e ops)
    (Hkeep : ~dropped p ops e), In e (drop_l_reads' p ops).
  Proof.
    unfold dropped; destruct ops; clarify.
    destruct e as [? (c, ?)]; destruct He; clarify.
    - destruct c; clarify; contradiction Hkeep; unfold reads;
        clarify; eauto.
    - right; apply drop_not_dropped; auto; unfold dropped; intro;
        contradiction Hkeep; clarify; eauto.
  Qed.

  Corollary not_dropped_set : forall E p ops e (Hkeep : ~dropped p ops e)
    (He : events E e) (Hin : Included (set_of ops) (events E))
    X l (Hlin : linearization (events E) (hb X) l),
    Union (Setminus (events E) (set_of ops)) (set_of (drop_l_reads' p ops)) e.
  Proof.
    intros; rewrite Union_spec, Setminus_spec.
    exploit in_ops_dec; eauto; clarify.
    right; apply drop_not_dropped'; auto.
  Qed.
  
  Lemma read_write : forall (c : conc_op) pr vr pw vw (Hreads : reads c pr vr)
    (Hwrites : writes c pw vw), pr = pw /\ exists t s, c = (ARW t pr vr vw, s).
  Proof.
    unfold reads, writes; destruct c as (c, ?); destruct c; clarify.
    inversion Hwrites; clarify.
    inversion Hreads; clarify; eauto.
  Qed.

  Lemma drop_ARW : forall p ops e t v v' s (Hin : In e ops)
    (HARW : op e = (ARW t p v v', s)),
    In (Build_event (id e) (Write t p v', s)) (drop_l_reads p ops).
  Proof.
    induction ops; clarify.
    destruct a as [? (c, ?)]; destruct c; clarify;
      try solve [right; eapply IHops; eauto].
    - destruct (eq_dec p0 p); simpl; [|right]; eapply IHops; eauto.
    - destruct Hin; clarify.
      destruct (eq_dec p0 p); simpl; right; eapply IHops; eauto.
  Qed.

  Corollary drop_ARW' : forall p ops e t v v' s (Hin : In e ops)
    (HARW : op e = (ARW t p v v', s)),
    In (Build_event (id e) (Write t p v', s)) (drop_l_reads' p ops).
  Proof.
    destruct ops; clarify.
    destruct e as [? (?, ?)]; destruct Hin;
      [clarify | right; eapply drop_ARW; eauto].
  Qed.

  Lemma drop_mod_op_inv : forall p ops e p' a (Ha : In a (to_seq' (op e)))
    (Hmods : op_modifies a p' = true)
    (He : In e (drop_l_reads p ops)),
    exists e', In e' ops /\ In a (to_seq' (op e')) /\ id e' = id e.
  Proof.
    induction ops; clarify.
    destruct a as [? (c, ?)]; destruct c; clarify; try solve [destruct He;
      [eauto | exploit IHops; eauto; clarify; eauto]].
    - destruct (eq_dec p0 p); clarify.
      + exploit IHops; eauto; clarify; eauto.
      + destruct He; [clarify | exploit IHops; eauto; clarify; eauto].
    - destruct (eq_dec p0 p); clarify.
      + destruct He; [clarify | exploit IHops; eauto; clarify; eauto].
        do 2 eexists; eauto; clarify.
      + destruct He; [eauto | exploit IHops; eauto; clarify; eauto].
    - exploit IHops; eauto; clarify; eauto.
  Qed.

  Lemma drop_mod_op_inv' : forall p ops e p' a (Ha : In a (to_seq' (op e)))
    (Hmods : op_modifies a p' = true)
    (He : In e (drop_l_reads' p ops)),
    exists e', In e' ops /\ In a (to_seq' (op e')) /\ id e' = id e.
  Proof.
    destruct ops; clarify.
    destruct e as [? (c, ?)]; clarify.
    destruct He; [|exploit drop_mod_op_inv; eauto; clarify; eauto].
    subst; destruct c; clarify; do 2 eexists; eauto; clarify.
  Qed.

  Corollary drop_mods_inv' : forall p ops e p' (Hmods : mods (op e) p')
    (He : In e (drop_l_reads' p ops)),
    exists e', In e' ops /\ mods (op e') p' /\ id e' = id e.
  Proof.
    intros ???? (a & ? & ?) ?.
    exploit drop_mod_op_inv'; eauto; clarify.
    do 2 eexists; eauto; unfold mods; eauto.
  Qed.

  Lemma drop_mods : forall p ops e p' (Hmods : mods (op e) p') (He : In e ops),
    exists e', In e' (drop_l_reads p ops) /\ mods (op e') p' /\ id e' = id e.
  Proof.
    induction ops; clarify.
    destruct a as [? (c, ?)]; destruct He; clarify.
    - unfold mods in Hmods; destruct c; clarify.
      + do 2 eexists; eauto; unfold mods; simpl; do 2 eexists; eauto 2; clarify.
      + destruct (eq_dec p0 p); clarify;
          do 2 eexists; eauto; unfold mods; simpl; do 2 eexists; eauto; clarify.
      + do 2 eexists; eauto; unfold mods; simpl; do 2 eexists; eauto 2; clarify.
      + do 2 eexists; eauto; unfold mods; simpl; do 2 eexists; eauto 2; clarify.
    - specialize (IHops e p'); clarify.
      destruct c; clarify; eauto.
      + destruct (eq_dec p0 p); clarify; eauto.
      + destruct (eq_dec p0 p); clarify; eauto.
  Qed.

  Corollary drop_mods' : forall p ops e p' (Hmods : mods (op e) p')
    (Hin : In e ops),
    exists e', In e' (drop_l_reads' p ops) /\ mods (op e') p' /\ id e' = id e.
  Proof.
    destruct ops; clarify.
    destruct e as [? (c, ?)]; clarify.
    destruct Hin; [|exploit drop_mods; eauto; clarify; eauto].
    destruct c; clarify; eauto.
    - unfold mods in *; clarify.
    - unfold mods in *; clarify.
      destruct (eq_dec p0 p).
      + do 2 eexists; eauto; simpl; do 2 eexists; eauto 2; clarify.
      + do 2 eexists; eauto; simpl; do 2 eexists; eauto; clarify.
  Qed.

  Lemma reads_one : forall (c : conc_op) p1 v1 p2 v2 (Hreads1 : reads c p1 v1)
    (Hreads2 : reads c p2 v2), p1 = p2 /\ v1 = v2.
  Proof.
    unfold reads; destruct c as (c, ?); destruct c; clarify.
    - inversion H0; inversion H; clarify.
    - inversion Hreads1; inversion Hreads2; clarify.
  Qed.

  Variable (t0 : thread).
  Definition def := Build_event 0 (Noop t0 (b0, 0), monotonic).

  (* Is this okay here? *)
  Hypothesis hb_dec : forall E X l (Hlin : linearization E (hb X) l)
    i1 i2 (Hi1 : In i1 (map id l)) (He2 : In i2 (map id l)),
    {hb X i1 i2} + {~hb X i1 i2}.

  Notation mem_op := (mem_op block val).

  Lemma drop_read_inv : forall p ops e p' v (Hin : In e ops)
    (Hreads : reads (op e) p' v) (Hneq : p' <> p), In e (drop_l_reads p ops).
  Proof.
    induction ops; clarify.
    unfold reads in Hreads; destruct a as [? (c, ?)]; destruct c; clarify;
      try (destruct Hin; clarify); try solve [exploit IHops; eauto; clarify].
    - inversion H; clarify.
    - inversion Hreads; clarify.
  Qed.

  Corollary drop_read_inv' : forall p ops e p' v (Hin : In e ops)
    (Hreads : reads (op e) p' v) (Hneq : p' <> p), In e (drop_l_reads' p ops).
  Proof.
    destruct ops; clarify.
    destruct e as [? (c, ?)]; destruct Hin; clarify.
    - unfold reads in Hreads; destruct c; clarify.
      + inversion H; clarify.
      + inversion Hreads; clarify.
    - right; eapply drop_read_inv; eauto.
  Qed.    

  Corollary read_drop_set : forall E e p ops p' v
    (He : events E e) (Hreads : reads (op e) p' v)
    (Hin : forall e, In e ops -> events E e)
    l R (Hlin : linearization (events E) R l),
    Union (Setminus (events E) (set_of ops)) (set_of (drop_l_reads' p ops)) 
      e \/ In e ops /\ p' = p.
  Proof.
    intros; rewrite Union_spec, Setminus_spec.
    destruct (in_dec eq_nat_dec (id e) (map id ops)).
    - rewrite in_map_iff in *; clarify.
      generalize (lin_id_inj _ _ Hlin He (Hin _ i2)); clarify.
      destruct (eq_dec p' p); clarify.
      exploit drop_read_inv'; eauto.
    - left; left; clarify.
      intro; contradiction n; rewrite in_map_iff; eauto.
  Qed.

  Lemma drop_writes : forall p ops e p' v (Hwrites : writes (op e) p' v)
    (He : In e ops), exists e', In e' (drop_l_reads p ops) /\
                                writes (op e') p' v /\ id e' = id e.
  Proof.
    induction ops; clarify.
    destruct a as [? (c, ?)]; destruct He; clarify.
    - unfold writes in Hwrites; destruct c; clarify.
      + inversion H; clarify.
        do 2 eexists; eauto; unfold writes; clarify.
      + inversion Hwrites; clarify.
        destruct (eq_dec p' p); simpl; do 2 eexists; eauto;
          unfold writes; clarify.
    - specialize (IHops e p' v); clarify.
      destruct c; clarify; eauto.
      + destruct (eq_dec p0 p); clarify; eauto.
      + destruct (eq_dec p0 p); clarify; eauto.
  Qed.

  Corollary drop_writes' : forall p ops e p' v (Hwrites : writes (op e) p' v)
    (He : In e ops),
    exists e', In e' (drop_l_reads' p ops) /\ writes (op e') p' v /\
               id e' = id e.
  Proof.
    destruct ops; clarify.
    destruct e as [? (c, ?)]; clarify.
    destruct He; [|exploit drop_writes; eauto; clarify; eauto].
    subst; destruct c; clarify; eauto.
    - unfold writes in *; clarify.
    - unfold writes in *; clarify.
      inversion Hwrites; clarify.
      do 2 eexists; eauto; destruct (eq_dec p' p); clarify.
  Qed.

  Lemma write_drop_set : forall E e p ops p' v
    (He : events E e) (Hwrites : writes (op e) p' v)
    (Hin : forall e, In e ops -> events E e)
    l R (Hlin : linearization (events E) R l),
    exists e', Union (Setminus (events E) (set_of ops))
      (set_of (drop_l_reads' p ops)) e' /\ writes (op e') p' v /\ id e' = id e.
  Proof.
    intros.
    destruct (in_dec eq_nat_dec (id e) (map id ops)).
    - rewrite in_map_iff in *; clarify.
      generalize (lin_id_inj _ _ Hlin He (Hin _ i2)); clarify.
      exploit drop_writes'; eauto; intros (e' & He').
      exists e'; clarify; rewrite Union_spec; eauto.
    - exists e; clarify.
      rewrite Union_spec, Setminus_spec; left; clarify.
      intro; contradiction n; rewrite in_map_iff; eauto.
  Qed.

  Lemma mod_drop_set : forall E e p ops p'
    (He : events E e) (Hwrites : mods (op e) p')
    (Hin : forall e, In e ops -> events E e)
    l R (Hlin : linearization (events E) R l),
    exists e', Union (Setminus (events E) (set_of ops))
      (set_of (drop_l_reads' p ops)) e' /\ mods (op e') p' /\ id e' = id e.
  Proof.
    intros.
    destruct (in_dec eq_nat_dec (id e) (map id ops)).
    - rewrite in_map_iff in *; clarify.
      generalize (lin_id_inj _ _ Hlin He (Hin _ i2)); clarify.
      exploit drop_mods'; eauto; intros (e' & He').
      exists e'; clarify; rewrite Union_spec; eauto.
    - exists e; clarify.
      rewrite Union_spec, Setminus_spec; left; clarify.
      intro; contradiction n; rewrite in_map_iff; eauto.
  Qed.

  Lemma drop_mod_op_set : forall E e p ops p' a
    (Hin : forall e, In e ops -> events E e)
    (He : Union (Setminus (events E) (set_of ops))
      (set_of (drop_l_reads' p ops)) e) (Ha : In a (to_seq' (op e)))
    (Hmods : op_modifies a p' = true),
    exists e', events E e' /\ In a (to_seq' (op e')) /\ id e' = id e.
  Proof.
    intros; rewrite Union_spec, Setminus_spec in *.
    destruct He; clarify; eauto.
    exploit drop_mod_op_inv'; eauto; clarify; eauto.
  Qed.

  Corollary drop_mod_set : forall E e p ops p'
    (Hin : forall e, In e ops -> events E e)
    (He : Union (Setminus (events E) (set_of ops))
      (set_of (drop_l_reads' p ops)) e) (Hmods : mods (op e) p'),
    exists e', events E e' /\ mods (op e') p' /\ id e' = id e.
  Proof.
    intros; destruct Hmods as (? & ? & ?); exploit drop_mod_op_set; eauto.
    clarify; do 2 eexists; unfold mods; eauto.
  Qed.

  Lemma mods_last : forall c p a, last_op (to_seq' c) (Ptr p) a <->
    In a (to_seq' c) /\ op_modifies a p = true.
  Proof.
    destruct c as (c, ?); destruct c; clarify; try rewrite last_single;
      split; clarify.
    - generalize (last_op_mods H); clarify.
      destruct H; destruct x; clarify.
      destruct x; clarsimp.
    - exists 1; clarify.
      econstructor; simpl; eauto 2; clarify.
      destruct j; clarify.
      destruct j; clarsimp.
    - generalize (last_nil H); auto.
  Qed.

  Corollary drop_mod_last_op : forall E e p ops p' a
    (Hin : forall e, In e ops -> events E e)
    (He : Union (Setminus (events E) (set_of ops))
      (set_of (drop_l_reads' p ops)) e)
    (Ha : last_op (to_seq' (op e)) (Ptr p') a),
    exists e', events E e' /\ last_op (to_seq' (op e')) (Ptr p') a /\
               id e' = id e.
  Proof.
    intros.
    rewrite mods_last in Ha; clarify.
    intros; exploit drop_mod_op_set; eauto 2; intros (e' & He'); exists e';
      clarify.
    rewrite mods_last; auto.
  Qed.

  Lemma lower_last : forall (ops : list event) i w p a
    (Hi : nth_error ops i = Some w) (Ha : In a (to_seq' (op w)))
    (Hmods : op_modifies a p = true)
    (Hlast : forall i2 w2, nth_error ops i2 = Some w2 -> mods (op w2) p ->
                           i2 <= i),
    last_op (lower ops) (Ptr p) a.
  Proof.
    intros.
    exploit nth_error_split'; eauto; intros (ops1 & ops2 & ?); clarify.
    rewrite map_app, map_app, flatten_app; simpl.
    rewrite app_assoc, last_op_app; right; split.
    - rewrite last_op_app; left.
      rewrite mods_last; auto.
    - rewrite Forall_forall; intros ? Hin.
      destruct (op_modifies x p) eqn: Hmods'.
      + rewrite flatten_in in *; clarify.
        do 2 (rewrite in_map_iff in *; clarify).
        generalize (in_nth_error _ _ Hin222); intros (i' & ? & Hi').
        specialize (Hlast (length ops1 + S i'));
          rewrite nth_error_plus in Hlast; specialize (Hlast _ Hi').
        use Hlast; [omega | unfold mods; eauto].
      + destruct x; clarify.
  Qed.

  Lemma drop_sync : forall p ops e c (Hsync : synchronizes_with (op e) c)
    (He : In e ops),
    (exists e', In e' (drop_l_reads p ops) /\ synchronizes_with (op e') c /\
                id e' = id e) \/ (exists t v s, op e = (Read t p v, s)).
  Proof.
    induction ops; clarify.
    destruct He; clarify.
    - destruct e as [? (c', ?)]; destruct c'; clarify; try solve [left; eauto].
      + destruct (eq_dec p0 p); clarify; [right | left]; eauto.
      + left; destruct (eq_dec p0 p); clarify; eauto.
    - exploit IHops; eauto; intros [? | ?]; clarify; [left | right]; eauto.
      destruct a as [? (c', ?)]; destruct c'; clarify; eauto.
      + destruct (eq_dec p0 p); clarify; eauto.
      + destruct (eq_dec p0 p); clarify; eauto.
  Qed.        

  Corollary drop_sync' : forall p ops e c (Hsync : synchronizes_with (op e) c)
    (He : In e ops),
    (exists e', In e' (drop_l_reads' p ops) /\ synchronizes_with (op e') c /\
                id e' = id e) \/ (exists t v s, op e = (Read t p v, s)).
  Proof.
    destruct ops; clarify.
    destruct e as [? (c', ?)]; clarify.
    destruct He; clarify.
    - destruct c'; clarify; try solve [left; eauto].
      + destruct (eq_dec p0 p); clarify; [right | left]; eauto.
      + left; destruct (eq_dec p0 p); clarify; eauto.
    - exploit drop_sync; eauto; intros [? | ?]; [left | right]; clarify; eauto.
  Qed.

  Lemma sync_drop_set : forall E e p ops
    (He : events E e) c (Hsync : synchronizes_with (op e) c)
    (Hin : forall e, In e ops -> events E e)
    l R (Hlin : linearization (events E) R l),
    (exists e', Union (Setminus (events E) (set_of ops))
       (set_of (drop_l_reads' p ops)) e' /\ id e' = id e /\ 
       synchronizes_with (op e') c) \/
    (In e ops /\ exists t v s, op e = (Read t p v, s)).
  Proof.
    intros.
    setoid_rewrite Union_spec; setoid_rewrite Setminus_spec.
    destruct (in_dec eq_nat_dec (id e) (map id ops)).
    - rewrite in_map_iff in *; clarify.
      generalize (lin_id_inj _ _ Hlin He (Hin _ i2)); clarify.
      exploit drop_sync'; eauto; intros [? | ?]; [left | right]; clarify; eauto.
    - left; exists e; clarify; left; clarify.
      intro; contradiction n; rewrite in_map_iff; eauto.
  Qed.    

  Notation find_mod c p := (find (fun a => op_modifies a p) (to_seq' c)).

  Lemma reads_cases : forall c, (exists p v, loc_of' c = Ptr p /\ reads c p v /\
    forall p' v', reads c p' v' -> p' = p /\ v' = v) \/
    forall p v, ~reads c p v.
  Proof.
    destruct c as (c, s); destruct c; clarify;
      try solve [right; unfold reads; repeat intro; clarify];
      left; unfold loc_of'; simpl; do 3 eexists; eauto; unfold reads; clarify;
      inversion H; clarify.
  Qed.

  Lemma drop_ids_set : forall E p ops
    (Hin : forall e, In e ops -> events E e)
    e (He : Union (Setminus (events E) (set_of ops))
      (set_of (drop_l_reads' p ops)) e),
    exists e', events E e' /\ id e = id e'.
  Proof.
    intros.
    rewrite Union_spec, Setminus_spec in He; destruct He; clarify; eauto.
    exploit drop_ids'; eauto; clarify; eauto.
  Qed.  

  Lemma R_sub' : forall (E E' : Ensemble event) X R i j
    (HE : forall e, E' e -> exists e', E e' /\ id e = id e')
    (HR : clos_trans (fun i j => full E' X i j \/ R i j) i j),
    clos_trans (fun i j => full E X i j \/ R i j) i j.
  Proof.
    intros; induction HR.
    - apply t_step; clarify.
      left; eapply full_sub'; eauto.
    - eapply t_trans; eauto.
  Qed.

  Definition readsb (c : conc_op) p :=
    match c with
    | (Read _ p' _, _) => beq p' p
    | (ARW _ p' _ _, _) => beq p' p
    | _ => false
    end.

  Lemma reads_spec : forall (c : conc_op) p,
    if readsb c p then exists v, reads c p v else forall v, ~reads c p v.
  Proof.
    destruct c as (c, ?); unfold reads; destruct c; clarify;
      try (intro; clarify).
    - unfold beq; destruct (eq_dec p p0); clarify; eauto; intro; clarify.
      inversion H; clarify.
    - unfold beq; destruct (eq_dec p p0); clarify; eauto; intro; clarify.
      inversion H; clarify.
  Qed.

  Lemma critical_seq : forall (E : execution) X (Hvalid : valid E X) ops
    (Hin : forall e, In e ops -> events E e)
    (Htotal : total_on (hb X) (set_of ops)) a z (Ha : In a ops) (Hz : In z ops) 
    (Hbegin : forall e (He : In e ops), e = a \/ hb X (id a) (id e))
    (Hend : forall e (He : In e ops), e = z \/ hb X (id e) (id z))
    p (Hordered : forall e, events E e -> mods (op e) p ->
       hb X (id e) (id a) \/ In e ops \/ hb X (id z) (id e))
    (Hops : linearization (set_of ops) (hb X) ops)
    ops' X' (Hdrop : dlr p E (ops, X) = (ops', X')),
    exists m1, linearization (before (events E) (full (events E) X) a)
      (full (events E) X) m1 /\ forall i r v (Hr : nth_error ops i = Some r)
      (Hreads : reads (op r) p v),
      match find (fun e => if find_mod (op e) p then true else false)
        (rev (m1 ++ firstn i ops)) with
      | Some w => rf X (id w) (id r) /\
          (exists a, last_op (to_seq' (op w)) (Ptr p) a /\ match_op err a v) /\
          forall r' v' (He' : Union (Setminus (events E) (set_of ops))
            (set_of ops') r') (Hreads : reads (op r') p v')
            (Hord : hb X (id w) (id r')), rf X (id w) (id r') \/ exists w',
            events E w' /\ hb X (id w) (id w') /\ rf X (id w') (id r')
      | None => False
      end.
  Proof.
    intros; destruct Hvalid as (Hreads & Hrf & Hwf & Hmo & ? & Htrans).
    destruct Hwf as (l & Hl & ?).
    exploit (before_lin(conc_op := conc_op) eq_nat_dec); try apply Hl; eauto.
    { admit. (* full must be decidable *) }
    { rewrite <- (lin_set Hl); apply Hin, Ha. }
    { apply clos_trans_trans. }
    intros (m1 & m2 & Hm1 & Hm).
    destruct (find_before (fun e => readsb (op e) p) (fun e =>
        match find_mod (op e) p with Some _ => true | _ => false end) ops)
        eqn: Hfind.
    - rewrite find_before_spec in Hfind.
      destruct Hfind as (r & Hr & ? & Hfirst).
      generalize (reads_spec (op e) p); intro Hread; clarify.
      generalize (Hreads e); intro Hw.
      exploit nth_error_in; eauto; clarify.
      specialize (Hw _ _ Hread); destruct Hw as (w & a' & Hw); clarify.
      exploit last_mods; eauto; intro.
      assert (before (events E) (hb X) a w).
      { unfold before; clarify.
        specialize (Hordered w); clarify.
        destruct Hordered as [Hw | Hw].
        + specialize (Htotal w e); clarify.
          destruct Htotal as [? | [? | ?]]; clarify.
          exploit (lin_order_2 Hops w); eauto; intros (i' & ?).
          generalize (mods_spec (op w) p).
          specialize (Hfirst i' w); clarify.
        + specialize (Hend e); clarify.
          specialize (Htrans e z w); clarify. }
      exploit (lin_reorder_last eq_nat_dec).
      { apply Hm1. }
      { unfold before in *; clarify; split; eauto.
        apply t_step; repeat eexists; auto; left; auto. }
      { eauto. }
      { apply clos_trans_trans. }
      { unfold before in *; clarify.
        specialize (Hmo p); destruct Hmo as (R & Hmo); inversion Hmo.
        specialize (HR_total w e'); clarify.
        intro; destruct HR_total as [HR | [? | ?]].
        exploit HcoWR; try apply HR; try apply Hw221; eauto.
        assert (hb X (id e') (id a)).
        { specialize (Hordered e'); clarify.
          assert (e' = a \/ hb X (id a) (id e')) as [? | ?].
          { destruct Hordered; clarify.
            right; eapply end_trans; try apply Hend; eauto. }
          * subst; exploit (lin_irrefl Hl); eauto 2; clarify.
          * exploit (lin_antisym Hl e' a); eauto 2; clarify.
            apply t_step; repeat eexists; auto; left; auto. }
        eapply begin_trans; try apply Hbegin; eauto.
        { subst; exploit (lin_irrefl Hl); eauto. }
        { specialize (Hacyclic w e'); clarify. } }
      { admit. }
      intros (m1' & Hm1' & Hwrite); exists m1'; clarify.
      rewrite rev_app_distr, find_app.
      exploit nth_error_in; eauto; intro.
      exploit Hreads; try apply Hreads0; eauto; intros (w' & a2 & Hw'); clarify.
      exploit (last_mods (op w')); eauto; intro.
      destruct (find (fun e => if find_mod (op e) p then true else false)
        (rev (firstn i ops))) eqn: Hfind.
      + rewrite find_spec in Hfind; generalize (mods_spec (op e0) p);
          clarify.
        exploit nth_error_rev'; eauto; intro Hi'.
        rewrite nth_error_firstn in *; clarify.
        exploit (total_lin_nth Hops Htotal Hi' Hr0); auto; intro.
        exploit nth_error_in; eauto; intro.
        generalize (Hordered w'), (Hw'222222 e0); intros Hw' Hhb.
        use Hw'; use Hw'.
        destruct Hw' as [? | [Hw' | ?]].
        * exfalso; apply Hhb; auto.
          eapply begin_trans; try apply Hbegin; eauto.
        * generalize (in_nth_error _ _ Hw'); intros (i2 & ? & Hi2).
          destruct (lt_dec i2 (length (firstn i ops) - x0 - 1)).
          { exploit (total_lin_nth Hops Htotal Hi2 Hi'); clarify. }
          destruct (eq_dec i2 (length (firstn i ops) - x0 - 1)).
          { subst; rewrite Hi2 in Hi'; clarify.
            split; [eauto | clarify].
            unfold dlr in *; clarify.
            exploit drop_read_set; eauto; intro.
            exploit Hreads; eauto 2; intros (w'' & a'' & Hw''); clarify.
            exploit last_mods; eauto; intro.
            specialize (Hw''222222 e0); specialize (Hw'222222 w''); clarify.
            specialize (Hordered w''); clarify.
            destruct Hordered as [? | [? | ?]].
            * exfalso; apply Hw''222222; auto.
              eapply begin_trans; try apply Hbegin; eauto.
            * specialize (Htotal w'' e0); clarify; eauto.
            * right; exists w''; clarify.
              eapply end_trans; try apply Hend; eauto. }
          destruct (lt_dec i2 i).
          { specialize (Hfind22 (length (firstn i ops) - i2 - 1) w');
              use Hfind22. use Hfind22.
            generalize (mods_spec (op w') p); clarify.
            { apply nth_error_rev; rewrite nth_error_firstn; clarify. }
            { clear - Hr0 Hfind1 n n0 l1.
              assert (length (firstn i ops) - x0 - 1 < i2) by abstract omega.
              generalize (nth_error_lt _ _ Hr0); intros.
              rewrite <- NPeano.Nat.sub_add_distr.
              rewrite (NPeano.Nat.add_lt_mono_r _ _ (i2 + 1)),
              NPeano.Nat.sub_add; [abstract omega|].
              rewrite List.firstn_length, Min.min_l; abstract omega. } }
          destruct (eq_dec i2 i).
          { subst; rewrite Hi2 in Hr0; clarify. }
          { assert (i < i2) by (clear - n1 n2; abstract omega).
            exploit (total_lin_nth Hops Htotal Hr0 Hi2); clarify. }
        * contradiction Hw'222221; eapply end_trans; try apply Hend; eauto.
      + rewrite Hwrite.
        destruct (lt_dec i r).
        { specialize (Hfirst i r0); generalize (reads_spec (op r0) p);
            intro Hno; clarify.
          exploit Hno; eauto; clarify. }
        destruct (eq_dec i r).
        { subst; rewrite Hr0 in Hr; clarify.
          assert (x = v).
          { unfold reads in *; destruct (op e) as (c, ?); destruct c; clarify;
              repeat match goal with H : MRead _ _ = MRead _ _ |- _ =>
                                     inversion H; clear H; clarify end. }
          subst; split; [eauto | intros].
          unfold dlr in *; clarify.
          exploit drop_read_set; eauto; intro.
          exploit Hreads; eauto 2; intros (w'' & a'' & Hw''); clarify.
          exploit last_mods; eauto; intro.
          specialize (Hw''222222 w); specialize (Hw222222 w''); clarify.
          specialize (Hordered w''); unfold before in *; clarify.
          destruct Hordered as [? | [? | ?]].
          * specialize (Hmo p); destruct Hmo as (R & Hmo); inversion Hmo.
            specialize (HR_total w w''); clarify.
            destruct HR_total as [HR | [? | HR]]; clarify.
            { exploit HcoWR; try apply HR; try apply Hreads0; clarify.
              eapply begin_trans; try apply Hbegin; eauto. }
            { exploit HcoWR; try apply HR; try apply Hreads1; clarify. }
          * right; exists w''; clarify.
            eapply begin_trans; try apply Hbegin; eauto.
          * right; exists w''; clarify.
            apply (Htrans _ a); auto.
            eapply end_trans; try apply Hend; eauto. }
        assert (r < i) by (clear - n n0; abstract omega).
        exploit (Hordered w'); eauto; intros [? | [Hw'2 | ?]].
        specialize (Hmo p); destruct Hmo as (mo & Hmo); inversion Hmo.
        exploit (HR_total w w'); eauto; intros [? | [? | ?]].
        * specialize (HcoWR e); use HcoWR.
          specialize (HcoWR _ Hread w); clarify.
          specialize (HcoWR w'); clarify.
          contradiction HcoWR; eapply begin_trans; try apply Hbegin; eauto.
        * subst; split; auto.
          split; [eauto | intros].
          unfold dlr in *; clarify.
          exploit drop_read_set; eauto; intro.
          exploit Hreads; eauto 2; intros (w'' & a'' & Hw''); clarify.
          exploit last_mods; eauto; intro.
(*          specialize (Hw''222222 w'); specialize (Hw222222 w''); clarify.*)
          specialize (Hordered w''); unfold before in *; clarify.
          destruct Hordered as [? | [? | ?]].
          { inversion Hmo.
            specialize (HR_total w' w''); clarify.
            destruct HR_total as [HR | [? | HR]]; clarify.
            { exploit HcoWR; try apply HR; try apply Hreads0; clarify.
              eapply begin_trans; try apply Hbegin; eauto. }
            { exploit HcoWR; try apply HR; try apply Hreads1; clarify. } }
          { right; exists w''; clarify.
            eapply begin_trans; try apply Hbegin; eauto. }
          { right; exists w''; clarify.
            apply (Htrans _ a); auto.
            eapply end_trans; try apply Hend; eauto. }
        * specialize (HcoWR r0); use HcoWR.
          specialize (HcoWR _ Hreads0 w'); clarify.
          specialize (HcoWR w); clarify.
          contradiction HcoWR.
          unfold before in *; clarify; eapply begin_trans; try apply Hbegin;
            eauto.
        * generalize (in_nth_error _ _ Hw'2); intros (i2 & ? & Hi2).
          destruct (lt_dec i i2).
          { exploit (total_lin_nth Hops Htotal Hr0 Hi2); clarify. }
          destruct (eq_dec i2 i).
          { subst; rewrite Hi2 in Hr0; clarify. }
          assert (nth_error (firstn i ops) i2 = Some w').
          { rewrite nth_error_firstn; clarify; abstract omega. }
          exploit nth_error_in; eauto; rewrite in_rev; intro.
          rewrite find_fail, Forall_forall in Hfind; exploit Hfind; eauto.
          generalize (mods_spec (op w') p); clarify.
        * contradiction Hw'222221; eapply end_trans; try apply Hend; eauto.
    - rewrite find_before_fail in Hfind; exists m1; clarify.
      specialize (Hfind _ _ Hr).
      use Hfind.
      destruct Hfind as (i' & e' & He').
      rewrite rev_app_distr, find_app.
      destruct (find (fun e => if find_mod (op e) p then true else false)
                     (rev (firstn i ops))) eqn: Hfind.
      exploit nth_error_in; eauto.
      clear i' e' He'; rewrite find_spec in Hfind; clarify.
      exploit Hreads; eauto; intros (w & a' & Hw); clarify.
      exploit last_mods; eauto; intro.
      exploit nth_error_rev'; eauto; rewrite nth_error_firstn; intro Hx.
      clarify; exploit nth_error_in; eauto; intro.
      specialize (Hw222222 e); generalize (mods_spec (op e) p); clarify.
      exploit (total_lin_nth Hops Htotal Hx Hr); auto; intro.
      exploit Hordered; eauto; intros [? | [Hw2 | ?]].
      + use Hw222222; clarify.
        eapply begin_trans; try apply Hbegin; eauto.
      + generalize (in_nth_error _ _ Hw2); intros (i2 & ? & Hi2).
        destruct (lt_dec i2 (length (firstn i ops) - x - 1)).
        { exploit (total_lin_nth Hops Htotal Hi2 Hx); clarify. }
        destruct (eq_dec i2 (length (firstn i ops) - x - 1)).
        { subst; rewrite Hi2 in Hx; clarify.
          split; [eauto | intros].
          unfold dlr in *; clarify.
          exploit drop_read_set; eauto; intro.
          exploit Hreads; eauto 2; intros (w'' & a'' & Hw''); clarify.
          exploit last_mods; eauto; intro.
          specialize (Hw''222222 e); clarify.
          specialize (Hordered w''); clarify.
          destruct Hordered as [? | [? | ?]].
          * exfalso; apply Hw''222222; auto.
            eapply begin_trans; try apply Hbegin; eauto.
          * specialize (Htotal w'' e); clarify; eauto.
          * right; exists w''; clarify.
            eapply end_trans; try apply Hend; eauto. }
        destruct (lt_dec i2 i).
        * specialize (Hfind22 (length (firstn i ops) - i2 - 1) w);
            use Hfind22. use Hfind22.
          generalize (mods_spec (op w) p); clarify.
          { apply nth_error_rev; rewrite nth_error_firstn; clarify. }
          { clear - Hr Hfind1 n n0 l1.
            assert (length (firstn i ops) - x - 1 < i2) by abstract omega.
            generalize (nth_error_lt _ _ Hr); intros.
            rewrite <- NPeano.Nat.sub_add_distr.
            rewrite (NPeano.Nat.add_lt_mono_r _ _ (i2 + 1)),
              NPeano.Nat.sub_add; [abstract omega|].
            rewrite List.firstn_length, Min.min_l; abstract omega. }
        * destruct (eq_dec i2 i).
          { subst; rewrite Hi2 in Hr; clarify. }
          { assert (i < i2) by (clear - n1 n2; abstract omega).
            exploit (total_lin_nth Hops Htotal Hr Hi2); clarify. }
      + contradiction Hw222221; eapply end_trans; try apply Hend; eauto.
      + rewrite find_fail, Forall_forall in Hfind; clarify.
        assert (nth_error (firstn i ops) i' = Some e')
          by (rewrite nth_error_firstn; clarify).
        exploit nth_error_in; eauto; rewrite in_rev; intro.
        exploit Hfind; eauto; clarify.
      + generalize (reads_spec (op r) p); intro Hno; clarify.
        exploit Hno; eauto.
  Qed.

  Lemma critical_reads : forall (E : execution) X ops
    (Htrans : transitive_on (hb X) (events E))
    (Hin : forall e, In e ops -> events E e)
    (Htotal : total_on (hb X) (set_of ops)) a z (Ha : In a ops) (Hz : In z ops) 
    (Hbegin : forall e (He : In e ops), e = a \/ hb X (id a) (id e))
    (Hend : forall e (He : In e ops), e = z \/ hb X (id e) (id z))
    p (Hordered : forall e, events E e -> mods (op e) p ->
       hb X (id e) (id a) \/ In e ops \/ hb X (id z) (id e))
    (Hops : linearization (set_of ops) (hb X) ops)
    ops' X' (Hdrop : dlr p E (ops, X) = (ops', X'))
    (Hvalid : valid (upd_events E (Union
      (Setminus (events E) (set_of ops)) (set_of ops'))) X')
    m1 (Hm1 : linearization (before (events E) (full (events E) X) a)
                            (full (events E) X) m1)
    (Hseq : forall i r v (Hr : nth_error ops i = Some r)
        (Hreads : reads (op r) p v),
      match find (fun e => if find_mod (op e) p then true else false)
        (rev (m1 ++ firstn i ops)) with
      | Some w => rf X (id w) (id r) /\
          exists a, last_op (to_seq' (op w)) (Ptr p) a /\ match_op err a v
      | None => False
      end) l (Hlin : linearization (events E) (full (events E) X) l),
    wf_reads E X.
  Proof.
    unfold dlr; repeat intro; clarify.
    destruct Hvalid as (Hreads & Hrf & Hwf & Hmo & Hcont & Htrans').
    destruct Hwf as (l' & Hlin' & Hcomplete'); clarify.
    exploit (read_drop_set E e p); eauto; intros [He' | He'].
    - specialize (Hreads _ He' _ _ Hread); destruct Hreads as (w & a' & Hw);
        clarify.
      exploit drop_mod_last_op; try apply Hw21; eauto 2.
      intros (w' & Hw' & Ha' & Hidw'); exists w', a'; split; clarify.
      + intro; subst.
        exploit (lin_irrefl Hlin); eauto.
        rewrite <- Hidw' in *; apply t_step; repeat eexists; auto; right;
          auto.
      + rewrite Hidw'; clarify.
        exploit mod_drop_set; eauto; intros (w2' & Hw2' & ? & Hidw2).
        specialize (Hw222222 _ Hw2'); rewrite Hidw2 in *; clarify.
    - clarify; exploit in_nth_error; eauto; intros (i & ? & Hi).
      specialize (Hseq _ _ _ Hi Hread).
      destruct (find (fun e => if find_mod (op e) p then true else false)
        (rev (m1 ++ firstn i ops))) eqn: Hfind; clarify.
      exists e0, x; split.
      { intro; subst.
        eapply (lin_irrefl Hlin); eauto 2.
        apply t_step; repeat eexists; auto; right; auto. }
      apply conjI1.
      { exploit find_success; eauto; rewrite <- in_rev, in_app;
          intros ([? | ?] & _).
        { rewrite <- (lin_set Hm1) in *; unfold before in *; clarify. }
        { eapply Hin, firstn_in; eauto. } }
      repeat split; auto.
      + intro.
        exploit find_success; eauto; rewrite <- in_rev, in_app;
          intros ([? | ?] & _).
        * rewrite <- (lin_set Hm1) in *; unfold before in *; clarify.
          exploit (lin_antisym Hlin e e0); eauto.
          { apply t_step; repeat eexists; auto; left; auto. }
          { specialize (Hbegin e); clarify.
            eapply t_trans; eauto.
            apply t_step; repeat eexists; auto; left; auto. }
        * exploit in_nth_error; eauto; intros (i' & ? & Hi').
          rewrite nth_error_firstn in Hi'; clarify.
          exploit (lin_order_3(e1 := e) Hops i i'); eauto; omega.
      + intros.
        assert (linearization (set_of (m1 ++ firstn i ops)) (hb X)
                              (m1 ++ firstn i ops)) as Hlin''.
        { rewrite set_of_app; apply lin_combine.
          * repeat intro; apply eq_nat_dec.
          * rewrite <- (firstn_skipn i) in Hops.
            eapply lin_app; eauto.
          * rewrite (lin_set' Hm1); auto.
            apply full_lin; auto.
            eapply lin_contained; eauto; apply full_cont.
            repeat intro; unfold before, Ensembles.In in *; clarify.
          * setoid_rewrite in_map_iff.
            intros ? (e1 & Hid1 & He1) (e2 & Hid2 & He2); subst.
            exploit firstn_in; eauto; intro.
            rewrite <- (lin_set Hm1) in *; unfold before in *; clarify.
            rewrite <- Hid2 in *; exploit Hbegin; eauto; intros [? | ?].
            { subst; exploit (lin_irrefl Hlin a); auto. }
            { exploit (lin_antisym Hlin a e2); auto.
              apply t_step; repeat eexists; auto; left; auto. }
          * setoid_rewrite in_map_iff.
            intros ?? (e1 & Hid1 & He1) (e2 & Hid2 & He2); subst.
            exploit firstn_in; eauto; intro.
            rewrite <- (lin_set Hm1) in *; unfold before in *; clarify.
            intro; exploit (lin_antisym Hlin e1 e2); auto.
            { specialize (Hbegin e2); clarify.
              eapply t_trans; eauto.
              apply t_step; repeat eexists; auto; left; auto. }
            { apply t_step; repeat eexists; auto; left; auto. } }
        assert (In w2 (m1 ++ firstn i ops)).
        { specialize (Hordered w2); clarify.
          rewrite in_app; destruct Hordered as [? | [Hw2 | ?]];
            [left | right | exfalso].
          * rewrite <- (lin_set Hm1); unfold before; clarify.
            apply t_step; repeat eexists; auto; left; auto.
          * generalize (in_nth_error _ _ Hw2); intros (i2 & ? & Hi2).
            apply (nth_error_in i2); rewrite nth_error_firstn; clarify.
            destruct (eq_dec i2 i); subst.
            { rewrite Hi2 in Hi; clarify.
              exploit (lin_irrefl Hops); eauto 2; clarify. }
            { exploit (total_lin_nth Hops Htotal Hi Hi2); [omega|].
              intro; exploit (lin_antisym Hops); eauto 2; clarify. }
          * exploit (end_trans E); try apply Hend; eauto; intro.
            exploit (lin_antisym Hops); eauto 2. }
        exploit in_nth_error; eauto; intros (i2 & ? & Hi2).
        rewrite find_spec in Hfind; clarify.
        exploit nth_error_rev'; eauto; intro Hi0.
        exploit (lin_order_3 Hlin'' _ _ Hi0 Hi2); auto; intro Hgt.
        generalize (nth_error_rev _ _ Hi2); intro Hi2'.
        specialize (Hfind22 (length (m1 ++ firstn i ops) - i2 - 1) w2).
        use Hfind22; [|omega].
        generalize (mods_spec (op w2) p); clarify.
  Qed.

  Lemma before_hb : forall (E : execution) X ops
    (Htrans : transitive_on (hb X) (events E))
    (Hin : forall e, In e ops -> events E e) a z (Ha : In a ops) (Hz : In z ops)
    (Hbegin : forall e (He : In e ops), e = a \/ hb X (id a) (id e))
    (Hend : forall e (He : In e ops), e = z \/ hb X (id e) (id z))
    p (Hordered : forall e, events E e -> mods (op e) p ->
       hb X (id e) (id a) \/ In e ops \/ hb X (id z) (id e))
    e e' (He : events E e) (Hbefore : hb X (id e) (id a))
    (He' : events E e') (Hmods : mods (op e') p),
      hb X (id e') (id a) \/ hb X (id e) (id e').
  Proof.
    intros.
    specialize (Hordered e'); clarify; right.
    destruct Hordered.
    - eapply begin_trans; try apply Hbegin; eauto.
    - apply (Htrans _ z); auto.
      eapply begin_trans; try apply Hbegin; eauto.
  Qed.

  Lemma critical_hb : forall (E : execution) X ops
    (Htrans : transitive_on (hb X) (events E))
    (Htotal : total_on (hb X) (set_of ops))
    (Hin : forall e, In e ops -> events E e) a z (Ha : In a ops) (Hz : In z ops)
    (Hbegin : forall e (He : In e ops), e = a \/ hb X (id a) (id e))
    (Hend : forall e (He : In e ops), e = z \/ hb X (id e) (id z))
    p (Hordered : forall e, events E e -> mods (op e) p ->
       hb X (id e) (id a) \/ In e ops \/ hb X (id z) (id e))
    e e' (He : In e ops) (He' : events E e') (Hmods : mods (op e') p),
    hb X (id e') (id e) \/ e' = e \/ hb X (id e) (id e').
  Proof.
    intros; specialize (Hordered e'); clarify.
    destruct Hordered as [? | [? | ?]].
    - left; eapply begin_trans; try apply Hbegin; eauto.
    - apply Htotal; auto.
    - right; right; eapply end_trans; try apply Hend; eauto.
  Qed.

  Lemma rf_hb_tri : forall (E : execution) X l
    (Hlin : linearization (events E) (full (events E) X) l)
    e1 e2 (He1 : events E e1) (He2 : events E e2) (Hrf : rf X (id e1) (id e2))
    (Htri : hb X (id e1) (id e2) \/ e1 = e2 \/ hb X (id e2) (id e1)),
    hb X (id e1) (id e2).
  Proof.
    clarify; destruct Htri.
    - subst; exploit (lin_irrefl Hlin); eauto; clarify.
      apply t_step; repeat eexists; auto; right; auto.
    - exploit (lin_antisym Hlin e1 e2); clarify; apply t_step; repeat eexists;
        auto; [right | left]; auto.
  Qed.

  Corollary crit_read_hb : forall (E : execution) X
    (Htrans : transitive_on (hb X) (events E))
    l (Hlin : linearization (events E) (full (events E) X) l)
    ops (Hin : forall e, In e ops -> events E e) r (Hr : In r ops)
    w (Hw : events E w) p (Hmods : mods (op w) p)
    (Hrf : rf X (id w) (id r)) (Htotal : total_on (hb X) (set_of ops)) a z
    (Ha : In a ops) (Hz : In z ops) 
    (Hbegin : forall e (He : In e ops), e = a \/ hb X (id a) (id e))
    (Hend : forall e (He : In e ops), e = z \/ hb X (id e) (id z))
    (Hordered : forall e, events E e -> mods (op e) p ->
       hb X (id e) (id a) \/ In e ops \/ hb X (id z) (id e)),
    hb X (id w) (id r).
  Proof.
    intros.
    specialize (Hordered w); clarify.
    destruct Hordered as [? | [? | ?]].
    - eapply begin_trans; try apply Hbegin; try apply Hend; eauto.
    - specialize (Htotal w r); eapply rf_hb_tri; eauto.
    - exploit (lin_antisym Hlin w r); clarify; apply t_step; repeat eexists;
        auto.
      + right; auto.
      + left; eapply end_trans; eauto.
  Qed.

  Lemma full_bridge : forall (E : Ensemble event) X i j k l
    (Hij : full E X i j) (Hhb : hb X j k) (Hkl : full E X k l), full E X i l.
  Proof.
    intros.
    eapply t_trans; eauto; eapply t_trans; eauto.
    apply t_step; split; [left; auto|].
    generalize (full_in2 Hij), (full_in1 Hkl); clarify; repeat eexists; eauto.
  Qed.

  Lemma full_hb : forall E X ops (Hin : forall e, In e ops -> events E e)
    (Htotal : total_on (hb X) (set_of ops))
    l (Hlin : linearization (events E) (full (events E) X) l)
    e1 e2 (He1 : In e1 ops) (He2 : In e2 ops)
    (Hfull : full (events E) X (id e1) (id e2)),
    hb X (id e1) (id e2).
  Proof.
    intros.
    specialize (Htotal e1 e2); clarify.
    destruct Htotal.
    - subst; exploit (lin_irrefl Hlin); eauto; clarify.
    - exploit (lin_antisym Hlin e1 e2); eauto; clarify.
      apply t_step; repeat eexists; auto; left; auto.
  Qed.

  Definition kept p ops (e : event) := ~In e ops \/
    match op e with (Read _ p' _, _) => p' <> p | _ => True end.

  Lemma kept_dec : forall p e E ops (He : events E e)
    (Hin : Included (set_of ops) (events E))
    X l (Hlin : linearization (events E) (hb X) l),
    kept p ops e \/ ~kept p ops e.
  Proof.
    intros.
    unfold kept; destruct (in_ops_dec _ _ He Hin _ Hlin); [|left; clarify].
    destruct (op e) as (c, ?); destruct c; clarify.
    destruct (eq_dec p0 p); clarify; right; intro; clarify.
  Qed.

  Lemma drop_kept : forall p ops e (He : In e ops)
    (Hkeep : kept p ops e), exists e', In e' (drop_l_reads p ops) /\
      id e' = id e.
  Proof.
    unfold kept; induction ops; clarify.
    destruct a as [? (c, ?)]; destruct He; clarify.
    - destruct c; clarify; eauto.
      + destruct (eq_dec p0 p); clarify; eauto.
      + destruct (eq_dec p0 p); clarify; eauto.
    - specialize (IHops e); clarify.
      exists x; destruct c; clarify.
  Qed.

  Corollary drop_kept' : forall p ops e (He : In e ops)
    (Hkeep : kept p ops e), exists e', In e' (drop_l_reads' p ops) /\
      id e' = id e.
  Proof.
    unfold kept; destruct ops; clarify.
    destruct e as [? (c, ?)]; destruct He; clarify.
    - destruct c; clarify; eauto; destruct (eq_dec p0 p); clarify; eauto.
    - exploit drop_kept; eauto.
      { unfold kept; eauto. }
      intros (e' & ?); exists e'; clarify.
  Qed.

  Lemma kept_set : forall E ops (Hin : Included (set_of ops) (events E))
    X l (Hlin : linearization (events E) (hb X) l) e p (He : events E e)
    (Hkept : kept p ops e), exists e', Union (Setminus (events E) (set_of ops))
      (set_of (drop_l_reads' p ops)) e' /\ id e' = id e.
  Proof.
    intros; setoid_rewrite Union_spec; setoid_rewrite Setminus_spec.
    exploit in_ops_dec; eauto; intros [? | ?].
    - exploit drop_kept'; eauto; intros (e' & ?); exists e'; clarify.
    - exists e; clarify.
  Qed.

  Lemma not_kept_in : forall E ops (Hin : Included (set_of ops) (events E))
    X l (Hlin : linearization (events E) (hb X) l) p e (He : events E e)
    (Hkept : ~kept p ops e), In e ops.
  Proof.
    intros.
    exploit in_ops_dec; eauto; clarify.
    contradiction Hkept; unfold kept; auto.
  Qed.    

  Lemma not_kept : forall E ops (Hin : Included (set_of ops) (events E))
    X l (Hlin : linearization (events E) (hb X) l) p e (He : events E e)
    (Hkept : ~kept p ops e), In e ops /\ exists t v, fst (op e) = Read t p v.
  Proof.
    intros.
    exploit not_kept_in; eauto; clarify.
    unfold kept in *; destruct (op e) as (c, ?); destruct c; clarify;
      try solve [contradiction Hkept; auto].
    destruct (eq_dec p0 p); [subst; eauto | contradiction Hkept; auto].
  Qed.    

  Corollary not_kept_dropped : forall E ops
    (Hin : Included (set_of ops) (events E))
    X l (Hlin : linearization (events E) (hb X) l) p e (He : events E e)
    (Hkept : ~kept p ops e), dropped p ops e.
  Proof.
    unfold dropped; intros; exploit not_kept; eauto; intros (? & ? & v & Hr).
    clarify; exists v; unfold reads.
    destruct (op e); clarify.
  Qed.
    
  Lemma full_into : forall E X (Htrans : transitive_on (hb X) (events E)) p ops 
    (Hin : forall e, In e ops -> events E e)
    (Htotal : total_on (hb X) (set_of ops))
    l (Hlin : linearization (events E) (full (events E) X) l)
    e1 e2 (He1 : events E e1) (Hkeep : kept p ops e1)
    (He2 : events E e2) (He2' : ~kept p ops e2)
    (Hfull : full (events E) X (id e1) (id e2))
    ops' X' (Hdrop : dlr p E (ops, X) = (ops', X'))
    (Hrf : forall e (He : events E e) (He' : dropped p ops e) i,
       rf X i (id e) -> hb X i (id e)),
    exists k, 
    (full (Union (Setminus (events E) (set_of ops)) (set_of ops')) X' (id e1) k
     \/ k = id e1) /\ hb X k (id e2).
  Proof.
    unfold full; intros; rewrite Operators_Properties.clos_trans_t1n_iff in *.
    remember (id e1) as i; remember (id e2) as j.
    generalize dependent e2; generalize dependent e1; induction Hfull; clarify.
    - exists (id e1); clarify.
      destruct H as ([? | ?] & ?); clarify.
      generalize (full_lin Hlin); intros (? & _).
      exploit not_kept_dropped; try apply He2'; eauto.
    - destruct H as (H & ? & e' & ?).
      generalize (full_lin Hlin); clarify.
      exploit (kept_dec p e'); eauto; intros [? | ?].
      + specialize (IHHfull e'); clarify.
        specialize (IHHfull _ He2 He2' eq_refl); destruct IHHfull as (k & Hk).
        exists k; clarify; left.
        assert (restrict (union (hb X') (rf X')) (Union (Setminus (events E)
          (set_of ops)) (set_of ops')) (id e1) (id e')).
        { exploit kept_set; try apply Hkeep; eauto; intros (? & ? & Hid1).
          exploit kept_set; eauto; intros (? & ? & Hid').
          unfold dlr in *; clarify.
          rewrite <- Hid1, <- Hid' in *; repeat eexists; auto.
          destruct H; [left|]; clarify.
          exploit (dropped_dec(ops := ops) E p e'); eauto; intros [? | ?].
          * rewrite Hid' in *; exploit Hrf; try apply H; auto.
            intro; left; auto.
          * right; clarify.
            rewrite Hj in *; exploit (lin_id_inj e e' Hlin); clarify. }
        destruct Hk1; [eapply t_trans; [apply t_step | eauto] |
          subst; apply t_step]; auto.
      + exploit full_hb; try (unfold full;
          rewrite Operators_Properties.clos_trans_t1n_iff; apply Hfull);
          try (eapply not_kept_in); eauto.
        intro; exists (id e1); clarify.
        apply (Htrans _ e'); auto.
        destruct H; eauto 2.
        exploit not_kept_dropped; eauto.
  Qed.

  Lemma full_cases : forall E X l
    (Hlin : linearization (events E) (full (events E) X) l) ops
    (Hin : forall e, In e ops -> events E e)
    p ops' X' (Hdrop : dlr p E (ops, X) = (ops', X'))
    (Hrf : forall e (He : events E e) (He' : dropped p ops e) i,
       rf X i (id e) -> hb X i (id e))
    (Hrf' : forall e1 e2 (He1 : events E e1) (He2 : events E e2)
      (Hrf : rf X (id e1) (id e2)), exists p, mods (op e1) p)
    e1 e2 (He1 : events E e1) (He2 : events E e2)
    (HR : union (hb X) (rf X) (id e1) (id e2)), hb X (id e1) (id e2) \/
      exists e1', Union (Setminus (events E) (set_of ops)) (set_of ops') e1' /\
        id e1' = id e1 /\ rf X' (id e1') (id e2).
  Proof.
    intros; destruct HR; clarify.
    exploit Hrf'; try apply H; auto; intros (? & Hmods).
    generalize (full_lin Hlin); intros [? _].
    exploit (dropped_dec(ops := ops) E p e2); eauto; intros [? | ?]; eauto.
    exploit mod_drop_set; try apply Hmods; eauto; intros (? & ? & ? & Hid).
    rewrite <- Hid in *.
    unfold dlr in *; clarify.
    right; repeat eexists; eauto; intros.
    exploit (lin_id_inj e e2 Hlin); clarify.
  Qed.

  Corollary full_cases' : forall E X l
    (Hlin : linearization (events E) (full (events E) X) l) ops
    (Hin : forall e, In e ops -> events E e)
    p ops' X' (Hdrop : dlr p E (ops, X) = (ops', X'))
    (Hrf : forall e (He : events E e) (He' : dropped p ops e) i,
       rf X i (id e) -> hb X i (id e))
    (Hrf' : forall e1 e2 (He1 : events E e1) (He2 : events E e2)
      (Hrf : rf X (id e1) (id e2)), exists p, mods (op e1) p)
    e1 e2 (He1 : events E e1) (He2 : events E e2) (He2' : kept p ops e2)
    (HR : union (hb X) (rf X) (id e1) (id e2)), hb X (id e1) (id e2) \/
    full (Union (Setminus (events E) (set_of ops)) (set_of ops')) X'
      (id e1) (id e2).
  Proof.
    intros; exploit full_cases; try apply HR; eauto;
      intros [? | (? & ? & Hid & ?)]; auto.
    generalize (full_lin Hlin); clarify.
    exploit kept_set; eauto; intros (? & ? & Hid2).
    unfold dlr in *; clarify.
    rewrite <- Hid, <- Hid2 in *; right; apply t_step; repeat eexists; clarify.
    right; auto.
  Qed.

  Lemma full_from : forall E X (Htrans : transitive_on (hb X) (events E)) p ops 
    (Hin : forall e, In e ops -> events E e)
    (Htotal : total_on (hb X) (set_of ops))
    l (Hlin : linearization (events E) (full (events E) X) l)
    e1 e2 (He2 : events E e2) (Hkeep : kept p ops e2)
    (He1 : events E e1) (He1' : ~kept p ops e1)
    (Hfull : full (events E) X (id e1) (id e2))
    ops' X' (Hdrop : dlr p E (ops, X) = (ops', X'))
    (Hrf : forall e (He : events E e) (He' : dropped p ops e) i,
       rf X i (id e) -> hb X i (id e))
    (Hrf' : forall e1 e2 (He1 : events E e1) (He2 : events E e2)
      (Hrf : rf X (id e1) (id e2)), exists p, mods (op e1) p),
    exists k, (hb X (id e1) k \/ k = id e1) /\
     (full (Union (Setminus (events E) (set_of ops)) (set_of ops')) X' k (id e2)
      \/ k = id e2).
  Proof.
    unfold full; intros; rewrite Operators_Properties.clos_trans_tn1_iff in *.
    remember (id e1) as i; remember (id e2) as j.
    generalize dependent e2; generalize dependent e1; induction Hfull; clarify.
    - destruct H; clarify; exploit full_cases'; try apply H; eauto.
      intros [? | ?]; eauto.
    - destruct H as (H & e' & ?); specialize (IHHfull e1); clarify.
      specialize (IHHfull e').
      generalize (full_lin Hlin); clarify.
      exploit (kept_dec p e'); eauto; intros [Hkeep' | ?].
      + use IHHfull; use IHHfull; destruct IHHfull as (k & Hk).
        exists k; clarify; left.
        assert (restrict (union (hb X') (rf X')) (Union (Setminus (events E)
          (set_of ops)) (set_of ops')) (id e') (id e2)).
        { exploit kept_set; try apply Hkeep; eauto; intros (? & ? & Hid2).
          exploit kept_set; try apply Hkeep'; eauto; intros (? & ? & Hid').
          unfold dlr in *; clarify.
          rewrite <- Hid2, <- Hid' in *; repeat eexists; auto.
          destruct H; [left|]; clarify.
          exploit (dropped_dec(ops := ops) E p e2); eauto; intros [? | ?].
          * rewrite Hid2 in *; exploit Hrf; try apply H; auto.
            intro; left; auto.
          * right; clarify.
            rewrite Hj in *; exploit (lin_id_inj e e2 Hlin); clarify. }
        destruct Hk2; [eapply t_trans; [eauto | apply t_step] |
          subst; apply t_step]; auto.
      + exploit full_hb; try (unfold full;
          rewrite Operators_Properties.clos_trans_tn1_iff; apply Hfull);
          try eapply not_kept_in; eauto.
        intro; exploit full_cases'; try apply H; eauto; intros [? | ?].
        * exists (id e2); clarify.
          left; apply (Htrans _ e'); auto.
        * eauto.
  Qed.

  Lemma full_across : forall E X (Htrans : transitive_on (hb X) (events E))
    p ops (Hin : forall e, In e ops -> events E e)
    (Htotal : total_on (hb X) (set_of ops))
    l (Hlin : linearization (events E) (full (events E) X) l)
    e1 e2 (He1 : events E e1) (He1' : kept p ops e1)
    (He2 : events E e2) (He2' : kept p ops e2) e (He : events E e)
    (He' : ~kept p ops e)
    (Hfull1 : full (events E) X (id e1) (id e))
    (Hfull2 : full (events E) X (id e) (id e2))
    ops' X' (Hdrop : dlr p E (ops, X) = (ops', X'))
    (Hrf : forall e (He : events E e) (He' : dropped p ops e) i,
       rf X i (id e) -> hb X i (id e))
    (Hrf' : forall e1 e2 (He1 : events E e1) (He2 : events E e2)
      (Hrf : rf X (id e1) (id e2)), exists p, mods (op e1) p),
    full (Union (Setminus (events E) (set_of ops)) (set_of ops')) X'
      (id e1) (id e2).
  Proof.
    intros.
    exploit full_into; try apply Hfull1; eauto; intros (k & Hk & Hhb).
    exploit full_from; try apply Hfull2; eauto; intros (k' & Hk'1 & Hk'2).
    generalize (full_lin Hlin); intros (? & _).
    unfold dlr in *; clarify.
    assert (exists ek, Union (Setminus (events E) (set_of ops))
      (set_of (drop_l_reads' p ops)) ek /\ id ek = k) as (ek & Hek & ?).
    { exploit kept_set; try apply He1'; eauto; intro.
      destruct Hk as [Hk | ?]; clarify; eauto.
      generalize (full_in2 Hk); clarify; eauto. }
    assert (exists ek', Union (Setminus (events E) (set_of ops))
      (set_of (drop_l_reads' p ops)) ek' /\ id ek' = k') as (ek' & Hek' & ?).
    { exploit kept_set; try apply He2'; eauto; intro.
      destruct Hk'2 as [Hk' | ?]; clarify; eauto.
      generalize (full_in1 Hk'); clarify; eauto. }
    assert (hb X k k').
    { destruct Hk'1; subst; auto.
      generalize (drop_ids_set E p); intro Hids; specialize (Hids ops); clarify.
      generalize (Hids _ Hek), (Hids _ Hek');
        intros (? & ? & Hid) (? & ? & Hid'); rewrite Hid, Hid' in *.
      apply (Htrans _ e); auto. }
    assert (full (Union (Setminus (events E) (set_of ops))
      (set_of (drop_l_reads' p ops))) {| rf := fun i j => rf X i j /\
      (forall e, events E e -> j = id e -> ~ dropped p ops e); hb := hb X |}
      k k').
    { subst; apply t_step; repeat eexists; auto; left; auto. }
    subst; destruct Hk as [? | Hidk].
    - eapply t_trans; eauto.
      destruct Hk'2 as [? | Hidk'];
        [eapply t_trans; eauto | rewrite Hidk' in *; auto].
    - rewrite Hidk in *.
      destruct Hk'2 as [? | Hidk'];
        [eapply t_trans; eauto | rewrite Hidk' in *; auto].
  Qed.

  Lemma full_transfer : forall E X (Htrans : transitive_on (hb X) (events E))
    p ops (Hin : forall e, In e ops -> events E e)
    (Htotal : total_on (hb X) (set_of ops))
    l (Hlin : linearization (events E) (full (events E) X) l)
    ops' X' (Hdrop : dlr p E (ops, X) = (ops', X'))
    (Hrf : forall e (He : events E e) (He' : dropped p ops e) i,
       rf X i (id e) -> hb X i (id e))
    (Hrf' : forall e1 e2 (He1 : events E e1) (He2 : events E e2)
      (Hrf : rf X (id e1) (id e2)), exists p, mods (op e1) p)
    e1 e2 (He1 : events E e1) (He1' : kept p ops e1)
    (He2 : events E e2) (He2' : kept p ops e2)
    (Hfull : full (events E) X (id e1) (id e2)),
    full (Union (Setminus (events E) (set_of ops)) (set_of ops')) X'
      (id e1) (id e2).
  Proof.
    intros; generalize (full_lin Hlin); intros (Hlin' & _).
    remember (id e1) as i; remember (id e2) as j; generalize dependent e2;
      generalize dependent e1; induction Hfull; clarify.
    - exploit kept_set; try apply He1'; eauto; intros (? & ? & Hid1).
      exploit kept_set; try apply He2'; eauto; intros (? & ? & Hid2).
      unfold dlr in *; clarify.
      destruct H; rewrite <- Hid1, <- Hid2 in *; apply t_step; repeat eexists;
        auto.
      destruct H; [left|]; clarify.
      exploit (dropped_dec(ops := ops) E p e2); eauto; intros [? | ?].
      + rewrite Hid2 in *; left; apply Hrf; auto.
      + right; clarify.
        rewrite Hj in *; exploit (lin_id_inj e e2 Hlin); clarify.
    - generalize (full_in2 Hfull1); intros (e' & ? & ?); subst.
      exploit (kept_dec p e'); eauto; intros [? | ?].
      + eapply t_trans; [eapply IHHfull1 | eapply IHHfull2]; try apply eq_refl;
          auto.
      + eapply full_across; eauto.
  Qed.

  Lemma mods_kept : forall p ops e p' (Hmods : mods (op e) p'), kept p ops e.
  Proof.
    intros; right.
    unfold mods in *; destruct e as [? (c, ?)]; destruct c; clarify.
  Qed.
    
  Lemma critical_mo : forall (E : execution) X
    (Htrans : transitive_on (hb X) (events E)) (Hrf : wf_rf E X)
    l (Hlin : linearization (events E) (full (events E) X) l)
    ops (Hin : forall e, In e ops -> events E e)
    (Htotal : total_on (hb X) (set_of ops)) a z (Ha : In a ops) (Hz : In z ops) 
    (Hbegin : forall e (He : In e ops), e = a \/ hb X (id a) (id e))
    (Hend : forall e (He : In e ops), e = z \/ hb X (id e) (id z))
    p (Hordered : forall e, events E e -> mods (op e) p ->
       hb X (id e) (id a) \/ In e ops \/ hb X (id z) (id e))
    ops' X' (Hdrop : dlr p E (ops, X) = (ops', X'))
    (Hvalid : valid (upd_events E (Union
      (Setminus (events E) (set_of ops)) (set_of ops'))) X')
    (Hops : forall e (He : In e ops) v (Hreads : reads (op e) p v),
      exists w, events E w /\ rf X (id w) (id e) /\ mods (op w) p)
    p' R (HR : good_mo (Union (Setminus (events E) (set_of ops))
      (set_of ops')) X' p' R),
    total_on R (fun e => events E e /\ mods (op e) p') /\
    (forall i j, R i j -> exists e1 e2, events E e1 /\ mods (op e1) p' /\
       i = id e1 /\ events E e2 /\ mods (op e2) p' /\ j = id e2) /\
    (forall e (He : events E e) v (Hp : reads (op e) p' v) w (Hw : events E w)
       (Hrf : rf X (id w) (id e)) w2 (Hw2 : events E w2)
       (Hsafe : ~dropped p ops e),
       R (id w) (id w2) -> ~hb X (id w2) (id e)) /\
    (forall e1 e2 (He1 : events E e1) (He2 : events E e2)
       (Hfull : full (events E) X (id e1) (id e2)), ~R (id e2) (id e1)).
  Proof.
    unfold dlr; clarify.
    destruct Hvalid as (Hreads & Hrf' & Hwf & _ & _).
    destruct Hwf as (l' & Hlin' & _); clarify.
    generalize (full_lin Hlin); intros (Hhb_lin & _).
    inversion HR; repeat split.
    - intros ?? He1 He2; clarify.
      generalize (mod_drop_set _ _ p _ He11 He12 Hin Hlin),
        (mod_drop_set _ _ p _ He21 He22 Hin Hlin);
        intros (e1' & ? & ? & Hid1) (e2' & ? & ? & Hid2).
      specialize (HR_total e1' e2'); clarify.
      rewrite Hid1, Hid2 in HR_total; clarify.
      rewrite Hid2 in Hid1.
      exploit (lin_id_inj e1 e2 Hlin); auto.
    - intros ?? Hij; specialize (Hdom _ _ Hij).
      destruct Hdom as (e1 & e2 & He11 & He12 & ? & He21 & He22 & ?).
      generalize (drop_mod_set _ _ Hin He11 He12),
        (drop_mod_set _ _ Hin He21 He22); intros (e1' & ?) (e2' & ?).
      exists e1', e2'; clarify.
    - intros.
      exploit not_dropped_set; eauto; intro He'.
      specialize (HcoWR _ He' _ Hp).
      exploit Hdom; eauto.
      intros (w'' & w2' & ? & ? & Hidw' & ? & ? & Hidw2).
      rewrite Hidw' in *; specialize (HcoWR w''); clarify.
      intro; rewrite Hidw2 in *; exploit HcoWR; eauto; clarify.
      generalize (lin_id_inj e0 e Hlin); clarify.
    - intros; intro HR21.
      specialize (Hdom _ _ HR21).
      destruct Hdom as (e1' & e2' & He11 & He12 & Hid1 & He21 & He22 & Hid2).
      rewrite Hid1, Hid2 in *; exploit Hacyclic; try apply HR21; auto.
      rewrite <- Hid1, <- Hid2 in *; eapply full_transfer; unfold dlr; eauto.
      + intros.
        unfold dropped in He'; clarify.
        exploit Hops; eauto; clarify.
        exploit crit_read_hb; try apply Hbegin; try apply Hend; eauto.
        destruct Hrf as (Hunique & _); specialize (Hunique i (id e)).
        exploit Hunique; eauto 2; clarify.
      + intros ea eb ???.
        destruct Hrf as (Hunique & Hread); specialize (Hunique (id ea) (id eb)).
        exploit (dropped_dec(ops := ops) E p eb); eauto; intros [? | ?].
        * unfold dropped in *; clarify.
          exploit Hops; eauto; intros (w & ? & ? & ?).
          exploit Hunique; eauto; intro.
          exploit (lin_id_inj w ea Hlin); eauto; clarify; eauto.
        * exploit not_dropped_set; eauto; intro.
          exploit Hread; eauto; clarify.
          exploit Hreads; eauto; intros (w & ?); clarify.
          exploit Hunique; eauto; intro.
          exploit last_mods; eauto; intro Hmods.
          exploit drop_mod_set; try apply Hmods; eauto; intros (w' & ?).
          clarify; exploit (lin_id_inj w' ea Hlin); eauto; clarify; eauto.
          clarsimp.
      + exploit drop_mod_set; try apply He22; eauto; intros (e & ? & ? & Hid).
        rewrite <- Hid in *; exploit (lin_id_inj e e1 Hlin); eauto; clarify.
        eapply mods_kept; eauto.
      + exploit drop_mod_set; try apply He12; eauto; intros (e & ? & ? & Hid).
        rewrite <- Hid in *; exploit (lin_id_inj e e2 Hlin); eauto; clarify.
        eapply mods_kept; eauto.
  Qed.
        
  Lemma critical_mo' : forall (E : execution) X
    (Htrans : transitive_on (hb X) (events E)) (Hrf : wf_rf E X)
    l (Hlin : linearization (events E) (full (events E) X) l)
    ops (Hin : forall e, In e ops -> events E e)
    (Htotal : total_on (hb X) (set_of ops)) a z (Ha : In a ops) (Hz : In z ops) 
    (Hbegin : forall e (He : In e ops), e = a \/ hb X (id a) (id e))
    (Hend : forall e (He : In e ops), e = z \/ hb X (id e) (id z))
    p (Hordered : forall e, events E e -> mods (op e) p ->
       hb X (id e) (id a) \/ In e ops \/ hb X (id z) (id e))
    (Hops : linearization (set_of ops) (hb X) ops)
    ops' X' (Hdrop : dlr p E (ops, X) = (ops', X'))
    (Hvalid : valid (upd_events E (Union
      (Setminus (events E) (set_of ops)) (set_of ops'))) X')
    m1 (Hm1 : linearization (before (events E) (full (events E) X) a)
                            (full (events E) X) m1)
    (Hseq : forall i r v (Hr : nth_error ops i = Some r)
        (Hreads : reads (op r) p v),
      match find (fun e => if find_mod (op e) p then true else false)
        (rev (m1 ++ firstn i ops)) with
      | Some w => rf X (id w) (id r) /\
          (exists a, last_op (to_seq' (op w)) (Ptr p) a /\ match_op err a v) /\
          forall r' v' (He' : Union (Setminus (events E) (set_of ops))
            (set_of ops') r') (Hreads : reads (op r') p v')
            (Hord : hb X (id w) (id r')), rf X (id w) (id r') \/ exists w',
            events E w' /\ hb X (id w) (id w') /\ rf X (id w') (id r')
      | None => False
      end), has_mo E X.
  Proof.
    intros; intro p'.
    assert (forall i e,
      find (fun e => if find_mod (op e) p then true else false)
        (rev (m1 ++ firstn i ops)) = Some e -> events E e) as Hfind_in.
    { intros; rewrite find_spec in *; clarify.
      exploit nth_error_rev'; eauto; intro.
      exploit nth_error_in; eauto; rewrite in_app; intros [? | ?].
      + rewrite <- (lin_set Hm1) in *; unfold before in *; clarify.
      + exploit firstn_in; eauto. }
    destruct Hvalid as (Hreads & Hrf' & Hwf & Hmo & ?); generalize (Hmo p');
      intros (R & HR).
    exploit critical_mo; try apply Hbegin; try apply Hend; eauto.
    { unfold valid; clarify. }
    { intros.
      exploit in_nth_error; eauto; clarify.
      exploit Hseq; eauto.
      destruct (find (fun e => if find_mod (op e) p then true else false)
        (rev (m1 ++ firstn x ops))) eqn: Hfind; clarify.
      exploit Hfind_in; eauto; exploit last_mods; eauto. }
    inversion HR; intros (HR_total' & Hdom' & HcoWR' & Hacyclic').
    destruct Hwf as (l' & Hlin' & Hcomplete'); clarify.
    generalize (full_lin Hlin); intros (Hhb_lin & _).
    destruct (eq_dec p' p); [subst;
      destruct (find_before (fun e => readsb (op e) p) (fun e =>
        match find_mod (op e) p with Some _ => true | _ => false end) ops)
        eqn: Hfind|].
    - rewrite find_before_spec in Hfind; generalize (reads_spec (op e) p);
        clarify.
      exploit Hseq; eauto; intro Hw.
      destruct (find (fun e => if find_mod (op e) p then true else false)
        (rev (m1 ++ firstn x ops))) as [w|] eqn: Hfind'; [|clarify].
      destruct Hw as (? & (a' & ? & ?) & Hord); exploit last_mods; eauto; intro.
      exploit Hfind_in; eauto; intro.
      rewrite rev_app_distr, find_app in Hfind'.
      destruct (find (fun e => if find_mod (op e) p then true else false)
        (rev (firstn x ops))) eqn: Hfind''; clarify.
      { rewrite find_spec in Hfind''; clarify.
        exploit nth_error_rev'; eauto; intro.
        rewrite nth_error_firstn in *; clarify.
        exploit Hfind22; eauto; clarify. }
      assert (hb X (id w) (id a)) as Hbefore.
      { exploit find_success; eauto; rewrite <- in_rev, <- (lin_set Hm1);
          unfold before; intros ((_ & ?) & _).
        specialize (Hordered w); clarify.
        destruct Hordered.
        * specialize (Hbegin w); destruct Hbegin; auto.
          { subst; exploit (lin_irrefl Hlin); eauto 2; clarify. }
          exploit (lin_antisym Hlin w a); clarify.
          apply t_step; repeat eexists; auto; left; auto.
        * exploit (lin_antisym Hlin w a); clarify.
          apply t_step; repeat eexists; auto; left.
          eapply end_trans; try apply Hend; eauto. }
      unfold dlr in *; clarify.
      exists (fun i j => j = id w /\ (exists e, events E e /\ mods (op e) p /\
        id e = i /\ id e <> id w /\ hb X i (id a)) \/
        R i j /\ (hb X j (id a) -> i <> id w)); repeat split.
      + intros ?? He1 He2; clarify.
        generalize (mod_drop_set _ _ p _ He11 He12 Hin Hlin),
          (mod_drop_set _ _ p _ He21 He22 Hin Hlin);
          intros (e1' & ? & ? & Hid1) (e2' & ? & ? & Hid2).
        destruct (eq_dec (id e1) (id e2)).
        { exploit (lin_id_inj e1 e2 Hlin); auto. }
        destruct (eq_dec (id e1) (id w)).
        { destruct (hb_dec X Hhb_lin (id e2) (id a)).
          { rewrite in_map_iff; exists e2; clarify.
            rewrite <- (lin_set Hlin); auto. }
          { rewrite in_map_iff; exists a; clarify.
            rewrite <- (lin_set Hlin); auto. }
          * right; right; left; clarify.
            rewrite e0 in *; exists e2; clarify.
          * left; right; clarify.
            specialize (HR_total e1' e2'); rewrite Hid1, Hid2 in HR_total;
              clarify.
            destruct HR_total as [? | HR21].
            { subst; rewrite Hid1 in *; rewrite Hid2 in *; rewrite e0 in *;
                clarify. }
            { exploit before_hb; try apply Hbegin; try apply Hend;
                try apply Hbefore; eauto; clarify.
              rewrite e0 in *; exploit Hacyclic'; try apply HR21; clarify.
              apply t_step; repeat eexists; auto; left; auto. } }
        destruct (eq_dec (id e2) (id w)).
        { destruct (hb_dec X Hhb_lin (id e1) (id a)).
          { rewrite in_map_iff; exists e1; clarify.
            rewrite <- (lin_set Hlin); auto. }
          { rewrite in_map_iff; exists a; clarify.
            rewrite <- (lin_set Hlin); auto. }
          * left; left; clarify.
            exists e1; clarify.
          * right; right; right; clarify.
            specialize (HR_total e1' e2'); clarify.
            rewrite Hid1, Hid2 in HR_total; destruct HR_total as [HR21 | ?].
            { exploit before_hb; try apply Hbegin; try apply Hend;
                try apply Hbefore; try apply He11; eauto; clarify.
              rewrite e0 in *; exploit Hacyclic'; try apply HR21; clarify.
              apply t_step; repeat eexists; auto; left; auto. }
            { clarify; rewrite Hid1 in *; rewrite Hid2 in *; rewrite e0 in *;
                clarify. } }
        specialize (HR_total e1' e2'); clarify.
        rewrite Hid1, Hid2 in HR_total; clarify.
        rewrite Hid2 in Hid1; contradiction n; auto.
      + intros ?? [(? & e2 & ?) | (Hij & ?)].
        * exists e2, w; clarify.
        * specialize (Hdom _ _ Hij).
          destruct Hdom as (e1 & e2 & He11 & He12 & ? & He21 & He22 & ?).
          generalize (drop_mod_set _ _ Hin He11 He12),
            (drop_mod_set _ _ Hin He21 He22); intros (e1' & ?) (e2' & ?).
          exists e1', e2'; clarify.
      + intros e' He' v Heread w' Hw' ? w2 Hw2 [(Hid & e1 & ?) | ?].
        { exploit (lin_id_inj w2 w Hlin); clarify.
          exploit (lin_id_inj e1 w' Hlin); clarify.
          generalize (dropped_dec(ops := ops) E p e'); intro Hdropped; clarify.
          destruct Hrf as (Hunique & Hread_rf).
          specialize (Hdropped _ _ Hhb_lin); destruct Hdropped.
          { unfold dropped in *; clarify.
            exploit in_nth_error; eauto; intros (i' & ? & Hi').
            exploit Hseq; eauto.
            destruct (find (fun e => if find_mod (op e) p then true else false)
              (rev (m1 ++ firstn i' ops))) eqn: Hfind; clarify.
            exploit Hunique; [apply Hrf0 | eauto | intro].
            exploit (lin_id_inj e0 w' Hlin); clarify.
            { eapply Hfind_in; eauto. }
            rewrite rev_app_distr, find_app in Hfind.
            destruct (find (fun e => if find_mod (op e) p then true else false)
              (rev (firstn i' ops))) eqn: Hfind2.
            { rewrite find_spec in Hfind2; clarify.
              exploit nth_error_rev'; eauto; intro.
              exploit nth_error_in; eauto; intro.
              exploit firstn_in; eauto; intro.
              exploit (begin_trans E); try apply Hbegin; try apply Hw'; eauto.
              intro; exploit (lin_irrefl Hops); eauto. }
            rewrite Hfind in Hfind'; clarify. }
          exploit not_dropped_set; eauto; intro.
          intro; exploit Hord; eauto; intros [? | ?].
          * exploit Hunique; [apply Hrf0 | eauto | clarify].
          * clarify.
            exploit Hunique; [apply Hrf0 | eauto | intro Hid].
            rewrite Hid in *.
            rewrite find_spec in Hfind'; clarify.
            exploit nth_error_rev'; eauto; intro.
            exploit nth_error_lt; eauto; intro Hlt1.
            exploit (lin_order_1 Hm1); eauto.
            { instantiate (1 := w'); unfold before; clarify.
              apply t_step; repeat eexists; auto; left; auto. }
            { apply t_step; repeat eexists; auto; left; auto. }
            intros (i' & Hi' & Hlt2).
            exploit nth_error_lt; eauto; intro Hlt3.
            exploit nth_error_rev; eauto; intro.
            generalize (mods_spec (op w') p).
            exploit Hfind'22; eauto; clarify.
            clear - Hlt1 Hlt2 Hlt3; omega. }
        exploit (dropped_dec(ops := ops) E p e'); eauto; intros [? | ?].
        * unfold dropped in *; clarify.
          exploit in_nth_error; eauto; intros (i & ? & Hi).
          specialize (Hseq i e' v); clarify.
          destruct (find (fun e => if find_mod (op e) p then true else false)
                         (rev (m1 ++ firstn i ops))) eqn: Hfind2; clarify.
          destruct Hrf as (Hrf & _); specialize (Hrf _ _ Hrf0 _ Hseq1).
          exploit (lin_id_inj e0 w' Hlin); auto.
          { rewrite find_spec in Hfind2; clarify.
            exploit nth_error_rev'; eauto; intro.
            exploit nth_error_in; eauto; rewrite in_app; intros [? | ?].
            * rewrite <- (lin_set Hm1) in *; unfold before in *; clarify.
            * exploit firstn_in; eauto. }
          intro; subst.
          exploit Hdom; eauto.
          intros (w'' & w2' & ? & ? & Hidw' & ? & ? & Hidw2).
          rewrite rev_app_distr, find_app in Hfind2.
          destruct (find (fun e => if find_mod (op e) p then true else false)
            (rev (firstn i ops))) eqn: Hfind2'.
          { clarify; intro; assert (hb X (id w2) (id w')).
            { assert (In w' ops).
              { rewrite find_spec in Hfind2'; clarify.
                exploit nth_error_rev'; eauto; intro.
                exploit nth_error_in; eauto; intro.
                eapply firstn_in; eauto. }
              exploit drop_mod_set; eauto 2; intros (w2'' & ? & ? & Hidw2').
              rewrite <- Hidw2 in Hidw2'; exploit (lin_id_inj w2'' w2 Hlin);
                eauto 2; intro; subst.
              specialize (Hordered w2); clarify.
              destruct Hordered as [? | [Hinw2 | ?]].
              * eapply begin_trans; try apply Hbegin; eauto.
              * generalize (in_nth_error _ _ Hinw2); intros (i2 & ? & Hi2).
                rewrite find_spec in Hfind2'; destruct Hfind2' as (i' & ? & ? &
                  Hlast').
                exploit nth_error_rev'; eauto 2; intro Hi'.
                rewrite nth_error_firstn in *; clarify.
                destruct (lt_dec i2 (length (firstn i ops) - i' - 1)).
                { eapply (total_lin_nth Hops Htotal Hi2 Hi'); auto. }
                destruct (eq_dec i2 (length (firstn i ops) - i' - 1)).
                { subst; rewrite Hi2 in Hi'; clarify.
                  exploit Hirrefl; eauto 2; clarify. }
                { exploit (lin_order_3(e1 := w2) Hops i2 i); eauto 2; intro Hlt.
                  exploit (Hlast' (length (firstn i ops) - i2 - 1)).
                  { clear - H7 n n0 Hlt.
                    rewrite List.firstn_length in *.
                    rewrite Min.min_l in *; omega. }
                  { eapply nth_error_rev; rewrite nth_error_firstn; clarify.
                    eauto. }
                  generalize (mods_spec (op w2) p); clarify. }
              * exploit (lin_antisym Hlin e' w2); eauto 2; clarify.
                { apply t_step; repeat eexists; auto.
                  left; eapply end_trans; try apply Hend; eauto 2. }
                { apply t_step; repeat eexists; auto; left; auto. } }
            apply (Hacyclic' w2 w'); auto.
            apply t_step; repeat eexists; auto; left; auto. }
          rewrite Hfind2 in Hfind'; clarify.
          exploit drop_mod_set; eauto; intros (w2'' & ? & ? & ?).
          rewrite <- Hidw2 in *; exploit (lin_id_inj w2'' w2 Hlin); clarify.
          intro; specialize (Hordered w2); clarify.
          destruct Hordered as [? | Hafter].
          { exploit (lin_order_2 Hops w2); eauto 2; intros (i2 & ? & ?).
            rewrite find_fail, Forall_forall in Hfind2'.
            exploit Hfind2'.
            { rewrite <- in_rev; eauto.
              eapply (nth_error_in i2); rewrite nth_error_firstn; clarify;
                eauto. }
            generalize (mods_spec (op w2) p); clarify. }
          { exploit (end_trans E); try apply Hend; try apply Hafter; eauto.
            intro; exploit (lin_antisym Hhb_lin); eauto 2. }
        * clarify; eapply HcoWR'; try apply Hrf0; eauto 2.
      + intros ????? [Hback | (Hback & ?)].
        * destruct Hback as (? & e2' & ?).
          exploit (lin_id_inj e1 w Hlin); eauto; clarify.
          exploit (lin_id_inj e2' e2 Hlin); eauto; clarify.
          rewrite find_spec in Hfind'; clarify.
          exploit nth_error_lt; eauto; rewrite rev_length; intro Hlt.
          exploit nth_error_rev'; eauto; intro.
          exploit (lin_order_1 Hm1); eauto.
          { unfold before; clarify.
            apply t_step; repeat eexists; auto; left; auto. }
          intros (i2 & Hi2 & Hlt2).
          exploit nth_error_lt; eauto; intro Hlt3.
          exploit (Hfind'22 (length m1 - i2 - 1)).
          { clear - Hlt Hlt2 Hlt3; omega. }
          { eapply nth_error_rev; eauto. }
          generalize (mods_spec (op e2) p); clarify.
        * eapply Hacyclic'; try apply Hback; auto.
      + intros ??; clarify; eapply Hirrefl; eauto.
    - exists R; constructor; auto; intros.
      rewrite find_before_fail in Hfind.
      exploit in_ops_dec; try apply He; eauto; intros [? | ?].
      + exploit in_nth_error; eauto; intros (i & ? & Hi).
        exploit Hseq; eauto.
        exploit Hfind; eauto 2.
        { generalize (reads_spec (op e) p); intro Hread.
          destruct (readsb (op e) p); clarify; exploit Hread; eauto. }
        intros (j & w' & ? & Hj & Hmods) Hr Hhb.
        destruct (find (fun e => if find_mod (op e) p then true else false)
          (rev (m1 ++ firstn i ops))) eqn: Hfind'; clarify.
        exploit Hfind_in; eauto; intro.
        rewrite rev_app_distr, find_app in Hfind'.
        destruct (find (fun e => if find_mod (op e) p then true else false)
          (rev (firstn i ops))) eqn: Hfind''; clarify.
        destruct Hrf as (Hunique & _).
        exploit Hunique; [apply Hrf0 | eauto | intro Hid].
        exploit (lin_id_inj e0 w Hlin); clarify.
        clear dependent w'.
        assert (~hb X (id w2) (id w)) as Hnot.
        { intro; exploit Hacyclic'; try apply H; auto.
          apply t_step; repeat eexists; auto; left; auto. }
        exploit find_success; eauto 2; intros (? & _).
        rewrite <- in_rev in *; exploit firstn_in; eauto 2; intro.
        exploit Hdom'; eauto 2; intros (_ & w2' & _ & _ & _ & ? & ? & ?).
        exploit (lin_id_inj w2' w2 Hlin); clarify.
        specialize (Hordered w2); clarify.
        destruct Hordered as [? | [Hinw2 | ?]].
        * contradiction Hnot; eapply begin_trans; try apply Hbegin; eauto.
        * specialize (Htotal w2 w); clarify.
          destruct Htotal.
          { subst; exploit Hirrefl; eauto. }
          exploit (lin_order_2 Hops w2); eauto 2; intros (i2 & Hi2 & Hlt2).
          rewrite find_spec in Hfind''; clarify.
          exploit nth_error_rev'; eauto 2; rewrite nth_error_firstn;
            intro Hi'; clarify.
          exploit (lin_order_3 Hops _ _ Hi' Hi2); auto; intro Hlt.
          exploit (Hfind''22 (length (firstn i ops) - i2 - 1)).
          { generalize (nth_error_lt _ _ Hfind''1); rewrite rev_length;
              intro Hlt'.
            clear - H3 Hlt Hlt' Hlt2.
            assert (i2 < length (firstn i ops)).
            { rewrite List.firstn_length, Min.min_l; omega. }
            omega. }
          { eapply nth_error_rev; rewrite nth_error_firstn; clarify; eauto. }
          generalize (mods_spec (op w2) p); clarify.
        * exploit (lin_antisym Hlin w2 e); auto; apply t_step; repeat eexists;
            auto; left; auto.
          eapply end_trans; try apply Hend; eauto.
        * rewrite find_fail, Forall_forall in Hfind''.
          specialize (Hfind'' w'); use Hfind''; clarify.
          rewrite <- in_rev; apply (nth_error_in j); rewrite nth_error_firstn;
            clarify.
      + eapply HcoWR'; try apply Hrf0; eauto.
        unfold dropped; intro; clarify.
    - exists R; constructor; auto; intros.
      eapply HcoWR'; try apply Hrf0; eauto.
      intros (? & ? & Hread).
      generalize (reads_one _ _ _ _ _ Hp Hread); clarify.
  Qed.

  Lemma full_transfer' : forall (E : execution) X ops
    (Hin : forall e, In e ops -> events E e)
    p ops' X' (Hdrop : dlr p E (ops, X) = (ops', X'))
    i j (Hfull : full (Union (Setminus (events E) (set_of ops)) (set_of ops'))
                      X' i j), full (events E) X i j.
  Proof.
    unfold dlr; clarify.
    induction Hfull.
    - destruct H as (H & e1 & e2 & He1 & He2 & ?).
      generalize (drop_ids_set E p); intro Hids; specialize (Hids ops); clarify.
      generalize (Hids _ He1), (Hids _ He2);
        intros (? & ? & Hid1) (? & ? & Hid2).
      rewrite Hid1, Hid2 in *; apply t_step; repeat eexists; auto.
      destruct H; [left | right]; clarify.
    - eapply t_trans; eauto.
  Qed.      

  Lemma drop_inv : forall p ops e (Hin : In e (drop_l_reads p ops)),
    exists e', In e' ops /\ id e' = id e /\
      drop_l_read p (fst (op e')) = fst (op e) /\ snd (op e') = snd (op e).
  Proof.
    induction ops; clarify.
    assert (forall e, In e (drop_l_reads p ops) ->
      exists e', (a = e' \/ In e' ops) /\ id e' = id e /\
      drop_l_read p (fst (op e')) = fst (op e) /\ snd (op e') = snd (op e)).
    { intros; exploit IHops; eauto; clarify; eauto 6. }
    destruct a as [? (c, ?)]; destruct c; clarify; eauto 6.
    - do 2 eexists; eauto; clarify.
    - destruct (eq_dec p0 p); clarify; do 2 eexists; eauto; clarify.
  Qed.
    
  Lemma drop_inv' : forall p ops e (Hin : In e (drop_l_reads' p ops)),
    exists e', In e' ops /\ id e' = id e /\
      drop_l_read p (fst (op e')) = fst (op e) /\ snd (op e') = snd (op e).
  Proof.
    destruct ops; clarify.
    destruct e as [? (c, ?)]; clarify.
    destruct Hin; [|exploit drop_inv; eauto; clarify; eauto 6].
    subst; do 2 eexists; eauto.
  Qed.

  Lemma drop_inv_set : forall E p ops (Hin : forall e, In e ops -> events E e)
    e (He : Union (Setminus (events E) (set_of ops))
                  (set_of (drop_l_reads' p ops)) e),
    exists e', events E e' /\ id e' = id e /\ snd (op e') = snd (op e) /\
      (fst (op e') = fst (op e) \/ drop_l_read p (fst (op e')) = fst (op e)).
  Proof.
    intros; rewrite Union_spec, Setminus_spec in *.
    destruct He; [exists e; clarify|].
    exploit drop_inv'; eauto; clarify; eauto 10.
  Qed.

  Lemma drop_loc : forall p c, loc_of (drop_l_read p c) = loc_of c.
  Proof.
    destruct c; clarify.
  Qed.

  Lemma drop_sync_set : forall E e1 e2 p ops
    (He1 : Union (Setminus (events E) (set_of ops))
       (set_of (drop_l_reads' p ops)) e1)
    (He2 : Union (Setminus (events E) (set_of ops))
       (set_of (drop_l_reads' p ops)) e2)
    (Hsync : synchronizes_with (op e1) (op e2))
    (Hin : forall e, In e ops -> events E e),
    exists e1' e2', events E e1' /\ events E e2' /\ id e1' = id e1 /\
      id e2' = id e2 /\ synchronizes_with (op e1') (op e2').
  Proof.
    intros.
    exploit drop_inv_set; try apply He1; auto; intros (e1' & ?).
    exploit drop_inv_set; try apply He2; auto; intros (e2' & ?).
    exists e1', e2'; clarify.
    unfold synchronizes_with in *; destruct e1 as [? (c1, ?)],
      e2 as [? (c2, ?)], e1' as [? (c1', ?)], e2' as [? (c2', ?)]; clarify.
    assert (loc_of c1' = loc_of c1) by (clarify; symmetry; apply drop_loc).
    assert (loc_of c2' = loc_of c2) by (clarify; symmetry; apply drop_loc).
    clarsimp.
  Qed.

  Lemma drop_lin_wf : forall p l E X
    (Hlin : linearization (events E) (full (events E) X) l)
    (Hcomplete : forall i j a b (Hlt : i < j) (Ha : nth_error l i = Some a)
       (Hb : nth_error l j = Some b) (Hsync : synchronizes_with (op a) (op b)),
       hb X (id a) (id b)) ops (Hsub : Included (set_of ops) (events E))
    (Hnodup : NoDup (map id ops))
    ops' X' (Hdrop : dlr p E (ops, X) = (ops', X')),
    linearization (Union (Setminus (events E) (set_of ops))
      (set_of ops')) (full (Union (Setminus (events E) (set_of ops))
                                  (set_of ops')) X') (drop_lin ops ops' l) /\
    forall i j a b (Hlt : i < j)
      (Ha : nth_error (drop_lin ops ops' l) i = Some a)
      (Hb : nth_error (drop_lin ops ops' l) j = Some b)
      (Hsync : synchronizes_with (op a) (op b)), hb X' (id a) (id b).
  Proof.
    unfold dlr; clarify.
    generalize (drop_ids' p ops), (drop_NoDup' p _ Hnodup); intros Hids Hnodup'.
    assert (forall e, Union (Setminus (events E) (set_of ops))
      (set_of (drop_l_reads' p ops)) e <->
      In e (drop_lin ops (drop_l_reads' p ops) l)) as Hset.
    { intro; rewrite drop_lin_in; auto; try (rewrite (lin_set' Hlin); auto;
                                             reflexivity).
      unfold linearization in Hlin; clarify. }
    split.
    - split; auto; split.
      + apply drop_lin_ids; unfold linearization in Hlin; clarify.
      + intros.
        exploit full_transfer'; unfold dlr; eauto; intro.
        rewrite Hset in He1, He2.
        generalize (in_nth_error _ _ He1), (in_nth_error _ _ He2);
          intros (i1 & ? & Hi1) (i2 & ? & Hi2); exists i1, i2; clarify.
        destruct (lt_dec i1 i2); auto.
        destruct (eq_dec i1 i2).
        { subst; rewrite Hi1 in Hi2; clarify.
          generalize (drop_lin_id _ _ _ _ _ He2); intros (? & ? & Hid).
          rewrite Hid in *; exploit (lin_irrefl Hlin); eauto; clarify.
          rewrite (lin_set Hlin); auto. }
        assert (i2 < i1) as Hlt by omega.
        generalize (drop_lin_ord _ _ _ _ Hi2 Hi1 Hlt);
          intros (i2' & i1' & e2' & e1' & ? & ? & ? & Hid2 & Hid1).
        rewrite <- Hid1, <- Hid2 in *.
        exploit (lin_order_3(e1 := e1') Hlin i1' i2'); eauto; omega.
    - intros.
      generalize (nth_error_in _ _ Ha), (nth_error_in _ _ Hb); intros.
      rewrite <- Hset in *.
      exploit drop_sync_set; try apply Hsync; eauto; intros (a' & b' & Ha' & Hb'
        & Hida & Hidb & ?).
      generalize (drop_lin_ord _ _ _ _ Ha Hb Hlt);
        intros (i' & j' & a'' & b'' & ?); clarify.
      rewrite <- Hida, <- Hidb in *.
      exploit (lin_id_inj a'' a' Hlin); clarify.
      { rewrite (lin_set Hlin); eapply nth_error_in; eauto. }
      exploit (lin_id_inj b'' b' Hlin); clarify.
      { rewrite (lin_set Hlin); eapply nth_error_in; eauto. }
      eauto.
  Qed.

  Lemma private_seq : forall (E : execution) X ops
    (Htrans : transitive_on (hb X) (events E)) (Hrf : wf_rf E X)
    (Hwf : wf_lin E X)
    (Hin : forall e, In e ops -> events E e)
    (Htotal : total_on (hb X) (set_of ops)) a z (Ha : In a ops) (Hz : In z ops) 
    (Hbegin : forall e (He : In e ops), e = a \/ hb X (id a) (id e))
    (Hend : forall e (He : In e ops), e = z \/ hb X (id e) (id z))
    p (Hordered : forall e, events E e -> mods (op e) p ->
       hb X (id e) (id a) \/ In e ops \/ hb X (id z) (id e))
    (Hops : linearization (set_of ops) (hb X) ops)
    ops' X' (Hdrop : dlr p E (ops, X) = (ops', X')),
    valid E X <-> valid (upd_events E (Union
      (Setminus (events E) (set_of ops)) (set_of ops'))) X' /\
      exists m1, linearization (before (events E) (full (events E) X) a)
        (full (events E) X) m1 /\
      forall i r v (Hr : nth_error ops i = Some r)
        (Hreads : reads (op r) p v),
      match find (fun e => if find_mod (op e) p then true else false)
        (rev (m1 ++ firstn i ops)) with
      | Some w => rf X (id w) (id r) /\
          (exists a, last_op (to_seq' (op w)) (Ptr p) a /\ match_op err a v) /\
          forall r' v' (Hr' : Union (Setminus (events E) (set_of ops))
            (set_of ops') r') (Hreads' : reads (op r') p v')
            (Hhb : hb X (id w) (id r')), rf X (id w) (id r') \/
            (exists w', events E w' /\ hb X (id w) (id w') /\
                        rf X (id w') (id r'))
      | None => False
      end.
  Proof.
    unfold dlr; clarify.
    generalize (drop_ids_set E p); intro Hids; specialize (Hids ops); clarify.
    split; intro Hvalid.
    - destruct Hvalid as (Hreads & _ & _ & Hmo & Hcont & _).
      destruct Hrf as (Hunique & Hrf).
      assert (wf_lin (upd_events E (Union (Setminus (events E) (set_of ops))
        (set_of (drop_l_reads' p ops)))) {| rf := fun i j => rf X i j /\
        (forall e, events E e -> j = id e -> ~ dropped p ops e); hb := hb X |})
        as Hwf'.
      { destruct Hwf as (? & Hlin & ?).
        eexists; eapply drop_lin_wf; unfold dlr; eauto.
        unfold linearization in Hops; clarify. }
      repeat split; clarify; eauto.
      + unfold wf_reads in *; simpl in *; intros.
        generalize (drop_read_set _ _ _ _ Hin He Hread); intro He'.
        assert (~dropped p ops e).
        { unfold dropped; intro; clarify.
          rewrite Union_spec, Setminus_spec in He; clarify.
          exploit drop_read'; eauto; clarify. }
        specialize (Hreads _ He' _ _ Hread); destruct Hreads as (w & a' & Hw).
        generalize (dropped_dec(ops := ops) E p w); intro Hdropped; clarify.
        destruct Hwf as (l & Hlin & Hcomplete).
        generalize (full_lin Hlin); intros (Hhb_lin & Hrf_lin).
        specialize (Hdropped _ _ Hhb_lin).
        unfold dropped in Hdropped; destruct Hdropped as [(? & v' & ?) | ?].
        * generalize (last_op_in _ Hw2221), (last_op_mods Hw2221); intros.
          unfold reads in *; destruct w as [? (c, ?)]; destruct c; clarify.
          inversion H1; clarify.
          exists (Build_event id (Write t p v, s)), (MWrite p v).
          exploit drop_ARW'; eauto.
          { simpl; eauto. }
          intro Hinw.
          split; [unfold reads in *; intro; clarify|].
          split; [rewrite Union_spec; auto|].
          split.
          { clarify.
            exploit (lin_id_inj e0 e Hlin); clarify. }
          split.
          { exists 0; clarify.
            econstructor; simpl; eauto 2; clarify.
            destruct j; clarsimp. }
          clarify.
          rewrite Union_spec, Setminus_spec in *.
          generalize (Hw222222 w2); clarify.
          exploit drop_mods_inv'; eauto; intros (w2' & Hw2' & ?); clarify.
          specialize (Hin _ Hw2'); specialize (Hw222222 w2'); clarsimp.
        * exists w, a'; clarify.
          split; [eapply not_dropped_set; eauto|].
          split.
          { clarify.
            exploit (lin_id_inj e0 e Hlin); clarify. }
          clarify.
          rewrite Union_spec, Setminus_spec in *.
          generalize (Hw222222 w2); clarify.
          exploit drop_mods_inv'; eauto; intros (w2' & Hw2' & ?); clarify.
          specialize (Hin _ Hw2'); specialize (Hw222222 w2'); clarsimp.
      + exploit Hids; eauto; intros (e' & ? & Hid).
        specialize (Hi2 e'); clarify.
        destruct Hwf as (? & Hlin & ?).
        generalize (full_lin Hlin); intros (? & _).
        exploit not_dropped_set; eauto; intro.
        destruct Hwf' as (? & Hlin' & ?).
        exploit (lin_id_inj e' e Hlin'); clarify.
        specialize (Hrf i e); clarify; eauto.
      + intro p'; specialize (Hmo p'); destruct Hmo as (R & Hmo);
          inversion Hmo; exists R; repeat split; auto.
        * intros ?? He1 He2; clarify.
          generalize (drop_mod_set _ _ Hin He11 He12),
            (drop_mod_set _ _ Hin He21 He22);
            intros (e1' & ? & ? & Hid1) (e2' & ? & ? & Hid2).
          specialize (HR_total e1' e2'); clarify.
          rewrite Hid1, Hid2 in HR_total; clarify.
          rewrite Hid2 in Hid1.
          destruct Hwf' as (l & Hl & ?); exploit (lin_id_inj e1 e2 Hl); auto.
        * intros ?? Hij; specialize (Hdom _ _ Hij).
          destruct Hdom as (e1 & e2 & He11 & He12 & ? & He21 & He22 & ?).
          destruct Hwf as (? & Hlin & _); generalize (full_lin Hlin);
            intros (Hhb_lin & _).
          generalize (mod_drop_set _ _ p _ He11 He12 Hin Hhb_lin),
            (mod_drop_set _ _ p _ He21 He22 Hin Hhb_lin);
            intros (e1' & ?) (e2' & ?); exists e1', e2'; clarify.
        * clarify.
          exploit drop_read_set; try apply Hp; eauto; intro.
          generalize (Hids _ Hw), (Hids _ Hw2);
            intros (w' & ? & Hidw) (w2' & ? & Hidw2).
          rewrite Hidw2, Hidw in *; eapply HcoWR with (w := w'); eauto.
        * clarify.
          generalize (Hids _ He1), (Hids _ He2); intros (e1' & ? & Hid1)
            (e2' & ? & Hid2).
          rewrite Hid1, Hid2 in *; apply Hacyclic; auto.
          eapply full_transfer'; unfold dlr; eauto.
      + eapply transitive_on_sub'; eauto.
      + eapply critical_seq; unfold dlr; eauto.
        repeat split; auto.
    - destruct Hvalid as (Hvalid & m1 & Hm1 & Hseq).
      destruct Hrf as (Hunique & Hrf).
      repeat split; auto.
      + destruct Hwf as (? & ? & ?).
        eapply critical_reads; try apply Hbegin; try apply Hend; unfold dlr;
          eauto.
        intros; exploit Hseq; eauto.
        destruct (find (fun e => if find_mod (op e) p then true else false)
          (rev (m1 ++ firstn i ops))); clarify; eauto.
      + destruct Hwf as (? & ? & ?).
        eapply critical_mo'; try apply Hbegin; try apply Hend; unfold dlr;
          eauto.
        split; auto.
      + destruct Hvalid; clarify.
  Qed.

  Lemma drop_lin_drop : forall p ops S (HS : incl ops S)
    (Hops : NoDup (map id ops)),
    drop_lin S (drop_l_reads p ops) ops = drop_l_reads p ops.
  Proof.
    unfold incl; intros; induction ops; clarify.
    inversion Hops; clarify.
    exploit (find_succeeds (fun e => beq (id e) (id a)) S); eauto 3; unfold beq;
      clarify.
    assert (forall b, id b = id a -> drop_lin S (b :: drop_l_reads p ops) ops = 
      drop_l_reads p ops) as Heq.
    { intros; erewrite drop_lin_mono; [setoid_rewrite IHops; auto|].
      rewrite Forall_forall; unfold beq; clarify.
      contradiction H1; rewrite in_map_iff; clarsimp; eauto. }
    destruct a as [i (c, ?)]; destruct c; clarify; try (rewrite Heq; auto).
    - destruct (eq_dec p0 p); clarify; [|rewrite Heq; auto].
      destruct (find (fun e => if eq_dec (id e) i then true else false)
        (drop_l_reads p ops)) eqn: Hfind; auto.
      exploit find_success; eauto; clarify.
      exploit drop_ids; eauto; clarify.
      contradiction H1; rewrite in_map_iff; eauto.
    - destruct (eq_dec p0 p); clarify; rewrite Heq; auto.
  Qed.

  Corollary drop_lin_drop' : forall p ops (Hops : NoDup (map id ops)),
    drop_lin ops (drop_l_reads' p ops) ops = drop_l_reads' p ops.
  Proof.
    destruct ops; clarify.
    destruct e as [? (c, ?)]; clarify.
    inversion Hops; clarify.
    erewrite drop_lin_mono; [rewrite drop_lin_drop; auto|].
    - apply incl_refl.
    - rewrite Forall_forall; unfold beq; clarify.
      contradiction H1; rewrite in_map_iff; eauto.
  Qed.

  Instance LLVM_model : Memory_Model err nat := { valid := valid;
    drop_l_reads := dlr;
    well_formed := fun E X => wf_lin E X /\ wf_rf E X /\
      transitive_on (hb X) (events E) }.
  Proof.
    - unfold valid; clarify.
    - unfold valid; clarify.
    - intros ?? (Hreads & _); unfold rf_reads, wf_reads in *;
        intros.
      specialize (Hreads _ He _ _ Hread); destruct Hreads as (w & Hw);
        exists w; clarify.
      exists x; split; [eapply last_op_in | eapply last_op_mods]; eauto.
    - unfold wf_lin; clarify; eauto.
    - unfold valid; clarify.
    - clarify.
      destruct Hwf21; repeat split; auto.
      + repeat intro.
        specialize (Hno_reads _ _ _ He Hread); clarify.
      + intro.
        destruct Hwf1 as (l & Hlin & ?).
        exists (fun i j => exists i1 i2 e1 e2, nth_error l i1 = Some e1 /\
          nth_error l i2 = Some e2 /\ id e1 = i /\ id e2 = j /\ i1 < i2 /\
          mods (op e1) p /\ mods (op e2) p); constructor.
        * intros e1 e2 (He1 & ?) (He2 & ?).
          rewrite (lin_set Hlin) in *; generalize (in_nth_error _ _ He1),
            (in_nth_error _ _ He2); intros (i1 & ? & ?) (i2 & ? & ?).
          destruct (lt_eq_lt_dec i1 i2) as [[? | ?] | ?].
          { left; exists i1, i2, e1, e2; clarify. }
          { clarsimp. }
          { right; right; exists i2, i1, e2, e1; clarify. }
        * intros ?? (? & ? & ? & ? & Hi1 & Hi2 & ?).
          generalize (nth_error_in _ _ Hi1), (nth_error_in _ _ Hi2);
            repeat rewrite <- (lin_set Hlin); clarify; eauto 10.
        * intros.
          exploit (Hno_reads e); eauto.
        * intros ????? (i1 & i2 & e1' & e2' & ?); clarify.
          exploit (lin_id_inj e1' e2 Hlin); auto.
          { rewrite (lin_set Hlin); eapply nth_error_in; eauto. }
          exploit (lin_id_inj e2' e1 Hlin); clarify.
          { rewrite (lin_set Hlin); eapply nth_error_in; eauto. }
          exploit (lin_order_3(e1 := e1) Hlin i2 i1); eauto; omega.
        * intros ? (i1 & i2 & e1 & e2 & ?); clarify.
          exploit (lin_id_inj e1 e2 Hlin); clarify.
          { rewrite (lin_set Hlin); eapply nth_error_in; eauto. }
          { rewrite (lin_set Hlin); eapply nth_error_in; eauto. }
          generalize (lin_nodup Hlin); intro Hnodup.
          exploit (NoDup_inj(x := e2) i1 i2 Hnodup); clarify; omega.
    - intros ?? (Hreads & (? & Hrf) & Hlin & Hmo & ?) ???.
      assert (forall e, In e l1 -> events E e).
      { intro; rewrite (lin_set Hlin0), in_app; auto. }
      repeat split; clarify; eauto.
      + unfold wf_reads in *; clarify.
        specialize (Hreads e); rewrite (lin_set Hlin0), in_app in Hreads;
          clarify.
        specialize (Hreads _ _ Hread); destruct Hreads as (w & a & Hw);
          exists w, a; clarify; repeat split; auto.
        * rewrite (lin_set Hlin0), in_app in Hw21; clarify.
          generalize (lin_split _ _ Hlin0); intro Hnot.
          exploit Hnot; eauto; clarify; apply t_step; repeat eexists; auto.
          right; auto.
          rewrite (lin_set Hlin0), in_app; auto.
        * intros.
          specialize (Hw222222 w2); rewrite (lin_set Hlin0), in_app in *;
            clarify.
      + destruct Hlin as (l & Hlin & Hcomplete).
        set (f := (fun e => match find (fun e' => beq (id e') (id e)) l1
          with Some _ => true | None => false end)).
        exists (filter f l); split.
        * simpl.
          assert (set_of l1 = set_of (filter f l)) as Hset.
          { apply set_ext; intro.
            subst f; setoid_rewrite filter_In; rewrite <- (lin_set Hlin),
              (lin_set Hlin0), in_app; split; clarify.
            * rewrite find_fail, Forall_forall in cond.
              exploit cond; eauto 2; unfold beq; clarify.
            * exploit find_success; eauto; unfold beq; clarify.
              unfold linearization in Hlin0; clarify.
              rewrite map_app, NoDup_app in Hlin021; clarify.
              exploit Hlin02122; clarify; rewrite in_map_iff; eauto. }
          rewrite Hset at 1; eapply lin_filter; eauto.
          eapply lin_contained; [|apply full_cont]; eauto.
        * intros ????? Hi Hj ?.
          generalize (filter_idem f l); intro Heq; symmetry in Heq.
          generalize (nth_error_in _ _ Hi), (nth_error_in _ _ Hj);
            repeat rewrite filter_In; clarify.
          eapply Hcomplete.
          { rewrite <- (find_match_mono f i j); try apply Heq; eauto 2. }
          { apply find_match_valid; auto. }
          { apply find_match_valid; auto. }
          auto.
      + intro p; specialize (Hmo p); destruct Hmo as (R & HR).
        exists (fun i j => In i (map id l1) /\ In j (map id l1) /\ R i j);
          inversion HR; simpl; constructor.
        * repeat intro; clarify.
          specialize (HR_total e1 e2); clarify.
          assert (In (id e1) (map id l1)) by (rewrite in_map_iff; eauto).
          assert (In (id e2) (map id l1)) by (rewrite in_map_iff; eauto).
          destruct HR_total as [? | [? | ?]]; auto.
        * intros ?? (Hi & Hj & Hij).
          rewrite in_map_iff in *; destruct Hi as (e1 & ?), Hj as (e2 & ?).
          specialize (Hdom _ _ Hij); destruct Hdom as (e1' & e2' & ?); clarify;
            exists e1', e2'; repeat split; auto.
          { exploit (lin_id_inj e1' e1 Hlin0); clarify. }
          { exploit (lin_id_inj e2' e2 Hlin0); clarify. }
        * clarify; eauto.
        * repeat intro; clarify.
          exploit (Hacyclic e1 e2); auto.
          eapply full_cont; eauto.
          intro; unfold Ensembles.In; auto.
        * repeat intro; clarify.
          exploit Hirrefl; eauto.
      + eapply transitive_on_sub; eauto.
    - unfold dlr; clarify; apply drop_l_reads_spec'.
    - clarify; split; [|split].
      + destruct Hwf1 as (l' & ? & ?).
        eexists; eapply drop_lin_wf; eauto.
      + unfold dlr in *; clarify.
        destruct Hwf21 as (? & Hrf); split; clarify; eauto.
        rewrite Union_spec, Setminus_spec in He; destruct He; clarify; eauto.
        exploit drop_inv'; eauto; intros (e' & ? & Hid & ?).
        specialize (Hi2 e'); clarify.
        rewrite <- Hid in *; exploit Hrf; eauto; intros (p & v & ?).
        unfold reads in *; clarify.
        destruct e' as [? (c, ?)], e as [? (c', ?)]; clarify.
        destruct c; clarify.
        * destruct (eq_dec p0 l); clarify; eauto.
          contradiction Hi2; split; eauto; unfold reads; simpl; eauto.
        * destruct (eq_dec p0 l); clarify; eauto.
          contradiction Hi2; split; eauto; unfold reads; simpl; eauto.
      + unfold dlr in *; clarify.
        eapply transitive_on_sub'; eauto.
        apply drop_ids_set; auto.
    - unfold dlr; clarify.
      split; [apply drop_NoDup' | apply drop_ids']; auto.
    - unfold dlr; clarify.
      split; [|clarify; split].
      + split; [reflexivity|].
        split; [unfold linearization in Hlin; clarify; apply drop_NoDup';
                auto|].
        intros.
        generalize (in_nth_error _ _ He1), (in_nth_error _ _ He2);
          intros (i1 & ? & Hi1) (i2 & ? & Hi2).
        destruct (lt_eq_lt_dec i1 i2) as [[? | ?] | ?]; eauto.
        { clarsimp.
          exploit drop_ids'; eauto; intros (? & ? & Hid).
          rewrite Hid in *; exploit (lin_irrefl Hlin); eauto; clarify. }
        assert (NoDup (map id ops)) by (unfold linearization in Hlin; clarify).
        erewrite <- drop_lin_drop' in Hi1, Hi2; eauto.
        generalize (drop_lin_ord _ _ _ _ Hi2 Hi1 l0).
        intros (i1' & i2' & e1' & e2' & ? & ? & ? & Hid1 & Hid2).
        rewrite <- Hid1, <- Hid2 in *.
        exploit (lin_order_3(e1 := e2') Hlin i2' i1'); eauto; omega.
      + apply contained_refl.
      + split; [|reflexivity].
        eapply transitive_on_sub'; eauto.
        apply drop_ids_set; auto.
    - unfold dlr; clarify.
      destruct c as [? (c, ?)].
      repeat intro; clarify.
      rewrite Union_spec, Subtract_spec in *; clarify.
      destruct He1 as [He1 | He1], He2 as [He2 | He2]; clarify.
      + eapply Hrf; eauto.
      + specialize (Hrf _ _ p He11 Hin); clarify.
        exploit drop_read_touches; eauto; clarify.
        destruct Hmods; clarify.
        exploit drop_read_mods; eauto; clarify.
      + specialize (Hrf _ _ p Hin He21); clarify.
        exploit drop_read_touches; eauto; clarify.
        destruct Hmods; clarify.
        exploit drop_read_mods; eauto; clarify.
    - unfold dlr; clarify.
      destruct ops; clarify.
      destruct e as [? (?, ?)]; simpl.
      apply le_n_S, drop_l_reads_length.
    - unfold dlr; clarify.
      destruct Hwf21 as (? & Hrf); split; intros (? & Hr).
      + rewrite Union_spec, Setminus_spec in He2; destruct He2.
        { specialize (Hrf (id e1) e2); clarify; eauto. }
        exploit drop_inv'; eauto; intros (e' & ? & Hid & ?).
        specialize (Hr e'); clarify.
        rewrite <- Hid in *; specialize (Hrf (id e1) e'); clarify.
        destruct (eq_dec x l).
        * contradiction Hr; split; clarify; eauto.
        * unfold reads in *; destruct e' as [? (c, ?)], e2 as [? (?, ?)];
            destruct c; clarify.
          { inversion H3; clarify.
            destruct (eq_dec x l); clarify; eauto. }
          { inversion Hrf; clarify.
            destruct (eq_dec x l); clarify; eauto. }
      + clarify; unfold dropped; intro; clarify.
        exploit drop_read_set; eauto; intro.
        destruct Hwf1 as (? & Hlin & ?).
        exploit (lin_id_inj e e2 Hlin); clarify.
        rewrite Union_spec, Setminus_spec in He2; clarify.
        exploit drop_read'; eauto; clarify.
    - intros; eapply private_seq; try apply Hordered; eauto; clarify.
  Defined.

End LLVM_model.