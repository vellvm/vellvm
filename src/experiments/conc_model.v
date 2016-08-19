(* Extending the block model to concurrency. *)
Require Import Ensembles.
Require Import Permutation.
Require Import Util.
Require Import block_model.
Require Import Relation_Operators.
Import Bool.
Import EquivDec.
Import CoqEqDec.

Set Implicit Arguments.

Arguments clos_trans [_] _ _ _.
Arguments union [_] _ _ _ _.
Arguments op_modifies [_] [_] [_] _ _.

Section Concurrency.
  Context `(ML : Memory_Layout) {thread : Type}.

  Variable err : val.

  Notation mem_op := (mem_op block val).

  Definition match_op (a : mem_op) v := match a with MWrite p' v' => v' = v
    | MFree _ | MAlloc _ _ => v = err | _ => False end.

  Class MM_base (conc_op : Type) :=
    { thread_of : conc_op -> thread;
      to_seq : conc_op -> list mem_op;
      write_after_mod : forall c i j p v a,
        nth_error (to_seq c) i = Some (MWrite p v) ->
        nth_error (to_seq c) j = Some a -> op_modifies a p = true -> j <= i;
      read_before_mod : forall c i j p v a,
        nth_error (to_seq c) i = Some (MRead p v) ->
        nth_error (to_seq c) j = Some a -> op_modifies a p = true -> i < j }.

  Context `{Mb : MM_base}.

  Definition adjust_range {A} (l1 l l' : list A) i :=
    if lt_dec i (length l1) then i else i + length l' - length l.

  Lemma adjust_idem : forall A (l1 l l' : list A) i
    (Hlen : length l = length l'), adjust_range l1 l l' i = i.
  Proof.
    unfold adjust_range; clarsimp.
  Qed.

  Lemma adjust_range_nth : forall A i (m1 ops : list A) m2 ops'
    (Hrange : i < length m1 \/ i >= length m1 + length ops),
    inth (iapp m1 (iapp ops' m2)) (adjust_range m1 ops ops' i) =
    inth (iapp m1 (iapp ops m2)) i.
  Proof.
    intros; repeat rewrite iapp_nth.
    unfold adjust_range; destruct (lt_dec i (length m1)); clarify.
    destruct (lt_dec (i - length m1) (length ops)); [omega|].
    destruct (lt_dec (i + length ops' - length ops) (length m1)); [omega|].
    destruct (lt_dec (i + length ops' - length ops - length m1) (length ops'));
      [omega|].
    assert (i + length ops' - length ops - length m1 - length ops' =
      i - length m1 - length ops) as Heq; [|rewrite Heq; auto].
    rewrite NPeano.Nat.add_sub_swap, NPeano.Nat.add_sub_swap; [| omega | omega].
    rewrite NPeano.Nat.add_sub, minus_comm; auto; omega.
  Qed.

  Corollary adjust_range_nth_error : forall A i (m1 ops : list A) m2 ops'
    (Hrange : i < length m1 \/ i >= length m1 + length ops),
    nth_error (m1 ++ ops' ++ m2) (adjust_range m1 ops ops' i) =
    nth_error (m1 ++ ops ++ m2) i.
  Proof.
    intros; repeat rewrite <- inth_nth_error; repeat rewrite to_ilist_app.
    apply adjust_range_nth; auto.
  Qed.

  Lemma adjust_adjust : forall {A} (l1 l l' : list A) i
    (Hrange : i < length l1 \/ i >= length l1 + length l),
    adjust_range l1 l' l (adjust_range l1 l l' i) = i.
  Proof.
    unfold adjust_range; intros.
    destruct (lt_dec i (length l1)); clarify.
    destruct (lt_dec (i + length l' - length l)); omega.
  Qed.

  Lemma adjust_lt : forall {A} (l1 l l' : list A) i j
    (Hi : i < length l1 \/ i >= length l1 + length l)
    (Hj : j < length l1 \/ j >= length l1 + length l),
    adjust_range l1 l l' i < adjust_range l1 l l' j <-> i < j.
  Proof.
    unfold adjust_range; intros.
    destruct (lt_dec i (length l1)), (lt_dec j (length l1)); omega.
  Qed.

  Lemma adjust_le : forall {A} (l1 l l' : list A) i j
    (Hi : i < length l1 \/ i >= length l1 + length l)
    (Hj : j < length l1 \/ j >= length l1 + length l),
    adjust_range l1 l l' i <= adjust_range l1 l l' j <-> i <= j.
  Proof.
    unfold adjust_range; intros.
    destruct (lt_dec i (length l1)), (lt_dec j (length l1)); omega.
  Qed.

  Notation not_read := (@not_read block val).

  Definition b_not_read b op := not_read op && beq (block_of op) b.

  Variables (eid : Type) (eid_eq : EqDec_eq eid).

  Record event := { id : eid; op : conc_op }.

  Definition order := eid -> eid -> Prop.

  Record execution := { events : event -> Prop; constraints : order }.

  Notation lower m := (flatten (map to_seq (map op m))).

  Lemma lower_app : forall m1 m2, lower (m1 ++ m2) = lower m1 ++ lower m2.
  Proof.
    intros; rewrite map_app, map_app, flatten_app; auto.
  Qed.
  
  Lemma nth_lower_split : forall m i x (Hnth : nth_error (lower m) i = Some x),
    exists m1 e m2 i', m = m1 ++ e :: m2 /\
      nth_error (to_seq (op e)) i' = Some x /\ i = length (lower m1) + i'.
  Proof.
    intros.
    exploit nth_flatten_split; eauto; clarify.
    exploit list_append_map_inv; eauto; intro Hm; clarify.
    exploit list_append_map_inv; [apply Hm22 | intros [m1 [m2 ?]]]; clarify.
    destruct m2; clarify.
    repeat eexists; eauto.
  Qed.

  Record witness := { rf : order; hb : order }.

  Definition hbe (X : witness) i j := i = j \/ hb X i j.

  Definition reads c p v := In (MRead p v) (to_seq c).
  Definition reads_from c p := exists v, reads c p v.
  Definition writes c p v := In (MWrite p v) (to_seq c).
  Definition writes_to c p := exists v, writes c p v.
  Definition mods c p := exists op, In op (to_seq c) /\
    op_modifies op p = true.
  Definition touches c p := exists op, In op (to_seq c) /\
    ~independent (loc_of op) (Ptr p).

  (* For now, races and critical sections are on a whole block
     (since this is the granularity of alloc/free). *)
  Definition race_free (E : Ensemble event) X := forall e1 e2 p (He1 : E e1)
    (He2 : E e2) (Hp1 : touches (op e1) p) (Hp2 : touches (op e2) p)
    (Hmods : mods (op e1) p \/ mods (op e2) p),
    hb X (id e1) (id e2) \/ e1 = e2 \/ hb X (id e2) (id e1).

  (* For drop_reads, we need to be able to pull the reads out of both the
     execution and the orders in the witness (since we're not generating
     the witness orders from the new trace). *)

  (* Sticking to finite ones for now because how do you linearize
     an infinite number of things? *)
  Definition linearization E (R : order) l := (forall e, E e <-> In e l) /\
    NoDup (map id l) /\ (forall e1 e2 (He1 : E e1) (He2 : E e2)
      (Horder : R (id e1) (id e2)),
     exists i1 i2, nth_error l i1 = Some e1 /\ nth_error l i2 = Some e2 /\
       i1 < i2).    

  Definition total_on (R : order) (E : event -> Prop) := forall e1 e2,
    E e1 -> E e2 -> R (id e1) (id e2) \/ e1 = e2 \/ R (id e2) (id e1).

  Lemma drop_nth_error : forall A (l1 l2 : list A) a i (Hneq : i <> length l1),
    nth_error (l1 ++ l2) (drop_index i (length l1)) =
    nth_error (l1 ++ a :: l2) i.
  Proof.
    intros; repeat rewrite nth_error_app.
    unfold drop_index; destruct (lt_dec i (length l1)); clarify.
    destruct (i - length l1) eqn: Hminus; [omega | simpl].
    destruct (lt_dec (i - 1) (length l1)); [omega|].
    rewrite minus_comm; [|omega].
    rewrite <- pred_of_minus; rewrite Hminus; auto.
  Qed.

  Lemma drop_index_lt : forall i j k (Hlt : i < j) (Hi : i <> k) (Hj : j <> k),
    drop_index i k < drop_index j k.
  Proof.
    unfold drop_index; intros.
    destruct (lt_dec i k), (lt_dec j k); omega.
  Qed.

  Lemma lin_cons_inv : forall a l E R (Hlin : linearization E R (a :: l)),
    linearization (Subtract E a) R l.
  Proof.
    unfold linearization; clarify.
    split; [|split].
    - setoid_rewrite Setminus_spec; setoid_rewrite Hlin1; split; clarify.
      + contradiction H2; constructor.
      + intro He; inversion He; subst.
        inversion Hlin21; clarify.
        rewrite in_map_iff in *; contradiction H2; eauto.
    - inversion Hlin21; auto.
    - setoid_rewrite Setminus_spec; clarify.
      specialize (Hlin22 e1 e2); clarify.
      destruct x0; [omega|].
      destruct x; clarify.
      + contradiction H2; constructor.
      + repeat eexists; eauto; omega.
  Qed.

  Lemma lin_nodup : forall l E R (Hlin : linearization E R l), NoDup l.
  Proof.
    induction l; clarify.
    specialize (IHl _ _ (lin_cons_inv Hlin)).
    constructor; auto.
    intro; unfold linearization in *; clarify.
    inversion Hlin21; clarify.
    rewrite in_map_iff in *; contradiction H2; eauto.
  Qed.    

  Lemma lin_cons_inv' : forall a l E R (Hlin : linearization E R (a :: l)),
    linearization (Subtract E a) R l /\ ~In (id a) (map id l) /\
    forall e, In e l -> ~R (id e) (id a).
  Proof.
    intros; exploit lin_cons_inv; eauto; clarify.
    generalize (lin_nodup Hlin); intro Hnodup.
    unfold linearization in Hlin; clarify.
    inversion Hlin21; clarify.
    intro; specialize (Hlin22 e a).
    repeat rewrite Hlin1 in Hlin22; clarify.
    generalize (NoDup_inj _ 0 Hnodup Hlin2221); clarify; omega.
  Qed.

  Lemma lin_cons : forall a l E R (Hlin : linearization E R l)
    (Hid : ~In (id a) (map id l)) (Hfree : forall e, E e -> ~R (id e) (id a))
    (Hirrefl : ~R (id a) (id a)), linearization (Add E a) R (a :: l).
  Proof.
    unfold linearization; clarify.
    assert (~E a).
    { intro; contradiction Hid.
      rewrite Hlin1 in *; rewrite in_map_iff; eauto. }
    split; [|split].
    - setoid_rewrite Add_spec; setoid_rewrite Hlin1; split; clarify.
    - constructor; auto.
    - intros ?? He1 He2 ?; rewrite Add_spec in *.
      destruct He1, He2; clarify.
      + specialize (Hlin22 e1 e2); clarify.
        exists (S x), (S x0); clarify.
      + specialize (Hfree e1); clarify.
      + rewrite Hlin1 in *; exploit in_nth_error; eauto; intros (i & Hi).
        exists 0, (S i); clarify.
  Qed.
      
  Lemma lin_remove : forall E R l1 e l2
    (Hlin : linearization E R (l1 ++ e :: l2)), E e /\
    linearization (Subtract E e) R (l1 ++ l2).
  Proof.
    intros; generalize (lin_nodup Hlin); intro Hnodup.
    unfold linearization in *; clarify.
    rewrite Hlin1, in_app; clarify.
    split; [|split].
    - intro; unfold Subtract, Setminus; rewrite Hlin1; repeat rewrite in_app;
        split; clarify.
      + contradiction H2; apply In_singleton.
      + split; clarify.
        intro Hin; inversion Hin; clarify.
        exploit NoDup_remove_2; eauto; rewrite in_app; auto.
    - rewrite map_app in *; eapply NoDup_remove_1; eauto.
    - intros ?? He1 He2 HR.
      unfold Subtract, Setminus in *; clarify.
      specialize (Hlin22 _ _  He11 He21 HR); destruct Hlin22 as [i1 [i2 Hi]].
      exists (drop_index i1 (length l1)), (drop_index i2 (length l1)).
      assert (i1 <> length l1).
      { intro; subst; rewrite nth_error_split in *; clarify.
        contradiction He12; apply In_singleton. }
      assert (i2 <> length l1).
      { intro; subst; rewrite nth_error_split in *; clarify.
        contradiction He22; apply In_singleton. }
      clarify; split; [erewrite drop_nth_error; eauto|].
      split; [erewrite drop_nth_error; eauto|].
      apply drop_index_lt; auto.
  Qed.

  Opaque minus.

  Lemma add_nth_error : forall A (l1 l2 : list A) a i,
    nth_error (l1 ++ a :: l2) (add_index i (length l1)) =
    nth_error (l1 ++ l2) i.
  Proof.
    intros; unfold add_index.
    repeat rewrite nth_error_app; destruct (lt_dec i (length l1)); clarify.
    destruct (lt_dec (S i) (length l1)); [omega|].
    rewrite <- minus_Sn_m; [clarify | omega].
  Qed.

  Lemma lin_add : forall E R l1 e l2 (Hlin : linearization E R (l1 ++ l2))
    (Hid : ~In (id e) (map id (l1 ++ l2))) (Hirrefl : ~R (id e) (id e))
    (Hfree1 : forall e', In e' l1 -> ~R (id e) (id e'))
    (Hfree2 : forall e', In e' l2 -> ~R (id e') (id e)),
    linearization (Add E e) R (l1 ++ e :: l2).
  Proof.
    unfold linearization; clarify.
    split; [|split].
    - intro; rewrite Add_spec, Hlin1, in_app, in_app; split; clarify.
    - rewrite map_app, NoDup_app in *; clarify.
      rewrite in_app in *; split; clarify.
      + constructor; auto.
      + intro; clarify.
        specialize (Hlin2122 x); clarify.
    - intros ?? He1 He2 ?; rewrite Add_spec in *.
      destruct He1 as [He1 | ?], He2 as [He2 | ?]; clarify.
      + specialize (Hlin22 e1 e2); clarify.
        exists (add_index x (length l1)), (add_index x0 (length l1)).
        repeat rewrite add_nth_error; clarify.
        apply add_lt; auto.
      + specialize (Hfree2 e1).
        rewrite Hlin1, in_app in He1; destruct He1; clarify.
        exploit in_nth_error; eauto; intros [i ?].
        exists i, (length l1); rewrite nth_error_app, nth_error_split; clarify.
      + specialize (Hfree1 e2).
        rewrite Hlin1, in_app in He2; destruct He2; clarify.
        exploit in_nth_error; eauto; intros [i ?].
        exists (length l1), (length l1 + S i);
          rewrite nth_error_plus, nth_error_split; clarify; omega.
  Qed.        
  
  Lemma total_on_sub : forall E E' R (Htotal : total_on R E)
    (Hsub : Included E' E), total_on R E'.
  Proof.
    repeat intro.
    apply Htotal; apply Hsub; auto.
  Qed.

  Lemma minus_sub : forall A (E E' : Ensemble A),
    Included (Setminus E E') E.
  Proof.
    unfold Setminus; repeat intro.
    unfold Ensembles.In in *; clarify.
  Qed.

  Corollary sub_sub : forall A E (x : A), Included (Subtract E x) E.
  Proof. intros; apply minus_sub. Qed.

  Lemma total_lin : forall E R l1 l2 (Htotal : total_on R E)
    (Hl1 : linearization E R l1) (Hl2 : linearization E R l2), l1 = l2.
  Proof.
    intros until l1; revert E; induction l1; clarify.
    - unfold linearization in *; clarify.
      setoid_rewrite Hl11 in Hl21; destruct l2; clarify.
      specialize (Hl21 e); destruct Hl21; clarify.
    - generalize (lin_remove [] _ _ Hl1); clarify.
      assert (In a l2).
      { unfold linearization in Hl2; clarify.
        rewrite <- Hl21; auto. }
      exploit in_split; eauto; intros [l2a [l2b ?]]; subst.
      exploit lin_remove; eauto; clarify.
      generalize (total_on_sub Htotal (@sub_sub _ _ a)); intro Htotal'.
      specialize (IHl1 _ (l2a ++ l2b) Htotal'); clarify.
      generalize (lin_nodup Hl2); intro Hnodup.
      destruct l2a; unfold linearization in Hl2; clarify.
      specialize (Hl21 e); destruct Hl21; clarify.
      inversion Hnodup as [|?? Hout]; clarify.
      specialize (Htotal a e); clarify; destruct Htotal as [? | [? | ?]];
        clarify.
      + specialize (Hl222 a e); clarify.
        destruct x0; clarify; [omega|].
        exploit nth_error_in; eauto; clarify.
      + contradiction Hout; rewrite in_app; clarify.
      + generalize (lin_nodup Hl1); intro Hnodup1.
        unfold linearization in Hl1; inversion Hnodup1; clarify.
        specialize (Hl122 e a); clarify.
        destruct x0; clarify; [omega|].
        exploit nth_error_in; eauto; clarify.
  Qed.
        
  Variable default : eid.

  Definition contained (R R' : order) := forall i j, R i j -> R' i j.

  Definition upd_events E es :=
    {| events := es; constraints := constraints E |}.

  Definition before E R e e' := E e' /\ R (id e') (id e).

  Definition transitive_on (R : order) (S : Ensemble event) := forall e1 e2 e3
    (He1 : S e1) (He2 : S e2) (He3 : S e3) (H12 : R (id e1) (id e2))
    (H23 : R (id e2) (id e3)), R (id e1) (id e3).

  Lemma transitive_on_sub : forall E E' R (Htrans : transitive_on R E)
    (Hsub : Included E' E), transitive_on R E'.
  Proof.
    repeat intro.
    eapply Htrans; eauto; apply Hsub; auto.
  Qed.

  Definition order_join (R1 R2 : order) i j := R1 i j \/ R2 i j.

  Lemma lin_join : forall E R1 R2 l,
    linearization E (order_join R1 R2) l <->
    linearization E R1 l /\ linearization E R2 l.
  Proof.
    unfold linearization, order_join; split; clarify.
  Qed.

  Lemma clos_trans_right : forall A (R : A -> A -> Prop)
    x y (Htrans : clos_trans R x y) z (Hstep : R y z), clos_trans R x z.
  Proof.
    intros ?????; induction Htrans; intros.
    - eapply t_trans; apply t_step; eauto.
    - eapply t_trans; [eauto | apply IHHtrans2; auto].
  Qed.

  Lemma clos_trans_trans : forall R S, transitive_on (clos_trans R) S.
  Proof.
    repeat intro; eapply t_trans; eauto.
  Qed.

  Lemma lin_contained : forall S R l R' (Hlin : linearization S R l)
    (Hcont : contained R' R), linearization S R' l.
  Proof. unfold linearization; clarify. Qed.

  Instance contained_refl : Reflexive contained.
  Proof. repeat intro; auto. Qed.

  Instance contained_trans : Transitive contained.
  Proof. repeat intro; auto. Qed.

  Definition restrict R (S : Ensemble event) i j := R i j /\
    exists ei ej, S ei /\ S ej /\ id ei = i /\ id ej = j.

  Definition full E X := clos_trans (restrict (union (hb X) (rf X)) E).

  Lemma full_lin : forall E X l (Hlin : linearization E (full E X) l),
    linearization E (hb X) l /\ linearization E (rf X) l.
  Proof.
    unfold linearization; split; clarify; apply Hlin22; auto.
    - unfold full; apply t_step; unfold restrict, union; clarify;
        repeat eexists; eauto.
    - unfold full; apply t_step; unfold restrict, union; clarify;
        repeat eexists; eauto.
  Qed.

  Definition complete_order R l a b := R a b \/
    exists i1 i2 e1 e2, i1 < i2 /\ nth_error l i1 = Some e1 /\
      nth_error l i2 = Some e2 /\ id e1 = a /\ id e2 = b.

  Lemma complete_order_total : forall R e1 e2 m (He1 : In e1 m) (He2 : In e2 m),
    complete_order R m (id e1) (id e2) \/ e1 = e2 \/
    complete_order R m (id e2) (id e1).
  Proof.
    unfold complete_order; intros.
    generalize (in_nth_error _ _ He1), (in_nth_error _ _ He2);
      intros (i1 & ? & ?) (i2 & ? & ?).
    destruct (lt_dec i1 i2).
    { left; right; do 4 eexists; eauto. }
    right; destruct (eq_dec i1 i2); clarsimp.
    assert (i2 < i1) by omega.
    right; right; do 4 eexists; eauto.
  Qed.

  Lemma complete_order_lin : forall S R l (Hlin : linearization S R l),
    linearization S (complete_order R l) l.
  Proof.
    unfold linearization, complete_order; clarify.
    rewrite Hlin1 in *.
    generalize (in_nth_error _ _ He1), (in_nth_error _ _ He2);
      intros (i1 & ? & ?) (i2 & ? & ?).
    generalize (NoDup_inj(x := id x1) x i1 Hlin21),
      (NoDup_inj(x := id x2) x0 i2 Hlin21).
    repeat (erewrite map_nth_error; eauto); clarsimp; eauto.
  Qed.

  Definition complete_hb X l := {| rf := rf X; hb := complete_order (hb X) l |}.

  Lemma complete_hb_contained : forall X l,
    contained (hb X) (hb (complete_hb X l)).
  Proof.
    unfold complete_hb; repeat intro.
    unfold complete_order; simpl; auto.
  Qed.

  Lemma complete_full_contained : forall E X l,
    contained (full E X) (full E (complete_hb X l)).
  Proof.
    repeat intro; induction H.
    - apply t_step; unfold union, restrict in *; clarify; split;
        [|repeat eexists; eauto].
      unfold complete_order; clarify; eauto.
    - eapply t_trans; eauto.
  Qed.    

  Notation find_mod c p := (find (fun a => op_modifies a p) (to_seq c)).

  Lemma mods_spec : forall c p, if find_mod c p then mods c p else ~mods c p.
  Proof.
    intros; destruct (find_mod c p) eqn: Hfind.
    - rewrite find_spec in Hfind; clarify.
      unfold mods; exploit nth_error_in; eauto.
    - intros (a & Hin & Hmods).
      rewrite find_fail, Forall_forall in Hfind; exploit Hfind; eauto; clarify.
  Qed.

  Definition SC E X := contained (constraints E) (hb X) /\
    transitive_on (hb X) (events E) /\
    exists l, linearization (events E) (full (events E) X) l /\
(*      consistent (filter not_read (lower l)) /\*)
    forall i r p v (Hr : nth_error l i = Some r) (Hreads : reads (op r) p v),
      match find (fun e => if find_mod (op e) p then true else false)
                 (rev (firstn i l)) with
      | Some w => rf X (id w) (id r) /\
          exists a, last_op (to_seq (op w)) (Ptr p) a /\ match_op a v
      | None => False
      end.
    
  Notation linear R l := (linearization (set_of l) R l).

  Lemma complete_order_trans : forall R l (Hlin : linear R l),
    transitive_on (complete_order R l) (set_of l).
  Proof.
    repeat intro.
    exploit complete_order_lin; eauto; intro Hlin'.
    generalize (complete_order_total R e1 e3 l); clarify.
    generalize (lin_nodup Hlin); intro Hnodup.
    unfold linearization in Hlin'; clarify.
    exploit (Hlin'22 e1 e2); eauto; intros (i1 & i2 & Hi1 & Hi2 & Hlt1).
    exploit (Hlin'22 e2 e3); eauto; intros (i2' & i3 & Hi2' & Hi3 & Hlt2).
    generalize (NoDup_inj _ _ Hnodup Hi2' Hi2); clarify.
    destruct H; subst.
    - generalize (NoDup_inj _ _ Hnodup Hi1 Hi3); omega.
    - specialize (Hlin'22 e3 e1); clarify.
      generalize (NoDup_inj _ _ Hnodup Hi1 Hlin'2221),
        (NoDup_inj _ _  Hnodup Hi3 Hlin'221); omega.
  Qed.    

  Lemma lin_set : forall E R l (Hlin : linearization E R l) e,
    E e <-> In e l.
  Proof. unfold linearization; clarify. Qed.

  Corollary lin_set' : forall E R l (Hlin : linearization E R l),
    set_of l = E.
  Proof.
    intros; apply set_ext; intro.
    setoid_rewrite <- (lin_set Hlin); reflexivity.
  Qed.

  Corollary lin_linear : forall E R l (Hlin : linearization E R l), linear R l.
  Proof. intros; rewrite (lin_set' Hlin); auto. Qed.

  Definition rf_reads (E : Ensemble event) X := forall e (He : E e) p v
    (Hread : reads (op e) p v), exists w, w <> e /\ E w /\
    rf X (id w) (id e) /\ mods (op w) p(* /\
    forall w2, E w2 -> mods (op w2) p ->
      hb X (id w) (id w2) -> hb X (id w2) (id e) -> False*).

  Notation ptr := (ptr block).

  Class Memory_Model := { well_formed : execution -> witness -> Prop;
    valid : execution -> witness -> Prop;
    valid_wf E X (Hvalid : valid E X) : well_formed E X;
    valid_hb E X (Hvalid : valid E X) : contained (constraints E) (hb X);
    valid_rf E X (Hvalid : valid E X) : rf_reads (events E) X;
    wf_full E X (Hwf : well_formed E X) :
      exists l, linearization (events E) (full (events E) X) l;
    (* At the moment this forces finiteness. Fix? *)
    hb_trans E X (Hvalid : valid E X) : transitive_on (hb X) (events E);
(*    valid_lin E X (Hvalid : valid E X) : forall l
      (Hlin : linearization (events E) (full (events E) X) l),
      consistent (filter not_read (lower l));*)
    valid_no_reads E X (Hwf : well_formed E X)
      (Hcont : contained (constraints E) (hb X))
      (Hno_reads : forall e p v, events E e -> ~reads (op e) p v) :
      valid E X;
    valid_prefix E X (Hvalid : valid E X) : forall l1 l2
      (Hlin : linearization (events E) (full (events E) X) (l1 ++ l2)),
      valid (upd_events E (set_of l1)) X;
    (* Does drop_b_reads really need to change the hb? *)
    (* We should be able to drop more than just reads. *)
    drop_l_reads : ptr -> execution -> 
      (list event * witness) -> (list event * witness);
    drop_l_reads_spec : forall l E ops X ops' X'
      (Hdrop : drop_l_reads l E (ops, X) = (ops', X')), lower ops' =
      filter (fun op => match op with MRead p v => negb (beq p l) | _ => true
                        end) (lower ops);
    drop_wf : forall l E ops X ops' X' (Hin : forall e, In e ops -> events E e)
      (Hnodup : NoDup (map id ops))
      (Hdrop : drop_l_reads l E (ops, X) = (ops', X')) (Hwf : well_formed E X),
      well_formed (upd_events E (Union
        (Setminus (events E) (set_of ops)) (set_of ops'))) X';
    drop_ids : forall l E ops X ops' X' (Hnodup : NoDup (map id ops))
      (Hdrop : drop_l_reads l E (ops, X) = (ops', X')), NoDup (map id ops') /\
      forall e, In e ops' -> exists e', In e' ops /\ id e = id e';
    drop_order : forall l E ops X ops' X'
      (Hcont : contained (constraints E) (hb X))
      (Hin : forall e, In e ops -> events E e)
      (Hlin : linearization (set_of ops) (hb X) ops)
      (Hdrop : drop_l_reads l E (ops, X) = (ops', X'))
      (Htrans : transitive_on (hb X) (events E)),
      linearization (set_of ops') (hb X') ops' /\
      contained (constraints E) (hb X') /\
      contained (hb X') (hb X) /\ transitive_on (hb X')
        (Union (Setminus (events E) (set_of ops)) (set_of ops')) /\
      forall i j (Hout : ~In i (map id ops) \/ ~In j (map id ops)),
        hb X i j <-> hb X' i j;
    drop_race_free : forall E X (Hrf : race_free (events E) X) c
      (Hin : events E c)
      l ops' X' (Hdrop : drop_l_reads l E ([c], X) = (ops', X')),
      race_free (Union (Subtract (events E) c) (set_of ops')) X';
    drop_len : forall l E ops X, length (fst (drop_l_reads l E (ops, X))) <=
      length ops;
    drop_rf : forall l E ops (Hin : forall e, In e ops -> events E e) X
      (Hwf : well_formed E X) ops' X'
      (Hdrop : drop_l_reads l E (ops, X) = (ops', X'))
      e1 e2 (He1 : Union (Setminus (events E) (set_of ops)) (set_of ops') e1)
      (He2 : Union (Setminus (events E) (set_of ops)) (set_of ops') e2),
      rf X' (id e1) (id e2) <->
      (rf X (id e1) (id e2) /\ exists p v, reads (op e2) p v);
    private_seq : forall E X ops (Hwf : well_formed E X)
    (Hin : forall e, In e ops -> events E e)
    (* This should be relaxable. *)
    (Htotal : total_on (hb X) (set_of ops)) a z (Ha : In a ops) (Hz : In z ops) 
    (Hbegin : forall e (He : In e ops), e = a \/ hb X (id a) (id e))
    (Hend : forall e (He : In e ops), e = z \/ hb X (id e) (id z))
    l (Hordered : forall e, events E e -> mods (op e) l ->
       hb X (id e) (id a) \/ In e ops \/ hb X (id z) (id e))
(*    (Huniform : forall e i v (He : nth_error ops i = Some e)
       (Hreads : reads (op e) l v), exists w, events E w /\
       mods (op w) l /\ rf X (id w) (id e))*)
    (Hops : linear (hb X) ops)
    ops' X' (Hdrop : drop_l_reads l E (ops, X) = (ops', X')),
    valid E X <-> valid (upd_events E (Union
      (Setminus (events E) (set_of ops)) (set_of ops'))) X' /\
      exists m1, linearization (before (events E) (full (events E) X) a)
        (full (events E) X) m1 /\
      forall i r v (Hr : nth_error ops i = Some r)
        (Hreads : reads (op r) l v),
      match find (fun e => if find_mod (op e) l then true else false)
        (rev (m1 ++ firstn i ops)) with
      | Some w => rf X (id w) (id r) /\
          (exists a, last_op (to_seq (op w)) (Ptr l) a /\ match_op a v) /\
          forall r' v' (Hr' : Union (Setminus (events E) (set_of ops))
            (set_of ops') r') (Hreads' : reads (op r') l v')
            (Hhb : hb X (id w) (id r')), rf X (id w) (id r') \/
            (exists w', events E w' /\ hb X (id w) (id w') /\
                        rf X (id w') (id r'))
      | None => False
      end
  }.

  Context {MM : Memory_Model}.

  Variable (val_eq : EqDec_eq val).

(* Well-synchronized programs *)

  (* up? *)
  Instance mem_op_eq : EqDec_eq mem_op.
  Proof. eq_dec_inst. Qed.

  Definition has_read e :=
    existsb (fun op => negb (not_read op)) (to_seq (op e)).

  Lemma has_read_reads : forall e,
    has_read e = true <-> exists p v, reads (op e) p v.
  Proof.
    intros; unfold has_read, reads.
    rewrite existsb_exists; split; clarify; eauto.
    destruct x; clarify; eauto.
  Qed.

  Corollary reads_has_read : forall e p v, reads (op e) p v ->
    has_read e = true.
  Proof. intros; rewrite has_read_reads; eauto. Qed.

  Lemma in_range_dec : forall i a b, (i < a \/ i >= b) \/ (a <= i < b).
  Proof. intros; omega. Qed.

(*  (* up? *)
  Definition read_init_op (m : ilist mem_op) := forall i p v
    (Hread : inth m i = Some (MRead p v)),
    exists v', last_op (itake i m) (Ptr p) (MWrite p v').
    
  Lemma read_init_alt : forall m, read_init m <-> read_init_op m.
  Proof.
    intro; split; repeat intro.
    - specialize (H i p v); clarify.
      unfold last_op; eexists; eexists; split; eauto.
      generalize (last_mod_lt _ H1); intro.
      generalize (itake_length i m); intro.
      rewrite inth_nth_error, itake_nth; destruct (lt_dec x i); eauto; omega.
    - specialize (H i p v); clarify.
      unfold last_op in *; clarify.
      eexists; eexists; split; eauto.
      rewrite inth_nth_error, itake_nth in *; clarify; eauto.
  Qed.
  (* This is a much better definition. *)

  (* up *)
  Lemma read_init_snoc : forall (m : list mem_op) a (Hread : read_init m),
    read_init (m ++ [a]) <->
      match a with
      | MRead p v => exists v', last_op m (Ptr p) (MWrite p v')
      | _ => True
      end.
  Proof.
    intros; rewrite read_init_alt in *; split; intro.
    - destruct a; clarify.
      specialize (H (length m) p v);
        rewrite inth_nth_error, nth_error_split in H; clarsimp; eauto.
    - repeat intro; specialize (Hread i p v).
      rewrite inth_nth_error, nth_error_app in *.
      destruct (lt_dec i (length m)); clarify.
      + exists x; clarsimp.
        rewrite not_le_minus_0, app_nil_r; clarify; omega.
      + rewrite nth_error_single in *; clarify.
        exists x; clarsimp.
        rewrite firstn_length'; auto; omega.
  Qed.

  (* up *)
  Definition write_alloc_op (m : ilist mem_op) := forall i p v
    (Hwrite : inth m i = Some (MWrite p v)),
    (exists v', last_op (itake i m) (Ptr p) (MWrite p v')) \/
    (exists n, last_op (itake i m) (Ptr p) (MAlloc (fst p) n) /\ snd p < n).
    
  Lemma write_alloc_alt : forall m, write_alloc m <-> write_alloc_op m.
  Proof.
    intro; split; intro Hw; repeat intro.
    - specialize (Hw i p v); clarify.
      generalize (lt_le_trans _ _ _ (last_mod_lt _ Hw1) (itake_length i m)).
      unfold last_op; destruct Hw2; [left | right]; clarify.
      + do 3 eexists; eauto.
        rewrite inth_nth_error, itake_nth; clarify; eauto.
      + do 2 eexists; eauto.
        do 2 eexists; eauto.
        rewrite inth_nth_error, itake_nth; clarify.
    - specialize (Hw i p v); clarify.
      unfold last_op in *; destruct Hw; clarify; do 2 eexists; eauto.
      + rewrite inth_nth_error, itake_nth in *; clarify; eauto.
      + rewrite inth_nth_error, itake_nth in *; clarify; eauto.
  Qed.
  (* This is a much better definition. *)

  (* up *)
  Lemma write_alloc_snoc : forall (m : list mem_op) a (Hwrite : write_alloc m),
    write_alloc (m ++ [a]) <->
      match a with
      | MWrite p v => (exists v', last_op m (Ptr p) (MWrite p v')) \/
          exists n, last_op m (Ptr p) (MAlloc (fst p) n) /\ snd p < n
      | _ => True
      end.
  Proof.
    intros; rewrite write_alloc_alt in *; split; intro.
    - destruct a; clarify.
      specialize (H (length m) p v);
        rewrite inth_nth_error, nth_error_split in H; clarsimp; eauto.
    - repeat intro; specialize (Hwrite i p v).
      rewrite inth_nth_error, nth_error_app in *.
      destruct (lt_dec i (length m)); clarify.
      + destruct Hwrite; [left | right]; clarsimp;
          rewrite not_le_minus_0, app_nil_r; clarify; eauto; omega.
      + rewrite nth_error_single in *; clarify.
        destruct H; [left | right]; clarsimp;
          rewrite firstn_length'; eauto; omega.
  Qed.

  Lemma read_init_drop_b : forall ops b E
    X ops' X' (Hdrop : drop_b_reads b E (ops, X) = (ops', X'))
    m1 m2 (Hread : read_init (iapp m1 (iapp (lower ops) m2))),
    read_init (iapp m1 (iapp (lower ops') m2)).
  Proof.
    intros ???????.
    rewrite (drop_b_reads_spec _ _ _ _ Hdrop).
    induction (lower ops); clarify.
    specialize (IHl (m1 ++ [a]) m2);
      repeat rewrite <- iapp_app in IHl; clarify.
    destruct a; clarsimp.
    eapply read_init_drop; eauto.
  Qed.

  Corollary read_init_drop_b' : forall m1 ops m2 b E X ops' X'
    (Hread : read_init (m1 ++ lower ops ++ m2))
    (Hdrop : drop_b_reads b E (ops, X) = (ops', X')),
    read_init (m1 ++ lower ops' ++ m2).
  Proof.
    intros; repeat rewrite to_ilist_app in *; eapply read_init_drop_b; eauto.
  Qed.

  Lemma write_alloc_drop_b : forall ops b E
    X ops' X' (Hdrop : drop_b_reads b E (ops, X) = (ops', X'))
    m1 m2 (Hwrite : write_alloc (iapp m1 (iapp (lower ops) m2))),
    write_alloc (iapp m1 (iapp (lower ops') m2)).
  Proof.
    intros ???????.
    rewrite (drop_b_reads_spec _ _ _ _ Hdrop).
    induction (lower ops); clarify.
    specialize (IHl (m1 ++ [a]) m2);
      repeat rewrite <- iapp_app in IHl; clarify.
    destruct a; clarsimp.
    eapply write_alloc_drop; eauto.
  Qed.

  Corollary write_alloc_drop_b' : forall m1 ops m2 b E X ops' X'
    (Hwrite : write_alloc (m1 ++ lower ops ++ m2))
    (Hdrop : drop_b_reads b E (ops, X) = (ops', X')),
    write_alloc (m1 ++ lower ops' ++ m2).
  Proof.
    intros; repeat rewrite to_ilist_app in *; eapply write_alloc_drop_b; eauto.
  Qed.*)

  Lemma lower_cons : forall x l, lower (x :: l) = to_seq (op x) ++ lower l.
  Proof. auto. Qed.

  Corollary lower_single : forall x, lower [x] = to_seq (op x).
  Proof. intro; rewrite lower_cons; clarsimp. Qed.

  Lemma drop_reads : forall m1 e m2 E X ops' X' p v (Hread : reads (op e) p v)
    (Hdrop : drop_l_reads p E ([e], X) = (ops', X')),
    length (filter (fun op => negb (not_read op)) (lower (m1 ++ ops' ++ m2))) <
    length (filter (fun op => negb (not_read op)) (lower (m1 ++ e :: m2))).
  Proof.
    intros; repeat rewrite lower_app; rewrite lower_cons.
    repeat rewrite filter_app, app_length.
    apply plus_lt_compat_l, plus_lt_compat_r.
    rewrite (drop_l_reads_spec _ _ _ _ Hdrop), lower_single, filter_comm.
    unfold reads in Hread; exploit in_split; eauto.
    clear; clarsimp; repeat rewrite filter_app; clarify.
    destruct p; unfold negb at 3; clarify.
    repeat rewrite app_length; apply plus_le_lt_compat; [apply filter_length|].
    simpl; eapply le_lt_trans; [apply filter_length | auto].
  Qed.

  (* up *)
  Lemma op_modifies_spec : forall a p, op_modifies a p = true <->
    ~independent (loc_of a) (Ptr p) /\ not_read a = true.
  Proof.
    destruct a; split; clarify.
  Qed.

  Lemma mods_touches : forall c p, mods c p -> touches c p.
  Proof.
    unfold mods, touches; clarify.
    rewrite op_modifies_spec in *; clarify; eauto.
  Qed.

  Lemma reads_touches : forall c p v, reads c p v -> touches c p.
  Proof.
    unfold reads, touches; clarify; eauto.
  Qed.

  Corollary race_free_mods_read : forall E X a b p v (Hrf : race_free E X)
    (Ha : E a) (Hb : E b) (Hmods : mods (op a) p) (Hread : reads (op b) p v),
    hb X (id a) (id b) \/ a = b \/ hb X (id b) (id a).
  Proof.
    intros; eapply Hrf; eauto; [apply mods_touches | eapply reads_touches];
      eauto.
  Qed.

  Corollary race_free_mods_mods : forall E X a b p (Hrf : race_free E X)
    (Ha : E a) (Hb : E b) (Hmods : mods (op a) p) (Hread : mods (op b) p),
    hb X (id a) (id b) \/ a = b \/ hb X (id b) (id a).
  Proof.
    intros; eapply Hrf; eauto; apply mods_touches; auto.
  Qed.

  Lemma lin_single : forall R x (Hirrefl : ~R (id x) (id x)), linear R [x].
  Proof.
    repeat split; clarify.
    constructor; auto.
  Qed.

  Lemma lin_irrefl : forall E R l
    (Hlin : linearization E R l) e (He : E e), ~R (id e) (id e).
  Proof.
    repeat intro.
    generalize (lin_nodup Hlin); intro.
    unfold linearization in *; clarify.
    specialize (Hlin22 e e); clarify.
    exploit NoDup_inj.
    { eauto. }
    { apply Hlin221. }
    { apply Hlin2221. }
    omega.
  Qed.

  Lemma private_seq_1 : forall E X a (Hwf : well_formed E X) (Hin : events E a) 
    l (Hordered : forall e, events E e -> mods (op e) l ->
       hb X (id e) (id a) \/ e = a \/ hb X (id a) (id e))
    ops' X' (Hdrop : drop_l_reads l E ([a], X) = (ops', X')),
    valid E X <->
    valid (upd_events E (Union (Subtract (events E) a) (set_of ops'))) X' /\
      exists m1, linearization (before (events E) (full (events E) X) a)
             (full (events E) X) m1 /\
      forall v (Hreads : reads (op a) l v),
      match find (fun e => if find_mod (op e) l then true else false)
        (rev m1) with
      | Some w => rf X (id w) (id a) /\
          (exists a, last_op (to_seq (op w)) (Ptr l) a /\ match_op a v) /\
          forall r' v' (Hr' : Union (Subtract (events E) a) (set_of ops') r')
            (Hreads : reads (op r') l v') (Hhb : hb X (id w) (id r')),
            rf X (id w) (id r') \/ exists w', events E w' /\
            hb X (id w) (id w') /\ rf X (id w') (id r')
      | None => False
      end.
  Proof.
    intros; rewrite (private_seq(ops := [a]) _ _); eauto; try solve [clarify].
    rewrite set_of_single; split; intro Hvalid; clarify.
    - do 2 eexists; eauto; clarify.
      specialize (Hvalid22 0); simpl in Hvalid22; exploit Hvalid22; eauto.
      rewrite app_nil_r; auto.
    - do 2 eexists; eauto; clarsimp.
      apply Hvalid22; auto.
    - repeat intro; clarify.
    - intros; exploit Hordered; eauto; clarify.
    - apply lin_single; auto.
      exploit wf_full; eauto; clarify.
      exploit full_lin; eauto; clarify.
      eapply lin_irrefl; eauto.
  Qed.

  (* up *)
  Lemma last_single : forall (a : mem_op) l a', last_op (icons a inil) l a' <->
    a' = a /\ ~independent (block_model.loc_of a) l /\ not_read a = true.
  Proof.
    split; clarify.
    - destruct H as (? & Hlast & ?).
      destruct x; clarsimp.
      inversion Hlast; clarify.
    - exists 0; clarify.
      econstructor; simpl; eauto 2; clarify.
      destruct j; clarsimp.
  Qed.

  (* up *)
  Lemma firstn_in : forall A (x : A) n l, In x (firstn n l) -> In x l.
  Proof.
    intros.
    exploit in_nth_error; eauto; clarify.
    rewrite nth_error_firstn in *; clarify.
    eapply nth_error_in; eauto.
  Qed.

  (* up *)
  Fixpoint find_before A (f g : A -> bool) l :=
    match l with
    | [] => None
    | a :: rest => if f a then Some a else if g a then None
                   else find_before f g rest
    end.

  Lemma find_before_spec : forall A (f g : A -> bool) l x,
    find_before f g l = Some x <-> exists i, nth_error l i = Some x /\
      f x = true /\ forall j y, j < i -> nth_error l j = Some y ->
                                f y = false /\ g y = false.
  Proof.
    induction l; clarify.
    { split; clarsimp. }
    destruct (f a) eqn: Hf; [|destruct (g a) eqn: Hg].
    - split; intro Hfind; clarify.
      + exists 0; clarify; omega.
      + specialize (Hfind22 0 a); destruct x0; clarify.
    - split; intro Hfind; clarify.
      specialize (Hfind22 0 a); destruct x0; clarify.
    - rewrite IHl; split; intro Hfind; clarify.
      + exists (S x0); clarify.
        destruct j; clarify.
        eapply Hfind22; eauto; omega.
      + destruct x0; clarify.
        exists x0; clarify.
        eapply (Hfind22 (S j)); eauto.
  Qed.

  Lemma find_before_fail : forall A (f g : A -> bool) l,
    find_before f g l = None <-> forall i x, nth_error l i = Some x ->
      f x = true -> exists j y, j < i /\ nth_error l j = Some y /\ g y = true.
  Proof.
    induction l; clarify.
    { split; clarsimp. }
    destruct (f a) eqn: Hf; [|destruct (g a) eqn: Hg].
    - split; intro Hfind; clarify.
      specialize (Hfind 0 a); clarify; omega.
    - split; intro Hfind; clarify.
      destruct i; clarify.
      exists 0, a; clarify.
    - rewrite IHl; split; intro Hfind; clarify.
      + destruct i; clarify.
        exploit Hfind; eauto; intros (j & y & ?).
        exists (S j), y; clarify.
      + specialize (Hfind (S i) x); clarify.
        destruct x0; clarify.
        repeat eexists; try apply Hfind21; auto; omega.
  Qed.
      
  Lemma last_op_in : forall (m : list mem_op) l a (Hlast : last_op m l a),
    In a m.
  Proof.
    intros ??? (i & ?); clarsimp.
    eapply nth_error_in; eauto.
  Qed.

  Lemma last_mod_mods : forall (m : ilist mem_op) p i
    (Hlast : last_mod_op m (Ptr p) i),
    exists a, inth m i = Some a /\ op_modifies a p = true.
  Proof.
    intros; inversion Hlast; do 2 eexists; eauto 2.
    destruct op0; clarify.
  Qed.

  Lemma last_op_mods : forall (m : ilist mem_op) p a
    (Hlast : last_op m (Ptr p) a), op_modifies a p = true.
  Proof.
    intros ??? (i & Hlast & Ha).
    exploit last_mod_mods; eauto; clarsimp.
  Qed.

  Lemma last_mods : forall c p a (Hlast : last_op (to_seq c) (Ptr p) a),
    mods c p.
  Proof.
    intros; eexists; split; [eapply last_op_in | eapply last_op_mods]; eauto.
  Qed.

  Lemma begin_trans : forall E X a ops e e'
    (Htrans : transitive_on (hb X) (events E))
    (Hin : forall e, In e ops -> events E e) (Ha : In a ops)
    (Hbegin : forall e (He : In e ops), e = a \/ hb X (id a) (id e))
    (He : events E e) (Hbefore : hb X (id e) (id a)) (He' : In e' ops),
      hb X (id e) (id e').
  Proof.
    intros.
    specialize (Hbegin e'); clarify.
    apply (Htrans _ a); auto.
  Qed.    

  Lemma end_trans : forall E X z ops e e'
    (Htrans : transitive_on (hb X) (events E))
    (Hin : forall e, In e ops -> events E e) (Ha : In z ops)
    (Hend : forall e (He : In e ops), e = z \/ hb X (id e) (id z))
    (He : events E e) (Hafter : hb X (id z) (id e)) (He' : In e' ops),
      hb X (id e') (id e).
  Proof.
    intros.
    specialize (Hend e'); clarify.
    apply (Htrans _ z); auto.
  Qed. 

  Lemma b_not_read_spec : forall b m, filter (b_not_read b) m =
    filter not_read (proj_block m b).
  Proof.
    intros; setoid_rewrite filter_filter; apply filter_ext.
    rewrite Forall_forall; auto.
  Qed.

  Lemma NoDup_middle : forall A (l1 l2 l3 : list A) (HNoDup : NoDup (l1 ++ l3))
    (Hl2 : NoDup l2) (Hdistinct : forall x, In x l2 -> ~In x (l1 ++ l3)),
    NoDup (l1 ++ l2 ++ l3).
  Proof.
    intros.
    repeat rewrite NoDup_app in *; clarify.
    split; clarify.
    - specialize (Hdistinct x); rewrite in_app in *; intro; clarify.
    - specialize (HNoDup22 x); rewrite in_app; intro; clarify.
      specialize (Hdistinct x); rewrite in_app in *; clarify.
  Qed.

  Lemma NoDup_app_in : forall A (l1 l2 : list A) x (HNoDup : NoDup (l1 ++ l2)),
    ~(In x l1 /\ In x l2).
  Proof.
    repeat intro; clarify.
    generalize (in_split _ _ H1); clarsimp.
    generalize (NoDup_remove_2 _ _ _ HNoDup); repeat rewrite in_app; clarify.
  Qed.

  Lemma lin_order : forall E R l1 l2 a b (Hlin : linearization E R (l1 ++ l2))
    (Ha : In a l1) (Hb : In b l2), ~R (id b) (id a).
  Proof.
    intros.
    generalize (lin_nodup Hlin); intro Hnodup.
    unfold linearization in *; clarify.
    intro; specialize (Hlin22 b a).
    rewrite Hlin1 in Hlin22.
    rewrite Hlin1, in_app, in_app in Hlin22; clarify.
    generalize (NoDup_app_in l1 l2 a Hnodup), (NoDup_app_in l1 l2 b Hnodup);
      intros.
    rewrite nth_error_app in *; destruct (lt_dec x (length l1)).
    - generalize (nth_error_in _ _ Hlin221); auto.
    - destruct (lt_dec x0 (length l1)); try omega.
      generalize (nth_error_in _ _ Hlin2221); auto.
  Qed.

  Lemma mods_before : forall E X m1 e m2 e'
    (Hlin : linearization (events E) (hb X) (m1 ++ e :: m2))
    (Hnodup : NoDup (m1 ++ e :: m2))
    (Hord : hb X (id e') (id e) \/ e' = e \/ hb X (id e) (id e'))
    (Hin' : events E e'),
    In e' m1 <-> hb X (id e') (hd default (map id [e])).
  Proof.
    intros.
    split; intro Hin.
    - generalize (lin_order _ _ _ e Hlin Hin); clarify.
      generalize (NoDup_remove_2 _ _ _ Hnodup); rewrite in_app; intro Hout.
      contradiction Hout; auto.
    - unfold linearization in *; clarify.
      specialize (Hlin22 e' e); clarify.
      rewrite Hlin1, in_app in Hlin22; clarify.
      generalize (NoDup_inj _ _ Hnodup Hlin2221 (nth_error_split _ _ _));
        clarify.
      rewrite nth_error_app in Hlin221; clarify.
      eapply nth_error_in; eauto.    
  Qed.

  Lemma lin_app : forall E R l1 l2 (Hlin : linearization E R (l1 ++ l2)),
    linearization (set_of l1) R l1.
  Proof.
    intros; generalize (lin_nodup Hlin); intro Hnodup.
    unfold linearization in Hlin; clarify; split; [|split].
    - reflexivity.
    - rewrite map_app, NoDup_app in *; clarify.
    - intros ?? He1 He2 ?.
      specialize (Hlin22 e1 e2); repeat rewrite Hlin1, in_app in Hlin22;
        clarify.
      generalize (in_nth_error _ _ He1), (in_nth_error _ _ He2);
        intros (i1 & ? & Hi1) (i2 & ? & Hi2).
      generalize (NoDup_inj _ i1 Hnodup Hlin221),
        (NoDup_inj _ i2 Hnodup Hlin2221); repeat rewrite nth_error_app; clarify;
        eauto.
  Qed.

  Lemma lift_last : forall (ops : list event) p a
    (Hlast : last_op (lower ops) (Ptr p) a),
    exists i w, nth_error ops i = Some w /\ last_op (to_seq (op w)) (Ptr p) a /\
      forall i2 w2, nth_error ops i2 = Some w2 -> mods (op w2) p -> i2 <= i.
  Proof.
    intros.
    assert (exists i, last_mod_op (lower ops) (Ptr p) i /\
      inth (lower ops) i = Some a) as (i & Hlast_mod & Hnth) by eauto.
    inversion Hlast_mod; setoid_rewrite Hop1 in Hnth; clarify.
    rewrite inth_nth_error in Hop1; exploit nth_lower_split; eauto;
      intros (ops1 & c & ops2 & i' & ? & Hi' & ?); clarify.
    exists (length ops1); rewrite nth_error_split; do 2 eexists; eauto.
    rewrite lower_app, lower_cons in Hlast.
    repeat setoid_rewrite last_op_app in Hlast.
    destruct Hlast as [[Hlast | Hlast] | Hlast].
    - destruct Hlast as (i2 & Hi2).
      specialize (Hlast0 (length (lower ops1) + (length (to_seq (op c)) + i2))).
      rewrite inth_nth_error, lower_app, lower_cons in Hlast0.
      repeat rewrite nth_error_plus in Hlast0; specialize (Hlast0 a); clarsimp.
      generalize (nth_error_lt _ _ Hi'); intro; exfalso; omega.
    - split; [clarify | intros i2 w2 Hw2 Hmods2].
      rewrite nth_error_app in *; destruct (lt_dec i2 (length ops1)); [omega|].
      destruct (i2 - length ops1) eqn: Hminus; [omega | clarify].
      exploit nth_error_split'; eauto; clarify.
      destruct Hmods2 as (a2 & Ha2 & ?).
      generalize (in_nth_error _ _ Ha2); intros (i2' & ?).
      specialize (Hlast0 (length (lower ops1) + (length (to_seq (op c)) +
        (length (lower x) + i2')))).
      rewrite inth_nth_error in Hlast0; repeat rewrite lower_app in Hlast0.
      rewrite nth_error_plus, lower_cons, nth_error_plus in Hlast0.
      setoid_rewrite lower_app in Hlast0; rewrite nth_error_plus in Hlast0.
      setoid_rewrite lower_cons in Hlast0; rewrite nth_error_app in Hlast0.
      exploit nth_error_lt; eauto; clarify.
      specialize (Hlast0 a2); clarify.
      rewrite <- NPeano.Nat.add_le_mono_l in Hlast0.
      assert (i' < length (to_seq (op c)) + (length (lower x) + i2')) as Hlt.
      { generalize (nth_error_lt _ _ Hi'); intro.
        eapply lt_le_trans; [eauto | apply le_plus_l]. }
      generalize (lt_not_le _ _ Hlt); intro.
      destruct a2; clarify.
    - rewrite Forall_app in *; clarify.
      generalize (nth_error_in _ _ Hi'); intro.
      rewrite Forall_forall in Hlast21; specialize (Hlast21 a); clarify.
  Qed.
 
  (* up *)
  Lemma op_modifies_block : forall (a : mem_op) b o,
    op_modifies a (b, o) = true -> block_of a = b.
  Proof. destruct a; clarify. Qed.

  Lemma NoDup_id_inj : forall l (e1 e2 : event) (Hids : NoDup (map id l))
    (He1 : In e1 l) (He2 : In e2 l) (Heq : id e1 = id e2), e1 = e2.
  Proof.
    intros.
    exploit in_split; eauto; clarify.
    rewrite map_app in Hids; clarify.
    generalize (NoDup_remove_2 _ _ _ Hids); rewrite in_app in *; intro H.
    destruct He1; clarify; contradiction H; repeat rewrite in_map_iff; eauto.
  Qed.

  Lemma lin_order_1 : forall E R l (Hlin : linearization E R l)
    i1 e1 e2 (He1 : nth_error l i1 = Some e1) (He2 : E e2)
    (HR : R (id e1) (id e2)),
    exists i2, nth_error l i2 = Some e2 /\ i1 < i2.
  Proof.
    intros; generalize (lin_nodup Hlin); intro Hnodup.
    unfold linearization in Hlin; clarify.
    exploit nth_error_in; eauto; intro.
    rewrite <- Hlin1 in *; specialize (Hlin22 e1 e2); clarify.
    generalize (NoDup_inj _ _ Hnodup Hlin221 He1); clarify; eauto.
  Qed.

  Lemma lin_order_2 : forall E R l (Hlin : linearization E R l)
    e1 i2 e2 (He1 : E e1) (He2 : nth_error l i2 = Some e2)
    (HR : R (id e1) (id e2)),
    exists i1, nth_error l i1 = Some e1 /\ i1 < i2.
    intros; generalize (lin_nodup Hlin); intro Hnodup.
    unfold linearization in Hlin; clarify.
    exploit nth_error_in; eauto; intro.
    rewrite <- Hlin1 in *; specialize (Hlin22 e1 e2); clarify.
    generalize (NoDup_inj _ _ Hnodup Hlin2221 He2); clarify; eauto.
  Qed.

  Lemma lin_order_3 : forall E R l (Hlin : linearization E R l)
    i1 e1 i2 e2 (He1 : nth_error l i1 = Some e1)
    (He2 : nth_error l i2 = Some e2) (HR : R (id e1) (id e2)), i1 < i2.
    intros; generalize (lin_nodup Hlin); intro Hnodup.
    unfold linearization in Hlin; clarify.
    generalize (nth_error_in _ _ He1), (nth_error_in _ _ He2); intros.
    rewrite <- Hlin1 in *; specialize (Hlin22 e1 e2); clarify.
    generalize (NoDup_inj _ _ Hnodup Hlin221 He1); clarify.
    generalize (NoDup_inj _ _ Hnodup Hlin2221 He2); clarify.
  Qed.

  Lemma race_free_lin : forall E X l (Hrf : race_free E X)
    (Hlin : linearization E (hb X) l) e1 e2 i1 i2
    (Hi1 : nth_error l i1 = Some e1) (Hi2 : nth_error l i2 = Some e2)
    (Hlt : i1 < i2) p (He1 : touches (op e1) p) (He2 : touches (op e2) p)
    (Hmods : mods (op e1) p \/ mods (op e2) p),
    hb X (id e1) (id e2).
  Proof.
    intros.
    specialize (Hrf e1 e2 p).
    generalize (nth_error_in _ _ Hi1), (nth_error_in _ _ Hi2); intros.
    generalize (lin_nodup Hlin); intro Hnodup.
    unfold linearization in Hlin; clarify.
    rewrite <- Hlin1 in *; clarify.
    destruct Hrf; clarify.
    - generalize (NoDup_inj _ _ Hnodup Hi1 Hi2); omega.
    - specialize (Hlin22 e2 e1); clarify.
      generalize (NoDup_inj _ _ Hnodup Hi1 Hlin2221),
        (NoDup_inj _ _ Hnodup Hi2 Hlin221); clarify; omega.
  Qed.

  Lemma race_free_same_last : forall E X (Hrf : race_free E X)
    l1 r l2 (Hlin : linearization E (hb X) (l1 ++ r :: l2))
    p v (Hreads : reads (op r) p v) a (Hlast : last_op (lower l1) (Ptr p) a)
    l1' l2' (Hlin' : linearization E (hb X) (l1' ++ r :: l2')),
    last_op (lower l1') (Ptr p) a.
  Proof.
    intros.
    generalize (lin_nodup Hlin); intro Hnodup.
    exploit lift_last; eauto; intros (i & w & Hw); clarify.
    exploit last_op_mods; eauto; intro.
    assert (E r) as Hr.
    { rewrite (lin_set Hlin), in_app; clarify. }
    assert (E w) as Hw.
    { rewrite (lin_set Hlin), in_app; left; eapply nth_error_in; eauto. }
    exploit last_op_in; eauto; intro.
    assert (mods (op w) p) as Hmods by (unfold mods; eauto).
    generalize (nth_error_lt _ _ Hw1); intro.
    exploit (race_free_lin Hrf Hlin).
    { instantiate (2 := i); rewrite nth_error_app; clarify; eauto. }
    { apply nth_error_split. }
    { auto. }
    { eapply mods_touches; eauto. }
    { eapply reads_touches; eauto. }
    { auto. }
    intro Hhb.
    generalize (lin_nodup Hlin'); intro Hnodup'.
    exploit lin_order_2; eauto.
    { apply nth_error_split. }
    intros (i' & Hi' & ?); rewrite nth_error_app in Hi'; clarify.
    exploit nth_error_split'; eauto; intros (m1 & m2 & ?); clarify.
    rewrite lower_app; setoid_rewrite last_op_app; left.
    rewrite lower_cons; setoid_rewrite last_op_app; right; clarify.
    rewrite Forall_forall; intros.
    destruct (op_modifies x p) eqn: Hmods2.
    - assert (exists w2, E w2 /\ mods (op w2) p /\
        hb X (id w) (id w2) /\ hb X (id w2) (id r)) as (w2 & Hw2).
      { exploit in_nth_error; eauto; clarify.
        exploit nth_lower_split; eauto; intros (m1' & w2 & m2' & i2' & ? &
          Hi2' & ?).
        exists w2; clarify.
        rewrite lin_set; eauto.
        split.
        { repeat (rewrite in_app; clarify).
          left; clarify. }
        generalize (nth_error_in _ _ Hi2'); intro.
        assert (mods (op w2) p) by (unfold mods; eauto); clarify.
        split; eapply (race_free_lin Hrf Hlin').
        + rewrite <- app_assoc; simpl; apply nth_error_split.
        + instantiate (1 := length m1 + S (length m1')).
          rewrite <- app_assoc; simpl.
          rewrite nth_error_plus; simpl.
          rewrite <- app_assoc; simpl; apply nth_error_split.
        + omega.
        + eapply mods_touches; eauto.
        + eapply mods_touches; eauto.
        + auto.
        + instantiate (1 := length m1 + S (length m1')).
          rewrite <- app_assoc; simpl.
          rewrite nth_error_plus; simpl.
          rewrite <- app_assoc; simpl; apply nth_error_split.
        + apply nth_error_split.
        + repeat (rewrite app_length; simpl); omega.
        + eapply mods_touches; eauto.
        + eapply reads_touches; eauto.
        + eauto. }
      rewrite (lin_set Hlin) in Hw2; clarify.
      exploit in_nth_error; eauto; intros (? & ? & Hw2).
      clear Hlin'; exploit (lin_order_3 Hlin _ _ Hw2 (nth_error_split _ _ _));
        clarify.
      exploit (lin_order_3 Hlin).
      { instantiate (2 := i); rewrite nth_error_app; clarify; eauto. }
      { eauto. }
      { auto. }
      rewrite nth_error_app in Hw2; clarify.
      specialize (Hw22 _ _ Hw2); clarify; omega.
    - destruct x; clarify.
  Qed.

  Lemma lin_id_inj : forall E R l e1 e2
    (Hlin : linearization E R l) (He1 : E e1) (He2 : E e2)
    (Hid : id e1 = id e2), e1 = e2.
  Proof.
    unfold linearization; clarify.
    rewrite Hlin1 in *; eapply NoDup_id_inj; eauto.
  Qed.

  Lemma lin_nil : forall E R, linearization E R [] <-> forall e, ~E e.
  Proof.
    unfold linearization; split; clarify.
    - rewrite H1; auto.
    - split; clarify.
      + specialize (H e); split; clarify.
      + specialize (H e1); clarify.
  Qed.

  Lemma lin_reorder : forall E R l1 l2 e
    (Hlin : linearization E R (l1 ++ l2 ++ [e]))
    (Hl2 : forall e', In e' l2 -> ~R (id e') (id e)),
    linearization E R (l1 ++ e :: l2).
  Proof.
    intros.
    rewrite app_assoc in Hlin; exploit lin_remove; eauto; intros (? & Hlin').
    rewrite app_nil_r in Hlin'.
    exploit (lin_add _ e _ Hlin'); auto.
    - unfold linearization in Hlin; clarify.
      rewrite map_app, NoDup_app in Hlin21; clarify.
      intro Hin; specialize (Hlin2122 _ Hin); clarify.
    - apply (lin_irrefl Hlin); auto.
    - repeat intro.
      generalize (lin_nodup Hlin); intro Hnodup.
      unfold linearization in Hlin; clarify.
      specialize (Hlin22 e e'); clarify.
      rewrite Hlin1, in_app, in_app in Hlin22; clarify.
      generalize (NoDup_inj _ (length (l1 ++ l2)) Hnodup Hlin221);
        rewrite nth_error_split; clarify.
      exploit in_nth_error; eauto; intros (i & ? & ?).
      generalize (NoDup_inj _ i Hnodup Hlin2221);
        rewrite <- app_assoc, nth_error_app; clarify.
      rewrite app_length in *; omega.
    - assert (Add (Subtract E e) e = E) as Heq; [|rewrite Heq; auto].
      apply set_ext; intro; rewrite Add_spec, Subtract_spec; split; clarify.
      destruct (eq_dec (id e0) (id e)).
      + right; apply (lin_id_inj _ _ Hlin); auto.
      + left; clarify; intro; clarify.
  Qed.

  Hypothesis hb_dec : forall E X l (Hlin : linearization E (hb X) l)
    i1 i2 (Hi1 : In i1 (map id l)) (He2 : In i2 (map id l)),
    {hb X i1 i2} + {~hb X i1 i2}.

  Lemma before_lin : forall l (E : Ensemble event) R e
    (HR_dec : forall e1 e2 (He1 : E e1) (He2 : E e2),
                R (id e1) (id e2) \/ ~R (id e1) (id e2))
    (Hlin : linearization E R l) (He : E e) (Htrans : transitive_on R E),
    exists l1 l2, linearization (before E R e) R l1 /\
      linearization E R (l1 ++ e :: l2).
  Proof.
    induction l; clarify.
    { rewrite lin_nil in Hlin; specialize (Hlin e); clarify. }
    exploit lin_cons_inv'; eauto; intros (Hlin0 & Hid & HR).
    assert (forall e, E e -> ~R (id e) (id a)) as Hfree.
    { intros e' He' ?.
      assert (In e' (a :: l)) as Hin by (rewrite <- (lin_set Hlin); auto).
      simpl in Hin; destruct Hin; subst.
      + exploit (lin_irrefl Hlin); eauto.
      + exploit HR; eauto. }
    assert (E a) by (rewrite lin_set; eauto; clarify).
    destruct (eq_dec (id a) (id e)).
    - generalize (lin_id_inj a e Hlin); clarify.
      exists [], l; clarify.
      rewrite lin_nil; unfold before; intros e' (He' & ?).
      exploit Hfree; eauto.
    - specialize (IHl (Subtract E a) R e); clarify.
      repeat setoid_rewrite Subtract_spec in IHl; use IHl; use IHl; use IHl;
        [|intro; clarify].
      use IHl; [|eapply transitive_on_sub, sub_sub; auto].
      destruct IHl as (l1 & l2 & Hbefore & Hlin').
      generalize (lin_nodup Hlin); intro Hnodup; inversion Hnodup; clarify.
      specialize (HR_dec a e); clarify; destruct HR_dec.
      + exists (a :: l1), l2; split.
        * assert (before E R e = Add (before (Subtract E a) R e) a) as Heq.
          { apply Extensionality_Ensembles; split; repeat intro;
              unfold before, Ensembles.In in *; rewrite Add_spec in *; clarify;
              rewrite Subtract_spec in *; clarify.
            destruct (eq_dec (id x) (id a));
              [right; apply (lin_id_inj _ _ Hlin); eauto |
               left; clarify; intro; clarify]. }
          rewrite Heq; apply lin_cons; auto.
          { unfold linearization in Hbefore; rewrite in_map_iff; intro; clarify.
            rewrite <- Hbefore1 in *; unfold before in *; clarify.
            rewrite Subtract_spec in *; clarify.
            exploit (lin_id_inj a x Hlin); eauto. }
          { unfold before; clarify.
            rewrite Subtract_spec in *; clarify. }
        * assert (E = Add (Subtract E a) a) as Heq.
          { apply Extensionality_Ensembles; split; repeat intro;
              unfold Ensembles.In in *; rewrite Add_spec in *; clarify;
              rewrite Subtract_spec in *; clarify.
            destruct (eq_dec (id x) (id a));
              [right; apply (lin_id_inj _ _ Hlin); eauto |
               left; clarify; intro; clarify]. }
          rewrite Heq; apply lin_cons; auto.
          { unfold linearization in Hlin'; rewrite in_map_iff; intro; clarify.
            rewrite <- Hlin'1, Subtract_spec in *; clarify.
            exploit (lin_id_inj a x Hlin); eauto. }
          { repeat intro.
            rewrite Subtract_spec in *; clarify.
            eapply Hfree; eauto. }
      + exists l1, (a :: l2); split.
        * assert (before E R e = before (Subtract E a) R e) as Heq;
            [|rewrite Heq; auto].
          apply Extensionality_Ensembles; split; repeat intro;
            unfold before, Ensembles.In in *; clarify;
            rewrite Subtract_spec in *; clarify.
          intro; clarify.
        * assert (E = Add (Subtract E a) a) as Heq.
          { apply Extensionality_Ensembles; split; repeat intro;
              unfold Ensembles.In in *; rewrite Add_spec in *; clarify;
              rewrite Subtract_spec in *; clarify.
            destruct (eq_dec (id x) (id a));
              [right; apply (lin_id_inj _ _ Hlin); eauto |
               left; clarify; intro; clarify]. }
          rewrite Heq, split_app; apply lin_add; try rewrite <- split_app;
            clear Heq; clarify.
          { rewrite in_map_iff; unfold linearization in Hlin'; intro; clarify.
            rewrite <- Hlin'1, Subtract_spec in *; clarify.
            exploit (lin_id_inj a x Hlin); eauto. }
          { rewrite in_app in *; intro; clarify.
            unfold linearization in Hbefore; clarify.
            rewrite <- Hbefore1 in *; unfold before in *; clarify.
            rewrite Subtract_spec in *; clarify.
            specialize (Htrans a e' e); clarify. }
          { apply Hfree.
            assert (Subtract E a e'); [|rewrite Subtract_spec in *; clarify].
            unfold linearization in Hlin'; clarify.
            rewrite Hlin'1, in_app; clarify. }
  Qed.

  Corollary before_lin_hb : forall l E X e
    (Hlin : linearization E (hb X) l) (He : E e)
    (Htrans : transitive_on (hb X) E),
    exists l1 l2, linearization (before E (hb X) e) (hb X) l1 /\
      linearization E (hb X) (l1 ++ e :: l2).
  Proof.
    intros; eapply before_lin; eauto; intros.
    specialize (hb_dec _ Hlin (id e1) (id e2)).
    rewrite (lin_set Hlin) in *.
    do 2 (use hb_dec; [|rewrite in_map_iff; eauto]).
    destruct hb_dec; auto.
  Qed.

  Lemma not_read_mods : forall a, not_read a = true ->
    exists p, op_modifies a p = true.
  Proof.
    destruct a; clarify.
    - exists p; clarify.
    - exists (b, 0); clarify.
    - exists (b, 0); clarify.
  Qed.

  Lemma lin_e_eq : forall E R l (Hlin : linearization E R l)
    e1 e2 (He1 : E e1) (He2 : E e2), e1 = e2 \/ e1 <> e2.
  Proof.
    intros; destruct (eq_dec (id e1) (id e2)).
    - left; eapply lin_id_inj; eauto.
    - right; intro; clarify.
  Qed.

  Lemma lin_combine : forall R l2 E2 (Hlin2 : linearization E2 R l2) l1 E1
    (Hlin1 : linearization E1 R l1)
    (Hdisjoint : forall i, In i (map id l1) -> ~In i (map id l2))
    (Hafter : forall i1 i2, In i1 (map id l1) -> In i2 (map id l2) ->
       ~R i2 i1), linearization (Union E1 E2) R (l1 ++ l2).
  Proof.
    induction l1; clarify.
    { rewrite lin_nil in Hlin1.
      assert (Union E1 E2 = E2) as Heq; [|rewrite Heq; auto].
      apply set_ext; intro; rewrite Union_spec; split; clarify.
      exploit Hlin1; eauto; clarify. }
    exploit lin_cons_inv; eauto; intro Hl1'.
    specialize (IHl1 _ Hl1'); use IHl1.
    use IHl1.
    assert (E1 a) by (rewrite (lin_set Hlin1); clarify).
    exploit lin_cons; eauto.
    { instantiate (1 := a); rewrite map_app, in_app; intros [? | ?].
      - unfold linearization in Hlin1; clarify.
        inversion Hlin121; clarify.
      - exploit Hdisjoint; eauto. }
    { intros ? He; rewrite Union_spec, Subtract_spec in He; destruct He.
      - generalize (lin_nodup Hlin1); intro Hnodup.
        unfold linearization in Hlin1; clarify.
        intro; specialize (Hlin122 e a); clarify.
        generalize (NoDup_inj _ 0 Hnodup Hlin12221); clarify; omega.
      - apply Hafter; auto.
        rewrite (lin_set Hlin2) in *; rewrite in_map_iff; eauto. }
    { apply (lin_irrefl Hlin1); auto. }
    assert (Add (Union (Subtract E1 a) E2) a = Union E1 E2) as Heq;
      [|rewrite Heq; auto].
    apply set_ext; intro; rewrite Add_spec, Union_spec, Subtract_spec,
      Union_spec; split; clarify.
    destruct (lin_e_eq Hlin1 e a); auto.
  Qed.

  Lemma lin_app2 : forall E R l1 l2 (Hlin : linearization E R (l1 ++ l2)),
    linearization (set_of l2) R l2.
  Proof.
    intros; generalize (lin_nodup Hlin); intro Hnodup.
    unfold linearization in Hlin; clarify; split; [|split].
    - reflexivity.
    - rewrite map_app, NoDup_app in *; clarify.
    - intros ?? He1 He2 ?.
      specialize (Hlin22 e1 e2); repeat rewrite Hlin1, in_app in Hlin22;
        clarify.
      generalize (in_nth_error _ _ He1), (in_nth_error _ _ He2);
        intros (i1 & ? & Hi1) (i2 & ? & Hi2).
      generalize (NoDup_inj _ (length l1 + i1) Hnodup Hlin221),
        (NoDup_inj _ (length l1 + i2) Hnodup Hlin2221);
        repeat rewrite nth_error_plus; clarify.
      exists i1, i2; clarify; omega.
  Qed.

  Lemma lin_filter : forall R f l E (Hlin : linearization E R l),
    linear R (filter f l).
  Proof.
    induction l; clarify.
    { rewrite lin_nil in *; auto. }
    destruct (f a) eqn: Ha.
    - exploit lin_cons_inv'; eauto; intros (Hlin' & Hid & HR).
      rewrite set_of_cons; apply lin_cons; eauto.
      + rewrite in_map_iff; intro; clarify.
        rewrite filter_In in *; clarify.
        unfold linearization in Hlin; clarify.
        inversion Hlin21; clarify.
        rewrite in_map_iff in *; eauto.
      + unfold set_of; repeat intro; rewrite filter_In in *; clarify.
        exploit HR; eauto.
      + apply (lin_irrefl Hlin); auto.
        rewrite (lin_set Hlin); clarify.
    - eapply IHl; eapply lin_cons_inv; eauto.
  Qed.

  Lemma lin_split : forall E R l1 l2 (Hlin : linearization E R (l1 ++ l2))
    e1 e2 (He1 : In e1 l1) (He2 : In e2 l2), ~R (id e2) (id e1).
  Proof.
    repeat intro.
    generalize (lin_nodup Hlin); intro Hnodup.
    unfold linearization in Hlin; clarify.
    specialize (Hlin22 e2 e1); repeat rewrite Hlin1, in_app in Hlin22; clarify.
    generalize (in_nth_error _ _ He1), (in_nth_error _ _ He2);
      intros (i1 & ? & Hi1) (i2 & ? & Hi2).
    generalize (NoDup_inj _ (length l1 + i2) Hnodup Hlin221),
      (NoDup_inj _ i1 Hnodup Hlin2221);
      rewrite nth_error_plus, nth_error_app; clarify; omega.
  Qed.

  Lemma transitive_on_sub' : forall (E E' : Ensemble event) R
    (Htrans : transitive_on R E)
    (Hsub : forall e (He : E' e), exists e', E e' /\ id e = id e'),
    transitive_on R E'.
  Proof.
    repeat intro.
    generalize (Hsub _ He1), (Hsub _ He2), (Hsub _ He3);
      intros (? & ? & Hid1) (e2' & ? & Hid2) (? & ? & Hid3).
    rewrite Hid1, Hid2, Hid3 in *.
    apply (Htrans _ e2'); auto.
  Qed.

  Lemma writes_mods : forall c p v, writes c p v -> mods c p.
  Proof.
    unfold writes, mods; clarify.
    do 2 eexists; eauto 2; clarify.
  Qed.

  Lemma read_prefix : forall c r p v
    (Hr : nth_error (to_seq c) r = Some (MRead p v)),
    Forall (fun x => not_read x = false \/ independent (loc_of x) (Ptr p))
     (firstn r (to_seq c)).
  Proof.
    intros; rewrite Forall_forall; intros.
    exploit in_nth_error; eauto; clarify.
    rewrite nth_error_firstn in *; clarify.
    destruct (op_modifies x p) eqn: Hmods.
    - exploit read_before_mod; eauto; omega.
    - destruct x; clarify.
  Qed.
  
  Definition after E R e e' := E e' /\ R (id e) (id e').

  Program Definition before_list l e R
    (R_dec : forall i (He1 : In i (map id l)), {R i (id e)} + {~R i (id e)}) :=
    filter (fun e1 => if in_dec eid_eq (id e1) (map id l) then
                      if R_dec (id e1) _ then true else false else false) l.

  Lemma lin_before : forall l (E : Ensemble event) R e
    (R_dec : forall i (Hi : In i (map id l)), {R i (id e)} + {~R i (id e)})
    (Hlin : linearization E R l) (He : E e),
    linearization (before E R e) R (before_list l e R R_dec).
  Proof.
    intros; split; [|split].
    - intro; unfold before; setoid_rewrite filter_In; split; clarify.
      + rewrite (lin_set Hlin) in *; clarify.
        destruct (in_dec eid_eq (id e0) (map id l)); clarify.
        rewrite in_map_iff in *; eauto.
      + rewrite (lin_set Hlin); clarify.
        destruct (in_dec eid_eq (id e0) (map id l)); clarify.
    - setoid_rewrite (map_filter _ _ (fun i => match in_dec eid_eq i (map id l)
        with left H => if R_dec i H then true else false | _ => false end)).
      apply NoDup_filter; unfold linearization in Hlin; clarify.
      { rewrite Forall_forall; reflexivity. }
    - unfold before; clarify.
      unfold linearization in Hlin; clarify.
      specialize (Hlin22 _ _ He11 He21 Horder); destruct Hlin22 as (i1 & i2 &
        Hi1 & Hi2 & Hlt).
      generalize (nth_error_split' _ _ Hi2); intros (l1' & l3 & ? & ?); subst.
      rewrite nth_error_app in Hi1; clarify.
      generalize (nth_error_split' _ _ Hi1); intros (l1 & l2 & ? & ?); subst.
      setoid_rewrite filter_app.
      destruct (in_dec eid_eq (id e1)
        (map id ((l1 ++ e1 :: l2) ++ e2 :: l3))) eqn: Hid.
      destruct (R_dec (id e1) (before_list_obligation_1 ((l1 ++ e1 :: l2) ++
        e2 :: l3) e R R_dec e1 i)) eqn: HR; clarify.
      repeat eexists.
      + setoid_rewrite filter_app; simpl.
        rewrite Hid, HR.
        rewrite <- app_assoc; simpl; apply nth_error_split.
      + destruct (in_dec eid_eq (id e2)
        (map id ((l1 ++ e1 :: l2) ++ e2 :: l3))).
        destruct (R_dec (id e2) (before_list_obligation_1 ((l1 ++ e1 :: l2) ++
          e2 :: l3) e R R_dec e2 i0)); clarify.
        apply nth_error_split.
        { contradiction n; rewrite in_map_iff.
          do 2 eexists; eauto; rewrite in_app; clarify. }
      + rewrite filter_app, app_length; simpl.
        rewrite Hid, HR; simpl; omega.
      + contradiction n; rewrite in_map_iff.
        do 2 eexists; eauto; rewrite <- app_assoc, in_app; clarify.
  Qed.

  Lemma hb_dec_a : forall E X l (Hlin : linearization E (hb X) l)
    a (Ha : E a) i (Hi : In i (map id l)), {hb X i (id a)} + {~hb X i (id a)}.
  Proof.
    intros; destruct (hb_dec _ Hlin _ (id a) Hi); auto.
    { rewrite (lin_set Hlin) in Ha; rewrite in_map_iff; eauto. }
  Qed.

  Program Definition after_list l e R
    (R_dec : forall i (He1 : In i (map id l)), {R (id e) i} + {~R (id e) i}) :=
    filter (fun e1 => if in_dec eid_eq (id e1) (map id l) then
                      if R_dec (id e1) _ then true else false else false) l.

  Lemma lin_after : forall l (E : Ensemble event) R e
    (R_dec : forall i (Hi : In i (map id l)), {R (id e) i} + {~R (id e) i})
    (Hlin : linearization E R l) (He : E e),
    linearization (after E R e) R (after_list l e R R_dec).
  Proof.
    intros.
    assert (set_of (after_list l e R R_dec) = after E R e) as Hset.
    { apply set_ext; intro; unfold after; setoid_rewrite filter_In; split;
        clarify.
      + rewrite (lin_set Hlin); clarify.
        destruct (in_dec eid_eq (id e0) (map id l)); clarify.
      + rewrite (lin_set Hlin) in *; clarify.
        destruct (in_dec eid_eq (id e0) (map id l)); clarify.
        rewrite in_map_iff in *; eauto. }
    rewrite <- Hset; eapply lin_filter; eauto.
  Qed.

  Lemma Add_Subtract : forall A (S : Ensemble A) x (Hx : S x)
    (Hdec : forall y, S y -> x = y \/ x <> y),
    Add (Subtract S x) x = S.
  Proof.
    intros; apply set_ext; intro; rewrite Add_spec, Subtract_spec; split;
      clarify.
    specialize (Hdec e); clarify.
  Qed.

  Program Definition not_after_list l e R
    (R_dec : forall i (He1 : In i (map id l)), {R (id e) i} + {~R (id e) i}) :=
    filter (fun e1 => if in_dec eid_eq (id e1) (map id l) then
                      if R_dec (id e1) _ then false else true else true) l.

  Lemma after_lin : forall l (E : Ensemble event) R e
    (Hlin : linearization E R l) (He : E e) (Htrans : transitive_on R E)
    (R_dec : forall i (Hi : In i (map id l)), {R (id e) i} + {~R (id e) i}),
    linearization E R (not_after_list l e R R_dec ++ after_list l e R R_dec).
  Proof.
    intros.
    assert (E = Union (set_of (not_after_list l e R R_dec))
      (set_of (after_list l e R R_dec))) as Hset.
    { apply set_ext; intro; rewrite Union_spec; setoid_rewrite filter_In.
      rewrite (lin_set Hlin); split; clarify.
      destruct (in_dec eid_eq (id e0) (map id l)); clarify. }
    rewrite Hset; clear Hset; apply lin_combine; try (eapply lin_filter; eauto).
    - setoid_rewrite in_map_iff; setoid_rewrite filter_In.
      intros ? (x & Hx) (y & Hy); clarify.
      destruct (in_dec eid_eq (id y) (map id l)); clarify.
      clear cond; rewrite Hy1 in *.
      destruct (in_dec eid_eq (id x) (map id l)); clarify.
    - setoid_rewrite in_map_iff; setoid_rewrite filter_In.
      intros ?? (x & Hx) (y & Hy); clarify.
      destruct (in_dec eid_eq (id y) (map id l)); clarify.
      destruct (in_dec eid_eq (id x) (map id l)); clarify.
      intro; contradiction n; apply (Htrans _ y); auto;
        rewrite (lin_set Hlin); auto.
      { contradiction n; rewrite in_map_iff; eauto. }
  Qed.

  Lemma lin_reorder_last : forall E R l e p (Hlin : linearization E R l)
    (He : E e) (Hmods : mods (op e) p) (Htrans : transitive_on R E)
    (Hlast : forall e', E e' -> mods (op e') p -> ~R (id e) (id e'))
    (HR_dec : forall i1 i2 (Hi1 : In i1 (map id l)) (He2 : In i2 (map id l)),
       {R i1 i2} + {~R i1 i2}),
    exists l', linearization E R l' /\
    find (fun e => if find_mod (op e) p then true else false) (rev l') = Some e.
  Proof.
    intros.
    assert (forall i, In i (map id l) -> {R (id e) i} + {~R (id e) i}) as R_dec.
    { intros; apply HR_dec; auto.
      rewrite in_map_iff; exists e; clarify.
      rewrite <- (lin_set Hlin); auto. }
    exploit after_lin; eauto.
    instantiate (1 := R_dec).
    intro Hlin'.
    assert (In e (not_after_list l e R R_dec)).
    { setoid_rewrite filter_In; rewrite <- (lin_set Hlin); clarify.
      destruct (in_dec eid_eq (id e) (map id l)); clarify.
      exploit lin_irrefl; eauto. }
    exploit in_split; eauto; intros (l1 & l2 & Hfirst); rewrite Hfirst in *.
    exists (l1 ++ l2 ++ e :: after_list l e R R_dec); split.
    - rewrite app_assoc, <- (Add_Subtract _ He).
      apply lin_add.
      + rewrite <- app_assoc in *; apply lin_remove; auto.
      + unfold linearization in Hlin'; clarify.
        repeat rewrite map_app in *; repeat rewrite NoDup_app in *; clarify.
        repeat setoid_rewrite in_app; intros [[? | ?] | ?].
        * exploit Hlin'21122; eauto.
        * inversion Hlin'21121; auto.
        * exploit Hlin'2122; eauto.
          rewrite in_app; clarify.
      + eapply lin_irrefl; eauto.
      + intros.
        assert (In e' (not_after_list l e R R_dec)) as He'
          by (rewrite Hfirst; rewrite in_app in *; clarify).
        setoid_rewrite filter_In in He'; clarify.
        destruct (in_dec eid_eq (id e') (map id l)); clarify.
        contradiction n; rewrite in_map_iff; eauto.
      + setoid_rewrite filter_In; clarify.
        destruct (in_dec eid_eq (id e') (map id l)); clarify.
        intro; exploit lin_irrefl; eauto.
        apply (Htrans _ e'); auto.
        rewrite (lin_set Hlin); auto.
      + intros; eapply lin_e_eq; eauto.
    - repeat (rewrite rev_app_distr; simpl).
      repeat rewrite <- app_assoc.
      generalize (mods_spec (op e) p); rewrite find_app; clarify.
      destruct (find (fun e => if find_mod (op e) p then true else false)
        (rev (after_list l e R R_dec))) eqn: Hfind; auto.
      rewrite find_spec in Hfind; clarify.
      generalize (mods_spec (op e0) p); clarify.
      exploit nth_error_in; eauto.
      rewrite <- in_rev; setoid_rewrite filter_In; clarify.
      destruct (in_dec eid_eq (id e0) (map id l)); clarify.
      specialize (Hlast e0); use Hlast; clarify.
      rewrite (lin_set Hlin); auto.
  Qed.
      
  Lemma total_lin_nth : forall E R l (Hlin : linearization E R l)
    (Htotal : total_on R E) i1 i2 e1 e2 (He1 : nth_error l i1 = Some e1)
    (He2 : nth_error l i2 = Some e2) (Hlt : i1 < i2), R (id e1) (id e2).
  Proof.
    intros; specialize (Htotal e1 e2).
    generalize (nth_error_in _ _ He1), (nth_error_in _ _ He2);
      repeat rewrite (lin_set Hlin) in Htotal; clarify.
    destruct Htotal.
    - subst; generalize (NoDup_inj _ _ (lin_nodup Hlin) He1 He2); omega.
    - generalize (lin_order_3 Hlin _ _ He2 He1); clarify; omega.
  Qed.

(*  Lemma lin_before_ops : forall (E : Ensemble event) R ops a z m1
    (Hops : total_on R (set_of ops)) (Hops : linear R ops)
    (Hin : forall e (He : In e ops), E e)
    (Hbegin : forall e (He : In e ops), e = a \/ R (id a) (id e))
    (Hend : forall e (He : In e ops), e = z \/ R (id e) (id z))
    (Ha : In a ops) (Hin : In z ops) (Hm1 : linearization (before E R a) R m1)
    b (Hordered : forall e o, E e -> mods (op e) (b, o) ->
       R (id e) (id a) \/ In e ops \/ R (id z) (id e))
    l (Hlin : linearization E R l)
    (HR_dec : forall i1 i2 (Hi1 : In i1 (map id l)) (He2 : In i2 (map id l)),
       {R i1 i2} + {~R i1 i2}),
    exists R_dec ops1, linearization E R (m1 ++ ops1 ++ after_list l z R R_dec) 
      /\ filter (modsb b) (map op ops1) = filter (modsb b) (map op ops).
  Proof.
    intros.
    assert (In (id a) (map id l)) as Hida.
    { rewrite in_map_iff; do 2 eexists; eauto.
      rewrite <- (lin_set Hlin); auto. }
    assert (In (id z) (map id l)) as Hidz.
    { rewrite in_map_iff; do 2 eexists; eauto.
      rewrite <- (lin_set Hlin); auto. }
    assert (forall i, In i (map id l) -> {R (id z) i} + {~R (id z) i})
      as R_dec by (intros; apply HR_dec; auto).
    exists R_dec, (filter (fun e => if in_dec eid_eq (id e) (map id m1)
      then false else if in_dec eid_eq (id e) (map id (after_list l z R R_dec)) 
      then false else true) l); split.
    - assert (E = Union (before E R a) (Union (Setminus E
        (Union (before E R a) (after E R z))) (after E R z))) as Heq.
      { apply set_ext; intro; rewrite Union_spec, Union_spec, Setminus_spec,
          Union_spec; unfold before, after; split; clarify.
        rewrite (lin_set Hlin) in *.
        assert (In (id e) (map id l)) as Hide
          by (rewrite in_map_iff; do 2 eexists; eauto).
        generalize (HR_dec (id e) (id a)); intros [? | ?]; auto.
        generalize (HR_dec (id z) (id e)); intros [? | ?]; auto.
        right; left; clarify; intro; clarify. }
      rewrite Heq; clear Heq.
      apply lin_combine; auto; [apply lin_combine| |].
      + apply lin_after; auto.
      + replace (Setminus E (Union (before E R a) (after E R z))) with
         (set_of (filter (fun e => if in_dec eid_eq (id e) (map id m1)
          then false else
          if in_dec eid_eq (id e) (map id (after_list l z R R_dec)) then false
          else true) l)); [eapply lin_filter; eauto|].
        apply set_ext. intros e. rewrite Setminus_spec, Union_spec. unfold set_of.
        unfold before. unfold after. rewrite filter_In. rewrite lin_set; eauto.
        destruct (in_dec eid_eq (id e) (map id m1));
          [|destruct (in_dec eid_eq (id e) (map id (after_list l z R R_dec)))].

        * rewrite in_map_iff in i. destruct i as [x [Heq Hin2]].
          subst.  rewrite <- lin_set in Hin2; eauto.  unfold before in Hin2. split; clarify.
          contradiction H2; clarify. rewrite Heq in Hin22. auto.

        * admit.
        * admit.
        
      + admit.
      + admit.
      + admit.
      + admit.
    - admit.
  Admitted.*)

  Lemma full_in : forall E X i j, full E X i j -> exists ei ej, E ei /\ E ej /\
    id ei = i /\ id ej = j.
  Proof.
    intros; induction H.
    - unfold restrict in H; clarify; repeat eexists; eauto.
    - clarify; repeat eexists; eauto.
  Qed.

  Corollary full_in1 : forall E X i j, full E X i j ->
    exists ei, E ei /\ id ei = i.
  Proof. intros; exploit full_in; eauto; clarify; eauto. Qed.

  Corollary full_in2 : forall E X i j, full E X i j ->
    exists ej, E ej /\ id ej = j.
  Proof. intros; exploit full_in; eauto; clarify; eauto. Qed.

  Lemma full_complete_lt : forall E X l i1 i2 e1 e2
    (Hlin : linearization E (full E X) l) (He1 : nth_error l i1 = Some e1)
    (He2 : nth_error l i2 = Some e2)
    (Hcomplete : full E (complete_hb X l) (id e1) (id e2)), i1 < i2.
  Proof.
    intros; remember (id e1) as i; remember (id e2) as j;
      generalize dependent e2; generalize dependent e1; revert i1 i2;
      induction Hcomplete; clarify.
    - unfold restrict, union in H; destruct H as (Horder & ei & ej & Heij);
        clarify.
      exploit lin_id_inj; try apply Heij221; eauto.
      { rewrite (lin_set Hlin); eapply nth_error_in; eauto. }
      exploit lin_id_inj; try apply Heij222; eauto.
      { rewrite (lin_set Hlin); eapply nth_error_in; eauto. }
      clarify; destruct Horder as [[? | He'] | ?]; clarify.
      + eapply lin_order_3; eauto.
        apply t_step; unfold restrict, union; clarify; repeat eexists; eauto.
      + exploit lin_id_inj; try apply He'2221; eauto.
        { rewrite (lin_set Hlin); eapply nth_error_in; eauto. }
        exploit lin_id_inj; try apply He'2222; eauto.
        { rewrite (lin_set Hlin); eapply nth_error_in; eauto. }
        clarify; generalize (NoDup_inj _ _ (lin_nodup Hlin) He'21 He1);
          generalize (NoDup_inj _ _ (lin_nodup Hlin) He'221 He2); clarify.
      + eapply lin_order_3; eauto.
        apply t_step; unfold restrict, union; clarify; repeat eexists; eauto.
    - generalize (full_in2(X := complete_hb X l) Hcomplete1);
        intros (e3 & He3 & ?); subst.
      rewrite (lin_set Hlin) in He3; exploit in_nth_error; eauto;
        intros (i3 & ? & Hi3).
      specialize (IHHcomplete1 _ _ _ He1 eq_refl _ Hi3 eq_refl);
        specialize (IHHcomplete2 _ _ _ Hi3 eq_refl _ He2 eq_refl); omega.
  Qed.
      
  Lemma full_complete_lin : forall E X l (Hlin : linearization E (full E X) l),
    linearization E (full E (complete_hb X l)) l.
  Proof.
    unfold linearization; clarify.
    rewrite Hlin1 in *.
    generalize (in_nth_error _ _ He1), (in_nth_error _ _ He2);
      intros (i1 & ? & Hi1) (i2 & ? & Hi2).
    exists i1, i2; clarify.
    eapply full_complete_lt; eauto.
    split; [|split]; auto.
  Qed.

  Lemma b_not_read_spec' : forall b (m : list mem_op), filter (b_not_read b) m =
    proj_block (filter not_read m) b.
  Proof.
    intros; setoid_rewrite filter_comm.
    rewrite b_not_read_spec; auto.
  Qed.

  Lemma last_filter_proj : forall (l1 l2 : list mem_op) b o a,
    last_op (filter (b_not_read b) l1 ++ proj_block l2 b) (Ptr (b, o)) a <->
    last_op (l1 ++ l2) (Ptr (b, o)) a.
  Proof.
    intros.
    setoid_rewrite <- last_op_filter at 2; rewrite <- last_op_filter.
    rewrite filter_app, b_not_read_spec, filter_idem.
    setoid_rewrite last_op_proj at 2; simpl.
    rewrite <- filter_app, <- proj_block_app, <- b_not_read_spec.
    rewrite <- b_not_read_spec'; reflexivity.
  Qed.

  Lemma b_not_read_last : forall (m : list mem_op) l a b
    (Hb : block_of_loc l = b),
    last_op m l a <-> last_op (filter (b_not_read b) m) l a.
  Proof.
    clarify.
    rewrite b_not_read_spec, last_op_filter, last_op_proj; reflexivity.
  Qed.

  Lemma lin_antisym : forall E R l (Hlin : linearization E R l)
    e1 e2 (He1 : E e1) (He2 : E e2) (HR : R (id e1) (id e2)),
    ~R (id e2) (id e1).
  Proof.
    repeat intro.
    rewrite (lin_set Hlin) in *; generalize (in_nth_error _ _ He1),
      (in_nth_error _ _ He2); intros (i1 & ? & Hi1) (i2 & ? & Hi2).
    exploit lin_order_3; try apply HR; eauto.
    exploit lin_order_3; try apply H; eauto; omega.
  Qed.

  Lemma lin_contained' : forall S (R R' : order) l (Hlin : linearization S R l)
    (Hcont : forall e1 e2 (He1 : S e1) (He2 : S e2), R' (id e1) (id e2) ->
      R (id e1) (id e2)), linearization S R' l.
  Proof. unfold linearization; clarify. Qed.

  Lemma full_sub' : forall E E' X i j (Hfull : full E' X i j)
    (Hsub : forall e (He : E' e), exists e', E e' /\ id e = id e'),
    full E X i j.
  Proof.
    intros; induction Hfull.
    - destruct H as (H & e1 & e2 & He1 & He2 & ?).
      generalize (Hsub _ He1), (Hsub _ He2); 
        intros (e1' & ? & Hid1) (e2' & ? & Hid2).
      apply t_step; split; auto; exists e1', e2'; clarify.
    - eapply t_trans; eauto.
  Qed.

  Lemma lower_last : forall (ops : list event) i w p a
    (Hi : nth_error ops i = Some w) (Ha : last_op (to_seq (op w)) (Ptr p) a)
    (Hlast : forall i2 w2, nth_error ops i2 = Some w2 -> mods (op w2) p ->
                           i2 <= i),
    last_op (lower ops) (Ptr p) a.
  Proof.
    intros.
    exploit nth_error_split'; eauto; intros (ops1 & ops2 & ?); clarify.
    rewrite lower_app, lower_cons, app_assoc, last_op_app; right.
    split.
    - rewrite last_op_app; auto.
    - rewrite Forall_forall; intros ? Hin.
      destruct (op_modifies x p) eqn: Hmods.
      + rewrite flatten_in in *; clarify.
        do 2 (rewrite in_map_iff in *; clarify).
        generalize (in_nth_error _ _ Hin222); intros (i' & ? & Hi').
        specialize (Hlast (length ops1 + S i'));
          rewrite nth_error_plus in Hlast; specialize (Hlast _ Hi').
        use Hlast; [omega | unfold mods; eauto].
      + destruct x; clarify.
  Qed.

  Lemma drop_ids_set : forall E X l ops
    (Hin : forall e, In e ops -> events E e) (Hlin : linear (hb X) ops)
    ops' X' (Hdrop : drop_l_reads l E (ops, X) = (ops', X'))
    e (He : Union (Setminus (events E) (set_of ops)) (set_of ops') e),
    exists e', events E e' /\ id e = id e'.
  Proof.
    intros.
    rewrite Union_spec, Setminus_spec in He; destruct He; clarify; eauto.
    exploit drop_ids; eauto.
    { unfold linearization in Hlin; clarify. }
    intros (_ & Hids); exploit Hids; eauto; clarify; eauto.
  Qed.  

  Lemma drop_full : forall l E ops X (Hwf : well_formed E X) ops' X'
    (Hcont : contained (constraints E) (hb X))
    (Hin : forall e, In e ops -> events E e) (Hops : linear (hb X) ops)
    (Hdrop : drop_l_reads l E (ops, X) = (ops', X'))
    (Htrans : transitive_on (hb X) (events E))
    i j (Hfull : full (Union (Setminus (events E) (set_of ops)) (set_of ops'))
      X' i j),
    full (events E) X i j.
  Proof.
    intros.
    exploit drop_order; eauto; clarify.
    induction Hfull; clarify.
    - destruct H as (H & x' & y' & Hx' & Hy' & ?); clarify.
      exploit drop_ids_set; try apply Hx'; eauto; intros (? & ? & Hidx).
      exploit drop_ids_set; try apply Hy'; eauto; intros (? & ? & Hidy).
      rewrite Hidx, Hidy in *; apply t_step; repeat eexists; auto.
      destruct H; [left | right]; clarify.
      rewrite <- Hidx, <- Hidy in *; rewrite drop_rf in H; clarify; eauto.
    - eapply t_trans; eauto.
  Qed.

  (* up *)
  Lemma minus_reverse : forall a b c (Hltb : b < a) (Hltc : c < a),
    a - b - 1 < c -> a - c - 1 < b.
  Proof.
    intros; omega.
  Qed.

  Lemma same_find : forall m1 E X e m2 m1' p
    (Hlin : linearization E (full E X) (m1 ++ e :: m2))
    (Hlin' : linearization (before E (full E X) e) (full E X) m1')
    (HE : E e) (He : forall e' (He' : E e') (Hmods : mods (op e') p),
       hb X (id e') (id e) \/ e' = e \/ hb X (id e) (id e'))
    (Hord : forall e1 e2 (He1 : E e1) (He2 : E e2)
      (Hmods1 : mods (op e1) p) (Hmods1 : mods (op e2) p),
       hb X (id e1) (id e2) \/ e1 = e2 \/ hb X (id e2) (id e1)),
    find (fun e => if find_mod (op e) p then true else false) (rev m1') =
    find (fun e => if find_mod (op e) p then true else false) (rev m1).
  Proof.
    intros.
    destruct (find (fun e => if find_mod (op e) p then true else false)
      (rev m1)) eqn: Hfind.
    - generalize (mods_spec (op e0) p).
      rewrite find_spec in Hfind; clarify.
      assert (E e0) as He0 by (rewrite (lin_set Hlin), in_app, in_rev;
        left; eapply nth_error_in; eauto).
      exploit He; eauto; intros [? | [? | ?]].
      rewrite find_spec.
      assert (In e0 (rev m1')).
      { rewrite <- in_rev, <- (lin_set Hlin'); unfold before; clarify.
        apply t_step; repeat eexists; auto; left; auto. }
      exploit in_nth_error; eauto; intros (i & ? & Hi); exists i; clarify.
      generalize (mods_spec (op y) p); clarify.
      generalize (nth_error_rev' _ _ Hi); exploit nth_error_rev'; eauto;
        intros Hj' Hi'.
      specialize (Hord e0 y); clarify.
      generalize (nth_error_in _ _ Hj'); rewrite <- (lin_set Hlin');
        unfold before; clarify.
      destruct Hord as [? | [? | ?]].
      + generalize (nth_error_rev' _ _ Hfind1); intro Hx.
        exploit nth_error_lt; eauto; intro.
        exploit (lin_order_1 Hlin (length m1 - x - 1)); eauto 2.
        { rewrite nth_error_app; clarify; eauto. }
        { apply t_step; repeat eexists; auto; left; auto. }
        intros (i2 & Hi2 & ?).
        exploit (lin_order_3 Hlin).
        { eauto. }
        { apply nth_error_split. }
        { auto. }
        rewrite nth_error_app in Hi2; clarify.
        exploit nth_error_rev; eauto; intro.
        specialize (Hfind22 (length m1 - i2 - 1) y); use Hfind22; clarify.
        apply minus_reverse; auto.
        generalize (nth_error_lt _ _ Hfind1); rewrite rev_length; auto.
      + subst.
        generalize (NoDup_inj _ _ (lin_nodup Hlin') Hi' Hj').
        rewrite rev_length in *; omega.
      + exploit (lin_order_3 Hlin' (length m1' - j - 1)); eauto 2.
        { apply t_step; repeat eexists; auto; left; auto. }
        omega.
      + subst.
        generalize (lin_nodup Hlin); rewrite NoDup_app; intro Hnodup; clarify.
        exploit nth_error_in; eauto; rewrite <- in_rev; intro.
        exploit Hnodup22; eauto; clarify.
      + exploit nth_error_rev'; eauto; intro.
        exploit nth_error_lt; eauto; intro.
        exploit (lin_order_3 Hlin); eauto 2.
        { apply nth_error_split. }
        { instantiate (2 := length m1 - x - 1); rewrite nth_error_app; clarify;
            eauto. }
        { apply t_step; repeat eexists; auto; left; auto. }
        omega.
    - rewrite find_fail, Forall_forall in *; intros.
      rewrite <- in_rev, <- (lin_set Hlin') in *; unfold before in *; clarify.
      specialize (Hfind x); use Hfind; clarify.
      exploit (lin_order_2 Hlin); eauto 2.
      { apply nth_error_split. }
      intros (i & Hi & ?); rewrite nth_error_app in Hi; clarify.
      rewrite <- in_rev; eapply nth_error_in; eauto.
  Qed.

  Theorem race_free_SC : forall (b0 : block) E X (Hrf : race_free (events E) X),
    valid E X <-> (SC E X /\ well_formed E X).
  Proof.
    intros; split; intro Hcon; simpl in *.
    - generalize (valid_wf _ _ Hcon); clarify.
      split; [apply valid_hb; auto|].
      generalize (hb_trans _ _ Hcon); clarify.
      exploit wf_full; eauto; intros (m & Hm); exists m; split; auto; intros.
      exploit nth_error_in; eauto; rewrite <- (lin_set Hm); intro Hinr.
      destruct (drop_l_reads p E ([r], X)) as [ops' X'] eqn: Hdrop.
      assert (forall e', events E e' -> mods (op e') p ->
        hb X (id e') (id r) \/ e' = r \/ hb X (id r) (id e')) as Hord.
      { intros; eapply race_free_mods_read; unfold reads; eauto; simpl; eauto.
      }
      generalize (lin_nodup Hm); intro Hnodup.
      generalize (valid_rf _ _ Hcon); intro Hrf_reads.
      generalize (full_lin Hm); intros (Hhb_lin & _).
      generalize (lin_irrefl Hhb_lin); intro Hirrefl.
      rewrite private_seq_1 in Hcon; eauto.
      destruct Hcon as (Hvalid & m1 & Hm1 & Hseq).
      specialize (Hseq _ Hreads).
      destruct (find (fun e => if find_mod (op e) p then true else false)
        (rev m1)) eqn: Hfind; clarify.
      generalize (nth_error_split' _ _ Hr); intros (l1 & l2 & ?); clarify.
      rewrite firstn_app, firstn_length, minus_diag, app_nil_r.
      erewrite <- same_find; eauto; clarify; eauto.
      eapply Hrf; eauto; eapply mods_touches; eauto.
    - destruct Hcon as ((Hcont' & Htrans' & m & Hlin & Hseq) & Hwf).
      (* Here we do need to do induction on the linearization. *)
      remember (length (filter (fun op => negb (not_read op)) (lower m)))
        as nreads; generalize dependent m;
        generalize dependent X; generalize dependent E;
        induction nreads using lt_wf_ind; intros.
      destruct (find has_read (rev m)) eqn: Hfind.
      + generalize (lin_nodup Hlin); intro Hnodup.
        rewrite find_spec in Hfind; clarify.
        rewrite has_read_reads in Hfind21; destruct Hfind21 as (p & v & Hr).
        exploit nth_error_in; eauto; rewrite <- in_rev; intro.
        exploit in_split; eauto; intros (m1 & m2 & ?); clarify.
        rewrite lower_app, lower_cons in *.
        destruct (drop_l_reads p E ([e], X)) as [ops' Xd] eqn: Hdrop.
        assert (events E e) as Hein.
        { unfold linearization in Hlin; clarify.
          rewrite Hlin1, in_app; clarify. }
        generalize (NoDup_remove_2 _ _ _ Hnodup); intro Heout.
        assert (forall e', events E e' -> mods (op e') p ->
          hb X (id e') (id e) \/ e' = e \/ hb X (id e) (id e')) as Hord.
        { intros; eapply race_free_mods_read; unfold reads; eauto; simpl; eauto.
        }
        generalize (full_lin Hlin); intros (Hhb_lin & _).
        assert (~hb X (id e) (id e)).
        { eapply lin_irrefl; eauto. }
(*        exploit (before_lin_hb(l := m1 ++ e :: m2)(E := events E) X); eauto.
        intros (l1 & l2 & Hbefore & Hlin').*)
        rewrite private_seq_1; eauto.
        assert (forall e0 (He : Union (Subtract (events E) e) (set_of ops') 
          e0), exists e', events E e' /\ id e0 = id e') as Hsub'.
        { simpl; exploit drop_ids; eauto.
          { constructor; auto. }
          intros (_ & Hids) ??.
          rewrite Union_spec, Subtract_spec in He; destruct He; clarify; eauto.
          specialize (Hids e0); clarify; eauto. }
        split; [eapply H; eauto 2|].
        * instantiate (1 := m1 ++ ops' ++ m2).
          generalize (drop_reads m1 _ m2 _ X _ _ Hr Hdrop);
            repeat rewrite lower_app; auto.
        * eapply drop_race_free; eauto.
        * exploit drop_order; try apply Hdrop; clarify.
          { apply lin_single; auto. }
        * exploit drop_order; try apply Hdrop; clarify.
          { apply lin_single; auto. }
          rewrite set_of_single in *; auto.
        * unfold Subtract; rewrite <- set_of_single.
          eapply drop_wf; eauto 2; clarify.
          constructor; auto.
        * simpl.
          unfold linearization in Hlin; clarify; split; [|split].
          { intro e'; repeat rewrite in_app; rewrite Union_spec, Subtract_spec.
            rewrite Hlin1, in_app; unfold set_of; split; intro Hin; clarify.
            rewrite in_app in *; destruct Hin; clarify; left; clarify; intro; 
                clarify. }
          { repeat rewrite map_app in *.
            generalize (NoDup_remove_1 _ _ _ Hlin21); intro.
            exploit drop_ids; eauto.
            { constructor; auto. }
            intros [? Hids].
            apply NoDup_middle; auto.
            intros.
            rewrite in_map_iff in *; clarify.
            exploit Hids; eauto; clarsimp.
            apply NoDup_remove_2; auto. }
          { intros; rewrite Union_spec, Subtract_spec in *.
            exploit drop_full; eauto.
            { clarify. }
            { apply lin_single; auto. }
            { rewrite set_of_single; eauto. }
            intro Horder'.
            exploit drop_order; try apply Hdrop; auto.
            { clarify. }
            { apply lin_single; auto. }
            (*clear Hlin';*) intros (Hlin' & ? & ? & Hord').
            assert (forall e', In e' ops' -> id e' = id e) as He'.
            { exploit drop_ids; try (apply Hdrop).
              { constructor; auto. }
              intros [_ Hids].
              intros ? Hin; specialize (Hids _ Hin); clarify. }
            destruct He1.
            { destruct He2; clarify.
              { specialize (Hlin22 e1 e2); clarify.
                assert (x0 < length m1 \/ x0 >= length m1 + length [e]).
                { destruct (eq_dec x0 (length m1)); [subst | simpl; omega].
                  rewrite nth_error_split in *; clarify. }
                assert (x1 < length m1 \/ x1 >= length m1 + length [e]).
                { destruct (eq_dec x1 (length m1)); [subst | simpl; omega].
                  rewrite nth_error_split in *; clarify. }
                exists (adjust_range m1 [e] ops' x0),
                  (adjust_range m1 [e] ops' x1);
                  repeat rewrite adjust_range_nth_error; clarify.
                apply adjust_lt; auto. }
              { unfold set_of in *; specialize (He' e2); clarify.
                rewrite He' in *; specialize (Hlin22 e1 e); clarify.
                destruct (eq_dec x1 (length m1));
                  [|rewrite <- drop_nth_error in Hlin2221; auto;
                    generalize (nth_error_in _ _ Hlin2221)]; clarify.
                exploit in_nth_error; eauto; clarify.
                exists (adjust_range m1 [e] ops' x0), (length m1 + x1);
                  rewrite adjust_range_nth_error; clarify.
                rewrite nth_error_app, lt_dec_plus_r, minus_plus.
                exploit nth_error_lt; eauto; intro; rewrite nth_error_app;
                  unfold adjust_range; clarify; omega. } }
            { unfold set_of in *; specialize (He' e1); clarify.
              rewrite He' in *; destruct He2.
              specialize (Hlin22 e e2); clarify.
              destruct (eq_dec x0 (length m1));
                [|rewrite <- drop_nth_error in Hlin221; auto;
                  generalize (nth_error_in _ _ Hlin221)]; clarify.
              exploit in_nth_error; eauto; clarify.
              exists (length m1 + x0), (adjust_range m1 [e] ops' x1);
                rewrite adjust_range_nth_error; clarify.
              rewrite nth_error_app, lt_dec_plus_r, minus_plus.
              exploit nth_error_lt; eauto; intro; rewrite nth_error_app;
                unfold adjust_range; clarify.
              destruct (lt_dec x1 (length m1)); omega.
              { omega. }
              { exploit drop_ids; try (apply Hdrop).
                { constructor; auto. }
                intros [Hnodup' Hids].
                specialize (Hids e2); clarify.
                rewrite Hids2 in *; specialize (Hlin22 _ _ Hein Hein); clarify.
                exploit NoDup_inj.
                { apply Hnodup. }
                { apply Hlin221. }
                { apply Hlin2221. }
                omega. } } }
(*        * repeat rewrite lower_app in *.
          repeat rewrite filter_app in *; clarify.
          rewrite (drop_b_reads_spec _ _ _ _ Hdrop), filter_filter,
            lower_single.
          setoid_rewrite (filter_ext _ not_read) at 2; auto.
          rewrite Forall_forall; unfold andb; clarsimp.*)
        * intros.
          generalize (drop_len p E [e] X); rewrite Hdrop; clarify.
          destruct ops'; clarify; [|destruct ops'; clarify; [|omega]].
          { specialize (Hseq (add_index i (length m1)));
              rewrite add_nth_error in Hseq; specialize (Hseq _ _ _ Hr0 Hreads).
            destruct (find (fun e => if find_mod (op e) p0 then true else false)
              (rev (firstn (add_index i (length m1)) (m1 ++ e :: m2))))
              eqn: Hfind; clarify.
            assert (events E r /\ r <> e).
            { exploit nth_error_in; eauto; intro; split.
              * rewrite (lin_set Hlin); rewrite in_app in *; clarify.
              * intro; clarify. }
            unfold add_index in Hfind; destruct (lt_dec i (length m1)).
            + rewrite firstn_app, not_le_minus_0, app_nil_r in *; try omega.
              clarify.
              rewrite drop_rf; eauto; clarify; [split; eauto| |];
                rewrite Union_spec, Setminus_spec; left; clarify;
                [|intro; clarify].
              exploit find_success; eauto; rewrite <- in_rev; intros (? & _).
              exploit firstn_in; eauto; intro.
              rewrite (lin_set Hlin), in_app; clarify.
              intro; clarify.
              rewrite NoDup_app in Hnodup; clarify.
              exploit Hnodup22; eauto.
            + rewrite firstn_app, firstn_length' in *; try omega.
              rewrite <- minus_Sn_m in Hfind; [|omega]; clarify.
              rewrite rev_app_distr in *; clarify.
              rewrite <- app_assoc in Hfind; setoid_rewrite find_drop in Hfind;
                clarify.
              rewrite drop_rf; eauto; clarify; [split; eauto| |];
                rewrite Union_spec, Setminus_spec; left; clarify;
                [|intro; clarify].
              * exploit find_success; eauto.
                rewrite <- rev_app_distr, <- in_rev; intros (? & _).
                assert (In e0 m1 \/ In e0 m2).
                { rewrite in_app in *; clarify.
                  right; eapply firstn_in; eauto. }
                rewrite (lin_set Hlin), in_app; split; [|intro]; clarify.
                rewrite NoDup_app in Hnodup; clarify.
                inversion Hnodup21; clarify.
                exploit Hnodup22; eauto.
              * rewrite find_spec in cond; clarify.
                generalize (drop_l_reads_spec _ _ _ _ Hdrop); intro Hnone.
                symmetry in Hnone; rewrite filter_none_iff, lower_single,
                  Forall_forall in Hnone.
                exploit nth_error_in; eauto 2; intro; exploit Hnone; eauto 2.
                destruct m; clarify. }
          { generalize (drop_l_reads_spec _ _ _ _ Hdrop);
              repeat rewrite lower_single; intro He.
            assert (id e0 = id e) as Hid.
            { exploit drop_ids; eauto.
              { simpl; constructor; auto. }
              intros (_ & Hids); specialize (Hids e0); clarify. }
            destruct (eq_dec i (length m1)).
            + subst; rewrite nth_error_split in Hr0; clarify.
              unfold reads in Hreads; rewrite He, filter_In in Hreads; clarify.
              exploit Hseq.
              { apply nth_error_split. }
              { unfold reads; eauto. }
              clear Hseq; intro Hseq.
              rewrite firstn_app, firstn_length, minus_diag, app_nil_r in *.
              rewrite Hid; destruct (find (fun e => if find_mod (op e) p0
                then true else false) (rev m1)) eqn: Hfind; clarify.
              split; eauto.
              assert (reads (op r) p0 v0).
              { unfold reads; rewrite He, filter_In; auto. }
              rewrite <- Hid in *; rewrite drop_rf; eauto; clarify;
              (* Really, drop_rf is still wrong. Each rf edge needs to be
                 associated with a location, and we need to be able to drop
                 only the ones for dropped reads. But this is irrelevant until
                 we have multi-read ops. *)
                rewrite Union_spec, Setminus_spec; clarify; left.
              exploit find_success; eauto; rewrite <- in_rev; intros (? & _).
              rewrite (lin_set Hlin), in_app; clarify.
              intro; clarify.
              rewrite NoDup_app in Hnodup; clarify.
              exploit Hnodup22; eauto.
            + rewrite <- drop_nth_error in Hr0; auto.
              specialize (Hseq i); rewrite <- drop_nth_error in Hseq; auto.
              specialize (Hseq _ _ _ Hr0 Hreads).
              destruct (find (fun e0 => if find_mod (op e0) p0 then true
                else false) (rev (firstn i (m1 ++ e :: m2)))) eqn: Hfind;
                clarify.
              assert (events E r /\ r <> e).
              { exploit nth_error_in; eauto; intro; split.
                * rewrite (lin_set Hlin); rewrite in_app in *; clarify.
                * intro; clarify. }
              destruct (lt_dec i (length m1)).
              * rewrite firstn_app, not_le_minus_0, app_nil_r in *; try omega.
                clarify.
                rewrite drop_rf; eauto; clarify; [split; eauto| |];
                  rewrite Union_spec, Setminus_spec; left; clarify;
                  [|intro; clarify].
                exploit find_success; eauto; rewrite <- in_rev; intros (? & _).
                exploit firstn_in; eauto; intro.
                rewrite (lin_set Hlin), in_app; clarify.
                intro; clarify.
                rewrite NoDup_app in Hnodup; clarify.
                exploit Hnodup22; eauto.
              * rewrite firstn_app, firstn_length' in *; try omega.
                destruct (i - length m1) eqn: Hminus; [omega | clarify].
                rewrite rev_app_distr in *; clarify.
                rewrite <- app_assoc in *; simpl in *.
                rewrite find_app in *.
                destruct (find (fun e => if find_mod (op e) p0 then true
                  else false) (rev (firstn n1 m2))) eqn: Hfind'; clarify.
                { rewrite drop_rf; eauto; clarify; [split; eauto| |];
                    rewrite Union_spec, Setminus_spec; left; clarify;
                    [|intro; clarify].
                  exploit find_success; eauto; rewrite <- in_rev;
                    intros (? & _).
                  exploit firstn_in; eauto; intro.
                  rewrite (lin_set Hlin), in_app; clarify.
                  intro; clarify.
                  rewrite NoDup_app in Hnodup; clarify.
                  inversion Hnodup21; clarify. }
                rewrite He, find_filter.
                destruct (find_mod (op e) p0); clarify.
                { rewrite <- Hid in *; rewrite drop_rf; eauto; clarify;
                    [split; eauto| |];
                    try rewrite Union_spec, Setminus_spec; clarify.
                  * rewrite He; exists x0; clarify.
                    rewrite <- last_op_filter in Hseq21;
                      rewrite <- last_op_filter, filter_filter_1; auto.
                    rewrite Forall_forall; intros a ?; destruct a; clarify.
                  * left; clarify; intro; clarify. }
                { rewrite drop_rf; eauto; clarify; [split; eauto| |];
                    rewrite Union_spec, Setminus_spec; left; clarify;
                    [|intro; clarify].
                  exploit find_success; eauto; rewrite <- in_rev;
                    intros (? & _).
                  rewrite (lin_set Hlin), in_app; clarify.
                  intro; clarify.
                  rewrite NoDup_app in Hnodup; clarify.
                  exploit Hnodup22; eauto. }
                { clear; intro a; destruct a; clarify. } }
        * exploit before_lin; try apply Hlin; eauto.
          { admit. (* decidability of full *) }
          { apply clos_trans_trans. }
          intros (m1' & ? & Hm1' & ?); exists m1'; clarify.
          exploit Hseq; eauto.
          { apply nth_error_split. }
          rewrite firstn_app, firstn_length, minus_diag, app_nil_r.
          destruct (find (fun e => if find_mod (op e) p then true
            else false) (rev m1)) eqn: Hfind; clarify.
          erewrite (same_find _ _ Hlin); eauto; clarify.
          split; eauto; intros.
          rewrite Union_spec, Subtract_spec in Hr'; destruct Hr'.
          { exploit find_success; eauto; rewrite <- in_rev; intros (? & _).
            exploit in_nth_error; eauto; intros (i & ? & Hi).
            assert (events E e0) by (rewrite (lin_set Hlin), in_app; auto).
            assert (nth_error (m1 ++ e :: m2) i = Some e0)
              by (rewrite nth_error_app; clarify).
            clarify; exploit (lin_order_1(e1 := e0) Hlin i r'); auto.
            { apply t_step; repeat eexists; auto; left; auto. }
            intros (i' & Hi' & ?).
            exploit last_mods; eauto; intro.
            exploit Hseq; eauto.
            destruct (find (fun e => if find_mod (op e) p then true else false)
              (rev (firstn i' (m1 ++ e :: m2)))) eqn: Hfind'; intro Hw; clarify.
            exploit find_success; eauto; rewrite <- in_rev; intros (? & _).
            exploit firstn_in; eauto; intro.
            rewrite <- (lin_set Hlin) in *.
            exploit (race_free_mods_mods(p := p) e0 e1 Hrf); auto.
            { eapply last_mods; eauto. }
            intros [? | [? | ?]]; subst; eauto.
            rewrite find_spec in Hfind'; clarify.
            exploit nth_error_rev'; eauto; intro Hi2.
            rewrite nth_error_firstn in *; clarify.
            exploit (lin_order_3(e2 := e0) Hlin _ i Hi2); eauto.
            { apply t_step; repeat eexists; auto; left; auto. }
            intro.
            exploit (Hfind'22 (length (firstn i' (m1 ++ e :: m2)) - i - 1)).
            { apply minus_reverse; auto.
              * generalize (nth_error_lt _ _ Hfind'1); rewrite rev_length; auto.
              * rewrite List.firstn_length.
                apply NPeano.Nat.min_glb_lt; auto.
                rewrite app_length; omega. }
            { apply nth_error_rev; rewrite nth_error_firstn; clarify; eauto. }
            { generalize (mods_spec (op e0) p); clarify. } }
          { exploit drop_ids; eauto.
            { simpl; constructor; auto. }
            intros (_ & Hids).
            exploit Hids; eauto; intros (? & ? & Hid); clarify.
            rewrite Hid; auto. }
          { eapply Hrf; eauto; eapply mods_touches; eauto. }
      + eapply valid_no_reads; eauto.
        repeat intro.
        rewrite find_fail in Hfind; unfold linearization in Hlin; clarify.
        rewrite Hlin1 in *.
        rewrite Forall_rev, Forall_forall in Hfind; specialize (Hfind e).
        exploit reads_has_read; eauto; clarify.
  Qed.
        
  Definition race_candidate a b := exists op1 op2, In op1 (to_seq a) /\
    In op2 (to_seq b) /\ ~independent (loc_of op1) (loc_of op2) /\
    (not_read op1 = true \/ not_read op2 = true).

  Fixpoint find_race_candidate_aux a l :=
    match l with
    | [] => false
    | op :: rest => (if indep_dec _ (loc_of a) (loc_of op) then false else
        (not_read a || not_read op)) || find_race_candidate_aux a rest
    end.

  Fixpoint find_race_candidate l1 l2 :=
    match l1 with
    | [] => false
    | op1 :: rest =>
        find_race_candidate_aux op1 l2 || find_race_candidate rest l2
    end.

  Lemma race_candidate_aux_spec : forall a l,
    find_race_candidate_aux a l = true <-> exists op, In op l /\
      ~independent (loc_of a) (loc_of op) /\
      (not_read a = true \/ not_read op = true).
  Proof.
    induction l; [split|]; clarify.
    destruct (find_race_candidate_aux a l).
    - destruct IHl; split; clarsimp; eexists; eauto.
    - split; unfold beq in *; clarsimp; eauto.
      destruct IHl as [_ Hfalse]; destruct H1; clarsimp.
      use Hfalse; clarify; eauto.
  Qed.

  Lemma race_candidate_spec : forall l1 l2, 
    find_race_candidate l1 l2 = true <->
    exists op1 op2, In op1 l1 /\ In op2 l2 /\
      ~independent (loc_of op1) (loc_of op2) /\
      (not_read op1 = true \/ not_read op2 = true).
  Proof.
    induction l1; [split|]; clarify.
    destruct (find_race_candidate_aux a l2) eqn: Haux; clarify.
    - rewrite race_candidate_aux_spec in Haux; split; clarify.
      do 3 eexists; eauto.
    - rewrite IHl1; split; clarify; do 3 eexists; eauto; clarify.
      assert (find_race_candidate_aux x l2 = true)
        by (rewrite race_candidate_aux_spec; eauto); clarify.
  Qed.

  Corollary race_candidate_dec : forall a b, race_candidate a b \/
    ~race_candidate a b.
  Proof.
    intros; unfold race_candidate.
    destruct (find_race_candidate (to_seq a) (to_seq b)) eqn: Hrace.
    - rewrite race_candidate_spec in Hrace; auto.
    - right; intro; rewrite <- race_candidate_spec in *; clarify.
  Qed.

  Definition race X e1 e2 := race_candidate (op e1) (op e2) /\
    ~hb X (id e1) (id e2) /\ id e1 <> id e2 /\ ~hb X (id e2) (id e1).

  Variables (program : Type) (sem : program -> execution -> Prop).

  Lemma race_free_incl : forall E X S (Hrf : race_free E X)
    (Hincl : Included S E), race_free S X.
  Proof.
    unfold race_free; clarify.
    eapply Hrf; eauto; apply Hincl; auto.
  Qed.

  Corollary race_free_sub : forall E X S (Hrf : race_free E X),
    race_free (Setminus E S) X.
  Proof. intros; eapply race_free_incl; eauto; apply minus_sub. Qed.
  
  Lemma incl_union_mono_l : forall A (S1 S2 S3 : Ensemble A)
    (Hincl : Included S1 S2), Included (Union S1 S3) (Union S2 S3).
  Proof.
    repeat intro.
    inversion H; clarify.
    - apply Union_introl, Hincl; auto.
    - apply Union_intror; auto.
  Qed.

  Lemma hb_dec' : forall E X l (Hlin : linearization E (hb X) l) e1 e2
    (He1 : E e1) (He2 : E e2),
    hb X (id e1) (id e2) \/ ~hb X (id e1) (id e2).
  Proof.
    intros.
    specialize (hb_dec _ Hlin (id e1) (id e2)).
    rewrite (lin_set Hlin) in *.
    do 2 (use hb_dec; [|rewrite in_map_iff; eauto]).
    destruct hb_dec; auto.
  Qed.

  Lemma race_dec : forall E X l (Hlin : linearization E (hb X) l)
    e1 e2 (He1 : E e1) (He2 : E e2), race X e1 e2 \/ ~race X e1 e2.
  Proof.
    unfold race; intros.
    destruct (race_candidate_dec (op e1) (op e2)); [|right; intro; clarify].
    destruct (hb_dec' _ Hlin _ _ He1 He2); [right; intro; clarify|].
    destruct (hb_dec' _ Hlin _ _ He2 He1); [right; intro; clarify|].
    destruct (eq_dec (id e1) (id e2)); [right; intro; clarify | auto].
  Qed.

  Lemma race_free_alt : forall E X l (Hlin : linearization E (hb X) l),
    race_free E X <-> forall e1 e2 (He1 : E e1) (He2 : E e2), ~race X e1 e2.
  Proof.
    intros; unfold race_free; split; intro Hrf; intros.
    - unfold race, race_candidate; intro Hrace; clarify.
      assert (exists p, touches (op e1) p /\ touches (op e2) p /\
        (mods (op e1) p \/ mods (op e2) p)) as (p & ?).
      { destruct (loc_of x) eqn: Hx, (loc_of x0) eqn: Hx0; clarify.
        + exists p; destruct (eq_dec p p0); clarify.
          split; [exists x; rewrite Hx; auto|].
          split; [exists x0; rewrite Hx0; auto|].
          destruct Hrace1222; [left; exists x; destruct x |
            right; exists x0; destruct x0]; clarify;
            [inversion Hx | inversion Hx0]; clarify.
        + exists p; destruct p as (b0, ?); destruct (eq_dec b0 b); clarify.
          split; [exists x; rewrite Hx; auto|].
          split; [exists x0; rewrite Hx0; auto|].
          right; exists x0; destruct x0; clarify; inversion Hx0; clarify.
        + exists p; destruct p as (b0, ?); destruct (eq_dec b b0); clarify.
          split; [exists x; rewrite Hx; auto|].
          split; [exists x0; rewrite Hx0; auto|].
          left; exists x; destruct x; clarify; inversion Hx; clarify.
        + exists (b, 0); destruct (eq_dec b b0); clarify.
          split; [exists x; rewrite Hx; auto|].
          split; [exists x0; rewrite Hx0; auto|].
          left; exists x; destruct x; clarify; inversion Hx; clarify. }
      specialize (Hrf e1 e2 p); clarify.
    - specialize (Hrf _ _ He1 He2).
      destruct (hb_dec' _ Hlin _ _ He1 He2); auto.
      destruct (hb_dec' _ Hlin _ _ He2 He1); auto.
      destruct (lin_e_eq Hlin _ _ He1 He2); auto.
      destruct (eq_dec (id e1) (id e2));
        [exploit lin_id_inj; try (apply e); eauto|].
      contradiction Hrf; unfold race, race_candidate; clarify.
      unfold mods in Hmods; destruct Hmods; clarify.
      + rewrite op_modifies_spec in *; clarify.
        unfold touches in Hp2; clarify.
        generalize (not_indep_trans _ (loc_of x) _ Hp22); clarify.
        do 3 eexists; eauto; split; eauto; clarify.
        intro Hindep; symmetry in Hindep; auto.
      + rewrite op_modifies_spec in *; clarify.
        unfold touches in Hp1; clarify.
        generalize (not_indep_trans _ (loc_of x) _ Hp12); clarify.
        do 3 eexists; eauto.
  Qed.
  
  Instance race_candidate_sym : Symmetric race_candidate.
  Proof.
    unfold race_candidate; repeat intro; clarify.
    do 3 eexists; eauto; split; eauto.
    split; clarify; intro Hindep; symmetry in Hindep; auto.
  Qed.

  Instance race_sym X : Symmetric (race X).
  Proof.
    unfold race; repeat intro; clarify.
    symmetry; auto.
  Qed.
  
  Lemma add_race_dec : forall l E X e (Hrf : race_free E X)
    (Hout : ~E e) (Hlin : linearization (Add E e) (hb X) l),
    race_free (Add E e) X \/ ~race_free (Add E e) X.
  Proof.
    intros.
    assert (exists l1 l2, l = l1 ++ e :: l2) as (l1 & l2 & ?); clarify.
    { unfold linearization in Hlin; clarify.
      specialize (Hlin1 e); rewrite Add_spec in Hlin1; destruct Hlin1; clarify.
      eapply in_split; auto. }
    exploit lin_remove; eauto; intros [_ Hlin'].
    rewrite Subtract_Add in Hlin'; auto.
    remember (l1 ++ l2) as l; generalize dependent l2; revert l1.
    generalize dependent E; induction l; clarify.
    { destruct l1; clarify.
      left; unfold linearization, race_free in *; clarify.
      rewrite Hlin1 in *; clarify. }
    generalize (lin_cons_inv Hlin'); intro Hlin''.
    specialize (IHl (Subtract E a)).
    use IHl; [|apply race_free_sub; auto].
    simpl in IHl; setoid_rewrite Setminus_spec in IHl; use IHl;
      [|intro]; clarify.
    assert (E a).
    { unfold linearization in Hlin'; clarify.
      specialize (Hlin'1 a); destruct Hlin'1; clarify. }
    assert (a <> e) by (intro; clarify).
    assert (linearization (Add (Subtract E a) e) (hb X)
      (skipn 1 l1 ++ e :: if nil_dec l1 then skipn 1 l2 else l2)) as Hlin0.
    { destruct l1; clarify.
      + assert (e :: a :: l = [e] ++ a :: l) as Heq by clarify.
        rewrite Heq in Hlin; generalize (lin_remove _ _ _ Hlin); clarify.
        rewrite Add_Subtract_comm; auto; intro; subst.
      + generalize (lin_cons_inv Hlin); rewrite Add_Subtract_comm; auto. }
    specialize (IHl _ _ Hlin0); use IHl.
    destruct IHl as [IHl | IHl].
    - assert ((Add E e) a) as Ha.
      { unfold linearization in Hlin; clarify.
        rewrite Hlin1; destruct l1; clarify. }
      assert ((Add E e) e) as He.
      { rewrite Add_spec; auto. }
      destruct (race_dec _ Hlin _ _ Ha He); [right | left].
      + rewrite race_free_alt; eauto.
      + rewrite race_free_alt in *; eauto; intros.
        setoid_rewrite Add_spec in He1; setoid_rewrite Add_spec in He2;
          destruct He1, He2; auto; subst.
        * destruct (lin_e_eq Hlin e1 a); clarify.
          { rewrite Add_spec; auto. }
          apply IHl; clarify.
          { rewrite Add_spec, Subtract_spec; clarify. }
          { rewrite Add_spec; auto. }
        * destruct (lin_e_eq Hlin e2 a); clarify.
          { rewrite Add_spec; auto. }
          { intro Hr; symmetry in Hr; auto. }
          apply IHl; clarify.
          { rewrite Add_spec; auto. }
          { rewrite Add_spec, Subtract_spec; clarify. }
        * unfold race; intro; clarify.
    - right; intro Hrf'; contradiction IHl.
      generalize (race_free_incl(S := Add (Subtract E a) e) Hrf');
        intro Hrf''; apply Hrf''.
      apply incl_union_mono_l, minus_sub.
    - destruct l1; clarify.
  Qed.

  Lemma add_race_dec' : forall l (E : Ensemble event) X e (Hin : E e)
    (Hrf : race_free (Subtract E e) X) (Hlin : linearization E (hb X) l),
    race_free E X \/ ~race_free E X.
  Proof.
    intros.
    assert (exists l1 l2, l = l1 ++ e :: l2) as (l1 & l2 & ?); clarify.
    { unfold linearization in Hlin; clarify.
      rewrite Hlin1 in Hin; eapply in_split; auto. }
    exploit lin_remove; eauto; intros [_ Hlin'].
    remember (l1 ++ l2) as l; generalize dependent l2; revert l1.
    generalize dependent E; induction l; clarify.
    { destruct l1; clarify.
      left; unfold linearization, race_free in *; clarify.
      rewrite Hlin1 in *; clarify. }
    generalize (lin_cons_inv Hlin'); intro Hlin''.
    specialize (IHl (Subtract E a)).
    assert (E a /\ a <> e) as [Ha ?].
    { unfold linearization in Hlin'; clarify.
      specialize (Hlin'1 a); destruct Hlin'1; clarify. 
      rewrite Subtract_spec in *; clarify. }
    simpl in IHl; rewrite Subtract_spec in IHl; clarify.
    use IHl.
    rewrite Subtract_comm in IHl; clarify.
    assert (linearization (Subtract E a) (hb X)
      (skipn 1 l1 ++ e :: if nil_dec l1 then skipn 1 l2 else l2)) as Hlin0.
    { destruct l1; clarify.
      + assert (e :: a :: l = [e] ++ a :: l) as Heq by clarify.
        rewrite Heq in Hlin; generalize (lin_remove _ _ _ Hlin); clarify.
      + apply lin_cons_inv; auto. }
    specialize (IHl _ _ Hlin0); use IHl.
    destruct IHl as [IHl | IHl].
    - destruct (race_dec _ Hlin _ _ Ha Hin); [right | left].
      + rewrite race_free_alt; eauto.
      + rewrite race_free_alt in *; eauto; intros.
        destruct (lin_e_eq Hlin e1 e), (lin_e_eq Hlin e2 e); auto;
          subst.
        * unfold race; intro; clarify.
        * destruct (lin_e_eq Hlin e2 a); clarify.
          { intro Hr; symmetry in Hr; auto. }
          apply IHl; rewrite Subtract_spec; auto.
        * destruct (lin_e_eq Hlin e1 a); clarify.
          apply IHl; rewrite Subtract_spec; auto.
        * apply Hrf; simpl; rewrite Subtract_spec; auto.
    - right; intro Hrf'; contradiction IHl.
      eapply race_free_incl; eauto; apply minus_sub.
    - destruct l1; clarify.
    - generalize (race_free_incl(S := Subtract (Subtract E a) e) Hrf);
        intro Hrf'; apply Hrf'.
      simpl; rewrite Subtract_comm; apply minus_sub.
  Qed.

(*  Lemma writes_last : forall c p v (Ha : In (MWrite p v) (to_seq c)),
    last_op (to_seq c) (Ptr p) (MWrite p v).
  Proof.
    intros.
    exploit in_split; eauto; intros (l1 & l2 & Heq).
    rewrite Heq, split_app, last_op_app; right.
    split.
    - rewrite last_op_app; left.
      exists 0; clarify.
      econstructor; clarify.
      destruct j; clarsimp.
    - rewrite Forall_forall; intros.
      destruct (op_modifies _ x p) eqn: Hmods'.
      + exploit in_nth_error; eauto; intros (i' & ? & ?).
        exploit write_after_mod; eauto.
        { setoid_rewrite Heq; apply nth_error_split. }
        { instantiate (1 := length l1 + S i').
          rewrite Heq, nth_error_plus; auto. }
        omega.
      + destruct x; clarify.
  Qed.*)

  Fixpoint replace_reads (la : list mem_op) lv :=
    match la with
    | [] => []
    | MRead p v :: rest => match lv with [] => la | v' :: restv =>
        MRead p v' :: replace_reads rest restv end
    | a :: rest => a :: replace_reads rest lv
    end.

  Hypothesis reads_op : forall c lv, exists c',
    to_seq c' = replace_reads (to_seq c) lv /\
    forall P E (Hsem : sem P E) X (Hvalid : valid E X)
    l r (Hlin : linearization (events E) (full (events E) X) (l ++ [r]))
    (Hr : op r = c),
    sem P (upd_events E (Add (Subtract (events E) r)
          {| id := id r; op := c' |})) /\
    well_formed (upd_events E (Add (Subtract (events E) r)
          {| id := id r; op := c' |})) X.
  (* In other words, if we have an op that contains a read, we should be able
     to swap in a read of any other value. *)
  (* This is actually a bit like drop_l_reads, and perhaps could be treated
     similarly. *)

  Lemma read_recent : forall m l
    (Hread : forall p v (Hread : In (MRead p v) l), exists w, In w m /\
       mods (op w) p),
    exists lv, forall p v (Hread : In (MRead p v) (replace_reads l lv)),
      match find (fun e => if find_mod (op e) p then true else false) (rev m)
      with Some w => exists a, last_op (to_seq (op w)) (Ptr p) a /\
                               match_op a v | None => False end.
  Proof.
    induction l; clarify.
    { exists []; clarify. }
    destruct (not_read a) eqn: Ha.
    - use IHl; eauto; clarify.
      exists x; intros.
      apply IHl; destruct a; clarify.
    - destruct a; clarify.
      generalize (Hread _ _ (or_introl eq_refl)); clarify.
      use IHl; [destruct IHl as (lv & IHl) | eauto].
      destruct (find (fun e => if find_mod (op e) p then true else false)
        (rev m)) eqn: Hfind.
      exploit find_success; eauto; intros (He & Hmods); clarify.
      rewrite find_spec in cond; clarify.
      exploit (has_last_op' (to_seq (op e)) (Ptr p)); eauto 2.
      { destruct m0; clarify. }
      { destruct m0; clarify. }
      intros (a & Ha).
      exploit last_op_mods; eauto; destruct a; clarify.
      + exists (v0 :: lv); clarify.
        destruct Hread0; [|apply IHl; auto].
        inversion H; clarify.
        do 2 eexists; eauto; clarify.
      + exists (err :: lv); clarify.
        inversion Hread0; [|apply IHl; auto].
        inversion H; clarify.
        do 2 eexists; eauto; clarify.
      + exists (err :: lv); clarify.
        inversion Hread0; [|apply IHl; auto].
        inversion H; clarify.
        do 2 eexists; eauto; clarify.
      + rewrite find_fail, Forall_forall in Hfind.
        generalize (mods_spec (op x) p).
        rewrite in_rev in *; exploit Hfind; eauto; clarify.
  Qed.

  Lemma rf_reads_snoc : forall E X l x (Hwf : rf_reads E X)
    (Hlin : linearization E (rf X) (l ++ [x])),
    rf_reads (Subtract E x) X.
  Proof.
    repeat intro; clarify.
    rewrite Subtract_spec in *; specialize (Hwf e); clarify.
    specialize (Hwf _ _ Hread); destruct Hwf as [w Hw]; exists w; clarify.
    rewrite Subtract_spec; split; clarify.
    { intro; subst.
      eapply lin_order; eauto; clarify.
      unfold linearization in *; clarify.
      rewrite Hlin1, in_app in He1; clarify. }
  Qed.

  Lemma lin_union : forall E R l1 l2 (Hlin : linearization E R (l1 ++ l2)),
    E = Union (set_of l1) (set_of l2).
  Proof.
    intros; apply set_ext; intro; rewrite (lin_set Hlin), in_app, Union_spec;
      reflexivity.
  Qed.

  Lemma lin_ids : forall l0 R l (Hlin : linearization (set_of l0) R l) i,
    In i (map id l) <-> In i (map id l0).
  Proof.
    intros; repeat rewrite in_map_iff.
    setoid_rewrite (lin_set Hlin); reflexivity.
  Qed.

  Lemma lin_replace : forall E R l1 l2 (Hlin : linearization E R (l1 ++ l2))
    l1' (Hlin' : linearization (set_of l1) R l1'),
    linearization E R (l1' ++ l2).
  Proof.
    intros.
    setoid_rewrite lin_union; eauto.
    apply lin_combine; auto.
    - eapply lin_app2; eauto.
    - intro; rewrite lin_ids; eauto.
      unfold linearization in Hlin; rewrite map_app, NoDup_app in Hlin; clarify.
    - intros ??; rewrite lin_ids; eauto.
      repeat rewrite in_map_iff; clarify; eapply lin_split; eauto.
  Qed.

  Hypothesis sem_prefix : forall P E (Hsem : sem P E) X (Hvalid : valid E X)
    l1 l2 (Hlin : linearization (events E) (full (events E) X) (l1 ++ l2)),
    sem P (upd_events E (set_of l1)).

  Lemma replace_not_reads : forall l lv, filter not_read (replace_reads l lv) =
    filter not_read l.
  Proof.
    induction l; clarify.
    destruct a; clarify; try rewrite IHl; auto.
    destruct lv; clarify.
  Qed.

  Lemma replace_in : forall a la lv (Hin : In a (replace_reads la lv)),
    match a with MRead p _ => exists v', In (MRead p v') la | _ => In a la end.
  Proof.
    induction la; clarify.
    destruct (in_dec mem_op_eq a (replace_reads la lv)).
    - exploit IHla; eauto; destruct a; clarify; eauto.
    - destruct a0; clarify.
      destruct lv; clarify.
      + destruct Hin; clarify; eauto.
        destruct a; clarify; eauto.
      + destruct Hin; clarify; eauto.
        exploit IHla; eauto; destruct a; clarify; eauto.
  Qed.

  Lemma replace_in' : forall a la lv (Hin : In a la),
    match a with MRead p _ => exists v', In (MRead p v') (replace_reads la lv)
    | _ => In a (replace_reads la lv) end.
  Proof.
    induction la; clarify.
    destruct Hin; clarify.
    - destruct a; clarify.
      destruct lv; clarify; eauto.
    - generalize (IHla lv); destruct a0; clarify;
        try solve [destruct a; clarify; eauto].
      destruct lv; clarify; eauto; destruct a; clarify; eauto.
      specialize (IHla lv); clarify; eauto.
  Qed.

  Lemma replace_touches : forall b c c' lv
    (Hreplace : to_seq c' = replace_reads (to_seq c) lv),
    touches c' b <-> touches c b. 
  Proof.
    unfold touches; split; clarify; rewrite Hreplace in *.
    - exploit replace_in; eauto; destruct x; clarify; eauto.
    - exploit replace_in'; eauto; destruct x; clarify; eauto.
  Qed.    

  Lemma replace_mods : forall p c c' lv
    (Hreplace : to_seq c' = replace_reads (to_seq c) lv),
    mods c' p <-> mods c p.
  Proof.
    unfold mods; split; clarify; rewrite Hreplace in *.
    - exploit replace_in; eauto; destruct x; clarify; do 2 eexists; eauto 2;
        clarify.
    - exploit replace_in'; eauto; destruct x; clarify; do 2 eexists; eauto 2;
        clarify.
  Qed.

  Lemma full_lin_cont : forall E X S (Hsub : Included S E)
    i j (Hfull : full S X i j), full E X i j.
  Proof.
    intros; induction Hfull; clarify.
    - destruct H as (? & e1 & e2 & He); clarify.
      apply t_step; repeat eexists; auto; apply Hsub; auto.
    - eapply t_trans; eauto.
  Qed.

  Lemma full_lin_app : forall E X l1 l2
    (Hlin : linearization E (full E X) (l1 ++ l2)),
    linear (full (set_of l1) X) l1.
  Proof.
    intros; exploit lin_app; eauto; intro Hlin'.
    unfold linearization in *; clarify.
    apply Hlin'22; auto.
    eapply full_lin_cont; eauto.
    repeat intro; setoid_rewrite Hlin1; rewrite in_app; auto.
  Qed.

  Lemma full_id : forall E X e e' (Hid : id e = id e') i j
    (Hfull : full (Add E e) X i j), full (Add E e') X i j.
  Proof.
    intros; induction Hfull.
    - destruct H as (? & e1 & e2 & He); clarify.
      apply t_step; split; auto.
      rewrite Add_spec in *; setoid_rewrite Add_spec; destruct He1, He21; subst.
      + repeat eexists; eauto.
      + exists e1, e'; auto.
      + exists e', e2; auto.
      + exists e', e'; auto.
    - eapply t_trans; eauto.
  Qed.

  Lemma conjI2 : forall (P1 P2 : Prop), (P2 -> P1) -> P2 -> P1 /\ P2.
  Proof. auto. Qed.

  Lemma lin_full : forall E X l (Hhb_lin : linearization E (hb X) l)
    (Hrf_lin : linearization E (rf X) l), linearization E (full E X) l.
  Proof.
    unfold linearization; clarify.
    remember (id e1) as i; remember (id e2) as j; generalize dependent e2;
      generalize dependent e1; induction Horder; clarify.
    - destruct H as ([? | ?] & ?); clarify.
    - exploit full_in2; eauto; intros (e3 & ? & ?).
      specialize (IHHorder1 _ He1 eq_refl e3); clarify.
      specialize (IHHorder2 e3); clarify.
      specialize (IHHorder2 _ He2 eq_refl); clarify.
      exploit lin_nodup.
      { split; [|split]; eauto. }
      intro Hnodup; generalize (NoDup_inj _ _ Hnodup IHHorder21 IHHorder121);
        clarify.
      do 3 eexists; eauto; split; eauto; omega.
  Qed.

  (* transfering linearizations *)
  Fixpoint drop_lin (ops ops' : list event) l :=
    match l with
    | [] => []
    | a :: rest =>
        match find (fun e => beq (id e) (id a)) ops with
        | Some e =>
            match find (fun e' => beq (id e') (id a)) ops' with
            | Some e' => e' :: drop_lin ops ops' rest
            | None => drop_lin ops ops' rest
            end
        | None => a :: drop_lin ops ops' rest
        end
    end.

  Lemma drop_nil : forall l, drop_lin [] [] l = l.
  Proof.
    induction l; clarsimp.
  Qed.    

  Lemma drop_lin_snoc : forall ops ops' l a, drop_lin ops ops' (l ++ [a]) =
    drop_lin ops ops' l ++ match find (fun e => beq (id e) (id a)) ops with
      | Some e =>
          match find (fun e' => beq (id e') (id a)) ops' with
          | Some e' => [e']
          | None => []
          end
      | None => [a]
      end.
  Proof.
    induction l; clarify.
    rewrite IHl; destruct (find (fun e => beq (id e) (id a)) ops); clarify.
    destruct (find (fun e' => beq (id e') (id a)) ops'); clarify.
  Qed.

  Lemma drop_lin_mono : forall ops1 ops1' ops2 ops2' l
    (Heq : Forall (fun a => find (fun e => beq (id e) (id a)) ops1 =
       find (fun e => beq (id e) (id a)) ops2 /\
       find (fun e => beq (id e) (id a)) ops1' =
       find (fun e => beq (id e) (id a)) ops2') l),
    drop_lin ops1 ops1' l = drop_lin ops2 ops2' l.
  Proof.
    induction l; clarify.
    inversion Heq; clarsimp.
  Qed.

  Lemma drop_lin_set : forall l ops ops'
    (Hsub : Included (set_of ops) (set_of l))
    (Hids : forall e, In e ops' -> exists e', In e' ops /\ id e = id e')
    (Hnodup : NoDup (map id l)) (Hnodup' : NoDup (map id ops')),
    set_of (drop_lin ops ops' l) = Union (Setminus (set_of l) (set_of ops))
      (set_of ops').
  Proof.
    induction l; clarify; apply set_ext; intro.
    - rewrite Union_spec, Setminus_spec; split; clarify.
      specialize (Hids e); clarify.
      specialize (Hsub _ Hids1); clarify.
    - inversion Hnodup as [|?? Hout Hnodup1]; clarify.
      rewrite in_map_iff in Hout.
      specialize (IHl (filter (fun e => negb (beq (id e) (id a))) ops)
        (filter (fun e => negb (beq (id e) (id a))) ops')).
      rewrite (drop_lin_mono _ _ ops ops') in IHl.
      use IHl.
      use IHl; clarify.
      use IHl.
      rewrite Union_spec, Setminus_spec.
      destruct (find (fun e => beq (id e) (id a)) ops) eqn: Hfind.
      + generalize (find_success _ _ Hfind); intros [He Hide].
        specialize (Hsub _ He); unfold Ensembles.In in *; clarify.
        destruct Hsub;
          [subst | contradiction Hout; unfold beq in *; clarify; eauto].
        destruct (find (fun e' => beq (id e') (id e0)) ops') eqn: Hfind'.
        * generalize (find_success _ _ Hfind'); clarify.
          rewrite IHl, Union_spec, Setminus_spec; split; intro Hx; clarify.
          { unfold set_of in *; repeat rewrite filter_In in Hx; clarify.
            left; clarify.
            intro; contradiction Hx2; unfold negb, beq; clarify; eauto. }
          { setoid_rewrite filter_In.
            destruct Hx; [right; left|]; clarify.
            { intro; clarify. }
            destruct (eq_dec (id e) (id e0)); unfold negb, beq in *; clarify.
            generalize (NoDup_id_inj _ e e1 Hnodup'); clarsimp. }
        * rewrite IHl, Union_spec, Setminus_spec; split; intro Hx; clarify.
          { unfold set_of in *; repeat rewrite filter_In in Hx; clarify.
            left; clarify.
            intro; contradiction Hx2; unfold negb, beq; clarify; eauto. }
          { setoid_rewrite filter_In.
            destruct Hx; [left|]; clarify.
            { intro; clarify. }
            rewrite find_fail, Forall_forall in Hfind'; specialize (Hfind' e);
              unfold negb, beq in *; clarify. }            
      + rewrite find_fail, Forall_forall in Hfind.
        assert (~set_of ops a); clarify.
        { intro Hin; specialize (Hfind _ Hin); unfold beq in Hfind; clarify. }
        rewrite IHl, Union_spec, Setminus_spec; split; intros Hx; clarify.
        * unfold set_of in *; repeat rewrite filter_In in Hx; clarify.
          left; clarify.
          intro; contradiction Hx2; unfold negb, beq; clarify; eauto.
        * setoid_rewrite filter_In.
          destruct Hx; clarify.
          { right; left; clarify; intro; clarify. }
          specialize (Hids e); clarify.
          right; right; unfold negb, beq; clarify.
          specialize (Hfind _ Hids1); unfold beq in *; clarsimp.
      + erewrite (map_filter _ _ (fun i => negb (beq i (id a))));
          [|rewrite Forall_forall; auto].
        apply NoDup_filter; auto.
      + rewrite filter_In in *; setoid_rewrite filter_In; clarify.
        specialize (Hids e0); clarify.
        rewrite Hids2 in *; eauto.
      + intros e' Hin.
        setoid_rewrite filter_In in Hin; clarify.
        specialize (Hsub _ Hin1); unfold Ensembles.In, negb, beq in *;
          clarify.
      + rewrite Forall_forall; intros; repeat rewrite find_filter; auto;
          unfold negb, implb, beq; clarify; contradiction Hout;
          clear cond1; rewrite e in *; eauto.
  Qed.

  Corollary drop_lin_in : forall l ops ops'
    (Hsub : Included (set_of ops) (set_of l))
    (Hids : forall e, In e ops' -> exists e', In e' ops /\ id e = id e')
    (Hnodup : NoDup (map id l)) (Hnodup' : NoDup (map id ops')) e,
    In e (drop_lin ops ops' l) <->
      Union (Setminus (set_of l) (set_of ops)) (set_of ops') e.
  Proof. intros; rewrite <- drop_lin_set; auto; reflexivity. Qed.
  
  Lemma drop_lin_id_in : forall ops ops' l,
    Included (set_of (map id (drop_lin ops ops' l))) (set_of (map id l)).
  Proof.
    induction l; repeat intro; unfold Ensembles.In in *; clarify.
    destruct (find (fun e => beq (id e) (id a)) ops) eqn: Hfind.
    - generalize (find_success _ _ Hfind); intros [He Hide].
      destruct (find (fun e' => beq (id e') (id a)) ops') eqn: Hfind'.
      + generalize (find_success _ _ Hfind'); intros [He' Hide'].
        unfold beq in *; clarify.
        right; apply IHl; auto.
      + right; apply IHl; auto.
    - clarify.
      right; apply IHl; auto.
  Qed.

  Lemma drop_lin_ids : forall l (Hnodup : NoDup (map id l)) ops ops',
    NoDup (map id (drop_lin ops ops' l)).
  Proof.
    induction l; clarify.
    inversion Hnodup as [|?? Hout Hnodup']; clarify.
    destruct (find (fun e => beq (id e) (id a)) ops) eqn: Hfind.
    - generalize (find_success _ _ Hfind); intros [He Hide].
      destruct (find (fun e' => beq (id e') (id a)) ops') eqn: Hfind'; auto.
      generalize (find_success _ _ Hfind'); intros [He' Hide'].
      simpl; constructor; auto.
      rewrite in_map_iff; intro Hin; unfold beq in *; clarify.
      contradiction Hout; rewrite <- e1; eapply drop_lin_id_in.
      setoid_rewrite in_map_iff; eauto.
    - simpl; constructor; auto.
      rewrite in_map_iff; intro Hin; clarify.
      contradiction Hout; eapply drop_lin_id_in.
      setoid_rewrite in_map_iff; eauto.
  Qed.

  Lemma drop_lin_id : forall ops ops' l e (He : In e (drop_lin ops ops' l)),
    exists e', In e' l /\ id e = id e'.
  Proof.
    induction l; clarify.
    destruct (find (fun e => beq (id e) (id a)) ops) eqn: Hfind.
    destruct (find (fun e => beq (id e) (id a)) ops') eqn: Hfind'.
    - simpl in He; destruct He.
      + subst; exists a; clarify.
        exploit find_success; eauto; unfold beq; clarify.
      + exploit IHl; eauto; clarify; eauto.
    - exploit IHl; eauto; clarify; eauto.
    - simpl in He; destruct He; eauto.
      exploit IHl; eauto; clarify; eauto.
  Qed.
    
  Lemma drop_lin_ord : forall ops ops' l, let l' := drop_lin ops ops' l in
    forall i1 i2 e1 e2 (Hi1 : nth_error l' i1 = Some e1)
    (Hi2 : nth_error l' i2 = Some e2) (Hlt : i1 < i2),
    exists i1' i2' e1' e2', i1' < i2' /\ nth_error l i1' = Some e1' /\
      nth_error l i2' = Some e2' /\ id e1' = id e1 /\ id e2' = id e2.
  Proof.
    induction l; clarsimp.
    subst l'.
    assert (forall i1 i2 e1 e2, nth_error (drop_lin ops ops' l) i1 = Some e1 ->
        nth_error (drop_lin ops ops' l) i2 = Some e2 -> S i1 < S i2 ->
      exists i1' i2' e1' e2', i1' < i2' /\ nth_error (a :: l) i1' = Some e1' /\ 
        nth_error (a :: l) i2' = Some e2' /\ id e1' = id e1 /\ id e2' = id e2).
    { intros i1' i2' ?????; exploit (IHl i1' i2'); eauto.
      { omega. }
      intros (i1'' & i2'' & e1' & e2' & ?); exists (S i1''), (S i2''), e1', e2';
        clarify. }
    destruct (find (fun e => beq (id e) (id a)) ops) eqn: Hfind.
    - destruct (find (fun e => beq (id e) (id a)) ops') eqn: Hfind'; eauto.
      destruct i1, i2; try omega; clarify; eauto.
      exploit nth_error_in; eauto; intro.
      exploit drop_lin_id; eauto; intros (e2' & ? & ?).
      exploit in_nth_error; eauto; intros (i2' & ? & ?).
      exists 0, (S i2'), a, e2'; clarify.
      exploit find_success; eauto; unfold beq; clarify.
    - destruct i1, i2; try omega; clarify; eauto.
      exploit nth_error_in; eauto; intro.
      exploit drop_lin_id; eauto; intros (e2' & ? & ?).
      exploit in_nth_error; eauto; intros (i2' & ? & ?).
      exists 0, (S i2'), e1, e2'; clarify.
  Qed.

  Lemma full_cont : forall (E E' : Ensemble event) X (Hsub : Included E E'),
    contained (full E X) (full E' X).
  Proof.
    repeat intro.
    induction H.
    - apply t_step; destruct H; clarify.
      repeat eexists; auto; apply Hsub; auto.
    - eapply t_trans; eauto.
  Qed.

  Lemma lin_switch : forall E R l1 l2 e e' (Hout : ~E e)
    (Hlin : linearization (Add E e) R (l1 ++ e :: l2))
    (Hid : id e' = id e), linearization (Add E e') R (l1 ++ e' :: l2).
  Proof.
    intros.
    exploit lin_remove; eauto; intros (_ & Hlin').
    exploit (lin_add _ e' _ Hlin').
    - rewrite Hid; unfold linearization in Hlin; clarify.
      rewrite map_app, NoDup_app in Hlin21; clarify.
      inversion Hlin2121; intro Hin.
      rewrite in_map_iff in Hin; clarify.
      rewrite in_app in Hin2; destruct Hin2.
      + eapply Hlin2122; rewrite in_map_iff; eauto.
      + eapply H1; rewrite in_map_iff; eauto.
    - rewrite Hid; eapply (lin_irrefl Hlin).
      rewrite Add_spec; auto.
    - rewrite Hid; generalize (lin_split _ _ Hlin); intros Hafter ???.
      eapply Hafter; eauto; clarify.
    - rewrite Hid; generalize (lin_app2 _ _ Hlin); intros Hlin2 ???.
      exploit lin_cons_inv'; eauto; intros (_ & _ & Hafter).
      eapply Hafter; eauto.
    - replace (Add (Subtract (Add E e) e) e') with (Add E e'); auto.
      apply set_ext; intro; repeat rewrite Add_spec;
        rewrite Subtract_spec, Add_spec; split; clarify.
      left; clarify; intro; clarify.
  Qed.

(*  Hypothesis rf_switch_wf : forall E X (Hwf : well_formed E X)*)

  Lemma SC_race_base : forall (b0 : block) E X (Hvalid : valid E X)
    P (Hsem : sem P E)
    l rest (Hlin : linearization (events E) (full (events E) X) (l ++ rest))
    (Hreads : rf_reads (set_of l) X),
    race_free (set_of l) X /\ SC (upd_events E (set_of l)) X \/
    exists l1 X', sem P (upd_events E (set_of l1)) /\
      SC (upd_events E (set_of l1)) X' /\
      well_formed (upd_events E (set_of l1)) X' /\ ~race_free (set_of l1) X'.
  Proof.
    induction l using rev_ind; clarify.
    { left; split; [repeat intro; clarify|].
      repeat split; clarify.
      - apply valid_hb; auto.
      - repeat intro; clarify.
      - exists []; split; [apply lin_nil|]; clarify.
        (*split; [apply consistent_nil; auto | clarsimp].*)
        clarsimp. }
    specialize (IHl (x :: rest)); clarsimp.
    rewrite split_app in Hlin; exploit full_lin_app; eauto; intro Hlin1.
    generalize (full_lin Hlin1); eauto; intros [Hhb_lin Horder].
    generalize (rf_reads_snoc _ Hreads Horder); intro Hreads'.
    assert (~In x l).
    { generalize (lin_nodup Hlin1); rewrite NoDup_app; intros (_ & _ & Hnodup).
      intro Hin; eapply Hnodup; eauto; clarify. }
    assert (Subtract (set_of (l ++ [x])) x = set_of l) as Heq.
    { apply set_ext; intro; unfold set_of; rewrite Subtract_spec, in_app;
        split; clarify; intro; clarify. }
    rewrite Heq in *; use IHl.
    destruct IHl as [(Hrf & Hseq) | ?]; auto.
    assert (In x (l ++ [x])) as Hin by (rewrite in_app; clarify).
    rewrite <- Heq in Hrf.
    generalize (add_race_dec' Hin Hrf Hhb_lin); intros [Hrf' | Hrace];
      [left | right]; clarify.
    - exploit valid_prefix; eauto; intro Hvalid'.
      rewrite race_free_SC in Hvalid'; eauto; clarify.
    - destruct Hseq as (Hcont & Htrans & m & Hm & (*Hcon & *)Hseq).
      exploit (read_recent m (to_seq (op x))).
      { intros.
        specialize (Hreads _ Hin _ _ Hread); destruct Hreads as (w & Hw);
          exists w; clarify.
        setoid_rewrite in_app in Hw21; destruct Hw21; clarify.
        rewrite <- (lin_set Hm); auto. }
      intros (lv & Hlv).
      generalize (reads_op (op x) lv); intros (c' & Hc' & Hsem').
      exploit sem_prefix; eauto; intro.
      exploit Hsem'; eauto.
      { eapply valid_prefix; eauto. }
      unfold upd_events; simpl; intros (Hsem'' & Hwf').
      set (x' := {| id := id x; op := c' |}).
      assert (Add (Subtract (set_of (l ++ [x])) x) x' = set_of (l ++ [x'])) 
        as Heq'.
      { apply set_ext; intro; rewrite Add_spec, Subtract_spec;
          setoid_rewrite in_app; split; clarify.
        left; clarify; intro; clarify. }
      set (X' := {| hb := hb X; rf := fun i j => if eq_dec j (id x) then
        exists p v, reads c' p v /\
        match find (fun e => if find_mod (op e) p then true else false) (rev m) 
        with Some w => i = id w | None => False end
        else rf X i j |}).
      (* This should be some kind of atomic operation on rfs ("redirect x's
         reads to these writes") that is guaranteed to preserve wf. *)
      exists (l ++ [x']), X'; repeat split; try (exists (m ++ [x']); split);
        try solve [rewrite <- Heq'; auto]; simpl.
      + eapply transitive_on_sub'; [apply hb_trans; eauto|].
        setoid_rewrite in_app; setoid_rewrite (lin_set Hlin);
          repeat setoid_rewrite in_app; intros ? [? | ?]; eauto; clarify.
        exists x; clarify.
      + apply lin_full.
        * rewrite set_of_app, set_of_single in *.
          eapply lin_switch; eauto.
          generalize (full_lin Hm); clarify.
          eapply lin_replace; eauto.
        * simpl in *; split; [|split].
          { intro; rewrite set_of_app, <- (lin_set' Hm), Union_spec, in_app;
              reflexivity. }
          { rewrite map_app, NoDup_app; split;
              [unfold linearization in Hm; clarify|].
            split; [simpl; constructor; auto|].
            intro; rewrite lin_ids; eauto.
            unfold linearization in Horder; clarify.
            rewrite map_app, NoDup_app in Horder21; clarify. }
          intros.
          destruct (eq_dec (id e2) (id x)).
          destruct Horder0 as (p & v & Hread & Hlast).
          destruct (find (fun e => if find_mod (op e) p then true else false)
            (rev m)) eqn: Hfind; clarify.
          setoid_rewrite in_app in He2; destruct He2; clarify.
          { unfold linearization in Horder; clarify.
            rewrite map_app, NoDup_app in Horder21; clarify.
            exploit Horder2122; eauto; clarify.
            rewrite in_map_iff; eauto. }
          setoid_rewrite in_app in He1; destruct He1 as [He1 | He1]; clarify.
          setoid_rewrite (lin_set Hm) in He1; exploit in_nth_error; eauto;
            intros (i1 & ? & ?); exists i1, (length m).
          rewrite nth_error_app, nth_error_split; clarify.
          { rewrite find_spec in Hfind; destruct Hfind as (i' & ? & ?).
            exploit nth_error_rev'; eauto; intro.
            exploit nth_error_in; eauto.
            rewrite <- (lin_set Hm).
            generalize (lin_id_inj x e0 Horder); setoid_rewrite in_app;
              clarify. }
          { setoid_rewrite in_app in He2; destruct He2 as [He2 | ?]; [|clarify].
            setoid_rewrite in_app in He1; destruct He1 as [He1 | He1].
            { unfold linearization in Hm; clarify.
              specialize (Hm22 e1 e2); clarify.
              use Hm22; [|apply t_step; repeat eexists; auto; right; auto].
              destruct Hm22 as (i1 & i2 & Hi1 & Hi2 & ?); exists i1, i2.
              generalize (nth_error_lt _ _ Hi1), (nth_error_lt _ _ Hi2); intros.
              repeat rewrite nth_error_app; clarify. }
            { clarify.
              exploit in_nth_error; eauto; intros (i2 & ? & Hi2).
              exploit (lin_order_3 Horder).
              { apply nth_error_split. }
              { instantiate (2 := i2); rewrite nth_error_app; clarify; eauto. }
              { auto. }
              omega. } }
(*      + exploit valid_lin; eauto; rewrite lower_app, filter_app; intro Hcon.
        generalize (consistent_app _ _ Hcon).
        repeat rewrite lower_app, filter_app, lower_single; simpl.
        rewrite Hc', replace_not_reads; auto.*)
      + intros ????? Hread.
        rewrite nth_error_app in Hr; destruct (lt_dec i (length m)).
        * specialize (Hseq _ _ _ _ Hr Hread).
          rewrite firstn_app, not_le_minus_0, app_nil_r; [|omega].
          destruct (find (fun e => if find_mod (op e) p then true else false)
            (rev (firstn i m))) eqn: Hfind; clarify.
          destruct (eq_dec (id r) (id x)); [|clarify; eauto].
          exploit nth_error_in; eauto; rewrite <- (lin_set Hm); intro.
          unfold linearization in Horder; clarify.
          rewrite map_app, NoDup_app in Horder21; clarify.
          exploit Horder2122; eauto; clarify.
          rewrite in_map_iff; eauto.
        * rewrite nth_error_single in Hr; clarify.
          assert (i = length m) by omega; subst.
          rewrite firstn_app, firstn_length, minus_diag, app_nil_r.
          unfold reads in Hread; rewrite Hc' in Hread.
          specialize (Hlv _ _ Hread).
          destruct (find (fun e => if find_mod (op e) p then true else false)
            (rev m)) eqn: Hfind; clarify; split; [|eauto].
          do 2 eexists; unfold reads; rewrite Hc'; split; eauto; clarify.
      + admit.
      + intro Hrf'; contradiction Hrace; repeat intro.
        assert (id e1 = id x -> e1 = x).
        { intro; eapply (lin_id_inj _ _ Hlin1); eauto. }
        assert (id e2 = id x -> e2 = x).
        { intro; eapply (lin_id_inj _ _ Hlin1); eauto. }
        specialize (Hrf' (if eq_dec (id e1) (id x) then x' else e1)
          (if eq_dec (id e2) (id x) then x' else e2) p).
        setoid_rewrite in_app in Hrf'; setoid_rewrite in_app in He1;
          setoid_rewrite in_app in He2; subst x'; use Hrf'; use Hrf'.
        clear He1 He2.
        do 2 (use Hrf'; [|rewrite replace_touches; eauto]).
        use Hrf'; [|destruct Hmods; [left | right];
                    clarify; rewrite replace_mods; eauto].
        assert (id (if eq_dec (id e1) (id x) then {| id := id x; op := c' |}
          else e1) = id e1) as Hid1 by clarify.
        assert (id (if eq_dec (id e2) (id x) then {| id := id x; op := c' |}
          else e2) = id e2) as Hid2 by clarify.
        rewrite Hid1, Hid2 in Hrf'; clear Hid1 Hid2; clarify.
        destruct (eq_dec (id e1) (id x)); clarify.
  Qed.

  Lemma SC_race : forall (b0 : block) P E (Hsem : sem P E)
    X (Hcon : valid E X),
    race_free (events E) X \/
    exists E' X', SC E' X' /\ well_formed E' X' /\ sem P E' /\
      ~race_free (events E') X'.
  Proof.
    intros.
    exploit valid_wf; eauto; intro.
    exploit wf_full; eauto; intros (l & Hlin).
    exploit (SC_race_base(E := E)(X := X) b0); eauto.
    { rewrite app_nil_r; eauto. }
    { rewrite (lin_set' Hlin); apply valid_rf; auto. }
    intros [? | (l1 & ? & ? & ? & ? & Hrace)]; [left | right].
    - rewrite <- (lin_set' Hlin); clarify.
    - do 3 eexists; eauto; clarify.
  Qed.

  Theorem race_free_SC' : forall (b0 : block) P
    (Hrf : forall E X, sem P E -> well_formed E X -> SC E X ->
      race_free (events E) X)
    E (HP : sem P E),
    (exists X, valid E X) <-> (exists X, SC E X /\ well_formed E X).
  Proof.
    split; clarify.
    - exploit valid_wf; eauto; intro.
      generalize (SC_race b0 HP _ H); intros [? | (E' & X' & X'' & ?)].
      + exists x; clarify.
        rewrite race_free_SC in *; clarify; eauto.
      + specialize (Hrf E' X'); clarify.
    - specialize (Hrf E x); clarify.
      exists x; rewrite race_free_SC; auto.
  Qed.

End Concurrency.

Arguments drop_lin [_] [_] [_] _ _ _.