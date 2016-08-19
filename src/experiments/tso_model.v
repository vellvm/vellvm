(* A formalization of the TSO memory model. *)
Require Import Ensembles.
Require Import Util.
Require Import block_model.
Require Import conc_model.
Import EquivDec.
Import CoqEqDec.

Set Implicit Arguments.

Section TSO_model.
  Context `(ML : Memory_Layout).
  Variables (thread : Type) (thread_eq : EqDec_eq thread).

  Definition ptr := ptr block.

  (* ARW is actually a fence. *)
  Inductive base_op : Type :=
  | Read : thread -> ptr -> val -> base_op
  | Write : thread -> ptr -> val -> base_op
(*  | ARW : thread -> ptr -> val -> val -> base_op*)
  | Alloc : thread -> block -> nat -> base_op
  | Free : thread -> block -> base_op
  | Fence : thread -> base_op.

  Definition to_seq c :=
    match c with
    | Read _ p v => [MRead p v]
    | Write _ p v => [MWrite p v]
(*    | ARW _ p v v' => [MRead p v; MWrite p v']*)
    | Alloc _ b n => [MAlloc b n]
    | Free _ b => [MFree b]
    | Fence _ => []
    end.

  Definition thread_of c :=
    match c with
    | Read t _ _ => t
    | Write t _ _ => t
(*    | ARW t _ _ _ => t*)
    | Alloc t _ _ => t
    | Free t _ => t
    | Fence t => t
    end.

  Definition loc_of c :=
    match c with
    | Read _ p _ => Some (Ptr p)
    | Write _ p _ => Some (Ptr p)
(*    | ARW _ p _ _ => Some (Ptr p)*)
    | Alloc _ b _ => Some (Block b)
    | Free _ b => Some (Block b)
    | Fence _ => None
    end.

  Definition mem := ilist base_op.

  Definition writesp (c : base_op) (p : ptr) :=
    match c with
    | (Write _ p' _) => p' = p
(*    | (ARW _ p' _ _) => p' = p*)
    | _ => False
    end.

  Definition write_val (c : base_op) :=
    match c with
    | (Write _ _ v) => Some v
(*    | (ARW _ _ _ v) => Some v*)
    | _ => None
    end.

  Instance TSO_base : MM_base(block := block) base_op := 
    { thread_of := thread_of; to_seq := to_seq }.
  Proof.
    - destruct c; clarsimp.
    - destruct c; clarsimp.
  Defined.
  
  Notation event := (event(conc_op := base_op) nat).
  Notation execution := (execution(conc_op := base_op) nat).

  Variable err : val.

  Definition is_read c :=
    match c with
    | Read _ _ _ => True
    | _ => False
    end.

  Definition is_mod c :=
    match c with
    | Read _ _ _ => False
    | Fence _ => False
    | _ => True
    end.

  (* Definition of TSO based on Viktor's paper. I think this is equivalent
     to CompCertTSO's, but more concise. *)
  Definition wf_reads (E : execution) X := forall e (He : events E e) p v
    (Hread : reads (op e) p v), exists w a, w <> e /\ events E w /\
    rf X (id w) (id e) /\ last_op (to_seq (op w)) (Ptr p) a /\
    match_op err a v.

  Definition wf_rf (E : execution) X :=
    (forall i j (Hi : rf X i j) i' (Hi' : rf X i' j), i' = i) /\
    (forall i e (He : events E e) (Hi : rf X i (id e)),
      exists p v, reads (op e) p v).

  Definition wf_lin (E : execution) X := exists l, 
    linearization (events E) (full (events E) X) l /\
    forall e1 e2 (He1 : events E e1) (He2 : events E e2)
      t (Hfence : op e1 = Fence t),
      hb X (id e1) (id e2) \/ hb X (id e2) (id e1).

  (* via Viktor *)
  Inductive good_mo (E : execution) X R := good_moI
    (HR_total : total_on R (fun e => events E e /\ ~is_read (op e)))
    (Hpo : forall e1 e2 (He1 : events E e1) (He2 : events E e2)
       (Hpo : constraints E (id e1) (id e2)), R (id e1) (id e2) \/
        is_mod (op e1) /\ is_read (op e2))
    (HR_read : forall e1 e2 (He1 : events E e1) (He2 : events E e2)
       (Hrf : rf X (id e1) (id e2)), R (id e1) (id e2) \/
       constraints E (id e1) (id e2))
    (Htri : forall a b c (Ha : events E a) (Hb : events E b) (Hc : events E c)
       (Hrf : rf X (id a) (id b)) (Hord : constraints E (id b) (id c) \/
       R (id b) (id c)) (Hmod : ~is_read (op b))
       (Hsame : loc_of (op a) = loc_of (op b)), ~R (id a) (id b))
    (Hacyclic : forall e1 e2 (He1 : events E e1) (He2 : events E e2)
       (Hfull : full (events E) X (id e1) (id e2)), ~R (id e2) (id e1)).

  Definition valid (E : execution) X := (exists R, good_mo E X R) /\
    wf_reads E X /\ wf_rf E X /\ wf_lin E X /\
    contained (constraints E) (hb X) /\ transitive_on (hb X) (events E).

  Fixpoint drop_l_reads p (l : list event) :=
    match l with
    | [] => []
    | e :: l' => match op e with
        | Read t p' v => if eq_dec p' p then drop_l_reads p l'
                         else e :: drop_l_reads p l'
        | _ => e :: drop_l_reads p l'
        end
    end.

  Definition dropped p ops (e : event) := In e ops /\
    exists v, reads (op e) p v.

  Notation witness := (witness nat).

  Definition dlr p (E : execution) (Y : list event * witness) :=
    (drop_l_reads p (fst Y), {| hb := hb (snd Y); rf := fun i j =>
       rf (snd Y) i j /\ forall e (He : events E e) (Hj : j = id e),
       ~dropped p (fst Y) e |}).

  Notation lower m := (flatten (map to_seq (map (@op base_op nat) m))).

  Lemma drop_l_reads_spec : forall p ops, lower (drop_l_reads p ops) =
    filter (fun op => match op with MRead p' v => negb (beq p' p) | _ => true
                      end) (lower ops).
  Proof.
    induction ops; clarify.
    destruct a as [? c]; destruct c; try setoid_rewrite lower_cons; clarsimp.
    unfold negb, beq; destruct (eq_dec p0 p); clarsimp.
  Qed.

  Notation id := (@id base_op nat).

  Lemma drop_in : forall p ops e (Hin : In e (drop_l_reads p ops)), In e ops.
  Proof.
    induction ops; clarify.
    destruct a as [? c]; destruct c; clarify; eauto.
  Qed.

(*  Corollary drop_id_in : forall p ops,
    Included (set_of (map id (drop_l_reads p ops))) (set_of (map id ops)).
  Proof.
    repeat intro.
    induction ops; repeat intro; unfold Ensembles.In in *; clarify.
    destruct a as [? c]; destruct c; clarify;
      try solve [right; apply IHops; auto].
    destruct (eq_dec p0 p); clarify; right; apply IHops; auto.
  Qed.*)

  Lemma drop_NoDup : forall p ops (Hnodup : NoDup (map id ops)),
    NoDup (map id (drop_l_reads p ops)).
  Proof.
    induction ops; clarify.
    inversion Hnodup as [|?? Hout ?]; clarify.
    assert (~In (id a) (map id (drop_l_reads p ops))).
    { intro; contradiction Hout; rewrite in_map_iff in *; clarify.
      do 2 eexists; [|eapply drop_in; eauto]; auto. }
    destruct a as [? c]; destruct c; clarify; try (constructor; auto).
  Qed.

  (* up? *)
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
    destruct (in_ops_dec _ _ He Hin _ Hlin); unfold dropped, reads.
    - destruct e as [? c]; destruct c; try solve [right; intro; clarify].
      destruct (eq_dec p0 p); clarify; eauto.
      right; intros (? & ? & [Hread | ]); [inversion Hread|]; clarify.
    - right; intro; clarify.
  Qed.

  Lemma drop_not_dropped : forall p ops e (He : In e ops)
    (Hkeep : ~dropped p ops e), In e (drop_l_reads p ops).
  Proof.
    unfold dropped; induction ops; clarify.
    destruct a as [? c]; destruct He; clarify.
    - destruct c; clarify.
      contradiction Hkeep; unfold reads; clarify; eauto.
    - specialize (IHops e); clarify.
      use IHops; [|intro; contradiction Hkeep; clarify; eauto].
      destruct c; clarify.
  Qed.

  Corollary not_dropped_set : forall E p ops e (Hkeep : ~dropped p ops e)
    (He : events E e) (Hin : Included (set_of ops) (events E))
    X l (Hlin : linearization (events E) (hb X) l),
    Union (Setminus (events E) (set_of ops)) (set_of (drop_l_reads p ops)) e.
  Proof.
    intros; rewrite Union_spec, Setminus_spec.
    exploit in_ops_dec; eauto; clarify.
    right; apply drop_not_dropped; auto.
  Qed.

  Lemma dropped_dropped : forall p e v ops (Hdropped : reads (op e) p v),
    ~In e (drop_l_reads p ops).
  Proof.
    induction ops; clarify.
    unfold reads in *.
    destruct e as [? c]; destruct c; clarify.
    inversion H; clarify.
    destruct a as [? c]; destruct c; clarify; intro; clarify.
    inversion H; clarify.
  Qed.

  Corollary drop_set : forall E p ops (Hin : forall e, In e ops -> events E e)
    X l (Hlin : linearization (events E) (hb X) l),
    Union (Setminus (events E) (set_of ops)) (set_of (drop_l_reads p ops)) =
    Setminus (events E) (dropped p ops).
  Proof.
    intros; apply set_ext; intro.
    rewrite Union_spec; repeat rewrite Setminus_spec; split; clarify.
    - destruct H; clarify.
      + unfold dropped; intro; clarify.
      + exploit drop_in; eauto; clarify.
        unfold dropped; intro; clarify.
        exploit dropped_dropped; eauto.
    - exploit in_ops_dec; eauto; clarify.
      right; apply drop_not_dropped; auto.
  Qed.

  Require Import Relation_Operators.

  Lemma full_drop_iff : forall E X p ops
    (Hin : forall e, In e ops -> events E e)
    ops' X' (Hdrop : dlr p E (ops, X) = (ops', X'))
    l (Hlin : linearization (events E) (full (events E) X) l) i j,
    full (Union (Setminus (events E) (set_of ops)) (set_of ops')) X' i j <->
    full (Union (Setminus (events E) (set_of ops)) (set_of ops')) X i j.
  Proof.
    intros; split; intro Hfull; induction Hfull.
    - apply t_step.
      destruct H; clarify; repeat eexists; auto.
      unfold dlr in *; destruct H; [left | right]; clarify.
    - eapply t_trans; eauto.
    - apply t_step.
      destruct H; clarify; repeat eexists; auto.
      unfold dlr in *; destruct H; [left | right]; clarify.
      generalize (full_lin Hlin); clarify.
      erewrite drop_set, Setminus_spec in *; eauto; clarify.
      generalize (lin_id_inj x1 e Hlin); clarify.
    - eapply t_trans; eauto.
  Qed.

  (* There must be a way to generalize this. *)
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
      constructor; repeat eexists; auto; left; auto.
  Qed.

  Lemma full_into : forall E X (Htrans : transitive_on (hb X) (events E)) p ops 
    (Hin : forall e, In e ops -> events E e)
    (Htotal : total_on (hb X) (set_of ops))
    l (Hlin : linearization (events E) (full (events E) X) l)
    e1 e2 (He1 : events E e1) (Hkeep : ~dropped p ops e1)
    (He2 : events E e2) (He2' : dropped p ops e2)
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
    - destruct H as (H & ? & e' & ?).
      generalize (full_lin Hlin); clarify.
      exploit (dropped_dec(ops := ops) E p e'); eauto; intros [? | ?].
      + unfold dropped in *; clarify; exploit full_hb; try (unfold full;
          rewrite Operators_Properties.clos_trans_t1n_iff; apply Hfull);
          eauto.
        intro; exists (id e1); clarify.
        apply (Htrans _ e'); auto.
        destruct H; auto.
        apply Hrf; auto; clarify; eauto.
      + specialize (IHHfull e'); clarify.
        specialize (IHHfull _ He2 He2' eq_refl); destruct IHHfull as (k & Hk).
        exists k; clarify; left.
        assert (restrict (union (hb X') (rf X')) (Union (Setminus (events E)
          (set_of ops)) (set_of ops')) (id e1) (id e')).
        { exploit not_dropped_set; try apply Hkeep; eauto; intro.
          exploit not_dropped_set; eauto; intro.
          unfold dlr in *; clarify.
          repeat eexists; auto.
          destruct H; [left|]; clarify.
          right; clarify.
          rewrite Hj in *; exploit (lin_id_inj e e' Hlin); clarify. }
        destruct Hk1; [eapply t_trans; [apply t_step | eauto] |
          subst; apply t_step]; auto.
  Qed.

  Lemma mod_drop_set : forall E e p ops p'
    (He : events E e) (Hwrites : mods (op e) p')
    (Hin : forall e, In e ops -> events E e)
    l X (Hlin : linearization (events E) (hb X) l),
    Union (Setminus (events E) (set_of ops)) (set_of (drop_l_reads p ops)) e.
  Proof.
    intros.
    erewrite drop_set, Setminus_spec; eauto; clarify.
    intro; unfold dropped, mods, reads in *; clarify.
    destruct e as [? c]; destruct c; clarify.
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
    exploit mod_drop_set; try apply Hmods; eauto; intro.
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
    e1 e2 (He1 : events E e1) (He2 : events E e2) (He2' : ~dropped p ops e2)
    (HR : union (hb X) (rf X) (id e1) (id e2)), hb X (id e1) (id e2) \/
    full (Union (Setminus (events E) (set_of ops)) (set_of ops')) X'
      (id e1) (id e2).
  Proof.
    intros; exploit full_cases; try apply HR; eauto;
      intros [? | (? & ? & Hid & ?)]; auto.
    generalize (full_lin Hlin); clarify.
    exploit not_dropped_set; eauto; intro.
    unfold dlr in *; clarify.
    rewrite <- Hid in *; right; apply t_step; repeat eexists; clarify.
    right; auto.
  Qed.

  Lemma full_from : forall E X (Htrans : transitive_on (hb X) (events E)) p ops 
    (Hin : forall e, In e ops -> events E e)
    (Htotal : total_on (hb X) (set_of ops))
    l (Hlin : linearization (events E) (full (events E) X) l)
    e1 e2 (He2 : events E e2) (Hkeep : ~dropped p ops e2)
    (He1 : events E e1) (He1' : dropped p ops e1)
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
      exploit (dropped_dec(ops := ops) E p e'); eauto; intros [Hkeep' | ?].
      + unfold dropped in *; clarify; exploit full_hb; try (unfold full;
          rewrite Operators_Properties.clos_trans_tn1_iff; apply Hfull);
          eauto.
        intro; exploit full_cases'; try apply H; eauto; intros [? | ?].
        * exists (id e2); clarify.
          left; apply (Htrans _ e'); auto.
        * eauto.
      + use IHHfull; use IHHfull; destruct IHHfull as (k & Hk).
        exists k; clarify; left.
        assert (restrict (union (hb X') (rf X')) (Union (Setminus (events E)
          (set_of ops)) (set_of ops')) (id e') (id e2)).
        { exploit not_dropped_set; try apply Hkeep; eauto; intro.
          exploit not_dropped_set; try apply Hkeep'; eauto; intro.
          unfold dlr in *; clarify.
          repeat eexists; auto.
          destruct H; [left|]; clarify.
          exploit (dropped_dec(ops := ops) E p e2); eauto; intros [? | ?].
          * exploit Hrf; try apply H; clarify.
          * right; clarify.
            rewrite Hj in *; exploit (lin_id_inj e e2 Hlin); clarify. }
        destruct Hk2; [eapply t_trans; [eauto | apply t_step] |
          subst; apply t_step]; auto.
  Qed.

  Lemma full_across : forall E X (Htrans : transitive_on (hb X) (events E))
    p ops (Hin : forall e, In e ops -> events E e)
    (Htotal : total_on (hb X) (set_of ops))
    l (Hlin : linearization (events E) (full (events E) X) l)
    e1 e2 (He1 : events E e1) (He1' : ~dropped p ops e1)
    (He2 : events E e2) (He2' : ~dropped p ops e2) e (He : events E e)
    (He' : dropped p ops e)
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
      (set_of (drop_l_reads p ops)) ek /\ id ek = k) as (ek & Hek & ?).
    { exploit not_dropped_set; try apply He1'; eauto; intro.
      destruct Hk as [Hk | ?]; clarify; eauto.
      generalize (full_in2 Hk); clarify; eauto. }
    assert (exists ek', Union (Setminus (events E) (set_of ops))
      (set_of (drop_l_reads p ops)) ek' /\ id ek' = k') as (ek' & Hek' & ?).
    { exploit not_dropped_set; try apply He2'; eauto; intro.
      destruct Hk'2 as [Hk' | ?]; clarify; eauto.
      generalize (full_in1 Hk'); clarify; eauto. }
    assert (hb X k k').
    { destruct Hk'1; subst; auto.
      erewrite drop_set, Setminus_spec in Hek, Hek'; eauto; clarify.
      apply (Htrans _ e); auto. }
    assert (full (Union (Setminus (events E) (set_of ops))
      (set_of (drop_l_reads p ops))) {| rf := fun i j => rf X i j /\
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
    e1 e2 (He1 : events E e1) (He1' : ~dropped p ops e1)
    (He2 : events E e2) (He2' : ~dropped p ops e2)
    (Hfull : full (events E) X (id e1) (id e2)),
    full (Union (Setminus (events E) (set_of ops)) (set_of ops')) X'
      (id e1) (id e2).
  Proof.
    intros; generalize (full_lin Hlin); intros (Hlin' & _).
    remember (id e1) as i; remember (id e2) as j; generalize dependent e2;
      generalize dependent e1; induction Hfull; clarify.
    - rewrite full_drop_iff; eauto.
      exploit not_dropped_set; try apply He1'; eauto; intro.
      exploit not_dropped_set; try apply He2'; eauto; intro.
      unfold dlr in *; clarify.
      destruct H; apply t_step; repeat eexists; auto.
    - generalize (full_in2 Hfull1); intros (e' & ? & ?); subst.
      exploit (dropped_dec(ops := ops) E p e'); eauto; intros [? | ?].
      + eapply full_across; eauto.
      + eapply t_trans; [eapply IHHfull1 | eapply IHHfull2]; try apply eq_refl;
          auto.
  Qed.

  Lemma full_transfer' : forall (E : execution) X ops
    (Hin : forall e, In e ops -> events E e)
    l (Hlin : linearization (events E) (full (events E) X) l)
    p ops' X' (Hdrop : dlr p E (ops, X) = (ops', X'))
    i j (Hfull : full (Union (Setminus (events E) (set_of ops)) (set_of ops'))
                      X' i j), full (events E) X i j.
  Proof.
    intros.
    rewrite full_drop_iff in Hfull; eauto.
    eapply full_cont; eauto.
    unfold dlr in *; clarify.
    generalize (full_lin Hlin); intros [? _].
    erewrite drop_set; eauto.
    apply minus_sub.
  Qed.      

  Lemma drop_in_set : forall E p ops (Hin : forall e, In e ops -> events E e) e
    (He : Union (Setminus (events E) (set_of ops))
                 (set_of (drop_l_reads p ops)) e), events E e.
  Proof.
    intros.
    rewrite Union_spec in He; repeat rewrite Setminus_spec in He; clarify.
    exploit drop_in; eauto.
  Qed.

  Lemma drop_lin_wf : forall p l E X
    (Hlin : linearization (events E) (full (events E) X) l)
    ops (Hin : forall e, In e ops -> events E e) (Hnodup : NoDup (map id ops))
    ops' X' (Hdrop : dlr p E (ops, X) = (ops', X')),
    linearization (Union (Setminus (events E) (set_of ops))
      (set_of ops')) (full (Union (Setminus (events E) (set_of ops))
                                  (set_of ops')) X') (drop_lin ops ops' l).
  Proof.
    unfold dlr; clarify.
    generalize (drop_NoDup p _ Hnodup); intro Hnodup'.
    assert (forall e, Union (Setminus (events E) (set_of ops))
      (set_of (drop_l_reads p ops)) e <->
      In e (drop_lin ops (drop_l_reads p ops) l)) as Hset.
    { intro; rewrite drop_lin_in; auto; try (rewrite (lin_set' Hlin); auto;
                                             reflexivity).
      * intros; exploit drop_in; eauto.
      * unfold linearization in Hlin; clarify. }
    split; auto; split.
    - apply drop_lin_ids; unfold linearization in Hlin; clarify.
    - intros.
      exploit full_transfer'; unfold dlr; eauto; intro.
      rewrite Hset in He1, He2.
      generalize (in_nth_error _ _ He1), (in_nth_error _ _ He2);
        intros (i1 & ? & Hi1) (i2 & ? & Hi2); exists i1, i2; clarify.
      destruct (lt_eq_lt_dec i1 i2) as [[? | ?] | ?]; auto.
      + subst; rewrite Hi1 in Hi2; clarify.
        exploit (lin_irrefl Hlin); eauto; clarify.
        rewrite <- Hset in He2.
        eapply drop_in_set; eauto.
      + generalize (drop_lin_ord _ _ _ _ Hi2 Hi1 l0);
          intros (i2' & i1' & e2' & e1' & ? & ? & ? & Hid2 & Hid1).
        rewrite <- Hid1, <- Hid2 in *.
        exploit (lin_order_3(e1 := e1') Hlin i1' i2'); eauto; omega.
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
    destruct a as [i c]; destruct c; clarify; try (rewrite Heq; auto).
    destruct (eq_dec p0 p); clarify; [|rewrite Heq; auto].
    destruct (find (fun e => if eq_dec (id e) i then true else false)
      (drop_l_reads p ops)) eqn: Hfind; auto.
      exploit find_success; eauto; clarify.
      exploit drop_in; eauto; intro.
      contradiction H1; rewrite in_map_iff; eauto.
  Qed.

  Lemma drop_l_reads_length : forall p l,
    length (drop_l_reads p l) <= length l.
  Proof.
    induction l; clarify.
    destruct a as [? c]; destruct c; clarify; omega.
  Qed.

  Definition well_formed E X := wf_lin E X /\ wf_rf E X /\
    transitive_on (hb X) (events E).

  Notation find_mod c p := (find (fun a => op_modifies a p) (to_seq c)).

  Lemma private_seq : forall E X ops (Hwf : well_formed E X)
    (Hin : forall e, In e ops -> events E e)
    (Htotal : total_on (hb X) (set_of ops)) a z (Ha : In a ops) (Hz : In z ops) 
    (Hbegin : forall e (He : In e ops), e = a \/ hb X (id a) (id e))
    (Hend : forall e (He : In e ops), e = z \/ hb X (id e) (id z))
    l (Hordered : forall e, events E e -> mods (op e) l ->
       hb X (id e) (id a) \/ In e ops \/ hb X (id z) (id e))
    (Hops : linearization (set_of ops) (hb X) ops)
    ops' X' (Hdrop : dlr l E (ops, X) = (ops', X')),
    valid E X <-> valid (upd_events E (Union
      (Setminus (events E) (set_of ops)) (set_of ops'))) X' /\
      exists m1, linearization (before (events E) (full (events E) X) a)
        (full (events E) X) m1 /\
      forall i r v (Hr : nth_error ops i = Some r)
        (Hreads : reads (op r) l v),
      match find (fun e => if find_mod (op e) l then true else false)
        (rev (m1 ++ firstn i ops)) with
      | Some w => rf X (id w) (id r) /\
          (exists a, last_op (to_seq (op w)) (Ptr l) a /\ match_op err a v) /\
          forall r' v' (Hr' : Union (Setminus (events E) (set_of ops))
            (set_of ops') r') (Hreads' : reads (op r') l v')
            (Hhb : hb X (id w) (id r')), rf X (id w) (id r') \/
            (exists w', events E w' /\ hb X (id w) (id w') /\
                        rf X (id w') (id r'))
      | None => False
      end.
  Proof.
    unfold dlr; clarify.
    destruct Hwf as ((l' & Hlin & Hcomplete) & (Hunique & Hrf) & Htrans).
    generalize (full_lin Hlin); intros (Hhb_lin & Hrf_lin).
    erewrite drop_set; eauto.
    split; intro Hvalid.
    - destruct Hvalid as ((R & HR) & Hreads & _ & _ & Hcont & _).
      repeat split; clarify; eauto.
      + exists R; inversion HR; constructor; simpl in *;
          repeat intro; rewrite Setminus_spec in *; clarify.
        * apply (Htri a0 b c); auto.
        * exploit full_transfer'; unfold dlr; eauto.
          { erewrite drop_set; eauto. }
          intro; apply (Hacyclic e1 e2); auto.
      + repeat intro; simpl in *.
        rewrite Setminus_spec in He; clarify.
        exploit Hreads; eauto; intros (w & a' & Hw).
        exists w, a'; clarify.
        rewrite Setminus_spec; split; clarify.
        { unfold dropped, reads; intro.
          destruct w as [? c]; destruct c; clarify.
          rewrite last_single in Hw2221; clarify. }
        exploit (lin_id_inj e e0 Hlin); clarify.
      + rewrite Setminus_spec in He; clarify; eauto.
      + exploit drop_lin_wf; unfold dlr; eauto.
        { unfold linearization in Hops; clarify. }
        

  Instance TSO_model : Memory_Model err nat := { valid := valid;
    drop_l_reads := dlr; well_formed := well_formed }.
  Proof.
    - unfold valid; clarify.
    - unfold valid; clarify.
    - intros ?? (? & Hreads & _); unfold wf_reads in *;
        repeat intro.
      specialize (Hreads _ He _ _ Hread); destruct Hreads as (w & Hw);
        exists w; clarify.
      eapply last_mods; eauto.
    - unfold wf_lin; clarify; eauto.
    - unfold valid; clarify.
    - clarify.
      destruct Hwf21 as (? & Hread); repeat split; clarify; eauto 2.
      + destruct Hwf1 as (l & Hlin & ?).
        exists (fun i j => exists i1 i2 e1 e2, nth_error l i1 = Some e1 /\
          nth_error l i2 = Some e2 /\ id e1 = i /\ id e2 = j /\ i1 < i2).
        constructor.
        * intros ?? He1 He2.
          rewrite (lin_set Hlin) in *; clarify.
          generalize (in_nth_error _ _ He11), (in_nth_error _ _ He21);
            intros (i1 & ? & ?) (i2 & ? & ?).
          destruct (lt_eq_lt_dec i1 i2) as [[? | ?] | ?].
          { left; repeat eexists; eauto. }
          { clarsimp. }
          { right; right; repeat eexists; eauto. }
        * intros; left.
          rewrite (lin_set Hlin) in *.
          generalize (in_nth_error _ _ He1), (in_nth_error _ _ He2);
            intros (i1 & ? & ?) (i2 & ? & ?).
          repeat eexists; eauto.
          eapply lin_order_3; eauto.
          rewrite <- (lin_set Hlin) in *.
          constructor; repeat eexists; auto; left; auto.
        * intros.
          exploit Hread; eauto; clarify.
          exploit Hno_reads; eauto; clarify.
        * intros.
          exploit Hread; try apply Hrf; auto; intro Hwrong; clarify.
          exploit Hno_reads; try apply Hwrong; auto.
        * intros.
          intros (i2 & i1 & e2' & e1' & ? & ? & Hid2 & Hid1 & ?).
          rewrite <- Hid1, <- Hid2 in Hfull.
          exploit (lin_order_3(e1 := e1') Hlin i1 i2); eauto; omega.
      + repeat intro.
        exploit Hno_reads; eauto; clarify.
    - intros ?? ((R & HR) & Hreads & (? & ?) & Hlin & ? & ?) ???.
      assert (forall e, In e l1 -> events E e).
      { intro; rewrite (lin_set Hlin0), in_app; auto. }
      repeat split; clarify; eauto.
      + exists R; inversion HR; constructor; clarify; eauto.
        * repeat intro; clarify.
        * eapply Hacyclic; auto.
          eapply full_lin_cont; eauto.
          repeat intro; unfold Ensembles.In in *; auto.
      + unfold wf_reads in *; clarify.
        specialize (Hreads e); rewrite (lin_set Hlin0), in_app in Hreads;
          clarify.
        specialize (Hreads _ _ Hread); destruct Hreads as (w & a & Hw);
          exists w, a; clarify; repeat split; auto.
        rewrite (lin_set Hlin0), in_app in Hw21; clarify.
        generalize (lin_split _ _ Hlin0); intro Hnot.
        exploit Hnot; eauto; clarify; constructor; repeat eexists; auto.
        * right; auto.
        * rewrite (lin_set Hlin0), in_app; auto.
      + destruct Hlin as (l & Hlin & Hcomplete).
        exists l1; simpl; split; eauto.
        eapply full_lin_app; eauto.
      + eapply transitive_on_sub; eauto.
    - unfold dlr; clarify; apply drop_l_reads_spec.
    - clarify; split; [|split].
      + destruct Hwf1 as (l' & ? & ?).
        eexists; split; simpl; [eapply drop_lin_wf; eauto|].
        intros.
        generalize (full_lin H); intros [? _].
        unfold dlr in *; clarify.
        erewrite drop_set, Setminus_spec in He1, He2; eauto; clarify; eauto.
      + unfold dlr in *; clarify.
        destruct Hwf21 as (? & Hrf); split; clarify; eauto.
        destruct Hwf1 as (? & Hlin & ?).
        generalize (full_lin Hlin); intros [? _].
        erewrite drop_set, Setminus_spec in He; eauto; clarify; eauto.
      + unfold dlr in *; clarify.
        eapply transitive_on_sub; eauto.
        repeat intro; eapply drop_in_set; eauto.
    - unfold dlr; clarify.
      split; [apply drop_NoDup; auto|].
      intros; exploit drop_in; eauto.
    - unfold dlr; clarify.
      split; [|clarify; split].
      + split; [reflexivity|].
        split; [unfold linearization in Hlin; clarify; apply drop_NoDup;
                auto|].
        intros.
        generalize (in_nth_error _ _ He1), (in_nth_error _ _ He2);
          intros (i1 & ? & Hi1) (i2 & ? & Hi2).
        destruct (lt_eq_lt_dec i1 i2) as [[? | ?] | ?]; eauto.
        { clarsimp.
          exploit drop_in; eauto; intro.
          exploit (lin_irrefl Hlin); eauto; clarify. }
        assert (NoDup (map id ops)) by (unfold linearization in Hlin; clarify).
        assert (incl ops ops) by (repeat intro; auto).
        erewrite <- drop_lin_drop in Hi1, Hi2; eauto.
        generalize (drop_lin_ord _ _ _ _ Hi2 Hi1 l0).
        intros (i1' & i2' & e1' & e2' & ? & ? & ? & Hid1 & Hid2).
        rewrite <- Hid1, <- Hid2 in *.
        exploit (lin_order_3(e1 := e2') Hlin i2' i1'); eauto; omega.
      + apply contained_refl.
      + split; [|reflexivity].
        eapply transitive_on_sub; eauto.
        repeat intro; eapply drop_in_set; eauto.
    - unfold dlr; clarify.
      destruct c as [? c].
      repeat intro; clarify.
      rewrite Union_spec, Subtract_spec in *; clarify.
      destruct He1 as [He1 | He1], He2 as [He2 | He2]; clarify.
      + eapply Hrf; eauto.
      + specialize (Hrf _ _ p He11 Hin); clarify.
        destruct c; clarify.
      + specialize (Hrf _ _ p Hin He21); clarify.
        destruct c; clarify.
      + destruct c; clarify.
    - unfold dlr; clarify.
      apply drop_l_reads_length.
    - unfold dlr; clarify.
      destruct Hwf1 as (? & Hlin & ?).
      generalize (full_lin Hlin); intros [? _].
      erewrite drop_set, Setminus_spec in He1, He2; eauto; clarify.
      destruct Hwf21 as (? & Hrf); split; intros (? & Hr); eauto.
      clarify; unfold dropped; intro; clarify.
      exploit (lin_id_inj e e2 Hlin); clarify.
      contradiction He22; unfold dropped; eauto.
    - intros; eapply private_seq; try apply Hordered; eauto; clarify.
  Defined.



(*
  Inductive buf_item :=
  | BWrite (p : ptr) (v : val)
  | BAlloc (b : block) (n : nat)
  | BFree (b : block).
  Definition bloc_of e :=
    match e with
    | BWrite p _ => Ptr p
    | BAlloc b _ => Block b
    | BFree b => Block b
    end.

  Definition order := list buf_item.
  Definition buffer := thread -> list nat.
  Record mem_state :=
    { hist : list (@mem_op block val); wbuf : buffer; word : order;
      wf : forall t, Forall (fun i => i < length word) (wbuf t) }.
  Definition upd_hist m h :=
    {| hist := h; wbuf := wbuf m; word := word m; wf := wf m |}.

  (* Is this a valid interpretation of TSO? *)

  (* It would be nice for this to be total, and/or to not have to carry around
     well-formedness predicates/fields. *)
  Fixpoint make_buf_aux b (o : order) :=
    match b with
    | [] => []
    | n :: rest =>
        match (nth_error o n, make_buf_aux rest o) with
        | (Some w, buf') => w :: buf'
        | _ => []
        end
    end.

  Definition make_buf (s : mem_state) t := make_buf_aux (wbuf s t) (word s).

  Definition buf_match p e :=
    if indep_dec _ (bloc_of e) (Ptr p) then false else true.

  Definition do_read (m : mem_state) t p v m' : Prop :=
    match find (buf_match p) (make_buf m t) with
    | Some (BWrite p v') => v' = v /\ m' = m
    | Some _ => False
    | None => m' = upd_hist m (hist m ++ [MRead p v])
    end.

  Program Definition add_buf (m : mem_state) t e :=
    {| hist := hist m; wbuf := fun_upd (wbuf m) t (length (word m) :: wbuf m t);
       word := word m ++ [e] |}.
  Next Obligation.
    generalize (wf m t0); repeat rewrite Forall_forall; intros Hwf x Hin.
    specialize (Hwf x).
    unfold fun_upd in *; rewrite app_length; destruct (eq_dec t0 t); clarify;
      try omega.
    destruct Hin; clarify; omega.
  Defined.

  Definition step m (c : base_op) m' : Prop :=
    match c with
    | Read t p v => do_read m t p v m'
    | Write t p v => m' = add_buf m t (BWrite p v)
    | Alloc t b n => m' = add_buf m t (BAlloc b n)
    | Free t b => m' = add_buf m t (BFree b)
    | Fence _ => False
    end.

  Definition buf_to_op e :=
    match e with
    | BWrite p v => MWrite p v
    | BAlloc b n => MAlloc b n
    | BFree b => MFree b
    end.

  Program Definition release_op m t b n e (Hbuf : wbuf m t = b ++ [n]) :=
    {| hist := hist m ++ [buf_to_op e]; wbuf := fun_upd (wbuf m) t b;
       word := word m |}.
  Next Obligation.
    generalize (wf m t0); unfold fun_upd; clarify.
    rewrite Hbuf, Forall_app in H; clarify.
  Defined.

  Inductive step_star (m : mem_state) : list base_op -> mem_state -> Prop :=
  | step_refl : step_star m [] m
  | step_op c m' (Hstep : step m c m') ops m''
      (Hsteps : step_star m' ops m'') :
      step_star m (c :: ops) m''
  | step_write_buf t b n (Hbuf : wbuf m t = b ++ [n])
      (Hnext : forall t', Forall (fun i => n < i) (fun_upd (wbuf m) t b t'))
      e (Hnth : nth_error (word m) n = Some e)
      ops m' (Hsteps : step_star (release_op _ _ _ _ e Hbuf) ops m') :
      step_star m ops m'
  | step_fence t (Hbuf : wbuf m t = []) ops m' (Hsteps : step_star m ops m') :
      step_star m (Fence t :: ops) m'.
  Hint Constructors step_star.

  Lemma step_star_trans : forall m ops1 m1 ops2 m2
    (Hstep1 : step_star m ops1 m1) (Hstep2 : step_star m1 ops2 m2),
    step_star m (ops1 ++ ops2) m2.
  Proof. intros; induction Hstep1; clarsimp; eauto. Qed.

  Lemma step_star_app_inv : forall ops1 m ops2 m'
    (Hstep : step_star m (ops1 ++ ops2) m'),
    exists m1, step_star m ops1 m1 /\ step_star m1 ops2 m'.
  Proof.
    intros; remember (ops1 ++ ops2) as ops; revert ops1 ops2 Heqops;
      induction Hstep; clarify.
    - destruct ops1; clarify; eauto.
    - destruct ops1; clarify; eauto.
      specialize (IHHstep _ _ eq_refl); clarify; eauto.
    - specialize (IHHstep _ _ eq_refl); clarify; eauto.
    - destruct ops1; clarify; eauto.
      specialize (IHHstep _ _ eq_refl); clarify; eauto.
  Qed.

  Corollary step_star_cons_inv : forall op m ops2 m'
    (Hstep : step_star m (op :: ops2) m'),
    exists m1, step_star m [op] m1 /\ step_star m1 ops2 m'.
  Proof. intros; apply step_star_app_inv; auto. Qed.

  Program Definition start_state :=
    {| hist := []; wbuf := fun _ => []; word := [] |}.

  Definition sees_op s t p a :=
    match find (buf_match p) (make_buf s t) with
    | Some b => a = buf_to_op b
    | None => last_op (hist s) (Ptr p) a
    end.

  Definition seq_con := seq_con ML.

  Definition future_hist s n := hist s ++ skipn n (map buf_to_op (word s)).
  Definition least_index s n := (exists t, In n (wbuf s t) /\
    forall n', (exists t, In n' (wbuf s t)) <-> n <= n' /\ n' < length (word s))
    \/ (n = length (word s) /\ forall t, wbuf s t = []).

  (* We could also build all the well-formedness constraints into the machine
     at each step. *)
  Definition consistent m := forall (ops : list _) (Hpre : iprefix ops m),
    exists s n, step_star start_state ops s /\ least_index s n /\
      seq_con (future_hist s n) /\ read_init (hist s).

  Definition can_read s t p v := exists s', step_star s [Read t p v] s' /\
    seq_con (hist s').

  Lemma step_star_step' : forall s op s' (Hstep : step_star s [op] s'),
    exists s1 s2, step_star s [] s1 /\
      match op with
      | Fence t => wbuf s1 t = [] /\ s2 = s1
      | _ => step s1 op s2
      end /\ step_star s2 [] s'.
  Proof.
    intros.
    remember [op] as ops; generalize dependent op.
    induction Hstep; clarify.
    - exists m; destruct op; clarify; eauto.
    - specialize (IHHstep _ eq_refl); destruct IHHstep as [s1 [s2 ?]]; clarify.
      exists s1, s2; eauto.
    - exists m; eauto.
  Qed.

  Corollary step_star_step_cases : forall s op s' (Hstep : step_star s [op] s'),
    exists s1 s2, step_star s [] s1 /\
      ((exists t, op = Fence t /\ wbuf s1 t = [] /\ s2 = s1) \/
       (forall t, op <> Fence t) /\ step s1 op s2) /\ step_star s2 [] s'.
  Proof.
    intros; exploit step_star_step'; eauto; clarify.
    repeat eexists; eauto; destruct op; clarify; eauto; right; clarify.
  Qed.    

  Corollary step_star_step : forall s op s' (Hstep : step_star s [op] s')
    (Hnot_fence : forall t, op <> Fence t),
    exists s1 s2, step_star s [] s1 /\ step s1 op s2 /\ step_star s2 [] s'.
  Proof.
    intros; exploit step_star_step_cases; eauto; intro Hcases; clarify.
    destruct Hcases21; clarify; eauto.
    exploit Hnot_fence; eauto.
  Qed.

  Lemma make_buf_aux_mono : forall b o o'
    (Hlt : Forall (fun n => n < length o) b),
    make_buf_aux b (o ++ o') = make_buf_aux b o.
  Proof.
    induction b; clarify.
    inversion Hlt; rewrite nth_error_app; clarify.
    rewrite IHb; auto.
  Qed.

  Lemma make_buf_mono : forall m t o',
    make_buf_aux (wbuf m t) (word m ++ o') = make_buf m t.
  Proof.
    intros; unfold make_buf.
    rewrite make_buf_aux_mono; auto.
    apply wf.
  Qed.

  Lemma make_buf_aux_snoc : forall b o n x
    (Hnth : nth_error o n = Some x)
    (Hlt : Forall (fun n => n < length o) b),
    make_buf_aux (b ++ [n]) o = make_buf_aux b o ++ [x].
  Proof.
    induction b; clarify.
    inversion Hlt; clarify.
    exploit nth_error_succeeds; eauto; clarify.
    erewrite IHb; eauto.
  Qed.

  Definition writesb (c : base_op) (p : ptr) :=
    match c with
    | (Write _ p' _) => beq p' p
(*    | (ARW _ p' _ _) => p' = p*)
    | _ => false
    end.

  Lemma hist_mono : forall s ops s' (Hsteps : step_star s ops s'),
    exists h', hist s' = hist s ++ h'.
  Proof.
    intros; induction Hsteps; clarify; try (exists []; clarsimp; fail); eauto.
    - rewrite IHHsteps.
      destruct c; clarify; eauto.
      + unfold do_read in *.
        destruct (find (buf_match p) (make_buf m t)) eqn: Hfind; clarify.
        * destruct b; clarify; eauto.
        * rewrite <- app_assoc; eauto.
    - rewrite IHHsteps.
      rewrite <- app_assoc; eauto.
  Qed.

  Lemma step_star_nil_trans : forall m m1 ops m2
    (Hstep1 : step_star m [] m1) (Hstep2 : step_star m1 ops m2),
    step_star m ops m2.
  Proof. intros; generalize (step_star_trans Hstep1 Hstep2); clarsimp. Qed.

  Lemma step_star_nil_trans2 : forall m m1 ops m2
    (Hstep1 : step_star m ops m1) (Hstep2 : step_star m1 [] m2),
    step_star m ops m2.
  Proof. intros; generalize (step_star_trans Hstep1 Hstep2); clarsimp. Qed.

  Lemma fun_upd_new : forall A B (A_eq : EqDec_eq A) (f : A -> B) x y,
    fun_upd f x y x = y.
  Proof. intros; unfold fun_upd; clarify. Qed.

  Require Import FunctionalExtensionality.
  (* Or just use a better data structure for the buffers, but that's a pain. *)

  Lemma fun_upd_triv : forall A B (A_eq : EqDec_eq A) (f : A -> B) x,
    fun_upd f x (f x) = f.
  Proof. intros; extensionality y; unfold fun_upd; clarify. Qed.

  Lemma fun_upd_twice : forall A B (A_eq : EqDec_eq A) (f : A -> B) x y z,
    fun_upd (fun_upd f x y) x z = fun_upd f x z.
  Proof. intros; extensionality a; unfold fun_upd; clarify. Qed.

  Lemma to_seq_last : forall c (Hnot_fence : forall t, c <> Fence t),
    exists op, nth_error (to_seq c) (length (to_seq c) - 1) = Some op.
  Proof.
    destruct c; clarify; eauto.
    specialize (Hnot_fence t); contradiction Hnot_fence; auto.
  Qed.

  Lemma lift_last_write : forall ops p v
    (Hlast : last_op (lower ops) (Ptr p) (MWrite p v)),
    exists i w, nth_error ops i = Some w /\ writesp w p /\ write_val w = Some v
    /\ forall i2 w2 l, nth_error ops i2 = Some w2 -> loc_of w2 = Some l ->
         ~independent l (Ptr p) -> i2 <= i \/ exists t v, w2 = Read t p v.
  Proof.
    unfold last_op; intros; destruct Hlast as [i [Hlast_mod Hnth]].
    inversion Hlast_mod; rewrite Hnth in Hop1; clarify.
    rewrite inth_nth_error in Hnth; exploit nth_lower_split; eauto;
      intros (ops1 & b & ops2 & i' & ? & Hi' & ?); clarify.
    exists (length ops1); unfold writes, write_val.
    rewrite nth_error_split; eexists; split; eauto.
    generalize (nth_error_in _ _ Hi'); intro.
    split; [destruct b; clarify; inversion H; clarify|].
    split; [destruct b; clarify; inversion H; clarify|].
    intros i2 w2; clarify.
    rewrite nth_error_app in *; destruct (lt_dec i2 (length ops1));
      [left; omega|].
    destruct (i2 - length ops1) eqn: Hminus; [left; omega | clarify].
    exploit nth_error_split'; eauto; clarify.
    exploit to_seq_last.
    { instantiate (1 := w2); destruct w2; clarify. }
    intros [op Hop].
    specialize (Hlast (length (lower ops1) + (length (to_seq b) +
      (length (lower x) + (length (to_seq w2) - 1)))) op).
    rewrite inth_nth_error in Hlast;
      repeat rewrite lower_app, lower_cons in Hlast.
    do 3 rewrite nth_error_app, lt_dec_plus_r, minus_plus in Hlast.
    exploit nth_error_lt; eauto; intro.
    rewrite nth_error_app in Hlast; clarify.
    generalize (nth_error_lt _ _ Hi'); intro Hlt.
    rewrite <- NPeano.Nat.add_le_mono_l in Hlast.
    destruct w2; clarify.
    - destruct (eq_dec p0 p); clarify; eauto.
    - generalize (lt_plus _ (le_lt_trans _ _ _ Hlast Hlt)); clarify.
    - generalize (lt_plus _ (le_lt_trans _ _ _ Hlast Hlt)); clarify.
    - generalize (lt_plus _ (le_lt_trans _ _ _ Hlast Hlt)); clarify.
  Qed.

  Definition not_read' c :=
    match c with
    | Read _ _ _ => false
    | _ => true
    end.

  Definition is_mod_op p c := not_read' c && match loc_of c with
    | Some l => if indep_dec _ l (Ptr p) then false else true
    | None => false
    end.

  Corollary find_last_write : forall ops p v
    (Hlast : last_op (lower ops) (Ptr p) (MWrite p v)),
    exists w, find (is_mod_op p) (rev ops) = Some w /\ writesp w p /\
              write_val w = Some v.
  Proof.
    intros; exploit lift_last_write; eauto; intros [i [w Hlast']]; clarify.
    exists w; rewrite find_spec; clarify.
    exploit nth_error_rev; eauto; intro.
    eexists; split; eauto.
    unfold is_mod_op; destruct w; clarify;
      destruct (indep_dec block_eq (Ptr p) (Ptr p)); clarify.
    destruct (loc_of y) eqn: Hloc; clarsimp.
    exploit nth_error_rev'; eauto 2; intro.
    exploit Hlast'222; eauto 2; intros [? | ?]; [omega | clarify].
  Qed.

  Lemma step_cases : forall m c m' (Hstep : step m c m'),
    (exists t p v, c = Read t p v /\ do_read m t p v m') \/
    (exists e, loc_of c = Some (bloc_of e) /\ not_read' c = true /\
               m' = add_buf m (thread_of c) e).
  Proof.
    intros; destruct c; clarify; [left | right | right | right];
      repeat eexists; eauto.
  Qed.

  Lemma word_mono : forall s ops s' (Hsteps : step_star s ops s'),
    exists l, word s' = word s ++ l.
  Proof.
    intros; induction Hsteps; clarify; eauto.
    - exists []; autorewrite with list; auto.
    - exploit step_cases; eauto; intros [[t [p [v ?]]] | ?]; clarify.
      + unfold do_read in *; clarify.
        destruct (find (buf_match p) (make_buf m t)); [destruct b|];
          clarify; eauto.
      + rewrite <- app_assoc in *; eauto.
  Qed.

  Lemma word_same : forall s ops s' (Hsteps : step_star s ops s')
    (Hsame : word s' = word s),
    Forall (fun op => forall p : ptr, is_mod_op p op = false) ops.
  Proof.
    intros; induction Hsteps; clarify.
    - exploit step_cases; eauto; intros [[t [p [v ?]]] | ?]; clarify.
      + unfold do_read in *; clarify.
        destruct (find (buf_match p) (make_buf m t)); clarify.
        destruct b; clarify.
      + exploit word_mono; eauto; intros [? Hword].
        rewrite Hword in Hsame; clarify.
        generalize (eq_refl (length (word m))); rewrite <- Hsame at 1.
        repeat rewrite app_length; clarify; omega.
  Qed.

  Lemma word_inv : forall s0 ops s (Hsteps : step_star s0 ops s)
    l p v (Hword : word s = word s0 ++ l ++ [BWrite p v]),
    exists ops1 ops2 t s1, ops = ops1 ++ Write t p v :: ops2 /\
      Forall (fun op => forall p, is_mod_op p op = false) ops2 /\
      step_star s0 ops1 s1 /\ word s1 = word s0 ++ l /\
      step_star (add_buf s1 t (BWrite p v)) ops2 s.
  Proof.
    intros ? ? ? ?; induction Hsteps; clarify; eauto.
    - generalize (eq_refl (length (word m))); rewrite Hword at 1;
        repeat rewrite app_length; clarify; omega.
    - destruct c; clarify.
      + unfold do_read in *; clarify.
        destruct (find (buf_match p0) (make_buf m t)) eqn: Hfind; clarify.
        * destruct b; clarify.
          exploit IHHsteps; eauto; clarify.
          exists (Read t p0 v0 :: x), x0, x1, x2; clarify.
          econstructor; eauto; simpl; unfold do_read; clarify.
        * exploit IHHsteps; eauto; clarify.
          exists (Read t p0 v0 :: x), x0, x1, x2; clarify.
          econstructor; eauto; simpl; unfold do_read; clarsimp.
      + exploit word_mono; eauto; clarsimp.
        exploit app_eq_inv; eauto; clarify.
        destruct l; clarify.
        * exists []; exists ops; eexists; eexists; eexists;
            autorewrite with list; clarify.
          eapply word_same; eauto.
        * exploit IHHsteps.
          { rewrite <- app_assoc; clarify. }
          clarify.
          exists (Write t p0 v0 :: x), x0, x1, x2; clarsimp.
          econstructor; eauto; simpl; clarsimp.
      + exploit word_mono; eauto; clarsimp.
        exploit app_eq_inv; eauto; clarify.
        destruct l; clarify.
        setoid_rewrite <- app_assoc in IHHsteps; clarify.
        exploit IHHsteps; eauto; clarify.
        exists (Alloc t b n :: x), x0, x1, x2; clarify.
        econstructor; eauto; clarify.
      + exploit word_mono; eauto; clarsimp.
        exploit app_eq_inv; eauto; clarify.
        destruct l; clarify.
        setoid_rewrite <- app_assoc in IHHsteps; clarify.
        exploit IHHsteps; eauto; clarify.
        exists (Free t b :: x), x0, x1, x2; clarify.
        econstructor; eauto; clarify.
    - exploit IHHsteps; eauto; clarify.
      exists x, x0, x1, x2; clarify.
      eapply step_write_buf; eauto.
    - exploit IHHsteps; eauto; clarify.
      exists (Fence t :: x), x0, x1, x2; clarify.
  Qed.

  Lemma make_buf_nth : forall b o i x
    (Hnth : nth_error (make_buf_aux b o) i = Some x),
    exists n, nth_error b i = Some n /\ nth_error o n = Some x.
  Proof.
    induction b; clarsimp.
    destruct (nth_error o a) eqn: Ho; clarsimp.
    destruct i; clarify; eauto.
  Qed.

  Lemma make_buf_length : forall b o (Hwf : Forall (fun i => i < length o) b),
    length (make_buf_aux b o) = length b.
  Proof.
    induction b; clarify.
    inversion Hwf; clarify.
    exploit nth_error_succeeds; eauto; clarify.
  Qed.

  Lemma make_buf_app : forall b1 b2 o (Hwf : Forall (fun i => i < length o) b1),
    make_buf_aux (b1 ++ b2) o = make_buf_aux b1 o ++ make_buf_aux b2 o.
  Proof.
    induction b1; clarify.
    inversion Hwf; clarify.
    exploit nth_error_succeeds; eauto; clarify.
    rewrite IHb1; auto.
  Qed.

  Lemma no_pending_write : forall s p
    (Hno : forall t, Forall (fun e => buf_match p e = false) (make_buf s t))
    ops s' (Hsteps : step_star s ops s'),
    (exists w, In w ops /\ is_mod_op p w = true) \/
    ((forall t, Forall (fun e => buf_match p e = false) (make_buf s' t)) /\
     (forall op, last_op (hist s') (Ptr p) op <-> last_op (hist s) (Ptr p) op)).
  Proof.
    intros; induction Hsteps; clarify; eauto.
    - right; clarify; reflexivity.
    - exploit step_cases; eauto; intros [[t [p' [? ?]]] | [e ?]]; clarify.
      + unfold do_read in *.
        destruct (find (buf_match p') (make_buf m t)); clarify; eauto.
        * destruct b; clarify; eauto.
        * destruct IHHsteps as [? | IH]; clarify; eauto.
          right; clarify.
          rewrite IH2; setoid_rewrite last_op_snoc; split; clarify.
      + unfold is_mod_op in *.
        unfold make_buf at 1 in IHHsteps; clarify.
        destruct (indep_dec _ (bloc_of e) (Ptr p));
          [|subst; left; eexists; clarsimp].
        use IHHsteps; clarify; eauto.
        specialize (Hno t); rewrite Forall_forall in *; intros x Hin.
        specialize (Hno x).
        unfold fun_upd in *; destruct (eq_dec t (thread_of c)); clarify.
        * rewrite nth_error_split in Hin; clarify.
          rewrite make_buf_mono in Hin; unfold buf_match; clarify.
        * rewrite make_buf_mono in Hin; auto.
    - generalize (Hno t); unfold make_buf, release_op in *; intro Hnot; clarify.
      erewrite Hbuf, make_buf_aux_snoc in Hnot; eauto.
      rewrite Forall_app in Hnot; clarify.
      inversion Hnot2; clarify.
      use IHHsteps; clarify.
      + right; clarify.
        rewrite IHHsteps2.
        setoid_rewrite last_op_snoc.
        unfold buf_match in *; split; destruct e; clarify.
      + unfold fun_upd; destruct (eq_dec t0 t); clarify.
      + generalize (wf m t); rewrite Hbuf, Forall_app; clarify.
  Qed.
  
  Lemma buf_steps : forall s ops s' (Hsteps : step_star s ops s') t p e
    i (Hbuf : find_index (buf_match p) (make_buf s t) = Some i)
    n (Hn : nth_error (wbuf s t) i = Some n)
    (Hnth : nth_error (word s) n = Some e)
    (Hfresh : forall n' e', nth_error (word s) n' = Some e' ->
       buf_match p e' = true -> n' <= n),
    (exists w, In w ops /\ is_mod_op p w = true) \/
    find (buf_match p) (make_buf s' t) = Some e \/
    (find (buf_match p) (make_buf s' t) = None /\
     last_op (hist s') (Ptr p) (buf_to_op e)).
  Proof.
    intros ? ? ? ? ? ? ?; induction Hsteps; clarify; eauto.
    - right; left.
      rewrite find_index_spec in Hbuf; clarify.
      exploit make_buf_nth; eauto; clarsimp.
      rewrite find_spec; eauto.
    - exploit step_cases; eauto; intros [[t' [p' ?]] | [e' ?]]; clarify.
      + unfold do_read in *; clarify.
        destruct (find (buf_match p') (make_buf m t')); clarify.
        * destruct b; clarify.
          exploit IHHsteps; eauto; clarify; eauto.
        * exploit IHHsteps; eauto; clarify; eauto.
      + unfold is_mod_op; destruct (indep_dec _ (bloc_of e') (Ptr p));
          [|subst; left; eexists; clarsimp].
        unfold make_buf in *; clarify.
        generalize (nth_error_lt _ _ Hnth); intro.
        unfold fun_upd in *; destruct (eq_dec t (thread_of c)); clarify.
        * rewrite nth_error_split in *; clarify.
          unfold buf_match in *; clarify.
          rewrite make_buf_mono in *.
          unfold make_buf in IHHsteps; rewrite Hbuf in IHHsteps; clarify.
          exploit IHHsteps; eauto; clarify; eauto.
          { rewrite nth_error_app; clarify. }
          { specialize (Hfresh n' e'0); rewrite nth_error_app in *; clarify.
            destruct (n' - length (word m)); clarsimp. }
        * rewrite make_buf_mono in *; clarify.
          exploit IHHsteps; eauto; clarify; eauto.
          { rewrite nth_error_app; clarify. }
          { specialize (Hfresh n' e'0); rewrite nth_error_app in *; clarify.
            destruct (n' - length (word m)); unfold buf_match in *; clarsimp. }
    - unfold make_buf, release_op in *; clarify.
      unfold fun_upd in IHHsteps; destruct (eq_dec t t0); clarify.
      + erewrite Hbuf, make_buf_aux_snoc, find_index_app in Hbuf0; eauto.
        rewrite Hbuf, nth_error_app in Hn.
        destruct (find_index (buf_match p) (make_buf_aux b (word m)))
          eqn: Hfind; [|unfold beq in *]; clarify.
        * rewrite find_index_spec in Hfind; clarify.
          exploit make_buf_nth; eauto; intro Hnth'; clarify.
          generalize (nth_error_lt _ _ Hnth'1); clarsimp.
          exploit IHHsteps; eauto; clarify; eauto.
        * rewrite make_buf_length in Hn; clarsimp.
          exploit no_pending_write; eauto.
          { unfold make_buf; clarify.
            clear Hsteps; specialize (Hnext t).
            unfold fun_upd in *; destruct (eq_dec t t0); clarify.
            { rewrite find_index_fail in Hfind; eapply Forall_impl; eauto;
                clarify; eauto. }
            { rewrite Forall_forall in *; intros ? Hin.
              exploit in_nth_error; eauto; clarify.
              exploit make_buf_nth; eauto; intro Hnth'; clarify.
              generalize (nth_error_in _ _ Hnth'1); intro Hin';
                specialize (Hnext _ Hin').
              specialize (Hfresh _ _ Hnth'2); destruct (buf_match p x); clarify;
                omega. } }
          intro IH; clarify.
          right; right; split.
          { unfold make_buf in IH1; specialize (IH1 t0).
            rewrite find_fail; eapply Forall_impl; eauto; clarify. }
          { rewrite IH2; setoid_rewrite last_op_snoc; left;
              unfold buf_match in *; destruct e0; clarify. }
          { generalize (wf m t0); rewrite Hbuf, Forall_app; clarify. }
        * { generalize (wf m t0); rewrite Hbuf, Forall_app; clarify. }
      + exploit IHHsteps; eauto; clarify; eauto.
    - exploit IHHsteps; eauto; clarify; eauto.
  Qed.

  Lemma step_cases' : forall m c m' (Hstep : step m c m'),
    (exists t p v, c = Read t p v /\ do_read m t p v m') \/
    (exists e, loc_of c = Some (bloc_of e) /\ not_read' c = true /\
               m' = add_buf m (thread_of c) e /\ to_seq c = [buf_to_op e]).
  Proof.
    intros; destruct c; clarify; [left | right | right | right];
      repeat eexists; eauto.
  Qed.

  Lemma sees_last_thread : forall ops w t p s0 s
    (Hlast : find (is_mod_op p) (rev ops) = Some w) (Ht : thread_of w = t)
    (Hsteps : step_star s0 ops s), exists a, to_seq w = [a] /\ sees_op s t p a.
  Proof.
    intros; induction Hsteps; clarify; eauto.
    - rewrite find_app in Hlast; destruct (find (is_mod_op p) (rev ops))
        eqn: Hfind; clarify.
      exploit step_cases'; eauto; intros [? | ?]; clarsimp.
      do 2 eexists; eauto; unfold sees_op.
      exploit buf_steps; eauto; simpl.
      { instantiate (3 := p).
        unfold make_buf; simpl.
        rewrite fun_upd_new; simpl.
        rewrite nth_error_split; unfold buf_match; clarify.
        unfold is_mod_op in *; destruct w, x; clarify. }
      { rewrite fun_upd_new; simpl; eauto. }
      { apply nth_error_split. }
      { intros; exploit nth_error_lt; eauto; rewrite app_length; clarify;
          omega. }
      intros [? | [? | ?]]; clarsimp.
      rewrite in_rev in *; exploit find_succeeds; eauto; clarify.
    - rewrite find_app in Hlast; clarify.
  Qed.

  Lemma hb_fence : forall m i j (Hhb : happens_before m i j)
    a (Ha : inth m i = Some a) b (Hb : inth m j = Some b),
    thread_of a = thread_of b \/
    exists k, i <= k /\ k < j /\ inth m k = Some (Fence (thread_of a)).
  Proof.
    intros ? ? ? ?; induction Hhb; clarsimp.
    - unfold synchronizes_with in Hsync; clarify; eauto.
    - specialize (IHHhb1 _ eq_refl).
      generalize (hb_inv Hhb1); intro Hk; clarify.
      generalize (hb_lt Hhb1), (hb_lt Hhb2); intros.
      specialize (IHHhb1 _ Hk21); destruct IHHhb1 as [Ht | [k' ?]]; clarify;
        [rewrite Ht in * | right; exists k'; clarify; omega].
      specialize (IHHhb2 _ Hk21 _ eq_refl); destruct IHHhb2 as [? | [k'' ?]];
        clarify.
      right; eexists k''; clarify; omega.
  Qed.

  Lemma buf_later : forall s ops s' (Hsteps : step_star s ops s')
    n (Hgt : forall t, Forall (fun i => n < i) (wbuf s t))
    (Hlt : n < length (word s)),
    forall t, Forall (fun i => n < i) (wbuf s' t).
  Proof.
    intros; induction Hsteps; clarify.
    - exploit step_cases; eauto; intros [[t' [p ?]] | ?]; clarify.
      + unfold do_read in *.
        destruct (find (buf_match p) (make_buf m t')); clarify.
        destruct b; clarify.
      + apply IHHsteps; [|rewrite app_length; simpl; omega].
        intro t'; specialize (Hgt t'); unfold fun_upd; clarify.
    - apply IHHsteps; auto; intro t'.
      specialize (Hgt t'); unfold fun_upd; clarify.
      rewrite Hbuf, Forall_app in Hgt; clarify.
  Qed.

  Lemma buf_gt : forall s ops s' (Hsteps : step_star s ops s')
    t n (Hbuf : In n (wbuf s t)) (Hbuf' : wbuf s' t = []),
    forall t', Forall (fun i => n < i) (wbuf s' t').
  Proof.
    intros; induction Hsteps; clarsimp.
    - exploit step_cases; eauto; intros [[t'' [p ?]] | ?]; clarify.
      + unfold do_read in *.
        destruct (find (buf_match p) (make_buf m t'')); clarify.
        destruct b; clarify.
      + unfold fun_upd in IHHsteps; destruct (eq_dec t (thread_of c)); clarify.
    - unfold release_op, fun_upd in IHHsteps; clarify.
      rewrite Hbuf0, in_app_iff in Hbuf; clarify.
      eapply buf_later; eauto.
      simpl; eapply nth_error_lt; eauto.
  Qed.

  Lemma word_add_none : forall s ops s' (Hsteps : step_star s ops s')
    p (Hnone : Forall (fun op => is_mod_op p op = false) ops)
    n (Hgt : length (word s) <= n) e (Hnth : nth_error (word s') n = Some e),
    buf_match p e = false.
  Proof.
    intros; induction Hsteps; repeat intro; clarify.
    - exploit nth_error_lt; eauto; omega.
    - inversion Hnone; clarify.
      exploit step_cases; eauto; intros [[t [p' ?]] | ?]; clarify.
      + unfold do_read in *.
        destruct (find (buf_match p') (make_buf m t)); clarify.
        destruct b; clarify.
      + exploit word_mono; eauto; clarsimp.
        rewrite nth_error_app in *; destruct (lt_dec n (length (word m)));
          [omega|].
        unfold is_mod_op in *; clarsimp.
        destruct (n - length (word m)) eqn: Hminus; unfold buf_match in *;
          clarify; apply IHHsteps; auto; omega.
    - inversion Hnone; clarify.
  Qed.

  Lemma release_least : forall s n (Hleast : least_index s n)
    t buf n' (Hbuf : wbuf s t = buf ++ [n'])
    (Hnext : forall t', Forall (fun i => n' < i) (fun_upd (wbuf s) t buf t')) e,
    n' = n /\ least_index (release_op s t buf n' e Hbuf) (S n).
  Proof.
    intros.
    unfold least_index in Hleast; destruct Hleast as [[t' Hsome] | [? Hnone]];
      [|exfalso; rewrite Hnone in Hbuf; destruct buf; clarify].
    assert (n' = n); clarify.
    { clarify.
      specialize (Hnext t'); specialize (Hsome2 n'); destruct Hsome2 as [Hr _].
      use Hr; [|exists t; rewrite Hbuf, in_app_iff; clarify].
      rewrite Forall_forall in Hnext; specialize (Hnext n);
        unfold fun_upd in Hnext; destruct (eq_dec t' t); clarify; [|omega].
      rewrite Hbuf, in_app_iff in Hsome1; destruct Hsome1; clarify; omega. }
    unfold least_index; destruct (eq_dec (S n) (length (word s)));
      [right | left]; clarify.
    - generalize (wf (release_op s t buf n e Hbuf) t0); simpl; intro Hlt.
      specialize (Hnext t0).
      destruct (fun_upd (wbuf s) t buf t0); auto.
      inversion Hnext; inversion Hlt; clarify; omega.
    - generalize (wf s t'); rewrite Forall_forall; intro Hlt;
        specialize (Hlt _ Hsome1).
      generalize (Hsome2 (S n)); intros [_ Ht]; use Ht; [|omega].
      destruct Ht as [u Hu]; exists u; split.
      + unfold fun_upd; clarify.
        rewrite Hbuf, in_app_iff in Hu; clarify; omega.
      + intro n'; specialize (Hsome2 n'); split; clarify.
        * specialize (Hnext x); rewrite Forall_forall in Hnext;
            specialize (Hnext n'); clarify.
          destruct Hsome2 as [Hrange _]; use Hrange; clarify.
          unfold fun_upd in *; destruct (eq_dec x t); eauto; subst.
          exists t; rewrite Hbuf, in_app_iff; clarify.
        * destruct Hsome2 as [_ Hin]; use Hin; [clarify | omega].
          exists x; unfold fun_upd; clarify.
          rewrite Hbuf, in_app_iff in Hin; clarify; omega.
  Qed.

  Lemma step_nil_least : forall s s' (Hsteps : step_star s [] s')
    n (Hleast : least_index s n), exists n', least_index s' n'.
  Proof.
    intros ? ? ?; remember [] as ops; induction Hsteps; clarify; eauto.
    eapply IHHsteps; apply release_least; eauto.
  Qed.

  Lemma step_least_iff : forall s op s' (Hstep : step s op s') n,
    least_index s n <-> least_index s' n.
  Proof.
    intros; exploit step_cases; eauto; intros [[t [(b', o) ?]] | [e ?]];
      clarify.
    - unfold do_read in *.
      destruct (find (buf_match (b', o)) (make_buf s t)); [destruct b|];
        clarify; reflexivity.
    - unfold least_index; destruct (eq_dec n (length (word s))).
      + split; [left | right]; clarify.
        * destruct H as [Hbuf | Hbuf]; clarify.
          { generalize (wf s x); rewrite Forall_forall; intro Hx;
              specialize (Hx _ Hbuf1); omega. }
          exists (thread_of op); rewrite fun_upd_new; clarify.
          rewrite app_length; simpl; transitivity (n' = length (word s));
            [|omega].
          rewrite Hbuf2; unfold fun_upd; split; clarify.
          { rewrite Hbuf2 in *; clarify. }
          { exists (thread_of op); clarify. }
        * destruct H as [Hbuf | Hbuf]; clarify.
          destruct (wbuf s t) eqn: Hbuf; auto.
          generalize (wf s t); clarsimp; inversion H; clarify.
          specialize (Hbuf2 n); destruct Hbuf2 as [Hbuf2 _]; use Hbuf2;
            [omega|].
          exists t; unfold fun_upd; clarsimp.
          { specialize (Hbuf2 t); unfold fun_upd in Hbuf2; clarify. }
      + split; [left | left].
        * destruct H as [Hbuf | Hbuf]; clarify.
          generalize (wf s x); rewrite Forall_forall; intro Hx;
            specialize (Hx _ Hbuf1).
          exists x; unfold fun_upd; split; clarify.
          specialize (Hbuf2 n'); rewrite app_length; split; clarify.
          { destruct (eq_dec x0 (thread_of op)); clarify.
            { destruct H; [omega|].
              destruct Hbuf2 as [Hbuf2 _]; use Hbuf2; [omega | eauto]. }
            { destruct Hbuf2 as [Hbuf2 _]; use Hbuf2; [omega | eauto]. } }
          { destruct (lt_dec n' (length (word s))).
            { destruct Hbuf2 as [_ Hbuf2]; clarify.
              exists x0; clarify. }
            exists (thread_of op); clarify; left; omega. }
        * destruct H as [Hbuf | Hbuf]; clarify.
          exists x; split; [unfold fun_upd in Hbuf1; clarify|].
          intro n'; specialize (Hbuf2 n'); split; clarify.
          { destruct Hbuf2 as [Hbuf2 _]; use Hbuf2; clarify.
            generalize (wf s x0); rewrite Forall_forall; intro Hx; apply Hx;
              auto.
            { exists x0; unfold fun_upd; clarify. } }
          { destruct Hbuf2 as [_ Hbuf2]; use Hbuf2; clarify.
            exists x0; unfold fun_upd in Hbuf2; clarify; omega.
            { rewrite app_length; omega. } }
          { specialize (Hbuf2 (thread_of op)); rewrite fun_upd_new in Hbuf2;
              clarify. }
  Qed.

  Corollary step_least : forall s op s' (Hstep : step s op s') n
    (Hleast : least_index s n), least_index s' n.
  Proof. intros; rewrite <- step_least_iff; eauto. Qed.

  Lemma least_le : forall s n (Hleast : least_index s n), n <= length (word s).
  Proof.
    unfold least_index; clarify.
    generalize (wf s x); rewrite Forall_forall; intro Hlt.
    specialize (Hlt _ Hleast1); omega.
  Qed.

  Lemma release_future : forall s t b n e Hbuf (Hleast : least_index s n)
    (He : nth_error (word s) n = Some e),
    future_hist (release_op s t b n e Hbuf) (S n) = future_hist s n.
  Proof.
    unfold future_hist; clarify.
    exploit map_nth_error; eauto; intro Hnth.
    erewrite (skipn_n _ _ Hnth); rewrite <- app_assoc; clarify.
  Qed.

  Lemma step_ops : forall s ops s' (Hsteps : step_star s ops s')
    n (Hleast : least_index s n),
    exists n', least_index s' n' /\ filter (@not_read _ _) (future_hist s' n') =
      filter (@not_read _ _) (future_hist s n ++ lower ops).
  Proof.
    intros ? ? ? ?; induction Hsteps; clarify; eauto.
    - repeat eexists; eauto; autorewrite with list; auto.
    - exploit step_least; eauto; intro Hleast'.
      specialize (IHHsteps _ Hleast'); destruct IHHsteps as [n' ?].
      exists n'; clarify.
      exploit step_cases'; eauto; intros [[t [p ?]] | [e ?]]; clarify.
      + unfold do_read in *.
        destruct (find (buf_match p) (make_buf m t)) eqn: Hfind;
          [destruct b|]; clarify; repeat rewrite filter_app; clarsimp.
        * rewrite filter_app; auto.
        * unfold future_hist; simpl; repeat rewrite filter_app; clarify.
          autorewrite with list; auto.
      + rewrite lower_cons; unfold future_hist in *; clarsimp.
        rewrite map_app; clarify.
        assert (not_read (buf_to_op e) = true) by (destruct c; clarify);
          clarify.
        generalize (least_le Hleast); intro. 
        assert (n - length (word m) = 0) by omega; clarsimp.
    - exploit release_least; eauto; clarify.
      exploit IHHsteps; eauto; clarify.
      eexists; split; eauto; clarsimp.
      rewrite release_future; auto.
  Qed.

  Lemma sees_last_fence : forall s ops s' (Hsteps : step_star s ops s')
    p i (Hlast : find_index (is_mod_op p) (rev ops) = Some i)
    w (Hw : nth_error ops (length ops - i - 1) = Some w)
    a (Ha : nth_error (to_seq w) 0 = Some a)
    j (Hlt : length ops - i - 1 < j)
    (Hf : nth_error ops j = Some (Fence (thread_of w))) t,
    sees_op s' t p a.
  Proof.
    intros.
    assert (is_mod_op p w = true) as Hmod.
    { rewrite find_index_spec in Hlast; clarify.
      exploit nth_error_rev'; eauto; clarsimp. }
    generalize (nth_error_split' _ _ Hw); intros [ops1 [ops2 ?]]; clarify.
    exploit step_star_app_inv; eauto; clarify.
    exploit step_star_cons_inv; eauto; intro Hstep2; clarify.
    exploit step_star_step; eauto; [repeat intro; clarify |
      intros [s1 Hs1]; clarify].
    rewrite nth_error_app in Hf; destruct (lt_dec j (length ops1)); [omega|].
    destruct (j - length ops1) eqn: Hminus; clarify.
    { rewrite H3 in *; clarify. }
    assert (forall x, In x ops2 -> is_mod_op p x = false) as Hnot_mod.
    { rewrite find_index_spec in Hlast; clarify.
      exploit in_nth_error; eauto; intros [i' Hi']; clarify.
      specialize (Hlast22 (length ops2 - i' - 1) x2).
      rewrite app_length in *; clarify.
      apply Hlast22.
      { clear - H1 Hi'1; omega. }
      rewrite rev_app_distr; clarify.
      rewrite nth_error_app, app_length, rev_length; simpl.
      destruct (lt_dec (length ops2 - i' - 1) (length ops2 + 1));
        [|clear - n1; omega].
      rewrite nth_error_app, rev_length; destruct (lt_dec (length ops2 - i' - 1)
        (length ops2)); [|clear - Hi'1 n1; omega].
      apply nth_error_rev; auto. }
    generalize (nth_error_split' _ _ Hf); intros [ops1' [ops2' ?]]; clarify.
    exploit step_star_app_inv; try (apply Hstep22); clarify.
    exploit step_star_cons_inv; eauto; clarify.
    exploit step_star_step'; eauto; intros [s2 Hs2]; clarify.
    assert (exists e, step_star (add_buf s1 (thread_of w) e) ops1' s2 /\
      buf_to_op e = a) as [e [Hs2' ?]].
    { unfold is_mod_op in *; destruct w; clarify;
        [exists (BWrite p0 v) | exists (BAlloc b n0) | exists (BFree b)];
        clarify; eapply step_star_nil_trans; eauto; eapply step_star_nil_trans2;
        eauto. }
    exploit buf_steps; eauto; try (intro Hcase); clarify.
    { unfold make_buf; simpl; rewrite fun_upd_new; simpl.
      instantiate (2 := p); rewrite nth_error_split; unfold buf_match; clarify.
      unfold is_mod_op in *; destruct w, e; clarify. }
    { rewrite fun_upd_new; simpl; eauto. }
    { apply nth_error_split. }
    { exploit nth_error_lt; eauto; rewrite app_length; simpl; omega. }
    destruct Hcase as [? | [? | ?]]; clarify.
    { setoid_rewrite in_app in Hnot_mod; exploit Hnot_mod; eauto; clarify. }
    { unfold make_buf in *; clarify; rewrite Hs2211 in *; clarify. }
    generalize (buf_gt Hs2' (thread_of w) (length (word s1))); simpl;
      rewrite fun_upd_new; intro Hgt; clarify.
    assert (step_star s2 ops2' s') by (eapply step_star_nil_trans; eauto).
    exploit no_pending_write; eauto.
    { instantiate (1 := p).
      intro t'; specialize (Hgt t').
      rewrite Forall_forall in *; intros e' Hin.
      exploit in_nth_error; eauto; clarify.
      exploit make_buf_nth; eauto; intro He; clarify.
      generalize (nth_error_in _ _ He1); intro Hin'.
      specialize (Hgt _ Hin').
      eapply word_add_none; try (apply He2); eauto.
      { rewrite Forall_forall; intros op ?.
        specialize (Hnot_mod op); rewrite in_app_iff in Hnot_mod;
          unfold is_mod_op in Hnot_mod; clarify. }
      { simpl.
        rewrite app_length, NPeano.Nat.add_1_r; simpl.
        apply lt_le_S; eauto. } }
    intro Hcase'.
    destruct Hcase' as [[w' ?] | [Hbuf Hhist]].
    { setoid_rewrite in_app in Hnot_mod; specialize (Hnot_mod w'); clarify. }
    unfold sees_op.
    specialize (Hbuf t).
    destruct (find (buf_match p) (make_buf s' t)) eqn: Hfind.
    - rewrite find_spec in Hfind; clarify.
      exploit nth_error_in; eauto; intro Hin.
      rewrite Forall_forall in Hbuf; specialize (Hbuf _ Hin); clarify.
    - rewrite Hhist; auto.
  Qed.
    
  Lemma hb_vis : forall ops i w p a m c s
    (Hlast : find_index (is_mod_op p) (rev ops) = Some i)
    (Hw : nth_error ops (length ops - i - 1) = Some w)
    (Ha : nth_error (to_seq w) 0 = Some a)
    (Hhb : happens_before (iapp ops m) (length ops - i - 1) (length ops))
    (Hc : inth m 0 = Some c) (Hsteps : step_star start_state ops s),
    sees_op s (thread_of c) p a.
  Proof.
    intros.
    rewrite find_index_spec in Hlast; destruct Hlast as [w' Hw']; clarify.
    exploit nth_error_rev'; eauto; clarsimp.
    exploit nth_error_lt; eauto; intro.
    exploit hb_fence; eauto.
    { rewrite iapp_nth; clarify; eauto. }
    { rewrite iapp_nth; clarsimp. }
    intros [? | Hfence].
    - exploit sees_last_thread; eauto; clarsimp; eauto.
      rewrite find_spec; eauto.
    - clarify.
      rewrite iapp_nth in *; clarify.
      eapply sees_last_fence; try (apply Hsteps); try (apply Hfence22); eauto.
      + rewrite find_index_spec; eauto.
      + destruct (eq_dec x (length ops - i - 1)); [|clear - Hfence1 n; omega].
        subst; rewrite Hw in Hfence22; clarify.
        rewrite H0 in Ha; clarify.
  Qed.

  Corollary hb_vis' : forall ops i w p a m c s
    (Hlast : find_index (is_mod_op p) (rev ops) = Some (length ops - i - 1))
    (Hw : nth_error ops i = Some w)
    (Ha : nth_error (to_seq w) 0 = Some a)
    (Hhb : happens_before (iapp ops m) i (length ops))
    (Ha : inth m 0 = Some c) (Hsteps : step_star start_state ops s),
    sees_op s (thread_of c) p a.
  Proof.
    intros.
    generalize (nth_error_lt _ _ Hw); intro.
    assert (length ops - (length ops - i - 1) - 1 = i) as Heq.
    { rewrite minus_distr; omega. }
    exploit hb_vis; eauto; clarsimp.
  Qed.

  Lemma least_start : least_index start_state 0.
  Proof. unfold least_index; right; clarify. Qed.
  Hint Resolve least_start.


  Lemma sees_unique : forall s t p a1 a2 (Ha1 : sees_op s t p a1)
    (Ha2 : sees_op s t p a2), a1 = a2.
  Proof.
    unfold sees_op; intros.
    destruct (find (buf_match p) (make_buf s t)); clarify.
    eapply last_op_unique; eauto.
  Qed.

  Lemma is_mod_mods : forall b o c (Hmod : is_mod_op (b, o) c = true),
    exists a, In a (to_seq c) /\ op_modifies _ a (b, o) = true.
  Proof.
    destruct c; unfold is_mod_op; clarify; do 2 eexists; eauto 2; clarify.
  Qed.

  Lemma hb_last : forall b (m : list _) m2 o a c s
    (Hbefore : forall i o, mods m i (b, o) ->
       happens_before (iapp m m2) i (length m))
    (Ha : inth m2 0 = Some c) (Hsteps : step_star start_state m s)
    (Hsees : sees_op s (thread_of c) (b, o) a),
    exists i w, find_index (is_mod_op (b, o)) (rev m) = Some i /\
      nth_error m (length m - i - 1) = Some w /\
      nth_error (to_seq w) 0 = Some a.
  Proof.
    intros.
    destruct (find_index (is_mod_op (b, o)) (rev m)) eqn: Hfind.
    - rewrite find_index_spec in Hfind; clarify.
      exploit nth_error_rev'; eauto; intro Hnth.
      do 4 eexists; eauto.
      assert (exists a', nth_error (to_seq x) 0 = Some a') as [a' Ha'].
      { unfold is_mod_op in *; destruct x; clarify; eauto. }
      assert (length m - (length m - n - 1) - 1 = n) as Hrev.
      { generalize (nth_error_lt _ _ Hfind1); rewrite rev_length; intro.
        repeat rewrite minus_distr; omega. }
      exploit hb_vis'; eauto.
      { rewrite Hrev, find_index_spec; eauto. }
      { eapply Hbefore; eauto.
        exploit is_mod_mods; eauto; clarify.
        unfold mods; rewrite inth_nth_error; eauto. }
      intro Hsees'; generalize (sees_unique _ _ _ _ _ Hsees Hsees'); clarsimp.
    - exploit (no_pending_write(s := start_state) (b, o)); eauto.
      { unfold make_buf; clarify. }
      intros [? | Hnone].
      { destruct H as [? [Hin ?]].
        rewrite find_index_fail, Forall_forall in Hfind.
        rewrite in_rev in Hin; specialize (Hfind _ Hin); clarify. }
      unfold sees_op in Hsees; clarify.
      setoid_rewrite <- find_fail in Hnone1; rewrite Hnone1, Hnone2 in Hsees.
      generalize (last_nil Hsees); clarify.
  Qed.
  (* These are the useful properties of the happens_before relation. *)

  Variable (val_eq : EqDec_eq val).

  Lemma least_unique : forall s n1 n2 (Hleast1 : least_index s n1)
    (Hleast2 : least_index s n2), n1 = n2.
  Proof.
    unfold least_index; intros.
    destruct Hleast1 as [[t1 Hsome1] | [? Hnone1]]; clarify;
      [|rewrite Hnone1 in *; clarify].
    destruct Hleast2 as [[t2 Hsome2] | [_ Hnone2]]; clarify;
      [|rewrite Hnone2 in *; clarify].
    specialize (Hsome12 n2); specialize (Hsome22 n1);
      destruct Hsome12 as [H1 _], Hsome22 as [H2 _]; use H1; use H2; eauto;
      omega.
  Qed.

  Definition next s := length (filter not_read (hist s)).

  Lemma least_start' : least_index start_state (next start_state).
  Proof. unfold next; auto. Qed.

  Lemma not_read_buf : forall e, not_read (buf_to_op e) = true.
  Proof. destruct e; auto. Qed.
  Hint Rewrite not_read_buf.

  Lemma least_hist : forall s ops s' (Hsteps : step_star s ops s')
    (Hleast : least_index s (next s)), least_index s' (next s').
  Proof.
    intros; induction Hsteps; clarify; apply IHHsteps; clear IHHsteps.
    - exploit step_cases; eauto; intros [[t [p ?]] | ?]; clarify.
      + unfold do_read in *; destruct (find (buf_match p) (make_buf m t));
          [destruct b|]; clarify.
        unfold next; simpl.
        rewrite filter_app, app_length; clarsimp.
      + exploit step_least; eauto.
    - generalize (release_least Hleast _ _ Hbuf Hnext e); clarify.
      unfold next at 2; simpl.
      rewrite filter_app, app_length; clarsimp.
  Qed.
      
  Variable (b0 : block).

  Fixpoint drop_b_reads b l :=
    match l with
    | [] => []
    | Read t p v :: l' => if beq (fst p) b then drop_b_reads b l'
                          else Read t p v :: drop_b_reads b l'
    | c :: l' => c :: drop_b_reads b l'
    end.

  Lemma future_read_past : forall s n i p v
    (Hread : nth_error (future_hist s n) i = Some (MRead p v)),
    nth_error (hist s) i = Some (MRead p v).
  Proof.
    unfold future_hist; intros.
    rewrite nth_error_app in Hread; clarify.
    rewrite skipn_nth in Hread; exploit nth_error_in; eauto.
    rewrite in_map_iff; intros [b ?]; destruct b; clarify.
  Qed.

  Lemma read_init_future : forall s n (Hread : read_init (hist s)),
    read_init (future_hist s n).
  Proof.
    repeat intro.
    rewrite inth_nth_error in *; exploit future_read_past; eauto; intro Hr.
    specialize (Hread i); rewrite inth_nth_error in Hread;
      specialize (Hread _ _ Hr).
    destruct Hread as [j [v' Hj]]; exists j, v'.
    exploit nth_error_lt; eauto; intro.
    unfold future_hist; assert (i - length (hist s) = 0)
      by (rewrite NPeano.Nat.sub_0_le; apply lt_le_weak; auto); clarsimp.
    generalize (nth_error_lt _ _ Hj2); rewrite nth_error_app; clarify.
  Qed.

  Lemma write_alloc_future_iff : forall s ops s' n n'
    (Hsteps : step_star s ops s') (Hleast : least_index s n)
    (Hleast' : least_index s' n'),
    write_alloc (future_hist s' n') <->
    write_alloc (future_hist s n ++ lower ops).
  Proof.
    intros; exploit step_ops; eauto; intros [? [Hleast'' ?]].
    generalize (least_unique Hleast'' Hleast'); clarify.
    setoid_rewrite <- write_alloc_filter; clarsimp; reflexivity.
  Qed.

  Corollary write_alloc_future : forall s ops s' n n'
    (Hsteps : step_star s ops s') (Hleast : least_index s n)
    (Hleast' : least_index s' n')
    (Hwrite : write_alloc (future_hist s n ++ lower ops)),
    write_alloc (future_hist s' n').
  Proof. intros; rewrite write_alloc_future_iff; eauto. Qed.
    
  Corollary write_alloc_future' : forall ops s n
    (Hsteps : step_star start_state ops s) (Hleast : least_index s n)
    (Hwrite : write_alloc (lower ops)),
    write_alloc (future_hist s n).
  Proof. intros; eapply write_alloc_future; eauto. Qed.

  Definition drop_b_reads_at b n1 n2 m := firstn n1 m ++
    let m' := skipn n1 m in drop_b_reads b (firstn n2 m') ++ skipn n2 m'.  

  Lemma drop_b_reads_app : forall b m1 m2, drop_b_reads b (m1 ++ m2) =
    drop_b_reads b m1 ++ drop_b_reads b m2.
  Proof.
    induction m1; clarify.
    rewrite IHm1; destruct a; clarify.
  Qed.

  Lemma drop_b_prefix : forall b m1 ops m2 (m : list _),
    iprefix m (iapp m1 (iapp ops m2)) ->
    iprefix (drop_b_reads_at b (length m1) (length ops) m)
      (iapp m1 (iapp (drop_b_reads b ops) m2)).
  Proof.
    intros.
    unfold drop_b_reads_at.
    exploit iprefix_app_inv; eauto; intros [Hpre | Hpre]; clarify.
    - exploit to_ilist_inj; eauto; clarify.
      rewrite firstn_firstn, skipn_all; clarsimp.
      rewrite <- (firstn_skipn (min (length m1) x) m1) at 3;
        rewrite <- iapp_app; apply iapp_prefix.
      { apply Min.le_min_r. }
    - rewrite to_ilist_app.
      exploit to_ilist_app_inv; eauto; clarsimp.
      apply prefix_mono.
      rewrite skipn_all; clarsimp.
      generalize (iprefix_app_inv _ _ Hpre2); intros [? | ?]; clarify.
      + exploit to_ilist_inj; eauto; clarify.
        rewrite firstn_firstn, skipn_all; clarsimp.
        rewrite <- (firstn_skipn (min (length ops) x) ops) at 3;
          rewrite drop_b_reads_app; rewrite <- iapp_app; apply iapp_prefix.
      { apply Min.le_min_r. }
      + rewrite to_ilist_app. 
        exploit to_ilist_app_inv; eauto; clarsimp.
        apply prefix_mono.
        rewrite skipn_all; auto.
  Qed.
  
  Lemma firstn_drop : forall b m n, exists n', n' <= length m /\
    firstn n (drop_b_reads b m) = drop_b_reads b (firstn n' m).
  Proof.
    induction m; clarify.
    - repeat setoid_rewrite firstn_nil; eauto.
    - destruct n; [exists 0|]; clarify; [omega|].
      destruct a; try (specialize (IHm n); destruct IHm as [n' ?];
        exists (S n'); clarsimp; omega).
      destruct (beq (fst p) b) eqn: Hb.
      + specialize (IHm (S n)); destruct IHm as [n' ?]; exists (S n'); clarsimp;
          omega.
      + specialize (IHm n); destruct IHm as [n' ?]; exists (S n'); clarsimp;
          omega.
  Qed.

  Lemma add_b_prefix : forall b m1 ops m2 (m : list _),
    iprefix m (iapp m1 (iapp (drop_b_reads b ops) m2)) ->
    exists m', drop_b_reads_at b (length m1) (length ops) m' = m /\
      iprefix m' (iapp m1 (iapp ops m2)).
  Proof.
    intros.
    unfold drop_b_reads_at.
    exploit iprefix_app_inv; eauto; intros [Hpre | Hpre]; clarify.
    - exists m; exploit to_ilist_inj; eauto; clarify.
      rewrite firstn_firstn, skipn_all; clarsimp.
      split.
      + generalize (Min.min_spec (length m1) x); intros [? | ?]; clarsimp.
        rewrite firstn_length'; [auto | omega].
      + rewrite <- (firstn_skipn x m1) at 2;
          rewrite <- iapp_app; apply iapp_prefix.
      + apply Min.le_min_r.
    - exploit to_ilist_app_inv; eauto; clarsimp.
      generalize (iprefix_app_inv _ _ Hpre2); intros [? | ?]; clarify.
      + exploit to_ilist_inj; eauto; clarify.
        generalize (firstn_drop b ops x); intros [n' ?]; clarsimp.
        exists (m1 ++ firstn n' ops); clarsimp.
        rewrite firstn_firstn, skipn_all; clarsimp.
        rewrite skipn_all; clarsimp.
        rewrite Min.min_r; clarify.
        rewrite to_ilist_app; apply prefix_mono.
        rewrite <- (firstn_skipn n' ops) at 2; rewrite <- iapp_app.
        apply iapp_prefix.
        { apply Min.le_min_r. }
      + exploit to_ilist_app_inv; eauto; clarsimp.
        exists (m1 ++ ops ++ x1); clarsimp.
        repeat rewrite skipn_all; clarsimp.
        repeat (rewrite to_ilist_app; apply prefix_mono); auto.
        { omega. }
  Qed.

  Definition ext s1 s2 := filter not_read (hist s1) = filter not_read (hist s2)
    /\ wbuf s1 = wbuf s2 /\ word s1 = word s2.

  Instance ext_refl : Reflexive ext.
  Proof. intro; unfold ext; auto. Qed.

  Instance ext_eq : Equivalence ext.
  Proof.
    constructor; repeat intro.
    - reflexivity.
    - unfold ext in *; clarsimp.
    - unfold ext in *; clarsimp.
  Qed.

  Lemma read_ext : forall s t p v s' (Hread : do_read s t p v s'), ext s s'.
  Proof.
    unfold do_read; intros.
    destruct (find (buf_match p) (make_buf s t)); [destruct b|]; clarify.
    - reflexivity.
    - unfold ext; clarify.
      rewrite filter_app; clarsimp.
  Qed.
  
  Lemma ext_least : forall s s' n (Hleast : least_index s n) (Hext : ext s s'),
    least_index s' n.
  Proof.
    unfold least_index, ext; clarify.
    destruct Hleast as [? | ?]; [left | right]; clarify;
      rewrite Hext21, Hext22 in *; eauto.
  Qed.

  Lemma write_alloc_ext : forall s s' n (Hext : ext s s')
    (Hwrite : write_alloc (future_hist s n)), write_alloc (future_hist s' n).
  Proof.
    unfold ext, future_hist; clarify.
    setoid_rewrite <- write_alloc_filter;
      setoid_rewrite <- write_alloc_filter in Hwrite.
    rewrite filter_app in *; clarsimp.
  Qed.

  Definition con_do_read m t p v m' :=
    match find (buf_match p) (make_buf m t) with
    | Some (BWrite _ v') => v' = v /\ m' = m
    | Some (BAlloc _ _) => False
    | Some (BFree _) => False
    | None => m' = upd_hist m (hist m ++ [MRead p v]) /\
        last_op (hist m) (Ptr p) (MWrite p v)
    end.

  Definition con_step n m c m' :=
    match c with
    | Read t p v => con_do_read m t p v m'
    | Write t p v => m' = add_buf m t (BWrite p v) /\
        ((exists v', last_op (future_hist m n) (Ptr p) (MWrite p v')) \/
         (exists z, last_op (future_hist m n) (Ptr p) (MAlloc (fst p) z) /\
            snd p < z))
    | Alloc t b z => m' = add_buf m t (BAlloc b z) /\
        (forall z', ~last_op (future_hist m n) (Block b) (MAlloc b z')) /\
        (forall p v, ~last_op (future_hist m n) (Block b) (MWrite p v))
    | Free t b => m' = add_buf m t (BFree b) /\
        ((exists p v', last_op (future_hist m n) (Block b) (MWrite p v')) \/
         (exists z, last_op (future_hist m n) (Block b) (MAlloc b z)))
    | Fence _ => False
    end.

  Inductive con_steps (s : mem_state) : list base_op -> mem_state -> Prop :=
  | cstep_refl : con_steps s [] s
  | cstep_op : forall n (Hleast : least_index s n) c s'
      (Hstep : con_step n s c s') ops s'' (Hsteps : con_steps s' ops s''),
      con_steps s (c :: ops) s''
  | cstep_write_buf : forall t b n (Hbuf : wbuf s t = b ++ [n])
      (Hnext : forall t', Forall (fun i : nat => n < i)
         (fun_upd (wbuf s) t b t')) e (He : nth_error (word s) n = Some e)
      ops s' (Hsteps : con_steps (release_op s t b n e Hbuf) ops s'),
      con_steps s ops s'
  | cstep_fence : forall t (Hempty : wbuf s t = []) ops s'
      (Hsteps : con_steps s ops s'), con_steps s (Fence t :: ops) s'.

  Definition con_state s := exists n, least_index s n /\ read_init (hist s) /\
    write_alloc (future_hist s n) /\ seq_con (future_hist s n).

  Lemma con_step_step : forall n s c s', con_step n s c s' -> step s c s'.
  Proof.
    destruct c; clarify.
    unfold con_do_read, do_read in *;
      destruct (find (buf_match p) (make_buf s t)); clarify.
  Qed.

  Lemma con_steps_steps : forall s ops s' (Hsteps : con_steps s ops s'),
    step_star s ops s'.
  Proof.
    intros; induction Hsteps; eauto.
    econstructor; eauto; eapply con_step_step; eauto.
  Qed.

  Lemma con_read : forall s (Hcon : con_state s) p v
    (Hlast : last_op (hist s) (Ptr p) (MWrite p v)),
    con_state (upd_hist s (hist s ++ [MRead p v])).
  Proof.
    unfold con_state; clarify.
    eexists; split; eauto; split; [|split].
    - rewrite read_init_snoc; eauto.
    - eapply write_alloc_ext; eauto.
      unfold ext; clarify; rewrite filter_app; clarsimp.
    - unfold future_hist in *; simpl.
      rewrite <- app_assoc, to_ilist_app in *; apply read_consistent_op; auto.
  Qed.

  Lemma con_write : forall s (Hcon : con_state s) t p v n
    (Hleast : least_index s n)
    (Hlast : (exists v', last_op (future_hist s n) (Ptr p) (MWrite p v')) \/
      (exists z, last_op (future_hist s n) (Ptr p) (MAlloc (fst p) z) /\
        snd p < z)), con_state (add_buf s t (BWrite p v)).
  Proof.
    unfold con_state, future_hist; clarify.
    generalize (least_unique Hcon1 Hleast); clarify.
    generalize (step_least(s := s) (Write t p v) (add_buf s t (BWrite p v)));
      intro Hleast'; clarify.
    specialize (Hleast' _ Hleast); eexists; split; eauto; clarify.
    rewrite map_app, skipn_app; simpl.
    destruct (n - length (map buf_to_op (word s))); clarsimp.
    assert (write_alloc ((hist s ++ skipn n (map buf_to_op (word s))) ++
      [MWrite p v])) as Hwrite by (rewrite write_alloc_snoc; auto);
      rewrite app_assoc; clarify.
    exploit (simple_op _ Hcon222); eauto.
    { rewrite read_init_snoc; auto.
      apply read_init_future; auto. }
    intros [sm [? Hcan]]; rewrite Hcan; simpl.
    destruct p as (b, o); destruct Hlast; clarify; exploit (simple_last_op _ H);
      eauto; clarify.
    exploit nth_error_lt; eauto; omega.
  Qed.

  Lemma con_alloc : forall s (Hcon : con_state s) t b z n
    (Hleast : least_index s n)
    (Hlast1 : forall z', ~last_op (future_hist s n) (Block b) (MAlloc b z'))
    (Hlast2 : forall p v, ~last_op (future_hist s n) (Block b) (MWrite p v)),
    con_state (add_buf s t (BAlloc b z)).
  Proof.
    unfold con_state, future_hist; clarify.
    generalize (least_unique Hcon1 Hleast); clarify.
    generalize (step_least(s := s) (Alloc t b z) (add_buf s t (BAlloc b z)));
      intro Hleast'; clarify.
    specialize (Hleast' _ Hleast); eexists; split; eauto; clarify.
    rewrite map_app, skipn_app; simpl.
    destruct (n - length (map buf_to_op (word s))); clarsimp.
    assert (write_alloc ((hist s ++ skipn n (map buf_to_op (word s))) ++
      [MAlloc b z])) as Hwrite by (rewrite write_alloc_snoc; auto);
      rewrite app_assoc; clarify.
    exploit (simple_op _ Hcon222); eauto.
    { rewrite read_init_snoc; auto.
      apply read_init_future; auto. }
    intros [sm [? Hcan]]; rewrite Hcan; clarify.
    destruct (last_op_dec _ (Block b) Hcon222) as [Hlast | Hlast]; clarify.
    + exploit (simple_last_block_op _ H); eauto.
      destruct x; clarify.
      { specialize (Hlast2 _ _ Hlast); auto. }
      { assert (b0 = b).
        { destruct Hlast as [? [Hlast ?]]; inversion Hlast; clarsimp.
          destruct (eq_dec b0 b); clarify. }
        subst; specialize (Hlast1 _ Hlast); auto. }
    + exploit (simple_no_last_op _ H); eauto; clarify.
  Qed.

  Lemma con_free : forall s (Hcon : con_state s) t b n
    (Hleast : least_index s n)
    (Hlast : (exists p v', last_op (future_hist s n) (Block b) (MWrite p v')) \/
      (exists z, last_op (future_hist s n) (Block b) (MAlloc b z))),
    con_state (add_buf s t (BFree b)).
  Proof.
    unfold con_state, future_hist; clarify.
    generalize (least_unique Hcon1 Hleast); clarify.
    generalize (step_least(s := s) (Free t b) (add_buf s t (BFree b)));
      intro Hleast'; clarify.
    specialize (Hleast' _ Hleast); eexists; split; eauto; clarify.
    rewrite map_app, skipn_app; simpl.
    destruct (n - length (map buf_to_op (word s))); clarsimp.
    assert (write_alloc ((hist s ++ skipn n (map buf_to_op (word s))) ++
      [MFree b])) as Hwrite by (rewrite write_alloc_snoc; auto);
      rewrite app_assoc; clarify.
    exploit (simple_op _ Hcon222); eauto.
    { rewrite read_init_snoc; auto.
      apply read_init_future; auto. }
    intros [sm [? Hcan]]; rewrite Hcan; clarify.
    destruct Hlast; clarify; exploit (simple_last_block_op _ H); eauto; clarify.
    destruct x; clarify.
  Qed.

  Lemma con_state_step : forall s (Hcon : con_state s)
    n (Hleast : least_index s n) c s' (Hstep : con_step n s c s'),
    con_state s'.
  Proof.
    intros.
    exploit step_least; eauto; [eapply con_step_step; eauto|]; intro Hleast'.
    unfold con_state in *; clarify.
    generalize (least_unique Hcon1 Hleast); exists n; clarify.
    destruct c; clarify.
    - unfold con_do_read in *; destruct (find (buf_match p) (make_buf s t));
        [destruct b|]; clarify.
      exploit con_read; eauto; [eexists; eauto|].
      unfold con_state; intros [? [Hleast' ?]].
      generalize (least_unique(n2 := n) Hleast'); clarify.
    - exploit con_write; try (apply Hstep2); eauto; [eexists; eauto|].
      unfold con_state; intros [? [Hleast2 ?]].
      generalize (least_unique Hleast2 Hleast'); clarify.
    - exploit con_alloc; try (apply Hstep21); eauto; [eexists; eauto|].
      unfold con_state; intros [? [Hleast2 ?]].
      generalize (least_unique Hleast2 Hleast'); clarify.
    - exploit con_free; try (apply Hstep2); eauto; [eexists; eauto|].
      unfold con_state; intros [? [Hleast2 ?]].
      generalize (least_unique Hleast2 Hleast'); clarify.
  Qed.

  Lemma con_release : forall s (Hcon : con_state s) t b n e Hbuf
    (Hnext : forall t', Forall (fun i => n < i) (fun_upd (wbuf s) t b t'))
    (He : nth_error (word s) n = Some e),
    con_state (release_op s t b n e Hbuf).
  Proof.
    unfold con_state; clarify.
    exploit release_least; eauto; clarify.
    do 2 eexists; eauto.
    rewrite release_future; clarify.
    rewrite read_init_snoc; destruct e; clarify.
  Qed.

  Lemma con_state_steps : forall s (Hcon : con_state s) ops s'
    (Hsteps : con_steps s ops s'), con_state s'.
  Proof.
    intros; induction Hsteps; auto; apply IHHsteps; clear IHHsteps.
    - eapply con_state_step; eauto.
    - apply con_release; auto.
  Qed.

  Lemma con_retract : forall s ops s' (Hsteps : step_star s ops s')
    n (Hleast : least_index s n) (Hcon : con_state s'), con_state s.
  Proof.
    intros.
    unfold con_state in *; clarify.
    exploit step_ops; eauto; intros [? [Hleast' ?]].
    generalize (least_unique Hleast' Hcon1); clarify.
    do 2 eexists; eauto.
    exploit hist_mono; eauto; intro Hhist; clarsimp.
    assert (read_init (hist s)).
    { eapply read_init_app; eauto. }
    assert (write_alloc (future_hist s n)).
    { rewrite write_alloc_future_iff in Hcon221; eauto.
      eapply write_alloc_app; eauto. }
    clarify; setoid_rewrite consistent_split_reads; auto.
    setoid_rewrite consistent_split_reads in Hcon222; clarsimp.
    split; [rewrite filter_app in *; eapply consistent_app; eauto | intros].
    exploit future_read_past; eauto; intro Hnth.
    specialize (Hcon2222 r); unfold future_hist in *; rewrite Hhist in Hcon2222;
      rewrite <- app_assoc in Hcon2222.
    exploit nth_error_lt; eauto; rewrite nth_error_app in Hcon2222; clarify.
    specialize (Hcon2222 _ _ Hnth).
    rewrite firstn_app, not_le_minus_0 in *; clarify; omega.
    { apply read_init_future; clarsimp. }
    { apply read_init_future; auto. }
  Qed.

  Corollary con_iff : forall s ops s' (Hsteps : con_steps s ops s')
    n (Hleast : least_index s n), con_state s' <-> con_state s.
  Proof.
    intros; split; intro.
    - exploit con_steps_steps; eauto; intro.
      eapply con_retract; eauto.
    - eapply con_state_steps; eauto.
  Qed.

  Hint Constructors con_steps.

  Lemma ext_future : forall s1 s2 (Hext : ext s1 s2)
    n (Hleast : least_index s1 n) l a,
    last_op (future_hist s1 n) l a <-> last_op (future_hist s2 n) l a.
  Proof.
    unfold ext, future_hist; clarsimp.
    setoid_rewrite <- last_op_filter; repeat rewrite filter_app; clarsimp;
      reflexivity.
  Qed.

  Lemma ext_sim' : forall s1 ops s1' (Hcon' : con_state s1)
    (Hsteps : con_steps s1 ops s1')
    s2 (Hext : ext s1 s2) (Hcon : con_state s2),
    exists s2', con_steps s2 ops s2' /\ ext s1' s2'.
  Proof.
    intros ? ? ? ? ?; induction Hsteps; eauto; clarify.
    - generalize (con_state_step Hcon' Hleast _ _ Hstep); clarify.
      exploit ext_least; eauto; intro Hleast2.
      exploit con_step_step; eauto; intro.
      exploit step_least; eauto; intro Hleast'.
      destruct c; clarify.
      + unfold con_do_read in *.
        destruct (find (buf_match p) (make_buf s t)) eqn: Hfind; [destruct b|];
          clarify.
        * specialize (IHHsteps _ Hext Hcon);
            destruct IHHsteps as [s2' ?]; exists s2'; clarify.
          econstructor; eauto; clarify.
          unfold ext in Hext; clarify.
          unfold con_do_read, make_buf in *; rewrite Hext21, Hext22 in Hfind;
            clarify.
        * unfold ext in Hext; clarify.
          assert (ext (upd_hist s (hist s ++ [MRead p v]))
            (upd_hist s2 (hist s2 ++ [MRead p v]))) as Hext'.
          { split; clarify.
            repeat rewrite filter_app; clarsimp. }
          assert (last_op (hist s2) (Ptr p) (MWrite p v)).
          { setoid_rewrite <- last_op_filter;
              setoid_rewrite <- last_op_filter in Hstep2; clarsimp. }
          exploit (con_read Hcon); eauto; intro Hcon2.
          specialize (IHHsteps _ Hext' Hcon2); destruct IHHsteps as [s2' ?];
            exists s2'; clarify.
          econstructor; eauto; clarify.
          unfold con_do_read, make_buf in *; rewrite Hext21, Hext22 in Hfind;
            rewrite Hfind; clarify.
      + assert ((exists v', last_op (future_hist s2 n) (Ptr p) (MWrite p v')) \/
          (exists z, last_op (future_hist s2 n) (Ptr p) (MAlloc (fst p) z) /\
            snd p < z)).
        { destruct Hstep2 as [Hstep2 | [? [Hstep2 ?]]]; [left | right]; clarify;
            rewrite ext_future in Hstep2; eauto. }
        exploit (con_write Hcon); eauto; intro Hcon2.
        unfold ext in Hext; clarify.
        assert (ext (add_buf s t (BWrite p v)) (add_buf s2 t (BWrite p v)))
          as Hext' by (split; clarsimp).
        specialize (IHHsteps _ Hext' Hcon2); destruct IHHsteps as [s2' ?];
          exists s2'; clarify.
        econstructor; eauto; clarify.
      + assert (forall z', ~last_op (future_hist s2 n) (Block b) (MAlloc b z')).
        { intro; rewrite <- ext_future; eauto. }
        assert (forall p v, ~last_op (future_hist s2 n) (Block b) (MWrite p v)).
        { intros; rewrite <- ext_future; eauto. }
        exploit (con_alloc Hcon); eauto; intro Hcon2.
        unfold ext in Hext; clarify.
        assert (ext (add_buf s t (BAlloc b n0)) (add_buf s2 t (BAlloc b n0)))
          as Hext' by (split; clarsimp).
        specialize (IHHsteps _ Hext' Hcon2); destruct IHHsteps as [s2' ?];
          exists s2'; clarify.
        econstructor; eauto; clarify.
      + assert ((exists p v', last_op (future_hist s2 n) (Block b)
          (MWrite p v')) \/ (exists z, last_op (future_hist s2 n) (Block b)
          (MAlloc b z))).
        { destruct Hstep2 as [Hstep2 | [? Hstep2]]; [left | right]; clarify;
            rewrite ext_future in Hstep2; eauto. }
        exploit (con_free Hcon); eauto; intro Hcon2.
        unfold ext in Hext; clarify.
        assert (ext (add_buf s t (BFree b)) (add_buf s2 t (BFree b)))
          as Hext' by (split; clarsimp).
        specialize (IHHsteps _ Hext' Hcon2); destruct IHHsteps as [s2' ?];
          exists s2'; clarify.
        econstructor; eauto; clarify.
    - exploit (con_release Hcon'); eauto; intro Hcon1.
      unfold ext in Hext; clarsimp.
      assert (wbuf s2 t = b ++ [n]) as Hbuf' by (rewrite <- Hext21; auto).
      exploit (con_release Hcon); eauto; intro Hcon2.
      specialize (IHHsteps (release_op _ _ _ _ e Hbuf')); use IHHsteps.
      specialize (IHHsteps Hcon2); 
        destruct IHHsteps as [s2' ?]; exists s2'; split; clarify.
      + eapply cstep_write_buf; eauto; clarsimp.
      + split; clarsimp.
        repeat rewrite filter_app; clarsimp.
    - specialize (IHHsteps _ Hext Hcon);
        destruct IHHsteps as [s2' ?]; exists s2'; clarify.
      constructor; auto.
      unfold ext in Hext; clarify.
      rewrite <- Hext21; auto.
  Qed.

  Lemma con_step_drop : forall b ops s1 s1' (Hsteps : con_steps s1 ops s1')
    s2 (Hext : ext s1 s2),
    exists s2', con_steps s2 (drop_b_reads b ops) s2' /\ ext s1' s2'.
  Proof.
    intros ? ? ? ? ?; induction Hsteps; clarify; eauto.
    - exploit ext_least; eauto; intro Hleast'.
      destruct c; clarify.
      + unfold con_do_read in *; destruct (find (buf_match p) (make_buf s t))
          eqn: Hfind; [destruct b0|]; clarify.
        * specialize (IHHsteps _ Hext); destruct IHHsteps as [s2' ?];
            exists s2'; clarify.
          econstructor; eauto; clarify.
          unfold con_do_read, make_buf in *; unfold ext in Hext; clarify.
          rewrite Hext21, Hext22 in Hfind; clarify.
        * destruct (beq (fst p) b).
          { apply IHHsteps; unfold ext in *; clarsimp.
            rewrite filter_app; clarsimp. }
          { specialize (IHHsteps (upd_hist s2 (hist s2 ++ [MRead p v])));
              use IHHsteps.
            destruct IHHsteps as [s2' ?]; exists s2'; clarify.
            econstructor; eauto; clarify.
            unfold con_do_read, make_buf in *; unfold ext in Hext; clarify.
            rewrite Hext21, Hext22 in Hfind; rewrite Hfind; clarify.
            setoid_rewrite <- last_op_filter;
              setoid_rewrite <- last_op_filter in Hstep2; clarsimp.
            { unfold ext in *; clarsimp.
              repeat rewrite filter_app; clarsimp. } }
      + specialize (IHHsteps (add_buf s2 t (BWrite p v))); use IHHsteps.
        destruct IHHsteps as [s2' ?]; exists s2'; clarify.
        econstructor; eauto; clarify.
        destruct Hstep2 as [Hstep2 | [? [Hstep2 ?]]]; [left | right]; clarify;
          rewrite ext_future in Hstep2; eauto.
        { unfold ext in Hext; split; clarsimp. }
      + specialize (IHHsteps (add_buf s2 t (BAlloc b0 n0))); use IHHsteps.
        destruct IHHsteps as [s2' ?]; exists s2'; clarify.
        econstructor; eauto; clarify.
        split; repeat intro; [eapply Hstep21 | eapply Hstep22];
          rewrite ext_future; eauto.
        { unfold ext in Hext; split; clarsimp. }
      + specialize (IHHsteps (add_buf s2 t (BFree b0))); use IHHsteps.
        destruct IHHsteps as [s2' ?]; exists s2'; clarify.
        econstructor; eauto; clarify.
        destruct Hstep2 as [Hstep2 | Hstep2]; [left | right]; clarify;
          rewrite ext_future in Hstep2; eauto.
        { unfold ext in Hext; split; clarsimp. }
    - unfold ext in Hext; clarify.
      assert (wbuf s2 t = b1 ++ [n]) as Hbuf' by (rewrite <- Hext21; auto).
      specialize (IHHsteps (release_op _ _ _ _ e Hbuf')); use IHHsteps.
      destruct IHHsteps as [s2' ?]; exists s2'; clarify.
      eapply cstep_write_buf; eauto; clarsimp.
      { split; clarsimp.
        repeat rewrite filter_app; clarsimp. }
    - specialize (IHHsteps _ Hext); destruct IHHsteps as [s2' ?]; exists s2';
        clarify.
      constructor; auto.
      unfold ext in Hext; clarify.
      rewrite <- Hext21; auto.
  Qed.

  Lemma sees_step : forall s t p v (Hsees : sees_op s t p (MWrite p v)),
    exists s', do_read s t p v s'.
  Proof.
    unfold do_read, sees_op; intros.
    destruct (find (buf_match p) (make_buf s t)); [destruct b|]; clarify; eauto.
    inversion Hsees; clarify; eauto.
  Qed.

  Lemma con_start : con_state start_state.
  Proof.
    unfold con_state; do 2 eexists; eauto; clarify.
    split; [|split].
    - apply read_init_nil.
    - apply write_alloc_nil.
    - apply block_model.consistent_nil; auto.
  Qed.

  Lemma step_star_con : forall s ops s' (Hsteps : step_star s ops s')
    (Hcon : con_state s) (Hcon' : con_state s'), con_steps s ops s'.
  Proof.
    intros; induction Hsteps; eauto.
    - unfold con_state in Hcon; clarify.
      exploit con_retract; eauto.
      { eapply step_least; eauto. }
      intro Hcons; clarify.
      econstructor; eauto.
      exploit step_least; eauto; intro Hleast.
      destruct c; clarify.
      + unfold do_read, con_do_read in *.
        destruct (find (buf_match p) (make_buf m t)); clarify.
        unfold con_state in Hcons; destruct Hcons as [n [? [Hread ?]]].
        generalize (read_init_future _ n Hread); clarify.
        unfold future_hist in *; clarsimp.
        rewrite to_ilist_app in *; eapply read_justified_op; eauto.
      + unfold con_state in Hcons; clarify.
        generalize (least_unique Hcons1 Hleast); clarify.
        unfold future_hist in Hcons221, Hcons222; clarify.
        rewrite map_app, skipn_app in *.
        generalize (least_le Hcon1); rewrite <- NPeano.Nat.sub_0_le; clarsimp.
        rewrite app_assoc in *.
        exploit (simple_op _ Hcon222); eauto.
        { rewrite read_init_snoc; auto.
          apply read_init_future; auto. }
        intros [sm [Hsm Hcan]].
        rewrite Hcan in Hcons222; clarify.
        destruct p as (b, o); clarify.
        destruct (sm b) eqn: Hb; clarify.
        destruct (last_op_dec (future_hist m x) (Ptr (b, o)))
          as [[a Hlast] | Hlast]; auto.
        * exploit (simple_last_op _ Hsm); eauto; destruct a; clarsimp;
            [left | right].
          { assert (p = (b, o)); [|clarify; eauto].
            destruct Hlast as [? [Hlast ?]]; inversion Hlast; clarsimp.
            destruct (eq_dec p (b, o)); clarify. }
          { assert (b0 = b); [|clarify; eauto].
            destruct Hlast as [? [Hlast ?]]; inversion Hlast; clarsimp.
            destruct (eq_dec b0 b); clarify. }
        * exploit (simple_no_last_op _ Hsm); eauto; clarify.
      + unfold con_state in Hcons; clarify.
        generalize (least_unique Hcons1 Hleast); clarify.
        unfold future_hist in Hcons221, Hcons222; clarify.
        rewrite map_app, skipn_app in *.
        generalize (least_le Hcon1); rewrite <- NPeano.Nat.sub_0_le; clarsimp.
        rewrite app_assoc in *.
        exploit (simple_op _ Hcon222); eauto.
        { rewrite read_init_snoc; auto.
          apply read_init_future; auto. }
        intros [sm [Hsm Hcan]].
        rewrite Hcan in Hcons222; clarify.
        destruct (last_op_dec (future_hist m x) (Block b))
          as [[a Hlast] | Hlast]; auto.
        exploit (simple_last_block_op _ Hsm); eauto; destruct a; clarsimp.
        { destruct p; clarify. }
        split; [intros ? Hlast' | intros ? ? Hlast'];
          generalize (last_op_unique Hlast Hlast'); clarify.
      + unfold con_state in Hcons; clarify.
        generalize (least_unique Hcons1 Hleast); clarify.
        unfold future_hist in Hcons221, Hcons222; clarify.
        rewrite map_app, skipn_app in *.
        generalize (least_le Hcon1); rewrite <- NPeano.Nat.sub_0_le; clarsimp.
        rewrite app_assoc in *.
        exploit (simple_op _ Hcon222); eauto.
        { rewrite read_init_snoc; auto.
          apply read_init_future; auto. }
        intros [sm [Hsm Hcan]].
        rewrite Hcan in Hcons222; clarify.
        destruct (last_op_dec (future_hist m x) (Block b))
          as [[a Hlast] | Hlast]; auto.
        * exploit (simple_last_block_op _ Hsm); eauto; destruct a; clarsimp;
            [left | right]; eauto.
          assert (b0 = b); [|clarify; eauto].
          destruct Hlast as [? [Hlast ?]]; inversion Hlast; clarsimp.
          destruct (eq_dec b0 b); clarify.
        * exploit (simple_no_last_op _ Hsm); eauto; clarify.
    - exploit (con_release Hcon); eauto.
  Qed.

  Lemma con_steps_app_inv : forall ops1 ops2 s s'
    (Hsteps : con_steps s (ops1 ++ ops2) s'),
    exists s'', con_steps s ops1 s'' /\ con_steps s'' ops2 s'.
  Proof.
    intros; remember (ops1 ++ ops2) as ops; revert ops1 ops2 Heqops;
      induction Hsteps; clarify.
    - destruct ops1; clarify; eauto.
    - destruct ops1; clarify; eauto.
      specialize (IHHsteps _ _ eq_refl); clarify; eauto.
    - specialize (IHHsteps _ _ eq_refl); clarify; eauto.
    - destruct ops1; clarify; eauto.
      specialize (IHHsteps _ _ eq_refl); clarify; eauto.
  Qed.
    
  Lemma con_steps_trans : forall ops1 ops2 s s1 s2
    (Hsteps1 : con_steps s ops1 s1) (Hsteps2 : con_steps s1 ops2 s2),
    con_steps s (ops1 ++ ops2) s2.
  Proof. intros; induction Hsteps1; clarsimp; eauto. Qed.

  Lemma sees_con_step : forall s t p v (Hsees : sees_op s t p (MWrite p v)),
    exists s', con_do_read s t p v s'.
  Proof.
    unfold con_do_read, sees_op; intros.
    destruct (find (buf_match p) (make_buf s t)); [destruct b|]; clarify; eauto.
    inversion Hsees; clarify; eauto.
  Qed.

  Lemma con_read_ext : forall s t p v s' (Hread : con_do_read s t p v s'),
    ext s s'.
  Proof.
    unfold con_do_read; intros.
    destruct (find (buf_match p) (make_buf s t)); [destruct b|]; clarify.
    - reflexivity.
    - unfold ext; clarify.
      rewrite filter_app; clarsimp.
  Qed.
  
  Lemma seq_con_step : forall b m1 s1 s2 t ops m2 s1'
    (Ht : Forall (fun c => thread_of c = t) ops)
    (Hstep1 : con_steps start_state m1 s1)
    (Hstep2 : con_steps start_state m1 s2)
    (Hstep : con_steps s1 (drop_b_reads b ops) s1') (Hext : ext s1 s2)
    (Hbefore : forall i o, mods m1 i (b, o) ->
       happens_before (iapp m1 (iapp ops m2)) i (length m1))
    (Hseq : seq_con (filter (b_not_read b) (lower m1) ++
       proj_block (lower ops) b))
    (Hread_init : read_init (filter (b_not_read b) (lower m1) ++
       proj_block (lower ops) b)),
    exists s2', con_steps s2 ops s2' /\ ext s1' s2'.
  Proof.
    induction ops using rev_ind; clarify.
    { eapply ext_sim'; eauto;
        eapply con_state_steps; eauto; apply con_start. }
    rewrite drop_b_reads_app in Hstep; exploit con_steps_app_inv; eauto;
      intros [s Hs]; specialize (IHops (icons x m2) s).
    rewrite lower_app, proj_block_app in Hseq, Hread_init.
    rewrite Forall_app in Ht; clarify.
    inversion Ht2; clarify.
    rewrite <- iapp_app in Hbefore; clarify.
    use IHops. use IHops. clarify.
    generalize (con_state_steps con_start Hstep1); intro Hcon1.
    generalize (con_state_steps Hcon1 Hs1); intro Hcon.
    generalize (con_state_steps con_start Hstep2); intro Hcon2.
    generalize (con_state_steps Hcon2 IHops1); intro Hcon0.
    generalize (ext_sim' Hcon Hs2 IHops2 Hcon0); intros [s2' [? ?]].
    destruct x; try (exists s2'; clarify; eapply con_steps_trans; eauto; fail).
    destruct (beq (fst p) b) eqn: Hb;
      [|exists s2'; clarify; eapply con_steps_trans; eauto].
    assert (sees_op s2' t p (MWrite p v)).
    { clarify.
      rewrite app_assoc, to_ilist_app in Hseq, Hread_init.
      exploit read_justified_op; eauto; intro Hlast.
      destruct p as (?, o); unfold beq in Hb; clarify.
      assert (last_op (lower (m1 ++ ops)) (Ptr (b, o)) (MWrite (b, o) v)).
      { rewrite <- last_op_filter, filter_app in Hlast.
        rewrite last_op_proj; rewrite <- last_op_filter, lower_app,
          proj_block_app, filter_app.
        unfold proj_block at 1; rewrite filter_filter.
        erewrite filter_filter, filter_ext in Hlast; eauto.
        { rewrite Forall_forall; unfold b_not_read, andb; clarify. } }
      exploit lift_last_write; eauto; intros [i [w Hi]]; clarify.
      assert (t = thread_of (Read t (b, o) v)) as Ht by auto; rewrite Ht;
        eapply hb_vis'; eauto.
      - rewrite find_index_spec; exists w.
        exploit nth_error_rev; eauto; clarify.
        unfold is_mod_op; split; [destruct w; clarify | intros].
        exploit nth_error_rev'; eauto 2; intro Hj.
        destruct (loc_of x') eqn: Hloc; [|clarsimp].
        destruct (indep_dec _ l (Ptr (b, o))); [clarsimp|].
        specialize (Hi222 _ _ _ Hj Hloc n); destruct Hi222; clarify; omega.
      - destruct w; clarify.
      - rewrite nth_error_app in *; destruct (lt_dec i (length m1)).
        + rewrite <- iapp_app; eapply hb_hbe_trans; [eapply Hbefore; eauto 2|].
          * destruct w; clarify.
            unfold mods; rewrite inth_nth_error; do 3 eexists; eauto; clarify.
          * assert (iapp ops (icons (Read t (b, o) v) m2) =
              iapp (ops ++ [Read t (b, o) v]) m2) as Heq
              by (rewrite <- iapp_app; auto); rewrite Heq.
            eapply seq_hbe; try (repeat rewrite app_length; simpl; omega).
            rewrite Forall_app; eauto.
        + rewrite <- iapp_app; assert (iapp ops (icons (Read t (b, o) v) m2) =
            iapp (ops ++ [Read t (b, o) v]) m2) as Heq
            by (rewrite <- iapp_app; auto); rewrite Heq.
          exploit nth_error_lt; eauto; intro.
          eapply seq_hb; try (repeat rewrite app_length; simpl; omega).
          rewrite Forall_app; eauto.
      - auto.
      - eapply con_steps_steps, con_steps_trans; eauto.
        generalize (con_steps_trans IHops1 H); autorewrite with list; auto. }
    exploit sees_con_step; eauto; intros [s' ?]; exists s'; split.
    - eapply con_steps_trans; eauto.
      generalize (con_state_steps Hcon0 H); unfold con_state; clarify.
      apply (con_steps_trans H); econstructor; eauto.
    - etransitivity; eauto; eapply con_read_ext; eauto.
    - eapply read_init_app; rewrite <- app_assoc; eauto.
    - eapply block_model.consistent_app; rewrite <- app_assoc; eauto.
  Qed.

  Corollary seq_con_step' : forall b m1 s1 t ops m2 s1'
    (Ht : Forall (fun c => thread_of c = t) ops)
    (Hstep1 : con_steps start_state m1 s1)
    (Hstep : con_steps s1 (drop_b_reads b ops) s1')
    (Hbefore : forall i o, mods m1 i (b, o) ->
       happens_before (iapp m1 (iapp ops m2)) i (length m1))
    (Hseq : seq_con (filter (b_not_read b) (lower m1) ++
       proj_block (lower ops) b))
    (Hread_init : read_init (filter (b_not_read b) (lower m1) ++
       proj_block (lower ops) b)),
    exists s2', con_steps s1 ops s2' /\ ext s1' s2'.
  Proof. intros; eapply seq_con_step; eauto; reflexivity. Qed.

  Lemma con_steps_step : forall s op s' (Hsteps : con_steps s [op] s'),
    exists s1 s2, con_steps s [] s1 /\
      match op with
      | Fence t => wbuf s1 t = [] /\ s2 = s1
      | _ => exists n, least_index s1 n /\ con_step n s1 op s2
      end /\ con_steps s2 [] s'.
  Proof.
    intros.
    remember [op] as ops; generalize dependent op.
    induction Hsteps; clarify.
    - do 3 eexists; [|split]; eauto.
      destruct op; clarify; eauto.
    - specialize (IHHsteps _ eq_refl); destruct IHHsteps as [s1 [s2 ?]];
        exists s1, s2; clarify; eauto.
    - eexists; eauto.
  Qed.

  (* Is this a reasonable redefinition of consistent? *)
  Definition consistent' m := forall (ops : list _) (Hpre : iprefix ops m),
    exists s, con_steps start_state ops s.

  Lemma lower_flatten : forall ops w p
    (Hfind : find_index (is_mod_op p) (rev ops) = Some w),
    last_mod_op (lower ops) (Ptr p)
      (length (lower (firstn (length ops - w - 1) ops))).
  Proof.
    intros.
    rewrite find_index_spec in Hfind; clarify.
    exploit nth_error_rev'; eauto; intro Hnth.
    exploit nth_error_split'; eauto; intros [ops1 [ops2 Hlen]]; clarify.
    assert (exists a, to_seq x = [a]) as [a Ha].
    { destruct x; clarify; eauto. }
    econstructor.
    - rewrite <- Hlen1, inth_nth_error, firstn_app, firstn_length, minus_diag;
        simpl.
      rewrite app_nil_r, lower_app, lower_cons.
      setoid_rewrite Ha; simpl; apply nth_error_split.
    - unfold is_mod_op in *; destruct x; clarify.
    - destruct x; clarify.
    - intros.
      rewrite inth_nth_error in *; exploit nth_lower_split; eauto;
        intros (l1 & b & l2 & i & Heq & Hi & ?); clarify.
      rewrite Heq, rev_app_distr in Hfind22; clarify.
      rewrite <- app_assoc in Hfind22; specialize (Hfind22 (length (rev l2)) b).
      clarify; rewrite nth_error_split in Hfind22.
      destruct (lt_dec (length (rev l2)) w); clarify.
      + unfold is_mod_op in Hfind22; destruct b; clarify;
          try (rewrite nth_error_single in *); try (rewrite nth_error_nil in *);
          clarify.
      + rewrite Heq, firstn_app.
        rewrite rev_length in *.
        rewrite firstn_length'; [|rewrite app_length; simpl; omega].
        rewrite lower_app, app_length.
        destruct i; [omega|].
        destruct b; clarify; rewrite nth_error_nil in *; clarify.
  Qed.

  Corollary lower_flatten_op : forall ops w p a
    (Hfind : find (is_mod_op p) (rev ops) = Some w)
    (Ha : nth_error (to_seq w) 0 = Some a),
    last_op (lower ops) (Ptr p) a.
  Proof.
    intros.
    rewrite find_find_index in Hfind; clarify.
    exploit lower_flatten; eauto; intro Hlast.
    inversion Hlast; eexists; split; eauto.
    rewrite <- (firstn_skipn (length ops - x - 1) ops) at 1.
    rewrite lower_app, inth_nth_error, nth_error_app, lt_dec_eq, minus_diag.
    exploit nth_error_rev'; eauto; intro.
    erewrite skipn_n; eauto; clarify.
    destruct w; clarify.
  Qed.

  Lemma private_seq : forall ops t (Ht : Forall (fun c => thread_of c = t) ops)
    (Hlen : length ops > 0) (m1 : list _) m2 b
    (Hbefore : forall i o, mods m1 i (b, o) ->
       happens_before (iapp m1 (iapp ops m2)) i (length m1))
    (Huniform : forall i o v, reads ops i (b, o) v ->
       exists j, j < length m1 + i /\ writes (m1 ++ ops) j (b, o) v /\
       forall k v', k < length m1 + i -> writes (m1 ++ ops) k (b, o) v' ->
       hbe (iapp m1 (iapp ops m2)) k j)
    (Hafter : forall i o, mods m2 i (b, o) ->
       happens_before (iapp m1 (iapp ops m2))
         (length m1 + length ops - 1) (i + length m1 + length ops))
    (Hread_init : read_init (filter (b_not_read b) (lower m1) ++
       proj_block (lower ops) b))
    (Hwrite_alloc : write_alloc (lower (m1 ++ ops))),
    consistent' (iapp m1 (iapp ops m2)) <->
    consistent' (iapp m1 (iapp (drop_b_reads b ops) m2)) /\
      seq_con (filter (b_not_read b) (lower m1) ++ proj_block (lower ops) b).
  Proof.
    intros.
    split; intro Hcon; clarify.
    - unfold consistent' in *; split.
      + intros; exploit add_b_prefix; eauto; intros [ops' Hpre']; clarify.
        specialize (Hcon _ Hpre'2); destruct Hcon as (s & Hsteps).
        unfold drop_b_reads_at.
        rewrite <- (firstn_skipn (length m1) ops') in Hsteps;
          exploit con_steps_app_inv; eauto; intros [s1 [Hs1 Hs]].
        rewrite <- (firstn_skipn (length ops) (skipn (length m1) ops')) in Hs;
          exploit con_steps_app_inv; eauto; intros [s2 [Hs2 Hs']].
        generalize (con_step_drop b Hs2 (ext_refl _)); intros [s2' [Hs2' Hext]].
        generalize (con_state_steps con_start Hs1); intro Hcon1.
        generalize (con_state_steps Hcon1 Hs2); intro Hcon2.
        generalize (con_state_steps Hcon1 Hs2'); intro Hcon2'.
        generalize (ext_sim' Hcon2 Hs' Hext Hcon2'); intros [s' [? Hext']].
        exists s'; eapply con_steps_trans; eauto.
        eapply con_steps_trans; eauto.
      + setoid_rewrite consistent_split_reads; auto.
        split.
        * specialize (Hcon (m1 ++ ops)); use Hcon; clarify.
          generalize (con_state_steps con_start Hcon); intro Hseq.
          exploit con_steps_steps; eauto; intro.
          exploit step_ops; eauto; intros [n [Hleast Heq]].
          unfold con_state in Hseq; clarify.
          generalize (least_unique Hseq1 Hleast); clarify.
          generalize (read_init_future _ n Hseq21); intro.
          generalize (consistent_filter _ Hseq222); intro Hseq'; clarsimp.
          generalize (consistent_proj _ b Hseq'); intro Hseq''.
          use Hseq''. use Hseq''.
          rewrite proj_filter_comm, lower_app, proj_block_app,
            filter_app in Hseq''.
          rewrite filter_app; unfold proj_block at 1 in Hseq'';
            rewrite filter_filter in *; erewrite filter_ext; eauto.
          rewrite Forall_forall; unfold andb; clarify.
          { rewrite <- Heq, write_alloc_filter; auto. }
          { apply read_init_none. }
          { rewrite to_ilist_app; apply prefix_mono, iapp_prefix. }
        * intros.
          rewrite nth_error_app in *.
          destruct (lt_dec r (length (filter (b_not_read b) (lower m1)))).
          { exploit nth_error_in; eauto; intro Hin.
            rewrite filter_In in Hin; clarify. }
          assert (beq (fst p) b = true).
          { exploit nth_error_in; eauto.
            setoid_rewrite filter_In; clarify. }
          unfold proj_block in H; exploit nth_filter_split; eauto;
            intros (ops1 & ops2 & Hops); clarify.
          generalize (nth_error_split ops1 ops2 (MRead p v)); rewrite <- Hops1;
            intro Hnth.
          exploit nth_lower_split; eauto;
            intros (l1 & b0 & l2 & i & ? & Hi & ?); clarify.
          destruct b0; clarify; try (rewrite nth_error_single in *);
            try (rewrite nth_error_nil in *); clarify.
          rewrite lower_app in Hops1; clarify.
          rewrite plus_0_r in *; exploit app_eq_inv; eauto; clarify.
          specialize (Hcon (m1 ++ l1 ++ [Read t0 p v])); use Hcon.
          destruct Hcon as [s Hsteps];
            generalize (con_state_steps con_start Hsteps); intro Hcon.
          rewrite app_assoc in Hsteps; exploit con_steps_app_inv; eauto;
            intros [s' [Hs' ?]].
          exploit con_steps_step; eauto; intros (s1 & s2 & Hs1 & Hread & ?);
            clarify.
          assert (sees_op s1 t0 p (MWrite p v)) as Hsees.
          { unfold sees_op, con_do_read in *.
            destruct (find (buf_match p) (make_buf s1 t0)) eqn: Hfind;
              [destruct b1|]; clarify.
            rewrite find_spec in Hfind; unfold buf_match in *; clarify.
            destruct (eq_dec p0 p); clarify. }
          destruct p as (?, o); unfold beq in *; clarify.
          assert (thread_of (Read t0 (b, o) v) = t0) as Ht0 by auto;
            rewrite <- Ht0 in Hsees.
          exploit hb_last; try (apply Hsees).
          { instantiate (1 := (m1 ++ l1)); intros.
            unfold mods in *; clarify.
            rewrite inth_nth_error in *; exploit nth_error_lt; eauto; intro.
            rewrite nth_error_app in *; destruct (lt_dec i (length m1)).
            { exploit Hbefore; eauto.
              { rewrite inth_nth_error; eauto. }
              intro; rewrite <- iapp_app in *.
              eapply hb_hbe_trans; eauto.
              rewrite (iapp_app l1); eapply seq_hbe; eauto;
                repeat rewrite app_length; simpl; omega. }
            { rewrite <- iapp_app; rewrite (iapp_app l1).
              eapply seq_hb; eauto; repeat rewrite app_length in *; simpl; 
                omega. } }
          { auto. }
          { apply con_steps_steps; auto.
            generalize (con_steps_trans Hs' Hs1); rewrite app_nil_r; auto. }
          intros [i [w Hw]]; clarify.
          assert (find (is_mod_op (b, o)) (rev (m1 ++ l1)) = Some w).
          { rewrite find_find_index; do 2 eexists; eauto.
            rewrite find_index_spec in Hw1; clarify.
            exploit nth_error_rev; eauto.
            assert (length (m1 ++ l1) - (length (m1 ++ l1) - i - 1) - 1 = i)
              as Heq; [|rewrite Heq; auto].
            { generalize (nth_error_lt _ _ Hw11); rewrite rev_length; intro Hlt.
              clear - Hlt; repeat rewrite minus_distr; omega. } }
          exploit lower_flatten_op; eauto.
          rewrite firstn_app, firstn_length', Hops21; [|omega].
          repeat rewrite lower_app.
          rewrite proj_block_app, firstn_app, firstn_length, minus_diag;
            simpl; rewrite app_nil_r.
          intro Hlast; rewrite last_op_proj, proj_block_app in Hlast.
          rewrite <- last_op_filter, filter_app in Hlast.
          rewrite <- last_op_filter, filter_app.
          unfold proj_block at 1 in Hlast; rewrite filter_filter in *;
            erewrite filter_ext; clarify; eauto 2.
          { rewrite Forall_forall; unfold b_not_read, andb; clarify. }
          { rewrite to_ilist_app; apply prefix_mono.
            rewrite <- iapp_app, to_ilist_app; apply prefix_mono.
            repeat constructor. }
        * generalize (write_alloc_proj _ Hwrite_alloc b);
            rewrite lower_app, proj_block_app; intro Hwrite'.
          generalize (write_alloc_filter' _ _ Hwrite').
          unfold proj_block at 1; rewrite filter_filter; erewrite filter_ext;
            eauto.
          { rewrite Forall_forall; unfold andb; clarify. }
    - intros m Hpre.
      exploit (drop_b_prefix b); eauto; intro Hpre'.
      specialize (Hcon1 _ Hpre'); destruct Hcon1 as [s Hs].
      unfold drop_b_reads_at in Hs; exploit con_steps_app_inv; eauto;
        intros [s' Hs']; clarify.
      generalize (iprefix_app_inv _ _ Hpre); intros [? | Hpre2]; clarify.
      { exploit to_ilist_inj; eauto; clarify.
        rewrite firstn_comm, firstn_length, skipn_all in Hs; clarsimp.
        eexists; eauto.
        { apply Min.le_min_r. } }
      exploit to_ilist_app_inv; eauto; intros [m' ?]; clarify.
      exploit con_steps_app_inv; eauto; intros [s'' Hs'']; clarsimp.
      rewrite skipn_length' in *; clarsimp.
      assert (exists k, firstn (length ops) m' = firstn k ops) as [k Hk].
      { generalize (iprefix_app_inv _ _ Hpre22); intros [? | ?]; clarify.
        + exploit to_ilist_inj; eauto; clarify.
          rewrite firstn_firstn; eauto.
        + exploit to_ilist_app_inv; eauto; clarsimp.
          exists (length ops); rewrite firstn_length; auto. }
      exploit seq_con_step'; try (apply Hs''1); eauto.
      { rewrite Hk in *; rewrite <- (firstn_skipn k), Forall_app in Ht; clarify;
          eauto. }
      { intros; rewrite Hk.
        instantiate (1 := iapp (skipn k ops) m2).
        rewrite (iapp_app _ _ m2), firstn_skipn; eapply Hbefore; eauto. }
      { rewrite Hk in *; rewrite <- (firstn_skipn k ops), lower_app,
          proj_block_app, app_assoc in Hcon2.
        eapply block_model.consistent_app; eauto. }
      { rewrite Hk in *; rewrite <- (firstn_skipn k ops), lower_app,
          proj_block_app, app_assoc in Hread_init.
        eapply read_init_app; eauto. }
      intros [s2 [Hs2 Hext]].
      generalize (con_state_steps con_start Hs'1); intro Hcon'.
      generalize (con_state_steps Hcon' Hs''1); intro Hcon''.
      generalize (con_state_steps Hcon' Hs2); intro Hcons2.
      generalize (ext_sim' Hcon'' Hs''2 Hext Hcons2); intros [s2' [? Hext']].
      exists s2'; eapply con_steps_trans; eauto.
      rewrite <- (firstn_skipn (length ops) m'); eapply con_steps_trans;
        eauto.
  Qed.

  Lemma drop_b_reads_spec : forall b ops, lower (drop_b_reads b ops) =
    filter (fun op => not_read op || negb (beq (block_of op) b)) (lower ops).
  Proof.
    induction ops; clarify.
    destruct a; try (rewrite lower_cons); clarsimp.
    destruct p as (b', ?); simpl; destruct (beq b' b);
      [|rewrite lower_cons]; unfold beq, negb; clarsimp.
  Qed.

  Definition is_fence c := match c with Fence _ => true | _ => false end.

  Definition sorted_bufs s := forall t, Sorted gt (wbuf s t).

  Lemma sorted_start : sorted_bufs start_state.
  Proof. intro; clarify. Qed.

  Lemma sorted_step : forall s (Hsorted : sorted_bufs s) ops s'
    (Hsteps : step_star s ops s'), sorted_bufs s'.
  Proof.
    intros; induction Hsteps; auto; apply IHHsteps; clear IHHsteps.
    - exploit step_cases; eauto; intros [[t [p ?]] | ?]; clarify.
      + unfold do_read in *; clarify.
        destruct (find (buf_match p) (make_buf m t)); [destruct b|]; clarify.
      + unfold sorted_bufs; clarify; unfold fun_upd in *; clarify.
        constructor; auto.
        generalize (wf m (thread_of c)); intro.
        clear Hsteps; destruct (wbuf m (thread_of c)); clarify.
        inversion H; constructor; clarify.
    - unfold sorted_bufs, release_op, fun_upd in *; clarify.
      specialize (Hsorted t); rewrite Hbuf in Hsorted.
      exploit Sorted_app; eauto; clarify.
  Qed.

  Definition unique_bufs s := forall t i n t' i'
    (Hn : nth_error (wbuf s t) i = Some n)
    (Hn' : nth_error (wbuf s t') i' = Some n), t' = t /\ i' = i.

  Lemma unique_start : unique_bufs start_state.
  Proof. intro; clarsimp. Qed.

  Lemma unique_step : forall s (Hunique : unique_bufs s) ops s'
    (Hsteps : step_star s ops s'), unique_bufs s'.
  Proof.
    intros; induction Hsteps; auto; apply IHHsteps; clear IHHsteps.
    - exploit step_cases; eauto; intros [[t [p ?]] | ?]; clarify.
      + unfold do_read in *; clarify.
        destruct (find (buf_match p) (make_buf m t)); [destruct b|]; clarify.
      + unfold unique_bufs in *; clarify.
        destruct (eq_dec n (length (word m))).
        * generalize (wf m t), (wf m t'); repeat rewrite Forall_forall;
            intros Hlt Hlt'.
          generalize (nth_error_in _ _ Hn), (nth_error_in _ _ Hn');
            intros Hin Hin'.
          unfold fun_upd in *; destruct (eq_dec t (thread_of c)); clarify;
            [|specialize (Hlt _ Hin); omega].
          destruct (eq_dec t' (thread_of c)); clarify;
            [|specialize (Hlt' _ Hin'); omega].
          destruct i; clarify; [|generalize (nth_error_in _ _ Hn); intro Hi;
                                 specialize (Hlt _ Hi); omega].
          destruct i'; clarify; generalize (nth_error_in _ _ Hn'); intro Hi';
            specialize (Hlt _ Hi'); omega.
        * specialize (Hunique t (if eq_dec t (thread_of c) then i - 1 else i) n 
            t' (if eq_dec t' (thread_of c) then i' - 1 else i'));
            unfold fun_upd in *; destruct (eq_dec t (thread_of c)),
            (eq_dec t' (thread_of c)), i, i'; clarsimp.
    - unfold unique_bufs in *; clarify.
      generalize (nth_error_lt _ _ Hn), (nth_error_lt _ _ Hn'); intros.
      specialize (Hunique t0 i n0 t' i'); unfold fun_upd in *;
        destruct (eq_dec t0 t), (eq_dec t' t); clarify;
        repeat rewrite Hbuf in *; repeat rewrite nth_error_app in *; clarify.
  Qed.

  Lemma empty_bufs : forall s n (Hleast : least_index s n)
    (Hsorted : sorted_bufs s) (Hunique : unique_bufs s),
    exists s', con_steps s [] s' /\ forall t, wbuf s' t = [].
  Proof.
    intros.
    remember (length (word s) - n) as num; generalize dependent n;
      generalize dependent s; induction num; clarify.
    - destruct Hleast; clarify; eauto.
      generalize (wf s x); rewrite Forall_forall; intro Hlt.
      specialize (Hlt n); clarify; omega.
    - destruct Hleast; clarify; [|omega].
      generalize (wf s x); rewrite Forall_forall; intro Hlt.
      generalize (Hlt n); clarify.
      exploit nth_error_succeeds; eauto; intros [e He].
      assert (exists b, wbuf s x = b ++ [n]) as [b Hbuf].
      { specialize (Hsorted x).
        exploit in_split; eauto; intros [l1 [l2 ?]]; clarsimp.
        exploit Sorted_app; eauto; clarify.
        exploit Sorted_extends; eauto.
        { unfold Relations_1.Transitive; apply gt_trans. }
        destruct l2; intro Hgt; clarify; eauto.
        inversion Hgt; clarify.
        specialize (H2 n0); destruct H2 as [Hrange _]; use Hrange; [omega|].
        exists x; clarsimp; rewrite in_app; clarify. }
      assert (forall t', Forall (fun i : nat => n < i)
        (fun_upd (wbuf s) x b t')) as Hnext.
      { intro; rewrite Forall_forall; intros n' ?.
        specialize (H2 n'); destruct H2 as [Hrange _]; use Hrange.
        destruct (eq_dec n' n); clarify; [|omega].
        exploit in_nth_error; eauto; intros (i & ? & Hnth).
        specialize (Hunique x (length b) n t' i).
        rewrite Hbuf, nth_error_split in Hunique; clarify.
        unfold fun_upd in *; destruct (eq_dec t' x); clarify.
        rewrite Hbuf, nth_error_app in Hunique; clarify; omega.
        { exists t'; unfold fun_upd in *; clarify.
          rewrite Hbuf, in_app; auto. } }
      exploit (cstep_write_buf(Hbuf := Hbuf) Hnext); eauto; intro Hstep.
      exploit con_steps_steps; eauto; intro.
      specialize (IHnum (release_op _ _ _ _ e Hbuf)); use IHnum.
      use IHnum.
      exploit (release_least(s := s)); [unfold least_index| |]; eauto; clarify.
      specialize (IHnum (S n)); clarify.
      use IHnum; [|omega].
      destruct IHnum as [s' [Hsteps ?]]; exists s'; clarify.
      apply (con_steps_trans Hstep Hsteps).
      { eapply unique_step; eauto. }
      { eapply sorted_step; eauto. }
  Qed.        

  Lemma to_seq_single : forall c (Hc : is_fence c = false),
    exists a, to_seq c = [a].  
  Proof.
    destruct c; clarify; eauto.
  Qed.  

  Lemma con_steps_no_reads : forall ops
    (Hno_reads : Forall (fun x => not_read x = true) (lower ops))
    (Hwrite : write_alloc (lower ops)) (Hseq : seq_con (lower ops)),
    exists s, con_steps start_state ops s.
  Proof.
    induction ops using rev_ind; clarify; eauto.
    rewrite lower_app, lower_single in Hno_reads, Hwrite, Hseq.
    rewrite Forall_app in *; clarify.
    generalize (write_alloc_app _ _ Hwrite); intro Hwrite'.
    generalize (consistent_app _ _ Hseq); intro Hseq'.
    specialize (IHops Hwrite' Hseq'); destruct IHops as [s ?].
    assert (exists s', con_steps s [x] s') as [? ?];
      [|eexists; eapply con_steps_trans; eauto].
    exploit (con_state_steps con_start); eauto; intros [n Hcon]; clarify.
    exploit con_steps_steps; eauto; intro.
    destruct (is_fence x) eqn: Hfence.
    - destruct x; clarify.
      exploit empty_bufs; eauto.
      { eapply (sorted_step sorted_start); eauto. }
      { eapply (unique_step unique_start); eauto. }
      intros [? [Hs' ?]].
      eexists; eapply (con_steps_trans Hs'); constructor; auto.
    - assert (exists s', con_step n s x s') as [? ?].
      { exploit step_ops; eauto; intros [? [Hleast Heq]].
        generalize (least_unique Hleast Hcon1); clarify.
        exploit to_seq_single; eauto; intros [a Ha].
        rewrite Ha in Hno_reads2, Hwrite, Hseq.
        generalize (simple_op _ Hseq' a).
        rewrite read_init_snoc; [intro Hsm|].
        destruct x; clarify.
        + inversion Hno_reads2; clarify.
        + do 2 eexists; eauto.
          specialize (Hwrite (length (lower ops))).
          rewrite inth_nth_error in Hwrite;
            specialize (Hwrite _ _ (nth_error_split _ _ _)); clarify.
          setoid_rewrite <- last_op_filter; setoid_rewrite Heq;
            setoid_rewrite last_op_filter.
          rewrite itake_firstn, firstn_app, firstn_length, minus_diag in *;
            clarify; rewrite app_nil_r in *.
          generalize (last_mod_lt _ Hwrite1); intro.
          destruct Hwrite2; [left | right]; clarify;
            rewrite inth_nth_error, nth_error_app in *; clarify;
            unfold last_op; setoid_rewrite inth_nth_error; eauto.
        + do 2 eexists; eauto.
          rewrite Hsm2 in Hseq; clarify.
          setoid_rewrite <- last_op_filter; setoid_rewrite Heq;
            setoid_rewrite last_op_filter.
          split; repeat intro; exploit (simple_last_block_op _ Hsm1); eauto;
            clarify.
          destruct p; clarify.
        + do 2 eexists; eauto.
          rewrite Hsm2 in Hseq; clarify.
          setoid_rewrite <- last_op_filter; setoid_rewrite Heq;
            setoid_rewrite last_op_filter.
          destruct (last_op_dec (lower ops) (Block b) Hseq')
            as [[op Hlast] | Hlast].
          * clarify; exploit (simple_last_block_op _ Hsm1); eauto.
            destruct op; clarify; eauto.
            destruct (eq_dec b0 b); clarify; eauto.
            destruct Hlast as [? [Hlast ?]]; inversion Hlast; clarsimp.
          * exploit (simple_no_last_op _ Hsm1); eauto; clarify.
        + generalize (read_init_none (lower ops)); rewrite filter_all; auto. }
      eexists; eapply cstep_op; eauto.
  Qed.

  Opaque minus.

  Lemma hb_drop : forall m1 t p v m2 i j
    (Hhb : happens_before (iapp m1 (icons (Read t p v) m2))
             (add_index i (length m1)) (add_index j (length m1))),
    happens_before (iapp m1 m2) i j.
  Proof.
    intros; remember (add_index i (length m1)) as i';
      remember (add_index j (length m1)) as j'.
    generalize dependent j; generalize dependent i; induction Hhb; clarify;
      try rewrite add_nth in *.
    - eapply hb_prog; eauto.
      eapply add_index_lt'; eauto.
    - eapply hb_sync; eauto.
      eapply add_index_lt'; eauto.
    - destruct (eq_dec k (length m1)).
      { subst.
        generalize (hb_lt Hhb1), (hb_lt Hhb2); intros.
        generalize (hb_boundary _ _ Hhb1); unfold add_index in *;
          destruct (lt_dec i0 (length m1)); [intro Hinv1; clarify | omega].
        exploit hbe_le; eauto; intro; assert (x0 = length m1) by omega; clarify.
        rewrite minus_diag in *; clarify.
        assert (iapp m1 (icons (Read t p v) m2) = iapp (m1 ++ [Read t p v]) m2)
          as Heq by (rewrite <- iapp_app; auto); rewrite Heq in Hhb2.
        generalize (hb_boundary _ _ Hhb2); rewrite app_length;
          destruct (lt_dec j0 (length m1)); [omega | intro Hinv2; clarify].
        do 2 (use Hinv2; [|omega]); clarify.
        generalize (hbe_le Hinv2221); intro; assert (x0 = length m1) by omega;
          subst; rewrite nth_error_split in *; clarify.
        unfold synchronizes_with in *; destruct Hinv2222222; clarify.
        eapply hbe_hb_trans; [eapply hbe_app; eauto|].
        generalize (hbe_app' _ _ m1 Hinv22221); rewrite app_length; intro Hhb'.
        do 2 (use Hhb'; [|omega]).
        do 2 (rewrite <- plus_minus_comm in Hhb'; [|simpl; omega]).
        rewrite plus_comm, (plus_comm (S j0)) in Hhb'.
        repeat rewrite <- minus_plus_simpl_l_reverse in Hhb'; simpl in Hhb'.
        rewrite (NPeano.Nat.sub_1_r (S j0)) in Hhb'; simpl in Hhb'.
        eapply hb_hbe_trans; [|eauto].
        destruct Hinv1222222; clarify.
        + eapply hb_prog; eauto.
          * omega.
          * rewrite iapp_nth; clarify.
          * rewrite iapp_nth; destruct (lt_dec (x2 - 1) (length m1)); [omega|].
            rewrite NPeano.Nat.sub_add_distr, minus_comm  in Hinv2222221; auto.
        + eapply hb_sync; eauto.
          * omega.
          * rewrite iapp_nth; clarify; eauto.
          * rewrite iapp_nth; destruct (lt_dec (x2 - 1) (length m1)); [omega|].
            rewrite NPeano.Nat.sub_add_distr, minus_comm in Hinv2222221; eauto.
          * simpl; unfold synchronizes_with; eauto. }
      assert (k = add_index (drop_index k (length m1)) (length m1)).
      { unfold add_index, drop_index; destruct (lt_dec k (length m1)); clarify;
          try omega.
        destruct (lt_dec (k - 1) (length m1)); omega. }
      eapply hb_trans; [apply IHHhb1 | apply IHHhb2]; eauto.
  Qed.

  Lemma writes_writesp : forall m w p v, writes m w p v <->
    match inth m w with Some c => writesp c p /\ write_val c = Some v
    | None => False end.
  Proof.
    unfold writes; intros; split; intro Hw; clarify.
    - destruct x; clarify.
      inversion H; clarify.
    - destruct (inth m w) eqn: Hnth; clarify.
      do 2 eexists; eauto.
      destruct b; clarify.
  Qed.

  Lemma step_star_fence_inv : forall s t ops s'
    (Hsteps : step_star s (Fence t :: ops) s'),
    exists s1, step_star s [] s1 /\ wbuf s1 t = [] /\ step_star s1 ops s'.
  Proof.
    intros; remember (Fence t :: ops) as ops'; induction Hsteps; clarify; eauto.
  Qed.

  Lemma step_star_step_inv : forall s c ops s'
    (Hsteps : step_star s (c :: ops) s') (Hnot_fence : is_fence c = false),
    exists s1 s2, step_star s [] s1 /\ step s1 c s2 /\ step_star s2 ops s'.
  Proof.
    intros; remember (c :: ops) as ops'; induction Hsteps; clarify; eexists;
      eauto.
  Qed.

  Lemma buf_in : forall s ops s' (Hsteps : con_steps s ops s')
    t p v (Hfind : find (buf_match p) (make_buf s' t) = Some (BWrite p v))
    (Hout : ~In (Write t p v) ops), In (BWrite p v) (make_buf s t).
  Proof.
    intros; induction Hsteps; clarify.
    - eapply find_success; eauto.
    - destruct c; clarify.
      + unfold con_do_read in *; destruct (find (buf_match p0) (make_buf s t0));
          [destruct b|]; clarify.
      + unfold make_buf in IHHsteps; simpl in IHHsteps.
        unfold fun_upd in *; destruct (eq_dec t t0); clarify.
        * rewrite nth_error_split in IHHsteps; clarify.
          destruct IHHsteps as [H | H]; clarify.
          { inversion H; contradiction Hout; clarify. }
          rewrite make_buf_mono in H; auto.
        * rewrite make_buf_mono in IHHsteps; auto.
      + unfold make_buf in IHHsteps; simpl in IHHsteps.
        unfold fun_upd in *; destruct (eq_dec t t0); clarify.
        * rewrite nth_error_split in IHHsteps; clarify.
          rewrite make_buf_mono in IHHsteps; auto.
        * rewrite make_buf_mono in IHHsteps; auto.
      + unfold make_buf in IHHsteps; simpl in IHHsteps.
        unfold fun_upd in *; destruct (eq_dec t t0); clarify.
        * rewrite nth_error_split in IHHsteps; clarify.
          rewrite make_buf_mono in IHHsteps; auto.
        * rewrite make_buf_mono in IHHsteps; auto.
    - unfold make_buf in IHHsteps; simpl in IHHsteps.
      unfold fun_upd in IHHsteps; clarify.
      unfold make_buf; rewrite Hbuf, make_buf_app, in_app; clarify.
      generalize (wf (release_op _ _ _ _ e Hbuf) t0); simpl;
        rewrite fun_upd_new; auto.
  Qed.

  Lemma wbuf_find : forall s ops s' (Hsteps : step_star s ops s')
    t p i (Hbuf : find_index (buf_match p) (make_buf s' t) = Some i)
    n (Hwbuf : nth_error (wbuf s' t) i = Some n)
    e (He : nth_error (word s') n = Some e),
    (exists ops1 c ops2 s1 s2, ops = ops1 ++ c :: ops2 /\ step_star s ops1 s1 /\
      n = length (word s1) /\ step s1 c s2 /\ step_star s2 ops2 s' /\
      to_seq c = [buf_to_op e] /\
      Forall (fun c => thread_of c <> t \/ is_mod_op p c = false) ops2) \/
    (exists i', find_index (buf_match p) (make_buf s t) = Some i' /\
      nth_error (wbuf s t) i' = Some n) /\
    Forall (fun c => thread_of c <> t \/ is_mod_op p c = false) ops.
  Proof.
    intros; induction Hsteps; clarify; eauto.
    - destruct IHHsteps as [? | IH]; clarify.
      { left; repeat eexists; eauto; clarify. }
      exploit step_cases'; eauto; intros [(t' & p' & ?) | ?]; clarify.
      + right; clarify.
        unfold do_read in *; destruct (find (buf_match p') (make_buf m t'));
          [destruct b|]; clarify; eauto.
      + unfold make_buf in IH11; simpl in IH11.
        unfold fun_upd in *; destruct (eq_dec t (thread_of c)); clarify;
          [|rewrite make_buf_mono in IH11; right; clarify; eauto].
        rewrite nth_error_split in IH11; clarify.
        destruct (buf_match p x0) eqn: Hp; clarify.
        * exploit word_mono; eauto; clarsimp.
          rewrite nth_error_split in He; clarify.
          left; repeat eexists; eauto; clarify.
        * right; rewrite make_buf_mono in *; split; eauto.
          constructor; unfold is_mod_op, buf_match in *; clarsimp.
    - destruct IHHsteps as [? | IH]; clarify; [left | right]; repeat eexists;
        eauto.
      + unfold make_buf in IH11; simpl in IH11.
        unfold fun_upd in IH11; destruct (eq_dec t t0); clarify; eauto.
        unfold make_buf; rewrite Hbuf0, make_buf_app, find_index_app; clarify.
        { generalize (wf (release_op _ _ _ _ e Hbuf0) t0); simpl;
            rewrite fun_upd_new; auto. }
      + unfold fun_upd in *; clarify.
        generalize (nth_error_lt _ _ IH12); rewrite Hbuf0, nth_error_app;
          clarify.
    - destruct IHHsteps as [? | ?]; [left | right]; clarify; eauto.
      exists (Fence t0 :: x); repeat eexists; eauto.
  Qed.

  Lemma word_eq : forall s ops s' (Hsteps : step_star s ops s'),
    map buf_to_op (word s') =
    map buf_to_op (word s) ++ filter not_read (lower ops).
  Proof.
    intros; induction Hsteps; clarsimp.
    rewrite lower_cons; exploit step_cases'; eauto; intros [[t [p ?]] | ?];
      clarify.
    - unfold do_read in *; destruct (find (buf_match p) (make_buf m t));
        [destruct b|]; clarify.
    - rewrite map_app; clarsimp.
  Qed.

  Lemma next_read : forall s p v, next (upd_hist s (hist s ++ [MRead p v])) =
    next s.
  Proof.
    unfold next; clarify.
    rewrite filter_app; clarsimp.
  Qed.

  Lemma next_step : forall s c s' (Hstep : step s c s'), next s' = next s.
  Proof.
    intros; exploit step_cases; eauto; intros [[t [p ?]] | ?]; clarify.
    unfold do_read in *; destruct (find (buf_match p) (make_buf s t));
      [destruct b|]; clarify.
    apply next_read.
  Qed.

  Lemma next_release : forall s t b n e Hbuf, next (release_op s t b n e Hbuf) =
    S (next s).
  Proof.
    unfold next; clarify.
    rewrite filter_app, app_length; clarsimp.
  Qed.

  Lemma hist_length : forall s ops s' (Hsteps : step_star s ops s')
    (Hleast : least_index s (next s)) t n (Hn : In n (wbuf s t))
    (Hmove : ~In n (wbuf s' t)), next s' > n.
  Proof.
    intros ????; induction Hsteps; clarify; eauto.
    - exploit least_hist; try (apply Hleast).
      { eapply step_op; [eauto | apply step_refl]. }
      intro; exploit step_cases; eauto; intros [[t' [p ?]] | ?]; clarify.
      + unfold do_read in *; destruct (find (buf_match p) (make_buf m t'));
          [destruct b|]; clarify; eauto.
      + eapply IHHsteps; eauto.
        unfold fun_upd; clarify.
    - exploit release_least; eauto.
      erewrite <- next_release; intros [? Hleast']; subst;
        specialize (IHHsteps Hleast').
      specialize (IHHsteps t0); unfold fun_upd in *; clarify.
      rewrite Hbuf, in_app in Hn; clarify.
      exploit least_hist; eauto; intro Hleast''.
      unfold next in *; exploit hist_mono; eauto; clarsimp.
      rewrite filter_app, app_length in *; clarsimp.
      rewrite <- plus_Snm_nSm in *; unfold gt.
      eapply lt_le_trans; eauto; apply le_plus_l.
  Qed.

  Instance TSO_model : Memory_Model ML := { consistent := consistent';
    drop_b_reads := drop_b_reads; well_formed := fun _ => True }.
  Proof.
    - repeat intro; inversion Hpre; destruct ops; clarify; eauto.
    - intros; assert (Forall (fun x => not_read x = true) (lower m)) as Hnone.
      { rewrite Forall_forall; intros.
        exploit in_nth_error; eauto; clarify.
        exploit nth_lower_split; eauto; intros (? & ? & ? & ? & ? & ? & ?).
        exploit nth_error_in; eauto; clarify.
        destruct x; clarify.
        exploit Hno_reads; clarify.
        { unfold reads; rewrite inth_nth_error, nth_error_split; eauto. } }
      unfold consistent'; setoid_rewrite iprefix_lists_inv; split; intro Hcon.
      + specialize (Hcon m); use Hcon; [|eexists; apply app_nil_end].
        clarify; exploit con_steps_steps; eauto; clarify.
        exploit step_ops; eauto; intros (? & Hleast & Heq).
        exploit con_state_steps; eauto.
        { apply con_start. }
        unfold con_state; intro Hs; clarify.
        generalize (least_unique Hleast Hs1); clarify.
        generalize (consistent_filter _ Hs222 (read_init_future _ _ Hs21));
          intro Hseq; clarify.
        setoid_rewrite filter_all in Heq at 2; clarsimp.
      + clarify.
        rewrite lower_app in Hwrite, Hcon, Hnone.
        eapply con_steps_no_reads; eauto.
        * rewrite Forall_app in *; clarify.
        * eapply write_alloc_app; eauto.
        * eapply consistent_app; eauto.
    - unfold reads; clarify.
      exploit inth_split; eauto; intros [l1 [l2 ?]]; clarify; clear Hread1.
      unfold consistent' in Hcon; specialize (Hcon (l1 ++ [x])); use Hcon.
      destruct Hcon as [s ?]; exploit con_steps_app_inv; eauto;
        intros [s' [Hl1 Hx]].
      destruct x; clarify.
      inversion H0; clarify.
      exploit con_steps_step; eauto; intros (s1 & s2 & Hs1 & Hs2 & ?); clarify.
      generalize (con_steps_trans Hl1 Hs1); rewrite app_nil_r; intro Hsteps1.
      exploit con_steps_trans.
      { apply Hsteps1. }
      { instantiate (2 := [Read t p v]); econstructor; try (apply cstep_refl);
          eauto. }
      intro Hsteps.
      generalize (con_state_steps con_start Hsteps); intro Hcon.
      unfold con_do_read in *.
      setoid_rewrite writes_writesp.
      destruct (find (buf_match p) (make_buf s1 t)) eqn: Hfind;
        [destruct b|]; clarify.
      + assert (p0 = p); subst.
        { rewrite find_spec in Hfind; clarify.
          unfold buf_match in *; clarify.
          destruct (eq_dec p0 p); clarify. }
        exploit con_steps_steps; eauto; intro.
        rewrite find_find_index in Hfind; destruct Hfind as [i [Hfind ?]].
        exploit make_buf_nth; eauto; intros (? & Hi & ?).
        exploit wbuf_find; eauto;
          intros [(l1' & c & l2' & ? & ? & Heq & ? & ? & ? & Hrest & ? & Hlast)
          | ?]; clarify.
        destruct c; clarify.
        rewrite (split_app _ _ (Write t0 p v)) in Heq.
        assert (exists l2'', l2' = l2'' ++ [Read t p v]) as [l2'' ?]; clarify.
        { destruct (nil_dec l2'); subst;
            [rewrite app_nil_r in *; exploit app_inj_tail; eauto; clarify|].
          rewrite (app_removelast_last (Read t p v) n), app_assoc in Heq.
          exploit app_inj_tail; eauto; intros [? Hllast].
          rewrite (app_removelast_last (Read t p v)); auto.
          rewrite <- Hllast; eauto. }
        rewrite app_assoc in Heq; exploit app_inj_tail; eauto; clarify.
        rewrite <- app_assoc in *; exists (length l1').
        split; [rewrite app_length; simpl; omega|].
        split; [rewrite <- iapp_app; rewrite iapp_nth, lt_dec_eq, minus_diag;
                clarify|].
        split; [|intro Hhb; generalize (hb_lt Hhb); rewrite app_length; omega].
        intros ? ? ? [Hhb1 Hhb2].
        destruct (inth (iapp (l1' ++ [Write t0 p v] ++ l2'')
          (icons (Read t p v) l2)) w2) eqn: Hw2; clarify.
        generalize (hb_lt Hhb1), (hb_lt Hhb2); intros.
        exploit hb_fence; eauto.
        { rewrite iapp_nth, lt_dec_eq, minus_diag; simpl; eauto. }
        intro Hfence.
        rewrite iapp_nth in Hw2; clarify.
        rewrite nth_error_app in Hw2; destruct (lt_dec w2 (length l1'));
          [omega|].
        destruct (w2 - length l1') eqn: Hminus; [omega | clarify].
        exploit nth_error_in; eauto; intro Hin.
        rewrite Forall_app in Hlast; clarify.
        rewrite Forall_forall in Hlast1; specialize (Hlast1 _ Hin).
        unfold is_mod_op in Hlast1; destruct b; clarify.
        rewrite iapp_nth in Hfence22; clarify.
        rewrite nth_error_app in Hfence22; destruct (lt_dec x0 (length l1'));
          [omega|].
        destruct (x0 - length l1') as [|k] eqn: Hx0; clarify.
        exploit nth_error_split'; eauto; intros (l3 & l4 & ?); clarify.
        generalize (step_star_app_inv _ _ Hrest); intros (? & ? & Hread).
        exploit step_star_app_inv; eauto; intros (? & Hwr0 & ?).
        exploit step_star_step_inv; eauto; intro Hwr; clarify.
        rewrite nth_error_app in Hfence22; destruct (lt_dec k (length l3));
          [omega|].
        destruct (k - length l3) eqn: Hk; clarify.
        generalize (nth_error_split' _ _ Hfence22); intros [lf [lf' ?]]; 
          clarify.
        exploit step_star_app_inv; eauto; intros (? & Hlw2 & ?).
        exploit step_star_fence_inv; eauto; intros [sf [Hf0 Hf]].
        generalize (step_star_trans Hlw2 Hf0); intro Hsteps2.
        generalize (buf_gt Hsteps2 t1); simpl; rewrite fun_upd_new; simpl.
        intro Hgt; specialize (Hgt _ (or_introl eq_refl)); clarify.
        generalize (step_star_trans Hf2 Hread); intro.
        exploit buf_later; eauto.
        { generalize (word_mono Hsteps2); intros [? Hword].
          simpl in Hword; rewrite Hword, app_length, app_length; simpl; omega. }
        instantiate (1 := t); intro Hgt1.
        generalize (nth_error_in _ _ Hi); intro Hin1.
        rewrite Forall_forall in Hgt1; specialize (Hgt1 _ Hin1).
        generalize (step_star_trans Hwr0 Hwr1); intro.
        exploit word_mono; eauto; simpl; intros [? Heq].
        rewrite Heq, app_length, app_length in Hgt1; omega.
      + unfold con_state in Hcon; clarify.
        exploit con_steps_steps; eauto; intro.
        exploit least_hist; eauto; rewrite next_read; intro Hleast.
        generalize (least_unique Hcon1 Hleast); clarify.
        unfold future_hist in Hcon222; clarify.
        exploit con_steps_steps; eauto; intro.
        exploit step_ops; eauto; intros [? [Hleast' Heq]].
        generalize (least_unique Hleast' Hleast); clarify.
        generalize (con_steps_trans Hl1 Hs1); intro.
        exploit con_steps_steps; eauto; intro.
        unfold future_hist in Heq; simpl in Heq; erewrite word_eq in Heq; eauto.
        simpl in Heq; repeat rewrite lower_app in Heq.
        setoid_rewrite filter_app in Heq at 3; simpl in Heq;
          repeat rewrite app_nil_r in Heq.
        rewrite filter_app in Heq; setoid_rewrite filter_all in Heq at 2.
        setoid_rewrite <- (firstn_skipn (next s1) (filter not_read (lower l1)))
          in Heq at 2; exploit app_inv_tail; eauto; intro Heq'.
        rewrite filter_app in Heq'; simpl in Heq'; rewrite app_nil_r in Heq'.
        rewrite <- last_op_filter in Hs222.
        setoid_rewrite Heq' in Hs222; destruct Hs222 as [w Hw].
        rewrite inth_nth_error, nth_error_firstn in Hw; clarify.
        exploit nth_filter_split; eauto; intros (m1 & m2 & Hm).
        assert (nth_error (lower l1) (length m1) = Some (MWrite p v))
          by (clarsimp; apply nth_error_split).
        exploit nth_lower_split; eauto; intros (l1' & c & l2' & i & ?); clarify.
        destruct c; clarify; try (rewrite nth_error_single in *);
          try (rewrite nth_error_nil in *); clarify.
        rewrite plus_0_r in *; rewrite lower_app, lower_cons in Hm1.
        exploit app_eq_inv; eauto; clarify.
        exists (length l1'); rewrite app_length; clarify; split; [omega|].
        split; [rewrite <- iapp_app, iapp_nth, lt_dec_eq, minus_diag; clarify|].
        split; [|intro Hhb; generalize (hb_lt Hhb); omega].
        intros ? ? ? [Hhb1 Hhb2].
        generalize (hb_lt Hhb1), (hb_lt Hhb2); intros.
        destruct (inth (iapp (l1' ++ Write t0 p v :: l2')
          (icons (Read t p v) l2)) w2) eqn: Hnth; clarify.
        destruct b; clarify.
        exploit hb_fence; eauto.
        { rewrite iapp_nth, app_length; simpl; rewrite lt_dec_eq, minus_diag;
            simpl; eauto. }
        intro Hcases.
        rewrite iapp_nth, app_length in Hnth; simpl in Hnth; clarify.
        rewrite nth_error_app in Hnth; destruct (lt_dec w2 (length l1'));
          [omega|].
        destruct (w2 - length l1') eqn: Hminus; [omega | clarify].
        exploit nth_error_split'; eauto; intros (l3 & l4 & ?); clarify.
        rewrite app_nil_r in *; exploit step_star_app_inv; eauto; clarify.
        exploit least_hist; try (apply least_start'); eauto; intro Hleast0.
        exploit step_star_step_inv; eauto; intros (? & ? & ? & ? & ?).
        exploit least_hist; try (apply Hleast0); eauto; intro.
        exploit step_least; eauto.
        erewrite <- next_step; eauto; intro.
        exploit step_star_app_inv; eauto; clarify.
        exploit least_hist; eauto; intro Hleast1.
        exploit step_star_step_inv; eauto; intros (sw & ? & ? & ? & ?).
        exploit least_hist; try (apply Hleast1); eauto; intro.
        exploit step_least; eauto.
        erewrite <- next_step; eauto; intro.
        assert (~In (length (word sw)) (wbuf s1 t1)).
        { intro Hin; destruct (eq_dec t1 t); clarify.
          * clear Hcases.
            rewrite find_fail in Hfind.
            generalize (wf s1 t); intro Hlt.
            exploit in_split; eauto; intros (? & ? & Hbuf).
            rewrite Hbuf, Forall_app in Hlt; destruct Hlt as [? Hlt];
              inversion Hlt; clarify.
            unfold make_buf in Hfind; rewrite Hbuf, make_buf_app in Hfind; auto.
            simpl in Hfind; exploit nth_error_succeeds; eauto; intros [e He].
            rewrite He, Forall_app in Hfind; destruct Hfind as [_ Hfind];
              inversion Hfind; clarify.
            exploit word_mono; eauto; intros [? Hword].
            rewrite Hword in He; simpl in He.
            rewrite <- app_assoc in He; simpl in He;
              rewrite nth_error_split in He; unfold buf_match in *; clarify.
          * rewrite iapp_nth, app_length in Hcases22; clarify.
            rewrite nth_error_app in Hcases22;
              destruct (lt_dec x4 (length l1')); [omega|].
            destruct (x4 - length l1') as [|k] eqn: Hk; clarify.
            rewrite nth_error_app in Hcases22; destruct (lt_dec k (length l3));
              [omega|].
            destruct (k - length l3) as [|k'] eqn: Hk'; clarify.
            generalize (nth_error_split' _ _ Hcases22); clarify.
            exploit step_star_app_inv; eauto; intros (? & Hf0 & ?).
            exploit step_star_fence_inv; eauto; intros (? & Hf1 & ? & Hf2).
            generalize (step_star_trans Hf0 Hf1); intro Hf.
            generalize (buf_gt Hf t1 (length (word sw))).
            simpl; rewrite fun_upd_new; simpl; clarify.
            exploit (buf_later Hf2); eauto.
            { exploit word_mono; eauto; intros [? Hword]; rewrite Hword.
              simpl; repeat rewrite app_length; simpl; omega. }
            instantiate (1 := t1); rewrite Forall_forall; intro Hgt.
            specialize (Hgt _ Hin); omega. }
        clear Hcases; clarify; exploit hist_length; eauto.
        { simpl; rewrite fun_upd_new; simpl; auto. }
        intro Hlen.
        assert (step_star start_state (l1' ++ Write t0 p v :: l3 ++
          [Write t1 p v2]) (add_buf sw t1 (BWrite p v2))).
        { eapply step_star_trans; eauto.
          eapply (step_star_trans(ops1 := [])); eauto.
          econstructor; simpl; eauto.
          eapply step_star_trans; eauto.
          eapply (step_star_trans(ops1 := [])); eauto.
          econstructor; simpl; eauto. }
        exploit word_eq; eauto; simpl; intro Heq''.
        assert (next s1 >= length (filter not_read
            (lower (l1' ++ Write t0 p v :: l3 ++ [Write t1 p v2])))).
        { rewrite <- Heq'', map_app, app_length, map_length; simpl; omega. }
        rewrite split_app, (split_app l3), app_assoc, app_assoc in Hw1.
        rewrite lower_app, filter_app, firstn_app in Hw1.
        repeat rewrite <- app_assoc in Hw1; simpl in Hw1;
          rewrite firstn_length' in Hw1; auto.
        inversion Hw1.
        rewrite lower_app, lower_cons, lower_app, lower_single in Hlast.
        do 2 rewrite app_assoc in Hlast; rewrite filter_app in Hlast;
          simpl in Hlast.
        rewrite <- app_assoc in Hlast; specialize (Hlast (length
          (filter not_read ((lower l1' ++ [MWrite p v]) ++ lower l3)))).
        simpl in Hlast; rewrite inth_nth_error, nth_error_split in Hlast.
        specialize (Hlast _ eq_refl); clarify.
        repeat rewrite filter_app, app_length in Hlast; simpl in Hlast.
        rewrite NPeano.Nat.add_1_r in Hlast.
        generalize (le_Sn_n _ (le_trans _ _ _ (le_plus_l _ _) Hlast)); auto.
        { apply Forall_skipn, filter_Forall; auto. }
      + rewrite to_ilist_app; apply prefix_mono; simpl; repeat constructor.
    - destruct c; repeat intro; clarify; try (rewrite nth_error_single in *);
        try (rewrite nth_error_nil in *); clarify.
    - apply drop_b_reads_spec.
    - auto.
    - destruct c; clarify.
      repeat intro.
      specialize (Hrf (add_index i (length m1)) (add_index j (length m1))).
      use Hrf.
      repeat rewrite add_nth in Hrf; specialize (Hrf _ _ Ha Hb).
      clarify; use Hrf; [|do 3 eexists; eauto].
      destruct Hrf; [left | right]; eapply hb_drop; eauto.
      { unfold add_index; intro; destruct (lt_dec i (length m1)); clarify;
          omega. }
    - intros; eapply private_seq; eauto.
  Defined.*)

End TSO_model.