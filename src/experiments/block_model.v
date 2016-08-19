Require Import Coqlib.
Require Import Util.
Require Import Arith.
Require Import Morphisms.
Import ListNotations.
Import Bool.
Import EquivDec.
Import CoqEqDec.

Set Implicit Arguments.

Local Close Scope Z.

Section Model.
  Variables (block val : Type).
  Context (block_eq : EqDec_eq block).
  Definition ptr := (block * nat)%type.

  (* We could also make each operation be on a range of bytes. *)
  (* Is it worth allocating blocks in order just for compatibility
     with CompCert? Probably not. *)
  Inductive mem_op :=
  | MRead : ptr -> val -> mem_op
  | MWrite : ptr -> val -> mem_op
  | MAlloc : block -> nat -> mem_op
  | MFree : block -> mem_op. (* Should we be able to free parts of blocks? *)
  Definition mem := ilist mem_op.

  Definition block_of op := match op with
  | MRead (b, _) _ => b
  | MWrite (b, _) _ => b
  | MAlloc b _ => b
  | MFree b => b
  end.

  Global Instance ptr_eq : @EqDec ptr eq eq_equivalence.
  Proof. eq_dec_inst. Qed.

  Definition op_modifies a p := match a with
  | MWrite p' _ => if eq_dec p p' then true else false
  | MAlloc b _ => if eq_dec b (fst p) then true else false
  | MFree b => if eq_dec b (fst p) then true else false
  | _ => false
  end.

  Definition not_read a := match a with
  | MRead _ _ => false
  | _ => true
  end.

  Inductive loc := Ptr (p : ptr) | Block (b : block).

  Definition loc_of op := match op with
  | MRead p _ => Ptr p
  | MWrite p _ => Ptr p
  | MAlloc b _ => Block b
  | MFree b => Block b
  end.

  Definition block_of_loc l := match l with
  | Ptr (b, _) => b
  | Block b => b
  end.

  Lemma block_of_loc_spec : forall op, block_of_loc (loc_of op) = block_of op.
  Proof. destruct op; clarify. Qed.

  (* Is there a more fundamental notion of independence hidden here? *)
  Fixpoint independent l1 l2 : Prop := match (l1, l2) with
  | (Ptr p, Ptr p') => ~(p = p')
  | _ => ~(block_of_loc l1 = block_of_loc l2)
  end.

  Global Instance indep_sym : Symmetric independent.
  Proof. intros x y H; destruct x, y; clarify. Qed.

  Definition indep_dec l1 l2 : {independent l1 l2} + {~independent l1 l2}.
  Proof.
    destruct l1; simpl.
    - destruct l2; simpl.
      + destruct (eq_dec p p0); clarify.
      + destruct p.
        destruct (eq_dec b0 b); clarify.
    - destruct (eq_dec b (block_of_loc l2)); clarify.
  Qed.

  Lemma block_indep : forall l1 l2, 
    block_of_loc l1 <> block_of_loc l2 -> independent l1 l2.
  Proof. destruct l1, l2; repeat intro; clarify. Qed.
  Hint Resolve block_indep.
  
  (* Perhaps this is just my inexperience with coinduction, but the reasonable
     theorems seem to become unprovable if the trace is reversed. *)
  Coercion to_ilist : list >-> ilist.
  Class Memory_Layout := { 
    consistent : mem -> Prop;
(*    consistent_eq : forall m m', EqSt m m' -> (consistent m <-> consistent m');*)
    consistent_prefix : forall m m' (Hcon : consistent m) (Hpre : iprefix m' m),
      consistent m';
    loc_comm : forall ops op1 op2 m
      (Hindep : independent (loc_of op1) (loc_of op2))
      (Hcon : consistent (iapp ops (icons op1 (icons op2 m)))),
      consistent (iapp ops (icons op2 (icons op1 m)));
    loc_valid : forall m op1 op2 
      (Hindep : independent (loc_of op1) (loc_of op2))
      (H1 : consistent (m ++ [op1])) (H2 : consistent (m ++ [op2])),
      consistent (m ++ [op1; op2]);
    read_noop : forall m p v m2 (Hcon : consistent (m ++ [MRead p v])),
      consistent (iapp (m ++ [MRead p v]) m2) <->
      consistent (iapp m m2);
    read_written : forall m p v v' (Hcon : consistent (m ++ [MWrite p v])),
      consistent (m ++ [MWrite p v; MRead p v']) <-> v' = v;
    (* This one's phrased a bit awkwardly. *)
    write_not_read : forall m p v ops
      (Hnot_read : Forall (fun op => forall v', op <> MRead p v') ops),
      consistent (m ++ MWrite p v :: ops) <->
      consistent (m ++ [MWrite p v]) /\ consistent (m ++ ops);
    not_mod_write : forall m p v op (Hnot_mod : op_modifies op p = false)
      (Hcon : consistent (m ++ [op])),
      consistent (m ++ [op; MWrite p v]) <->
      consistent (m ++ [MWrite p v]);
    alloc_allows : forall m b n (Hcon : consistent (m ++ [MAlloc b n])),
      (forall o v, o < n -> consistent (m ++ [MAlloc b n; MWrite (b, o) v])) /\
      consistent (m ++ [MAlloc b n; MFree b]) /\
      (forall n', ~consistent (m ++ [MAlloc b n; MAlloc b n']));
    free_allows : forall m b (Hcon : consistent (m ++ [MFree b])),
      (forall o v, ~consistent (m ++ [MFree b; MRead (b, o) v])) /\
      (forall n, consistent (m ++ [MFree b; MAlloc b n])) /\
      ~consistent (m ++ [MFree b; MFree b]);
    base_allows : (forall p v, ~consistent [MRead p v]) /\
      (forall b, (forall n, consistent [MAlloc b n]) /\ ~consistent [MFree b]);
    write_any_value : forall m p v v',
      consistent (m ++ [MWrite p v]) <-> consistent (m ++ [MWrite p v']) }.

  Context {ML : Memory_Layout}.

  Lemma loc_comm_iff : forall ops op1 op2 m
    (Hindep : independent (loc_of op1) (loc_of op2)),
    consistent (iapp ops (icons op1 (icons op2 m))) <->
    consistent (iapp ops (icons op2 (icons op1 m))).
  Proof. intros; split; apply loc_comm; [|symmetry]; auto. Qed.

  Lemma loc_comm_hd : forall op1 op2 m
    (Hindep : independent (loc_of op1) (loc_of op2)),
    consistent (icons op1 (icons op2 m)) <->
    consistent (icons op2 (icons op1 m)).
  Proof. apply (loc_comm_iff []). Qed.

  Lemma loc_comm_tl : forall m op1 op2
    (Hindep : independent (loc_of op1) (loc_of op2)),
    consistent (m ++ [op1; op2]) <-> consistent (m ++ [op2; op1]).
  Proof. 
    intros.
    repeat rewrite to_ilist_app; clarify.
    apply loc_comm_iff; auto.
  Qed.

  Lemma consistent_app : forall m1 m2, consistent (m1 ++ m2) -> consistent m1.
  Proof. intros; eapply consistent_prefix; eauto; apply app_prefix. Qed.

  Lemma loc_valid_iff : forall m op1 op2 
    (Hindep : independent (loc_of op1) (loc_of op2)),
    consistent (m ++ [op1; op2]) <->
    (consistent (m ++ [op1]) /\ consistent (m ++ [op2])).
  Proof.
    intros; split; clarify; [|apply loc_valid; auto]; split.
    - eapply consistent_app; rewrite <- app_assoc; simpl; eauto.
    - rewrite loc_comm_tl in H; auto.
      eapply consistent_app; rewrite <- app_assoc; simpl; eauto.
  Qed.

  Definition can_do_op m op := consistent (m ++ [op]).

  Definition can_do_ops m ops := consistent (m ++ ops).

  Lemma do_one_op : forall m a, can_do_op m a = can_do_ops m [a].
  Proof. unfold can_do_op, can_do_ops; clarify. Qed.

  Lemma loc_comm_ops1 : forall op ops m1 m2 
    (Hindep : Forall (independent (loc_of op)) (map loc_of ops)),
    consistent (iapp m1 (icons op (iapp ops m2))) <-> 
    consistent (iapp m1 (iapp ops (icons op m2))).
  Proof.
    induction ops; clarify; try reflexivity.
    inversion Hindep; clarify.
    rewrite loc_comm_iff; clarsimp.
    transitivity (consistent (iapp (m1 ++ [a]) (icons op (iapp ops m2)))).
    - rewrite <- iapp_app; simpl; reflexivity.
    - rewrite IHops; auto; rewrite <- iapp_app; simpl; reflexivity.
  Qed.

  Lemma loc_comm_ops : forall ops ops' m1 m2
    (Hindep : Forall (fun l => Forall (independent l) (map loc_of ops)) 
                     (map loc_of ops')),
    consistent (iapp m1 (iapp ops (iapp ops' m2))) <-> 
    consistent (iapp m1 (iapp ops' (iapp ops m2))).
  Proof.
    induction ops; clarify; try reflexivity.
    rewrite <- loc_comm_ops1; clarsimp.
    transitivity (consistent (iapp (m1 ++ [a])
                                      (iapp ops (iapp ops' m2)))).
    - rewrite <- iapp_app; simpl; reflexivity.
    - rewrite IHops.
      rewrite <- iapp_app; simpl; reflexivity.
      { eapply Forall_impl; eauto; clarify.
        inversion H; auto. }
    - eapply Forall_impl; [|apply Hindep]; clarify.
      inversion H; symmetry; auto.
  Qed.

  Lemma loc_valid_ops1 : forall op ops m
    (Hindep : Forall (independent (loc_of op)) (map loc_of ops))
    (Hops : consistent (m ++ ops)) (Hop : consistent (m ++ [op])),
    consistent (m ++ ops ++ [op]).
  Proof.
    induction ops using rev_ind; clarsimp.
    rewrite map_app in Hindep; clarify; rewrite Forall_snoc in Hindep; clarify.
    rewrite app_assoc; apply loc_valid; try rewrite <- app_assoc; auto.
    { symmetry; auto. }
    apply IHops; auto.
    eapply consistent_app; rewrite <- app_assoc; eauto.
  Qed.

  (* Would we also need the version where ops' is infinite?
     Can we prove it? *)
  Lemma loc_valid_ops : forall ops ops' m
    (Hindep : Forall (fun l => Forall (independent l) (map loc_of ops')) 
                     (map loc_of ops))
    (H1 : consistent (m ++ ops)) (H2 : consistent (m ++ ops')),
    consistent (m ++ ops ++ ops').
  Proof.
    induction ops; clarify.
    specialize (IHops ops' (m ++ [a])).
    inversion Hindep; clarsimp.
    apply IHops.
    generalize (loc_comm_ops1 a ops' m inil), (loc_valid_ops1 a ops' m),
      (consistent_app (m ++ [a]) ops); intros Hcomm Hvalid Hcon.
    repeat rewrite to_ilist_app in *; clarify.
    rewrite iapp_nil_ilist in *; rewrite Hcomm; apply Hvalid; apply Hcon.
    rewrite <- iapp_app; clarify.
  Qed.

  Lemma reads_noops : forall ops m m2 (Hcon : consistent (m ++ ops))
    (Hreads : Forall (fun x => match x with MRead _ _ => True | _ => False end)
                      ops),
    consistent (iapp (m ++ ops) m2) <-> consistent (iapp m m2).
  Proof.
    induction ops; clarsimp; [reflexivity|].
    inversion Hreads; clarify; destruct a; clarify.
    generalize (consistent_app (m ++ [MRead p v]) ops); clarsimp.
    assert (m ++ MRead p v :: ops = (m ++ [MRead p v]) ++ ops) as X by clarsimp.
    rewrite X; rewrite <- iapp_app; rewrite read_noop; auto.
    rewrite iapp_app; apply IHops; auto.
    rewrite X in Hcon; rewrite to_ilist_app in *; rewrite read_noop in Hcon;
      auto.
    rewrite to_ilist_app; auto.
  Qed.

  Lemma not_mod_ops_write : forall ops m p v
    (Hnot_mod : Forall (fun op => op_modifies op p = false) ops)
    (Hcon : consistent (m ++ ops)),
    consistent (m ++ ops ++ [MWrite p v]) <-> consistent (m ++ [MWrite p v]).
  Proof.
    induction ops using rev_ind; clarify; [reflexivity|].
    rewrite Forall_snoc in Hnot_mod; clarify.
    rewrite <- app_assoc, app_assoc; simpl; rewrite not_mod_write; clarsimp.
    apply IHops; auto.
    eapply consistent_app; rewrite <- app_assoc; eauto.
  Qed.

  Lemma consistent_nil : forall (b : block), consistent inil.
  Proof.
    generalize base_allows; clarify.
    specialize (H2 b); clarify.
    specialize (H21 0); eapply consistent_prefix; eauto; constructor.
  Qed.    

  Lemma read_noop_single : forall m p v op
    (Hread : consistent (m ++ [MRead p v])),
    consistent (m ++ [MRead p v; op]) <-> consistent (m ++ [op]).
  Proof.
    intros; generalize (read_noop _ _ _ [op] Hread); intro H.
    repeat rewrite to_ilist_app; rewrite <- H; clarify.
    rewrite <- iapp_app; simpl; reflexivity.
  Qed.

  Lemma write_not_read_single : forall m p v op
    (Hnot_read : forall v' : val, op <> MRead p v'),
    consistent (m ++ [MWrite p v; op]) <->
    consistent (m ++ [MWrite p v]) /\ consistent (m ++ [op]).
  Proof.
    intros; exploit write_not_read.
    { instantiate (1 := [op]); constructor; clarify. }
    intro H; repeat rewrite to_ilist_app in *; rewrite <- H; reflexivity.
  Qed.

  Lemma dep_block : forall l l', ~independent l l' ->
    block_of_loc l = block_of_loc l'.
  Proof.
    destruct l, l'; try (destruct p); try (destruct p0); destruct (eq_dec b b0);
      clarify.
    - destruct (eq_dec (b, n) (b0, n0)); clarify.
    - destruct (eq_dec b0 b); clarify.
  Qed.

  Class ML_impl := {
    read : list mem_op -> ptr -> option val;
    get_free : list mem_op -> nat -> option block;
    can_do : list mem_op -> mem_op -> bool;
    read_correct : forall (m : list mem_op) p v (Hread : read m p = Some v),
      consistent (m ++ [MRead p v]);
    get_free_correct : forall (m : list mem_op) n b
      (Hfree : get_free m n = Some b),
      consistent (m ++ [MAlloc b n]);
    can_do_correct : forall (m : list mem_op) op (Hcan_do : can_do m op = true)
      (Hcon : consistent m), consistent (m ++ [op]) }.
  
  Context {MLI : ML_impl}.
  Fixpoint can_do_list (m : list mem_op) ops :=
    match ops with
    | [] => true
    | op :: rest => can_do m op && can_do_list (m ++ [op]) rest
    end.

End Model.
Arguments MAlloc [block] [val] _ _.
Arguments MFree [block] [val] _.
Arguments loc_of {block} {val} _.
Arguments not_read {block} {val} _.

Section Simple.
  Context {block val : Type} {block_eq : EqDec_eq block}
    {val_eq : EqDec_eq val}.

  Inductive mem_cell := Uninit | Stored (v : val).
  Instance mem_cell_eq : @EquivDec.EqDec mem_cell eq eq_equivalence.
  Proof. eq_dec_inst. Qed.

  Definition simple_mem := block -> option (list mem_cell).
  Definition simple_update m (b : block) (c : option (list mem_cell)) b' := 
    if eq_dec b' b then c else m b'.

  Definition simple_access (m : simple_mem) (a : mem_op block val) := 
  match a with
  | MRead (b, o) v => 
      match m b with
      | Some c => match nth_error c o with 
                  | Some (Stored v') => if eq_dec v' v then Some m else None 
                  | _ => None 
                  end
      | None => None
      end
  | MWrite (b, o) v =>
      match m b with
      | Some c => if lt_dec o (length c)
                  then Some (simple_update m b (Some (replace c o (Stored v)))) 
                  else None
      | None => None
      end
  | MAlloc b n => match m b with
                  | Some _ => None
                  | None => Some (simple_update m b (Some (replicate Uninit n)))
                  end
  | MFree b => match m b with
               | Some _ => Some (simple_update m b None)
               | None => None
               end
  end.

  Fixpoint simple_accesses m ops := match ops with
  | [] => Some m
  | op :: rest => match simple_access m op with
                  | Some m' => simple_accesses m' rest
                  | None => None
                  end
  end.

  Lemma simple_diff_block : forall sm a sm' b, simple_access sm a = Some sm' ->
    b <> block_of a -> sm' b = sm b.
  Proof.
    destruct a; clarify; destruct (sm b) eqn: Hb; try (destruct p); clarify;
      unfold simple_update; destruct (eq_dec b b0); clarify;
      destruct x0; clarify.
  Qed.

  Lemma simple_indep_ptr : forall sm a sm' b, simple_access sm a = Some sm' ->
    forall o c, independent (loc_of a) (Ptr (b, o)) -> sm b = Some c ->
    exists c', sm' b = Some c' /\ length c' = length c /\ 
               nth_error c' o = nth_error c o.
  Proof.
    destruct a; clarify; destruct (sm b) eqn: Hb; try (destruct p); clarify;
      unfold simple_update; destruct (eq_dec b b0); try (destruct x0); clarsimp;
      eauto 4.
    - destruct (eq_dec o n); clarify; eexists; split; eauto.
      rewrite replace_length, nth_error_replace_2; auto.
    - eexists; clarify.
    - eexists; clarify.
  Qed.

  Lemma simple_indep_ptr' : forall sm a sm' b, simple_access sm a = Some sm' ->
    forall o c', independent (loc_of a) (Ptr (b, o)) -> sm' b = Some c' ->
    exists c, sm b = Some c /\ length c' = length c /\ 
               nth_error c' o = nth_error c o.
  Proof.
    destruct a; clarify; try (destruct p); clarify; unfold simple_update in *;
      destruct (eq_dec b b0); try (destruct x0); clarsimp; eauto 4.
    - rewrite replace_length, nth_error_replace_2; eauto.
    - eexists; clarify.
  Qed.

  Lemma simple_indep_access : forall sm a sma
    (Ha : simple_access sm a = Some sma) 
    b (Hindep : independent (loc_of a) (loc_of b))
    smb (Hb : simple_access sm b = Some smb),
    exists sm', simple_access sma b = Some sm'.
  Proof.
    destruct a; clarify.
    - destruct p; clarify.
      destruct x0; clarify; eauto.
    - destruct p; clarify.
      destruct b; clarify; try (destruct p; clarify); 
        try (destruct x1; clarify); unfold simple_update;
        destruct (eq_dec b b0); clarsimp; eauto 2.
      + destruct (eq_dec n0 n); clarify.
        rewrite nth_error_replace_2; clarsimp; eauto.
      + rewrite replace_length; clarify; eauto.
    - destruct b0; clarify; try (destruct p; clarify); 
        try (destruct x0; clarify); unfold simple_update;
        destruct (eq_dec b0 b); clarsimp; eauto.
    - destruct b0; clarify; try (destruct p; clarify); 
        try (destruct x1; clarify); unfold simple_update;
        destruct (eq_dec b0 b); clarsimp; eauto.
  Qed.

  Lemma simple_indep_access' : forall sm a sma
    (Ha : simple_access sm a = Some sma)
    b (Hindep : independent (loc_of a) (loc_of b))
    smb (Hb : simple_access sma b = Some smb),
    exists sm', simple_access sm b = Some sm'.
  Proof.
    destruct a; clarify.
    - destruct p; clarify.
      destruct x0; clarify; eauto.
    - destruct p; clarify.
      destruct b; clarify; try (destruct p; clarify);
        try (destruct x1; clarify); unfold simple_update in *;
        destruct (eq_dec b b0); clarsimp; eauto 2.
      + destruct (eq_dec n0 n); clarify.
        rewrite nth_error_replace_2 in Hb21; clarsimp; eauto.
      + clear cond0; rewrite replace_length in l0; clarify; eauto.
    - destruct b0; clarify; try (destruct p; clarify); 
        try (destruct x0; clarify); unfold simple_update in *;
        destruct (eq_dec b0 b); clarsimp; eauto.
    - destruct b0; clarify; try (destruct p; clarify); 
        try (destruct x1; clarify); unfold simple_update in *;
        destruct (eq_dec b0 b); clarsimp; eauto.
  Qed.      

  CoInductive admits m : mem block val -> Prop :=
  | admits_nil : admits m inil
  | admits_step : forall op m' (Hstep : simple_access m op = Some m')
      ops (Hadmits : admits m' ops), admits m (icons op ops).
  Hint Constructors admits.

  Lemma admits_prefix : forall m ops (Hadmits : admits m ops)
    ops' (Hpre : iprefix ops' ops), admits m ops'.
  Proof.
    cofix; intros.
    inversion Hpre; clarify.
    inversion Hadmits; clarify.
    econstructor; eauto.
  Qed.

  Lemma admits_app : forall ops m ops'
    m' (Hops : simple_accesses m ops = Some m') (Hadmits : admits m' ops'),
    admits m (iapp ops ops').
  Proof.
    induction ops; clarify.
    econstructor; eauto.
  Qed.

  Lemma admits_app_inv : forall ops m ops' (Hadmits : admits m (iapp ops ops')),
    exists m', simple_accesses m ops = Some m' /\ admits m' ops'.
  Proof.
    induction ops; clarify; eauto.
    inversion Hadmits; clarify.
  Qed.

  Lemma single_access : forall sm op, simple_accesses sm [op] = 
    simple_access sm op.
  Proof. clarify; destruct (simple_access sm op); auto. Qed.

  Lemma simple_accesses_app : forall m sm m',
    simple_accesses sm (m ++ m') =
      match simple_accesses sm m with
      | Some sm' => simple_accesses sm' m'
      | None => None
      end.
  Proof.
    induction m; clarify.
    destruct (simple_access sm a); clarify.
  Qed.

  Corollary simple_accesses_snoc : forall m sm op,
    simple_accesses sm (m ++ [op]) =
      match simple_accesses sm m with
      | Some sm' => simple_access sm' op
      | None => None
      end.
  Proof.
    intros; rewrite simple_accesses_app; simpl.
    destruct (simple_accesses sm m); clarify.
    destruct (simple_access s op); clarify.
  Qed.

  Section Instance.
    Lemma simple_comm : forall op1 op2
      (Hindep : independent (loc_of op1) (loc_of op2)) m m',
      simple_accesses m [op1; op2] = Some m' ->
      exists m'', simple_accesses m [op2; op1] = Some m'' /\
                  forall b, m'' b = m' b.
    Proof.
      intros; destruct op1; clarify.
      - destruct p as (b1, o1).
        destruct (m b1) eqn: Hblock1; clarify.
        destruct x0; clarify.
        exploit simple_indep_ptr; eauto.
        { apply indep_sym; eauto. }
        clarsimp.
        eexists; split; eauto; clarify.
      - destruct p as (b1, o1).
        destruct (m b1) eqn: Hblock1; clarify.
        destruct op2; clarify.
        + destruct p as (b2, o2); unfold simple_update in *; clarify.
          destruct x0; clarify.
          destruct (eq_dec b2 b1); clarsimp; eauto.
          destruct (eq_dec o2 o1); clarify.
          rewrite nth_error_replace_2 in H2121; clarify; eauto.
        + destruct p as (b2, o2); unfold simple_update in *; clarify.
          destruct (eq_dec b2 b1); clarsimp.
          * clear cond0; rewrite replace_length in l1; clarify.
            rewrite replace_length; clarify.
            eexists; split; eauto; clarify.
            rewrite replace_replace; auto.
          * destruct (eq_dec b1 b2); clarify.
            eexists; split; eauto; clarify.
        + unfold simple_update in *; clarify.
          destruct (eq_dec b1 b); clarify.
          eexists; split; eauto; clarify.
        + unfold simple_update in *; clarify.
          destruct (eq_dec b b1); clarsimp.
          destruct (eq_dec b1 b); clarify.
          eexists; split; eauto; clarify.
      - destruct op2; clarify.
        + destruct p as (b2, o2); unfold simple_update in *; clarify.
          destruct x0; clarify.
          destruct (eq_dec b2 b); clarsimp; eauto.
        + destruct p as (b2, o2); unfold simple_update in *; clarify.
          destruct (eq_dec b2 b); clarsimp.
          destruct (eq_dec b b2); clarify.
          eexists; split; eauto; clarify.
        + unfold simple_update in *; clarify.
          destruct (eq_dec b b0); clarify.
          eexists; split; eauto; clarify.
        + unfold simple_update in *; clarify.
          destruct (eq_dec b0 b); clarsimp.
          destruct (eq_dec b b0); clarify.
          eexists; split; eauto; clarify.
      - destruct op2; clarify.
        + destruct p as (b2, o2); unfold simple_update in *; clarify.
          destruct x0; clarify; eauto.
        + destruct p as (b2, o2); unfold simple_update in *; clarify.
          destruct (eq_dec b b2); clarsimp.
          eexists; split; eauto; clarify.
        + unfold simple_update in *; clarify.
          destruct (eq_dec b0 b); clarify.
          destruct (eq_dec b b0); clarify.
          eexists; split; eauto; clarify.
        + unfold simple_update in *; clarify.
          destruct (eq_dec b b0); clarify.
          eexists; split; eauto; clarify.
    Qed.

    Lemma ext_sim : forall m1 m2 (Hext : forall b, m2 b = m1 b)
      a m1' (Ha : simple_access m1 a = Some m1'),
      exists m2', simple_access m2 a = Some m2' /\ forall b, m2' b = m1' b.
    Proof.
      intros; destruct a; clarify; try (destruct p; clarify); rewrite Hext;
        clarsimp; try (eexists; split; eauto; unfold simple_update; clarify;
                       fail).
      destruct x0; clarify; eauto.
    Qed.

    Lemma ext_sim_ops : forall ops m1 m2 (Hext : forall b, m2 b = m1 b)
      m1' (Ha : simple_accesses m1 ops = Some m1'),
      exists m2', simple_accesses m2 ops = Some m2' /\ forall b, m2' b = m1' b.
    Proof.
      induction ops; clarify; eauto.
      exploit ext_sim; eauto; clarify; eauto.
    Qed.

    Lemma admits_sim : forall m1 m2 (Hext : forall b, m2 b = m1 b) ops
      (Hadmits : admits m1 ops), admits m2 ops.
    Proof.
      cofix; intros.
      inversion Hadmits; clarify.
      generalize (ext_sim _ _ Hext _ Hstep); clarify.
      econstructor; [eauto|].
      eapply admits_sim; eauto.
    Qed.

    Lemma admits_comm : forall m ops op1 op2 ops'
      (Hindep : independent (loc_of op1) (loc_of op2))
      (Hadmits : admits m (iapp ops (icons op1 (icons op2 ops')))),
      admits m (iapp ops (icons op2 (icons op1 ops'))).
    Proof.
      intros.
      exploit admits_app_inv; eauto; clarify.
      eapply admits_app; eauto.
      inversion H2; clarify.
      inversion Hadmits0; clarify.
      exploit simple_comm; eauto; clarify.
      { setoid_rewrite Hstep; clarify. }
      econstructor; eauto.
      econstructor; eauto.
      eapply admits_sim; eauto.
    Qed.

    Lemma exists_reorder : forall {A B} (f : A -> B -> Prop),
      (exists a b, f a b) <-> (exists b a, f a b).
    Proof. intros; split; clarify; eauto. Qed.

    Lemma not_read_sim : forall m1 m2 b o c (Hc : m1 b = Some c)
      v' (Hm2 : forall b', b' <> b -> m2 b' = m1 b')
      (Hb : m2 b = Some (replace c o v')) 
      op (Hnot_read : forall v, op <> MRead (b, o) v)
      m1' (Hop : simple_access m1 op = Some m1'),
      exists m2', simple_access m2 op = Some m2' /\
        (forall b', b' <> b -> m2' b' = m1' b') /\
        (m2' b = m1' b \/ exists c', m1' b = Some c' /\
                                     m2' b = Some (replace c' o v')).
    Proof.
      intros; destruct op; clarify.
      - destruct p as (b1, o1); clarify.
        destruct x0; clarify.
        destruct (eq_dec b1 b); clarsimp.
        + generalize (nth_error_lt _ _ Hop21); intro Hlt.
          specialize (Hnot_read v).
          destruct (eq_dec o1 o); clarify.
          rewrite nth_error_replace_2; clarify.
          eexists; split; eauto.
        + rewrite Hm2; clarsimp.
          eexists; split; eauto.
      - destruct p as (b1, o1); clarify.
        destruct (eq_dec b1 b); clarsimp.
        + rewrite replace_length; clarify.
          eexists; split; eauto; unfold simple_update; split; clarify.
          destruct (eq_dec o1 o); clarify.
          * rewrite replace_same; auto.
          * right; eexists; split; eauto.
          rewrite replace_replace; auto.
        + rewrite Hm2; clarsimp.
          eexists; split; eauto; unfold simple_update; split; clarify; eauto.
      - destruct (eq_dec b0 b); clarify.
        rewrite Hm2; clarsimp.
        eexists; split; eauto; unfold simple_update; split; clarify; eauto.
      - destruct (eq_dec b0 b); clarify.
        + eexists; split; eauto; unfold simple_update; split; clarify.
        + rewrite Hm2; clarsimp.
          eexists; split; eauto; unfold simple_update; split; clarify; eauto.
    Qed.

    Lemma not_read_sim_ops : forall ops m1 m2 b o c (Hc : m1 b = Some c)
      v' (Hm2 : forall b', b' <> b -> m2 b' = m1 b')
      (Hb : m2 b = Some (replace c o v')) 
      (Hnot_read : Forall (fun op => forall v, op <> MRead (b, o) v) ops)
      m1' (Hop : simple_accesses m1 ops = Some m1'),
      exists m2', simple_accesses m2 ops = Some m2' /\
        (forall b', b' <> b -> m2' b' = m1' b') /\
        (m2' b = m1' b \/ exists c', m1' b = Some c' /\
                                     m2' b = Some (replace c' o v')).
    Proof.
      induction ops; clarify.
      - eexists; split; eauto.
      - inversion Hnot_read; clarify.
        exploit not_read_sim; try (apply Hop1); eauto; clarify.
        destruct H32; clarify.
        + exploit (ext_sim_ops ops x x0); eauto; clarsimp; eauto.
          { destruct (eq_dec b0 b); clarify. }
        + exploit IHops; try (apply Hop2); eauto.
    Qed.

    Lemma admits_not_read_sim : forall m1 m2 b o c (Hc : m1 b = Some c)
      v' (Hm2 : forall b', b' <> b -> m2 b' = m1 b')
      (Hb : m2 b = Some (replace c o v'))
      ops (Hnot_read : Forall (fun op => forall v, op <> MRead (b, o) v) ops)
      (Hadmits : admits m1 ops), admits m2 ops.
    Proof.
      cofix CIH; intros.
      inversion Hadmits; clarify.
      inversion Hnot_read; clarify.
      inversion H0; clarify.
      generalize (not_read_sim _ _ Hc _ Hm2 Hb H Hstep); clarify.
      econstructor; [eauto|].
      specialize (CIH m' x0).
      destruct H022; clarify.
      - eapply admits_sim; [|eassumption].
        intro b'; destruct (eq_dec b' b); clarify.
      - eapply CIH; eauto.
    Qed.

    Instance simple_instance : Memory_Layout val block_eq :=
      {| consistent := fun m => admits (fun _ => None) m |}.
    Proof.
      - intros; eapply admits_prefix; eauto.
      - intros; apply admits_comm; auto.
      - intros; rewrite to_ilist_app in *.
        generalize (admits_app_inv _ _ H1), (admits_app_inv _ _ H2); clarsimp.
        inversion H02; clarify.
        inversion H3; clarify.
        exploit simple_indep_access; eauto; clarify.
        eapply admits_app; eauto.
      - intros; rewrite to_ilist_app in *; generalize (admits_app_inv _ _ Hcon);
          clarify.
        inversion H2; clarify.
        destruct p; clarify.
        destruct x1; clarify.
        split; intro Happ; generalize (admits_app_inv _ _ Happ); clarify;
          eapply admits_app; eauto.
        + rewrite simple_accesses_app in *; clarify.
          destruct x4; clarsimp.
        + rewrite simple_accesses_app; clarsimp.
          repeat eexists; eauto; clarify.
      - intros; rewrite to_ilist_app in *; generalize (admits_app_inv _ _ Hcon);
          clarify.
        inversion H2; clarify.
        destruct p; clarify.
        split; clarify.
        + generalize (admits_app_inv _ _ H); clarify.
          inversion H02; clarify.
          inversion Hadmits0; clarify.
          unfold simple_update in *; clarify.
          rewrite nth_error_replace in Hstep31; clarify.
        + eapply admits_app; eauto.
          econstructor; clarify.
          econstructor; unfold simple_update; clarify.
          rewrite nth_error_replace; clarify.
      - intros.
        split; intro Hadmits; clarify.
        + rewrite to_ilist_app in *.
          generalize (admits_app_inv _ _ Hadmits); clarify.
          inversion H2; clarify.
          destruct p; clarify.
          split.
          * eapply admits_prefix; eauto.
            apply prefix_mono; constructor; constructor.
          * rewrite to_ilist_app.
            eapply admits_app; eauto.
            exploit (nth_error_succeeds(A := mem_cell)); eauto; clarify.
            eapply admits_not_read_sim; try (apply Hadmits0); eauto;
              unfold simple_update; clarify.
            rewrite replace_same; rewrite replace_idem; eauto.
        + rewrite to_ilist_app in *.
          generalize (admits_app_inv _ _ Hadmits1),
            (admits_app_inv _ _ Hadmits2); clarsimp.
          eapply admits_app; eauto.
          inversion H2; clarify.
          simpl; econstructor; eauto.
          destruct p; clarify.
          eapply admits_not_read_sim; eauto; unfold simple_update; clarify.
      - intros; rewrite to_ilist_app in *; generalize (admits_app_inv _ _ Hcon);
          clarify.
        inversion H2; clarify.
        rewrite to_ilist_app.
        split; intro Hadmits'; generalize (admits_app_inv _ _ Hadmits');
          clarify; eapply admits_app; eauto.
        + inversion H3; clarify.
          inversion Hadmits0; clarify.
          destruct p; clarify.
          destruct (eq_dec (block_of op) b); clarify.
          * destruct op; clarify.
            { destruct p; clarify.
              destruct x3, x5; clarsimp. }
            { destruct p; unfold simple_update in *; clarify.
              clear cond; rewrite replace_length in l.
              econstructor; clarify. }
          * econstructor; clarify.
            exploit simple_diff_block; eauto; intro H.
            rewrite <- H; clarify.
        + inversion H3; clarify.
          destruct p; clarify.
          destruct (eq_dec (block_of op) b); clarify.
          * destruct op; clarify.
            { destruct p; clarify.
              destruct x3; clarsimp.
              econstructor; clarify. }
            { destruct p; clarsimp.
              econstructor; clarify.
              econstructor; unfold simple_update; clarify.
              clear cond2; rewrite replace_length in n2; clarify. }
          * exploit simple_diff_block; eauto; intro H.
            clarsimp.
            destruct op; clarify.
            { destruct p; clarify.
              destruct x2; clarify.
              econstructor; clarify. }
            { destruct p; clarify.
              econstructor; clarify.
              econstructor; unfold simple_update in *; clarify. }
            { econstructor; clarify.
              econstructor; clarify. }
            { econstructor; clarify.
              econstructor; clarify. }
      - intros; rewrite to_ilist_app in *; generalize (admits_app_inv _ _ Hcon);
          clarify.
        inversion H2; clarify.
        repeat split; clarify; try rewrite to_ilist_app; try (eapply admits_app;
          eauto); clarify.
        + econstructor; clarify.
          econstructor; unfold simple_update; clarify.
          clear cond0; rewrite replicate_length in n0; clarify.
        + econstructor; clarify.
          econstructor; unfold simple_update; clarify.
        + intro Halloc.
          generalize (admits_app_inv _ _ Halloc); clarify.
          inversion H3; clarify.
          inversion Hadmits0; unfold simple_update in *; clarify.
      - intros; rewrite to_ilist_app in *; generalize (admits_app_inv _ _ Hcon);
          clarify.
        inversion H2; clarify.
        repeat split; clarify; try rewrite to_ilist_app; try (eapply admits_app;
          eauto); clarify.
        + intro HRead.
          generalize (admits_app_inv _ _ HRead); clarify.
          inversion H3; clarify.
          inversion Hadmits0; unfold simple_update in *; clarify.
        + econstructor; clarify.
          econstructor; unfold simple_update; clarify.
        + intro Hfree.
          generalize (admits_app_inv _ _ Hfree); clarify.
          inversion H3; clarify.
          inversion Hadmits0; unfold simple_update in *; clarify.
      - repeat split; clarify.
        + intro Hread; inversion Hread; clarify.
          destruct p; clarify.
        + econstructor; eauto; clarify.
        + intro Hfree; inversion Hfree; clarify.
      - intros; repeat rewrite to_ilist_app.
        split; intro Hwrite; generalize (admits_app_inv _ _ Hwrite);
          clarify; eapply admits_app; eauto.
        + inversion H2; clarify.
          destruct p; clarify.
          econstructor; clarify.
        + inversion H2; clarify.
          destruct p; clarify.
          econstructor; clarify.
    Defined.

    Definition make_simple ops := simple_accesses (fun _ => None) ops.

    Lemma make_simple_app : forall ops m,
      make_simple (m ++ ops) =
        match make_simple m with
        | Some sm' => simple_accesses sm' ops
        | None => None
        end.
    Proof. unfold make_simple; intros; apply simple_accesses_app. Qed.

    Definition simple_read m (p : ptr block) := let (b, o) := p in
      match make_simple m with
      | Some sm =>
          match sm b with
          | Some c =>
              match nth_error c o with
              | Some (Stored v) => Some v
              | _ => None
              end
          | None => None
          end
      | None => None
      end.

    Variable (fresh : list block -> block).
    Hypothesis fresh_spec : forall l, ~In (fresh l) l.

    Fixpoint gather_blocks (m : list (mem_op block val)) :=
      match m with
      | [] => []
      | MAlloc b _ :: rest => b :: gather_blocks rest
      | _ :: rest => gather_blocks rest
      end.

    Lemma gather_blocks_spec : forall m b,
      In b (gather_blocks m) <-> exists n, In (MAlloc b n) m.
    Proof.
      induction m; clarify.
      - split; clarify.
      - destruct a; simpl; rewrite IHm; split; clarify; eauto.
        + destruct H; clarify; eauto.
        + destruct H as [H | ?]; [inversion H|]; clarify; eauto.
    Qed.

    Lemma block_allocated : forall m sm (Hmake : make_simple m = Some sm)
      b c (Hblock : sm b = Some c), exists n, In (MAlloc b n) m.
    Proof.
      induction m using rev_ind; clarify.
      - unfold make_simple in Hmake; clarify.
      - rewrite make_simple_app in Hmake; clarify.
        setoid_rewrite in_app_iff; simpl.
        specialize (IHm _ Hmake1).
        destruct x; clarify.
        + destruct p; clarify.
          destruct x1; clarify.
          specialize (IHm _ _ Hblock); clarify; eauto.
        + destruct p; clarify.
          unfold simple_update in *; clarify.
          destruct (eq_dec b b0); clarify; exploit IHm; eauto; clarify; eauto.
        + unfold simple_update in *; clarify.
          destruct (eq_dec b b0); clarify; eauto.
          exploit IHm; eauto; clarify; eauto.
        + unfold simple_update in *; clarify.
          exploit IHm; eauto; clarify; eauto.
    Qed.

    Instance simple_impl : ML_impl(ML := simple_instance) :=
      {| read := simple_read; 
         get_free := fun m n => match make_simple m with
                                | Some _ => Some (fresh (gather_blocks m))
                                | None => None
                                end;
         can_do := fun m op => match make_simple (m ++ [op]) with
                               | Some _ => true
                               | _ => false
                               end |}.
    Proof.
      - unfold simple_read; clarify.
        destruct p; clarsimp.
        rewrite to_ilist_app; eapply admits_app; eauto.
        destruct x1; clarify.
        econstructor; clarify.
      - clarify.
        rewrite to_ilist_app; eapply admits_app; eauto.
        econstructor; clarify.
        specialize (fresh_spec (gather_blocks m));
          rewrite gather_blocks_spec in fresh_spec.
        exploit block_allocated; eauto; clarify.
        contradiction fresh_spec; eauto.
      - clarify.
        rewrite make_simple_app in *; clarify.
        rewrite to_ilist_app; eapply admits_app; eauto.
        econstructor; eauto.
    Qed.
        
  End Instance.

  Context {ML : Memory_Layout val block_eq}.

  Lemma simple_freed : forall m b sm (Hsimple : make_simple m = Some sm)
    (Hfree : sm b = None) (Hcon : consistent m),
    (forall o v, ~can_do_op m (MRead (b, o) v)) /\ 
    (forall n, can_do_op m (MAlloc b n)) /\ ~can_do_op m (MFree b).
  Proof.
    unfold can_do_op; induction m using rev_ind; clarify.
    - repeat split; intros; apply base_allows.
    - rewrite make_simple_app in Hsimple; clarsimp.
      setoid_rewrite <- app_assoc; simpl.
      destruct (eq_dec b (block_of x)).      
      + destruct x; try (destruct p); clarify; try (destruct x1; clarify);
          try (unfold simple_update in *; clarify).
        apply free_allows; auto.
      + erewrite simple_diff_block in Hfree; eauto.
        specialize (IHm _ _ eq_refl Hfree (consistent_app _ _ Hcon)).
        repeat split; intros; rewrite loc_valid_iff; try intro; clarify;
          try (solve [destruct x; clarify]).
        * specialize (IHm1 o v); clarify.
        * destruct x; clarify; destruct p; intro; clarify.
  Qed.

  Lemma simple_allocated : forall m b sm (Hsimple : make_simple m = Some sm)
    c (Hblock : sm b = Some c) (Hcon : consistent m),
    (forall n, ~can_do_op m (MAlloc b n)) /\ can_do_op m (MFree b).
  Proof.
    unfold can_do_op; induction m using rev_ind; clarify.
    - unfold make_simple in Hsimple; clarify.
    - rewrite make_simple_app in Hsimple; clarsimp.
      setoid_rewrite <- app_assoc; simpl.
      destruct (eq_dec b (block_of x)).
      + destruct x; try (destruct p); clarify; try (destruct x1; clarify);
          try (unfold simple_update in *; clarify).
        * exploit IHm; eauto; [eapply consistent_app; eauto | intros [? ?]].
          split; intros; rewrite read_noop_single; auto.
        * exploit IHm; eauto; [eapply consistent_app; eauto | 
                               intros [Halloc ?]].
          split; intros; rewrite write_not_read_single; clarify.
          specialize (Halloc n0); intro; clarify.
        * split; apply alloc_allows; auto.
      + erewrite simple_diff_block in Hblock; eauto.
        exploit IHm; eauto; [eapply consistent_app; eauto | 
                             intros [Halloc ?]].
        repeat split; intros; rewrite loc_valid_iff; try intro; clarify;
          try (solve [destruct x; clarify]).
        specialize (Halloc n0); clarify.
  Qed.

  Lemma simple_uninit : forall m b sm (Hsimple : make_simple m = Some sm)
    c (Hblock : sm b = Some c) o (Huninit : nth_error c o = Some Uninit)
    (Hcon : consistent m) v, can_do_op m (MWrite (b, o) v).
  Proof.
    unfold can_do_op; induction m using rev_ind; clarify.
    - unfold make_simple in Hsimple; clarify.
    - rewrite make_simple_app in Hsimple; clarsimp.
      destruct (indep_dec _ (loc_of x) (Ptr (b, o))).
      + destruct (x0 b) eqn: Hblock'.
        * exploit (simple_indep_ptr x0); eauto; intros [c' [? Hnth']]; clarify.
          rewrite H in *; clarify.
          rewrite Hnth'2 in Huninit.
          exploit IHm; eauto; [eapply consistent_app; eauto | intro].
          rewrite loc_valid_iff; clarify; eauto.
        * destruct x; try (destruct p); clarify; try (destruct x1); clarify;
            unfold simple_update in *; clarify.
      + destruct x; try (destruct p); clarify; try (destruct x1); clarify;
          unfold simple_update in *; clarsimp.
        * destruct (eq_dec (b0, n0) (b, o)); clarsimp.
        * destruct (eq_dec (b0, n0) (b, o)); clarsimp.
          rewrite write_not_read_single; clarify.
          rewrite write_any_value; eauto.
        * destruct (eq_dec b0 b); clarify.
          generalize (alloc_allows m b0 n0); clarify.
          apply H1; generalize (nth_error_lt _ _ Huninit);
            rewrite replicate_length; auto.
        * destruct (eq_dec b0 b); clarify.
  Qed.

  Lemma simple_stored : forall m b sm (Hsimple : make_simple m = Some sm) 
    c (Hc : sm b = Some c) o v (Hstored : nth_error c o = Some (Stored v)) 
    (Hcon : consistent m) v',
    (can_do_op m (MRead (b, o) v') <-> v' = v) /\ 
    can_do_op m (MWrite (b, o) v').
  Proof.
    unfold can_do_op; induction m using rev_ind; clarify.
    - unfold make_simple in Hsimple; clarify.
    - rewrite make_simple_app in Hsimple; clarsimp.
      generalize (consistent_app _ _ Hcon); intro Hcon'.
      destruct (indep_dec _ (loc_of x) (Ptr (b, o))).
      + destruct (x0 b) eqn: Hblock'.
        * exploit (simple_indep_ptr x0); eauto; intros [c' [? Hnth']];
            clarsimp.
          specialize (IHm _ _ eq_refl _ Hblock' _ _ Hstored
                        (consistent_app _ _ Hcon) v').
          split; intros; rewrite loc_valid_iff; clarify.
          rewrite IHm1; split; clarify.
        * destruct x; try (destruct p); clarify; try (destruct x1); clarify;
            unfold simple_update in *; clarify.
      + destruct x; try (destruct p); clarify; try (destruct x1); clarify;
          unfold simple_update in *; clarsimp.
        * destruct (eq_dec (b0, n0) (b, o)); clarsimp.
          split; intros; rewrite read_noop_single; eapply IHm; eauto.
        * destruct (eq_dec (b0, n0) (b, o)); clarsimp.
          rewrite nth_error_replace in Hstored; clarify.
          generalize (nth_error_succeeds _ l); intros [c0 ?].
          destruct c0.
          { exploit simple_uninit; eauto; unfold can_do_op; intro.
            split; [apply read_written; auto |
              rewrite write_not_read_single; eauto; clarify]. }
          { exploit IHm; eauto; unfold can_do_op; intros [? ?].
            split; [apply read_written; auto |
              rewrite write_not_read_single; eauto; clarify]. }
        * destruct (eq_dec b0 b); clarify.
          rewrite nth_error_replicate in Hstored; clarify.
        * destruct (eq_dec b0 b); clarify.
  Qed.

  (* Another way of thinking of the simple machine: the last operation
     on a location dictates its state. *)
  Inductive last_mod_op (m : mem block val) l i : Prop :=
  | last_mod_opI : forall op (Hop1 : inth m i = Some op)
      (Hdep : ~independent (loc_of op) l) (Hmod : not_read op = true)
      (Hlast : forall j op2, inth m j = Some op2 ->
         not_read op2 = true -> ~independent (loc_of op2) l -> j <= i),
      last_mod_op m l i.
  Hint Constructors last_mod_op.

  Lemma last_mod_take : forall m l i (Hlast_mod : last_mod_op m l i)
    n (Hgt : i < n), last_mod_op (itake n m) l i.
  Proof.
    intros; inversion Hlast_mod; clarify.
    econstructor; eauto; clarsimp; rewrite itake_nth in *; clarify; eauto.
  Qed.

  Lemma last_mod_lt : forall (m : list (mem_op _ _)) l i
    (Hlast_mod : last_mod_op m l i), i < length m.
  Proof.
    intros; inversion Hlast_mod; clarsimp.
    eapply nth_error_lt; eauto.
  Qed.

  Lemma simple_last : forall m sm (Hsm : make_simple m = Some sm)
    b o i (Hlast_mod : last_mod_op m (Ptr (b, o)) i),
    match nth_error m i with
    | Some (MRead _ _) => False
    | Some (MWrite _ v) => exists c, sm b = Some c /\
                                     nth_error c o = Some (Stored v)
    | Some (MAlloc _ n) => exists c, sm b = Some c /\ length c = n /\
                        nth_error c o = if lt_dec o n then Some Uninit else None
    | Some (MFree _) => sm b = None
    | None => False
    end.
  Proof.
    induction m using rev_ind; intros; inversion Hlast_mod; clarsimp.
    rewrite make_simple_app in *; clarify.
    specialize (IHm _ Hsm1).
    rewrite nth_error_app in Hop1; destruct (lt_dec i (length m)).
    - generalize (last_mod_take Hlast_mod l); clarsimp.
      specialize (IHm _ _ _ H); clarsimp.
      specialize (Hlast (length m) x); clarsimp.
      rewrite nth_error_app in Hlast; clarsimp.
      destruct (not_read x) eqn: Hnot_read; clarify.
      destruct (indep_dec _ (loc_of x) (Ptr (b, o))); clarify; [|omega].
      destruct op; clarify.
      + exploit simple_indep_ptr; eauto; clarsimp; eauto.
      + exploit simple_indep_ptr; eauto; clarify.
        eexists; split; eauto; clarsimp.
      + destruct (sm b) eqn: Hcell; auto.
        exploit simple_indep_ptr'; eauto; clarify.
      + destruct x; clarify.
        destruct p; clarify.
        destruct x1; clarify.
    - destruct (i - length m) eqn: Hi; clarsimp.
      destruct op; clarify.
      + destruct p; clarify.
        unfold simple_update; destruct (eq_dec b b0);
          [|contradiction Hdep; intro]; clarify.
        eexists; split; eauto.
        rewrite nth_error_replace; auto; destruct (eq_dec n0 o);
          [|contradiction Hdep; intro]; clarify.
      + unfold simple_update; destruct (eq_dec b0 b); clarify.
        eexists; split; eauto.
        split; [apply replicate_length | apply nth_error_replicate].
      + unfold simple_update; destruct (eq_dec b0 b); clarify.
  Qed.

  Lemma simple_last_block : forall m sm (Hsm : make_simple m = Some sm)
    b i (Hlast_mod : last_mod_op m (Block b) i),
    match nth_error m i with
    | Some (MRead _ _) => False
    | Some (MWrite (_, o) v) => exists c, sm b = Some c /\
                                     nth_error c o = Some (Stored v)
    | Some (MAlloc _ n) => sm b = Some (replicate Uninit n)
    | Some (MFree _) => sm b = None
    | None => False
    end.
  Proof.
    induction m using rev_ind; intros; inversion Hlast_mod; clarsimp.
    rewrite make_simple_app in *; clarify.
    specialize (IHm _ Hsm1).
    rewrite nth_error_app in Hop1; destruct (lt_dec i (length m)).
    - generalize (last_mod_take Hlast_mod l); clarsimp.
      specialize (IHm _ _ H); clarsimp.
      specialize (Hlast (length m) x); clarsimp.
      rewrite nth_error_app in Hlast; clarsimp.
      destruct (not_read x) eqn: Hnot_read; clarify.
      + destruct (indep_dec _ (loc_of x) (Block b)); clarify; [|omega].
        exploit simple_diff_block; eauto.
        { instantiate (1 := b); destruct x; clarify. }
        clarsimp.
      + destruct x; clarify.
        destruct p; clarify.
        destruct x1; clarify.
    - destruct (i - length m) eqn: Hi; clarsimp.
      destruct op; clarify.
      + destruct p; clarify.
        unfold simple_update; destruct (eq_dec b b0);
          [|contradiction Hdep; intro]; clarify.
        eexists; split; eauto; rewrite nth_error_replace; clarify.
      + unfold simple_update; destruct (eq_dec b0 b); clarify; eauto.
      + unfold simple_update; destruct (eq_dec b0 b); clarify.
  Qed.

  Definition write_alloc m := forall i p v, inth m i = Some (MWrite p v) ->
    exists j, last_mod_op (itake i m) (Ptr p) j /\
              ((exists v', inth m j = Some (MWrite p v')) \/
               (exists n, inth m j = Some (MAlloc (fst p) n) /\ snd p < n)).
  
  Lemma write_alloc_nil : write_alloc inil.
  Proof.
    repeat intro.
    rewrite inth_nil in *; clarify.
  Qed.
  Hint Resolve write_alloc_nil.

  Lemma write_alloc_prefix : forall m m', write_alloc (iapp m m') ->
    write_alloc m.
  Proof.
    repeat intro.
    specialize (H i p v); rewrite iapp_nth, inth_nth_error in *.
    generalize (nth_error_lt _ _ H0); intro; destruct (lt_dec i (length m));
      [clarify | omega].
    assert (itake i (iapp m m') = itake i m).
    { rewrite iapp_take, itake_firstn.
      destruct (i - length m) eqn: Hminus; [destruct m'; clarsimp | omega]. }
    exists x; clarsimp.
    generalize (last_mod_lt _ H1).
    rewrite List.firstn_length, NPeano.Nat.min_glb_lt_iff .
    rewrite iapp_nth in *; destruct (lt_dec x (length m)); [clarsimp; eauto 
      | omega].
  Qed.

  Corollary write_alloc_app : forall m m', write_alloc (m ++ m') ->
    write_alloc m.
  Proof.
    intros; rewrite <- iapp_nil_ilist in H; rewrite <- iapp_app in H;
      eapply write_alloc_prefix; eauto.
  Qed.

  Definition read_init m := forall i p v, inth m i = Some (MRead p v) ->
    exists j v', last_mod_op (itake i m) (Ptr p) j /\
                 inth m j = Some (MWrite p v').

  Lemma read_init_nil : read_init inil.
  Proof.
    repeat intro.
    rewrite inth_nil in *; clarify.
  Qed.
  Hint Resolve read_init_nil.

  Lemma read_init_prefix : forall m m', read_init (iapp m m') ->
    read_init m.
  Proof.
    repeat intro.
    specialize (H i p v); rewrite iapp_nth, inth_nth_error in *.
    generalize (nth_error_lt _ _ H0); intro; destruct (lt_dec i (length m));
      [clarify | omega].
    assert (itake i (iapp m m') = itake i m).
    { rewrite iapp_take, itake_firstn.
      destruct (i - length m) eqn: Hminus; [destruct m'; clarsimp | omega]. }
    exists x, x0; clarsimp.
    generalize (last_mod_lt _ H1).
    rewrite List.firstn_length, NPeano.Nat.min_glb_lt_iff.
    rewrite iapp_nth in *; destruct (lt_dec x (length m)); [clarsimp | omega].
  Qed.

  Corollary read_init_app : forall m m', read_init (m ++ m') ->
    read_init m.
  Proof.
    intros; rewrite <- iapp_nil_ilist in H; rewrite <- iapp_app in H;
      eapply read_init_prefix; eauto.
  Qed.

  Lemma exists_scope : forall {A B} P (Q : A -> B -> Prop), 
    (exists x, P x /\ exists y, Q x y) -> exists x y, P x /\ Q x y.
  Proof. clarify; eauto. Qed.

  Lemma consistent_simple : forall (m : list (mem_op _ _)) (Hcon : consistent m)
    (Hread_init : read_init m) (Hwrite_alloc : write_alloc m),
    exists sm, make_simple m = Some sm.
  Proof.
    induction m using rev_ind; clarify; eauto.
    { unfold make_simple; clarify; eauto. }
    generalize (consistent_app _ _ Hcon);
      generalize (write_alloc_app _ _ Hwrite_alloc);
      generalize (read_init_app _ _ Hread_init); clarify.
    setoid_rewrite make_simple_app; clarify.
    destruct (x0 (block_of x)) as [c|] eqn: Hc.
    - exploit simple_allocated; eauto; unfold can_do_op; intros [Halloc Hfree].
      destruct x; try (destruct p); clarify; eauto.
      + specialize (Hread_init (length m) (b, n) v); clarsimp.
        rewrite nth_error_app in Hread_init; clarsimp.
        generalize (last_mod_lt _ Hread_init1); intro.
        rewrite nth_error_app in Hread_init2; clarify.
        exploit simple_last; eauto; clarsimp.
        exploit simple_stored; eauto; unfold can_do_op; intros [Hread _].
        rewrite Hread in Hcon; clarify; eauto.
      + specialize (Hwrite_alloc (length m) (b, n) v); clarsimp.
        rewrite nth_error_app in Hwrite_alloc; clarsimp.
        generalize (last_mod_lt _ Hwrite_alloc1); intro.
        rewrite nth_error_app in Hwrite_alloc2; clarify.
        exploit simple_last; eauto; destruct Hwrite_alloc2; clarsimp;
          exploit nth_error_lt; eauto; clarify; eauto.
      + specialize (Halloc n); clarify.    
    - exploit simple_freed; eauto; intros [Hread [Halloc Hfree]].
      destruct x; try (destruct p); clarify; eauto.
      + specialize (Hread n v); clarify.
      + specialize (Hwrite_alloc (length m) (b, n) v); clarsimp.
        rewrite nth_error_app in Hwrite_alloc; clarsimp.
        generalize (last_mod_lt _ Hwrite_alloc1); intro.
        rewrite nth_error_app in Hwrite_alloc2; clarify.
        exploit simple_last; eauto; destruct Hwrite_alloc2; clarsimp.
  Qed.

  Lemma simple_op : forall (m : list (mem_op _ _)) (Hcon : consistent m) op
    (Hread_init : read_init (m ++ [op]))
    (Hwrite_alloc : write_alloc (m ++ [op])),
    exists sm, make_simple m = Some sm /\ 
               (can_do_op m op <-> simple_access sm op <> None).
  Proof.
    intros; generalize (write_alloc_app _ _ Hwrite_alloc);
      generalize (read_init_app _ _ Hread_init); intros.
    exploit consistent_simple; eauto; intros [sm Hmake]; rewrite Hmake;
      eexists; split; eauto.
    split; intro Hsm.
    { exploit consistent_simple; eauto; rewrite make_simple_app; clarsimp. }
    destruct (simple_access sm op) as [sm'|] eqn: Hop; clarify; clear Hsm.
    destruct (sm (block_of op)) as [c|] eqn: Hc.
    - exploit simple_allocated; eauto; intros [Halloc Hfree].
      destruct op; try (destruct p); clarsimp.
      + destruct x0; clarify.
        exploit simple_stored; eauto; intros [Hread ?]; rewrite Hread; 
          split; clarify.
      + generalize (nth_error_succeeds _ l); clarify.
        destruct x.
        * exploit simple_uninit; eauto.
        * exploit simple_stored; eauto; clarify; eauto.
    - exploit simple_freed; eauto; intros [Hread [Halloc Hfree]].
      destruct op; try (destruct p); clarsimp.
  Qed.

  Lemma simple_ops : forall ops (m : list (mem_op _ _)) (Hcon : consistent m)
    (Hread_init : read_init (m ++ ops))
    (Hwrite_alloc : write_alloc (m ++ ops)),
    exists sm, make_simple m = Some sm /\ 
               (can_do_ops m ops <-> simple_accesses sm ops <> None).
  Proof.
    intros; generalize (write_alloc_app _ _ Hwrite_alloc);
      generalize (read_init_app _ _ Hread_init); intros.
    exploit consistent_simple; eauto; intros [sm Hmake]; rewrite Hmake;
      eexists; split; eauto.
    split; intro Hsm.
    { exploit consistent_simple; eauto; rewrite make_simple_app; clarsimp. }
    destruct (simple_accesses sm ops) as [sm'|] eqn: Hops; clarify; clear Hsm.
    unfold can_do_ops; generalize dependent m; generalize dependent sm;
      generalize dependent ops; induction ops; clarsimp.
    generalize (read_init_app (m ++ [a]) ops),
      (write_alloc_app (m ++ [a]) ops); clarsimp.
    exploit simple_op; eauto; clarsimp.
    specialize (IHops _ Hops2 (m ++ [a])); clarsimp.
    rewrite H32 in IHops; use IHops; clarify.
    rewrite make_simple_app in IHops; rewrite Hmake in IHops; clarify.
  Qed.

  Corollary simple_ops_iff : forall ops (m : list (mem_op _ _))
    (Hcon : consistent m)
    (Hread_init : read_init (m ++ ops))
    (Hwrite_alloc : write_alloc (m ++ ops))
    sm (Hsm : make_simple m = Some sm),
  can_do_ops m ops <-> simple_accesses sm ops <> None.
  Proof. intros; exploit simple_ops; eauto 2; clarsimp. Qed.
  (* For now, this only applies to finite prefixes of memory traces.
     Is this sufficient for reasoning about programs?
     If not, we should be able to define the coinductive result of applying
     infinite traces (a la simple_trace), but I may have trouble
     reasoning about it. *)

  Opaque minus.

  Definition commute_index i j :=
    if eq_dec i j then S j else if eq_dec i (S j) then j else i.

  Lemma commute_nth : forall A (l1 : list A) l2 a b i,
    inth (iapp l1 (icons a (icons b l2))) i =
    inth (iapp l1 (icons b (icons a l2))) (commute_index i (length l1)).
  Proof.
    intros; repeat rewrite iapp_nth; unfold commute_index.
    destruct (eq_dec i (length l1)); clarsimp.
    { rewrite <- minus_Sn_m; clarsimp. }
    destruct (eq_dec i (S (length l1))); clarsimp.
    { rewrite <- minus_Sn_m; clarsimp. }
    destruct (i - length l1) eqn: Hminus; [omega | clarify].
    destruct n2; [omega | clarify].
  Qed.

  Lemma commute_lt : forall i j k, i < j -> ~(i = k /\ j = S k) ->
    commute_index i k < commute_index j k.
  Proof.
    unfold commute_index; intros; destruct (eq_dec i k), (eq_dec j k),
      (eq_dec i (S k)), (eq_dec j (S k)); omega.
  Qed.

  Lemma last_mod_comm : forall m1 op1 op2 m2 n i op p
    (Hindep : independent (loc_of op1) (loc_of op2))
    (Hn : inth (iapp m1 (icons op2 (icons op1 m2))) n = Some op)
    (Hptr : loc_of op = Ptr p)
    (Hlast_mod : last_mod_op (itake (commute_index n (length m1))
       (iapp m1 (icons op1 (icons op2 m2)))) (Ptr p) i),
    last_mod_op (itake n (iapp m1 (icons op2 (icons op1 m2)))) (Ptr p)
      (commute_index i (length m1)).
  Proof.
    intros.
    inversion Hlast_mod; clarify.
    econstructor; eauto.
    - rewrite inth_nth_error, itake_nth in *; clarify.
      destruct (lt_dec (commute_index i (length m1)) n).
      + rewrite <- commute_nth; auto.
      + destruct (eq_dec i (commute_index n (length m1))); [omega|].
        clear cond; unfold commute_index in l, n0, n1.
        destruct (eq_dec i (length m1)), (eq_dec n (length m1)),
          (eq_dec i (S (length m1))), (eq_dec n (S (length m1))); clarify;
          try omega.
        rewrite iapp_nth in *; clarsimp.
    - intros.
      specialize (Hlast (commute_index j (length m1)) op3).
      rewrite inth_nth_error, itake_nth in *; clarify.
      use Hlast; clarify.
      + unfold commute_index; unfold commute_index in Hlast.
        destruct (eq_dec i (length m1)), (eq_dec j (length m1)),
          (eq_dec i (S (length m1))), (eq_dec j (S (length m1)));
          try omega.
        rewrite iapp_nth in *; clarsimp.
        rewrite <- minus_Sn_m in *; clarsimp.
        destruct (loc_of op0); clarify.
        * destruct (eq_dec p0 p); clarify.
        * destruct p.
          destruct (eq_dec b b0); clarify.
          contradiction H1.
          destruct (loc_of op3) as [(?, ?) | ?]; intro; clarify.
      + generalize (commute_lt(k := length m1) l); intro X; use X; clarify.
        * rewrite <- commute_nth; auto.
        * intros [? ?]; subst.
          rewrite iapp_nth in H, Hn; clarsimp.
          rewrite <- minus_Sn_m in Hn; clarsimp.
          destruct (loc_of op3); clarify.
  Qed.

  Lemma read_init_comm : forall m1 op1 op2 m2
    (Hread : read_init (iapp m1 (icons op1 (icons op2 m2))))
    (Hindep : independent (loc_of op1) (loc_of op2)),
    read_init (iapp m1 (icons op2 (icons op1 m2))).
  Proof.
    repeat intro.
    specialize (Hread (commute_index i (length m1)) p v);
      rewrite <- commute_nth in Hread; clarify.
    exists (commute_index x (length m1)); rewrite <- commute_nth;
      eexists; split; eauto.
    eapply last_mod_comm; eauto.
  Qed.

  Lemma read_init_comm_ops1 : forall op ops m1 m2
    (Hread : read_init (iapp m1 (icons op (iapp ops m2))))
    (Hindep : Forall (independent (loc_of op)) (map loc_of ops)),
    read_init (iapp m1 (iapp ops (icons op m2))).
  Proof.
    induction ops; clarify.
    inversion Hindep; clarify.
    generalize (read_init_comm _ _ _ _ Hread H1); intro.
    specialize (IHops (m1 ++ [a]) m2); repeat rewrite <- iapp_app in IHops;
      clarify.
  Qed.

  Lemma read_init_comm_ops : forall ops1 ops2 m1 m2
    (Hread : read_init (iapp m1 (iapp ops1 (iapp ops2 m2))))
    (Hindep : Forall (fun l => Forall (independent l) (map loc_of ops1))
                     (map loc_of ops2)),
    read_init (iapp m1 (iapp ops2 (iapp ops1 m2))).
  Proof.
    induction ops1; clarify.
    specialize (IHops1 ops2 (m1 ++ [a]) m2);
      repeat rewrite <- iapp_app in IHops1; clarify; use IHops1.
    apply read_init_comm_ops1; auto.
    - eapply Forall_impl; [|apply Hindep]; clarify.
      symmetry; inversion H; clarify.
    - eapply Forall_impl; [|apply Hindep]; clarify.
      inversion H; clarify.
  Qed.
        
  Lemma write_alloc_comm : forall m1 op1 op2 m2
    (Hwrite : write_alloc (iapp m1 (icons op1 (icons op2 m2))))
    (Hindep : independent (loc_of op1) (loc_of op2)),
    write_alloc (iapp m1 (icons op2 (icons op1 m2))).
  Proof.
    repeat intro.
    specialize (Hwrite (commute_index i (length m1)) p v);
      rewrite <- commute_nth in Hwrite; clarify.
    exists (commute_index x (length m1)); rewrite <- commute_nth; split; auto.
    eapply last_mod_comm; eauto.
  Qed.

  Definition add_index i k := if lt_dec i k then i else S i.

  Lemma add_nth : forall A (l1 : list A) l2 a i,
    inth (iapp l1 (icons a l2)) (add_index i (length l1)) =
    inth (iapp l1 l2) i.
  Proof.
    intros; repeat rewrite iapp_nth; unfold add_index.
    destruct (lt_dec i (length l1)); clarify.
    destruct (lt_dec (S i) (length l1)); [omega | clarify].
    rewrite <- minus_Sn_m; clarify; omega.
  Qed.

  Lemma add_lt : forall i j k, i < j -> add_index i k < add_index j k.
  Proof.
    unfold add_index; intros; destruct (lt_dec i k), (lt_dec j k); omega.
  Qed.

  Lemma add_index_lt' : forall k i j (Hlt : add_index i k < add_index j k),
    i < j.
  Proof.
    unfold add_index; intros; destruct (lt_dec i k), (lt_dec j k); clarify;
      omega.
  Qed.

  Definition drop_index i k := if lt_dec i k then i else i - 1.

  Lemma drop_nth : forall A (l1 : list A) l2 a i, i <> length l1 ->
    inth (iapp l1 l2) (drop_index i (length l1)) =
    inth (iapp l1 (icons a l2)) i.
  Proof.
    intros; repeat rewrite iapp_nth; unfold drop_index.
    destruct (lt_dec i (length l1)); clarify.
    destruct (lt_dec (i - 1) (length l1)); [omega | clarify].
    destruct (i - length l1) eqn: Hminus; [omega | clarify].
    assert (n1 = i - 1 - length l1) by omega; clarify.
  Qed.

  Lemma drop_lt : forall i j k, i < add_index j k -> i <> k ->
    drop_index i k < j.
  Proof.
    unfold add_index, drop_index; intros; destruct (lt_dec i k), (lt_dec j k);
      omega.
  Qed.

  Lemma last_mod_drop : forall m1 op m2 n i op' p
    (Hn : inth (iapp m1 m2) n = Some op')
    (Hptr : loc_of op' = Ptr p) (Hneq : i <> length m1)
    (Hlast_mod : last_mod_op (itake (add_index n (length m1))
                                    (iapp m1 (icons op m2))) (Ptr p) i),
    last_mod_op (itake n (iapp m1 m2)) (Ptr p) (drop_index i (length m1)).
  Proof.
    intros.
    inversion Hlast_mod; clarify.
    econstructor; eauto.
    - rewrite inth_nth_error, itake_nth in *; clarify.
      exploit drop_lt; eauto; clarify.
      erewrite drop_nth; eauto.
    - intros.
      specialize (Hlast (add_index j (length m1)) op2).
      rewrite inth_nth_error, itake_nth in *; clarify.
      exploit add_lt; eauto; instantiate (1 := length m1); clarify.
      rewrite add_nth in Hlast; clarify.
      unfold add_index in Hlast; unfold drop_index.
      destruct (lt_dec i (length m1)), (lt_dec j (length m1)); try omega.
  Qed.

  Lemma read_init_drop : forall m1 p v m2
    (Hread : read_init (iapp m1 (icons (MRead p v) m2))),
    read_init (iapp m1 m2).
  Proof.
    repeat intro.
    specialize (Hread (add_index i (length m1)) p0 v0).
    rewrite add_nth in Hread; clarify.
    assert (x <> length m1).
    { intro; subst; rewrite iapp_nth in Hread2; clarsimp. }
    exists (drop_index x (length m1)); eexists; erewrite drop_nth; auto.
    split; eauto; eapply last_mod_drop; eauto.
  Qed.    

  Lemma read_init_drop' : forall m1 op (m2 : list (mem_op _ _))
    (Hread : read_init (iapp m1 (icons op m2)))
    (Hindep : Forall (independent (loc_of op)) (map loc_of m2)),
    read_init (iapp m1 m2).
  Proof.
    repeat intro.
    rewrite iapp_nth in H.
    destruct (lt_dec i (length m1)).
    - specialize (Hread i p v).
      rewrite iapp_nth in Hread; clarify.
      rewrite iapp_take in Hread1.
      destruct (i - length m1) eqn: Hminus; [clarsimp | omega].
      generalize (last_mod_lt _ Hread1); intro.
      generalize (Min.min_spec i (length m1)); intros [? | ?];
        [clarsimp | omega].
      rewrite iapp_nth in Hread2; destruct (lt_dec x (length m1)); [|omega].
      rewrite iapp_take; clarsimp.
      exists x, x0; rewrite iapp_nth; clarify.
    - specialize (Hread (S i) p v).
      rewrite iapp_nth in Hread; destruct (lt_dec (S i) (length m1)); [omega|].
      rewrite iapp_take, firstn_length' in Hread; [|omega].
      rewrite <- minus_Sn_m in Hread; [clarify | omega].
      rewrite iapp_nth in Hread2.
      destruct (lt_dec x (length m1)).
      + exists x, x0; rewrite iapp_nth, iapp_take; clarify.
        rewrite firstn_length'; [|omega].
        inversion Hread1; clarify.
        rewrite inth_nth_error, nth_error_app in Hop1; clarify.
        econstructor; eauto.
        * rewrite inth_nth_error, nth_error_app; clarify.
        * intros.
          rewrite inth_nth_error, nth_error_app in H0.
          destruct (lt_dec j (length m1)).
          { specialize (Hlast j op2); rewrite inth_nth_error, nth_error_app
              in Hlast; clarify. }
          { specialize (Hlast (S j) op2); rewrite inth_nth_error, nth_error_app
              in Hlast.
            destruct (lt_dec (S j) (length m1)); [omega|].
            rewrite <- minus_Sn_m in Hlast; clarify; omega. }
      + destruct (x - length m1) eqn: Hminus; clarify.
        { rewrite Forall_forall in Hindep.
          rewrite inth_nth_error in H; exploit nth_error_in; eauto; intro Hin.
          specialize (Hindep (Ptr p)); rewrite in_map_iff in Hindep;
            use Hindep; [|exists (MRead p v)]; clarify. }
        generalize (last_mod_lt _ Hread1); rewrite app_length; clarify.
        rewrite itake_firstn, List.firstn_length in H0.
        rewrite inth_nth_error in H; generalize (nth_error_lt _ _ H); intro.
        generalize (Min.min_spec (i - length m1) (length m2)); intros [? | ?];
          try omega; clarsimp.
        rewrite minus_Sn_m in H0; [|omega].
        rewrite NPeano.Nat.add_sub_assoc, minus_plus in H0; [|omega].
        destruct x; clarify.
        exists x, x0; rewrite iapp_nth; destruct (lt_dec x (length m1));
          [omega|].
        rewrite <- minus_Sn_m in Hminus; [|omega].
        inversion Hminus; clarify.
        inversion Hread1.
        rewrite inth_nth_error, nth_error_app in Hop1; clarify.
        rewrite <- minus_Sn_m in Hop1; [clarify | omega].
        rewrite inth_nth_error; clarify.
        econstructor; eauto.
        * rewrite inth_nth_error, itake_nth.
          destruct (lt_dec x i); [|omega].
          rewrite iapp_nth, inth_nth_error; clarify.
          rewrite nth_error_firstn in Hop1; clarify.
        * intros.
          rewrite inth_nth_error, itake_nth in H2; clarify.
          rewrite iapp_nth in H2; destruct (lt_dec j (length m1)); [omega|].
          specialize (Hlast (S j) op2).
          rewrite inth_nth_error, nth_error_app in Hlast.
          destruct (lt_dec (S j) (length m1)); [omega|].
          rewrite <- minus_Sn_m in Hlast; [clarify | omega].
          rewrite inth_nth_error, nth_error_firstn in *.
          destruct (lt_dec (j - length m1) (i - length m1)); [clarify | omega].
          omega.
  Qed.        

  Lemma read_init_drop_ops : forall ops m1 (m2 : list (mem_op _ _))
    (Hread : read_init (iapp m1 (iapp ops m2)))
    (Hindep : Forall (fun l => Forall (independent l) (map loc_of ops))
                     (map loc_of m2)),
    read_init (iapp m1 m2).
  Proof.
    induction ops; clarify.
    specialize (IHops (m1 ++ [a]) m2); rewrite <- iapp_app in IHops; clarify.
    use IHops.
    rewrite <- iapp_app in IHops; clarify.
    generalize (read_init_drop' _ _ _ IHops); intro X; apply X.
    - eapply Forall_impl; [intros | apply Hindep].
      inversion H; symmetry; clarify.
    - eapply Forall_impl; [intros | apply Hindep].
      inversion H; clarify.
  Qed.

  Lemma write_alloc_drop : forall m1 p v m2
    (Hwrite : write_alloc (iapp m1 (icons (MRead p v) m2))),
    write_alloc (iapp m1 m2).
  Proof.
    repeat intro.
    specialize (Hwrite (add_index i (length m1)) p0 v0).
    rewrite add_nth in Hwrite; clarify.
    assert (x <> length m1).
    { intro; subst; rewrite iapp_nth in Hwrite2; clarsimp. }
    exists (drop_index x (length m1)); erewrite drop_nth; auto.
    split; eauto; eapply last_mod_drop; eauto.
  Qed.

  Lemma read_last_val : forall m (Hcon : consistent m)
    r p v (Hr : inth m r = Some (MRead p v))
    w (Hlast_mod : last_mod_op (itake r m) (Ptr p) w)
    v' (Hwrite_val : inth m w = Some (MWrite p v')),
    v' = v.
  Proof.
    intros.
    assert (w < r) as Hlt.
    { eapply lt_le_trans; [eapply last_mod_lt; eauto | apply itake_length]. }
    exploit inth_split; eauto; intros [l1 [l2 [? ?]]]; subst.
    rewrite iapp_nth in Hr; rewrite iapp_take, firstn_length' in Hlast_mod;
      clarsimp; [|omega].
    destruct (lt_dec r (length l1)); [omega|].
    destruct (r - length l1) eqn: Hminus; clarify.
    clear Hwrite_val; exploit inth_split; eauto; intros [l1' [l2' [? ?]]];
      clarify.
    clear dependent r; clear Hr.
    rewrite iapp_take, firstn_length in Hlast_mod; clarsimp.
    generalize dependent l2'; induction l1' using rev_ind; clarify.
    - generalize (consistent_prefix(m' := l1 ++ [MWrite p v']) Hcon),
        (consistent_prefix(m' := l1 ++ [MWrite p v'; MRead p v]) Hcon);
        intros Hwrite Hread; use Hread.
      rewrite read_written in Hread; auto.
      { apply Hwrite.
        rewrite <- iapp_nil_ilist; rewrite <- iapp_app; simpl.
        apply prefix_mono; repeat constructor. }
      { rewrite <- iapp_nil_ilist; rewrite <- iapp_app; simpl.
        apply prefix_mono; repeat constructor. }
    - generalize (last_mod_take Hlast_mod); intro Hlast';
        specialize (Hlast' (length l1 + S (length l1'))).
      use Hlast'; [|omega].
      rewrite itake_firstn, firstn_app in Hlast'.
      rewrite firstn_length' in Hlast'; [|omega].
      rewrite minus_plus in Hlast'; clarify.
      rewrite firstn_app in Hlast'; clarsimp.
      inversion Hlast_mod; clarify.
      specialize (Hlast (length l1 + S (length l1'))).
      rewrite inth_nth_error, nth_error_app in Hlast.
      destruct (lt_dec (length l1 + S (length l1')) (length l1)); [omega|].
      rewrite minus_plus in Hlast; clarify.
      rewrite nth_error_app in Hlast; clarsimp.
      specialize (Hlast _ eq_refl).
      rewrite <- iapp_app in Hcon; clarify.
      destruct (not_read x) eqn: Hnot_read; clarify.
      + destruct (indep_dec _ (loc_of x) (Ptr p)); clarify; [|omega].
        generalize (loc_comm (l1 ++ MWrite p v' :: l1') x (MRead p v) l2');
          clarify.
        repeat rewrite <- iapp_app in H; clarify; eauto.
      + destruct x; clarify.
        generalize (read_noop (l1 ++ MWrite p v' :: l1') p0 v0
                              (icons (MRead p v) l2')); clarify.
        rewrite <- iapp_nil_ilist in H; repeat rewrite <- iapp_app in H;
          clarify.
        rewrite H in Hcon; eauto.
        eapply consistent_prefix; eauto.
        apply prefix_mono; constructor; apply prefix_mono; repeat constructor.
  Qed.
      
  Lemma read_justified : forall m p v m'
    (Hcon : consistent (iapp m (icons (MRead p v) m')))
    (Hread : read_init (iapp m (icons (MRead p v) m'))),
    exists m1 m2, m = m1 ++ MWrite p v :: m2 /\
      Forall (fun op => op_modifies _ op p = false) m2.
  Proof.
    intros; specialize (Hread (length m) p v); rewrite iapp_nth in Hread;
      clarsimp.
    generalize (read_last_val _ Hcon (length m)); intro Hval.
    rewrite iapp_nth in Hval; clarsimp.
    specialize (Hval _ _ eq_refl _ Hread1 _ Hread2); clarify.
    rewrite iapp_take in Hread1; clarsimp.
    generalize (last_mod_lt _ Hread1); intro.
    rewrite iapp_nth in Hread2; clarify.
    exploit nth_error_split'; eauto; clarify.
    eexists; eexists; split; eauto.
    inversion Hread1; rewrite Forall_forall; clarify.
    exploit in_nth_error; eauto; intros [j [Hlt Hnth]].
    specialize (Hlast (S (length x0) + j) x);
      rewrite inth_nth_error, nth_error_app in Hlast.
    destruct (lt_dec (S (length x0) + j) (length x0)); [omega|].
    assert (S (length x0) + j - length x0 = S j) as Heq by omega;
      rewrite Heq in Hlast; clarify.
    destruct x; clarify; omega.
  Qed.

  Lemma read_consistent : forall m p v m' w
    (Hcon : consistent (iapp m m'))
    (Hlast_mod : last_mod_op m (Ptr p) w)
    (Hwrite : nth_error m w = Some (MWrite p v)),
    consistent (iapp m (icons (MRead p v) m')).
  Proof.
    induction m using rev_ind; clarsimp.
    inversion Hlast_mod; clarify.
    rewrite inth_nth_error, nth_error_app in *; clarsimp.
    destruct (lt_dec w (length m)); clarify.
    - specialize (Hlast (length m) x);
        rewrite inth_nth_error, nth_error_app in Hlast; clarsimp.
      destruct (not_read x) eqn: Hnot_read; clarify.
      + destruct (indep_dec _ (loc_of x) (Ptr p)); clarify; [|omega].
        rewrite <- iapp_app in *; simpl; apply loc_comm; [symmetry; auto|].
        eapply IHm; eauto.
        generalize (last_mod_take Hlast_mod l); clarsimp.
      + destruct x; clarify.
        rewrite read_noop.
        eapply IHm; eauto.
        * rewrite read_noop in Hcon; auto.
          eapply consistent_prefix; eauto.
          apply iapp_prefix.
        * generalize (last_mod_take Hlast_mod l); clarsimp.
        * eapply consistent_prefix; eauto.
          apply iapp_prefix.
    - destruct (w - length m) eqn: Hminus; clarsimp.
      assert (consistent (iapp ((m ++ [MWrite p v]) ++ [MRead p v]) m'));
        [|repeat rewrite <- iapp_app in *; clarify].
      rewrite read_noop; clarsimp.
      apply read_written; auto.
      eapply consistent_prefix; eauto; apply iapp_prefix.
  Qed.

  Definition last_op (m : mem block val) l op :=
    exists i, last_mod_op m l i /\ inth m i = Some op.

  Lemma last_op_unique : forall m l a b (Ha : last_op m l a)
    (Hb : last_op m l b), a = b.
  Proof.
    intros.
    destruct Ha as [i Ha], Hb as [j Hb]; clarify.
    inversion Ha1; inversion Hb1; clarsimp.
    specialize (Hlast _ _ Hb2); clarify.
    specialize (Hlast0 _ _ Ha2); clarify.
    assert (i = j) by omega; clarsimp.
  Qed.

  Corollary read_consistent_op : forall m p v m'
    (Hcon : consistent (iapp m m')) (Hlast : last_op m (Ptr p) (MWrite p v)),
    consistent (iapp m (icons (MRead p v) m')).
  Proof. intros; destruct Hlast; clarsimp; eapply read_consistent; eauto. Qed.

  Lemma indep_irrefl : forall l, ~(independent(block := block)) l l.
  Proof. destruct l; auto. Qed.
  Hint Resolve indep_irrefl.

  Lemma not_indep_trans : forall l1 l2 (p : ptr block)
    (H1 : ~independent l1 (Ptr p))(H2 : ~independent l2 (Ptr p)),
    ~independent l1 l2.
  Proof.
    destruct p, l1, l2; clarify; intro; contradiction H1; intro; clarify.
    contradiction H2; intro; clarify.
  Qed.

  Lemma read_exists : forall m p v (Hcon : consistent (m ++ [MRead p v])),
    exists i op, nth_error m i = Some op /\ ~independent (loc_of op) (Ptr p) /\
    not_read op = true.
  Proof.
    induction m using rev_ind; clarsimp.
    - exploit base_allows; clarify.
      exploit H1; eauto; clarify.
    - destruct (indep_dec _ (loc_of x) (Ptr p)).
      + rewrite loc_comm_tl in Hcon; clarify.
        exploit IHm; clarify.
        { eapply consistent_app; clarsimp; eauto. }
        exists x0, x1; clarify; rewrite nth_error_app; clarify.
        exploit nth_error_lt; eauto; clarify.
      + destruct x; try (exists (length m); eexists; rewrite nth_error_app;
                                clarsimp; fail).
        exploit (consistent_app (m ++ [MRead p0 v0])); clarsimp; eauto.
        rewrite read_noop_single in Hcon; auto.
        specialize (IHm _ _ Hcon); clarify.
        exists x, x0; clarify.
        rewrite nth_error_app; exploit nth_error_lt; eauto; clarify.
  Qed.

  Lemma last_mod_snoc : forall m op l, last_mod_op (m ++ [op]) l (length m) \/
    forall i, last_mod_op (m ++ [op]) l i <-> last_mod_op m l i.
  Proof.
    intros.
    destruct (indep_dec _ (loc_of op) l); [|destruct (not_read op) eqn: Hnr].
    - right; intro; split; intro Hlast; inversion Hlast.
      + rewrite inth_nth_error, nth_error_app in *.
        destruct (lt_dec i0 (length m)); clarify.
        econstructor; eauto; clarsimp.
        exploit nth_error_lt; eauto; intro.
        specialize (Hlast0 j op2); rewrite inth_nth_error, nth_error_app in *;
          clarify.
        { destruct (i0 - length m); clarsimp. }
      + econstructor; eauto.
        * rewrite inth_nth_error, nth_error_app in *; clarify.
          exploit nth_error_lt; eauto; clarify.
        * clarify; specialize (Hlast0 j op2).
          rewrite inth_nth_error, nth_error_app in *; clarify.
          destruct (j - length m); clarsimp.
    - left; econstructor; eauto.
      + rewrite inth_nth_error, nth_error_app; clarsimp.
      + clarify.
        rewrite inth_nth_error in *; exploit nth_error_lt; eauto; clarsimp;
          omega.
    - right; intro; split; intro Hlast; inversion Hlast.
      + rewrite inth_nth_error, nth_error_app in *.
        destruct (lt_dec i (length m)); clarify.
        econstructor; eauto; clarsimp.
        exploit nth_error_lt; eauto; intro.
        specialize (Hlast0 j op2); rewrite inth_nth_error, nth_error_app in *;
          clarify.
        { destruct (i - length m); clarsimp. }
      + econstructor; eauto.
        * rewrite inth_nth_error, nth_error_app in *; clarify.
          exploit nth_error_lt; eauto; clarify.
        * clarify; specialize (Hlast0 j op2).
          rewrite inth_nth_error, nth_error_app in *; clarify.
          destruct (j - length m); clarsimp.
  Qed.

  Lemma last_mod_iff_impl : forall m op l
    (Hiff : forall i, last_mod_op (m ++ [op]) l i <-> last_mod_op m l i),
    not_read op = false \/ independent (loc_of op) l.
  Proof.
    intros; specialize (Hiff (length m)); destruct Hiff as [H _].
    destruct (not_read op) eqn: Hnot_read; auto.
    destruct (indep_dec _ (loc_of op) l); auto; use H.
    - inversion H; rewrite inth_nth_error in *; exploit nth_error_lt; [eauto |
        omega].
    - econstructor; eauto.
      + rewrite inth_nth_error, nth_error_app; clarsimp.
      + intros; rewrite inth_nth_error in *; exploit nth_error_lt; eauto;
          clarsimp; omega.
  Qed.    

  Corollary last_mod_iff_impl' : forall m op
    (Hiff : forall i, last_mod_op (m ++ [op]) (loc_of op) i <->
                      last_mod_op m (loc_of op) i),
    not_read op = false.
  Proof.
    intros; exploit last_mod_iff_impl; clarify.
    exploit indep_irrefl; eauto; clarify.
  Qed.    

  Lemma has_last_op1 : forall (m : list (mem_op _ _)) l i op
    (Hop : nth_error m i = Some op) (Hnot_read : not_read op = true)
    (Hloc : ~independent (loc_of op) l), exists i', last_mod_op m l i'.
  Proof.
    induction m using rev_ind; clarsimp.
    generalize (last_mod_snoc m x l); intros [? | ?]; eauto.
    setoid_rewrite H.
    rewrite nth_error_app in Hop; destruct (lt_dec i (length m)); eauto.
    destruct (i - length m) eqn: Hi; clarsimp.
    exploit last_mod_iff_impl; eauto; clarify.
  Qed.    

  Lemma has_last_op : forall (m : list (mem_op _ _)) i op (Hcon : consistent m)
    (Hop : nth_error m i = Some op), exists i, last_mod_op m (loc_of op) i.
  Proof.
    induction m using rev_ind; clarsimp.
    exploit consistent_app; eauto; clarify.
    generalize (last_mod_snoc m x (loc_of op)); intros [? | Hrest]; eauto.
    setoid_rewrite Hrest.
    rewrite nth_error_app in Hop; destruct (lt_dec i (length m)); eauto.
    destruct (i - length m) eqn: Hi; clarsimp.
    exploit last_mod_iff_impl'; eauto; intro.
    destruct op; clarify.
    exploit read_exists; eauto; clarify.
    eapply has_last_op1; eauto.
  Qed.

  Corollary has_last_op' : forall m l i (op : mem_op block val)
    (Hnth : nth_error m i = Some op)
    (Hnot_read : not_read op = true) (Hdep : ~independent (loc_of op) l),
    exists op', last_op m l op'.
  Proof.
    intros; generalize (has_last_op1 _ _ _ Hnth Hnot_read Hdep); intros [x Hx].
    inversion Hx; unfold last_op; eauto.
  Qed.

  Lemma simple_no_last : forall m sm (Hsm : make_simple m = Some sm)
    l (Hlast_mod : forall i, ~last_mod_op m l i),
    sm (block_of_loc l) = None.
  Proof.
    induction m using rev_ind; clarify.
    - unfold make_simple in *; clarify.
    - rewrite make_simple_app in *; clarify.
      specialize (IHm _ Hsm1 l); use IHm.
      destruct x; clarify.
      + destruct p; clarify.
        destruct x1; clarify.
      + destruct p; unfold simple_update in *; clarify.
      + unfold simple_update; clarify.
        specialize (Hlast_mod (length m)); contradiction Hlast_mod.
        econstructor; eauto.
        * rewrite inth_nth_error, nth_error_app; clarsimp.
        * clarify.
        * clarify.
        * clarify.
          rewrite inth_nth_error in *; exploit nth_error_lt; [eauto | clarsimp;
            omega].
      + unfold simple_update; clarify.
      + intro.
        generalize (last_mod_snoc m x l); intros [? | Hrest].
        * specialize (Hlast_mod (length m)); eauto.
        * setoid_rewrite Hrest in Hlast_mod; specialize (Hlast_mod i); eauto.
  Qed.

  Corollary simple_last_op : forall (m : list (mem_op block val)) sm
    (Hsm : make_simple m = Some sm) b o a (Hlast : last_op m (Ptr (b, o)) a),
    match a with
    | MRead _ _ => False
    | MWrite _ v => exists c, sm b = Some c /\
                      nth_error c o = Some (Stored v)
    | MAlloc _ n => exists c, sm b = Some c /\ length c = n /\
                      nth_error c o = if lt_dec o n then Some Uninit else None
    | MFree _ => sm b = None
    end.
  Proof.
    unfold last_op; clarify.
    rewrite inth_nth_error in *.
    exploit (simple_last m); eauto; setoid_rewrite Hlast2; auto.
  Qed.

  Corollary simple_last_block_op : forall (m : list (mem_op block val)) sm
    (Hsm : make_simple m = Some sm) b a (Hlast : last_op m (Block b) a),
    match a with
    | MRead _ _ => False
    | MWrite (_, o) v => exists c, sm b = Some c /\
                                   nth_error c o = Some (Stored v)
    | MAlloc _ n => sm b = Some (replicate Uninit n)
    | MFree _ => sm b = None
    end.
  Proof.
    unfold last_op; clarify.
    rewrite inth_nth_error in *.
    exploit (simple_last_block m); eauto; setoid_rewrite Hlast2; auto.
  Qed.

  Corollary simple_no_last_op : forall (m : list (mem_op block val)) sm
    (Hsm : make_simple m = Some sm) l (Hlast : forall i, ~last_op m l i),
    sm (block_of_loc l) = None.
  Proof.
    unfold last_op; intros.
    exploit (simple_no_last m); eauto; repeat intro.
    inversion H; specialize (Hlast op); contradiction Hlast; eauto.
  Qed.

  Lemma last_op_dec : forall (m : list _) l (Hcon : consistent m),
    (exists op, last_op m l op) \/ (forall op, ~last_op m l op).
  Proof.
    induction m using rev_ind; unfold last_op in *.
    - right; repeat intro; clarsimp.
    - intros.
      generalize (last_mod_snoc m x l); intros [? | ?].
      + left; eexists; eexists; split; eauto.
        rewrite inth_nth_error, nth_error_app; clarsimp.
      + setoid_rewrite H.
        exploit consistent_app; eauto; intro Hcon'.
        specialize (IHm l Hcon'); destruct IHm as [IHm | IHm]; clarify.
        * left; eexists; eexists; split; eauto.
          rewrite inth_nth_error, nth_error_app in *; exploit nth_error_lt;
            [eauto | clarify; eauto].
        * right; repeat intro; clarify.
          exploit last_mod_lt; eauto; intro.
          specialize (IHm op); contradiction IHm; exists x0.
          rewrite inth_nth_error, nth_error_app in *; clarify.
  Qed.      

  (* replacement lemmas *)
  Lemma read_write_step : forall (m m' : list (mem_op _ _)) op
    (Hread : read_init (m ++ [op])) (Hread' : read_init (m' ++ [op]))
    (Hwrite : write_alloc (m ++ [op])) (Hwrite' : write_alloc (m' ++ [op]))
    (Hcon : consistent m) (Hcon' : consistent m')
    (Hlast : forall a, last_op m (loc_of op) a <-> last_op m' (loc_of op) a),
    consistent (m ++ [op]) <-> consistent (m' ++ [op]).
  Proof.
    intros; exploit (simple_op m); eauto; intros [sm [Hsm Hm]].
    exploit (simple_op m'); eauto; intros [sm' [Hsm' Hm']].
    rewrite Hm, Hm'; clear Hm Hm'.
    destruct (last_op_dec m (loc_of op)); auto.
    - destruct H as [op0 Hop0].
      assert (last_op m' (loc_of op) op0) as Hop0' by (rewrite <- Hlast; auto).
      destruct (loc_of op) eqn: Hloc; unfold last_op in *; clarify.
      + destruct p; exploit (simple_last m); eauto; exploit (simple_last m');
          eauto; intros Hop' Hop; clarsimp.
        destruct op0, op; try (inversion Hloc); unfold simple_update;
          split; clarsimp.
        * generalize (nth_error_lt _ _ Hop'2); clarify.
        * generalize (nth_error_lt _ _ Hop2); clarify.
        * generalize (nth_error_lt _ _ Hop22); clarify.
      + exploit (simple_last_block m); eauto; exploit (simple_last_block m');
          eauto; intros Hop' Hop; clarsimp.
        destruct op0, op; try (destruct p); try (inversion Hloc);
          unfold simple_update; split; clarsimp.
    - exploit (simple_no_last m); eauto.
      { intros i Hi; inversion Hi.
        specialize (H op0); contradiction H; unfold last_op; eauto. }
      intro Hb.
      setoid_rewrite Hlast in H.
      exploit (simple_no_last m'); eauto.
      { intros i Hi; inversion Hi.
        specialize (H op0); contradiction H; unfold last_op; eauto. }
      intro Hb'.
      destruct op; try (destruct p); clarsimp; split; clarify.
  Qed.

  Lemma read_init_last_app : forall (m1 m1' m2 : list _)
    (Hlast : forall l op, last_op m1 l op <-> last_op m1' l op)
    (Hread2 : read_init (m1 ++ m2)) (Hread' : read_init m1'),
    read_init (m1' ++ m2).
  Proof.
    repeat intro.
    rewrite inth_nth_error, nth_error_app in *.
    destruct (lt_dec i (length m1')).
    - specialize (Hread' i p v); rewrite inth_nth_error in Hread'; clarify.
      exists x, x0; rewrite inth_nth_error, nth_error_app in *.
      generalize (nth_error_lt _ _ Hread'2); clarify.
      rewrite to_ilist_app, iapp_take.
      destruct (i - length m1') eqn: Hminus; [autorewrite with list | omega].
      rewrite itake_firstn in *; auto.
    - specialize (Hread2 (i - length m1' + length m1) p v).
      rewrite inth_nth_error, nth_error_app in *.
      destruct (lt_dec (i - length m1' + length m1) (length m1)); [omega|].
      rewrite NPeano.Nat.add_sub in *; clarify.
      rewrite to_ilist_app, iapp_take in Hread21.
      rewrite NPeano.Nat.add_sub in *; clarify.
      rewrite inth_nth_error, nth_error_app in *.
      destruct (lt_dec x (length m1)).
      + exploit last_mod_take; eauto; intro Hlast'; clarsimp.
        rewrite firstn_firstn, Min.min_comm in *.
        generalize (Min.min_spec (i - length m1' + length m1) (length m1));
          intros [? | ?]; try omega; clarsimp.
        specialize (Hlast (Ptr p) (MWrite p x0)); unfold last_op in Hlast;
          destruct Hlast as [Hlast _]; use Hlast;
          [clarify | setoid_rewrite inth_nth_error; eauto].
        exists x1, x0; rewrite inth_nth_error, nth_error_app in *.
        generalize (nth_error_lt _ _ Hlast2); clarify.
        rewrite firstn_length' in *; try omega.
        inversion Hlast1; econstructor; eauto; clarsimp.
        * rewrite nth_error_app; clarify.
        * specialize (Hlast j op2); rewrite inth_nth_error, nth_error_app in *;
            clarify.
          generalize (last_mod_lt _ Hlast'); intro; inversion Hread21.
          specialize (Hlast0 (j - length m1' + length m1) op2);
            rewrite inth_nth_error, nth_error_app in *.
          destruct (lt_dec (j - length m1' + length m1) (length m1)); [omega|].
          rewrite NPeano.Nat.add_sub in *; clarify; omega.
      + exists (x - length m1 + length m1'), x0; rewrite inth_nth_error,
          nth_error_app.
        destruct (lt_dec (x - length m1 + length m1') (length m1')); [omega|].
        rewrite NPeano.Nat.add_sub; clarify.
        rewrite to_ilist_app, iapp_take, firstn_length', itake_firstn in *;
          try omega.
        inversion Hread21.
        rewrite iapp_nth in *; clarify.
        econstructor; eauto; clarsimp.
        * rewrite nth_error_app; clarify.
          rewrite NPeano.Nat.add_sub, nth_error_firstn in *; clarify.
        * rewrite nth_error_app in *; destruct (lt_dec j (length m1'));
            [omega|].
          specialize (Hlast0 (j - length m1' + length m1) op2);
            rewrite iapp_nth in *.
          destruct (lt_dec (j - length m1' + length m1) (length m1));
            [omega | clarsimp].
          omega.
  Qed.

  Lemma write_alloc_last_app : forall (m1 m1' m2 : list _)
    (Hlast : forall l op, last_op m1 l op <-> last_op m1' l op)
    (Hwrite2 : write_alloc (m1 ++ m2)) (Hwrite' : write_alloc m1'),
    write_alloc (m1' ++ m2).
  Proof.
    repeat intro.
    rewrite inth_nth_error, nth_error_app in *.
    destruct (lt_dec i (length m1')).
    - specialize (Hwrite' i p v); rewrite inth_nth_error in Hwrite'; clarify.
      exists x; rewrite inth_nth_error, nth_error_app in *.
      assert (x < length m1')
        by (destruct Hwrite'2; clarify; eapply nth_error_lt; eauto).
      rewrite to_ilist_app, iapp_take.
      destruct (i - length m1') eqn: Hminus; [autorewrite with list | omega].
      rewrite itake_firstn in *; clarify.
    - specialize (Hwrite2 (i - length m1' + length m1) p v).
      rewrite inth_nth_error, nth_error_app in *.
      destruct (lt_dec (i - length m1' + length m1) (length m1)); [omega|].
      rewrite NPeano.Nat.add_sub in *; clarify.
      rewrite to_ilist_app, iapp_take in Hwrite21.
      rewrite NPeano.Nat.add_sub in *; clarify.
      rewrite inth_nth_error, nth_error_app in *.
      destruct (lt_dec x (length m1)).
      + exploit last_mod_take; eauto; intro Hlast'; clarsimp.
        rewrite firstn_firstn, Min.min_comm in *.
        generalize (Min.min_spec (i - length m1' + length m1) (length m1));
          intros [? | ?]; try omega; clarsimp.
        assert (exists op, nth_error m1 x = Some op) as [op Hop]
          by (destruct Hwrite22; clarify; eauto).
        specialize (Hlast (Ptr p) op); unfold last_op in Hlast;
          destruct Hlast as [Hlast _]; use Hlast;
          [clarify | setoid_rewrite inth_nth_error; eauto].
        exists x0; rewrite inth_nth_error, nth_error_app in *.
        generalize (nth_error_lt _ _ Hlast2); clarify.
        rewrite firstn_length' in *; try omega.
        split; [inversion Hlast1; econstructor; eauto; clarsimp|].
        * rewrite nth_error_app; clarify.
        * specialize (Hlast j op2); rewrite inth_nth_error, nth_error_app in *;
            clarify.
          generalize (last_mod_lt _ Hlast'); intro; inversion Hwrite21.
          specialize (Hlast0 (j - length m1' + length m1) op2);
            rewrite inth_nth_error, nth_error_app in *.
          destruct (lt_dec (j - length m1' + length m1) (length m1)); [omega|].
          rewrite NPeano.Nat.add_sub in *; clarify; omega.
        * destruct Hwrite22; clarsimp; eauto.
      + exists (x - length m1 + length m1'); rewrite inth_nth_error,
          nth_error_app.
        destruct (lt_dec (x - length m1 + length m1') (length m1')); [omega|].
        rewrite NPeano.Nat.add_sub; clarify.
        rewrite to_ilist_app, iapp_take, firstn_length', itake_firstn in *;
          try omega.
        inversion Hwrite21.
        rewrite iapp_nth in *; clarify.
        econstructor; eauto; clarsimp.
        * rewrite nth_error_app; clarify.
          rewrite NPeano.Nat.add_sub, nth_error_firstn in *; clarify.
        * rewrite nth_error_app in *; destruct (lt_dec j (length m1'));
            [omega|].
          specialize (Hlast0 (j - length m1' + length m1) op2);
            rewrite iapp_nth in *.
          destruct (lt_dec (j - length m1' + length m1) (length m1));
            [omega | clarsimp].
          omega.
  Qed.

  Lemma last_ext : forall (m2 m1 m1' : list (mem_op _ _))
    (Hcon : consistent (m1 ++ m2)) (Hcon' : consistent m1')
    (Hlast : forall l op, last_op m1 l op <-> last_op m1' l op)
    (Hread_init : read_init (m1 ++ m2)) (Hwrite_alloc : write_alloc (m1 ++ m2))
    (Hread_init' : read_init m1') (Hwrite_alloc' : write_alloc m1'),
    consistent (m1' ++ m2).
  Proof.
    induction m2 using rev_ind; clarsimp.
    exploit IHm2; eauto.
    { eapply consistent_app; eauto; clarsimp; eauto. }
    { eapply read_init_app; eauto; clarsimp; eauto. }
    { eapply write_alloc_app; eauto; clarsimp; eauto. }
    intro.
    rewrite app_assoc in *; rewrite <- read_write_step; eauto.
    - rewrite <- app_assoc in *; eapply read_init_last_app; eauto.
    - rewrite <- app_assoc in *; eapply write_alloc_last_app; eauto.
    - eapply consistent_app; eauto.
    - intros.
      specialize (Hlast (loc_of x) a).
      split; unfold last_op in *; intro Hlast_op; clarify.
      + rewrite inth_nth_error, nth_error_app in *; clarify.
        destruct (lt_dec x0 (length m1)).
        * exploit last_mod_take; eauto; clarsimp.
          destruct Hlast as [Hlast _]; use Hlast;
            [clarify | setoid_rewrite inth_nth_error; eauto].
          generalize (last_mod_lt _ Hlast1); intro.
          assert (inth (m1' ++ m2) x1 = Some a)
            by (rewrite inth_nth_error, nth_error_app in *; clarify).
          exists x1; clarify.
          inversion Hlast1.
          assert (op = a)
            by (rewrite inth_nth_error, nth_error_app in *; clarsimp); subst.
          econstructor; eauto; intros.
          inversion Hlast_op1; rewrite inth_nth_error, nth_error_app in *;
            clarify.
          destruct (lt_dec j (length m1')).
          { specialize (Hlast j op2); rewrite inth_nth_error in *; clarify. }
          { specialize (Hlast0 (j - length m1' + length m1) op2);
              rewrite inth_nth_error, nth_error_app in *.
            destruct (lt_dec (j - length m1' + length m1) (length m1));
              [omega|].
            rewrite NPeano.Nat.add_sub in *; clarify; omega. }
        * assert (inth (m1' ++ m2) (x0 - length m1 + length m1') = Some a).
          { rewrite inth_nth_error, nth_error_app.
            destruct (lt_dec (x0 - length m1 + length m1') (length m1'));
              [omega|].
            rewrite NPeano.Nat.add_sub; auto. }
          exists (x0 - length m1 + length m1'); clarify.
          inversion Hlast_op1.
          assert (op = a)
            by (rewrite inth_nth_error, nth_error_app in *; clarsimp); subst.
          econstructor; eauto; intros.
          rewrite inth_nth_error, nth_error_app in *.
          destruct (lt_dec j (length m1')); [omega|].
          specialize (Hlast0 (j - length m1' + length m1) op2);
            rewrite inth_nth_error, nth_error_app in *.
          destruct (lt_dec (j - length m1' + length m1) (length m1));
            [omega|].
          rewrite NPeano.Nat.add_sub in *; clarify; omega.
      + rewrite inth_nth_error, nth_error_app in *; clarify.
        destruct (lt_dec x0 (length m1')).
        * exploit last_mod_take; eauto; clarsimp.
          destruct Hlast as [_ Hlast]; use Hlast;
            [clarify | setoid_rewrite inth_nth_error; eauto].
          generalize (last_mod_lt _ Hlast1); intro.
          assert (inth (m1 ++ m2) x1 = Some a)
            by (rewrite inth_nth_error, nth_error_app in *; clarify).
          exists x1; clarify.
          inversion Hlast1.
          assert (op = a)
            by (rewrite inth_nth_error, nth_error_app in *; clarsimp); subst.
          econstructor; eauto; intros.
          inversion Hlast_op1; rewrite inth_nth_error, nth_error_app in *;
            clarify.
          destruct (lt_dec j (length m1)).
          { specialize (Hlast j op2); rewrite inth_nth_error in *; clarify. }
          { specialize (Hlast0 (j - length m1 + length m1') op2);
              rewrite inth_nth_error, nth_error_app in *.
            destruct (lt_dec (j - length m1 + length m1') (length m1'));
              [omega|].
            rewrite NPeano.Nat.add_sub in *; clarify; omega. }
        * assert (inth (m1 ++ m2) (x0 - length m1' + length m1) = Some a).
          { rewrite inth_nth_error, nth_error_app.
            destruct (lt_dec (x0 - length m1' + length m1) (length m1));
              [omega|].
            rewrite NPeano.Nat.add_sub; auto. }
          exists (x0 - length m1' + length m1); clarify.
          inversion Hlast_op1.
          assert (op = a)
            by (rewrite inth_nth_error, nth_error_app in *; clarsimp); subst.
          econstructor; eauto; intros.
          rewrite inth_nth_error, nth_error_app in *.
          destruct (lt_dec j (length m1)); [omega|].
          specialize (Hlast0 (j - length m1 + length m1') op2);
            rewrite inth_nth_error, nth_error_app in *.
          destruct (lt_dec (j - length m1 + length m1') (length m1'));
            [omega|].
          rewrite NPeano.Nat.add_sub in *; clarify; omega.
  Qed.

  Definition proj_block (m : list (mem_op block val)) b :=
    filter (fun c => beq (block_of c) b) m.

  Lemma read_init_proj : forall (m : list _) (Hread : read_init m) b,
    read_init (proj_block m b).
  Proof.
    unfold proj_block; repeat intro.
    rewrite inth_nth_error in *; exploit nth_error_in; eauto; rewrite filter_In;
      unfold beq at 1; destruct p as (?, o); clarify.
    exploit nth_filter_split; eauto; intros [l1 [l2 [? Hfilter]]]; clarify.
    specialize (Hread (length l1) (b, o) v);
      rewrite inth_nth_error, nth_error_app, lt_dec_eq, minus_diag in *;
      clarify.
    generalize (last_mod_lt _ Hread1); intro Hlt; autorewrite with list in Hlt.
    rewrite minus_diag in Hlt; clarify; rewrite plus_0_r in Hlt.
    rewrite inth_nth_error, nth_error_app in Hread2; clarify.
    generalize (nth_error_split' _ _ Hread2); intros [l1' [l2' ?]]; clarsimp.
    exists (length (proj_block l1' b)), x0; unfold proj_block.
    rewrite inth_nth_error, filter_app, nth_error_app, app_length; clarify.
    rewrite lt_dec_plus_l, nth_error_app, lt_dec_eq, minus_diag; clarify.
    inversion Hread1; econstructor; eauto; clarsimp.
    - rewrite nth_error_app in *; clarsimp.
      exploit (Min.min_r (length l1' + S (length l2')) (length l1'));
        [omega | intro Hmin; rewrite Hmin in *; clarsimp].
    - rewrite nth_error_app in *.
      destruct (lt_dec j (length (filter (fun op => beq (block_of op) b) l1')));
        [omega|].
      destruct (j - length (filter (fun op => beq (block_of op) b) l1'))
        eqn: Hminus; [omega | clarify].
      exploit nth_filter_split; eauto; intros [m1 [m2 ?]]; clarify.
      rewrite firstn_length' in Hlast; [|omega].
      specialize (Hlast (length l1' + S (length m1)) op2); clarsimp.
      rewrite nth_error_app, lt_dec_plus_r, minus_plus in Hlast; clarify.
      rewrite nth_error_split in Hlast; clarify; omega.
  Qed.
    
  Lemma write_alloc_proj : forall (m : list _) (Hwrite : write_alloc m) b,
    write_alloc (proj_block m b).
  Proof.
    unfold proj_block; repeat intro.
    rewrite inth_nth_error in *; exploit nth_error_in; eauto; rewrite filter_In;
      unfold beq at 1; destruct p as (?, o); clarify.
    exploit nth_filter_split; eauto; intros [l1 [l2 [? Hfilter]]]; clarify.
    specialize (Hwrite (length l1) (b, o) v);
      rewrite inth_nth_error, nth_error_app, lt_dec_eq, minus_diag in *;
      clarify.
    generalize (last_mod_lt _ Hwrite1); intro Hlt; autorewrite with list in Hlt.
    rewrite minus_diag in Hlt; clarify; rewrite plus_0_r in Hlt.
    rewrite inth_nth_error, nth_error_app in Hwrite2; clarify.
    assert (exists a, nth_error l1 x = Some a /\ block_of a = b) as [a [Ha ?]] 
      by (destruct Hwrite2; clarify; eauto).
    generalize (nth_error_split' _ _ Ha); intros [l1' [l2' ?]]; clarsimp.
    exists (length (proj_block l1' (block_of a))); unfold proj_block.
    rewrite inth_nth_error, filter_app, nth_error_app, app_length; clarify.
    rewrite lt_dec_plus_l, nth_error_app, lt_dec_eq, minus_diag; clarify.
    inversion Hwrite1; econstructor; eauto; clarsimp.
    - rewrite nth_error_app in *; clarsimp.
      exploit (Min.min_r (length l1' + S (length l2')) (length l1'));
        [omega | intro Hmin; rewrite Hmin in *].
      rewrite lt_dec_eq, minus_diag in Hop1; clarify.
      rewrite H0; auto.
    - rewrite nth_error_app in *.
      destruct (lt_dec j (length (filter (fun op => beq (block_of op)
        (block_of a)) l1'))); [omega|].
      destruct (j - length (filter (fun op => beq (block_of op) (block_of a))
        l1')) eqn: Hminus; [omega | clarify].
      exploit nth_filter_split; eauto; intros [m1 [m2 ?]]; clarify.
      rewrite firstn_length' in Hlast; [|omega].
      specialize (Hlast (length l1' + S (length m1)) op2).
      rewrite inth_nth_error, nth_error_app, lt_dec_plus_r, minus_plus in Hlast;
        clarify.
      rewrite nth_error_split in Hlast; clarify; omega.
  Qed.

  Lemma proj_block_app : forall m1 m2 b, proj_block (m1 ++ m2) b =
    proj_block m1 b ++ proj_block m2 b.
  Proof. unfold proj_block; intros; apply filter_app. Qed.

  Lemma proj_idem : forall (m : list _) b,
    proj_block (proj_block m b) b = proj_block m b.
  Proof.
    intros; unfold proj_block; apply filter_idem.
  Qed.

  Lemma last_op_proj : forall (m : list _) l b,
    last_op m l b <-> last_op (proj_block m (block_of_loc l)) l b.
  Proof.
    intros.
    unfold last_op; split; intros [i [Hlast Hnth]];
      rewrite inth_nth_error in *; setoid_rewrite inth_nth_error.
    - exploit nth_error_split'; eauto; intros [l1 [l2 [? Heq]]]; clarify.
      inversion Hlast; clarsimp.
      generalize (dep_block _ _ _ Hdep); repeat rewrite block_of_loc_spec;
        intro.
      exists (length (proj_block l1 (block_of_loc l)));
        rewrite proj_block_app, nth_error_app; clarsimp.
      econstructor; eauto.
      + rewrite inth_nth_error, nth_error_app; clarsimp.
      + intros; rewrite inth_nth_error, nth_error_app in *.
        destruct (lt_dec j (length (proj_block l1 (block_of_loc l)))); [omega|].
        destruct (j - (length (proj_block l1 (block_of_loc l)))) eqn: Hminus;
          [omega | clarify].
        unfold proj_block in *; exploit nth_filter_split; eauto;
          intros [l1' [l2' ?]]; clarify.
        specialize (Hlast0 (length l1 + S (length l1')) op2);
          rewrite inth_nth_error, nth_error_app in Hlast0.
        destruct (lt_dec (length l1 + S (length l1')) (length l1));
          [omega|].
        rewrite minus_plus in Hlast0; clarify.
        rewrite nth_error_split in Hlast0; clarify; omega.
    - unfold proj_block in Hnth; exploit nth_filter_split; eauto;
        intros [l1 [l2 [Heq' ?]]]; clarify.
      exists (length l1); rewrite nth_error_app; clarsimp.
      inversion Hlast; econstructor; eauto.
      + rewrite inth_nth_error, nth_error_app; clarsimp.
      + intros; rewrite inth_nth_error, nth_error_app in *.
        destruct (lt_dec j (length l1)); [omega|].
        destruct (j - length l1) eqn: Hminus; [omega | clarify].
        exploit nth_error_split'; eauto; intros [l1' [l2' ?]]; clarify.
        specialize (Hlast0 (length (proj_block l1 (block_of_loc l)) +
          S (length (proj_block l1' (block_of_loc l)))) op2);
          rewrite inth_nth_error, nth_error_app, filter_app in Hlast0.
        unfold proj_block in *; rewrite lt_dec_plus_r, minus_plus in Hlast0;
          clarify.
        rewrite nth_error_app, lt_dec_eq, minus_diag in Hlast0.
        generalize (dep_block _ _ _ H1); repeat rewrite block_of_loc_spec;
          intro Hblock; rewrite Hblock in *; clarify; omega.
  Qed.

  Corollary last_proj : forall (m : list _) (a : mem_op _ val) b,
    last_op m (loc_of a) b <-> last_op (proj_block m (block_of a)) (loc_of a) b.
  Proof. intros; repeat rewrite <- block_of_loc_spec; apply last_op_proj. Qed.

  Lemma consistent_proj_snoc : forall (m : list _) a
    (Hread : read_init (m ++ [a])) (Hwrite : write_alloc (m ++ [a])),
    consistent (m ++ [a]) <->
    (consistent m /\ consistent (proj_block m (block_of a) ++ [a])).
  Proof.
    induction m using rev_ind; clarsimp.
    { split; clarify; apply consistent_nil; apply (block_of a). }
    generalize (read_write_step (m ++ [x])); intro Hiff.
    setoid_rewrite <- app_assoc in Hiff; simpl in Hiff.
    destruct (eq_dec (block_of x) (block_of a)); [split; intro Hcon|].
    - generalize (consistent_app (m ++ [x]) [a]); rewrite <- app_assoc;
        clarify.
      rewrite <- Hiff; auto.
      + unfold proj_block; generalize (read_init_proj _ Hread); intro Hread'.
        specialize (Hread' (block_of a)); unfold proj_block in Hread';
          rewrite filter_app in *; clarify.
        rewrite <- app_assoc; destruct (beq (block_of x) (block_of a)); auto.
      + unfold proj_block; generalize (write_alloc_proj _ Hwrite);
          intro Hwrite'.
        specialize (Hwrite' (block_of a)); unfold proj_block in Hwrite';
          rewrite filter_app in *; clarify.
        rewrite <- app_assoc; destruct (beq (block_of x) (block_of a)); auto.
      + rewrite IHm in H; clarify.
        unfold proj_block, beq in *; rewrite filter_app, e in *; clarify.
        { eapply read_init_app; rewrite <- app_assoc; simpl; eauto. }
        { eapply write_alloc_app; rewrite <- app_assoc; simpl; eauto. }
      + apply last_proj.
    - clarify; rewrite <- Hiff in Hcon2; auto.
      + unfold proj_block; generalize (read_init_proj _ Hread); intro Hread'.
        specialize (Hread' (block_of a)); unfold proj_block in Hread';
          rewrite filter_app in *; clarify.
        rewrite <- app_assoc; destruct (beq (block_of x) (block_of a)); auto.
      + unfold proj_block; generalize (write_alloc_proj _ Hwrite);
          intro Hwrite'.
        specialize (Hwrite' (block_of a)); unfold proj_block in Hwrite';
          rewrite filter_app in *; clarify.
        rewrite <- app_assoc; destruct (beq (block_of x) (block_of a)); auto.
      + eapply consistent_app; eauto.
      + apply last_proj.
    - repeat rewrite <- block_of_loc_spec in n; generalize (block_indep _ _ n);
        intro.
      rewrite loc_valid_iff; auto.
      rewrite (IHm a).
      + repeat rewrite block_of_loc_spec in n.
        unfold proj_block, beq; rewrite filter_app; split; clarsimp.
        eapply consistent_app; eauto.
      + rewrite to_ilist_app in Hread; clarify.
        generalize (read_init_comm _ _ _ _ Hread); clarify.
        eapply read_init_prefix; rewrite <- iapp_app; simpl; eauto.
      + rewrite to_ilist_app in Hwrite; clarify.
        generalize (write_alloc_comm _ _ _ _ Hwrite); clarify.
        eapply write_alloc_prefix; rewrite <- iapp_app; simpl; eauto.
  Qed.

  Definition exclude_block (m : list (mem_op block val)) b :=
    filter (fun c => negb (beq (block_of c) b)) m.

  Lemma exclude_block_app : forall m1 m2 b, exclude_block (m1 ++ m2) b =
    exclude_block m1 b ++ exclude_block m2 b.
  Proof. unfold exclude_block; intros; apply filter_app. Qed.

  Lemma consistent_b : forall b a (m1 m2 m3 : list _)
    (Hcon : consistent (m1 ++ m2 ++ a :: m3)) (Hb : block_of a = b)
    (Hnot : Forall (fun a => ~block_of a = b) m2),
    consistent (m1 ++ a :: m2 ++ m3).
  Proof.
    intros.
    rewrite to_ilist_app in *; simpl; rewrite to_ilist_app in *.
    rewrite loc_comm_ops1; auto.
    rewrite Forall_forall in *; intros x Hin.
    rewrite in_map_iff in Hin; clarify.
    specialize (Hnot _ Hin2).
    apply block_indep; repeat rewrite block_of_loc_spec; auto.
  Qed.

  Lemma loc_split : forall f (ops m1 m2 m3 : list _)
    (Hcon : consistent (m1 ++ ops ++ m2 ++ m3))
    ops1 ops2 (Hpart : partition f ops = (ops1, ops2))
    (Hindep : Forall (fun c => Forall (fun c' =>
      independent (loc_of c') (loc_of c)) m2 /\
      Forall (fun c' => independent (loc_of c') (loc_of c)) ops1) ops2),
    consistent (m1 ++ ops1 ++ m2 ++ ops2 ++ m3).
  Proof.
    setoid_rewrite partition_filter.
    induction ops using rev_ind; clarify.
    repeat rewrite filter_app in *; clarify.
    rewrite Forall_app in *; clarify.
    destruct (f x) eqn: Hx; clarify.
    - specialize (IHops m1 (x :: m2) m3); clarsimp.
      apply IHops; auto.
      rewrite Forall_forall in *; intros ? Hin.
      specialize (Hindep1 _ Hin); rewrite Forall_app in *; clarify.
      inversion Hindep122; clarify.
    - specialize (IHops m1 m2 (x :: m3)); clarsimp.
      apply IHops; auto.
      rewrite app_assoc, to_ilist_app in H; simpl in H;
        rewrite to_ilist_app, loc_comm_ops1 in H.
      rewrite app_assoc; repeat rewrite to_ilist_app; auto.
      { inversion Hindep2; clarify.
        rewrite Forall_forall in *; intros ? Hin.
        symmetry; rewrite in_map_iff in Hin; clarify. }
  Qed.

  Corollary consistent_proj : forall b (m : list _) (Hcon : consistent m),
    consistent (proj_block m b).
  Proof.
    intros.
    generalize (loc_split(m2 := []) (fun c => beq (block_of c) b) m [] []);
      setoid_rewrite partition_filter; clarsimp.
    specialize (H _ _ eq_refl); clarify.
    use H; [eapply consistent_app; eauto|].
    rewrite Forall_forall; clarify.
    rewrite Forall_forall; clarify.
    rewrite filter_In in *; unfold negb, beq in *; clarify.
    apply block_indep; repeat rewrite block_of_loc_spec; auto.
  Qed.

  Lemma consistent_proj_ops : forall ops (m : list _) b
    (Hb : Forall (fun op => block_of op = b) ops)
    (Hread : read_init (m ++ ops)) (Hwrite : write_alloc (m ++ ops)),
    consistent (m ++ ops) <->
    (consistent m /\ consistent (proj_block m b ++ ops)).
  Proof.
    induction ops; clarsimp.
    - split; clarify; apply consistent_proj; auto.
    - specialize (IHops (m ++ [a]) b); rewrite <- app_assoc in IHops; clarify.
      inversion Hb; clarify.
      rewrite IHops; auto.
      rewrite proj_block_app; unfold proj_block at 2; clarify.
      rewrite <- app_assoc; split; clarify.
      + eapply consistent_app; eauto.
      + rewrite consistent_proj_snoc; clarify.
        * eapply consistent_app; rewrite <- app_assoc; simpl; eauto.
        * eapply read_init_app; rewrite <- app_assoc; simpl; eauto.
        * eapply write_alloc_app; rewrite <- app_assoc; simpl; eauto.
  Qed.

  Lemma proj_exclude : forall m b b' (Hdiff : b <> b'),
    proj_block (exclude_block m b) b' = proj_block m b'.
  Proof.
    intros; unfold proj_block, exclude_block; apply filter_filter_1.
    rewrite Forall_forall; unfold implb, negb, beq; clarify.
  Qed.

  Lemma read_init_exclude : forall (m : list _) (Hread : read_init m) b,
    read_init (exclude_block m b).
  Proof.
    unfold exclude_block; repeat intro.
    rewrite inth_nth_error in *; exploit nth_error_in; eauto; rewrite filter_In;
      unfold beq at 1; destruct p as (b', o); clarify.
    exploit nth_filter_split; eauto; intros [l1 [l2 [? Hfilter]]]; clarify.
    specialize (Hread (length l1) (b', o) v);
      rewrite inth_nth_error, nth_error_app, lt_dec_eq, minus_diag in *;
      clarify.
    generalize (last_mod_lt _ Hread1); intro Hlt; autorewrite with list in Hlt.
    rewrite minus_diag in Hlt; clarify; rewrite plus_0_r in Hlt.
    rewrite inth_nth_error, nth_error_app in Hread2; clarify.
    generalize (nth_error_split' _ _ Hread2); intros [l1' [l2' ?]]; clarsimp.
    exists (length (exclude_block l1' b)), x0; unfold exclude_block.
    rewrite inth_nth_error, filter_app, nth_error_app, app_length; clarify.
    destruct (negb (beq b' b)) eqn: Hdiff; [|unfold negb, beq in Hdiff];
      clarify.
    rewrite lt_dec_plus_l, nth_error_app, lt_dec_eq, minus_diag; clarify.
    inversion Hread1; econstructor; eauto; clarsimp.
    - rewrite nth_error_app in *; clarsimp.
      exploit (Min.min_r (length l1' + S (length l2')) (length l1'));
        [omega | intro Hmin; rewrite Hmin in *; timeout 10 clarsimp].
    - rewrite nth_error_app in *.
      destruct (lt_dec j (length (filter (fun c => negb (beq (block_of c) b))
        l1'))); [omega|].
      destruct (j - length (filter (fun c => negb (beq (block_of c) b)) l1'))
        eqn: Hminus; [omega | clarify].
      exploit nth_filter_split; eauto; intros [m1 [m2 ?]]; clarify.
      rewrite firstn_length' in Hlast; [|omega].
      specialize (Hlast (length l1' + S (length m1)) op2).
      rewrite inth_nth_error, nth_error_app, lt_dec_plus_r, minus_plus in Hlast;
        clarify.
      rewrite nth_error_split in Hlast; clarify; omega.
  Qed.

  Lemma write_alloc_exclude : forall (m : list _) (Hwrite : write_alloc m) b,
    write_alloc (exclude_block m b).
  Proof.
    unfold exclude_block; repeat intro.
    rewrite inth_nth_error in *; exploit nth_error_in; eauto; rewrite filter_In;
      unfold beq at 1; destruct p as (b', o); clarify.
    exploit nth_filter_split; eauto; intros [l1 [l2 [? Hfilter]]]; clarify.
    specialize (Hwrite (length l1) (b', o) v);
      rewrite inth_nth_error, nth_error_app, lt_dec_eq, minus_diag in *;
      clarify.
    generalize (last_mod_lt _ Hwrite1); intro Hlt; autorewrite with list in Hlt.
    rewrite minus_diag in Hlt; clarify; rewrite plus_0_r in Hlt.
    rewrite inth_nth_error, nth_error_app in Hwrite2; clarify.
    assert (exists a, nth_error l1 x = Some a /\ block_of a = b') as [a [Ha ?]] 
      by (destruct Hwrite2; clarify; eauto).
    generalize (nth_error_split' _ _ Ha); intros [l1' [l2' ?]]; clarsimp.
    exists (length (exclude_block l1' b)); unfold exclude_block.
    rewrite inth_nth_error, filter_app, nth_error_app, app_length; clarify.
    destruct (negb (beq (block_of a) b)) eqn: Hdiff;
      [|unfold negb, beq in Hdiff]; clarify.
    rewrite lt_dec_plus_l, nth_error_app, lt_dec_eq, minus_diag; clarify.
    inversion Hwrite1; econstructor; eauto; clarsimp.
    - rewrite nth_error_app in *; clarsimp.
      exploit (Min.min_r (length l1' + S (length l2')) (length l1'));
        [omega | intro Hmin; rewrite Hmin in *].
      rewrite lt_dec_eq, minus_diag in Hop1; clarify.
      rewrite H0; auto.
    - rewrite nth_error_app in *.
      destruct (lt_dec j (length (filter (fun op => negb (beq (block_of op) b))
                                         l1'))); [omega|].
      destruct (j - length (filter (fun op => (negb (beq (block_of op) b)))
        l1')) eqn: Hminus; [omega | clarify].
      exploit nth_filter_split; eauto; intros [m1 [m2 ?]]; clarify.
      rewrite firstn_length' in Hlast; [|omega].
      specialize (Hlast (length l1' + S (length m1)) op2).
      rewrite inth_nth_error, nth_error_app, lt_dec_plus_r, minus_plus in Hlast;
        clarify.
      rewrite nth_error_split in Hlast; clarify; omega.
  Qed.

  Lemma consistent_exclude : forall (m : list _) b (Hcon : consistent m)
    (Hread : read_init m) (Hwrite : write_alloc m),
    consistent (exclude_block m b).
  Proof.
    induction m using rev_ind; clarify.
    generalize (read_init_exclude _ Hread b), (write_alloc_exclude _ Hwrite b);
      intros.
    rewrite exclude_block_app in *; clarify.
    generalize (consistent_app _ _ Hcon), (read_init_app _ _ Hread),
      (write_alloc_app _ _ Hwrite); specialize (IHm b); clarify.
    destruct (negb (beq (block_of x) b)) eqn: Hblock; clarsimp.
    unfold negb, beq in Hblock; clarify.
    rewrite consistent_proj_snoc; clarify.
    rewrite proj_exclude; clarify.
    generalize (consistent_proj (block_of x) _ Hcon); clarify.
    rewrite proj_block_app in *; unfold proj_block, beq in *; clarsimp.
  Qed.

  Lemma last_exclude : forall (m : list (mem_op block val)) l op b
                              (Hdiff : block_of_loc l <> b),
    last_op m l op <-> last_op (exclude_block m b) l op.
  Proof.
    intros.
    unfold last_op; split; intros [i [Hlast Hnth]];
      rewrite inth_nth_error in *; setoid_rewrite inth_nth_error.
    - exploit nth_error_split'; eauto; intros [l1 [l2 [? Heq]]]; clarify.
      inversion Hlast; clarsimp.
      generalize (dep_block _ _ _ Hdep); repeat rewrite block_of_loc_spec;
        intro.
      exists (length (exclude_block l1 b));
        rewrite exclude_block_app, nth_error_app; clarsimp.
      unfold negb, beq; destruct (eq_dec (block_of_loc l) b); clarify.
      econstructor; eauto.
      + rewrite inth_nth_error, nth_error_app; clarsimp.
      + intros; rewrite inth_nth_error, nth_error_app in *.
        destruct (lt_dec j (length (exclude_block l1 b))); [omega|].
        destruct (j - (length (exclude_block l1 b))) eqn: Hminus;
          [omega | clarify].
        unfold exclude_block in *; exploit nth_filter_split; eauto;
          intros [l1' [l2' ?]]; clarify.
        specialize (Hlast0 (length l1 + S (length l1')) op2);
          rewrite inth_nth_error, nth_error_app in Hlast0.
        destruct (lt_dec (length l1 + S (length l1')) (length l1));
          [omega|].
        rewrite minus_plus in Hlast0; clarify.
        rewrite nth_error_split in Hlast0; clarify; omega.
    - unfold exclude_block in Hnth; exploit nth_filter_split; eauto;
        intros [l1 [l2 [Heq' ?]]]; clarify.
      exists (length l1); rewrite nth_error_app; clarsimp.
      inversion Hlast; econstructor; eauto.
      + rewrite inth_nth_error, nth_error_app; clarsimp.
      + intros; rewrite inth_nth_error, nth_error_app in *.
        destruct (lt_dec j (length l1)); [omega|].
        destruct (j - length l1) eqn: Hminus; [omega | clarify].
        exploit nth_error_split'; eauto; intros [l1' [l2' ?]]; clarify.
        specialize (Hlast0 (length (exclude_block l1 b) +
          S (length (exclude_block l1' b))) op2);
          rewrite inth_nth_error, nth_error_app, filter_app in Hlast0.
        unfold exclude_block in *; rewrite lt_dec_plus_r, minus_plus in Hlast0;
          clarify.
        rewrite nth_error_app, lt_dec_eq, minus_diag in Hlast0.
        generalize (dep_block _ _ _ H1); repeat rewrite block_of_loc_spec;
          intro Hblock; rewrite <- Hblock in Hdiff.
        unfold negb, beq in Hlast0; destruct (eq_dec (block_of op2) b);
          clarify; omega.
  Qed.

  Lemma consistent_split : forall (m : list _) b (Hread : read_init m)
    (Hwrite : write_alloc m), consistent m <->
    consistent (proj_block m b) /\ consistent (exclude_block m b).
  Proof.
    intros; split; intro.
    - split; [apply consistent_proj | apply consistent_exclude]; auto.
    - induction m using rev_ind; clarify.
      rewrite consistent_proj_snoc; auto.
      generalize (read_init_exclude _ Hread b),
        (write_alloc_exclude _ Hwrite b); intros.
    rewrite proj_block_app, exclude_block_app in *; clarify.
      unfold negb, beq in *.
      exploit IHm.
      { eapply read_init_app; eauto. }
      { eapply write_alloc_app; eauto. }
      { destruct (eq_dec (block_of x) b); clarsimp;
          eapply consistent_app; eauto. }
      clarify.
      destruct (eq_dec (block_of x) b); clarify.
      generalize (consistent_proj (block_of x) _ H2); intro Hcon.
      rewrite proj_block_app, proj_exclude in Hcon; clarify.
  Qed.
          
  Lemma replace_block : forall m ops (Hcon : consistent (m ++ ops))
    ops' b (Hexclude : exclude_block ops' b = exclude_block ops b)
    (Hcon : consistent (proj_block (m ++ ops') b))
    (Hread : read_init (m ++ ops)) (Hwrite : write_alloc (m ++ ops))
    (Hread' : read_init (m ++ ops')) (Hwrite' : write_alloc (m ++ ops')),
    consistent (m ++ ops').
  Proof.
    intros.
    rewrite consistent_split; auto; split; eauto.
    rewrite exclude_block_app, Hexclude.
    rewrite <- exclude_block_app; apply consistent_exclude; auto.
  Qed.

  Lemma exclude_filter_comm : forall f (m : list _) b,
    exclude_block (filter f m) b = filter f (exclude_block m b).
  Proof. intros; unfold exclude_block; apply filter_comm. Qed.
    
  Lemma proj_filter_comm : forall f (m : list _) b,
    proj_block (filter f m) b = filter f (proj_block m b).
  Proof. intros; unfold proj_block; apply filter_comm. Qed.

  Lemma read_init_none : forall m, read_init (filter (@not_read _ _) m).
  Proof.
    repeat intro.
    rewrite inth_nth_error in *; exploit nth_error_in; eauto.
    rewrite filter_In; clarify.
  Qed.

  Lemma write_alloc_filter : forall m, write_alloc (filter (@not_read _ _) m)
    <-> write_alloc m.
  Proof.
    intros; split; repeat intro; rewrite inth_nth_error in *.
    - exploit nth_error_split'; eauto; intros [l1 [l2 ?]]; clarify.
      specialize (H (length (filter (@not_read _ _) l1)) p v);
        rewrite filter_app, inth_nth_error, nth_error_app, lt_dec_eq,
        minus_diag in *; clarsimp.
      generalize (last_mod_lt _ H1); intro.
      rewrite nth_error_app in *; clarify.
      assert (exists a, nth_error (filter (@not_read _ _) l1) x = Some a)
        as [a ?] by (destruct H2; clarify; eauto).
      exploit nth_filter_split; eauto; intros [l1' [l2' ?]]; clarify.
      exists (length l1'); rewrite <- app_assoc, inth_nth_error, nth_error_app;
        clarsimp.
      inversion H1; econstructor; eauto; intros;
        rewrite inth_nth_error, nth_error_app in *; clarsimp.
      destruct (lt_dec j (length l1')); [omega|].
      destruct (j - length l1') eqn: Hminus; [omega | clarify].
      exploit nth_error_split'; eauto; intros [m1 [m2 ?]]; clarify.
      specialize (Hlast (length (filter (@not_read _ _) l1') +
                         S (length (filter (@not_read _ _) m1))) op2);
        rewrite inth_nth_error, nth_error_app, filter_app, lt_dec_plus_r,
        minus_plus in Hlast; clarify.
      rewrite nth_error_split in Hlast; clarify; omega.
    - exploit nth_filter_split; eauto; intros [l1 [l2 ?]]; clarify.
      specialize (H (length l1) p v);
        rewrite filter_app, inth_nth_error, nth_error_app, lt_dec_eq,
        minus_diag in *; clarsimp.
      generalize (last_mod_lt _ H1); intro.
      rewrite nth_error_app in *; clarify.
      assert (exists a, nth_error l1 x = Some a /\ not_read a = true)
        as [a [? ?]] by (destruct H2; clarify; eauto).
      exploit nth_error_split'; eauto; intros [l1' [l2' ?]]; clarify.
      exists (length (filter (@not_read _ _) l1')); 
        rewrite filter_app, inth_nth_error, nth_error_app; clarsimp.
      rewrite nth_error_split; clarify.
      inversion H1; econstructor; eauto; intros;
        rewrite inth_nth_error, nth_error_app in *; clarsimp.
      destruct (lt_dec j (length (filter (@not_read _ _) l1'))); [omega|].
      destruct (j - length (filter (@not_read _ _) l1')) eqn: Hminus;
        [omega | clarify].
      exploit nth_filter_split; eauto; intros [m1 [m2 ?]]; clarify.
      specialize (Hlast (length l1' + S (length m1)) op2);
        rewrite inth_nth_error, nth_error_app, lt_dec_plus_r, minus_plus
        in Hlast; clarify.
      rewrite nth_error_split in Hlast; clarify; omega.
  Qed.

  Lemma last_op_filter : forall m l op, last_op (filter (@not_read _ _) m) l op 
    <-> last_op m l op.
  Proof.
    unfold last_op; intros; split; intro Hlast_op; clarify;
      rewrite inth_nth_error in *.
    - exploit nth_filter_split; eauto; intros [l1 [l2 ?]]; clarify.
      exists (length l1); assert (inth (l1 ++ op :: l2) (length l1) = Some op)
        by (rewrite inth_nth_error, nth_error_app; clarsimp); clarify.
      inversion Hlast_op1; clarsimp.
      econstructor; eauto; clarsimp.
      rewrite nth_error_app in *; destruct (lt_dec j (length l1)); [omega|].
      destruct (j - length l1) eqn: Hminus; [omega | clarify].
      exploit nth_error_split'; eauto; intros [l1' [l2' ?]]; clarify.
      specialize (Hlast (length (filter (@not_read _ _) l1) +
        S (length (filter (@not_read _ _) l1'))) op2);
        rewrite inth_nth_error, nth_error_app in *; clarsimp.
      rewrite filter_app, nth_error_app in Hlast; clarsimp; omega.
    - exploit nth_error_split'; eauto; intros [l1 [l2 ?]]; clarify.
      exists (length (filter (@not_read _ _) l1)); rewrite filter_app.
      inversion Hlast_op1; clarsimp.
      assert (nth_error (filter (@not_read _ _) l1 ++ op0 ::
        filter (@not_read _ _) l2) (length (filter (@not_read _ _) l1)) =
        Some op0) by (rewrite nth_error_app; clarsimp); clarify.
      econstructor; eauto; clarsimp.
      rewrite nth_error_app in *;
        destruct (lt_dec j (length (filter (@not_read _ _) l1))); [omega|].
      destruct (j - length (filter (@not_read _ _) l1)) eqn: Hminus; [omega |
        clarify].
      exploit nth_filter_split; eauto; intros [l1' [l2' ?]]; clarify.
      specialize (Hlast (length l1 + S (length l1')) op2);
        rewrite inth_nth_error, nth_error_app, lt_dec_plus_r, minus_plus in *;
        clarify.
      rewrite nth_error_split in Hlast; clarify; omega.
  Qed.

  Corollary read_init_filter' : forall m1 m2 (Hread : read_init (m1 ++ m2)),
    read_init (filter (@not_read _ _) m1 ++ m2).
  Proof.
    intros; eapply read_init_last_app; eauto; [|apply read_init_none].
    symmetry; apply last_op_filter.
  Qed.

  Corollary write_alloc_filter' : forall m1 m2 (Hread : write_alloc (m1 ++ m2)),
    write_alloc (filter (@not_read _ _) m1 ++ m2).
  Proof.
    intros; eapply write_alloc_last_app; eauto.
    - symmetry; apply last_op_filter.
    - apply write_alloc_filter; eapply write_alloc_app; eauto.
  Qed.

  Lemma consistent_filter : forall (m : list _) (Hcon : consistent m)
    (Hread : read_init m) (Hwrite : write_alloc m),
    consistent (filter (@not_read _ _) m).
  Proof.
    intros.
    induction m using rev_ind; clarify.
    rewrite filter_app; simpl.
    exploit consistent_app; eauto.
    generalize (read_init_app _ _ Hread), (write_alloc_app _ _ Hwrite); intros.
    destruct (not_read x) eqn: Hnot_read; simpl.
    - rewrite read_write_step; eauto.
      + apply read_init_filter'; auto.
      + apply write_alloc_filter'; auto.
      + apply last_op_filter.
    - autorewrite with list; auto.
  Qed.

  Lemma consistent_core : forall (m : list _) a
    (Hread : read_init (m ++ [a])) (Hwrite : write_alloc (m ++ [a])),
    consistent (m ++ [a]) <->
    (consistent m /\
     consistent (filter (@not_read _ _) (proj_block m (block_of a)) ++ [a])).
  Proof.
    intros; rewrite consistent_proj_snoc; auto.
    assert (proj_block m (block_of a) ++ [a] = proj_block (m ++ [a])
      (block_of a)) as Heq by (rewrite proj_block_app; clarify).
    assert (read_init (proj_block m (block_of a) ++ [a])) as Hread'
      by (rewrite Heq; apply read_init_proj; auto).
    assert (write_alloc (proj_block m (block_of a) ++ [a])) as Hwrite'
      by (rewrite Heq; apply write_alloc_proj; auto).
    generalize (read_init_app _ _ Hread'), (write_alloc_app _ _ Hwrite').
    split; clarify.
    - rewrite read_write_step; eauto.
      + apply read_init_filter'; auto.
      + apply write_alloc_filter'; auto.
      + apply consistent_filter; auto.
        eapply consistent_app; eauto.
      + eapply consistent_app; eauto.
      + setoid_rewrite last_op_filter; reflexivity.
    - generalize (read_init_app _ _ Hread), (write_alloc_app _ _ Hwrite);
        intros.
      rewrite read_write_step; eauto.
      + apply read_init_filter'; auto.
      + apply write_alloc_filter'; auto.
      + apply consistent_proj; auto.
      + eapply consistent_app; eauto.
      + setoid_rewrite last_op_filter; reflexivity.
  Qed.

  Lemma consistent_core_ops : forall b ops (m : list _)
    (Hb : Forall (fun op => block_of op = b) ops)
    (Hread : read_init (m ++ ops)) (Hwrite : write_alloc (m ++ ops)),
    consistent (m ++ ops) <-> (consistent m /\
      consistent (filter (@not_read _ _) (proj_block m b) ++ ops)).
  Proof.
    induction ops; clarsimp.
    - split; clarify.
      apply consistent_filter; [apply consistent_proj | apply read_init_proj |
        apply write_alloc_proj]; auto.
    - inversion Hb; clarify.
      generalize (IHops (m ++ [a])); repeat rewrite <- app_assoc; intro Hiff;
        rewrite Hiff; clarify; split; intro Hcon; clarify.
      + rewrite consistent_core in Hcon1; clarify.
        * rewrite proj_block_app, filter_app in Hcon2; clarify.
          destruct (not_read a) eqn: Hr; clarsimp.
          destruct a; clarify.
          destruct p as (b, o).
          generalize (read_noop (filter not_read (proj_block m b)) (b, o)
            v ops); repeat rewrite to_ilist_app in *.
          rewrite <- iapp_app; intro Hnoop; clarify; rewrite Hnoop; auto.
        * eapply read_init_app; rewrite <- app_assoc; simpl; eauto.
        * eapply write_alloc_app; rewrite <- app_assoc; simpl; eauto.
      + rewrite consistent_core; clarify.
        split; clarify.
        * eapply consistent_app; rewrite <- app_assoc; simpl; eauto.
        * rewrite proj_block_app, filter_app; clarify.
          rewrite <- app_assoc; destruct (not_read a) eqn: Hr; auto.
          destruct a; clarify.
          destruct p as (b, o).
          generalize (read_noop (filter not_read (proj_block m b)) (b, o)
            v ops); repeat rewrite to_ilist_app in *.
          rewrite <- iapp_app; intro Hnoop; clarify; rewrite Hnoop in Hcon2;
            auto.
          eapply consistent_prefix; eauto; apply prefix_mono;
            repeat constructor.
        * eapply read_init_app; rewrite <- app_assoc; simpl; eauto.
        * eapply write_alloc_app; rewrite <- app_assoc; simpl; eauto.
  Qed.

  Lemma no_last_op : forall (m : list _) l,
    (forall op, ~last_op m l op) <->
    Forall (fun x => not_read x = false \/ independent (loc_of x) l) m.
  Proof.
    intros; split; rewrite Forall_forall; repeat intro.
    - exploit in_split; eauto; intros [l1 [l2 ?]].
      destruct (not_read x) eqn: Hnot_read; auto.
      destruct (indep_dec _ (loc_of x) l); auto.
      exploit (has_last_op1 m); eauto.
      { subst; apply nth_error_split. }
      intros [i Hlast_mod].
      inversion Hlast_mod; specialize (H op); contradiction H.
      unfold last_op; eauto.
    - unfold last_op in *; clarsimp.
      exploit nth_error_in; eauto; intro Hin.
      specialize (H _ Hin); inversion H01; clarsimp.
  Qed.

  Lemma last_nil : forall l (op : mem_op block val), ~last_op inil l op.
  Proof.
    unfold last_op; repeat intro; clarsimp.
  Qed.

  Lemma last_op_snoc : forall (m : list (mem_op block val)) x l op,
    last_op (m ++ [x]) l op <->
    (op = x /\ not_read x = true /\ ~independent (loc_of x) l) \/
    (last_op m l op /\ (not_read x = false \/ independent (loc_of x) l)).
  Proof.
    unfold last_op; intros; split; clarify.
    - inversion H1; clarsimp.
      rewrite nth_error_app in *.
      destruct (lt_dec x0 (length m)).
      + specialize (Hlast (length m) x).
        right; split.
        * exists x0; clarsimp.
          generalize (last_mod_take H1 l0); clarsimp.
        * rewrite inth_nth_error, nth_error_app in *; clarsimp.
          destruct (not_read x) eqn: Hnot_read; clarify.
          destruct (indep_dec _ (loc_of x) l); clarify; omega.
      + left; destruct (x0 - length m); clarsimp.
    - destruct H; clarify.
      + exists (length m); rewrite inth_nth_error, nth_error_app; clarsimp.
        econstructor; eauto.
        * rewrite inth_nth_error, nth_error_app; clarsimp.
        * clarsimp.
          generalize (nth_error_lt _ _ H); rewrite app_length; clarify; omega.
      + exists x0; rewrite inth_nth_error, nth_error_app in *.
        generalize (nth_error_lt _ _ H12); clarify.
        inversion H11; econstructor; eauto.
        * rewrite inth_nth_error, nth_error_app; clarsimp.
        * intros; specialize (Hlast j op2).
          rewrite inth_nth_error, nth_error_app in *; clarify.
          destruct (j - length m); clarsimp.
  Qed.

  Lemma last_op_app : forall (m2 m1 : list (mem_op block val)) l op,
    last_op (m1 ++ m2) l op <->
    last_op m2 l op \/ (last_op m1 l op /\
      Forall (fun x => (not_read x = false \/ independent (loc_of x) l)) m2).
  Proof.
    induction m2 using rev_ind; clarsimp.
    - split; intro.
      + right; clarify.
      + destruct H; clarify; exploit last_nil; eauto; clarify.
    - rewrite app_assoc; repeat rewrite last_op_snoc; rewrite IHm2; split;
        clarify.
      + right; rewrite Forall_app; clarify.
      + destruct H; clarify.
        rewrite Forall_app in *; clarify.
        right; inversion H22; clarify.
  Qed.

  Lemma last_iff_ext : forall (m1 m2 m2' : list _)
    (Hlast : forall l op, last_op m2 l op <-> last_op m2' l op) l op,
    last_op (m1 ++ m2) l op <-> last_op (m1 ++ m2') l op.
  Proof.
    intros; repeat rewrite last_op_app.
    repeat rewrite <- no_last_op.
    rewrite Hlast.
    split; intros [? | ?]; [left | right | left | right]; clarify.
    - rewrite <- Hlast; eauto.
    - rewrite Hlast; eauto.
  Qed.

  Lemma read_justified_op : forall m p v m'
    (Hcon : consistent (iapp m (icons (MRead p v) m')))
    (Hread : read_init (iapp m (icons (MRead p v) m'))),
    last_op m (Ptr p) (MWrite p v).
  Proof.
    intros; exploit read_justified; eauto; clarify.
    rewrite split_app, last_op_app; right; split.
    - rewrite last_op_snoc; left; clarify.
    - eapply Forall_impl; eauto; clarify.
      destruct a; clarify.
  Qed.
    
  Lemma consistent_split_reads : forall (m : list _)
    (Hread : read_init m) (Hwrite : write_alloc m),
    consistent m <-> consistent (filter not_read m) /\
      forall r p v, nth_error m r = Some (MRead p v) ->
                    last_op (firstn r m) (Ptr p) (MWrite p v).
  Proof.
    intro; split; intro Hcon.
    - split; [apply consistent_filter; auto|].
      intros.
      exploit nth_error_split'; eauto; clarify.
      rewrite to_ilist_app in *; clarify; exploit read_justified; eauto;
        intros [m1 [m2 ?]]; clarsimp.
      rewrite firstn_length'; [|omega].
      rewrite split_app, last_op_app; right.
      split; [rewrite last_op_snoc; left; clarify|].
      eapply Forall_impl; eauto; clarify.
      destruct a; clarify.
    - clarify.
      induction m using rev_ind; clarify.
      use IHm; [|eapply read_init_app; eauto].
      use IHm; [|eapply write_alloc_app; eauto].
      rewrite filter_app in *; use IHm; [|eapply consistent_app; eauto].
      use IHm.
      rewrite consistent_core; clarify.
      generalize (consistent_proj (block_of x) _ Hcon1); intro H.
      destruct (not_read x) eqn: Hnot; clarify.
      { rewrite proj_block_app, proj_filter_comm in H; clarify; apply H. }
      autorewrite with list in H.
      destruct x; clarify.
      specialize (Hcon2 _ _ _ (nth_error_split _ _ _)).
      rewrite to_ilist_app in *; clarify; apply read_consistent_op.
      + rewrite iapp_nil_ilist; rewrite proj_filter_comm in H; auto.
      + rewrite last_op_filter.
        destruct p as (b, o).
        assert (block_of_loc (Ptr (b, o)) = b) as Hblock by auto;
          rewrite <- Hblock; rewrite <- last_op_proj; clarsimp.
      + exploit nth_error_lt; eauto; intro.
        specialize (Hcon2 r p v); rewrite nth_error_app in Hcon2; clarsimp.
        destruct (r - length m) eqn: Hminus; [clarsimp | omega].
  Qed.

End Simple.