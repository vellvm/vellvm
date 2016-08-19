Require Import block_model.
Require Import conc_model.
Require Import Ensembles.
Require Import Util.
Require Import LTS.
Require Import Relation_Operators.

Set Implicit Arguments.

Section Examples.

Definition var := nat.
Definition local := nat.
Definition tid := nat.

Instance var_eq : EqDec_eq var. eq_dec_inst. Qed.

Definition ptr := (var * nat)%type.

Inductive conc_op : Type :=
| Read (t : tid) (x : ptr) (v : nat)
| Write (t : tid) (x : ptr) (v : nat)
| ARW (t : tid) (x : ptr) (v : nat) (v' : nat).

Definition thread_of c :=
  match c with
  | Read t _ _ => t
  | Write t _ _ => t
  | ARW t _ _ _ => t
  end.

Definition to_seq c :=
  match c with
  | Read _ x v => [MRead x v]
  | Write _ x v => [MWrite x v]
  | ARW _ x v v' => [MRead x v; MWrite x v']
  end.

Hint Rewrite nth_error_single : util.

Instance Base : @MM_base _ _ var_eq _ _ := { thread_of := thread_of;
  to_seq := to_seq }.
Proof.
  - destruct c; clarsimp.
    destruct i; clarsimp.
    destruct j; clarsimp.
  - destruct c; clarsimp.
    destruct i; clarsimp.
    destruct j; clarify.
Defined.

Context (*(ML : Memory_Layout nat var_eq)*) (MM : Memory_Model 0 nat).

Notation event := (event(conc_op := conc_op) nat).

Section Lang.

  Inductive expr : Set :=
  | I (n : nat)
  | V (a : local)
  | Plus (e1 e2 : expr).

  Inductive instr : Set :=
  | Assign (a : local) (e : expr)
  | Load (a : local) (x : ptr)
  | Store (x : ptr) (e : expr)
  | Lock (m : ptr)
  | Unlock (m : ptr)
  | Signal (m : ptr)
  | Wait (m : ptr).

  Definition prog := list (list instr).

  Definition env := tid -> local -> nat.

  Definition init_env (t : tid) (a : local) := 0.

  Fixpoint eval G e := match e with
  | I n => n
  | V a => G a
  | Plus e1 e2 => eval G e1 + eval G e2
  end.

  Definition loc_of c :=
    match c with
    | Read _ x _ => x
    | Write _ x _ => x
    | ARW _ x _ _ => x
    end.

  Definition synchronizes_with c1 c2 := loc_of c1 = loc_of c2 /\
    exists t x v v', c1 = ARW t x v v' \/ c2 = ARW t x v v'.

(*  Fixpoint drop_b_reads b l :=
    match l with
    | [] => []
    | Read t x v :: rest => if eq_dec (fst x) b then drop_b_reads b rest
                            else Read t x v :: drop_b_reads b rest
    | ARW t x v v' :: rest => if eq_dec (fst x) b
                              then Write t x v' :: drop_b_reads b rest
                              else ARW t x v v' :: drop_b_reads b rest
    | c :: rest => c :: drop_b_reads b rest
    end.*)

  Definition upd_env G (t : tid) (a : local) (v : nat) t' a' :=
    if eq_dec t' t then if eq_dec a' a then v else G t' a' else G t' a'.

  Inductive instr_result G t : instr -> list conc_op -> env -> Prop :=
  | assign a e : instr_result G t (Assign a e) [] (upd_env G t a (eval (G t) e))
  | load a x v : instr_result G t (Load a x) [Read t x v] (upd_env G t a v)
  | store x e : instr_result G t (Store x e) [Write t x (eval (G t) e)] G
  | lock m : instr_result G t (Lock m) [ARW t m 0 (S t)] G
  | unlock m : instr_result G t (Unlock m) [ARW t m (S t) 0] G
  | signal m : instr_result G t (Signal m) [ARW t m 0 1] G
  | wait m : instr_result G t (Wait m) [ARW t m 1 0] G.

  Definition state := (prog * env)%type.

  Inductive step : step_rel state conc_op :=
  | step_instr P G t i rest l G' (Hinstr : nth_error P t = Some (i :: rest))
      (Hresult : instr_result G t i l G') :
      step (P, G) l (replace P t rest, G').

  Record indexed_events := { evst : execution _;
    next : nat; Hnext : forall e : event, events evst e -> id e < next }.

  Program Definition add_event E c := {| evst :=
    {| events := Add (events (evst E)) {| id := next E; op := c |};
       constraints := fun i j => constraints (evst E) i j \/
         exists c0, events (evst E) {| id := i; op := c0 |} /\ j = next E /\
         (thread_of c0 = thread_of c \/ synchronizes_with c0 c) |};
    next := S (next E) |}.
  Next Obligation.
  Proof.
    rewrite Add_spec in H; clarify.
    exploit Hnext; eauto.
  Defined.
  
  Fixpoint add_events E l :=
    match l with 
    | [] => E
    | c :: rest => add_events (add_event E c) rest
    end.

  Inductive mem_step S E : state -> indexed_events -> Prop :=
  | step_mem l S' (Hstep : step S l S')
      X (Hvalid : valid (evst (add_events E l)) X) :
      mem_step S E S' (add_events E l).

  Program Definition E0 := {|
    evst := {| events := Empty_set; constraints := fun _ _ => False |};
    next := 0 |}.
  Next Obligation.
    inversion H.
  Defined.

  Definition op_match t i lc :=
    match i with
    | Assign _ _ => lc = []
    | Load _ x => exists v, lc = [Read t x v]
    | Store x (I n) => lc = [Write t x n]
    | Lock m => lc = [ARW t m 0 (S t)]
    | Unlock m => lc = [ARW t m (S t) 0]
    | Signal m => lc = [ARW t m 0 1]
    | Wait m => lc = [ARW t m 1 0]
    | _ => False
    end.

  Definition simple i := match i with Store _ e =>
      match e with I _ => True | _ => False end
    | _ => True end.

  Lemma instr_ops : forall G t i lc G' (Hsimple : simple i)
    (Hresult : instr_result G t i lc G'), op_match t i lc.
  Proof.
    intros; inversion Hresult; clarify; eauto.
    destruct e; clarify.
  Qed.

  Fixpoint make_events (ids : list nat) (ops : list conc_op) :=
    match (ids, ops) with
    | (i :: irest, c :: crest) =>
        {| id := i; op := c |} :: make_events irest crest
    | _ => []
    end.

  Fixpoint ops_match t li E :=
    match li with
    | [] => events E = Empty_set
    | i :: rest => exists l ids, op_match t i l /\ length ids = length l /\
        Included (set_of (make_events ids l)) (events E) /\
        let S' := Setminus (events E) (set_of (make_events ids l)) in
        (forall e e', In e (make_events ids l) -> S' e' ->
           constraints E (id e) (id e')) /\ ops_match t rest (upd_events E S')
    end.

  Definition t_events (E : execution nat) t e :=
    events E e /\ thread_of (op e) = t.

  Definition prog_match P E := forall t,
    match nth_error P t with
    | Some li => ops_match t li (upd_events E (t_events E t))
    | None => forall e, events E e -> thread_of (op e) <> t
    end.

  Definition final_state (S : state) := Forall (fun il => il = []) (fst S).

  Lemma step_star_break : forall S l Sf (Hsteps : rtc step S l Sf)
    (Hfinal : final_state Sf) t il1 il2
    (Ht : nth_error (fst S) t = Some (il1 ++ il2)),
    exists l1 S' l2, rtc step S l1 S' /\ rtc step S' l2 Sf /\ l = l1 ++ l2 /\
      nth_error (fst S') t = Some il2.
  Proof.
    intros ??????; induction Hsteps; clarify.
    { exploit nth_error_in; eauto; intro Hin.
      setoid_rewrite Forall_forall in Hfinal; specialize (Hfinal _ Hin).
      destruct il1; clarify.
      exists [], s, []; clarify. }
    inversion Hstep; clarify.
    destruct (eq_dec t0 t); clarify.
    - destruct il1; clarsimp.
      { exists []; do 3 eexists; [apply rtc_refl|].
        split; [eapply rtc_step; eauto | clarify]. }
      exploit nth_error_lt; eauto; intro.
      rewrite nth_error_replace in IHHsteps; clarify.
      specialize (IHHsteps _ _ eq_refl);
        destruct IHHsteps as (l1 & S' & l2 & ?).
      exists (l ++ l1), S', l2; clarsimp.
      econstructor; eauto.
    - rewrite nth_error_replace_2 in IHHsteps; auto.
      specialize (IHHsteps _ _ Ht); destruct IHHsteps as (l1 & S' & l2 & ?).
      exists (l ++ l1), S', l2; clarsimp.
      econstructor; eauto.
  Qed.    

  Lemma step_star_thread : forall S l Sf (Hsteps : rtc step S l Sf)
    (Hfinal : final_state Sf) t il1 i il2
    (Ht : nth_error (fst S) t = Some (il1 ++ i :: il2)),
    exists l1 S' lc G' l2, rtc step S l1 S' /\
      nth_error (fst S') t = Some (i :: il2) /\
      instr_result (snd S') t i lc G' /\
      rtc step (replace (fst S') t il2, G') l2 Sf /\ l = l1 ++ lc ++ l2.
  Proof.
    intros ??????; induction Hsteps; clarify.
    { exploit nth_error_in; eauto; intro Hin.
      setoid_rewrite Forall_forall in Hfinal; specialize (Hfinal _ Hin).
      destruct il1; clarify. }
    inversion Hstep; clarify.
    generalize (nth_error_lt _ _ Hinstr); intro.
    rewrite nth_error_replace in *; auto.
    destruct (eq_dec t0 t); clarsimp.
    - destruct il1; clarify.
      + exists [], (P, G); clarify; repeat eexists; eauto.
      + specialize (IHHsteps _ _ _ eq_refl);
          destruct IHHsteps as (l1 & S' & lc & G'' & l2 & ?).
        exists (l ++ l1), S', lc, G'', l2; clarsimp.
        econstructor; eauto.
    - specialize (IHHsteps _ _ _ eq_refl);
        destruct IHHsteps as (l1 & S' & lc & G'' & l2 & ?).
      exists (l ++ l1), S', lc, G'', l2; clarsimp.
      econstructor; eauto.
  Qed.    

  Lemma final_ops : forall S (Hfinal : final_state S) E
    (Hempty : events E = Empty_set), prog_match (fst S) E.
  Proof.
    unfold prog_match; clarify.
    destruct (nth_error (fst S) t) eqn: Hnth; intros.
    - exploit nth_error_in; eauto; intro Hin.
      setoid_rewrite Forall_forall in Hfinal; specialize (Hfinal _ Hin);
        clarify.
      apply set_ext; unfold t_events; split; clarify.
      rewrite Hempty in *; auto.
    - rewrite Hempty in H; inversion H.
  Qed.

  Lemma add_events_app : forall l1 l2 E, add_events E (l1 ++ l2) =
    add_events (add_events E l1) l2.
  Proof.
    induction l1; clarify.
  Qed.
  
  Lemma add_events_events : forall l E, events (evst (add_events E l)) =
    Union (events (evst E))
          (set_of (make_events (interval (next E) (next E + length l)) l)).
  Proof.
    induction l; clarify.
    - rewrite plus_0_r, interval_nil; simpl.
      rewrite set_of_nil, Union_Empty; auto.
    - rewrite IHl.
      setoid_rewrite interval_alt at 2.
      rewrite lt_dec_plus_l, NPeano.Nat.add_succ_r.
      simpl; rewrite set_of_cons, Union_Add; auto.
  Qed.

  Definition minus_events E (S : Ensemble event) :=
    upd_events E (Setminus (events E) S).

  Program Definition empty_events E :=
    {| evst := upd_events (evst E) Empty_set; next := next E |}.
  Next Obligation.
  Proof.
    inversion H.
  Defined.

  Lemma t_events_Add : forall E e t,
    t_events (upd_events E (Add (events E) e)) t =
    if beq (thread_of (op e)) t then Add (t_events E t) e else t_events E t.
  Proof.
    intros; apply set_ext; intro; unfold t_events, beq; simpl.
    rewrite Add_spec; split; intro Hin; clarify.
    - destruct Hin1; clarify; rewrite Add_spec; clarify.
    - rewrite Add_spec in Hin; clarify.
  Qed.

  Lemma add_t_events : forall l E t,
    exists ids, t_events (evst (add_events E l)) t =
    Union (set_of (make_events ids (filter (fun c => beq (thread_of c) t) l)))
          (t_events (evst E) t) /\
      length ids = length ((filter (fun c => beq (thread_of c) t) l)).
  Proof.
    induction l; clarify.
    { exists []; clarify; rewrite set_of_nil, Empty_Union; auto. }
    specialize (IHl (add_event E a) t); destruct IHl as (ids & Heq & Hlen).
    rewrite Heq; unfold t_events; simpl.
    destruct (beq (thread_of a) t) eqn: Ht; unfold beq in Ht;
      clarify.
    + exists (next E :: ids); clarify.
      rewrite set_of_cons; apply set_ext; intro; repeat rewrite Union_spec,
        Add_spec; split; clarify.
    + exists ids; clarify.
      apply set_ext; intro; repeat rewrite Union_spec; rewrite Add_spec;
        split; clarify.
  Qed.

  Lemma op_match_thread : forall t i l, op_match t i l ->
    Forall (fun c => thread_of c = t) l.
  Proof.
    destruct i; clarify.
    destruct e; clarify.
  Qed.

  Lemma ops_match_ext : forall t li E E'
    (Hevents : events E = events E')
    (Hconstraints : forall e1 e2 (He1 : events E e1) (He2 : events E e2),
       constraints E (id e1) (id e2) <-> constraints E' (id e1) (id e2))
    (Hmatch : ops_match t li E), ops_match t li E'.
  Proof.
    induction li; clarify.
    { clarsimp. }
    do 3 eexists; eauto; split; eauto.
    rewrite <- Hevents; clarify.
    split; intros.
    - rewrite Setminus_spec in *; rewrite <- Hconstraints; clarify.
      apply Hmatch2221; auto; rewrite Setminus_spec; clarify.
      apply Hmatch221; auto.
    - apply (IHli (upd_events E (Setminus (events E)
        (set_of (make_events x0 x))))); clarify.
      apply Hconstraints; rewrite Setminus_spec in *; clarify.
  Qed.

  Lemma make_events_nth : forall ids ops i e,
    nth_error (make_events ids ops) i = Some e <->
      nth_error ids i = Some (id e) /\ nth_error ops i = Some (op e).
  Proof.
    induction ids; clarify; destruct ops; split; clarsimp.
    - destruct i; clarify.
      rewrite IHids in *; auto.
    - destruct i; clarify.
      + destruct e; clarify.
      + rewrite IHids; auto.
  Qed.

  Corollary in_make_events : forall ids ops e, In e (make_events ids ops) ->
    In (op e) ops /\ In (id e) ids.
  Proof.
    intros.
    exploit in_nth_error; eauto; clarify.
    rewrite make_events_nth in *; clarify.
    split; eapply nth_error_in; eauto.
  Qed.

  Corollary make_shift_ids : forall a n b e ops
    (He : In e (make_events (interval a (a + n)) ops)),
    In {| id := id e + b - a; op := op e |}
       (make_events (interval b (b + n)) ops).
  Proof.
    intros.
    exploit in_nth_error; eauto; clarify.
    rewrite make_events_nth in *; clarify.
    rewrite nth_error_interval in *; clarify.
    eapply nth_error_in; rewrite make_events_nth; split; eauto; clarify.
    rewrite nth_error_interval.
    clear cond; rewrite minus_plus in *; clarify.
    rewrite <- plus_assoc, minus_plus, plus_comm; auto.
  Qed.

  Lemma add_next : forall l E, next (add_events E l) = next E + length l.
  Proof.
    induction l; clarify.
    rewrite IHl; clarify.
  Qed.

  Lemma t_events_Empty : forall E t, events E = Empty_set ->
    t_events E t = Empty_set.
  Proof.
    intros; apply set_ext; intro; unfold t_events; split; clarify.
    rewrite H in *; auto.
  Qed.

  Lemma add_constraints_mono : forall l E i j,
    constraints (evst E) i j -> constraints (evst (add_events E l)) i j.
  Proof.
    induction l; clarify.
    apply IHl; clarify.
  Qed.

  Lemma add_constraints_iff : forall l E i j,
    constraints (evst (add_events E l)) i j <->
      constraints (evst E) i j \/
      next E <= j /\ exists e c, nth_error l (j - next E) = Some c /\
        id e = i /\ (events (evst E) e \/
         next E <= i < j /\ nth_error l (i - next E) = Some (op e)) /\
        (thread_of (op e) = thread_of c \/ synchronizes_with (op e) c).
  Proof.
    induction l; clarify.
    { split; clarsimp. }
    rewrite IHl; split; intros [Hcon | Hcon]; clarify.
    - right; clarsimp.
      do 3 eexists; eauto.
      split; eauto; clarify.
    - rewrite NPeano.Nat.sub_succ_r in *.
      destruct (j - next E) eqn: Hminus; [omega | clarify].
      right; split; [omega|].
      rewrite Add_spec in *; destruct Hcon2221 as [[? | ?] | ?]; clarify.
      + do 2 eexists; eauto.
      + exists {| id := next E; op := a |}; eexists; split; eauto; clarsimp.
      + exists x; destruct (id x - next E) eqn: Hminus'; [omega | clarify].
        do 2 eexists; eauto; clarify.
        right; clarify; omega.
    - destruct (j - next E) eqn: Hminus; clarify.
      + left; right.
        destruct Hcon2221; clarify; [|omega].
        exists (op x); destruct x; clarify; omega.
      + right; split; [omega|].
        repeat rewrite NPeano.Nat.sub_succ_r; rewrite Hminus.
        exists x; do 2 eexists; eauto; clarify.
        rewrite Add_spec; clarify.
        destruct (id x - next E) eqn: Hminus'; clarify.
        * left; right; destruct x; clarify.
          f_equal; omega.
        * right; clarify; omega.
  Qed.

  Lemma add_events_po : forall t l E e e'
    (He : t_events (evst E) t e) (He' : t_events (evst (add_events E l)) t e')
    (Hafter : ~t_events (evst E) t e'),
    constraints (evst (add_events E l)) (id e) (id e').
  Proof.
    induction l; clarify.
    specialize (IHl (add_event E a) e e'); unfold t_events in *; clarify.
    repeat rewrite Add_spec in IHl; clarify.
    rewrite add_events_events, Union_spec in He'1; destruct He'1.
    - clarify.
      rewrite Add_spec in *; clarify.
      apply add_constraints_mono; clarify.
      right; exists (op e); destruct e; clarify.
    - apply IHl; intros [[? | ?] _]; auto.
      generalize (in_nth_error _ _ H); intros (? & _ & ?).
      rewrite make_events_nth, nth_error_interval in *; clarify; omega.
  Qed.

  Lemma add_empty_constraints : forall E l e1 e2
    (He1 : events (evst (add_events (empty_events E) l)) e1)
    (He2 : events (evst (add_events (empty_events E) l)) e2),
    constraints (evst (add_events (empty_events E) l)) (id e1) (id e2) <->
    constraints (evst (add_events E l)) (id e1) (id e2).
  Proof.
    intros.
    rewrite add_events_events, Union_spec in *; clarify.
    rewrite add_constraints_iff.
    simpl; repeat rewrite add_constraints_iff.
    split; intro Hcon; clarify.
    - right; split; [omega|].
      do 3 eexists; eauto; split; eauto.
    - right; clarify.
      do 3 eexists; eauto; split; eauto; clarify.
      generalize (in_nth_error _ _ He1); clarify.
      rewrite make_events_nth in *; clarify.
      rewrite nth_error_interval in *; clarify.
      generalize (Hnext E x); clarify; omega.
  Qed.
      
  Lemma op_match_one : forall P t i rest l E l'
    (Hempty : events (evst E) = Empty_set)
    (Ht : nth_error P t = Some (i :: rest)) (Hi : op_match t i l)
    (Hrest : prog_match (replace P t rest)
      (evst (add_events (empty_events (add_events E l)) l'))),
    prog_match P (evst (add_events (add_events E l) l')).
  Proof.
    repeat intro.
    specialize (Hrest t0); destruct (eq_dec t0 t); clarify.
    - exploit nth_error_lt; eauto; intro.
      rewrite nth_error_replace in Hrest; clarify.
      generalize (add_t_events l' (add_events E l) t), (add_t_events l E t);
        intros (ids' & Hadd' & Hlen') (ids & Hadd & Hlen).
      setoid_rewrite t_events_Empty in Hadd at 2; auto.
      assert (Forall (fun x => beq (thread_of x) t = true) l).
      { eapply Forall_impl; [|eapply op_match_thread; eauto].
        unfold beq; clarify. }
      rewrite filter_all in Hadd, Hlen; auto.
      rewrite Union_Empty in Hadd; rewrite Hadd in Hadd'.
      do 3 eexists; eauto; split; eauto.
      split; [|split].
      + rewrite Hadd', Union_comm; apply Incl_Union.
      + intros ?? He He'.
        rewrite Setminus_spec in He'; clarify.
        eapply add_events_po; eauto.
        * rewrite Hadd; auto.
        * rewrite Hadd; auto.
      + eapply ops_match_ext; try (apply Hrest); clarify.
        * rewrite <- Hadd.
          apply set_ext; intro; unfold t_events; rewrite Setminus_spec.
          repeat rewrite add_events_events, Union_spec; split; intro Hin;
            clarify.
          { intro Hin'; rewrite Hempty in *; clarify.
            generalize (in_make_events _ _ _ Hin1),
              (in_make_events _ _ _ Hin'1); repeat rewrite interval_in_iff.
            rewrite add_next; omega. }
          { rewrite Hempty in *; clarify.
            contradiction Hin2; clarify. }
        * unfold t_events in He1, He2; clarify.
          apply add_empty_constraints; auto.
    - rewrite nth_error_replace_2 in Hrest; auto.
      exploit op_match_thread; eauto; rewrite Forall_forall; intro Hin.
      destruct (nth_error P t0) eqn: Hnth; clarify.
      + eapply ops_match_ext; try (apply Hrest); clarify.
        * apply set_ext; intro x; unfold t_events.
          repeat rewrite add_events_events, Union_spec; rewrite Hempty;
            split; clarify.
          exploit in_make_events; eauto; clarify.
          specialize (Hin (op x)); clarify.
        * unfold t_events in He1, He2; clarify.
          apply add_empty_constraints; auto.
      + intro; clarify; contradiction n.
        specialize (Hrest e).
        repeat rewrite add_events_events, Union_spec in *; clarify.
        rewrite Hempty in H; clarify.
        eapply Hin, in_make_events; eauto.
  Qed.

  Lemma prog_ops : forall S l Sf (Hsteps : rtc step S l Sf)
    (Hsimple : Forall (fun li => Forall simple li) (fst S))
    (Hfinal : final_state Sf) E (Hempty : events (evst E) = Empty_set),
    prog_match (fst S) (evst (add_events E l)).
  Proof.
    intros ??????; induction Hsteps; clarify.
    { apply final_ops; auto. }
    inversion Hstep; clarify.
    assert (Forall simple (i :: rest)) as Ht.
    { rewrite Forall_forall in Hsimple; eapply Hsimple, nth_error_in; eauto. }
    inversion Ht; clarify.
    exploit instr_ops; eauto; intro.
    rewrite add_events_app; eapply op_match_one; eauto.
    apply IHHsteps; auto.
    apply Forall_replace; auto.
  Qed.

  Fixpoint count_instr_ops i :=
    match i with
    | Assign _ _ => 0
    | _ => 1
    end.

  Fixpoint count_thread_ops li :=
    match li with
    | [] => 0
    | i :: rest => count_instr_ops i + count_thread_ops rest
    end.

  Fixpoint count_ops P :=
    match P with
    | [] => 0
    | li :: rest => count_thread_ops li + count_ops rest
    end.

  Lemma count_final : forall S (Hfinal : final_state S), count_ops (fst S) = 0.
  Proof.
    destruct S as (P, G); induction P; clarify.
    inversion Hfinal; clarify.
  Qed.

  Lemma count_step : forall P G t i rest l G'
    (Hnth : nth_error P t = Some (i :: rest))
    t' (Hresult : instr_result G t' i l G'),
    count_ops P = length l + count_ops (replace P t rest).
  Proof.
    induction P; clarsimp.
    destruct t; clarify.
    - inversion Hresult; clarify.
    - erewrite IHP; eauto; omega.
  Qed.

  Lemma step_count_ops : forall S l S' (Hsteps : rtc step S l S')
    (Hfinal : final_state S'), length l = count_ops (fst S).
  Proof.
    intros; induction Hsteps.
    - symmetry; apply count_final; auto.
    - rewrite app_length; inversion Hstep; clarify.
      erewrite count_step; eauto.
  Qed.
      
End Lang.

Definition ordered_ARWs E := forall x, total_on (constraints (evst E))
  (fun e => events (evst E) e /\ exists t v v', op e = ARW t x v v').

Lemma ARW_order : forall l E (Horder : ordered_ARWs E),
  ordered_ARWs (add_events E l).
Proof.
  induction l; clarify.
  apply IHl; clear IHl; unfold ordered_ARWs in *.
  intros x e1 e2 He1 He2; clarify.
  rewrite Add_spec in *; specialize (Horder x e1 e2).
  destruct He11, He21; clarify.
  - do 2 (use Horder; [|eauto]); clarify.
  - left; right.
    exists (op e1); destruct e1; clarify.
    right; repeat eexists; eauto.
  - right; right; right.
    exists (op e2); destruct e2; clarify.
    right; repeat eexists; eauto.
Qed.

Corollary ARW_order' : forall l E (HE : E = evst (add_events E0 l)) x,
  total_on (constraints E)
    (fun e => events E e /\ exists t v v', op e = ARW t x v v').
Proof.
  intros ???; subst; eapply ARW_order.
  repeat intro; clarify.
Qed.

Definition x_events (E : execution nat) x e :=
  events E e /\ fst (loc_of (op e)) = x.

(*Corollary ARW_only : forall E (Horder : ordered_ARWs E) x
  (Honly : forall e, events (evst E) e -> fst (loc_of (op e)) = x ->
     exists t o v v', op e = ARW t (x, o) v v'),
  total_on (constraints (evst E)) (x_events (evst E) x).
Proof.
  unfold x_events; repeat intro; eapply Horder; clarify.
  - specialize 
Qed.*)

Lemma lower_loc : forall a c (Ha : In a (to_seq c)),
  block_model.loc_of a = Ptr (loc_of c).
Proof.
  destruct c; clarify.
Qed.

Corollary reads_x : forall E e p v (Hreads : reads (op e) p v)
  (He : events E e), x_events E (fst p) e.
Proof.
  unfold x_events; clarify.
  exploit lower_loc; eauto; clarify; inversion H; auto.
Qed.

Corollary mods_x : forall E e p (Hreads : mods (op e) p)
  (He : events E e), x_events E (fst p) e.
Proof.
  unfold mods, x_events; clarify.
  exploit lower_loc; eauto; clarify.
  destruct x; clarify; inversion H; auto.
Qed.

Corollary writes_x : forall E e p v (Hreads : writes (op e) p v)
  (He : events E e), x_events E (fst p) e.
Proof.
  intros; apply mods_x; [eapply writes_mods; eauto | auto].
Qed.

Lemma clos_trans_total : forall R (S : Ensemble event) (Htotal : total_on R S),
  total_on (clos_trans R) S.
Proof.
  repeat intro.
  specialize (Htotal e1 e2); clarify.
  destruct Htotal; clarify; [left | right; right]; apply t_step; auto.
Qed.

(* up? *)
Definition domain (R : order nat) (S : Ensemble event) :=
  forall i j, R i j -> exists ei ej, id ei = i /\ id ej = j /\ S ei /\ S ej.

Lemma clos_trans_domain : forall R S (Hdom : domain R S),
  domain (clos_trans R) S.
Proof.
  repeat intro; induction H; eauto; clarify.
  eexists; eauto.
Qed.

Lemma cont_trans : forall R R' (S : Ensemble event) (Hdom : domain R S)
  (Hcont : contained R R') (Htrans : transitive_on R' S),
  contained (clos_trans R) R'.
Proof.
  repeat intro; induction H; clarify.
  generalize (clos_trans_domain Hdom H), (clos_trans_domain Hdom H0); clarify.
  eapply (Htrans _ x3); auto.
Qed.

Hypothesis hb_dec : forall E X (l : list event)
  (Hlin : linearization E (hb X) l)
  i1 i2 (Hi1 : In i1 (map (@id _ _) l)) (He2 : In i2 (map (@id _ _) l)),
  {hb X i1 i2} + {~hb X i1 i2}.

Lemma total_uniform : forall E X b
  (Hcont : contained (clos_trans (constraints E)) (hb X))
  (Htotal : total_on (clos_trans (constraints E)) (x_events E b))
  (Hreads' : rf_reads (events E) X) e o v (He : events E e)
  (Hreads : reads (op e) (b, o) v)
  l (Hlin : linearization (events E) (full (events E) X) l),
  exists w, events E w /\ mods (op w) (b, o) /\ hb X (id w) (id e) /\
    forall w' (Hw' : events E w') (Hmods : mods (op w') (b, o)), 
    hb X (id w') (id w) \/ w' = w \/ w' = e \/ hb X (id e) (id w').
Proof.
  intros.
  exploit reads_x; eauto; intro Hxe.
  rewrite (lin_set Hlin) in He; exploit in_split; eauto; intros (l1 & l2 & ?).
  subst; destruct (find (fun e' => if find (fun a => op_modifies _ a (b, o))
    (to_seq (op e')) then true else false) (rev l1)) eqn: Hfind.
  rewrite find_spec in Hfind; destruct Hfind as (i & Hi & Hmods & Hlast).
  generalize (mods_spec (op e0) (b, o)); intro Hmods0; exists e0; clarify.
  assert (events E e0) by (exploit nth_error_in; eauto;
    rewrite <- in_rev, (lin_set Hlin), in_app; auto); clarify.
  exploit mods_x; eauto; intro Hxe0.
  generalize (Htotal _ _ Hxe0 Hxe); intros [? | [? | ?]]; clarify.
  exploit mods_x; eauto; intro Hxw'.
  generalize (Htotal _ _ Hxw' Hxe); intros [? | [? | ?]]; clarify.
  exploit (lin_order_2 Hlin); eauto.
  { apply nth_error_split. }
  { apply t_step; repeat eexists; auto.
    left; auto.
    { unfold x_events in Hxe; clarify. } }
  intros (i' & Hi' & ?).
  specialize (Htotal _ _ Hxw' Hxe0); clarify.
  exploit nth_error_rev'; eauto; intro Hi0.
  exploit (lin_order_3 Hlin).
  { instantiate (2 := (length l1 - i - 1)); rewrite nth_error_app.
    exploit nth_error_lt; eauto; clarify; eauto. }
  { eauto. }
  { apply t_step; repeat eexists; auto; left; auto. }
  intro Hgt.
  rewrite nth_error_app in Hi'; clarify.
  generalize (nth_error_rev _ _ Hi'); intro.
  generalize (mods_spec (op w') (b, o)).
  specialize (Hlast (length l1 - i' - 1) w'); use Hlast; [clarify | omega].
  - generalize (lin_nodup Hlin); intro Hnodup.
    rewrite NoDup_app in Hnodup; clarify.
    exploit nth_error_in; eauto; rewrite <- in_rev; intro; exploit Hnodup22;
      eauto; clarify.
  - exploit (lin_order_3 Hlin); eauto.
    { apply nth_error_split. }
    { instantiate (2 := length l1 - i - 1).
      exploit nth_error_rev'; eauto; intro.
      exploit nth_error_lt; eauto; rewrite nth_error_app; clarify; eauto. }
    { apply t_step; repeat eexists; auto.
      left; auto.
      { unfold x_events in Hxe; clarify. } }
    Opaque minus.
    destruct l1; clarify; [clarsimp | exfalso; omega].
  - rewrite find_fail, Forall_forall in Hfind.
    exploit Hreads'; eauto.
    { rewrite (lin_set Hlin); auto. }
    intros (w & Hw); clarify.
    exploit (lin_order_2 Hlin); eauto.
    { apply nth_error_split. }
    { apply t_step; repeat eexists; auto.
      right; auto.
      { unfold x_events in Hxe; clarify. } }
    intros (i & Hi & ?); rewrite nth_error_app in Hi; clarify.
    exploit nth_error_in; eauto; rewrite in_rev; intro.
    exploit Hfind; eauto; generalize (mods_spec (op w) (b, o)); clarify.
Qed.

(*Notation find_mod c p := (find (fun a => op_modifies _ a p) (to_seq c)).*)

Lemma total_read : forall E x (Hdom : domain (constraints E) (events E))
  (Htotal : total_on (clos_trans (constraints E)) (x_events E (fst x)))
  r (Hr : events E r) v (Hreads : reads (op r) x v) X (Hvalid : valid E X),
  exists w a, events E w /\ In a (to_seq (op w)) /\ op_modifies _ a x = true /\
    match_op 0 a v /\ clos_trans (constraints E) (id w) (id r)
    /\ forall w2 v2, events E w2 -> writes (op w2) x v2 ->
         w2 = w \/ clos_trans (constraints E) (id w2) (id w) \/
         w2 = r \/ clos_trans (constraints E) (id r) (id w2).
Proof.
  intros.
  destruct (drop_b_reads (fst x) E ([r], X)) as (ops, X') eqn: Hdrop.
  generalize (valid_hb _ _ Hvalid); intro Hcont.
  generalize (hb_trans _ _ Hvalid); intro Htrans.
  generalize (cont_trans Hdom Hcont Htrans); intro Hcont'.
  generalize (reads_x _ _ _ _ Hreads Hr); intro.
  generalize (valid_full _ _ Hvalid); intros (l & Hlin).
  generalize (full_lin Hlin); intros (? & _).
  exploit (before_lin_hb(conc_op := conc_op)); eauto;
    intros (m1 & m2 & Hm1 & Hm2).
  rewrite private_seq_1 in Hvalid; eauto.
  destruct Hvalid as (_ & Hseq).
  assert (nth_error (proj_block (to_seq (op r)) (fst x)) 0 = Some (MRead x v))
    as Hr0.
  { unfold reads in Hreads; destruct (op r); simpl in *;
      repeat (destruct Hreads as [Hreads | Hreads]); inversion Hreads;
      destruct x; unfold beq in *; clarify. }
  destruct x as (b, o); clarify.
  specialize (Hseq _ _ Hreads).
  destruct (find (fun e => if find (fun a => op_modifies _ a (b, o))
    (to_seq (op e)) then true else false) (@rev event m1)) eqn: Hfind; clarify.
  exists e, x; clarify.
  exploit find_success; eauto; rewrite <- in_rev, <- (lin_set Hm1);
    unfold before; clarify.
  generalize (last_op_in _ Hseq21), (last_op_mods Hseq21); clarify.
  generalize (Htotal r e); intro Hord.
  exploit mods_x; eauto.
  { unfold mods; eauto. }
  clarify; destruct Hord as [? | [? | ?]].
  { exploit (lin_antisym Hm2); eauto; clarify. }
  { subst; exploit (lin_irrefl Hm2); eauto; clarify. }
  split; [auto | intros ?? Hw2 Hwrites2].
  generalize (Htotal w2 r).
  generalize (writes_x _ _ _ _ Hwrites2 Hw2); intros ? Hord'; clarify.
  generalize (Htotal w2 e); intro Hordw; clarify.
  admit. (* from find *)
  { apply valid_wf; auto. }
  { intros ?? He Hmods.
    specialize (Htotal e r).
    generalize (mods_x _ _ Hmods He); clarify. }
  { intros; generalize (valid_rf _ _ Hvalid); intro Hrf.
    exploit Hrf; eauto; clarify; eauto. }
  { eapply lin_irrefl; eauto. }
Qed.

(* This lets us know that the only valid executions are ones in which each
   ARW reads the value written by the previous ARW.
   That should allow us to reduce the possibility space of executions to 2. *)

Lemma clos_trans_iff : forall R S (Hdom : domain R S)
  (Htrans : transitive_on R S) i j, clos_trans R i j <-> R i j.
Proof.
  split; intros; [|apply t_step; auto].
  induction H; auto.
  generalize (Hdom _ _ IHclos_trans1), (Hdom _ _ IHclos_trans2); clarify; eauto.
Qed.

Lemma total_trans : forall R (S : Ensemble event) (Htotal : total_on R S)
  e1 e2 (He1 : S e1) (He2 : S e2)
  (Hirrefl : forall e (He : S e), ~clos_trans R (id e) (id e)),
  clos_trans R (id e1) (id e2) <-> R (id e1) (id e2).
Proof.
  split; intros; [|apply t_step; auto].
  remember (id e1) as i; remember (id e2) as j; generalize dependent e2;
    generalize dependent e1; induction H; clarify.
  specialize (Htotal e1 e2); clarify.
  generalize (t_trans _ R (id e1) y (id e2)); clarify.
  specialize (Hirrefl e1); clarify.
  generalize (t_step _ R _ _ Htotal).
  generalize (t_trans _ R (id e1) (id e2) (id e1)); clarify.
Qed.  

Lemma cont_irrefl : forall R R' (S : Ensemble event) (Hcont : contained R R')
  (Hirrefl : forall e (He : S e), ~R' (id e) (id e)) e (He : S e),
  ~R (id e) (id e).
Proof.
  repeat intro.
  specialize (Hirrefl e); clarify.
Qed.

Instance event_eq : EqDec_eq event.
Proof. eq_dec_inst. Qed.

Section CS.

  Definition m := (0, 0).
  Definition x := (1, 0).
  Definition a := 0.

  Definition CS_prog := [[Lock m; Store x (I 4); Load a x; Unlock m];
    [Lock m; Store x (I 5); Load a x; Unlock m]].

  Definition sec (i1 i2 i3 i4 : nat) t v v' :=
    [{| id := i1; op := ARW t m 0 (S t)|};
     {| id := i2; op := Write t x v |};
     {| id := i3; op := Read t x v' |};
     {| id := i4; op := ARW t m (S t) 0 |}].

  Fixpoint ordered_list (R : order nat) l :=
    match l with
    | [] => True
    | x :: rest =>
        match rest with
        | [] => True
        | y :: rest' => R x y /\ ordered_list R rest
        end
    end.

  Lemma ordered_list_trans : forall R l (Horder : ordered_list R l)
    i1 i2 j1 j2 (Hlt : i1 < i2) (Hi1 : nth_error l i1 = Some j1)
    (Hi2 : nth_error l i2 = Some j2), clos_trans R j1 j2.
  Proof.
    induction l; clarsimp.
    destruct i2; [omega | destruct i1; clarify].
    - destruct l; clarsimp.
      destruct i2; clarify.
      + apply t_step; auto.
      + specialize (IHl 0 (S i2)); clarify.
        exploit IHl; eauto; intro.
        eapply t_trans; [apply t_step|]; eauto.
    - destruct l; clarsimp.
      exploit lt_S_n; eauto.
  Qed.

  (* Fudging the initial state for now. *)
  Program Definition add_init E := {| evst :=
    {| events := Add (events (evst E)) {| id := next E; op := Write 0 m 0|};
       constraints := fun i j => (i = next E /\ j < next E) \/
                                 constraints (evst E) i j |};
    next := S (next E) |}.
  Next Obligation.
    rewrite Add_spec in H; clarify.
    exploit Hnext; eauto.
  Defined.

  Lemma simple_CS : Forall (fun li => Forall simple li) CS_prog.
  Proof.
    unfold CS_prog; repeat constructor.
  Qed.

  Lemma single_dec : forall (e e' : event),
    Singleton e e' \/ ~Singleton e e'.
  Proof.
    intros; rewrite Singleton_spec; destruct (eq_dec e e'); clarify.
  Qed.

  Lemma all_t_events : forall E e, events E e <->
    t_events E (thread_of (op e)) e.
  Proof.
    unfold t_events; split; clarify.
  Qed.    

  Lemma add_events_id : forall E e l, events (evst (add_events E l)) e ->
    events (evst E) e \/ next E <= id e < next E + length l.
  Proof.
    intros.
    rewrite add_events_events, Union_spec in H; clarify.
    exploit in_make_events; eauto; clarify.
    rewrite interval_in_iff in *; auto.
  Qed.
  
  Lemma add_events_domain : forall l E
    (Hdom : domain (constraints (evst E)) (events (evst E))),
    domain (constraints (evst (add_events E l)))
           (events (evst (add_events E l))).
  Proof.
    induction l; clarify.
    apply IHl; repeat intro; clarify.
    setoid_rewrite Add_spec.
    specialize (Hdom i j); destruct H; clarify.
    - do 3 eexists; eauto.
    - exists {| id := i; op := x0 |}; do 2 eexists; eauto; split; eauto; auto.
  Qed.

  Lemma add_events_all : forall l i (Hi : i < length l),
    exists e, id e = i /\ events (evst (add_events E0 l)) e.
  Proof.
    intros.
    generalize (add_events_events l E0); intro Heq.
    exploit nth_error_succeeds; eauto; intros (c & Hc).
    exists {| id := i; op := c |}; clarify.
    rewrite Heq, Union_spec; right.
    apply (nth_error_in i); rewrite make_events_nth; clarify.
    rewrite nth_error_interval; clarify; omega.
  Qed.    

  Lemma add_init_domain : forall l
    (Hdom : domain (constraints (evst (add_events E0 l)))
      (events (evst (add_events E0 l)))),
    domain (constraints (evst (add_init (add_events E0 l))))
           (events (evst (add_init (add_events E0 l)))).
  Proof.
    repeat intro; clarify.
    setoid_rewrite Add_spec.
    specialize (Hdom i j); destruct H; clarify.
    - rewrite add_next in *; clarify.
      exploit add_events_all; eauto; intros (ej & ?).
      exists {| id := length l; op := Write 0 m 0 |}; do 2 eexists; eauto;
        clarify.
    - do 3 eexists; eauto.
  Qed.

  Lemma dom0 : domain (constraints (evst E0)) (events (evst E0)).
  Proof.
    repeat intro; clarify.
  Qed.

  Lemma ordered_list_add : forall E l
    (Horder : ordered_list (constraints (evst E)) l),
    ordered_list (constraints (evst (add_init E))) l.
  Proof.
    induction l; clarify.
    destruct l; clarify.
  Qed.

  Lemma CS_events : forall l Gr
    (Hsteps : rtc step (CS_prog, init_env) l ([[]; []], Gr))
    E (HE : E = evst (add_init (add_events E0 l))) X (Hvalid : valid E X),
    exists i1 i2 i3 i4 j1 j2 j3 j4 v0 v1,
      events E = Add (Union (set_of (sec i1 i2 i3 i4 0 4 v0))
       (set_of (sec j1 j2 j3 j4 1 5 v1))) {| id := 8; op := Write 0 m 0 |} /\
      (forall e, events E e -> id e = 8 \/ constraints E 8 (id e)) /\
      ordered_list (constraints E) [i1; i2; i3; i4] /\
      ordered_list (constraints E) [j1; j2; j3; j4] /\
       (constraints E i4 j1 \/ constraints E j4 i1).
  Proof.
    intros.
    assert (final_state ([[]; []], Gr)) as Hfinal
      by (unfold final_state; clarify).
    assert (length l = 8) as Hlen.
    { erewrite step_count_ops; eauto; clarify. }
    generalize (prog_ops Hsteps simple_CS Hfinal); intro Hmatch.
    specialize (Hmatch E0); use Hmatch.
    assert (exists i1 i2 i3 i4 v0, t_events (evst (add_events E0 l)) 0 =
      set_of (sec i1 i2 i3 i4 0 4 v0) /\
      ordered_list (constraints (evst (add_events E0 l))) [i1; i2; i3; i4])
      as (i1 & i2 & i3 & i4 & v1 & Ht0 & Hcon0).
    { specialize (Hmatch 0).
      destruct Hmatch as (lock & i1 & Hlock & ? & Hin1 & Hcon1 & Hmatch).
      destruct Hmatch as (write & i2 & Hwrite & ? & Hin2 & Hcon2 & Hmatch).
      destruct Hmatch as (read & i3 & Hread & ? & Hin3 & Hcon3 & Hmatch).
      destruct Hmatch as (unlock & i4 & Hunlock & ? & Hin4 & Hcon4 & Hmatch).
      clarify.
      destruct i1 as [|i1 [|??]]; clarify.
      destruct i2 as [|i2 [|??]]; clarify.
      destruct i3 as [|i3 [|??]]; clarify.
      destruct i4 as [|i4 [|??]]; clarify.
      exists i1, i2, i3, i4, x0.
      repeat rewrite set_of_single in *.
      setoid_rewrite Included_Minus at 1; eauto; [|apply single_dec].
      setoid_rewrite (Included_Minus
        (single_dec {| id := i2; op := Write 0 x 4 |})) at 3; auto.
      setoid_rewrite (Included_Minus
        (single_dec {| id := i3; op := Read 0 x x0 |})) at 5; auto.
      setoid_rewrite (Included_Minus
        (single_dec {| id := i4; op := ARW 0 m 1 0 |})) at 7; auto.
      rewrite Hmatch, Union_Empty; repeat rewrite Union_Single.
      split.
      - apply set_ext; intro; repeat rewrite Add_spec; rewrite Singleton_spec;
          split; clarify.
      - rewrite Incl_Single in *.
        specialize (Hcon1 {| id := i1; op := ARW 0 m 0 1 |}
          {| id := i2; op := Write 0 x 4 |}); clarify.
        specialize (Hcon2 {| id := i2; op := Write 0 x 4 |}
          {| id := i3; op := Read 0 x x0 |}); clarify.
        specialize (Hcon3 {| id := i3; op := Read 0 x x0 |}
          {| id := i4; op := ARW 0 m 1 0 |}); clarify. }
    assert (exists i1 i2 i3 i4 v0, t_events (evst (add_events E0 l)) 1 =
      set_of (sec i1 i2 i3 i4 1 5 v0) /\
      ordered_list (constraints (evst (add_events E0 l))) [i1; i2; i3; i4])
      as (j1 & j2 & j3 & j4 & v2 & Ht1 & Hcon1).
    { specialize (Hmatch 1).
      destruct Hmatch as (lock & j1 & Hlock & ? & Hin1 & Hcon1 & Hmatch).
      destruct Hmatch as (write & j2 & Hwrite & ? & Hin2 & Hcon2 & Hmatch).
      destruct Hmatch as (read & j3 & Hread & ? & Hin3 & Hcon3 & Hmatch).
      destruct Hmatch as (unlock & j4 & Hunlock & ? & Hin4 & Hcon4 & Hmatch).
      clarify.
      destruct j1 as [|j1 [|??]]; clarify.
      destruct j2 as [|j2 [|??]]; clarify.
      destruct j3 as [|j3 [|??]]; clarify.
      destruct j4 as [|j4 [|??]]; clarify.
      exists j1, j2, j3, j4, x0.
      repeat rewrite set_of_single in *.
      setoid_rewrite Included_Minus at 1; eauto; [|apply single_dec].
      setoid_rewrite (Included_Minus
        (single_dec {| id := j2; op := Write 1 x 5 |})) at 3; auto.
      setoid_rewrite (Included_Minus
        (single_dec {| id := j3; op := Read 1 x x0 |})) at 5; auto.
      setoid_rewrite (Included_Minus
        (single_dec {| id := j4; op := ARW 1 m 2 0 |})) at 7; auto.
      rewrite Hmatch, Union_Empty; repeat rewrite Union_Single.
      split.
      - apply set_ext; intro; repeat rewrite Add_spec; rewrite Singleton_spec;
          split; clarify.
      - rewrite Incl_Single in *.
        specialize (Hcon1 {| id := j1; op := ARW 1 m 0 2 |}
          {| id := j2; op := Write 1 x 5 |}); clarify.
        specialize (Hcon2 {| id := j2; op := Write 1 x 5 |}
          {| id := j3; op := Read 1 x x0 |}); clarify.
        specialize (Hcon3 {| id := j3; op := Read 1 x x0 |}
          {| id := j4; op := ARW 1 m 2 0 |}); clarify. }
    assert (events (evst (add_events E0 l)) =
    Union (set_of (sec i1 i2 i3 i4 0 4 v1)) (set_of (sec j1 j2 j3 j4 1 5 v2)))
      as Hevents.
    { apply set_ext; intro e.
      rewrite all_t_events, Union_spec; rewrite <- Ht0; rewrite <- Ht1.
      destruct (thread_of (op e)) as [| [|t]] eqn: Ht.
      - unfold t_events; split; clarify.
      - unfold t_events; split; clarify.
      - specialize (Hmatch (S (S t))); clarsimp.
        specialize (Hmatch e); unfold t_events; split; clarify. }
    exists i1, i2, i3, i4, j1, j2, j3, j4, v1, v2; clarify.
    rewrite Hevents, add_next, Hlen; clarify.
    assert (forall e, events (evst (add_events E0 l)) e -> id e < 8) as Hlt.
    { intros; exploit add_events_id; eauto; clarify; omega. }
    split.
    - intro; rewrite Add_spec; rewrite <- Hevents; intro Hin; clarify.
    - split; clarify.
      generalize (ARW_order' l eq_refl); intro Horder.
      specialize (Horder m).
      generalize (Horder {| id := i4; op := ARW 0 m 1 0 |}
        {| id := j1; op := ARW 1 m 0 2 |}); rewrite Hevents;
        repeat rewrite Union_spec; intro Hcon0.
      use Hcon0; [|split; [left|]; clarify; eauto].
      use Hcon0; eauto; clarify.
      generalize (Horder {| id := j4; op := ARW 1 m 2 0 |}
        {| id := i1; op := ARW 0 m 0 1 |}); rewrite Hevents;
        repeat rewrite Union_spec; intro Hcon1.
      use Hcon1; [|split; [right|]; clarify; eauto].
      use Hcon1; eauto; clarify.
      generalize (Horder {| id := i1; op := ARW 0 m 0 1 |}
        {| id := j1; op := ARW 1 m 0 2 |}); rewrite Hevents;
        repeat rewrite Union_spec; intro Hfirst.
      do 2 (use Hfirst; eauto); clarify.
      assert (let E := evst (add_init (add_events E0 l)) in
        total_on (constraints E) (x_events E (fst m))) as Htotal.
      { simpl; intros e1 e2 He1 He2.
        unfold x_events in He1, He2; clarify.
        rewrite Add_spec in *; clarify.
        specialize (Horder e1 e2);
          destruct He11 as [He1 | ?], He21 as [He2 | ?]; clarify.
        + use Horder; [use Horder|]; clarify.
          * rewrite Hevents, Union_spec in He2; simpl in He2.
            destruct He2 as [[? | ?] | [? | ?]]; clarify; eexists; eauto.
          * rewrite Hevents, Union_spec in He1; simpl in He1.
            destruct He1 as [[? | ?] | [? | ?]]; clarify; eexists; eauto.
        + specialize (Hlt e1); rewrite add_next, Hlen in *; clarify.
        + specialize (Hlt e2); rewrite add_next, Hlen in *; clarify. }
      assert (forall w a, events (evst (add_events E0 l)) w ->
        In a (to_seq (op w)) -> match_op 0 a 0 ->
           w = {| id := i4; op := ARW 0 m 1 0 |} \/
           w = {| id := j4; op := ARW 1 m 2 0 |}) as Hzero.
      { clear - Hevents; intros w Hw; rewrite Hevents, Union_spec in *; clarify.
        destruct H as [[? | [? | ?]] | [? | [? | ?]]]; clarify. }
      generalize (hb_trans _ _ Hvalid); intro Htrans.
      generalize (valid_hb _ _ Hvalid); intro Hcont.
      generalize (valid_full _ _ Hvalid); intros (l0 & Hlin).
      generalize (lin_irrefl Hlin); intro Hirrefl.
      generalize (add_init_domain _ (add_events_domain l _ dom0)); intro Hdom.
      assert (contained (clos_trans (constraints (evst (add_init
        (add_events E0 l))))) (full (events (evst (add_init
        (add_events E0 l)))) X)) as Hcont'.
      { repeat intro; apply t_step; unfold order_join; exploit cont_trans;
          eauto.
        exploit clos_trans_domain; eauto; clarify.
        repeat eexists; auto; left; auto. }
      generalize (cont_irrefl _  Hcont' Hirrefl); intro Hirrefl'.
      setoid_rewrite Add_spec in Hirrefl'.
      destruct Hfirst as [? | [? | ?]]; [|clarify|].
      + exploit total_read; eauto.
        { apply clos_trans_total; eauto. }
        { instantiate (1 := {| id := j1; op := ARW 1 m 0 2 |}).
          simpl; rewrite Add_spec; left.
          rewrite Hevents, Union_spec; clarify. }
        { unfold reads; simpl; eauto. }
        intros (w & a & Hw); clarify.
        rewrite Add_spec in Hw1; destruct Hw1 as [Hw1 | Hw1].
        specialize (Hzero w a); clarify; destruct Hzero; clarify.
        * generalize (t_trans _ _ _ _ i4 Hw22221); intro Hrefl.
          specialize (Hirrefl' {| id := i4; op := ARW 0 m 1 0|}); use Hrefl;
            clarify.
          apply t_step; auto.
        * generalize (t_trans _ _ _ _ j4 Hw22221); intro Hrefl.
          specialize (Hirrefl' {| id := j4; op := ARW 1 m 2 0|}); use Hrefl;
            clarify.
          eapply t_trans; [apply t_step; right; apply Hcon11|].
          eapply t_trans; apply t_step; right; eauto.
        * subst.
          specialize (Hw22222 {| id := i1; op := ARW 0 m 0 1 |} 1);
            rewrite Add_spec, Hevents, Union_spec in Hw22222; clarify.
          unfold writes in Hw22222; clarify.
          rewrite add_next, Hlen in *.
          generalize (Hlt {| id := i1; op := ARW 0 m 0 1 |}),
            (Hlt {| id := j1; op := ARW 1 m 0 2 |}); rewrite Hevents;
            repeat rewrite Union_spec; clarify.
          destruct Hw22222 as [Hcon' | Hcon']; clarify.
          { generalize (t_trans _ _ _ _ i1 Hcon'); intro Hrefl.
            specialize (Hirrefl' {| id := i1; op := ARW 0 m 0 1 |});
              rewrite Hevents, Union_spec in Hirrefl'; use Hrefl; clarify.
            apply t_step; auto. }
          { generalize (t_trans _ _ _ _ j1 Hcon'); intro Hrefl.
            specialize (Hirrefl' {| id := j1; op := ARW 1 m 0 2 |});
              rewrite Hevents, Union_spec in Hirrefl'; use Hrefl; clarify.
            apply t_step; auto. }
      + exploit total_read; eauto.
        { apply clos_trans_total; eauto. }
        { instantiate (1 := {| id := i1; op := ARW 0 m 0 1 |}).
          simpl; rewrite Add_spec; left.
          rewrite Hevents, Union_spec; clarify. }
        { unfold reads; simpl; eauto. }
        intros (w & a & Hw); clarify.
        rewrite Add_spec in Hw1; destruct Hw1 as [Hw1 | Hw1].
        specialize (Hzero w a); clarify; destruct Hzero; clarify.
        * generalize (t_trans _ _ _ _ i4 Hw22221); intro Hrefl.
          specialize (Hirrefl' {| id := i4; op := ARW 0 m 1 0|}); use Hrefl;
            clarify.
          eapply t_trans; [apply t_step; right; apply Hcon01|].
          eapply t_trans; apply t_step; right; eauto.
        * generalize (t_trans _ _ _ _ j4 Hw22221); intro Hrefl.
          specialize (Hirrefl' {| id := j4; op := ARW 1 m 2 0|}); use Hrefl;
            clarify.
          apply t_step; auto.
        * subst.
          specialize (Hw22222 {| id := j1; op := ARW 1 m 0 2 |} 2);
            rewrite Add_spec, Hevents, Union_spec in Hw22222; clarify.
          unfold writes in Hw22222; clarify.
          rewrite add_next, Hlen in *.
          generalize (Hlt {| id := i1; op := ARW 0 m 0 1 |}),
            (Hlt {| id := j1; op := ARW 1 m 0 2 |}); rewrite Hevents;
            repeat rewrite Union_spec; clarify.
          destruct Hw22222 as [Hcon' | Hcon']; clarify.
          { generalize (t_trans _ _ _ _ j1 Hcon'); intro Hrefl.
            specialize (Hirrefl' {| id := j1; op := ARW 1 m 0 2 |});
              rewrite Hevents, Union_spec in Hirrefl'; use Hrefl; clarify.
            apply t_step; auto. }
          { generalize (t_trans _ _ _ _ i1 Hcon'); intro Hrefl.
            specialize (Hirrefl' {| id := i1; op := ARW 0 m 0 1 |});
              rewrite Hevents, Union_spec in Hirrefl'; use Hrefl; clarify.
            apply t_step; auto. }
  Qed.

  Definition updates i a :=
    match i with
    | Assign b _ => b = a
    | Load b _ => b = a
    | _ => False
    end.

  Lemma step_local_same : forall t a S l S' (Hsteps : rtc step S l S')
    li (Ht : nth_error (fst S) t = Some li)
    (Hsame : Forall (fun i => ~updates i a) li), snd S' t a = snd S t a.
  Proof.
    intros ??????; induction Hsteps; clarify.
    inversion Hstep; clarify.
    generalize (nth_error_lt _ _ Hinstr); intro.
    rewrite nth_error_replace in *; auto.
    destruct (eq_dec t0 t); clarsimp.
    - specialize (IHHsteps _ eq_refl).
      inversion Hsame; clarsimp.
      inversion Hresult; unfold upd_env; clarify.
    - specialize (IHHsteps _ eq_refl); clarsimp.
      inversion Hresult; unfold upd_env; clarify.
  Qed.

  Lemma CS_read0 : forall l Gr
    (Hsteps : rtc step (CS_prog, init_env) l ([[]; []], Gr))
    E (HE : E = evst (add_init (add_events E0 l))) X (Hvalid : valid E X)
    i v (Hread : events E {| id := i; op := Read 0 x v |}),
    Gr 0 a = v.
  Proof.
    intros.
    assert (nth_error CS_prog 0 = Some ([Lock m; Store x (I 4)] ++
      Load a x :: [Unlock m])) by auto.
    exploit step_star_thread; eauto.
    { unfold final_state; clarify. }
    intros (l1 & S' & lc & G' & l2 & Hsteps1 & Hnth & Hload & Hsteps2).
    inversion Hload; clarify.
    generalize (step_local_same 0 a Hsteps21); intro Hsame; clarify.
    destruct S' as ([|??], ?); clarify.
    specialize (Hsame _ eq_refl); clarify.
    rewrite Hsame; unfold upd_env; clarify.
    exploit CS_events; eauto; intros (i1 & i2 & i3 & i4 & j1 & j2 & j3 & j4 &
      v1 & v2 & Hevents & _).
    assert (exists i, (Add (Union (set_of (sec i1 i2 i3 i4 0 4 v1))
      (set_of (sec j1 j2 j3 j4 1 5 v2))) {| id := 8; op := Write 0 m 0 |})
      {| id := i; op := Read 0 x v0 |}) as Hread'.
    { rewrite <- Hevents; exists (length l1); simpl.
      rewrite Add_spec; left.
      rewrite add_events_events, Union_spec; right.
      apply (nth_error_in (length l1)); rewrite make_events_nth; clarify.
      split; [|apply nth_error_split].
      rewrite nth_error_interval; clarify.
      clear cond; rewrite app_length in *; clarify; omega. }
    clarify.
    rewrite Add_spec, Union_spec in Hread'.
    destruct Hread' as [[? | ?] | ?]; clarify.
    inversion H; clarify.
    rewrite Hevents, Add_spec, Union_spec in Hread.
    destruct Hread as [[? | ?] | ?]; clarify.
    inversion H; clarify.
  Qed.

  Lemma CS_read1 : forall l Gr
    (Hsteps : rtc step (CS_prog, init_env) l ([[]; []], Gr))
    E (HE : E = evst (add_init (add_events E0 l))) X (Hvalid : valid E X)
    i v (Hread : events E {| id := i; op := Read 1 x v |}),
    Gr 1 a = v.
  Proof.
    intros.
    assert (nth_error CS_prog 1 = Some ([Lock m; Store x (I 5)] ++
      Load a x :: [Unlock m])) by auto.
    exploit step_star_thread; eauto.
    { unfold final_state; clarify. }
    intros (l1 & S' & lc & G' & l2 & Hsteps1 & Hnth & Hload & Hsteps2).
    inversion Hload; clarify.
    generalize (step_local_same 1 a Hsteps21); intro Hsame; clarify.
    destruct S' as ([|??], ?); clarify.
    destruct l0; clarify.
    specialize (Hsame _ eq_refl); clarify.
    rewrite Hsame; unfold upd_env; clarify.
    exploit CS_events; eauto; intros (i1 & i2 & i3 & i4 & j1 & j2 & j3 & j4 &
      v1 & v2 & Hevents & _).
    assert (exists i, (Add (Union (set_of (sec i1 i2 i3 i4 0 4 v1))
      (set_of (sec j1 j2 j3 j4 1 5 v2))) {| id := 8; op := Write 0 m 0 |})
      {| id := i; op := Read 1 x v0 |}) as Hread'.
    { rewrite <- Hevents; exists (length l1); simpl.
      rewrite Add_spec; left.
      rewrite add_events_events, Union_spec; right.
      apply (nth_error_in (length l1)); rewrite make_events_nth; clarify.
      split; [|apply nth_error_split].
      rewrite nth_error_interval; clarify.
      clear cond; rewrite app_length in *; clarify; omega. }
    clarify.
    rewrite Add_spec, Union_spec in Hread'.
    destruct Hread' as [[? | ?] | ?]; clarify.
    inversion H; clarify.
    rewrite Hevents, Add_spec, Union_spec in Hread.
    destruct Hread as [[? | ?] | ?]; clarify.
    inversion H; clarify.
  Qed.

  Opaque ordered_list.

  Lemma sec_nth : forall i1 i2 i3 i4 t v v' k e,
    nth_error (sec i1 i2 i3 i4 t v v') k = Some e ->
    nth_error [i1; i2; i3; i4] k = Some (id e).
  Proof.
    repeat (destruct k; clarify).
  Qed.

  Lemma CS_correct : forall l Gr
    (Hsteps : rtc step (CS_prog, init_env) l ([[]; []], Gr))
    X (Hvalid : valid (evst (add_init (add_events E0 l))) X),
    Gr 0 a = 4 /\ Gr 1 a = 5.
  Proof.
    intros.
    exploit CS_events; eauto; intros (i1 & i2 & i3 & i4 & j1 & j2 & j3 & j4 &
      v1 & v2 & Hevents & Hstart & Hpo0 & Hpo1 & Harw).
    assert (let E := evst (add_init (add_events E0 l)) in 
      total_on (clos_trans (constraints E)) (x_events E (fst x))).
    { intros ??? He1 He2; unfold x_events in *; clarify.
      rewrite Hevents, Add_spec, Union_spec in *.
      destruct He11 as [[He1 | He1] | ?], He21 as [[He2 | He2] | ?];
        try solve [clarify].
      - generalize (in_nth_error _ _ He1), (in_nth_error _ _ He2);
          intros (k1 & ? & Hk1) (k2 & ? & Hk2).
        destruct (lt_dec k1 k2).
        + left; eapply (ordered_list_trans _ _ Hpo0); eauto;
            eapply sec_nth; eauto.
        + destruct (eq_dec k1 k2); [subst; rewrite Hk1 in Hk2; clarify|].
          assert (k2 < k1) by omega.
          right; right; eapply (ordered_list_trans _ _ Hpo0); eauto;
            eapply sec_nth; eauto.
      - destruct Harw.
        + left.
          assert (clos_trans (fun i j =>
            i = next (add_events E0 l) /\ j < next (add_events E0 l) \/
            constraints (evst (add_events E0 l)) i j) i4 (id e2)).
          { generalize (in_nth_error _ _ He2); intros (k2 & ? & Hk2).
            destruct k2; [clarify|].
            apply (t_trans _ _ _ j1); [apply t_step; auto|].
            assert (0 < S k2) by omega.
            eapply (ordered_list_trans _ _ Hpo1); eauto; eapply sec_nth; eauto.
          }
          destruct (eq_dec (id e1) i4); [clarsimp|].
          apply (t_trans _ _ _ i4); auto.
          generalize (in_nth_error _ _ He1); intros (k1 & ? & Hk1).
          destruct (eq_dec k1 3); clarify.
          assert (k1 < 3) by omega.
          eapply (ordered_list_trans _ _ Hpo0); eauto; clarify;
            eapply sec_nth; eauto.
        + right; right.
          assert (clos_trans (fun i j =>
            i = next (add_events E0 l) /\ j < next (add_events E0 l) \/
            constraints (evst (add_events E0 l)) i j) j4 (id e1)).
          { generalize (in_nth_error _ _ He1); intros (k1 & ? & Hk1).
            destruct k1; [clarify|].
            apply (t_trans _ _ _ i1); [apply t_step; auto|].
            assert (0 < S k1) by omega.
            eapply (ordered_list_trans _ _ Hpo0); eauto; eapply sec_nth; eauto.
          }
          destruct (eq_dec (id e2) j4); [clarsimp|].
          apply (t_trans _ _ _ j4); auto.
          generalize (in_nth_error _ _ He2); intros (k2 & ? & Hk2).
          destruct (eq_dec k2 3); clarify.
          assert (k2 < 3) by omega.
          eapply (ordered_list_trans _ _ Hpo1); eauto; clarify;
            eapply sec_nth; eauto.
      - destruct Harw.
        + right; right.
          assert (clos_trans (fun i j =>
            i = next (add_events E0 l) /\ j < next (add_events E0 l) \/
            constraints (evst (add_events E0 l)) i j) i4 (id e1)).
          { generalize (in_nth_error _ _ He1); intros (k1 & ? & Hk1).
            destruct k1; [clarify|].
            apply (t_trans _ _ _ j1); [apply t_step; auto|].
            assert (0 < S k1) by omega.
            eapply (ordered_list_trans _ _ Hpo1); eauto; eapply sec_nth; eauto.
          }
          destruct (eq_dec (id e2) i4); [clarsimp|].
          apply (t_trans _ _ _ i4); auto.
          generalize (in_nth_error _ _ He2); intros (k2 & ? & Hk2).
          destruct (eq_dec k2 3); clarify.
          assert (k2 < 3) by omega.
          eapply (ordered_list_trans _ _ Hpo0); eauto; clarify;
            eapply sec_nth; eauto.
        + left.
          assert (clos_trans (fun i j =>
            i = next (add_events E0 l) /\ j < next (add_events E0 l) \/
            constraints (evst (add_events E0 l)) i j) j4 (id e2)).
          { generalize (in_nth_error _ _ He2); intros (k2 & ? & Hk2).
            destruct k2; [clarify|].
            apply (t_trans _ _ _ i1); [apply t_step; auto|].
            assert (0 < S k2) by omega.
            eapply (ordered_list_trans _ _ Hpo0); eauto; eapply sec_nth; eauto.
          }
          destruct (eq_dec (id e1) j4); [clarsimp|].
          apply (t_trans _ _ _ j4); auto.
          generalize (in_nth_error _ _ He1); intros (k1 & ? & Hk1).
          destruct (eq_dec k1 3); clarify.
          assert (k1 < 3) by omega.
          eapply (ordered_list_trans _ _ Hpo1); eauto; clarify;
            eapply sec_nth; eauto.
      - generalize (in_nth_error _ _ He1), (in_nth_error _ _ He2);
          intros (k1 & ? & Hk1) (k2 & ? & Hk2).
        destruct (lt_dec k1 k2).
        + left; eapply (ordered_list_trans _ _ Hpo1); eauto;
            eapply sec_nth; eauto.
        + destruct (eq_dec k1 k2); [subst; rewrite Hk1 in Hk2; clarify|].
          assert (k2 < k1) by omega.
          right; right; eapply (ordered_list_trans _ _ Hpo1); eauto;
            eapply sec_nth; eauto. }
    generalize (add_init_domain _ (add_events_domain l _ dom0)); intro Hdom.
    assert (forall w a v (Hw : events (evst (add_init (add_events E0 l))) w)
      (Ha : In a (to_seq (op w))) (Hx : op_modifies _ a x = true)
      (Hv : match_op 0 a v), w = {| id := i2; op := Write 0 x 4 |} \/
         w = {| id := j2; op := Write 1 x 5 |}) as Hwrite.
    { intros.
      rewrite Hevents, Add_spec, Union_spec in Hw;
        destruct Hw as [[[? | [? | [? | ?]]] | [? | [? | [? | ?]]]] | ?];
        clarify. }
      generalize (hb_trans _ _ Hvalid); intro Htrans.
      generalize (valid_hb _ _ Hvalid); intro Hcont.
      generalize (valid_full _ _ Hvalid); intros (l0 & Hlin).
      generalize (lin_irrefl Hlin); intro Hirrefl.
      assert (contained (clos_trans (constraints (evst (add_init
        (add_events E0 l))))) (full (events (evst (add_init
        (add_events E0 l)))) X)) as Hcont'.
      { repeat intro; apply t_step.
        exploit clos_trans_domain; eauto; clarify.
        repeat eexists; auto; left; auto.
        eapply cont_trans; eauto. }
      generalize (cont_irrefl _  Hcont' Hirrefl); intro Hirrefl'.
    assert (v1 = 4).
    { exploit total_read; eauto.
      { instantiate (1 := {| id := i3; op := Read 0 x v1 |});
          rewrite Hevents, Add_spec, Union_spec; left; clarify. }
      { unfold reads; simpl; eauto. }
      intros (w & a & Hw).
      specialize (Hwrite w a v1); clarify.
      unfold writes in Hw21; destruct Hwrite; clarify.
      specialize (Hw22222 {| id := i2; op := Write 0 x 4 |} 4).
      rewrite Hevents, Add_spec, Union_spec in Hw22222;
        unfold writes in Hw22222; clarify.
      destruct Hw22222 as [Hword | Hword]; clarify.
      - destruct Harw as [Harw | Harw].
        + generalize (t_trans _ _ _ _ j2 Hw22221); intro Hrefl.
          specialize (Hirrefl' {| id := j2; op := Write 1 x 5 |});
            rewrite Hevents, Add_spec, Union_spec in Hirrefl'; use Hrefl;
            clarify.
          Transparent ordered_list.
          apply (t_trans _ _ _ i4); [|apply (t_trans _ _ _ j1)];
            apply t_step; clarify.
          Opaque ordered_list.
        + generalize (t_trans _ _ _ _ i2 Hword); intro Hrefl.
          specialize (Hirrefl' {| id := i2; op := Write 0 x 4 |});
            rewrite Hevents, Add_spec, Union_spec in Hirrefl'; use Hrefl;
            clarify.
          Transparent ordered_list.
          apply (t_trans _ _ _ j4); [apply (t_trans _ _ _ j3) |
            apply (t_trans _ _ _ i1)]; apply t_step; clarify.
          Opaque ordered_list.
      - generalize (t_trans _ _ _ _ i3 Hword); intro Hrefl.
        specialize (Hirrefl' {| id := i3; op := Read 0 x 5 |});
          rewrite Hevents, Add_spec, Union_spec in Hirrefl'; use Hrefl;
          clarify.
        use Hirrefl'; clarify.
        + left; clarify.
        + Transparent ordered_list.
          apply t_step; clarify. }
    Opaque ordered_list.
    assert (v2 = 5).
    { exploit total_read; eauto.
      { instantiate (1 := {| id := j3; op := Read 1 x v2 |});
          rewrite Hevents, Add_spec, Union_spec; left; clarify. }
      { unfold reads; simpl; eauto. }
      intros (w & a & Hw).
      specialize (Hwrite w a v2); clarify.
      destruct Hwrite; clarify.
      specialize (Hw22222 {| id := j2; op := Write 1 x 5 |} 5).
      rewrite Hevents, Add_spec, Union_spec in Hw22222;
        unfold writes in Hw22222; clarify.
      destruct Hw22222 as [Hword | Hword]; clarify.
      - destruct Harw as [Harw | Harw].
        + generalize (t_trans _ _ _ _ j2 Hword); intro Hrefl.
          specialize (Hirrefl' {| id := j2; op := Write 1 x 5 |});
            rewrite Hevents, Add_spec, Union_spec in Hirrefl'; use Hrefl;
            clarify.
          Transparent ordered_list.
          apply (t_trans _ _ _ i4); [apply (t_trans _ _ _ i3) |
            apply (t_trans _ _ _ j1)]; apply t_step; clarify.
          Opaque ordered_list.
        + generalize (t_trans _ _ _ _ i2 Hw22221); intro Hrefl.
          specialize (Hirrefl' {| id := i2; op := Write 0 x 4 |});
            rewrite Hevents, Add_spec, Union_spec in Hirrefl'; use Hrefl;
            clarify.
          Transparent ordered_list.
          apply (t_trans _ _ _ j4); [|apply (t_trans _ _ _ i1)];
            apply t_step; clarify.
          Opaque ordered_list.
      - generalize (t_trans _ _ _ _ j3 Hword); intro Hrefl.
        specialize (Hirrefl' {| id := j3; op := Read 1 x 4 |});
          rewrite Hevents, Add_spec, Union_spec in Hirrefl'; use Hrefl;
          clarify.
        use Hirrefl'; clarify.
        + left; clarify.
        + Transparent ordered_list.
          apply t_step; clarify. }
    clear Hpo0 Hpo1; subst.
    split; [eapply CS_read0 | eapply CS_read1]; eauto.
    - rewrite Hevents, Add_spec, Union_spec.
      left; clarify.
    - rewrite Hevents, Add_spec, Union_spec.
      left; clarify.
  Qed.

End CS.

Lemma add_events_inj : forall l E (Hinj : forall e1 e2
  (He1 : events (evst E) e1) (He2 : events (evst E) e2) (Hid : id e1 = id e2),
    e1 = e2) e1 e2
  (He1 : events (evst (add_events E l)) e1)
  (He2 : events (evst (add_events E l)) e2) (Hid : id e1 = id e2), e1 = e2.
Proof.
  intros.
  rewrite add_events_events, Union_spec in *;
    destruct He1 as [? | He1], He2 as [? | He2]; auto.
  - exploit in_make_events; eauto; clarify.
    rewrite interval_in_iff in *.
    exploit Hnext; eauto; omega.
  - exploit in_make_events; eauto; clarify.
    rewrite interval_in_iff in *.
    exploit Hnext; eauto; omega.
  - generalize (in_nth_error _ _ He1), (in_nth_error _ _ He2);
      intros (i1 & ? & Hi1) (i2 & ? & Hi2).
    rewrite make_events_nth, nth_error_interval in *; clarify.
    assert (i1 = i2) as Heq by omega; rewrite Heq in *.
    rewrite Hi12 in *; destruct e1, e2; clarify.
Qed.

Section Barrier.

  Definition barrier_prog := [[Store x (I 4); Signal m];
    [Store x (I 5); Wait m; Load a x]].

  Lemma simple_barrier : Forall (fun li => Forall simple li) barrier_prog.
  Proof.
    unfold barrier_prog; repeat constructor.
  Qed.

  Lemma barrier_events : forall l Gr
    (Hsteps : rtc step (barrier_prog, init_env) l ([[]; []], Gr))
    E (HE : E = evst (add_init (add_events E0 l))) X (Hvalid : valid E X),
    exists i1 i2 j1 j2 j3 v, events (evst (add_events E0 l)) = set_of
     [{| id := i1; op := Write 0 x 4 |}; {| id := i2; op := ARW 0 m 0 1 |};
      {| id := j1; op := Write 1 x 5 |}; {| id := j2; op := ARW 1 m 1 0 |};
      {| id := j3; op := Read 1 x v |}] /\
     NoDup [i1; i2; j1; j2; j3; 5] /\
     (forall e (He : events E e), id e = 5 \/ constraints E 5 (id e)) /\
     ordered_list (constraints E) [i1; i2] /\
     ordered_list (constraints E) [j1; j2; j3] /\
     constraints E i2 j2.
  Proof.
    intros.
    assert (final_state ([[]; []], Gr)) as Hfinal
      by (unfold final_state; clarify).
    assert (length l = 5) as Hlen.
    { erewrite step_count_ops; eauto; clarify. }
    generalize (prog_ops Hsteps simple_barrier Hfinal); intro Hmatch.
    specialize (Hmatch E0); use Hmatch.
    assert (exists i1 i2, t_events (evst (add_events E0 l)) 0 =
      set_of [{| id := i1; op := Write 0 x 4 |};
              {| id := i2; op := ARW 0 m 0 1 |}] /\
      ordered_list (constraints (evst (add_events E0 l))) [i1; i2])
      as (i1 & i2 & Ht0 & Hcon0).
    { specialize (Hmatch 0).
      destruct Hmatch as (write & i1 & Hwrite & ? & Hin1 & Hcon1 & Hmatch).
      destruct Hmatch as (signal & i2 & Hsignal & ? & Hin2 & Hcon2 & Hmatch).
      clarify.
      destruct i1 as [|i1 [|??]]; clarify.
      destruct i2 as [|i2 [|??]]; clarify.
      exists i1, i2.
      repeat rewrite set_of_single in *.
      setoid_rewrite Included_Minus at 1; eauto; [|apply single_dec].
      setoid_rewrite (Included_Minus
        (single_dec {| id := i2; op := ARW 0 m 0 1 |})) at 3; auto.
      rewrite Hmatch, Union_Empty; repeat rewrite Union_Single.
      split; clarify.
      - apply set_ext; intro; repeat rewrite Add_spec; rewrite Singleton_spec;
          split; clarify.
      - rewrite Incl_Single in *.
        specialize (Hcon1 _ {| id := i2; op := ARW 0 m 0 1 |}
                          (or_introl eq_refl)); clarify. }
    assert (exists j1 j2 j3 v, t_events (evst (add_events E0 l)) 1 =
      set_of [{| id := j1; op := Write 1 x 5 |};
              {| id := j2; op := ARW 1 m 1 0 |};
              {| id := j3; op := Read 1 x v |}] /\
      ordered_list (constraints (evst (add_events E0 l))) [j1; j2; j3])
      as (j1 & j2 & j3 & v & Ht1 & Hcon1).
    { specialize (Hmatch 1).
      destruct Hmatch as (write & j1 & Hwrite & ? & Hin1 & Hcon1 & Hmatch).
      destruct Hmatch as (wait & j2 & Hwait & ? & Hin2 & Hcon2 & Hmatch).
      destruct Hmatch as (read & j3 & Hread & ? & Hin3 & Hcon3 & Hmatch).
      clarify.
      destruct j1 as [|j1 [|??]]; clarify.
      destruct j2 as [|j2 [|??]]; clarify.
      destruct j3 as [|j3 [|??]]; clarify.
      exists j1, j2, j3, x0.
      repeat rewrite set_of_single in *.
      setoid_rewrite Included_Minus at 1; eauto; [|apply single_dec].
      setoid_rewrite (Included_Minus
        (single_dec {| id := j2; op := ARW 1 m 1 0 |})) at 3; auto.
      setoid_rewrite (Included_Minus
        (single_dec {| id := j3; op := Read 1 x x0 |})) at 5; auto.
      rewrite Hmatch, Union_Empty; repeat rewrite Union_Single.
      split.
      - apply set_ext; intro; repeat rewrite Add_spec; rewrite Singleton_spec;
          split; clarify.
      - rewrite Incl_Single in *.
        specialize (Hcon1 _ {| id := j2; op := ARW 1 m 1 0 |}
                          (or_introl eq_refl)); clarify.
        specialize (Hcon2 _ {| id := j3; op := Read 1 x x0 |}
                          (or_introl eq_refl)); clarify. }
    assert (events (evst (add_events E0 l)) =
    Union (set_of [{| id := i1; op := Write 0 x 4 |};
          {| id := i2; op := ARW 0 m 0 1 |}])
          (set_of [{| id := j1; op := Write 1 x 5 |};
          {| id := j2; op := ARW 1 m 1 0 |};
          {| id := j3; op := Read 1 x v |}])) as Hevents.
    { apply set_ext; intro e.
      rewrite all_t_events, Union_spec; rewrite <- Ht0; rewrite <- Ht1.
      destruct (thread_of (op e)) as [| [|t]] eqn: Ht.
      - unfold t_events; split; clarify.
      - unfold t_events; split; clarify.
      - specialize (Hmatch (S (S t))); clarsimp.
        specialize (Hmatch e); unfold t_events; split; clarify. }
    exists i1, i2, j1, j2, j3, v; clarify.
    rewrite Hevents, add_next, Hlen; clarify.
    split.
    { apply set_ext; intro; rewrite Union_spec; split; clarify. }
    assert (forall e, events (evst (add_events E0 l)) e -> id e < 5) as Hlt.
    { intros; exploit add_events_id; eauto; clarify; omega. }
    split; [|split].
    - rewrite Hevents in Hlt; setoid_rewrite Union_spec in Hlt.
      generalize (Hlt {| id := i1; op := Write 0 x 4 |}),
        (Hlt {| id := i2; op := ARW 0 m 0 1 |}),
        (Hlt {| id := j1; op := Write 1 x 5 |}),
        (Hlt {| id := j2; op := ARW 1 m 1 0 |}),
        (Hlt {| id := j3; op := Read 1 x v |}); clarify.
      repeat constructor; clarify; intro;
        repeat match goal with H : ?P \/ ?Q |- _ => destruct H end; try omega.
      + exploit (add_events_inj l E0); try rewrite Hevents, Union_spec.
        { clarify. }
        { left; simpl; left; eauto. }
        { left; simpl; right; eauto. }
        { auto. }
        clarify.
      + exploit (add_events_inj l E0); try rewrite Hevents, Union_spec.
        { clarify. }
        { left; simpl; left; eauto. }
        { right; simpl; left; eauto. }
        { auto. }
        clarify.
      + exploit (add_events_inj l E0); try rewrite Hevents, Union_spec.
        { clarify. }
        { left; simpl; left; eauto. }
        { right; simpl; right; left; eauto. }
        { auto. }
        clarify.
      + exploit (add_events_inj l E0); try rewrite Hevents, Union_spec.
        { clarify. }
        { left; simpl; left; eauto. }
        { right; simpl; right; eauto. }
        { auto. }
        clarify.
      + exploit (add_events_inj l E0); try rewrite Hevents, Union_spec.
        { clarify. }
        { left; simpl; right; eauto. }
        { right; simpl; left; eauto. }
        { auto. }
        clarify.
      + exploit (add_events_inj l E0); try rewrite Hevents, Union_spec.
        { clarify. }
        { left; simpl; right; eauto. }
        { right; simpl; right; left; eauto. }
        { auto. }
        clarify.
      + exploit (add_events_inj l E0); try rewrite Hevents, Union_spec.
        { clarify. }
        { left; simpl; right; eauto. }
        { right; simpl; right; eauto. }
        { auto. }
        clarify.
      + exploit (add_events_inj l E0); try rewrite Hevents, Union_spec.
        { clarify. }
        { right; simpl; left; eauto. }
        { right; simpl; right; left; eauto. }
        { auto. }
        clarify.
      + exploit (add_events_inj l E0); try rewrite Hevents, Union_spec.
        { clarify. }
        { right; simpl; left; eauto. }
        { right; simpl; right; eauto. }
        { auto. }
        clarify.
      + exploit (add_events_inj l E0); try rewrite Hevents, Union_spec.
        { clarify. }
        { right; simpl; right; left; eauto. }
        { right; simpl; right; eauto. }
        { auto. }
        clarify.
    - intro; rewrite Add_spec; rewrite <- Hevents; intro Hin; clarify.
    - split; clarify.
      generalize (ARW_order' l eq_refl); intro Horder.
      specialize (Horder m).
      generalize (Horder {| id := i2; op := ARW 0 m 0 1 |}
        {| id := j2; op := ARW 1 m 1 0 |}); rewrite Hevents;
        repeat rewrite Union_spec; intro Hcon0; do 2 (use Hcon0; [|eauto]).
      clarify.
      assert (let E := evst (add_init (add_events E0 l)) in
        total_on (constraints E) (x_events E (fst m))) as Htotal.
      { simpl; intros e1 e2 He1 He2.
        unfold x_events in He1, He2; clarify.
        rewrite Add_spec in *; clarify.
        specialize (Horder e1 e2);
          destruct He11 as [He1 | ?], He21 as [He2 | ?]; clarify.
        + use Horder; [use Horder|]; clarify.
          * rewrite Hevents, Union_spec in He2; simpl in He2.
            destruct He2 as [[? | ?] | [? | ?]]; clarify; eexists; eauto.
          * rewrite Hevents, Union_spec in He1; simpl in He1.
            destruct He1 as [[? | ?] | [? | ?]]; clarify; eexists; eauto.
        + specialize (Hlt e1); rewrite add_next, Hlen in *; clarify.
        + specialize (Hlt e2); rewrite add_next, Hlen in *; clarify. }
      assert (forall w a, events (evst (add_events E0 l)) w ->
        In a (to_seq (op w)) -> match_op 0 a 1 ->
           w = {| id := i2; op := ARW 0 m 0 1 |}) as Hone.
      { clear - Hevents; intros w Hw; rewrite Hevents, Union_spec in *; clarify.
        destruct H as [[? | [? | ?]] | [? | [? | ?]]]; clarify. }
      generalize (hb_trans _ _ Hvalid); intro Htrans.
      generalize (valid_hb _ _ Hvalid); intro Hcont.
      generalize (valid_full _ _ Hvalid); intros (l0 & Hlin).
      generalize (lin_irrefl Hlin); intro Hirrefl.
      generalize (add_init_domain _ (add_events_domain l _ dom0)); intro Hdom.
      assert (contained (clos_trans (constraints (evst (add_init
        (add_events E0 l))))) (full (events (evst (add_init 
        (add_events E0 l)))) X)) as Hcont'.
      { repeat intro; apply t_step.
        exploit clos_trans_domain; eauto; clarify.
        repeat eexists; auto; left; auto.
        eapply cont_trans; eauto. }
      generalize (cont_irrefl _  Hcont' Hirrefl); intro Hirrefl'.
      setoid_rewrite Add_spec in Hirrefl'.
      exploit total_read; eauto.
      { apply clos_trans_total; eauto. }
      { instantiate (1 := {| id := j2; op := ARW 1 m 1 0 |}).
        simpl; rewrite Add_spec; left.
        rewrite Hevents, Union_spec; clarify. }
      { unfold reads; simpl; eauto. }
      intros (w & a & Hw); clarify.
      rewrite Add_spec in Hw1; destruct Hw1 as [Hw1 | Hw1]; clarify.
      specialize (Hone w a); clarify.
      generalize (t_trans _ _ _ _ i2 Hw22221); intro Hrefl.
      specialize (Hirrefl' {| id := i2; op := ARW 0 m 0 1|}); use Hrefl;
        clarify.
      apply t_step; auto.
  Qed.

  Corollary barrier_before : forall l Gr
    (Hsteps : rtc step (barrier_prog, init_env) l ([[]; []], Gr))
    E (HE : E = evst (add_init (add_events E0 l))) X (Hvalid : valid E X),
    exists i1 i2 j1 j2 j3 v, events (evst (add_events E0 l)) = set_of
     [{| id := i1; op := Write 0 x 4 |}; {| id := i2; op := ARW 0 m 0 1 |};
      {| id := j1; op := Write 1 x 5 |}; {| id := j2; op := ARW 1 m 1 0 |};
      {| id := j3; op := Read 1 x v |}] /\ NoDup [i1; i2; j1; j2; j3; 5] /\
     (forall e (He : events E e), id e = j3 \/
        clos_trans (constraints E) (id e) j3).
  Proof.
    intros.
    exploit barrier_events; eauto; intros (i1 & i2 & j1 & j2 & j3 & v & Hevents
      & Hnodup & Hcon).
    repeat eexists; eauto; intros.
    assert (final_state ([[]; []], Gr)) as Hfinal.
    { unfold final_state; clarify. }
    assert (length l = 5) as Hlen.
    { erewrite step_count_ops; eauto; clarify. }
    assert (forall e, events (evst (add_events E0 l)) e -> id e < 5) as Hlt.
    { intros; exploit add_events_id; eauto; clarify; omega. }
    assert (events (evst (add_events E0 l)) {| id := j3; op := Read 1 x v |})
      as Hr.
    { rewrite Hevents; right; clarify. }
    clarify; set (E := (evst (add_init (add_events E0 l)))).
    assert (clos_trans (constraints E) i2 j3).
    { apply (t_trans _ _ _ j2); apply t_step; auto. }
    clarify; rewrite Add_spec, Hevents in He; simpl in He.
    destruct He as [[? | [? | [? | [? | ?]]]] | ?]; clarify;
      right.
    - eapply t_trans; eauto; apply t_step; auto.
    - apply (t_trans _ _ _ j2); apply t_step; auto.
    - apply t_step; auto.
    - apply t_step; left.
      rewrite add_next, Hlen in *.
      specialize (Hlt _ Hr); auto.
  Qed.

  Lemma barrier_read : forall l Gr
    (Hsteps : rtc step (barrier_prog, init_env) l ([[]; []], Gr))
    E (HE : E = evst (add_init (add_events E0 l))) X (Hvalid : valid E X)
    i v (Hread : events E {| id := i; op := Read 1 x v |}),
    Gr 1 a = v.
  Proof.
    intros.
    assert (nth_error barrier_prog 1 = Some ([Store x (I 5); Wait m] ++
      [Load a x])) by auto.
    exploit step_star_thread; eauto.
    { unfold final_state; clarify. }
    intros (l1 & S' & lc & G' & l2 & Hsteps1 & Hnth & Hload & Hsteps2).
    inversion Hload; clarify.
    generalize (step_local_same 1 a Hsteps21); intro Hsame; clarify.
    destruct S' as ([|??], ?); clarify.
    destruct l0; clarify.
    specialize (Hsame _ eq_refl); clarify.
    rewrite Hsame; unfold upd_env; clarify.
    exploit barrier_events; eauto; intros (i1 & i2 & j1 & j2 & j3 & v' &
      Hevents & _).
    assert (exists i, (Add (set_of [{| id := i1; op := Write 0 x 4 |};
              {| id := i2; op := ARW 0 m 0 1 |};
              {| id := j1; op := Write 1 x 5 |};
              {| id := j2; op := ARW 1 m 1 0 |};
              {| id := j3; op := Read 1 x v' |}])
              {| id := 8; op := Write 0 m 0 |})
             {| id := i; op := Read 1 x v0 |}) as Hread'.
    { rewrite <- Hevents; exists (length l1); simpl.
      rewrite Add_spec; left.
      rewrite add_events_events, Union_spec; right.
      apply (nth_error_in (length l1)); rewrite make_events_nth; clarify.
      split; [|apply nth_error_split].
      rewrite nth_error_interval; clarify.
      clear cond; rewrite app_length in *; clarify; omega. }
    clarify.
    rewrite Add_spec in Hread'.
    destruct Hread' as [[? | ?] | ?]; clarify.
    inversion H; clarify.
    rewrite Add_spec, Hevents in Hread.
    destruct Hread as [[? | ?] | ?]; clarify.
    inversion H; clarify.
  Qed.

  Lemma barrier_correct : forall l Gr
    (Hsteps : rtc step (barrier_prog, init_env) l ([[]; []], Gr))
    X (Hvalid : valid (evst (add_init (add_events E0 l))) X),
    Gr 1 a = 4 \/ Gr 1 a = 5.
  Proof.
    intros.
    exploit barrier_before; eauto; intros (i1 & i2 & j1 & j2 & j3 & v & Hevents
      & Hnodup & Hbefore).
    set (E := evst (add_init (add_events E0 l))).
    set (r := {| id := j3; op := Read 1 x v |}).
    destruct (drop_b_reads (fst x) E ([r], X)) as (ops, X') eqn: Hdrop.
      generalize (hb_trans _ _ Hvalid); intro Htrans.
      generalize (valid_hb _ _ Hvalid); intro Hcont.
      generalize (valid_full _ _ Hvalid); intros (l0 & Hlin).
      generalize (lin_irrefl Hlin); intro Hirrefl.
      generalize (add_init_domain _ (add_events_domain l _ dom0)); intro Hdom.
      assert (contained (clos_trans (constraints (evst (add_init
        (add_events E0 l))))) (full (events (evst (add_init
        (add_events E0 l)))) X)) as Hcont'.
      { repeat intro; apply t_step.
        exploit clos_trans_domain; eauto; clarify.
        repeat eexists; auto; left; auto.
        eapply cont_trans; eauto. }
      generalize (cont_irrefl _  Hcont' Hirrefl); intro Hirrefl'.
    assert (final_state ([[]; []], Gr)) as Hfinal.
    { unfold final_state; clarify. }
    assert (length l = 5) as Hlen.
    { erewrite step_count_ops; eauto; clarify. }
    assert (events E r) as Hr.
    { setoid_rewrite Add_spec; rewrite Hevents; left; right; clarify. }
    exploit barrier_read; eauto; intro.
    generalize (full_lin Hlin); intros (? & _).
    exploit (before_lin_hb(conc_op := conc_op) eq_nat_dec); eauto;
      intros (m1 & m2 & Hm1 & Hm2).
    rewrite private_seq_1 in Hvalid; eauto.
    destruct Hvalid as (Hvalid & Hcon); subst r; clarify.
    unfold x in Hcon; exploit Hcon.
    { unfold reads; simpl; eauto.  }
    destruct (find (fun e => if find (fun a => op_modifies _ a (1, 0))
      (to_seq (op e)) then true else false) (rev m1)) eqn: Hfind;
      setoid_rewrite Hfind; [intros (? & a' & Hlast & Ha') | clarify].
    generalize (last_op_in _ Hlast); intro Hwrite.
    generalize (last_op_mods Hlast); intro.
    exploit find_success; eauto; rewrite <- in_rev, <- (lin_set Hm1);
      unfold before; intros ((Hin & _) & _).
    rewrite Add_spec, Hevents in Hin;
      destruct Hin as [[? | [? | [? | [? | ?]]]] | ?]; clarify.
    - apply valid_wf; auto.
    - intros ?? He ?.
      specialize (Hbefore e); clarify.
      rewrite Add_spec in *; clarify.
      destruct Hbefore; clarify.
      + rewrite add_next, Hlen in *; destruct He; clarify.
        * exploit (add_events_inj l E0).
          { clarify. }
          { eauto. }
          { apply Hr. }
          { auto. }
          auto.
        * subst r; clarify.
          generalize (NoDup_inj(x := 5) 4 5 Hnodup); clarify.
      + exploit cont_trans; eauto.
    - admit.
    - eapply lin_irrefl; eauto.
  Qed.

End Barrier.

End Examples.