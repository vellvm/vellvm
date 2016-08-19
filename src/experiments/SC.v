Require Import CpdtTactics.
Require Import Util.
Require Import ZArith.
Require Import String.
Require Import List.
Require Import memory_model.
Require Import Morphisms.
Import ListNotations.
Import Bool.
Import CoqEqDec.

Set Implicit Arguments.
(* Ask Dmitri about barbed simulation *)

Lemma forall_trivial : forall {A} (l : list A), Forall (fun _ => True) l.
Proof. induction l; auto. Qed.
Hint Resolve forall_trivial.

(* SC, the simplest concurrency model, simply passes operations on to the memory layout. *)
Section SC.
  Context `(ML : Memory_Layout).
  Context (thread : Type).

  Definition to_ops_SC (a : access thread loc val concrete_ptr) := match a with
  | Read _ l v => [MRead l v]
  | Write _ l v => [MWrite l v]
  | ARW _ l v v' => [MRead l v; MWrite l v']
  | Alloc _ l => [MAlloc l]
  | Free _ l => [MFree l]
  | Cast _ l p => [MCast l p]
  end.

  Definition run_op_SC (m : mem) a := do_ops m (to_ops_SC a).
  Definition apply_access_SC m a m' := run_op_SC m a = Some m'.
  Hint Unfold run_op_SC apply_access_SC.

  Instance SC_base : Memory_Model_Base thread loc val concrete_ptr mem := 
  { apply_access := apply_access_SC; initial_mem := init_mem(Memory_Layout := ML) }.

  Lemma diff_loc_run : forall m m' a a' (Hdiff_loc : get_loc a' <> get_loc a)
    (Hrun : run_op_SC m a' = Some m') (Hnot_cast : is_cast a = false),
    (exists m2, run_op_SC m a = Some m2) <-> (exists m2, run_op_SC m' a = Some m2).
  Proof.
    autounfold; intros.
    generalize (loc_indep_ops(ops := to_ops_SC a) _ _ Hrun); unfold can_do_ops; intro X.
    use X. use X.
    - repeat (rewrite exists_not_None); auto.
    - destruct a; clarify.
    - destruct a; destruct a'; simpl; repeat constructor; try intro; clarify.
  Qed.

  Lemma diff_loc : forall m (a a' : access thread loc val concrete_ptr) m'
    (Hdiff_loc : get_loc a' <> get_loc a) (Happly : apply_access' m a' m')
    (Hnot_cast : is_cast a = false), can_do m a <-> can_do m' a.
  Proof.
    intros; inversion Happly.
    repeat (rewrite can_do_apply_iff); simpl; eapply diff_loc_run; eauto.
  Qed.

  Lemma do_rw : forall m m' l v v' (P : mem_op loc val concrete_ptr -> Prop)
    (Hcan_do : forall op, P op -> (can_do_op m op <-> can_do_op m' op)),
    P (MRead l v) -> P (MWrite l v') -> 
    (can_do_ops m [MRead l v; MWrite l v'] <-> can_do_ops m' [MRead l v; MWrite l v']).
  Proof.
    unfold can_do_ops; clarify.
    generalize (Hcan_do (MRead l v)); unfold can_do_op; destruct (do_op m (MRead l v)) eqn: read; 
      destruct (do_op m' (MRead l v)) eqn: read'; clarify; try (destruct H1; clarify; fail).
    specialize (Hcan_do (MWrite l v')); generalize (read_noop _ _ _ (MWrite l v') read);
      generalize (read_noop _ _ _ (MWrite l v') read'); crush.
  Qed.

  Lemma can_op : forall m m' a (P : mem_op loc val concrete_ptr -> Prop)
    (Hcan_do : forall op, P op -> (can_do_op (mrep m) op <-> can_do_op (mrep m') op)),
    Forall P (to_ops_SC a) -> (can_do m a <-> can_do m' a).
  Proof.
    intros; repeat (rewrite can_do_apply_iff); simpl; repeat autounfold.
    repeat (rewrite exists_not_None); clarify.
    destruct (to_ops_SC a) as [| op rest] eqn: ops; [destruct a; clarify |].
    inversion H; destruct rest; [repeat (rewrite do_one_op_iff); eauto | destruct a; clarify].
    inversion H3; eapply do_rw; eauto.
  Qed.

  Lemma read_noop : forall m t l v m' a (Hread : apply_access' m (Read t l v) m'),
    can_do m a <-> can_do m' a.
  Proof.
    intros; inversion Hread; simpl in *; apply (can_op(P := fun _ => True) _ _ _); auto.
    repeat autounfold in *; clarify.
    eapply read_noop; eauto.
  Qed.

  Lemma cast_noop : forall m t l p m' a (Hcast : apply_access' m (Cast t l p) m')
    (Hnot_cast : is_cast a = false), can_do m a <-> can_do m' a.
  Proof.
    intros; inversion Hcast; simpl in *; apply (can_op(P := fun op => is_mcast op = false) _ _ _).
    - clear Hcast0; repeat autounfold in *; clarify.
      eapply cast_noop; eauto.
    - destruct a; clarify.
  Qed.

  Lemma reads_first : forall a l, reads a l = true -> exists v rest, to_ops_SC a = MRead l v :: rest.
  Proof. destruct a; clarify; eauto. Qed.

  Lemma writes_val_last : forall a l v (Hwrites_val : writes_val Val a l v = true) m m'
    (Hops : do_ops m (to_ops_SC a) = Some m'),
    exists rest m0, to_ops_SC a = rest ++ [MWrite l v] /\ do_ops m rest = Some m0 /\
      do_op m0 (MWrite l v) = Some m'.
  Proof.
    destruct a; clarify.
    - exists []; eexists; clarify.
    - exists [MRead l v]; eexists; repeat (split; eauto; clarify).
  Qed.

  Lemma read_written : forall m l v a m' a' (Hwrites : writes_val Val a l v = true) (Happly : apply_access' m a m')
    (Hread : reads a' l = true), can_do m' a' <-> reads_val Val a' l v = true.
  Proof.
    intros; inversion Happly; simpl in *.
    rewrite can_do_apply_iff; simpl; repeat autounfold in *; simpl.
    generalize (reads_first _ _ Hread); clarify.
    rewrite H; simpl.
    generalize (writes_val_last _ _ _ Hwrites _ Happly0); intros [rest [m0 [ops [do_rest write]]]].
    generalize (read_written _ _ _ x write); intros [H1 H2].
    destruct (eq_dec x v); rewrite <- exists_not_None in H2; clarify.
    - destruct a'; clarify.
      + split; eauto; clarify.
      + split; auto; rewrite exists_not_None; destruct a; clarify.
        * destruct rest; [| destruct rest]; clarify.
          generalize (memory_model.read_noop _ _ _ (MWrite l0 v1) H0); intro H;
            rewrite <- H.
          generalize (write_not_read _ _ Happly0); intro X.
          specialize (X (MWrite l0 v1)); use X; rewrite <- X.
          rewrite <- (write_any_value _ _ v0); rewrite Happly0; clarify.
        * destruct rest; clarify; destruct rest; [| destruct rest]; clarify.
          generalize (memory_model.read_noop _ _ _ (MWrite l0 v1) H0); intro X;
            rewrite <- X; clear X.
          generalize (write_not_read _ _ H4); intro X.
          specialize (X (MWrite l0 v1)); use X; rewrite <- X.
          rewrite <- (write_any_value _ _ v2); rewrite H4; clarify.
    - destruct (do_op (mrep m') (MRead l x)); clarify.
      destruct a'; clarify; split; clarify.
  Qed.
  
  Lemma not_mod_op : forall a l, modifies a l = false -> 
    Forall (fun op => op_modifies _ op l = false) (to_ops_SC a).
  Proof. intros; destruct a; clarify. Qed.

  Lemma not_mod_write : forall m t l v a m' (Hnot_mod : modifies a l = false)
    (Happly : apply_access' m a m'), can_do m (Write t l v) <-> can_do m' (Write t l v).
  Proof.
    intros; inversion Happly; simpl in *.
    repeat (rewrite can_do_apply_iff); simpl; repeat autounfold in *; simpl.
    generalize (not_mod_op _ _ Hnot_mod); intro Hnot_mods.
    inversion Hnot_mods; [destruct a |]; clarify.
    rewrite <- H in *; clarify.
    generalize (not_mod_write _ _ v _ H0 H2); intro.
    inversion H1; clarify.
    - repeat (rewrite exists_not_None); auto.
    - generalize (not_mod_write _ _ v _ H5 H3); destruct a; clarify.
      repeat (rewrite exists_not_None); etransitivity; eauto.
  Qed.

  Lemma alloc_write : forall m t l v m' (Halloc : apply_access' m (Alloc t l) m'),
    can_do m' (Write t l v).
  Proof.
    intros; inversion Halloc.
    rewrite can_do_apply_iff; simpl in *; repeat autounfold in *; clarify.
    generalize (alloc_allows _ _ Happly); intros [Hwrite [_ _]].
    rewrite exists_not_None; eauto.
  Qed.

  Lemma free_rw : forall m t l a m' (Hfree : apply_access' m (Free t l) m')
    (Hrw : reads a l = true \/ writes a l = true), ~can_do m' a.
  Proof.
    intros; inversion Hfree.
    rewrite can_do_apply_iff; simpl in *; repeat autounfold in *; clarify.
    generalize (free_allows _ _ Happly); intros [Hread [Hwrite _]].
    destruct a; clarify.
    - destruct (eq_dec l l0); clarify.
      specialize (Hread v); clarify.
    - destruct (eq_dec l l0); clarify.
      specialize (Hwrite v); clarify.
    - specialize (Hread v); clarify.
  Qed.

  Lemma alloc_free : forall m t l m' (Halloc : apply_access' m (Alloc t l) m'),
    can_do m' (Free t l).
  Proof.
    intros; inversion Halloc.
    rewrite can_do_apply_iff; simpl in *; repeat autounfold in *; clarify.
    generalize (alloc_allows _ _ Happly); clarify.
    rewrite exists_not_None; eauto.
  Qed.

  Lemma alloc_alloc : forall m t l m' (Halloc : apply_access' m (Alloc t l) m'),
    ~can_do m' (Alloc t l).
  Proof.
    intros; inversion Halloc.
    rewrite can_do_apply_iff; simpl in *; repeat autounfold in *; clarify.
    generalize (alloc_allows _ _ Happly); clarify.
  Qed.

  Lemma free_free : forall m t l m' (Hfree : apply_access' m (Free t l) m'),
    ~can_do m' (Free t l).
  Proof.
    intros; inversion Hfree.
    rewrite can_do_apply_iff; simpl in *; repeat autounfold in *; clarify.
    generalize (free_allows _ _ Happly); clarify.
  Qed.

  Lemma free_alloc : forall m t l m' (Hfree : apply_access' m (Free t l) m'),
    can_do m' (Alloc t l).
  Proof.
    intros; inversion Hfree.
    rewrite can_do_apply_iff; simpl in *; repeat autounfold in *; clarify.
    generalize (free_allows _ _ Happly); clarify.
    rewrite exists_not_None; eauto.
  Qed.

  Lemma write_not_read : forall m t l v m' a (Hwrite : apply_access' m (Write t l v) m')
    (Hnot_read : reads a l = false), can_do m a <-> can_do m' a.
  Proof.
    intros; inversion Hwrite; simpl in *; apply (can_op(P := fun op => forall v' : val, op <> MRead l v') _ _ _).
    - repeat autounfold in *; clarify.
      eapply write_not_read; eauto.
    - destruct a; clarify; constructor; try constructor; clarify; crush.
  Qed.

  Lemma ARW_not_read : forall m t l v v' m' a (HARW : apply_access' m (ARW t l v v') m')
    (Hnot_read : reads a l = false), can_do m a <-> can_do m' a.
  Proof.
    intros; inversion HARW; simpl in *; repeat autounfold in *; clarify.
    erewrite (read_noop(t := t)(m' := {| mrep := x |})); [eapply (write_not_read(t := t)(l := l)(v := v')); auto |].
    - constructor; simpl; repeat autounfold; clarify; eauto.
    - constructor; simpl; repeat autounfold; clarify; eauto.
  Qed.

  Lemma alloc_cast : forall m t l m' p (Halloc : apply_access' m (Alloc t l) m'),
    can_do m (Cast t l p) <-> can_do m' (Cast t l p).
  Proof.
    intros; inversion Halloc.
    repeat (rewrite can_do_apply_iff); simpl in *; repeat autounfold in *; clarify.
    repeat (rewrite exists_not_None); apply alloc_cast; auto.
  Qed.

  Lemma free_cast : forall m t l m' p (Hfree : apply_access' m (Free t l) m')
    (Hno_addr : ~In (l, p) (acs m ++ fcs m)), can_do m (Cast t l p) <-> can_do m' (Cast t l p).
  Admitted.

  Lemma ARW_reads : forall m t l v v' (HARW : can_do m (ARW t l v v')),
    can_do m (Read t l v).
  Proof.
    unfold can_do; clarify.
    inversion H; clarify; repeat autounfold in *; clarify.
    eexists {| mrep := x0 |}; constructor; clarify; repeat autounfold; clarify.
  Qed.    

  Print Memory_Model.

  Instance SC : Memory_Model(mem := mem) Val.
  Proof.
    constructor.
    - intros; eapply diff_loc; eauto.
    - admit.
    - admit.
    - intros; eapply read_noop; eauto.
    - intros; eapply cast_noop; eauto.
    - intros; eapply read_written; eauto.
    - intros; eapply not_mod_write; eauto.
    - intros; eapply alloc_write; eauto.
    - intros; eapply free_rw; eauto.
    - intros; eapply alloc_free; eauto.
    - intros; eapply alloc_alloc; eauto.
    - intros; eapply free_free; eauto.
    - intros; eapply free_alloc; eauto.
    - intros; eapply write_not_read; eauto.
    - intros; eapply ARW_not_read; eauto.
    - intros; eapply alloc_cast; eauto.
    - intros; eapply free_cast; eauto.
    - apply ARW_reads; auto.
  Defined.

End SC.

(*Module SC_Mem_Dec <: Equalities.DecidableType.
  Definition t := SC_mem.
  Definition eq := SC_mem_eq.
  Definition eq_dec := SC_mem_eq_dec.
  Definition eq_equiv := SC_mem_eq_equiv.
End SC_Mem_Dec.
Module SC_MemSet := MSet' SC_Mem_Dec.
Definition SC_mem_set := SC_MemSet.t.*)

(* Executable implementation of SC *)
Section SC_impl.
  (* Need an implementation of the layout. *)
(*  Definition read_SC (m : SC_mem) (_ : string) l := if NatSet.mem l (snd m) then None else
    NatMap.find l (fst m).
  Definition get_free_SC (m : SC_mem) (_ : string) := NatSet.choose (snd m).
  Definition cast_SC (m : SC_mem) (_ : string) l := Some (Z.of_nat l).

  Instance SC_impl : MM_impl SC := 
  { apply_access_fun := run_op_SC; read := read_SC; get_free := get_free_SC;
    cast := cast_SC }.
  Proof.
    unfold read_SC; clarify; eexists; econstructor; [simpl | reflexivity].
      setoid_rewrite c; setoid_rewrite H; crush_if.
    unfold get_free_SC; clarify; eexists; econstructor; [simpl | reflexivity].
      generalize (NatSet.choose_spec1 H); rewrite <- NatSet.mem_spec; intro.
        setoid_rewrite H0; auto.
    unfold cast_SC; clarify; eexists; econstructor; [clarify | reflexivity].
      generalize (Z.eqb_refl (Z.of_nat l)); intro; contr.
    intros; econstructor; eauto; reflexivity.
  Defined.*)
    
End SC_impl.

(* Move this section to a file for concrete MiniLLVM semantics.         
Recursive Extraction run_op_SC step_fun.

(* No fairness, scheduling determined by the implementation of FMap.elements. *)
Definition conc_step_fun_SC tG gt C m :=
  match StringMap.elements C with
  | nil => None
  | (t, c)::rest => 
    match StringMap.find t tG with
    | None => None
    | Some G => 
      match step_fun G SC_impl t m gt c with
      | None => None
      | Some (ops, c') => 
        match update_mem_fun(MM_exec := SC_impl) m ops with
        | None => None
        | Some m' => Some (StringMap.add t c' C, m')
        end
      end
    end
  end.
    
Recursive Extraction conc_step_fun_SC.

Lemma conc_step_fun_SC_sound: forall tG gt C m C' m', conc_step_fun_SC tG gt C m = Some (C', m') ->
  conc_step SC tG gt (C, m) (C', m').
Proof.
  unfold conc_step_fun_SC; intros.
    destruct (StringMap.elements C) eqn: Cs; try discriminate.
    repeat (destruct p).
    repeat (rewrite must_be_Some in *; crush).
    destruct x0.
    rewrite must_be_Some in *; crush.
    eapply step_thread.
      eapply StringMap.find_2; eauto.
      eapply StringMap.elements_2; setoid_rewrite Cs; constructor; reflexivity.
      eapply step_fun_sound; eauto.
      eapply update_mem_correct; eauto.
      unfold StringMap.F.Add; auto.
Qed.

Recursive Extraction conc_step_fun_SC.*)