Require Import Arith.
Require Import List.
Import ListNotations.

Require Import Vminus.Util.
Require Import Vminus.Vminus.

Require Import Vminus.CFG.

(** *** List-based CFG Implementation *)

(**  One possible implementation of cfgs *)

Module ListCFG <: CFG.
  Definition block := (lbl * list insn)%type.
  Definition t := (lbl * list block)%type.
  Local Notation cfg := t.

  Definition entry_block : cfg -> lbl := @fst _ _.

  Inductive wf_cfg' : cfg -> Prop :=
    wf_cfg_intro : forall l bs,
    NoDup (map (@fst _ _) bs) ->
    NoDup (flat_map (fun b => map (@fst _ _) (snd b)) bs) ->
    In l (map (@fst _ _) bs) ->
    ~ In [] (map (@snd _ _) bs) ->
    wf_cfg' (l, bs).

  (* hack around some limitation re inductive types & parameters *)
  Definition wf_cfg := wf_cfg'.

  Lemma wf_cfg_block_len : forall g, wf_cfg g ->
    forall l is, In (l, is) (snd g) -> length is <> 0.
  Proof.
    inversion 1. intros. destruct is; simpl; auto. 
    contradict H2. 
    eapply in_map with (f:=@snd _ _) in H5. auto.
  Qed.

  Definition wf_pc (g:cfg) (p:pc) : Prop :=
    let (l, n) := p in
    exists is i, In (l, is) (snd g) /\ Nth i is n.

  Definition tmn_pc (g:cfg) (p:pc) : Prop :=
    let (l, n) := p in
    exists is, In (l, is) (snd g) /\ n = pred (length is).

  Definition insn_at_pc (g:cfg) (p:pc) (i:insn) : Prop :=
    let (l, n) := p in
    exists is, In (l, is) (snd g) /\ Nth i is n.
    
  Definition uid_at_pc (g:cfg) (p:pc) (uid:uid) : Prop :=
    exists c, insn_at_pc g p (uid, c).

  Lemma wf_pc_insn : forall g, wf_cfg g ->
    forall p, wf_pc g p -> exists i, insn_at_pc g p i.
  Proof.
    unfold wf_pc, insn_at_pc. destruct p; intros. 
    decompose [ex and] H0. eauto.
  Qed.

  Lemma wf_pc_tmn : forall g, wf_cfg g ->
    forall p, wf_pc g p -> exists p', tmn_pc g p' /\ le_pc p p'.
  Proof.
    unfold wf_pc, tmn_pc. destruct p. intros.
    decompose [ex and] H0. 
    exists (t0, pred (length x)). split. eauto.
    constructor. 
    apply PeanoNat.Nat.lt_le_pred.
    eapply Nth_length; eauto.
  Qed.

  Lemma wf_pc_le_tmn : forall g, wf_cfg g ->
    forall p', tmn_pc g p' -> forall p, le_pc p p' -> wf_pc g p.
  Proof.
    unfold wf_pc, tmn_pc. intros. destruct p, p'.
    decompose [ex and] H0. exists x.

    destruct x. apply wf_cfg_block_len in H3; auto. contradict H3; auto.
    inversion H1; subst. apply le_lt_n_Sm in H5. 
    erewrite <- S_pred in H5. 
    apply length_Nth in H5 as [? ?]. 
    eexists. split; eauto. eauto.
  Qed.

  Lemma wf_entry : forall g, wf_cfg g ->
    wf_pc g (block_entry (entry_block g)).
  Proof.
    unfold wf_pc. inversion 1. simpl.
    apply in_map_iff in H2 as [[? ?] [? ?]].
    destruct l0.
    exfalso. pose proof (wf_cfg_block_len g H t0 []) as contra. 
    subst g; simpl in *. apply contra; auto.
    eexists. eexists. 
    simpl in *. subst l. split; eauto.
    simpl; eauto.
  Qed.

  Lemma insn_at_pc_func : forall g, wf_cfg g ->
    functional (insn_at_pc g).
  Proof. 
    unfold functional, insn_at_pc. inversion 1. destruct a.
    intros b1 b2 [is1 [Hin1 Hnth1]] [is2 [Hin2 Hnth2]].
    cut (is1 = is2). intro; subst is2. eapply Nth_eq; eauto.
    eapply NoDup_assoc_func; eauto.
  Qed.

  Lemma uid_at_pc_inj : forall g, wf_cfg g ->
    injective (uid_at_pc g).
  Proof.
    unfold injective, uid_at_pc, insn_at_pc. inversion 1.
    intros [l1 n1] [l2 n2] uid [c1 [is1 [Hin1 Hnth1]]] [c2 [is2 [Hin2 Hnth2]]].
    cut ((l1, is1) = (l2, is2)).
    intro Heq. inversion Heq; clear Heq. f_equal.
    eapply NoDup_flat_map__NoDup in H1; eauto.
    change is1 with (snd (l1, is1)) in Hnth1.
    change is2 with (snd (l2, is2)) in Hnth2.
    subst; eapply NoDup_nth_inj; eauto. 

    set (f1 b := map (@fst _ _) (snd b)) in *.
    apply (NoDup_flat_map (l1, is1) (l2, is2) uid f1 bs); auto.
    unfold f1; simpl. 
    apply in_map_iff. exists (uid, c1); eauto using Nth_In.
    apply in_map_iff. exists (uid, c2); eauto using Nth_In.
  Qed.

  (** ** Working with ListCFG. *)

  (** Adds the given instruction list as a block labeled [l]. *)

  Definition update (bs:list block) (l:lbl) (is:list insn) : list block :=
    (l, is)::bs.

  (** Lookup the block in the list. *)

  Definition lookup (bs:list block) (l:lbl) : option (list insn) :=
    assoc Lbl.eq_dec l bs.

  (** ** Simple lemmas about CFG modifications. *)

  Lemma update_eq :
    forall (is : list insn) (l1 l2 : lbl) (bs : list block),
      l1 = l2 -> lookup (update bs l1 is) l2 = Some is.
  (* FOLD *)
  Proof.
    intros; unfold update, lookup.
    subst. simpl. destruct (Lbl.eq_dec l2 l2); tauto.
  Qed.
  (* /FOLD *)

  Lemma update_neq :
    forall (l1 l2 : lbl) (is : list insn) (bs: list block),
      l1 <> l2 -> lookup (update bs l1 is) l2 = lookup bs l2.
  (* FOLD *)
  Proof.
    intros; subst; simpl.
    destruct (Lbl.eq_dec l2 l1); subst; tauto.
  Qed.
  (* /FOLD *)

  (* Added *)
  Fixpoint find_block {A : Type} (lst : list (lbl * A)) (trgt_label : lbl) :=
    match lst with
    | [] => None
    | (label, data) :: other_blks =>
      if Lbl.eq_dec label trgt_label then
        Some data 
      else find_block other_blks trgt_label
    end.
      
  Definition fetch (g : cfg) (p: pc): option insn :=
    let '(entry_label, blocks) := g in
    let '(trgt_block, offset) := p in
    match (find_block blocks trgt_block) with
    | Some found_block => nth_error found_block offset
    | None => None
    end.
  
  Lemma find_block_ok: forall (blks: list (lbl * list insn)) found_instrs (label: lbl),
      NoDup (List.map fst blks) -> 
      find_block blks label = Some found_instrs <->
      In (label, found_instrs) blks.
  Proof.
    intros blks found_instrs label nodups.
    induction blks as [| blk other_blks].
    { simpl; split; intros H; inversion H. }
    { simpl; destruct blk as [this_label this_insns].
      destruct (Lbl.eq_dec this_label label) as [label_eq | label_neq].
      { split; intros H;
          [inversion H as [found_this] | idtac].
        - subst; left; auto.
        - destruct H as [found_here | found_in_others].
          + inversion found_here; subst; trivial.
          + simpl in nodups.
            (* Want the following as lemma *)
            replace (this_label :: map fst other_blks) with
                ([] ++ (this_label :: map fst other_blks)) in nodups
              by auto.
            apply NoDup_remove in nodups.
            inversion nodups as [? not_found_in_others].
            apply in_map with (f := fst) in found_in_others.
            simpl in found_in_others.
            contradiction not_found_in_others.
            simpl; subst; apply found_in_others.
      } 
      { simpl in nodups.
        replace (this_label :: map fst other_blks) with
            ([] ++ (this_label :: map fst other_blks)) in nodups
          by auto.
        apply NoDup_remove in nodups.
        inversion nodups as [nodups_in_others this_label_in_others].
        generalize (IHother_blks nodups_in_others) as IH; intros IH.
        rewrite IH.
        split; auto.
        intros [Hcontra | ?]; auto.
        contradiction label_neq.
        inversion Hcontra; auto.
      }
    } 
  Qed.
      
  Lemma find_block_iff_in_cfg: forall entry_label blks trgt_label trgt_offset i,
      NoDup (map fst blks) -> 
      fetch (entry_label, blks) (trgt_label, trgt_offset) = Some i <->
      exists instrs, In (trgt_label, instrs) blks /\ Nth i instrs trgt_offset.
  Proof.
    intros entry_label blks trgt_label trgt_offset i nodup.
    unfold fetch.
    destruct (find_block blks trgt_label) eqn:found.
    { apply find_block_ok in found; auto.
      split.
      { intros H; exists l; split; trivial.
        rewrite nth_error_iff_Nth in H.
        trivial.
      }
      { intros [instrs [trgt_blk_found trgt_instr_found]].
        rewrite <- nth_error_iff_Nth in trgt_instr_found.
        replace l with instrs; auto.
        eapply NoDup_assoc_func.
        apply nodup.
        apply trgt_blk_found.
        trivial.
      }         
    } 
    { split; intros H; [inversion H | idtac].
      destruct H as [instrs [trgt_label_found trgt_instr_found]].
      rewrite <- nth_error_iff_Nth in trgt_instr_found.
      rewrite <- find_block_ok in trgt_label_found; auto.
      rewrite trgt_label_found in found; inversion found.
    }
  Qed.
  
  (* Added *)
  Lemma insn_at_pc_fetch :
    forall g pc i, wf_cfg g ->
              insn_at_pc g pc i <-> fetch g pc = Some i.
  Proof.
    intros [l blks] pc i wf_g.
    inversion wf_g as
        [l' blks' nodup nodup_uid l_in_blks blks_not_empty [l_l' blks_blk]].
    destruct pc as [curr_label curr_offset].
    rewrite find_block_iff_in_cfg; auto.
    simpl.
    split; auto.
  Qed.      
    
End ListCFG.