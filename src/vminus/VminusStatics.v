Require Import Arith.
Require Import List.
Import ListNotations.

Require Import Vminus.Classes.
Require Import Vminus.Util.
Require Import Vminus.Env.
Require Import Vminus.Vminus.
Require Import Vminus.CFG.

Require Import Vminus.Dom.
Require Import Vminus.VminusOpSem.

Module MakeStatics (Cfg: CFG).
Import Cfg.

(** ** Typing *)
(** FULL: The only ways in which a Vminus program can "go wrong" are
    by accessing a local variable that hasn't been defined or jumping
    to a label that isn't in the CFG.  Therefore, its typing
    constraints ensure that each instruction only mentions local
    identifiers that are in scope according to the domination
    structure of the control-flow graph and that all mentioned labels
    are associated with blocks defined in the CFG.  *)

(** TERSE:
    The type system for Vminus ensures that:
    - All local variables are defined.
    - All jump targets are legal.
*)

Module Typing.  
  (** *** GRAPH instance for dominance calculation *)

  (** Edge relation *)

  Inductive succ_pc (g:Cfg.t) : pc -> pc -> Prop :=
  | succ_pc_S : forall p,
      succ_pc g p (incr_pc p)
  | succ_pc_J : forall p l i,
      insn_at_pc g p i ->
      In l (insn_lbls i) ->
      succ_pc g p (block_entry l).

  (** Graph of program points *)

  Module PcGraph <: GRAPH.
    Definition t := Cfg.t.
    Definition V := pc.
    Definition entry g := block_entry (entry_block g).
    Definition Succ := succ_pc.
    Definition Mem := wf_pc.
  End PcGraph.

  Module Export Dom := Dom.Spec PcGraph.

  (** *** Definitions for Well-formed SSA programs. *)

  (** FULL: Most of the Vminus instructions define the uid associated
  with their program point.  Some (like [store] and the [tmn]s)
  do not. *)
  (** TERSE: The command at the given [pc] defines uid. *)

  Definition def_at_pc (g:Cfg.t) (p:pc) (uid:uid) : Prop :=
    exists c, insn_at_pc g p (uid, c) /\ defs_uid (uid, c). 

  (** The definition of [uid] strictly dominates the pc. *)
 
  Definition uid_sdom_pc (g:Cfg.t) (uid:uid) (p:pc) : Prop :=
    exists p', def_at_pc g p' uid /\ SDom g p' p.

  (** All uses of a [uid] must be strictly dominated by
      their definitions. *)

  Definition wf_use (g:Cfg.t) (i:insn) (p:pc) : Prop :=
    forall uid, In (val_uid uid) (insn_uses i) -> uid_sdom_pc g uid p.

  (** All jump targets must be legal block labels. *)

  Definition wf_lbl (g:Cfg.t) (i:insn) : Prop :=
    forall l, In l (insn_lbls i) -> wf_pc g (block_entry l).

  (** *** Well-formed phi nodes *)

  (**  Consider [ %x = phi [lbl1:v1, ...,lbln:vn] ].  This is well formed
       when every predecessor block with terminator program point p' 
       has a label associated with value v.  Moreover, if v is a uid then
       the definition of the uid strictly dominates p'.
  *)

  Definition wf_phi_args (g:Cfg.t) (i:insn) (p:pc) : Prop :=
    forall pred, succ_pc g pred (entry_of_pc p) ->
      (exists v, In (lbl_of pred, v) (insn_phis i)) /\
      (forall uid, In (lbl_of pred, val_uid uid) (insn_phis i) -> 
          uid_sdom_pc g uid pred).

  Definition wf_phi_pred (g:Cfg.t) (i:insn) (p:pc) : Prop :=
    forall l v, In (l, v) (insn_phis i) ->
      (exists pred, succ_pc g pred (entry_of_pc p) /\ lbl_of pred = l).

  Definition wf_phi (g:Cfg.t) (i:insn) (p:pc) : Prop :=
    is_phi i -> wf_phi_args g i p
             /\ wf_phi_pred g i p
             /\ insn_phis i <> [].

  (** *** Well-formed instructions *)

  Inductive wf_insn (g:Cfg.t) : insn -> pc -> Prop :=
  | wf_insn_intro : forall i p,
      wf_use g i p ->
      wf_lbl g i ->
      wf_phi g i p ->
      wf_insn g i p.

  Inductive wf_prog (g:Cfg.t) : Prop :=
  | wf_prog_intro : forall
      (Hwfcfg : wf_cfg g)
      (Hwfis : forall p i, insn_at_pc g p i -> wf_insn g i p)
      (Hwftmn : forall p' i, tmn_pc g p' -> insn_at_pc g p' i -> is_tmn i)
      (Hwfentry : forall p, ~ succ_pc g p (block_entry (entry_block g))),
      wf_prog g.

End Typing.

(** ** Correctness *)

Module OpsemCorrect.
  Module Import V := Make (Cfg).  
  Import Typing Opsem.

(** First, some utilities. *)
(* HIDE *)
(*
  Lemma insn_at_pc_inj : forall g, wf_cfg g ->
    injective (insn_at_pc g).
(* FOLD *)
  Proof.
    intros g Hwfc. specialize (uid_at_pc_inj g Hwfc).
    unfold injective, uid_at_pc. intros.
    destruct b; eauto.
  Qed.
(* /FOLD *)
*)
(* /HIDE *)

(* HIDE *)
  (* LATER: Arguably the next two lemmas could go in the CFG module. *)
(* /HIDE *)

  Lemma uid_at_pc_func : forall g, wf_cfg g ->
    functional (uid_at_pc g).
(* FOLD *)
  Proof.
    intros g Hwfc. specialize (insn_at_pc_func g Hwfc).
    unfold functional, uid_at_pc. intros.
    destruct H0 as [c1 ?]. destruct H1 as [c2 ?].
    cut ((b1,c1) = (b2,c2)). inversion 1; auto.
    eauto.
  Qed.
(* /FOLD *)

  Lemma eq_pc_uid : forall g pc id1 id2 c1 c2,
    wf_prog g ->
    insn_at_pc g pc (id1, c1) ->
    insn_at_pc g pc (id2, c2) ->
    id1 = id2.
(* FOLD *)
  Proof.
    intros. inversion H. pose proof (uid_at_pc_func g Hwfcfg).
    unfold functional in H2. eapply H2; red; eauto.
  Qed.
(* /FOLD *)

(* HIDE *)
  Unset Printing Records.
(* /HIDE *)


  (** *** Dominance relation *)

  (** A more convenient form for typing rules *)

  Lemma uid_sdom_step : forall g uid' uid pc1 pc2 c,
    wf_prog g ->
    uid' <> uid ->
    wf_pc g pc2 ->
    succ_pc g pc1 pc2 ->
    insn_at_pc g pc1 (uid, c) ->
    uid_sdom_pc g uid' pc2 ->
    uid_sdom_pc g uid' pc1.
(* FOLD *)
  Proof.
    unfold uid_sdom_pc. 
    intros g uid' uid pc1 pc2 c Hwff Hneq Hpc Hsucc Hi [pc' [Hdef Hdom]]. 
    exists pc'. split. assumption. 
    split. contradict Hneq. subst pc'. 
    destruct Hdef as [? [? ?]]; eapply eq_pc_uid; eauto. 
    inversion Hwff; eapply dom_step; eauto. 
  Qed.
(* /FOLD *)

  (** ** Progress & Preservation *)

  (** Extend well-formedness definitions to include all components of 
  the state. *)

  Definition wf_loc (g:Cfg.t) (p:pc) (loc:loc) : Prop :=
  forall uid, uid_sdom_pc g uid p -> exists n, loc uid = Some n.

  Definition at_entry (g:Cfg.t) (p:pc) : Prop :=
    entry_of_pc p = block_entry (entry_block g).

  Inductive wf_state (g:Cfg.t) : state -> Prop :=
  | wf_state_intro : forall st
      (Hwfpc: wf_pc g st.(st_pc))
      (Hwfloc: wf_loc g st.(st_pc) st.(st_loc))
      (Hwfppc: at_entry g st.(st_pc) \/ 
                 succ_pc g st.(st_ppc) (entry_of_pc st.(st_pc)))
      (Hwfploc: at_entry g st.(st_pc) \/ 
                  wf_loc g st.(st_ppc) st.(st_ploc)),
      wf_state g st.

  (** Initial state is well formed *)

  Lemma wf_init_state : 
    forall g m, wf_prog g ->
    wf_state g (init_state g m).
(* FOLD *)
  Proof.
    intros g m Hprog. inversion Hprog. 
    apply wf_entry in Hwfcfg.
    econstructor. auto.
    red. simpl. intros. red in H. destruct H as [? [? [? ?]]].
    red in H1. contradict H0.
    cut (In x [block_entry (entry_block g)]). simpl. intuition.
    eapply H1. econstructor. auto.
    left. unfold init_state, at_entry, entry_of_pc. auto.
    left. unfold init_state, at_entry, entry_of_pc. auto.
  Qed.
(* /FOLD *)  


  (** *** Progress helper lemmas. *)

  (** There are no phi nodes in the entry block. *)

  Lemma at_entry_not_phi : forall g st i,
    wf_prog g ->
    at_entry g st.(st_pc) ->
    insn_at_pc g st.(st_pc) i ->
    ~ is_phi i.
(* FOLD *)
   Proof.
     intros g st i Hprog Hentry Hinsn. 
     destruct Hprog as [_ ? _ ?].
     specialize (Hwfis _ _ Hinsn). inversion Hwfis; subst.
     intro Hphi. specialize (H1 Hphi). destruct H1 as [? [? ?]].
     destruct (insn_phis i) eqn:His. contradiction H3; auto.
     assert (In p (insn_phis i)) as Hin. rewrite His. left; auto.
     destruct p. apply H2 in Hin. destruct Hin as [pred [Hpred Ht0]].
     specialize (Hwfentry pred). contradict Hwfentry. 
     rewrite <- Hentry; auto.
   Qed.
(* /FOLD *)  

  (** In a well-formed program with well-formed locals, evaluating
  a value is never undefined. *)

  Lemma eval_val__wf_loc : forall g pc loc i v,
    wf_prog g ->
    wf_loc g pc loc ->
    insn_at_pc g pc i ->
    In v (insn_uses i) ->
    exists n, eval_val loc v = Some n.
(* FOLD *)
  Proof.
    intros ? ? ? ? v Hwff Hwfloc Hi ?. 
    destruct v as [uid | n].
    simpl. inversion Hwff as [_ ? _]. apply Hwfis in Hi. 
    destruct Hi as [? ? Huse]. specialize (Huse uid). 
    lapply Huse; auto.
    simpl; eauto.
  Qed.
(* /FOLD *)  

  (** ** Progress *)

  Definition FinalState (g:Cfg.t) (s:state) : Prop :=
    exists uid, insn_at_pc g s.(st_pc) (uid, cmd_tmn tmn_ret).
  
  Lemma progress : forall g s,
    wf_prog g -> wf_state g s ->
    FinalState g s \/ exists s', step g s s'.
(* FOLD *)
  Proof.
    intros g s Hwff Hwfs.
    inversion Hwfs as [? Hwfpc]; subst. inversion Hwff.
    pose proof (wf_pc_insn g Hwfcfg _ Hwfpc) as [[i c] Hi].
    rename s into j. set (s:=j) in *. destruct j. 
    destruct c.
  
    - (* Case "cmd_bop". *)
    eelim (eval_val__wf_loc) with (v:=v) (loc:=st_loc0); eauto; simpl; auto.
    eelim (eval_val__wf_loc) with (v:=v0) (loc:=st_loc0); eauto; simpl; auto.
    intros n1 Heqn1 n2 Heqn2.
    right. eexists. eapply step_bop; eauto. unfold eval_bop.
    rewrite Heqn1, Heqn2. reflexivity. 

    - (* Case "cmd_phi". *)
    right. specialize (Hwfis _ _ Hi). inversion Hwfis; subst.
    
    destruct Hwfppc as [|Hwfppc]. 
    exfalso; eapply at_entry_not_phi; eauto. simpl; trivial.
    destruct Hwfploc as [|Hwfploc]. 
    exfalso; eapply at_entry_not_phi; eauto. simpl; trivial.

    destruct (H1 I) as [Hphi _]. clear H1.
    specialize (Hphi st_ppc0 Hwfppc). destruct Hphi as [[v Hin] Hdom].

    cut (exists v, assoc Lbl.eq_dec (lbl_of st_ppc0) l = Some v). intros [v' Hv].
    cut (exists n, eval_val st_ploc0 v' = Some n). intros [n Hn].
    eexists. eapply step_phi. eauto. unfold eval_phi.
    rewrite Hv. rewrite Hn. reflexivity.
  
    destruct v' as [i' | n']. simpl in *. apply Hwfploc. apply Hdom. 
    eapply assoc_in. apply Hv. simpl; eauto.
    eapply in_assoc_some. apply Hin.
  
    - (* Case "cmd_tmn". *)
    destruct t0.
    * (*  SCase "tmn_jmp". *)
      right. eexists. eapply step_tmn. eauto. reflexivity.

    * (* SCase "tmn_cbr". *)
      cut (exists n, eval_val st_loc0 v = Some n). intros [n Heqn].
      right. eexists. eapply step_tmn. eauto. simpl. rewrite Heqn. reflexivity.
      eapply eval_val__wf_loc; eauto. simpl; auto.

    * (* SCase "tmn_ret". *)
      left. red; eauto. 

    - (* Case "cmd_load". *)
    right. eexists. apply step_load; eauto.

    - (* Case "cmd_store". *)
    right. cut (exists n1, eval_val st_loc0 v = Some n1). 
    intros [n1 Heqn1]. eexists. eapply step_store. eauto. eauto.
    eapply eval_val__wf_loc; eauto. simpl; auto.
  Qed.
(* /FOLD *)

  (** *** Some first steps towards preservation. *)

  Lemma wf_pc_incr : forall g p i,
    wf_prog g ->
    wf_pc g p ->
    insn_at_pc g p i ->
    ~ is_tmn i ->
    wf_pc g (incr_pc p).
(* FOLD *)
  Proof.
    intros. inversion H. 
    apply (wf_pc_tmn g Hwfcfg) in H0 as [pt [Ht Hle]].
    eapply wf_pc_le_tmn; eauto.
    inversion Hle; subst. destruct H0.
    contradict H2. eapply Hwftmn; eauto. 
    constructor; auto with arith.
  Qed.
(* /FOLD *)

  Lemma eval_tmn_in_lbls : forall l loc t uid,
    Some l = eval_tmn loc t -> In l (insn_lbls (uid, cmd_tmn t)).
(* FOLD *)
  Proof.
    intros.
    destruct t0; simpl in *.
    inversion H; auto.
    destruct (eval_val loc v). injection H. 
      destruct n; eauto.
      discriminate H. discriminate H.
  Qed.
(* /FOLD *)

  (** *** More preservation helpers*)

  Lemma not_def_sdom_step : forall g p1 p2 i uid,
    wf_prog g ->
    wf_pc g p2 ->
    insn_at_pc g p1 i ->
    ~ defs_uid i ->
    succ_pc g p1 p2 ->
    uid_sdom_pc g uid p2 ->
    uid_sdom_pc g uid p1.
(* FOLD *)
  Proof. 
    destruct i; intros. inversion H4 as [? [[? [? Ht]] ?]].
    eapply uid_sdom_step; eauto. 
    contradict Ht. subst t0. assert (x = p1). 
    inversion H; eapply uid_at_pc_inj; try red; eauto. subst x.
    replace (uid, x0) with (uid, c); trivial. 
    inversion H; eapply insn_at_pc_func; eauto.
  Qed.
(* /FOLD *)    

  Lemma wf_loc_succ : forall g p1 p2 loc uid n c,
   wf_prog g ->
   wf_pc g p2 ->
   insn_at_pc g p1 (uid, c) ->
   succ_pc g p1 p2 ->
   wf_loc g p1 loc ->
   wf_loc g p2 (update loc uid (Some n)).
(* FOLD *)
  Proof.
    intros. red; intros. destruct (Uid.eq_dec uid0 uid). subst.
    rewrite Locals.update_eq; eauto. reflexivity.
    rewrite Locals.update_neq; eauto. apply H3.
    eapply uid_sdom_step; eauto. 
  Qed.
(* /FOLD *)

  (** ** Preservation *)

  Lemma preservation : forall g s s',
    wf_prog g ->
    wf_state g s -> step g s s' -> wf_state g s'.
(* FOLD *)
  Proof.
    intros g _ s' Hwff [s Hwfpc Hwfloc] Hstep.
    inversion Hstep; subst; simpl in *;
      rename pc into pc0.
    
    - (* Case "step_bop". *)
    assert (wf_pc g (incr_pc pc0)) as Hwfpc' by (eapply wf_pc_incr; eauto).
    constructor; simpl; try solve [destruct pc0; auto].
    eapply wf_loc_succ; eauto. constructor.

    - (* Case "step_phi". *)
    assert (wf_pc g (incr_pc pc0)) as Hwfpc' by (eapply wf_pc_incr; eauto).
    constructor; simpl; try solve [destruct pc0; auto].
    eapply wf_loc_succ; eauto. constructor.
  
    - (* Case "step_tmn". *)
    assert (wf_pc g (l', 0)) as Hwfpc'.
      inversion Hwff as [_ Hwfi _]. specialize (Hwfi _ _ H).
      inversion Hwfi. red in H2. apply H2. 
      eauto. eapply eval_tmn_in_lbls. eauto.

    assert (succ_pc g pc0 (l', 0)) as Hsucc.
      econstructor. eauto. eapply eval_tmn_in_lbls. eauto.
    constructor; simpl; eauto. red; intros. apply Hwfloc.
    eapply not_def_sdom_step; eauto.

    - (* Case "step_load". *)
    assert (wf_pc g (incr_pc pc0)) as Hwfpc' by (eapply wf_pc_incr; eauto).
    constructor; simpl; try solve [destruct pc0; auto].
    eapply wf_loc_succ; eauto. constructor.

    - (* Case "step_store". *)
    assert (wf_pc g (incr_pc pc0)) as Hwfpc' by (eapply wf_pc_incr; eauto).
    constructor; simpl; try solve [destruct pc0; auto].
    red; intros. apply Hwfloc. eapply not_def_sdom_step; eauto. constructor.
  Qed.
(* /FOLD *)  

(* HIDE *)
Lemma step_deterministic : forall g s s1 s2, wf_prog g -> wf_state g s ->
  step g s s1 -> step g s s2 -> s1 = s2.
(* FOLD *)
Proof.
    intros g s s1 s2 Hwfprog Hwfs Hs1 Hs2.
    inversion Hwfs as [? Hwfpc]; subst. inversion Hwfprog.
    inversion Hs1; subst; simpl in *;
      try (rename bop into bop0);
      rename pc into pc0.

    - (* Case "step_bop". *)
    inversion Hs2; subst; simpl in *;
      try (rename bop into bop1);
      try (rename tmn into tmn0).
    assert ((uid, cmd_bop bop0 v1 v2) = (uid0, cmd_bop bop1 v0 v3)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.
    rewrite <- H8 in H0. inversion H0; subst. auto.

    assert ((uid, cmd_bop bop0 v1 v2) = (uid0, cmd_phi pas)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.

    assert ((uid, cmd_bop bop0 v1 v2) = (uid0, cmd_tmn tmn0)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.

    assert ((uid, cmd_bop bop0 v1 v2) = (uid0, cmd_load addr)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.
    
    assert ((uid, cmd_bop bop0 v1 v2) = (uid0, cmd_store addr v)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.
    
    - (* Case "step_phi". *)
    inversion Hs2; subst; simpl in *;
      try (rename bop into bop0);
      try (rename tmn into tmn0).

    assert ((uid, cmd_phi pas) = (uid0, cmd_bop bop0 v1 v2)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.

    assert ((uid, cmd_phi pas) = (uid0, cmd_phi pas0)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.
    rewrite <- H8 in H0. inversion H0; subst; auto.

    assert ((uid, cmd_phi pas) = (uid0, cmd_tmn tmn0)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.

    assert ((uid, cmd_phi pas) = (uid0, cmd_load addr)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.
    
    assert ((uid, cmd_phi pas) = (uid0, cmd_store addr v)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.

    - (* Case "step_tmn". *)
    inversion Hs2; subst; simpl in *;
      try (rename bop into bop0);
      try (rename tmn into tmn0).

    assert ((uid, cmd_tmn tmn0) = (uid0, cmd_bop bop0 v1 v2)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.

    assert ((uid, cmd_tmn tmn0) = (uid0, cmd_phi pas)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.

    rename tmn0 into tmn1.
    rename tmn into tmn0.
    assert ((uid, cmd_tmn tmn0) = (uid0, cmd_tmn tmn1)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto.
    inversion H1; subst.
    rewrite <- H8 in H0. inversion H0; subst; auto.

    assert ((uid, cmd_tmn tmn0) = (uid0, cmd_load addr)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.
    
    assert ((uid, cmd_tmn tmn0) = (uid0, cmd_store addr v)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.

    - (* Case "step_load". *)
    inversion Hs2; subst; simpl in *;
      try (rename bop into bop0);
      try (rename tmn into tmn0).
    assert ((uid, cmd_load addr) = (uid0, cmd_bop bop0 v1 v2)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H0; subst.

    assert ((uid, cmd_load addr) = (uid0, cmd_phi pas)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H0; subst.

    assert ((uid, cmd_load addr) = (uid0, cmd_tmn tmn0)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H0; subst.

    assert ((uid, cmd_load addr) = (uid0, cmd_load addr0)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H0; subst.
    auto.

    assert ((uid, cmd_load addr) = (uid0, cmd_store addr0 v)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H0; subst.


    - (* "step_store". *)
    inversion Hs2; subst; simpl in *;
      try (rename bop into bop0);
      try (rename tmn into tmn0).
      
    assert ((uid, cmd_store addr v) = (uid0, cmd_bop bop0 v1 v2)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.

    assert ((uid, cmd_store addr v) = (uid0, cmd_phi pas)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.

    assert ((uid, cmd_store addr v) = (uid0, cmd_tmn tmn0)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.

    assert ((uid, cmd_store addr v) = (uid0, cmd_load addr0)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.

    assert ((uid, cmd_store addr v) = (uid0, cmd_store addr0 v0)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.
    rewrite <- H8 in H0. inversion H0. subst; auto.
Qed.
(* /FOLD *)
(* /HIDE *)

End OpsemCorrect.

End MakeStatics.