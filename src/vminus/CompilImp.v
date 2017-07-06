(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)


(** * Imp to Vminus Compiler *)

(** Imports, instantiated with the list implementation of 
    control-flow graphs. *)


Require Import Arith List RelationClasses.
Import ListNotations.

Require Import Imp Vminus Sequences Stmon Util.
Require Import FunctionalExtensionality. (* TODO: don't really need this *)

Module Import V := Vminus.Make ListCFG.
Import Opsem.
Import ListCFG.

Notation cfg := ListCFG.t.

Unset Printing Records.

(** * Compiling Expressions *)

(** Compilation context for expressions.  The state monad keeps track
    of the list of generated uids so that we can generate fresh names. *)

Open Scope stmon.
Notation ectmon := (stmon (list uid)).

(** Generate a fresh uid. *)

Definition fresh : ectmon uid :=
  fun is =>
  let i := Uid.fresh is in
  (i::is, i).

(** ** Compiling binops. *)

(** Compile a general binary operation. *)

Definition comp_bop (b:bop) (e1 e2: ectmon (val * list insn))  
  : ectmon (val * list insn) :=
  do (v1, c1) <- e1;
  do (v2, c2) <- e2;
  do r <- fresh; 
  ret (val_uid r, (c1 ++ c2 ++ [(r, cmd_bop b v1 v2)])).

(** Compile an arithmetic expression. *)

Fixpoint comp_aexp (a:aexp) : ectmon (val * list insn) :=
  match a with
    | ANum n => ret (val_nat n, [])
    | AId i => do r <- fresh; ret (val_uid r, [(r, cmd_load i)])
    | APlus a1 a2 => comp_bop bop_add (comp_aexp a1) (comp_aexp a2)
    | AMinus a1 a2 => comp_bop bop_sub (comp_aexp a1) (comp_aexp a2)
    | AMult a1 a2 => comp_bop bop_mul (comp_aexp a1) (comp_aexp a2)
  end.

(** ** Compiling boolean expressions. *)

(* HIDE *)
(* guard condition doesn't allow `comp_bexp BFalse`, so we unfold *)
(* /HIDE *)
Fixpoint comp_bexp (b:bexp) : ectmon (val * list insn) :=
  match b with
    | BTrue => ret (val_nat 1, [])
    | BFalse => ret (val_nat 0, [])
    | BEq a1 a2 => comp_bop bop_eq (comp_aexp a1) (comp_aexp a2)
    | BLe a1 a2 => comp_bop bop_le (comp_aexp a1) (comp_aexp a2) 
    | BAnd b1 b2 => comp_bop bop_and (comp_bexp b1) (comp_bexp b2)
    | BNot b1 => comp_bop bop_eq (comp_bexp b1) (ret (val_nat 0, []))
  end.

(** ** Correspondence between concrete and abstract CFGs. *)

(** Asserts that the instruction sequence found at program point p in 
    the control-flow graph g is exactly the list [is]. *)

Fixpoint insns_at_pc (g:ListCFG.t) (p:pc) (is:list insn) : Prop := 
  match is with
    | nil => True
    | i :: is' => insn_at_pc g p i /\ insns_at_pc g (incr_pc p) is'
  end.

(** Looking up the block labeled [l] in the concrete represenation
    agrees with the declarative specification. *)

Lemma cfg_insns_at : forall g l is e,
  lookup g l = Some is ->
  insns_at_pc (e, g) (block_entry l) is.
(* FOLD *)
Proof.
  intros.
  pose (k:=@nil insn). change is with (k ++ is) in H.
  unfold block_entry. change 0 with (length k).
  clearbody k. generalize dependent k.
  induction is; intros. simpl; auto.
    simpl. split. eexists. split.
    unfold lookup in H.
    apply assoc_in in H. simpl; eauto.
    clear H. induction k; simpl; auto.
    replace (S (length k)) with (length (k ++ [a])). apply IHis.
      rewrite <- app_assoc. auto. rewrite app_length.
      simpl. apply PeanoNat.Nat.add_1_r.
Qed.
(* /FOLD *)

(** ** Auxiliary definitions. *)

Definition ids_preserved (cs:list uid) (st st':state) : Prop :=
  forall uid n, In uid cs -> 
    st_loc st uid = Some n -> st_loc st' uid = Some n.

Definition good_return (cs:list uid) (v:val) : Prop :=
  forall uid, v = val_uid uid -> In uid cs.

Definition ctx_incr (cs cs':list uid) : Prop :=
  forall uid, In uid cs -> In uid cs'.

Instance ctx_incr_trans : Transitive ctx_incr.
(* FOLD *)
Proof. red; unfold ctx_incr; intuition. Qed.
(* /FOLD *)


Ltac bind_step H :=
  match type of H with
    | context[(bind ?ma ?f) ?s] => 
        unfold bind at 1 in H; 
        destruct (ma s) as [?cs1 ?r1] eqn:?Hc1
    | context[(bind2 ?ma ?f) ?s] =>
        unfold bind2 at 1 in H;
        destruct (ma s) as [?cs1 [?rl1 ?rr1]] eqn:?Hc1
  end.

Definition comp_correct (comp : ectmon (val * list insn))
                        (eval : mem -> nat) : Prop :=
  forall cs cs' g st is k v,
  (cs', (v, is)) = comp cs ->
  insns_at_pc g (st_pc st) (is ++ k) ->
  exists st',
    st_mem st' = st_mem st /\
    insns_at_pc g (st_pc st') k /\
    star (Opsem.step g) st st' /\
    ids_preserved cs st st' /\
    good_return cs' v /\
    ctx_incr cs cs' /\
    eval_val (st_loc st') v = Some (eval (st_mem st)).

Lemma comp_bop_correct : forall b comp1 comp2 eval1 eval2
    (IHa1: comp_correct comp1 eval1)
    (IHa2: comp_correct comp2 eval2),
    comp_correct (comp_bop b comp1 comp2)
                 (fun m => bop_denote b (eval1 m) (eval2 m)).
(* FOLD *)
Proof.
  unfold comp_correct. 
  intros b comp1 comp2 eval1 eval2.
  intros until v. intros Hcomp Hinsns.

  unfold comp_bop in Hcomp.
  repeat bind_step Hcomp.
  inversion Hcomp; clear Hcomp. subst v is.

  repeat rewrite <- app_assoc in Hinsns.
  eelim IHa1; [| eauto ..]. 
  intros st1 (Hinv1 & His1 & Hstep1 & Hpres1 & Hret1 & Hincr1 & Heval1).
  eelim IHa2; [| eauto ..]. 
  intros st2 (Hinv2 & His2 & Hstep2 & Hpres2 & Hret2 & Hincr2 & Heval2).
  clear IHa1 IHa2.
  
  rename st2 into st2'; set (st2:=st2') in *; destruct st2'.
  eexists {| st_pc  := incr_pc (st_pc st2);
             st_loc := Locals.update (st_loc st2) r1 _ |}. simpl.

  (* exp_invar *)
  split. transitivity (st_mem st1); [ transitivity (st_mem st2); auto | auto].

  (* insns_at_pc *)
  split. inversion His2. auto.

  (* star (Opsem.step g) *)
  split. eapply star_trans; eauto. eapply star_trans; eauto.
    eapply star_one. eapply step_bop. inversion His2; eauto.  
    unfold eval_bop. simpl in Heval2. rewrite Heval2. 
    replace (eval_val st_loc0 _) with (Some (eval1 (st_mem st))).
    reflexivity. symmetry. 

    destruct rl1; auto. simpl. 
    unfold good_return in *.
    assert (In t0 cs1). apply Hret1; auto.
    unfold ids_preserved in Hpres2.
    apply Hpres2. auto. auto.

  (* ids_preserved *)
  split. red; simpl; intros. rewrite Locals.update_neq.
  change st_loc0 with (st_loc st2).
  apply Hpres2; auto. apply Hincr1, Hincr2 in H.
  inversion Hc2. contradict H. rewrite <- H. apply Uid.fresh_not_in.

  (* good_return *)
  split. red. intros uid' Hid. injection Hid; inversion Hc2. left; auto.

  (* ctx_incr *)
  split. transitivity cs1; auto. transitivity cs0; auto. 
  unfold ctx_incr. inversion Hc2; intros. right; auto.

  (* eval_val *)
  simpl. rewrite Locals.update_eq.
  replace (st_mem st1) with (st_mem st). subst. reflexivity. 
  inversion Hinv1; auto. reflexivity.
Qed.
(* /FOLD *)


Lemma comp_aexp_correct : forall (a:aexp),
  comp_correct (comp_aexp a) (aeval a).
(* FOLD *)
Proof.
  (* comp_bop_correct takes care of all the inductive cases *)
  induction a; [ | | eapply comp_bop_correct; auto ..].

  - (* Case "ANum". *)
  unfold comp_correct; intros. inversion H; subst; clear H. 
  exists st. repeat split; try red; auto using star_refl. discriminate.

  - (* Case "AId". *)
  unfold comp_correct. intros cs cs' g st is k v Hcomp Hinsns.
  simpl in Hcomp. unfold bind in Hcomp. 
  destruct (fresh cs) as [cs1 idr] eqn:Hc.
  inversion Hcomp. clear Hcomp. subst.

  rename st into st'. set (st := st'). destruct st'.
  eexists {| st_pc := (incr_pc (st_pc st));
             st_loc := Locals.update (st_loc st) idr _ |}. simpl.
  split. reflexivity.
  split. inversion Hinsns; auto.
  split. apply star_one. apply step_load.
    inversion Hinsns; eauto.
  split. red; simpl; intros. rewrite Locals.update_neq; auto. 
    inversion Hc. contradict H. rewrite <- H. apply Uid.fresh_not_in.
  split. red. intros. inversion Hc. injection H; intro. subst idr uid. left; auto.
  split. inversion Hc; red; intuition.
  rewrite Locals.update_eq; reflexivity.
Qed.
(* /FOLD *)

Local Hint Resolve comp_aexp_correct.

Lemma comp_bexp_correct : forall (b:bexp),
  comp_correct (comp_bexp b) (fun m => b2n (beval b m)).
(* FOLD *)
Proof.
  induction b.

  - (* Case "BTrue". *)
  unfold comp_correct; intros. inversion H; subst; clear H. 
  exists st; repeat split; try red; auto using star_refl. discriminate.

  - (* Case "BFalse". *)
  unfold comp_correct; intros. inversion H; subst; clear H. 
  exists st; repeat split; try red; auto using star_refl. discriminate.

  - (* Case "BEq". *)
  eapply (comp_bop_correct bop_eq); auto.

  - (* Case "BLe". *)
  eapply (comp_bop_correct bop_le); auto.

  - (* Case "BNot". *)
  simpl. evar (SPEC : mem -> nat). replace (fun (m:mem) => b2n _) with SPEC.
  subst SPEC. apply (comp_bop_correct bop_eq); eauto.
  unfold comp_correct; intros. inversion H; subst; clear H.
  instantiate (1:=fun m => 0).
  exists st; repeat split; try red; auto using star_refl. discriminate.
  unfold SPEC. apply functional_extensionality. intro.
  destruct (beval b x); auto.

  - (* Case "BAnd". *)
  simpl. evar (SPEC : mem -> nat). replace (fun (m:mem) => b2n _) with SPEC.
  subst SPEC. apply (comp_bop_correct bop_and); eauto.
  subst SPEC. apply functional_extensionality. intro. 
  simpl. destruct (beval b1 x), (beval b2 x); auto.
Qed.
(* /FOLD *)


(**
  - First we define some helper definitions for compiling assignments and 
    conditionals.
    - To simplify the simulation: each store is compiled to its own basic block.
  - Then we define the command compilation context as a state monad.
    - Generate fresh uids (like the [ectmon])
    - Generate fresh block labels 
    - Add instructions to the (partial) CFG
  - Then we define the translation of commands (recursively).
*)

Definition comp_store (a:aexp) (v:addr) (lr:lbl) : ectmon (list insn) :=
  do x <- fresh;
  do y <- fresh;
  do (i, is) <- comp_aexp a; 
  ret (is ++ [ (x, cmd_store v i); 
               (y, cmd_tmn (tmn_jmp lr)) ]).

Definition comp_cond (b:bexp) (l1 l2:lbl) : ectmon (list insn) :=
  do (v, is) <- comp_bexp b;
  do x <- fresh;
  ret (is ++ [ (x, cmd_tmn (tmn_cbr v l1 l2)) ] ).

Lemma comp_store_correct : 
  forall g a v le lr cs st,
  insns_at_pc g (block_entry le) (steval (comp_store a v lr) cs) ->
  st_pc st = (block_entry le) ->
  exists st',
    plus (step g) st st' /\
    st_pc st' = (block_entry lr) /\
    st_mem st' = (Memory.update (st_mem st) v (aeval a (st_mem st))).
(* FOLD *)
Proof.
  intros.
  unfold steval, comp_store in H.
  repeat bind_step H.
  simpl in H. symmetry in Hc2.
  
  rewrite <- H0 in H.
  eelim (comp_aexp_correct a); eauto.
  intros st' H'. decompose [and] H'; clear H'.
  rename st' into st''. set (st' := st'') in *. destruct st''.

  eexists.
  split. eapply plus_star_trans'. eauto. 
  eapply plus_left. eapply step_store. apply H3. eauto.
  eapply star_step. eapply step_tmn. inversion H3. apply H9.
  reflexivity.
  eapply star_refl.
  simpl. split; auto.
  rewrite <- H1. reflexivity.
Qed.
(* /FOLD *)


Lemma comp_cond_correct :
  forall g cs b le l1 l2 st,
  insns_at_pc g (block_entry le) (steval (comp_cond b l1 l2) cs) ->
  st_pc st = (block_entry le) ->
  exists st',
    plus (step g) st st' /\
    st_pc st' = block_entry (if beval b (st_mem st) then l1 else l2) /\
    st_mem st = st_mem st'.
(* FOLD *)
Proof.
  intros.
  unfold steval, comp_cond in H.
  repeat bind_step H. simpl in H.

  rewrite <- H0 in H.
  eelim (comp_bexp_correct b); eauto.
  intros st' H'. decompose [and] H'; clear H'.
  rename st' into st''. set (st' := st'') in *. destruct st''.

  eexists.
  split. eapply plus_star_trans'. eauto. 
  eapply plus_one. eapply step_tmn. 
  apply H3. simpl in *. rewrite H8. reflexivity.
  simpl. split; auto.
  destruct (beval b (st_mem st)); simpl; auto.
Qed.
(* /FOLD *)
  

(* ** Compiling Commands *)

(** State:
    - list of used block labels
    - list of used uids
    - current cfg *)

Definition cstate := (list lbl * list uid * list block)%type.
Notation ctmon := (stmon cstate).

Definition fresh_lbl : ctmon lbl :=
  fun cs =>
  let '(ls, is, bs) := cs in
  let l := Lbl.fresh ls in 
  (l::ls, is, update bs l [], l).

Definition raise_ectmon {T} (ec:ectmon T) : ctmon T :=
  fun cs =>
  let '(ls, is, cfg) := cs in
  let (is', r) := ec is in
  (ls, is', cfg, r).

Definition add_insns (l:lbl) (b:list insn) : ctmon unit :=
  fun cs =>
  let '(ls, is, cfg) := cs in
  (ls, is, update cfg l b, tt).

Open Scope stmon.

(** The input [lr] is the label of the block to which
    control should return after the command is done. 
    The output is the label of the entry block for the
    command. *)

Fixpoint comp_com (c:Imp.com) (lr:lbl) : ctmon lbl :=
  match c with
    | CSkip => ret lr
    | CAss i a => 
        do l <- fresh_lbl;
        do b <- raise_ectmon (comp_store a i lr);
        do _ <- add_insns l b;
        ret l
    | CSeq c1 c2 =>
        do l <- comp_com c2 lr; comp_com c1 l
    | CIf b c1 c2 =>
        do l1 <- comp_com c1 lr;
        do l2 <- comp_com c2 lr;
        do lh <- fresh_lbl;
        do b  <- raise_ectmon (comp_cond b l1 l2);
        do _  <- add_insns lh b;
        ret lh
    | CWhile b c => 
        do lh <- fresh_lbl;
        do lb <- comp_com c lh;
        do b  <- raise_ectmon (comp_cond b lb lr);
        do _  <- add_insns lh b;
        ret lh
  end.

Open Scope imp_scope.

(** * Correctness? *)

(** - Vminus is deterministic
    - Suffices to show a forward simulation. *)

(** ** Simulation relation. *)

(** Relate Imp commands to sequences of basic blocks in the cfg. *)

Inductive match_config : Imp.com -> (cfg * lbl * lbl) -> Prop :=
  | MC_Skip : forall bs l,
      match_config SKIP (bs, l, l)
  | MC_Ass : forall g l l' uid a cs,
      insns_at_pc g (block_entry l) (steval (comp_store a uid l') cs) ->
      match_config (CAss uid a) (g, l, l')
  | MC_Seq : forall g l1 l2 l3 c1 c2,
      match_config c1 (g, l1, l2) ->
      match_config c2 (g, l2, l3) ->
      match_config (CSeq c1 c2) (g, l1, l3)
  | MC_If : forall g le lr l1 l2 b c1 c2 cs,
      match_config c1 (g, l1, lr) ->
      match_config c2 (g, l2, lr) ->
      insns_at_pc g (block_entry le) (steval (comp_cond b l1 l2) cs) ->
      match_config (CIf b c1 c2) (g, le, lr)
  | MC_While : forall g le lb lr b c cs,
      match_config c (g, lb, le) ->
      insns_at_pc g (block_entry le) (steval (comp_cond b lb lr) cs) ->
      match_config (CWhile b c) (g, le, lr).

Inductive match_states (g:cfg) (r:lbl)
  : (com * Imp.state) -> Opsem.state -> Prop :=
  match_states_intro : forall c mem st l,
    match_config c (g, l, r) ->
    st_pc st = block_entry l ->
    st_mem st = mem ->
    match_states g r (c, mem) st.


Require Import Program.Equality.

(** ** Translation simulation: First try. *)

Lemma simulation_step' :
  forall g c c' mem mem' st r,
  Imp.step (c, mem) (c', mem') ->
  match_states g r (c, mem) st ->
  exists st',
    star (Opsem.step g) st st' /\
    match_states g r (c', mem') st'.
(* FOLD *)
Proof.
  intros. generalize dependent st. revert r.
  
  dependent induction H; intros;
  inversion H0 as [? ? ? ? H']; inversion H'; subst.

  - (* Case "S_Ass". *)
  eapply comp_store_correct in H6 as [st' [? [? ?]]]; eauto.
  eexists. split. apply plus_star. apply H1. econstructor; eauto. apply MC_Skip. 

  - (* Case "S_Seq". *)
    specialize (IHstep c1 c1' (st_mem st) mem').
    pose (K:=IHstep ltac:(auto) ltac:(auto)); clearbody K; clear IHstep.
    specialize (K l2 st).
    lapply K.
    intros [st' [? ?]].
    exists st'. split; auto.
    inversion H3. 
    econstructor; eauto. econstructor; eauto.
    econstructor; eauto.  

  - (* Case "S_SeqSkip". *)
  exists st. split. apply star_refl.
  inversion H'; subst. inversion H4; subst.
  econstructor; eauto.

  - (* Case "S_IfTrue". *)
  eapply comp_cond_correct in H14 as [st' [? [? ?]]].
  exists st'. split. apply plus_star; eauto. econstructor. 
  eauto. rewrite H in H3. auto. symmetry; auto. auto.

  - (* Case "S_IfFalse". *)
  eapply comp_cond_correct in H14 as [st' [? [? ?]]].
  exists st'. split. apply plus_star; eauto. econstructor. 
  eauto. rewrite H in H3. auto. symmetry; auto. auto.

  - (* Case "S_While". *)
  exists st. split. apply star_refl. 
  econstructor; eauto. eapply MC_If; eauto.
  econstructor; eauto. apply MC_Skip; eauto.
Qed.
(* /FOLD *)

(** * Stuttering *)

(** The proof above goes through, but does not ensure that if the
    source program diverges the compiled program does not go wrong! 

    To fix it, we need to ensure that there is no "infinite stuttering"
    in which the source program takes an infinite number of steps while 
    the target terminates (or gets stuck).
*)

(** ** Eliminating Stuttering *)

(** First, define an appropriate measure. *)

Fixpoint num_skips (c:com) : nat :=
  match c with
    | (c1 ;; c2) => num_skips c1 + num_skips c2
    | SKIP => 2
    | _ => 0
  end.

Fixpoint while_head (c:com) : nat :=
  match c with
    | (c1 ;; _) => while_head c1
    | WHILE _ DO _ END => 1
    | _ => 0
  end.

Definition com_size (c:com) : nat := num_skips c + while_head c.

(** ** Lemmas about the measure. *)

Require Import Omega.

Lemma while_head_bound : forall c, while_head c < 2.
(* FOLD *)
Proof. induction c; simpl; omega. Qed.
(* /FOLD *)

Lemma com_size_seq : forall c1 c1' c2,
  com_size c1' < com_size c1 ->
  com_size (c1';; c2) < com_size (c1;; c2).
(* FOLD *)
Proof.
  unfold com_size; destruct c1, c1'; 
  try solve [simpl; intros; omega].
Qed.
(* /FOLD *) 

Lemma com_size_seqskip : forall c,
  com_size c < com_size (SKIP;; c).
(* FOLD *)
Proof.
  unfold com_size; destruct c;
  try solve [simpl; try match goal with
                        | |- context[while_head ?X] => 
                             pose proof (while_head_bound X)
                        end; intros; omega].
Qed.


(* lift to states *)
Definition imp_size (st:com * mem) : nat := 
  let (c, _) := st in com_size c.


(* /FOLD *)

Local Hint Constructors match_config.
Hint Resolve com_size_seqskip com_size_seq.

(** ** Final simulation relation. *)

Lemma transl_sim_step_final :
  forall g r imp_st imp_st' vmn_st,
  Imp.step imp_st imp_st' ->
  match_states g r imp_st vmn_st ->
  exists vmn_st',
    (plus (Opsem.step g) vmn_st vmn_st' \/
     star (Opsem.step g) vmn_st vmn_st' /\ imp_size imp_st' < imp_size imp_st) /\
    match_states g r imp_st' vmn_st'.
(* FOLD *)
Proof.
  intros. generalize dependent vmn_st. revert r.
  
  dependent induction H; intros r vmn_st Hst;
  inversion Hst as [? ? ? ? Hcfg]; inversion Hcfg; subst.

  - (* Case "S_Ass". *)
  eapply comp_store_correct in H6 as [st' [? [? ?]]]; eauto.
  eexists. split; eauto. econstructor; eauto.
  
  - (* Case "S_Seq". *)
  specialize (IHstep l2 vmn_st).
  lapply IHstep. intros [vmn_st' [? ?]]. exists vmn_st'. split. 
  simpl in *; intuition. inversion H2; subst. 
  econstructor; eauto. econstructor; eauto.

  - (* Case "S_SeqSkip". *)
  exists vmn_st. split. right. 
  split. apply star_refl. unfold imp_size. 
  simpl; intuition. inversion H7; subst. econstructor; eauto.

  - (* Case "S_IfTrue". *)
  eapply comp_cond_correct in H13 as [st' [? [? ?]]]; eauto.
  exists st'. split; eauto. econstructor; eauto. 
  rewrite H in H2; auto. 

  - (* Case "S_IfFalse". *)
  eapply comp_cond_correct in H13 as [st' [? [? ?]]]; eauto.
  exists st'. split; eauto. econstructor; eauto.  
  rewrite H in H2; auto. 

  - (* Case "S_While". *)
  exists vmn_st. split. right; intuition. apply star_refl. 
  econstructor; eauto. 
Qed.
(* /FOLD *)

(** Is this enough? *)

(** ** Relating initial states *)

(** We still must relate the initial states! *)

(** First, some helpers: *)

Require Import LtacDebug.

Lemma comp_store_not_nil : forall a v l cs,
  steval (comp_store a v l) cs <> [].
(* FOLD *)
Proof.
  intros. unfold steval.
  remember (comp_store _ _ _ _) as ma.
  unfold comp_store in Heqma.
  repeat bind_step Heqma. subst ma; simpl. intro.
  eapply app_cons_not_nil; eauto.
Qed.
(* /FOLD *)

Lemma comp_cond_not_nil : forall b v l cs,
  steval (comp_cond b v l) cs <> [].
(* FOLD *)
Proof.
  intros. unfold steval.
  remember (comp_cond _ _ _ _) as ma.
  unfold comp_cond in Heqma.
  repeat bind_step Heqma. subst ma; simpl. intro.
  eapply app_cons_not_nil; eauto.
Qed.
(* /FOLD *)

(** ** Compilation invariant *)

(** Compilation only "extends" the compilation state:
    - Uids and labels change only monotonically.
    - Compilation never removes code.
  *) 

Inductive cstate_incr : cstate -> cstate -> Prop :=
  cstate_incr_intro : forall ls ls' ids ids' g g',
    (forall l, In l ls -> In l ls') ->
    (forall l is, In l ls -> is <> nil ->
      lookup g  l = Some is -> lookup g' l = Some is) ->
    cstate_incr (ls, ids, g) (ls', ids', g').

Instance cstate_incr_trans : Transitive cstate_incr.
(* FOLD *)
Proof.
  red. inversion 1. inversion 1. constructor; intuition.
Qed.
(* /FOLD *)

Inductive cstate_incr_strong : cstate -> cstate -> Prop :=
  cstate_incr_strong_intro : forall ls ls' ids ids' g g',
    (forall l, In l ls -> In l ls') ->
    (forall l, In l ls -> lookup g l = lookup g' l) ->
    cstate_incr_strong (ls, ids, g) (ls', ids', g').

Instance cstate_incr_strong_trans : Transitive cstate_incr_strong.
(* FOLD *)
Proof.
  red. inversion 1. inversion 1. subst. constructor. 
  auto. intros. transitivity (lookup g' l); eauto.
Qed.
(* /FOLD *)


Instance cstate_incr_strong_refl : Reflexive cstate_incr_strong.
(* FOLD *)
Proof.
  red. intro cs. destruct cs as [[? ?] ?]. constructor; auto.
Qed.
(* /FOLD *)


Lemma add_insns_incr : forall l is g ls ids cs',
  lookup g l = Some [] ->
  add_insns l is (ls, ids, g) = (cs', tt) ->
  cstate_incr (ls, ids, g) cs'.
(* FOLD *)
Proof.
  destruct cs' as [[? ?] ?]. intros.
  constructor. inversion H0; intuition.
  intros. inversion H0; subst. rewrite update_neq. auto.
  contradict H2. subst l. rewrite H3 in H. injection H; auto.
Qed.
(* /FOLD *)


Lemma ectmon_incr_strong : 
  forall (A:Type) (m:ectmon A) (r:A) cs cs' ,
  raise_ectmon m cs = (cs', r) ->
  cstate_incr_strong cs cs'.
(* FOLD *)
Proof.
  destruct cs as [[? ?] ?], cs' as [[? ?] ?].
  inversion 1.
  destruct (m l0). inversion H1; subst; clear H1.
  constructor; auto; intros. 
Qed.
(* /FOLD *)


Lemma fresh_add_incr_strong :
  forall l is cs1 cs2 cs3 cs4,
  fresh_lbl cs1 = (cs2, l) ->
  cstate_incr_strong cs2 cs3 ->
  add_insns l is cs3 = (cs4, tt) ->
  cstate_incr_strong cs1 cs4.
(* FOLD *)
Proof.
  intros until cs4. intros Hfresh Hincr Hadd.
  destruct cs1 as [[? ?] ?], cs2 as [[? ?] ?],
           cs3 as [[? ?] ?], cs4 as [[? ?] ?].
  inversion Hadd; inversion Hfresh; inversion Hincr; subst.

  constructor; intros. apply H8. right; auto.
  assert (Lbl.fresh l0 <> l).
    contradict H. rewrite <- H. apply Lbl.fresh_not_in.
  rewrite update_neq; auto. rewrite <- H13.
  rewrite update_neq; auto. right; auto.
Qed.
(* /FOLD *)


Lemma comp_com_incr_strong: forall c cst cst' e r,
  comp_com c r cst = (cst', e) -> cstate_incr_strong cst cst'.
(* FOLD *)
Proof.
  induction c; intros cst cst' e r Htr;
  simpl in Htr; repeat bind_step Htr; 
  inversion Htr; subst; clear Htr.
  
  - (* Case "CSkip".*)
    reflexivity. 

  - (* Case "CAss". *)
  destruct r2.
  eapply fresh_add_incr_strong; eauto.
  eapply ectmon_incr_strong; eauto. 

  - (* Case "CSeq". *)
  transitivity cs1. 
  eapply IHc2; eauto. eapply IHc1; eauto.

  - (* Case "CIf". *)
  destruct r4.
  transitivity cs1. eapply IHc1; eauto.
  transitivity cs0. eapply IHc2; eauto.
  eapply fresh_add_incr_strong; eauto. 
  eapply ectmon_incr_strong; eauto.

  - (* Case "CWhile". *)
  destruct r3.
  eapply fresh_add_incr_strong.
  eauto. transitivity cs0. eapply IHc; eauto.
  eapply ectmon_incr_strong; eauto. eauto.
Qed.
(* /FOLD *)
  

Lemma cstate_incr_weaken : forall cst cst',
  cstate_incr_strong cst cst' ->
  cstate_incr cst cst'.
(* FOLD *)
Proof.
  inversion 1. constructor. auto. intros. rewrite <- H1; auto.
Qed.
(* /FOLD *)

Lemma comp_com_incr: forall c cst cst' e r,
  comp_com c r cst = (cst', e) -> cstate_incr cst cst'.
(* FOLD *)
Proof.
  intros. apply cstate_incr_weaken.
  eapply comp_com_incr_strong; eauto.
Qed.
(* /FOLD *)

(** ** Relating Initial Compilation *)

(** The key lemma is: *)

Lemma match_init : forall c le lr csti cst x g' e,
  comp_com c lr csti = (cst, le) ->
  cstate_incr cst (x, g') ->
  match_config c (e, g', le, lr).
(* FOLD *)
Proof.
  induction c; intros.
  
  - (* Case "CSkip". *)
  inversion H; subst. apply MC_Skip.

  - (* Case "CAss". *)
  simpl in H. repeat bind_step H.
  inversion H; subst; clear H. destruct r2.

  destruct cs1 as [[? ?] ?], csti as [[? ?] ?].
  inversion Hc0 as [Hcomp]. destruct (comp_store _ _ _ _) eqn:Hc'. 
  inversion Hcomp; subst; clear Hcomp.
  inversion Hc1; subst. inversion Hc2; subst.

  eapply MC_Ass, cfg_insns_at.
  inversion H0; subst. apply H6. left; auto.
  apply comp_store_not_nil. rewrite update_eq; auto. 
  f_equal. rewrite surjective_pairing in Hc' at 1. 
  inversion Hc'. reflexivity.

  - (* Case "CSeq". *)
  simpl in H. repeat bind_step H.
  eapply MC_Seq. eapply IHc1; eauto. eapply IHc2; eauto.
  transitivity cst; eauto. eapply comp_com_incr; eauto.

  - (* Case "CIf". *)
  simpl in H. repeat bind_step H.
  inversion H; subst; clear H. destruct r4.

  destruct cs2 as [[? ?] ?]. eapply MC_If.

  eapply IHc1; eauto.
  transitivity cs0. eapply comp_com_incr; eauto.
  transitivity cst; eauto. eapply cstate_incr_weaken. 
    eapply fresh_add_incr_strong; eauto.
    eapply ectmon_incr_strong; eauto.

  eapply IHc2; eauto.
  transitivity cst; eauto. eapply cstate_incr_weaken.
    eapply fresh_add_incr_strong; eauto.
    eapply ectmon_incr_strong; eauto.

  destruct cs0 as [[? ?] ?].
  inversion Hc3 as [Hcomp]. destruct (comp_cond _ _ _ _) eqn:Hc'.
  inversion Hcomp; subst; clear Hcomp.
  inversion Hc2; subst. inversion Hc4; subst.

  apply cfg_insns_at. inversion H0; subst. apply H6. left; auto.
  apply comp_cond_not_nil. rewrite update_eq; auto. 
  f_equal. rewrite surjective_pairing in Hc' at 1. 
  inversion Hc'. reflexivity.

  - (* Case "CWhile". *)
  simpl in H. repeat bind_step H.
  inversion H; subst; clear H. destruct r3.
  
  destruct cs0 as [[? ?] ?], csti as [[? ?] ?].
  inversion Hc2 as [Hcomp]. destruct (comp_cond _ _ _ _) eqn:Hc'.
  inversion Hcomp; subst; clear Hcomp.

  eapply MC_While.
  eapply IHc. eauto.
  transitivity cst; eauto.
  transitivity (l, l5, l1).
  eapply cstate_incr_weaken. eapply ectmon_incr_strong; eauto.

  eapply add_insns_incr; eauto.
  apply comp_com_incr_strong in Hc0. 
  inversion Hc0; subst. inversion Hc1; subst.
  rewrite <- H5. rewrite update_eq; auto. left; auto.

  apply cfg_insns_at.
  inversion H0; subst. inversion Hc3; subst.

  apply H4. apply comp_com_incr_strong in Hc0. 
  inversion Hc0; subst. inversion Hc1; subst.
  apply H5. left; auto.

  apply comp_cond_not_nil. rewrite update_eq; auto.
  f_equal. rewrite surjective_pairing in Hc' at 1. 
  inversion Hc'. reflexivity.
Qed.
(* /FOLD *)


(* adapted from Leroy, OPLSS '12 Compil.v *)
(* Generic simulation proof. *)

Section SIMULATION_DIAGRAM.

Variable state1: Type.	                          (* source states *)
Variable step1: state1 -> state1 -> Prop.         (* source step relation *)

Variable state2: Type.	                          (* target states *)
Variable step2: state2 -> state2 -> Prop.         (* target step relation *)

Variable match_states: state1 -> state2 -> Prop.  (* the invariant *)

Variable measure: state1 -> nat.                  (* for stuttering *)

Hypothesis simulation:
  forall S1 S1' S2,
  step1 S1 S1' -> match_states S1 S2 ->
  exists S2',
    (plus step2 S2 S2' \/ 
     star step2 S2 S2' /\ measure S1' < measure S1) /\
    match_states S1' S2'.

Lemma simulation_star:
  forall S1 S1', star step1 S1 S1' ->
  forall S2, match_states S1 S2 ->
  exists S2', star step2 S2 S2' /\ match_states S1' S2'.
Proof.
  induction 1; intros.

  - (* Case "zero transition". *)
  exists S2; split. apply star_refl. auto.

  - (* Case "one or more transitions". *)
  destruct (simulation _ _ _ H H1) as [S2' [P Q]].
  destruct (IHstar _ Q) as [S2'' [U V]].
  exists S2''; split. 
  eapply star_trans; eauto. destruct P. 
  apply plus_star; auto. destruct H2; auto.
  auto.
Qed.

Lemma simulation_infseq_productive:
  forall N S1 S2,
  measure S1 < N ->
  infseq step1 S1 ->
  match_states S1 S2 ->
  exists S1', exists S2',
      plus step2 S2 S2'
   /\ infseq step1 S1'
   /\ match_states S1' S2'.
Proof.
  induction N; intros. 
  - (* Case "N = 0". *)
  omega. 
  - (* Case "N > 0". *)
  inversion H0; clear H0; subst.
  destruct (simulation _ _ _ H2 H1) as [S2' [P Q]].
  destruct P.
  + (* SCase "one or several transitions". *)
  exists b; exists S2'; auto.
  + (* SCase "zero, one or several transitions". *)
  destruct H0. inversion H0; clear H0; subst.
    * (* SSCase "zero transitions". *)
    eapply IHN; eauto. omega.
    * (* SSCase "one or several transitions". *)
    exists b; exists S2'; split. eapply plus_left; eauto. auto.
Qed.

Lemma simulation_infseq:
  forall S1 S2,
  infseq step1 S1 ->
  match_states S1 S2 ->
  infseq step2 S2.
Proof.
  intros. 
  apply infseq_coinduction_principle_2 with
    (X := fun S2 => exists S1, infseq step1 S1 /\ match_states S1 S2).
  intros. destruct H1 as [S [A B]]. 
  destruct (simulation_infseq_productive (measure S + 1) S a) 
  as [S1' [S2' [P [Q R]]]].
  omega. auto. auto.
  exists S2'; split. auto. exists S1'; auto. 
  exists S1; auto.
Qed.

End SIMULATION_DIAGRAM.


Definition vminus_terminates (g:cfg) (m m':mem) : Prop :=
  exists x st',
    insns_at_pc g st'.(st_pc) [(x, cmd_tmn tmn_ret)] /\
    st'.(st_mem) = m' /\
    star (Opsem.step g) (init_state g m) st'.
  
Definition vminus_diverges (g:cfg) (m:mem) : Prop :=
  infseq (Opsem.step g) (init_state g m).

Definition imp_terminates (c: com) (m m':mem) : Prop :=
  star Imp.step (c, m) (SKIP, m').

Definition imp_diverges (c: com) (mem: mem) : Prop :=
  infseq Imp.step (c, mem).

Definition comp_prog (c:com) : ctmon (lbl * lbl) :=
  do r <- fresh_lbl;
  do x <- raise_ectmon fresh;
  do _ <- add_insns r [(x, cmd_tmn tmn_ret)];
  do e <- comp_com c r;
  ret (e, r).

(* TODO: le is redundant ... fix up match_config *)
Definition compile (c:com) : cfg * lbl * lbl :=
  let '(_, _, bs, (le, lr)) := comp_prog c ([], [], []) in
    ((le, bs), le, lr).

Lemma match_config_ret : forall g le lr c,
  (g, le, lr) = compile c ->
  exists x, insns_at_pc g (block_entry lr) [(x, cmd_tmn tmn_ret)].
Proof.
  intros. unfold compile, comp_prog in H. repeat bind_step H.
  destruct cs3 as [[? ?] ?], cs1 as [[? ?] ?], cs0 as [[? ?] ?]. 
  inversion H; subst; clear H. destruct r2.
  inversion Hc2; subst.
  
  eexists. eapply cfg_insns_at. apply comp_com_incr_strong in Hc3.
  inversion Hc3; subst. rewrite <- H6. rewrite update_eq; auto. 

  inversion Hc1; subst. inversion Hc0; subst. left; auto.
Qed.

Lemma match_config_initial : forall g le lr c m,
  (g, le, lr) = compile c ->
  match_states g lr (c, m) (init_state g m).
Proof.
  intros. unfold compile, comp_prog in H. repeat bind_step H.
  destruct cs3 as [[? ?] ?], cs1 as [[? ?] ?].
  inversion H; subst; clear H.

  inversion Hc1; subst; clear Hc1.
  econstructor; simpl; eauto.

  eapply match_init. eauto. eapply cstate_incr_weaken. 
  eapply cstate_incr_strong_refl.
Qed.

Theorem compile_program_correct_terminating:
  forall c m m' g le lr,
  (g, le, lr) = compile c ->
  imp_terminates c m m' ->
  vminus_terminates g m m'.
Proof.
  intros. unfold imp_terminates in H.
  assert (exists machconf2, 
           star (Opsem.step g) (init_state g m) machconf2
           /\ match_states g lr (SKIP, m') machconf2).
  eapply simulation_star; eauto. eapply transl_sim_step_final. 
  eapply match_config_initial; eauto.
  destruct H1 as [machconf2 [STAR MS]]. 
  inversion MS; subst.
  eelim match_config_ret. intros.
  red. exists x, machconf2. split. rewrite H4. eauto. eauto. 
  inversion H3; subst. eauto.
Qed.

Theorem compile_program_correct_diverging:
  forall c m g le lr,
  (g, le, lr) = compile c ->
  imp_diverges c m ->
  vminus_diverges g m.
Proof.
  intros; red; intros. 
  eapply simulation_infseq with (match_states := match_states g lr); eauto.
  eapply transl_sim_step_final. eapply match_config_initial; eauto.
Qed.
