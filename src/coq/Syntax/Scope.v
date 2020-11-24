(* begin hide *)
From Coq Require Import
     List.
Import ListNotations.

From Vellvm Require Import
     Numeric.Coqlib
     Utils.Util
     Utils.Tactics
     Syntax.LLVMAst
     Syntax.CFG
     Syntax.TypToDtyp.

From ExtLib Require Import List.
(* end hide *)

(** * Scoping
    We define through this file several functions and predicates having to do with the scope
    of VIR programs, w.r.t. both block identifiers and local variables.
    We unfortunately inherit from LLVM IR a fully named representation of variables, forcing
    on us fairly heavy sanity checks.
    - [inputs]: input labels of an [ocfg]
    - [outputs]: output labels of an [ocfg]
    - [wf_ocfg_bid]: no duplicate block identifiers


 *)

(** * Well-formedness w.r.t. block identifiers
    An [ocfg] should not admit any collisions w.r.t. to its labels.
 *)
Section LABELS_OPERATIONS.

  Context {T : Set}.

  (** * inputs
     Collect the list of input labels in an open control flow graph.
     Denoting an [ocfg] starting from a label out of this static list
     always results in the identity.
   *)
  Definition inputs (ocfg : @ocfg T) :=
    map blk_id ocfg.

  (** * outputs
     Collect the list of output labels in an open control flow graph.
     Denoting an [ocfg] starting from a label that belongs to its [inputs]
     will always result in a label in the static [output] list, or in a value.
   *)
  Definition terminator_outputs (term : terminator T) : list block_id
    := match term with
       | TERM_Ret v => []
       | TERM_Ret_void => []
       | TERM_Br v br1 br2 => [br1; br2]
       | TERM_Br_1 br => [br]
       | TERM_Switch v default_dest brs => default_dest :: map snd brs
       | TERM_IndirectBr v brs => brs
       | TERM_Resume v => []
       | TERM_Invoke fnptrval args to_label unwind_label => [to_label; unwind_label]
       end.

  Definition bk_outputs (bk : block T) : list block_id :=
    terminator_outputs (snd (blk_term bk)).

  Definition outputs (bks : ocfg T) : list block_id
    := fold_left (fun acc bk => acc ++ bk_outputs bk) bks [].

  (** * well-formed
      All labels in a list of blocks are distinct
   *)
  Definition wf_ocfg_bid (bks : ocfg T) : Prop :=
    list_norepet (map blk_id bks).

  Infix "⊍" := Coqlib.list_disjoint (at level 60).

  Definition no_reentrance (bks1 bks2 : ocfg T) : Prop :=
    outputs bks2 ⊍ inputs bks1.

  Definition no_duplicate_bid (bks1 bks2 : ocfg T) : Prop :=
    inputs bks1 ⊍ inputs bks2.

End LABELS_OPERATIONS.

Section DEF_SITES_OPERATIONS.

  Context {T : Set}.

  Definition def_sites_instr_id (id : instr_id) : list raw_id :=
    match id with
    | IId id => [id]
    | _ => []
    end.

  Definition def_sites_code (c : code T) : list raw_id :=
    List.fold_left (fun acc '(id,_) => match id with | IId id => id :: acc | _ => acc end) c [].

End DEF_SITES_OPERATIONS.

Section LABELS_THEORY.

  Context {T : Set}.

  Lemma wf_ocfg_bid_nil:
    wf_ocfg_bid (T := T) []. 
  Proof.
    intros; apply list_norepet_nil.
  Qed.

  Lemma wf_ocfg_bid_cons :
    forall (b : block T) bs,
      wf_ocfg_bid (b :: bs) ->
      wf_ocfg_bid bs.
  Proof.
    intros * NOREP; inv NOREP; eauto.
  Qed.

  Lemma wf_ocfg_bid_cons_not_in :
    forall (b : block T) bs,
      wf_ocfg_bid (b :: bs) ->
      not (In (blk_id b) (map blk_id bs)).
  Proof.
    intros * NOREP; inv NOREP; eauto.
  Qed.

  Lemma wf_ocfg_bid_app_r :
    forall (bs1 bs2 : ocfg T), 
      wf_ocfg_bid (bs1 ++ bs2) ->
      wf_ocfg_bid bs2.
  Proof.
    intros * NR.
    eapply list_norepet_append_right.
    unfold wf_ocfg_bid in NR.
    rewrite map_app in NR.
    eauto.
  Qed.

  Lemma wf_ocfg_bid_app_l :
    forall (bs1 bs2 : ocfg T), 
      wf_ocfg_bid (bs1 ++ bs2) ->
      wf_ocfg_bid bs1.
  Proof.
    intros * NR.
    eapply list_norepet_append_left.
    unfold wf_ocfg_bid in NR.
    rewrite map_app in NR.
    eauto.
  Qed.

  Lemma blk_id_convert_typ :
    forall env b,
      blk_id (convert_typ env b) = blk_id b.
  Proof.
    intros ? []; reflexivity.
  Qed.

  (* TODO: Show symmetric case *)
  Lemma wf_ocfg_bid_app_not_in_l :
    forall id (bs bs' : ocfg T),
      In id (inputs bs) ->
      wf_ocfg_bid (bs' ++ bs) ->
      not (In id (inputs bs')).
  Proof.
    intros. destruct bs.
    inversion H.
    inv H.
    apply wf_ocfg_bid_cons_not_in.
    unfold wf_ocfg_bid in *.
    rewrite map_app in H0.
    rewrite map_cons. rewrite map_cons in H0.
    rewrite list_cons_app in H0.
    rewrite app_assoc in H0.
    apply list_norepet_append_left in H0.
    rewrite list_cons_app.
    rewrite list_norepet_app in *.
    intuition. apply list_disjoint_sym. auto.
    unfold wf_ocfg_bid in H0.
    rewrite map_app in H0. rewrite map_cons in H0. rewrite list_cons_app in H0.
    apply list_norepet_append_commut in H0. rewrite <- app_assoc in H0.
    apply list_norepet_append_right in H0.
    rewrite list_norepet_app in H0.
    destruct H0 as (? & ? & ?).
    red in H2. intro. eapply H2; eauto.
  Qed.

  (* TODO: Show symmetric case *)
  Lemma wf_ocfg_app_not_in_r :
    forall id (bs bs' : ocfg T),
      In id (inputs bs) ->
      wf_ocfg_bid (bs' ++ bs) ->
      not (In id (inputs bs')).
  Proof.
    intros. destruct bs.
    inversion H.
    inv H.
    apply wf_ocfg_bid_cons_not_in.
    unfold wf_ocfg_bid in *.
    rewrite map_app in H0.
    rewrite map_cons. rewrite map_cons in H0.
    rewrite list_cons_app in H0.
    rewrite app_assoc in H0.
    apply list_norepet_append_left in H0.
    rewrite list_cons_app.
    rewrite list_norepet_app in *.
    intuition. apply list_disjoint_sym. auto.
    unfold wf_ocfg_bid in H0.
    rewrite map_app in H0. rewrite map_cons in H0. rewrite list_cons_app in H0.
    apply list_norepet_append_commut in H0. rewrite <- app_assoc in H0.
    apply list_norepet_append_right in H0.
    rewrite list_norepet_app in H0.
    destruct H0 as (? & ? & ?).
    red in H2. intro. eapply H2; eauto.
  Qed.

  Lemma outputs_acc: forall (bks: ocfg T) acc,
      fold_left (fun acc bk => acc ++ bk_outputs bk) bks acc =
      acc ++ fold_left (fun acc bk => acc ++ bk_outputs bk) bks [].
  Proof.
    induction bks using list_rev_ind; intros; cbn.
    - rewrite app_nil_r; reflexivity.
    - rewrite 2 fold_left_app, IHbks.
      cbn.
      rewrite app_assoc.
      reflexivity.
  Qed.

  Lemma outputs_app: forall l l',
      @outputs T (l ++ l') = outputs l ++ outputs l'.
  Proof.
    intros.
    unfold outputs at 1.
    rewrite fold_left_app, outputs_acc.
    reflexivity.
  Qed.

  Lemma outputs_cons: forall b l,
      @outputs T (b :: l) = bk_outputs b ++ outputs l.
  Proof.
    intros.
    rewrite list_cons_app, outputs_app; reflexivity.
  Qed.

  Lemma In_bk_outputs: forall bid br (b: block T) l,
      In br (bk_outputs b) ->
      find_block l bid = Some b ->
      In br (outputs l). 
  Proof.
    induction l as [| ? l IH].
    - cbn; intros ? abs; inv abs.
    - intros IN FIND.
      cbn in FIND.
      flatten_hyp FIND; inv FIND.
      + flatten_hyp Heq; inv Heq.
        rewrite outputs_cons.
        apply in_or_app; left; auto.
      + flatten_hyp Heq; inv Heq. 
        rewrite outputs_cons.
        apply in_or_app; right.
        auto.
  Qed.

  Lemma find_block_in_inputs :
    forall {T} to (bks : ocfg T),
      In to (inputs bks) ->
      exists bk, find_block bks to = Some bk.
  Proof.
    induction bks as [| id ocfg IH]; cbn; intros IN; [inv IN |].
    flatten_goal; flatten_hyp Heq; intuition; eauto.
  Qed.

  Lemma no_reentrance_not_in (bks1 bks2 : ocfg T) :
    no_reentrance bks1 bks2 ->
    forall x, In x (outputs bks2) -> ~ In x (inputs bks1).
  Proof.
    intros; eauto using Coqlib.list_disjoint_notin.
  Qed.

  Lemma no_duplicate_bid_not_in_l (bks1 bks2 : ocfg T) :
    no_duplicate_bid bks1 bks2 ->
    forall x, In x (inputs bks2) -> ~ In x (inputs bks1).
  Proof.
    intros; eauto using Coqlib.list_disjoint_notin, Coqlib.list_disjoint_sym.
  Qed.

  Lemma no_duplicate_bid_not_in_r (bks1 bks2 : ocfg T) :
    no_duplicate_bid bks1 bks2 ->
    forall x, In x (inputs bks1) -> ~ In x (inputs bks2).
  Proof.
    intros; eauto using Coqlib.list_disjoint_notin, Coqlib.list_disjoint_sym.
  Qed.

  Definition independent_flows (bks1 bks2 : ocfg T) : Prop :=
    no_reentrance bks1 bks2 /\ 
    no_reentrance bks2 bks1 /\
    no_duplicate_bid bks1 bks2.

  Lemma independent_flows_no_reentrance_l (bks1 bks2 : ocfg T):
    independent_flows bks1 bks2 ->
    no_reentrance bks1 bks2.
  Proof.
    intros INDEP; apply INDEP; auto.
  Qed.

  Lemma independent_flows_no_reentrance_r (bks1 bks2 : ocfg T):
    independent_flows bks1 bks2 ->
    no_reentrance bks2 bks1.
  Proof.
    intros INDEP; apply INDEP; auto.
  Qed.

  Lemma independent_flows_no_duplicate_bid (bks1 bks2 : ocfg T):
    independent_flows bks1 bks2 ->
    no_duplicate_bid bks1 bks2.
  Proof.
    intros INDEP; apply INDEP; auto.
  Qed.

  Lemma find_block_not_in_inputs:
    forall bid (l : ocfg T),
      ~ In bid (inputs l) ->
      find_block l bid = None.
  Proof.
    induction l as [| bk l IH]; intros NIN; auto.
    cbn.
    flatten_goal.
    - exfalso.
      flatten_hyp Heq; [| inv Heq].
      apply NIN.
      left; rewrite e; reflexivity.
    - flatten_hyp Heq; [inv Heq |].
      apply IH.
      intros abs; apply NIN.
      right; auto.
  Qed.


End LABELS_THEORY.

Section FIND_BLOCK.

  Context {T : Set}.

  Lemma find_block_app_r_wf :
    forall  (x : block_id) (b : block T) (bs1 bs2 : ocfg T),
      wf_ocfg_bid (bs1 ++ bs2)  ->
      find_block bs2 x = Some b ->
      find_block (bs1 ++ bs2) x = Some b.
  Proof.
    intros x b; induction bs1 as [| hd bs1 IH]; intros * NOREP FIND.
    - rewrite app_nil_l; auto.
    - cbn; break_inner_match_goal.
      + cbn in *.
        apply wf_ocfg_bid_cons_not_in in NOREP.
        exfalso; apply NOREP.
        rewrite e.
        apply find_some in FIND as [FIND EQ].
        clear - FIND EQ.
        rewrite map_app; eapply in_or_app; right.
        break_match; [| intuition].
        rewrite <- e.
        eapply in_map; auto.
      + cbn in NOREP; apply wf_ocfg_bid_cons in NOREP.
        apply IH; eauto.
  Qed.

  Lemma find_block_app_l_wf :
    forall (x : block_id) (b : block T) (bs1 bs2 : ocfg T),
      wf_ocfg_bid (bs1 ++ bs2)  ->
      find_block bs1 x = Some b ->
      find_block (bs1 ++ bs2) x = Some b.
  Proof.
    intros x b; induction bs1 as [| hd bs1 IH]; intros * NOREP FIND.
    - inv FIND.
    - cbn in FIND |- *.
      break_inner_match; auto.
      apply IH; eauto.
      eapply wf_ocfg_bid_cons, NOREP.
  Qed.

  Lemma find_block_tail_wf :
    forall (x : block_id) (b b' : block T) (bs : ocfg T),
      wf_ocfg_bid (b :: bs)  ->
      find_block bs x = Some b' ->
      find_block (b :: bs) x = Some b'.
  Proof.
    intros.
    rewrite list_cons_app.
    apply find_block_app_r_wf; auto.
  Qed.

  Definition free_in_cfg (cfg : ocfg T ) (id : block_id) : Prop :=
    not (In id (inputs cfg)).

  Lemma free_in_cfg_cons:
    forall b (bs : ocfg T) id,
      free_in_cfg (b::bs) id ->
      free_in_cfg bs id .
  Proof.
    intros * FR abs; apply FR; cbn.
    destruct (Eqv.eqv_dec_p (blk_id b) id); [rewrite e; auto | right; auto].
  Qed.

  Lemma find_block_free_id :
    forall (cfg : ocfg T) id,
      free_in_cfg cfg id ->
      find_block cfg id = None.
  Proof.
    induction cfg as [| b bs IH]; cbn; intros * FREE; auto.
    break_inner_match_goal.
    + exfalso; eapply FREE.
      cbn; rewrite e; auto.
    + apply IH.
      apply free_in_cfg_cons in FREE; auto.
  Qed.

  Lemma find_block_nil:
    forall {T} b,
      @find_block T [] b = None.
  Proof.
    reflexivity.
  Qed.

  Lemma find_block_eq:
    forall {T} x (b : block T) (bs : ocfg T),
      blk_id b = x ->
      find_block (b:: bs) x = Some b.
  Proof.
    intros; cbn.
    rewrite H.
    destruct (Eqv.eqv_dec_p x x).
    reflexivity.
    contradiction n; reflexivity.
  Qed.

  Lemma find_block_ineq: 
    forall {T} x (b : block T) (bs : ocfg T),
      blk_id b <> x ->
      find_block (b::bs) x = find_block bs x. 
  Proof.
    intros; cbn.
    destruct (Eqv.eqv_dec_p (blk_id b)) as [EQ | INEQ].
    unfold Eqv.eqv, AstLib.eqv_raw_id in *; intuition.
    reflexivity.
  Qed.

  Lemma find_none_app:
    forall {A} (l1 l2 : list A) pred,
      find pred l1 = None ->
      find pred (l1 ++ l2) = find pred l2.
  Proof.
    induction l1; intros l2 pred FIND.
    - reflexivity.
    - cbn in FIND; cbn.
      destruct (pred a); inversion FIND.
      auto.
  Qed.

  Lemma find_some_app:
    forall {A} (l1 l2 : list A) a pred,
      find pred l1 = Some a ->
      find pred (l1 ++ l2) = Some a.
  Proof.
    induction l1 as [|x l1']; intros l2 a pred FIND.
    - inversion FIND.
    - cbn in FIND. destruct (pred x) eqn:PRED.
      + inversion FIND; cbn; subst.
        rewrite PRED. reflexivity.
      + cbn. rewrite PRED.
        auto.
  Qed.

  Lemma find_block_none_app:
    forall {T} (bks1 bks2 : ocfg T) bid,
      find_block bks1 bid = None ->
      find_block (bks1 ++ bks2) bid = find_block bks2 bid.
  Proof.
    intros; apply find_none_app; auto.
  Qed.

  Lemma find_block_some_app:
    forall {T} (bks1 bks2 : ocfg T) (bk : block T) bid,
      find_block bks1 bid = Some bk ->
      find_block (bks1 ++ bks2) bid = Some bk.
  Proof.
    intros; apply find_some_app; auto.
  Qed.

End FIND_BLOCK.


(* TODO:  *)

  (* Lemma def_sites_modified_instr : forall defs id (i : instr _) g l m, *)
  (*   interp_cfg_to_L3 defs (denote_instr (id,i)) g l m ⤳ (fun '(_,(l',_)) => forall k, l' @ k <> l @ k -> In k (def_sites_instr_id id)). *)
  (* Proof. *)
  (*   intros. *)
  (*   destruct i; cbn. *)
  (*   - rewrite denote_instr_comment; apply eutt_Ret; intros; intuition. *)
  (*   - destruct id. *)
  (*     + admit. *)
  (*     + Transparent denote_instr. *)
  (*       cbn. *)
        
  (*     has_failure *)
  (*       unfold has_post. *)
  (*     rewrite denote_instr_op. apply eutt_Ret; intros; intuition. *)

  (*     Lemma def_sites_modified_code : forall defs (c : code _) g l m, *)
  (*         interp_cfg_to_L3 defs (denote_code c) g l m ⤳ (fun '(_,(l',_)) => forall k, l' @ k <> l @ k -> In k (def_sites_code c)). *)
  (*     Proof. *)
  (*       induction c as [| i c IH]; intros. *)
  (*       - cbn. *)
  (*         rewrite denote_code_nil, interp_cfg_to_L3_ret. *)
  (*         apply eutt_Ret. *)
  (*         intros; auto. *)
  (*       - cbn. *)
  (*         rewrite denote_code_cons, interp_cfg_to_L3_bind. *)
  (*         eapply has_post_bind_strong. *)
          
  (*         apply eutt_Ret. *)
  (*         intros ? abs; auto. *)

(* TODO move to wherever lemmas about convert_typ get hosted  *)

(* Lemma blk_id_map_convert_typ : forall env bs, *)
(*     map blk_id (convert_typ env bs) = map blk_id bs. *)
(* Proof. *)
(*   induction bs as [| b bs IH]; cbn; auto. *)
(*   f_equal; auto. *)
(* Qed. *)

(* Lemma wf_ocfg_bid_convert_typ : *)
(*   forall env (bs : ocfg typ), *)
(*     wf_ocfg_bid bs -> *)
(*     wf_ocfg_bid (convert_typ env bs). *)
(* Proof. *)
(*   induction bs as [| b bs IH]; intros NOREP. *)
(*   - cbn; auto. *)
(*   - cbn. *)
(*     apply list_norepet_cons.  *)
(*     + cbn. *)
(*       apply wf_ocfg_bid_cons_not_in in NOREP. *)
(*       rewrite blk_id_map_convert_typ; auto. *)
(*     + eapply IH, wf_ocfg_bid_cons; eauto.  *)
(* Qed. *)

