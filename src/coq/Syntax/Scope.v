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

