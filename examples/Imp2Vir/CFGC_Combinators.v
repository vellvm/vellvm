From Coq Require Import Lists.List.
Import ListNotations.

From Vellvm Require Import Syntax.

From Imp2Vir Require Import CFGC_Utils.

Section CFG_Combinators.

Notation code := (code typ).
Notation ocfg := (ocfg typ).
Notation conv := (convert_typ []).
Notation texp := (texp typ).

Definition texp_break (e : texp) : dtyp * exp dtyp :=
  let (t,e) := e in
  ((typ_to_dtyp [] t), (conv e)).


(** Combinators over OCFG *)


(* Define an ocfg containing a unique block, labeled with /input/ and jumping to /output/ *)
Definition cfg_block (c : code) (input output : block_id) : ocfg :=
  [mk_block input [] c (TERM_Br_1 output) None].

(* Define an ocfg containing a unique block, labeled with /input/ and returning the expression /e/ *)
Definition cfg_ret (c : code) (e : texp) (input : block_id) : ocfg :=
  [mk_block input [] c (TERM_Ret e) None].

(* Given 2 ocfg and an expression /e/, conditionnal branch over theses graphs,
 and jumping to output *)
Definition cfg_branch (cond : texp)
           (gT gF : ocfg)
           (input inT inF : block_id) : ocfg :=
  let cond_block := [mk_block input [] [] (TERM_Br cond inT inF) None] in
  cond_block++gT++gF.

(* Given 2 ocfg, make them jump into the same block *)
Definition cfg_join (g : ocfg) (output out1 out2 : block_id) : ocfg :=
 let dead_block1 := [mk_block out1 [] [] (TERM_Br_1 output) None] in
 let dead_block2 := [mk_block out2 [] [] (TERM_Br_1 output) None] in
 g ++ dead_block1 ++ dead_block2.

(* Given 2 ocfg, sequence them g1 ;; g2 *)
Definition cfg_seq (g1 g2 : ocfg) (out1 in2 : block_id) : ocfg :=
  let dead_block := [mk_block out1 [] [] (TERM_Br_1 in2) None] in
  g1 ++ dead_block ++ g2.

(* While *)
Definition cfg_while_loop (code_expr : code) (cond : texp)
           (body : ocfg) (input inB output outB: block_id) : ocfg :=
  let cond_block := [mk_block input [] code_expr (TERM_Br cond inB output) None] in
  let dead_block := [mk_block outB [] [] (TERM_Br_1 input) None] in
  cond_block++body++dead_block.

(* Dedicated combinators for /for_loops/ *)
Definition cfg_for_loop (b e step : nat) (body : ocfg) (inb : block_id) : ocfg.
Admitted.


(** Misc lemmas on combinators *)
Lemma inputs_seq : forall (g1 g2 : ocfg) (out1 in2 :  block_id),
    inputs (cfg_seq g1 g2 out1 in2) =
      inputs g1 ++ [out1] ++ inputs g2.
Proof.
  intros.
  unfold cfg_seq.
  rewrite (inputs_app g1 _).
  rewrite (inputs_app _ g2).
  reflexivity.
Qed.

(** WF properties *)

Lemma wf_bid_cfg_block :
  forall c input output,
    wf_ocfg_bid (cfg_block c input output).
Proof.
  intros.
  unfold wf_ocfg_bid ; simpl.
  apply List_norepet_singleton.
Qed.

Lemma wf_bid_cfg_ret :
  forall c e input,
    wf_ocfg_bid (cfg_ret c e input).
Proof.
  intros.
  unfold wf_ocfg_bid ; simpl.
  apply List_norepet_singleton.
Qed.

Lemma wf_bid_cfg_seq :
  forall g1 g2 out1 in2,
    wf_ocfg_bid g1 ->
    wf_ocfg_bid g2 ->
    no_duplicate_bid g1 g2 ->
    free_in_cfg g1 out1 ->
    free_in_cfg g2 out1 ->
    wf_ocfg_bid (cfg_seq g1 g2 out1 in2).
Proof.
  intros * WF_G1 WF_G2 SEP_G1_G2 FREE_G1_OUT1 FREE_G2_OUT1.
  unfold cfg_seq, wf_ocfg_bid.
  unfold free_in_cfg in *.
  rewrite 2 inputs_app ; simpl.
  rewrite Util.list_cons_app.
  rewrite Coqlib.list_norepet_app ; intuition.
  - rewrite Coqlib.list_norepet_app ; intuition.
    apply List_norepet_singleton.
    unfold Coqlib.list_disjoint.
    intros * Hsing contra ?; subst.
    apply In_singleton in Hsing ; subst.
    now apply FREE_G2_OUT1 in contra.
  - unfold Coqlib.list_disjoint.
    intros * H contra ?; subst.
    apply in_app_or in contra.
    destruct contra as [ Hsing | contra0 ].
    + apply In_singleton in Hsing ; subst ; now apply FREE_G1_OUT1 in H.
    + unfold no_duplicate_bid,Coqlib.list_disjoint in SEP_G1_G2.
      now apply (SEP_G1_G2 y y) in H.
Qed.

Lemma wf_bid_cfg_join :
  forall output out1 out2 g,
    out1 <> out2 ->
    free_in_cfg g out1 ->
    free_in_cfg g out2 ->
    wf_ocfg_bid g ->
    wf_ocfg_bid (cfg_join g output out1 out2).
Proof.
  intros * SEP_OUTS FREE_G_OUT1 FREE_G_OUT2 WF_G.
  unfold cfg_join, wf_ocfg_bid.
  rewrite inputs_app ; simpl.
  apply Coqlib.list_norepet_append ; try assumption.
  apply Coqlib.list_norepet_cons.
  - intro contra ; apply In_singleton in contra ; now subst.
  - apply List_norepet_singleton.
  - repeat (apply Coqlib.list_disjoint_cons_r ; [|assumption]).
    apply Util.list_disjoint_nil_r.
Qed.


Lemma wf_bid_cfg_branch :
  forall cond gT gF input inT inF,
    wf_ocfg_bid gT ->
    wf_ocfg_bid gF ->
    no_duplicate_bid gT gF ->
    free_in_cfg gT input ->
    free_in_cfg gF input ->
    wf_ocfg_bid (cfg_branch cond gT gF input inT inF).
Proof.
  intros * WF_GT WF_GF SEP_GT_GF FREE_GT_INPUT FREE_GF_INPUT.
  unfold cfg_branch, wf_ocfg_bid.
  repeat (rewrite inputs_app ; simpl).
  apply Coqlib.list_norepet_cons.
  - intro contra; apply in_app_or in contra ; intuition.
  - apply Coqlib.list_norepet_append; assumption.
Qed.

Lemma wf_bid_cfg_while_loop:
  forall code_expr cond body input inB output outB,
    input <> outB ->
    free_in_cfg body input ->
    free_in_cfg body outB ->
    wf_ocfg_bid body ->
    wf_ocfg_bid (cfg_while_loop code_expr cond body input inB output outB).
Proof.
  intros * NEQ_INPUT_OUTB FREE_BODY_INPUT FREE_BODY_OUTB WF_BODY.
  unfold cfg_while_loop, wf_ocfg_bid.
  repeat (rewrite inputs_app ; simpl).
  apply Coqlib.list_norepet_cons.
  - intro contra; apply in_app_or in contra ; intuition.
    apply In_singleton in H ; now subst.
  - apply Coqlib.list_norepet_append.
    + assumption.
    + apply List_norepet_singleton.
    + repeat (apply Coqlib.list_disjoint_cons_r ; [|assumption]).
      apply Util.list_disjoint_nil_r.
Qed.



Definition wf_block (c : code) (input output : block_id) : Prop :=
  input <> output.
Definition wf_ret (c : code) (e : texp) (input : block_id) : Prop := True.
Definition wf_seq (g1 g2 : ocfg) (out1 in2 : block_id) : Prop :=
  wf_ocfg_bid g1
  /\ wf_ocfg_bid g2
  /\ no_duplicate_bid g1 g2
  /\ no_reentrance g1 g2
  /\ free_in_cfg g1 out1 (* cfg_seq cannot create a new block with an existing ID *)
  /\ free_in_cfg g2 out1 (* cfg_seq cannot create a new block with an existing ID *)
  /\ free_in_cfg g1 in2 (* in2 should be an input of g2, not g1 *)
  /\ ~ In out1 (outputs g2)
  /\ out1 <> in2.

Definition wf_join (body : ocfg) (output out1 out2 : block_id) : Prop :=
  free_in_cfg body output
  /\ output <> out1
  /\ output <> out2.

Definition wf_branch (cond : texp) (gT gF : ocfg) (input inT inF : block_id) : Prop :=
  input <> inT
  /\ input <> inF
  /\ free_in_cfg gF inT
  /\ free_in_cfg gT inF
  /\ independent_flows gT gF
  /\ ~ In input (outputs gT)
  /\ ~ In input (outputs gF).

Definition wf_while (expr_code : code) (cond : texp) (body : ocfg) (input inB output outB : block_id) : Prop :=
  input <> output
  /\ input <> inB
  /\ input <> outB
  /\ output <> inB
  /\ output <> outB
  /\ free_in_cfg body input
  /\ free_in_cfg body output
  /\ free_in_cfg body outB
  /\ wf_ocfg_bid body
  /\ In inB (inputs body).

End CFG_Combinators.
