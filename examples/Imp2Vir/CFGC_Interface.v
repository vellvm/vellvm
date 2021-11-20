From Coq Require Import
     Lists.List
     Strings.String
     FSets.FMapList
     Structures.OrderedTypeEx
     ZArith.
Module Import StringMap := Coq.FSets.FMapList.Make(String_as_OT).

From ExtLib Require Import
     Structures.Monads
     Data.Monads.OptionMonad.
Import MonadNotation.

From Vellvm Require Import
     Syntax
     SurfaceSyntax .

From Imp2Vir Require Import Imp CFGC_Combinators CFGC_Utils.


Import ListNotations.
Import VIR_Notations.
Notation ocfg := (ocfg typ).

Record dcfg : Type :=
  make_dcfg { graph : ocfg ;
    ins : list block_id ;
    outs : list block_id }.

Definition mk_dcfg g (ins outs : list block_id)
  : dcfg :=
  {| graph := g;
    ins := ins ;
    outs := outs |}.

Section FreshnessMonad.

  Definition mk_anon (n : nat) := Anon (Z.of_nat n).
  Definition name := mk_anon.

  Definition wf_inputs (g : dcfg) : Prop :=
    List.incl (ins g) (inputs (graph g)).

  Definition wf_outputs (g : dcfg) : Prop :=
    List.incl (outs g) (outputs (graph g))
    /\ Coqlib.list_disjoint (outs g) (inputs (graph g)) .

  Definition wf_graph (g : dcfg) : Prop :=
    wf_ocfg_bid (graph g).

  Definition wf_dcfg (g : dcfg) : Prop :=
    wf_inputs g
    /\ wf_outputs g
    /\ wf_graph g .
  
  Definition empty_dcfg : dcfg := (mk_dcfg [] [] []).

  Lemma empty_wf : wf_dcfg empty_dcfg.
  Proof.
    unfold empty_dcfg, wf_dcfg, wf_inputs, wf_outputs, wf_graph, wf_ocfg_bid.
    intuition ; simpl.
    apply Util.list_disjoint_nil_r.
    apply Coqlib.list_norepet_nil.
  Qed.

  Record FST :=
    mk_FST
      {
        counter_bid : nat ;
        counter_reg : int ;
      }.

  Definition fresh_init : FST :=
    mk_FST 0 0%Z.

  Definition fresh : Type -> Type := fun X => FST -> (FST * X).
  #[global] Instance freshM : Monad fresh :=
    {|
      ret := fun _ x s => (s,x);
      bind := fun _ _ c k s => let '(s',x) := c s in k x s'
    |}.

  Definition freshLabel : fresh block_id :=
    fun '(mk_FST bid reg) => (mk_FST (S bid) reg, name bid).

  Definition freshReg : fresh int :=
    fun '(mk_FST bid reg) => (mk_FST bid (reg+1)%Z, reg).
End FreshnessMonad.

Section InterfaceCombinators.

  Notation code := (code typ).
  Notation texp := (texp typ).

  Definition mk_block (c : code) : fresh dcfg :=
    input <- freshLabel ;;
    output <- freshLabel ;;
    let g := cfg_block c input output in
    let dg := mk_dcfg g [input] [output] in
    ret dg.

  Definition mk_ret (c : code) (e : texp) : fresh dcfg :=
    input <- freshLabel ;;
    let g := cfg_ret c e input in
    ret (mk_dcfg g [input] []).

  Definition mk_seq (g1 g2 : dcfg) (out1 in2 : block_id) : fresh dcfg :=
    let '(make_dcfg g1 ins1 outs1) := g1 in
    let '(make_dcfg g2 ins2 outs2) := g2 in
    let g := cfg_seq g1 g2 out1 in2 in
    let ins := ins1++(remove in2 ins2) in
    let outs := (remove out1 outs1)++outs2 in
    let dg := mk_dcfg g ins outs in
    ret dg.

  Definition mk_join (g0: dcfg) (out1 out2 : block_id) : fresh dcfg :=
    output <- freshLabel ;;
    let '(make_dcfg g0 ins0 outs0) := g0 in
    let g := cfg_join g0 output out1 out2 in
    let outs := (remove out1 outs0) in
    let outs := (remove out2 outs) in
    let outs := output::outs in
    let dg := mk_dcfg g ins0 outs in
    ret dg.

  Definition mk_branch (cond : texp) (gT gF : dcfg)
             (inT inF : block_id) : fresh dcfg :=
    input <- freshLabel ;;
    let '(make_dcfg gT insT outsT) := gT in
    let '(make_dcfg gF insF outsF) := gF in
    let g := cfg_branch cond gT gF input inT inF in
    let ins := [input]
                 ++ (remove inT insT)
                 ++ (remove inF insF)
    in
    let outs := outsT++outsF in
    let dg := mk_dcfg g ins outs in
    ret dg.

  Definition mk_while (expr_code : code) (cond : texp) (gBody : dcfg)
             (inB outB : block_id) : fresh dcfg :=
    input <- freshLabel ;;
    output <- freshLabel ;;
    let '(make_dcfg gBody insBody outsBody) := gBody in
    let g := cfg_while_loop expr_code cond gBody input inB output outB in
    let ins := [input] ++ (remove inB insBody) in
    let outs := [output] ++ (remove outB outsBody) in
    let dg := mk_dcfg g ins outs in
    ret dg.

End InterfaceCombinators.

From Vellvm Require Import Utils.Tactics.

Lemma neq_name : forall n1 n2, name n1 <> name n2 <-> n1 <> n2.
Proof.
  intros.
  unfold name, mk_anon.
  split ; intro.
  - intros ->. now destruct H.
  - apply inj_neq in H.
    unfold Zne in H.
    intro.
    injection H0.
    intro.
    rewrite H1 in H .
    contradiction.
Qed.

From Coq Require Import Lia.
Lemma wf_mk_block : forall σ c, wf_dcfg (snd ((mk_block c) σ )).
Proof.
  intros.
  unfold wf_dcfg, wf_inputs, wf_outputs, mk_block, wf_graph, wf_ocfg_bid.
  destruct σ ; cbn.
  unfold incl.
  intuition
  ; try reflexivity
  ; try (cbn in * ; assumption)
  ; try apply List_norepet_singleton.
  apply Util.list_disjoint_singletons.
  rewrite neq_name. lia.
Qed.

Ltac break_list_hyp :=
  match goal with
    | h: List.In _ (_ ++ _) |- _ => repeat (apply in_app_or in h)
  end.

Ltac break_list_goal :=
  try (rewrite Util.list_cons_app) ;
  try (
  match goal with
  | |- context[inputs (_ ++ _)] =>
      repeat (rewrite !ScopeTheory.inputs_app)
  | |- context[outputs (_ ++ _)] =>
      repeat (rewrite !ScopeTheory.outputs_app)
  end ) ;
  try (
  match goal with
  | |- context[List.In _ (_ ++ _)] => repeat (apply in_or_app)
  end).

Lemma in_remove : forall l x y, List.In x (remove y l) -> List.In x l.
Proof. intros.
       rewrite remove_ListRemove in H
       ; apply in_remove in H.
       intuition.
Qed.

Ltac in_list :=
  match goal with
  | h: List.In _ _  |- _ => apply in_remove in h
  end.

Lemma wf_mk_seq : forall σ g1 g2 out1 in2,
    wf_dcfg g1 -> (* recursive use of the interface *)
    wf_dcfg g2 ->
    wf_dcfg (snd ((mk_seq g1 g2 out1 in2) σ )).
Proof.
  intros *  WF_G1 WF_G2.
  unfold wf_dcfg, wf_inputs, wf_outputs, mk_seq, wf_graph, wf_ocfg_bid.
  destruct σ ; cbn.
  unfold wf_dcfg, wf_inputs, wf_outputs, wf_graph, wf_ocfg_bid in WF_G1, WF_G2.
  destruct WF_G1 as [INPUTS_G1 [[OUTPUTS_G1 DISJOINTS_G1] WF_BID_G1]].
  destruct WF_G2 as [INPUTS_G2 [[OUTPUTS_G2 DISJOINTS_G2] WF_BID_G2]].
  unfold incl in *.
  simpl in *.
  intuition ;
    repeat flatten_all.
  - unfold cfg_seq.
    simpl in *.
    break_list_goal.
    break_list_hyp.
    match goal with
    | h: List.In _ _ \/ List.In _ _ |- _ => destruct h
    end.
    + left. now apply INPUTS_G1.
    + right ; right.
      apply INPUTS_G2.
      now in_list.
  - unfold cfg_seq.
    simpl in *.
    break_list_goal.
    break_list_hyp.
    match goal with
    | h: List.In _ _ \/ List.In _ _ |- _ => destruct h
    end.
    + left. apply OUTPUTS_G1.
      now in_list.
    + right ; apply in_or_app ; right.
      now apply OUTPUTS_G2.
  - unfold cfg_seq.
    simpl in *.
    break_list_goal.
    (* NOTE i'm stuck here, because I can't say anything about
       for instance, the disjointness between l2 and (input graph0)
     *)
    admit.
  - unfold cfg_seq.
    simpl in *.
    break_list_goal.
    simpl.
    apply Coqlib.list_norepet_append ; try assumption.
    break_list_goal.
    apply Coqlib.list_norepet_append ; try assumption.
    apply List_norepet_singleton.
    (* NOTE: Coqlib.list_disjoint [out1] (inputs G2) *)
    (* a property I'd really like to have, via independent_flows, but how ? *)
    admit.
    apply Coqlib.list_disjoint_cons_r.
    (* NOTE: Coqlib.list_disjoint (inputs G1) (inputs G2) *)
    admit.
    (* I need 2 things:
       - new hypothesis (out1 ∈ (fst (outs dg)))
          --> the programmer will have to prove that, but easy if he uses the
              interface correctly
       - new wf property on dcfg, st ∀ bk ∈ (fst (outs dg)), bk ∉ (graph dg)
     *)
    admit.
Abort.

Lemma wf_mk_join : forall σ g out1 out2,
    wf_dcfg g ->
    wf_dcfg (snd ((mk_join g out1 out2) σ)).
Proof.
  intros * WF_G.
  unfold wf_dcfg, wf_inputs, wf_outputs, mk_seq, wf_graph, wf_ocfg_bid.
  destruct σ ; cbn.
  unfold wf_dcfg, wf_inputs, wf_outputs, wf_graph, wf_ocfg_bid in WF_G.
  destruct WF_G as [INPUTS_G [[OUTPUTS_G DISJOINTS_G] WF_BID_G]].
  unfold incl in *.
  repeat flatten_all.
  simpl in *.
  intuition.
  - inv Heq.
    apply INPUTS_G in H.
    unfold cfg_join.
    break_list_goal.
    now left.
  - rewrite H0.
    unfold cfg_join.
    break_list_goal.
    simpl ; intuition.
  - unfold cfg_join.
    break_list_goal.
    inv Heq ; clear H.
    left.
    apply OUTPUTS_G.
    repeat in_list.
    assumption.
  - unfold cfg_join.
    break_list_goal.
    simpl in *.
    apply Coqlib.list_disjoint_cons_l.
    (* I need lemmas about remove, but it should be easy here *)
    admit.
    (* freshness of (name counter_bid0)*)
    admit.
  - unfold cfg_join.
    break_list_goal.
    simpl in *.
    apply Coqlib.list_norepet_append ; try assumption.
    (* NOTE out1 ≠ out2 *)
    (* ... should I need new wf property on outputs ? (no_repeat) *)
    (* ... or hypothesis let to the programmer ? *)
    admit.
    (* NOTE Coqlib.list_disjoint (inputs graph0) [out1; out2] *)
    (* I need 2 things:
       - new hypothesis (out1, out2 ∈ (fst (outs dg)))
          --> the programmer will have to prove that, but easy if he uses the
              interface correctly
       - new wf property on dcfg, st ∀ bk ∈ (fst (outs dg)), bk ∉ (graph dg)
     *)
    admit.
Abort.
    
Lemma wf_mk_branch : forall σ cond gT gF inT inF,
    wf_dcfg gT ->
    wf_dcfg gF ->
    wf_dcfg (snd ((mk_branch cond gT gF inT inF) σ)).
Proof.
  intros *  WF_GT WF_GF.

  unfold wf_dcfg, wf_inputs, wf_outputs, mk_seq, wf_graph, wf_ocfg_bid.
  destruct σ ; cbn.
  unfold wf_dcfg, wf_inputs, wf_outputs, wf_graph, wf_ocfg_bid in WF_GT, WF_GF.
  destruct WF_GT as [INPUTS_GT [[OUTPUTS_GT DISJOINTS_GT] WF_BID_GT]].
  destruct WF_GF as [INPUTS_GF [[OUTPUTS_GF DISJOINTS_GF] WF_BID_GF]].
  unfold incl in *.
  simpl in *.
  intuition ;
    repeat flatten_all ; simpl in * ; try auto.
  - intuition. right.
    inv Heq0.
    break_list_goal.
    break_list_hyp.
    match goal with
    | h: List.In _ _ \/ List.In _ _ |- _ => destruct h
    end
    ; [left ; apply INPUTS_GT | right ; apply INPUTS_GF]
    ; now in_list.
  - inv Heq ; clear H0.
    break_list_goal.
    break_list_hyp.
    right.
    break_list_goal.
    match goal with
    | h: List.In _ _ \/ List.In _ _ |- _ => destruct h
    end
    ; [left ; apply OUTPUTS_GT | right ; apply OUTPUTS_GF]
    ; assumption.
  - apply Coqlib.list_disjoint_cons_r.
    (* NOTE Coqlib.list_disjoint (l0 ++ l2) (inputs (graph0 ++ graph1)*)
    admit.
    (* freshness (name counter_bid0)*)
    admit.
  - break_list_goal.
    apply Coqlib.list_norepet_append ; try assumption.
    apply List_norepet_singleton.
    apply Coqlib.list_norepet_append ; try assumption.
    (* NOTE: Coqlib.list_disjoint (inputs GT) (inputs GF) *)
    admit.
    apply Util.list_disjoint_singleton_left.
    (* freshness (name counter_bid0) *)
    admit.
Abort.

Lemma wf_mk_while : forall σ expr_code cond gB inB outB,
    wf_dcfg gB ->
    wf_dcfg (snd ((mk_while expr_code cond gB inB outB) σ)).
Proof.
  intros * WF_G.
  unfold wf_dcfg, wf_inputs, wf_outputs, mk_seq, wf_graph, wf_ocfg_bid.
  destruct σ ; cbn.
  unfold wf_dcfg, wf_inputs, wf_outputs, wf_graph, wf_ocfg_bid in WF_G.
  destruct WF_G as [INPUTS_G [[OUTPUTS_G DISJOINTS_G] WF_BID_G]].
  unfold incl in *.
  repeat flatten_all.
  simpl in *.
  intuition.
  - inv Heq.
    right.
    do 2 break_list_goal ; simpl.
    left.
    apply INPUTS_G.
    now in_list.
  - rewrite H0.
    clear.
    do 2 (break_list_goal ; simpl).
    left ; cbn ; intuition.
  - inv Heq.
    break_list_goal ; simpl.
    right.
    break_list_goal ; simpl.
    left.
    apply OUTPUTS_G.
    now in_list.
  - break_list_goal.
    simpl in *.
    apply Coqlib.list_disjoint_cons_l.
    apply Coqlib.list_disjoint_cons_r.
    (* lemma on remove - easy *)
    admit.
    (* freshness (name counter_bid0) *)
    admit.
    (* freshness (name counter_bid0) *)
    admit.
  - break_list_goal.
    simpl in *.
    break_list_goal.
    apply Coqlib.list_norepet_append ; try assumption.
    apply List_norepet_singleton.
    apply Coqlib.list_norepet_append ; try assumption.
    apply List_norepet_singleton.
    apply Util.list_disjoint_singleton_right.
    (* NOTE: ~ List.In outB (inputs gB)
       - outB ∈ (outs gB)
       - disjonction (inputs gB) (outs gB)
     *)
    admit.
    apply Util.list_disjoint_singleton_left.
    intro.
    break_list_hyp.
    (* NOTE: freshness (name counter_bid0) *)
    admit.
Abort.


Lemma wf_mk_block_bind :
  forall σ0 σ1 σ2 c1 c2 g1 g2,
    (mk_block c1) σ0 = (σ1, g1) ->
    (mk_block c2) σ1 = (σ2, g2) ->
    independent_flows (graph g1) (graph g2).
Proof.
  intros.
  unfold mk_block in *.
  unfold freshLabel in *.
  destruct σ0.
  cbn in *.
  inv H. inv H0.
  simpl.
  unfold independent_flows, no_duplicate_bid, no_reentrance.
  unfold cfg_block.
  cbn.
  unfold Coqlib.list_disjoint.
  intuition ; subst ;
    repeat (
        match goal with
        | h:context[List.In _ [_]] |- _ => apply CFGC_Utils.In_singleton in h
        end
      )
  ; rewrite H0 in H ; clear H0
  ; match goal with
    | h:context[ name ?x = name ?y ] |- _ =>
        assert (contra : name x <> name y)
        by (apply neq_name ; lia )
    end ;
    now apply contra in H.
Qed.

(* NOTE: Now, I want a similar lemma, but with X states between
         the 1st mk_block and the 2nd mk_block *)

(* NOTE: Now, I want a similar lemma, but I can ALSO use other operations,
         such mk_seq (instead of mk_block) *)

(* Lemma wf_mk_seq_wf_seq : forall g1 g2 out1 in2, *)
(*     List.In out1 (fst (outs g1)) -> (* easy to ensure *) *)
(*     List.In in2 (fst (ins g2)) -> *)
(*     wf_dcfg g1 -> (* recursive use of the interface *) *)
(*     wf_dcfg g2 -> *)
(*     wf_seq (graph g1) (graph g2) out1 in2. *)
(* Proof. *)
(*   intros * CORRECT_OUT1 CORRECT_IN2 WF_G1 WF_G2. *)
(*   unfold wf_dcfg, wf_inputs, wf_outputs in WF_G1, WF_G2. *)
(*   destruct WF_G1 as [[LEN_INS_G1 INPUTS_G1] [LEN_OUT_G1 OUTPUTS_G1]]. *)
(*   destruct WF_G2 as [[LEN_INS_G2 INPUTS_G2] [LEN_OUT_G2 OUTPUTS_G2]]. *)
(*   unfold wf_seq. *)

(*
In order to use the interface, the function compile should
work with dcfg instead of ocfg.
It remains some properties to prove, as
`List.In out1 (fst (outs g1))`, but if the user uses the interface
correctly, this is very easy to ensure.
In this example, the user should pick out1 using the information
in the DCFG (the outputs here).
 *)
