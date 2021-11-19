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
    ins : (list block_id * nat) ;
    outs : (list block_id * nat) }.

Definition mk_dcfg g (ins outs : list block_id)
  : dcfg :=
  {| graph := g;
    ins := (ins, List.length ins) ;
    outs := (outs, List.length outs) |}.

Section FreshnessMonad.

  Definition mk_anon (n : nat) := Anon (Z.of_nat n).
  Definition name := mk_anon.

  Definition wf_inputs (g : dcfg) : Prop :=
    snd (ins g) = List.length (fst (ins g))
    /\ List.incl (fst (ins g)) (inputs (graph g)).

  Definition wf_outputs (g : dcfg) : Prop :=
    snd (outs g) = List.length (fst (outs g))
    /\ List.incl (fst (outs g)) (outputs (graph g)).

  Definition wf_dcfg (g : dcfg) : Prop :=
    wf_inputs g
    /\ wf_outputs g.
  
  Definition empty_dcfg : dcfg := (mk_dcfg [] [] []).

  Lemma empty_wf : wf_dcfg empty_dcfg.
  Proof.
    unfold empty_dcfg, wf_dcfg, wf_inputs, wf_outputs.
    intuition.
  Qed.

  (* Could be a fresh/state monad *)
  Record FST :=
    mk_FST
      {
        counter_bid : nat ;
        counter_reg : int ;
        g : dcfg
      }.

  Definition fresh_init : FST :=
    mk_FST 0 0%Z empty_dcfg.

  Definition fresh : Type -> Type := fun X => FST -> (FST * X).
  #[global] Instance freshM : Monad fresh :=
    {|
      ret := fun _ x s => (s,x);
      bind := fun _ _ c k s => let '(s',x) := c s in k x s'
    |}.

  Definition freshLabel : fresh block_id :=
    fun '(mk_FST bid reg g) => (mk_FST (S bid) reg g , name bid).

  Definition freshReg : fresh int :=
    fun '(mk_FST bid reg g) => (mk_FST bid (reg+1)%Z g, reg).

  Definition setGraph g' : fresh unit :=
    fun '(mk_FST bid reg g) => (mk_FST bid reg g', tt).

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
    let '(make_dcfg g1 (ins1, _) (outs1, _)) := g1 in
    let '(make_dcfg g2 (ins2, _) (outs2, _)) := g2 in
    let g := cfg_seq g1 g2 out1 in2 in
    let ins := ins1++(remove in2 ins2) in
    let outs := (remove out1 outs1)++outs2 in
    let dg := mk_dcfg g ins outs in
    ret dg.

  Definition mk_join (g0: dcfg) (out1 out2 : block_id) : fresh dcfg :=
    output <- freshLabel ;;
    let '(make_dcfg g0 (ins0, _) (outs0, _)) := g0 in
    let g := cfg_join g0 output out1 out2 in
    let outs := (remove out1 outs0) in
    let outs := (remove out2 outs) in
    let outs := output::outs in
    let dg := mk_dcfg g ins0 outs in
    ret dg.

  Definition mk_branch (cond : texp) (gT gF : dcfg)
             (inT inF : block_id) : fresh dcfg :=
    input <- freshLabel ;;
    let '(make_dcfg gT (insT, _) (outsT, _)) := gT in
    let '(make_dcfg gF (insF, _) (outsF, _)) := gF in
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
    let '(make_dcfg gBody (insBody, _) (outsBody, _)) := gBody in
    let g := cfg_while_loop expr_code cond gBody input inB output outB in
    let ins := [input] ++ (remove inB insBody) in
    let outs := [output] ++ (remove outB outsBody) in
    let dg := mk_dcfg g ins outs in
    ret dg.

End InterfaceCombinators.

From Vellvm Require Import Utils.Tactics.

Lemma wf_mk_block : forall σ c, wf_dcfg (snd ((mk_block c) σ )).
Proof.
  intros.
  unfold wf_dcfg, wf_inputs, wf_outputs, mk_block.
  destruct σ ; cbn.
  unfold incl.
  intuition
  ; try reflexivity
  ; try (cbn in * ; assumption).
Qed.

Lemma wf_mk_seq : forall σ g1 g2 out1 in2,
    wf_dcfg g1 -> (* recursive use of the interface *)
    wf_dcfg g2 ->
    wf_dcfg (snd ((mk_seq g1 g2 out1 in2) σ )).
Proof.
  intros *  WF_G1 WF_G2.
  unfold wf_dcfg, wf_inputs, wf_outputs, mk_seq.
  destruct σ ; cbn.
  unfold wf_dcfg, wf_inputs, wf_outputs in WF_G1, WF_G2.
  destruct WF_G1 as [[LEN_INS_G1 INPUTS_G1] [LEN_OUT_G1 OUTPUTS_G1]].
  destruct WF_G2 as [[LEN_INS_G2 INPUTS_G2] [LEN_OUT_G2 OUTPUTS_G2]].
  unfold incl in *.
  simpl in *.
  intuition ;
    repeat flatten_all.
  - inv Heq0. reflexivity.
  - unfold cfg_seq.
    simpl in *.
    rewrite Util.list_cons_app ;
    rewrite !CFGC_Utils.inputs_app in *.
    apply in_app_or in H.
    apply in_or_app.
    destruct H as [ H | H ].
    + left. now apply INPUTS_G1.
    + right ; apply in_or_app ; right.
      apply INPUTS_G2.
      rewrite remove_ListRemove in H ;
      apply in_remove in H. intuition.
  - inv Heq0. reflexivity.
  - unfold cfg_seq.
    simpl in *.
    rewrite Util.list_cons_app ;
    rewrite !ScopeTheory.outputs_app in *.
    apply in_app_or in H.
    apply in_or_app.
    destruct H as [ H | H ].
    + left. apply OUTPUTS_G1.
      rewrite remove_ListRemove in H ;
      apply in_remove in H. intuition.
    + right ; apply in_or_app ; right.
      now apply OUTPUTS_G2.
Qed.

Lemma wf_mk_join : forall σ g out1 out2,
    wf_dcfg g ->
    wf_dcfg (snd ((mk_join g out1 out2) σ)).
Proof.
  intros * WF_G.
  unfold wf_dcfg, wf_inputs, wf_outputs, mk_seq.
  destruct σ ; cbn.
  unfold wf_dcfg, wf_inputs, wf_outputs in WF_G.
  destruct WF_G as [[LEN_INS_G INPUTS_G] [LEN_OUT_G OUTPUTS_G]].
  unfold incl in *.
  repeat flatten_all.
  simpl in *.
  intuition.
  - inv Heq0.
    apply INPUTS_G in H.
    unfold cfg_join.
    rewrite Util.list_cons_app ;
    rewrite !CFGC_Utils.inputs_app in *.
    apply in_or_app. now left.
  - rewrite H0.
    unfold cfg_join.
    rewrite Util.list_cons_app ;
    rewrite !ScopeTheory.outputs_app in *.
    apply in_or_app ; right. 
    apply in_or_app ; right. simpl ; intuition.
  - unfold cfg_join.
    rewrite Util.list_cons_app
    ; rewrite !ScopeTheory.outputs_app in *.
    inv Heq1 ; clear H.
    apply in_or_app ; left.
    apply OUTPUTS_G.
    rewrite remove_ListRemove in H0 ;
      apply in_remove in H0 ; destruct H0 as [H0 _].
    rewrite remove_ListRemove in H0 ;
      apply in_remove in H0 ; destruct H0 as [H0 _].
    assumption.
Qed.
    
Lemma wf_mk_branch : forall σ cond gT gF inT inF,
    wf_dcfg gT ->
    wf_dcfg gF ->
    wf_dcfg (snd ((mk_branch cond gT gF inT inF) σ)).
Proof.
  intros *  WF_GT WF_GF.
  unfold wf_dcfg, wf_inputs, wf_outputs, mk_seq.
  destruct σ ; cbn.
  unfold wf_dcfg, wf_inputs, wf_outputs in WF_GT, WF_GF.
  destruct WF_GT as [[LEN_INS_GT INPUTS_GT] [LEN_OUT_GT OUTPUTS_GT]].
  destruct WF_GF as [[LEN_INS_GF INPUTS_GF] [LEN_OUT_GF OUTPUTS_GF]].
  unfold incl in *.
  simpl in *.
  intuition ;
    repeat flatten_all ; simpl in * ; try auto.
  - intuition. right.
    inv Heq0.
    rewrite !ScopeTheory.inputs_app.
    apply in_or_app.
    apply in_app_or in H0.
    destruct H0 ; [left ; apply INPUTS_GT | right ; apply INPUTS_GF] ;
    now rewrite remove_ListRemove in H0
    ; apply in_remove in H0
    ; destruct H0 as [H0 _].
  - inv Heq1. clear H0.
    rewrite Util.list_cons_app
    ; rewrite !ScopeTheory.outputs_app in *.
    apply in_or_app ; right.
    apply in_or_app.
    apply in_app_or in H.
    destruct H ; [left ; apply OUTPUTS_GT | right ; apply OUTPUTS_GF] ; assumption.
Qed.

Lemma wf_mk_while : forall σ expr_code cond gB inB outB,
    wf_dcfg gB ->
    wf_dcfg (snd ((mk_while expr_code cond gB inB outB) σ)).
Proof.
  intros * WF_G.
  unfold wf_dcfg, wf_inputs, wf_outputs, mk_seq.
  destruct σ ; cbn.
  unfold wf_dcfg, wf_inputs, wf_outputs in WF_G.
  destruct WF_G as [[LEN_INS_G INPUTS_G] [LEN_OUT_G OUTPUTS_G]].
  unfold incl in *.
  repeat flatten_all.
  simpl in *.
  intuition.
  - inv Heq0.
    right.
    rewrite !ScopeTheory.inputs_app.
    apply in_or_app ; left.
    apply INPUTS_G.
    now rewrite remove_ListRemove in H0
    ; apply in_remove in H0.
  - rewrite H0.
    clear.
    rewrite Util.list_cons_app
    ; rewrite !ScopeTheory.outputs_app in *.
    apply in_or_app ; left ; cbn ; intuition.
  - inv Heq1.
    rewrite Util.list_cons_app
    ; rewrite !ScopeTheory.outputs_app in *.
    apply in_or_app ; right.
    apply in_or_app ; left.
    apply OUTPUTS_G.
    now rewrite remove_ListRemove in H0
    ; apply in_remove in H0.
Qed.


From Coq Require Import Lia.
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
