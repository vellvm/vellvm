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

Section FreshnessMonad.

  Definition name := mk_anon.
  Lemma neq_name : forall n1 n2, name n1 <> name n2 <-> n1 <> n2.
  Proof.
    intros.
    unfold name. now apply neq_mk_anon.
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

  Record dcfg : Type :=
    make_dcfg { graph : ocfg ;
                ins : list block_id ;
                outs : list block_id }.

  Definition mk_dcfg g (ins outs : list block_id)
    : dcfg :=
    {| graph := g;
      ins := ins ;
      outs := outs |}.

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

Section CFG_LANG.
  Inductive cfg_lang : Type :=
  | CBlock ( c : code typ )
  | CSeq (g1 g2 : cfg_lang )
  | CBranch (cond : texp typ) (gT gF : cfg_lang)
  | CJoin (g0: cfg_lang)
  | CWhile (exp_code : code typ) (cond : texp typ) (gB : cfg_lang) .

  Definition default_bid := Anon 0%Z.

  Fixpoint evaluate (cfg : cfg_lang) : fresh dcfg :=
    match cfg with
    | CBlock c =>
        mk_block c
    | CSeq g1 g2 =>
        ( dg1 <- evaluate g1 ;;
          dg2 <- evaluate g2 ;;
          let out1 := List.hd default_bid (outs dg1) in
          let in2 := List.hd default_bid (ins dg2) in
          mk_seq dg1 dg2 out1 in2)
    | CBranch cond gT gF =>
        dgT <- evaluate gT ;;
        dgF <- evaluate gF ;;
        let inT := List.hd default_bid (ins dgT) in
        let inF := List.hd default_bid (ins dgF) in
        mk_branch cond dgT dgF inT inF
    | CJoin g =>
        dgB <- evaluate g ;;
        let out1 := List.hd default_bid (outs dgB) in
        let out2 := List.hd default_bid (List.tl (outs dgB)) in
        mk_join dgB out1 out2
    | CWhile expr_code cond gB =>
        dgB <- evaluate gB ;;
        let inB := List.hd default_bid (ins dgB) in
        let outB := List.hd default_bid (outs dgB) in
        mk_while expr_code cond dgB inB outB
    end.

End CFG_LANG.


From Vellvm Require Import Utils.Tactics.

From Coq Require Import Lia.
Require Import Coqlib.
Require Import Util.

Definition independent_flows_dcfg g1 g2 :=
  independent_flows (graph g1) (graph g2).

Definition wf_inputs (g : dcfg) : Prop :=
  List.incl (ins g) (inputs (graph g)).

Definition wf_outputs (g : dcfg) : Prop :=
  List.incl (outs g) (outputs (graph g))
  /\ list_disjoint (outs g) (inputs (graph g)) .

Definition wf_graph (g : dcfg) : Prop :=
  wf_ocfg_bid (graph g).

Definition wf_dcfg (g : dcfg) : Prop :=
  wf_inputs g
  /\ wf_outputs g
  /\ wf_graph g .

Lemma wf_dcfg_ocfg : forall dg, wf_dcfg dg -> wf_ocfg_bid (graph dg).
Proof.
  intros.
  unfold wf_dcfg, wf_graph in H ; intuition.
Qed.

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
  apply list_disjoint_singletons.
  rewrite neq_name. lia.
Qed.

Lemma wf_mk_seq : forall σ g1 g2 out1 in2,
    independent_flows_dcfg g1 g2 ->
    (outs g1) ⊍ (outs g2) ->
    List.In out1 (outs g1) ->
    List.In in2 (ins g2) ->
    wf_dcfg g1 -> (* recursive use of the interface *)
    wf_dcfg g2 ->
    wf_dcfg (snd ((mk_seq g1 g2 out1 in2) σ )).
Proof.
  intros *  FLOWS DISJOINTS_OUTPUTS OUT IN WF_G1 WF_G2.
  unfold wf_dcfg, wf_inputs, wf_outputs, mk_seq, wf_graph, wf_ocfg_bid.
  destruct σ ; cbn.
  unfold wf_dcfg, wf_inputs, wf_outputs, wf_graph, wf_ocfg_bid in WF_G1, WF_G2.
  destruct WF_G1 as [INPUTS_G1 [[OUTPUTS_G1 DISJOINTS_G1] WF_BID_G1]].
  destruct WF_G2 as [INPUTS_G2 [[OUTPUTS_G2 DISJOINTS_G2] WF_BID_G2]].
  unfold incl.
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
      now in_list_rem.
  - unfold cfg_seq.
    simpl in *.
    break_list_goal.
    break_list_hyp.
    match goal with
    | h: List.In _ _ \/ List.In _ _ |- _ => destruct h
    end.
    + left. apply OUTPUTS_G1.
      now in_list_rem.
    + right ; apply in_or_app ; right.
      now apply OUTPUTS_G2.
  - unfold cfg_seq.
    simpl in *.
    break_list_goal.
    apply list_disjoint_app_r.
    split
    ; [ apply list_disjoint_app_l
      | apply list_disjoint_app_r
        ; split
        ; apply list_disjoint_app_l
      ] ; try split ; try assumption.
    + now apply remove_disjoint.
    + simpl.
      unfold independent_flows_dcfg in FLOWS
      ; simpl in FLOWS
      ; unfold independent_flows in FLOWS
      ; unfold no_reentrance in FLOWS.
      destruct FLOWS as [FLOWS  [_ _]].
      eapply incl_disjoint ; try eassumption.
    + apply remove_disjoint_remove ; simpl.
      rewrite eq_bid_refl.
      apply list_disjoint_nil_r.
    + simpl.
      unfold independent_flows_dcfg in FLOWS
      ; simpl in FLOWS
      ; unfold independent_flows in FLOWS
      ; unfold no_reentrance in FLOWS.
      apply list_disjoint_cons_r ; [apply list_disjoint_nil_r|].
      eapply list_disjoint_notin ; eassumption.
    + simpl.
      unfold independent_flows_dcfg in FLOWS
      ; simpl in FLOWS
      ; unfold independent_flows in FLOWS
      ; unfold no_reentrance in FLOWS.
      apply remove_disjoint.
      destruct FLOWS as [_ [FLOWS _]].
      eapply incl_disjoint ; try eassumption.
  - unfold cfg_seq.
    simpl in *.
    break_list_goal.
    simpl.
    apply Coqlib.list_norepet_append
    ; try assumption
    ; unfold independent_flows_dcfg in FLOWS
    ; simpl in FLOWS
    ; unfold independent_flows in FLOWS
    ; unfold no_reentrance in FLOWS.
    + break_list_goal.
      apply Coqlib.list_norepet_append ; try assumption.
      apply List_norepet_singleton.
      destruct FLOWS as [_ [FLOWS _]].
      apply Util.list_disjoint_singleton_left.
      clear IN INPUTS_G1 WF_BID_G1 INPUTS_G2 OUTPUTS_G2 WF_BID_G2.
      eapply Coqlib.list_disjoint_notin.
      2:{ eassumption. }
      eapply incl_disjoint ; eassumption.
    + destruct FLOWS as [_ [_ FLOWS]] ; unfold no_duplicate_bid in FLOWS.
      apply Coqlib.list_disjoint_cons_r ; try assumption.
      apply Util.list_disjoint_singleton_left.
      clear -DISJOINTS_G1 OUT.
      apply Util.list_disjoint_singleton_left.
      eapply Coqlib.list_disjoint_notin ; eassumption.
Admitted.

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
    inv Heq.
    left.
    apply OUTPUTS_G.
    repeat in_list_rem.
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
Admitted.

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
    ; now in_list_rem.
  - inv Heq.
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
Admitted.

Lemma wf_mk_while : forall σ expr_code cond gB inB outB,
    List.In outB (outs gB) ->
    wf_dcfg gB ->
    wf_dcfg (snd ((mk_while expr_code cond gB inB outB) σ)).
Proof.
  intros * OUTPUT WF_G.
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
    now in_list_rem.
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
    now in_list_rem.
  - break_list_goal.
    simpl in *.
    apply list_disjoint_cons_l.
    + apply list_disjoint_cons_r.
      * apply remove_disjoint_remove ; cbn.
        rewrite CFGC_Utils.remove_app.
        apply list_disjoint_app_r.
        split ;
          [apply remove_disjoint_remove
           ; apply remove_disjoint ; assumption
          | simpl ; rewrite eq_bid_refl
            ; apply list_disjoint_nil_r].
      * (* freshness (name counter_bid0) *)
        admit.
    + (* freshness (name counter_bid0) *)
      admit.
  (* NOTE: for freshness, I need hypothesis about intervals of
         block_id in graphs *)
  - break_list_goal.
    simpl in *.
    break_list_goal.
    apply list_norepet_append ; try assumption.
    apply List_norepet_singleton.
    apply list_norepet_append ; try assumption.
    apply List_norepet_singleton.
    apply list_disjoint_singleton_right.
    eapply list_disjoint_notin ; eassumption.
    apply list_disjoint_singleton_left.
    (* NOTE: freshness (name counter_bid0) *)
    admit.
Admitted.



Require Import Datatypes.

Theorem inv_len_inputs : forall (σ: FST) (c : cfg_lang) (dg : dcfg),
    snd ((evaluate c) σ) = dg ->
    (length (ins dg) >= 1)%nat.
Proof.
  intros *. revert σ dg.
  induction c ; intros ; simpl in *.
  - rewrite <- H.
    unfold mk_block.
    simpl.
    repeat flatten_all ; cbn.
    lia.
  - repeat flatten_all ; cbn.
    rewrite <- H.
    unfold mk_seq.
    simpl.
    repeat flatten_all ; cbn.
    rewrite app_length.
    inv Heq.
    assert ((length ins0 >= 1)%nat) by
      (match goal with
       | h: evaluate c1 σ = (_,?dg) |- _ =>
           assert (snd (evaluate c1 σ) = dg) by now rewrite h
       end ;
       apply IHc1 in H;
       now simpl in H).
    lia.
  - repeat flatten_all ; cbn.
    rewrite <- H.
    unfold mk_branch ; simpl.
    repeat flatten_all ; cbn.
    lia.
  - repeat flatten_all ; cbn.
    rewrite <- H.
    unfold mk_join ; simpl.
    repeat flatten_all ; cbn.
    match goal with
    | h: evaluate c σ = (_,?dg) |- _ =>
        assert (snd (evaluate c σ) = dg) by now rewrite h
    end.
    apply IHc in H0 ; simpl in H0.
    assumption.
  - repeat flatten_all ; cbn.
    rewrite <- H.
    unfold mk_while ; simpl.
    repeat flatten_all ; cbn.
    lia.
Qed.

Theorem inv_len_outputs : forall (σ: FST) (c : cfg_lang) (dg : dcfg),
    snd ((evaluate c) σ) = dg ->
    (length (outs dg) >= 1)%nat.
Proof.
  intros *. revert σ dg.
  induction c ; intros ; simpl in *.
  - rewrite <- H.
    unfold mk_block.
    simpl.
    repeat flatten_all ; cbn.
    lia.
  - repeat flatten_all ; cbn.
    rewrite <- H.
    unfold mk_seq.
    simpl.
    repeat flatten_all ; cbn.
    rewrite app_length.
    inv Heq0.
    assert ((length outs1 >= 1)%nat) by
      (match goal with
       | h: evaluate c2 ?f = (_,?dg) |- _ =>
           assert (snd (evaluate c2 f) = dg) by now rewrite h
       end ;
       apply IHc2 in H ;
       now simpl in H).
    lia.
  - repeat flatten_all ; cbn.
    rewrite <- H.
    unfold mk_branch ; simpl.
    repeat flatten_all ; cbn.
    rewrite app_length.
    inv Heq0.
    assert ((length outs1 >= 1)%nat) by
      (match goal with
       | h: evaluate c2 ?f = (_,?dg) |- _ =>
           assert (snd (evaluate c2 f) = dg) by now rewrite h
       end ;
       apply IHc2 in H ;
       now simpl in H).
    lia.
  - repeat flatten_all ; cbn.
    rewrite <- H.
    unfold mk_join ; simpl.
    repeat flatten_all ; cbn.
    lia.
  - repeat flatten_all ; cbn.
    rewrite <- H.
    unfold mk_while ; simpl.
    repeat flatten_all ; cbn.
    lia.
Qed.


Theorem inv_independent_flows :
  forall (σ1 σ2 σ3: FST) (c1 c2 : cfg_lang) (dg1 dg2 : dcfg),
    (evaluate c1) σ1 = (σ2, dg1) ->
    (evaluate c2) σ2 = (σ3, dg2) ->
    independent_flows_dcfg dg1 dg2.
Proof.
  intros.
  unfold independent_flows_dcfg, independent_flows.
Admitted.

Theorem inv_disjoint_outputs :
  forall (σ1 σ2 σ3: FST) (c1 c2 : cfg_lang) (dg1 dg2 : dcfg),
    (evaluate c1) σ1 = (σ2, dg1) ->
    (evaluate c2) σ2 = (σ3, dg2) ->
    (outs dg1) ⊍ (outs dg2).
Proof.
  intros.
Admitted.

Theorem wf_evaluate : forall (σ: FST) (c : cfg_lang) (dg : dcfg),
    snd ((evaluate c) σ) = dg ->
    wf_dcfg dg.
Proof.
  intros *. revert σ dg.
  induction c ; intros ; simpl in *.
  - rewrite <- H.
    apply wf_mk_block.
  - repeat flatten_all.
    rewrite <- H.
    apply wf_mk_seq.
    + eapply inv_independent_flows ; eassumption.
    (* PROVE INVARIANT INDEPENDENT FLOWS  *)
    + eapply inv_disjoint_outputs ; eassumption.
    (* PROVE INVARIANT DISJOINT FLOWS *)
    + apply hd_In.
      apply (inv_len_outputs σ c1 d). now rewrite Heq.
    + apply hd_In.
      apply (inv_len_inputs f c2 d0). now rewrite Heq0.
    + eapply IHc1. now erewrite Heq.
    + eapply IHc2. now erewrite Heq0.
  - repeat flatten_all.
    rewrite <- H.
    apply wf_mk_branch.
    + eapply IHc1. now erewrite Heq.
    + eapply IHc2. now erewrite Heq0.
  - repeat flatten_all.
    rewrite <- H.
    apply wf_mk_join.
    eapply IHc. now erewrite Heq.
  - repeat flatten_all.
    rewrite <- H.
    apply wf_mk_while.
    + apply hd_In.
      apply (inv_len_outputs σ c d). now rewrite Heq.
    + eapply IHc. now erewrite Heq.
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
        | h:context[List.In _ [_]] |- _ => apply In_singleton in h
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

Definition denote_dcfg (dg : dcfg) := denote_cfg (graph dg).
Definition denote_cfg_lang (g : cfg_lang) (σ : FST) := denote_dcfg (snd ((evaluate g) σ)).
