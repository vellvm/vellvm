From Coq Require Import
     Lists.List
     Strings.String
     FSets.FMapList
     Structures.OrderedTypeEx
     ZArith
     Lia.
Module Import StringMap := Coq.FSets.FMapList.Make(String_as_OT).

From ExtLib Require Import
     Structures.Monads
     Data.Monads.OptionMonad.
Import MonadNotation.

From Vellvm Require Import
     Syntax
     SurfaceSyntax
     Utils.Tactics.

From Imp2Vir Require Import Imp CFGC_Combinators CFGC_Utils.

Require Import Coqlib.
Require Import Util.

Import ListNotations.
Import VIR_Notations.
Notation ocfg := (ocfg typ).

Section FreshnessMonad.
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

  Lemma freshLabel_ord : forall f1 f2 f3 b1 b2,
      freshLabel f1 = (f2, b1) ->
      freshLabel f2 = (f3, b2) ->
      lt_bid b1 b2.
  Proof.
    intros.
    unfold freshLabel in *.
    repeat flatten_all ; simpl in *.
    inv H. inv H0.
    admit. (* obviously true *)
  Admitted.

  Lemma freshLabel_fresh : forall f1 f2 f3 b1 b2,
      freshLabel f1 = (f2, b1) ->
      freshLabel f2 = (f3, b2) ->
      b1 <> b2.
  Proof.
    intros.
    unfold freshLabel in *.
    repeat flatten_all ; simpl in *.
    inv H. inv H0.
    apply neq_name.
    lia.
  Qed.

End FreshnessMonad.

Import CFGC_Utils.
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
  | CWhile (exp_code : code typ) (cond : texp typ) (gB : cfg_lang).

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


Definition independent_flows_dcfg g1 g2 :=
  independent_flows (graph g1) (graph g2).

Definition wf_inputs (g : dcfg) : Prop :=
  List.incl (ins g) (inputs (graph g)).

Definition wf_outputs (g : dcfg) : Prop :=
  List.incl (outs g) (outputs (graph g))
  /\ list_disjoint (outs g) (inputs (graph g))
  /\ list_norepet (outs g).

Definition wf_name (g : dcfg) : Prop :=
  Forall (fun b => is_anon b ) (inputs (graph g))
  /\ Forall (fun b => is_anon b ) (outputs (graph g)).

Definition wf_graph (g : dcfg) : Prop :=
  wf_ocfg_bid (graph g).

Definition wf_dcfg (g : dcfg) : Prop :=
  wf_inputs g
  /\ wf_outputs g
  /\ wf_graph g
  /\ wf_name g.

Lemma wf_dcfg_ocfg : forall dg, wf_dcfg dg -> wf_ocfg_bid (graph dg).
Proof.
  intros.
  unfold wf_dcfg, wf_graph in H ; intuition.
Qed.

Lemma snd_intro : forall {A B : Type} (p : A * B) x y, p = (x, y) -> snd p = y.
Proof.
  intros. now inv H.
Qed.

Ltac intro_snd_evaluate :=
  match goal with
  | h: evaluate ?c ?σ = (_,?dg) |- _ =>
      apply snd_intro in h
  end.


(** Invariants through the function evaluate *)

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



Theorem inv_wf_inputs_outputs : forall (σ: FST) (c : cfg_lang) (dg : dcfg),
    snd ((evaluate c) σ) = dg ->
    wf_inputs dg /\ List.incl (outs dg) (outputs (graph dg)).
Proof.
  intros *. revert σ dg.
  unfold wf_inputs.
  induction c ; intros ; simpl in *.
  - unfold mk_block in H.
    unfold freshLabel in H.
    simpl in H.
    repeat flatten_all.
    simpl in *.
    rewrite <- H.
    unfold cfg_block ; cbn.
    split ; apply incl_refl.
  - unfold mk_seq in *.
    simpl in *.
    repeat flatten_all.
    simpl in *.
    unfold cfg_seq in *.
    inv H.
    simpl in *.
    do 2 intro_snd_evaluate.
    apply IHc1 in Heq.
    apply IHc2 in Heq0.
    simpl in *.
    destruct Heq, Heq0.
    unfold incl in *.
    split ; intros
    ; break_list_goal ; break_list_hyp
    ; simpl in *.
    destruct H3.
    apply H in H3 ; intuition.
    in_list_rem; apply H1 in H3 ; intuition.
    destruct H3.
    in_list_rem; apply H0 in H3; intuition.
    apply H2 in H3; intuition.
  - unfold mk_branch in *.
    simpl in *.
    repeat flatten_all.
    simpl in *.
    unfold cfg_branch in *.
    inv H.
    simpl in *.
    do 2 intro_snd_evaluate.
    apply IHc1 in Heq.
    apply IHc2 in Heq0.
    simpl in *.
    destruct Heq, Heq0.
    unfold incl in *.
    split ; intros
    ; break_list_goal
    ; simpl in *.
    destruct H3. intuition.
    break_list_hyp.
    destruct H3.
    in_list_rem; apply H in H3 ; intuition.
    in_list_rem; apply H1 in H3 ; intuition.
    break_list_hyp.
    destruct H3.
    apply H0 in H3; intuition.
    apply H2 in H3; intuition.
  - unfold mk_join in *.
    simpl in *.
    repeat flatten_all.
    simpl in *.
    unfold cfg_join in *.
    inv H.
    simpl in *.
    intro_snd_evaluate.
    apply IHc in Heq.
    simpl in *.
    destruct Heq.
    unfold incl in *.
    split ; intros
    ; break_list_goal
    ; simpl in *.
    apply H in H1 ; intuition.
    destruct H1.
    intuition.
    do 2 in_list_rem ; apply H0 in H1 ; intuition.
  - unfold mk_while in *.
    simpl in *.
    repeat flatten_all.
    simpl in *.
    unfold cfg_while_loop in *.
    inv H.
    simpl in *.
    intro_snd_evaluate.
    apply IHc in Heq.
    simpl in *.
    destruct Heq.
    unfold incl in *.
    split ; intros
    ; break_list_goal
    ; simpl in *.
    destruct H1.
    intuition.
    in_list_rem ; apply H in H1 ; intuition.
    destruct H1.
    intuition.
    in_list_rem ; apply H0 in H1 ; intuition.
Qed.


Definition max_label (dg : dcfg) (max : block_id) :=
  max_bid (inputs (graph dg) ++ outputs (graph dg)) = max.

Definition min_label (dg : dcfg) (min : block_id) :=
  min_bid (inputs (graph dg) ++ outputs (graph dg)) = min.

Definition interval_label (dg : dcfg) (min max : block_id) :=
  max_label dg max /\ min_label dg min.

Open Scope Z_scope.

(* NOTE important - easy but tedious *)
Theorem inv_name_anon : forall (σ: FST) (c : cfg_lang) (dg : dcfg),
    snd ((evaluate c) σ) = dg ->
    wf_name dg.
Proof.
  intros *. revert σ dg.
  unfold wf_name.
  pose proof inv_wf_inputs_outputs as INV_IN_OUT ;
    unfold wf_inputs in INV_IN_OUT.
  induction c ; intros ; simpl in H.
  - admit.
  - unfold mk_seq in H
    ; repeat flatten_all
    ; simpl in *.
    inv H ; simpl.
    unfold cfg_seq ; simpl.
    repeat flatten_all ; simpl in *.
    repeat intro_snd_evaluate.
    match goal with
    | h:context[snd (evaluate ?c ?σ) = ?dg] |- _ =>
        let B := fresh "H" in
        assert (B : snd (evaluate c σ) =  dg) by now rewrite h
        (* ; apply INV_IN_OUT in B *)
    end.
    apply INV_IN_OUT in H ; destruct H.
    apply IHc2 in Heq0 ; simpl in Heq0.
   match goal with
    | h:context[snd (evaluate ?c ?σ) = ?dg] |- _ =>
        let B := fresh "H" in
        assert (B : snd (evaluate c σ) =  dg) by now rewrite h
        (* ; apply INV_IN_OUT in B *)
    end.
    apply INV_IN_OUT in H1 ; destruct H1.
    apply IHc1 in Heq ; simpl in Heq.
    simpl in *.
    split
    ; break_list_goal
    (* ; rewrite !Forall_app *)
    ; intuition
    ; cbn
    ; break_list_goal
    ; rewrite !List.Forall_app
    ; intuition
    ; [apply incl_Forall with (l1 := outs0) | apply incl_Forall with (l1 := ins1)]
    ; unfold incl ; intros
    ; try (
          match goal with | h: In _ [_] |- _ => apply In_singleton in h end
          ; subst ; apply hd_In
        ).
    admit. (* true by invariant on length outs *)
    eapply incl_Forall ; try eassumption.
    admit. (* true by invariant on length ins *)
    eapply incl_Forall ; try eassumption.
  - admit.
  - admit.
  - admit.
Admitted.


(* TODO important invariant here - some work todo *)
Lemma inv_counter_bid :
  forall (c : cfg_lang) (cb cb' : nat) (cr cr' : int) (dg : dcfg) min max,
    (evaluate c) {| counter_bid := cb; counter_reg := cr |}
    = ({| counter_bid := cb'; counter_reg := cr' |}, dg) ->
    interval_label dg min max ->
    name cb' = next_anon max.
Proof.
  induction c ; intros ; subst ; simpl in *.
  - unfold mk_block in *.
    unfold freshLabel, interval_label in *.
    simpl in * ; repeat flatten_all ; simpl in *.
    inv H.
    unfold cfg_block in *.
    unfold max_label, min_label in *.
    cbn in *.
    rewrite leb_bid_refl in *.
    unfold leb_bid in *. simpl in *.
    match goal with
    | h:context[ ?x <? ?y ] |- _ =>
        let H := fresh "H" in
        assert (H : x <? y = true) by admit
        ; rewrite H in * ; clear H
    end; simpl in *.
    destruct H0 ; subst.
    rewrite next_anon_name.
    rewrite <- Nat.add_1_l.
    now rewrite Nat.add_comm.
  - unfold mk_seq in *.
    repeat flatten_all ; simpl in *.
    inv H.
    destruct f.
    eapply IHc1 in Heq.
    eapply IHc2 in Heq0.
    eassumption.
    all: eexists.
    unfold cfg_seq in H0.
    unfold interval_label, max_label in H0 ; destruct H0 as [MAX_LABEL _].
    simpl in *.
    admit. (* there is some work to do here *)
    eexists.
    eexists.
    eexists.
  - unfold mk_branch in *.
    repeat flatten_all ; simpl in *.
    repeat flatten_all ; simpl in *.
    inv H0.
    admit.
  - unfold mk_join in *.
    repeat flatten_all ; simpl in *.
    repeat flatten_all ; simpl in *.
    inv H0.
    admit.
  - unfold mk_while in *.
    repeat flatten_all ; simpl in *.
    repeat flatten_all ; simpl in *.
    inv H0.
    admit.
Admitted.

Lemma inv_max_label :
  forall (cb cb' : nat) (cr cr' : int) (c : cfg_lang) (dg : dcfg) min max,
    interval_label dg min max ->
    (evaluate c) {| counter_bid := cb; counter_reg := cr |}
    = ({| counter_bid := cb'; counter_reg := cr' |}, dg) ->
    lt_bid max (name cb').
Proof.
  intros.
  assert (INV_ANON := H0).
  assert (LEN_OUTS := H0).
  assert (LEN_INS := H0).
  assert (INS := H0).
  do 4 intro_snd_evaluate.
  apply inv_name_anon in INV_ANON.
  unfold wf_name in INV_ANON.
  apply inv_len_inputs in LEN_INS.
  apply inv_len_outputs in LEN_OUTS.
  apply inv_wf_inputs_outputs in INS.
  destruct INS as [INCL_IN INCL_OUT] ; unfold wf_inputs in *.
  eapply inv_counter_bid in H0 ; try eassumption.
  rewrite H0.
  apply lt_bid_next.
  destruct H as [H _]; unfold max_label in H.
  assert (In max (inputs (graph dg) ++ outputs (graph dg))).
  rewrite <- H. apply max_bid_in. intro.
  apply length_zero_iff_nil in H1.
  rewrite app_length in H1.
  eapply length_incl in LEN_INS ; try eassumption.
  lia.
  apply in_app_or in H1 ; destruct H1
  ; destruct INV_ANON as [INV_ANON_IN INV_ANON_OUT]
  ; rewrite Forall_forall in INV_ANON_IN, INV_ANON_OUT.
  now apply INV_ANON_IN.
  now apply INV_ANON_OUT.
Qed.

(* TODO important invariant here - some work todo *)
Lemma inv_min_label :
  forall (c : cfg_lang) (cb cb' : nat) (cr cr' : int) (dg : dcfg) min max,
    (evaluate c) {| counter_bid := cb; counter_reg := cr |}
    = ({| counter_bid := cb'; counter_reg := cr' |}, dg) ->
    interval_label dg min max ->
    min = name cb.
Proof.
  induction c ; intros ; subst ; simpl in *.
  - unfold mk_block in *.
    unfold freshLabel, interval_label in *.
    simpl in * ; repeat flatten_all ; simpl in *.
    inv H.
    unfold cfg_block in *.
    unfold max_label, min_label in *.
    cbn in *.
    rewrite leb_bid_refl in *.
    unfold leb_bid in * ; simpl in *.
    match goal with
    | h:context[ ?x <? ?y ] |- _ =>
        let H := fresh "H" in
        assert (H : x <? y = true) by admit
        ; rewrite H in * ; clear H
    end ; simpl in *.
    intuition.
  - unfold mk_seq in H
    ; repeat flatten_all ; simpl in *.
    inv H.
    destruct f ; eapply IHc1 in Heq. eassumption.
    eapply IHc2 in Heq0.
    all: eexists.
    all: try eexists. (* it's still some work to do here *)
    (* NOTE similar than inv_counter_bid *)
Admitted.

(* NOTE relies on inv_counter_bid' and  inv_min_label *)
 Theorem inv_interval_name :
  forall (c1 c2 : cfg_lang) (σ1 σ2 σ3: FST) (dg1 dg2 : dcfg) min1 max1 min2 max2,
    interval_label dg1 min1 max1 ->
    interval_label dg2 min2 max2 ->
    (evaluate c1) σ1 = (σ2, dg1) ->
    (evaluate c2) σ2 = (σ3, dg2) ->
    lt_bid max1 min2.
Proof.
  intros.
  destruct σ1, σ2, σ3.
  assert (H' := H)
  ; eapply inv_max_label in H ; try eassumption
  ; eapply inv_min_label in H' ; try eassumption.
   assert (H0' := H0)
  ; eapply inv_max_label in H0 ; try eassumption
   ; eapply inv_min_label in H0' ; try eassumption.
  now subst.
Qed.

Ltac auto_apply :=
  match goal with
  | h1 : context [ In _ (?f ?g) -> _ ] |- _ =>
      match goal with
      | h : In _ (f g) |- _ => apply h1 in h
      end
  end.

Lemma inv_interval_independant :
  forall dg1 dg2 min1 max1 min2 max2,
    wf_dcfg dg1 -> wf_dcfg dg2 ->
    (length (inputs (graph dg1) ++ outputs (graph dg1)) >= 1)%nat ->
    (length (inputs (graph dg2) ++ outputs (graph dg2)) >= 1)%nat ->
    interval_label dg1 min1 max1 ->
    interval_label dg2 min2 max2 ->
    lt_bid max1 min2 ->
    independent_flows_dcfg dg1 dg2 /\ (outs dg1) ⊍ (outs dg2).
Proof.
  intros * WF_G1 WF_G2 HL1 HL2 INT_G1 INT_G2 LE.
  unfold independent_flows_dcfg, independent_flows,
    interval_label, max_label, min_label in *.
  destruct dg1, dg2.
  simpl in *.
  unfold no_reentrance, no_duplicate_bid.
  destruct INT_G1 as [ MAX_G1 _ ], INT_G2 as [ _ MIN_G2 ].
  eapply max_bid_spec_nn in HL1 ; try eassumption.
  eapply min_bid_spec_nn in HL2 ; try eassumption.
  rewrite Forall_app in HL1,HL2.
  intuition
  ; rewrite Forall_forall in *
  ; unfold list_disjoint
  ; repeat intro
  ; subst
  ; remember (inputs graph1 ++ outputs graph1) as dg1
  ; remember (inputs graph0 ++ outputs graph0) as dg0
  ; repeat auto_apply.
  - eapply le_bid_trans in H4 ; try eassumption.
    eapply lt_bid_trans_le in LE ; try eassumption.
    now apply lt_bid_irrefl in LE.
  - eapply lt_bid_trans_le in LE ; try eassumption.
    eapply lt_bid_trans_le2 in LE ; try eassumption.
    now apply lt_bid_irrefl in LE.
  - eapply lt_bid_trans_le in LE ; try eassumption.
    eapply lt_bid_trans_le2 in LE ; try eassumption.
    now apply lt_bid_irrefl in LE.
  - unfold wf_dcfg, wf_outputs in *  ; simpl in *.
    destruct WF_G1 as [_ [[INCL_G1 _]  _]].
    destruct WF_G2 as [_ [[INCL_G2 _]  _]].
    eapply incl_In in H3,H4 ; try eassumption.
    repeat auto_apply.
    eapply le_bid_trans in H3 ; try eassumption.
    eapply lt_bid_trans_le2 in LE ; try eassumption.
    now apply lt_bid_irrefl in LE.
Qed.


Theorem inv_independent_flows :
  forall (σ1 σ2 σ3: FST) (c1 c2 : cfg_lang) (dg1 dg2 : dcfg),
    wf_dcfg dg1 ->
    wf_dcfg dg2 ->
    (evaluate c1) σ1 = (σ2, dg1) ->
    (evaluate c2) σ2 = (σ3, dg2) ->
    independent_flows_dcfg dg1 dg2.
Proof.
  intros * WF_DG1 WF_DG2 ; intros.
  pose proof (inv_interval_independant dg1 dg2).
  unfold independent_flows_dcfg, independent_flows in *.
  pose proof (inv_interval_name c1 c2 σ1 σ2 σ3 dg1 dg2).
  eapply H1 in H2
  ; try intuition
  ; try
      ( assert (H' := H) ; assert (H0' := H0)
        ; do 4 intro_snd_evaluate
        ; apply inv_len_outputs in H
        ; apply inv_len_inputs in H0
        ; apply inv_wf_inputs_outputs in H', H0'
        ; unfold wf_inputs in H0'
        ; destruct H' as [ _ H' ], H0' as [ H0' _ ]
        ; rewrite app_length
        ; eapply length_incl in H', H0' ; try eassumption
        ; lia).
  all : eexists.
  all : eexists.
Qed.

Theorem inv_disjoint_outputs :
  forall (σ1 σ2 σ3: FST) (c1 c2 : cfg_lang) (dg1 dg2 : dcfg),
    wf_dcfg dg1 ->
    wf_dcfg dg2 ->
    (evaluate c1) σ1 = (σ2, dg1) ->
    (evaluate c2) σ2 = (σ3, dg2) ->
    (outs dg1) ⊍ (outs dg2).
Proof.
  intros * WF_DG1 WF_DG2 ; intros.
  pose proof (inv_interval_independant dg1 dg2).
  unfold independent_flows_dcfg, independent_flows in *.
  pose proof (inv_interval_name c1 c2 σ1 σ2 σ3 dg1 dg2).
  eapply H1 in H2
  ; try intuition
  ; try
      ( assert (H' := H) ; assert (H0' := H0)
        ; do 4 intro_snd_evaluate
        ; apply inv_len_outputs in H
        ; apply inv_len_inputs in H0
        ; apply inv_wf_inputs_outputs in H', H0'
        ; unfold wf_inputs in H0'
        ; destruct H' as [ _ H' ], H0' as [ H0' _ ]
        ; rewrite app_length
        ; eapply length_incl in H', H0' ; try eassumption
        ; lia).
  all : eexists.
  all : eexists.
Qed.


(** WF lemmas on the interface *)

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
  unfold wf_name.
  simpl.
  split
  ; apply Forall_cons
  ; try apply is_anon_name
  ; try apply Forall_nil.
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
  unfold wf_dcfg, wf_inputs, wf_outputs, mk_seq, wf_graph, wf_ocfg_bid, wf_name.
  destruct σ ; cbn.
  unfold wf_dcfg, wf_inputs, wf_outputs, wf_graph, wf_ocfg_bid,wf_name in WF_G1, WF_G2.
  destruct WF_G1 as [INPUTS_G1 [[OUTPUTS_G1 [DISJOINTS_G1 OUTS_NOREP_G1]] [WF_BID_G1 [NAME_IN_G1 NAME_OUT_G1]]]].
  destruct WF_G2 as [INPUTS_G2 [[OUTPUTS_G2 [DISJOINTS_G2 OUTS_NOREP_G2]] [WF_BID_G2 [NAME_IN_G2 NAME_OUT_G2]]]].
  unfold incl.
  cbn in *.
  intuition ; repeat flatten_all.
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
      rewrite eqb_bid_refl.
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
    apply list_norepet_append.
    now apply list_norepet_remove.
    assumption.
    now eapply remove_disjoint.
  - unfold cfg_seq ; simpl in *.
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
  - simpl in *.
    unfold cfg_seq ; simpl.
    repeat intro_snd_evaluate.
    break_list_goal
    ; rewrite !Forall_app
    ; intuition
    ; cbn.
    apply incl_Forall with (l1 := outs0).
    apply incl_cons ; [ assumption | apply incl_nil_l ].
    eapply incl_Forall ; eassumption.
  - simpl in *.
    unfold cfg_seq ; simpl.
    repeat intro_snd_evaluate.
    break_list_goal
    ; rewrite !Forall_app
    ; intuition
    ; cbn.
    apply incl_Forall with (l1 := ins1).
    apply incl_cons ; [ assumption | apply incl_nil_l ].
    eapply incl_Forall ; eassumption.
Qed.

Lemma wf_mk_join : forall σ g out1 out2,
    out1 <> out2 ->
    List.In out1 (outs g) ->
    List.In out2 (outs g) ->
    wf_dcfg g ->
    wf_dcfg (snd ((mk_join g out1 out2) σ)).
Proof.
  intros * NEQ_OUTS OUT1_OUTS OUT2_OUTS WF_G.
  unfold wf_dcfg, wf_inputs, wf_outputs, mk_seq, wf_graph, wf_ocfg_bid, wf_name.
  destruct σ ; cbn.
  unfold wf_dcfg, wf_inputs, wf_outputs, wf_graph, wf_ocfg_bid, wf_name in WF_G.
  destruct WF_G as [INPUTS_G [[OUTPUTS_G [DISJOINTS_G OUTS_NOREP_G]] [WF_BID_G [NAME_IN_G NAME_OUT_G]]]].
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
    now repeat in_list_rem.
  - unfold cfg_join.
    break_list_goal.
    simpl in *.
    apply Coqlib.list_disjoint_cons_l.
    + apply list_disjoint_app_r.
      split.
      * now do 2 apply remove_disjoint.
      * apply remove_disjoint_remove.
        rewrite list_cons_app.
        rewrite CFGC_Utils.remove_app.
        simpl.
        rewrite eqb_bid_refl.
        apply eqb_bid_neq in NEQ_OUTS ; rewrite eqb_bid_comm,NEQ_OUTS ; simpl.
        apply remove_disjoint.
        apply remove_disjoint_remove.
        rewrite list_cons_app.
        rewrite CFGC_Utils.remove_app.
        simpl.
        rewrite eqb_bid_refl.
        simpl ; now apply list_disjoint_nil_r.
    + (* freshness of (name counter_bid0)*)
      (* ~ In (name cb) (inputs graph0) /\ ~ In (name cb) (outputs graph0) *)
      admit.
  - unfold cfg_join.
    break_list_goal.
    simpl in *.
    apply list_norepet_cons.
    + intro contra.
      do 2 apply CFGC_Utils.in_remove in contra.
      (* freshness counter_bid0 *)
      (* ~ In (name cb) (inputs graph0) /\ ~ In (name cb) (outputs graph0) *)
      admit.
    + now do 2 apply list_norepet_remove.
  - unfold cfg_join.
    break_list_goal.
    simpl in *.
    apply Coqlib.list_norepet_append ; try assumption.
    apply list_norepet_cons ; try apply List_norepet_singleton.
    now rewrite In_singleton.
    apply list_disjoint_sym.
    apply incl_disjoint with (l1 := outs0) ; try assumption.
    apply incl_cons ; try assumption.
    apply incl_cons ; try assumption ; try apply incl_nil_l.
  - unfold cfg_join ; simpl.
    break_list_goal
    ; rewrite !Forall_app
    ; intuition
    ; cbn.
    apply incl_Forall with (l1 := outs0).
    apply incl_cons ; [ assumption | apply incl_nil_l ].
    eapply incl_Forall ; eassumption.
    apply incl_Forall with (l1 := outs0).
    apply incl_cons ; [ assumption | apply incl_nil_l ].
    eapply incl_Forall ; eassumption.
  - unfold cfg_join ; simpl.
    break_list_goal
    ; rewrite !Forall_app
    ; intuition
    ; cbn.
    apply Forall_cons ; [ apply is_anon_name | apply Forall_nil ].
    apply Forall_cons ; [ apply is_anon_name | apply Forall_nil ].
Admitted.

Lemma wf_mk_branch : forall σ cond gT gF inT inF,
    independent_flows_dcfg gT gF ->
    (outs gT) ⊍ (outs gF) ->
    List.In inT (ins gT) ->
    List.In inF (ins gF) ->
    wf_dcfg gT ->
    wf_dcfg gF ->
    wf_dcfg (snd ((mk_branch cond gT gF inT inF) σ)).
Proof.
  intros *  INDEPENDENT_FLOWS DISJOINT_OUTS IN_T IN_F WF_GT WF_GF.
  unfold wf_dcfg, wf_inputs, wf_outputs, mk_seq, wf_graph, wf_ocfg_bid, wf_name.
  destruct σ ; cbn.
  unfold wf_dcfg, wf_inputs, wf_outputs, wf_graph, wf_ocfg_bid, wf_name in WF_GT, WF_GF.
  destruct WF_GT as [INPUTS_GT [[OUTPUTS_GT [DISJOINTS_GT NO_REP_GT]] [WF_BID_GT [NAME_IN_GT NAME_OUT_GT]]]].
  destruct WF_GF as [INPUTS_GF [[OUTPUTS_GF [DISJOINTS_GF NO_REP_GF]] [WF_BID_GF [NAME_IN_GF NAME_OUT_GF]]]].
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
    unfold independent_flows_dcfg,independent_flows,no_reentrance in *
    ; simpl in *.
    break_list_goal.
    apply list_disjoint_app_l.
    split ; eapply list_disjoint_sym ; apply list_disjoint_app_l.
    intuition.
    eapply incl_disjoint ; [unfold incl ; intros ; eassumption
                           | try assumption ; try  now apply list_disjoint_sym].
    apply list_disjoint_sym.
    eapply incl_disjoint with (l1 := outputs graph0) ; assumption.
    intuition.
    apply list_disjoint_sym.
    eapply incl_disjoint with (l1 := outputs graph1) ; assumption.
    eapply incl_disjoint ; [unfold incl ; intros ; eassumption
                           | try assumption ; try  now apply list_disjoint_sym].
    (* freshness (name counter_bid0)*)
    (* ~ In (name cb) (outputs graph0) /\ ~ In (name cb) (outputs graph1) *)
    admit.
  - apply list_norepet_append ; assumption.
  - break_list_goal.
    apply Coqlib.list_norepet_append ; try assumption
    ; try apply List_norepet_singleton.
    + apply Coqlib.list_norepet_append ; try assumption.
      unfold independent_flows_dcfg,independent_flows,no_duplicate_bid in *
      ; simpl in *.
      intuition.
    + apply Util.list_disjoint_singleton_left.
    (* ~ In (name cb) (inputs graph0) /\ ~ In (name cb) (inputs graph1) *)
    (* freshness (name counter_bid0) *)
    admit.
  - break_list_goal
    ; rewrite !Forall_app
    ; intuition
    ; cbn
    ; apply Forall_cons ; [ apply is_anon_name | apply Forall_nil ].
  - break_list_goal
    ; rewrite !Forall_app
    ; intuition
    ; cbn.
    rewrite list_cons_app.
    apply Forall_app.
    split.
    eapply incl_Forall
    ; unfold incl
    ; [intros * HIN ; apply In_singleton in HIN ; subst a ; eassumption|] .
    eapply incl_Forall ; eassumption.
    eapply incl_Forall
    ; unfold incl
    ; [intros * HIN ; apply In_singleton in HIN ; subst a ; eassumption|] .
    eapply incl_Forall ; eassumption.
Admitted.

Lemma wf_mk_while : forall σ expr_code cond gB inB outB,
    List.In outB (outs gB) ->
    List.In inB (ins gB) ->
    wf_dcfg gB ->
    wf_dcfg (snd ((mk_while expr_code cond gB inB outB) σ)).
Proof.
  intros * OUTPUT INPUT WF_G.
  unfold wf_dcfg, wf_inputs, wf_outputs, mk_seq, wf_graph, wf_ocfg_bid, wf_name.
  destruct σ ; cbn.
  unfold wf_dcfg, wf_inputs, wf_outputs, wf_graph, wf_ocfg_bid, wf_name in WF_G.
  destruct WF_G as [INPUTS_G [[OUTPUTS_G [DISJOINTS_G NO_REP_G]] [WF_BID_G [NAME_IN_G NAME_OUT_G]]]].
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
          | simpl ; rewrite eqb_bid_refl
            ; apply list_disjoint_nil_r].
      * (* freshness (name counter_bid0) *)
        (* ~ In (name cb) (outputs graph0) *)
        admit.
    + (* freshness (name counter_bid0) *)
      (* ~ In (name (S cb)) (outputs graph0) /\ ~ In (name (S cb)) (inputs graph0) *)
      admit.
  - break_list_goal.
    simpl in *.
    break_list_goal.
    apply list_norepet_append ; try assumption.
    apply List_norepet_singleton.
    now apply list_norepet_remove.
    apply list_disjoint_singleton_left.
    (* ~ In (name (S cb)) (outputs graph0) *)
    admit. (* freshness counter_bid0 *)
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
    apply not_in_app.
    split.
    admit. (* should be an hypothesis *)
    intro. apply In_singleton in H.
    subst.
    apply OUTPUTS_G in OUTPUT. (* (not OUTPUT) should be an hypothesis hypothesis *)
    admit.
    (* NOTE: freshness (name counter_bid0) *)
  - break_list_goal
    ; rewrite !Forall_app
    ; intuition
    ; cbn.
    apply Forall_cons ; [ apply is_anon_name | apply Forall_nil ].
    eapply incl_Forall
    ; unfold incl
    ; [intros * HIN ; apply In_singleton in HIN ; subst a ; eassumption|] .
    eapply incl_Forall ; eassumption.
  - break_list_goal
    ; rewrite !Forall_app
    ; intuition
    ; cbn.
    break_list_goal
    ; rewrite !Forall_app
    ; intuition
    ; cbn.
    eapply incl_Forall
    ; unfold incl
    ; [intros * HIN ; apply In_singleton in HIN ; subst a ; eassumption|] .
    eapply incl_Forall ; eassumption.
    apply Forall_cons ; [ apply is_anon_name | apply Forall_nil ].
    apply Forall_cons ; [ apply is_anon_name | apply Forall_nil ].
Admitted.

(* WF EVALUATE *)
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
    + assert (Heq' := Heq )
      ; assert (Heq0' := Heq0 )
      ; do 2 intro_snd_evaluate
      ; apply IHc1 in Heq'
      ; apply IHc2 in Heq0'
      ; eapply inv_independent_flows ; try eassumption.
    (* PROVE INVARIANT INDEPENDENT FLOWS  *)
    + assert (Heq' := Heq )
      ; assert (Heq0' := Heq0 )
      ; do 2 intro_snd_evaluate
      ; apply IHc1 in Heq'
      ; apply IHc2 in Heq0'
      ; eapply inv_disjoint_outputs ; try eassumption.
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
    + assert (Heq' := Heq )
      ; assert (Heq0' := Heq0 )
      ; do 2 intro_snd_evaluate
      ; apply IHc1 in Heq'
      ; apply IHc2 in Heq0'
      ; eapply inv_independent_flows ; eassumption.
    + assert (Heq' := Heq )
      ; assert (Heq0' := Heq0 )
      ; do 2 intro_snd_evaluate
      ; apply IHc1 in Heq'
      ; apply IHc2 in Heq0'
      ; eapply inv_disjoint_outputs ; eassumption.
    + apply hd_In.
      apply (inv_len_inputs σ c1 d). now rewrite Heq.
    + apply hd_In.
      apply (inv_len_inputs f c2 d0). now rewrite Heq0.
    + eapply IHc1. now erewrite Heq.
    + eapply IHc2. now erewrite Heq0.
  - repeat flatten_all.
    rewrite <- H.
    apply wf_mk_join.
    + admit. (* we have no_repet_outs thanks to WF + (hd l) and (hd (tl l))*)
    + apply hd_In.
      apply (inv_len_outputs σ c d). now rewrite Heq.
    + admit. (* TODO we need WF on cfg_lang st JOIN can only take cfg_lang with at least 2 outputs *)
    + eapply IHc. now erewrite Heq.
  - repeat flatten_all.
    rewrite <- H.
    apply wf_mk_while.
    + apply hd_In.
      apply (inv_len_outputs σ c d). now rewrite Heq.
    + apply hd_In.
      apply (inv_len_inputs σ c d). now rewrite Heq.
    + eapply IHc. now erewrite Heq.
Admitted.


(** Recover the hypothesis we need to use the denotation lemmas *)
Theorem wf_evaluate_wf_seq : forall σ0 σ1 σ2 c1 c2 graph1 ins1 outs1 graph2 ins2 outs2,
    evaluate c1 σ0 = (σ1, {| graph := graph1; ins := ins1; outs := outs1 |}) ->
    evaluate c2 σ1 = (σ2, {| graph := graph2; ins := ins2; outs := outs2 |}) ->
    wf_seq graph1 graph2 (hd default_bid outs1) (hd default_bid ins2).
Proof.
  intros * E1 E2.
  pose proof wf_evaluate as WF_EVAL.
  pose proof inv_independent_flows as INV_INDE_FLOWS.
  unfold independent_flows_dcfg, independent_flows in INV_INDE_FLOWS.
  assert (E1' := E1).
  assert (E2' := E2).
  do 2 intro_snd_evaluate.
  apply WF_EVAL in E1', E2' ; clear WF_EVAL.
  eapply INV_INDE_FLOWS in E2 ; try eapply E1 ; clear INV_INDE_FLOWS.
  unfold wf_seq, wf_dcfg, wf_inputs,
    wf_outputs, wf_graph, wf_name, free_in_cfg, no_reentrance in *
  ; simpl in *.
  intuition.
  (* In (hd default_bid outs1) (inputs graph1) *)
  (* (hd default_bid outs1) ∈ outs1
    ∧ outs1 ⊍ inputs graph1 *)
  admit.
  (* In (hd default_bid outs1) (inputs graph2) *)
  (* (hd default_bid outs1) ∈ outs1
    ∧ outs1 ⊆ (outputs graph1)
    ∧ outputs graph1 ⊍ inputs graph2 *)
  admit.
  (* In (hd default_bid ins2) (inputs graph1) *)
  admit.
  (* In (hd default_bid outs1) (ouputs graph2) *)
  admit.
  (* hd default_bid outs1 = hd default_bid ins2 *)
  (* outs1 ⊆ outputs graph1
     ∧ ins2 ⊆ inputs graph2
     ∧ outputs graph1 ⊍ inputs graph2
   *)
  admit.
Admitted.

Lemma evaluate_fresh : forall f1 f2 f3 b c dg min max,
    (evaluate c) f1 = (f2, dg) ->
    freshLabel f2 = (f3, b) ->
    interval_label dg min max ->
    ~ List.In b (inputs (graph dg)++outputs (graph dg)).
Proof.
  intros.
  destruct f1, f2.
  assert (H1' := H1).
  eapply inv_max_label in H1 ; try apply H ; try reflexivity.
  unfold interval_label in H1'; destruct H1' as [ LOWER_BOUND _ ].
  unfold max_label in LOWER_BOUND.
  unfold freshLabel in H0 ; inversion H0 ; subst b.
  apply ord_list ; rewrite LOWER_BOUND ; assumption.
Qed.

Lemma evaluate_fresh' : forall f1 f2 f3 f4 b1 b2 c dg min max,
    (evaluate c) f1 = (f2, dg) ->
    freshLabel f2 = (f3, b1) ->
    freshLabel f3 = (f4, b2) ->
    interval_label dg min max ->
    ~ List.In b2 (inputs (graph dg)++outputs (graph dg)).
Proof.
  intros.
  destruct f1, f2, f3.
  assert (H2' := H2).
  eapply inv_max_label in H2 ; try apply H ; try reflexivity.
  unfold interval_label in H2' ; destruct H2' as [ LOWER_BOUND _ ].
  unfold max_label in LOWER_BOUND.
  unfold freshLabel in H0,H1. inversion H0; inversion H1. subst b1 b2.
  destruct H1.
  subst counter_bid2.
  eapply ord_list.
  eapply evaluate_fresh in H ; try eassumption.
  rewrite LOWER_BOUND.
  now apply lt_bid_S.
  eexists.  all :eexists.
Qed.

Theorem wf_evaluate_wf_while :
  forall f0 f1 f2 f3 c graph ins outs b1 b2 code cond,
    evaluate c f0 = (f1, {| graph := graph; ins := ins; outs := outs |}) ->
    freshLabel f1 = (f2, b1) ->
    freshLabel f2 = (f3, b2) ->
    wf_while code cond graph
             b1 (hd CFGC_Interface.default_bid ins)
             b2 (hd CFGC_Interface.default_bid outs).
Proof.
  intros * E FRESH1 FRESH2.
  pose proof wf_evaluate as WF_EVAL.
  unfold wf_while.
  repeat split.
  - eapply freshLabel_fresh ; eassumption.

  - pose proof evaluate_fresh
    ; assert (E' := E)
    ; assert (E'' := E)
    ; eapply H in E ; try eassumption ; [|eexists; eexists]
    ; apply not_in_app_l in E
    ; do 2 intro_snd_evaluate
    ; apply WF_EVAL in E'
    ; unfold wf_dcfg in E' ; destruct E' as [ E' _]
    ; unfold wf_inputs in E'
    ; eapply not_in_incl in E ; try eassumption ; simpl in E
    ; unfold not in E
    ; intro ; subst
    ; apply inv_len_inputs in E'' ; simpl in E''
    ; eapply hd_In in E'' ; apply E in E'' ; apply E''.

  - pose proof evaluate_fresh
    ; assert (E' := E)
    ; assert (E'' := E)
    ; eapply H in E ; try eassumption ; [|eexists; eexists]
    ; apply not_in_app_r in E
    ; do 2 intro_snd_evaluate
    ; apply WF_EVAL in E'
    ; unfold wf_dcfg in E' ; destruct E' as [ _ [E' _]]
    ; unfold wf_outputs in E' ; destruct E' as [ E' _ ] ; simpl in E'
    ; eapply not_in_incl in E ; try eassumption ; simpl in E
    ; unfold not in E
    ; intro ; subst
    ; apply inv_len_outputs in E'' ; simpl in E''
    ; eapply hd_In in E'' ; apply E in E'' ; apply E''.

  - pose proof evaluate_fresh'
    ; assert (E' := E)
    ; assert (E'' := E)
    ; eapply H in E ; try eassumption ; [|eexists; eexists]
    ; apply not_in_app_l in E
    ; do 2 intro_snd_evaluate
    ; apply WF_EVAL in E'
    ; unfold wf_dcfg in E' ; destruct E' as [ E' _ ]
    ; unfold wf_inputs in E'
    ; eapply not_in_incl in E ; try eassumption ; simpl in E
    ; unfold not in E
    ; intro ; subst
    ; apply inv_len_inputs in E'' ; simpl in E''
    ; eapply hd_In in E'' ; apply E in E'' ; apply E''.

  - pose proof evaluate_fresh'
    ; assert (E' := E)
    ; assert (E'' := E)
    ; eapply H in E ; try eassumption ; [|eexists; eexists]
    ; apply not_in_app_r in E
    ; do 2 intro_snd_evaluate
    ; apply WF_EVAL in E'
    ; unfold wf_dcfg in E' ; destruct E' as [ _ [E' _]]
    ; unfold wf_outputs in E' ; destruct E' as [ E' _ ] ; simpl in E'
    ; eapply not_in_incl in E ; try eassumption ; simpl in E
    ; unfold not in E
    ; intro ; subst
    ; apply inv_len_outputs in E'' ; simpl in E''
    ; eapply hd_In in E'' ; apply E in E'' ; apply E''.

  - unfold free_in_cfg ;
    pose proof evaluate_fresh
    ; assert (E' := E)
    ; eapply H in E ; try eassumption ; [|eexists; eexists]
    ; apply not_in_app_l in E ; assumption.

  - unfold free_in_cfg
    ; pose proof evaluate_fresh'
    ; assert (E' := E)
    ; eapply H in E ; try eassumption ; [|eexists; eexists]
    ; apply not_in_app_l in E ; assumption.

  - unfold free_in_cfg
    ; assert (E' := E)
    ; assert (E'' := E)
    ; do 2 intro_snd_evaluate
    ; apply WF_EVAL in E'
    ; unfold wf_dcfg in E' ; destruct E' as [ _ [E' _]]
    ; unfold wf_outputs in E' ; destruct E' as [ _ [ E' _ ]] ; simpl in E'
    ; apply inv_len_outputs in E'' ; simpl in E''
    ; intro ; simpl
    ; apply hd_In with (d := default_bid) in E''.
    eapply list_disjoint_notin in E' ; eapply E' in H ; eauto.

  - intro_snd_evaluate ; apply WF_EVAL in E
    ; apply wf_dcfg_ocfg in E ; now simpl in E.

  - pose proof inv_len_inputs.
    assert (E' := E).
    do 2 intro_snd_evaluate.
    apply WF_EVAL in E' ; unfold wf_dcfg, wf_inputs in E'
    ; destruct E' as [ E' _ ] ; simpl in E'.
    unfold incl in E'.
    apply E' ; clear E'.
    apply H in E ; simpl in E.
    now apply hd_In.
Qed.

Require Import CFGC_DenotationsCombinators.
Definition denote_dcfg (dg : dcfg) := denote_cfg (graph dg).
Definition denote_cfg_lang (g : cfg_lang) (σ : FST) := denote_dcfg (snd ((evaluate g) σ)).


(* TODO :
- Add the hypothesis of freshness to the lemmas wf_mk_combinators (+ fix uses )
- Write and prove all the needed wf_evaluate_wf_combinator
  (ie. see the compiler to know which one I need)
- End the proof of the counter_bid ( inv_max_label, inv_min_label )
- I need a way to have a property st. we know that if (CJoin c),
  c have always at least 2 outputs
- Correctness compiler
 *)
