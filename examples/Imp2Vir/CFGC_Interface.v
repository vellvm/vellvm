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

  Definition is_anon (b : block_id) : Prop :=
    exists n, b = Anon n.

  Lemma is_anon_name : forall n, is_anon (name n).
  Proof.
    intros.
    unfold name, mk_anon.
    unfold is_anon.
    now eexists.
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

  Fixpoint len_entry_exit (cfg : cfg_lang) : (nat * nat) :=
    match cfg with
    | CBlock c => (1,1)
    | CSeq c1 c2 =>
        let '(i1,e1) := len_entry_exit c1 in
        let '(i2,e2) := len_entry_exit c2 in
        (i1+i2, e1+e2)
    | CBranch _ c1 c2 =>
        let '(i1,e1) := len_entry_exit c1 in
        let '(i2,e2) := len_entry_exit c2 in
        (i1+i2-1, e1+e2)
    | CJoin c =>
        let '(i,e) := len_entry_exit c in
        (i, e-1)
    | CWhile _ _ c => len_entry_exit c
    end.

  Definition wf_cfg_lang c :=
    forall i e,
    len_entry_exit c = (i,e) ->
    i >= 1 /\ e >= 1.
  From Vellvm Require Import Utils.Tactics.
  From Coq Require Import Lia.

  Lemma t :
    forall c c1 i e,
      c = CJoin c1 ->
      wf_cfg_lang c ->
      len_entry_exit c1 = (i,e) ->
      e >= 2.
  Admitted.


  (* TODO I want to ensure that,
     for CJoin c, len_entry_exit c = (i,e) -> e >= 2 (else it is not WF)
   *)

End CFG_LANG.



Require Import Coqlib.
Require Import Util.

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

Fixpoint max_bid' (l : list block_id) b :=
  match l with
  | [] => b
  | h :: t => if leb_bid b h then max_bid' t h else max_bid' t b
  end.

Fixpoint min_bid' (l : list block_id) b :=
  match l with
  | [] => b
  | h :: t => if leb_bid b h then min_bid' t b else min_bid' t h
  end.

Definition max_bid (l : list block_id) :=
  max_bid' l (hd (Anon 0) l).

Definition min_bid (l : list block_id) :=
  min_bid' l (hd (Anon 0) l).

Lemma leb_bid_refl : forall a, leb_bid a a = true.
Admitted.


Lemma max_bid_spec : forall l,
    (length l >= 1)%nat ->
    Forall (fun b => le_bid b (max_bid l)) l.
Proof.
  induction l ; try (now simpl).
  intros.
  apply Forall_cons.
  unfold le_bid.
  unfold max_bid ; simpl.
  rewrite leb_bid_refl.
Admitted.

Lemma min_bid_spec : forall l,
    (length l >= 1)%nat ->
        Forall (fun b => le_bid (min_bid l) b) l.
Admitted.

Definition max_label (dg : dcfg) (max : block_id) :=
  max_bid (inputs (graph dg) ++ outputs (graph dg)) = max.

Definition min_label (dg : dcfg) (min : block_id) :=
  min_bid (inputs (graph dg) ++ outputs (graph dg)) = min.

Definition interval_label (dg : dcfg) (min max : block_id) :=
  max_label dg max /\ min_label dg min.

Lemma inv_counter_bid :
  forall σ σ' (cb cb' : nat) (cr cr' : int) (c : cfg_lang) (dg : dcfg) min max,
    σ = {| counter_bid := cb; counter_reg := cr |} ->
    σ' = {| counter_bid := cb'; counter_reg := cr' |} ->
    interval_label dg min max ->
    (evaluate c) σ = (σ', dg) ->
    le_bid (name cb') max.
Proof.
  induction c ; intros ; subst ; simpl in *.
  - unfold mk_block in *.
    unfold freshLabel, interval_label in *.
    simpl in * ; repeat flatten_all ; simpl in *.
    inv H2.
    unfold cfg_block in H1.
    unfold max_label, min_label in H1.
    cbn in *.
    rewrite Z.leb_refl in *.
    match goal with
    | h:context[ ?x <=? ?y ] |- _ =>
        let H := fresh "H" in
        assert (H : x <=? y = true) by admit
        ; rewrite H in * ; clear H
    end.
    destruct H1 ; subst.
    unfold le_bid.
    admit. (* obviously true *)
Admitted.

Lemma inv_min_label :
  forall σ σ' (cb cb' : nat) (cr cr' : int) (c : cfg_lang) (dg : dcfg) min max,
    σ = {| counter_bid := cb; counter_reg := cr |} ->
    σ' = {| counter_bid := cb'; counter_reg := cr' |} ->
    interval_label dg min max ->
    (evaluate c) σ = (σ', dg) ->
    min = name cb.
Proof.
  induction c ; intros ; subst ; simpl in *.
  - unfold mk_block in *.
    unfold freshLabel, interval_label in *.
    simpl in * ; repeat flatten_all ; simpl in *.
    inv H2.
    unfold cfg_block in H1.
    unfold max_label, min_label in H1.
    cbn in *.
    rewrite Z.leb_refl in *.
    match goal with
    | h:context[ ?x <=? ?y ] |- _ =>
        let H := fresh "H" in
        assert (H : x <=? y = true) by admit
        ; rewrite H in * ; clear H
    end.
    intuition.
  - unfold mk_seq in H2
    ; repeat flatten_all ; simpl in *.
    inv H2.
    (* eapply IHc1; try reflexivity ; try eassumption. *)
    unfold cfg_seq in *.
Admitted.

 Theorem inv_interval_name :
  forall (σ1 σ2 σ3: FST) (c1 c2 : cfg_lang) (dg1 dg2 : dcfg) min1 max1 min2 max2,
    (evaluate c1) σ1 = (σ2, dg1) ->
    (evaluate c2) σ2 = (σ3, dg2) ->
    interval_label dg1 min1 max1 ->
    interval_label dg2 min2 max2 ->
    le_bid max1 min2.
Proof.
  induction c1 ; intros.
  - (* CBlock, CBlock *)
    simpl in *.
    unfold mk_block in *.
    unfold freshLabel in *.
    simpl in *. repeat flatten_all ; cbn in *.
    inv H. inv H0. (* inv Heq3. *) inv Heq. inv Heq0. (* inv Heq4. *)
    unfold interval_label, max_label, min_label in H1.
    unfold cfg_block in *.
    simpl in *.
    unfold outputs in H1.
    simpl in *.
    unfold successors in H1.
    simpl in *.
    unfold max_bid, min_bid in *.
    simpl in *.
    rewrite Z.leb_refl in *.
    match goal with
    | h:context[ ?x <=? ?y ] |- _ =>
        let H := fresh "H" in
        assert (H : x <=? y = true) by admit
        ; rewrite H in * ; clear H
    end.
    intuition ; subst.
    eapply inv_counter_bid.
Admitted.

Lemma inv_interval_independant :
  forall dg1 dg2 min1 max1 min2 max2,
    interval_label dg1 min1 max1 ->
    interval_label dg2 min2 max2 ->
    le_bid max1 min2 ->
    independent_flows_dcfg dg1 dg2 /\ (outs dg1) ⊍ (outs dg2).
Proof.
  intros.
  unfold independent_flows_dcfg, independent_flows,
    interval_label, max_label, min_label in *.
  destruct dg1, dg2.
  simpl in *.
  unfold no_reentrance, no_duplicate_bid.
  assert ((length (inputs graph0 ++ outputs graph0) >= 1)%nat) by admit. (* true using the invariant*)
  assert ((length (inputs graph1 ++ outputs graph1) >= 1)%nat) by admit. (* true using the invariant*)
  apply max_bid_spec in H3.
  apply min_bid_spec in H2.
  destruct H, H0.
  rewrite H4, H0 in *.
  rewrite Forall_app in H2,H3.
  intuition.
Admitted.


Theorem inv_independent_flows :
  forall (σ1 σ2 σ3: FST) (c1 c2 : cfg_lang) (dg1 dg2 : dcfg),
    (evaluate c1) σ1 = (σ2, dg1) ->
    (evaluate c2) σ2 = (σ3, dg2) ->
    independent_flows_dcfg dg1 dg2.
Proof.
  intros.
  pose proof (inv_interval_independant dg1 dg2).
  unfold independent_flows_dcfg, independent_flows in *.
  pose proof (inv_interval_name σ1 σ2 σ3 c1 c2 dg1 dg2).
  eapply H1 in H2
  ; try intuition.
  all : eexists.
  all : eexists.
Qed.

Theorem inv_disjoint_outputs :
  forall (σ1 σ2 σ3: FST) (c1 c2 : cfg_lang) (dg1 dg2 : dcfg),
    (evaluate c1) σ1 = (σ2, dg1) ->
    (evaluate c2) σ2 = (σ3, dg2) ->
    (outs dg1) ⊍ (outs dg2).
Proof.
  intros.
  pose proof (inv_interval_independant dg1 dg2).
  unfold independent_flows_dcfg, independent_flows in *.
  pose proof (inv_interval_name σ1 σ2 σ3 c1 c2 dg1 dg2).
  eapply H1 in H2
  ; try intuition.
  all : eexists.
  all : eexists.
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
    apply list_norepet_append.
    (* lemma with remove, but easy *)
    admit.
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
    (* apply IHc1 in Heq ; simpl in Heq. *)
    (* apply IHc2 in Heq0 ; simpl in Heq0. *)
    break_list_goal
    ; rewrite !Forall_app
    ; intuition
    ; cbn.
    eapply incl_Forall.
    (* In out1 (outs _) => incl [out1] (outs _)*)
    (* NOTE easy but tedious *)
    admit.
    admit.
  - simpl in *.
    unfold cfg_seq ; simpl.
    repeat intro_snd_evaluate.
    break_list_goal
    ; rewrite !Forall_app
    ; intuition
    ; cbn.
    eapply incl_Forall.
    (* NOTE easy but tedious *)
    admit.
    admit.
Admitted.

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
    apply remove_disjoint_remove.
    (* easy but tedious *)
    admit.
    (* freshness of (name counter_bid0)*)
    admit.
  - unfold cfg_join.
    break_list_goal.
    simpl in *.
    admit. (* NOTE easy but tedious + freshness counter_bid0 *)
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
  - admit. (* NOTE easy but tedious *)
  - admit. (* NOTE easy but tedious *)
Admitted.

Lemma wf_mk_branch : forall σ cond gT gF inT inF,
    independent_flows_dcfg gT gF ->
    (outs gT) ⊍ (outs gF) ->
    wf_dcfg gT ->
    wf_dcfg gF ->
    wf_dcfg (snd ((mk_branch cond gT gF inT inF) σ)).
Proof.
  intros *  INDEPENDENT_FLOWS DISJOINT_OUTS WF_GT WF_GF.
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
    (* freshness (name counter_bid0) *)
    admit.
  - admit.
  - admit.
Admitted.

Lemma wf_mk_while : forall σ expr_code cond gB inB outB,
    List.In outB (outs gB) ->
    wf_dcfg gB ->
    wf_dcfg (snd ((mk_while expr_code cond gB inB outB) σ)).
Proof.
  intros * OUTPUT WF_G.
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
    admit. (* easy but tedious *)
    apply list_disjoint_singleton_left.
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
    (* NOTE: freshness (name counter_bid0) *)
    admit.
  - admit.
  - admit.
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
    + eapply inv_independent_flows ; eassumption.
    + eapply inv_disjoint_outputs ; eassumption.
    + eapply IHc1. now erewrite Heq.
    + eapply IHc2. now erewrite Heq0.
  - repeat flatten_all.
    rewrite <- H.
    apply wf_mk_join.
    + admit. (* we have no_rep_outs thanks to WF + (hd l) and (hd (tl l))*)
    + apply hd_In.
      apply (inv_len_outputs σ c d). now rewrite Heq.
    + admit. (* TODO we need WF on cfg_lang st JOIN can only take cfg_lang with at least 2 outputs *)
    + eapply IHc. now erewrite Heq.
  - repeat flatten_all.
    rewrite <- H.
    apply wf_mk_while.
    + apply hd_In.
      apply (inv_len_outputs σ c d). now rewrite Heq.
    + eapply IHc. now erewrite Heq.
Admitted.



Definition denote_dcfg (dg : dcfg) := denote_cfg (graph dg).
Definition denote_cfg_lang (g : cfg_lang) (σ : FST) := denote_dcfg (snd ((evaluate g) σ)).
