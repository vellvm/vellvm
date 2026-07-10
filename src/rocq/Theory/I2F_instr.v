From Equations Require Import Equations.

From Stdlib Require Import Lia.

From ExtLib Require Import Structures.Monads.

From ITree Require Import ITree Eq HeterogeneousRelations.

From Vellvm Require Import
  Utils
  Syntax
  VellvmIntegers
  Integers
  DynamicValues
  EOU
  LLVMEvents
  Semantics.Operations
  Interfaces.IPtr
  Interfaces.Params
  Implementations.Address
  Implementations.Provenance
  Implementations.IPtrInfinite
  Implementations.IPtrFinite
  Implementations.Memory
  Implementations.ParamsV
  Denotation.

From Vellvm Require Import
  Theory.rutt_cutoff
  Theory.I2F.

From Paco Require Import paco.
  Ltac rstep :=
    first [apply ruttc_trigger |
            apply ruttc_trigger_cast |
            apply ruttc_ret 
      ].

Tactic Notation "rbind" uconstr(x) := eapply ruttc_bind with (RR := x).
Tactic Notation "erbind" := eapply ruttc_bind.

From Stdlib Require Import
  Program Setoid Morphisms List.

#[global]Instance ruttc_eq_itree {E1 E2 R1 R2 Rcutr Rcutl REv RAns RR} :
  Proper (eq_itree Logic.eq ==> eq_itree Logic.eq ==> flip impl) (@ruttc E1 E2 R1 R2 Rcutr Rcutl REv RAns RR).
Proof.
  intros ?? EQ1 ?? EQ2; rewrite EQ1,EQ2; intuition.
Qed.

Ltac cbnn := cbn; unfold resum, ReSum_id, id_, Id_IFun.
Ltac bind_exp := erbind; [apply I2F_denote_exp'| intros].

(* Can we avoid these duplications? *)
Lemma I2F_freeze' a b :
  I2F_dvalue a b ->
  I2F_refine_CFG I2F_dvalue (freeze a) (freeze b).
Proof with try now (rstep; cbnn; try (easy); eauto).
  (* automation is different in this file from the expression one, to understand *)
  intros HDV.
  induction HDV; cbn...
  all: try (rstep; now constructor).
  all: eapply ruttc_bind; [apply ruttc_map_monad_gen; eauto |]; intros...
  all: try (rstep; now constructor).
 Qed. 
  
Lemma I2F_refine_lift' {R1 R2} (RR : R1 -> R2 -> Prop) (m1 : EOU R1) (m2 : EOU R2) :
  I2F_EOU RR m1 m2 ->
  I2F_refine_CFG RR (EOU_to_itree m1) (EOU_to_itree m2).
Proof.
  intros []; cbn.
  - pfold; constructor; auto.
  - apply ruttc_trigger_cast; easy.
  - pfold; red; cbn.
    apply EqCutL; constructor.
  - pfold; red; cbn.
    apply EqCutR; constructor.
Qed.

Lemma I2F_denote_instr :
  forall i va1 va2,
    option_rel I2F_Addr va1 va2 ->
      I2F_refine_CFG TT
        (@denote_instr PInf i va1) (@denote_instr PFin i va2).
  Proof with try now (rstep; cbnn; try (easy); eauto).
    intros [[x i] ?] ? ? HR.
    destruct i.
    - cbn; break_match...
    - cbn; break_match...
      subst.
      bind_exp.
      rbind TT...
      intros ???...
    - destruct x, fn.
      + cbn.
        rbind (Forall2 I2F_dvalue).
        { apply ruttc_map_monad.
          intros [] HIN.
          apply I2F_denote_exp'.
        }
        break_match...
        * intros.
          rewrite 2 Eqit.bind_bind.
          rbind (sum_rel I2F_dvalue I2F_dvalue)...
          intros * HR'.
          inv HR'.
          rbind (fun _ _ => False)...
          intros ?? [].
          rewrite 2 Eqit.bind_ret_l...
        * intros.
          rewrite 2 Eqit.bind_bind.
          bind_exp.
          rewrite 2 Eqit.bind_bind.
          rbind (sum_rel I2F_dvalue I2F_dvalue)...
          intros * HR'.
          inv HR'.
          rbind (fun _ _ => False)...
          intros ?? [].
          rewrite 2 Eqit.bind_ret_l...
      + cbn.
        rbind (Forall2 I2F_dvalue).
        { apply ruttc_map_monad.
          intros [] HIN.
          apply I2F_denote_exp'.
        }
        intros.
        break_match...
        * intros.
          rewrite 2 Eqit.bind_bind.
          rbind (sum_rel I2F_dvalue I2F_dvalue)...
          intros * HR'.
          inv HR'.
          rbind (fun _ _ => False)...
          intros ?? [].
          rewrite 2 Eqit.bind_ret_l...
        * intros.
          rewrite 2 Eqit.bind_bind.
          bind_exp.
          rewrite 2 Eqit.bind_bind.
          rbind (sum_rel I2F_dvalue I2F_dvalue)...
          intros * HR'.
          inv HR'.
          rbind (fun _ _ => False)...
          intros ?? [].
          rewrite 2 Eqit.bind_ret_l...
        
    - destruct x; cbn[denote_instr].
      2: rstep; constructor.
      break_match_goal.
      + break_goal_fast.
        cbn; rewrite 2 Eqit.bind_bind.
        bind_exp.
        rewrite ?Eqit.bind_bind.
        rbind I2F_dvalue; [rstep; [cbnn; constructor; intuition | cbnn; intros; simp I2FA_Memory in *; eauto] |].
        pose proof I2F_dvalue_int_unsigned H as EQ; rewrite EQ; reflexivity.
        intros.
        rbind (fun _ _ => True); [rstep; cbnn; easy | intros]...
      + cbn; rewrite 2 Eqit.bind_bind.
        rbind I2F_dvalue; [rstep; [cbnn; constructor; intuition | cbnn; intros; simp I2FA_Memory in *; eauto] |].
        intros.
        rbind (fun _ _ => True); [rstep; cbnn; easy | intros]...
        
    - destruct x; cbn...
      destruct ptr.
      bind_exp.
      erbind; [rstep; [cbnn; easy | cbnn; intros; simp I2FA_Memory in *; eauto] |].
      intros.
      erbind; [apply I2F_freeze'; auto | intros]...
    - destruct val,ptr, x; cbn...
      bind_exp.
      bind_exp.
      induction H0...
      6: rbind (fun _ _ => False); [|intros _ _ []]...
      all: rbind (fun _ _ => True); [rstep; cbnn; [constructor; intuition; constructor; auto| cbn; auto] | intros [] [] _ ]; cbn...
    - destruct x; cbn...
    - destruct x; cbn...
      unfold denote_cmpxchg.
      do 3 break_goal_fast.
      break_match_goal...
      do 3 bind_exp.
      erbind; [rstep; [cbnn; easy | cbnn; intros; simp I2FA_Memory in *; eauto] |].
      intros.
      erbind.
      apply I2F_refine_lift', I2F_eval_icmp; eauto.
      intros.
      induction H3...
      break_goal_fast...
      break_goal_fast...
      rbind (fun _ _ => True); [rstep; [cbnn; easy | cbnn; intros; simp I2FA_Memory in *; eauto] |].
      intros.
      rstep; [cbnn; simp I2FE_Local; intuition | eauto].
      repeat constructor; auto.
      rstep; [cbnn; simp I2FE_Local; intuition | eauto].
      repeat constructor; auto.
    - destruct x; cbn...
      unfold denote_atomicrmw.
      repeat break_goal_fast.
      bind_exp.
      bind_exp.
      erbind; [rstep; [cbnn; easy | cbnn; intros; simp I2FA_Memory in *; eauto] | intros].
      unfold denote_atomic_rmw_operation.
      break_goal_fast...
      
      cbn; erewrite 2 Eqit.bind_ret_l;
      rbind (fun _ _ => True); [rstep; cbnn; easy | intros];
        rbind (fun _ _ => True); [rstep; cbnn; easy | intros]...

      all: try (cbn; erbind; [apply I2F_refine_lift', I2F_eval_iop; eauto | intros];
      rbind (fun _ _ => True); [rstep; cbnn; easy | intros];
        rbind (fun _ _ => True); [rstep; cbnn; easy | intros])...

      2-5: rbind (fun _ _ => False); [|intros _ _ []]...
      4-11: rbind (fun _ _ => False); [|intros _ _ []]...
      { cbn; inversion H0...
        1,3-11: rbind (fun _ _ => False); [|intros _ _ []]...
        rbind I2F_dvalue.
        2: intros;
        rbind (fun _ _ => True); [rstep; cbnn; easy | intros];
        rbind (fun _ _ => True); [rstep; cbnn; easy | intros]...
        apply I2F_refine_lift'.
        pose proof @I2F_eval_iop _ (DVALUE_I sz i) _ (DVALUE_I sz i) And H1.
        forward H4; [constructor |].
        inv H4; repeat constructor.
        induction H7; repeat constructor.
        break_goal_fast; repeat constructor.
        subst; cbn; repeat constructor.
      }
      all: erbind; [apply I2F_refine_lift', I2F_eval_fop; eauto | intros].
      all: rbind (fun _ _ => True); [rstep; cbnn; easy | intros].
      all: rbind (fun _ _ => True); [rstep; cbnn; easy | intros]...
    - destruct x, va_list_and_arg_list; cbn.
      all: bind_exp.
      all: rbind I2F_dvalue; [rstep; [cbnn; easy | cbnn; intros; simp I2FA_Memory in *; eauto] | intros].
      all: rbind I2F_dvalue; [rstep; [cbnn; easy | cbnn; intros; simp I2FA_Memory in *; eauto] | intros].
      all: rewrite 2 Eqit.bind_ret_l.
      all: erbind; [apply I2F_refine_lift', I2F_eval_gep; eauto; repeat constructor | intros].
      all: rbind (fun _ _ => True); [rstep; cbnn; easy | intros]...
    - destruct x; cbn...
      rbind (option_rel I2F_dvalue); [|intros].
      rstep; cbnn; [easy | intros; simp I2FA_Stack in *].
      induction H...
Qed.

Lemma I2F_denote_code :
  forall c va1 va2,
    option_rel I2F_Addr va1 va2 ->
    I2F_refine_CFG TT (@denote_code PInf c va1) (@denote_code PFin c va2).
Proof.
  intros.
  unfold denote_code, map_monad_.
  rbind TT; [| intros; now rstep].
  induction c; cbn.
  - now rstep.
  - rbind TT; [apply I2F_denote_instr; auto | intros [] [] _].
    rbind TT.
    apply IHc.
    intros; now rstep.
Qed.

Hint Constructors I2F_dvalue : core.
Hint Unfold TT : core.

Lemma I2F_dvalue_is_poison : forall v1 v2,
    I2F_dvalue v1 v2 ->
    @dvalue_is_poison PInf v1 = @dvalue_is_poison PFin v2.
Proof.
  intros * H; now destruct H.
Qed.

(** [select_switch] computes in the parameter-free [EOU block_id]: on
    related selectors and switch tables the two sides are literally
    equal (related [DVALUE_I]s carry equal payloads). *)
Lemma I2F_select_switch :
  forall v1 v2,
    I2F_dvalue v1 v2 ->
    forall sw1 sw2,
      Forall2 (prod_rel I2F_dvalue Logic.eq) sw1 sw2 ->
      forall db,
        @select_switch PInf v1 db sw1 = @select_switch PFin v2 db sw2.
Proof.
  intros v1 v2 HV sw1 sw2 F; induction F; intros db; cbn; [reflexivity |].
  destruct x as [xv xid], y as [yv yid].
  destruct H as [HXY EQ]; cbn in HXY, EQ; subst.
  inversion HV; subst; cbn; auto.
  all: inversion HXY; subst; cbn; auto.
  destruct (Pos.eq_dec _ _); [| reflexivity].
  destruct e; cbv [eq_rec_r eq_rec eq_rect Logic.eq_sym].
  break_match_goal; auto.
Qed.

Lemma I2F_denote_terminator :
  forall t,
    I2F_refine_CFG (sum_rel Logic.eq I2F_dvalue) (@denote_terminator PInf t) (@denote_terminator PFin t).
Proof with try now (rstep; cbnn; try (easy); eauto).
  destruct t as [[? []] ?]; cbn...
  - destruct v; bind_exp...
  - destruct v; bind_exp.
    induction H...
    repeat break_goal_fast...
  - destruct v; bind_exp.
    rewrite (I2F_dvalue_is_poison H).
    break_match_goal...
    rbind (Forall2 (prod_rel I2F_dvalue (@Logic.eq block_id))).
    { apply ruttc_map_monad.
      intros [[sz x] id] _; cbn.
      rbind I2F_dvalue.
      { first [ apply I2F_refine_lift'; now repeat constructor
              | rstep; now repeat constructor ]. }
      intros; rstep; now repeat constructor. }
    intros sw1 sw2 HSW.
    rbind (@Logic.eq block_id).
    { apply I2F_refine_lift'.
      erewrite I2F_select_switch; eauto.
      apply I2F_EOU_refl. }
    intros ?? <-...
  - destruct v.
    bind_exp...
  - destruct fnptrval.
    erbind.
    apply ruttc_map_monad.
    intros [] ?; apply I2F_denote_exp'.
    intros.
    bind_exp.
    rbind (sum_rel I2F_dvalue I2F_dvalue)...
    intros * HR.
    induction HR.
    rbind TT...
    intros...
    break_goal_fast...
    rbind TT...
    intros...
    rewrite !Eqit.bind_ret_l...
Qed.

Lemma I2F_denote_phi :
  forall from phi,
    I2F_refine_CFG (prod_rel Logic.eq I2F_dvalue) (@denote_phi PInf from phi) (@denote_phi PFin from phi).
Proof with try now (rstep; cbnn; try (easy); eauto).
  intros ? [[? []] ?]; cbn.
  break_goal_fast...
  bind_exp...
Qed.

Lemma I2F_denote_phis :
  forall from phis,
    I2F_refine_CFG TT (@denote_phis PInf from phis) (@denote_phis PFin from phis).
Proof with try now (rstep; cbnn; try (easy); eauto).
  intros; cbn.
  erbind.
  apply ruttc_map_monad.
  intros; apply I2F_denote_phi.
  intros.
  erbind.
  unshelve apply ruttc_map_monad_gen.
  exact TT.
  2: intros...
  induction H; cbn; auto.
  constructor; auto.
  destruct H,x,y; cbn in *; subst...
Qed.

Lemma I2F_denote_block :
  forall from block a1 a2,
    option_rel I2F_Addr a1 a2 ->
    I2F_refine_CFG (sum_rel Logic.eq I2F_dvalue) (@denote_block PInf block from a1) (@denote_block PFin block from a2).
Proof with try now (rstep; cbnn; try (easy); eauto).
  intros.
  erbind;[apply I2F_denote_phis| intros ???].
  erbind;[apply I2F_denote_code; auto| intros ???].
  apply I2F_denote_terminator.
Qed.

Lemma I2F_denote_ocfg :
  forall ocfg ft a1 a2,
    option_rel I2F_Addr a1 a2 ->
    I2F_refine_CFG (sum_rel Logic.eq I2F_dvalue) (@denote_ocfg PInf ocfg a1 ft) (@denote_ocfg PFin ocfg a2 ft).
Proof with try now (rstep; cbnn; try (easy); eauto).
  intros.
  apply ruttc_iter with Logic.eq; auto.
  intros [] ? <-.
  break_goal_fast...
  erbind; [apply I2F_denote_block; auto |].
  intros ?? HR; inv HR...
Qed.

Lemma I2F_denote_cfg :
  forall ocfg a1 a2,
    option_rel I2F_Addr a1 a2 ->
    I2F_refine_CFG I2F_dvalue (@denote_cfg PInf ocfg a1) (@denote_cfg PFin ocfg a2).
Proof with try now (rstep; cbnn; try (easy); eauto).
  intros.
  cbn.
  erbind; [apply I2F_denote_ocfg; auto |].
  intros ?? HR; inv HR...
Qed.


