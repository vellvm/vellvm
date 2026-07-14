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
  Implementations.Pointer
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
  intros ?? EQ1 ?? EQ2; rewrite EQ1,EQ2; intuition eauto with *.
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
  induction H; cbn...
  all: try rstep; cbnn; repeat constructor; auto.
  all: eapply ruttc_bind; [apply ruttc_map_monad_gen; eauto |]; intros...
  all: try (rstep; repeat constructor); auto.
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
        rbind I2F_dvalue_base; [apply I2F_refine_lift', I2F_dvalue_to_dvalue_base; auto |].
        intros.
        rewrite 2 Eqit.bind_bind.
        pose proof I2F_dvalue_base_int_unsigned H0 as EQ; rewrite EQ.
        rbind I2F_dvalue; [rstep; cbnn; easy | intros]...
        rbind (fun _ _ => True); [rstep; cbnn; repeat constructor; auto | intros]...
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
      induction H0...
      6: rbind (fun _ _ => False); [|intros _ _ []]...
      all: rbind (fun _ _ => True); [rstep; cbnn; [constructor; intuition; repeat constructor; auto| cbn; auto] | intros [] [] _ ]; cbn...
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
      { cbn; inv H0; [inv H2 | |]...
        1,3-10: rbind (fun _ _ => False); [|intros _ _ []]...
        rbind I2F_dvalue.
        2: intros;
        rbind (fun _ _ => True); [rstep; cbnn; easy | intros];
        rbind (fun _ _ => True); [rstep; cbnn; easy | intros]...
        apply I2F_refine_lift'.
        pose proof @I2F_eval_iop _ (DVALUE_I sz i) _ (DVALUE_I sz i) And H1.
        forward H0; [repeat constructor |].
        inv H0; [inv H4 |..]; repeat constructor.
        induction H0; repeat constructor.
        destruct (Pos.eq_dec sz sz0); repeat constructor.
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
  intros * H; destruct H; [destruct H |..]; auto.
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
  all: inv H0; cbn; auto.
  all: inv H; cbn; auto.
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
  - rstep; repeat constructor.
  - destruct v; bind_exp.
    inv H; [induction H0 | |]...
    repeat break_goal_fast...
  - destruct v; bind_exp.
    rewrite (I2F_dvalue_is_poison H).
    break_match_goal...
    rbind (Forall2 (prod_rel I2F_dvalue (@Logic.eq block_id))).
    { apply ruttc_map_monad.
      intros [[sz x] id] _; cbn.
      rbind I2F_dvalue_base.
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

Definition I2F_function_denotation
  (ctx1 : @function_denotation PInf)
  (ctx2 : @function_denotation PFin) : Prop :=
  forall args1 args2,
    Forall2 I2F_dvalue args1 args2 ->
    I2F_refine_CFG (sum_rel I2F_dvalue I2F_dvalue) (ctx1 args1) (ctx2 args2).

Lemma I2F_combine_lists_varargs : 
  forall (d : definition dtyp (cfg dtyp)) y1 y2,
    Forall2 I2F_dvalue y1 y2 -> 
    I2F_EOU 
      (prod_rel (Forall2 (prod_rel Logic.eq I2F_dvalue)) (Forall2 I2F_dvalue))
      (combine_lists_varargs (df_args d) y1)
      (combine_lists_varargs (df_args d) y2).
Proof with cbn; eauto using I2F_EOU_error, I2F_EOU_ret, I2F_EOU_oom, I2F_EOU_ub.
  intros d.
  generalize (df_args d) as l.
  induction l as [| x l IH]; intros * HR.
  - dependent induction HR...
    apply I2F_EOU_ret; constructor...
  - dependent induction HR...
    apply IH in HR.
    induction HR...
    destruct a1,a2; constructor.
    inv H0.
    constructor; cbn...
Qed.

(** [dtyp_of_dvalue] computes in the parameter-free [EOU dtyp]: on
    related values the two sides are literally equal (related scalars
    carry equal payloads, and aggregates share their annotations). *)
Lemma I2F_dtyp_of_dvalue_eq :
  forall v v',
    I2F_dvalue v v' ->
    @dtyp_of_dvalue PInf v = @dtyp_of_dvalue PFin v'.
Proof.
  induction v using dvalue_ind; intros v' R; inversion R; subst;
    repeat match goal with
      | H : existT _ _ _ = existT _ _ _ |- _ =>
          apply Eqdep_dec.inj_pair2_eq_dec in H; [| apply Pos.eq_dec]; subst
      end;
    clear R; cbn; auto.
  - inv H0; reflexivity.
  - (* Struct *)
    match goal with
    | F2 : Forall2 I2F_dvalue fields ?l2 |- context [?L fields] =>
        match goal with
        | |- context [?R l2] =>
            assert (GO : L fields = R l2); [| rewrite GO; reflexivity]
        end
    end.
    match goal with
    | F2 : Forall2 I2F_dvalue fields _, IH : Forall _ fields |- _ =>
        revert IH; induction F2 as [| u u' us us' HU HUS IHUS]
    end; intros FIH; cbn; auto.
    inversion FIH; subst.
    match goal with
    | HP : forall _, I2F_dvalue u _ -> _ |- _ => rewrite (HP _ HU)
    end.
    rewrite IHUS by assumption; reflexivity.
  - (* Array *)
    break_match_goal; cbn; auto.
    match goal with
    | F2 : Forall2 I2F_dvalue elts ?l2 |- context [forallb ?f elts] =>
        match goal with
        | |- context [forallb ?g l2] =>
            assert (FB : forallb f elts = forallb g l2);
            [| assert (LEN : length elts = length l2)
                 by (eapply Forall2_length; eauto);
               rewrite FB, LEN; reflexivity ]
        end
    end.
    match goal with
    | F2 : Forall2 I2F_dvalue elts _, IH : Forall _ elts |- _ =>
        revert IH; induction F2 as [| u u' us us' HU HUS IHUS]
    end; intros FIH; cbn; auto.
    inversion FIH; subst.
    match goal with
    | HP : forall _, I2F_dvalue u _ -> _ |- _ => rewrite (HP _ HU)
    end.
    rewrite IHUS by assumption; reflexivity.
Qed.

Lemma I2F_dtyp_of_dvalue :
  forall a1 a2 : dvalue,
    I2F_dvalue a1 a2 ->
    I2F_EOU Logic.eq (dtyp_of_dvalue a1) (dtyp_of_dvalue a2).
Proof.
  intros * H; erewrite I2F_dtyp_of_dvalue_eq; eauto.
  apply I2F_EOU_refl.
Qed.
  
Lemma I2F_push_call_frame d args1 args2:
    Forall2 I2F_dvalue args1 args2 ->
    I2F_refine_CFG I2F_Addr (push_call_frame d args1) (push_call_frame d args2).
Proof with try now (rstep; cbnn; try (easy); eauto).
  intros.
  erbind; [apply I2F_refine_lift', I2F_combine_lists_varargs; auto | intros].
  destruct r1, r2; inv H0; cbn in * |-.
  erbind; [eapply I2F_refine_lift', I2F_EOU_map_monad2 with (RB := Logic.eq); eauto | intros ?? HEQ; apply Forall2_eq in HEQ; subst].
  apply I2F_dtyp_of_dvalue.
  rbind TT...
  intros _ _ _.
  rbind TT...
  intros _ _ _.
  rbind I2F_dvalue...
  intros ?? HR.
  rbind TT.
  rstep; cbnn; try easy.
  constructor; intuition.
  intros _ _ _.
  induction HR; [induction H0 | |]...
Qed.

Lemma unfold_run_exc_strong `{Params.Params} {A} (t : itree _ A) :
  run_exc t ≅ match observe t with
         | RetF a  => Ret (inr a)
         | TauF u' => Tau (run_exc u')
         | VisF X e k =>
             match exc_of_event e with
             | Some x => Ret (inl x)
             | None   => Vis e (fun x => Tau (run_exc (k x)))
             end
    end.
Proof.
  unfold run_exc.
  rewrite unfold_iter.
  desobs t ot; cbn; auto.
  rewrite Eqit.bind_ret_l; reflexivity.
  rewrite Eqit.bind_ret_l; reflexivity.
  break_goal_fast; rewrite ?Eqit.bind_ret_l; [reflexivity |].
  rewrite bind_vis. apply eqit_Vis.
  intros.
  rewrite Eqit.bind_ret_l; reflexivity.
Qed.

Lemma unfold_run_exc `{Params.Params} {A} (t : itree _ A) :
  run_exc t ≳ match observe t with
         | RetF a  => Ret (inr a)
         | TauF u' => run_exc u'
         | VisF X e k =>
             match exc_of_event e with
             | Some x => Ret (inl x)
             | None   => Vis e (fun x => run_exc (k x))
             end
    end.
Proof.
  unfold run_exc.
  rewrite unfold_iter.
  desobs t ot; cbn; auto.
  rewrite Eqit.bind_ret_l; reflexivity.
  rewrite Eqit.bind_ret_l, tau_euttge; reflexivity.
  break_goal_fast; rewrite ?Eqit.bind_ret_l; [reflexivity |].
  rewrite bind_vis. apply eqit_Vis.
  intros.
  rewrite Eqit.bind_ret_l, tau_euttge; reflexivity.
Qed.

Lemma cutUB_exc_of_event `{Params.Params} {X} (e : _ X) :
  cutUB e ->
  exc_of_event e = None.
Proof.
  intros CUT.
  induction CUT; reflexivity.
Qed.

Lemma cutOOM_exc_of_event `{Params.Params} {X} (e : _ X) :
  cutOOM e ->
  exc_of_event e = None.
Proof.
  intros CUT.
  induction CUT; reflexivity.
Qed.

(** Related events have related exception projections: the [LLVMExcE]
    payloads are related by [I2FE_Exc], and every other component
    projects to [None] on both sides (mismatched injections are ruled
    out by the computing [sum_prerel]). *)
Lemma I2FE_CFG_exc_of_event {A B} (e1 : @CFGEtop PInf A) (e2 : @CFGEtop PFin B) :
  I2FE_CFG e1 e2 ->
  option_rel I2F_dvalue (exc_of_event e1) (exc_of_event e2).
Proof.
  intros HE.
  repeat (destruct e1 as [e1|e1]); repeat (destruct e2 as [e2|e2]);
    cbn in *; try easy; try (now constructor).
  destruct e1, e2; simp I2FE_Exc in HE; constructor; auto.
Qed.

Lemma I2F_run_exc {R1 R2 : Type} {RR : R1 -> R2 -> Prop} t1 t2 :
  ruttc cutUB cutOOM I2FE_CFG I2FA_CFG RR t1 t2 ->
  ruttc cutUB cutOOM I2FE_CFG I2FA_CFG (sum_rel I2F_dvalue RR) (run_exc t1) (run_exc t2).
Proof.
  revert t1 t2.
  ginit; gcofix cih.
  intros * HR.
  rewrite 2 unfold_run_exc_strong.
  punfold HR; red in HR.
  induction HR; pclearbot.
  - gstep; constructor; eauto.
  - gstep. constructor; eauto.
    gfinal; left; apply cih; auto.
  - pose proof (I2FE_CFG_exc_of_event _ _ H) as EXC.
    destruct (exc_of_event e1), (exc_of_event e2); inv EXC.
    + gstep; constructor; constructor; auto.
    + gstep; constructor; auto.
      intros a b HAns.
      gstep; constructor.
      gfinal; left; apply cih.
      now apply H0.
  - rewrite tau_euttge, unfold_run_exc_strong.
    apply IHHR.
  - rewrite tau_euttge, unfold_run_exc_strong.
    apply IHHR.
  - rewrite cutUB_exc_of_event; auto.
    gstep; constructor; auto.
  - rewrite cutOOM_exc_of_event; auto.
    gstep; constructor; auto.
Qed.

Lemma I2F_denote_function d :
    I2F_function_denotation (@denote_function PInf d) (@denote_function PFin d).
Proof with try now (rstep; cbnn; try (easy); eauto).
  unfold denote_function.
  intros ???.
  rbind I2F_Addr; [apply I2F_push_call_frame; auto | intros].
  erbind...
  eapply I2F_run_exc, I2F_denote_cfg; constructor; auto.
  intros.
  unfold pop_call_frame; cbn; rewrite 2 Eqit.bind_bind.
  rbind TT...
  intros ???.
  rbind TT...
  intros ???...
Qed.

(** Pointwise lifting of [I2F_function_denotation] to function contexts,
    extensionally over [lookup] (in the style of [IntMaps.Equiv]): the two
    maps have the same domain, and denotations found at a common key are
    related. [lookup_defn] keys the map by [ptr_to_int], which coincides
    on [I2F_Addr]-related addresses, so related lookups share their key. *)
Definition I2F_ctx
  (ctx1 : IntMap (@function_denotation PInf))
  (ctx2 : IntMap (@function_denotation PFin)) : Prop :=
  forall k, option_rel I2F_function_denotation (lookup k ctx1) (lookup k ctx2).

(** Related function values look up related denotations: [ptr_to_int]
    coincides on related addresses, and no other shape is a key. *)
Lemma I2F_lookup_defn f1 f2 ctx1 ctx2 :
  I2F_dvalue f1 f2 ->
  I2F_ctx ctx1 ctx2 ->
  option_rel I2F_function_denotation
    (lookup_defn f1 ctx1) (lookup_defn f2 ctx2).
Proof.
  intros HF HC; inv HF; [inv H | |]; cbn; try constructor.
  destruct p, p'; destruct H0 as [HI ->]; red in HI; subst.
  apply HC.
Qed.
    
Lemma I2F_denote_mcfg :
  forall t ctx1 ctx2 f1 f2 args1 args2,
    I2F_dvalue f1 f2 ->
    Forall2 I2F_dvalue args1 args2 ->
    I2F_ctx ctx1 ctx2 ->
    I2F_refine_MCFG
      (sum_rel I2F_dvalue I2F_dvalue)
      (@denote_mcfg PInf ctx1 t f1 args1)
      (@denote_mcfg PFin ctx2 t f2 args2).
Proof with try now (rstep; cbnn; try (easy); eauto).
  intros * HF Hargs Hctx.
  red; unfold denote_mcfg.
  (* [ruttc_mrec] concludes at the per-call answer relation
     [fun a b => I2FA_Call d1 a d2 b]; weaken it into [sum_rel] (they
     compute to each other), the other relations are untouched. *)
  eapply ruttc_weaken; cycle -1.
  { eapply ruttc_mrec with (RCall := I2FE_Call) (RCall' := I2FA_Call).
    2: { simp I2FE_Call; repeat split; auto. }
    (* the bodies: related calls dispatch through related contexts *)
    intros A B [dt fv1 fas1] [dt' fv2 fas2] HC.
    simp I2FE_Call in HC; destruct HC as (<- & HFv & HAs).
    (* transport the CFG-level relations to the structural ones
       demanded by [ruttc_mrec] *)
    eapply ruttc_weaken with (RR := sum_rel I2F_dvalue I2F_dvalue).
    { intros ? ? CUT; exact (proj1 (I2F_cutUB_CFG _) CUT). }
    { intros ? ? CUT; exact (proj1 (I2F_cutOOM_CFG _) CUT). }
    { intros * HE; exact (I2FE_CFG_sum _ _ HE). }
    { intros * HA; exact (I2FA_CFG_sum HA). }
    { intros ? ? HS; cbn; simp I2FA_Call; exact HS. }
    cbn.
    pose proof (I2F_lookup_defn HFv Hctx) as HL.
    destruct (lookup_defn fv1 ctx1) eqn:L1, (lookup_defn fv2 ctx2) eqn:L2;
      inv HL.
    - (* internal call: the related denotations found in the contexts *)
      match goal with
      | HFD : I2F_function_denotation _ _ |- _ => now apply HFD
      end.
    - (* external call *)
      unfold external_call.
      rbind I2F_dvalue.
      { rstep.
        - cbnn; simp I2FE_ExternalCall; intuition.
        - cbnn; intros; simp I2FA_ExternalCall in *; eauto. }
      intros...
  }
  (* the four identity inclusions, and [sum_rel] from the [I2FA_Call]
     instance (they are convertible) *)
  all: auto.
Qed.
