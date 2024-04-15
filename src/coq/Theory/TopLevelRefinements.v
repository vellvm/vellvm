(* begin hide *)
From ITree Require Import
  ITree
  ITreeFacts
  Basics.HeterogeneousRelations
  Events.State
  Events.StateFacts
  InterpFacts
  KTreeFacts
  Eq.Eqit.

From Vellvm Require Import
  Utilities
  Utils.VellvmRelations
  Syntax
  Semantics
  Theory.Refinement
  Theory.InterpreterMCFG
  Theory.InterpreterCFG
  Utils.InterpMemoryProp
  Utils.InterpPropOOM.

From ExtLib Require Import
  Structures.Functor.

From Coq Require Import
  RelationClasses
  Strings.String
  Logic
  Morphisms
  Relations
  List
  ZArith.

Require Import Paco.paco.

From Coq Require Import Program.Equality.

Import ListNotations.
Import ITree.Basics.Basics.Monads.

Module Type TopLevelRefinements (IS : InterpreterStack) (TOP : LLVMTopLevel IS).
  Export TOP.
  Export IS.
  Export IS.LLVM.
  Export IS.LLVM.MEM.CP.CONC.
  Export IS.LLVM.MEM.
  Import MEM.MEM_MODEL.
  Import MEM.MMEP.
  Import MEM.MMEP.MMSP.
  Import MEM.MEM_EXEC_INTERP.
  Import MEM.MEM_SPEC_INTERP.

  Import SemNotations.

  Module R := Refinement.Make LP LLVM.
  Export R.
  (* end hide *)

  (**
   This file is currently a holdall.
   In here, we have:
   * partial interpreters to each levels;
   * hierarchies of refinements of mcfgs and proofs of inclusions;
   * lemmas for each partial interpreter of commutation with bind and ret;
   * some misc proper instances;
   * admitted statement of inclusion of the intepreter into the model;
   **)

  (** The module _Refinement.Make_ defines a series of refinements between
    [itree]s at the various signatures of events a Vellvm goes through during
    the chain of interpretations leading to the definition of the model.
    These refinements state set inclusion of the concretization of the
    returned under-defined values, but impose no constraints on the states.

    In this module, we show that these refinements define a chain of growing
    relations when composed with the bits of interpretations relating each
    level.

    Finally, this allows us to lift these relations on [itree]s to a growing
    chain of relations on [mcfg typ].
   *)

  (** BEGIN TO MOVE *)
  Lemma subrelation_R_TT:
    forall A (R : relation A), subrelation R TT.
  Proof using. firstorder. Qed.

  Lemma subrelation_prod_left :
    forall A B (R R' : relation A) (R2 : relation B), subrelation R R' -> subrelation (R × R2) (R' × R2).
  Proof using.
    intros A B R R' R2 H.
    unfold subrelation in *.
    intros x y HRR2.
    inversion HRR2; firstorder.
  Qed.

  Lemma eutt_tt_to_eq_prod :
    forall X R (RR : relation R) E (t1 t2 : itree E (X * R)),
      eutt (eq × RR) t1 t2 -> eutt (TT × RR) t1 t2.
  Proof using.
    intros X R RR E t1 t2 Heutt.
    unfold eutt.
    apply (eqit_mon (eq × RR) (TT × RR) true true true true); trivial.
    intros x0 x1 PR.
    eapply subrelation_prod_left. apply subrelation_R_TT. all: apply PR.
  Qed.

  Import AlistNotations.
  Lemma alist_find_eq_dec_local_env :
    forall k (m1 m2 : local_env),
      {m2 @ k = m1 @ k} + {m2 @ k <> m1 @ k}.
  Proof using.
    intros; eapply alist_find_eq_dec.
  Qed.


  #[global] Instance interp_state_proper {T E F S}
   (h: forall T : Type, E T -> Monads.stateT S (itree F) T)
    : Proper (eutt Logic.eq ==> Monad.eq1) (State.interp_state h (T := T)).
  Proof using.
    einit. ecofix CIH. intros.

    rewrite !unfold_interp_state. punfold H0. red in H0.
    induction H0; intros; subst; simpl; pclearbot.
    - eret.
    - etau.
    - ebind. econstructor; [reflexivity|].
      intros; subst.
      etau. ebase.
    - rewrite tau_euttge, unfold_interp_state; eauto.
    - rewrite tau_euttge, unfold_interp_state; eauto.
  Qed.

  #[export] Hint Unfold TT : core.
  Instance TT_equiv :
    forall A, Equivalence (@TT A).
  Proof using.
    intros A; split; repeat intro; auto.
  Qed.

  (** END TO MOVE *)

  Section REFINEMENT.
    (** We first prove that the [itree] refinement at level [i] entails the
    refinement at level [i+1] after running the [i+1] level of interpretation
     *)

    (* Lemma 5.7
     See the related definition of [refine_L0] in Refinement.v. (Search for Lemma 5.7)

     The similar results mentioned in the paper are listed below.
     *)
    Lemma refine_01: forall t1 t2 g,
        refine_L0 t1 t2 -> refine_L1 (interp_global t1 g) (interp_global t2 g).
    Proof using.
      intros t1 t2 g REF.
      apply eutt_tt_to_eq_prod, eutt_interp_state; auto.
    Qed.

    Lemma refine_12 : forall t1 t2 l,
        refine_L1 t1 t2 -> refine_L2 (interp_local_stack t1 l) (interp_local_stack t2 l).
    Proof using.
      intros t1 t2 l REF.
      apply eutt_tt_to_eq_prod, eutt_interp_state; auto.
    Qed.

    Lemma refine_23 : forall t1 t2 sid m,
        refine_L2 t1 t2 -> refine_L3 (interp_memory_spec refine_res2 t1 sid m) (interp_memory_spec refine_res2 t2 sid m).
    Proof using.
      intros t1 t2 sid ms REF t Ht.
      exists t; split.
      - unfold L3 in *.
        unfold refine_L2 in *.
        eapply interp_memory_prop_Proper_eq in Ht; try typeclasses eauto; eauto.
        Unshelve.
      - reflexivity.
    Qed.

    (* Things are different for L4 and L5: we get into the [Prop] monad. *)
    Lemma refine_34 : forall t1 t2,
        refine_L3 t1 t2 -> refine_L4 (model_undef refine_res3 t1) (model_undef refine_res3 t2).
    Proof using.
      intros t1 t2 REF t Ht.
      exists t; split.
      - unfold model_undef in *.
        unfold refine_L3 in *.
        destruct Ht as [t_pre [T2 MODEL]].
        specialize (REF _ T2).
        destruct REF as [t_pre1 [T1 EUTT]].
        exists t_pre1; split; auto.
        eapply interp_prop_oom_Proper_eq in MODEL; try typeclasses eauto; eauto.
      - reflexivity.
    Qed.

    Lemma refine_45 : forall Pt1 Pt2,
        refine_L4 Pt1 Pt2 -> refine_L5 (model_UB Pt1) (model_UB Pt2).
    Proof using.
      intros Pt1 Pt2 HR t2 HM.
      destruct HM as [Pt2_t2 | [ub [Pt2_ub UB]]].
      - specialize (HR t2 Pt2_t2) as [t1 [Pt1_t1 EQ]].
        exists t1.
        split; auto.
        left; auto.
      - specialize (HR ub Pt2_ub) as [ub1 [Pt1_ub1 EQ]].
        exists t2.
        split; try reflexivity.
        right. exists ub1; split; auto.
        rewrite EQ; auto.
    Qed.

    Lemma refine_56 : forall Pt1 Pt2,
        refine_L5 Pt1 Pt2 -> refine_L6 Pt1 Pt2.
    Proof using.
      intros Pt1 Pt2 HR t2 HM.
      apply HR in HM as (t1 & HPt1 & HPT1);
        exists t1; split; auto;
        apply eutt_refine_oom_h; auto;
        typeclasses eauto.
    Qed.

    Hint Resolve refine_12 refine_23 refine_34 refine_45 refine_56 : refine_xx.

    Variable ret_typ : dtyp.
    Variable entry : string.
    Variable args : list uvalue.

    Definition denote_vellvm_init := denote_vellvm ret_typ entry args.

    (**
   In particular, we can therefore define top-level models
   short-circuiting the interpretation early.
     *)

    Definition model_to_L1  (prog: mcfg dtyp) :=
      let L0_trace := denote_vellvm_init prog in
      ℑs1 L0_trace [].

    Definition model_to_L2 (prog: mcfg dtyp) :=
      let L0_trace := denote_vellvm_init prog in
      ℑs2 L0_trace [] ([],[]).

    Definition model_to_L3 (prog: mcfg dtyp) :=
      let L0_trace := denote_vellvm_init prog in
      ℑs3 (refine_res2) L0_trace [] ([],[]) 0 initial_memory_state.

    Definition model_to_L4 (prog: mcfg dtyp) :=
      let L0_trace := denote_vellvm_init prog in
      ℑs4 (refine_res2) (refine_res3) L0_trace [] ([],[]) 0 initial_memory_state.

    Definition model_to_L5 (prog: mcfg dtyp) :=
      let L0_trace := denote_vellvm_init prog in
      ℑs5 (refine_res2) (refine_res3) L0_trace [] ([],[]) 0 initial_memory_state.

    (**
   Which leads to five notion of equivalence of [mcfg]s.
   Note that all reasoning is conducted after conversion to [mcfg] and
   normalization of types.
     *)
    Definition refine_mcfg_L1 (p1 p2: mcfg dtyp): Prop :=
      R.refine_L1 (model_to_L1 p1) (model_to_L1 p2).

    Definition refine_mcfg_L2 (p1 p2: mcfg dtyp): Prop :=
      R.refine_L2 (model_to_L2 p1) (model_to_L2 p2).

    Definition refine_mcfg_L3 (p1 p2: mcfg dtyp): Prop :=
      R.refine_L3 (model_to_L3 p1) (model_to_L3 p2).

    Definition refine_mcfg_L4 (p1 p2: mcfg dtyp): Prop :=
      R.refine_L4 (model_to_L4 p1) (model_to_L4 p2).

    Definition refine_mcfg_L5 (p1 p2: mcfg dtyp): Prop :=
      R.refine_L5 (model_to_L5 p1) (model_to_L5 p2).

    Definition refine_mcfg_L6 (p1 p2: mcfg dtyp): Prop :=
      R.refine_L6 (model_to_L5 p1) (model_to_L5 p2).

    Definition refine_mcfg  (p1 p2: mcfg dtyp): Prop :=
      refine_mcfg_L6 p1 p2.

    Hint Unfold refine_mcfg refine_mcfg_L1 refine_mcfg_L2
         refine_mcfg_L3 refine_mcfg_L4 refine_mcfg_L5
         refine_mcfg_L6 : refine_xx.

    (* Apparently auto's use of simple apply fails here *)
    Hint Extern 1 (refine_L4 (model_to_L4 _) (model_to_L4 _))
         => apply refine_34 : refine_xx.

    Hint Extern 1 (refine_L5 (model_to_L5 _) (model_to_L5 _))
         => apply refine_45 : refine_xx.

    Ltac solve_refine :=
      auto 9 with refine_xx.

    (**
   The chain of refinements is monotone, legitimating the ability to
   conduct reasoning before interpretation when suitable.
     *)
    Lemma refine_mcfg_L1_correct: forall p1 p2,
        refine_mcfg_L1 p1 p2 -> refine_mcfg p1 p2.
    Proof using.
      intros p1 p2 HR;
        solve_refine.
    Qed.

    Lemma refine_mcfg_L2_correct: forall p1 p2,
        refine_mcfg_L2 p1 p2 -> refine_mcfg p1 p2.
    Proof using.
      intros p1 p2 HR;
        solve_refine.
    Qed.

    Lemma refine_mcfg_L3_correct: forall p1 p2,
        refine_mcfg_L3 p1 p2 -> refine_mcfg p1 p2.
    Proof using.
      intros p1 p2 HR;
        solve_refine.
    Qed.

    Lemma refine_mcfg_L4_correct: forall p1 p2,
        refine_mcfg_L4 p1 p2 -> refine_mcfg p1 p2.
    Proof using.
      intros p1 p2 HR;
        solve_refine.
    Qed.

    Lemma refine_mcfg_L5_correct: forall p1 p2,
        refine_mcfg_L5 p1 p2 -> refine_mcfg p1 p2.
    Proof using.
      intros p1 p2 HR;
        solve_refine.
    Qed.

    Lemma refine_mcfg_L6_correct: forall p1 p2,
        refine_mcfg_L6 p1 p2 -> refine_mcfg p1 p2.
    Proof using.
      intros p1 p2 HR;
        solve_refine.
    Qed.

    (* MOVE *)
    Ltac flatten_goal :=
      match goal with
      | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
      end.

    Ltac flatten_hyp h :=
      match type of h with
      | context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
      end.

    Ltac flatten_all :=
      match goal with
      | h: context[match ?x with | _ => _ end] |- _ => let Heq := fresh "Heq" in destruct x eqn:Heq
      | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
      end.

    #[global] Instance Proper_E_trigger_prop E F T : Proper (eq ==> (eutt eq) ==> iff) (@E_trigger_prop E F T).
    Proof using.
      repeat red; intros.
      split; intros; unfold E_trigger_prop in *.
      - rewrite <- H0. rewrite <- H. assumption.
      - rewrite H0. rewrite H. assumption.
    Qed.

    #[global] Instance Proper_F_trigger_prop E F T : Proper (eq ==> (eutt eq) ==> iff) (@F_trigger_prop E F T).
    Proof using.
      repeat red; intros.
      split; intros; unfold F_trigger_prop in *.
      - rewrite <- H0. rewrite <- H. assumption.
      - rewrite H0. rewrite H. assumption.
    Qed.

    #[global] Instance ProperPickUvalue_handler E T `{FailureE -< E} `{UBE -< E} `{OOME -< E} :  Proper (eq ==> (eutt eq) ==> iff) (@PickUvalue_handler E _ _ _ T).
    Proof using.
      repeat red; intros.
      split; intros.
      - inversion H4.
        + (* PickUV_UniqueUB *)
          dependent destruction H5.
          apply inj_pair2 in H8, H10.
          subst.
          apply PickUV_UniqueUB. assumption.
        + (* PickUV_UniqueRet *)
          dependent destruction H5.
          apply inj_pair2 in H6.
          apply inj_pair2 in H10.
          subst.
          eapply PickUV_UniqueRet; eauto.
          rewrite <- H3. apply H11.
        + (* PickUV_NonPoisonUB *)
          dependent destruction H5.
          apply inj_pair2 in H8, H10.
          subst.
          apply PickUV_NonPoisonUB. assumption.
        + (* PickUV_NonPoisonRet *)
          dependent destruction H5.
          apply inj_pair2 in H6.
          apply inj_pair2 in H10.
          subst.
          eapply PickUV_NonPoisonRet; eauto.
          rewrite <- H3. apply H11.
        + (* PickUV_Ret *)
          dependent destruction H5.
          apply inj_pair2 in H8.
          apply inj_pair2 in H10.
          subst.
          eapply PickUV_Ret; eauto.
          rewrite <- H3. apply H7.
      - inversion H4.
        + (* PickUV_UniqueUB *)
          dependent destruction H5.
          apply inj_pair2 in H8, H10.
          subst.
          apply PickUV_UniqueUB. assumption.
        + (* PickUV_UniqueRet *)
          dependent destruction H5.
          apply inj_pair2 in H6.
          apply inj_pair2 in H10.
          subst.
          eapply PickUV_UniqueRet; eauto.
          rewrite H3. apply H11.
        + (* PickUV_NonPoisonUB *)
          dependent destruction H5.
          apply inj_pair2 in H8, H10.
          subst.
          apply PickUV_NonPoisonUB. assumption.
        + (* PickUV_NonPoisonRet *)
          dependent destruction H5.
          apply inj_pair2 in H6.
          apply inj_pair2 in H10.
          subst.
          eapply PickUV_NonPoisonRet; eauto.
          rewrite H3. apply H11.
        + (* PickUV_Ret *)
          dependent destruction H5.
          apply inj_pair2 in H8.
          apply inj_pair2 in H10.
          subst.
          eapply PickUV_Ret; eauto.
          rewrite H3. apply H7.
    Qed.

    (* SAZ: I'm not sure which Proper instance is missing that prevents this from being
       automatically derived from the two instances above.
     *)
    #[global] Instance adhoc_Proper F E A e `{UBE -< F}  `{FailureE -< F}  `{OOME -< F} :
@Proper (forall _ : itree (sum1 E F) A, Prop)
        (@respectful (itree (sum1 E F) A) Prop (@eutt (sum1 E F) A A (@eq A)) (@flip Prop Prop Prop impl))
        (@case_ (forall _ : Type, Type) IFun sum1 Case_sum1 E (sum1 PickUvalueE F)
           (fun T : Type => forall _ : itree (sum1 E F) T, Prop) (@E_trigger_prop E F)
           (@case_ (forall _ : Type, Type) IFun sum1 Case_sum1 PickUvalueE F
              (fun T : Type => forall _ : itree (sum1 E F) T, Prop)
              (@PickUvalue_handler (sum1 E F)
                 (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 FailureE F E H0)
                 (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 UBE F E H)
                 (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME F E H1))
              (@F_trigger_prop E F)) A e).
    Proof using.
      repeat red.
      intros.
      destruct e; simpl in *.
      - rewrite H2. apply H3.
      - destruct s. cbn in *. rewrite H2. assumption.
        cbn in *. rewrite H2. assumption.
    Qed.

    (* TODO: prove and move this? *)
    Import EitherMonad.
    Import IdentityMonad.
    Import MapMonadExtra.

    (* TODO: Move this *)
    Lemma uvalue_strict_subterm_struct :
      forall f f' fields,
        uvalue_strict_subterm f (UVALUE_Struct fields) ->
        uvalue_strict_subterm f (UVALUE_Struct (f' :: fields)).
    Proof.
      intros f f' fields H.
      dependent induction H.
      - inv H.
        constructor.
        constructor.
        right; auto.
      - specialize (IHclos_trans2 fields eq_refl).
        eapply t_trans.
        apply H.
        apply IHclos_trans2.
    Qed.

    (* TODO: Move this *)
    Lemma uvalue_strict_subterm_packed_struct :
      forall f f' fields,
        uvalue_strict_subterm f (UVALUE_Packed_struct fields) ->
        uvalue_strict_subterm f (UVALUE_Packed_struct (f' :: fields)).
    Proof.
      intros f f' fields H.
      dependent induction H.
      - inv H.
        constructor.
        constructor.
        right; auto.
      - specialize (IHclos_trans2 fields eq_refl).
        eapply t_trans.
        apply H.
        apply IHclos_trans2.
    Qed.

    (* TODO: Move this *)
    Lemma uvalue_strict_subterm_array :
      forall f f' fields,
        uvalue_strict_subterm f (UVALUE_Array fields) ->
        uvalue_strict_subterm f (UVALUE_Array (f' :: fields)).
    Proof.
      intros f f' fields H.
      dependent induction H.
      - inv H.
        constructor.
        constructor.
        right; auto.
      - specialize (IHclos_trans2 fields eq_refl).
        eapply t_trans.
        apply H.
        apply IHclos_trans2.
    Qed.

    (* TODO: Move this *)
    Lemma uvalue_strict_subterm_vector :
      forall f f' fields,
        uvalue_strict_subterm f (UVALUE_Vector fields) ->
        uvalue_strict_subterm f (UVALUE_Vector (f' :: fields)).
    Proof.
      intros f f' fields H.
      dependent induction H.
      - inv H.
        constructor.
        constructor.
        right; auto.
      - specialize (IHclos_trans2 fields eq_refl).
        eapply t_trans.
        apply H.
        apply IHclos_trans2.
    Qed.

    Lemma eval_int_op_err_ub_oom_to_itree :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E} {I} `{VMI : VellvmIntegers.VMemInt I} `{DVI : ToDvalue I}
        x y iop,
        (@eval_int_op (itree E) I _ _ _ _ _ _ iop x y) ≈
          match eval_int_op iop x y with
          | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
              match m with
              | inl (OOM_message x) => raiseOOM x
              | inr (inl (UB_message x)) => raiseUB x
              | inr (inr (inl (ERR_message x))) => raise x
              | inr (inr (inr x)) => ret x
              end
          end.
    Proof.
      intros E H H0 H1 I VMI DVI x y iop.
      unfold eval_int_op.
      destruct iop; cbn; try reflexivity;
        try solve
          [ break_match; reflexivity
          | break_match; cbn; try reflexivity;
            unfold lift_OOM;
            break_inner_match; cbn;
            repeat setoid_rewrite Raise.raiseOOM_bind_itree;
            repeat setoid_rewrite Raise.raiseUB_bind_itree;
            repeat setoid_rewrite Raise.raise_bind_itree;
            repeat rewrite bind_ret_l; try reflexivity
          | break_match; cbn; try reflexivity;
            unfold lift_OOM;
            break_inner_match; cbn;
            repeat setoid_rewrite Raise.raiseOOM_bind_itree;
            repeat setoid_rewrite Raise.raiseUB_bind_itree;
            repeat setoid_rewrite Raise.raise_bind_itree;
            repeat rewrite bind_ret_l; try reflexivity;
            setoid_rewrite IP.VMemInt_intptr_dtyp;
            setoid_rewrite dtyp_eqb_refl;
            break_match; cbn; reflexivity
          ].
      - break_match; cbn; try reflexivity;
          unfold lift_OOM;
          break_inner_match; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.
        repeat (break_match; cbn; try reflexivity);
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.
      - break_match; cbn; try reflexivity;
          unfold lift_OOM;
          break_inner_match; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.
        repeat (break_match; cbn; try reflexivity);
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.
        repeat (break_match; cbn; try reflexivity);
          repeat rewrite bind_ret_l; try reflexivity;
          try discriminate.
        repeat (break_match; cbn; try reflexivity);
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat rewrite bind_ret_l; inv Heqi1; try reflexivity; try discriminate.
        repeat (break_match; cbn; try reflexivity);
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat rewrite bind_ret_l; inv Heqi1; try reflexivity; try discriminate.
        repeat (break_match; cbn; try reflexivity);
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat rewrite bind_ret_l; reflexivity; try discriminate.
      - break_match; cbn; try reflexivity;
          unfold lift_OOM;
          break_inner_match; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.
        repeat (break_match; cbn; try reflexivity);
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.
      - break_match; cbn; try reflexivity;
          unfold lift_OOM;
          break_inner_match; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.
        repeat (break_match; cbn; try reflexivity);
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.
      - break_match; cbn; try reflexivity;
          unfold lift_OOM;
          break_inner_match; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.
        repeat (break_match; cbn; try reflexivity);
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.
    Qed.

    (* TODO: Move this *)
    Lemma combine_cons :
      forall {X Y} (x : X) (y : Y) xs ys,
        combine (x :: xs) (y :: ys) = (x,y) :: combine xs ys.
    Proof.
      cbn; auto.
    Qed.

    (* TODO: Move this *)
    Import MonadNotation.
    Lemma vec_loop_cons :
      forall {A M} `{HM : Monad M}
        (f : A -> A -> M A)
        a b xs,
        @vec_loop A M HM f ((a,b) :: xs) =
          res <- @vec_loop A M HM f xs;;
          val <- f a b;;
          ret (val :: res).
    Proof.
      intros A M HM f a b xs.
      cbn.
      reflexivity.
    Qed.

    Lemma eval_iop_integer_h_err_ub_oom_to_itree :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E}
        x y iop,
        (@eval_iop_integer_h (itree E) _ _ _ _ iop x y) ≈
          match eval_iop_integer_h iop x y with
          | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
              match m with
              | inl (OOM_message x) => raiseOOM x
              | inr (inl (UB_message x)) => raiseUB x
              | inr (inr (inl (ERR_message x))) => raise x
              | inr (inr (inr x)) => ret x
              end
          end.
    Proof.
      intros E H H0 H1 x y iop.
      destruct x, y; cbn; try reflexivity;
        try solve
          [ break_match; reflexivity
          | cbn; rewrite eval_int_op_err_ub_oom_to_itree; reflexivity
          ].
    Qed.

    Lemma eval_iop_err_ub_oom_to_itree :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E}
        x y iop,
        (@eval_iop (itree E) _ _ _ _ iop x y) ≈
          match eval_iop iop x y with
          | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
              match m with
              | inl (OOM_message x) => raiseOOM x
              | inr (inl (UB_message x)) => raiseUB x
              | inr (inr (inl (ERR_message x))) => raise x
              | inr (inr (inr x)) => ret x
              end
          end.
    Proof.
      intros E H H0 H1 x y iop.
      unfold eval_iop.
      destruct x, y; cbn;
        try solve
          [ reflexivity
          | break_match; reflexivity
          | cbn; apply eval_int_op_err_ub_oom_to_itree
          ].

      (* Need vec_loop lemma *)
      rename elts into xs.
      rename elts0 into ys.

      remember (xs, ys) as ZIP.
      replace xs with (fst ZIP) by (subst; cbn; auto).
      replace ys with (snd ZIP) by (subst; cbn; auto).
      clear HeqZIP xs ys.

      induction ZIP using double_list_rect.
      - (* Both nil *)
        unfold fst, snd in *; cbn; rewrite bind_ret_l; reflexivity.
      - (* nil l *)
        unfold fst, snd in *; cbn; rewrite bind_ret_l; reflexivity.
      - (* nil r *)
        unfold fst, snd in *; cbn; rewrite bind_ret_l; reflexivity.
      - (* Both cons *)
        unfold fst, snd in *.
        rewrite combine_cons.
        setoid_rewrite vec_loop_cons.
        setoid_rewrite bind_bind.
        remember
          (@vec_loop dvalue (err_ub_oom_T ident) (@Monad_err_ub_oom ident Monad_ident)
          (@eval_iop_integer_h (err_ub_oom_T ident) (@Monad_err_ub_oom ident Monad_ident)
             (@RAISE_ERROR_err_ub_oom ident Monad_ident) (@RAISE_UB_err_ub_oom_T ident Monad_ident)
             (@RAISE_OOM_err_ub_oom_T ident Monad_ident) iop) (@combine dvalue dvalue xs ys)) as res.

        destruct_err_ub_oom res; cbn in *;
          repeat rewrite (Raise.raiseOOM_map_itree_inv E (list dvalue) _ _ _ _ IHZIP);
          repeat rewrite (Raise.raiseUB_map_itree_inv E (list dvalue) _ _ _ _ IHZIP);
          repeat rewrite (Raise.raise_map_itree_inv E (list dvalue) _ _ _ _ IHZIP);
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        eapply eutt_inv_bind_ret in IHZIP.
        destruct IHZIP as (?&?&?).
        eapply eutt_inv_Ret in H3; inv H3.
        rewrite H2.
        cbn.
        rewrite bind_ret_l.
        rewrite eval_iop_integer_h_err_ub_oom_to_itree.
        remember (eval_iop_integer_h iop x y) as r.

        destruct_err_ub_oom r; cbn in *;
          repeat rewrite (Raise.raiseOOM_map_itree_inv E (list dvalue) _ _ _ _ IHZIP);
          repeat rewrite (Raise.raiseUB_map_itree_inv E (list dvalue) _ _ _ _ IHZIP);
          repeat rewrite (Raise.raise_map_itree_inv E (list dvalue) _ _ _ _ IHZIP);
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.
    Qed.

    Lemma eval_icmp_err_ub_oom_to_itree :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E}
        x y icmp,
        (@eval_icmp (itree E) _ _ icmp x y) ≈
          match eval_icmp icmp x y with
          | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
              match m with
              | inl (OOM_message x) => raiseOOM x
              | inr (inl (UB_message x)) => raiseUB x
              | inr (inr (inl (ERR_message x))) => raise x
              | inr (inr (inr x)) => ret x
              end
          end.
    Proof.
      intros E H H0 H1 x y icmp.
      destruct x, y; cbn;
        try solve
          [ reflexivity
          | break_match; reflexivity
          | cbn; apply eval_int_op_err_ub_oom_to_itree
          ].

      all:
        try solve
          [ destruct icmp; cbn;
            repeat setoid_rewrite Raise.raiseUB_bind_itree;
            repeat setoid_rewrite Raise.raise_bind_itree;
            repeat rewrite bind_ret_l; try reflexivity
          ].

      destruct icmp;
        unfold eval_icmp;
        cbn;
        try setoid_rewrite IP.VMemInt_intptr_dtyp;
        try setoid_rewrite dtyp_eqb_refl;
        cbn;
        repeat setoid_rewrite Raise.raiseUB_bind_itree;
        repeat setoid_rewrite Raise.raise_bind_itree;
        repeat rewrite bind_ret_l; try reflexivity.
    Qed.

    Lemma double_op_err_ub_oom_to_itree :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E}
        x y fop,
      @double_op (itree E) (@Monad_itree E) (@RAISE_ERR_ITREE_FAILUREE E H0) (@RAISE_UB_ITREE_UB E H1) fop
        x y
        ≈ match
          @double_op (err_ub_oom_T ident) (@Monad_err_ub_oom ident Monad_ident)
            (@RAISE_ERROR_err_ub_oom ident Monad_ident) (@RAISE_UB_err_ub_oom_T ident Monad_ident) fop x y
        with
        | OOM_unERR_UB_OOM x1 => @raiseOOM E H dvalue x1
        | UB_unERR_UB_OOM x1 => @raiseUB E H1 dvalue x1
        | ERR_unERR_UB_OOM x1 => @raise E dvalue H0 x1
        | success_unERR_UB_OOM x1 => Ret x1
        end.
    Proof.
      intros E H H0 H1 x y fop.
      destruct fop; cbn; reflexivity.
    Qed.

    Lemma float_op_err_ub_oom_to_itree :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E}
        x y fop,
      @float_op (itree E) (@Monad_itree E) (@RAISE_ERR_ITREE_FAILUREE E H0) (@RAISE_UB_ITREE_UB E H1) fop
        x y
        ≈ match
          @float_op (err_ub_oom_T ident) (@Monad_err_ub_oom ident Monad_ident)
            (@RAISE_ERROR_err_ub_oom ident Monad_ident) (@RAISE_UB_err_ub_oom_T ident Monad_ident) fop x y
        with
        | OOM_unERR_UB_OOM x1 => @raiseOOM E H dvalue x1
        | UB_unERR_UB_OOM x1 => @raiseUB E H1 dvalue x1
        | ERR_unERR_UB_OOM x1 => @raise E dvalue H0 x1
        | success_unERR_UB_OOM x1 => Ret x1
        end.
    Proof.
      intros E H H0 H1 x y fop.
      destruct fop; cbn; reflexivity.
    Qed.

    Lemma eval_fop_err_ub_oom_to_itree :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E}
        x y fop,
        (@eval_fop (itree E) _ _ _ fop x y) ≈
          match eval_fop fop x y with
          | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
              match m with
              | inl (OOM_message x) => raiseOOM x
              | inr (inl (UB_message x)) => raiseUB x
              | inr (inr (inl (ERR_message x))) => raise x
              | inr (inr (inr x)) => ret x
              end
          end.
    Proof.
      intros E H H0 H1 x y fop.
      unfold eval_fop.
      destruct x, y; cbn;
        try solve
          [ reflexivity
          | break_match; reflexivity
          ].

      apply double_op_err_ub_oom_to_itree.
      apply float_op_err_ub_oom_to_itree.
    Qed.

    Lemma eval_fcmp_err_ub_oom_to_itree :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E}
        x y cmp,
        (@eval_fcmp (itree E) _ _ cmp x y) ≈
          match eval_fcmp cmp x y with
          | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
              match m with
              | inl (OOM_message x) => raiseOOM x
              | inr (inl (UB_message x)) => raiseUB x
              | inr (inr (inl (ERR_message x))) => raise x
              | inr (inr (inr x)) => ret x
              end
          end.
    Proof.
      intros E H H0 H1 x y cmp.
      destruct x, y; cbn;
        try solve
          [ reflexivity
          | break_match; reflexivity
          ].
    Qed.

    Lemma index_into_vec_dv_loop_err_ub_oom_to_itree :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E}
        elts t n,
        (fix loop (dt : dtyp) (elts0 : list dvalue) (i : Z) {struct elts0} : itree E dvalue :=
           match elts0 with
           | [] => Ret (DVALUE_Poison dt)
           | h :: tl => if (i =? 0)%Z then Ret h else loop dt tl (i - 1)%Z
           end) t elts n
          ≈ match
            (fix loop (dt : dtyp) (elts0 : list dvalue) (i : Z) {struct elts0} :
              err_ub_oom_T ident dvalue :=
               match elts0 with
               | [] => success_unERR_UB_OOM (DVALUE_Poison dt)
               | h :: tl => if (i =? 0)%Z then success_unERR_UB_OOM h else loop dt tl (i - 1)%Z
               end) t elts n
          with
          | OOM_unERR_UB_OOM x0 => raiseOOM x0
          | UB_unERR_UB_OOM x0 => raiseUB x0
          | ERR_unERR_UB_OOM x0 => raise x0
          | success_unERR_UB_OOM x0 => Ret x0
          end.
    Proof.
      intros E H H0 H1 elts.
      induction elts;
        intros t n;
        try reflexivity.

      break_match; try reflexivity.
      rewrite IHelts.
      reflexivity.
    Qed.

    Lemma index_into_vec_dv_err_ub_oom_to_itree :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E}
        x y t,
        (@index_into_vec_dv (itree E) _ _ t x y) ≈
          match index_into_vec_dv t x y with
          | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
              match m with
              | inl (OOM_message x) => raiseOOM x
              | inr (inl (UB_message x)) => raiseUB x
              | inr (inr (inl (ERR_message x))) => raise x
              | inr (inr (inr x)) => ret x
              end
          end.
    Proof.
      intros E H H0 H1 x y t.
      destruct x, y; cbn;
        try solve
          [ reflexivity
          | break_match; reflexivity
          | unfold index_into_vec_dv;
            break_match; cbn;
            try reflexivity;
            rewrite index_into_vec_dv_loop_err_ub_oom_to_itree;
            reflexivity
          ].
    Qed.

    Lemma insert_into_vec_dv_err_ub_oom_to_itree :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E}
        x y z t,
        (@insert_into_vec_dv (itree E) _ _ t x y z) ≈
          match insert_into_vec_dv t x y z with
          | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
              match m with
              | inl (OOM_message x) => raiseOOM x
              | inr (inl (UB_message x)) => raiseUB x
              | inr (inr (inl (ERR_message x))) => raise x
              | inr (inr (inr x)) => ret x
              end
          end.
    Proof.
      intros E H H0 H1 x y z t.
      destruct x, y; cbn;
        try reflexivity;
      destruct z; cbn;
        try solve
          [ reflexivity
          | break_match; reflexivity
          | cbn;
            unfold insert_into_vec_dv;
            repeat break_match; cbn; try reflexivity;
            try discriminate;
            inv Heqe; reflexivity
          ].
    Qed.

    Lemma index_into_str_dv_loop_err_ub_oom_to_itree :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E}
        fields i,
        (fix loop (elts : list dvalue) (i0 : Z) {struct elts} : itree E dvalue :=
           match elts with
           | [] => raise_error "index_into_str_dv: index out of bounds"
           | h :: tl => if (i0 =? 0)%Z then ret h else loop tl (i0 - 1)%Z
           end) fields i ≈
          match (fix loop (elts : list dvalue) (i0 : Z) {struct elts} : err_ub_oom dvalue :=
                   match elts with
                   | [] => raise_error "index_into_str_dv: index out of bounds"
                   | h :: tl => if (i0 =? 0)%Z then ret h else loop tl (i0 - 1)%Z
                   end) fields i with
          | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
              match m with
              | inl (OOM_message x) => raiseOOM x
              | inr (inl (UB_message x)) => raiseUB x
              | inr (inr (inl (ERR_message x))) => raise x
              | inr (inr (inr x)) => ret x
              end
          end.
    Proof.
      intros E H H0 H1 fields;
        induction fields; intros i;
        try reflexivity.
      break_match; try reflexivity.
      rewrite IHfields.
      reflexivity.
    Qed.

    Lemma index_into_str_dv_err_ub_oom_to_itree :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E}
        str i,
        (@index_into_str_dv (itree E) _ _ str i) ≈
          match index_into_str_dv str i with
          | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
              match m with
              | inl (OOM_message x) => raiseOOM x
              | inr (inl (UB_message x)) => raiseUB x
              | inr (inr (inl (ERR_message x))) => raise x
              | inr (inr (inr x)) => ret x
              end
          end.
    Proof.
      intros E H H0 H1 str i.
      destruct str; cbn;
        try solve
          [ reflexivity
          | break_match; reflexivity
          | unfold index_into_str_dv;
            rewrite index_into_str_dv_loop_err_ub_oom_to_itree;
            reflexivity
          ].
    Qed.

    Lemma extract_value_loop_err_ub_oom_to_itree :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E}
        idxs str,
        (fix loop str idxs {struct idxs} : itree E dvalue :=
           match idxs with
           | [] => ret str
           | i :: tl =>
               v <- index_into_str_dv str i ;;
               loop v tl
           end) str idxs ≈
          match (fix loop str idxs {struct idxs} : err_ub_oom dvalue :=
                   match idxs with
                   | [] => ret str
                   | i :: tl =>
                       v <- index_into_str_dv str i ;;
                       loop v tl
                   end) str idxs with
          | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
              match m with
              | inl (OOM_message x) => raiseOOM x
              | inr (inl (UB_message x)) => raiseUB x
              | inr (inr (inl (ERR_message x))) => raise x
              | inr (inr (inr x)) => ret x
              end
          end.
    Proof.
      induction idxs;
        intros str; try reflexivity.
      rewrite index_into_str_dv_err_ub_oom_to_itree.
      remember (index_into_str_dv str a) as ind.
      destruct_err_ub_oom ind; cbn;
        repeat setoid_rewrite Raise.raiseOOM_bind_itree;
        repeat setoid_rewrite Raise.raiseUB_bind_itree;
        repeat setoid_rewrite Raise.raise_bind_itree;
        repeat rewrite bind_ret_l; try reflexivity.
      rewrite IHidxs.
      remember ((fix loop (str0 : dvalue) (idxs0 : list int_ast) {struct idxs0} : err_ub_oom dvalue :=
                   match idxs0 with
                   | [] => ret str0
                   | i :: tl => v <- index_into_str_dv str0 i;; loop v tl
                   end) ind0 idxs) as res.
      setoid_rewrite <- Heqres.
      destruct_err_ub_oom res; reflexivity.
    Qed.

    Lemma insert_into_str_loop_err_ub_oom_to_itree :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E}
        elts acc v i,
        (fix loop (acc elts:list dvalue) (i:LLVMAst.int_ast) : itree E (list dvalue) :=
           match elts with
           | [] => raise "insert_into_str: index out of bounds"
           | h :: tl =>
               (if i =? 0 then @ret (itree E) _ _ (acc ++ (v :: tl))
                else loop (acc ++ [h]) tl (i-1))%Z
           end%list) acc elts i ≈
          match
            (fix loop (acc elts:list dvalue) (i:LLVMAst.int_ast) : err_ub_oom (list dvalue) :=
               match elts with
               | [] => raise_error "insert_into_str: index out of bounds"
               | h :: tl =>
                   (if i =? 0 then @ret err_ub_oom _ _ (acc ++ (v :: tl))
                    else loop (acc ++ [h]) tl (i-1))%Z
               end%list) acc elts i
          with
          | OOM_unERR_UB_OOM x => raiseOOM x
          | UB_unERR_UB_OOM x => raiseUB x
          | ERR_unERR_UB_OOM x => raise x
          | success_unERR_UB_OOM x => ret x
          end.
    Proof.
      intros E H H0 H1 elts.
      induction elts; intros acc v i; try reflexivity.
      break_match; try reflexivity.
      rewrite IHelts.
      reflexivity.
    Qed.

    Lemma insert_into_str_err_ub_oom_to_itree :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E}
        str elt a,
        @insert_into_str (itree E) _ _ str elt a
          ≈ match insert_into_str str elt a with
          | OOM_unERR_UB_OOM x => raiseOOM x
          | UB_unERR_UB_OOM x => raiseUB x
          | ERR_unERR_UB_OOM x => raise x
          | success_unERR_UB_OOM x => ret x
          end.
    Proof.
      intros E H H0 H1 str elt a.
      destruct str; try reflexivity.
      - cbn.
        unfold insert_into_str.
        setoid_rewrite insert_into_str_loop_err_ub_oom_to_itree.
        cbn.
        remember ((fix loop (acc elts : list dvalue) (i : int_ast) {struct elts} :
                    err_ub_oom_T ident (list dvalue) :=
                     match elts with
                     | [] => ERR_unERR_UB_OOM "insert_into_str: index out of bounds"
                     | h :: tl =>
                         if (i =? 0)%Z
                         then success_unERR_UB_OOM (acc ++ elt :: tl)%list
                         else loop (acc ++ [h])%list tl (i - 1)%Z
                     end) [] fields a) as res.
        setoid_rewrite <- Heqres.
        destruct_err_ub_oom res; cbn;
        repeat setoid_rewrite Raise.raiseOOM_bind_itree;
        repeat setoid_rewrite Raise.raiseUB_bind_itree;
        repeat setoid_rewrite Raise.raise_bind_itree;
        repeat rewrite bind_ret_l; try reflexivity.
      - cbn.
        unfold insert_into_str.
        setoid_rewrite insert_into_str_loop_err_ub_oom_to_itree.
        cbn.
        remember ((fix loop (acc elts : list dvalue) (i : int_ast) {struct elts} :
                    err_ub_oom_T ident (list dvalue) :=
                     match elts with
                     | [] => ERR_unERR_UB_OOM "insert_into_str: index out of bounds"
                     | h :: tl =>
                         if (i =? 0)%Z
                         then success_unERR_UB_OOM (acc ++ elt :: tl)%list
                         else loop (acc ++ [h])%list tl (i - 1)%Z
                     end) [] fields a) as res.
        setoid_rewrite <- Heqres.
        destruct_err_ub_oom res; cbn;
        repeat setoid_rewrite Raise.raiseOOM_bind_itree;
        repeat setoid_rewrite Raise.raiseUB_bind_itree;
        repeat setoid_rewrite Raise.raise_bind_itree;
        repeat rewrite bind_ret_l; try reflexivity.
      - cbn.
        unfold insert_into_str.
        setoid_rewrite insert_into_str_loop_err_ub_oom_to_itree.
        cbn.
        remember ((fix loop (acc elts : list dvalue) (i : int_ast) {struct elts} :
                    err_ub_oom_T ident (list dvalue) :=
                     match elts with
                     | [] => ERR_unERR_UB_OOM "insert_into_str: index out of bounds"
                     | h :: tl =>
                         if (i =? 0)%Z
                         then success_unERR_UB_OOM (acc ++ elt :: tl)%list
                         else loop (acc ++ [h])%list tl (i - 1)%Z
                     end) [] elts a) as res.
        setoid_rewrite <- Heqres.
        destruct_err_ub_oom res; cbn;
        repeat setoid_rewrite Raise.raiseOOM_bind_itree;
        repeat setoid_rewrite Raise.raiseUB_bind_itree;
        repeat setoid_rewrite Raise.raise_bind_itree;
        repeat rewrite bind_ret_l; try reflexivity.
    Qed.

    Lemma insert_value_loop_err_ub_oom_to_itree :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E}
        idxs str elt,
        (fix loop str idxs : itree E dvalue :=
           match idxs with
           | [] => raise_error "Index was not provided"
           | i :: nil =>
               v <- insert_into_str str elt i;;
               ret v
           | i :: tl =>
               subfield <- index_into_str_dv str i;;
               modified_subfield <- loop subfield tl;;
               insert_into_str str modified_subfield i
           end) str idxs ≈
          match
            (fix loop str idxs : err_ub_oom dvalue :=
               match idxs with
               | [] => raise_error "Index was not provided"
               | i :: nil =>
                   v <- insert_into_str str elt i;;
                   ret v
               | i :: tl =>
                   subfield <- index_into_str_dv str i;;
                   modified_subfield <- loop subfield tl;;
                   insert_into_str str modified_subfield i
               end) str idxs with
          | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
              match m with
              | inl (OOM_message x) => raiseOOM x
              | inr (inl (UB_message x)) => raiseUB x
              | inr (inr (inl (ERR_message x))) => raise x
              | inr (inr (inr x)) => ret x
              end
          end.
    Proof.
      intros E H H0 H1.
      induction idxs; intros str elt; try reflexivity.
      destruct idxs; try reflexivity.
      - setoid_rewrite bind_ret_r.
        rewrite insert_into_str_err_ub_oom_to_itree.
        remember (insert_into_str str elt a) as res.
        destruct_err_ub_oom res; reflexivity.
      - rewrite index_into_str_dv_err_ub_oom_to_itree.
        setoid_rewrite IHidxs.
        setoid_rewrite insert_into_str_err_ub_oom_to_itree.
        remember (index_into_str_dv str a) as ar.
        destruct_err_ub_oom ar;
          try solve
            [ cbn;
              repeat setoid_rewrite Raise.raiseOOM_bind_itree;
              repeat setoid_rewrite Raise.raiseUB_bind_itree;
              repeat setoid_rewrite Raise.raise_bind_itree;
              repeat rewrite bind_ret_l; try reflexivity
            ].
        setoid_rewrite bind_ret_l.
        remember (match idxs with
                  | [] => v <- insert_into_str ar0 elt i;; ret v
                  | _ :: _ =>
                      subfield0 <- index_into_str_dv ar0 i;;
                      modified_subfield <-
                        (fix loop (str0 : dvalue) (idxs0 : list int_ast) {struct idxs0} : err_ub_oom dvalue :=
                           match idxs0 with
                           | [] => raise_error "Index was not provided"
                           | [i1] => v <- insert_into_str str0 elt i1;; ret v
                           | i1 :: (_ :: _) as tl =>
                               subfield1 <- index_into_str_dv str0 i1;;
                               modified_subfield <- loop subfield1 tl;; insert_into_str str0 modified_subfield i1
                           end) subfield0 idxs;; insert_into_str ar0 modified_subfield i
                  end).
        cbn in *.
        setoid_rewrite <- Heqe.
        destruct_err_ub_oom e; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        remember (insert_into_str str e0 a) as r.
        destruct_err_ub_oom r; reflexivity.
    Qed.

    Lemma eval_select_loop_err_ub_oom_to_itree :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E}
        (conds xs ys : list dvalue),
        (fix loop conds xs ys {struct conds} : itree E (list dvalue) :=
           match conds, xs, ys with
           | [], [], [] => @ret _ _ _ []
           | (c::conds), (x::xs), (y::ys) =>
               @bind _ _ _ _
                 (match c with
                  | DVALUE_Poison t =>
                      (* TODO: Should be the type of the result of the select... *)
                      @ret _ _ _ (DVALUE_Poison t)
                  | DVALUE_I1 i =>
                      if (VellvmIntegers.Int1.unsigned i =? 1)%Z
                      then @ret _ _ _ x
                      else @ret _ _ _ y
                  | _ =>
                      raise "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1."
                  end)
                 (fun selected =>
                    @bind _ _ _ _
                      (loop conds xs ys)
                      (fun rest =>
                         @ret _ _ _ (selected :: rest)))
           | _, _, _ =>
               raise "concretize_uvalueM: ill-typed vector select, length mismatch."
           end) conds xs ys ≈
          match (fix loop conds xs ys {struct conds} : err_ub_oom (list dvalue) :=
                   match conds, xs, ys with
                   | [], [], [] => @ret err_ub_oom _ _ []
                   | (c::conds), (x::xs), (y::ys) =>
                       @bind err_ub_oom _ _ _
                         (match c with
                          | DVALUE_Poison t =>
                              (* TODO: Should be the type of the result of the select... *)
                              @ret err_ub_oom _ _ (DVALUE_Poison t)
                          | DVALUE_I1 i =>
                              if (VellvmIntegers.Int1.unsigned i =? 1)%Z
                              then @ret _ _ _ x
                              else @ret _ _ _ y
                          | _ =>
                              raise_error "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1."
                          end)
                         (fun selected =>
                            @bind err_ub_oom _ _ _
                              (loop conds xs ys)
                              (fun rest =>
                                 @ret _ _ _ (selected :: rest)))
                   | _, _, _ =>
                       raise_error "concretize_uvalueM: ill-typed vector select, length mismatch."
                   end) conds xs ys
          with
           | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
               match m with
               | inl (OOM_message x) => raiseOOM x
               | inr (inl (UB_message x)) => raiseUB x
               | inr (inr (inl (ERR_message x))) => raise x
               | inr (inr (inr x)) => ret x
               end
           end.
    Proof.
      intros E H H0 H1 conds.
      induction conds;
        intros xs ys;
        cbn in *; subst; auto;
        try reflexivity;
        destruct xs, ys; try reflexivity.

      destruct a; cbn;
        repeat setoid_rewrite Raise.raiseOOM_bind_itree;
        repeat setoid_rewrite Raise.raiseUB_bind_itree;
        repeat setoid_rewrite Raise.raise_bind_itree;
        repeat rewrite bind_ret_l; try reflexivity.

      { break_match; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        - setoid_rewrite IHconds.
          match goal with
          | [ |- context [ match ?X with _ => _ end ] ] =>
              remember X
          end.

          destruct_err_ub_oom e; cbn;
            repeat setoid_rewrite Raise.raiseOOM_bind_itree;
            repeat setoid_rewrite Raise.raiseUB_bind_itree;
            repeat setoid_rewrite Raise.raise_bind_itree;
            repeat rewrite bind_ret_l; try reflexivity.
        - setoid_rewrite IHconds.
          match goal with
          | [ |- context [ match ?X with _ => _ end ] ] =>
              remember X
          end.

          destruct_err_ub_oom e; cbn;
            repeat setoid_rewrite Raise.raiseOOM_bind_itree;
            repeat setoid_rewrite Raise.raiseUB_bind_itree;
            repeat setoid_rewrite Raise.raise_bind_itree;
            repeat rewrite bind_ret_l; try reflexivity.
      }

      { cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        - setoid_rewrite IHconds.
          match goal with
          | [ |- context [ match ?X with _ => _ end ] ] =>
              remember X
          end.

          destruct_err_ub_oom e; cbn;
            repeat setoid_rewrite Raise.raiseOOM_bind_itree;
            repeat setoid_rewrite Raise.raiseUB_bind_itree;
            repeat setoid_rewrite Raise.raise_bind_itree;
            repeat rewrite bind_ret_l; try reflexivity.
      }
    Qed.

    Lemma eval_select_err_ub_oom_to_itree :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E}
        cnd x y,
        ((@concretize_uvalue (itree E) _ _ _ _ x) ≈
           match concretize_uvalue x with
           | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
               match m with
               | inl (OOM_message x) => raiseOOM x
               | inr (inl (UB_message x)) => raiseUB x
               | inr (inr (inl (ERR_message x))) => raise x
               | inr (inr (inr x)) => ret x
               end
           end) ->
        ((@concretize_uvalue (itree E) _ _ _ _ y) ≈
           match concretize_uvalue y with
           | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
               match m with
               | inl (OOM_message x) => raiseOOM x
               | inr (inl (UB_message x)) => raiseUB x
               | inr (inr (inl (ERR_message x))) => raise x
               | inr (inr (inr x)) => ret x
               end
           end) ->
        eval_select (itree E) (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
          (itree E) (fun (A : Type) (x : itree E A) => x) cnd x y ≈
          match
            (eval_select (err_ub_oom_T ident)
               (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
               (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) cnd x y)
          with
          | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
              match m with
              | inl (OOM_message x) => raiseOOM x
              | inr (inl (UB_message x)) => raiseUB x
              | inr (inr (inl (ERR_message x))) => raise x
              | inr (inr (inr x)) => ret x
              end
          end.
    Proof.
      intros E H H0 H1 cnd x y X Y.
      destruct cnd; try reflexivity.
      - (* i1 *)
        repeat rewrite eval_select_equation.
        break_match; eauto.
      - (* Vector *)
        setoid_rewrite eval_select_equation.
        cbn.
        setoid_rewrite X.
        setoid_rewrite Y.
        cbn.
        unfold concretize_uvalue.
        remember (concretize_uvalueM (err_ub_oom_T ident)
                    (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
                    (err_ub_oom_T ident) (fun (A : Type) (x0 : err_ub_oom_T ident A) => x0) x) as xr.
        remember (concretize_uvalueM (err_ub_oom_T ident)
                    (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
                    (err_ub_oom_T ident) (fun (A : Type) (x0 : err_ub_oom_T ident A) => x0) y) as yr.

        destruct_err_ub_oom xr; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        destruct_err_ub_oom yr; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        destruct xr0; try reflexivity.
        destruct yr0; try reflexivity.

        setoid_rewrite eval_select_loop_err_ub_oom_to_itree.

        remember ((fix loop (conds xs ys : list dvalue) {struct conds} : err_ub_oom (list dvalue) :=
         match conds with
         | [] =>
             match xs with
             | [] =>
                 fun ys0 : list dvalue =>
                 match ys0 with
                 | [] => ret []
                 | _ :: _ =>
                     raise_error "concretize_uvalueM: ill-typed vector select, length mismatch."
                 end
             | _ :: _ =>
                 fun _ : list dvalue =>
                 raise_error "concretize_uvalueM: ill-typed vector select, length mismatch."
             end ys
         | c :: conds0 =>
             match xs with
             | [] => raise_error "concretize_uvalueM: ill-typed vector select, length mismatch."
             | x0 :: xs0 =>
                 match ys with
                 | [] => raise_error "concretize_uvalueM: ill-typed vector select, length mismatch."
                 | y0 :: ys0 =>
                     selected <-
                     match c with
                     | DVALUE_I1 i =>
                         if (VellvmIntegers.Int1.unsigned i =? 1)%Z then ret x0 else ret y0
                     | DVALUE_Poison t => ret (DVALUE_Poison t)
                     | _ =>
                         raise_error
                           "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1."
                     end;; rest <- loop conds0 xs0 ys0;; ret (selected :: rest)
                 end
             end
         end) elts elts0 elts1) as r.
        setoid_rewrite <- Heqr.
        destruct_err_ub_oom r; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.
    Qed.

    Lemma concretize_uvalue_bytes_helper_err_ub_oom_to_itree :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E}
        uvs acc
        (IH : forall (u : uvalue),
            Exists (uvalue_subterm u) uvs ->
            (@concretize_uvalue (itree E) _ _ _ _ u) ≈
              match concretize_uvalue u with
              | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
                  match m with
                  | inl (OOM_message x) => raiseOOM x
                  | inr (inl (UB_message x)) => raiseUB x
                  | inr (inr (inl (ERR_message x))) => raise x
                  | inr (inr (inr x)) => ret x
                  end
              end),
        CONCBASE.concretize_uvalue_bytes_helper (itree E)
        (fun dt0 : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt0))
        (itree E) (fun (A : Type) (x : itree E A) => x) acc uvs ≈
        match
          CONCBASE.concretize_uvalue_bytes_helper err_ub_oom
            (fun dt0 : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt0))
            _ (fun (A : Type) x => x) acc uvs
        with
        | OOM_unERR_UB_OOM x => raiseOOM x
        | UB_unERR_UB_OOM x => raiseUB x
        | ERR_unERR_UB_OOM x => raise x
        | success_unERR_UB_OOM x => ret x
        end.
    Proof.
      intros E H H0 H1 uvs.
      induction uvs; intros acc IH; try reflexivity.
      setoid_rewrite CONCBASE.concretize_uvalue_bytes_helper_equation.
      destruct a; try reflexivity.
      break_match.
      - cbn.
        setoid_rewrite IHuvs.
          match goal with
          | [ |- context [ match ?X with _ => _ end ] ] =>
              remember X
          end.
          destruct_err_ub_oom e; cbn;
            repeat setoid_rewrite Raise.raiseOOM_bind_itree;
            repeat setoid_rewrite Raise.raiseUB_bind_itree;
            repeat setoid_rewrite Raise.raise_bind_itree;
            repeat rewrite bind_ret_l; try reflexivity.
          eauto.
      - cbn.
        setoid_rewrite IHuvs; eauto.
        setoid_rewrite IH; eauto.
        2: repeat constructor.

        unfold concretize_uvalue.
        match goal with
        | [ |- context [ match ?X with _ => _ end ] ] =>
            remember X
        end.
        setoid_rewrite <- Heqe.

        destruct_err_ub_oom e; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        match goal with
        | [ |- context [ match ?X with _ => _ end ] ] =>
            remember X
        end.

        destruct_err_ub_oom e1; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.
    Qed.

    (* TODO: Move this and use this *)
    (* TODO: this is duplicated *)
    Ltac destruct_err_oom_poison x :=
      destruct x as [[[[[?err_x | ?x] | ?oom_x] | ?poison_x]]] eqn:?Hx.

    Lemma handle_poison_and_oom_dvalue_bytes_to_dvalue_err_ub_oom_to_itree :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E}
        dvbs dt,
        @ErrOomPoison.ErrOOMPoison_handle_poison_and_oom (itree E) _ _ _ _ DVALUE_Poison
          (DVALUE_BYTES.dvalue_bytes_to_dvalue dvbs dt) ≈
          match @ErrOomPoison.ErrOOMPoison_handle_poison_and_oom _ _ _ _ _ DVALUE_Poison
                  (DVALUE_BYTES.dvalue_bytes_to_dvalue dvbs dt) with
          | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
              match m with
              | inl (OOM_message x) => raiseOOM x
              | inr (inl (UB_message x)) => raiseUB x
              | inr (inr (inl (ERR_message x))) => raise x
              | inr (inr (inr x)) => ret x
              end
          end.
    Proof.
      intros E H H0 H1 dvbs dt.
      remember (DVALUE_BYTES.dvalue_bytes_to_dvalue dvbs dt).

      destruct_err_oom_poison y; cbn;
        repeat setoid_rewrite Raise.raiseOOM_bind_itree;
        repeat setoid_rewrite Raise.raiseUB_bind_itree;
        repeat setoid_rewrite Raise.raise_bind_itree;
        repeat rewrite bind_ret_l; try reflexivity.

      destruct err_x; reflexivity.
    Qed.

    Lemma map_monad_concretize_uvalueM_err_ub_oom_to_itree :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E}
        idxs
        (IH : forall (u : uvalue),
            Exists (uvalue_subterm u) idxs ->
            (@concretize_uvalue (itree E) _ _ _ _ u) ≈
              match concretize_uvalue u with
              | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
                  match m with
                  | inl (OOM_message x) => raiseOOM x
                  | inr (inl (UB_message x)) => raiseUB x
                  | inr (inr (inl (ERR_message x))) => raise x
                  | inr (inr (inr x)) => ret x
                  end
              end),
        (map_monad
           (concretize_uvalueM (itree E)
              (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt)) 
              (itree E) (fun (A : Type) (x : itree E A) => x)) idxs) ≈
          match
            map_monad
              (concretize_uvalueM (err_ub_oom_T ident)
                 (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
                 (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x)) idxs
          with
          | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
              match m with
              | inl (OOM_message x) => raiseOOM x
              | inr (inl (UB_message x)) => raiseUB x
              | inr (inr (inl (ERR_message x))) => raise x
              | inr (inr (inr x)) => ret x
              end
          end.
    Proof.
      intros E H H0 H1 idxs.
      induction idxs; intros IH; try reflexivity.

      setoid_rewrite map_monad_unfold.
      setoid_rewrite (IH a).
      2: {
        constructor.
        apply rt_refl.
      }

      unfold concretize_uvalue.

      match goal with
      | [ |- context [ match ?X with _ => _ end ] ] =>
          remember X
      end.

      destruct_err_ub_oom e; cbn;
        repeat setoid_rewrite Raise.raiseOOM_bind_itree;
        repeat setoid_rewrite Raise.raiseUB_bind_itree;
        repeat setoid_rewrite Raise.raise_bind_itree;
        repeat rewrite bind_ret_l; try reflexivity.

      rewrite IHidxs.

      match goal with
      | [ |- context [ match ?X with _ => _ end ] ] =>
          remember X
      end.

      destruct_err_ub_oom e1; cbn;
        repeat setoid_rewrite Raise.raiseOOM_bind_itree;
        repeat setoid_rewrite Raise.raiseUB_bind_itree;
        repeat setoid_rewrite Raise.raise_bind_itree;
        repeat rewrite bind_ret_l; try reflexivity.
      auto.
    Qed.

    Lemma concretize_uvalue_err_ub_oom_to_itree :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E} u,
        (@concretize_uvalue (itree E) _ _ _ _ u) ≈
        match concretize_uvalue u with
        | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
            match m with
            | inl (OOM_message x) => raiseOOM x
            | inr (inl (UB_message x)) => raiseUB x
            | inr (inr (inl (ERR_message x))) => raise x
            | inr (inr (inr x)) => ret x
            end
        end.
    Proof using.
      intros E OOM FAIL UB.
      induction u using uvalue_strong_ind; unfold concretize_uvalue at 2; rewrite concretize_uvalueM_equation;
        try solve [unfold concretize_uvalue; rewrite concretize_uvalueM_equation; reflexivity].
      { unfold concretize_uvalue; rewrite concretize_uvalueM_equation.
        destruct (default_dvalue_of_dtyp t); cbn in *; reflexivity.
      }

      destruct u; try reflexivity.
      10: { (* Conversion *)
        idtac.
        unfold concretize_uvalue.
        rewrite concretize_uvalueM_equation.
        unfold concretize_uvalue in H.
        specialize (H u).
        forward H.
        repeat constructor.

        remember (concretize_uvalueM (err_ub_oom_T ident)
           (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
           (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) u) as ur.
        destruct_err_ub_oom ur; cbn;
          rewrite H; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        break_match; cbn; try reflexivity.
        - break_match; cbn; try reflexivity.
        - break_match; cbn; try reflexivity.
          break_match; cbn; try reflexivity.
          repeat (break_match; cbn; try reflexivity).

          unfold lift_OOM.
          repeat (break_match; cbn; try reflexivity);
            repeat setoid_rewrite Raise.raiseOOM_bind_itree;
            repeat setoid_rewrite Raise.raiseUB_bind_itree;
            repeat setoid_rewrite Raise.raise_bind_itree;
            repeat rewrite bind_ret_l; try reflexivity.
      }

      16: { (* ConcatBytes *)
        unfold concretize_uvalue.
        rewrite concretize_uvalueM_equation.
        break_match.
        - break_match.
          + cbn.
            pose proof Heqo.
            apply ByteM.all_extract_bytes_from_uvalue_success_inv in H0 as (?&?&?);
              subst.
            apply H.
            eapply uvalue_concat_bytes_strict_subterm; auto.
            constructor.
            constructor.
            constructor.
          + cbn.
            setoid_rewrite concretize_uvalue_bytes_helper_err_ub_oom_to_itree.
            unfold CONCBASE.concretize_uvalue_bytes_helper.
            cbn.
            match goal with
            | [ |- context [ match ?X with _ => _ end ] ] =>
                remember X
            end.
            setoid_rewrite <- Heqe.
            destruct_err_ub_oom e;
              cbn;
              repeat setoid_rewrite Raise.raiseOOM_bind_itree;
              repeat setoid_rewrite Raise.raiseUB_bind_itree;
              repeat setoid_rewrite Raise.raise_bind_itree;
              repeat rewrite bind_ret_l; try reflexivity.

            rewrite handle_poison_and_oom_dvalue_bytes_to_dvalue_err_ub_oom_to_itree.
            remember (ErrOomPoison.ErrOOMPoison_handle_poison_and_oom DVALUE_Poison
                        (DVALUE_BYTES.dvalue_bytes_to_dvalue e0 dt)).
            destruct_err_ub_oom y;
              cbn;
              repeat setoid_rewrite Raise.raiseOOM_bind_itree;
              repeat setoid_rewrite Raise.raiseUB_bind_itree;
              repeat setoid_rewrite Raise.raise_bind_itree;
              repeat rewrite bind_ret_l; try reflexivity.

            intros u H0.
            apply H.
            eapply uvalue_concat_bytes_strict_subterm; auto.
        - cbn.
          setoid_rewrite concretize_uvalue_bytes_helper_err_ub_oom_to_itree.
          unfold CONCBASE.concretize_uvalue_bytes_helper.
          cbn.
          match goal with
          | [ |- context [ match ?X with _ => _ end ] ] =>
              remember X
          end.
          setoid_rewrite <- Heqe.
          destruct_err_ub_oom e;
            cbn;
            repeat setoid_rewrite Raise.raiseOOM_bind_itree;
            repeat setoid_rewrite Raise.raiseUB_bind_itree;
            repeat setoid_rewrite Raise.raise_bind_itree;
            repeat rewrite bind_ret_l; try reflexivity.

          rewrite handle_poison_and_oom_dvalue_bytes_to_dvalue_err_ub_oom_to_itree.
          remember (ErrOomPoison.ErrOOMPoison_handle_poison_and_oom DVALUE_Poison
                      (DVALUE_BYTES.dvalue_bytes_to_dvalue e0 dt)).
          destruct_err_ub_oom y;
            cbn;
            repeat setoid_rewrite Raise.raiseOOM_bind_itree;
            repeat setoid_rewrite Raise.raiseUB_bind_itree;
            repeat setoid_rewrite Raise.raise_bind_itree;
            repeat rewrite bind_ret_l; try reflexivity.

          intros u H0.
          apply H.
          eapply uvalue_concat_bytes_strict_subterm; auto.
      }

      - cbn.
        destruct (default_dvalue_of_dtyp t); reflexivity.
      - (* Struct *)
        unfold concretize_uvalue.
        rewrite concretize_uvalueM_equation.
        induction fields.
        + cbn.
          rewrite bind_ret_l.
          reflexivity.
        + repeat rewrite map_monad_unfold.
          pose proof (H a).
          forward H0.
          repeat constructor.
          cbn.
          rewrite H0.
          unfold concretize_uvalue.
          remember (concretize_uvalueM (err_ub_oom_T ident)
           (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
           (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) a) as conca.
          destruct_err_ub_oom conca;
            cbn;
            repeat setoid_rewrite Raise.raiseOOM_bind_itree;
            repeat setoid_rewrite Raise.raiseUB_bind_itree;
            repeat setoid_rewrite Raise.raise_bind_itree;
            repeat rewrite bind_ret_l; try reflexivity.
          
          forward IHfields.
          { clear - H.
            intros u H0.
            eapply H.
            eapply uvalue_strict_subterm_struct; eauto.
          }

          remember (map_monad
                      (concretize_uvalueM (err_ub_oom_T ident)
                         (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
                         (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x)) fields) as m.
          destruct_err_ub_oom m; cbn in IHfields; cbn;
            setoid_rewrite <- Heqm; cbn.
            -- pose proof Raise.raiseOOM_map_itree_inv E (list dvalue) _ (fun x : list dvalue => (DVALUE_Struct x)) _ _ IHfields.

               rewrite H1.
               repeat setoid_rewrite Raise.raiseOOM_bind_itree.
               reflexivity.
            -- pose proof Raise.raiseUB_map_itree_inv E (list dvalue) _ (fun x : list dvalue => (DVALUE_Struct x)) _ _ IHfields.

               rewrite H1.
               repeat setoid_rewrite Raise.raiseUB_bind_itree.
               reflexivity.
            -- pose proof Raise.raise_map_itree_inv E (list dvalue) _ (fun x : list dvalue => (DVALUE_Struct x)) _ _ IHfields.

               rewrite H1.
               repeat setoid_rewrite Raise.raise_bind_itree.
               reflexivity.
            -- eapply eutt_inv_bind_ret in IHfields.
               destruct IHfields as (?&?&?).
               rewrite H1.
               repeat rewrite bind_ret_l.
               eapply eutt_inv_Ret in H2; inv H2.
               reflexivity.
      - (* Packed Struct *)
        unfold concretize_uvalue.
        rewrite concretize_uvalueM_equation.
        induction fields.
        + cbn.
          rewrite bind_ret_l.
          reflexivity.
        + repeat rewrite map_monad_unfold.
          pose proof (H a).
          forward H0.
          repeat constructor.
          cbn.
          rewrite H0.
          unfold concretize_uvalue.
          remember (concretize_uvalueM (err_ub_oom_T ident)
           (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
           (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) a) as conca.
          destruct_err_ub_oom conca;
            cbn;
            repeat setoid_rewrite Raise.raiseOOM_bind_itree;
            repeat setoid_rewrite Raise.raiseUB_bind_itree;
            repeat setoid_rewrite Raise.raise_bind_itree;
            repeat rewrite bind_ret_l; try reflexivity.
          
          forward IHfields.
          { clear - H.
            intros u H0.
            eapply H.
            eapply uvalue_strict_subterm_packed_struct; eauto.
          }

          remember (map_monad
                      (concretize_uvalueM (err_ub_oom_T ident)
                         (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
                         (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x)) fields) as m.
          destruct_err_ub_oom m; cbn in IHfields; cbn;
            setoid_rewrite <- Heqm; cbn.
            -- pose proof Raise.raiseOOM_map_itree_inv E (list dvalue) _ (fun x : list dvalue => (DVALUE_Packed_struct x)) _ _ IHfields.

               rewrite H1.
               repeat setoid_rewrite Raise.raiseOOM_bind_itree.
               reflexivity.
            -- pose proof Raise.raiseUB_map_itree_inv E (list dvalue) _ (fun x : list dvalue => (DVALUE_Packed_struct x)) _ _ IHfields.

               rewrite H1.
               repeat setoid_rewrite Raise.raiseUB_bind_itree.
               reflexivity.
            -- pose proof Raise.raise_map_itree_inv E (list dvalue) _ (fun x : list dvalue => (DVALUE_Packed_struct x)) _ _ IHfields.

               rewrite H1.
               repeat setoid_rewrite Raise.raise_bind_itree.
               reflexivity.
            -- eapply eutt_inv_bind_ret in IHfields.
               destruct IHfields as (?&?&?).
               rewrite H1.
               repeat rewrite bind_ret_l.
               eapply eutt_inv_Ret in H2; inv H2.
               reflexivity.
      - (* Arrays *)
        unfold concretize_uvalue.
        rewrite concretize_uvalueM_equation.
        induction elts.
        + cbn.
          rewrite bind_ret_l.
          reflexivity.
        + repeat rewrite map_monad_unfold.
          pose proof (H a).
          forward H0.
          repeat constructor.
          cbn.
          rewrite H0.
          unfold concretize_uvalue.
          remember (concretize_uvalueM (err_ub_oom_T ident)
           (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
           (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) a) as conca.
          destruct_err_ub_oom conca; cbn.
          * repeat setoid_rewrite Raise.raiseOOM_bind_itree.
            reflexivity.
          * repeat setoid_rewrite Raise.raiseUB_bind_itree.
            reflexivity.
          * repeat setoid_rewrite Raise.raise_bind_itree.
            reflexivity.
          * rewrite bind_ret_l.
            forward IHelts.
            { clear - H.
              intros u H0.
              eapply H.
              eapply uvalue_strict_subterm_array; eauto.
            }

            remember (map_monad
                      (concretize_uvalueM (err_ub_oom_T ident)
                         (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
                         (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x)) elts) as m.
            destruct_err_ub_oom m; cbn in IHelts; cbn;
              setoid_rewrite <- Heqm; cbn.
            -- pose proof Raise.raiseOOM_map_itree_inv E (list dvalue) _ _ _ _ IHelts.

               rewrite H1.
               repeat setoid_rewrite Raise.raiseOOM_bind_itree.
               reflexivity.
            -- pose proof Raise.raiseUB_map_itree_inv E (list dvalue) _ _ _ _ IHelts.

               rewrite H1.
               repeat setoid_rewrite Raise.raiseUB_bind_itree.
               reflexivity.
            -- pose proof Raise.raise_map_itree_inv E (list dvalue) _ _ _ _ IHelts.

               rewrite H1.
               repeat setoid_rewrite Raise.raise_bind_itree.
               reflexivity.
            -- eapply eutt_inv_bind_ret in IHelts.
               destruct IHelts as (?&?&?).
               rewrite H1.
               repeat rewrite bind_ret_l.
               eapply eutt_inv_Ret in H2; inv H2.
               reflexivity.
      - (* Vectors *)
        unfold concretize_uvalue.
        rewrite concretize_uvalueM_equation.
        induction elts.
        + cbn.
          rewrite bind_ret_l.
          reflexivity.
        + repeat rewrite map_monad_unfold.
          pose proof (H a).
          forward H0.
          repeat constructor.
          cbn.
          rewrite H0.
          unfold concretize_uvalue.
          remember (concretize_uvalueM (err_ub_oom_T ident)
           (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
           (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) a) as conca.
          destruct_err_ub_oom conca; cbn.
          * repeat setoid_rewrite Raise.raiseOOM_bind_itree.
            reflexivity.
          * repeat setoid_rewrite Raise.raiseUB_bind_itree.
            reflexivity.
          * repeat setoid_rewrite Raise.raise_bind_itree.
            reflexivity.
          * rewrite bind_ret_l.
            forward IHelts.
            { clear - H.
              intros u H0.
              eapply H.
              eapply uvalue_strict_subterm_vector; eauto.
            }

            remember (map_monad
                      (concretize_uvalueM (err_ub_oom_T ident)
                         (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
                         (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x)) elts) as m.
            destruct_err_ub_oom m; cbn in IHelts; cbn;
              setoid_rewrite <- Heqm; cbn.
            -- pose proof Raise.raiseOOM_map_itree_inv E (list dvalue) _ _ _ _ IHelts.

               rewrite H1.
               repeat setoid_rewrite Raise.raiseOOM_bind_itree.
               reflexivity.
            -- pose proof Raise.raiseUB_map_itree_inv E (list dvalue) _ _ _ _ IHelts.

               rewrite H1.
               repeat setoid_rewrite Raise.raiseUB_bind_itree.
               reflexivity.
            -- pose proof Raise.raise_map_itree_inv E (list dvalue) _ _ _ _ IHelts.

               rewrite H1.
               repeat setoid_rewrite Raise.raise_bind_itree.
               reflexivity.
            -- eapply eutt_inv_bind_ret in IHelts.
               destruct IHelts as (?&?&?).
               rewrite H1.
               repeat rewrite bind_ret_l.
               eapply eutt_inv_Ret in H2; inv H2.
               reflexivity.
      - (* IBinop *)
        unfold concretize_uvalue.
        rewrite concretize_uvalueM_equation.
        cbn.
        setoid_rewrite H.
        2-3: repeat constructor.
        unfold concretize_uvalue.
        remember (concretize_uvalueM (err_ub_oom_T ident)
        (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
        (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) u1) as u1r.

        destruct_err_ub_oom u1r; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        remember (concretize_uvalueM (err_ub_oom_T ident)
        (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
        (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) u2) as u2r.

        destruct_err_ub_oom u2r; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        rewrite eval_iop_err_ub_oom_to_itree.
        cbn.
        remember (eval_iop iop u1r0 u2r0).
        destruct_err_ub_oom y; cbn; reflexivity.
      - (* ICmp *)
        unfold concretize_uvalue.
        rewrite concretize_uvalueM_equation.
        cbn.
        setoid_rewrite H.
        2-3: repeat constructor.
        unfold concretize_uvalue.
        remember (concretize_uvalueM (err_ub_oom_T ident)
        (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
        (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) u1) as u1r.

        destruct_err_ub_oom u1r; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        remember (concretize_uvalueM (err_ub_oom_T ident)
        (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
        (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) u2) as u2r.

        destruct_err_ub_oom u2r; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        rewrite eval_icmp_err_ub_oom_to_itree.
        cbn.
        remember (eval_icmp cmp u1r0 u2r0).
        destruct_err_ub_oom y; cbn; reflexivity.
      - (* FBinop *)
        unfold concretize_uvalue.
        rewrite concretize_uvalueM_equation.
        cbn.
        setoid_rewrite H.
        2-3: repeat constructor.
        unfold concretize_uvalue.
        remember (concretize_uvalueM (err_ub_oom_T ident)
        (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
        (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) u1) as u1r.

        destruct_err_ub_oom u1r; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        remember (concretize_uvalueM (err_ub_oom_T ident)
        (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
        (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) u2) as u2r.

        destruct_err_ub_oom u2r; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        rewrite eval_fop_err_ub_oom_to_itree.
        cbn.
        remember (eval_fop fop u1r0 u2r0).
        destruct_err_ub_oom y; cbn; reflexivity.
      - (* FCmp *)
        unfold concretize_uvalue.
        rewrite concretize_uvalueM_equation.
        cbn.
        setoid_rewrite H.
        2-3: repeat constructor.
        unfold concretize_uvalue.
        remember (concretize_uvalueM (err_ub_oom_T ident)
        (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
        (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) u1) as u1r.

        destruct_err_ub_oom u1r; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        remember (concretize_uvalueM (err_ub_oom_T ident)
        (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
        (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) u2) as u2r.

        destruct_err_ub_oom u2r; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        rewrite eval_fcmp_err_ub_oom_to_itree.
        cbn.
        remember (eval_fcmp cmp u1r0 u2r0).
        destruct_err_ub_oom y; cbn; reflexivity.
      - (* GEP *)
        unfold concretize_uvalue.
        rewrite concretize_uvalueM_equation.
        cbn.
        setoid_rewrite H.
        2: repeat constructor.
        unfold concretize_uvalue.
        remember (concretize_uvalueM (err_ub_oom_T ident)
        (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
        (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) u) as ur.

        destruct_err_ub_oom ur; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        rewrite map_monad_concretize_uvalueM_err_ub_oom_to_itree.

        match goal with
        | [ |- context [ match ?X with _ => _ end ] ] =>
            remember X
        end.

        destruct_err_ub_oom e; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        2: {
          intros u0 H0.
          eapply H.
          eapply uvalue_getelementptr_strict_subterm; auto.
        }

        match goal with
        | [ |- context [ match ?X with _ => _ end ] ] =>
            remember X
        end.

        destruct s; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        destruct o; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.
      - (* ExtractElement *)
        unfold concretize_uvalue.
        rewrite concretize_uvalueM_equation.
        cbn.
        setoid_rewrite H.
        2-3: repeat constructor.
        unfold concretize_uvalue.
        remember (concretize_uvalueM (err_ub_oom_T ident)
        (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
        (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) u1) as u1r.

        destruct_err_ub_oom u1r; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        remember (concretize_uvalueM (err_ub_oom_T ident)
        (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
        (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) u2) as u2r.

        destruct_err_ub_oom u2r; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        break_match; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        rewrite index_into_vec_dv_err_ub_oom_to_itree.
        cbn.
        remember (index_into_vec_dv d u1r0 u2r0).
        destruct_err_ub_oom y; cbn; reflexivity.
      - (* InsertElement *)
        unfold concretize_uvalue.
        rewrite concretize_uvalueM_equation.
        cbn.
        setoid_rewrite H.
        2-4: repeat constructor.
        unfold concretize_uvalue.
        remember (concretize_uvalueM (err_ub_oom_T ident)
        (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
        (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) u1) as u1r.

        destruct_err_ub_oom u1r; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        remember (concretize_uvalueM (err_ub_oom_T ident)
        (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
        (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) u2) as u2r.

        remember (concretize_uvalueM (err_ub_oom_T ident)
        (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
        (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) u3) as u3r.

        destruct_err_ub_oom u3r; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        destruct_err_ub_oom u2r; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        rewrite insert_into_vec_dv_err_ub_oom_to_itree.
        cbn.
        remember (insert_into_vec_dv vec_typ u1r0 u2r0 u3r0).
        destruct_err_ub_oom y; cbn; reflexivity.
      - (* ExtractValue *)
        unfold concretize_uvalue.
        rewrite concretize_uvalueM_equation.
        cbn.
        setoid_rewrite H.
        2: repeat constructor.
        unfold concretize_uvalue.
        remember (concretize_uvalueM (err_ub_oom_T ident)
        (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
        (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) u) as ur.

        destruct_err_ub_oom ur; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        setoid_rewrite extract_value_loop_err_ub_oom_to_itree.
        remember ((fix loop (str : dvalue) (idxs0 : list int_ast) {struct idxs0} : err_ub_oom dvalue :=
                     match idxs0 with
                     | [] => ret str
                     | i :: tl => v <- index_into_str_dv str i;; loop v tl
                     end) ur0 idxs) as res.
        setoid_rewrite <- Heqres.
        destruct_err_ub_oom res; reflexivity.
      - (* InsertValue *)
        unfold concretize_uvalue.
        rewrite concretize_uvalueM_equation.
        cbn.
        setoid_rewrite H.
        2-3: repeat constructor.
        unfold concretize_uvalue.
        remember (concretize_uvalueM (err_ub_oom_T ident)
        (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
        (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) u1) as u1r.

        destruct_err_ub_oom u1r; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        remember (concretize_uvalueM (err_ub_oom_T ident)
        (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
        (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) u2) as u2r.

        destruct_err_ub_oom u2r; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        setoid_rewrite insert_value_loop_err_ub_oom_to_itree.
        remember ((fix loop (str : dvalue) (idxs0 : list int_ast) {struct idxs0} : err_ub_oom dvalue :=
                     match idxs0 with
                     | [] => raise_error "Index was not provided"
                     | [i] => v <- insert_into_str str u2r0 i;; ret v
                     | i :: (_ :: _) as tl =>
                         subfield <- index_into_str_dv str i;;
                         modified_subfield <- loop subfield tl;; insert_into_str str modified_subfield i
                     end) u1r0 idxs).
        setoid_rewrite <- Heqe.
        destruct_err_ub_oom e; reflexivity.
      - (* Select *)
        unfold concretize_uvalue.
        rewrite concretize_uvalueM_equation.
        cbn.
        setoid_rewrite H.
        2: repeat constructor.
        unfold concretize_uvalue.
        remember (concretize_uvalueM (err_ub_oom_T ident)
        (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
        (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) u1) as u1r.

        destruct_err_ub_oom u1r; cbn;
          repeat setoid_rewrite Raise.raiseOOM_bind_itree;
          repeat setoid_rewrite Raise.raiseUB_bind_itree;
          repeat setoid_rewrite Raise.raise_bind_itree;
          repeat rewrite bind_ret_l; try reflexivity.

        remember (concretize_uvalueM (err_ub_oom_T ident)
        (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
        (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) u2) as u2r.

        remember (concretize_uvalueM (err_ub_oom_T ident)
        (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
        (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) u3) as u3r.

        destruct u1r0; try reflexivity.
        + break_match.
          setoid_rewrite H.
          subst.
          unfold concretize_uvalue.
          remember (concretize_uvalueM (err_ub_oom_T ident)
                    (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
                    (err_ub_oom_T ident) (fun (A : Type) (x0 : err_ub_oom_T ident A) => x0) u2).
          destruct_err_ub_oom e; reflexivity.
          repeat constructor.

          setoid_rewrite H.
          subst.
          unfold concretize_uvalue.
          remember (concretize_uvalueM (err_ub_oom_T ident)
                    (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt))
                    (err_ub_oom_T ident) (fun (A : Type) (x0 : err_ub_oom_T ident A) => x0) u3).
          destruct_err_ub_oom e; reflexivity.
          repeat constructor.
        + setoid_rewrite H.
          2-3: repeat constructor.

          unfold concretize_uvalue.
          subst.
          remember (concretize_uvalueM (err_ub_oom_T ident)
                      (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt)) 
                      (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) u2).
          destruct_err_ub_oom e; cbn;
            repeat setoid_rewrite Raise.raiseOOM_bind_itree;
            repeat setoid_rewrite Raise.raiseUB_bind_itree;
            repeat setoid_rewrite Raise.raise_bind_itree;
            repeat rewrite bind_ret_l; try reflexivity.

          remember (concretize_uvalueM (err_ub_oom_T ident)
                      (fun dt : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt)) 
                      (err_ub_oom_T ident) (fun (A : Type) (x : err_ub_oom_T ident A) => x) u3).
          destruct_err_ub_oom e1; cbn;
            repeat setoid_rewrite Raise.raiseOOM_bind_itree;
            repeat setoid_rewrite Raise.raiseUB_bind_itree;
            repeat setoid_rewrite Raise.raise_bind_itree;
            repeat rewrite bind_ret_l; try reflexivity.

          destruct e0; cbn;
            repeat setoid_rewrite Raise.raiseOOM_bind_itree;
            repeat setoid_rewrite Raise.raiseUB_bind_itree;
            repeat setoid_rewrite Raise.raise_bind_itree;
            repeat rewrite bind_ret_l; try reflexivity.

          destruct e2; cbn;
            repeat setoid_rewrite Raise.raiseOOM_bind_itree;
            repeat setoid_rewrite Raise.raiseUB_bind_itree;
            repeat setoid_rewrite Raise.raise_bind_itree;
            repeat rewrite bind_ret_l; try reflexivity.

          setoid_rewrite eval_select_loop_err_ub_oom_to_itree.
          match goal with
          | [ |- context [ match ?X with _ => _ end ] ] =>
              remember X
          end.

          setoid_rewrite <- Heqe0.
          destruct_err_ub_oom e0; cbn;
            repeat setoid_rewrite Raise.raiseOOM_bind_itree;
            repeat setoid_rewrite Raise.raiseUB_bind_itree;
            repeat setoid_rewrite Raise.raise_bind_itree;
            repeat rewrite bind_ret_l; try reflexivity.
    Qed.

    Lemma PickUvalue_handler_correct :
      forall E `{FailureE -< E} `{UBE -< E} `{OOME -< E},
        handler_correct (@PickUvalue_handler E _ _ _) concretize_picks.
    Proof using.
      unfold handler_correct.
      intros * EQ.
      destruct e as [uv | uv | uv];
        rewrite EQ.
      - destruct (Classical_Prop.classic (unique_prop uv)).
        + eapply PickUV_UniqueRet with (res := concretize_uvalue uv); eauto.
          apply concretize_u_concretize_uvalue.

          { cbn.
            unfold ITree.map.
            unfold lift_err_ub_oom_post_ret, lift_err_ub_oom_post.
            destruct ((concretize_uvalue uv) : err_ub_oom_T _ _) eqn: HU.
            repeat break_match.
            + unfold raiseOOM.
              apply eutt_clo_bind with (UU:=fun _ _ => True).
              setoid_rewrite concretize_uvalue_err_ub_oom_to_itree.
              rewrite HU. unfold raiseOOM.
              rewrite bind_trigger. unfold trigger.
              apply eqit_Vis. intros [].
              intros ? [].
            + unfold raiseUB.
              apply eutt_clo_bind with (UU:=fun _ _ => True).
              setoid_rewrite concretize_uvalue_err_ub_oom_to_itree.
              rewrite HU.
              unfold raiseUB. rewrite bind_trigger. unfold trigger.
              apply eqit_Vis. intros [].
              intros ? [].
            + unfold raise.
              apply eutt_clo_bind with (UU:=fun _ _ => True).
              setoid_rewrite concretize_uvalue_err_ub_oom_to_itree.
              rewrite HU. unfold raise.
              rewrite bind_trigger. unfold trigger.
              apply eqit_Vis. intros [].
              intros ? [].
            + cbn. unfold ITree.map.
              setoid_rewrite concretize_uvalue_err_ub_oom_to_itree.
              rewrite HU. setoid_rewrite bind_ret_l. reflexivity.
          }
        + eapply PickUV_UniqueUB; eauto.
      - destruct (Classical_Prop.classic (non_poison_prop uv)).
        + eapply PickUV_NonPoisonRet with (res := concretize_uvalue uv); eauto.
          eapply concretize_u_concretize_uvalue.

          { cbn.
            unfold ITree.map.
            unfold lift_err_ub_oom_post_ret, lift_err_ub_oom_post.
            destruct ((concretize_uvalue uv) : err_ub_oom_T _ _) eqn: HU.
            repeat break_match.
            + unfold raiseOOM.
              apply eutt_clo_bind with (UU:=fun _ _ => True).
              setoid_rewrite concretize_uvalue_err_ub_oom_to_itree.
              rewrite HU. unfold raiseOOM.
              rewrite bind_trigger. unfold trigger.
              apply eqit_Vis. intros [].
              intros ? [].
            + unfold raiseUB.
              apply eutt_clo_bind with (UU:=fun _ _ => True).
              setoid_rewrite concretize_uvalue_err_ub_oom_to_itree.
              rewrite HU.
              unfold raiseUB. rewrite bind_trigger. unfold trigger.
              apply eqit_Vis. intros [].
              intros ? [].
            + unfold raise.
              apply eutt_clo_bind with (UU:=fun _ _ => True).
              setoid_rewrite concretize_uvalue_err_ub_oom_to_itree.
              rewrite HU. unfold raise.
              rewrite bind_trigger. unfold trigger.
              apply eqit_Vis. intros [].
              intros ? [].
            + cbn. unfold ITree.map.
              setoid_rewrite concretize_uvalue_err_ub_oom_to_itree.
              rewrite HU. setoid_rewrite bind_ret_l. reflexivity.
          }
        + eapply PickUV_NonPoisonUB; eauto.
      - eapply PickUV_Ret with (res := concretize_uvalue uv); eauto.
        eapply concretize_u_concretize_uvalue.

       cbn.
        unfold ITree.map.
        unfold lift_err_ub_oom_post_ret, lift_err_ub_oom_post.
        destruct ((concretize_uvalue uv) : err_ub_oom_T _ _) eqn: HU.
        repeat break_match.
        + unfold raiseOOM.
          apply eutt_clo_bind with (UU:=fun _ _ => True).
          setoid_rewrite concretize_uvalue_err_ub_oom_to_itree.
          rewrite HU. unfold raiseOOM.
          rewrite bind_trigger. unfold trigger.
          apply eqit_Vis. intros [].
          intros ? [].
        + unfold raiseUB.
          apply eutt_clo_bind with (UU:=fun _ _ => True).
          setoid_rewrite concretize_uvalue_err_ub_oom_to_itree.
          rewrite HU.
          unfold raiseUB. rewrite bind_trigger. unfold trigger.
          apply eqit_Vis. intros [].
          intros ? [].
        + unfold raise.
          apply eutt_clo_bind with (UU:=fun _ _ => True).
          setoid_rewrite concretize_uvalue_err_ub_oom_to_itree.
          rewrite HU. unfold raise.
          rewrite bind_trigger. unfold trigger.
          apply eqit_Vis. intros [].
          intros ? [].
        + cbn. unfold ITree.map.
          setoid_rewrite concretize_uvalue_err_ub_oom_to_itree.
          rewrite HU. setoid_rewrite bind_ret_l. reflexivity.
    Qed.

    Lemma refine_undef
      : forall (E F:Type -> Type) T TT (HR: Reflexive TT)  `{UBE -< F} `{FailureE -< F} `{OOME -< F}
               (xs : PropT _ T),
        forall x, xs x -> model_undef TT xs (@exec_undef E F _ _ _ _ x).
    Proof using.
      intros E F T TT REL UB FAIL OOM xs x XS.
      unfold model_undef.
      unfold exec_undef.
      exists x; split; auto.
      apply interp_prop_oom_correct_exec; try typeclasses eauto;
        try reflexivity; auto.
      repeat intro.
      unfold case_, Case_sum1, case_sum1.
      destruct e as [ | [ | ]]; eauto.
       apply PickUvalue_handler_correct; eauto.
   Qed.

    (* TODO: probably a bad name... model_UB_exec is just... id *)
    Lemma refine_UB
      : forall (E F G : Type -> Type) T
          (xs : PropT (E +' F +' UBE +' G) T) x,
        xs x ->
        model_UB xs x.
    Proof using.
      intros E F G T xs x XS.
      red.
      left; auto.
    Qed.

    Definition build_singleton {A} : A -> A -> Prop := eq.


    Lemma MemMonad_valid_state_initial :
      forall st,
        MemExecM.MemMonad_valid_state initial_memory_state st.
    Proof.
      intros st.
      red.
      intros sid' H.
      repeat red in H.
      destruct H as (?&?&?&?).
      pose proof initial_memory_state_correct.
      eapply initial_memory_read_ub in H; eauto; contradiction.
    Qed.

    (**
   Theorem 5.8: We prove that the interpreter belongs to the model.
     *)
    Theorem interpreter_sound: forall p,
        refine_L6 (model p) (build_singleton (interpreter p)).
    Proof using.
      intros p.
      intros ? [].
      exists (interpreter p).
      split.
      - apply refine_UB.
        unfold interpreter.
        unfold interpreter_gen.
        apply refine_undef; auto.
        apply interp_memory_correct.
        apply MemMonad_valid_state_initial.
      - apply eutt_refine_oom_h; try typeclasses eauto.
        reflexivity.
    Qed.

  End REFINEMENT.

  (**
   Each interpreter commutes with [bind] and [ret].
   **)

  (** We hence can also commute them at the various levels of interpretation *)

  Lemma interp2_bind:
    forall {R S} (t: itree L0 R) (k: R -> itree L0 S) s1 s2,
      ℑs2 (ITree.bind t k) s1 s2 ≈
          (ITree.bind (ℑs2 t s1 s2) (fun '(s1',(s2',x)) => ℑs2 (k x) s2' s1')).
  Proof using.
    intros.
    unfold ℑs2.
    rewrite interp_intrinsics_bind, interp_global_bind, interp_local_stack_bind.
    apply eutt_clo_bind with (UU := Logic.eq); [reflexivity | intros ? (? & ? & ?) ->; reflexivity].
  Qed.

  Lemma interp2_ret:
    forall (R : Type) s1 s2 (x : R),
      ℑs2 (Ret x) s1 s2 ≈ Ret (s2, (s1, x)).
  Proof using.
    intros; unfold ℑs2.
    rewrite interp_intrinsics_ret, interp_global_ret, interp_local_stack_ret; reflexivity.
  Qed.

  Definition interp_cfg {R: Type} (trace: itree instr_E R) g l sid m :=
    let uvalue_trace   := interp_intrinsics trace in
    let L1_trace       := interp_global uvalue_trace g in
    let L2_trace       := interp_local L1_trace l in
    let L3_trace       := interp_memory_spec eq L2_trace sid m in
    let L4_trace       := model_undef eq L3_trace in
    L4_trace.

  Definition model_to_L4_cfg (prog: cfg dtyp) :=
    let trace := denote_cfg prog in
    interp_cfg trace [] [] 0 initial_memory_state.

  Definition refine_cfg_ret: relation (PropT L5 (MemState * (local_env * (global_env * uvalue)))) :=
    fun ts ts' => forall t, ts t -> exists t', ts' t' /\ eutt  (TT × (TT × (TT × refine_uvalue))) t t'.

End TopLevelRefinements.

Module Make (IS : InterpreterStack) (TOP : LLVMTopLevel IS) : TopLevelRefinements IS TOP.
  Include TopLevelRefinements IS TOP.
End Make.

Module TopLevelRefinementsBigIntptr := Make InterpreterStackBigIntptr TopLevelBigIntptr.
Module TopLevelRefinements64BitIntptr := Make InterpreterStack64BitIntptr TopLevel64BitIntptr.
