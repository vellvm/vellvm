(* begin hide *)
From ITree Require Import
     ITree
     ITreeFacts
     Basics.HeterogeneousRelations
     Events.State
     Events.StateFacts
     InterpFacts
     KTreeFacts
     Eq.Eq.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics
     Theory.Refinement
     Theory.InterpreterMCFG
     Theory.InterpreterCFG.

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
  Proof. firstorder. Qed.

  Lemma subrelation_prod_left :
    forall A B (R R' : relation A) (R2 : relation B), subrelation R R' -> subrelation (R × R2) (R' × R2).
  Proof.
    intros A B R R' R2 H.
    unfold subrelation in *.
    intros x y HRR2.
    inversion HRR2; firstorder.
  Qed.

  Lemma eutt_tt_to_eq_prod :
    forall X R (RR : relation R) E (t1 t2 : itree E (X * R)),
      eutt (eq × RR) t1 t2 -> eutt (TT × RR) t1 t2.
  Proof.
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
  Proof.
    intros; eapply alist_find_eq_dec.
  Qed.


  #[global] Instance interp_state_proper {T E F S}
   (h: forall T : Type, E T -> Monads.stateT S (itree F) T)
    : Proper (eutt Logic.eq ==> Monad.eq1) (State.interp_state h (T := T)).
  Proof.
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
  Proof.
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
    Proof.
      intros t1 t2 g REF.
      apply eutt_tt_to_eq_prod, eutt_interp_state; auto.
    Qed.

    Lemma refine_12 : forall t1 t2 l,
        refine_L1 t1 t2 -> refine_L2 (interp_local_stack t1 l) (interp_local_stack t2 l).
    Proof.
      intros t1 t2 l REF.
      apply eutt_tt_to_eq_prod, eutt_interp_state; auto.
    Qed.

    Lemma refine_23 : forall t1 t2 sid m,
        refine_L2 t1 t2 -> refine_L3 (interp_memory_prop refine_res2 t1 sid m) (interp_memory_prop refine_res2 t2 sid m).
    Proof.
      intros t1 t2 sid ms REF t Ht.
      exists t; split.
      - unfold L3 in *.
        unfold refine_L2 in *.
        eapply interp_prop_Proper_eq in Ht; try typeclasses eauto; eauto.
        Unshelve.
      - reflexivity.
    Qed.

    (* Things are different for L4 and L5: we get into the [Prop] monad. *)
    Lemma refine_34 : forall t1 t2,
        refine_L3 t1 t2 -> refine_L4 (model_undef refine_res3 t1) (model_undef refine_res3 t2).
    Proof.
      intros t1 t2 REF t Ht.
      exists t; split.
      - unfold model_undef in *.
        unfold refine_L3 in *.
        destruct Ht as [t_pre [T2 MODEL]].
        specialize (REF _ T2).
        destruct REF as [t_pre1 [T1 EUTT]].
        exists t_pre1; split; auto.
        eapply interp_prop_Proper_eq in MODEL; try typeclasses eauto.
        + unfold model_undef_h.
          apply MODEL.
        + assumption.
        + reflexivity.
      - reflexivity.
    Qed.

    Lemma refine_45 : forall Pt1 Pt2,
        refine_L4 Pt1 Pt2 -> refine_L5 (model_UB Pt1) (model_UB Pt2).
    Proof.
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
    Proof.
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
    Proof.
      intros p1 p2 HR;
        solve_refine.
    Qed.

    Lemma refine_mcfg_L2_correct: forall p1 p2,
        refine_mcfg_L2 p1 p2 -> refine_mcfg p1 p2.
    Proof.
      intros p1 p2 HR;
        solve_refine.
    Qed.

    Lemma refine_mcfg_L3_correct: forall p1 p2,
        refine_mcfg_L3 p1 p2 -> refine_mcfg p1 p2.
    Proof.
      intros p1 p2 HR;
        solve_refine.
    Qed.

    Lemma refine_mcfg_L4_correct: forall p1 p2,
        refine_mcfg_L4 p1 p2 -> refine_mcfg p1 p2.
    Proof.
      intros p1 p2 HR;
        solve_refine.
    Qed.

    Lemma refine_mcfg_L5_correct: forall p1 p2,
        refine_mcfg_L5 p1 p2 -> refine_mcfg p1 p2.
    Proof.
      intros p1 p2 HR;
        solve_refine.
    Qed.

    Lemma refine_mcfg_L6_correct: forall p1 p2,
        refine_mcfg_L6 p1 p2 -> refine_mcfg p1 p2.
    Proof.
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

    From Coq Require Import Program.Equality.

    #[global] Instance Proper_E_trigger_prop E F T : Proper (eq ==> (eutt eq) ==> iff) (@E_trigger_prop E F T).
    Proof.
      repeat red; intros.
      split; intros; unfold E_trigger_prop in *.
      - rewrite <- H0. rewrite <- H. assumption.
      - rewrite H0. rewrite H. assumption.
    Qed.
    
    #[global] Instance Proper_F_trigger_prop E F T : Proper (eq ==> (eutt eq) ==> iff) (@F_trigger_prop E F T).
    Proof.
      repeat red; intros.
      split; intros; unfold F_trigger_prop in *.
      - rewrite <- H0. rewrite <- H. assumption.
      - rewrite H0. rewrite H. assumption.
    Qed.

    #[global] Instance ProperPickUvalue_handler E T `{FailureE -< E} `{UBE -< E} `{OOME -< E} :  Proper (eq ==> (eutt eq) ==> iff) (@PickUvalue_handler E _ _ _ T).
    Proof.
      repeat red; intros.
      split; intros.
      - inversion H4.
        + dependent destruction H5.
          apply inj_pair2 in H8.
          subst.
          apply PickUV_UB. assumption.
        + dependent destruction H5.
          apply inj_pair2 in H8.
          apply inj_pair2 in H10.
          subst.
          eapply PickUV_Ret.
          apply Conc.
          rewrite <- H3. apply H7.
      - inversion H4.
        + dependent destruction H5.
          apply inj_pair2 in H8.
          subst.
          apply PickUV_UB. assumption.
        + dependent destruction H5.
          apply inj_pair2 in H8.
          apply inj_pair2 in H10.
          subst.
          eapply PickUV_Ret.
          apply Conc.
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
    Proof.
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
    Proof.
      intros E OOM FAIL UB.
      induction u; unfold concretize_uvalue at 2; rewrite concretize_uvalueM_equation; 
        try solve [unfold concretize_uvalue; rewrite concretize_uvalueM_equation; reflexivity].
      - unfold concretize_uvalue; rewrite concretize_uvalueM_equation.
        destruct (default_dvalue_of_dtyp t); cbn in *; reflexivity.
      - 
(*        
        + simpl.
          unfold concretize_uvalue; rewrite concretize_uvalueM_equation. simpl.
          rewrite bind_ret_l. reflexivity.
        + simpl.
          
      unfold concretize_uvalue.
      induction u; rewrite concretize_uvalueM_equation; 
        rewrite concretize_uvalueM_equation; cbn; try reflexivity.
      - destruct (default_dvalue_of_dtyp t); cbn in *; reflexivity.
      - induction fields.
        + simpl. rewrite bind_ret_l. reflexivity.
        + simpl. 
      
      
      
      unfold concretize_uvalue in *.
      - induction u; cbn;
          rewrite concretize_uvalueM_equation;
          rewrite concretize_uvalueM_equation in Heqe;
          try solve
              [ inv Heqe
              | destruct (default_dvalue_of_dtyp t); cbn in *; inv Heqe
              ].
        cbn. unfold map_monad.
        all: admit.
      - admit.
      - admit.
      - admit.*)
    Admitted.

    Lemma PickUvalue_handler_correct :
      forall E `{FailureE -< E} `{UBE -< E} `{OOME -< E},
        handler_correct (@PickUvalue_handler E _ _ _) concretize_picks.
    Proof.
      unfold handler_correct.
      intros * EQ.
      destruct e as [Pre u].
      rewrite EQ.
      apply PickUV_Ret with (res := concretize_uvalue u).
      - apply concretize_u_concretize_uvalue.
      - unfold ITree.map.
        unfold lift_err_ub_oom_post_ret, lift_err_ub_oom_post.
        destruct ((concretize_uvalue u) : err_ub_oom_T _ _) eqn: HU.
        repeat break_match.
        + unfold raiseOOM.
          apply eutt_clo_bind with (UU:=fun _ _ => True).
          setoid_rewrite concretize_uvalue_err_ub_oom_to_itree.
          rewrite HU. unfold raiseOOM.
          rewrite bind_trigger. unfold trigger.
          apply eqit_Vis. intros. inversion u0.
          intros; inv u2.
        + unfold raiseUB.
          apply eutt_clo_bind with (UU:=fun _ _ => True).
          setoid_rewrite concretize_uvalue_err_ub_oom_to_itree.
          rewrite HU.
          unfold raiseUB. rewrite bind_trigger. unfold trigger.
          apply eqit_Vis. intros. inversion u1. intros.
          inversion u2.
        + unfold raise.
          apply eutt_clo_bind with (UU:=fun _ _ => True).
          setoid_rewrite concretize_uvalue_err_ub_oom_to_itree.
          rewrite HU. unfold raise.
          rewrite bind_trigger. unfold trigger.
          apply eqit_Vis. intros. inversion u0.
          intros. inversion u2.
        + cbn. unfold ITree.map.
          setoid_rewrite concretize_uvalue_err_ub_oom_to_itree.
          rewrite HU. setoid_rewrite bind_ret_l. reflexivity.
    Qed.

    Lemma refine_undef
      : forall (E F:Type -> Type) T TT (HR: Reflexive TT)  `{UBE -< F} `{FailureE -< F} `{OOME -< F}
               (xs : PropT _ T),
        forall x, xs x -> model_undef TT xs (@exec_undef E F _ _ _ _ x).
    Proof.
      intros E F T TT REL UB FAIL OOM xs x XS.
      unfold model_undef.
      unfold exec_undef.
      exists x; split; auto.
      apply interp_prop_correct_exec; try reflexivity; auto.
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
    Proof.
      intros E F G T xs x XS.
      red.
      left; auto.
    Qed.

    Definition build_singleton {A} : A -> A -> Prop := eq.

    (**
   Theorem 5.8: We prove that the interpreter belongs to the model.
     *)
    Theorem interpreter_sound: forall p,
        refine_L6 (model p) (build_singleton (interpreter p)).
    Proof.
      intros p.
      intros ? [].
      exists (interpreter p).
      split.
      - apply refine_UB.
        unfold interpreter.
        unfold interpreter_gen.
        apply refine_undef; auto.
        apply interp_memory_correct.
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
  Proof.
    intros.
    unfold ℑs2.
    rewrite interp_intrinsics_bind, interp_global_bind, interp_local_stack_bind.
    apply eutt_clo_bind with (UU := Logic.eq); [reflexivity | intros ? (? & ? & ?) ->; reflexivity].
  Qed.

  Lemma interp2_ret:
    forall (R : Type) s1 s2 (x : R),
      ℑs2 (Ret x) s1 s2 ≈ Ret (s2, (s1, x)).
  Proof.
    intros; unfold ℑs2.
    rewrite interp_intrinsics_ret, interp_global_ret, interp_local_stack_ret; reflexivity.
  Qed.

  Definition interp_cfg {R: Type} (trace: itree instr_E R) g l sid m :=
    let uvalue_trace   := interp_intrinsics trace in
    let L1_trace       := interp_global uvalue_trace g in
    let L2_trace       := interp_local L1_trace l in
    let L3_trace       := interp_memory_prop eq L2_trace sid m in
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
