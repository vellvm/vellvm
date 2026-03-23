From Stdlib Require Import
  Lia
  ZArith
  List
  Relations
  String
  Program.Equality.

From ExtLib Require Import
  Structures.Monads
  Structures.Functor.

From Vellvm Require Import
  TopLevelRefinements.

From Vellvm.Semantics Require Import
  MemoryAddress
  VellvmIntegers
  DynamicValues
  InterpretationStack
  TopLevel
  LLVMEvents
  Memory.Sizeof.

Import DynamicTypes.

From Vellvm.Semantics.InfiniteToFinite.Conversions Require Import
  BaseConversions
  DvalueConversions
  EventConversions.

From Vellvm.Semantics.InfiniteToFinite.LangRefine Require Import
  Events
  Sizeof
  Values.

From Vellvm.Utils Require Import
  Error
  Tactics
  Monads
  MapMonadExtra
  OOMRutt
  OOMRuttProps
  ListUtil
  RuttPropsExtra
  VellvmRelations.

From ITree Require Import
  ITree
  Basics.HeterogeneousRelations
  Eq.Rutt
  Eq.RuttFacts
  Eq.Eqit.

Import ListNotations.

Module Type FloatOpsRefine
  (IS1 : InterpreterStack)
  (IS2 : InterpreterStack)
  (LLVM1 : LLVMTopLevel IS1)
  (LLVM2 : LLVMTopLevel IS2)
  (TLR1 : TopLevelRefinements IS1 LLVM1)
  (TLR2 : TopLevelRefinements IS2 LLVM2)
  (AC1 : AddrConvert IS1.LP.ADDR IS1.LP.PTOI IS2.LP.ADDR IS2.LP.PTOI)
  (AC2 : AddrConvert IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI)
  (IPS : IPConvertSafe IS2.LP.IP IS1.LP.IP)
  (ACS : AddrConvertSafe IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI AC2 AC1)
  (DVC : DVConvert IS1.LP IS2.LP AC1)
  (DVCrev : DVConvert IS2.LP IS1.LP AC2)
  (EC : EventConvert IS1.LP IS2.LP AC1 AC2 DVC DVCrev)
  (SIZEOF_REF : Sizeof_Refine IS1.LP.SZ IS2.LP.SZ)
  (ER : EventRefine IS1 IS2 LLVM1 LLVM2 AC1 AC2 DVC DVCrev EC)
  (VAL_REF : ValueRefine 
               IS1 IS2
               LLVM1 LLVM2
               AC1 AC2
               IPS ACS
               DVC DVCrev
               EC SIZEOF_REF ER).

  Import DVC.
  Import TLR2.
  Import IS2.LP.
  Import IS2.LP.DV.
  Import IS2.LLVM.D.
  Import ER.
  Import IPS.
  Import ADDR.
  Import VAL_REF.

  Lemma double_op_fin_inf :
    forall fop a b res_fin res_inf,
      double_op fop a b = success_unERR_UB_OOM res_fin ->
      DVCrev.dvalue_convert_strict res_fin = NoOom res_inf ->
      DV1.double_op fop a b = success_unERR_UB_OOM res_inf.
  Proof.
    intros fop a b res_fin res_inf EVAL REF.
    destruct fop; cbn in *; inv EVAL;
      cbn in REF;
      inv REF; reflexivity.
  Qed.

  (*
  x : ll_double
  x1 : DVCrev.DV2.dvalue
  e1 : dvalue_convert_strict x1 = NoOom (DVALUE_Double (Floats.Float.neg x))
  ============================
  DV1.eval_fneg (DVCrev.DV2.DVALUE_Double x) = success_unERR_UB_OOM x1

*)

  
  Lemma double_neg_fin_inf :
    forall f res_fin,
      dvalue_convert_strict res_fin = NoOom (DVALUE_Double (Floats.Float.neg f)) ->
      DV1.eval_fneg (DV1.DVALUE_Double f) = success_unERR_UB_OOM res_fin.
  Proof.
    intros f res_fin  EVAL.
    cbn in *; inv EVAL.
    destruct res_fin; cbn in *; try break_match_hyp_inv; try inversion H0.
    reflexivity.
  Qed.


  Lemma float_neg_fin_inf :
    forall f res_fin,
      dvalue_convert_strict res_fin = NoOom (DVALUE_Float (Floats.Float32.neg f)) ->
      DV1.eval_fneg (DV1.DVALUE_Float f) = success_unERR_UB_OOM res_fin.
  Proof.
    intros f res_fin  EVAL.
    cbn in *; inv EVAL.
    destruct res_fin; cbn in *; try break_match_hyp_inv; try inversion H0.
    reflexivity.
  Qed.

  Lemma poison_neg_fin_inf :
    forall t res_fin res_inf,
      eval_fneg (DVALUE_Poison t) = success_unERR_UB_OOM res_fin -> 
      DVCrev.dvalue_convert_strict res_fin = NoOom res_inf ->
      DV1.eval_fneg (DV1.DVALUE_Poison t) = success_unERR_UB_OOM res_inf.
  Proof.
    intros t res_fin res_inf EVAL REF.
    cbn in *; inv EVAL;
      cbn in REF;
      inv REF; reflexivity.
  Qed.


  Lemma float_op_fin_inf :
    forall fop a b res_fin res_inf,
      float_op fop a b = success_unERR_UB_OOM res_fin ->
      DVCrev.dvalue_convert_strict res_fin = NoOom res_inf ->
      DV1.float_op fop a b = success_unERR_UB_OOM res_inf.
  Proof.
    intros fop a b res_fin res_inf EVAL REF.
    destruct fop; cbn in *; inv EVAL;
      cbn in REF;
      inv REF; reflexivity.
  Qed.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_fop_fin_inf :
    forall dv1_fin dv2_fin res_fin fop dv1_inf dv2_inf,
      @eval_fop err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        fop dv1_fin dv2_fin = ret res_fin ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @DV1.eval_fop err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        fop dv1_inf dv2_inf = ret (fin_to_inf_dvalue res_fin).
  Proof.
    intros dv1_fin dv2_fin res_fin fop dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    unfold eval_fop in EVAL.
    (* Nasty case analysis... *)
    break_match_hyp_inv.
    { (* dv1: Double *)
      break_match_hyp_inv.
      2: {
        break_match_hyp_inv.
        unfold fin_to_inf_dvalue.
        break_match_goal; clear Heqs; destruct p; clear e0.
        break_match_goal; clear Heqs; destruct p; clear e1.
        inv e; inv e0.
        cbn.

        (* These should be the same... *)
        unfold AstLib.fop_is_div in *.
        rewrite Heqb.
        reflexivity.
      }

      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs; destruct p; clear e0.
      break_match_goal; clear Heqs; destruct p; clear e1.
      inv e; inv e0.
      cbn.
      break_match_goal; clear Heqs; destruct p; clear e0.
      eapply double_op_fin_inf; eauto.
    }

    { (* dv1: Float *)
      break_match_hyp_inv.
      2: {
        break_match_hyp_inv.
        unfold fin_to_inf_dvalue.
        break_match_goal; clear Heqs; destruct p; clear e0.
        break_match_goal; clear Heqs; destruct p; clear e1.
        inv e; inv e0.
        cbn.

        (* These should be the same... *)
        unfold AstLib.fop_is_div in *.
        rewrite Heqb.
        reflexivity.
      }

      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs; destruct p; clear e0.
      break_match_goal; clear Heqs; destruct p; clear e1.
      inv e; inv e0.
      cbn.
      break_match_goal; clear Heqs; destruct p; clear e0.
      eapply float_op_fin_inf; eauto.
    }

    { (* dv1: Poison *)
      unfold fin_to_inf_dvalue.

      break_match_goal; clear Heqs; destruct p; clear e0;
        cbn in *; inv e.
      cbn. reflexivity.
    }
  Qed.

  Lemma eval_fneg_fin_inf :
    forall dv1_fin res_fin dv1_inf,
      @eval_fneg err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        dv1_fin  = ret res_fin ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      @DV1.eval_fneg err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        dv1_inf = ret (fin_to_inf_dvalue res_fin).
  Proof.
    intros dv1_fin res_fin dv1_inf EVAL LIFT1.
    unfold eval_fneg in EVAL.

    break_match_hyp_inv.
    { (* dv1: Double *)
      cbn. 
      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs; destruct p; clear e0.
      break_match_goal; clear Heqs; destruct p; clear e0.
      cbn in e. inversion e. 
      eapply double_neg_fin_inf. auto.
    }

    { (* dv1: Float *)
      cbn.
      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs; destruct p; clear e0.
      break_match_goal; clear Heqs; destruct p; clear e0.
      cbn in e. inversion e.
      eapply float_neg_fin_inf. auto.
    }

    { cbn.
      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs; destruct p; clear e0.
      cbn in e. inversion e.
      reflexivity.
    } 
  Qed.


  Lemma double_cmp_fin_inf :
    forall fcmp a b res_fin res_inf,
      double_cmp fcmp a b = res_fin ->
      DVCrev.dvalue_convert_strict res_fin = NoOom res_inf ->
      DV1.double_cmp fcmp a b = res_inf.
  Proof.
    intros fcmp a b res_fin res_inf EVAL REF.
    destruct fcmp; cbn in *; subst;
      cbn in REF;
      inv REF; auto;
      solve
        [ unfold double_cmp, DV1.double_cmp in *;
          repeat break_match_hyp_inv; auto;
          setoid_rewrite Heqb0; reflexivity
        ].
  Qed.

  Lemma float_cmp_fin_inf :
    forall fcmp a b res_fin res_inf,
      float_cmp fcmp a b = res_fin ->
      DVCrev.dvalue_convert_strict res_fin = NoOom res_inf ->
      DV1.float_cmp fcmp a b = res_inf.
  Proof.
    intros fcmp a b res_fin res_inf EVAL REF.
    destruct fcmp; cbn in *; subst;
      cbn in REF;
      inv REF; auto;
      solve
        [ unfold float_cmp, DV1.float_cmp in *;
          repeat break_match_hyp_inv; auto;
          setoid_rewrite Heqb0; reflexivity
        ].
  Qed.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_fcmp_fin_inf :
    forall dv1_fin dv2_fin res_fin fcmp dv1_inf dv2_inf,
      @eval_fcmp err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        fcmp dv1_fin dv2_fin = ret res_fin ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @DV1.eval_fcmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        fcmp dv1_inf dv2_inf = ret (fin_to_inf_dvalue res_fin).
  Proof.
    intros dv1_fin dv2_fin res_fin fcmp dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    unfold eval_fcmp in EVAL.
    (* Nasty case analysis... *)
    break_match_hyp_inv;
      try solve
        [ (* Simple integer cases *)
          break_match_hyp_inv;
          [ unfold fin_to_inf_dvalue;

            break_match_goal; clear Heqs; destruct p; clear e0;
            cbn in *; inv e;

            break_match_goal; clear Heqs; destruct p; clear e0;
            cbn in *; inv e;

            break_match_goal; clear Heqs; destruct p; clear e0;
            cbn;

            rewrite eval_int_icmp_fin_inf in e; inv e;
            reflexivity
          | unfold fin_to_inf_dvalue;

            break_match_goal; clear Heqs; destruct p; clear e0;
            cbn in *; inv e;

            break_match_goal; clear Heqs; destruct p; clear e0;
            cbn in *; inv e;

            cbn;
            reflexivity
          ]
        | (* Ill-typed cases *)
          break_match_hyp_inv
        ].

    { (* dv1: Double *)
      break_match_hyp_inv.
      unfold fin_to_inf_dvalue.

      break_match_goal; clear Heqs; destruct p; clear e0.
      cbn in *; inv e.

      break_match_goal; clear Heqs; destruct p; clear e0.
      cbn in *; inv e.

      break_match_goal; clear Heqs; destruct p; clear e0.
      cbn.

      erewrite double_cmp_fin_inf; eauto.
      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs; destruct p; clear e0.
      cbn in *; inv e.

      break_match_goal; clear Heqs; destruct p; clear e0.
      cbn in *; inv e.
      reflexivity.
    }

    { (* dv1: Float *)
      break_match_hyp_inv.
      unfold fin_to_inf_dvalue.

      break_match_goal; clear Heqs; destruct p; clear e0.
      cbn in *; inv e.

      break_match_goal; clear Heqs; destruct p; clear e0.
      cbn in *; inv e.

      break_match_goal; clear Heqs; destruct p; clear e0.
      cbn.

      erewrite float_cmp_fin_inf; eauto.
      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs; destruct p; clear e0.
      cbn in *; inv e.

      break_match_goal; clear Heqs; destruct p; clear e0.
      cbn in *; inv e.
      reflexivity.
    }

    { (* dv1: poison *)
      break_match_hyp_inv;
        unfold fin_to_inf_dvalue;

        break_match_goal; clear Heqs; destruct p; clear e0;
        cbn in *; inv e;

        break_match_goal; clear Heqs; destruct p; clear e0;
        cbn in *; inv e;

        cbn;
        reflexivity.
    }
  Qed.

  Lemma double_op_ub_fin_inf :
    forall fop a b ub_msg,
      double_op fop a b = UB_unERR_UB_OOM ub_msg ->
      DV1.double_op fop a b = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros fop a b ub_msg EVAL.
    destruct fop; cbn in *; inv EVAL.
  Qed.

  Lemma float_op_ub_fin_inf :
    forall fop a b ub_msg,
      float_op fop a b = UB_unERR_UB_OOM ub_msg ->
      DV1.float_op fop a b = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros fop a b ub_msg EVAL.
    destruct fop; cbn in *; inv EVAL.
  Qed.

  Lemma double_op_err_fin_inf :
    forall fop a b err_msg,
      double_op fop a b = ERR_unERR_UB_OOM err_msg ->
      DV1.double_op fop a b = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros fop a b err_msg EVAL.
    destruct fop; cbn in *; inv EVAL; auto.
  Qed.

  Lemma float_op_err_fin_inf :
    forall fop a b err_msg,
      float_op fop a b = ERR_unERR_UB_OOM err_msg ->
      DV1.float_op fop a b = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros fop a b err_msg EVAL.
    destruct fop; cbn in *; inv EVAL; auto.
  Qed.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_fop_ub_fin_inf :
    forall dv1_fin dv2_fin ub_msg fop dv1_inf dv2_inf,
      @eval_fop err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        fop dv1_fin dv2_fin = UB_unERR_UB_OOM ub_msg ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @DV1.eval_fop err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        fop dv1_inf dv2_inf = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros dv1_fin dv2_fin ub_msg fop dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    unfold eval_fop in EVAL.
    (* Nasty case analysis... *)
    break_match_hyp_inv.
    { (* dv1: Double *)
      break_match_hyp_inv.
      2: {
        break_match_hyp_inv.
        unfold fin_to_inf_dvalue.
        break_match_goal; clear Heqs; destruct p; clear e0.
        break_match_goal; clear Heqs; destruct p; clear e1.
        inv e; inv e0.
        cbn.

        (* These should be the same... *)
        unfold AstLib.fop_is_div in *.
        rewrite Heqb.
        reflexivity.
      }

      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs; destruct p; clear e0.
      break_match_goal; clear Heqs; destruct p; clear e1.
      inv e; inv e0.
      cbn.
      eapply double_op_ub_fin_inf; eauto.
    }

    { (* dv1: Float *)
      break_match_hyp_inv.
      2: {
        break_match_hyp_inv.
        unfold fin_to_inf_dvalue.
        break_match_goal; clear Heqs; destruct p; clear e0.
        break_match_goal; clear Heqs; destruct p; clear e1.
        inv e; inv e0.
        cbn.

        (* These should be the same... *)
        unfold AstLib.fop_is_div in *.
        rewrite Heqb.
        reflexivity.
      }

      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs; destruct p; clear e0.
      break_match_goal; clear Heqs; destruct p; clear e1.
      inv e; inv e0.
      cbn.
      eapply float_op_ub_fin_inf; eauto.
    }
  Qed.


  Lemma eval_fneg_ub_fin_inf :
    forall dv1_fin ub_msg dv1_inf,
      @eval_fneg err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        dv1_fin  = UB_unERR_UB_OOM ub_msg ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      @DV1.eval_fneg err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        dv1_inf = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros dv1_fin ub_msg dv1_inf EVAL LIFT1.
    unfold eval_fneg in EVAL.
    (* Nasty case analysis... *)
    break_match_hyp_inv.
  Qed.


  (* TODO: Move this / generalize monad? *)
  Lemma eval_fop_err_fin_inf :
    forall dv1_fin dv2_fin err_msg fop dv1_inf dv2_inf,
      @eval_fop err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        fop dv1_fin dv2_fin = ERR_unERR_UB_OOM err_msg ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @DV1.eval_fop err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        fop dv1_inf dv2_inf = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros dv1_fin dv2_fin err_msg fop dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    unfold eval_fop in EVAL.
    (* Nasty case analysis... *)
    break_match_hyp_inv;
      repeat rewrite_fin_to_inf_dvalue;
      repeat erewrite ceres_to_string_fin_inf;
      try apply fin_to_inf_dvalue_refine_strict;
      repeat rewrite_fin_to_inf_dvalue;
      cbn; eauto.

    { (* dv1: Double *)
      break_match_hyp_inv;
        repeat rewrite_fin_to_inf_dvalue;
        repeat erewrite ceres_to_string_fin_inf;
        try apply fin_to_inf_dvalue_refine_strict;
        repeat rewrite_fin_to_inf_dvalue;
        cbn; eauto.
      2: break_match_hyp_inv.

      eapply double_op_err_fin_inf; eauto.
    }

    { (* dv1: Float *)
      break_match_hyp_inv;
        repeat rewrite_fin_to_inf_dvalue;
        repeat erewrite ceres_to_string_fin_inf;
        try apply fin_to_inf_dvalue_refine_strict;
        repeat rewrite_fin_to_inf_dvalue;
        cbn; eauto.
      2: break_match_hyp_inv.

      eapply float_op_err_fin_inf; eauto.
    }
  Qed.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_fcmp_ub_fin_inf :
    forall dv1_fin dv2_fin ub_msg fcmp dv1_inf dv2_inf,
      @eval_fcmp err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        fcmp dv1_fin dv2_fin = UB_unERR_UB_OOM ub_msg ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @DV1.eval_fcmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        fcmp dv1_inf dv2_inf = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros dv1_fin dv2_fin ub_msg fcmp dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    unfold eval_fcmp in EVAL.
    repeat break_match_hyp_inv.
  Qed.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_fcmp_err_fin_inf :
    forall dv1_fin dv2_fin err_msg fcmp dv1_inf dv2_inf,
      @eval_fcmp err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        fcmp dv1_fin dv2_fin = ERR_unERR_UB_OOM err_msg ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @DV1.eval_fcmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        fcmp dv1_inf dv2_inf = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros dv1_fin dv2_fin err_msg fcmp dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    unfold eval_fcmp in EVAL.
    (* Nasty case analysis... *)
    repeat break_match_hyp_inv;
      repeat rewrite_fin_to_inf_dvalue;
      repeat erewrite ceres_to_string_fin_inf;
      try apply fin_to_inf_dvalue_refine_strict;
      repeat rewrite_fin_to_inf_dvalue;
      cbn; eauto.
  Qed.


  Lemma eval_fneg_err_fin_inf :
    forall dv1_fin err_msg dv1_inf,
      @eval_fneg err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        dv1_fin = ERR_unERR_UB_OOM err_msg ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      @DV1.eval_fneg err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        dv1_inf = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros dv1_fin err_msg dv1_inf EVAL LIFT1.
    unfold eval_fneg in EVAL.
    (* Nasty case analysis... *)
    break_match_hyp_inv;
      repeat rewrite_fin_to_inf_dvalue;
      repeat erewrite ceres_to_string_fin_inf;
      try apply fin_to_inf_dvalue_refine_strict;
      repeat rewrite_fin_to_inf_dvalue;
      cbn; eauto.
  Qed.

  Lemma orutt_eval_fop :
    forall E1 E2
      `{OOM1 : OOME -< E1} `{OOM2 : OOME -< E2}
      `{UB1 : UBE -< E1} `{UB2 : UBE -< E2}
      `{ERR1: FailureE -< E1} `{ERR2: FailureE -< E2}
      (pre : prerel E1 E2) (post : postrel E1 E2)
      (UBDISC : forall e1 e2, @subevent UBE E2 UB2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (ERRDISC : forall e1 e2, @subevent FailureE E2 ERR2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (UBINJ : pre void void (@subevent UBE E1 UB1 void (ThrowUB tt)) (@subevent UBE E2 UB2 void (ThrowUB tt)))
      (ERRINJ : pre void void (@subevent FailureE E1 ERR1 void (Throw tt)) (@subevent FailureE E2 ERR2 void (Throw tt)))
      fop dv1_1 dv2_1 dv1_2 dv2_2,
      dvalue_refine_strict dv1_1 dv1_2 ->
      dvalue_refine_strict dv2_1 dv2_2 ->
      orutt pre post dvalue_refine_strict
        (DV1.eval_fop fop dv1_1 dv2_1) (eval_fop fop dv1_2 dv2_2)
        (OOM:=OOME).
  Proof.
    intros E1 E2 OOM1 OOM2 UB1 UB2 ERR1 ERR2 pre post UBDISC ERRDISC UBINJ ERRINJ fop dv1_1 dv2_1 dv1_2 dv2_2 H H0.
    rewrite eval_fop_err_ub_oom_to_itree,
      TLR1.eval_fop_err_ub_oom_to_itree.

    remember (eval_fop fop dv1_2 dv2_2) as e.
    destruct_err_ub_oom e; symmetry in Heqe.
    - apply orutt_raiseOOM.
    - erewrite eval_fop_ub_fin_inf; cbn; eauto;
        try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_raiseUB; cbn; auto.
    - erewrite eval_fop_err_fin_inf; cbn; eauto;
        try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_raise; cbn; auto.
    - erewrite eval_fop_fin_inf; cbn; eauto; subst.
      2-3: try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_Ret; cbn; eauto.
      apply fin_to_inf_dvalue_refine_strict.
  Qed.

  #[global] Hint Resolve
    orutt_eval_fop
    : ORUTT.

  Lemma orutt_eval_fneg :
    forall E1 E2
      `{OOM1 : OOME -< E1} `{OOM2 : OOME -< E2}
      `{UB1 : UBE -< E1} `{UB2 : UBE -< E2}
      `{ERR1: FailureE -< E1} `{ERR2: FailureE -< E2}
      (pre : prerel E1 E2) (post : postrel E1 E2)
      (UBDISC : forall e1 e2, @subevent UBE E2 UB2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (ERRDISC : forall e1 e2, @subevent FailureE E2 ERR2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (UBINJ : pre void void (@subevent UBE E1 UB1 void (ThrowUB tt)) (@subevent UBE E2 UB2 void (ThrowUB tt)))
      (ERRINJ : pre void void (@subevent FailureE E1 ERR1 void (Throw tt)) (@subevent FailureE E2 ERR2 void (Throw tt)))
      dv1_1 dv1_2,
      dvalue_refine_strict dv1_1 dv1_2 ->
      orutt pre post dvalue_refine_strict
        (DV1.eval_fneg dv1_1) (eval_fneg dv1_2)
        (OOM:=OOME).
  Proof.
    intros E1 E2 OOM1 OOM2 UB1 UB2 ERR1 ERR2 pre post UBDISC ERRDISC UBINJ ERRINJ
      dv1_1 dv1_2  H.
    rewrite eval_neg_err_ub_oom_to_itree,
      TLR1.eval_neg_err_ub_oom_to_itree.

    remember (eval_fneg dv1_2) as e.
    destruct_err_ub_oom e; symmetry in Heqe.
    - apply orutt_raiseOOM.
    - erewrite eval_fneg_ub_fin_inf; cbn; eauto;
        try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_raiseUB; cbn; auto.
    - erewrite eval_fneg_err_fin_inf; cbn; eauto;
        try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_raise; cbn; auto.
    - erewrite eval_fneg_fin_inf; cbn; eauto; subst.
      2: try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_Ret; cbn; eauto.
      apply fin_to_inf_dvalue_refine_strict.
  Qed.

  #[global] Hint Resolve
    orutt_eval_fneg
    : ORUTT.

  Lemma orutt_eval_fcmp :
    forall E1 E2
      `{OOM1 : OOME -< E1} `{OOM2 : OOME -< E2}
      `{UB1 : UBE -< E1} `{UB2 : UBE -< E2}
      `{ERR1: FailureE -< E1} `{ERR2: FailureE -< E2}
      (pre : prerel E1 E2) (post : postrel E1 E2)
      (UBDISC : forall e1 e2, @subevent UBE E2 UB2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (ERRDISC : forall e1 e2, @subevent FailureE E2 ERR2 void e1 <> @subevent OOME E2 OOM2 void e2)
      (UBINJ : pre void void (@subevent UBE E1 UB1 void (ThrowUB tt)) (@subevent UBE E2 UB2 void (ThrowUB tt)))
      (ERRINJ : pre void void (@subevent FailureE E1 ERR1 void (Throw tt)) (@subevent FailureE E2 ERR2 void (Throw tt)))
      cmp dv1_1 dv2_1 dv1_2 dv2_2,
      dvalue_refine_strict dv1_1 dv1_2 ->
      dvalue_refine_strict dv2_1 dv2_2 ->
      orutt pre post dvalue_refine_strict
        (DV1.eval_fcmp cmp dv1_1 dv2_1) (eval_fcmp cmp dv1_2 dv2_2)
        (OOM:=OOME).
  Proof.
    intros E1 E2 OOM1 OOM2 UB1 UB2 ERR1 ERR2 pre post UBDISC ERRDISC UBINJ ERRINJ cmp dv1_1 dv2_1 dv1_2 dv2_2 H
      H0.
    rewrite eval_fcmp_err_ub_oom_to_itree,
      TLR1.eval_fcmp_err_ub_oom_to_itree.

    remember (eval_fcmp cmp dv1_2 dv2_2) as e.
    destruct_err_ub_oom e; symmetry in Heqe.
    - apply orutt_raiseOOM.
    - erewrite eval_fcmp_ub_fin_inf; cbn; eauto;
        try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_raiseUB; cbn; auto.
    - erewrite eval_fcmp_err_fin_inf; cbn; eauto;
        try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_raise; cbn; auto.
    - erewrite eval_fcmp_fin_inf; cbn; eauto; subst.
      2-3: try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_Ret; cbn; eauto.
      apply fin_to_inf_dvalue_refine_strict.
  Qed.

  #[global] Hint Resolve
    orutt_eval_fcmp
    : ORUTT.

End FloatOpsRefine.
