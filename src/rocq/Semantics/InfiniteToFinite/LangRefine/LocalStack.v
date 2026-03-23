From Stdlib Require Import
  Lia
  ZArith
  List
  Relations
  String
  Program.Equality.

Require Import Paco.paco.

From ExtLib Require Import
  Structures.Monads
  Structures.Functor.

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
  Sizeof.

From Vellvm.Utils Require Import
  Error
  Tactics
  Monads
  MapMonadExtra
  OOMRutt
  OOMRuttProps
  ListUtil
  RuttPropsExtra
  VellvmRelations
  AListFacts.

From ITree Require Import
  ITree
  Basics.HeterogeneousRelations
  Eq.Rutt
  Eq.RuttFacts
  Eq.Eqit.

Import ListNotations.

Module Type LocalStackRefine
  (IS1 : InterpreterStack)
  (IS2 : InterpreterStack)
  (LLVM1 : LLVMTopLevel IS1)
  (LLVM2 : LLVMTopLevel IS2)
  (AC1 : AddrConvert IS1.LP.ADDR IS1.LP.PTOI IS2.LP.ADDR IS2.LP.PTOI)
  (AC2 : AddrConvert IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI)
  (IPS : IPConvertSafe IS2.LP.IP IS1.LP.IP)
  (ACS : AddrConvertSafe IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI AC2 AC1)
  (DVC : DVConvert IS1.LP IS2.LP AC1)
  (DVCrev : DVConvert IS2.LP IS1.LP AC2)
  (EC : EventConvert IS1.LP IS2.LP AC1 AC2 DVC DVCrev)
  (SIZEOF_REF : Sizeof_Refine IS1.LP.SZ IS2.LP.SZ)
  (ER : EventRefine IS1 IS2 LLVM1 LLVM2 AC1 AC2 DVC DVCrev EC).
  Import DVC.
  Import IS2.LP.
  Import IS2.LP.DV.
  Import IS2.LLVM.D.
  Import ER.
  Import IPS.
  Import ADDR.

  Lemma handle_local_orutt :
    forall A B E1 E2
      `{OOME -< E2}
      `{FailureE -< E1} `{FailureE -< E2}
      (NOOM : forall A (e : FailureE A) (o : OOME A), @subevent FailureE E2 _ _ e <> @subevent OOME E2 _ _ o)
      (l1 : LocalE LLVMAst.raw_id DV1.uvalue A) (l2 : LocalE LLVMAst.raw_id DV2.uvalue B)
      (REF : localE_refine_strict l1 l2)
      (s1 : IS1.LLVM.Stack.lstack_frame) (s2 : IS2.LLVM.Stack.lstack_frame)
      (SREF : stack_frame_refine_strict s1 s2)
      (pre : prerel E1 E2)
      (FAILPRE : forall A (e : FailureE A), pre _ _ (@subevent FailureE E1 _ _ e) (@subevent FailureE E2 _ _ e))
      (post : postrel E1 E2),
      orutt (OOM:=OOME) pre post (prod_rel stack_frame_refine_strict (fun a b => localE_res_refine_strict l1 a l2 b))
        (handle_local (map:=IS1.LLVM.Stack.lstack_frame) l1 s1)
        (handle_local (map:=IS2.LLVM.Stack.lstack_frame) l2 s2).
  Proof.
    intros A B E1 E2 H H0 H1 NOOM l1 l2 REF s1 s2 SREF pre FAILPRE post.
    red in REF.
    destruct l1, l2; inversion REF; subst; cbn in *.
    - (* LocalWrite *)
      apply orutt_Ret.
      constructor; cbn.
      red in SREF.
      destruct s1, s2; cbn in *.
      split; try tauto.
      destruct SREF.
      eapply local_stack_refine_strict_add; eauto.
      split; eauto.
    - (* LocalRead *)
      destruct s1, s2; cbn in *.
      destruct SREF.
      pose proof H2 as FIND.
      red in FIND.
      repeat break_match_goal.
      + eapply alist_refine_find_some in FIND; eauto.
        apply orutt_Ret; constructor; cbn; eauto.
      + eapply alist_refine_find_some_iff with (k:=id0) in  FIND.
        destruct FIND.
        forward H4; eauto.
        destruct H4.
        rewrite H4 in Heqo0.
        discriminate.
      + eapply alist_refine_find_some_iff with (k:=id0) in  FIND.
        destruct FIND.
        forward H5; eauto.
        destruct H5.
        rewrite H5 in Heqo.
        discriminate.
      + apply orutt_raise.
        intros ? ? CONTRA.
        apply NOOM in CONTRA; auto.
        eauto.
  Qed.

  Lemma handle_stack_orutt :
    forall A B E1 E2
      `{OOME -< E2}
      `{FailureE -< E1} `{FailureE -< E2}
      (NOOM : forall A (e : FailureE A) (o : OOME A), @subevent FailureE E2 _ _ e <> @subevent OOME E2 _ _ o)
      (e1 : StackE LLVMAst.raw_id DV1.uvalue DV1.uvalue A) (e2 : StackE LLVMAst.raw_id DV2.uvalue DV2.uvalue B)
      (REF : stackE_refine_strict e1 e2)
      (s1 : IS1.LLVM.Stack.lstack_frame * IS1.LLVM.Stack.lstack) (s2 : IS2.LLVM.Stack.lstack_frame * IS2.LLVM.Stack.lstack)
      (SREF : (prod_rel stack_frame_refine_strict stack_refine_strict) s1 s2)
      (pre : prerel E1 E2)
      (FAILPRE : forall A (e : FailureE A), pre _ _ (@subevent FailureE E1 _ _ e) (@subevent FailureE E2 _ _ e))
      (post : postrel E1 E2),
      orutt (OOM:=OOME) pre post (prod_rel local_stack_refine_strict (fun a b => stackE_res_refine_strict e1 a e2 b))
        (handle_stack e1 s1)
        (handle_stack e2 s2).
  Proof.
    intros A B E1 E2 H H0 H1 NOOM e1 e2 REF s1 s2 SREF pre FAILPRE post.
    red in REF.
    destruct e1, e2; cbn in *; try contradiction.
    - (* StackPush *)
      destruct s1, s2; cbn in *.
      repeat rewrite bind_ret_l.
      apply orutt_Ret.
      destruct SREF; cbn in *.
      repeat (constructor; cbn; eauto).
      eapply alist_refine_strict_fold_right_add.
      apply REF.
    - (* StackPop *)
      destruct s1, s2; cbn in *.
      destruct SREF; cbn in *.
      destruct snd_rel.
      solve_orutt_raise.
      repeat rewrite bind_ret_l.
      apply orutt_Ret.
      repeat (constructor; cbn; eauto).
    - (* StackSetHandler *)
      destruct s1, s2; cbn in *.
      destruct SREF; cbn in *.
      apply orutt_Ret; cbn;
        repeat (constructor; cbn; eauto).
      destruct l, l1; cbn in *; tauto.
      destruct REF; subst; eauto.
      destruct l, l1; cbn in *; tauto.
    - (* StackHandler *)
      destruct s1, s2; cbn in *.
      destruct SREF; cbn in *.
      destruct l, l1; cbn in *;
      apply orutt_Ret; cbn;
        repeat (constructor; cbn; eauto); tauto.
    - (* StackRaise *)
      destruct s1, s2; cbn in *.
      destruct SREF; cbn in *.
      destruct l, l1; cbn in *;
      apply orutt_Ret; cbn;
        repeat (constructor; cbn; eauto); tauto.
    - (* StackGetExc *)
      destruct s1, s2; cbn in *.
      destruct SREF; cbn in *.
      destruct l, l1; cbn in *;
      apply orutt_Ret; cbn;
        repeat (constructor; cbn; eauto); tauto.
  Qed.

  Lemma orutt_interp_local_stack_h :
    forall A B e1 e2 ls1 ls2,
      L1_refine_strict A B e1 e2 ->
      local_stack_refine_strict ls1 ls2 ->
      orutt L2_refine_strict L2_res_refine_strict
        (fun '(s0, a) '(s3, b) =>
           L1_res_refine_strict A B e1 a e2 b /\ (stack_frame_refine_strict × stack_refine_strict) s0 s3)
        (interp_local_stack_h (handle_local (v:=DV1.uvalue)) e1 ls1)
        (interp_local_stack_h (handle_local (v:=uvalue)) e2 ls2)
        (OOM:=OOME).
  Proof.
    intros A B e1 e2 ls1 ls2 REF LSR.
    destruct e1; repeat (destruct e); repeat (destruct s);
    try
      solve
        [ cbn in REF;
          destruct e2; try inv REF;
          repeat (break_match_hyp; try inv REF);
          cbn in *;
          repeat rewrite bind_trigger;
          pstep; red; cbn;
          constructor;
          [ cbn; tauto
          | intros a b H;
            left; apply orutt_Ret;
            split; try tauto;
            destruct ls1, ls2; constructor; cbn in *; tauto
          | intros o CONTRA; inv CONTRA
          ]
        ].

    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF);
        cbn.
      eapply orutt_bind.
      apply orutt_trigger; cbn; eauto.
      intros [] [] ?; reflexivity.
      intros o CONTRA. inv CONTRA.
      intros [] [] ?.
      apply orutt_Ret; split; eauto.
      unfold local_stack_refine_strict in LSR.
      destruct ls1, ls2, LSR.
      constructor; cbn; eauto.
    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF);
        cbn.
      eapply orutt_bind.
      apply orutt_trigger; cbn; eauto.
      intros [] [] ?; reflexivity.
      intros o CONTRA. inv CONTRA.
      intros [] [] ?.
      apply orutt_Ret; split; eauto.
      unfold local_stack_refine_strict in LSR.
      destruct ls1, ls2, LSR.
      constructor; cbn; eauto.
    - (* LocalE *) cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF); subst.
      destruct ls1, ls2.
      cbn in *.
      unfold ITree.map.
      eapply orutt_bind.
      + eapply handle_local_orutt; eauto; try tauto.
        intros ? ? ? CONTRA; inv CONTRA.
        intros ? ?.
        red. cbn.
        red.
        repeat break_match_goal; auto.
      + intros r1 r2 R1R2.
        destruct r1, r2.
        apply orutt_Ret.
        destruct R1R2; cbn in *.
        split; try tauto.
        constructor; cbn; eauto.
        tauto.
    - (* StackE *) cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF); subst.
      cbn in *.
      eapply orutt_weaken with (PRE1:=L2_refine_strict) (POST1:=L2_res_refine_strict); eauto.
      + eapply handle_stack_orutt; eauto.
        intros ? ? ? CONTRA; inv CONTRA.
        destruct ls1, ls2; cbn in *.
        constructor; cbn; tauto.
        intros A0 e.
        cbn. destruct e; cbn; auto.
      + intros r1 r2 H.
        destruct r1, r2, H; cbn in *.
        constructor; eauto.
        destruct p, p0; cbn in *.
        repeat (constructor; cbn; eauto); tauto.
    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF).
      cbn.
      rewrite !bind_trigger.
      pstep; red; cbn.
      change (inr1 (inr1 (inl1 o0))) with
        (@subevent _ _ (ReSum_inr IFun sum1 OOME
                          ((PickUvalueE DV2.dvalue DV2.uvalue) +' OOME +' LLVMExcE uvalue +' UBE +' DebugE +' FailureE)
                          (MemoryE DV2.dvalue DV2.uvalue)

           ) B o0).
      rewrite subevent_subevent.
      eapply EqVisOOM.
    - (* UBE Events *)
      cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF);
        try solve [cbn;
         repeat rewrite bind_trigger;
         red; pstep; red; cbn;
         constructor; cbn; auto;
         [ intros ?a ?b ?H;
           left;
           pstep; red; cbn;
           constructor; cbn; auto;
           split; auto;
           destruct ls1, ls2; cbn in *;
           constructor; tauto
         | intros o CONTRA; inv CONTRA
          ]].
      cbn.

      rewrite !bind_trigger.
      pstep; red; cbn.
      constructor.
      constructor.
      intros a b H.
      cbn in H.
      left.
      apply orutt_Ret.
      split; eauto.
      destruct ls1, ls2; cbn in *; constructor; tauto.
      intros ? CONTRA; inv CONTRA.
  Qed.

  Lemma orutt_interp_local_stack_h_debug :
    forall A B e1 e2 ls1 ls2,
      L1_refine_strict A B e1 e2 ->
      local_stack_refine_strict ls1 ls2 ->
      orutt L2_refine_strict L2_res_refine_strict
        (fun '(s0, a) '(s3, b) =>
           L1_res_refine_strict A B e1 a e2 b /\ (stack_frame_refine_strict × stack_refine_strict) s0 s3)
        (interp_local_stack_h (handle_local_debug_stack (exc:=DV1.uvalue)) e1 ls1)
        (interp_local_stack_h (handle_local_debug_stack (exc:=uvalue)) e2 ls2)
        (OOM:=OOME).
  Proof.
    intros A B e1 e2 ls1 ls2 REF LSR.
    destruct e1; repeat (destruct e); repeat (destruct s);
    try
      solve
        [ cbn in REF;
          destruct e2; try inv REF;
          repeat (break_match_hyp; try inv REF);
          cbn in *;
          repeat rewrite bind_trigger;
          pstep; red; cbn;
          constructor;
          [ cbn; tauto
          | intros a b H;
            left; apply orutt_Ret;
            split; try tauto;
            destruct ls1, ls2; constructor; cbn in *; tauto
          | intros o CONTRA; inv CONTRA
          ]
        ].

    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF);
        cbn.
      eapply orutt_bind.
      apply orutt_trigger; cbn; eauto.
      intros [] [] ?; reflexivity.
      intros o CONTRA. inv CONTRA.
      intros [] [] ?.
      apply orutt_Ret; split; eauto.
      unfold local_stack_refine_strict in LSR.
      destruct ls1, ls2, LSR.
      constructor; cbn; eauto.
    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF);
        cbn.
      eapply orutt_bind.
      apply orutt_trigger; cbn; eauto.
      intros [] [] ?; reflexivity.
      intros o CONTRA. inv CONTRA.
      intros [] [] ?.
      apply orutt_Ret; split; eauto.
      unfold local_stack_refine_strict in LSR.
      destruct ls1, ls2, LSR.
      constructor; cbn; eauto.
    - (* LocalE *) cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF); subst.
      destruct ls1, ls2.
      cbn in *.
      unfold ITree.map.
      repeat setoid_rewrite bind_ret_l.
      setoid_rewrite bind_bind.
      eapply orutt_bind.
      + eapply handle_local_orutt; eauto; try tauto.
        intros ? ? ? CONTRA; inv CONTRA.
        intros ? ?.
        red. cbn.
        red.
        repeat break_match_goal; auto.
      + intros r1 r2 R1R2.
        destruct r1, r2.
        setoid_rewrite bind_ret_l.
        apply orutt_Ret.
        destruct R1R2; cbn in *.
        split; try tauto.
        constructor; cbn; eauto.
        tauto.
    - (* StackE *) cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF); subst.
      cbn in *.
      eapply orutt_weaken with (PRE1:=L2_refine_strict) (POST1:=L2_res_refine_strict); eauto.
      + eapply handle_stack_orutt; eauto.
        intros ? ? ? CONTRA; inv CONTRA.
        destruct ls1, ls2; cbn in *.
        constructor; cbn; tauto.
        intros A0 e.
        cbn. destruct e; cbn; auto.
      + intros r1 r2 H.
        destruct r1, r2, H; cbn in *.
        constructor; eauto.
        destruct p, p0; cbn in *.
        repeat (constructor; cbn; eauto); tauto.
    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF).
      cbn.
      rewrite !bind_trigger.
      pstep; red; cbn.
      change (inr1 (inr1 (inl1 o0))) with
        (@subevent _ _ (ReSum_inr IFun sum1 OOME
                          (PickUvalueE DV2.dvalue DV2.uvalue +' OOME +' LLVMExcE uvalue +' UBE +' DebugE +' FailureE)
                          (MemoryE DV2.dvalue DV2.uvalue)

           ) B o0).
      rewrite subevent_subevent.
      eapply EqVisOOM.
    - (* UBE Events *)
      cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF);
        try solve [cbn;
         repeat rewrite bind_trigger;
         red; pstep; red; cbn;
         constructor; cbn; auto;
         [ intros ?a ?b ?H;
           left;
           pstep; red; cbn;
           constructor; cbn; auto;
           split; auto;
           destruct ls1, ls2; cbn in *;
           constructor; tauto
         | intros o CONTRA; inv CONTRA
          ]].
      cbn.

      rewrite !bind_trigger.
      pstep; red; cbn.
      constructor.
      constructor.
      intros a b H.
      cbn in H.
      left.
      apply orutt_Ret.
      split; eauto.
      destruct ls1, ls2; cbn in *; constructor; tauto.
      intros ? CONTRA; inv CONTRA.
  Qed.

  Lemma model_E1E2_12_orutt_strict :
    forall t1 t2 ls1 ls2,
      L1_E1E2_orutt_strict t1 t2 ->
      local_stack_refine_strict ls1 ls2 ->
      L2_E1E2_orutt_strict (interp_local_stack t1 ls1) (interp_local_stack t2 ls2).
  Proof.
    intros t1 t2 ls1 ls2 RL1 LSR.
    red in RL1.

    unfold interp_local_stack.
    eapply orutt_interp_state; eauto.
    { unfold local_stack_refine_strict in *.
      destruct ls1, ls2;
      constructor; tauto.
    }

    intros A B e1 e2 s1 s2 H H0.
    eapply orutt_interp_local_stack_h_debug; eauto.
    inv H0.
    destruct s1, s2; cbn in *; auto.

    intros A o s.
    exists o.
    cbn.
    setoid_rewrite bind_trigger.
    exists (fun x : A => IS2.SemNotations.Ret1 s x).
    reflexivity.
  Qed.
End LocalStackRefine.
