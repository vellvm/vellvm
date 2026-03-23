From Stdlib Require Import
  Lia
  ZArith
  Program.Equality
  String
  List.

From ExtLib Require Import
  Structures.Monads
  Structures.Functor
  EitherMonad.

From Vellvm Require Import
  TopLevelRefinements.

From Vellvm.Semantics Require Import
  MemoryAddress
  VellvmIntegers
  DynamicValues
  InterpretationStack
  TopLevel
  LLVMEvents.

From Vellvm.Semantics.InfiniteToFinite.Conversions Require Import
  BaseConversions
  DvalueConversions
  EventConversions.

From Vellvm.Utils Require Import
  Error
  Tactics
  ListUtil
  OOMRutt
  OOMRuttProps
  InterpEither.

From Vellvm.Semantics.InfiniteToFinite.LangRefine Require Import
  Events
  Sizeof
  Values
  Vectors
  IntegerUtils.

From ITree Require Import
  ITree
  Basics.HeterogeneousRelations
  Eq.Rutt
  Eq.RuttFacts
  Eq.Eqit.

Require Import Stdlib.Program.Equality.
Require Import Paco.paco.

Module Type ExceptionsRefine
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
  (VMEM_IP_PROP1 : VMemInt_Intptr_Properties IS1.LP.IP)
  (VMEM_IP_PROP2 : VMemInt_Intptr_Properties IS2.LP.IP)
  (VMEM_REF : VMemInt_Refine IS1.LP.IP IS2.LP.IP)
  (ER : EventRefine IS1 IS2 LLVM1 LLVM2 AC1 AC2 DVC DVCrev EC)
  (VAL_REF : ValueRefine 
               IS1 IS2
               LLVM1 LLVM2
               AC1 AC2
               IPS ACS
               DVC DVCrev
               EC SIZEOF_REF ER)
  (VEC_REF : VectorsRefine
               IS1
               IS2
               LLVM1
               LLVM2
               AC1
               AC2
               IPS
               ACS
               DVC
               DVCrev
               EC
               SIZEOF_REF
               ER
               VAL_REF).

  Import EC.
  Import DV2.
  Import IS2.LP.
  Import DynamicTypes.
  Import IPS.
  Import ER.
  Import VAL_REF.
  Import VEC_REF.
  Import DVC.
  Import TLR2.

  (* TODO: Move this *)
  Lemma raiseOOM_bind_itree_eq_itree :
    forall {E} `{OOME -< E} A B (f : A -> itree E B) x,
      bind (raiseOOM x) f ≅ raiseOOM x.
  Proof using.
    intros E OOM A B f x.
    unfold raiseOOM.
    cbn.
    rewrite bind_bind.
    eapply eq_itree_clo_bind.
    reflexivity.
    intros u1 u2 H.
    destruct u1.
  Qed.

  Lemma interp_either_orutt :
    forall {E1 E2 F1 F2 X Y EXC1 EXC2}
      `{OOME2 : OOME -< E2}
      `{OOMF2 : OOME -< F2}
      (pre1 : prerel E1 E2)
      (pre2 : prerel F1 F2)
      (post1 : postrel E1 E2)
      (post2 : postrel F1 F2)
      (RXY : X -> Y -> Prop)
      (REXC : EXC1 -> EXC2 -> Prop)
      (h1 : E1 ~> eitherT EXC1 (itree F1))
      (h2 : E2 ~> eitherT EXC2 (itree F2))
      (PRE12 : forall (A B : Type) (e1 : E1 A) (e2 : E2 B),
          pre1 A B e1 e2 ->
          orutt (OOME:=OOMF2) pre2 post2 (sum_rel REXC (fun a b => post1 A B e1 a e2 b)) (unEitherT (h1 A e1)) (unEitherT (h2 B e2)))
      (* (POST12 : forall (A B : Type) (e1 : E1 A) (a : A) (e2 : E2 B) (b : B),
          post2 A B (h1 A e1) a (h2 B e2) b -> post1 A B e1 a e2 b) *)
      (OOMH2 : forall A (e : OOME A), unEitherT (h2 A (subevent A e)) ≅ raiseOOM "")
      (t1 : itree E1 X) (t2 : itree E2 Y)
      (ORUTT : orutt (OOME:=OOME2) pre1 post1 RXY t1 t2),
      orutt (OOME:=OOMF2) pre2 post2 (sum_rel REXC RXY)
            (unEitherT (interp_either h1 t1))
            (unEitherT (interp_either h2 t2)).
  Proof.
    intros.
    rewrite (EqAxiom.itree_eta_ t1) in *.
    rewrite (EqAxiom.itree_eta_ t2) in *.
    genobs t1 ot1.
    genobs t2 ot2.
    clear t1 t2 Heqot1 Heqot2.
    revert ot1 ot2 ORUTT.
    ginit. gcofix CIH.
    intros t1 t2 ORUTT.
    punfold ORUTT.
    red in ORUTT; cbn in ORUTT.
    hinduction ORUTT before r; intros.
    - rewrite !interp_either_ret'.
      cbn.
      gstep; constructor.
      constructor; auto.
    - rewrite !interp_either_tau'.
      gstep; constructor.
      gbase.
      rewrite (EqAxiom.itree_eta_ m1).
      rewrite (EqAxiom.itree_eta_ m2).
      apply CIH.
      pclearbot.
      rewrite <- !itree_eta.
      apply H.
    - (* TODO: proper instances for eq_either_itree *)
      epose proof interp_either_vis'.
      unfold eq_either_itree in *.
      rewrite H2.
      epose proof interp_either_vis'.
      unfold eq_either_itree in *.
      rewrite H3.
      clear H2 H3.
      eapply gpaco2_uclo; [|eapply orutt_clo_bind|]; eauto with paco.
      econstructor.
      (* Assumption *)
      apply PRE12; auto.

      intros u1 u2 H2.
      destruct H2.
      + gstep; red; constructor.
        constructor; auto.
      + rewrite !interp_either_tau'.
        gstep; red; constructor.
        gbase.
        rewrite (EqAxiom.itree_eta_ (k1 b1)).
        rewrite (EqAxiom.itree_eta_ (k2 b2)).
        apply CIH.
        rewrite <- !itree_eta.
        pclearbot.
        apply H0; auto.
    - (* OOM *)
      (* TODO: proper instances for eq_either_itree *)
      epose proof interp_either_vis'.
      unfold eq_either_itree in *.
      rewrite H.
      clear H.
      cbn.
      rewrite OOMH2.
      setoid_rewrite raiseOOM_bind_itree_eq_itree.
      gfinal.
      right.
      eapply paco2_mon_bot.
      eapply orutt_raiseOOM.
      intros x0 x1 x2 PR.
      apply PR.
    - (* TauL *)
      rewrite interp_either_tau'.
      rewrite tau_euttge.
      rewrite (EqAxiom.itree_eta_ t1).
      eauto with itree.
    - (* TauR *)
      rewrite interp_either_tau'.
      rewrite tau_euttge.
      rewrite (EqAxiom.itree_eta_ t2).
      eauto with itree.
  Qed.

  Lemma catch_llvm_exc_L0'_orutt :
    forall (t1 : itree (L0' DV1.dvalue DV1.uvalue) DV1.uvalue) (t2 : itree (L0' _ _) DV2.uvalue),
      orutt (OOM:=OOME) L0'_refine_strict L0'_res_refine_strict uvalue_refine_strict t1 t2 ->
      orutt (OOM:=OOME) L0'_refine_strict L0'_res_refine_strict (sum_rel uvalue_refine_strict uvalue_refine_strict)
        (EitherMonad.unEitherT (IS1.LLVM.D.catch_llvm_exc_L0' t1))
        (EitherMonad.unEitherT (catch_llvm_exc_L0' t2)).
(*
      orutt (OOM:=OOME) (sum_prerel call_refine_strict event_refine_strict)
        (sum_postrel call_res_refine_strict event_res_refine_strict)
        (sum_rel uvalue_refine_strict uvalue_refine_strict)
        (EitherMonad.unEitherT (IS1.LLVM.D.catch_llvm_exc_L0' t1))
        (EitherMonad.unEitherT (catch_llvm_exc_L0' t2)). *)
  Proof.
    intros t1 t2 ORUTT.
    unfold catch_llvm_exc_L0'.
    unfold IS1.LLVM.D.catch_llvm_exc_L0'.
    eapply interp_either_orutt with (pre1:=L0'_refine_strict); eauto.
    - intros A B e1 e2 H.
      unfold IS1.LLVM.D.catch_llvm_exc_L0'_h.
      unfold IS2.LLVM.D.catch_llvm_exc_L0'_h.
      destruct H.

      { cbn.
        eapply orutt_bind.
        - apply orutt_trigger; cbn; eauto.
          constructor; auto.
          intros t0 t3 H0.
          apply H0.
          intros o CONTRA.
          inv CONTRA.
        - intros r1 r2 H0.
          apply orutt_Ret.
          constructor; auto.
      }

      destruct e2, d2; try inversion H.
      { cbn.
        eapply orutt_bind.
        - apply orutt_trigger; cbn; eauto.
          constructor; auto.
          intros t0 t3 H0.
          apply H0.
          intros o CONTRA.
          inv CONTRA.
        - intros r1 r2 H0.
          apply orutt_Ret.
          constructor; auto.
      }

      cbn in H.
      repeat (destruct s; try contradiction).

      cbn in *.
      repeat (try destruct s; try destruct s0; try contradiction); try contradiction;
        try (cbn;
             eapply orutt_bind;
             [ apply orutt_trigger; cbn; eauto;
               try constructor; auto;
               try intros t0 t3 HT0T3;
               try apply HT0T3;
          intros o CONTRA;
          inv CONTRA
       | intros r1 r2 H0;
          apply orutt_Ret;
          constructor; auto
        ]).

      { cbn.
        setoid_rewrite bind_trigger.
        cbn.
        pstep; red; cbn.
        change (@subevent (L0' dvalue uvalue) (L0' dvalue uvalue) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun (L0' dvalue uvalue)) B
          (@inr1 (CallE DV2.uvalue) (L0 DV2.dvalue DV2.uvalue) B
             (@inr1 (ExternalCallE DV2.dvalue DV2.uvalue)
                (sum1 (IntrinsicE DV2.dvalue DV2.uvalue)
                   (sum1 (LLVMGEnvE DV2.dvalue)
                      (sum1 (sum1 (LLVMEnvE DV2.uvalue) (LLVMStackE DV2.uvalue))
                         (sum1 (MemoryE DV2.dvalue DV2.uvalue)
                            (sum1 (PickUvalueE DV2.dvalue DV2.uvalue) (sum1 OOME (sum1 (LLVMExcE DV2.uvalue) (sum1 UBE (sum1 DebugE FailureE)))))))))
                B
                (@inr1 (IntrinsicE DV2.dvalue DV2.uvalue)
                   (sum1 (LLVMGEnvE DV2.dvalue)
                      (sum1 (sum1 (LLVMEnvE DV2.uvalue) (LLVMStackE DV2.uvalue))
                         (sum1 (MemoryE DV2.dvalue DV2.uvalue)
                            (sum1 (PickUvalueE DV2.dvalue DV2.uvalue) (sum1 OOME (sum1 (LLVMExcE DV2.uvalue) (sum1 UBE (sum1 DebugE FailureE))))))))
                   B
                   (@inr1 (LLVMGEnvE DV2.dvalue)
                      (sum1 (sum1 (LLVMEnvE DV2.uvalue) (LLVMStackE DV2.uvalue))
                         (sum1 (MemoryE DV2.dvalue DV2.uvalue)
                            (sum1 (PickUvalueE DV2.dvalue DV2.uvalue) (sum1 OOME (sum1 (LLVMExcE DV2.uvalue) (sum1 UBE (sum1 DebugE FailureE)))))))
                      B
                      (@inr1 (sum1 (LLVMEnvE DV2.uvalue) (LLVMStackE DV2.uvalue))
                         (sum1 (MemoryE DV2.dvalue DV2.uvalue)
                            (sum1 (PickUvalueE DV2.dvalue DV2.uvalue) (sum1 OOME (sum1 (LLVMExcE DV2.uvalue) (sum1 UBE (sum1 DebugE FailureE))))))
                         B
                         (@inr1 (MemoryE DV2.dvalue DV2.uvalue)
                            (sum1 (PickUvalueE DV2.dvalue DV2.uvalue) (sum1 OOME (sum1 (LLVMExcE DV2.uvalue) (sum1 UBE (sum1 DebugE FailureE))))) B
                            (@inr1 (PickUvalueE DV2.dvalue DV2.uvalue) (sum1 OOME (sum1 (LLVMExcE DV2.uvalue) (sum1 UBE (sum1 DebugE FailureE)))) B
                               (@inl1 OOME (sum1 (LLVMExcE DV2.uvalue) (sum1 UBE (sum1 DebugE FailureE))) B o0)))))))))
          with
          (@subevent OOME (L0' dvalue uvalue) _ B o0).                 
        eapply EqVisOOM.
      }

      { red in H.
        destruct l, l0.
        cbn.
        eapply orutt_Ret.
        constructor; auto.
      }
    - intros A o.
      inversion o; subst.
      cbn.
      unfold raiseOOM.
      eapply eq_itree_clo_bind with (UU:=eq).
      2: intros [].
      dependent destruction o.
      destruct u.
      unfold print_msg.
      reflexivity.
  Qed.

End ExceptionsRefine.
