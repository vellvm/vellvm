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
  VellvmRelations.

From ITree Require Import
  ITree
  Basics.HeterogeneousRelations
  Eq.Rutt
  Eq.RuttFacts
  Eq.Eqit.

Import ListNotations.

Module Type GlobalsRefine
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

    Lemma orutt_interp_global_h :
      forall A B e1 e2 genv1 genv2,
        event_refine_strict A B e1 e2 ->
        global_refine_strict genv1 genv2 ->
        orutt L1_refine_strict L1_res_refine_strict
          (fun '(s0, a) '(s3, b) => event_res_refine_strict A B e1 a e2 b /\ global_refine_strict s0 s3)
          (interp_global_h e1 genv1) (interp_global_h e2 genv2)
          (OOM:=OOME).
    Proof.
    intros A B e1 e2 genv1 genv2 REF GREF.
    destruct e1; repeat (destruct e); repeat (destruct s);
    try
      solve
        [
          cbn in REF;
          destruct e2; try inv REF;
          repeat (break_match_hyp; try inv REF);
          cbn in *;
          pstep; red; cbn;
          constructor; cbn; auto;
          [ intros ? ? ?;
              left;
            pstep; red; cbn;
            constructor; auto
          | intros o CONTRA; inv CONTRA
          ]
        ].

    all: try
           solve
           [ cbn in REF;
             destruct e2; try inv REF;
             repeat (break_match_hyp; try inv REF);
             cbn in *;
             (pstep; red; cbn;
              constructor; cbn; try tauto;
              [ intros ? ? ?; left; apply orutt_Ret; tauto
              | intros o CONTRA; inv CONTRA
             ])
           |
             cbn in REF;
             destruct e2; try inv REF;
             repeat (break_match_hyp; try inv REF);
             cbn in *;
             (pstep; red; cbn;
              constructor; cbn;
              [ first [red; red; auto | tauto]
              | intros ? ? ?; left; apply orutt_Ret; tauto
              | intros o CONTRA; inv CONTRA
             ])
           ].

    -
      cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF).
      + cbn in *.
        subst.
        red in REF.
        destruct l, l0; cbn in *; try contradiction.
        -- repeat setoid_rewrite bind_ret_l.
           apply orutt_Ret.
           split; auto.
           destruct REF; subst.
           apply global_refine_strict_add; auto.
        -- subst.
           pose proof GREF as GREF'.
           do 2 red in GREF.
           specialize (GREF id0).
           red in GREF.
           repeat setoid_rewrite bind_ret_l.
           break_match_goal; break_match_goal;
             repeat setoid_rewrite bind_ret_l; try contradiction.
           apply orutt_Ret; eauto.
           eapply orutt_bind with (RR:=prod_rel global_refine_strict dvalue_refine_strict).
           solve_orutt_raise.
           intros (g1 & r1) (g2 & r2) (G & R).
           cbn in *.
           apply orutt_Ret.
           split; auto.
    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF).

      { cbn.
        inversion o.
        inversion o0.
        subst.
        setoid_rewrite bind_trigger.
        cbn.
        pstep; red; cbn.
        (* SAZ: There has got to be a better way !*)
           change 
          (@subevent ((LLVMEnvE _ +' LLVMStackE _) +' MemoryE _ _ +' PickUvalueE _ _ +' OOME +' LLVMExcE uvalue +' UBE +' DebugE +' FailureE) (ExternalCallE _ _ +' IntrinsicE _ _ +' (LLVMEnvE _ +' LLVMStackE _) +' MemoryE _ _ +' PickUvalueE _ _+' OOME +' LLVMExcE uvalue +' UBE +' DebugE +' FailureE)
             (@ReSum_inr (Type -> Type) IFun sum1 Cat_IFun Inr_sum1 ((LLVMEnvE _ +' LLVMStackE _) +' MemoryE _ _ +' PickUvalueE _ _ +' OOME +' LLVMExcE uvalue +' UBE +' DebugE +' FailureE) (IntrinsicE _ _ +' (LLVMEnvE _ +' LLVMStackE _) +' MemoryE _ _ +' PickUvalueE _ _ +' OOME +' LLVMExcE uvalue +' UBE +' DebugE +' FailureE) (ExternalCallE _ _)
                (@ReSum_inr (Type -> Type) IFun sum1 Cat_IFun Inr_sum1 ((LLVMEnvE _ +' LLVMStackE _) +' MemoryE _ _ +' PickUvalueE _ _ +' OOME +' LLVMExcE uvalue +' UBE +' DebugE +' FailureE) ((LLVMEnvE _ +' LLVMStackE _) +' MemoryE _ _ +' PickUvalueE _ _ +' OOME +' LLVMExcE uvalue +' UBE +' DebugE +' FailureE) (IntrinsicE _ _)
                   (@ReSum_id (Type -> Type) IFun Id_IFun ((LLVMEnvE _ +' LLVMStackE _) +' MemoryE _ _ +' PickUvalueE _ _ +' OOME +' LLVMExcE uvalue +' UBE +' DebugE +' FailureE))))
             void
             (@inr1 (LLVMEnvE _ +' LLVMStackE _) (MemoryE _ _ +' PickUvalueE _ _ +' OOME +' LLVMExcE uvalue +' UBE +' DebugE +' FailureE) void
                (@inr1 (MemoryE _ _) (PickUvalueE _ _ +' OOME +' LLVMExcE uvalue +' UBE +' DebugE +' FailureE) void (@inr1 (PickUvalueE _ _) (OOME +' LLVMExcE uvalue +' UBE +' DebugE +' FailureE) void (@inl1 OOME (LLVMExcE uvalue +' UBE +' DebugE +' FailureE) void o0)))))
          with (@subevent OOME (@L1 DV2.dvalue DV2.uvalue) _ _ o0).

        apply EqVisOOM.
      }
    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF).

       { cbn.
         setoid_rewrite bind_trigger.
         apply orutt_Vis.
         constructor.
         intros.
         apply orutt_Ret; split; eauto.
         intros o CONTRA; inv CONTRA.
      }
    Qed.

  Lemma E1E2_interp_global_orutt_strict :
    forall t1 t2 g1 g2,
      L0_E1E2_orutt_strict t1 t2 ->
      global_refine_strict g1 g2 ->
      L1_E1E2_orutt_strict (interp_global t1 g1) (interp_global t2 g2).
  Proof.
    intros t1 t2 g1 g2 RL0 GENVS.
    unfold interp_global.
    unfold State.interp_state.
    red.
    red in RL0.

    eapply orutt_interp_state; eauto.
    { intros A B e1 e2 s1 s2 H H0.
      apply orutt_interp_global_h; auto.
    }
    { intros A o s.
      cbn.
      setoid_rewrite bind_trigger.
      exists (resum IFun A o).
      exists (fun x : A => IS2.SemNotations.Ret1 s x).
      reflexivity.
    }
  Qed.
End GlobalsRefine.
