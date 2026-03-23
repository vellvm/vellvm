From Stdlib Require Import
  Relations
  String
  List
  Lia
  ZArith
  Morphisms.

Require Import Stdlib.Logic.ProofIrrelevance.

From Vellvm Require Import
  Semantics.InterpretationStack
  Semantics.LLVMEvents
  Semantics.Denotation
  Semantics.MemoryAddress
  Semantics.Memory.Sizeof
  Semantics.Lang
  Semantics.InterpretationStack
  Semantics.TopLevel
  Semantics.DynamicValues
  Semantics.VellvmIntegers
  Semantics.LLVMParams
  Semantics.InfiniteToFinite.Conversions.BaseConversions
  Semantics.InfiniteToFinite.Conversions.DvalueConversions
  Semantics.InfiniteToFinite.Conversions.EventConversions
  Semantics.InfiniteToFinite.Conversions.TreeConversions
  Semantics.InfiniteToFinite.R2Injective
  Semantics.Memory.DvalueBytes
  Syntax.DynamicTypes
  Theory.TopLevelRefinements
  Theory.ContainsUB
  Utils.Error
  Utils.Monads
  Utils.MapMonadExtra
  Utils.PropT
  Utils.InterpProp
  Utils.InterpPropOOM
  Utils.ListUtil
  Utils.Tactics
  Utils.OOMRutt
  Utils.OOMRuttProps
  Utils.RuttPropsExtra
  Utils.AListFacts
  Utils.VellvmRelations
  Utils.ErrUbOomProp
  Utils.ErrOomPoison
  Utils.Oomable
  Utils.Poisonable
  Utils.NMaps
  Utils.IntMaps
  Handlers.MemoryModules.FiniteAddresses
  Handlers.MemoryModules.InfiniteAddresses
  Handlers.MemoryModelImplementation
  Handlers.SerializationTheory.

From Vellvm.Semantics.InfiniteToFinite.LangRefine Require Import
  Events
  Sizeof
  Values
  Vectors
  Bytes
  IntegerUtils
  IntegerOps
  IntegerCmps
  FloatOps
  PointerOps
  AggregateOps
  Select
  Conversions
  GEP
  Utils
  Concretization
  Expressions
  MemoryOps
  Functions
  Exceptions
  MCFG
  Phis
  Atomics
  Blocks
  Calls
  Instructions
  Globals
  LocalStack
  Builtins.

From ExtLib Require Import
  Structures.Monads
  Structures.Functor.

From ITree Require Import
  ITree
  Basics
  Basics.HeterogeneousRelations
  Eq.Rutt
  Eq.RuttFacts
  Eq.Eqit
  Eq.EqAxiom.

Require Import Stdlib.Program.Equality.
Require Import Paco.paco.

Import InterpFacts.

Import MonadNotation.
Import ListNotations.
Import Classical.

(* TODO: Move these *)
Program Fixpoint Forall2_HInT {A B : Type}
  (xs : list A) (ys : list B) (R : forall a b, InT a xs -> InT b ys -> Prop) : Prop :=
  match xs, ys with
  | [], [] => True
  | (x::xs), (y::ys) =>
      R x y _ _ /\ Forall2_HInT xs ys (fun x y IN1 IN2 => R x y _ _)
  | _, _ =>
      False
  end.
Next Obligation.
  exact (inl eq_refl).
Defined.
Next Obligation.
  exact (inl eq_refl).
Defined.
Next Obligation.
  exact (inr IN1).
Defined.
Next Obligation.
  exact (inr IN2).
Defined.
Next Obligation.
  split. intros; intro C.
  intuition. inversion H.
  intro C. intuition. inversion H0.
Defined.
Next Obligation.
  split. intros; intro C.
  intuition. inversion H0.
  intro C. intuition. inversion H.
Defined.

(* Lemma map_monad_InT_oom_forall2 : *)
(*   forall {A B} l (f : forall (a : A), InT a l -> OOM B) res, *)
(*     map_monad_InT l f = NoOom res <-> *)
(*       Forall2_HInT l res (fun a b INA INB => f a INA = NoOom b). *)
(* Proof. *)
(*   intros A B. *)
(*   induction l; intros f res. *)
(*   - split; intros MAP. *)
(*     + cbn in *. *)
(*       inv MAP. *)
(*       auto. *)
(*     + cbn in *. *)
(*       break_match_hyp; tauto. *)
(*   - split; intros MAP. *)
(*     + rewrite map_monad_InT_unfold in MAP. *)
(*       cbn in *. *)
(*       break_match_hyp; inv MAP. *)
(*       break_match_hyp; inv H0. *)

(*       pose proof (IHl (fun (x : A) (HIn : InT x l) => f x (inr HIn)) l0) as FORALL. *)
(*       constructor; auto. *)
(*       eapply FORALL. eauto. *)
(*     + rewrite map_monad_InT_cons. *)
(*       cbn in *. *)
(*       break_match_hyp; try contradiction. *)
(*       cbn in *. *)
(*       destruct MAP as [FA MAP]. *)
(*       rewrite FA. *)

(*       pose proof (IHl (fun (x : A) (HIn : InT x l) => f x (inr HIn)) l0) as FORALL. *)
(*       apply FORALL in MAP. *)
(*       rewrite MAP. *)
(*       auto. *)
(* Qed. *)

Lemma Forall2_Forall2_HInT :
  forall {A B : Type} (xs : list A) (ys : list B) f,
    Forall2 f xs ys <->
      Forall2_HInT xs ys (fun a b HIna HInb => f a b).
Proof.
  intros A B xs ys f.
  split; intros H.
  - induction H; cbn; auto.
  - remember (xs, ys) as ZIP.
    replace xs with (fst ZIP) in H by (subst; cbn; auto).
    replace xs with (fst ZIP) by (subst; cbn; auto).
    replace ys with (snd ZIP) in H by (subst; cbn; auto).
    replace ys with (snd ZIP) by (subst; cbn; auto).
    clear HeqZIP xs ys.

    induction ZIP using double_list_rect;
      cbn in *; try contradiction.
    + constructor.
    + destruct H.
      constructor; eauto.
Qed.

Import VellvmIntegers.


Module Type LangRefine
  (IS1 : InterpreterStack)
  (IS2 : InterpreterStack)
  (AC1 : AddrConvert IS1.LP.ADDR IS1.LP.PTOI IS2.LP.ADDR IS2.LP.PTOI)
  (AC2 : AddrConvert IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI)
  (LLVM1 : LLVMTopLevel IS1)
  (LLVM2 : LLVMTopLevel IS2)
  (TLR1 : TopLevelRefinements IS1 LLVM1)
  (TLR2 : TopLevelRefinements IS2 LLVM2)
  (IPS : IPConvertSafe IS2.LP.IP IS1.LP.IP)
  (ACS : AddrConvertSafe IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI AC2 AC1)
  (DVC : DVConvert IS1.LP IS2.LP AC1)
  (DVCrev : DVConvert IS2.LP IS1.LP AC2)
  (EC : EventConvert IS1.LP IS2.LP AC1 AC2 DVC DVCrev)
  (TC : TreeConvert IS1 IS2 AC1 AC2 DVC DVCrev EC)
  (VMEM_IP_PROP1 : VMemInt_Intptr_Properties IS1.LP.IP)
  (VMEM_IP_PROP2 : VMemInt_Intptr_Properties IS2.LP.IP)
  (VMEM_REF : VMemInt_Refine IS1.LP.IP IS2.LP.IP)
  (SIZEOF_REF : Sizeof_Refine IS1.LP.SZ IS2.LP.SZ) (ITOP_REF : ItoP_Refine IS1 IS2 AC1 AC2).
  Import TLR2.

  Import TC.
  Import EC.
  Import DVC.
  Import IPS.
  Import ACS.

  Import SIZEOF_REF.
  Import ITOP_REF.

  (* Module DVCSafe := DVConvertSafe IS2.LP IS1.LP AC2 AC1 ACS IPS DVCrev DVC. *)
  (* Import DVCSafe. *)

  Module MBT := MemBytesTheory IS2.LP IS2.LLVM.MEM.MP ByteM IS2.LLVM.MEM.CP.
  Import MBT.


  Import TranslateFacts.
  Import RecursionFacts.

  Import CONCBASE.

  Import Utils.InterpEither.
  Import EitherMonad.

  Include (EventRefine IS1 IS2 LLVM1 LLVM2 AC1 AC2 DVC DVCrev EC).
  Include (ValueRefine
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
             SIZEOF_REF).
  Include (VectorsRefine
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
             SIZEOF_REF).
  Include (BytesRefine
             IS1
             IS2
             LLVM1
             LLVM2
             TLR1
             TLR2
             AC1
             AC2
             IPS
             ACS
             DVC
             DVCrev
             EC
             SIZEOF_REF
             ITOP_REF).
  Include (IntOpsRefine
             IS1
             IS2
             LLVM1
             LLVM2
             TLR1
             TLR2
             AC1
             AC2
             IPS
             ACS
             DVC
             DVCrev
             EC
             SIZEOF_REF
             VMEM_IP_PROP1
             VMEM_IP_PROP2
             VMEM_REF).
  Include (IntCmpsRefine
             IS1
             IS2
             LLVM1
             LLVM2
             TLR1
             TLR2
             AC1
             AC2
             IPS
             ACS
             DVC
             DVCrev
             EC
             SIZEOF_REF
             VMEM_IP_PROP1
             VMEM_IP_PROP2
             VMEM_REF).
  Include (FloatOpsRefine
             IS1
             IS2
             LLVM1
             LLVM2
             TLR1
             TLR2
             AC1
             AC2
             IPS
             ACS
             DVC
             DVCrev
             EC
             SIZEOF_REF).
  Include (ConversionsRefine
             IS1
             IS2
             LLVM1
             LLVM2
             TLR1
             TLR2
             AC1
             AC2
             IPS
             ACS
             DVC
             DVCrev
             EC
             SIZEOF_REF
             ITOP_REF).
  Include (GEPRefine
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
             ITOP_REF).
  Include (AggregateOpsRefine
             IS1
             IS2
             LLVM1
             LLVM2
             TLR1
             TLR2
             AC1
             AC2
             IPS
             ACS
             DVC
             DVCrev
             EC
             SIZEOF_REF).
  Include (SelectRefine
             IS1
             IS2
             LLVM1
             LLVM2
             TLR1
             TLR2
             AC1
             AC2
             IPS
             ACS
             DVC
             DVCrev
             EC
             SIZEOF_REF).
  Include (ConcretizationRefine             
             IS1
             IS2
             LLVM1
             LLVM2
             TLR1
             TLR2
             AC1
             AC2
             IPS
             ACS
             DVC
             DVCrev
             EC
             SIZEOF_REF
             ITOP_REF
             VMEM_IP_PROP1
             VMEM_IP_PROP2
             VMEM_REF).
  Include (ExpressionsRefine
             IS1
             IS2
             LLVM1
             LLVM2
             TLR1
             TLR2
             AC1
             AC2
             IPS
             ACS
             DVC
             DVCrev
             EC
             SIZEOF_REF
             ITOP_REF
             VMEM_IP_PROP1
             VMEM_IP_PROP2
             VMEM_REF).
  Include (MemoryOpsRefine
             IS1
             IS2
             LLVM1
             LLVM2
             TLR1
             TLR2
             AC1
             AC2
             IPS
             ACS
             DVC
             DVCrev
             EC
             SIZEOF_REF
             ITOP_REF
             VMEM_IP_PROP1
             VMEM_IP_PROP2
             VMEM_REF).
  Include (CallsRefine
             IS1
             IS2
             LLVM1
             LLVM2
             TLR1
             TLR2
             AC1
             AC2
             IPS
             ACS
             DVC
             DVCrev
             EC
             SIZEOF_REF
             ITOP_REF
             VMEM_IP_PROP1
             VMEM_IP_PROP2
             VMEM_REF).
  Include (PhisRefine
             IS1
             IS2
             LLVM1
             LLVM2
             TLR1
             TLR2
             AC1
             AC2
             IPS
             ACS
             DVC
             DVCrev
             EC
             SIZEOF_REF
             ITOP_REF
             VMEM_IP_PROP1
             VMEM_IP_PROP2
             VMEM_REF).
  Include (AtomicsRefine
             IS1
             IS2
             LLVM1
             LLVM2
             TLR1
             TLR2
             AC1
             AC2
             IPS
             ACS
             DVC
             DVCrev
             EC
             SIZEOF_REF
             ITOP_REF
             VMEM_IP_PROP1
             VMEM_IP_PROP2
             VMEM_REF).
  Include (InstructionsRefine
             IS1
             IS2
             LLVM1
             LLVM2
             TLR1
             TLR2
             AC1
             AC2
             IPS
             ACS
             DVC
             DVCrev
             EC
             SIZEOF_REF
             ITOP_REF
             VMEM_IP_PROP1
             VMEM_IP_PROP2
             VMEM_REF).
  Include (BlocksRefine
             IS1
             IS2
             LLVM1
             LLVM2
             TLR1
             TLR2
             AC1
             AC2
             IPS
             ACS
             DVC
             DVCrev
             EC
             SIZEOF_REF
             ITOP_REF
             VMEM_IP_PROP1
             VMEM_IP_PROP2
             VMEM_REF).
  Include (FunctionsRefine
             IS1
             IS2
             LLVM1
             LLVM2
             TLR1
             TLR2
             AC1
             AC2
             IPS
             ACS
             DVC
             DVCrev
             EC
             SIZEOF_REF
             ITOP_REF
             VMEM_IP_PROP1
             VMEM_IP_PROP2
             VMEM_REF).
  Include (GlobalsRefine
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
             SIZEOF_REF).
  Include (LocalStackRefine
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
             SIZEOF_REF).
  Include (BuiltinsRefine
             IS1
             IS2
             LLVM1
             LLVM2
             TLR1
             TLR2
             AC1
             AC2
             IPS
             ACS
             DVC
             DVCrev
             EC
             SIZEOF_REF
             ITOP_REF
             VMEM_IP_PROP1
             VMEM_IP_PROP2
             VMEM_REF).
  Include (ExceptionsRefine
             IS1
             IS2
             LLVM1
             LLVM2
             TLR1
             TLR2
             AC1
             AC2
             IPS
             ACS
             DVC
             DVCrev
             EC
             SIZEOF_REF
             VMEM_IP_PROP1
             VMEM_IP_PROP2
             VMEM_REF).
  Include (MCFGRefine
             IS1
             IS2
             LLVM1
             LLVM2
             TLR1
             TLR2
             AC1
             AC2
             IPS
             ACS
             DVC
             DVCrev
             EC
             SIZEOF_REF
             ITOP_REF
             VMEM_IP_PROP1
             VMEM_IP_PROP2
             VMEM_REF).

  Lemma model_E1E2_01_orutt_strict :
    forall t1 t2 g1 g2,
      L0_E1E2_orutt_strict t1 t2 ->
      global_refine_strict g1 g2 ->
      L1_E1E2_orutt_strict (interp_global (IS1.LLVM.Intrinsics.interp_intrinsics t1) g1) (interp_global (IS2.LLVM.Intrinsics.interp_intrinsics t2) g2).
  Proof.
    intros t1 t2 g1 g2 RL0 GENVS.
    red in RL0.
    apply E1E2_interp_global_orutt_strict; auto.
    apply E1E2_interp_intrinsics_orutt_strict; auto.
  Qed.

  Lemma model_E1E2_L0_orutt_strict_sound
    (args1 : list DV1.uvalue)
    (args2 : list uvalue)
    (ARGS : Forall2 uvalue_refine_strict args1 args2)
    (p : list
           (LLVMAst.toplevel_entity
              LLVMAst.typ
              (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ)))) :
    model_E1E2_L0_orutt_strict args1 args2 p p.
  Proof.
    red.

    unfold LLVM2.denote_vellvm.
    unfold LLVM1.denote_vellvm.
    eapply orutt_bind; [apply build_global_environment_E1E2_orutt_strict_sound|].

    intros [] [] _.
    eapply orutt_bind; [apply address_one_functions_E1E2_orutt|].

    intros r1' r2' R1R2'.
    eapply orutt_bind; [apply address_one_builtin_functions_E1E2_orutt; apply builtins_refine_strict|].

    intros r1 r2 R1R2.
    eapply orutt_bind;
      [apply rutt_orutt;
       [try apply GlobalRead_L0_E1E2_rutt | idtac]|].
    intros ? s; repeat destruct s;
    try solve
      [
        left;
        intros o CONTRA;
        inv CONTRA
      ];
    right;
    eexists; reflexivity.


    intros r3 r4 R3R4.
    eapply orutt_bind.

    { apply denote_mcfg_E1E2_orutt; auto.
      - apply IM_Refine_of_list_app; eauto.
      - apply dvalue_refine_strict_dvalue_to_uvalue; auto.
    }

    intros r0 r5 H.
    destruct H.
    { apply orutt_raiseLLVM.
      intros ? ? CONTRA; inv CONTRA.
      cbn; auto.
    }

    eapply orutt_bind with (RR:=fun x y => dvalue_refine_strict (proj1_sig x) (proj1_sig y)).
    { (* Pick *)
      apply orutt_trigger.
      { cbn; auto.
      }

      intros t1 t2 H0.
      cbn in *.
      destruct t1, t2; tauto.
      intros o CONTRA; inv CONTRA.
    }

    intros r6 r7 H0.
    cbn.
    apply orutt_Ret; auto.
  Qed.

  Lemma model_E1E2_L1_orutt_strict_sound
    (args : list string)
    (p : list
           (LLVMAst.toplevel_entity
              LLVMAst.typ
              (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ)))) :
    model_E1E2_L1_orutt_strict args args p p.
  Proof.
    apply model_E1E2_01_orutt_strict.
    - eapply orutt_bind with (RR:=Forall2 uvalue_refine_strict).
      + apply rutt_orutt.
        apply build_main_args_fin_inf.
        intros ? s. repeat destruct s;
    try solve
      [
        left;
        intros o CONTRA;
        inv CONTRA
      ];
    right;
    eexists; reflexivity.
      + intros r1 r2 H.
        intros *; apply model_E1E2_L0_orutt_strict_sound; auto.
    - apply global_refine_strict_empty.
  Qed.

  Lemma model_E1E2_L2_orutt_strict_sound
    (args : list string)
    (p : list
           (LLVMAst.toplevel_entity
              LLVMAst.typ
              (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ)))) :
    model_E1E2_L2_orutt_strict args args p p.
  Proof.
    apply model_E1E2_12_orutt_strict;
      [ apply model_E1E2_L1_orutt_strict_sound
      | apply local_stack_refine_strict_empty
      ].
  Qed.

End LangRefine.

Module MakeLangRefine
  (IS1 : InterpreterStack) (IS2 : InterpreterStack)
  (AC1 : AddrConvert IS1.LP.ADDR IS1.LP.PTOI IS2.LP.ADDR IS2.LP.PTOI)
  (AC2 : AddrConvert IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI)
  (LLVM1 : LLVMTopLevel IS1) (LLVM2 : LLVMTopLevel IS2)
  (TLR1 : TopLevelRefinements IS1 LLVM1) (TLR2 : TopLevelRefinements IS2 LLVM2)
  (IPS : IPConvertSafe IS2.LP.IP IS1.LP.IP)
  (ACS : AddrConvertSafe IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI AC2 AC1)
  (DVC : DVConvert IS1.LP IS2.LP AC1)
  (DVCrev : DVConvert IS2.LP IS1.LP AC2)
  (EC : EventConvert IS1.LP IS2.LP AC1 AC2 DVC DVCrev)
  (TC : TreeConvert IS1 IS2 AC1 AC2 DVC DVCrev EC)
  (VMEM_IP_PROP1 : VMemInt_Intptr_Properties IS1.LP.IP)
  (VMEM_IP_PROP2 : VMemInt_Intptr_Properties IS2.LP.IP)
  (VMEM_REF : VMemInt_Refine IS1.LP.IP IS2.LP.IP)
  (SZ_REF : Sizeof_Refine IS1.LP.SZ IS2.LP.SZ)
  (ITOP_REF : ItoP_Refine IS1 IS2 AC1 AC2) : LangRefine IS1 IS2 AC1 AC2 LLVM1 LLVM2 TLR1 TLR2 IPS ACS DVC DVCrev EC TC VMEM_IP_PROP1 VMEM_IP_PROP2 VMEM_REF SZ_REF ITOP_REF.
  Include LangRefine IS1 IS2 AC1 AC2 LLVM1 LLVM2 TLR1 TLR2 IPS ACS DVC DVCrev EC TC VMEM_IP_PROP1 VMEM_IP_PROP2 VMEM_REF SZ_REF ITOP_REF.
End MakeLangRefine.

Module InfFinLangRefine := MakeLangRefine InterpreterStackBigIntptr InterpreterStack64BitIntptr InfToFinAddrConvert FinToInfAddrConvert TopLevelBigIntptr TopLevel64BitIntptr TopLevelRefinementsBigIntptr TopLevelRefinements64BitIntptr FinToInfIntptrConvertSafe FinToInfAddrConvertSafe DVCInfFin DVCFinInf ECInfFin TCInfFin VMemInt_Intptr_Properties_Inf VMemInt_Intptr_Properties_Fin VMemInt_Refine_InfFin Sizeof_Refine_InfFin ItoP_Refine_InfFin.

(* Just planning on using this for L4_convert from finite to infinite events. *)
(* Module FinInfLangRefine := MakeLangRefine InterpreterStack64BitIntptr InterpreterStackBigIntptr FinToInfAddrConvert InfToFinAddrConvert TopLevel64BitIntptr TopLevelBigIntptr TopLevelRefinementsBigIntptr FinToInfIntptrConvertSafe. DVCFinInf DVCInfFin ECFinInf . *)
