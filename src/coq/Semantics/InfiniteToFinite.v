From Coq Require Import
     Relations
     String
     List
     Lia
     ZArith
     Morphisms.

Require Import Coq.Logic.ProofIrrelevance.

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
     Semantics.LLVMParams
     Semantics.InfiniteToFinite.Conversions.BaseConversions
     Semantics.InfiniteToFinite.Conversions.DvalueConversions
     Semantics.InfiniteToFinite.Conversions.EventConversions
     Semantics.InfiniteToFinite.Conversions.TreeConversions
     Semantics.InfiniteToFinite.LangRefine
     Syntax.DynamicTypes
     Theory.TopLevelRefinements
     Theory.ContainsUB
     Utils.Error
     Utils.Monads
     Utils.MapMonadExtra
     Utils.PropT
     Utils.InterpProp
     Utils.ListUtil
     Utils.Tactics
     Utils.OOMRutt
     Utils.OOMRuttProps
     Handlers.MemoryModules.FiniteAddresses
     Handlers.MemoryModules.InfiniteAddresses
     Handlers.MemoryModelImplementation.

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

Require Import Coq.Program.Equality.
Require Import Paco.paco.

Import InterpFacts.

Import MonadNotation.
Import ListNotations.

Notation LLVM_syntax :=
  (list (LLVMAst.toplevel_entity
              LLVMAst.typ
              (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ)))).

Infix "×" := prod_rel (at level 90, left associativity).

Module InfiniteToFinite.
  (* Import FinInfLangRefine. (* Just planning on using this for L4_convert from finite to infinite events. *) *)
  Import InfFinLangRefine.

  From Vellvm Require Import InterpreterMCFG.

  Import MCFGTheoryBigIntptr.
  Import MCFGTheory64BitIntptr.

  Module TLR_INF := TopLevelRefinementsBigIntptr.
  Module TLR_FIN := TopLevelRefinements64BitIntptr.

  Hint Resolve interp_PropT__mono : paco.

  (* TODO: Move these refine_OOM_h lemmas? *)
  Import Morphisms.


  Module E1 := InterpreterStackBigIntptr.LP.Events.
  Module E2 := InterpreterStack64BitIntptr.LP.Events.

  #[local] Notation E1 := (E1.ExternalCallE +' OOME +' UBE +' DebugE +' FailureE).
  #[local] Notation E2 := (E2.ExternalCallE +' OOME +' UBE +' DebugE +' FailureE).
  #[local] Notation OOM_h := (refine_OOM_handler).

  Module InfLLVM := Vellvm.Semantics.InterpretationStack.InterpreterStackBigIntptr.LLVM.
  Module FinLLVM := Vellvm.Semantics.InterpretationStack.InterpreterStack64BitIntptr.LLVM.

  Module EC1 := ECInfFin.
  Module DVC1 := DVCInfFin.
  Module DVC2 := DVCFinInf.

  Module InfMem := MemoryBigIntptr.
  Module FinMem := Memory64BitIntptr.

  Module InfMemMMSP := MemoryBigIntptr.MMEP.MMSP.
  Module FinMemMMSP := Memory64BitIntptr.MMEP.MMSP.

  Module InfMemInterp := MemoryBigIntptr.MEM_SPEC_INTERP.
  Module FinMemInterp := Memory64BitIntptr.MEM_SPEC_INTERP.

  Module InfLP := InterpreterStackBigIntptr.LP.
  Module FinLP := InterpreterStack64BitIntptr.LP.

  (* Module EC2 := EventConvert FinLP InfLP FinToInfAddrConvert InfToFinAddrConvert FinLP.Events InfLP.Events DVC1. *)

  Module DVCS := DVConvertSafe FinLP InfLP FinToInfAddrConvert InfToFinAddrConvert FinToInfAddrConvertSafe FinToInfIntptrConvertSafe FinLP.Events InfLP.Events DVC2 DVC1.
  Import DVCS.

  (* TODO: Should we move this? *)
  Definition fin_to_inf_addr (a : FinAddr.addr) : InfAddr.addr.
    pose proof FinToInfAddrConvertSafe.addr_convert_succeeds a as [a' CONV].
    apply a'.
  Defined.

  (* TODO: Should we move this? *)
  Definition fin_to_inf_dvalue (dv : LLVMParams64BitIntptr.Events.DV.dvalue) : LLVMParamsBigIntptr.Events.DV.dvalue.
    pose proof dvalue_convert_strict_safe dv as [dvi [CONV RCONV]].
    apply dvi.
  Defined.

  (* TODO: Should we move this? *)
  Definition fin_to_inf_uvalue (uv : LLVMParams64BitIntptr.Events.DV.uvalue) : LLVMParamsBigIntptr.Events.DV.uvalue.
    pose proof uvalue_convert_strict_safe uv as [uvi [CONV RCONV]].
    apply uvi.
  Defined.

  (* Could not put with the other conversions, need to know what memory structures like MemState are *)
  Definition convert_SByte (sb1 : MemoryBigIntptr.MP.BYTE_IMPL.SByte) : OOM (Memory64BitIntptr.MP.BYTE_IMPL.SByte).
    destruct sb1.
    refine (uv' <- DVC1.uvalue_convert_strict uv;;
            idx' <- DVC1.uvalue_convert_strict idx;;
            ret (FiniteSizeof.mkUByte LLVMParams64BitIntptr.Events.DV.uvalue uv' dt idx' sid)).
  Defined.

  Definition lift_SByte (sb1 : Memory64BitIntptr.MP.BYTE_IMPL.SByte) : MemoryBigIntptr.MP.BYTE_IMPL.SByte.
    destruct sb1.
    remember (DVC2.uvalue_convert_strict uv).
    exact (FiniteSizeof.mkUByte DVC2.DV2.uvalue (fin_to_inf_uvalue uv) dt (fin_to_inf_uvalue idx) sid).
  Defined.

  Definition convert_mem_byte (mb1 : InfMemMMSP.mem_byte) : OOM (FinMemMMSP.mem_byte).
    destruct mb1.
    refine (s' <- convert_SByte s;;
            ret _).

    constructor.
    apply s'.
    apply a.
  Defined.

  Definition lift_mem_byte (mb1 : FinMemMMSP.mem_byte) : InfMemMMSP.mem_byte.
    destruct mb1.
    constructor.
    - exact (lift_SByte s).
    - apply a.
  Defined.

  (* Slightly tricky.

     Both the infinite and finite memory have the same underlying
     structure --- a map from Z to mem_bytes.

     The Z indexes in the finite memory may need to be limited to the
     range of the address type, but it may not matter because trying
     to look these up in a program should cause OOM anyway.
   *)
  Definition convert_memory (mem : InfMemMMSP.memory) : OOM (FinMemMMSP.memory).
    refine (elems <- map_monad _ (IntMaps.IM.elements mem);;
            ret (IntMaps.IP.of_list elems)).

    refine (fun '(ix, mb) =>
              mb' <- convert_mem_byte mb;;
              ret (ix, mb')).
  Defined.

  Definition lift_memory (mem : FinMemMMSP.memory) : InfMemMMSP.memory.
    refine (let elems := map _ (IntMaps.IM.elements mem) in
            IntMaps.IP.of_list elems).

    refine (fun '(ix, mb) =>
              let mb' := lift_mem_byte mb in
              (ix, mb')).
  Defined.

  Definition convert_Frame (f : InfMemMMSP.Frame) : OOM (FinMemMMSP.Frame).
    induction f.
    - exact (ret []).
    - refine (a' <- InfToFinAddrConvert.addr_convert a;;
              f' <- IHf;;
              ret (a' :: f')).
  Defined.

  Definition lift_Frame (f : FinMemMMSP.Frame) : InfMemMMSP.Frame.
    induction f.
    - exact [].
    - exact (fin_to_inf_addr a :: IHf).
  Defined.

  Definition convert_FrameStack (fs : InfMemMMSP.FrameStack) : OOM (FinMemMMSP.FrameStack).
    induction fs.
    - refine (f' <- convert_Frame f;;
              ret (FinMemMMSP.Singleton f')).
    - refine (f' <- convert_Frame f;;
              fs' <- IHfs;;
              ret (FinMemMMSP.Snoc fs' f')).
  Defined.

  Definition lift_FrameStack (fs : FinMemMMSP.FrameStack) : InfMemMMSP.FrameStack.
    induction fs.
    - refine (let f' := lift_Frame f in
              InfMemMMSP.Singleton f').
    - refine (let f' := lift_Frame f in
              InfMemMMSP.Snoc IHfs f').
  Defined.

  Definition convert_Block (b : InfMemMMSP.Block) : OOM (FinMemMMSP.Block)
    := map_monad InfToFinAddrConvert.addr_convert b.

  Definition lift_Block (b : FinMemMMSP.Block) : InfMemMMSP.Block
    := map fin_to_inf_addr b.

  Definition convert_Heap (h : InfMemMMSP.Heap) : OOM (FinMemMMSP.Heap).
    refine (blocks <- map_monad _ (IntMaps.IM.elements h);;
            ret (IntMaps.IP.of_list blocks)).

    refine (fun '(ix, b) =>
              b' <- convert_Block b;;
              ret (ix, b')).
  Defined.

  Definition lift_Heap (h : FinMemMMSP.Heap) : InfMemMMSP.Heap.
    refine (let blocks := map _ (IntMaps.IM.elements h) in
            IntMaps.IP.of_list blocks).

    refine (fun '(ix, b) =>
              let b' := lift_Block b in
              (ix, b')).
  Defined.

  Definition convert_memory_stack (ms1 : InfMemMMSP.memory_stack) : OOM (FinMemMMSP.memory_stack).
    destruct ms1 as [mem fs h].
    refine (mem' <- convert_memory mem;;
            fs' <- convert_FrameStack fs;;
            h' <- convert_Heap h;;
            ret _).

    constructor; auto.
  Defined.

  Definition lift_memory_stack (ms1 : FinMemMMSP.memory_stack) : InfMemMMSP.memory_stack.
    destruct ms1 as [mem fs h].
    refine (let mem' := lift_memory mem in
            let fs' := lift_FrameStack fs in
            let h' := lift_Heap h in
            _).

    constructor; auto.
  Defined.

  Definition convert_MemState (m1 : InfMem.MMEP.MMSP.MemState) : OOM (FinMem.MMEP.MMSP.MemState).
    destruct m1 as [ms pr].
    refine (ms' <- convert_memory_stack ms;;
            ret _).

    constructor; auto.
  Defined.

  Definition lift_MemState (m1 : FinMem.MMEP.MMSP.MemState) : InfMem.MMEP.MMSP.MemState.
    destruct m1 as [ms pr].
    refine (let ms' := lift_memory_stack ms in
            _).

    constructor; auto.
  Defined.

  Definition MemState_refine (m1 : InfMem.MMEP.MMSP.MemState) (m2 : FinMem.MMEP.MMSP.MemState) : Prop
    := convert_MemState m1 = NoOom m2.

  Lemma MemState_refine_initial :
    MemState_refine InfMemMMSP.initial_memory_state FinMemMMSP.initial_memory_state.
  Proof.
    reflexivity.
  Qed.

  (** More refinement relations *)
  Definition L3_E1E2_orutt_strict (t1 : PropT InfLP.Events.L3 (InfMemMMSP.MemState *
                                                                 (MemPropT.store_id * (InfLLVM.Local.local_env * InfLLVM.Stack.lstack * (InfLLVM.Global.global_env * InfLP.Events.DV.dvalue))))) t2
    : Prop :=
    forall t', t2 t' ->
          exists t, t1 t /\
                 orutt
                   L3_refine_strict
                   L3_res_refine_strict
                   (MemState_refine × (eq × (local_refine_strict × stack_refine_strict × (global_refine_strict × DVC1.dvalue_refine_strict))))
                   t t' (OOM:=OOME).

  Definition model_E1E2_L3_orutt_strict p1 p2 :=
    L3_E1E2_orutt_strict
      (TopLevelBigIntptr.model_oom_L3 p1)
      (TopLevel64BitIntptr.model_oom_L3 p2).

  Definition lift_local_env (lenv : InterpreterStack64BitIntptr.LLVM.Local.local_env) : InterpreterStackBigIntptr.LLVM.Local.local_env.
    refine (map _ lenv).

    refine (fun '(ix, uv) =>
              let uv' := fin_to_inf_uvalue uv in
              (ix, uv')).
  Defined.

  Definition lift_global_env (genv : InterpreterStack64BitIntptr.LLVM.Global.global_env) : InterpreterStackBigIntptr.LLVM.Global.global_env.
    refine (map _ genv).

    refine (fun '(ix, dv) =>
              let dv' := fin_to_inf_dvalue dv in
              (ix, dv')).
  Defined.

  Definition lift_stack (stack : InterpreterStack64BitIntptr.LLVM.Stack.lstack) : InterpreterStackBigIntptr.LLVM.Stack.lstack.
    induction stack.
    - exact [].
    - exact (lift_local_env a :: IHstack).
  Defined.

  Definition get_inf_tree :
    forall (t_fin2 : itree L3 (FinMem.MMEP.MMSP.MemState * (MemPropT.store_id * (local_env * @stack local_env * res_L1)))), itree InfLP.Events.L3 TopLevelBigIntptr.res_L6.
  Proof.
    cofix CIH.
    intros t_fin2.
    inversion t_fin2.
    inversion _observe.
    - (* Ret *)
      refine (ret _).
      destruct r as [ms [sid [[lenv s] [genv res]]]].
      constructor.
      exact (lift_MemState ms).

      constructor.
      exact sid.

      constructor.
      constructor.
      exact (lift_local_env lenv).
      exact (lift_stack s).

      constructor.
      exact (lift_global_env genv).
      exact (fin_to_inf_dvalue res).
    - (*Tau *)
      apply go.
      apply TauF.
      apply CIH.
      apply t.
    - (* Vis *)
      inversion e; clear e; subst.
      { (* ExternalCallE *)
        inversion H; subst.
        apply go.
        apply (VisF (subevent _ (E1.ExternalCall t (fin_to_inf_uvalue f) (map fin_to_inf_dvalue args)))).

        (* Continuation *)
        intros x.
        apply CIH.

        pose proof (DVCInfFin.dvalue_convert_strict x).
        destruct H0.
        - exact (k d).
        - (* OOM -- somewhat worried about this case *)
          exact (raiseOOM s).
      }

      inversion X0; clear X0; subst.
      { (* PickUvalue *)
        inversion X1; subst.
        apply go.
        apply (VisF (subevent _ (E1.pick Pre (fin_to_inf_uvalue x)))).

        (* Continuation *)
        intros res.
        destruct res.
        apply CIH.

        pose proof (DVCInfFin.dvalue_convert_strict x0).
        destruct H.
        - apply k.
          constructor.
          apply d.
          apply t.
        - (* OOM -- somewhat worried about this case *)
          exact (raiseOOM s).
      }

      inversion H; clear H; subst.
      { (* OOM *)
        inversion H0; subst.
        exact (raiseOOM H).
      }

      inversion H0; clear H0; subst.
      { (* UBE *)
        inversion H; subst.
        exact (raiseUB H0).
      }

      inversion H; clear H; subst.
      { (* DebugE *)
        inversion H0; subst.
        apply go.
        apply (VisF (subevent _ (Debug H))).
        intros H1.
        apply CIH.
        apply k; auto.
      }

      { (* FailureE *)
        inversion H0; subst.
        exact (LLVMEvents.raise H).
      }
  Defined.

  Lemma fin_to_inf_dvalue_refine_strict :
    forall d,
      DVC1.dvalue_refine_strict (fin_to_inf_dvalue d) d.
  Proof.
    intros d.
    rewrite DVC1.dvalue_refine_strict_equation.
    unfold fin_to_inf_dvalue.
    break_match; cbn in *.
    destruct p.
    auto.
  Qed.

  Lemma fin_to_inf_uvalue_refine_strict :
    forall u,
      DVC1.uvalue_refine_strict (fin_to_inf_uvalue u) u.
  Proof.
    intros u.
    rewrite DVC1.uvalue_refine_strict_equation.
    unfold fin_to_inf_uvalue.
    break_match; cbn in *.
    destruct p.
    auto.
  Qed.

  Import AListFacts.

  Lemma lift_local_env_refine_strict :
    forall l,
      local_refine_strict (lift_local_env l) l.
  Proof.
    induction l.
    - cbn.
      apply alist_refine_empty.
    - destruct a.
      apply alist_refine_cons; cbn; auto.
      apply fin_to_inf_uvalue_refine_strict.
  Qed.

  Lemma lift_stack_refine_strict :
    forall s,
      stack_refine_strict (lift_stack s) s.
  Proof.
    induction s.
    - cbn.
      apply stack_refine_strict_empty.
    - apply stack_refine_strict_add; auto.
      apply lift_local_env_refine_strict.
  Qed.

  Lemma lift_global_env_refine_strict :
    forall g,
      global_refine_strict (lift_global_env g) g.
  Proof.
    induction g.
    - cbn.
      apply alist_refine_empty.
    - destruct a.
      apply alist_refine_cons; cbn; auto.
      apply fin_to_inf_dvalue_refine_strict.
  Qed.

  Lemma convert_FrameStack_lift :
    forall fs,
      convert_FrameStack (lift_FrameStack fs) = NoOom fs.
  Proof.
  Admitted.

  Lemma convert_memory_lift :
    forall m,
      convert_memory (lift_memory m) = NoOom m.
  Proof.
  Admitted.

  Lemma convert_Heap_lift :
    forall h,
      convert_Heap (lift_Heap h) = NoOom h.
  Proof.
  Admitted.

  Lemma convert_memory_stack_lift :
    forall ms,
      convert_memory_stack (lift_memory_stack ms) = NoOom ms.
  Proof.
    induction ms.
    cbn.
    setoid_rewrite convert_memory_lift.
    setoid_rewrite convert_FrameStack_lift.
    setoid_rewrite convert_Heap_lift.
    reflexivity.
  Qed.

  Lemma lift_MemState_refine :
    forall ms,
      MemState_refine (lift_MemState ms) ms.
  Proof.
    intros ms.
    red.
    destruct ms.
    cbn.
    rewrite convert_memory_stack_lift.
    auto.
  Qed.

  Lemma get_inf_tree_rutt :
    forall t,
      orutt (OOM:=OOME) L3_refine_strict L3_res_refine_strict
        (MemState_refine
           × (eq
                × (local_refine_strict × stack_refine_strict
                     × (global_refine_strict × DVC1.dvalue_refine_strict)))) (get_inf_tree t) t.
  Proof.
    intros t.
    rewrite (itree_eta_ t).
    genobs t ot.
    clear t Heqot.
    revert ot.
    pcofix CIH.
    intros ot.

    induction ot.
    - (* Ret *)
      pstep; red; cbn.
      constructor.
      destruct r0.
      repeat destruct p.
      destruct p0.
      repeat constructor; cbn.
      + apply lift_MemState_refine.
      + apply lift_local_env_refine_strict.
      + apply lift_stack_refine_strict.
      + apply lift_global_env_refine_strict.
      + apply fin_to_inf_dvalue_refine_strict.
    - (* Tau *)
      pstep; red; cbn.
      constructor.
      right.
      rewrite (itree_eta_ t).
      apply CIH.
    - (* Vis nodes *)
      destruct e.
      { (* ExternalCallE *)
        destruct e.
        pstep; red; cbn.

        constructor.
        { red. cbn.
          split; auto.
          split.
          apply fin_to_inf_uvalue_refine_strict.
          apply Util.Forall2_forall.
          split.
          apply map_length.

          intros i a b H H0.
          apply Nth_map_iff in H.
          destruct H. destruct H.
          subst.

          cbn in *.
          rewrite H1 in H0.
          inv H0.
          apply fin_to_inf_dvalue_refine_strict.
        }

        { intros a b [TT [F [ARGS AB]]].
          rewrite DVCInfFin.dvalue_refine_strict_equation in AB.
          rewrite AB.
          rewrite (itree_eta_ (k b)).
          right.
          apply CIH.
        }

        { intros o CONTRA; inv CONTRA.
        }
      }

      destruct s.
      { (* PickUvalue *)
        destruct p.
        pstep; red; cbn.

        constructor.
        { red. cbn.
          split; [tauto|].
          apply fin_to_inf_uvalue_refine_strict.
        }

        { intros [a []] [b []] [_ [X AB]].
          rewrite DVCInfFin.dvalue_refine_strict_equation in AB.
          rewrite AB.
          rewrite (itree_eta_ (k _)).
          right.
          apply CIH.
        }

        { intros o CONTRA; inv CONTRA.
        }
      }

      destruct s.
      { (* OOM *)
        destruct o.
        pstep; red; cbn.

        change (inr1 (inr1 (inl1 (ThrowOOM s)))) with (@subevent _ _ (ReSum_inr IFun sum1 OOME
                                                                                 (PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                                                                                 ExternalCallE) _ (ThrowOOM s)).

        apply EqVisOOM.
      }

      destruct s.
      { (* UBE *)
        destruct u.
        pstep; red; cbn.

        constructor.
        { cbn; auto.
        }

        { intros [] [] _.
        }

        { intros o CONTRA; inv CONTRA.
        }
      }

      destruct s.
      { (* DebugE *)
        destruct d.
        pstep; red; cbn.

        constructor.
        { cbn; auto.
        }

        { intros [] [] _.
          rewrite (itree_eta_ (k _)).
          right.
          apply CIH.
        }

        { intros o CONTRA; inv CONTRA.
        }
      }

      { (* FailureE *)
        destruct f.
        pstep; red; cbn.

        constructor.
        { cbn; auto.
        }

        { intros [] [] _.
        }

        { intros o CONTRA; inv CONTRA.
        }
      }
  Qed.

  Import InterpMemoryProp.

  #[global] Instance get_inf_tree_Proper :
    Proper (eutt eq ==> eutt eq) get_inf_tree.
  Proof.
    unfold Proper, respectful.
    intros x y EQ.
    rewrite (itree_eta_ x) in *.
    rewrite (itree_eta_ y) in *.
    genobs x ox.
    genobs y oy.
    clear x Heqox y Heqoy.
    revert ox oy EQ.
    pcofix CIH.
    intros ox oy EQ.
    punfold EQ. red in EQ. cbn in EQ.
    dependent induction EQ.
    - (* Ret Ret *)
      subst.
      pstep; red; cbn.
      constructor; auto.
    - (* Tau Tau *)
      pstep; red; cbn.
      constructor.
      right.
      rewrite (itree_eta_ m1).
      rewrite (itree_eta_ m2).
      eapply CIH.
      pclearbot.
      repeat rewrite <- itree_eta_.
      apply REL.
    - (* Vis Vis *)
      destruct e.

      { (* ExternalCallE *)
        destruct e.
        pstep; red; cbn.
        constructor.
        intros v.
        red.
        right.
        rewrite (itree_eta_
                   match DVCInfFin.dvalue_convert_strict v with
                   | NoOom a => k1 a
                   | Oom s => raiseOOM s
                   end).
        rewrite (itree_eta_
                   match DVCInfFin.dvalue_convert_strict v with
                   | NoOom a => k2 a
                   | Oom s => raiseOOM s
                   end).
        apply CIH.
        repeat rewrite <- itree_eta_.
        break_match; [|reflexivity].
        specialize (REL d).
        red in REL.
        pclearbot.
        eauto.
      }

      destruct s.
      { (* PickUvalueE *)
        destruct p.
        pstep; red; cbn.
        constructor.
        intros [v []].
        red.
        right.
        match goal with
        | H: _ |- r (get_inf_tree ?t1) (get_inf_tree ?t2) =>
            rewrite (itree_eta_ t1);
            rewrite (itree_eta_ t2)
        end.
        apply CIH.
        repeat rewrite <- itree_eta_.
        break_match; [|reflexivity].
        specialize (REL (exist _ d I)).
        red in REL.
        pclearbot.
        eauto.
      }

      destruct s.
      { (* OOME *)
        destruct o.
        pstep; red; cbn.
        constructor.
        intros [] _.
      }

      destruct s.
      { (* UBE *)
        destruct u0.
        pstep; red; cbn.
        constructor.
        intros [] _.
      }

      destruct s.
      { (* DebugE *)
        destruct d.
        pstep; red; cbn.
        constructor.
        intros [].
        red.
        right.
        match goal with
        | H: _ |- r (get_inf_tree ?t1) (get_inf_tree ?t2) =>
            rewrite (itree_eta_ t1);
            rewrite (itree_eta_ t2)
        end.
        apply CIH.
        repeat rewrite <- itree_eta_.
        specialize (REL tt).
        red in REL.
        pclearbot.
        eauto.
      }

      { (* FailureE *)
        destruct f.
        pstep; red; cbn.
        constructor.
        intros [] _.
      }
    - (* TauL *)
      pstep; red; cbn.
      constructor; auto.
      punfold IHEQ.
    - (* TauR *)
      pstep; red; cbn.
      constructor; auto.
      punfold IHEQ.
  Qed.

  (* TODO: not 100% sure what R, T1T2, pre, post should be / what constraints are needed for them *)
  Lemma oom_orutt :
    forall {E F T1 T2}
      `{OE : OOME -< E}
      `{OF : OOME -< F}
      (R : relation T1)
      (T1T2 : T1 -> T2 -> Prop)
      (pre : prerel E F)
      (post : postrel E F)
      (t_source t_oom : itree E T1) (t_final : itree F T2),
      refine_OOM_h R t_source t_oom ->
      orutt (OOM:=OOME) pre post T1T2 t_oom t_final ->
      orutt (OOM:=OOME) pre post T1T2 t_source t_final.
  Proof.
    intros E F T1 T2 OE OF R T1T2 pre post t_source t_oom t_final REF_OOM ORUTT.
  Admitted.    

  Lemma model_E1E2_23_orutt_strict :
    forall t_inf t_fin sid ms1 ms2,
      L2_E1E2_orutt_strict t_inf t_fin ->
      MemState_refine ms1 ms2 ->
      L3_E1E2_orutt_strict (InfMemInterp.interp_memory_prop TLR_INF.R.refine_res2 t_inf sid ms1) (FinMemInterp.interp_memory_prop TLR_FIN.R.refine_res2 t_fin sid ms2).
  Proof.
    intros t_inf t_fin sid ms1 ms2 REL MSR.
    red.
    red in REL.
    (* red in REL. *)

    unfold L3_E1E2_orutt_strict.
    intros t_fin2 FIN_HANDLED.

    exists (get_inf_tree t_fin2).
    split.
    { red.
      revert FIN_HANDLED.
      revert REL.

      rewrite (itree_eta_ t_fin).
      rewrite (itree_eta_ t_fin2).
      rewrite (itree_eta_ t_inf).

      genobs t_fin ot_fin.
      genobs t_fin2 ot_fin2.
      genobs t_inf ot_inf.
      clear t_inf Heqot_inf.
      clear t_fin Heqot_fin.
      clear t_fin2 Heqot_fin2.

      revert ot_inf ot_fin ot_fin2.
      pcofix CIH.
      intros ot_inf ot_fin ot_fin2 REL RUN.

      punfold REL.
      red in REL.
      cbn in REL.

      remember (upaco2
                  (orutt_ L2_refine_strict L2_res_refine_strict
                     (local_refine_strict × stack_refine_strict
                        × (global_refine_strict × DVCInfFin.dvalue_refine_strict))) bot2) as r'.
      revert Heqr'.

      dependent induction REL; intros Heqr'.
      - subst.
        apply interp_memory_prop_ret_inv in RUN.
        destruct RUN as [r3 [REQ EQ]]; subst.

        (assert (eutt eq (get_inf_tree {| _observe := ot_fin2 |}) (get_inf_tree (ret r3)))).
        { rewrite <- EQ.
          reflexivity.
        }

        eapply paco2_mon_bot; eauto.
        rewrite H0.

        destruct r3. repeat (destruct p; subst).
        destruct p0.

        destruct r1 as [[lenv lstack] [stack res]].
        destruct H as [[LR SR] [GR DR]]. cbn in *.

        pstep; red; cbn.
        constructor.

        red.
        constructor; cbn; red; auto.
        constructor; cbn.
        red. auto.

        destruct REQ as [_ [_ REQ]].
        destruct r2 as [l' [s' r2]].
        cbn in *. subst.
        pose proof (fin_to_inf_dvalue_refine_strict d).

        (* TODO: a little unsure of this one, but it seems plausible. *)
        Set Nested Proofs Allowed.
        Lemma fin_to_inf_dvalue_refine_strict' :
          forall d_inf d_fin,
            DVC1.dvalue_refine_strict d_inf d_fin ->
            d_inf = fin_to_inf_dvalue d_fin.
        Proof.
          intros d_inf d_fin H.
          rewrite DVC1.dvalue_refine_strict_equation in H.
          unfold fin_to_inf_dvalue.
          break_match; cbn in *.
          destruct p.
          clear Heqs.

          induction d_inf;
            try solve
              [ rewrite DVC1.dvalue_convert_strict_equation in H;
                cbn in *; inv H;
                rewrite DVC2.dvalue_convert_strict_equation in e;
                cbn in *; inv e;
                auto
              ].
          - rewrite DVC1.dvalue_convert_strict_equation in H.
            cbn in *.
            break_match_hyp; inv H.
            rewrite DVC2.dvalue_convert_strict_equation in e.
            cbn in *.
            break_match_hyp; inv e.
            rewrite DVC1.dvalue_convert_strict_equation in e0.
            cbn in *.
            break_match_hyp; inv e0.

            pose proof InfToFinAddrConvert.addr_convert_injective a a1 a0 Heqo Heqo1.
            subst.
            auto.
          - rewrite DVC1.dvalue_convert_strict_equation in H.
            cbn in *; break_match_hyp; inv H.
            rewrite DVC2.dvalue_convert_strict_equation in e.
            cbn in *; inv e.
            rewrite DVC1.dvalue_convert_strict_equation in e0.
            cbn in *; break_match_hyp; inv e0.
            admit. (* Some painful IP / BigIP reasoning *)
          - rewrite DVC1.dvalue_convert_strict_equation in H.
            cbn in *; break_match_hyp; inv H.
            rewrite DVC2.dvalue_convert_strict_equation in e.
            cbn in *; break_match_hyp; inv e.
            rewrite DVC1.dvalue_convert_strict_equation in e0.
            cbn in *; break_match_hyp; inv e0.

            induction fields.
            + cbn in *. inv Heqo.
              cbn in *. inv Heqo0.
              reflexivity.
            + rewrite map_monad_InT_unfold in Heqo.
              cbn in *.
              break_match_hyp; inv Heqo.
              break_match_hyp; inv H1.

              rewrite map_monad_InT_unfold in Heqo0.
              cbn in *.
              break_match_hyp; inv Heqo0.
              break_match_hyp; inv H1.

              rewrite map_monad_InT_unfold in Heqo1.
              cbn in *.
              break_match_hyp; inv Heqo1.
              break_match_hyp; inv H1.
              admit.
          - admit.
          - admit.
          - admit.
        Admitted.

        apply fin_to_inf_dvalue_refine_strict'; auto.
    - punfold RUN.
      red in RUN.
      cbn in RUN.

      assert (DEC: (exists m3, ot_fin2 = TauF m3) \/ (forall m3, ot_fin2 <> TauF m3)).
      { destruct ot_fin2; eauto; right; red; intros; inversion H0. }

      destruct DEC as [EQ | EQ].
      { destruct EQ as [m3 EQ].
        subst.
        pstep; red; cbn.
        constructor.
        right.
        rewrite (itree_eta_ m1).
        rewrite (itree_eta_ m3).
        eapply CIH.

        pclearbot.
        punfold H; red in H.
        pstep. red. cbn.
        eauto.

        red.
        rewrite <- itree_eta_.
        rewrite <- itree_eta_.

        rewrite <- tau_eutt.
        rewrite <- (tau_eutt m3).
        pstep; red; cbn.
        auto.
      }

      inversion RUN; subst.
      + specialize (EQ t2).
        contradiction.
      + pstep; red; cbn.
        constructor; auto.

        rewrite (itree_eta_ m2) in H.
        rewrite (itree_eta_ m2) in RUN.
        genobs m2 om2.
        setoid_rewrite <- Heqom2 in HS.
        clear Heqom2.
        clear m2.
        induction HS; subst.
        -- inversion RUN; subst.
           cbn in *.
           inversion HS; subst.

           pclearbot.
           punfold H.
           red in H.

           { dependent induction H.
             - rewrite <- x.
               constructor.
               destruct H as [[LR SR] [GR DR]]. cbn in *; subst; auto.
               destruct r2 as [l' [s' r2]].
               destruct r2.
               destruct p.
               destruct p0.
               cbn.
               cbn in *.
               destruct r0.
               destruct p, p0.
               constructor; auto.
               constructor; auto.
               constructor; auto.
               cbn. red. auto.
               cbn in *.
               destruct r1, p, p0. cbn in *.
               destruct REL as [_ [_ REL]].
               cbn in REL. subst.
               apply fin_to_inf_dvalue_refine_strict'. auto.
             - rewrite <- x.
               constructor; eauto.
           }

           { rewrite itree_eta in HT1.
             rewrite H1 in HT1.
             pinversion HT1.
           }

           { rewrite itree_eta in HT1.
             rewrite H1 in HT1.
             pinversion HT1.
             inversion REL0.
           }
        -- specialize (EQ t2).
           contradiction.
        -- eapply IHHS; eauto.
           left.
           pclearbot.
           assert (orutt (OOM:=OOME) (@L2_refine_strict) (@L2_res_refine_strict) (local_refine_strict × stack_refine_strict
                                                                        × (global_refine_strict × DVCInfFin.dvalue_refine_strict)) m1 (Tau t1)).
           { apply H.
           }
           setoid_rewrite tau_eutt in H0.
           rewrite <- itree_eta_.
           apply H0.
        -- specialize (EQ t2).
           contradiction.
        -- { dependent induction RUN; subst.
             - specialize (EQ t2).
               contradiction.
             - (* TauL *)
               clear IHRUN.
               pclearbot.
               rewrite itree_eta in HT1.
               epose proof orutt_Proper_R2.
               unfold Proper, respectful in H0.
               pose proof H.
               eapply H0 in H1.
               6: {
                 symmetry.
                 apply HT1.
               }
               all: try reflexivity.
               clear H. rename H1 into H.
               apply orutt_inv_Vis_r in H.
               destruct H.
               2: {
                 (* OOM *)
                 eapply Interp_Memory_PropT_Vis_OOM.
                 destruct H.
                 subst.
                 cbn in H0.
                 red in H0.
                 admit.
               }

               destruct H as [U1 [e1 [k3 [M1 [EV_REL K_RUTT]]]]].
               punfold M1.
               red in M1.
               genobs m1 om1.
               clear m1 Heqom1.
               dependent induction M1.
               + (* rename H1 into VIS_HANDLED. *)
                 destruct e1.
                 cbn in EV_REL; destruct e0; inv EV_REL.
                 destruct s. cbn in EV_REL; destruct i; try contradiction.
                 destruct s. cbn in EV_REL; destruct m; try contradiction.
                 destruct s. cbn in EV_REL; destruct p; try contradiction.
                 destruct s.
                 2: {
                   destruct s. cbn in EV_REL; destruct u; try contradiction.
                   destruct s; cbn in EV_REL; try contradiction.
                 }

                 cbn in *.
                 change (VisF (inr1 (inr1 (inr1 (inr1 (inl1 o))))) k0) with (observe (vis (inr1 (inr1 (inr1 (inr1 (inl1 o))))) k0)).
                 eapply Interp_Memory_PropT_Vis_OOM with (k1 := k0) (e:=o).
                 reflexivity.
               + destruct e, e1;
                   cbn in EV_REL.
                 destruct e; try contradiction.
                 destruct s0; try contradiction.
                 destruct i; try contradiction.
                 repeat (destruct s0; try contradiction).

                 constructor; eauto.
             - (* TauR *)
               specialize (EQ t2).
               contradiction.
             - (* Vis_OOM *)
               pclearbot.
               rewrite itree_eta in HT0.
               punfold H.
               red in H.
               cbn in H.
               inversion H;
                 try solve [rewrite <- H1 in HT0; pinversion HT0; try inv CHECK0].
               + rewrite <- H1 in HT0.
                 pinversion HT0; subst_existT.
                 subst_existT.
                 specialize (H4 e0).
                 contradiction.
               + rewrite <- H2 in HT0.
                 pinversion HT0.
                 subst_existT.
                 subst_existT.
                 Unset Printing Notations.
                 Goal (Prop) -> False.
                   intros H.
                   induction H.
                 
                 admit.
               + 
                 cbn in *.
                 
                 subst.
               
               cbn.
               constructor; eauto.
               eapply IHRUN.

                 cbn in *.
                   { (* Nondeterminism events *)
                     red in H0.
                     destruct H0.
                     - (* True *)
                       subst.
                       setoid_rewrite bind_ret_l in VIS_HANDLED.

                       specialize (HK true).
                       forward HK. constructor; reflexivity.
                       pclearbot.
                       rewrite <- VIS_HANDLED in HK.

                       eapply Interp_PropT_Vis with (k2 := fun _ => get_nat_tree' {| _observe := observe t2 |}).
                       2: {
                         red.
                         left; auto.
                       }
                       2: {
                         setoid_rewrite bind_ret_l.
                         reflexivity.
                       }

                       intros a RET.
                       eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                       right.
                       rewrite (itree_eta_ (k0 _)).

                       eapply CIH.
                       + specialize (K_RUTT true true).
                         forward K_RUTT; cbn; auto.
                         pclearbot.
                         repeat rewrite <- itree_eta_.
                         assert (k0 true ≈ k3 true) as K0K3 by apply REL.
                         rewrite K0K3.
                         punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.
                         pstep; red; cbn; eauto.
                       + repeat rewrite <- itree_eta_.
                         eapply HK.
                     - (* False *)
                       subst.
                       setoid_rewrite bind_ret_l in VIS_HANDLED.

                       specialize (HK false).
                       forward HK. constructor; reflexivity.
                       pclearbot.
                       rewrite <- VIS_HANDLED in HK.

                       eapply Interp_PropT_Vis with (k2 := fun _ => get_nat_tree' {| _observe := observe t2 |}).
                       2: {
                         red.
                         right; auto.
                       }
                       2: {
                         setoid_rewrite bind_ret_l.
                         reflexivity.
                       }

                       intros a RET.
                       eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                       right.
                       rewrite (itree_eta_ (k0 _)).

                       eapply CIH.
                       + specialize (K_RUTT false false).
                         forward K_RUTT; cbn; auto.
                         pclearbot.
                         repeat rewrite <- itree_eta_.
                         assert (k0 false ≈ k3 false) as K0K3 by apply REL.
                         rewrite K0K3.

                         punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.
                         pstep; red; cbn; eauto.
                       + repeat rewrite <- itree_eta_.
                         eapply HK.
                   }

                   { (* Regular events *)
                     destruct b.
                     red in H0.
                     rewrite H0 in VIS_HANDLED.

                     setoid_rewrite bind_trigger in VIS_HANDLED.
                     punfold VIS_HANDLED. red in VIS_HANDLED.
                     cbn in VIS_HANDLED.
                     dependent induction VIS_HANDLED.
                     { rewrite <- x.

                       eapply Interp_PropT_Vis with (k2:=(fun n0 : nat =>
                                                            get_nat_tree' (k2 (if Nat.eqb n0 0 then false else if Nat.eqb n0 1 then true else false)))).
                       2: {
                         red.
                         reflexivity.
                       }
                       2: {
                         cbn.
                         setoid_rewrite bind_trigger.
                         pstep; red; cbn.

                         destruct EV_REL as [[R1 R3] | [R1 R3]]; subst; auto.
                         - constructor.
                           intros v.
                           red.
                           specialize (REL0 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false)).
                           red in REL0.
                           pclearbot.
                           assert (k5 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false) ≈ k2 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false)) as K0K2.
                           { eapply REL0.
                           }

                           setoid_rewrite H0 in HK.

                           destruct v; [| destruct v]; cbn in *.
                           + repeat (rewrite <- itree_eta_).
                             specialize (HK false).
                             forward HK.
                             { eapply ReturnsVis.
                               unfold ITree.trigger.
                               reflexivity.
                               constructor. reflexivity.
                             }
                             pclearbot.
                             left.
                             setoid_rewrite K0K2.
                             assert ((get_nat_tree' (k2 false)) ≈ (get_nat_tree' (k2 false))).
                             reflexivity.
                             eauto.
                           + repeat (rewrite <- itree_eta_).
                             specialize (HK true).
                             forward HK.
                             { eapply ReturnsVis.
                               unfold ITree.trigger.
                               reflexivity.
                               constructor. reflexivity.
                             }
                             pclearbot.
                             left.
                             setoid_rewrite K0K2.
                             assert ((get_nat_tree' (k2 true)) ≈ (get_nat_tree' (k2 true))).
                             reflexivity.
                             eauto.
                             + (* Bogus case *)
                               repeat (rewrite <- itree_eta_).
                               specialize (HK false).
                               forward HK.
                               { eapply ReturnsVis.
                                 unfold ITree.trigger.
                                 reflexivity.
                                 constructor. reflexivity.
                               }
                               pclearbot.
                               left.
                               setoid_rewrite K0K2.
                               assert ((get_nat_tree' (k2 false)) ≈ (get_nat_tree' (k2 false))).
                               reflexivity.
                               eauto.
                         - constructor.
                           intros v.
                           red.
                           specialize (REL0 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false)).
                           red in REL0.
                           pclearbot.
                           assert (k5 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false) ≈ k2 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false)) as K0K2.
                           { eapply REL0.
                           }

                           setoid_rewrite H0 in HK.

                           destruct v; [| destruct v]; cbn in *.
                           + repeat (rewrite <- itree_eta_).
                             specialize (HK false).
                             forward HK.
                             { eapply ReturnsVis.
                               unfold ITree.trigger.
                               reflexivity.
                               constructor. reflexivity.
                             }
                             pclearbot.
                             left.
                             setoid_rewrite K0K2.
                             assert ((get_nat_tree' (k2 false)) ≈ (get_nat_tree' (k2 false))).
                             reflexivity.
                             eauto.
                           + repeat (rewrite <- itree_eta_).
                             specialize (HK true).
                             forward HK.
                             { eapply ReturnsVis.
                               unfold ITree.trigger.
                               reflexivity.
                               constructor. reflexivity.
                             }
                             pclearbot.
                             left.
                             setoid_rewrite K0K2.
                             assert ((get_nat_tree' (k2 true)) ≈ (get_nat_tree' (k2 true))).
                             reflexivity.
                             eauto.
                             + (* Bogus case *)
                               repeat (rewrite <- itree_eta_).
                               specialize (HK false).
                               forward HK.
                               { eapply ReturnsVis.
                                 unfold ITree.trigger.
                                 reflexivity.
                                 constructor. reflexivity.
                               }
                               pclearbot.
                               left.
                               setoid_rewrite K0K2.
                               assert ((get_nat_tree' (k2 false)) ≈ (get_nat_tree' (k2 false))).
                               reflexivity.
                               eauto.
                       }

                       intros a RET.
                       specialize (K_RUTT a (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)).
                       forward K_RUTT.
                       cbn; auto.

                       specialize (HK (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)).
                       rewrite H0 in HK.
                       forward HK.
                       { eapply ReturnsVis.
                         unfold ITree.trigger.
                         reflexivity.
                         cbn.
                         constructor.
                         reflexivity.
                       }

                       right.
                       rewrite (itree_eta_ (k0 a)).
                       rewrite (itree_eta_ (k2 _)).
                       pclearbot.
                       eapply CIH;
                         repeat rewrite <- itree_eta_.

                       repeat rewrite <- itree_eta_.
                       assert (k0 a ≈ k3 a) as K0K3 by apply REL.
                       rewrite K0K3.
                       eapply K_RUTT.
                       red.
                       eapply HK.
                     }

                     { rewrite <- x in EQ.
                       specialize (EQ t1).
                       contradiction.
                     }
                   }
               + constructor; auto.
                 eapply IHM1; eauto.
             - rewrite <- x in EQ.
               exfalso.
               eapply EQ; eauto.
           }
      + pstep; red; cbn.
        constructor.
        right.
        rewrite (itree_eta_ m1).
        rewrite (itree_eta_ t2).

        pclearbot.
        eapply CIH; repeat rewrite <- itree_eta_.
        eauto.

        red.
        rewrite <- (tau_eutt m2).

        pstep; red; cbn.
        auto.
      - subst.
        apply interp_memory_prop_inv_tau_l in RUN.
        pclearbot.

        pstep; red; constructor; auto.
        pclearbot.

        punfold RUN. red in RUN.

        
        
        apply interp_memory_prop _tau_inv in RUN.
        destruct RUN as [r3 [REQ EQ]]; subst.

        inversion REQ; cbn in *.
        
        red.
        red.

        (* TODO: Move these *)
        Set Nested Proofs Allowed.
        Lemma local_env_refine_lift :
          forall lenv l,
            local_refine_strict lenv l ->
            lenv = lift_local_env l.
        Proof.
          induction lenv, l; intros LR; auto.
          - apply alist_refine_nil_cons_inv in LR.
            contradiction.
          - apply alist_refine_cons_nil_inv in LR.
            contradiction.
          - red in LR.
            red in LR.
            cbn in LR.
            unfold OptionUtil.option_rel2 in LR.
            cbn in *.
            destruct p, a.
            cbn.
        Qed.
        
        destruct H as [[R1 R3] | [R1 R3]]; subst; auto.
      - punfold RUN.
        red in RUN.
        cbn in RUN.

        assert (DEC: (exists m3, ot_bool2 = TauF m3) \/ (forall m3, ot_bool2 <> TauF m3)).
        { destruct ot_bool2; eauto; right; red; intros; inversion H0. }

        destruct DEC as [EQ | EQ].
        { destruct EQ as [m3 EQ].
          subst.
          pstep; red; cbn.
          constructor.
          right.
          rewrite (itree_eta_ m1).
          rewrite (itree_eta_ m3).
          eapply CIH.

          pclearbot.
          punfold H; red in H.
          pstep. red. cbn.
          eauto.

          red.
          rewrite <- itree_eta_.
          rewrite <- itree_eta_.

          rewrite <- tau_eutt.
          rewrite <- (tau_eutt m3).
          pstep; red; cbn.
          auto.
        }

        inversion RUN; subst.
        + specialize (EQ t2).
          contradiction.
        + pstep; red; cbn.
          constructor; auto.

          rewrite (itree_eta_ m2) in H.
          rewrite (itree_eta_ m2) in RUN.
          genobs m2 om2.
          setoid_rewrite <- Heqom2 in HS.
          clear Heqom2.
          clear m2.
          induction HS; subst.
          -- inversion RUN; subst.
             cbn in *.
             inversion HS; subst.

             pclearbot.
             punfold H.
             red in H.

             { dependent induction H.
               - rewrite <- x.
                 constructor.
                 destruct H as [[R1 R3] | [R1 R3]]; subst; auto.
               - rewrite <- x.
                 constructor; auto.
             }
          -- specialize (EQ t2).
             contradiction.
          -- eapply IHHS; eauto.
             left.
             pclearbot.
             assert (rutt (@top_level_rel) (@top_level_rel_ans) nb  m1 (Tau t1)).
             { apply H.
             }
             setoid_rewrite tau_eutt in H0.
             rewrite <- itree_eta_.
             apply H0.
          -- specialize (EQ t2).
             contradiction.
          -- { dependent induction RUN; subst.
               - rewrite <- x in EQ.
                 specialize (EQ t0).
                 contradiction.
               - (* TauL *)
                 clear IHRUN.
                 pclearbot.

                 apply rutt_inv_Vis_r in H.
                 destruct H as [U1 [e1 [k3 [M1 [EV_REL K_RUTT]]]]].
                 punfold M1.
                 red in M1.
                 genobs m1 om1.
                 clear m1 Heqom1.
                 dependent induction M1.
                 + rename H1 into VIS_HANDLED.
                   destruct e, e1; try destruct n; try destruct n0; cbn in EV_REL; try inversion EV_REL.

                   { (* Nondeterminism events *)
                     red in H0.
                     destruct H0.
                     - (* True *)
                       subst.
                       setoid_rewrite bind_ret_l in VIS_HANDLED.

                       specialize (HK true).
                       forward HK. constructor; reflexivity.
                       pclearbot.
                       rewrite <- VIS_HANDLED in HK.

                       eapply Interp_PropT_Vis with (k2 := fun _ => get_nat_tree' {| _observe := observe t2 |}).
                       2: {
                         red.
                         left; auto.
                       }
                       2: {
                         setoid_rewrite bind_ret_l.
                         reflexivity.
                       }

                       intros a RET.
                       eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                       right.
                       rewrite (itree_eta_ (k0 _)).

                       eapply CIH.
                       + specialize (K_RUTT true true).
                         forward K_RUTT; cbn; auto.
                         pclearbot.
                         repeat rewrite <- itree_eta_.
                         assert (k0 true ≈ k3 true) as K0K3 by apply REL.
                         rewrite K0K3.
                         punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.
                         pstep; red; cbn; eauto.
                       + repeat rewrite <- itree_eta_.
                         eapply HK.
                     - (* False *)
                       subst.
                       setoid_rewrite bind_ret_l in VIS_HANDLED.

                       specialize (HK false).
                       forward HK. constructor; reflexivity.
                       pclearbot.
                       rewrite <- VIS_HANDLED in HK.

                       eapply Interp_PropT_Vis with (k2 := fun _ => get_nat_tree' {| _observe := observe t2 |}).
                       2: {
                         red.
                         right; auto.
                       }
                       2: {
                         setoid_rewrite bind_ret_l.
                         reflexivity.
                       }

                       intros a RET.
                       eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                       right.
                       rewrite (itree_eta_ (k0 _)).

                       eapply CIH.
                       + specialize (K_RUTT false false).
                         forward K_RUTT; cbn; auto.
                         pclearbot.
                         repeat rewrite <- itree_eta_.
                         assert (k0 false ≈ k3 false) as K0K3 by apply REL.
                         rewrite K0K3.

                         punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.
                         pstep; red; cbn; eauto.
                       + repeat rewrite <- itree_eta_.
                         eapply HK.
                   }

                   { (* Regular events *)
                     destruct b.
                     red in H0.
                     rewrite H0 in VIS_HANDLED.

                     setoid_rewrite bind_trigger in VIS_HANDLED.
                     punfold VIS_HANDLED. red in VIS_HANDLED.
                     cbn in VIS_HANDLED.
                     dependent induction VIS_HANDLED.
                     { rewrite <- x.

                       eapply Interp_PropT_Vis with (k2:=(fun n0 : nat =>
                                                            get_nat_tree' (k2 (if Nat.eqb n0 0 then false else if Nat.eqb n0 1 then true else false)))).
                       2: {
                         red.
                         reflexivity.
                       }
                       2: {
                         cbn.
                         setoid_rewrite bind_trigger.
                         pstep; red; cbn.

                         destruct EV_REL as [[R1 R3] | [R1 R3]]; subst; auto.
                         - constructor.
                           intros v.
                           red.
                           specialize (REL0 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false)).
                           red in REL0.
                           pclearbot.
                           assert (k5 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false) ≈ k2 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false)) as K0K2.
                           { eapply REL0.
                           }

                           setoid_rewrite H0 in HK.

                           destruct v; [| destruct v]; cbn in *.
                           + repeat (rewrite <- itree_eta_).
                             specialize (HK false).
                             forward HK.
                             { eapply ReturnsVis.
                               unfold ITree.trigger.
                               reflexivity.
                               constructor. reflexivity.
                             }
                             pclearbot.
                             left.
                             setoid_rewrite K0K2.
                             assert ((get_nat_tree' (k2 false)) ≈ (get_nat_tree' (k2 false))).
                             reflexivity.
                             eauto.
                           + repeat (rewrite <- itree_eta_).
                             specialize (HK true).
                             forward HK.
                             { eapply ReturnsVis.
                               unfold ITree.trigger.
                               reflexivity.
                               constructor. reflexivity.
                             }
                             pclearbot.
                             left.
                             setoid_rewrite K0K2.
                             assert ((get_nat_tree' (k2 true)) ≈ (get_nat_tree' (k2 true))).
                             reflexivity.
                             eauto.
                           + (* Bogus case *)
                             repeat (rewrite <- itree_eta_).
                             specialize (HK false).
                             forward HK.
                             { eapply ReturnsVis.
                               unfold ITree.trigger.
                               reflexivity.
                               constructor. reflexivity.
                             }
                             pclearbot.
                             left.
                             setoid_rewrite K0K2.
                             assert ((get_nat_tree' (k2 false)) ≈ (get_nat_tree' (k2 false))).
                             reflexivity.
                             eauto.
                         - constructor.
                           intros v.
                           red.
                           specialize (REL0 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false)).
                           red in REL0.
                           pclearbot.
                           assert (k5 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false) ≈ k2 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false)) as K0K2.
                           { eapply REL0.
                           }

                           setoid_rewrite H0 in HK.

                           destruct v; [| destruct v]; cbn in *.
                           + repeat (rewrite <- itree_eta_).
                             specialize (HK false).
                             forward HK.
                             { eapply ReturnsVis.
                               unfold ITree.trigger.
                               reflexivity.
                               constructor. reflexivity.
                             }
                             pclearbot.
                             left.
                             setoid_rewrite K0K2.
                             assert ((get_nat_tree' (k2 false)) ≈ (get_nat_tree' (k2 false))).
                             reflexivity.
                             eauto.
                           + repeat (rewrite <- itree_eta_).
                             specialize (HK true).
                             forward HK.
                             { eapply ReturnsVis.
                               unfold ITree.trigger.
                               reflexivity.
                               constructor. reflexivity.
                             }
                             pclearbot.
                             left.
                             setoid_rewrite K0K2.
                             assert ((get_nat_tree' (k2 true)) ≈ (get_nat_tree' (k2 true))).
                             reflexivity.
                             eauto.
                           + (* Bogus case *)
                             repeat (rewrite <- itree_eta_).
                             specialize (HK false).
                             forward HK.
                             { eapply ReturnsVis.
                               unfold ITree.trigger.
                               reflexivity.
                               constructor. reflexivity.
                             }
                             pclearbot.
                             left.
                             setoid_rewrite K0K2.
                             assert ((get_nat_tree' (k2 false)) ≈ (get_nat_tree' (k2 false))).
                             reflexivity.
                             eauto.
                       }

                       intros a RET.
                       specialize (K_RUTT a (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)).
                       forward K_RUTT.
                       cbn; auto.

                       specialize (HK (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)).
                       rewrite H0 in HK.
                       forward HK.
                       { eapply ReturnsVis.
                         unfold ITree.trigger.
                         reflexivity.
                         cbn.
                         constructor.
                         reflexivity.
                       }

                       right.
                       rewrite (itree_eta_ (k0 a)).
                       rewrite (itree_eta_ (k2 _)).
                       pclearbot.
                       eapply CIH;
                         repeat rewrite <- itree_eta_.

                       repeat rewrite <- itree_eta_.
                       assert (k0 a ≈ k3 a) as K0K3 by apply REL.
                       rewrite K0K3.
                       eapply K_RUTT.
                       red.
                       eapply HK.
                     }

                     { rewrite <- x in EQ.
                       specialize (EQ t1).
                       contradiction.
                     }
                   }
                 + constructor; auto.
                   eapply IHM1; eauto.
               - rewrite <- x in EQ.
                 exfalso.
                 eapply EQ; eauto.
             }
        + pstep; red; cbn.
          constructor.
          right.
          rewrite (itree_eta_ m1).
          rewrite (itree_eta_ t2).

          pclearbot.
          eapply CIH; repeat rewrite <- itree_eta_.
          eauto.

          red.
          rewrite <- (tau_eutt m2).

          pstep; red; cbn.
          auto.
      - rename H into EV_REL.
        destruct e1, e2; try destruct n; try destruct n0; cbn in EV_REL; try inversion EV_REL.
        rename H0 into K_RUTT.
        subst.

        + (* NonDet events *)
          punfold RUN. red in RUN.
          cbn in RUN.
          dependent induction RUN.
          -- pstep; red; cbn.
             constructor; auto.
             rewrite (itree_eta_ t2).

             forward IHRUN; auto.
             specialize (IHRUN k2).
             forward IHRUN; auto.
             forward IHRUN; auto.
             punfold IHRUN.
          --
            red in H.
            { destruct H; subst; setoid_rewrite bind_ret_l in H0.
              - pstep; red; cbn.

                eapply Interp_PropT_Vis with (k2 := fun _ => get_nat_tree' {| _observe := observe t2 |}).
                2: {
                  left. reflexivity.
                }
                2: {
                  setoid_rewrite bind_ret_l.
                  reflexivity.
                }

                intros a RET.
                eapply Returns_Ret_ in RET; [| reflexivity]; subst.
                right.

                rewrite (itree_eta_ (k1 true)).
                eapply CIH; repeat rewrite <- itree_eta_.
                + specialize (K_RUTT true true).
                  forward K_RUTT; cbn; auto.
                  pclearbot.
                  apply K_RUTT.
                + rewrite H0.
                  specialize (HK true).
                  forward HK.
                  constructor; reflexivity.
                  pclearbot.
                  apply HK.
              - pstep; red; cbn.

                eapply Interp_PropT_Vis with (k2 := fun _ => get_nat_tree' {| _observe := observe t2 |}).
                2: {
                  right. reflexivity.
                }
                2: {
                  setoid_rewrite bind_ret_l.
                  reflexivity.
                }

                intros a RET.
                eapply Returns_Ret_ in RET; [| reflexivity]; subst.
                right.

                rewrite (itree_eta_ (k1 false)).
                eapply CIH; repeat rewrite <- itree_eta_.
                + specialize (K_RUTT false false).
                  forward K_RUTT; cbn; auto.
                  pclearbot.
                  apply K_RUTT.
                + rewrite H0.
                  specialize (HK false).
                  forward HK.
                  constructor; reflexivity.
                  pclearbot.
                  apply HK.
            }
        + { (* Regular events *)
            destruct b.
            rename EV_REL into NB.
            subst.
            punfold RUN. red in RUN. cbn in RUN.

            dependent induction RUN.
            - pstep; red; cbn.
              constructor; auto.

              forward IHRUN; auto.
              specialize (IHRUN _ k2 NB).
              forward IHRUN; auto.
              forward IHRUN; auto.
              punfold IHRUN.
            - red in H.
              rewrite H in H1.
              rename H0 into K_RUTT.

              setoid_rewrite bind_trigger in H1.
              punfold H1; red in H1; cbn in H1.
              dependent induction H1.
              { rewrite <- x.
                pstep; red; cbn.
                assert ((VisF (nat_ev (if b then 1 else 0))
                           (fun n0 : nat =>
                              get_nat_tree'
                                (if Nat.eqb n0 0
                                 then k0 false
                                 else if Nat.eqb n0 1 then k0 true else k0 false))) = observe (Vis (nat_ev (if b then 1 else 0))
                                                                                                 (fun n0 : nat =>
                                                                                                    get_nat_tree'
                                                                                                      (if Nat.eqb n0 0
                                                                                                       then k0 false
                                                                                                       else if Nat.eqb n0 1 then k0 true else k0 false)))) as VIS by auto.

                rewrite VIS.
                clear VIS.
                { eapply Interp_PropT_Vis with (k2:=(fun n0 : nat =>
                                                       get_nat_tree'
                                                         (if Nat.eqb n0 0
                                                          then k0 false
                                                          else if Nat.eqb n0 1 then k0 true else k0 false))).
                  2: {
                    red.
                    reflexivity.
                  }
                  2: {
                    setoid_rewrite bind_trigger.
                    destruct NB as [[R1 R3] | [R1 R3]]; subst; auto;
                      reflexivity.
                  }

                  intros a RET.
                  right.
                  rewrite (itree_eta_ (k1 _)).
                  rewrite (itree_eta_ (if Nat.eqb a 0 then _ else _)).
                  eapply CIH; repeat rewrite <- itree_eta_.

                  specialize (K_RUTT a (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)).
                  forward K_RUTT; cbn; auto.
                  pclearbot.
                  apply K_RUTT.

                  setoid_rewrite H in HK.
                  specialize (HK (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)).

                  destruct a; [| destruct a]; cbn in *.
                  - forward HK.
                    { eapply ReturnsVis.
                      unfold ITree.trigger.
                      reflexivity.
                      constructor. reflexivity.
                    }
                    pclearbot.
                    assert (k0 false ≈ k3 false) as K0K3 by apply REL.
                    rewrite K0K3.
                    eapply HK.
                  - repeat (rewrite <- itree_eta_).
                    forward HK.
                    { eapply ReturnsVis.
                      unfold ITree.trigger.
                      reflexivity.
                      constructor. reflexivity.
                    }
                    pclearbot.
                    assert (k0 true ≈ k3 true) as K0K3 by apply REL.
                    setoid_rewrite K0K3.
                    eapply HK.
                  - (* Bogus case *)
                    repeat (rewrite <- itree_eta_).
                    forward HK.
                    { eapply ReturnsVis.
                      unfold ITree.trigger.
                      reflexivity.
                      constructor. reflexivity.
                    }
                    pclearbot.
                    assert (k0 false ≈ k3 false) as K0K3 by apply REL.
                    setoid_rewrite K0K3.
                    eapply HK.
                }
              }

              { rewrite <- x.
                pstep; red; cbn.
                constructor; auto.

                specialize (IHeqitF b k3 t1 HK H eq_refl eq_refl).
                forward IHeqitF; auto.
                forward IHeqitF; auto.
                forward IHeqitF; auto.

                punfold IHeqitF.
              }
          }
      - pstep; red; cbn.
        constructor; auto.
        forward IHREL; auto.
        forward IHREL; auto.

        punfold IHREL.
      - eapply IHREL; eauto.
        red in RUN.
        setoid_rewrite tau_eutt in RUN.
        rewrite <- itree_eta_.
        apply RUN.
    }
    admit.

    { apply get_inf_tree_rutt.
    }
  Qed.


    assert (itree InfLP.Events.L3 TopLevelBigIntptr.res_L6).



    { revert FIN_HANDLED.
      revert REL.
      revert t_inf t_fin t_fin2.
      cofix CIH.

      intros t_inf t_fin t_fin2 REL FIN_HANDLED.
      apply orutt_inv_Type in REL.
      destruct REL.
      destruct s as [[[[[RET | TAU] | VIS] | VISOOM] | TauL] | TauR].
      - (* Ret *)
        destruct RET as (r1 & r2 & (RRr1r2 & RET1) & RET2).
        admit.
      - (* TauR *)
        exfalso.
        red in REL.
        pinversion REL.
        admit.
        admit.
        admit.
        admit.
        admit.

        Set Nested Proofs Allowed.

        +
          (* Double tau *)
          (exists t1' t2', (paco2 (interp_PropT_ h_spec RR true true (OOME:=OOME)) bot2 t1' t2') * (TauF t1' = observe t1) * (TauF t2' = observe t2)) +
            (* Tau left *)
            (exists t1' t2',
                (interp_PropTF (OOME:=OOME) h_spec RR true true (upaco2 (interp_PropT_ h_spec RR true true (OOME:=OOME)) bot2) (observe t1') (observe t2)) *
                  (TauF t1' = observe t1) * (t2' = observe t2)) +
            (* Tau right *)
            (exists t1' t2',
                (interp_PropTF (OOME:=OOME) h_spec RR true true (upaco2 (interp_PropT_ h_spec RR true true (OOME:=OOME)) bot2) (observe t1) (observe t2')) *
                  (t1' = observe t1) * (TauF t2' = observe t2)) +
            (* OOM vis *)
            (exists (A : Type) (e : OOM A) k1 t1' t2',
                (t1' ≅ vis e k1) * (observe t1' = observe t1) * (t2' = observe t2)) +
            (* Vis nodes *)
            (exists (A : Type) e k1 k2 ta t2',
                (forall (a : A), Returns a ta -> upaco2 (interp_PropT_ h_spec RR true true (OOME:=OOME)) bot2 (k1 a) (k2 a)) *
                  (h_spec A e ta) *
                  (t2' ≈ x <- ta;; k2 x) *
                  (VisF e k1 = observe t1) *
                  (observe t2' = observe t2))
    )
    )%type.
     Admitted.

     apply interp_prop_inv_Type in REL.
     pinversion REL.

     }

     punfold RL2.
     red in RL2.
     punfold H.
     red in H.


     Set Nested Proofs Allowed.

     Definition convert_tree (t : itree L3 (FinMem.MMEP.MMSP.MemState * (MemPropT.store_id * (local_env * @stack local_env * res_L1)))) : itree InfLP.Events.L3 TopLevelBigIntptr.res_L6.
     Proof.
       revert t.
       cofix CIH.
       intros t.
       destruct t.
       rename _observe into t.
       constructor.
       induction t.
       - (* Ret *)
         destruct r as [ms [sid [[lenv s] [genv dv]]]].
         apply RetF.
         (* Convert the finite values to infinite ones*)
         constructor; [|constructor; [| constructor; [| constructor]]].
         + (* MemState conversion *)
           admit.
         + exact sid.
         + (* Locals and local stack *)
           admit.
         + (* Global environment *)
           admit.
         + pose proof DVC2.dvalue_convert_strict.
           specialize (H dv).
           (* I *should* know that converting a finite dvalue to an
            infinite dvalue always succeeds *)
           destruct H.
           -- exact d.
           -- (* OOM here should be a contradiction... *)
             admit.
       - (* Tau *)
         apply TauF.
         specialize (CIH t).
         apply CIH.
       - (* Vis *)
         apply VisF with (X:=X).
         + (* Result from handler *)
           (* We actually already have event conversions... *)
           pose proof (EC2.L3_convert_strict _ e).
           (* Actually the event conversion we have gives us a new itree... *)
           destruct e.
           -- (* ExternalCallE *)
             inv e.
             constructor.

             admit.
         + intros x.
           specialize (k x).
           apply CIH. apply k.
           Guarded.
           punfold t.
     Defined.

    (* I need to find a `t` that corresponds to the `t'` that's in the
       set given by the interpretation of memory events in `t2`...

       I guess I need to know what decisions were made to get `t'` out
       of `t2`, and make similar decisions to get `t` out of `t1`.

       I guess we need to do coinduction on `t2`?

       - Whenever we have a `Ret` `t'` is should going to end up being
         basically the same `Ret`...
       - Tau nodes should basically be irrelevant...
       - Vis nodes have two cases...
         1. The vis node is an event that isn't interpreted by the
            memory handler... No non-determinism in this, so the
            corresponding `t` should just raise the same event again.
         2. The vis node is a memory event...

       In the second case where the vis is a memory event that we
       interpret we can have non-determinism. E.g., we might have an
       Alloca event, and we will have to pick the location in memory
       that the block gets allocated. `t'` can be any tree where a
       valid address for the allocated block is returned... So, we'll
       need to show that any valid address to allocate a block in the
       current state of the finite memory corresponds to a valid
       address to allocate a block in the current state of the
       corresponding infinite memory. This should hopefully not be too
       bad because the infinite and finite memories will have the same
       layout (this assumption is missing from the initial draft
       of this lemma).
     *)

  (*   unfold IS1.MEM.MEM_SPEC_INTERP.interp_memory_prop. *)
  (*   unfold IS2.MEM.MEM_SPEC_INTERP.interp_memory_prop. *)
  (*   cbn. *)
  (*   eapply orutt_interp_state; eauto. *)
  (*   { unfold local_stack_refine_strict in *. *)
  (*     destruct ls1, ls2; *)
  (*     constructor; tauto. *)
  (*   } *)

  (*   intros A B e1 e2 s1 s2 H H0. *)
  (*   eapply orutt_interp_local_stack_h; eauto. *)
  (*   inv H0. *)
  (*   destruct s1, s2; cbn in *; auto. *)

  (*   intros A o s. *)
  (*   exists o. *)
  (*   cbn. *)
  (*   setoid_rewrite bind_trigger. *)
  (*   exists (fun x : A => SemNotations.Ret1 s x). *)
  (*   reflexivity. *)
    (* Qed. *)

  Lemma model_E1E2_L3_orutt_strict_sound
    (p : list
           (LLVMAst.toplevel_entity
              LLVMAst.typ
              (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ)))) :
    model_E1E2_L3_orutt_strict p p.
  Proof.
    apply model_E1E2_13_orutt_strict;
      [ apply model_E1E2_L2_orutt_strict_sound
      | apply local_stack_refine_strict_empty
      ].
  Qed.

  (* If

    - ti2 is a refinement of ti1 tf2 refines ti2 tf1 refines tf2 at
    - finite level

    Not sure that this is true.

    If ti1 -i> ti2

    and ti2 -if> tf2

    And tf2 -f> tf1...

    Does it really follow that ti1 -if> tf1?

    In theory I can refine ti1 to ti2, and to tf1 through
    tf2... BUT... Does this mean I can refine ti1 directly to tf1?

    In theory ti2 has fewer behaviours than ti1, and so if I can
    refine it to tf2, then I can also refine ti1 to tf2.
   *)
  Lemma refine_E1E2_L6_strict_compose_inf_to_fin :
    forall tx ty tz,
      TLR_INF.R.refine_L6 tx ty ->
      refine_E1E2_L6_strict ty tz ->
      refine_E1E2_L6_strict tx tz.
  Proof.
    intros tx ty tz XY_INF YZ_FIN.

    unfold refine_E1E2_L6_strict in *.
    unfold TLR_INF.R.refine_L6 in *.
    unfold TLR_FIN.R.refine_L6 in *.

    intros rz TZ.
    specialize (YZ_FIN rz TZ).
    destruct YZ_FIN as (ry_fin & TY_FIN & YZ).

    unfold L6_convert_PropT_strict in TY_FIN.
    destruct TY_FIN as (ry_inf & TY_INF & ry_fin_inf).

    specialize (XY_INF ry_inf TY_INF).
    destruct XY_INF as (rx_inf & TX_INF & XY_INF).

    set (rx_fin := L4_convert_tree_strict' res_L6_convert_strict_unsafe rx_inf).
    exists rx_fin.
    split.
    - unfold L6_convert_PropT_strict, L4_convert_PropT_strict.
      exists rx_inf; split; auto.
      subst rx_fin.
      reflexivity.
    - rewrite <- YZ.
      rewrite <- ry_fin_inf.
      subst rx_fin.

      (* There's probably a more general lemma hiding here *)
      unfold L4_convert_tree_strict'.

      Unset Universe Checking.
      eapply refine_OOM_h_bind with (RR1:=TopLevelRefinementsBigIntptr.R.refine_res3).
      { intros r1 r2 H.
        unfold TLR_INF.R.refine_res3, TLR_INF.R.refine_res2, TLR_INF.R.refine_res1 in H.
        destruct r1 as [r1a [r1sid [[r1b1 r1b2] [r1c dv1]]]].
        destruct r2 as [r2a [r2sid [[r2b1 r2b2] [r2c dv2]]]].
        cbn.

        inversion H; subst.
        inversion snd_rel; subst.
        inversion snd_rel0; subst.
        inversion snd_rel1; subst.
        cbn in *; subst; reflexivity.
      }
      { apply refine_OOM_h_L6_convert_tree_strict; auto.
      }
  Qed.

  Lemma refine_E1E2_L6_strict_compose_fin_to_inf :
    forall tx ty tz,
      refine_E1E2_L6_strict tx ty ->
      TLR_FIN.R.refine_L6 ty tz ->
      refine_E1E2_L6_strict tx tz.
  Proof.
    intros tx ty tz XY_INF_TO_FIN YZ_FIN.

    unfold refine_E1E2_L6_strict in *.
    unfold TLR_INF.R.refine_L6 in *.
    unfold TLR_FIN.R.refine_L6 in *.

    intros rz TZ.
    specialize (YZ_FIN rz TZ).
    destruct YZ_FIN as (ry_fin & TY_FIN & YZ).

    specialize (XY_INF_TO_FIN ry_fin TY_FIN).
    destruct XY_INF_TO_FIN as (rx_fin & TX_FIN & refine_inf_fin_x).

    exists rx_fin.
    split; auto.
    rewrite refine_inf_fin_x; auto.
  Qed.

  Theorem refine_E1E2_L6_transitive :
    forall ti1 ti2 tf1 tf2,
      TLR_INF.R.refine_L6 ti1 ti2 ->
      refine_E1E2_L6_strict ti2 tf1 ->
      TLR_FIN.R.refine_L6 tf1 tf2 ->
      refine_E1E2_L6_strict ti1 tf2.
  Proof.
    intros ti1 ti2 tf1 tf2 RINF RITOF RFIN.

    eapply refine_E1E2_L6_strict_compose_fin_to_inf; eauto.
    eapply refine_E1E2_L6_strict_compose_inf_to_fin; eauto.
  Qed.

  (** Safe conversion lemmas *)
  (* TODO: These used the Fin to Inf LangRefine that no longer exists
     because we added safe conversion modules... See if I still need
     these *)
  (* Lemma infinite_to_finite_dvalue_convert_safe : *)
  (*   forall dv_i, *)
  (*   exists dv_f, *)
  (*     EC1.DVC.dvalue_convert_strict dv_i = NoOom dv_f /\ *)
  (*       EC2.DVC.dvalue_convert_strict dv_f = NoOom dv_i. *)
  (* Proof. *)
  (*   intros dv_i. *)

  (*   rewrite EC1.DVC.dvalue_convert_equation. *)
  (*   destruct dv_i. *)
  (*   - (* Addresses *) *)

  (*   setoid_rewrite EC2.DVC.dvalue_convert_equation. *)

  (*   (* TODO: Ugh, everything is opaque. Fix and prove. *) *)
  (* Admitted. *)

  (* Lemma L0_convert_safe : *)
  (*   forall t, *)
  (*     InfFinTC.L0_convert_tree' EC1.DVC.dvalue_convert *)
  (*       (FinInfTC.L0_convert_tree' EC2.DVC.dvalue_convert t) ≈ t. *)
  (* Proof. *)
  (*   intros t. *)
  (*   unfold InfFinTC.L0_convert_tree', InfFinTC.L0_convert_tree. *)
  (*   unfold FinInfTC.L0_convert_tree', FinInfTC.L0_convert_tree. *)
  (*   cbn. *)
  (*   setoid_rewrite interp_bind. *)
  (*   rewrite bind_bind. *)
  (*   rewrite interp_interp. *)


  (*   cbn. *)
  (*   red. *)
  (* Admitted. *)

  (** Refinement lemmas *)
  Lemma refine_E1E2_L0_strict_interp_intrinsics :
    forall t1 t2,
      refine_E1E2_L0_strict t1 t2 ->
      refine_E1E2_L0_strict (InfLLVM.Intrinsics.interp_intrinsics t1) (FinLLVM.Intrinsics.interp_intrinsics t2).
  Proof.
    intros t1 t2 RL0.
    red in RL0.
    destruct RL0 as [t1' [OOM_T1 RL0]].
    red in RL0.
    red.
    (* exists (FinInfTC.L0_convert_tree_strict' EC2.DVC.dvalue_convert (FinLLVM.Intrinsics.interp_intrinsics t2)). *)
    (* split. *)
    (* - assert ((FinInfTC.L0_convert_tree' EC2.DVC.dvalue_convert (FinLLVM.Intrinsics.interp_intrinsics t2)) ≈  (FinInfTC.L0_convert_tree' EC2.DVC.dvalue_convert (LLVM.Intrinsics.interp_intrinsics (InfFinTC.L0_convert_tree' EC1.DVC.dvalue_convert t1')))) as EQT2. *)
    (*   { eapply @FinInfTC.L0_convert_tree'_eutt_proper with (RA:=eq). *)
    (*     intros u1 u2 H; subst. *)
    (*     reflexivity. *)

    (*     rewrite RL0. *)
    (*     reflexivity. *)
    (*   } *)

    (*   rewrite EQT2. *)

    (*   eapply refine_OOM_h_transitive with (y:=(InfLLVM.Intrinsics.interp_intrinsics t1')); try typeclasses eauto. *)
    (*   (* May hold... OOM_T1 *) *)
    (*   admit. *)

    (*   red. *)
    (*   red. *)
    (*   (* This might actually be provable by walking through t1'? *)

    (*      The conversions may cause early OOM, but otherwise preserves *)
    (*      the event structure. *)
    (*    *) *)
    (*   admit. *)
    (* - red. *)
    (*   (* This can't hold unless I know converting from E2 -> E1 -> E2 *)
    (*      is "safe" and doesn't cause any OOM. *)

    (*      This should be the case for the particular Inf / Fin case we *)
    (*      care about, though. *)
    (*    *) *)
    (*   rewrite L0_convert_safe. *)
    (*   reflexivity. *)
  Admitted.

  Lemma refine_E1E2_interp_global_strict :
    forall t1 t2 g1 g2,
      refine_E1E2_L0_strict t1 t2 ->
      global_refine_strict g1 g2 ->
      refine_E1E2_L1_strict (interp_global t1 g1) (interp_global t2 g2).
  Proof.
    intros t1 t2 g1 g2 RL0 GENVS.
    red in RL0.
    destruct RL0 as [t1' [OOM_T1 RL0]].
    red.

    (* Perhaps I need a lemma about L1_convert_tree and interp_global here? *)
  Admitted.

  Lemma refine_E1E2_interp_local_stack_strict :
    forall t1 t2 ls1 ls2,
      refine_E1E2_L1_strict t1 t2 ->
      local_stack_refine_strict ls1 ls2 ->
      refine_E1E2_L2_strict (interp_local_stack t1 ls1) (interp_local_stack t2 ls2).
  Proof.
  Admitted.

  (* Most of these are aliases of the above, but some levels of the interpreter interpret more than one event *)
  Lemma refine_E1E2_01_strict :
    forall t1 t2 g1 g2,
      refine_E1E2_L0_strict t1 t2 ->
      global_refine_strict g1 g2 ->
      refine_E1E2_L1_strict (interp_global (InfLLVM.Intrinsics.interp_intrinsics t1) g1) (interp_global (FinLLVM.Intrinsics.interp_intrinsics t2) g2).
  Proof.
    intros t1 t2 g1 g2 RL0 GENVS.
    red in RL0.
    apply refine_E1E2_interp_global_strict; auto.
    apply refine_E1E2_L0_strict_interp_intrinsics; auto.
  Qed.

  Lemma refine_E1E2_12_strict :
    forall t1 t2 l1 l2,
      refine_E1E2_L1_strict t1 t2 ->
      local_stack_refine_strict l1 l2 ->
      refine_E1E2_L2_strict (interp_local_stack t1 l1) (interp_local_stack t2 l2).
  Proof.
    intros t1 t2 g1 g2 RL1 GENVS.
    red in RL1.
    apply refine_E1E2_interp_local_stack_strict; auto.
  Qed.

  Import InterpMemoryProp.
  Lemma refine_E1E2_23_strict :
    forall t1 t2 sid m1 m2,
      refine_E1E2_L2_strict t1 t2 ->
      MemState_refine m1 m2 ->
      refine_E1E2_L3_strict (InfMemInterp.interp_memory_prop eq t1 sid m1) (FinMemInterp.interp_memory_prop eq t2 sid m2).
  Proof.
    intros t1 t2 sid m1 m2 RL2.

  (*
    h1 and h2 are handlers

    (* h2 refines h1 *)
    (forall e,
    refine_E1E2_L3 (h1 e) (h2 e)) ->
    forall u : itree,
    refine_E1E2_L3 (interp_prop h1 u) (interp_prop h2 u)

    Need something a bit more general like rutt.

    (forall e1 e2,
    refine_events e1 e2 ->
    refine_E1E2_L3 (h1 e1) (h2 e2)) ->
    forall u1 u2 : itree,
    rutt refine_events refine_dvalue eq u1 u2 ->
    refine_E1E2_L3 (interp_prop h1 u1) (interp_prop h2 u2)


    (forall e1 e2,
    refine_events e1 e2 ->
    refine_E1E2_L4 (h1 e1) (h2 e2)) ->
    forall u1 u2 : itree,
    refine_E1E2_L3 u1 u2 ->
    refine_E1E2_L4 (interp_prop h1 u1) (interp_prop h2 u2)

   *)

    (* I'll probably need something about MemMonad_valid_state eventually... *)
  Admitted.

  Lemma refine_E1E2_34_strict :
    forall t1 t2,
      refine_E1E2_L3_strict t1 t2 ->
      refine_E1E2_L4_strict (InfLLVM.Pick.model_undef eq t1) (FinLLVM.Pick.model_undef eq t2).
  Proof.
    intros t1 t2 RL3.
    red.
  Admitted.

  Lemma refine_E1E2_45_strict :
    forall t1 t2,
      refine_E1E2_L4_strict t1 t2 ->
      refine_E1E2_L5_strict (model_UB t1) (model_UB t2).
  Proof.
    intros t1 t2 RL4.
    red.
  Admitted.

  Lemma refine_E1E2_56_strict :
    forall t1 t2,
      refine_E1E2_L5_strict t1 t2 ->
      refine_E1E2_L6_strict (refine_OOM eq t1) (refine_OOM eq t2).
  Proof.
    intros t1 t2 RL4.
    red.
  Admitted.


  From Vellvm Require Import Tactics.

  From ITree Require Import
        ITree
        Basics.Monad
        Events.StateFacts
        Eq.Eqit.

  Import TranslateFacts.
  Import TopLevelBigIntptr.
  Import TopLevel64BitIntptr.
  Import InterpreterStackBigIntptr.
  Import TopLevelRefinements64BitIntptr.

  Ltac force_rewrite H :=
    let HB := fresh "HB" in
    pose proof @H as HB; eapply bisimulation_is_eq in HB; rewrite HB; clear HB.

  Tactic Notation "force_rewrite" constr(H) "in" hyp(H') :=
    let HB := fresh "HB" in
    pose proof @H as HB; eapply bisimulation_is_eq in HB; rewrite HB in H'; clear HB.


  (* TODO: this is going to be a big one *)
  Theorem model_E1E2_L0_sound :
    forall (p : LLVM_syntax),
      model_E1E2_L0 p p.
  Proof.
    intros p.
    unfold model_E1E2_L0.
    red.
    unfold refine_L0.
    unfold L0_convert_tree_strict'.
    unfold L0_convert_tree_strict.

    (* exists (FinInfTC.L0_convert_tree_strict' EC2.DVC.dvalue_convert *)
    (*      (denote_vellvm (DynamicTypes.DTYPE_I 32) "main" main_args *)
    (*         (TypToDtyp.convert_types (CFG.mcfg_of_tle p)))). *)

    (* split. *)
    (* - (* src' may have additional OOM *) *)
    (*   (* I think this pretty much has to be by induction over the syntax? *) *)
    (*   admit. *)
    (* - (* src' when converted agrees with target *) *)
    (*   (* Target may just be OOM for all we know *) *)
    (*   red. *)
    (*   setoid_rewrite L0_convert_safe. *)
    (*   reflexivity. *)
  Admitted.

  Theorem model_E1E2_L1_sound :
    forall (p : LLVM_syntax),
      model_E1E2_L1 p p.
  Proof.
    intros p.
    red.

  (* Maybe I need some lemmas akin to these:

    Lemma refine_34 : forall t1 t2,
        refine_L3 t1 t2 -> refine_L4 (model_undef refine_res3 t1) (model_undef refine_res3 t2).

    But for crossing the infinite / finite boundary...

   *)
    unfold model_oom_L1.
    unfold model_gen_oom_L1.
    unfold interp_mcfg1.

    apply refine_E1E2_01_strict.
    { (* Still need to deal with interp_intrinsics... *)
      apply model_E1E2_L0_sound.
    }

    apply global_refine_strict_empty.
  Qed.

  Theorem model_E1E2_L2_sound :
    forall (p : LLVM_syntax),
      model_E1E2_L2 p p.
  Proof.
    intros p.
    red.
    apply refine_E1E2_12_strict; [| apply local_stack_refine_strict_empty].
    apply model_E1E2_L1_sound.
  Qed.

  Theorem model_E1E2_L3_sound :
    forall (p : LLVM_syntax),
      model_E1E2_L3 p p.
  Proof.
    intros p.
    red.
    apply refine_E1E2_23_strict; [| apply MemState_refine_initial].
    apply model_E1E2_L2_sound.
  Qed.

  Theorem model_E1E2_L4_sound :
    forall (p : LLVM_syntax),
      model_E1E2_L4 p p.
  Proof.
    intros p.
    red.
    apply refine_E1E2_34_strict.
    apply model_E1E2_L3_sound.
  Qed.

  Theorem model_E1E2_L5_sound :
    forall (p : LLVM_syntax),
      model_E1E2_L5 p p.
  Proof.
    intros p.
    red.
    apply refine_E1E2_45_strict.
    apply model_E1E2_L4_sound.
  Qed.

  Theorem model_E1E2_L6_sound :
    forall (p : LLVM_syntax),
      model_E1E2_L6 p p.
  Proof.
    intros p.
    red.
    apply refine_E1E2_56_strict.
    apply model_E1E2_L5_sound.
  Qed.

End InfiniteToFinite.
