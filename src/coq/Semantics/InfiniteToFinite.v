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

  Definition sbyte_refine byte_inf byte_fin : Prop :=
    convert_SByte byte_inf = NoOom byte_fin.

  Definition sbytes_refine bytes_inf bytes_fin : Prop :=
    Forall2 sbyte_refine bytes_inf bytes_fin.

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

  Unset Implicit Arguments.
  Unset Contextual Implicit.
  Definition get_inf_tree' :
    forall (t_fin2 : itree L3 (FinMem.MMEP.MMSP.MemState * (MemPropT.store_id * (local_env * @stack local_env * res_L1)))), itree InfLP.Events.L3 TopLevelBigIntptr.res_L6.
  Proof.
    cofix CIH.
    intros t_fin2.
    destruct t_fin2.
    destruct _observe.
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

      Show Proof.
  Defined.

  Set Printing All.
  Set Printing Implicit.
  Set Printing Depth 1000.


  Unset Printing All.
  Unset Printing Implicit.
  Definition get_inf_tree :
    forall (t_fin2 : itree L3 (FinMem.MMEP.MMSP.MemState * (MemPropT.store_id * (local_env * @stack local_env * res_L1)))), itree InfLP.Events.L3 TopLevelBigIntptr.res_L6 :=
cofix CIH (t_fin2 : itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) :
    itree InfLP.Events.L3
      (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
  (fun _observe : itreeF L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue)))) (itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) =>
   match
     _observe
     return
       (itree InfLP.Events.L3
          (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
   with
   | RetF r =>
       (fun r0 : prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))) =>
        @ret (itree InfLP.Events.L3) (@Monad_itree InfLP.Events.L3)
          (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
          match
            r0 return (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
          with
          | pair a b =>
              (fun (ms : FinMem.MMEP.MMSP.MemState) (p : prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))) =>
               match
                 p
                 return
                   (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
               with
               | pair a0 b0 =>
                   (fun (sid : MemPropT.store_id) (p0 : prod (prod local_env (@stack local_env)) (prod global_env dvalue)) =>
                    match
                      p0
                      return
                        (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                    with
                    | pair a1 b1 =>
                        (fun p1 : prod local_env (@stack local_env) =>
                         match
                           p1
                           return
                             (forall _ : prod global_env dvalue,
                              prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                         with
                         | pair a2 b2 =>
                             (fun (lenv : local_env) (s : @stack local_env) (p2 : prod global_env dvalue) =>
                              match
                                p2
                                return
                                  (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                     (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                              with
                              | pair a3 b3 =>
                                  (fun (genv : global_env) (res : dvalue) =>
                                   @pair InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                     (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))) (lift_MemState ms)
                                     (@pair MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)) sid
                                        (@pair (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)
                                           (@pair InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack (lift_local_env lenv) (lift_stack s))
                                           (@pair InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue (lift_global_env genv) (fin_to_inf_dvalue res))))) a3 b3
                              end) a2 b2
                         end) a1 b1
                    end) a0 b0
               end) a b
          end) r
   | TauF t =>
       (fun t0 : itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue)))) =>
        @go InfLP.Events.L3
          (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
          (@TauF InfLP.Events.L3
             (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
             (itree InfLP.Events.L3
                (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
             (CIH t0))) t
   | @VisF _ _ _ X e k =>
       (fun (X0 : Type) (e0 : L3 X0) (k0 : forall _ : X0, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) =>
        let X1 :
          itree InfLP.Events.L3
            (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
          match
            e0
            return
              (itree InfLP.Events.L3
                 (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
          with
          | inl1 x =>
              (fun H : ExternalCallE X0 =>
               (fun H0 : ExternalCallE X0 =>
                let X1 :
                  forall _ : @eq Type X0 X0,
                  itree InfLP.Events.L3
                    (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                  match
                    H0 in (ExternalCallE T)
                    return
                      (forall _ : @eq Type T X0,
                       itree InfLP.Events.L3
                         (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                            (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                  with
                  | ExternalCall t f args =>
                      (fun (t0 : dtyp) (f0 : uvalue) (args0 : list dvalue) (H1 : @eq Type dvalue X0) =>
                       (fun H2 : @eq Type dvalue X0 =>
                        let H3 : @eq Type dvalue X0 := H2 in
                        @eq_rect Type dvalue
                          (fun _ : Type =>
                           forall (_ : dtyp) (_ : uvalue) (_ : list dvalue),
                           itree InfLP.Events.L3
                             (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                          (fun (t1 : dtyp) (f1 : uvalue) (args1 : list dvalue) =>
                           @eq_rect Type dvalue
                             (fun X1 : Type =>
                              forall (_ : forall _ : X1, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : ExternalCallE X1),
                              itree InfLP.Events.L3
                                (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                   (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                             (fun (k1 : forall _ : dvalue, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : ExternalCallE dvalue) =>
                              @go InfLP.Events.L3
                                (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                   (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                (@VisF InfLP.Events.L3
                                   (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                      (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                   (itree InfLP.Events.L3
                                      (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                         (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))) E1.DV.dvalue
                                   (@subevent E1.ExternalCallE InfLP.Events.L3
                                      (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 E1.ExternalCallE InfLP.Events.ExternalCallE (sum1 InfLP.Events.PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun InfLP.Events.ExternalCallE)) E1.DV.dvalue
                                      (E1.ExternalCall t1 (fin_to_inf_uvalue f1) (@map LLVMParams64BitIntptr.Events.DV.dvalue LLVMParamsBigIntptr.Events.DV.dvalue fin_to_inf_dvalue args1)))
                                   (fun x0 : E1.DV.dvalue =>
                                    CIH
                                      (let H5 : OOM DVCInfFin.DV2.dvalue := DVCInfFin.dvalue_convert_strict x0 in
                                       match H5 return (itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) with
                                       | NoOom a => (fun d : DVCInfFin.DV2.dvalue => k1 d) a
                                       | Oom s =>
                                           (fun s0 : string =>
                                            @raiseOOM L3
                                              (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME (sum1 PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) ExternalCallE
                                                 (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) PickUvalueE
                                                    (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 OOME OOME (sum1 UBE (sum1 DebugE FailureE)) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun OOME))))
                                              (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue)))) s0) s
                                       end)))) X0 H2 k0 H0) X0 H3) H1 t0 f0 args0) t f args
                  end in
                X1 (@eq_refl Type X0)) H) x
          | inr1 x =>
              (fun X1 : sum1 PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) X0 =>
               (fun X2 : sum1 PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) X0 =>
                let X3 :
                  itree InfLP.Events.L3
                    (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                  match
                    X2
                    return
                      (itree InfLP.Events.L3
                         (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                            (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                  with
                  | inl1 x0 =>
                      (fun X3 : PickUvalueE X0 =>
                       (fun X4 : PickUvalueE X0 =>
                        let X5 :
                          forall _ : @eq Type X0 X0,
                          itree InfLP.Events.L3
                            (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                               (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                          match
                            X4 in (PickE T)
                            return
                              (forall _ : @eq Type T X0,
                               itree InfLP.Events.L3
                                 (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                    (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                          with
                          | pick Pre x1 =>
                              (fun (Pre0 : Prop) (x2 : uvalue) (H : @eq Type (@sig dvalue (fun _ : dvalue => True)) X0) =>
                               (fun H0 : @eq Type (@sig dvalue (fun _ : dvalue => True)) X0 =>
                                let H1 : @eq Type (@sig dvalue (fun _ : dvalue => True)) X0 := H0 in
                                @eq_rect Type (@sig dvalue (fun _ : dvalue => True))
                                  (fun _ : Type =>
                                   forall (_ : Prop) (_ : uvalue),
                                   itree InfLP.Events.L3
                                     (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                        (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                  (fun (Pre1 : Prop) (x3 : uvalue) =>
                                   @eq_rect Type (@sig dvalue (fun _ : dvalue => True))
                                     (fun X5 : Type =>
                                      forall (_ : forall _ : X5, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : PickUvalueE X5),
                                      itree InfLP.Events.L3
                                        (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                           (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                     (fun (k1 : forall _ : @sig dvalue (fun _ : dvalue => True), itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : PickUvalueE (@sig dvalue (fun _ : dvalue => True))) =>
                                      @go InfLP.Events.L3
                                        (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                           (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                        (@VisF InfLP.Events.L3
                                           (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                              (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                           (itree InfLP.Events.L3
                                              (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                 (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                           (@sig InfLP.Events.DV.dvalue (fun _ : InfLP.Events.DV.dvalue => True))
                                           (@subevent (@E1.PickE LLVMParamsBigIntptr.Events.DV.uvalue InfLP.Events.DV.dvalue (fun (_ : InfLP.Events.DV.uvalue) (_ : InfLP.Events.DV.dvalue) => True)) InfLP.Events.L3
                                              (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 (@E1.PickE LLVMParamsBigIntptr.Events.DV.uvalue InfLP.Events.DV.dvalue (fun (_ : InfLP.Events.DV.uvalue) (_ : InfLP.Events.DV.dvalue) => True))
                                                 (sum1 InfLP.Events.PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) InfLP.Events.ExternalCallE
                                                 (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 (@E1.PickE LLVMParamsBigIntptr.Events.DV.uvalue InfLP.Events.DV.dvalue (fun (_ : InfLP.Events.DV.uvalue) (_ : InfLP.Events.DV.dvalue) => True)) InfLP.Events.PickUvalueE
                                                    (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun InfLP.Events.PickUvalueE))) (@sig InfLP.Events.DV.dvalue (fun _ : InfLP.Events.DV.dvalue => True))
                                              (@E1.pick LLVMParamsBigIntptr.Events.DV.uvalue InfLP.Events.DV.dvalue (fun (_ : InfLP.Events.DV.uvalue) (_ : InfLP.Events.DV.dvalue) => True) Pre1 (fin_to_inf_uvalue x3)))
                                           (fun res : @sig InfLP.Events.DV.dvalue (fun _ : InfLP.Events.DV.dvalue => True) =>
                                            match
                                              res
                                              return
                                                (itree InfLP.Events.L3
                                                   (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                      (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                            with
                                            | @exist _ _ x4 p =>
                                                (fun (x5 : InfLP.Events.DV.dvalue) (t : True) =>
                                                 CIH
                                                   (let H2 : OOM DVCInfFin.DV2.dvalue := DVCInfFin.dvalue_convert_strict x5 in
                                                    match H2 return (itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) with
                                                    | NoOom a => (fun d : DVCInfFin.DV2.dvalue => k1 (@exist dvalue (fun _ : dvalue => True) d t)) a
                                                    | Oom s =>
                                                        (fun s0 : string =>
                                                         @raiseOOM L3
                                                           (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME (sum1 PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) ExternalCallE
                                                              (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) PickUvalueE
                                                                 (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 OOME OOME (sum1 UBE (sum1 DebugE FailureE)) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun OOME))))
                                                           (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue)))) s0) s
                                                    end)) x4 p
                                            end))) X0 H0 k0 X4) X0 H1) H Pre0 x2) Pre x1
                          end in
                        X5 (@eq_refl Type X0)) X3) x0
                  | inr1 x0 =>
                      (fun H : sum1 OOME (sum1 UBE (sum1 DebugE FailureE)) X0 =>
                       (fun H0 : sum1 OOME (sum1 UBE (sum1 DebugE FailureE)) X0 =>
                        let X3 :
                          itree InfLP.Events.L3
                            (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                               (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                          match
                            H0
                            return
                              (itree InfLP.Events.L3
                                 (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                    (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                          with
                          | inl1 x1 =>
                              (fun H1 : OOME X0 =>
                               (fun H2 : OOME X0 =>
                                let X3 :
                                  forall _ : @eq Type X0 X0,
                                  itree InfLP.Events.L3
                                    (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                       (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                  match
                                    H2 in (OOME T)
                                    return
                                      (forall _ : @eq Type T X0,
                                       itree InfLP.Events.L3
                                         (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                            (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                  with
                                  | ThrowOOM x2 =>
                                      (fun (H3 : string) (H4 : @eq Type Empty_set X0) =>
                                       (fun H5 : @eq Type Empty_set X0 =>
                                        let H6 : @eq Type Empty_set X0 := H5 in
                                        @eq_rect Type Empty_set
                                          (fun _ : Type =>
                                           forall _ : string,
                                           itree InfLP.Events.L3
                                             (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                          (fun H7 : string =>
                                           @eq_rect Type Empty_set
                                             (fun X3 : Type =>
                                              forall (_ : forall _ : X3, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : OOME X3),
                                              itree InfLP.Events.L3
                                                (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                   (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                             (fun (_ : forall _ : Empty_set, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : OOME Empty_set) =>
                                              @raiseOOM InfLP.Events.L3
                                                (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME (sum1 InfLP.Events.PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) InfLP.Events.ExternalCallE
                                                   (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) InfLP.Events.PickUvalueE
                                                      (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 OOME OOME (sum1 UBE (sum1 DebugE FailureE)) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun OOME))))
                                                (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                   (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) H7) X0 H5 k0 H2) X0 H6) H4 H3)
                                        x2
                                  end in
                                X3 (@eq_refl Type X0)) H1) x1
                          | inr1 x1 =>
                              (fun H1 : sum1 UBE (sum1 DebugE FailureE) X0 =>
                               (fun H2 : sum1 UBE (sum1 DebugE FailureE) X0 =>
                                let X3 :
                                  itree InfLP.Events.L3
                                    (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                       (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                  match
                                    H2
                                    return
                                      (itree InfLP.Events.L3
                                         (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                            (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                  with
                                  | inl1 x2 =>
                                      (fun H3 : UBE X0 =>
                                       (fun H4 : UBE X0 =>
                                        let X3 :
                                          forall _ : @eq Type X0 X0,
                                          itree InfLP.Events.L3
                                            (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                               (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                          match
                                            H4 in (UBE T)
                                            return
                                              (forall _ : @eq Type T X0,
                                               itree InfLP.Events.L3
                                                 (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                    (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                          with
                                          | ThrowUB x3 =>
                                              (fun (H5 : string) (H6 : @eq Type Empty_set X0) =>
                                               (fun H7 : @eq Type Empty_set X0 =>
                                                let H8 : @eq Type Empty_set X0 := H7 in
                                                @eq_rect Type Empty_set
                                                  (fun _ : Type =>
                                                   forall _ : string,
                                                   itree InfLP.Events.L3
                                                     (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                        (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                  (fun H9 : string =>
                                                   @eq_rect Type Empty_set
                                                     (fun X3 : Type =>
                                                      forall (_ : forall _ : X3, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : UBE X3),
                                                      itree InfLP.Events.L3
                                                        (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                           (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                     (fun (_ : forall _ : Empty_set, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : UBE Empty_set) =>
                                                      @raiseUB InfLP.Events.L3
                                                        (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 UBE (sum1 InfLP.Events.PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) InfLP.Events.ExternalCallE
                                                           (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 UBE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) InfLP.Events.PickUvalueE
                                                              (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 UBE (sum1 UBE (sum1 DebugE FailureE)) OOME
                                                                 (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 UBE UBE (sum1 DebugE FailureE) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun UBE)))))
                                                        (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                           (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) H9) X0 H7 k0 H4) X0 H8)
                                                 H6 H5) x3
                                          end in
                                        X3 (@eq_refl Type X0)) H3) x2
                                  | inr1 x2 =>
                                      (fun H3 : sum1 DebugE FailureE X0 =>
                                       (fun H4 : sum1 DebugE FailureE X0 =>
                                        let X3 :
                                          itree InfLP.Events.L3
                                            (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                               (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                          match
                                            H4
                                            return
                                              (itree InfLP.Events.L3
                                                 (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                    (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                          with
                                          | inl1 x3 =>
                                              (fun H5 : DebugE X0 =>
                                               (fun H6 : DebugE X0 =>
                                                let X3 :
                                                  forall _ : @eq Type X0 X0,
                                                  itree InfLP.Events.L3
                                                    (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                       (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                                  match
                                                    H6 in (DebugE T)
                                                    return
                                                      (forall _ : @eq Type T X0,
                                                       itree InfLP.Events.L3
                                                         (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                            (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                  with
                                                  | Debug x4 =>
                                                      (fun (H7 : string) (H8 : @eq Type unit X0) =>
                                                       (fun H9 : @eq Type unit X0 =>
                                                        let H10 : @eq Type unit X0 := H9 in
                                                        @eq_rect Type unit
                                                          (fun _ : Type =>
                                                           forall _ : string,
                                                           itree InfLP.Events.L3
                                                             (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                          (fun H11 : string =>
                                                           @eq_rect Type unit
                                                             (fun X3 : Type =>
                                                              forall (_ : forall _ : X3, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : DebugE X3),
                                                              itree InfLP.Events.L3
                                                                (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                   (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                             (fun (k1 : forall _ : unit, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : DebugE unit) =>
                                                              @go InfLP.Events.L3
                                                                (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                   (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                                                (@VisF InfLP.Events.L3
                                                                   (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                      (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                                                   (itree InfLP.Events.L3
                                                                      (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                         (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))) unit
                                                                   (@subevent DebugE InfLP.Events.L3
                                                                      (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 DebugE (sum1 InfLP.Events.PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) InfLP.Events.ExternalCallE
                                                                         (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 DebugE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) InfLP.Events.PickUvalueE
                                                                            (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 DebugE (sum1 UBE (sum1 DebugE FailureE)) OOME
                                                                               (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 DebugE (sum1 DebugE FailureE) UBE
                                                                                  (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 DebugE DebugE FailureE (@ReSum_id (forall _ : Type, Type) IFun Id_IFun DebugE)))))) unit (Debug H11)) (fun H13 : unit => CIH (k1 H13)))) X0 H9 k0 H6) X0 H10) H8 H7) x4
                                                  end in
                                                X3 (@eq_refl Type X0)) H5) x3
                                          | inr1 x3 =>
                                              (fun H5 : FailureE X0 =>
                                               (fun H6 : FailureE X0 =>
                                                let X3 :
                                                  forall _ : @eq Type X0 X0,
                                                  itree InfLP.Events.L3
                                                    (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                       (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                                  match
                                                    H6 in (FailureE T)
                                                    return
                                                      (forall _ : @eq Type T X0,
                                                       itree InfLP.Events.L3
                                                         (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                            (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                  with
                                                  | Throw x4 =>
                                                      (fun (H7 : string) (H8 : @eq Type Empty_set X0) =>
                                                       (fun H9 : @eq Type Empty_set X0 =>
                                                        let H10 : @eq Type Empty_set X0 := H9 in
                                                        @eq_rect Type Empty_set
                                                          (fun _ : Type =>
                                                           forall _ : string,
                                                           itree InfLP.Events.L3
                                                             (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                          (fun H11 : string =>
                                                           @eq_rect Type Empty_set
                                                             (fun X3 : Type =>
                                                              forall (_ : forall _ : X3, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : FailureE X3),
                                                              itree InfLP.Events.L3
                                                                (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                   (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                             (fun (_ : forall _ : Empty_set, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : FailureE Empty_set) =>
                                                              @LLVMEvents.raise InfLP.Events.L3
                                                                (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                   (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                                                (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 FailureE (sum1 InfLP.Events.PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) InfLP.Events.ExternalCallE
                                                                   (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 FailureE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) InfLP.Events.PickUvalueE
                                                                      (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 FailureE (sum1 UBE (sum1 DebugE FailureE)) OOME
                                                                         (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 FailureE (sum1 DebugE FailureE) UBE
                                                                            (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 FailureE FailureE DebugE (@ReSum_id (forall _ : Type, Type) IFun Id_IFun FailureE)))))) H11) X0 H9 k0 H6) X0 H10) H8 H7) x4
                                                  end in
                                                X3 (@eq_refl Type X0)) H5) x3
                                          end in
                                        X3) H3) x2
                                  end in
                                X3) H1) x1
                          end in
                        X3) H) x0
                  end in
                X3) X1) x
          end in
        X1) X e k
   end) (@_observe _ _ t_fin2).

  Definition _get_inf_tree (t_fin2 : itree' L3 (FinMem.MMEP.MMSP.MemState * (MemPropT.store_id * (local_env * @stack local_env * res_L1)))) : itree InfLP.Events.L3 TopLevelBigIntptr.res_L6 :=
    match t_fin2 with
    | RetF r =>
        (fun r0 : prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))) =>
           @ret (itree InfLP.Events.L3) (@Monad_itree InfLP.Events.L3)
             (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
             match
               r0 return (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
             with
             | pair a b =>
                 (fun (ms : FinMem.MMEP.MMSP.MemState) (p : prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))) =>
                    match
                      p
                      return
                      (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                    with
                    | pair a0 b0 =>
                        (fun (sid : MemPropT.store_id) (p0 : prod (prod local_env (@stack local_env)) (prod global_env dvalue)) =>
                           match
                             p0
                             return
                             (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                           with
                           | pair a1 b1 =>
                               (fun p1 : prod local_env (@stack local_env) =>
                                  match
                                    p1
                                    return
                                    (forall _ : prod global_env dvalue,
                                        prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                          (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                  with
                                  | pair a2 b2 =>
                                      (fun (lenv : local_env) (s : @stack local_env) (p2 : prod global_env dvalue) =>
                                         match
                                           p2
                                           return
                                           (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                              (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                         with
                                         | pair a3 b3 =>
                                             (fun (genv : global_env) (res : dvalue) =>
                                                @pair InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                  (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))) (lift_MemState ms)
                                                  (@pair MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)) sid
                                                     (@pair (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)
                                                        (@pair InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack (lift_local_env lenv) (lift_stack s))
                                                        (@pair InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue (lift_global_env genv) (fin_to_inf_dvalue res))))) a3 b3
                                         end) a2 b2
                                  end) a1 b1
                           end) a0 b0
                    end) a b
             end) r
    | TauF t =>
        (fun t0 : itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue)))) =>
           @go InfLP.Events.L3
             (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
             (@TauF InfLP.Events.L3
                (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                (itree InfLP.Events.L3
                   (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                (get_inf_tree t0))) t
    | VisF X e k =>
       (fun (X0 : Type) (e0 : L3 X0) (k0 : forall _ : X0, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) =>
        let X1 :
          itree InfLP.Events.L3
            (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
          match
            e0
            return
              (itree InfLP.Events.L3
                 (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
          with
          | inl1 x =>
              (fun H : ExternalCallE X0 =>
               (fun H0 : ExternalCallE X0 =>
                let X1 :
                  forall _ : @eq Type X0 X0,
                  itree InfLP.Events.L3
                    (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                  match
                    H0 in (ExternalCallE T)
                    return
                      (forall _ : @eq Type T X0,
                       itree InfLP.Events.L3
                         (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                            (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                  with
                  | ExternalCall t f args =>
                      (fun (t0 : dtyp) (f0 : uvalue) (args0 : list dvalue) (H1 : @eq Type dvalue X0) =>
                       (fun H2 : @eq Type dvalue X0 =>
                        let H3 : @eq Type dvalue X0 := H2 in
                        @eq_rect Type dvalue
                          (fun _ : Type =>
                           forall (_ : dtyp) (_ : uvalue) (_ : list dvalue),
                           itree InfLP.Events.L3
                             (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                          (fun (t1 : dtyp) (f1 : uvalue) (args1 : list dvalue) =>
                           @eq_rect Type dvalue
                             (fun X1 : Type =>
                              forall (_ : forall _ : X1, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : ExternalCallE X1),
                              itree InfLP.Events.L3
                                (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                   (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                             (fun (k1 : forall _ : dvalue, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : ExternalCallE dvalue) =>
                              @go InfLP.Events.L3
                                (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                   (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                (@VisF InfLP.Events.L3
                                   (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                      (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                   (itree InfLP.Events.L3
                                      (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                         (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))) E1.DV.dvalue
                                   (@subevent E1.ExternalCallE InfLP.Events.L3
                                      (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 E1.ExternalCallE InfLP.Events.ExternalCallE (sum1 InfLP.Events.PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun InfLP.Events.ExternalCallE)) E1.DV.dvalue
                                      (E1.ExternalCall t1 (fin_to_inf_uvalue f1) (@map LLVMParams64BitIntptr.Events.DV.dvalue LLVMParamsBigIntptr.Events.DV.dvalue fin_to_inf_dvalue args1)))
                                   (fun x0 : E1.DV.dvalue =>
                                    get_inf_tree
                                      (let H5 : OOM DVCInfFin.DV2.dvalue := DVCInfFin.dvalue_convert_strict x0 in
                                       match H5 return (itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) with
                                       | NoOom a => (fun d : DVCInfFin.DV2.dvalue => k1 d) a
                                       | Oom s =>
                                           (fun s0 : string =>
                                            @raiseOOM L3
                                              (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME (sum1 PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) ExternalCallE
                                                 (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) PickUvalueE
                                                    (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 OOME OOME (sum1 UBE (sum1 DebugE FailureE)) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun OOME))))
                                              (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue)))) s0) s
                                       end)))) X0 H2 k0 H0) X0 H3) H1 t0 f0 args0) t f args
                  end in
                X1 (@eq_refl Type X0)) H) x
          | inr1 x =>
              (fun X1 : sum1 PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) X0 =>
               (fun X2 : sum1 PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) X0 =>
                let X3 :
                  itree InfLP.Events.L3
                    (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                  match
                    X2
                    return
                      (itree InfLP.Events.L3
                         (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                            (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                  with
                  | inl1 x0 =>
                      (fun X3 : PickUvalueE X0 =>
                       (fun X4 : PickUvalueE X0 =>
                        let X5 :
                          forall _ : @eq Type X0 X0,
                          itree InfLP.Events.L3
                            (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                               (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                          match
                            X4 in (PickE T)
                            return
                              (forall _ : @eq Type T X0,
                               itree InfLP.Events.L3
                                 (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                    (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                          with
                          | pick Pre x1 =>
                              (fun (Pre0 : Prop) (x2 : uvalue) (H : @eq Type (@sig dvalue (fun _ : dvalue => True)) X0) =>
                               (fun H0 : @eq Type (@sig dvalue (fun _ : dvalue => True)) X0 =>
                                let H1 : @eq Type (@sig dvalue (fun _ : dvalue => True)) X0 := H0 in
                                @eq_rect Type (@sig dvalue (fun _ : dvalue => True))
                                  (fun _ : Type =>
                                   forall (_ : Prop) (_ : uvalue),
                                   itree InfLP.Events.L3
                                     (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                        (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                  (fun (Pre1 : Prop) (x3 : uvalue) =>
                                   @eq_rect Type (@sig dvalue (fun _ : dvalue => True))
                                     (fun X5 : Type =>
                                      forall (_ : forall _ : X5, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : PickUvalueE X5),
                                      itree InfLP.Events.L3
                                        (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                           (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                     (fun (k1 : forall _ : @sig dvalue (fun _ : dvalue => True), itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : PickUvalueE (@sig dvalue (fun _ : dvalue => True))) =>
                                      @go InfLP.Events.L3
                                        (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                           (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                        (@VisF InfLP.Events.L3
                                           (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                              (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                           (itree InfLP.Events.L3
                                              (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                 (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                           (@sig InfLP.Events.DV.dvalue (fun _ : InfLP.Events.DV.dvalue => True))
                                           (@subevent (@E1.PickE LLVMParamsBigIntptr.Events.DV.uvalue InfLP.Events.DV.dvalue (fun (_ : InfLP.Events.DV.uvalue) (_ : InfLP.Events.DV.dvalue) => True)) InfLP.Events.L3
                                              (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 (@E1.PickE LLVMParamsBigIntptr.Events.DV.uvalue InfLP.Events.DV.dvalue (fun (_ : InfLP.Events.DV.uvalue) (_ : InfLP.Events.DV.dvalue) => True))
                                                 (sum1 InfLP.Events.PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) InfLP.Events.ExternalCallE
                                                 (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 (@E1.PickE LLVMParamsBigIntptr.Events.DV.uvalue InfLP.Events.DV.dvalue (fun (_ : InfLP.Events.DV.uvalue) (_ : InfLP.Events.DV.dvalue) => True)) InfLP.Events.PickUvalueE
                                                    (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun InfLP.Events.PickUvalueE))) (@sig InfLP.Events.DV.dvalue (fun _ : InfLP.Events.DV.dvalue => True))
                                              (@E1.pick LLVMParamsBigIntptr.Events.DV.uvalue InfLP.Events.DV.dvalue (fun (_ : InfLP.Events.DV.uvalue) (_ : InfLP.Events.DV.dvalue) => True) Pre1 (fin_to_inf_uvalue x3)))
                                           (fun res : @sig InfLP.Events.DV.dvalue (fun _ : InfLP.Events.DV.dvalue => True) =>
                                            match
                                              res
                                              return
                                                (itree InfLP.Events.L3
                                                   (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                      (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                            with
                                            | @exist _ _ x4 p =>
                                                (fun (x5 : InfLP.Events.DV.dvalue) (t : True) =>
                                                 get_inf_tree
                                                   (let H2 : OOM DVCInfFin.DV2.dvalue := DVCInfFin.dvalue_convert_strict x5 in
                                                    match H2 return (itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) with
                                                    | NoOom a => (fun d : DVCInfFin.DV2.dvalue => k1 (@exist dvalue (fun _ : dvalue => True) d t)) a
                                                    | Oom s =>
                                                        (fun s0 : string =>
                                                         @raiseOOM L3
                                                           (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME (sum1 PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) ExternalCallE
                                                              (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) PickUvalueE
                                                                 (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 OOME OOME (sum1 UBE (sum1 DebugE FailureE)) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun OOME))))
                                                           (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue)))) s0) s
                                                    end)) x4 p
                                            end))) X0 H0 k0 X4) X0 H1) H Pre0 x2) Pre x1
                          end in
                        X5 (@eq_refl Type X0)) X3) x0
                  | inr1 x0 =>
                      (fun H : sum1 OOME (sum1 UBE (sum1 DebugE FailureE)) X0 =>
                       (fun H0 : sum1 OOME (sum1 UBE (sum1 DebugE FailureE)) X0 =>
                        let X3 :
                          itree InfLP.Events.L3
                            (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                               (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                          match
                            H0
                            return
                              (itree InfLP.Events.L3
                                 (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                    (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                          with
                          | inl1 x1 =>
                              (fun H1 : OOME X0 =>
                               (fun H2 : OOME X0 =>
                                let X3 :
                                  forall _ : @eq Type X0 X0,
                                  itree InfLP.Events.L3
                                    (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                       (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                  match
                                    H2 in (OOME T)
                                    return
                                      (forall _ : @eq Type T X0,
                                       itree InfLP.Events.L3
                                         (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                            (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                  with
                                  | ThrowOOM x2 =>
                                      (fun (H3 : string) (H4 : @eq Type Empty_set X0) =>
                                       (fun H5 : @eq Type Empty_set X0 =>
                                        let H6 : @eq Type Empty_set X0 := H5 in
                                        @eq_rect Type Empty_set
                                          (fun _ : Type =>
                                           forall _ : string,
                                           itree InfLP.Events.L3
                                             (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                          (fun H7 : string =>
                                           @eq_rect Type Empty_set
                                             (fun X3 : Type =>
                                              forall (_ : forall _ : X3, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : OOME X3),
                                              itree InfLP.Events.L3
                                                (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                   (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                             (fun (_ : forall _ : Empty_set, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : OOME Empty_set) =>
                                              @raiseOOM InfLP.Events.L3
                                                (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME (sum1 InfLP.Events.PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) InfLP.Events.ExternalCallE
                                                   (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) InfLP.Events.PickUvalueE
                                                      (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 OOME OOME (sum1 UBE (sum1 DebugE FailureE)) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun OOME))))
                                                (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                   (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) H7) X0 H5 k0 H2) X0 H6) H4 H3)
                                        x2
                                  end in
                                X3 (@eq_refl Type X0)) H1) x1
                          | inr1 x1 =>
                              (fun H1 : sum1 UBE (sum1 DebugE FailureE) X0 =>
                               (fun H2 : sum1 UBE (sum1 DebugE FailureE) X0 =>
                                let X3 :
                                  itree InfLP.Events.L3
                                    (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                       (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                  match
                                    H2
                                    return
                                      (itree InfLP.Events.L3
                                         (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                            (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                  with
                                  | inl1 x2 =>
                                      (fun H3 : UBE X0 =>
                                       (fun H4 : UBE X0 =>
                                        let X3 :
                                          forall _ : @eq Type X0 X0,
                                          itree InfLP.Events.L3
                                            (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                               (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                          match
                                            H4 in (UBE T)
                                            return
                                              (forall _ : @eq Type T X0,
                                               itree InfLP.Events.L3
                                                 (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                    (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                          with
                                          | ThrowUB x3 =>
                                              (fun (H5 : string) (H6 : @eq Type Empty_set X0) =>
                                               (fun H7 : @eq Type Empty_set X0 =>
                                                let H8 : @eq Type Empty_set X0 := H7 in
                                                @eq_rect Type Empty_set
                                                  (fun _ : Type =>
                                                   forall _ : string,
                                                   itree InfLP.Events.L3
                                                     (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                        (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                  (fun H9 : string =>
                                                   @eq_rect Type Empty_set
                                                     (fun X3 : Type =>
                                                      forall (_ : forall _ : X3, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : UBE X3),
                                                      itree InfLP.Events.L3
                                                        (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                           (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                     (fun (_ : forall _ : Empty_set, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : UBE Empty_set) =>
                                                      @raiseUB InfLP.Events.L3
                                                        (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 UBE (sum1 InfLP.Events.PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) InfLP.Events.ExternalCallE
                                                           (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 UBE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) InfLP.Events.PickUvalueE
                                                              (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 UBE (sum1 UBE (sum1 DebugE FailureE)) OOME
                                                                 (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 UBE UBE (sum1 DebugE FailureE) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun UBE)))))
                                                        (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                           (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) H9) X0 H7 k0 H4) X0 H8)
                                                 H6 H5) x3
                                          end in
                                        X3 (@eq_refl Type X0)) H3) x2
                                  | inr1 x2 =>
                                      (fun H3 : sum1 DebugE FailureE X0 =>
                                       (fun H4 : sum1 DebugE FailureE X0 =>
                                        let X3 :
                                          itree InfLP.Events.L3
                                            (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                               (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                          match
                                            H4
                                            return
                                              (itree InfLP.Events.L3
                                                 (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                    (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                          with
                                          | inl1 x3 =>
                                              (fun H5 : DebugE X0 =>
                                               (fun H6 : DebugE X0 =>
                                                let X3 :
                                                  forall _ : @eq Type X0 X0,
                                                  itree InfLP.Events.L3
                                                    (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                       (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                                  match
                                                    H6 in (DebugE T)
                                                    return
                                                      (forall _ : @eq Type T X0,
                                                       itree InfLP.Events.L3
                                                         (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                            (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                  with
                                                  | Debug x4 =>
                                                      (fun (H7 : string) (H8 : @eq Type unit X0) =>
                                                       (fun H9 : @eq Type unit X0 =>
                                                        let H10 : @eq Type unit X0 := H9 in
                                                        @eq_rect Type unit
                                                          (fun _ : Type =>
                                                           forall _ : string,
                                                           itree InfLP.Events.L3
                                                             (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                          (fun H11 : string =>
                                                           @eq_rect Type unit
                                                             (fun X3 : Type =>
                                                              forall (_ : forall _ : X3, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : DebugE X3),
                                                              itree InfLP.Events.L3
                                                                (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                   (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                             (fun (k1 : forall _ : unit, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : DebugE unit) =>
                                                              @go InfLP.Events.L3
                                                                (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                   (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                                                (@VisF InfLP.Events.L3
                                                                   (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                      (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                                                   (itree InfLP.Events.L3
                                                                      (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                         (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))) unit
                                                                   (@subevent DebugE InfLP.Events.L3
                                                                      (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 DebugE (sum1 InfLP.Events.PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) InfLP.Events.ExternalCallE
                                                                         (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 DebugE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) InfLP.Events.PickUvalueE
                                                                            (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 DebugE (sum1 UBE (sum1 DebugE FailureE)) OOME
                                                                               (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 DebugE (sum1 DebugE FailureE) UBE
                                                                                  (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 DebugE DebugE FailureE (@ReSum_id (forall _ : Type, Type) IFun Id_IFun DebugE)))))) unit (Debug H11)) (fun H13 : unit => get_inf_tree (k1 H13)))) X0 H9 k0 H6) X0 H10) H8 H7) x4
                                                  end in
                                                X3 (@eq_refl Type X0)) H5) x3
                                          | inr1 x3 =>
                                              (fun H5 : FailureE X0 =>
                                               (fun H6 : FailureE X0 =>
                                                let X3 :
                                                  forall _ : @eq Type X0 X0,
                                                  itree InfLP.Events.L3
                                                    (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                       (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                                  match
                                                    H6 in (FailureE T)
                                                    return
                                                      (forall _ : @eq Type T X0,
                                                       itree InfLP.Events.L3
                                                         (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                            (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                  with
                                                  | Throw x4 =>
                                                      (fun (H7 : string) (H8 : @eq Type Empty_set X0) =>
                                                       (fun H9 : @eq Type Empty_set X0 =>
                                                        let H10 : @eq Type Empty_set X0 := H9 in
                                                        @eq_rect Type Empty_set
                                                          (fun _ : Type =>
                                                           forall _ : string,
                                                           itree InfLP.Events.L3
                                                             (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                          (fun H11 : string =>
                                                           @eq_rect Type Empty_set
                                                             (fun X3 : Type =>
                                                              forall (_ : forall _ : X3, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : FailureE X3),
                                                              itree InfLP.Events.L3
                                                                (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                   (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                             (fun (_ : forall _ : Empty_set, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : FailureE Empty_set) =>
                                                              @LLVMEvents.raise InfLP.Events.L3
                                                                (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                   (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                                                (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 FailureE (sum1 InfLP.Events.PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) InfLP.Events.ExternalCallE
                                                                   (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 FailureE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) InfLP.Events.PickUvalueE
                                                                      (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 FailureE (sum1 UBE (sum1 DebugE FailureE)) OOME
                                                                         (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 FailureE (sum1 DebugE FailureE) UBE
                                                                            (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 FailureE FailureE DebugE (@ReSum_id (forall _ : Type, Type) IFun Id_IFun FailureE)))))) H11) X0 H9 k0 H6) X0 H10) H8 H7) x4
                                                  end in
                                                X3 (@eq_refl Type X0)) H5) x3
                                          end in
                                        X3) H3) x2
                                  end in
                                X3) H1) x1
                          end in
                        X3) H) x0
                  end in
                X3) X1) x
          end in
        X1) X e k
    end.

  Require Import ITree.Eq.EuttExtras.

  Lemma paco2_eq_itree_refl : forall E R r (t : itree E R), paco2 (eqit_ eq false false id) r t t.
  Proof.
    intros. eapply paco2_mon with (r := bot2); intuition.
    enough (t ≅ t); auto. reflexivity.
  Qed.

  Lemma get_inf_tree_equation :
    forall t_fin2,
      get_inf_tree t_fin2 ≅ _get_inf_tree (observe t_fin2).
  Proof.
    pcofix CIH.
    intros t_fin2.
    destruct (observe t_fin2) eqn:HTFIN.
    - rewrite (itree_eta_ t_fin2).
      rewrite HTFIN.
      cbn.
      pstep; red; cbn.
      constructor.
      reflexivity.
    - rewrite (itree_eta_ t_fin2).
      rewrite HTFIN.
      cbn.
      pstep; red; cbn.
      constructor.
      left.
      apply paco2_eq_itree_refl.
    - rewrite (itree_eta_ t_fin2).
      unfold _get_inf_tree.
      rewrite HTFIN.
      destruct e.
      admit.
      admit.
  Admitted.

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
        destruct RUN as [[r3 [REQ EQ]] | [A [e [k EUTT]]]]; subst.
        2: {
          eapply paco2_mon_bot; eauto.
          rewrite EUTT.
          pstep; red; cbn.
          econstructor.
          destruct e.
          pstep; red; cbn.
          constructor.
          intros [] _.
        }

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

        (* TODO: a little unsure of this one, but it seems plausible. *)
        Set Nested Proofs Allowed.
        Lemma fin_to_inf_uvalue_refine_strict' :
          forall d_inf d_fin,
            DVC1.uvalue_refine_strict d_inf d_fin ->
            d_inf = fin_to_inf_uvalue d_fin.
        Proof.
          intros d_inf d_fin H.
          rewrite DVC1.uvalue_refine_strict_equation in H.
          unfold fin_to_inf_uvalue.
          break_match; cbn in *.
          destruct p.
          clear Heqs.

          induction d_inf;
            try solve
              [ rewrite DVC1.uvalue_convert_strict_equation in H;
                cbn in *; inv H;
                rewrite DVC2.uvalue_convert_strict_equation in e;
                cbn in *; inv e;
                auto
              ].
          - rewrite DVC1.uvalue_convert_strict_equation in H.
            cbn in *.
            break_match_hyp; inv H.
            rewrite DVC2.uvalue_convert_strict_equation in e.
            cbn in *.
            break_match_hyp; inv e.
            rewrite DVC1.uvalue_convert_strict_equation in e0.
            cbn in *.
            break_match_hyp; inv e0.

            pose proof InfToFinAddrConvert.addr_convert_injective a a1 a0 Heqo Heqo1.
            subst.
            auto.
          - rewrite DVC1.uvalue_convert_strict_equation in H.
            cbn in *; break_match_hyp; inv H.
            rewrite DVC2.uvalue_convert_strict_equation in e.
            cbn in *; inv e.
            rewrite DVC1.uvalue_convert_strict_equation in e0.
            cbn in *; break_match_hyp; inv e0.
            admit. (* Some painful IP / BigIP reasoning *)
          - rewrite DVC1.uvalue_convert_strict_equation in H.
            cbn in *; break_match_hyp; inv H.
            rewrite DVC2.uvalue_convert_strict_equation in e.
            cbn in *; break_match_hyp; inv e.
            rewrite DVC1.uvalue_convert_strict_equation in e0.
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
             rewrite H2 in HT1.
             pinversion HT1.
           }

           { rewrite itree_eta in HT1.
             rewrite H2 in HT1.
             pinversion HT1.
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
        -- (* Vis OOM *)
          rewrite itree_eta in HT1.
          genobs t2 ot2. clear t2 Heqot2.
          punfold HT1; red in HT1; cbn in HT1.
          dependent induction HT1.
          ++ destruct e.
             econstructor.
             pstep; red; cbn.
             constructor.
             intros [] _.
          ++ specialize (EQ t0); contradiction.
        -- (* Vis *)
          { rewrite itree_eta in H1.
            genobs t2 ot2.
            clear t2 Heqot2.
            dependent induction RUN; subst.
            - (* Tau Tau *)
              specialize (EQ t2).
              contradiction.
            - (* TauL *)
              clear IHRUN.
              pclearbot.
              apply orutt_inv_Vis_r in H.
              destruct H as [[U1 [e1 [k3 [M1 [EV_REL K_RUTT]]]]] | OOM].
              2: {
                destruct OOM as [o OOM].
                inv OOM.
                repeat red in H0.
                rewrite H0 in H1.
                setoid_rewrite bind_trigger in H1.
                setoid_rewrite bind_vis in H1.
                punfold H1; red in H1; cbn in H1.
                dependent induction H1.
                - destruct o.
                  eapply Interp_Memory_PropT_Vis_OOM.
                  rewrite get_inf_tree_equation.
                  cbn.
                  unfold raiseOOM.
                  rewrite bind_trigger.
                  reflexivity.
                - specialize (EQ t1). contradiction.
              }

              punfold M1; red in M1; cbn in M1.
              genobs m1 om1.
              clear m1 Heqom1.
              dependent induction M1.
              + (* om1 = Vis *)
                rename H1 into VIS_HANDLED.

                (* Need to break apart events e / e1 to figure out
                what event we're dealing with. *)
                red in EV_REL.
                destruct e, e1; try destruct e, e0; cbn in EV_REL;
                  move EV_REL after VIS_HANDLED;
                  repeat (first [destruct s | destruct i | destruct e | destruct s0 | destruct m | destruct m0]; try contradiction); cbn in *.

                { (* ExternalCallE *)
                  destruct EV_REL as (T&F&ARGS); subst.
                  red in H0.
                  rewrite H0 in VIS_HANDLED.

                  setoid_rewrite bind_trigger in VIS_HANDLED.
                  setoid_rewrite bind_vis in VIS_HANDLED.
                  setoid_rewrite bind_ret_l in VIS_HANDLED.
                  punfold VIS_HANDLED; red in VIS_HANDLED; cbn in VIS_HANDLED.
                  dependent induction VIS_HANDLED.
                  { eapply Interp_Memory_PropT_Vis with
                      (k2:=(fun '(ms_inf, (sid', dv_inf)) =>
                              match DVCInfFin.dvalue_convert_strict dv_inf with
                              | NoOom dv_fin => get_inf_tree (k5 dv_fin)
                              | Oom s => raiseOOM s
                              end)
                      ).
                    2: {
                      cbn. red.
                      reflexivity.
                    }
                    2: {
                      cbn.
                      setoid_rewrite bind_trigger.
                      pstep; red; cbn.

                      pose proof (fin_to_inf_uvalue_refine_strict' _ _ F).
                      rewrite <- H.

                      rewrite Forall2_map_eq with (l2:=args0).
                      2: {
                        eapply Forall2_flip.
                        eapply Util.Forall2_impl; [| apply ARGS].
                        intros a b H1.
                        red.
                        symmetry.
                        apply fin_to_inf_dvalue_refine_strict'.
                        auto.
                      }

                      constructor.
                      intros v.
                      red.

                      left.
                      setoid_rewrite bind_ret_l.
                      cbn.
                      break_match_goal.
                      apply paco2_eqit_refl.
                      rewrite get_inf_tree_equation; cbn.
                      apply paco2_eqit_refl.
                    }

                    intros a (ms'&sid'&b) RET H1 H2; cbn in *; subst.
                    break_match_goal.
                    2: {
                      (* OOM *)
                      cbn.
                      left.
                      pstep; red; cbn.
                      observe_vis; solve_interp_prop_oom.
                    }

                    (* Need to figure out how k0 and k5 are related *)
                    (*
                      REL : forall v : InterpreterStackBigIntptr.LP.Events.DV.dvalue,
                          id (upaco2 (eqit_ eq true true id) bot2) (k0 v) (k3 v)

                      REL0 : forall v : dvalue,
                          id (upaco2 (eqit_ eq true true id) bot2) (k5 v) (k2 (s2, (s1, v)))

                      HK : forall (a : dvalue) (b : Memory64BitIntptr.MMEP.MMSP.MemState * (MemPropT.store_id * dvalue)),
                        Returns a (trigger (inl1 (ExternalCall t f args))) ->
                        Returns b ta ->
                        a = snd (snd b) ->
                        upaco2
                          (interp_memory_PropT_ FinMemInterp.interp_memory_prop_h
                          (fun (x : res_L2) '(_, (_, y)) => TLR_FIN.R.refine_res2 x y) true true) bot2
                          (k1 a) (k2 b)

                      K_RUTT : forall (v1 : InterpreterStackBigIntptr.LP.Events.DV.dvalue) (v2 : dvalue),
                         t = t /\
                         DVCInfFin.uvalue_refine_strict f0 f /\
                         Forall2 DVCInfFin.dvalue_refine_strict args0 args /\ DVCInfFin.dvalue_refine_strict v1 v2 ->
                         orutt L2_refine_strict L2_res_refine_strict
                         (local_refine_strict × stack_refine_strict
                         × (global_refine_strict × DVCInfFin.dvalue_refine_strict)) (k3 v1)
                         (k1 v2)


                     *)

                    pclearbot.
                    right.
                    rewrite (itree_eta_ (k0 b)).
                    rewrite (itree_eta_ (k5 d)).

                    eapply CIH;
                      repeat rewrite <- itree_eta_.

                    2: {
                      red.
                      rewrite REL0.
                      specialize (HK d (s2, (s1, d))).
                      forward HK.
                      { eapply ReturnsVis.
                        pstep; red; cbn.
                        constructor.
                        intros v. red.
                        left; apply paco2_eqit_refl.
                        constructor.
                        reflexivity.
                      }
                      forward HK.
                      { rewrite H0.
                        rewrite bind_trigger.
                        eapply ReturnsVis.
                        reflexivity.
                        cbn.
                        constructor.
                        reflexivity.
                      }
                      forward HK; cbn; auto.
                      pclearbot.
                      apply HK.
                    }

                    rewrite REL.
                    eapply K_RUTT; split; auto.
                  }
                  { specialize (EQ t1).
                    contradiction.
                  }
                }

                { (* Intrinsic *)
                  destruct EV_REL as (T&F&ARGS); subst.
                  red in H0.
                  red in H0.
                  destruct H0 as [UB | [ERR | [OOM | H0]]].
                  { (* Handler raises UB *)
                    destruct UB as [ub_msg INTRINSIC].
                    red in INTRINSIC.
                    break_match_hyp.
                    { (* memcpy *)
                      cbn in *.
                      destruct INTRINSIC as [HANDLER | [sab [[] [HANDLER []]]]].
                      red in HANDLER.
                      repeat (destruct ARGS;
                              [solve [ inversion HANDLER
                                     | red in HANDLER;
                                       repeat break_match_hyp; cbn in HANDLER; inversion HANDLER
                                 ]
                              |
                             ]).
                      repeat break_match_hyp; cbn in HANDLER; try contradiction.

                      { (* 32 bit *)
                        red in HANDLER.
                        break_match_hyp.
                        { (* Negative length UB *)
                          admit.
                        }

                        break_match_hyp.
                        2: {
                          (* Overlapping UB *)
                          admit.
                        }

                        (* No UB *)
                        (* May be UB in read / write... *)
                        cbn in HANDLER.
                        admit.
                      }

                      { (* 64 bit *)
                        admit.
                      }

                      { (* iptr *)
                        admit.
                      }
                    }

                    (* Not memcpy... *)
                    admit.
                  }

 (*                  { (* Handler raises Error *) *)
 (*                    destruct ERR as [err_msg [TA HANDLER]]. *)
 (*                    unfold raise_error in TA. *)
 (*                    cbn in TA. *)
 (*                    unfold LLVMEvents.raise in TA. *)
 (*                    rewrite bind_trigger in TA. *)

 (*                    rewrite TA in VIS_HANDLED. *)
 (*                    rewrite bind_vis in VIS_HANDLED. *)

 (*                    punfold VIS_HANDLED; red in VIS_HANDLED; cbn in VIS_HANDLED. *)
 (*                    dependent induction VIS_HANDLED. *)
 (*                    2: { *)
 (*                      specialize (EQ t1); contradiction. *)
 (*                    } *)

 (*                    eapply Interp_Memory_PropT_Vis with (ta:= *)
 (*                                                           vis (Throw err_msg) *)
 (*                                                             (fun x : void => *)
 (*                                                                match *)
 (*                                                                  x *)
 (*                                                                  return *)
 (*                                                                  (itree *)
 (*                                                                     (InterpreterStackBigIntptr.LP.Events.ExternalCallE +' *)
 (*                                                                                       LLVMParamsBigIntptr.Events.PickUvalueE +' OOME +' UBE +' DebugE +' FailureE) *)
 (*                                                                     (MemoryBigIntptr.MMEP.MMSP.MemState * *)
 (*                                                                        (MemPropT.store_id * LLVMParamsBigIntptr.Events.DV.dvalue))) *)
 (*                                                                with *)
 (*                                                                end)). *)

 (*                    3: { *)
 (*                      rewrite get_inf_tree_equation. *)
 (*                      cbn. unfold LLVMEvents.raise. *)
 (*                      rewrite bind_trigger. *)
 (*                      rewrite bind_vis. *)
 (*                      pstep; red; cbn. *)
 (*                      constructor. *)
 (*                      intros []. *)
 (*                    } *)

 (*                    { intros a (ms_b, (sid_b, b)) RET1 RET2 AB. *)
 (*                      cbn in AB; subst. *)

 (*                      pclearbot. *)
 (*                      right. *)
 (*                      rewrite (itree_eta_ (k0 _)). *)
 (*                      rewrite (itree_eta_). *)

 (*                      eapply CIH; *)
 (*                        repeat rewrite <- itree_eta_. *)

 (*                      2: { *)
 (*                        red. *)
 (*                        specialize (HK d (ms', (st1, d))). *)
 (*                        forward HK. *)
 (*                        { eapply ReturnsVis. *)
 (*                          pstep; red; cbn. *)
 (*                          constructor. *)
 (*                          intros v. red. *)
 (*                          left; apply paco2_eqit_refl. *)
 (*                          constructor. *)
 (*                          reflexivity. *)
 (*                        } *)
 (*                        forward HK. *)
 (*                        { rewrite H0. *)
 (*                          constructor. *)
 (*                          reflexivity. *)
 (*                        } *)
 (*                        forward HK; cbn; auto. *)
 (*                        pclearbot. *)
 (*                        rewrite MemState_fin_to_inf_to_fin in Heqo0; inv Heqo0. *)
 (*                        rewrite dvalue_fin_to_inf_to_fin in Heqo; inv Heqo. *)
 (*                        apply HK. *)
 (*                      } *)

 (*                      rewrite REL. *)
 (*                      eapply K_RUTT; split; auto. *)
 (*                    } *)

 (*                    eapply CIH. *)

 (*                  } *)

 (*                    2: { *)
 (*                      red. cbn. red. cbn. *)
 (*                    } *)

 (*                      with *)
 (*                      (k2:=(fun '(ms_inf, (sid', dv_inf)) => *)
 (*                              match DVCInfFin.dvalue_convert_strict dv_inf with *)
 (*                              | NoOom dv_fin => get_inf_tree (k5 dv_fin) *)
 (*                              | Oom s => raiseOOM s *)
 (*                              end) *)
 (*                      ). *)

 (*                      (k2:=tt). *)
 (* "MemoryBigIntptr.MMEP.MMSP.MemState * *)
 (*  (MemPropT.store_id * InterpreterStackBigIntptr.LP.Events.DV.dvalue) -> *)
 (*  itree *)
 (*    (InterpreterStackBigIntptr.LP.Events.ExternalCallE +' *)
 (*     LLVMParamsBigIntptr.Events.PickUvalueE +' OOME +' UBE +' DebugE +' FailureE) *)
 (*    TopLevelBigIntptr.res_L6". *)

 (*                    3: { *)
 (*                      rewrite get_inf_tree_equation. *)
 (*                      cbn. *)
 (*                      unfold LLVMEvents.raise. *)
 (*                      rewrite bind_trigger. *)
 (*                      setoid_rewrite bind_trigger. *)
 (*                    } *)
 (*                    rewrite get_inf_tree_equation. *)
 (*                    cbn. *)
 (*                    unfold LLVMEvents.raise. *)
 (*                    rewrite bind_trigger. *)
 (*                    Unset Printing Notations. *)
 (*                    Set Printing Implicit. *)
 (*                    reflexivity. *)

 (*                    admit. *)
                  (*                  } *)
                  admit.

                  { (* Handler raises OOM *)
                    destruct OOM as [oom_msg [TA HANDLER]].
                    unfold raise_oom in TA.
                    cbn in TA.
                    unfold raiseOOM in TA.
                    rewrite bind_trigger in TA.

                    rewrite TA in VIS_HANDLED.
                    rewrite bind_vis in VIS_HANDLED.

                    punfold VIS_HANDLED; red in VIS_HANDLED; cbn in VIS_HANDLED.
                    dependent induction VIS_HANDLED.
                    2: {
                      specialize (EQ t1); contradiction.
                    }

                    econstructor.
                    rewrite get_inf_tree_equation.
                    cbn.
                    unfold raiseOOM.
                    rewrite bind_trigger.
                    reflexivity.
                  }

                  (* Handler succeeds *)
                  destruct H0 as (st1&ms'&d&H0&INTRINSIC).
                  rewrite H0 in VIS_HANDLED.
                  setoid_rewrite bind_ret_l in VIS_HANDLED.

                  { eapply Interp_Memory_PropT_Vis with
                      (k2:=(fun '(ms_inf, (sid', dv_inf)) =>
                              match DVCInfFin.dvalue_convert_strict dv_inf with
                              | NoOom dv_fin =>
                                  match convert_MemState ms_inf with
                                  | NoOom ms_fin =>
                                      get_inf_tree (k2 (ms_fin, (st1, dv_fin)))
                                  | Oom s => raiseOOM s
                                  end
                              | Oom s => raiseOOM s
                              end)
                      )
                      (s1:=s1)
                      (s2:=lift_MemState s2).
                    2: {
                      cbn. red. red.
                      repeat right.
                      exists s1.
                      exists (lift_MemState ms').
                      exists (fin_to_inf_dvalue d).
                      split; try reflexivity.

                      (* TODO: inversion lemmas for dvalue_convert_strict *)
                      Lemma dvalue_convert_strict_addr_inv :
                        forall x a,
                          DVCInfFin.dvalue_convert_strict x = NoOom (DVCInfFin.DV2.DVALUE_Addr a) ->
                          exists a',
                            InfToFinAddrConvert.addr_convert a' = NoOom a /\
                              x = DVCInfFin.DV1.DVALUE_Addr a'.
                      Proof.
                        intros x a H.
                        rewrite DVCInfFin.dvalue_convert_strict_equation in H.
                        destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
                        break_match_hyp; inv H1.
                        exists a0; auto.
                      Qed.

                      Lemma dvalue_convert_strict_iptr_inv :
                        forall x n,
                          DVCInfFin.dvalue_convert_strict x = NoOom (DVCInfFin.DV2.DVALUE_IPTR n) ->
                          exists n',
                            IP.from_Z (InterpreterStackBigIntptr.LP.IP.to_Z n') = NoOom n /\
                              x = DVCInfFin.DV1.DVALUE_IPTR n'.
                      Proof.
                        intros x n H.
                        rewrite DVCInfFin.dvalue_convert_strict_equation in H.
                        destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
                        break_match_hyp; inv H1.
                        exists x; auto.
                      Qed.

                      Lemma dvalue_convert_strict_i1_inv :
                        forall x n,
                          DVCInfFin.dvalue_convert_strict x = NoOom (DVCInfFin.DV2.DVALUE_I1 n) ->
                          x = DVCInfFin.DV1.DVALUE_I1 n.
                      Proof.
                        intros x n H.
                        rewrite DVCInfFin.dvalue_convert_strict_equation in H.
                        destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
                        subst.
                        auto.
                      Qed.

                      Lemma fin_inf_no_overlap :
                        forall a1 sz1 a2 sz2 a1' a2',
                          InfToFinAddrConvert.addr_convert a1' = NoOom a1 ->
                          InfToFinAddrConvert.addr_convert a2' = NoOom a2 ->
                          Memory64BitIntptr.MMEP.MemSpec.OVER_H.no_overlap a1 sz1 a2 sz2 = MemoryBigIntptr.MMEP.MemSpec.OVER_H.no_overlap a1' sz1 a2' sz2.
                      Proof.
                      Admitted.

                      Lemma fin_inf_ptoi :
                        forall a a',
                          InfToFinAddrConvert.addr_convert a' = NoOom a ->
                          LLVMParams64BitIntptr.PTOI.ptr_to_int a = LLVMParamsBigIntptr.PTOI.ptr_to_int a'.
                      Proof.
                      Admitted.

                      Lemma fin_inf_from_Z :
                        forall ip_f z,
                          LLVMParams64BitIntptr.IP.from_Z z = NoOom ip_f ->
                          exists ip_i,
                            LLVMParamsBigIntptr.IP.from_Z z = NoOom ip_i.
                      Proof.
                      Admitted.

                      (* TODO: Move this and use it in picky intptr reasoning admits *)
                      Lemma fin_inf_from_Z_to_Z :
                        forall z x y,
                          LLVMParamsBigIntptr.IP.from_Z z = NoOom x ->
                          LLVMParams64BitIntptr.IP.from_Z z = NoOom y ->
                          LLVMParams64BitIntptr.IP.to_Z y = LLVMParamsBigIntptr.IP.to_Z x.
                      Proof.
                        intros z x y ZX ZY.
                        pose proof BigIP.from_Z_to_Z z x ZX.
                        pose proof IP.from_Z_to_Z z y ZY.
                        rewrite H, H0.
                        auto.
                      Qed.

                      Lemma fin_inf_intptr_seq :
                        forall start len ips,
                          Memory64BitIntptr.MMEP.MemSpec.MemHelpers.intptr_seq start len = NoOom ips ->
                          exists ips_big, MemoryBigIntptr.MMEP.MemSpec.MemHelpers.intptr_seq start len = NoOom ips_big /\
                                       Forall2 (fun a b => LLVMParams64BitIntptr.IP.to_Z a = LLVMParamsBigIntptr.IP.to_Z b) ips ips_big.
                      Proof.
                        intros start len ips SEQ.
                        pose proof Memory64BitIntptr.MMEP.MemSpec.MemHelpers.intptr_seq_len _ _ _ SEQ as LEN.
                        generalize dependent start.
                        generalize dependent len.
                        induction ips; intros len LEN start SEQ.
                        - cbn in *; subst.
                          exists [].
                          split.
                          + cbn; auto.
                          + constructor.
                        - cbn in *; inv LEN.
                          pose proof SEQ.
                          rewrite Memory64BitIntptr.MMEP.MemSpec.MemHelpers.intptr_seq_succ in H0.
                          cbn in H0.
                          break_match_hyp; inv H0.
                          break_match_hyp; inv H2.

                          pose proof Heqo.
                          apply fin_inf_from_Z in Heqo as [ip_i IP_I].
                          specialize (IHips (Datatypes.length ips) eq_refl (Z.succ start) Heqo0).
                          destruct IHips as [ips_big [SEQ' ALL]].
                          exists (ip_i :: ips_big).
                          split.
                          + rewrite MemoryBigIntptr.MMEP.MemSpec.MemHelpers.intptr_seq_succ.
                            cbn.
                            rewrite SEQ'.
                            cbn in IP_I.
                            inv IP_I.
                            auto.
                          + constructor; eauto.
                            eapply fin_inf_from_Z_to_Z; eauto.
                      Qed.

                      Lemma fin_inf_get_consecutive_ptrs_success :
                        forall a a' n ms ms_x xs ms_y ys,
                          (* TODO: ADDR probably not necessary, can conclude this from ADDRS...
                           *)
                          InfToFinAddrConvert.addr_convert a' = NoOom a ->
                          Forall2 (fun x y => InfToFinAddrConvert.addr_convert y = NoOom x) xs ys ->
                          (@Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs
                             (MemPropT Memory64BitIntptr.MMEP.MMSP.MemState)
                             (@MemPropT_Monad Memory64BitIntptr.MMEP.MMSP.MemState)
                             (@MemPropT_RAISE_OOM Memory64BitIntptr.MMEP.MMSP.MemState)
                             (@MemPropT_RAISE_ERROR Memory64BitIntptr.MMEP.MMSP.MemState) a n ms (success_unERR_UB_OOM (ms_x, xs))) ->
                          (@MemoryBigIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs
                             (MemPropT MemoryBigIntptr.MMEP.MMSP.MemState)
                             (@MemPropT_Monad MemoryBigIntptr.MMEP.MMSP.MemState)
                             (@MemPropT_RAISE_OOM MemoryBigIntptr.MMEP.MMSP.MemState)
                             (@MemPropT_RAISE_ERROR MemoryBigIntptr.MMEP.MMSP.MemState) a' n ms_y (success_unERR_UB_OOM (ms_y, ys))).
                      Proof.
                        intros a a' n ms ms_x xs ms_y ys A'A ADDRS CONSEC.
                        cbn in *.
                        destruct CONSEC as [sab [a0 [SEQ_OOM CONSEC]]].
                        destruct (Memory64BitIntptr.MMEP.MemSpec.MemHelpers.intptr_seq 0 n) eqn:SEQ; cbn in *; try contradiction.
                        destruct SEQ_OOM; subst.

                        destruct CONSEC as [sab [addrs CONSEC]].

                        pose proof (fin_inf_intptr_seq _ _ _ SEQ).
                        destruct H as [lb [SEQ_BIG ALL]].
                        exists ms_y. exists lb.
                        split.
                        { rewrite SEQ_BIG.
                          cbn; auto.
                        }

                        destruct CONSEC as [GEN_ADDRS SEQ_ADDRS].
                        destruct (map_monad
                                    (fun ix : LLVMParams64BitIntptr.IP.intptr =>
                                       inr
                                         (LLVMParams64BitIntptr.ITOP.int_to_ptr
                                            (LLVMParams64BitIntptr.PTOI.ptr_to_int a +
                                               Z.of_N (LLVMParams64BitIntptr.SIZEOF.sizeof_dtyp (DTYPE_I 8)) *
                                                 LLVMParams64BitIntptr.IP.to_Z ix)
                                            (LLVMParams64BitIntptr.PROV.address_provenance a))) l) eqn:HMAPM; cbn in *; try contradiction.

                        destruct GEN_ADDRS; subst.

                        destruct (@map_monad err (EitherMonad.Monad_either string) LLVMParamsBigIntptr.IP.intptr
                                    (OOM LLVMParamsBigIntptr.ADDR.addr)
                                    (fun ix : LLVMParamsBigIntptr.IP.intptr =>
                                       @inr string (OOM LLVMParamsBigIntptr.ADDR.addr)
                                         (@NoOom (Z * Prov)
                                            ((LLVMParamsBigIntptr.PTOI.ptr_to_int a' +
                                                Z.of_N (LLVMParamsBigIntptr.SIZEOF.sizeof_dtyp (DTYPE_I 8)) *
                                                  LLVMParamsBigIntptr.IP.to_Z ix)%Z, LLVMParamsBigIntptr.PROV.address_provenance a')))
                                    lb) eqn:HMAPM'.
                        { (* Should be a contradiction *)
                          apply map_monad_err_fail in HMAPM'.
                          destruct HMAPM' as [a'' [IN CONTRA]].
                          inv CONTRA.
                        }

                        exists ms_y. exists l1.
                        split.
                        {
                          red.
                          (* I have no clue why this rewrite won't work *)
                          (* rewrite HMAPM'. *)
                          break_match_goal.
                          { apply map_monad_err_fail in Heqs.
                            destruct Heqs as [a'' [IN CONTRA]].
                            inv CONTRA.
                          }
                          setoid_rewrite HMAPM' in Heqs.
                          inv Heqs.

                          cbn.
                          split; reflexivity.
                        }

                        red.
                        break_match_goal.
                        2: {
                          (* TODO: There's probably a nice lemma in here *)
                          cbn.
                          apply map_monad_OOM_fail in Heqo.
                          destruct Heqo as [x [INx OOMx]].
                          unfold id in OOMx.
                          inv OOMx.

                          apply map_monad_err_forall2 in HMAPM'.
                          apply Util.Forall2_forall in HMAPM' as [LEN HMAPM'].
                          apply In_Nth in INx. destruct INx as [i NTHl1].

                          epose proof (Nth_exists lb i) as NTHlb.
                          forward NTHlb.
                          { apply Nth_ix_lt_length in NTHl1.
                            lia.
                          }
                          destruct NTHlb as (?&NTHlb).
                          specialize (HMAPM' _ _ _ NTHlb NTHl1).
                          inv HMAPM'.
                        }

                        cbn.

                        split; auto.

                        { (* Might follow from ADDRS? *)
                          red in SEQ_ADDRS.
                          break_match_hyp; cbn in *; try contradiction.
                          inv SEQ_ADDRS.
                          rename l3 into xs.
                          rename l0 into oxs.
                          rename l into ixs.
                          rename lb into ixs_big.
                          rename l1 into oys.
                          rename l2 into ys'.

                          (* Each y in ys should match up with a y in ys'... I.e.,

                                     forall i y y', Util.Nth ys i y -> Util.Nth ys' i y' -> y = y'

                                     Why?

                                     HMAPM' / Heqo should yield: y' = a' + i
                                     ADDRS should suggest that y = xs[i]
                                     HMAPM / Heqo0 yields xs[i] = a + i

                           *)

                          assert (forall i y y', Util.Nth ys i y -> Util.Nth ys' i y' -> y = y') as NTHysys'.
                          {
                            intros i y y' H H0.

                            (* Figure out what y' is *)
                            pose proof (map_monad_OOM_Nth _ _ _ y' i Heqo H0) as [y'' [Y NTHoys]].
                            unfold id in Y. cbn in Y. inv Y. clear H1.
                            pose proof (map_monad_err_Nth _ _ _ _ i HMAPM' NTHoys) as [y'' [Y NTHixs_big]].
                            inv Y.

                            (* Figure out what y is *)
                            pose proof (Util.Forall2_Nth_right H ADDRS) as [x [NTHxs CONVxy]].
                            pose proof (map_monad_OOM_Nth _ _ _ x i Heqo0 NTHxs) as [x'' [X NTHoxs]].
                            unfold id in X. cbn in X. inv X. clear H1.
                            pose proof (map_monad_err_Nth _ _ _ _ i HMAPM NTHoxs) as [x'' [X NTHixs]].
                            inv X.

                            eapply InfToFinAddrConvert.addr_convert_injective; eauto.
                            unfold InfToFinAddrConvert.addr_convert.

                            assert (LLVMParams64BitIntptr.IP.to_Z x'' = LLVMParamsBigIntptr.IP.to_Z y'') as X''Y''.
                            {
                              eapply fin_inf_from_Z_to_Z.
                              - apply (MemoryBigIntptr.MMEP.MemSpec.MemHelpers.intptr_seq_nth 0 n _ i y'' SEQ_BIG NTHixs_big).
                              - apply (Memory64BitIntptr.MMEP.MemSpec.MemHelpers.intptr_seq_nth 0 n _ i x'' SEQ NTHixs).
                            }
                            rewrite <- X''Y''.

                            rewrite LLVMParamsBigIntptr.SIZEOF.sizeof_dtyp_i8.
                            rewrite LLVMParams64BitIntptr.SIZEOF.sizeof_dtyp_i8 in H2.

                            pose proof ADDRS.
                            inversion H1; subst.
                            { apply Util.not_Nth_nil in NTHxs.
                              contradiction.
                            }

                            rename l into xs.
                            rename l' into ys.

                            (* x0 and y0 should correspond to a and a' *)
                            assert (x0 = a).
                            {
                              eapply map_monad_OOM_Nth with (n:=0%nat) in Heqo0; cbn; eauto.
                              destruct Heqo0 as (x0'&X0&NTHx0).
                              unfold id in X0. subst.
                              eapply map_monad_err_Nth with (n:=0%nat) in HMAPM; cbn; eauto.
                              destruct HMAPM as (x0''&X0&NTHx0').
                              cbn in *.
                              inv X0.

                              destruct ixs; inv NTHx0'.
                              destruct n; inv SEQ.
                              cbn in *.
                              rewrite IP64Bit.from_Z_0 in H7.
                              break_match_hyp; inv H7.
                              rewrite IP64Bit.to_Z_0 in H6.
                              replace (LLVMParams64BitIntptr.PTOI.ptr_to_int a +
                                         Z.of_N (LLVMParams64BitIntptr.SIZEOF.sizeof_dtyp (DTYPE_I 8)) * 0)%Z with (LLVMParams64BitIntptr.PTOI.ptr_to_int a) in H6 by lia.

                              pose proof LLVMParams64BitIntptr.ITOP.int_to_ptr_ptr_to_int a (LLVMParams64BitIntptr.PROV.address_provenance a) eq_refl.
                              rewrite H6 in H5.
                              inv H5.
                              reflexivity.
                            }
                            subst.

                            assert (y0 = a').
                            { eapply InfToFinAddrConvert.addr_convert_injective.
                              eapply H3.
                              eauto.
                            }
                            subst.

                            rewrite <- H2.
                            destruct a' as (ptr', pr').
                            erewrite fin_inf_ptoi; eauto.
                            erewrite FinLP.ITOP.int_to_ptr_provenance; eauto.
                          }

                          eapply Nth_eq; eauto.
                          (* Length:

                                     ys = xs = oxs = ixs = n
                                     ys' = oys = ixs_big = n
                           *)

                          apply Util.Forall2_length in ADDRS, ALL.
                          apply map_monad_err_length in HMAPM, HMAPM'.
                          apply map_monad_oom_length in Heqo, Heqo0.
                          congruence.
                        }
                      Qed.

                      Lemma fin_inf_get_consecutive_ptrs_success_exists :
                        forall a_fin a_inf n ms_fin ms_fin' addrs_fin ms_inf,
                          (* TODO: ADDR probably not necessary, can conclude this from ADDRS...
                           *)
                          InfToFinAddrConvert.addr_convert a_inf = NoOom a_fin ->
                          (@Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs
                             (MemPropT Memory64BitIntptr.MMEP.MMSP.MemState)
                             (@MemPropT_Monad Memory64BitIntptr.MMEP.MMSP.MemState)
                             (@MemPropT_RAISE_OOM Memory64BitIntptr.MMEP.MMSP.MemState)
                             (@MemPropT_RAISE_ERROR Memory64BitIntptr.MMEP.MMSP.MemState) a_fin n ms_fin (success_unERR_UB_OOM (ms_fin', addrs_fin))) ->
                          exists addrs_inf,
                            (@MemoryBigIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs
                               (MemPropT MemoryBigIntptr.MMEP.MMSP.MemState)
                               (@MemPropT_Monad MemoryBigIntptr.MMEP.MMSP.MemState)
                               (@MemPropT_RAISE_OOM MemoryBigIntptr.MMEP.MMSP.MemState)
                               (@MemPropT_RAISE_ERROR MemoryBigIntptr.MMEP.MMSP.MemState) a_inf n ms_inf (success_unERR_UB_OOM (ms_inf, addrs_inf))) /\
                              Forall2 (fun x y => InfToFinAddrConvert.addr_convert y = NoOom x) addrs_fin addrs_inf.
                      Proof.
                        intros a_fin a_inf n ms_fin ms_fin' addrs_fin ms_inf ADDR_CONV GCP.
                        pose proof fin_inf_get_consecutive_ptrs_success a_fin a_inf n ms_fin ms_fin' addrs_fin ms_inf.
                        pose proof MemoryBigIntptrInfiniteSpec.MSIH.big_intptr_seq_succeeds 0 n as (ips & SEQ_INF).
                        pose proof
                          map_monad_err_succeeds
                          (fun ix : LLVMParamsBigIntptr.IP.intptr =>
                             @inr string (OOM LLVMParamsBigIntptr.ADDR.addr)
                               (@NoOom (Z * Prov)
                                  ((LLVMParamsBigIntptr.PTOI.ptr_to_int a_inf +
                                      Z.of_N (LLVMParamsBigIntptr.SIZEOF.sizeof_dtyp (DTYPE_I 8)) *
                                        LLVMParamsBigIntptr.IP.to_Z ix)%Z, LLVMParamsBigIntptr.PROV.address_provenance a_inf)))
                          ips as ADDRS_INF.
                        forward ADDRS_INF.
                        { intros a IN.
                          eexists; reflexivity.
                        }

                        destruct ADDRS_INF as [oaddrs_inf ADDRS_INF].

                        pose proof
                          map_monad_oom_succeeds id oaddrs_inf as SEQ.
                        forward SEQ.
                        {
                          intros a IN.
                          epose proof map_monad_err_In _ _ _ _ ADDRS_INF IN as (y&A&INy).
                          inv A.
                          eexists.
                          unfold id.
                          reflexivity.
                        }
                        destruct SEQ as (RES&MAP_INF).

                        cbn.
                        eexists.
                        split.
                        { eexists.
                          eexists.
                          split.
                          - red.
                            rewrite SEQ_INF.
                            cbn.
                            split; auto.
                          - eexists. eexists.
                            split.
                            + red.
                              (* TODO: Why can't I rewrite with ADDRS_INF? *)
                              break_match_goal;
                                setoid_rewrite ADDRS_INF in Heqs;
                                inv Heqs.
                              cbn.
                              split; auto.
                            + red.
                              unfold Monads.sequence.
                              rewrite MAP_INF.
                              cbn.
                              split; reflexivity.
                        }

                        apply Util.Forall2_forall.
                        split.
                        - apply map_monad_oom_length in MAP_INF.
                          apply map_monad_err_length in ADDRS_INF.

                          (* Need something about get_consecutive_ptrs_length...

                             There is one: FinLLVM.MEM.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs_length.

                             Need to refresh memory on Within, though.
                           *)

                          assert (n = Datatypes.length addrs_fin) as ADDRS_FIN_LEN.
                          {
                            assert (exists (pre : Memory64BitIntptr.MMEP.MMSP.MemState) (post : Memory64BitIntptr.MMEP.MMSP.MemState),
                                       Within.within (FinLLVM.MEM.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs a_fin n) pre
                                         (ret addrs_fin) post).
                            {
                              exists FinMemMMSP.initial_memory_state. exists FinMemMMSP.initial_memory_state.
                              cbn.
                              exists FinMemMMSP.initial_memory_state.

                              red in GCP.
                              destruct (Memory64BitIntptr.MMEP.MemSpec.MemHelpers.intptr_seq 0 n) eqn:SEQ_FIN; cbn in GCP.
                              2: { destruct GCP as [sab [a [[] _]]]. }

                              destruct GCP as [sab [a [[MS A] GCP]]]; subst.
                              destruct GCP as [sab [a [GCP SEQ]]]; subst.
                              destruct (map_monad
                                          (fun ix : LLVMParams64BitIntptr.IP.intptr =>
                                             inr
                                               (LLVMParams64BitIntptr.ITOP.int_to_ptr
                                                  (LLVMParams64BitIntptr.PTOI.ptr_to_int a_fin +
                                                     Z.of_N (LLVMParams64BitIntptr.SIZEOF.sizeof_dtyp (DTYPE_I 8)) *
                                                       LLVMParams64BitIntptr.IP.to_Z ix)
                                                  (LLVMParams64BitIntptr.PROV.address_provenance a_fin))) l) eqn:HMAPM; cbn in GCP; try contradiction.
                              destruct GCP; subst.
                              red in SEQ.
                              break_match_hyp; inv SEQ.

                              eexists; split; cbn; eauto.
                              exists FinMemMMSP.initial_memory_state.
                              eexists; split; cbn; eauto.
                              rewrite HMAPM.
                              cbn; eauto.
                              rewrite Heqo. cbn. auto.
                            }

                            pose proof FinLLVM.MEM.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs_length _ _ _ H0; eauto.
                          }

                          apply MemoryBigIntptr.MMEP.MemSpec.MemHelpers.intptr_seq_len in SEQ_INF.
                          congruence.
                        - intros i a b NTHaddrs NTHres.
                          pose proof (map_monad_OOM_Nth _ _ _ _ _ MAP_INF NTHres) as (y&Y&NTHoaddrs).
                          unfold id in Y; subst.

                          pose proof (map_monad_err_Nth _ _ _ _ _ ADDRS_INF NTHoaddrs) as (y&Y&NTHips).
                          cbn in Y. inv Y.

                          rename a into ptr_fin.

                          (* Need to break apart GCP to find out about ptr_fin *)
                          pose proof Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs_nth_eq1 a_fin n addrs_fin.
                          forward H0.
                          {
                            red. red.
                            intros ms x.
                            split.
                            - intros GCP'.
                              cbn.
                              destruct_err_ub_oom x.
                              + (* Contradiction *)
                                cbn in GCP'.
                                clear H0.
                                cbn in GCP.
                                move GCP after GCP'.
                                destruct GCP as [ms' [a [SEQ GCP]]].
                                red in SEQ.
                                break_match_hyp; inv SEQ.

                                destruct GCP'.
                                cbn in H0; auto.

                                destruct H0 as [sab [a [[MS LA] GCP']]].
                                subst.

                                destruct GCP as [ms' [a [GCP SEQ_FIN]]].
                                red in GCP.
                                break_match_hyp; inv GCP.
                                rename Heqs into GCP.

                                red in SEQ_FIN.
                                break_match_hyp; inv SEQ_FIN.

                                destruct GCP' as [GCP' | GCP'];
                                  cbn in *; auto.

                                destruct GCP' as [sab [a [[MS LA] SEQ]]].
                                subst.

                                rewrite Heqo0 in SEQ.
                                cbn in SEQ.
                                auto.
                              + (* Contradiction *)
                                cbn in GCP'.
                                clear H0.
                                cbn in GCP.
                                move GCP after GCP'.
                                destruct GCP as [ms' [a [SEQ GCP]]].
                                red in SEQ.
                                break_match_hyp; inv SEQ.

                                destruct GCP'.
                                cbn in H0; auto.

                                destruct H0 as [sab [a [[MS LA] GCP']]].
                                subst.

                                destruct GCP as [ms' [a [GCP SEQ_FIN]]].
                                red in GCP.
                                break_match_hyp; inv GCP.
                                rename Heqs into GCP.

                                red in SEQ_FIN.
                                break_match_hyp; inv SEQ_FIN.

                                destruct GCP' as [GCP' | GCP'];
                                  cbn in *; auto.

                                destruct GCP' as [sab [a [[MS LA] SEQ]]].
                                subst.

                                rewrite Heqo0 in SEQ.
                                cbn in SEQ.
                                auto.
                              + (* Contradiction *)
cbn in GCP'.
                                clear H0.
                                cbn in GCP.
                                move GCP after GCP'.
                                destruct GCP as [ms' [a [SEQ GCP]]].
                                red in SEQ.
                                break_match_hyp; inv SEQ.

                                destruct GCP'.
                                cbn in H0; auto.

                                destruct H0 as [sab [a [[MS LA] GCP']]].
                                subst.

                                destruct GCP as [ms' [a [GCP SEQ_FIN]]].
                                red in GCP.
                                break_match_hyp; inv GCP.
                                rename Heqs into GCP.

                                red in SEQ_FIN.
                                break_match_hyp; inv SEQ_FIN.

                                destruct GCP' as [GCP' | GCP'];
                                  cbn in *; auto.

                                destruct GCP' as [sab [a [[MS LA] SEQ]]].
                                subst.

                                rewrite Heqo0 in SEQ.
                                cbn in SEQ.
                                auto.
                              + destruct x0.
                                inv Hx.
                                (* Should be able to conclude this with a mix of GCP' and GCP *)
                                cbn in *.
                                destruct GCP' as [ms' [a [SEQ_FIN GCP']]].
                                red in SEQ_FIN.
                                break_match_hyp; inv SEQ_FIN.
                                destruct GCP' as [sab [a [GCP' SEQ_FIN]]].

                                red in SEQ_FIN.
                                break_match_hyp; inv SEQ_FIN.

                                red in GCP'.
                                break_match_hyp; inv GCP'.
                                split; auto.

                                destruct GCP as [ms' [a [[MS L] GCP]]].
                                subst.
                                destruct GCP as [ms' [a [GCP SEQ]]].
                                red in GCP.
                                break_match_hyp; inv GCP.
                                red in SEQ.
                                break_match_hyp; inv SEQ.

                                clear H0 H.
                                inv Heqs.
                                rewrite Heqo1 in Heqo0.
                                inv Heqo0.
                                reflexivity.
                            - intros RET.
                              cbn in RET.
                              destruct_err_ub_oom x; try inv RET.
                              destruct x0.
                              destruct RET; subst.

                              red in GCP.
                              destruct (Memory64BitIntptr.MMEP.MemSpec.MemHelpers.intptr_seq 0 n) eqn:SEQ_FIN; cbn in GCP.
                              2: { destruct GCP as [sab [a [[] _]]]. }.
                              destruct GCP as [sab [a [[MS A] GCP]]]; subst.
                              destruct GCP as [sab [a [GCP SEQ]]]; subst.
                              destruct (map_monad
                                          (fun ix : LLVMParams64BitIntptr.IP.intptr =>
                                             inr
                                               (LLVMParams64BitIntptr.ITOP.int_to_ptr
                                                  (LLVMParams64BitIntptr.PTOI.ptr_to_int a_fin +
                                                     Z.of_N (LLVMParams64BitIntptr.SIZEOF.sizeof_dtyp (DTYPE_I 8)) *
                                                       LLVMParams64BitIntptr.IP.to_Z ix)
                                                  (LLVMParams64BitIntptr.PROV.address_provenance a_fin))) l) eqn:HMAPM; cbn in GCP; try contradiction.
                              destruct GCP; subst.
                              red in SEQ.
                              break_match_hyp; inv SEQ.

                              cbn.
                              exists ms. exists l.
                              split.
                              rewrite SEQ_FIN; cbn; auto.

                              exists ms. exists l0.
                              rewrite HMAPM. cbn.
                              split; auto.
                              rewrite Heqo; cbn; auto.
                          }

                          specialize (H0 _ _ NTHaddrs).
                          destruct H0 as [ip [IP GEP]].
                          pose proof GEP as GEP'.
                          apply FinLLVM.MEM.MP.GEP.handle_gep_addr_ix in GEP.

                          assert (LLVMParamsBigIntptr.IP.to_Z y = Z.of_nat i) as IPI.
                          { pose proof MemoryBigIntptr.MMEP.MemSpec.MemHelpers.intptr_seq_nth _ _ _ _ _ SEQ_INF NTHips.
                            replace (0 + (Z.of_nat i))%Z with (Z.of_nat i) in H0 by lia.
                            eapply FiniteIntptr.BigIP.from_Z_to_Z.
                            apply H0.
                          }
                          rewrite IPI.

                          symmetry in IP.
                          eapply FinLP.IP.from_Z_to_Z in IP.
                          rewrite IP in GEP.

                          replace (LLVMParamsBigIntptr.PTOI.ptr_to_int a_inf +
                                     Z.of_N (LLVMParamsBigIntptr.SIZEOF.sizeof_dtyp (DTYPE_I 8)) * Z.of_nat i)%Z with (PTOI.ptr_to_int ptr_fin).
                          2: {
                            rewrite GEP.
                            erewrite fin_inf_ptoi; eauto.
                          }

                          pose proof GEP' as GEP''.
                          apply Memory64BitIntptr.GEP.handle_gep_addr_preserves_provenance in GEP'.

                          Lemma inf_fin_addr_convert_provenance :
                            forall a_inf a_fin,
                              InfToFinAddrConvert.addr_convert a_inf = NoOom a_fin ->
                              LLVMParamsBigIntptr.PROV.address_provenance a_inf = LLVMParams64BitIntptr.PROV.address_provenance a_fin.
                          Proof.
                            intros a_inf a_fin ADDR_CONV.
                            destruct a_inf, a_fin.
                            cbn in *.
                            apply ITOP.int_to_ptr_provenance in ADDR_CONV.
                            cbn in *.
                            auto.
                          Qed.

                          erewrite inf_fin_addr_convert_provenance; eauto.
                          rewrite GEP'.

                          cbn.
                          apply ITOP.int_to_ptr_ptr_to_int.
                          reflexivity.
                      Qed.

                      (* TODO: Some tricky IntMap reasoning *)
                      Lemma fin_inf_read_byte_raw :
                        forall m_inf m_fin ptr b_fin aid,
                          convert_memory m_inf = NoOom m_fin ->
                          Memory64BitIntptr.MMEP.MMSP.read_byte_raw
                            m_fin
                            ptr = Some (b_fin, aid) ->
                            MemoryBigIntptr.MMEP.MMSP.read_byte_raw
                              m_inf
                              ptr = Some (lift_SByte b_fin, aid).
                      Proof.
                        intros m_inf m_fin ptr b_fin aid CONV READ.
                        Transparent Memory64BitIntptr.MMEP.MMSP.read_byte_raw.
                        Transparent MemoryBigIntptr.MMEP.MMSP.read_byte_raw.
                        unfold Memory64BitIntptr.MMEP.MMSP.read_byte_raw in READ.
                        unfold MemoryBigIntptr.MMEP.MMSP.read_byte_raw.
                        Opaque Memory64BitIntptr.MMEP.MMSP.read_byte_raw.
                        Opaque MemoryBigIntptr.MMEP.MMSP.read_byte_raw.

                        cbn in CONV.
                        break_match_hyp; inv CONV.
                        rename Heqo into CONV.
                        rename l into m_fin_elems.

                        (* I should be able to use CONV.

                           We know that m_fin_elems is derived from
                           the elements of m_inf... So when I look up
                           an element in (IntMaps.IP.of_list m_fin_elems),
                           like in READ, we should get a byte from a
                           convert_mem_byte call on the same byte in
                           m_inf.
                         *)

                        Lemma IntMap_find_NoOom_elements :
                          forall {X Y} (m : IntMaps.IM.t X) (f : (IntMaps.IM.key * X) -> OOM (IntMaps.IM.key * Y)) m_elts (n : Z) (y : Y),
                            map_monad f (IntMaps.IM.elements (elt:=X) m) = NoOom m_elts ->
                            (forall '(ix, x) ix', f (ix, x) = NoOom (ix', y) -> ix = ix') ->
                            IntMaps.IM.find (elt:=Y) n (IntMaps.IP.of_list m_elts) = Some y ->
                            exists x, IntMaps.IM.find (elt:=X) n m = Some x /\ NoOom (n, y) = f (n, x).
                        Proof.
                          intros X Y m f m_elts n y HMAPM F FIND.
                        Admitted.

                        epose proof IntMap_find_NoOom_elements _ _ _ ptr _ CONV.
                        forward H.
                        {
                          intros pat. destruct pat.
                          intros ix' H0.
                          break_match_hyp; inv H0.
                          auto.
                        }
                        forward H.
                        {
                          exact READ.
                        }

                        destruct H as [[b_inf aid'] [FIND BYTE_INF]].
                        cbn in *.
                        break_match_hyp; inv BYTE_INF.
                        break_match_hyp; inv Heqo.

                        unfold lift_SByte.
                        destruct b_inf. cbn in Heqo0.
                        break_match_hyp; inv Heqo0.
                        break_match_hyp; inv H0.
                        rewrite FIND.

                        erewrite <- fin_to_inf_uvalue_refine_strict'; eauto.
                        erewrite <- fin_to_inf_uvalue_refine_strict'; eauto.

                        rewrite DVC1.uvalue_refine_strict_equation.
                        auto.
                      Qed.

                      (* TODO: Some tricky IntMap reasoning *)
                      Lemma fin_inf_read_byte_raw_None :
                        forall m_inf m_fin ptr,
                          convert_memory m_inf = NoOom m_fin ->
                          Memory64BitIntptr.MMEP.MMSP.read_byte_raw
                            m_fin
                            ptr = None ->
                          MemoryBigIntptr.MMEP.MMSP.read_byte_raw
                            m_inf
                            ptr = None.
                      Proof.
                        intros m_inf m_fin ptr CONV READ.
                        Transparent Memory64BitIntptr.MMEP.MMSP.read_byte_raw.
                        Transparent MemoryBigIntptr.MMEP.MMSP.read_byte_raw.
                        unfold Memory64BitIntptr.MMEP.MMSP.read_byte_raw in READ.
                        unfold MemoryBigIntptr.MMEP.MMSP.read_byte_raw.

                        cbn in CONV.
                        break_match_hyp; inv CONV.

                        Opaque Memory64BitIntptr.MMEP.MMSP.read_byte_raw.
                        Opaque MemoryBigIntptr.MMEP.MMSP.read_byte_raw.
                      Admitted.

                      (* TODO: Maybe swap MemState for memory_stack to get rid of MemState_get_memory *)
                      Lemma fin_inf_addr_allocated_prop :
                        forall addr_fin addr_inf ms_fin ms_inf aid,
                          convert_memory_stack ms_inf = NoOom ms_fin ->
                          InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
                          Memory64BitIntptr.MMEP.MMSP.addr_allocated_prop addr_fin aid
                            ms_fin
                            (success_unERR_UB_OOM (ms_fin, true)) ->
                          MemoryBigIntptr.MMEP.MMSP.addr_allocated_prop addr_inf aid
                            ms_inf
                            (success_unERR_UB_OOM (ms_inf, true)).
                      Proof.
                        intros addr_fin addr_inf ms_fin ms_inf aid MSR ADDR_CONV ALLOCATED.
                        cbn in *.
                        destruct ALLOCATED as [mst_fin [mst_fin' [[MST MST'] ALLOCATED]]]; subst.
                        exists ms_inf.
                        exists ms_inf.
                        split; auto.
                        break_match_hyp; cbn in *.
                        2: {
                          destruct ALLOCATED.
                          discriminate.
                        }

                        destruct m.
                        destruct ms_inf, mst_fin.
                        Opaque convert_memory.
                        cbn in *.
                        break_match_hyp; inv MSR.
                        break_match_hyp; inv H0.
                        break_match_hyp; inv H1.
                        break_match_hyp; inv Heqo2.

                        eapply fin_inf_read_byte_raw in Heqo; eauto.
                        erewrite fin_inf_ptoi in Heqo; eauto.
                        rewrite Heqo.

                        destruct ALLOCATED.
                        split; auto.

                        destruct (LLVMParams64BitIntptr.PROV.aid_eq_dec aid a); cbn in *; try discriminate; subst.
                        destruct (LLVMParamsBigIntptr.PROV.aid_eq_dec a a); cbn in *; try contradiction; auto.
                      Qed.

                      Lemma MemState_refine_convert_memory_stack :
                        forall ms_inf ms_fin,
                          MemState_refine ms_inf ms_fin ->
                          convert_memory_stack (MemoryBigIntptr.MMEP.MMSP.MemState_get_memory ms_inf) = NoOom (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory ms_fin).
                      Proof.
                        intros ms_inf ms_fin REF.
                        destruct ms_inf; cbn in *.
                        unfold MemState_refine in REF.
                        cbn in *.
                        break_match_hyp; inv REF.
                        cbn.
                        reflexivity.
                      Qed.

                      Lemma MemState_refine_convert_memory :
                        forall ms_inf ms_fin,
                          MemState_refine ms_inf ms_fin ->
                          convert_memory (MemoryBigIntptr.MMEP.MMSP.mem_state_memory ms_inf) = NoOom (Memory64BitIntptr.MMEP.MMSP.mem_state_memory ms_fin).
                      Proof.
                        intros ms_inf ms_fin REF.
                        destruct ms_inf; cbn in *.
                        unfold MemState_refine in REF.
                        cbn in *.
                        break_match_hyp; inv REF.
                        destruct ms_memory_stack; cbn in *.
                        destruct memory_stack_memory; cbn in *.
                        break_match_hyp; inv Heqo.
                        break_match_hyp; inv H0.
                        break_match_hyp; inv H1.
                        break_match_hyp; inv Heqo1.
                        cbn in *.
                        reflexivity.
                      Qed.

                      Lemma MemState_refine_convert_memory' :
                        forall ms_inf ms_fin,
                          MemState_refine ms_inf ms_fin ->
                          convert_memory (MemoryBigIntptr.MMEP.MMSP.memory_stack_memory
                                            (MemoryBigIntptr.MMEP.MMSP.MemState_get_memory ms_inf)) = NoOom (Memory64BitIntptr.MMEP.MMSP.memory_stack_memory
                                                                                                               (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory ms_fin)).
                      Proof.
                        intros ms_inf ms_fin REF.
                        destruct ms_inf; cbn in *.
                        unfold MemState_refine in REF.
                        cbn in *.
                        break_match_hyp; inv REF.
                        destruct ms_memory_stack; cbn in *.
                        destruct memory_stack_memory; cbn in *.
                        break_match_hyp; inv Heqo.
                        break_match_hyp; inv H0.
                        break_match_hyp; inv H1.
                        break_match_hyp; inv Heqo1.
                        cbn in *.
                        reflexivity.
                      Qed.

                      Lemma fin_inf_byte_allocated_MemPropT :
                        forall addr_fin addr_inf ms_fin ms_inf aid,
                          MemState_refine ms_inf ms_fin ->
                          InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
                          Memory64BitIntptr.MMEP.MemSpec.byte_allocated_MemPropT addr_fin aid ms_fin (ret (ms_fin, tt)) ->
                          MemoryBigIntptr.MMEP.MemSpec.byte_allocated_MemPropT addr_inf aid ms_inf (ret (ms_inf, tt)).
                      Proof.
                        intros addr_fin addr_inf ms_fin ms_inf aid MSR ADDR_CONV ALLOCATED.
                        red; red in ALLOCATED.
                        Opaque Memory64BitIntptr.MMEP.MMSP.addr_allocated_prop.
                        Opaque MemoryBigIntptr.MMEP.MMSP.addr_allocated_prop.
                        cbn in *.
                        destruct ALLOCATED as [ms_fin' [res [ALLOCATED [MS RES]]]]; subst.
                        exists ms_inf. exists true.
                        split; auto.
                        red.
                        destruct ALLOCATED.
                        split.
                        - eapply fin_inf_addr_allocated_prop; eauto.
                          + eapply MemState_refine_convert_memory_stack; eauto.
                          + destruct ms_fin. cbn in *.
                            eauto.
                        - intros ms' x H1.
                          cbn in *.
                          inv H1.
                          auto.
                      Qed.

                      Lemma fin_inf_byte_allocated :
                        forall addr_fin addr_inf ms_fin ms_inf aid,
                          MemState_refine ms_inf ms_fin ->
                          InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
                          Memory64BitIntptr.MMEP.MemSpec.byte_allocated ms_fin addr_fin aid ->
                          MemoryBigIntptr.MMEP.MemSpec.byte_allocated ms_inf addr_inf aid.
                      Proof.
                        intros addr_fin addr_inf ms_fin ms_inf aid MSR ADDR_CONV ALLOCATED.
                        red; red in ALLOCATED.
                        eapply fin_inf_byte_allocated_MemPropT; eauto.
                      Qed.

                      Lemma fin_inf_access_allowed :
                        forall addr_fin addr_inf aid res,
                          InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
                          LLVMParams64BitIntptr.PROV.access_allowed
                            (LLVMParams64BitIntptr.PROV.address_provenance addr_fin) aid = res ->
                          LLVMParamsBigIntptr.PROV.access_allowed (LLVMParamsBigIntptr.PROV.address_provenance addr_inf) aid = res.
                      Proof.
                        intros addr_fin addr_inf aid res ADDR_CONV ACCESS.
                        destruct addr_inf.
                        cbn in *.
                        pose proof ITOP.int_to_ptr_provenance _ _ _ ADDR_CONV. subst.
                        unfold LLVMParams64BitIntptr.PROV.access_allowed in *.
                        unfold LLVMParamsBigIntptr.PROV.access_allowed in *.

                        (* TODO: Need to expose access_allowed *)
                        admit.
                      Admitted.

                      Lemma fin_inf_read_byte_allowed :
                        forall addr_fin addr_inf ms_fin ms_inf,
                          MemState_refine ms_inf ms_fin ->
                          InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
                          Memory64BitIntptr.MMEP.MemSpec.read_byte_allowed ms_fin addr_fin ->
                          MemoryBigIntptr.MMEP.MemSpec.read_byte_allowed ms_inf addr_inf.
                      Proof.
                        intros addr_fin addr_inf ms_fin ms_inf MSR ADDR_CONV READ_ALLOWED.
                        red. red in READ_ALLOWED.

                        destruct READ_ALLOWED as [aid [BYTE_ALLOCATED ACCESS_ALLOWED]].
                        exists aid.
                        split.
                        - eapply fin_inf_byte_allocated; eauto.
                        - eapply fin_inf_access_allowed; eauto.
                      Qed.

                      Lemma fin_inf_read_byte_prop_MemPropT :
                        forall addr_fin addr_inf ms_fin ms_inf byte_fin,
                          MemState_refine ms_inf ms_fin ->
                          InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
                          Memory64BitIntptr.MMEP.MMSP.read_byte_MemPropT addr_fin
                            (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory ms_fin)
                            (ret (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory ms_fin, byte_fin)) ->
                          MemoryBigIntptr.MMEP.MMSP.read_byte_MemPropT addr_inf
                            (MemoryBigIntptr.MMEP.MMSP.MemState_get_memory ms_inf)
                            (ret (MemoryBigIntptr.MMEP.MMSP.MemState_get_memory ms_inf, lift_SByte byte_fin)).
                      Proof.
                        intros addr_fin addr_inf ms_fin ms_inf byte_fin MSR ADDR_CONV RBP.
                        (* TODO: make things opaque? *)
                        destruct RBP as [ms_fin' [ms_fin'' [[MS MS'] READ]]].
                        subst.
                        destruct ms_fin eqn:MSFIN. cbn in READ.
                        destruct ms_inf eqn:MSINF.
                        break_match_hyp.
                        (* read_byte_MemPropT may have UB... Which
                           means sbyte_refine byte_inf byte_fin might not
                           hold because byte_fin could be any byte.
                         *)
                        - destruct m.
                          epose proof fin_inf_read_byte_raw (MemoryBigIntptr.MMEP.MMSP.memory_stack_memory ms_memory_stack0) _ _ _ _ _ Heqo.

                          cbn.
                          eexists. eexists.
                          split; eauto.
                          erewrite fin_inf_ptoi in H; eauto.
                          rewrite H.
                          erewrite fin_inf_access_allowed; cbn; eauto.
                          break_match_goal; cbn; eauto.

                          break_match_hyp.
                          destruct READ; subst; auto.

                          cbn in Heqb0.
                          rewrite Heqb0 in Heqb.
                          discriminate.
                        - epose proof fin_inf_read_byte_raw_None _ _ _ _ Heqo.
                          cbn.
                          eexists. eexists.
                          split; eauto.
                          erewrite fin_inf_ptoi in H; eauto.
                          rewrite H.
                          auto.

                          Unshelve.
                          all: clear READ.
                          + replace (Memory64BitIntptr.MMEP.MMSP.memory_stack_memory ms_memory_stack) with (Memory64BitIntptr.MMEP.MMSP.memory_stack_memory
       (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory ms_fin)).
                            replace (MemoryBigIntptr.MMEP.MMSP.memory_stack_memory ms_memory_stack0) with (MemoryBigIntptr.MMEP.MMSP.memory_stack_memory
                                                                                                              (MemoryBigIntptr.MMEP.MMSP.MemState_get_memory ms_inf)).
                            eapply MemState_refine_convert_memory'; subst; eauto.
                            subst; cbn. auto.
                            subst; cbn. auto.
                          + replace (Memory64BitIntptr.MMEP.MMSP.memory_stack_memory ms_memory_stack) with (Memory64BitIntptr.MMEP.MMSP.memory_stack_memory
       (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory ms_fin)).
                            replace (MemoryBigIntptr.MMEP.MMSP.memory_stack_memory ms_memory_stack0) with (MemoryBigIntptr.MMEP.MMSP.memory_stack_memory
                                                                                                              (MemoryBigIntptr.MMEP.MMSP.MemState_get_memory ms_inf)).
                            eapply MemState_refine_convert_memory'; subst; eauto.
                            subst; cbn. auto.
                            subst; cbn. auto.
                      Qed.

                      Lemma fin_inf_read_byte_prop :
                        forall addr_fin addr_inf ms_fin ms_inf byte_fin,
                          MemState_refine ms_inf ms_fin ->
                          InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
                          Memory64BitIntptr.MMEP.MemSpec.read_byte_prop ms_fin addr_fin byte_fin ->
                          MemoryBigIntptr.MMEP.MemSpec.read_byte_prop ms_inf addr_inf (lift_SByte byte_fin).
                      Proof.
                        intros addr_fin addr_inf ms_fin ms_inf byte_fin MSR ADDR_CONV RBP.
                        red. red in RBP.
                        eapply fin_inf_read_byte_prop_MemPropT; eauto.
                      Qed.

                      Lemma fin_inf_read_byte_spec :
                        forall addr_fin addr_inf ms_fin ms_inf byte_fin,
                          MemState_refine ms_inf ms_fin ->
                          InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
                          Memory64BitIntptr.MMEP.MemSpec.read_byte_spec ms_fin addr_fin byte_fin ->
                          MemoryBigIntptr.MMEP.MemSpec.read_byte_spec ms_inf addr_inf (lift_SByte byte_fin).
                      Proof.
                        intros addr_fin addr_inf ms_fin ms_inf byte_fin MSR ADDR_CONV READ_SPEC.
                        destruct READ_SPEC.
                        split.
                        - eapply fin_inf_read_byte_allowed; eauto.
                        - eapply fin_inf_read_byte_prop; eauto.
                      Qed.

                      Lemma fin_inf_read_byte_spec_MemPropT :
                        forall addr_fin addr_inf ms_fin ms_inf byte_fin,
                          MemState_refine ms_inf ms_fin ->
                          InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
                          Memory64BitIntptr.MMEP.MemSpec.read_byte_spec_MemPropT addr_fin ms_fin (success_unERR_UB_OOM (ms_fin, byte_fin)) ->
                          MemoryBigIntptr.MMEP.MemSpec.read_byte_spec_MemPropT addr_inf ms_inf (success_unERR_UB_OOM (ms_inf, lift_SByte byte_fin)).
                      Proof.
                        intros addr_fin addr_inf ms_fin ms_inf byte_fin MSR ADDR_CONV READ_SPEC.
                        red. cbn.
                        split; auto.
                        red in READ_SPEC. cbn in READ_SPEC.
                        destruct READ_SPEC.
                        eapply fin_inf_read_byte_spec; eauto.
                      Qed.

                      (* TODO: need to relate bytes_fin and bytes_inf *)
                      (* Will need ms_fin and ms_inf to be related as well *)
                      Lemma fin_inf_read_bytes_spec :
                        forall a_fin a_inf n ms_fin ms_inf bytes_fin,
                          InfToFinAddrConvert.addr_convert a_inf = NoOom a_fin ->
                          MemState_refine ms_inf ms_fin ->
                          Memory64BitIntptr.MMEP.MemSpec.read_bytes_spec a_fin n ms_fin (success_unERR_UB_OOM (ms_fin, bytes_fin)) ->
                          MemoryBigIntptr.MMEP.MemSpec.read_bytes_spec a_inf n ms_inf (success_unERR_UB_OOM (ms_inf, map lift_SByte bytes_fin)).
                      Proof.
                        intros a_fin a_inf n ms_fin ms_inf bytes_fin ADDR_CONV MEM_REF READ_SPEC.

                        (* TODO: Make these opaque earlier *)
                        Opaque Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs.
                        Opaque MemoryBigIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs.
                        red. red in READ_SPEC.
                        cbn in *.
                        destruct READ_SPEC as (ms_fin' & addrs_fin & CONSEC & READ_SPEC).
                        exists ms_inf.
                        pose proof fin_inf_get_consecutive_ptrs_success_exists a_fin a_inf n ms_fin ms_fin' addrs_fin ms_inf ADDR_CONV CONSEC as (addrs_inf & GCP & ADDRS_CONV).
                        exists addrs_inf.
                        split; auto.

                        (* Not sure if induction is the right thing to do here *)
                        generalize dependent a_fin.
                        generalize dependent a_inf.
                        generalize dependent n.
                        generalize dependent bytes_fin.
                        induction ADDRS_CONV; intros bytes_fin READ_SPEC n a_inf GCP a_fin ADDR_CONV CONSEC.
                        - cbn in *.
                          destruct READ_SPEC; subst; cbn.
                          auto.
                        - rewrite map_monad_unfold.
                          cbn.

                          rename l into addrs_fin.
                          rename l' into addrs_inf.
                          rename y into x_inf.
                          rename x into x_fin.

                          cbn in READ_SPEC.
                          destruct READ_SPEC as [ms_fin'' [a [[MS READ_SPEC] READ_SPEC_REST]]]; subst.

                          assert (ms_fin'' = ms_fin) as MSFIN.
                          {
                            (* TODO: make this a lemma *)
                            Transparent Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs.
                            unfold Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs in CONSEC.
                            cbn in CONSEC.
                            destruct CONSEC as [sab [ips [SEQ CONSEC]]].
                            red in SEQ.
                            break_match_hyp; inv SEQ.
                            destruct CONSEC as [sab [addrs [CONSEC SEQ]]].
                            red in CONSEC.
                            break_match_hyp; inv CONSEC.
                            red in SEQ.
                            break_match_hyp; inv SEQ.                                                   auto.
                            Opaque Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs.
                          }
                          subst.

                          pose proof READ_SPEC_REST as READ_SPEC_REST'.
                          destruct READ_SPEC_REST as [ms_fin' [bytes_fin' READ_SPEC_REST]].
                          destruct READ_SPEC_REST as [READ_SPEC_REST [MS BYTES_FIN]].
                          subst.

                          exists ms_inf. exists (lift_SByte a).
                          split.
                          { split; auto.
                            eapply fin_inf_read_byte_spec; eauto.
                          }

                          assert ((exists (pre : MemoryBigIntptr.MMEP.MMSP.MemState) (post : MemoryBigIntptr.MMEP.MMSP.MemState),
                                      Within.within (InfLLVM.MEM.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs a_inf n) pre
                                        (ret (x_inf :: addrs_inf)) post)).
                          { exists ms_inf. exists ms_inf.
                            cbn. red. cbn.
                            auto.
                          }

                          specialize (IHADDRS_CONV _ READ_SPEC_REST).

                          epose proof InfLLVM.MEM.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs_cons _ _ _ _ H0.
                          destruct H1 as [XA [[PTRS N] | [ptr' [ip' [len' [LEN [IP [GEP [pre [post WITHIN]]]]]]]]]].
                          { subst.
                            cbn in *.
                            exists ms_inf. exists [].
                            split; auto.
                            split; auto.

                            specialize (IHADDRS_CONV 0%nat a_inf).
                            forward IHADDRS_CONV.
                            { cbn.
                              (* TODO: This should probably be a lemma *)
                              Transparent MemoryBigIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs.
                              unfold MemoryBigIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs.
                              Opaque MemoryBigIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs.
                              cbn.
                              exists ms_inf. exists [].
                              split; auto.
                              exists ms_inf. exists [].
                              cbn.
                              auto.
                            }

                            specialize (IHADDRS_CONV _ H).
                            inv ADDRS_CONV.
                            forward IHADDRS_CONV.
                            { cbn.
                              (* TODO: This should probably be a lemma *)
                              Transparent Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs.
                              unfold Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs.
                              Opaque Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs.
                              cbn.
                              exists ms_fin'. exists [].
                              split; auto.
                              exists ms_fin'. exists [].
                              cbn.
                              auto.
                            }

                            destruct IHADDRS_CONV; subst.
                            pose proof (map_eq_nil _ _ H2) as BYTES_FIN'_NIL; subst.
                            cbn; auto.
                          }

                          pose proof H0 as WITHIN_INF.
                          destruct H0 as [pre' [post' WITHIN']].
                          cbn in WITHIN'.
                          red in WITHIN'.
                          cbn in WITHIN'.


                          subst.
                          cbn in WITHIN.
                          red in WITHIN.
                          cbn in WITHIN.

                          pose proof WITHIN as PREPOST.
                          eapply MemoryBigIntptr.MMEP.get_consecutive_ptrs_MemPropT_MemState_eq in PREPOST.
                          subst.

                          exists ms_inf. exists (map lift_SByte bytes_fin').
                          split; auto.

                          destruct addrs_inf as [? | a_inf' addrs_inf].
                          {
                            destruct addrs_fin as [? | a_fin' addrs_fin].
                            {
                              cbn in READ_SPEC_REST.
                              destruct READ_SPEC_REST; subst.
                              cbn; auto.
                            }

                            (* Should be a contradiction *)
                            inv ADDRS_CONV.
                          }

                          destruct addrs_fin as [? | a_fin' addrs_fin].
                          { (* Should be a contradiction *)
                            inv ADDRS_CONV.
                          }

                          eapply IHADDRS_CONV.
                          + eapply MemoryBigIntptr.MMEP.get_consecutive_ptrs_MemPropT_MemState.
                            eapply WITHIN.
                          + (* How do I know ptr' is safe to convert
                               to a finite pointer?

                               I know it's a_inf + 1...

                               Need to show that a_inf' is a_inf + 1
                               as well, and that it relates to a_fin'.
                             *)

                            (* ptr' is a_inf + 1 (AKA a_inf'). It
                               should share the same provenance as well.
                             *)

                            pose proof (MemoryBigIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs_nth_eq1  a_inf (S len') (a_inf :: a_inf' :: addrs_inf) (M:=(MemPropT MemoryBigIntptr.MMEP.MMSP.MemState))).
                            forward H0.
                            { red. red.
                              intros ms x0.
                              split.
                              - intros GCP'.
                                cbn.
                                (* Ideally want to use GCP to show this... *)
                                assert (exists (pre : MemoryBigIntptr.MMEP.MMSP.MemState) (post : MemoryBigIntptr.MMEP.MMSP.MemState),
                                           @Within.within (MemPropT MemoryBigIntptr.MMEP.MMSP.MemState) (@MemPropT_Eq1 MemoryBigIntptr.MMEP.MMSP.MemState) err_ub_oom MemoryBigIntptr.MMEP.MMSP.MemState MemoryBigIntptr.MMEP.MMSP.MemState _ _ (MemoryBigIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs a_inf (S len')) pre (fmap snd x0) post).
                                { exists ms. exists ms.
                                  red. red. red.
                                  destruct_err_ub_oom x0;
                                    cbn; auto.

                                  destruct x1; cbn in *.
                                  pose proof GCP' as GCP''.
                                  assert (success_unERR_UB_OOM (m, l) = @ret _ _ _ (m, l)); cbn; auto.
                                  rewrite H1 in GCP''.

                                  pose proof MemoryBigIntptr.MMEP.get_consecutive_ptrs_MemPropT_MemState_eq a_inf (S len') l ms m GCP''; subst.
                                  eauto.
                                }

                                pose proof MemoryBigIntptr.CP.CONCBASE.MemHelpers.get_consecutive_ptrs_success_always_succeeds (M:=(MemPropT MemoryBigIntptr.MMEP.MMSP.MemState)) (B:=err_ub_oom) a_inf (S len') (a_inf :: a_inf' :: addrs_inf) _ WITHIN_INF H1.
                                destruct_err_ub_oom x0; cbn in *; inv H2.
                                destruct x1; cbn in *; subst.
                                pose proof GCP' as MM.
                                apply MemoryBigIntptr.MMEP.get_consecutive_ptrs_MemPropT_MemState_eq in MM.
                                subst.
                                split; auto.
                              - intros H1.
                                cbn in H1.
                                destruct_err_ub_oom x0; try inv H1.
                                destruct x1.
                                destruct H1.
                                subst.
                                pose proof WITHIN'.
                                apply MemoryBigIntptr.MMEP.get_consecutive_ptrs_MemPropT_MemState_eq in H1; subst.
                                eapply MemoryBigIntptr.MMEP.get_consecutive_ptrs_MemPropT_MemState.
                                eapply WITHIN'.
                            }

                            specialize (H0 a_inf' 1%nat).
                            forward H0; cbn; auto.
                            destruct H0 as [ix [IX GEP_IX]].

                            (* Show that ip' = ix *)
                            assert (ip' = ix) as IPIX.
                            {
                              cbn in IX.
                              inv IX.
                              unfold InterpreterStackBigIntptr.LP.IP.to_Z in IP.
                              auto.
                            }
                            subst.

                            rewrite GEP in GEP_IX.
                            inv GEP_IX.
                            inv ADDRS_CONV.
                            eauto.
                          + (* Should follow from CONSEC *)

                            assert ((exists (pre : FinMem.MMEP.MMSP.MemState) (post : FinMem.MMEP.MMSP.MemState),
                                        Within.within (FinLLVM.MEM.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs a_fin (S len')) pre
                                          (ret (x_fin :: a_fin' :: addrs_fin)) post)).
                            {
                              exists ms_fin'. exists ms_fin'.
                              cbn. red. cbn.
                              auto.
                            }

                            pose proof FinMem.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs_cons _ _ _ _ H0.
                            destruct H1.
                            destruct H2.
                            { destruct H2; discriminate.
                            }

                            destruct H2 as [ptr'' [ip [len'' [LEN [IP' [GEP'' WITHIN'']]]]]].
                            (* GEP'' suggests ptr'' = a_fin' *)
                            assert (ptr'' = a_fin').
                            {
                              subst.
                              pose proof FinMem.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs_cons _ _ _ _ WITHIN''.
                              destruct H1.
                              auto.
                            }
                            subst.

                            destruct WITHIN'' as [pre [post'' WITHIN'']].
                            cbn in WITHIN''.
                            red in WITHIN''.
                            cbn in WITHIN''.
                            pose proof WITHIN''.
                            inv LEN.
                            apply FinMem.MMEP.get_consecutive_ptrs_MemPropT_MemState_eq in H1; subst.
                            eapply FinMem.MMEP.get_consecutive_ptrs_MemPropT_MemState; eauto.
                            eapply WITHIN''.
                      Qed.

                      (* TODO: Lemma about lifting intrinsic handlers *)
                      (* TODO: Move this *)
                      Lemma handle_intrinsic_fin_inf :
                        forall t f args args0 ms ms' d
                          (ARGS: Forall2 DVCInfFin.dvalue_refine_strict args0 args),
                          Memory64BitIntptr.MMEP.MemSpec.handle_intrinsic_prop
                            LLVMParams64BitIntptr.Events.DV.dvalue
                            (LLVMParams64BitIntptr.Events.Intrinsic t f args) ms (ret (ms', d)) ->
                          MemoryBigIntptr.MMEP.MemSpec.handle_intrinsic_prop DVCInfFin.DV1.dvalue
                            (InterpreterStackBigIntptr.LP.Events.Intrinsic t f args0) (lift_MemState ms)
                            (ret (lift_MemState ms', fin_to_inf_dvalue d)).
                      Proof.
                        intros t f args args0 ms ms' d ARGS INTRINSIC.

                        pose proof lift_MemState_refine ms as MS_REF.
                        pose proof lift_MemState_refine ms' as MS'_REF.

                        red in INTRINSIC.
                        red.
                        break_match.
                        { (* Memcpy *)
                          cbn in *.
                          destruct INTRINSIC as [sab [[] [HANDLER [SAB D]]]].
                          subst.
                          exists (lift_MemState sab).
                          exists tt.
                          repeat split; auto.
                          - (* Handler *)
                            repeat (destruct ARGS;
                                    [solve [ inversion HANDLER
                                           | red in HANDLER;
                                             repeat break_match_hyp; inversion HANDLER
                                       ]
                                    |
                                   ]).
                            red in HANDLER.
                            repeat break_match_hyp; try inversion HANDLER; subst.
                            { (* 32 bit memcpy *)
                              admit.
                            }

                            { (* 64 bit memcpy *)
                              admit.
                            }

                            { (* iptr memcpy *)
                              inversion ARGS; subst.
                              clear ARGS.
                              rewrite DVCInfFin.dvalue_refine_strict_equation in H, H0, H1, H2, H3.

                              apply dvalue_convert_strict_addr_inv in H as (a' & H & X); subst.
                              apply dvalue_convert_strict_addr_inv in H0 as (a0' & H0 & X0); subst.
                              apply dvalue_convert_strict_iptr_inv in H1 as (x4' & H1 & X4); subst.
                              apply dvalue_convert_strict_iptr_inv in H2 as (x5' & H2 & X5); subst.
                              apply dvalue_convert_strict_i1_inv in H3; subst.

                              red. red.
                              red in HANDLER.

                              assert (LLVMParams64BitIntptr.IP.to_Z x4 = LLVMParamsBigIntptr.IP.to_Z x4') as X4.
                              { (* TODO: weird iptr reasoning... *)
                                admit.
                              }
                              rewrite <- X4; clear X4.

                              break_match_hyp; auto.

                              erewrite <- fin_inf_no_overlap; eauto.
                              repeat erewrite <- fin_inf_ptoi; eauto.
                              break_match_goal; auto.

                              do 2 red in HANDLER.
                              destruct HANDLER as (ms_read&bytes_fin&READ&WRITE).
                              epose proof fin_inf_read_bytes_spec _ _ _ _ _ _ H0 MS_REF.
                              (* TODO: Move this to somewhere it can
                                 be instantiated for all memory model
                                 instances
                               *)
                              Lemma read_bytes_spec_MemState_eq :
                                forall a sz ms ms' res,
                                  Memory64BitIntptr.MMEP.MemSpec.read_bytes_spec a sz ms (ret (ms', res)) ->
                                  ms = ms'.
                              Proof.
                                intros a sz ms ms' res READ.
                                red in READ.
                                cbn in *.
                                destruct READ as [sab [a0 [GCP HMAPM]]].
                                apply Memory64BitIntptr.MMEP.get_consecutive_ptrs_MemPropT_MemState_eq in GCP. subst.
                                generalize dependent res.
                                induction a0; intros res HMAPM.
                                - cbn in *.
                                  destruct HMAPM; subst; auto.
                                - rewrite map_monad_unfold in HMAPM.
                                  cbn in *.
                                  destruct HMAPM as [sab0 [a' [[MS READ] HMAPM]]]; subst.
                                  destruct HMAPM as [sab [a'' [HMAPM [MS RES]]]]; subst.
                                  eapply IHa0.
                                  eapply HMAPM.
                              Qed.

                              pose proof READ as READ'.
                              eapply read_bytes_spec_MemState_eq in READ'; subst.
                              forward H3.
                              { eapply READ.
                              }

                              destruct H3 as [ms [addrs [GCP READ']]].
                              red. red.
                              exists ms. exists (map lift_SByte bytes_fin).
                              split.
                              { (* Read portion *)
                                red.
                                cbn.
                                exists ms. exists addrs.
                                split; auto.

                                assert (ms = lift_MemState ms_read).
                                {
                                  symmetry.
                                  eapply MemoryBigIntptr.MMEP.get_consecutive_ptrs_MemPropT_MemState_eq; eauto.
                                }
                                subst; eauto.
                              }

                              (* Write bytes portion *)
                              

                              -


                              red. red.
                              
                              cbn in READ'.
                              destruct READ' as [ms
                              

                              Set Printing Implicit.

                                    unfold LLVMParams64BitIntptr.ITOP.int_to_ptr in H2.
                                    unfold FinITOP.int_to_ptr.

                                    break_match_hyp; inv H2.
                                    break_match_goal.
                                    admit.



                                    pose proof (fin_inf_ptoi a a').
                                    assert (InfToFinAddrConvert.addr_convert a' = NoOom a) as AA'.
                                    { (* clear - ADDRS HMAPM Heqo0. *)
                                      (* pose proof (Util.Forall2_Nth_right H ADDRS) as [x [NTHxs CONVxy]]. *)
                                      (* pose proof (map_monad_OOM_Nth _ _ _ x 0 Heqo0 NTHxs) as [x'' [X NTHoxs]]. *)
                                      (* unfold id in X. cbn in X. inv X. clear H1. *)
                                      (* pose proof (map_monad_err_Nth _ _ _ _ i HMAPM NTHoxs) as [x'' [X NTHixs]]. *)

                                      (* Can maybe do this by induction on i or something *)
                                      admit.
                                    }
                                    specialize (H1 AA').

                                    rewrite <- H1.
                                    change (LLVMParams64BitIntptr.PTOI.ptr_to_int a) with (FinPTOI.ptr_to_int a).

                                    eapply FinITOP.int_to_ptr_ptr_to_int.
                                    eapply ITOP.int_to_ptr_ptr_to_int.

                                    rewrite <- H2 in CONVxy.


                                    eapply CONVxy.
                                    pose proof FinLP.ITOP.ptr_to_int_int_to_ptr _ _ _ H2.
                                    pose proof ITOP.int_to_ptr_provenance _ _ _ H2.
                                    unfold InfToFinAddrConvert.addr_convert in CONVxy.
                                    destruct y.
                                    unfold FinITOP.int_to_ptr in CONVxy.
                                    cbn in CONVxy.
                                    clear H
                                    inv Y.
                                    destruct H1.
                                  }

                                  assert (forall i a b, Util.Nth ys i a -> Util.Nth l2 i b -> a = b) as NTHysl2.
                                  {
                                    intros i y x NTHy NTHx.

                                    generalize dependent l0.
                                    induction ADDRS; intros l0' HMAPM Heqo0.
                                    - cbn in NTHy; rewrite Util.nth_error_nil in NTHy; inv NTHy.
                                    - pose proof Heqo0 as SEQ_XS.
                                      apply sequence_oom_cons_inv in Heqo0.
                                      destruct Heqo0 as (?&?&?); subst.
                                      rename l0 into xs.
                                      rename l' into ys.
                                      rename H into ADDR.

                                      rename x0 into ox.
                                      rename x1 into oxs.

                                      specialize (IHADDRS oxs).
                                      forward IHADDRS.
                                      { rewrite sequence_cons in SEQ_XS.
                                        cbn in SEQ_XS.
                                        break_match_hyp; inv SEQ_XS.
                                        break_match_hyp; inv H0.
                                        reflexivity.
                                      }



                                      rename l1 into addrs_inf_oom.
                                      rename l2 into addrs_inf.
                                      rename l0 into addrs_fin.
                                      rename l' into addrs_inf_of_fin.

                                      eapply IHADDRS.



                                      pose proof sequence_oom_nth' _ _ Heqo.
                                      specialize (H1 i x) as [NTH1x NTH2x].
                                      specialize (NTH1x NTHx).

                                      pose proof (map_monad_err_Nth _ _ _ _ _ HMAPM' NTH1x).
                                      destruct H1 as (x_ip & X_IP & NTHxip).
                                      inv X_IP.

                                      induction i.
                                      + cbn in *.
                                        destruct l2; inv NTHx.
                                        inv NTHy.
                                        destruct y as [y_ptr y_prov].
                                        destruct lb; inv NTHxip.
                                        destruct l1; inv NTH1x.

                                        pose proof MemoryBigIntptr.MMEP.MemSpec.MemHelpers.intptr_seq_nth 0 n (x_ip :: lb) 0 x_ip SEQ_BIG eq_refl as X_IP0.
                                        erewrite FiniteIntptr.BigIP.from_Z_to_Z; eauto.
                                        replace ((LLVMParamsBigIntptr.PTOI.ptr_to_int a' +
                                                    Z.of_N (LLVMParamsBigIntptr.SIZEOF.sizeof_dtyp (DTYPE_I 8)) * (0 + Z.of_nat 0))%Z) with (LLVMParamsBigIntptr.PTOI.ptr_to_int a') by lia.
                                        destruct a' as [a'_ptr a'_prov]; cbn.

                                        rewrite map_monad_unfold in HMAPM'.
                                        cbn in HMAPM'.
                                        break_match_hyp; inv HMAPM'.

                                        pose proof HMAPM as HMAPM2.
                                        apply map_monad_err_cons_inv in HMAPM2.
                                        destruct HMAPM2 as (?&?&?); subst.

                                        rewrite map_monad_unfold in HMAPM.
                                        cbn in HMAPM.
                                        break_match_hyp; inv HMAPM.
                                        clear NTH2x.

                                        (* I don't know anything about...

                                        H : InfToFinAddrConvert.addr_convert (y_ptr, y_prov) = NoOom x0


                                        *)

                                        pose proof HMAPM' as HMAPM''.
                                        apply map_monad_err_cons_inv in HMAPM''.
                                        destruct HMAPM'' as (?&?&?).
                                        inv H1.
                                        clear NTH2x.

                                        rename a into blah.

                                        (* Right hand side is literally a'... *)
                                        assert (((LLVMParamsBigIntptr.PTOI.ptr_to_int a' +
                                                    Z.of_N (LLVMParamsBigIntptr.SIZEOF.sizeof_dtyp (DTYPE_I 8)) * LLVMParamsBigIntptr.IP.to_Z x_ip)%Z,
                                                  LLVMParamsBigIntptr.PROV.address_provenance a') = a').
                                        { destruct a'. cbn.

                                        }


InfToFinAddrConvert.addr_convert_injective:
  forall (a b : InfAddr.addr) (c : FinAddr.addr),
  InfToFinAddrConvert.addr_convert a = NoOom c ->
  InfToFinAddrConvert.addr_convert b = NoOom c -> a = b

                                        rename y into blah.

                                      pose proof sequence_oom_nth' _ _ Heqo.

                                      pose proof HMAPM.
                                      apply map_monad_err_cons_inv in HMAPM as (?&?&?); subst.
                                      inversion ALL; subst.

                                      apply map_monad_err_cons in HMAPM' as (?&?&?); subst.
                                      apply sequence_oom_cons in Heqo as (?&?&?); subst.

                                      induction i.
                                      + cbn in *.
                                        inv NTHy; inv NTHx.

                                        rename x into blah.

                                    admit.
                                  }

                                  epose proof (Util.Forall2_forall eq ys l2).
                                  destruct H as [_ H].
                                  forward H.
                                  { split.
                                    - (* Length *)
                                      (* TODO: Use a hint DB for this? *)
                                      (* Hint Resolve sequence_OOM_length map_monad_err_length Memory64BitIntptr.MMEP.MemSpec.MemHelpers.intptr_seq_len MemoryBigIntptr.MMEP.MemSpec.MemHelpers.intptr_seq_len Util.Forall2_length : LENGTH. *)
                                      (* Hint Extern 0 => lia : LENGTH. *)

                                      apply sequence_OOM_length in Heqo, Heqo0.
                                      apply map_monad_err_length in HMAPM', HMAPM.
                                      apply Memory64BitIntptr.MMEP.MemSpec.MemHelpers.intptr_seq_len in SEQ.
                                      apply MemoryBigIntptr.MMEP.MemSpec.MemHelpers.intptr_seq_len in SEQ_BIG.
                                      apply Util.Forall2_length in ALL.
                                      apply Util.Forall2_length in ADDRS.
                                      lia.
                                    - intros i a0 b NTHys NTHls.
                                      eauto.
                                  }

                                  clear - H.
                                  induction H; subst; auto.
                                }



                                  eapply Util.Forall2_Nth.
                                  apply Forall2

                                  induction ADDRS.
                                  - apply sequence_OOM_length in Heqo0.
                                    cbn in *.
                                    apply length_zero_iff_nil in Heqo0; subst.
                                    apply map_monad_err_nil_inv in HMAPM; subst.
                                    inversion ALL; subst.

                                    apply map_monad_err_nil in HMAPM'; subst.
                                    cbn in *.
                                    inv Heqo.
                                    auto.
                                  - pose proof Heqo0.
                                    apply sequence_oom_cons_inv in Heqo0.
                                    destruct Heqo0 as (x'&xs&Heqo0).
                                    subst.

                                    apply map_monad_err_cons_inv in HMAPM.
                                    destruct HMAPM as (?&?&?); subst.

                                    inversion ALL; subst.
                                    pose proof HMAPM'.
                                    apply map_monad_err_cons in HMAPM'.
                                    destruct HMAPM' as (?&?&?); subst.

                                    cbn in Heqo.

                                    break_match_hyp; inv Heqo.
                                    break_match_hyp; inv H4.
                                    apply

                                }

                                (* TODO: Move this *)
                                Lemma sequence_noom :
                                  forall {X} (l : list (OOM X)),
                                    Forall (fun x => exists y, x = NoOom y) l ->
                                    exists l', Monads.sequence l = NoOom l'.
                                Proof.

                                Abort.

                                apply map_monad_err_forall2 in HMAPM'.
                                red.
                                break_match_goal.
                                cbn.
                                2: {
                                  (* Heqo should end up being a contradiction *)
                                  admit.
                                }
                                split; auto.

                                (* ys is related to xs...
                                   xs is related to l0
                                 *)

                                Set Printing Implicit.
                                assert (map_monad
                                  (fun ix : LLVMParamsBigIntptr.IP.intptr =>
                                     inr
                                       (LLVMParamsBigIntptr.ITOP.int_to_ptr
                                          (LLVMParamsBigIntptr.PTOI.ptr_to_int a' +
                                             Z.of_N (LLVMParamsBigIntptr.SIZEOF.sizeof_dtyp (DTYPE_I 8)) *
                                               LLVMParamsBigIntptr.IP.to_Z ix) (LLVMParamsBigIntptr.PROV.address_provenance a')))
                                    lb = inr y).

                                exists ms_x.

                              Admitted.

                              (* TODO: Need lemmas for read_bytes_spec and write_bytes_spec... *)
                              Lemma fin_inf_read_bytes_spec :
                                forall a a' n ms ms' x y,
                                  InfToFinAddrConvert.addr_convert a' = NoOom a ->
                                  Memory64BitIntptr.MMEP.MemSpec.read_bytes_spec a n ms x ->
                                  MemoryBigIntptr.MMEP.MemSpec.read_bytes_spec a' n ms' y.
                              Proof.
                                intros a a' n ms ms' x y ACONV READ.
                                red.
                                red in READ.
                              Admitted.

                              cbn in HANDLER.


                                destruct_err_ub_oom x.
                              Unset Printing Notations.
                              Set Printing Implicit.

(@Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs
              (MemPropT Memory64BitIntptr.MMEP.MMSP.MemState)
              (@MemPropT_Monad Memory64BitIntptr.MMEP.MMSP.MemState)
              (@MemPropT_RAISE_OOM Memory64BitIntptr.MMEP.MMSP.MemState)
              (@MemPropT_RAISE_ERROR Memory64BitIntptr.MMEP.MMSP.MemState) a n)

    (@MemoryBigIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs
       (MemPropT MemoryBigIntptr.MMEP.MMSP.MemState)
       (@MemPropT_Monad MemoryBigIntptr.MMEP.MMSP.MemState)
       (@MemPropT_RAISE_OOM MemoryBigIntptr.MMEP.MMSP.MemState)
       (@MemPropT_RAISE_ERROR MemoryBigIntptr.MMEP.MMSP.MemState) a' n)
                              Lemma fin_inf_get_consecutive_ptrs :
                                forall a a' n ms ms' x y,
                                  InfToFinAddrConvert.addr_convert a' = NoOom a ->
                                  Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs a n ms x->
                                  MemoryBigIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs a' n ms' y.

  READ : (ptrs <- Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs a n;;
          map_monad
            (fun ptr : LLVMParams64BitIntptr.ADDR.addr =>
             Memory64BitIntptr.MMEP.MemSpec.read_byte_spec_MemPropT ptr) ptrs) ms
           (OOM_unERR_UB_OOM oom_x)
  ub_x : string
  Hx0 : y = UB_unERR_UB_OOM ub_x
  ============================
  (ptrs <- MemoryBigIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs a' n;;

                                - destruct_err_ub_oom y.
                                  + admit.
                                  + cbn in *.
                                cbn in *.
                                destruct x.
                              Qed.

                              cbn.
                                .


                              - (* Negative length UB in finite case *)
                                cbn in *.
                                rewrite DVCInfFin.dvalue_convert_strict_equation in H1.
                                destruct x1; inversion H1; try solve [ break_match_hyp; inv H5 ].
                                break_match_hyp; inv H5.
                                (* TODO: silly intptr reasoning... *)
                                red.
                                setoid_rewrite (IP.to_Z_from_Z x1). in Heqo.
                                unfold DVCInfFin.dvalue_convert_strict in H1.
                                red in H2.
                                break_match_goal.
                                + admit.
                                + cbn in *.

                              admit.
                            }
                          - unfold fin_to_inf_dvalue.
                            break_match.
                            destruct p; cbn in *.
                            clear Heqs.
                            rewrite DVC2.dvalue_convert_strict_equation in e.
                            inv e.
                            reflexivity.
                        }

                        admit.
                      Admitted.

                      eapply handle_intrinsic_fin_inf; eauto.
                    }
                    2: {
                      cbn.
                      setoid_rewrite bind_ret_l.
                      rewrite VIS_HANDLED.
                      pstep; red; cbn.

                      (* TODO: Move this, make uvalue versions *)
                      Lemma dvalue_fin_to_inf_to_fin :
                        forall d,
                          DVCInfFin.dvalue_convert_strict (fin_to_inf_dvalue d) = NoOom d.
                      Proof.
                        intros d.
                        pose proof fin_to_inf_dvalue_refine_strict d.
                        auto.
                      Qed.

                      Lemma MemState_fin_to_inf_to_fin :
                        forall ms,
                          convert_MemState (lift_MemState ms) = NoOom ms.
                      Proof.
                      Admitted.

                      rewrite dvalue_fin_to_inf_to_fin.
                      rewrite MemState_fin_to_inf_to_fin.
                      eapply Reflexive_eqitF_eq.
                      { red. intros x.
                        left.
                        apply paco2_eqit_refl.
                      }
                    }

                    clear INTRINSIC.
                    intros a (ms''&sid'&b) RET H1 H2; cbn in *; subst.
                    apply Returns_ret_inv in H1.
                    inv H1.

                    break_match_goal.
                    2: {
                      (* OOM *)
                      cbn.
                      left.
                      pstep; red; cbn.
                      observe_vis; solve_interp_prop_oom.
                    }
                    break_match_goal.
                    2: {
                      (* OOM *)
                      cbn.
                      left.
                      pstep; red; cbn.
                      observe_vis; solve_interp_prop_oom.
                    }

                    pclearbot.
                    right.
                    rewrite (itree_eta_ (k0 _)).
                    rewrite (itree_eta_ (k2 _)).

                    eapply CIH;
                      repeat rewrite <- itree_eta_.

                    2: {
                      red.
                      specialize (HK d (ms', (st1, d))).
                      forward HK.
                      { eapply ReturnsVis.
                        pstep; red; cbn.
                        constructor.
                        intros v. red.
                        left; apply paco2_eqit_refl.
                        constructor.
                        reflexivity.
                      }
                      forward HK.
                      { rewrite H0.
                        constructor.
                        reflexivity.
                      }
                      forward HK; cbn; auto.
                      pclearbot.
                      rewrite MemState_fin_to_inf_to_fin in Heqo0; inv Heqo0.
                      rewrite dvalue_fin_to_inf_to_fin in Heqo; inv Heqo.
                      apply HK.
                    }

                    rewrite REL.
                    eapply K_RUTT; split; auto.
                  }
                }

                { (* MemPush *)
                  admit.
                }

                { (* MemPop *)
                  admit.
                }

                { (* Alloca *)
                  admit.
                }

                { (* Load *)
                  admit.
                }

                { (* Store *)
                  admit.
                }

                { (* Pick *)
                  admit.
                }

                { (* OOM *)
                  admit.
                }

                { (* UBE *)
                  admit.
                }

                { (* DebugE *)
                  admit.
                }

                { (* FailureE *)
                  admit.
                }

                admit.
                admit.
                admit.
                admit.
                cbn in *.
                discriminate.
                admit.
                destruct e, e1. try destruct n; try destruct n0; cbn in EV_REL; try inversion EV_REL.

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
                admit.
              + (* om1 = Tau *)
                (* Tau on the left... *)
                constructor; auto.
                eapply IHM1; eauto.
            - (* TauL *)
              pclearbot.
              apply orutt_inv_Vis_r in H.
              destruct H as [[U1 [e1 [k3 [M1 [EV_REL K_RUTT]]]]] | OOM].
              2: {
                destruct OOM as [o OOM].
                inv OOM.
                repeat red in H0.
                rewrite H0 in H1.
                setoid_rewrite bind_trigger in H1.
                setoid_rewrite bind_vis in H1.
                punfold H1; red in H1; cbn in H1.
                dependent induction H1.
                - destruct o.
                  eapply Interp_Memory_PropT_Vis_OOM.
                  rewrite get_inf_tree_equation.
                  cbn.
                  unfold raiseOOM.
                  rewrite bind_trigger.
                  reflexivity.
                - specialize (EQ t1). contradiction.
              }

              repeat red in H0.
              destruct e; cbn in *.
              + (* ExternalCallE *)
                red in H0.
                setoid_rewrite bind_trigger in H0.
                setoid_rewrite H0 in H1.
                setoid_rewrite bind_vis in H1.
                punfold H1; red in H1; cbn in H1.
                dependent induction H1.
                * { clear IHRUN.
                    punfold M1; red in M1; cbn in M1.
                    genobs m1 om1.
                    clear m1 Heqom1.
                    assert (DEC: (exists m1, om1 = TauF m1) \/ (forall m1, om1 <> TauF m1)).
                    { destruct om1; eauto; right; red; intros; inversion H. }
                    destruct DEC as [EQ' | EQ'].
                    { (* Tau case *)
                      destruct EQ' as [m1' EQ'].
                      subst.
                      constructor; auto.
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

                    dependent induction M1.
                    - repeat red in EV_REL.
                      destruct e1; repeat destruct s; repeat destruct i; try contradiction.
                      destruct e0, e.
                      destruct EV_REL as (T&F&ARGS); subst.
                      eapply Interp_Memory_PropT_Vis with
                        (k2:=
                           fun '(_, (_, v)) => (get_inf_tree
                                               match DVCInfFin.dvalue_convert_strict v with
                                               | NoOom a => k0 a
                                               | Oom s => raiseOOM s
                                               end)
                        ).
                      + intros a b H H1 H2.
                        destruct b as (?&(?&a')).
                        cbn in *; subst.

                        (*
                         REL0 is k1 to k3...
                         K_RUTT is k3 to k4
                         HK gives k4 to k2
                         REL gives k2 to k0

                         RUN may be useful too... Although, I'm in the
                         middle of dependent induction on RUN, so
                         probably not.
                         *)
                        left.
                        eapply paco2_mon_bot; eauto.

                        specialize (REL0 a').
                        red in REL0.
                        pclearbot.
                        rewrite REL0.



                        inversion RUN.
                        { rewrite itree_eta in HT1.
                          rewrite H4 in HT1.
                          punfold HT1; red in HT1; cbn in HT1.
                          dependent induction HT1.
                        }

                        subst_existT.
                        cbn in H4.
                        red in H4.
                        setoid_rewrite bind_trigger in H4.
                        rewrite H4 in H7.
                        setoid_rewrite bind_vis in H7.
                        setoid_rewrite bind_ret_l in H7.
                        rewrite itree_eta in H7.
                        rewrite H6 in H7.
                        punfold H7; red in H7; cbn in H7.
                        dependent destruction H7.
                        dependent destruction RUN.
                        admit.



                        admit.
                      + cbn. red.
                        setoid_rewrite bind_trigger.
                        reflexivity.
                      + rewrite get_inf_tree_equation.
                        cbn.
                        rewrite bind_vis.
                        pose proof (fin_to_inf_uvalue_refine_strict' _ _ F).
                        rewrite <- H.

                        rewrite Forall2_map_eq with (l2:=args).
                        2: {
                          eapply Forall2_flip.
                          eapply Util.Forall2_impl; [| apply ARGS].
                          intros a b H1.
                          red.
                          symmetry.
                          apply fin_to_inf_dvalue_refine_strict'.
                          auto.
                        }

                        setoid_rewrite bind_ret_l.

                        pstep; red; cbn.
                        constructor.
                        intros v. red.
                        left.
                        apply paco2_eqit_refl.
                    - eapply IHRUN.

                      constructor; auto.
                  }
                * specialize (EQ t1). contradiction.
              +

                genobs m1 om1.
                clear m1 Heqom1 IHRUN.

                cbn in *.



                repeat red in EV_REL.


                assert (get_inf_tree {| _observe := t2 |} ≈ get_inf_tree (vis (@resum (Type -> Type) IFun OOME
                                                                                 (PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                                                                                 (@ReSum_inr (Type -> Type) IFun sum1 Cat_IFun Inr_sum1 OOME
                                                                                    (OOME +' UBE +' DebugE +' FailureE) PickUvalueE
                                                                                    (@ReSum_inl (Type -> Type) IFun sum1 Cat_IFun Inl_sum1 OOME OOME
                                                                                       (UBE +' DebugE +' FailureE)
                                                                                       (@ReSum_id (Type -> Type) IFun Id_IFun OOME))) A o) (fun x : A => ITree.bind (ret (s2, (s1, x))) k2))).
                {
                  rewrite H1.
                  reflexivity.
                }
                rewrite H2.
                eapply get_inf_tree_Proper.
                setoid_rewrite H1.
          }
               punfold H; red in H; cbn in H.
               genobs m1 om1.
               setoid_rewrite (itree_eta_ m1) in IHRUN.
               rewrite <- Heqom1 in IHRUN.
               clear m1 Heqom1.
               dependent induction H.
               + repeat red in H2.
                 break_match_hyp.
                 * red in H2.
                   setoid_rewrite bind_trigger in H2.
                   rewrite H2 in H3.
                   setoid_rewrite bind_vis in H3.
                   setoid_rewrite bind_ret_l in H3.
                   inv Heqs.
                   repeat red in H.
                   destruct e1; try discriminate.
                   2: { destruct s. destruct i; try contradiction.
                        repeat destruct s; try contradiction.
                   }
                   destruct e, e0.
                   destruct H as (?&?&?); subst.
                   eapply Interp_Memory_PropT_Vis.
                   2: {
                     repeat red.
                     setoid_rewrite bind_trigger.
                     apply paco2_eqit_refl.
                   }
                   2: {
                     rewrite H3.
                     rewrite get_inf_tree_equation.
                     cbn.
                     rewrite <- bind_ret_r.
                     eapply eutt_clo_bind. he

H5 : DVCInfFin.uvalue_refine_strict f f0

                     eapply eutt_clo_bind with
                       (UU:=fun '(ms, (sid, ((lenv, stack), (genv, dv)))) '(ms', (sid', dv')) => ms = ms' /\ sid = sid' /\ dv = dv').
                     2: {
                       intros u1 u2 H.
                       destruct u1 as (ms & (sid' & ((lenv & stack) & (genv & dv)))).
                       destruct u2 as (ms' & (sid'' & dv')).
                       destruct H as (?&?&?). subst.

                       k2 := (fun '(ms, (sid, dv)) => SemNotations.Ret5 genv (lenv, stack) sid ms dv)

                       unfold SemNotations.Ret5.

                     }
                       (t2 := (observe (vis
       (subevent E1.DV.dvalue
          (E1.ExternalCall t0 (fin_to_inf_uvalue f0) (map fin_to_inf_dvalue args0)))
       (fun x0 : E1.DV.dvalue =>
        get_inf_tree
          match DVCInfFin.dvalue_convert_strict x0 with
          | NoOom a => k2 (s2, (s1, a))
          | Oom s => raiseOOM s
          end)))).
                     - pstep; red; cbn.
                       constructor.
                     reflexivity.



  Notation res_L6 := (MemState * (store_id * (local_env * lstack * (global_env * dvalue))))%type.

with (ta:=(vis (E1.ExternalCall t0 (fin_to_inf_uvalue f0) (map fin_to_inf_dvalue args0))
       (fun x0 : E1.DV.dvalue =>
        get_inf_tree
          match DVCInfFin.dvalue_convert_strict x0 with
          | NoOom a => k2 (s2, (s1, a))
          | Oom s => raiseOOM s
          end))).

                     vis (E1.ExternalCall t0 (fin_to_inf_uvalue f0) (map fin_to_inf_dvalue args0))
                       (fun x0 : E1.DV.dvalue =>
                          get_inf_tree
                            match DVCInfFin.dvalue_convert_strict x0 with
                            | NoOom a => k2 (s2, (s1, a))
                            | Oom s => raiseOOM s
                            end)
                     pstep; red; cbn.
                     constructor.
                     intros v.
                     red.
                     left.
                     cbn.
                     break_match.
                     admit.
                     - cbn.
                     pose proof (dvalue_convert_strict_safe ).
                     reflexivity.
                     cbn.
                   }
                   -- intros a b H H7 H8.
                      destruct b as (?&?&?); cbn in *; subst.
                      pclearbot.
                      left.

                      pstep; red; cbn.
                      econstructor.
                      reflexivity.
                      eapply upaco2_mon_bot; eauto.
                      eapply H0.
                      eauto.
                      specialize (H0 a).
                      forward H0.

  H0 : forall (a : A0) (b : A),
       L2_res_refine_strict A0 A e1 a (inl1 e0) b ->
       upaco2
         (orutt_ L2_refine_strict L2_res_refine_strict
            (local_refine_strict × stack_refine_strict
             × (global_refine_strict × DVCInfFin.dvalue_refine_strict))) bot2
         (k0 a) (k1 b)



             - pclearbot.

               do 4 red in H0.
               break_match_hyp.
               + red in H0.
                 setoid_rewrite bind_trigger in H0.
                 rewrite H0 in H1.
                 setoid_rewrite bind_vis in H1.
                 punfold H1; red in H1; cbn in H1.
                 dependent induction H1.
                 * destruct e0.
                   rewrite get_inf_tree_equation.
                   cbn.
                   reflexivity.
                   (* TODO: Why won't this evaluate? *)
                   admit.
                 *
               + red in H0. repeat red in H0.

               cbn in H0.
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
