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

  Import TC1.

  #[local] Notation E1 := (E1.ExternalCallE +' OOME +' UBE +' DebugE +' FailureE).
  #[local] Notation E2 := (E2.ExternalCallE +' OOME +' UBE +' DebugE +' FailureE).
  #[local] Notation OOM_h := (refine_OOM_handler).

  Module InfLLVM := Vellvm.Semantics.InterpretationStack.InterpreterStackBigIntptr.LLVM.
  Module FinLLVM := Vellvm.Semantics.InterpretationStack.InterpreterStack64BitIntptr.LLVM.
  Module InfFinTC := Vellvm.Semantics.InfiniteToFinite.LangRefine.InfFinLangRefine.TC1.
  (* Module FinInfTC := Vellvm.Semantics.InfiniteToFinite.LangRefine.FinInfLangRefine.TC1. *)

  Module EC1 := InfFinTC.EC.
  Module DVC1 := EC1.DVC.
  (* Module EC2 := FinInfTC.EC. *)

  Module InfMem := MemoryBigIntptr.
  Module FinMem := Memory64BitIntptr.

  Module InfMemMMSP := MemoryBigIntptr.MMEP.MMSP.
  Module FinMemMMSP := Memory64BitIntptr.MMEP.MMSP.

  Module InfMemInterp := MemoryBigIntptr.MEM_SPEC_INTERP.
  Module FinMemInterp := Memory64BitIntptr.MEM_SPEC_INTERP.

  Module InfLP := InterpreterStackBigIntptr.LP.
  Module FinLP := InterpreterStack64BitIntptr.LP.

  Module EC2 := EventConvert FinLP InfLP FinToInfAddrConvert InfToFinAddrConvert FinLP.Events InfLP.Events.
  Module DVC2 := EC2.DVC.

  Module DVCS := DVConvertSafe FinLP InfLP FinToInfAddrConvert InfToFinAddrConvert FinToInfAddrConvertSafe FinToInfIntptrConvertSafe FinLP.Events InfLP.Events DVC2 DVC1.
  Import DVCS.

  (* Could not put with the other conversions, need to know what memory structures like MemState are *)
  Definition convert_SByte (sb1 : MemoryBigIntptr.MP.BYTE_IMPL.SByte) : OOM (Memory64BitIntptr.MP.BYTE_IMPL.SByte).
    destruct sb1.
    refine (uv' <- EC.DVC.uvalue_convert_strict uv;;
            idx' <- EC.DVC.uvalue_convert_strict idx;;
            ret (FiniteSizeof.mkUByte LLVMParams64BitIntptr.Events.DV.uvalue uv' dt idx' sid)).
  Defined.

  Definition lift_SByte (sb1 : Memory64BitIntptr.MP.BYTE_IMPL.SByte) : MemoryBigIntptr.MP.BYTE_IMPL.SByte.
    destruct sb1.
    remember (EC2.DVC.uvalue_convert_strict uv).
    pose proof uvalue_convert_strict_safe uv as [uv_i [CONV REVCONV]].
    pose proof (uvalue_convert_strict_safe idx) as [idx_i [CONV_idx REVCONV_idx]].
    exact (FiniteSizeof.mkUByte LLVMParams64BitIntptr.Events.DV.uvalue uv_i dt idx_i sid).
    refine (uv' <- EC2.DVC.uvalue_convert_strict uv;;
            idx' <- EC2.DVC.uvalue_convert_strict idx;;
            ret (FiniteSizeof.mkUByte LLVMParams64BitIntptr.Events.DV.uvalue uv' dt idx' sid)).
  Defined.

  Definition convert_mem_byte (mb1 : InfMemMMSP.mem_byte) : OOM (FinMemMMSP.mem_byte).
    destruct mb1.
    refine (s' <- convert_SByte s;;
            ret _).

    constructor.
    apply s'.
    apply a.
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

  Definition convert_Frame (f : InfMemMMSP.Frame) : OOM (FinMemMMSP.Frame).
    induction f.
    - exact (ret []).
    - refine (a' <- InfToFinAddrConvert.addr_convert a;;
              f' <- IHf;;
              ret (a' :: f')).
  Defined.

  Definition convert_FrameStack (fs : InfMemMMSP.FrameStack) : OOM (FinMemMMSP.FrameStack).
    induction fs.
    - refine (f' <- convert_Frame f;;
              ret (FinMemMMSP.Singleton f')).
    - refine (f' <- convert_Frame f;;
              fs' <- IHfs;;
              ret (FinMemMMSP.Snoc fs' f')).
  Defined.

  Definition convert_Block (b : InfMemMMSP.Block) : OOM (FinMemMMSP.Block)
    := map_monad InfToFinAddrConvert.addr_convert b.

  Definition convert_Heap (h : InfMemMMSP.Heap) : OOM (FinMemMMSP.Heap).
    refine (blocks <- map_monad _ (IntMaps.IM.elements h);;
            ret (IntMaps.IP.of_list blocks)).

    refine (fun '(ix, b) =>
              b' <- convert_Block b;;
              ret (ix, b')).
  Defined.

  Definition convert_memory_stack (ms1 : InfMemMMSP.memory_stack) : OOM (FinMemMMSP.memory_stack).
    destruct ms1 as [mem fs h].
    refine (mem' <- convert_memory mem;;
            fs' <- convert_FrameStack fs;;
            h' <- convert_Heap h;;
            ret _).

    constructor; auto.
  Defined.

  Definition convert_MemState (m1 : InfMem.MMEP.MMSP.MemState) : OOM (FinMem.MMEP.MMSP.MemState).
    destruct m1 as [ms pr].
    refine (ms' <- convert_memory_stack ms;;
            ret _).

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
                   (MemState_refine × (eq × (local_refine_strict × stack_refine_strict × (global_refine_strict × EC.DVC.dvalue_refine_strict))))
                   t t' (OOM:=OOME).

  Definition model_E1E2_L3_orutt_strict p1 p2 :=
    L3_E1E2_orutt_strict
      (TopLevelBigIntptr.model_oom_L3 p1)
      (TopLevel64BitIntptr.model_oom_L3 p2).

  Definition get_inf_tree :
    forall (t_fin2 : itree L3 (FinMem.MMEP.MMSP.MemState * (MemPropT.store_id * (local_env * @stack local_env * res_L1)))), itree InfLP.Events.L3 TopLevelBigIntptr.res_L6.
  Proof.
    cofix CIH.
    intros t_fin2.
    inversion t_fin2.
    inversion _observe.
    - (* Ret *)
      refine (ret _).
      destruct r as [ms [sid [[lid s] [genv res]]]].
      constructor.
      Unset Printing Notations.
      unfold TopLevelBigIntptr.res_L6.
      apply (ret (if r then 1 else 0)).
    - (* Tau *)
      apply go.
      apply TauF.
      apply CIH.
      apply t.
    - (* Vis *)
      inversion e; subst.
      rename H into r.
      apply go.
      apply (VisF (nat_ev (if r then 1 else 0))).
      intros n. (* Result *)
      apply CIH.
      apply (if Nat.eqb n 0 then k false else if Nat.eqb n 1 then k true else k false).

    - (* Ret *)
      cbn.
      

  Defined.

  Lemma model_E1E2_23_orutt_strict :
    forall t1 t2 sid ms1 ms2,
      L2_E1E2_orutt_strict t1 t2 ->
      MemState_refine ms1 ms2 ->
      L3_E1E2_orutt_strict (InfMemInterp.interp_memory_prop eq t1 sid ms1) (FinMemInterp.interp_memory_prop eq t2 sid ms2).
  Proof.
    intros t_inf t_fin sid ms1 ms2 REL MSR.
    (* red in REL. *)

    unfold L3_E1E2_orutt_strict.
    intros t_fin2 FIN_HANDLED.

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
