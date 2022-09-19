From Vellvm Require Import
     TopLevel
     TopLevelRefinements
     Refinement
     Utils.Monads
     Utils.PropT
     Utils.Tactics
     Utils.MonadEq1Laws
     Utils.InterpProp
     Theory.DenotationTheory
     Theory.InterpreterMCFG
     Handlers.MemoryModelImplementation.

From ITree Require Import
     ITree
     Eq
     Basics.

From Coq Require Import
     ZArith.

From ExtLib Require Import
     Monads.

Import MonadNotation.
Import DynamicTypes.

Require Import Morphisms.
Require Import Paco.paco.

Module Infinite.
  Import TopLevelBigIntptr.
  Import TopLevelRefinementsBigIntptr.
  Import DenotationTheoryBigIntptr.
  Import MCFGTheoryBigIntptr.
  Import MemoryBigIntptrInfiniteSpec.
  Import MemoryBigIntptrInfiniteSpecHelpers.
  Import D.

  Import Global.
  Import Local.
  Import Stack.

  Import MCFGTactics.

  Import Global.
  Import InterpretationStack.
  Import InterpreterStackBigIntptr.
  Import MEM.
  Import MEM_SPEC_INTERP.

  Import SemNotations.
  Import InterpFacts.
  Import LLVMEvents.
  Import LLVMAst.
  Import CFG.

  Import List.
  Import ListNotations.
  Require Import Coq.Strings.String.

  Definition alloc_code : code dtyp :=
    [ (IId (Name "ptr"), INSTR_Alloca (DTYPE_I 64%N) None None)
    ].

  Definition ptoi_code : code dtyp :=
    [ (IId (Name "ptr"), INSTR_Alloca (DTYPE_I 64%N) None None);
      (IId (Name "i"), INSTR_Op (OP_Conversion Ptrtoint DTYPE_Pointer (EXP_Ident (ID_Local (Name "ptr"))) (DTYPE_IPTR)))
    ].

  Definition ret_code : code dtyp :=
    [].

  Definition alloc_block : block dtyp :=
    {|
      blk_id := Name "";
      blk_phis := [];
      blk_code := alloc_code;
      blk_term := TERM_Ret (DTYPE_I 1%N, EXP_Bool true);
      blk_comments := None;
    |}.

  Definition ptoi_block : block dtyp :=
    {|
      blk_id := Name "";
      blk_phis := [];
      blk_code := ptoi_code;
      blk_term := TERM_Ret (DTYPE_I 1%N, EXP_Bool true);
      blk_comments := None;
    |}.

  Definition ret_block : block dtyp :=
    {|
      blk_id := Name "";
      blk_phis := [];
      blk_code := ret_code;
      blk_term := TERM_Ret (DTYPE_I 1%N, EXP_Bool true);
      blk_comments := None;
    |}.

  Definition block_to_dvalue {E} `{FailureE -< E}
             (t : itree E (block_id + uvalue)) : itree E dvalue :=
    b_or_v <- t;;
    match b_or_v with
    | inl _ => raise "id"
    | inr uv =>
        match uvalue_to_dvalue uv with
        | inl msg => raise msg
        | inr dv => ret dv
        end
    end.

  Definition denote_program prog :=
    block_to_dvalue (denote_block prog (Name "blk")).

  Definition alloc_tree : itree instr_E dvalue :=
    denote_program alloc_block.

  Definition ptoi_tree : itree instr_E dvalue :=
    denote_program ptoi_block.

  Definition ret_tree : itree instr_E dvalue :=
    denote_program ret_block.

  Definition t_alloc : itree L0 dvalue
    := trigger (Alloca (DTYPE_I 64%N));; ret (DVALUE_I1 one).

  Definition t_ret : itree L0 dvalue
    := ret (DVALUE_I1 one).

  (* Remove allocation in infinite language *)
  Lemma remove_alloc:
    forall genv lenv stack sid m,
      refine_L6 (interp_mcfg4 TT TT t_alloc genv (lenv, stack) sid m) (interp_mcfg4 TT TT t_ret genv (lenv, stack) sid m).
  Proof.
    intros genv lenv stack sid m.
    unfold refine_L6.
    intros t' INTERP.
    exists t'.
    split; [| reflexivity].
    - cbn in *.

      (* TODO: Should make lemmas about ret, etc for interp_mcfg4 *)
      unfold interp_mcfg4 in *.
      unfold model_undef in *.

      destruct INTERP as [t_pre [INTERP UNDEF]].

      (* TODO: Need something about interp_memory_prop being proper with respect to eutt? *)
      (* Not sure if this is exactly what it should be *)

      Set Nested Proofs Allowed.
      #[global] Instance interp_mem_prop_Proper3 :
        forall {E F} `{FAIL : FailureE -< F} `{UB : UBE -< F} `{OOM : OOME -< F}
          {R} (RR : R -> R -> Prop),
          Proper (eutt eq ==> eq ==> eq ==> eq ==> iff) (@interp_memory_prop E F FAIL UB OOM R RR).
      Proof.
        intros E F FAIL UB OOM R RR.
        unfold interp_memory_prop.
        unfold Proper, respectful.
        intros x y H x0 y0 H0 x1 y1 H1 x2 y2 H2.
        subst.
        split; intros INTERP.
        - eapply interp_prop_eutt_Proper_impl.
          + admit.
          + eauto.
          + reflexivity.
          + auto.
        - eapply interp_prop_eutt_Proper_impl.
          + admit.
          + symmetry. apply H.
          + reflexivity.
          + auto.
      Admitted.

      setoid_rewrite interp_intrinsics_ret in INTERP.
      setoid_rewrite interp_global_ret in INTERP.
      setoid_rewrite interp_local_stack_ret in INTERP.

      (* TODO: Turn this into an interp_memory_prop lemma *)
      unfold interp_memory_prop in INTERP.
      cbn in INTERP.

      apply interp_prop_ret_inv in INTERP.
      destruct INTERP as [r2 [INTERP_TT EQ]].

      assert (ITree.map (fun '(_, (_, x)) => x) t_pre ≈ Ret ((fun '(_, (_, x)) => x) (m, (sid, r2)))).
      auto.
      clear EQ.
      rename H into EQ.

      Lemma ret_map_itree :
        forall Eff A B (f : A -> B) (t : itree Eff A) (a : A),
          ITree.map f t ≈ ret (f a) ->
          exists a', t ≈ ret a' /\ f a' = f a.
      Proof.
      Admitted.

      Class KSPEC_WF {E F} (h_spec : forall T : Type, E T -> PropT F T)
            (k_spec : forall T R : Type, E T -> itree F T -> (T -> itree F R) -> itree F R -> Prop) : Type
        := k_spec_WF_class : k_spec_WF h_spec k_spec.

      #[global] Instance interp_prop_eutt_Proper2:
        forall {E F : Type -> Type} {h_spec : forall T : Type, E T -> PropT F T}
          {k_spec : forall T R : Type, E T -> itree F T -> (T -> itree F R) -> itree F R -> Prop}
          `{WF : @KSPEC_WF _ _ h_spec k_spec},
          forall (R : Type) (RR : Relation_Definitions.relation R),
            Proper (eutt eq ==> eutt eq ==> iff) (interp_prop h_spec k_spec R RR).
      Proof.
        intros E F h_spec k_spec H R RR.
        unfold Proper, respectful.
        intros x y H0 x0 y0 H1.
        split; intros H2.
        - eapply interp_prop_eutt_Proper; eauto.
          symmetry; auto.
          symmetry; auto.
        - eapply interp_prop_eutt_Proper; eauto.
      Qed.

      #[global] Instance KSPEC_poison :
        KSPEC_WF
          (case_ (E_trigger_prop (F:=OOME +' UBE +' DebugE +' FailureE))
                 (case_ PickUvalue_handler (F_trigger_prop (F:=OOME +' UBE +' DebugE +' FailureE))))
          (@pick_uvalue_k_spec ExternalCallE (OOME +' UBE +' DebugE +' FailureE)).
      Proof.
        apply k_spec_WF_pick_uvalue_k_spec.
      Defined.

      #[global] Instance KSPEC_memory {sid m} :
        KSPEC_WF
          (fun (T : Type)
             (e : (ExternalCallE +'
                                    LLVMParamsBigIntptr.Events.IntrinsicE +'
                                                                             LLVMParamsBigIntptr.Events.MemoryE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE) T)
             (t : itree (ExternalCallE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE) T) =>
             exists (sid' : store_id) (ms' : MMEP.MMSP.MemState),
               interp_memory_prop_h e sid m (ITree.map (fun x : T => (ms', (sid', x))) t))
          (@memory_k_spec ExternalCallE (PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)).
      Proof.
        apply k_spec_WF_memory_k_spec.
      Defined.

      apply ret_map_itree in EQ as ((m', (s', a')) & EQ & FEQ).

      rewrite EQ in UNDEF.
      cbn in UNDEF.

      cbn in EQ.
      subst.

      Import MMEP.MMSP.
      Import MemoryBigIntptr.MMEP.MMSP.
      epose proof allocate_dtyp_spec_can_always_succeed m m (mkMemState (ms_memory_stack m) (next_provenance (ms_provenance m))) (DTYPE_I 64) _ _ _ _ _ as (ms_final & addr & ALLOC).

      exists (Ret2 s' m' (lenv, stack, (genv, DVALUE_Addr addr))). (* Not sure if should be s' or sid, and m' or m *) (* Used to be r2 *)

      split.
      + go.
        rewrite bind_trigger.
        repeat setoid_rewrite bind_ret_l.
        setoid_rewrite interp_local_stack_ret.
        repeat setoid_rewrite bind_ret_l.

        (* LEMMA *)
        unfold interp_memory_prop.
        cbn.

        Opaque MMEP.MemSpec.allocate_dtyp_spec.

        Lemma interp_prop_vis :
          forall {E F X} (h_spec : E ~> PropT F) k_spec R RR
            (e : E X) kk t,
            interp_prop h_spec k_spec R RR (Vis e kk) t <->
            (x <- h_spec X e;;
            interp_prop h_spec k_spec R RR (kk x)) t. (* Do I need to use k_spec anywhere...? *)
        Proof.
        Admitted.

        eapply interp_prop_vis.
        cbn.
        unfold bind_PropT.

        (* was just ret r2... *)
        exists (ITree.map (fun '(_, (_, x)) => x) (Ret (lenv, (stack, DVALUE_Addr addr)))).
        exists (fun dv => ret (lenv, stack, (genv, dv))).
        split; [|split].
        * exists sid. exists ms_final.
          unfold my_handle_memory_prop.
          unfold MemPropT_lift_PropT_fresh.
          right; right; right.
          do 3 eexists.
          split.
          -- do 2 rewrite map_ret; cbn.
             reflexivity.
          -- cbn.
             exists ms_final. exists addr.
             tauto.
        * rewrite map_ret.
          setoid_rewrite map_bind.
          rewrite bind_ret_l.
          rewrite map_ret.
          reflexivity.
        * intros a RET.
          rewrite map_ret in RET.
          apply Returns_Ret in RET.
          subst.
          cbn.
          go.
          eapply interp_prop_ret_refine; eauto.
      + apply interp_prop_ret_inv in UNDEF as (r3 & R3 & T').
        unfold model_undef_h.
        eapply interp_prop_eutt_Proper2.
        reflexivity.
        eauto.
        cbn.
        eapply interp_prop_ret_refine; eauto.

        Unshelve.
        exact initial_provenance.
        exact 0%N.
        cbn.
        all: admit.
  Admitted.

  Definition instr_E_to_L0 {T : Type} : instr_E T -> itree L0 T :=
    fun (e : instr_E T) =>
      match e with
      | inl1 call =>
          match call with
          | Call dt fv args =>
              raise "call"
          end
      | inr1 e0 =>
          trigger (inr1 e0)
      end.

  Definition interp_instr_E_to_L0 :=
    interp (@instr_E_to_L0).

  Import TranslateFacts.
  Import StateFacts.

  Lemma remove_alloc_block :
    forall genv lenv stack sid m,
      refine_L6 (interp_mcfg4 TT TT (interp_instr_E_to_L0 _ alloc_tree) genv (lenv, stack) sid m) (interp_mcfg4 TT TT (interp_instr_E_to_L0 _ ret_tree) genv (lenv, stack) sid m).
  Proof.
    intros genv lenv stack sid m.
    unfold refine_L6.
    intros t' INTERP.
    exists t'.
    split; [| reflexivity].
    - cbn in *.

      (* TODO: Should make lemmas about ret, etc for interp_mcfg4 *)
      unfold interp_mcfg4 in *.
      unfold model_undef in *.

      destruct INTERP as [t_pre [INTERP UNDEF]].

      go_in INTERP.
      repeat setoid_rewrite bind_ret_l in INTERP.
      rewrite TranslateFacts.translate_ret in INTERP.
      repeat setoid_rewrite bind_ret_l in INTERP.
      cbn in INTERP.
      setoid_rewrite interp_ret in INTERP.
      setoid_rewrite interp_intrinsics_ret in INTERP.
      setoid_rewrite interp_global_ret in INTERP.
      setoid_rewrite interp_local_stack_ret in INTERP.

      repeat setoid_rewrite bind_ret_l.
      repeat setoid_rewrite bind_bind.
      repeat setoid_rewrite bind_ret_l.

      (* TODO: Turn this into an interp_memory_prop lemma *)
      unfold interp_memory_prop in INTERP.
      cbn in INTERP.

      apply interp_prop_ret_inv in INTERP.
      destruct INTERP as [r2 [INTERP_TT EQ]].

      assert (ITree.map (fun '(_, (_, x)) => x) t_pre ≈ Ret ((fun '(_, (_, x)) => x) (m, (sid, r2)))).
      auto.
      clear EQ.
      rename H into EQ.

      apply ret_map_itree in EQ as ((m', (s', a')) & EQ & FEQ).

      rewrite EQ in UNDEF.
      cbn in UNDEF.

      cbn in EQ.
      subst.

      Import MMEP.MMSP.
      Import MemoryBigIntptr.MMEP.MMSP.
      Import MapMonadExtra.
      epose proof allocate_dtyp_spec_can_always_succeed m m (mkMemState (ms_memory_stack m) (next_provenance (ms_provenance m))) (DTYPE_I 64) _ _ _ _ _ as (ms_final & addr & ALLOC).

      exists (Ret2 s' m' (lenv, stack, (genv, DVALUE_Addr addr))). (* Not sure if should be s' or sid, and m' or m *) (* Used to be r2 *)

      split.
      + rewrite interp_bind with (f:=@instr_E_to_L0);
          rewrite interp_trigger; cbn; rewrite subevent_subevent.
        go.
        repeat setoid_rewrite bind_ret_l.
        setoid_rewrite interp_local_stack_ret.
        repeat setoid_rewrite bind_ret_l.

        (* LEMMA *)
        unfold interp_memory_prop.
        cbn.


        Opaque MMEP.MemSpec.allocate_dtyp_spec.

        rewrite bind_trigger.
        eapply interp_prop_vis.
        cbn.
        unfold bind_PropT.

        (* was just ret r2... *)
        exists (ITree.map (fun '(_, (_, x)) => x) (Ret (lenv, (stack, DVALUE_Addr addr)))).
        exists (fun dv => ret (lenv, stack, (genv, dv))).
        split; [|split].
        * exists sid. exists ms_final.
          unfold my_handle_memory_prop.
          unfold MemPropT_lift_PropT_fresh.
          right; right; right.
          do 3 eexists.
          split.
          -- do 2 rewrite map_ret; cbn.
             reflexivity.
          -- cbn.
             exists ms_final. exists addr.
             tauto.
        * rewrite map_ret.
          setoid_rewrite map_bind.
          rewrite bind_ret_l.
          rewrite map_ret.
          reflexivity.
        * intros a RET.
          rewrite map_ret in RET.
          apply Returns_Ret in RET.
          subst.
          cbn.
          go.
          rewrite interp_bind with (f:=@instr_E_to_L0);
            rewrite interp_trigger; cbn; rewrite subevent_subevent.
          go.
          rewrite map_ret.
          go.
          cbn.
          rewrite interp_ret.
          go.
          eapply interp_prop_ret_refine; eauto.
      + apply interp_prop_ret_inv in UNDEF as (r3 & R3 & T').
        unfold model_undef_h.
        eapply interp_prop_eutt_Proper2.
        reflexivity.
        eauto.
        cbn.
        eapply interp_prop_ret_refine; eauto.

        Unshelve.
        exact initial_provenance.
        exact 0%N.
        cbn.
        all: admit.
  Admitted.

  Lemma remove_alloc_ptoi_block :
    forall genv lenv stack sid m,
      refine_L6 (interp_mcfg4 TT TT (interp_instr_E_to_L0 _ ptoi_tree) genv (lenv, stack) sid m) (interp_mcfg4 TT TT (interp_instr_E_to_L0 _ ret_tree) genv (lenv, stack) sid m).
  Proof.
    intros genv lenv stack sid m.
    unfold refine_L6.
    intros t' INTERP.
    exists t'.
    split; [| reflexivity].
    - cbn in *.

      (* TODO: Should make lemmas about ret, etc for interp_mcfg4 *)
      unfold interp_mcfg4 in *.
      unfold model_undef in *.

      destruct INTERP as [t_pre [INTERP UNDEF]].

      go_in INTERP.
      repeat setoid_rewrite bind_ret_l in INTERP.
      rewrite TranslateFacts.translate_ret in INTERP.
      repeat setoid_rewrite bind_ret_l in INTERP.
      cbn in INTERP.
      setoid_rewrite interp_ret in INTERP.
      setoid_rewrite interp_intrinsics_ret in INTERP.
      setoid_rewrite interp_global_ret in INTERP.
      setoid_rewrite interp_local_stack_ret in INTERP.

      (* TODO: Turn this into an interp_memory_prop lemma *)
      unfold interp_memory_prop in INTERP.
      cbn in INTERP.

      apply interp_prop_ret_inv in INTERP.
      destruct INTERP as [r2 [INTERP_TT EQ]].

      assert (ITree.map (fun '(_, (_, x)) => x) t_pre ≈ Ret ((fun '(_, (_, x)) => x) (m, (sid, r2)))).
      auto.
      clear EQ.
      rename H into EQ.

      apply ret_map_itree in EQ as ((m', (s', a')) & EQ & FEQ).

      rewrite EQ in UNDEF.
      cbn in UNDEF.

      cbn in EQ.
      subst.

      epose proof allocate_dtyp_spec_can_always_succeed m _ _ (DTYPE_I 64) _ _ _ _ _ as (ms_final & addr & ALLOC).

      exists (Ret2 s' m' (lenv, stack, (genv, DVALUE_Addr addr))). (* Not sure if should be s' or sid, and m' or m *) (* Used to be r2 *)

      split.
      + 
        Ltac go_setoid :=
          repeat match goal with
                 | |- context [interp_intrinsics (ITree.bind _ _)] => setoid_rewrite interp_intrinsics_bind
                 | |- context [interp_global (ITree.bind _ _)] => setoid_rewrite interp_global_bind
                 | |- context [interp_local_stack (ITree.bind _ _)] => setoid_rewrite interp_local_stack_bind
                 (* | |- context [interp_memory (ITree.bind _ _)] => setoid_rewrite interp_memory_bind *)
                 | |- context [interp_intrinsics (trigger _)] => setoid_rewrite interp_intrinsics_trigger; cbn; rewrite ?subevent_subevent
                 | |- context [interp_intrinsics (ITree.trigger _)] => setoid_rewrite interp_intrinsics_trigger; cbn; rewrite ?subevent_subevent
                 | |- context [interp_global (trigger _)] => setoid_rewrite interp_global_trigger; cbn; rewrite ?subevent_subevent
                 | |- context [interp_global (ITree.trigger _)] => setoid_rewrite interp_global_trigger; cbn; rewrite ?subevent_subevent
                 | |- context [interp_local_stack (trigger _)] => setoid_rewrite interp_local_stack_trigger; cbn; rewrite ?subevent_subevent
                 | |- context [interp_local_stack (ITree.trigger _)] => setoid_rewrite interp_local_stack_trigger; cbn; rewrite ?subevent_subevent
                 | |- context [ITree.bind (ITree.bind _ _) _] => setoid_rewrite bind_bind
                 | |- context [interp_intrinsics (Ret _)] => setoid_rewrite interp_intrinsics_ret
                 | |- context [interp_global (Ret _)] => setoid_rewrite interp_global_ret
                 | |- context [interp_local_stack (Ret _)] => setoid_rewrite interp_local_stack_ret
                 (* | |- context [interp_memory (Ret _)] => setoid_rewrite interp_memory_ret *)
                 | |- context [ITree.bind (Ret _) _] => setoid_rewrite bind_ret_l
                 | |- context [translate _ (Ret _)] => setoid_rewrite translate_ret
                 | |- context [interp _ (trigger _)] => setoid_rewrite interp_trigger
                 | |- context [interp _ (ITree.bind _ _)] => setoid_rewrite interp_bind
                 | |- context [interp _ (Ret _)] => setoid_rewrite interp_ret
                 | |- context [map _ (ret _)] => setoid_rewrite map_ret
                 | |- context [ITree.map _ (Ret _)] => setoid_rewrite map_ret
                 | |- context [translate _ (trigger _)] => setoid_rewrite translate_trigger; cbn; rewrite ?subevent_subevent
                 | |- context [translate _ (ITree.trigger _)] => setoid_rewrite translate_trigger; cbn; rewrite ?subevent_subevent
                 | |- context [translate _ (ITree.bind _ _)] => setoid_rewrite translate_bind
                 end.

        Ltac go_prime :=
          repeat match goal with
                 | |- context [interp_intrinsics (ITree.bind _ _)] => rewrite interp_intrinsics_bind
                 | |- context [interp_global (ITree.bind _ _)] => rewrite interp_global_bind
                 | |- context [interp_local_stack (ITree.bind _ _)] => rewrite interp_local_stack_bind
                 (* | |- context [interp_memory (ITree.bind _ _)] => rewrite interp_memory_bind *)
                 | |- context [interp_intrinsics (trigger _)] => rewrite interp_intrinsics_trigger; cbn; rewrite ?subevent_subevent
                 | |- context [interp_intrinsics (ITree.trigger _)] => rewrite interp_intrinsics_trigger; cbn; rewrite ?subevent_subevent
                 | |- context [interp_global (trigger _)] => rewrite interp_global_trigger; cbn; rewrite ?subevent_subevent
                 | |- context [interp_global (ITree.trigger _)] => rewrite interp_global_trigger; cbn; rewrite ?subevent_subevent
                 | |- context [interp_local_stack (trigger _)] => rewrite interp_local_stack_trigger; cbn; rewrite ?subevent_subevent
                 | |- context [interp_local_stack (ITree.trigger _)] => rewrite interp_local_stack_trigger; cbn; rewrite ?subevent_subevent
                 | |- context [ITree.bind (ITree.bind _ _) _] => rewrite bind_bind
                 | |- context [interp_intrinsics (Ret _)] => rewrite interp_intrinsics_ret
                 | |- context [interp_global (Ret _)] => rewrite interp_global_ret
                 | |- context [interp_local_stack (Ret _)] => rewrite interp_local_stack_ret
                 (* | |- context [interp_memory (Ret _)] => rewrite interp_memory_ret *)
                 | |- context [ITree.bind (Ret _) _] => rewrite bind_ret_l
                 | |- context [translate _ (Ret _)] => rewrite translate_ret
                 | |- context [interp _ (trigger _)] => rewrite interp_trigger
                 | |- context [interp _ (ITree.bind _ _)] => rewrite interp_bind
                 | |- context [interp _ (Ret _)] => rewrite interp_ret
                 | |- context [map _ (ret _)] => rewrite map_ret
                 | |- context [ITree.map _ (Ret _)] => rewrite map_ret
                 | |- context [translate _ (trigger _)] => rewrite translate_trigger; cbn; rewrite ?subevent_subevent
                 | |- context [translate _ (ITree.trigger _)] => rewrite translate_trigger; cbn; rewrite ?subevent_subevent
                 | |- context [translate _ (ITree.bind _ _)] => rewrite translate_bind
                 end.

        unfold interp_instr_E_to_L0; cbn.
        repeat (go_setoid; cbn). (* This is sloooow *)

        setoid_rewrite bind_trigger.

        (* LEMMA *)
        unfold interp_memory_prop.
        cbn.

        eapply interp_prop_vis.
        cbn.
        unfold bind_PropT.

        (* was just ret r2... *)
        exists (ITree.map (fun '(_, (_, x)) => x) (Ret (lenv, (stack, DVALUE_Addr addr)))).
        exists (fun dv => ret (lenv, stack, (genv, dv))).
        split; [|split].
        * exists sid. exists ms_final.
          unfold my_handle_memory_prop.
          unfold MemPropT_lift_PropT_fresh.
          right; right; right.
          do 3 eexists.
          split.
          -- do 2 rewrite map_ret; cbn.
             reflexivity.
          -- cbn.
             exists ms_final. exists addr.
             tauto.
        * rewrite map_ret.
          setoid_rewrite map_bind.
          rewrite bind_ret_l.
          rewrite map_ret.
          reflexivity.
        * intros a RET.
          rewrite map_ret in RET.
          apply Returns_Ret in RET.
          subst.
          cbn.

          eapply interp_prop_ret_refine; eauto.
      + apply interp_prop_ret_inv in UNDEF as (r3 & R3 & T').
        unfold model_undef_h.

        eapply interp_prop_eutt_Proper2.
        reflexivity.
        apply T'.

        cbn.
        eapply interp_prop_ret_refine; eauto.
  Admitted.

  (* Add allocation in infinite language *)
  Lemma add_alloc :
    forall genv lenv stack sid m,
      refine_L6 (interp_mcfg4 eq eq t_ret genv (lenv, stack) sid m) (interp_mcfg4 eq eq t_alloc genv (lenv, stack) sid m).
  Proof.
    intros genv lenv stack sid m.
    unfold refine_L6.
    intros t' INTERP.

    (* either t' succeeds and we're eqv some ret like t_ret...
       or t' runs out of memory because it's an allocation.
     *)

    unfold interp_mcfg4 in *.
    unfold model_undef in *.

    destruct INTERP as [t_pre [INTERP UNDEF]].
    unfold interp_memory_prop in INTERP.
    unfold t_alloc in INTERP.
    cbn in INTERP.
    go_in INTERP.
    rewrite bind_trigger in INTERP.
    repeat setoid_rewrite bind_ret_l in INTERP.
    setoid_rewrite interp_local_stack_ret in INTERP.
    repeat setoid_rewrite bind_ret_l in INTERP.
    
    setoid_rewrite interp_intrinsics_ret in INTERP.
    setoid_rewrite interp_global_ret in INTERP.
    setoid_rewrite interp_local_stack_ret in INTERP.

    rewrite interp_prop_vis in INTERP.

    (* Maybe write a lemma to unfold this... *)
    cbn in INTERP.
    Import MMEP.MemSpec.
    unfold my_handle_memory_prop in INTERP.
    Opaque bind ret.
    Opaque MMEP.MemSpec.allocate_dtyp_spec.
    cbn in INTERP.
    unfold bind_PropT in INTERP.
    destruct INTERP as [ta [k [ALLOC [K INTERP]]]].
    destruct ALLOC as [sid' [ms' ALLOC]].

    Import MemTheory.
    pose proof allocate_dtyp_spec_inv m (DTYPE_I 64) as ALLOCINV.
    forward ALLOCINV. intros CONTRA; inv CONTRA.

    Transparent bind ret.
    Transparent MMEP.MemSpec.allocate_dtyp_spec.

    (* TODO: move this *)
    Arguments MMEP.MemSpec.allocate_dtyp_spec dt : simpl never.

    cbn in ALLOC.
    unfold MemPropT_lift_PropT_fresh in ALLOC.
    cbn in ALLOC.

    Transparent bind ret.
    Transparent MMEP.MemSpec.allocate_dtyp_spec.

    destruct ALLOC as [ALLOC_UB | [ALLOC_ERR | [ALLOC_OOM | ALLOC_SUC]]].
    - (* UB *)
      destruct ALLOC_UB as [ub_msg [ALLOC_UB | [sab [a [ALLOC_UB []]]]]].
      apply ALLOCINV in ALLOC_UB.
      destruct ALLOC_UB as [[ms_final [ptr ALLOC_UB]] | [oom_msg ALLOC_UB]];
        inv ALLOC_UB.
    - (* ERR *)
      destruct ALLOC_ERR as [err_msg [MAP [spec_msg [ALLOC_ERR | [sab [a [ALLOC_ERR []]]]]]]].
      apply ALLOCINV in ALLOC_ERR.
      destruct ALLOC_ERR as [[ms_final [ptr ALLOC_ERR]] | [oom_msg ALLOC_ERR]];
        inv ALLOC_ERR.
    - (* OOM *)
      destruct ALLOC_OOM as [err_msg [MAP [spec_msg [ALLOC_OOM | [sab [a [ALLOC_OOM []]]]]]]].
      apply ALLOCINV in ALLOC_OOM.
      destruct ALLOC_OOM as [[ms_final [ptr ALLOC_OOM]] | [oom_msg ALLOC_OOM]];
        inv ALLOC_OOM.

      Import Raise.
      apply raiseOOM_map_itree_inv in MAP.
      rewrite MAP in K.
      rewrite (@rbm_raise_bind _ _ _ _ _ (RaiseBindM_OOM _)) in K.
      apply raiseOOM_map_itree_inv in K.

      (* TODO: why can't I just do this rewrite? *)
      rewrite K in UNDEF.

      (* TODO: should be clear that t' is raiseOOM as well *)
      (* Should be able to have a lemma for that *)
      assert (t' ≈ raiseOOM err_msg) as T' by admit.

      exists (Ret5 genv (lenv, stack) sid m (DVALUE_I1 DynamicValues.Int1.one)).
      split.
      +  exists (Ret5 genv (lenv, stack) sid m (DVALUE_I1 DynamicValues.Int1.one)).
         (* exists (Ret2 genv (lenv, stack) (DVALUE_I1 DynamicValues.Int1.one)). *)
         split.
         * cbn.
           go_prime.

           (* TODO: ret lemma for interp_memory_prop *)
           unfold interp_memory_prop.
           cbn.
           rewrite map_ret.
           eapply interp_prop_ret_refine; reflexivity.
         * red.
           eapply interp_prop_ret_pure; eauto.
      + (* TODO: Move this *)
        Import Relation_Definitions.
        #[global] Instance refine_OOM_h_eutt_Proper {T : Type} {RR : relation T} {E F}:
          Proper (eutt eq ==> eutt eq ==> iff) (@refine_OOM_h E F T RR).
        Proof.
          unfold Proper, respectful.
          intros x1 x2 X y1 y2 Y.
          split; intros REFINE.
        Admitted.

        rewrite T'.
        eapply refine_oom_h_raise_oom; typeclasses eauto.
    - (* Success *)
      exists (Ret5 genv (lenv, stack) sid m (DVALUE_I1 DynamicValues.Int1.one)).
      split.
      +  exists (Ret5 genv (lenv, stack) sid m (DVALUE_I1 DynamicValues.Int1.one)).
         (* exists (Ret2 genv (lenv, stack) (DVALUE_I1 DynamicValues.Int1.one)). *)
         split.
         * cbn.
           go_prime.

           (* TODO: ret lemma for interp_memory_prop *)
           unfold interp_memory_prop.
           cbn.
           rewrite map_ret.
           eapply interp_prop_ret_refine; reflexivity.
         * red.
           eapply interp_prop_ret_pure; eauto.
      + (* t' is the successful result of t_alloc *)
        destruct ALLOC_SUC as [sid'' [ ms'' [x [MAP ALLOC_SUC]]]].        
        destruct ALLOC_SUC as [ms''' [a [ALLOC [MEQ XEQ]]]].
        subst.

        Lemma itree_map_ret_inv :
          forall {E X Y} f (t : itree E X) (y : Y),
            ITree.map f t ≈ ret y ->
            exists (x : X), t ≈ ret x /\ f x = y.
        Proof.
        Admitted.

        apply itree_map_ret_inv in MAP as [x [TA EQ]].
        rewrite TA in K.
        setoid_rewrite bind_ret_l in K.

        specialize (INTERP x).
        forward INTERP.
        { constructor; auto.
        }

        apply interp_prop_ret_inv in INTERP.
        destruct INTERP as [[lenv' [stack' res']] [R2 K']].
        rewrite K' in K.

        apply itree_map_ret_inv in K.
        destruct K as [[ms'''' [sid'''' [lenv'''' [stack'''' res]]]] [TPRE ENV]].
        inv ENV.

        unfold model_undef_h in UNDEF.

        (* TODO: why can't I just do this rewrite? *)
        rewrite TPRE in UNDEF.

        eapply interp_prop_ret_inv in UNDEF.
        destruct UNDEF as [r2 [RPICK T']].
        destruct r2 as [ms''''' [sid''''' z]].
        rewrite T'.
        cbn.

        inv RPICK.
        inv R2.

        (* Not quite reflexivity... *)
        unfold refine_OOM_h.
        apply interp_prop_ret_refine.
        do 2 red.
        unfold refine_res2, refine_res1.
        repeat constructor; auto.
  Admitted.
End Infinite.

Module Finite.
  Import TopLevel64BitIntptr.
  Import TopLevelRefinements64BitIntptr.
  Import DenotationTheory64BitIntptr.
  Import MCFGTheory64BitIntptr.
  Import D.

  Import Global.
  Import Local.
  Import Stack.

  Import MCFGTactics.

  Import Global.
  Import ESID.

  Definition t_alloc : itree L0 uvalue
    := trigger (Alloca (DTYPE_I 64%N));; ret UVALUE_None.

  Definition t_ret : itree L0 uvalue
    := ret UVALUE_None.

  (* Add allocation in finite language *)
  Lemma add_alloc :
    forall g l s m,
      refine_L6 (interp_mcfg4 refine_res3 t_ret g (l, s) m) (interp_mcfg4 refine_res3 t_alloc g (l, s) m).
  Proof.
    intros g l s m.
    unfold refine_L6.
    intros t' INTERP.
    Require Import String.
    
    cbn in INTERP.
    unfold interp_mcfg4 in INTERP.

    unfold model_undef in INTERP.
    go_in INTERP.

    rewrite interp_memory_trigger in INTERP.
    cbn in INTERP.
    go_in INTERP.
    cbn in INTERP.

    (* I basically need to show that t' is the same as t_alloc, but
       with a different effects signature..

       I.e., it either OOMs or it returns UVALUE_None
     *)
    pose proof (@allocate_succeeds_or_OOMs (ms_memory_stack m) (DTYPE_I 64)) as SUCFAIL.
    forward SUCFAIL; [intros contra; inversion contra|].

    destruct SUCFAIL as [ALLOC_SUC | ALLOC_OOM].
    - apply ErrSID_succeeds_ErrSID_runs_to with (sid:=ms_sid m) (pr := ms_prov m) in ALLOC_SUC.
      destruct ALLOC_SUC as ((ms' & addr) & sid'' & pr'' & RUNS).
      unfold ErrSID_runs_to in RUNS.
      rewrite RUNS in INTERP.
      cbn in INTERP.
      go_in INTERP.
      cbn in INTERP.
      go_in INTERP.
      cbn in INTERP.

      apply interp_prop_ret_inv in INTERP.
      destruct INTERP as ((ms'' & (lenv & ls & res)) & REF & RES).

      inversion REF; subst.
      inversion H4; subst.
      inversion H6; subst.

      
      (* Any dv that res concretizes to, UVALUE_None can also
         concretize to...

         This doesn't necessarily tell me that 
       *)

      exists (ret (ms'', (lenv, (ls, res)))).
      cbn.
      split.

      { unfold interp_mcfg4.
        go.

        (* TODO: lemma about model_undef? *)
        unfold model_undef.
        apply interp_prop_ret_refine.
        repeat split; eauto.
      }

      right.
      
      apply OOM.eutt_refine_oom_h.
      typeclasses eauto.
      typeclasses eauto.

      rewrite RES.
      reflexivity.
    - unfold ErrSID_OOMs in ALLOC_OOM.
      specialize (ALLOC_OOM (ms_sid m) (ms_prov m)).
      break_match_hyp; inversion ALLOC_OOM.

      destruct (runErrSID (allocate (ms_memory_stack m) (DTYPE_I 64)) (ms_sid m) (ms_prov m)) eqn:Halloc.
      destruct p.
      assert (s0 = inl o). admit.
      subst.
      destruct o.
      cbn in *.
      go_in INTERP.

      setoid_rewrite Raise.raiseOOM_bind_itree in INTERP.

      eexists.

      split.

      { unfold interp_mcfg4.
        go.

        unfold model_undef.
        apply interp_prop_ret_pure.
        typeclasses eauto.
      }

      right.

      (* TODO: Lemma to get this information from INTERP *)
      assert (t' = LLVMEvents.raiseOOM s0).
      admit.

      rewrite H.

      (* TODO: Lemma about refine_OOM_h and raiseOOM *)
      cbn.
      unfold OOM.refine_OOM_h.

      cbn.
      constructor.
    - cbn.
      unfold interp_mcfg4.
      unfold model_undef.
      go.

      epose proof interp_prop_refl.
      unfold Proper, respectful in *.

      eapply interp_prop_ret_pure; typeclasses eauto.
    - right.
      Import OOM.

      unfold refine_OOM_h.

      Require Import Stack.
      Require Import Global.
      cbn.
      
      (* I basically need to show that t' is the same as t_alloc, but
         with a different effects signature..

         I.e., it either OOMs or it returns UVALUE_None
       *)
      pose proof (@allocate_succeeds_or_OOMs (ms_memory_stack m) (DTYPE_I 64)) as SUCFAIL.
      forward SUCFAIL; [intros contra; inversion contra|].

      destruct SUCFAIL as [ALLOC_SUC | ALLOC_OOM].

      + apply ErrSID_succeeds_ErrSID_runs_to with (sid:=ms_sid m) (pr := ms_prov m) in ALLOC_SUC.
        destruct ALLOC_SUC as ((ms' & addr) & sid'' & pr'' & RUNS).
        unfold ErrSID_runs_to in RUNS.
        rewrite RUNS in INTERP.
        cbn in INTERP.
        go_in INTERP.
        cbn in INTERP.
        go_in INTERP.
        cbn in INTERP.

        apply interp_prop_ret_inv in INTERP.
        destruct INTERP as (r2 & _ & RES).
        rewrite RES.

        cbn.

        (* Won't work... *)
        (* Just need to lift some of this proof and go back and change the existential, I think *)
        
        rewrite bind_ret_l in INTERP.
        rewrite H
          unfold ErrSID_succeeds in ALLOC_SUC.

      + rewrite interp_intrinsics_trigger in INTERP.


      go_in INTERP.

      epose proof interp_prop_Proper_eq.

      eapply interp_prop_Proper_eq in INTERP; try typeclasses eauto.
      2 : {
        go.
        rewrite interp_memory_trigger.
        cbn.
        go.
        cbn.
      }

      setoid_rewrite interp_intrinsics_trigger in INTERP.


      rewrite interp_prop _bind in INTERP.


      
      cbn in GOAL.
      
      setoid_rewrite bind_trigger in INTERP.
      unfolf
      apply OOM.eutt_refine_oom_h; try typeclasses eauto.
      reflexivity.
  Qed.
End Finite.
