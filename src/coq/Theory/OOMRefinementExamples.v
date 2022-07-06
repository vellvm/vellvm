From Vellvm Require Import
     TopLevel
     TopLevelRefinements
     Refinement
     Utils.Monads
     Utils.PropT
     Utils.Tactics
     Utils.MonadEq1Laws
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
          {R} (RR : R -> R -> Prop) a b,
          Proper (eqit eq a b ==> eq ==> eq ==> eq ==> iff) (@interp_memory_prop E F FAIL UB OOM R RR).
      Proof.
        intros E F FAIL UB OOM R RR a b.
        unfold interp_memory_prop.
        unfold Proper, respectful.
        intros x y H x0 y0 H0 x1 y1 H1 x2 y2 H2.
        subst.
        rewrite H.
        reflexivity.
      Qed.

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

      apply ret_map_itree in EQ as ((m', (s', a')) & EQ & FEQ).

      rewrite EQ in UNDEF.
      cbn in UNDEF.

      cbn in EQ.
      subst.

      epose proof allocate_dtyp_spec_can_always_succeed m _ _ (DTYPE_I 64) _ _ _ _ _ as (ms_final & addr & ALLOC).

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
          right.
          split; [|split].
          -- intros msg ERR.
             rewrite map_ret in ERR.
             rewrite map_ret in ERR.
             cbn in ERR.
             (* TODO: inv *)
             admit.
          -- intros msg OOM.
             rewrite map_ret in OOM.
             rewrite map_ret in OOM.
             cbn in OOM.
             (* TODO: inv *)
             admit.
          -- intros st' ms' addr_dv SUCC.
             rewrite map_ret in SUCC.
             rewrite map_ret in SUCC.
             cbn in SUCC.
             assert ((ms_final, (sid, DVALUE_Addr addr)) = (ms', (st', addr_dv))) as EQRES.
             { eapply (@eq1_ret_ret
                       (itree
                          (sum1 ExternalCallE
                                (sum1 PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))))
                    )); eauto.

               typeclasses eauto.
             }

             inversion EQRES.
             subst ms' st' addr_dv.

             cbn.
             exists ms_final, addr.
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
        (* Supposedly I can do this rewrite with T' with the new interp_prop... *)
        assert (interp_prop
                  (case_ (E_trigger_prop (F:=OOME +' UBE +' DebugE +' FailureE))
                         (case_ PickUvalue_handler (F_trigger_prop (F:=OOME +' UBE +' DebugE +' FailureE))))
                  (@pick_uvalue_k_spec ExternalCallE (OOME +' UBE +' DebugE +' FailureE))
                  (MMEP.MMSP.MemState * (store_id * (local_env * Stack.stack * res_L1))) TT
                  (Ret5 genv (lenv, stack) s' m' (DVALUE_Addr addr)) (ret r3)).
        2: admit. (* Pretending I rewrote *)

        cbn.
        eapply interp_prop_ret_refine; eauto.
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
      + go.
        cbn.
        repeat setoid_rewrite bind_ret_l.
        repeat setoid_rewrite bind_bind.
        repeat rewrite bind_trigger.
        repeat setoid_rewrite bind_ret_l.
        setoid_rewrite TranslateFacts.translate_ret.
        repeat setoid_rewrite bind_ret_l.

        setoid_rewrite interp_vis.
        cbn.
        rewrite bind_trigger.
        rewrite interp_intrinsics_vis.
        go.
        cbn.
        go.
        setoid_rewrite bind_ret_l.
        setoid_rewrite interp_local_stack_ret.
        setoid_rewrite bind_ret_l.

        repeat setoid_rewrite bind_trigger.
        setoid_rewrite interp_vis.
        cbn.
        setoid_rewrite bind_trigger.
        setoid_rewrite interp_intrinsics_Tau.
        setoid_rewrite interp_global_Tau.

        setoid_rewrite interp_intrinsics_vis.
        setoid_rewrite interp_global_bind.
        cbn.
        setoid_rewrite interp_global_trigger.
        cbn.
        setoid_rewrite bind_bind.
        setoid_rewrite bind_ret_l.
        setoid_rewrite StateFacts.interp_state_tau.
        setoid_rewrite tau_eutt.
        setoid_rewrite interp_state_bind.
        setoid_rewrite interp_state_trigger.
        cbn.
        setoid_rewrite map_ret.
        setoid_rewrite bind_ret_l.
        cbn.
        setoid_rewrite tau_eutt.
        setoid_rewrite interp_ret.
        setoid_rewrite interp_intrinsics_ret.
        setoid_rewrite interp_global_ret.
        setoid_rewrite interp_state_ret.

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
          right.
          split; [|split].
          -- intros msg ERR.
             rewrite map_ret in ERR.
             rewrite map_ret in ERR.
             cbn in ERR.
             (* TODO: inv *)
             admit.
          -- intros msg OOM.
             rewrite map_ret in OOM.
             rewrite map_ret in OOM.
             cbn in OOM.
             (* TODO: inv *)
             admit.
          -- intros st' ms' addr_dv SUCC.
             rewrite map_ret in SUCC.
             rewrite map_ret in SUCC.
             cbn in SUCC.
             assert ((ms_final, (sid, DVALUE_Addr addr)) = (ms', (st', addr_dv))) as EQRES.
             { eapply (@eq1_ret_ret
                       (itree
                          (sum1 ExternalCallE
                                (sum1 PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))))
                    )); eauto.

               typeclasses eauto.
             }

             inversion EQRES.
             subst ms' st' addr_dv.

             cbn.
             exists ms_final, addr.
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
        (* Supposedly I can do this rewrite with T' with the new interp_prop... *)
        assert (interp_prop
                  (case_ (E_trigger_prop (F:=OOME +' UBE +' DebugE +' FailureE))
                         (case_ PickUvalue_handler (F_trigger_prop (F:=OOME +' UBE +' DebugE +' FailureE))))
                  (@pick_uvalue_k_spec ExternalCallE (OOME +' UBE +' DebugE +' FailureE))
                  (MMEP.MMSP.MemState * (store_id * (local_env * Stack.stack * res_L1))) TT
                  (Ret5 genv (lenv, stack) s' m' (DVALUE_Addr addr)) (ret r3)).
        2: admit. (* Pretending I rewrote *)

        cbn.
        eapply interp_prop_ret_refine; eauto.
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
          right.
          split; [|split].
          -- intros msg ERR.
             rewrite map_ret in ERR.
             rewrite map_ret in ERR.
             cbn in ERR.
             (* TODO: inv *)
             admit.
          -- intros msg OOM.
             rewrite map_ret in OOM.
             rewrite map_ret in OOM.
             cbn in OOM.
             (* TODO: inv *)
             admit.
          -- intros st' ms' addr_dv SUCC.
             rewrite map_ret in SUCC.
             rewrite map_ret in SUCC.
             cbn in SUCC.
             assert ((ms_final, (sid, DVALUE_Addr addr)) = (ms', (st', addr_dv))) as EQRES.
             { eapply (@eq1_ret_ret
                       (itree
                          (sum1 ExternalCallE
                                (sum1 PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))))
                    )); eauto.

               typeclasses eauto.
             }

             inversion EQRES.
             subst ms' st' addr_dv.

             cbn.
             exists ms_final, addr.
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
        (* Supposedly I can do this rewrite with T' with the new interp_prop... *)
        assert (interp_prop
                  (case_ (E_trigger_prop (F:=OOME +' UBE +' DebugE +' FailureE))
                         (case_ PickUvalue_handler (F_trigger_prop (F:=OOME +' UBE +' DebugE +' FailureE))))
                  (@pick_uvalue_k_spec ExternalCallE (OOME +' UBE +' DebugE +' FailureE))
                  (MMEP.MMSP.MemState * (store_id * (local_env * Stack.stack * res_L1))) TT
                  (Ret5 genv (lenv, stack) s' m' (DVALUE_Addr addr)) (ret r3)).
        2: admit. (* Pretending I rewrote *)

        cbn.
        eapply interp_prop_ret_refine; eauto.
  Admitted.

  (* Add allocation in infinite language *)
  Lemma add_alloc :
    forall {RR_mem RR_pick} `{REF_mem : @Reflexive _ RR_mem} `{REF_pick : @Reflexive _ RR_pick} genv lenv stack sid m,
      refine_L6 (interp_mcfg4 RR_mem RR_pick t_ret genv (lenv, stack) sid m) (interp_mcfg4 RR_mem RR_pick t_alloc genv (lenv, stack) sid m).
  Proof.
    intros RR_mem RR_pick REF_mem REF_pick genv lenv stack sid m.
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

    exists (Ret (m, (sid, (lenv, stack, (genv, DVALUE_I1 one))))).
    split.
    { exists (Ret (m, (sid, (lenv, stack, (genv, DVALUE_I1 one))))).
      split.
      unfold t_ret.
      cbn.
      go.
      unfold interp_memory_prop.
      admit.
      unfold model_undef_h.
      eapply interp_prop_ret_refine; eauto.
    }
    {
      (* t' is the result of t_alloc *)
      (* t' could in general be:

         - OOM: OOM is a refinement of everything, so this is fine.
         - Ret: Needs to return one, but it will if alloca succeeds
         - UB:
           + May not be possible
         - ERR:
           + Shouldn't actually be possible.
       *)

      (* Ruling out UB and ERR are the real problems now. *)
      apply interp_prop_vis_inv in INTERP.
      destruct INTERP as (ta & k_alloc & HANDLER & KSPEC).
      destruct HANDLER as (sid' & ms_alloc & HANDLER).

      cbn in HANDLER.
      unfold my_handle_memory_prop in HANDLER.
      unfold MemPropT_lift_PropT_fresh in HANDLER.

      unfold memory_k_spec in *.
      Transparent MMEP.MemSpec.allocate_dtyp_spec.

      Ltac break_fresh_sid_in H :=
        destruct H as [?ms [?fresh_sid [?FRESHSID H]]].

      Ltac break_fresh_provenance_in H :=
        destruct H as [?ms [?fresh_pr [?FRESHPR H]]].

      destruct HANDLER as [[ubmsg UB] | [ALLOC_ERROR [ALLOC_OOM ALLOC]]].
      - cbn in UB.
        exfalso.
        destruct UB as [[UB | UB] | UB]; auto.
        + break_fresh_sid_in UB.
          cbn in *.
          destruct (MMEP.MemSpec.MemHelpers.generate_undef_bytes (DTYPE_I 64) fresh_sid).
          * cbn in UB; destruct UB as [UB | UB]; auto; subst.
            destruct UB as [ms' [bytes [[EQ1 EQ2] UB]]]; subst.
            destruct UB as [UB | UB]; auto.

            break_fresh_provenance_in UB.
            destruct UB as [UB_NO_SUCCESS | UB_RAISE_UB].
            -- eapply UB_NO_SUCCESS.
               
               unfold MMEP.MemSpec.allocate_bytes_succeeds_spec.
               repeat eexists.
            destruct UB as [sab 
            
        destruct UB as [[ubmsg' | UB] | UB].
        contradiction.
        admit.
    }
    split; auto.

    unfold interp_memory_prop.
    cbn.
    go.

    pose proof INTERP as INTERP_BACKUP.
    apply interp_prop_vis_inv in INTERP.
    destruct INTERP as (ta & k_alloc & HANDLER & KSPEC).
    destruct HANDLER as (sid' & ms_alloc & HANDLER).

    cbn in HANDLER.
    unfold my_handle_memory_prop in HANDLER.
    unfold MemPropT_lift_PropT_fresh in HANDLER.

    unfold memory_k_spec in *.
    destruct HANDLER as [[ubmsg UB] | [ALLOC_ERROR [ALLOC_OOM ALLOC]]].
    - destruct UB as [UB | UB].
      + unfold MMEP.MemSpec.allocate_dtyp_spec in *. admit.
    destruct HANDLER as [[ubmsg UB] | [ALLOC_ERROR [ALLOC_OOM ALLOC]]].

    (* If alloc is UB, then the ret is allowed... *)
    (* If alloc is OOM, then t_pre should be OOM *)

    (* &&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&& *)
    
    (* LEMMA *)
    (* (* apply interp_prop_vis_inv in INTERP. *) *)

    (* (* I seem to know very little about k_alloc *) *)
    (* destruct INTERP as (ta & k_alloc & HANDLER & KSPEC). *)
    (* unfold memory_k_spec in KSPEC. *)

    (* destruct HANDLER as (sid' & ms_alloc & HANDLER). *)

    (* cbn in HANDLER. *)
    (* unfold my_handle_memory_prop in HANDLER. *)
    (* unfold MemPropT_lift_PropT_fresh in HANDLER. *)

    destruct HANDLER as [[ubmsg UB] | [ALLOC_ERROR [ALLOC_OOM ALLOC]]].
    - (* t_alloc raises UB *)
      admit. (* alloca shouldn't raise UB *)
      (* ... Although, it can in the spec...? *)
    - (* t_alloc doesn't have UB *)
      (* In reality it's going to either OOM or succeed... *)
      (* Need some kind of lemma about that... *)

      exists t'. (* (ret (m, (sid, (lenv, stack, (genv, DVALUE_I1 one))))). *)
      split.
      + exists t_pre. (* (ret (m, (sid, (lenv, stack, (genv, DVALUE_I1 one))))). *)
        split; auto.
        cbn.
        go.
        unfold interp_memory_prop.
        cbn.
        red in UNDEF.

        unfold UNDEF.
        (* Pretending I can do rewrite... *)
        assert (interp_prop
                  (fun (T : Type)
                     (e : (ExternalCallE +'
                                            LLVMParamsBigIntptr.Events.IntrinsicE +'
                                                                                     LLVMParamsBigIntptr.Events.MemoryE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE) T)
                     (t : itree (ExternalCallE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE) T) =>
                     exists (sid'0 : store_id) (ms' : MMEP.MMSP.MemState),
                       interp_memory_prop_h e sid m (ITree.map (fun x : T => (ms', (sid'0, x))) t))
                  (@memory_k_spec ExternalCallE (PickUvalueE +' OOME +' UBE +' DebugE +' FailureE))
                  (local_env * Stack.stack * res_L1) RR_mem
                  (Ret2 genv (lenv, stack) (DVALUE_I1 DynamicValues.Int1.one))
                  (Ret2 genv (lenv, stack) (DVALUE_I1 DynamicValues.Int1.one))).
        2: admit.

        eapply interp_prop_ret_refine; eauto.
        eauto.
        cbn.
        unfold model_undef_h.
        eapply interp_prop_ret_refine; eauto.
      + cbn.
        red.
        red in UNDEF.

      (* TODO: PLACEHOLDER *)
      destruct ALLOC_OOM as (oom1 & oom2 & ALLOC_OOM).
      forward ALLOC_OOM.
      admit.
      cbn in ALLOC_OOM.

      unfold t_alloc in KSPEC.
      
      cbn in *.
    
    

    exists (Ret2 sid m (lenv, stack, (genv, DVALUE_None))).
    (* exists (ITree.map (fun '(_, (_, x)) => x) (Ret2 sid m (lenv, stack, (genv, DVALUE_None)))). *)
    split.
    - cbn.
      unfold interp_mcfg4 in *.
      unfold model_undef in *.
      unfold interp_memory_prop.
      cbn.
      unfold interp_memory_prop_h.
      cbn.
      exists (Ret5 genv (lenv, stack) sid m DVALUE_None).

      split.
      + go.
        (* TODO: reflexivity *)
        unfold interp_memory_prop.
        cbn.

        (* Supposedly rewriteable *)
        assert (interp_prop
          (fun (T : Type)
             (e : (ExternalCallE +'
                                    LLVMParamsBigIntptr.Events.IntrinsicE +'
                                                                             LLVMParamsBigIntptr.Events.MemoryE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE) T)
             (t : itree (ExternalCallE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE) T) =>
             exists (sid' : store_id) (ms' : MMEP.MMSP.MemState),
               interp_memory_prop_h e sid m (ITree.map (fun x : T => (ms', (sid', x))) t))
          (@memory_k_spec ExternalCallE (PickUvalueE +' OOME +' UBE +' DebugE +' FailureE))
          (local_env * Stack.stack * res_L1) RR_mem (Ret2 genv (lenv, stack) DVALUE_None)
          (Ret2 genv (lenv, stack) DVALUE_None)).
        2: admit.

        eapply interp_prop_ret_refine; eauto.
      + unfold model_undef_h.
        eapply interp_prop_ret_refine; eauto.
    - destruct INTERP as [t_pre [INTERP UNDEF]].
      unfold refine_OOM_h.
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

      unfold interp_memory_prop in INTERP.
      apply interp_prop_vis_inv in INTERP.

      destruct INTERP as (m' & k & BLAH).
      destruct BLAH as (HANDLER & KSPEC).
      cbn in *.
      unfold memory_k_spec in KSPEC.
      
      apply interp_prop_vis in INTERP.


      apply OOM.eutt_refine_oom_h; try typeclasses eauto.
      reflexivity.
  Qed.
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
