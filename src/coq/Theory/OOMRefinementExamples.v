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

  Definition t_alloc : itree L0 dvalue
    := trigger (Alloca (DTYPE_I 64%N));; ret DVALUE_None.

  Definition t_ret : itree L0 dvalue
    := ret DVALUE_None.

  (* Remove allocation in infinite language *)
  Lemma remove_alloc:
    forall genv lenv stack sid m,
      refine_L6 (interp_mcfg4 TT TT t_alloc genv (lenv, stack) sid m) (interp_mcfg4 TT TT t_ret genv (lenv, stack) sid m).
  Proof.
    intros genv lenv stack sid m.
    unfold refine_L6.
    intros t' INTERP.
    exists t'.
    split.
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
      exists (Ret2 s' m' r2). (* Not sure if should be s' or sid, and m' or m *)

      split.
      + rewrite bind_trigger.
        rewrite interp_intrinsics_vis.
        cbn.
        rewrite bind_trigger.
        rewrite interp_global_vis.
        cbn.
        rewrite bind_bind.
        setoid_rewrite bind_ret_l.
        cbn.
        setoid_rewrite interp_intrinsics_ret.
        setoid_rewrite interp_global_ret.
        cbn.

        rewrite bind_trigger.
        rewrite interp_local_stack_vis.
        cbn.

        rewrite bind_bind.
        rewrite bind_trigger.

        setoid_rewrite bind_ret_l.
        cbn.


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
            
        epose proof allocate_dtyp_spec_can_always_succeed m _ _ (DTYPE_I 64) _ _ _ _ _ as (ms_final & addr & ALLOC).

        eapply interp_prop_vis.
        cbn.
        unfold bind_PropT.

        exists (ITree.map (fun '(_, (_, x)) => x) (Ret r2)).
        eexists.
        split.
        * exists sid. exists ms_final.
          unfold my_handle_memory_prop.
          unfold MemPropT_lift_PropT_fresh.
          right.
          split; [|split].
          -- exists String.EmptyString.
             exists String.EmptyString.
             intros ERR.
             rewrite map_ret in ERR.
             rewrite map_ret in ERR.
             cbn in ERR.
             (* TODO: inv *)
             admit.
          -- exists String.EmptyString.
             exists String.EmptyString.
             intros OOM.
             rewrite map_ret in OOM.
             rewrite map_ret in OOM.
             cbn in OOM.
             (* TODO: inv *)
             admit.
          -- intros st' ms' addr_dv SUCC.
             rewrite map_ret in SUCC.
             rewrite map_ret in SUCC.
             cbn in SUCC.
             destruct r2 as (lenv' & lstack & dv).
             assert ((ms_final, (sid, dv)) = (ms', (st', addr_dv))) as EQRES.
             { eapply (@eq1_ret_ret
                       (itree
                          (sum1 ExternalCallE
                                (sum1 PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))))
                    )); eauto.

               typeclasses eauto.
             }

             inversion EQRES.
             subst ms' st' dv.

             cbn.
             exists ms_final, addr.
             split; [|split]; auto.
             
        
        pfold. red.
        cbn.
        (* t2 = (ITree.map (fun '(_, (_, x)) => x) (Ret2 s' m' r2)) *)
        (* t2 ≈ bind ta k2 *)
        (* *)\
        eapply Interp_PropT_Vis. (* with (ta := (ITree.map (fun '(_, (_, x)) => x) (Ret r2))). *)
        * cbn.
          exists sid. exists ms_final.
          unfold my_handle_memory_prop.
          unfold MemPropT_lift_PropT_fresh.
          split; [|split; [|split]].
          admit.
          -- (* UB *)
            split; intros UB.
            ++ destruct UB as [ubm UB].
               rewrite map_ret in UB.
               rewrite map_ret in UB.
               (* TODO: inv *)
               admit.
            ++ unfold MMEP.MemSpec.handle_memory_prop in UB.
               exfalso.
               apply UB with (res := ret (ms_final, DVALUE_Addr addr)).
               cbn.
               clear UB.

               exists ms_final. exists addr.
               tauto.
          -- (* Error *)
            split; intros ERR.
            ++ (* TODO: inv *)
              admit.
            ++ destruct ERR as [errm ERR].
               (* I don't actually know that allocate_dtyp_spec *can't* error *)
               exists errm.
               unfold MMEP.MemSpec.handle_memory_prop in ERR.
               cbn in ERR.
               destruct ERR as [ERR | ERR].
               rewrite ALLOC in ERR.
               exfalso.
               apply ERR with (res := ret (ms_final, DVALUE_Addr addr)).
               cbn.
               clear UB.

               exists ms_final. exists addr.
               tauto.

              setoid_rewrite ALLOC in ERR.
          --
        setoid_rewrite map_ret.
        
        Set Nested Proofs Allowed.
        Lemma interp_memory_prop_vis :
          interp_memor
          
        (* TODO: lemma *)
        unfold interp_memory_prop.
        cbn.
      + auto. (* s' and m' may be unimportant *)

      rewrite EQ.
      
      setoid_rewrite R2 in EQ.
      (* TODO: I feel like I need a map lemma involving eutt ret * )
      assert (@ret (itree (ExternalCallE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE))
                   (@Monad_itree (ExternalCallE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE))
                   (local_env * @Stack.stack local_env * res_L1) r2 = (ret ((fun '(_, (_, x)) => x) (m, (sid, r2))))) as R2 by reflexivity.
      Unset Printing Notations.
      setoid_rewrite R2 in EQ.
      eassert (Ret r2 = ).
      reflexivity.
      rewrite H in EQ.

(MMEP.MMSP.MemState * (store_id * (local_env * @Stack.stack local_env * res_L1)))
      erewrite <- map_ret in EQ.
      
      setoid_rewrite interp_memory_prop_ret2 in INTERP.


    Definition interp_memory_prop {R} (RR : R -> R -> Prop) :
      itree Effin R -> MemStateFreshT (PropT Effout) R :=
      fun (t : itree Effin R) (sid : store_id) (ms : MemState) (t' : itree Effout (MemState * (store_id * R))) =>
        interp_prop (fun T (e : Effin T) (t : itree Effout T) => exists (sid' : store_id) (ms' : MemState),
                         @interp_memory_prop_h T e sid ms (fmap (fun (x : T) => (ms', (sid', x))) t)) (@memory_k_spec) R RR t ((fmap (fun '(_, (_, x)) => x) t') : itree Effout R).

      unfold interp_memory_prop in INTERP.
      
      setoid_rewrite interp_intrinsics_ret in INTERP.
      Show Proof.
      rewrite interp_ret in INTERP.
      
      pose proof allocate_can_always_succeed m (DTYPE_I 64%N) as ALLOC_SUCCESS.


      unfold interp_mcfg4.
      unfold model_undef.

      eexists; cbn; split.
      + setoid_rewrite bind_trigger.

        
      + reflexivity.

      
      cbn.

      
      epose proof interp_prop_Proper_eq.
      
      unfold Proper, respectful in *.
      unfold Basics.flip, Basics.impl in *.
      eapply H.
      all: eauto; try typeclasses eauto.
      cbn.
      go.

      rewrite interp_memory_trigger.
      cbn.
      go.
      cbn.

      pose proof (allocate_succeeds (ms_memory_stack m) (DTYPE_I 64)) as ALLOC_SUC.
      forward ALLOC_SUC. intros CONTRA; inversion CONTRA.

      destruct m as [ms sid pr].
      eapply ErrSID_succeeds_ErrSID_runs_to in ALLOC_SUC as ((ms' & a) & sid' & pr' & REST).
      rewrite REST.

      go.
      cbn.
      go.
      cbn.

      apply eutt_Ret.
      reflexivity.
    - right.
      apply OOM.eutt_refine_oom_h; try typeclasses eauto.
      reflexivity.
  Qed.

  (* Add allocation in infinite language *)
  Lemma add_alloc :
    forall g l s m,
      refine_L6 (interp_mcfg4 TT t_ret g (l, s) m) (interp_mcfg4 TT t_alloc g (l, s) m).
  Proof.
    intros g l s m.
    unfold refine_L6.
    intros t' INTERP.
    exists t'.
    split.
    - cbn.
      unfold interp_mcfg4.
      unfold model_undef.
      epose proof interp_prop_Proper_eq.
      unfold Proper, respectful in *.
      unfold Basics.flip, Basics.impl in *.
      eapply H.
      all: eauto.
      cbn.
      go.

      rewrite interp_memory_trigger.
      cbn.
      go.
      cbn.

      pose proof (allocate_succeeds (ms_memory_stack m) (DTYPE_I 64)) as ALLOC_SUC.
      forward ALLOC_SUC. intros CONTRA; inversion CONTRA.

      destruct m as [ms sid pr].
      eapply ErrSID_succeeds_ErrSID_runs_to in ALLOC_SUC as ((ms' & a) & sid' & pr' & REST).
      rewrite REST.

      go.
      cbn.
      go.
      cbn.

      apply eutt_Ret.
      reflexivity.
    - right.
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
