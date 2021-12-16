From Vellvm Require Import
     TopLevel
     TopLevelRefinements
     Refinement
     Utils.Monads
     Utils.PropT
     Utils.Tactics
     Theory.DenotationTheory
     Theory.InterpreterMCFG
     Handlers.InfiniteMemoryTheory.

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
  Import BigIntptrInfiniteMemoryTheory.
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

  (* Remove allocation in infinite language *)
  Lemma remove_alloc:
    forall g l s m,
      refine_L6 (interp_mcfg4 TT t_alloc g (l, s) m) (interp_mcfg4 TT t_ret g (l, s) m).
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
      
      
      inversion H8; subst.
      admit.
      cbn in REF.
      
      cbn in REF.
      
      destruct r2 as .
        rewrite RES.

        cbn.

        (* Won't work... *)
        (* Just need to lift some of this proof and go back and change the existential, I think *)
        

    exists (SemNotations.Ret3 g (l, s) m UVALUE_None).
    split.
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
