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
      refine_L6 (interp_mcfg4 TT t_ret g (l, s) m) (interp_mcfg4 TT t_alloc g (l, s) m).
  Proof.
    intros g l s m.
    unfold refine_L6.
    intros t' INTERP.
    Require Import String.
    exists (SemNotations.Ret3 g (l, s) m UVALUE_None).
    split.
    - cbn.
      unfold interp_mcfg4.
      unfold model_undef.
      go.

      epose proof interp_prop_refl.
      unfold Proper, respectful in *.

      eapply interp_prop_ret_pure; typeclasses eauto.
    -
      
      right.
      Import OOM.

      unfold refine_OOM_h.
      cbn in INTERP.
      unfold interp_mcfg4 in INTERP.


      Require Import Stack.
      Require Import Global.
      cbn.
    Ltac go_in H :=
      repeat match goal with
             | H: context [interp_intrinsics (ITree.bind _ _)] |- _ => rewrite interp_intrinsics_bind in H
             | H: context [interp_global (ITree.bind _ _)] |- _ => rewrite interp_global_bind in H
             | H: context [interp_local_stack (ITree.bind _ _)] |- _ => rewrite interp_local_stack_bind in H
             | H: context [interp_memory (ITree.bind _ _)] |- _ => rewrite interp_memory_bind in H
             | H: context [interp_intrinsics (trigger _)] |- _ => rewrite interp_intrinsics_trigger in H; cbn in H; rewrite ?subevent_subevent in H
             | H: context [interp_global (trigger _)] |- _ => rewrite interp_global_trigger in H; cbn in H; rewrite ?subevent_subevent in H
             | H: context [interp_local_stack (trigger _)] |- _ => rewrite interp_local_stack_trigger in H; cbn in H; rewrite ?subevent_subevent in H
             | H: context [ITree.bind (ITree.bind _ _) _] |- _ => rewrite bind_bind in H
             | H: context [interp_intrinsics (Ret _)] |- _ => rewrite interp_intrinsics_ret in H
             | H: context [interp_global (Ret _)] |- _ => rewrite interp_global_ret in H
             | H: context [interp_local_stack (Ret _)] |- _ => rewrite interp_local_stack_ret in H
             | H: context [interp_memory (Ret _)] |- _ => rewrite interp_memory_ret in H
             | H: context [ITree.bind (Ret _) _] |- _ => rewrite bind_ret_l in H
             end.

      go_in INTERP.

      unfold model_undef in INTERP.

      (* I basically need to show that t' is the same as t_alloc, but
         with a different effects signature..

         I.e., it either OOMs or it returns UVALUE_None
       *)

      epose proof interp_prop_Proper_eq.

      destruct (runErrSID (allocate (ms_memory_stack m) (DTYPE_I 64)) (ms_sid m) (ms_prov m))
        as [[res sid'] pr'].
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
