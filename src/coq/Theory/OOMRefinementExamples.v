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

Require Import Morphisms.
Require Import Paco.paco.

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
