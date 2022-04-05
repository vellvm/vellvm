From Coq Require Import
     Morphisms
     ZArith
     Lia.

From Vellvm.Semantics Require Import
     MemoryParams
     Memory.ErrSID
     LLVMParams
     LLVMEvents.

From Vellvm.Handlers Require Import
     MemoryModel
     MemPropT.

From Vellvm.Utils Require Import
     StateMonads.

From ITree Require Import
     ITree
     Basics.Basics
     Eq.Eq
     Events.StateFacts
     Events.State.

From ExtLib Require Import
     Structures.Functor
     Structures.Monads.

(* Needs to be after ITree.Events.State *)
From Vellvm.Utils Require Import
     PropT.

Import Basics.Basics.Monads.
Import MonadNotation.

Import MemoryAddress.
Import Error.

Set Implicit Arguments.
Set Contextual Implicit.

Module Type MemorySpecInterpreter (LP : LLVMParams) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MM : MemoryModelSpec LP MP MMSP).
  Import MM.
  Import MMSP.
  Import LP.Events.
  Import LP.PROV.

  Section Interpreters.
    Variable (E F : Type -> Type).
    Context `{FailureE -< F} `{UBE -< F} `{OOME -< F}.
    Notation Effin := (E +' IntrinsicE +' MemoryE +' F).
    Notation Effout := (E +' F).

    Definition MemStateT M := stateT MemState M.
    Definition MemStateFreshT M := stateT store_id (stateT Provenance (MemStateT M)).

    Definition MemStateFreshT_from_MemStateT {M X} `{Monad M} (mst : MemStateT M X) : MemStateFreshT M X :=
      fun sid pr => x <- mst;; ret (pr, (sid, x)).

    (** MemMonad Instances *)
    #[global] Instance MemStateFreshT_MonadAllocationId M `{Monad M} : MonadAllocationId AllocationId (MemStateFreshT M).
    Proof.
      split.
      unfold MemStateFreshT.
      apply (lift (pr <- get;;
                   let pr' := next_provenance pr in
                   put pr';;
                   ret (provenance_to_allocation_id pr'))).
    Defined.

    #[global] Instance MemStateFreshT_MonadStoreId M `{Monad M} : MonadStoreId (MemStateFreshT M).
    Proof.
      split.
      unfold MemStateFreshT.
      apply (sid <- get;;
             let sid' := BinNatDef.N.succ sid in
             put sid';;
             ret sid').
    Defined.

    #[global] Instance MemStateFreshT_MonadMemState M `{Monad M} : MonadMemState MemState (MemStateFreshT M).
    Proof.
      split.
      - apply (lift (lift get)).
      - intros ms; apply (lift (lift (put ms))).
    Defined.

    #[global] Instance MemState_StoreIdFreshness : StoreIdFreshness MemState.
    Proof.
      split.
      apply used_store_id_prop.
    Defined.

    #[global] Instance MemState_AllocationIdFreshness : AllocationIdFreshness AllocationId MemState.
    Proof.
      split.
      - (* Is a store id used in a memstate *)
        apply MMSP.used_allocation_id_prop.
    Defined.

    #[global] Instance MemStateFreshT_MonadT {M} `{Monad M} : MonadT (MemStateFreshT M) M.
    Proof.
      unfold MemStateFreshT.
      unfold MemStateT.
      split.
      - intros t X.
        intros sid pr ms.
        apply (res <- X;; ret (ms, (pr, (sid, res)))).
    Defined.

    Definition MemStateFreshT_State := (store_id * Provenance)%type.

    (* M may be PropT or itree... *)
    Definition MemStateFreshT_run {A} {Eff} `{FailureE -< Eff} `{OOME -< Eff} `{UBE -< Eff} (ma : MemStateFreshT (itree Eff) A) (ms : MemState) (st : MemStateFreshT_State) : itree Eff (MemStateFreshT_State * (MemState * A)).
    Proof.
      unfold MemStateFreshT in *.
      destruct st as [s p].
      specialize (ma s p ms).
      unfold MemStateFreshT_State.
      eapply fmap; [ |eauto].
      intros [ms' [p' [s' x]]].
      apply (s', p', (ms', x)).
    Defined.

    Definition MemStateFreshT_valid_state (ms : MemState) (st : MemStateFreshT_State) : Prop
      := let '(sid, pr) := st in
         (forall sid', used_store_id ms sid' -> (sid' < sid)%N) /\
           (* TODO: freshness of aids... *)
           (forall aid, used_allocation_id ms aid -> False).

    #[global] Instance MemStateFreshT_MemMonad {Eff} `{FAIL: FailureE -< Eff} `{OOM: OOME -< Eff} `{UB: UBE -< Eff}
      : MemMonad MemState MemStateFreshT_State AllocationId (MemStateFreshT (itree Eff)) (itree Eff).
    Proof.
      esplit with
        (MemMonad_run := fun A => @MemStateFreshT_run A Eff FAIL OOM UB)
        (MemMonad_valid_state := MemStateFreshT_valid_state).

      (* TODO: didn't need valid for ret / bind laws... *)
      - (* run bind *)
        intros A B ma k ms st VALID.
        unfold MemStateFreshT_run.
        destruct st.
        cbn.
        rewrite map_bind.
        rewrite bind_map.
        eapply eutt_clo_bind.
        reflexivity.
        intros u1 u2 H2; subst.
        destruct u2 as [ms' [pr' [sid' x]]].
        cbn.
        reflexivity.
      - (* run ret *)
        intros A x ms st VALID.
        cbn.
        destruct st.
        cbn.
        rewrite map_ret.
        reflexivity.
      - (* get_mem_state *)
        intros ms [sid pr].
        cbn.
        rewrite map_bind.
        repeat rewrite bind_ret_l.
        rewrite map_ret.
        cbn.
        reflexivity.
      - (* put_mem_state *)
        intros ms ms' [sid pr].
        cbn.
        rewrite map_bind.
        repeat rewrite bind_ret_l.
        rewrite map_ret.
        cbn.
        reflexivity.
      - (* fresh_sid *)
        intros ms [sid pr] VALID.
        do 2 eexists.
        cbn.
        rewrite map_bind.
        rewrite bind_ret_l.
        rewrite map_bind.
        rewrite bind_ret_l.
        rewrite map_ret.
        cbn.
        split; [reflexivity|].

        cbn in VALID.
        destruct VALID as [SID AID].

        intros USED.
        apply SID in USED.
        lia.
      - (* fresh_allocation_id *)
        intros ms [sid pr] VALID.
        do 2 eexists.
        cbn.
        rewrite map_bind.
        repeat rewrite bind_ret_l.
        rewrite map_ret.
        cbn.
        split; [reflexivity|].

        cbn in VALID.
        destruct VALID as [SID AID].

        intros USED.
        apply AID in USED.
        auto. (* TODO: Need to fix this statement *)
      - (* raise_oom *)
        intros A ms oom_msg [sid pr].
        cbn.
        rewrite map_bind.
        setoid_rewrite Raise.raiseOOM_bind_itree.
        reflexivity.
      - (* raise_ub *)
        intros A ms oom_msg [sid pr].
        cbn.
        rewrite map_bind.
        setoid_rewrite Raise.raiseUB_bind_itree.
        reflexivity.
      - (* raise_error *)
        intros A ms oom_msg [sid pr].
        cbn.
        rewrite map_bind.
        setoid_rewrite Raise.raise_bind_itree.
        reflexivity.
    Defined.

    Definition E_trigger' : forall R, E R -> (MemStateT (PropT Effout) R) :=
      fun R e m => fun t => t ≈ r <- trigger e;; ret (m, r).

    Definition F_trigger' : forall R, F R -> (MemStateT (PropT Effout) R) :=
      fun R e m => fun t => t ≈ r <- trigger e;; ret (m, r).

    Definition E_trigger : forall R, E R -> (MemStateFreshT (PropT Effout) R) :=
      fun R e sid pr m => fun t => t ≈ r <- trigger e;; ret (m, (pr, (sid, r))).

    Definition F_trigger : forall R, F R -> (MemStateFreshT (PropT Effout) R) :=
      fun R e sid pr m => fun t => t ≈ r <- trigger e;; ret (m, (pr, (sid, r))).

    (* TODO: get rid of this silly hack. *)
    Definition my_handle_memory_prop' :
      forall T : Type, MemoryE T -> MemStateT (PropT Effout) T.
    Proof.
      intros T MemE.
      eapply MemPropT_lift_PropT.
      eapply handle_memory_prop; auto.
    Defined.

    Definition my_handle_intrinsic_prop' :
      forall T : Type, IntrinsicE T -> MemStateT (PropT Effout) T.
    Proof.
      intros T IntE.
      eapply MemPropT_lift_PropT.
      eapply handle_intrinsic_prop; auto.
    Defined.

    Definition my_handle_memory_prop :
      forall T : Type, MemoryE T -> MemStateFreshT (PropT Effout) T.
    Proof.
      intros T MemE.
      eapply MemPropT_lift_PropT_fresh.
      eapply handle_memory_prop; auto.
    Defined.

    Definition my_handle_intrinsic_prop :
      forall T : Type, IntrinsicE T -> MemStateFreshT (PropT Effout) T.
    Proof.
      intros T IntE.
      eapply MemPropT_lift_PropT_fresh.
      eapply handle_intrinsic_prop; auto.
    Defined.

    Definition interp_memory_prop_h' : forall T, Effin T -> MemStateT (PropT Effout) T
      := case_ E_trigger' (case_ my_handle_intrinsic_prop' (case_ my_handle_memory_prop' F_trigger')).

    Definition interp_memory_prop_h : forall T, Effin T -> MemStateFreshT (PropT Effout) T
      := case_ E_trigger (case_ my_handle_intrinsic_prop (case_ my_handle_memory_prop F_trigger)).

    (* TODO: I find the lack of interp_prop here disturbing... *)
    Definition memory_k_spec
               {T R : Type}
               (e : Effin T)
               (ta : itree Effout T)
               (k1 : T -> itree Effin R)
               (k2 : T -> itree Effout R)
               (t2 : itree Effout R) : Prop
      := t2 ≈ (bind ta k2).

    #[global] Instance memory_k_spec_proper {T R : Type} {RR : R -> R -> Prop} {b a : bool} :
      Proper
        (eq ==>
            eq ==>
            (fun k1 k2 : T -> itree Effin R =>
               forall x : T, eqit RR b a (k1 x) (k2 x)) ==> eq ==> eq ==> iff)
        (memory_k_spec).
    Proof.
      unfold Proper, respectful.
      intros x y ? x0 y0 ? x1 y1 ? x2 y2 ? x3 y3 ?; subst.
      split; cbn; auto.
    Qed.

    Definition interp_memory_prop' {R} (RR : R -> R -> Prop) :
      itree Effin R -> MemStateT (PropT Effout) R :=
      fun (t : itree Effin R) (ms : MemState) (t' : itree Effout (MemState * R)) =>
        interp_prop (fun T e t => exists ms', @interp_memory_prop_h' T e ms (fmap (fun x => (ms', x)) t)) (@memory_k_spec) R RR t (fmap snd t').

    (* Things line up a lot better if interp_memory_prop has the same
       type signature as interp_memory... *)
    Definition interp_memory_prop {R} (RR : R -> R -> Prop) :
      itree Effin R -> MemStateFreshT (PropT Effout) R :=
      fun (t : itree Effin R) (sid : store_id) (pr : Provenance) (ms : MemState) (t' : itree Effout (MemState * (Provenance * (store_id * R)))) =>
        interp_prop (fun T (e : Effin T) (t : itree Effout T) => exists (sid' : store_id) (pr' : Provenance) (ms' : MemState), @interp_memory_prop_h T e sid pr ms (fmap (fun (x : T) => (ms', (pr', (sid', x)))) t)) (@memory_k_spec) R RR t ((fmap (fun '(_, (_, (_, x))) => x) t') : itree Effout R).
  End Interpreters.
End MemorySpecInterpreter.

Module Type MemoryExecInterpreter (LP : LLVMParams) (MP : MemoryParams LP) (MMEP : MemoryModelExecPrimitives LP MP) (MM : MemoryModelExec LP MP MMEP) (SPEC_INTERP : MemorySpecInterpreter LP MP MMEP.MMSP MMEP.MemSpec).
  Import MM.
  Import MMEP.
  Import MMEP.MMSP.
  Import LP.
  Import LP.Events.
  Import LP.PROV.

  (** Specification of the memory model *)
  Import SPEC_INTERP.
  Import MMSP.
  Import MMSP.MemByte.
  Import MemSpec.

  Section Interpreters.
    Variable (E F : Type -> Type).
    Context `{FailureE -< F} `{UBE -< F} `{OOME -< F}.
    Notation Effin := (E +' IntrinsicE +' MemoryE +' F).
    Notation Effout := (E +' F).

    (* TODO: Why do I have to duplicate this >_<? *)
    (** MemMonad Instances *)
    #[global] Instance MemStateFreshT_MonadAllocationId M `{Monad M} : MonadAllocationId AllocationId (MemStateFreshT M).
    Proof.
      split.
      unfold MemStateFreshT.
      apply (lift (pr <- get;;
                   let pr' := next_provenance pr in
                   put pr';;
                   ret (provenance_to_allocation_id pr'))).
    Defined.

    #[global] Instance MemStateFreshT_MonadStoreId M `{Monad M} : MonadStoreId (MemStateFreshT M).
    Proof.
      split.
      unfold MemStateFreshT.
      apply (sid <- get;;
             let sid' := BinNatDef.N.succ sid in
             put sid';;
             ret sid').
    Defined.

    #[global] Instance MemStateFreshT_MonadMemState M `{Monad M} : MonadMemState MemState (MemStateFreshT M).
    Proof.
      split.
      - apply (lift (lift get)).
      - intros ms; apply (lift (lift (put ms))).
    Defined.

    #[global] Instance MemState_StoreIdFreshness : StoreIdFreshness MemState.
    Proof.
      split.
      apply used_store_id_prop.
    Defined.

    #[global] Instance MemState_AllocationIdFreshness : AllocationIdFreshness AllocationId MemState.
    Proof.
      split.
      - (* Is a store id used in a memstate *)
        apply MMSP.used_allocation_id_prop.
    Defined.

    #[global] Instance MemStateFreshT_MonadT {M} `{Monad M} : MonadT (MemStateFreshT M) M.
    Proof.
      unfold MemStateFreshT.
      unfold MemStateT.
      split.
      - intros t X.
        intros sid pr ms.
        apply (res <- X;; ret (ms, (pr, (sid, res)))).
    Defined.

    Definition MemStateFreshT_State := (store_id * Provenance)%type.

    (* M may be PropT or itree... *)
    Definition MemStateFreshT_run {A} {Eff} `{FailureE -< Eff} `{OOME -< Eff} `{UBE -< Eff} (ma : MemStateFreshT (itree Eff) A) (ms : MemState) (st : MemStateFreshT_State) : itree Eff (MemStateFreshT_State * (MemState * A)).
    Proof.
      unfold MemStateFreshT in *.
      destruct st as [s p].
      specialize (ma s p ms).
      unfold MemStateFreshT_State.
      eapply fmap; [ |eauto].
      intros [ms' [p' [s' x]]].
      apply (s', p', (ms', x)).
    Defined.

    Definition MemStateFreshT_valid_state (ms : MemState) (st : MemStateFreshT_State) : Prop
      := let '(sid, pr) := st in
         (forall sid', used_store_id ms sid' -> (sid' < sid)%N) /\
           (* TODO: freshness of aids... *)
           (forall aid, used_allocation_id ms aid -> False).

    #[global] Instance MemStateFreshT_MemMonad {Eff} `{FAIL: FailureE -< Eff} `{OOM: OOME -< Eff} `{UB: UBE -< Eff}
      : MemMonad MemState MemStateFreshT_State AllocationId (MemStateFreshT (itree Eff)) (itree Eff).
    Proof.
      esplit with
        (MemMonad_run := fun A => @MemStateFreshT_run A Eff FAIL OOM UB)
        (MemMonad_valid_state := MemStateFreshT_valid_state).

      (* TODO: didn't need valid for ret / bind laws... *)
      - (* run bind *)
        intros A B ma k ms st VALID.
        unfold MemStateFreshT_run.
        destruct st.
        cbn.
        rewrite map_bind.
        rewrite bind_map.
        eapply eutt_clo_bind.
        reflexivity.
        intros u1 u2 H2; subst.
        destruct u2 as [ms' [pr' [sid' x]]].
        cbn.
        reflexivity.
      - (* run ret *)
        intros A x ms st VALID.
        cbn.
        destruct st.
        cbn.
        rewrite map_ret.
        reflexivity.
      - (* get_mem_state *)
        intros ms [sid pr].
        cbn.
        rewrite map_bind.
        repeat rewrite bind_ret_l.
        rewrite map_ret.
        cbn.
        reflexivity.
      - (* put_mem_state *)
        intros ms ms' [sid pr].
        cbn.
        rewrite map_bind.
        repeat rewrite bind_ret_l.
        rewrite map_ret.
        cbn.
        reflexivity.
      - (* fresh_sid *)
        intros ms [sid pr] VALID.
        do 2 eexists.
        cbn.
        rewrite map_bind.
        rewrite bind_ret_l.
        rewrite map_bind.
        rewrite bind_ret_l.
        rewrite map_ret.
        cbn.
        split; [reflexivity|].

        cbn in VALID.
        destruct VALID as [SID AID].

        intros USED.
        apply SID in USED.
        lia.
      - (* fresh_allocation_id *)
        intros ms [sid pr] VALID.
        do 2 eexists.
        cbn.
        rewrite map_bind.
        repeat rewrite bind_ret_l.
        rewrite map_ret.
        cbn.
        split; [reflexivity|].

        cbn in VALID.
        destruct VALID as [SID AID].

        intros USED.
        apply AID in USED.
        auto. (* TODO: Need to fix this statement *)
      - (* raise_oom *)
        intros A ms oom_msg [sid pr].
        cbn.
        rewrite map_bind.
        setoid_rewrite Raise.raiseOOM_bind_itree.
        reflexivity.
      - (* raise_ub *)
        intros A ms oom_msg [sid pr].
        cbn.
        rewrite map_bind.
        setoid_rewrite Raise.raiseUB_bind_itree.
        reflexivity.
      - (* raise_error *)
        intros A ms oom_msg [sid pr].
        cbn.
        rewrite map_bind.
        setoid_rewrite Raise.raise_bind_itree.
        reflexivity.
    Defined.

    (** Handlers *)
    Definition E_trigger : E ~> MemStateFreshT (itree Effout) :=
      fun R e sid aid m => r <- trigger e;; ret (m, (aid, (sid, r))).

    Definition F_trigger : F ~> MemStateFreshT (itree Effout) :=
      fun R e sid aid m => r <- trigger e;; ret (m, (aid, (sid, r))).

    (* TODO: get rid of this silly hack. *)
    Definition my_handle_memory : MemoryE ~> MemStateFreshT (itree Effout) :=
      @handle_memory (MemStateFreshT (itree Effout)) _ MemStateFreshT_State _ _ _ _ _ _ _ _ _ _ _ _ _ _ MemStateFreshT_MemMonad.

    Definition my_handle_intrinsic : IntrinsicE ~> MemStateFreshT (itree Effout) :=
      @handle_intrinsic (MemStateFreshT (itree Effout)) _ MemStateFreshT_State _ _ _ _ _ _ _ _ _ _ _ _ _ _ MemStateFreshT_MemMonad.

    Definition interp_memory_h : Effin ~> MemStateFreshT (itree Effout)
      := case_ E_trigger (case_ my_handle_intrinsic (case_ my_handle_memory F_trigger)).

    (* TODO: I find the lack of interp_prop here disturbing... *)
    Definition interp_memory :
      itree Effin ~> MemStateFreshT (itree Effout) :=
      interp_state interp_memory_h.

    (* fmap throws away extra sid / provenance from state
       handler. This is fine because interp_memory_prop should include
       propositions that make sure ids and provenances are fresh when
       necessary.
     *)
    Lemma interp_memory_correct :
      forall {T} t (ms : MemState) (sid : store_id) (pr : Provenance),
        interp_memory_prop eq t sid pr ms (@interp_memory T t sid pr ms).
    Proof.
      intros T t ms sid pr.
      unfold interp_memory_prop.
      unfold interp_memory.
      unfold interp_state.
    Admitted.
  End Interpreters.
End MemoryExecInterpreter.


Module MakeMemorySpecInterpreter (LP : LLVMParams) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MS : MemoryModelSpec LP MP MMSP) <: MemorySpecInterpreter LP MP MMSP MS.
  Include MemorySpecInterpreter LP MP MMSP MS.
End MakeMemorySpecInterpreter.

Module MakeMemoryExecInterpreter (LP : LLVMParams) (MP : MemoryParams LP) (MMEP : MemoryModelExecPrimitives LP MP) (ME : MemoryModelExec LP MP MMEP) (SPEC_INTERP : MemorySpecInterpreter LP MP MMEP.MMSP MMEP.MemSpec) <: MemoryExecInterpreter LP MP MMEP ME SPEC_INTERP.
  Include MemoryExecInterpreter LP MP MMEP ME SPEC_INTERP.
End MakeMemoryExecInterpreter.
