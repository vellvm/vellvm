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
     MemPropT
     MemoryModules.Within.

From Vellvm.Utils Require Import
     InterpProp
     StateMonads.

From ITree Require Import
     ITree
     Eq.Eq.

From ExtLib Require Import
     Structures.Functor
     Structures.Monads.

(* Needs to be after ITree.Events.State *)
From Vellvm.Utils Require Import
     PropT.

Require Import Paco.paco.

Import Basics.Basics.Monads.
Import MonadNotation.

Import MemoryAddress.
Import Error.

Set Implicit Arguments.
Set Contextual Implicit.

Module Type MemorySpecInterpreter (LP : LLVMParams) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MM : MemoryModelSpec LP MP MMSP) (MemExecM : MemoryExecMonad LP MP MMSP MM).
  Import MM.
  Import MMSP.
  Import MemExecM.
  Import LP.Events.
  Import LP.PROV.

  Section Interpreters.
    Variable (E F : Type -> Type).
    Context `{FailureE -< F} `{UBE -< F} `{OOME -< F}.
    Notation Effin := (E +' IntrinsicE +' MemoryE +' F).
    Notation Effout := (E +' F).

    Definition MemStateT M := stateT MemState M.
    Definition MemStateFreshT M := stateT store_id (MemStateT M).

    Definition MemStateFreshT_from_MemStateT {M X} `{Monad M} (mst : MemStateT M X) : MemStateFreshT M X :=
      fun sid => x <- mst;; ret (sid, x).

    (** MemMonad Instances *)
    #[global] Instance MemStateFreshT_Provenance M `{Monad M} : MonadProvenance Provenance (MemStateFreshT M).
    Proof.
      split.
      exact (lift
               (ms <- get;;
                let (pr', ms') := mem_state_fresh_provenance ms in
                put ms';;
                ret pr')).
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
      - apply (lift get).
      - intros ms; apply (lift (put ms)).
    Defined.

    #[global] Instance MemState_StoreIdFreshness : StoreIdFreshness MemState.
    Proof.
      split.
      apply used_store_id_prop.
    Defined.

    Definition MemStateFreshT_State := store_id.

    #[global] Instance MemState_ProvenanceFreshness : ProvenanceFreshness Provenance MemState.
     Proof.
       split.
       - apply used_provenance_prop.
     Defined.

    #[global] Instance MemState_memory_MemStateMem : MemStateMem MemState memory_stack :=
      {| ms_get_memory := MemState_get_memory;
        ms_put_memory := MemState_put_memory;
        ms_get_put_memory := MemState_get_put_memory;
      |}.

    #[global] Instance MemStateFreshT_MonadT {M} `{Monad M} : MonadT (MemStateFreshT M) M.
    Proof.
      unfold MemStateFreshT.
      unfold MemStateT.
      split.
      - intros t X.
        intros sid ms.
        apply (res <- X;; ret (ms, (sid, res))).
    Defined.

    (* M may be PropT or itree... *)
    Definition MemStateFreshT_run {A} {Eff} (ma : MemStateFreshT (itree Eff) A) (ms : MemState) (st : MemStateFreshT_State) : itree Eff (MemStateFreshT_State * (MemState * A)).
    Proof.
      unfold MemStateFreshT in *.
      specialize (ma st ms).
      unfold MemStateFreshT_State.
      eapply fmap; [ |eauto].
      intros [ms' [s' x]].
      apply (s', (ms', x)).
    Defined.

    Definition MemStateFreshT_valid_state (ms : MemState) (st : MemStateFreshT_State) : Prop
      := let sid := st in
         (forall sid', used_store_id ms sid' -> (sid' < sid)%N).

  Definition within_MemStateFreshT_itree
    {Eff}
    {A} (msf : MemStateFreshT (itree Eff) A) (pre : MemStateFreshT_State * MemState) (t : itree Eff A) (post : MemStateFreshT_State * MemState) : Prop :=
    let '(sid, ms) := pre in
    let '(sid', ms') := post in
    MemStateFreshT_run msf ms sid ≈ fmap (fun x => (sid', (ms', x))) t.

  Lemma within_eq1_Proper_MemStateFreshT_itree
    {Eff} :
    forall A : Type,
      Proper (Monad.eq1 ==> eq ==> eq ==> eq ==> iff)
        (@within_MemStateFreshT_itree Eff A).
  Proof.
    intros A.
    unfold Proper, respectful.
    intros x y H2 x0 y0 H3 x1 y1 H4 x2 y2 H5.
    subst.
    unfold within_MemStateFreshT_itree.
    cbn.
    destruct y0, y2.
    split; intros WITHIN.
    - rewrite H2 in WITHIN.
      auto.
    - rewrite H2.
      auto.
  Qed.

  #[global] Instance MemStateFreshT_Within {Eff} :
    Within (MemStateFreshT (itree Eff)) (itree Eff) (MemStateFreshT_State * MemState) (MemStateFreshT_State * MemState).
  Proof.
    esplit.
    Unshelve.
    2: {
      intros A m pre b post.
      eapply within_MemStateFreshT_itree.
      2: apply pre.
      3: apply post.
      eauto.
      eauto.
    }

    intros A.
    unfold Proper, respectful.
    intros x y H2 x0 y0 H3 x1 y1 H4 x2 y2 H5.
    subst.

    eapply within_eq1_Proper_MemStateFreshT_itree; eauto.
  Defined.

    Lemma oom_error_inv :
      forall {A Eff} `{FailureE -< Eff} `{OOME -< Eff} oom_msg error_msg,
        ~ (raise_oom oom_msg : itree Eff A) ≈ (raise_error error_msg).
    Proof.
    Admitted.

    Lemma ub_error_inv :
      forall {A Eff} `{FailureE -< Eff} `{UBE -< Eff} ub_msg error_msg,
        ~ (raise_ub ub_msg : itree Eff A) ≈ (raise_error error_msg).
    Proof.
    Admitted.

    Lemma oom_ub_inv :
      forall {A Eff} `{UBE -< Eff} `{OOME -< Eff} oom_msg ub_msg,
        ~ (raise_oom oom_msg : itree Eff A) ≈ (raise_ub ub_msg).
    Proof.
    Admitted.

    Import MonadEq1Laws.

    #[global] Instance MemStateFreshT_Eq1_ret_inv {Eff} `{FAIL: FailureE -< Eff} `{OOM: OOME -< Eff} `{UB: UBE -< Eff}
      : Eq1_ret_inv (MemStateFreshT (itree Eff)).
    Proof.
      split.
      intros A x y EQ.
      cbn in EQ.
      unfold Monad.eq1 in *.
      unfold MonadState.Eq1_stateTM in *.
      unfold pointwise_relation in *.
      specialize (EQ 0%N).
      specialize (EQ initial_memory_state).
      unfold Monad.eq1 in *.
      unfold ITreeMonad.Eq1_ITree in *.
      cbn in EQ.
      apply eqit_inv_Ret in EQ.
      inv EQ.
      reflexivity.
    Qed.

    #[global] Instance MemStateFreshT_run_Proper {A Eff} :
      Proper (Monad.eq1 ==> eq ==> eq ==> Monad.eq1) (@MemStateFreshT_run A Eff).
    Proof.
      unfold Proper, respectful.
      intros x y H2 x0 y0 H3 x1 y1 H4; subst.
      cbn. do 2 red.
      do 8 red in H2.
      rewrite H2.
      reflexivity.
    Qed.

    #[global] Instance MemStateFreshT_MemMonad {Eff} `{FAIL: FailureE -< Eff} `{OOM: OOME -< Eff} `{UB: UBE -< Eff}
      : MemMonad MemStateFreshT_State (MemStateFreshT (itree Eff)) (itree Eff).
    Proof.
      esplit with
        (MemMonad_run := fun A => @MemStateFreshT_run A Eff)
        (MemMonad_valid_state := MemStateFreshT_valid_state); try solve [typeclasses eauto].

      (* TODO: didn't need valid for ret / bind laws... *)
      - (* run bind *)
        intros A B ma k ms sid.
        unfold MemStateFreshT_run.
        cbn.
        rewrite map_bind.
        rewrite bind_map.
        eapply eutt_clo_bind.
        reflexivity.
        intros u1 u2 H2; subst.
        destruct u2 as [ms' [sid' x]].
        cbn.
        reflexivity.
      - (* run ret *)
        intros A x ms sid.
        cbn.
        rewrite map_ret.
        reflexivity.
      - (* get_mem_state *)
        intros ms sid.
        cbn.
        rewrite map_bind.
        repeat rewrite bind_ret_l.
        rewrite map_ret.
        cbn.
        reflexivity.
      - (* put_mem_state *)
        intros ms ms' sid.
        cbn.
        rewrite map_bind.
        repeat rewrite bind_ret_l.
        rewrite map_ret.
        cbn.
        reflexivity.
      - (* fresh_sid *)
        intros ms sid VALID_SID.
        do 2 eexists.
        cbn.
        rewrite map_bind.
        rewrite bind_ret_l.
        rewrite map_bind.
        rewrite bind_ret_l.
        rewrite map_ret.
        cbn.
        split; [reflexivity|].

        split.
        + red.
          intros sid' USED.
          apply VALID_SID in USED.
          lia.
        + intros USED.
          apply VALID_SID in USED.
          lia.
      - (* fresh_provenance *)
        intros ms sid VALID_SID.

        destruct (mem_state_fresh_provenance ms) as [pr' ms'] eqn:HFRESH.
        exists ms'. exists pr'.
        cbn.
        rewrite map_bind.
        repeat setoid_rewrite bind_ret_l.
        cbn.
        rewrite HFRESH.
        repeat setoid_rewrite bind_ret_l.
        cbn.

        split; [|split].
        + reflexivity.
        + unfold MemStateFreshT_valid_state in *; auto.
          unfold used_store_id, used_store_id_prop in *. cbn in *.
          unfold used_store_id, used_store_id_prop in *. cbn in *.
          unfold read_byte_prop.
          apply mem_state_fresh_provenance_fresh in HFRESH as [MEM [NUSED USED]].
          rewrite <- MEM.

          auto.
        + unfold used_provenance.
          apply mem_state_fresh_provenance_fresh; auto.
      - (* raise_oom *)
        intros A ms oom_msg sid.
        cbn.
        rewrite map_bind.
        setoid_rewrite Raise.raiseOOM_bind_itree.
        reflexivity.
      - (* raise_oom_inv *)
        intros A x oom_msg.
        intros EQ.
        pinversion EQ.
      - (* raise_ub *)
        intros A ms oom_msg sid.
        cbn.
        rewrite map_bind.
        setoid_rewrite Raise.raiseUB_bind_itree.
        reflexivity.
      - (* raise_ub_inv *)
        intros A x ub_msg.
        intros EQ.
        pinversion EQ.
      - (* raise_error *)
        intros A ms oom_msg sid.
        cbn.
        rewrite map_bind.
        setoid_rewrite Raise.raise_bind_itree.
        reflexivity.
      - (* raise_error_inv *)
        intros A x error_msg.
        intros EQ.
        pinversion EQ.
      - (* raise_oom_raise_error_inv *)
        intros A oom_msg error_msg.
        apply oom_error_inv.
      - (* raise_error_raise_oom_inv *)
        intros A oom_msg error_msg.
        intros EQ.
        symmetry in EQ.
        apply oom_error_inv in EQ; auto.
      - intros A ub_msg error_msg.
        apply ub_error_inv.
      - intros A ub_msg error_msg EQ.
        symmetry in EQ.
        apply ub_error_inv in EQ; auto.
      - intros A oom_msg ub_msg.
        apply oom_ub_inv.
      - intros A oom_msg ub_msg EQ.
        symmetry in EQ.
        apply oom_ub_inv in EQ; auto.
    Defined.

    Definition E_trigger' : forall R, E R -> (MemStateT (PropT Effout) R) :=
      fun R e m => fun t => t ≈ r <- trigger e;; ret (m, r).

    Definition F_trigger' : forall R, F R -> (MemStateT (PropT Effout) R) :=
      fun R e m => fun t => t ≈ r <- trigger e;; ret (m, r).

    Definition E_trigger : forall R, E R -> (MemStateFreshT (PropT Effout) R) :=
      fun R e sid m => fun t => t ≈ r <- trigger e;; ret (m, (sid, r)).

    Definition F_trigger : forall R, F R -> (MemStateFreshT (PropT Effout) R) :=
      fun R e sid m => fun t => t ≈ r <- trigger e;; ret (m, (sid, r)).

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

    Definition interp_memory_prop' {R} (RR : R -> R -> Prop) :
      itree Effin R -> MemStateT (PropT Effout) R :=
      fun (t : itree Effin R) (ms : MemState) (t' : itree Effout (MemState * R)) =>
        interp_prop (OOM := void1) (fun T e t => exists ms', @interp_memory_prop_h' T e ms (fmap (fun x => (ms', x)) t)) RR t (fmap snd t').

    (* Things line up a lot better if interp_memory_prop has the same
       type signature as interp_memory... *)
    Definition interp_memory_prop {R} (RR : R -> R -> Prop) :
      itree Effin R -> MemStateFreshT (PropT Effout) R :=
      fun (t : itree Effin R) (sid : store_id) (ms : MemState) (t' : itree Effout (MemState * (store_id * R))) =>
        interp_prop (OOM := void1) (fun T (e : Effin T) (t : itree Effout T) => exists (sid' : store_id) (ms' : MemState),
                         @interp_memory_prop_h T e sid ms (fmap (fun (x : T) => (ms', (sid', x))) t)) RR t ((fmap (fun '(_, (_, x)) => x) t') : itree Effout R).
  End Interpreters.
End MemorySpecInterpreter.

Module Type MemoryExecInterpreter (LP : LLVMParams) (MP : MemoryParams LP) (MMEP : MemoryModelExecPrimitives LP MP) (MM : MemoryModelExec LP MP MMEP) (SPEC_INTERP : MemorySpecInterpreter LP MP MMEP.MMSP MMEP.MemSpec MMEP.MemExecM).
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
  Import MemExecM.

  Section Interpreters.
    Variable (E F : Type -> Type).
    Context `{FailureE -< F} `{UBE -< F} `{OOME -< F}.
    Notation Effin := (E +' IntrinsicE +' MemoryE +' F).
    Notation Effout := (E +' F).

    (* TODO: Why do I have to duplicate this >_<? *)
    (** MemMonad Instances *)
    #[global] Instance MemStateFreshT_Provenance M `{Monad M} : MonadProvenance Provenance (MemStateFreshT M).
    Proof.
      split.
      exact (lift
               (ms <- get;;
                let (pr', ms') := mem_state_fresh_provenance ms in
                put ms';;
                ret pr')).
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
      - apply (lift get).
      - intros ms; apply (lift (put ms)).
    Defined.

    #[global] Instance MemState_StoreIdFreshness : StoreIdFreshness MemState.
    Proof.
      split.
      apply used_store_id_prop.
    Defined.

    Definition MemStateFreshT_State := store_id.

    #[global] Instance MemState_ProvenanceFreshness : ProvenanceFreshness Provenance MemState.
     Proof.
       split.
       - apply used_provenance_prop.
     Defined.

    #[global] Instance MemStateFreshT_MonadT {M} `{Monad M} : MonadT (MemStateFreshT M) M.
    Proof.
      unfold MemStateFreshT.
      unfold MemStateT.
      split.
      - intros t X.
        intros sid ms.
        apply (res <- X;; ret (ms, (sid, res))).
    Defined.

    (* M may be PropT or itree... *)
    Definition MemStateFreshT_run {A} {Eff} `{FailureE -< Eff} `{OOME -< Eff} `{UBE -< Eff} (ma : MemStateFreshT (itree Eff) A) (ms : MemState) (st : MemStateFreshT_State) : itree Eff (MemStateFreshT_State * (MemState * A)).
    Proof.
      unfold MemStateFreshT in *.
      specialize (ma st ms).
      unfold MemStateFreshT_State.
      eapply fmap; [ |eauto].
      intros [ms' [s' x]].
      apply (s', (ms', x)).
    Defined.

    Definition MemStateFreshT_valid_state (ms : MemState) (st : MemStateFreshT_State) : Prop
      := let sid := st in
         (forall sid', used_store_id ms sid' -> (sid' < sid)%N).

    #[global] Instance MemStateFreshT_MemMonad {Eff} `{FAIL: FailureE -< Eff} `{OOM: OOME -< Eff} `{UB: UBE -< Eff}
      : MemMonad MemStateFreshT_State (MemStateFreshT (itree Eff)) (itree Eff).
    Proof.
      esplit with
        (MemMonad_run := fun A => @MemStateFreshT_run A Eff FAIL OOM UB)
        (MemMonad_valid_state := MemStateFreshT_valid_state); try solve [typeclasses eauto].

      (* TODO: didn't need valid for ret / bind laws... *)
      - (* run bind *)
        intros A B ma k ms sid.
        unfold MemStateFreshT_run.
        cbn.
        rewrite map_bind.
        rewrite bind_map.
        eapply eutt_clo_bind.
        reflexivity.
        intros u1 u2 H2; subst.
        destruct u2 as [ms' [sid' x]].
        cbn.
        reflexivity.
      - (* run ret *)
        intros A x ms sid.
        cbn.
        rewrite map_ret.
        reflexivity.
      - (* get_mem_state *)
        intros ms sid.
        cbn.
        rewrite map_bind.
        repeat rewrite bind_ret_l.
        rewrite map_ret.
        cbn.
        reflexivity.
      - (* put_mem_state *)
        intros ms ms' sid.
        cbn.
        rewrite map_bind.
        repeat rewrite bind_ret_l.
        rewrite map_ret.
        cbn.
        reflexivity.
      - (* fresh_sid *)
        intros ms sid VALID_SID.
        do 2 eexists.
        cbn.
        rewrite map_bind.
        rewrite bind_ret_l.
        rewrite map_bind.
        rewrite bind_ret_l.
        rewrite map_ret.
        cbn.
        split; [reflexivity|].

        split.
        + red.
          intros sid' USED.
          apply VALID_SID in USED.
          lia.
        + intros USED.
          apply VALID_SID in USED.
          lia.
      - (* fresh_provenance *)
        intros ms sid VALID_SID.

        destruct (mem_state_fresh_provenance ms) as [pr' ms'] eqn:HFRESH.
        exists ms'. exists pr'.
        cbn.
        rewrite map_bind.
        repeat setoid_rewrite bind_ret_l.
        cbn.
        rewrite HFRESH.
        repeat setoid_rewrite bind_ret_l.
        cbn.

        split; [|split].
        + reflexivity.
        + unfold MemStateFreshT_valid_state in *; auto.
          unfold used_store_id, used_store_id_prop in *. cbn in *.
          unfold used_store_id, used_store_id_prop in *. cbn in *.
          unfold read_byte_prop.
          apply mem_state_fresh_provenance_fresh in HFRESH as [MEM [NUSED USED]].
          rewrite <- MEM.

          auto.
        + unfold used_provenance.
          apply mem_state_fresh_provenance_fresh; auto.
      - (* raise_oom *)
        intros A ms oom_msg sid.
        cbn.
        rewrite map_bind.
        setoid_rewrite Raise.raiseOOM_bind_itree.
        reflexivity.
      - (* raise_oom_inv *)
        intros A x oom_msg.
        intros EQ.
        pinversion EQ.
      - (* raise_ub *)
        intros A ms oom_msg sid.
        cbn.
        rewrite map_bind.
        setoid_rewrite Raise.raiseUB_bind_itree.
        reflexivity.
      - (* raise_ub_inv *)
        intros A x ub_msg.
        intros EQ.
        pinversion EQ.
      - (* raise_error *)
        intros A ms oom_msg sid.
        cbn.
        rewrite map_bind.
        setoid_rewrite Raise.raise_bind_itree.
        reflexivity.
      - (* raise_error_inv *)
        intros A x error_msg.
        intros EQ.
        pinversion EQ.
      - (* raise_oom_raise_error_inv *)
        intros A oom_msg error_msg.
        eapply oom_error_inv; eauto.
      - (* raise_error_raise_oom_inv *)
        intros A oom_msg error_msg.
        intros EQ.
        symmetry in EQ.
        eapply oom_error_inv in EQ; eauto.
      - intros A ub_msg error_msg.
        eapply ub_error_inv; eauto.
      - intros A ub_msg error_msg EQ.
        symmetry in EQ.
        eapply ub_error_inv in EQ; eauto.
      - intros A oom_msg ub_msg.
        eapply oom_ub_inv; eauto.
      - intros A oom_msg ub_msg EQ.
        symmetry in EQ.
        eapply oom_ub_inv in EQ; eauto.
    Defined.

    (** Handlers *)
    Definition E_trigger : E ~> MemStateFreshT (itree Effout) :=
      fun R e sid m => r <- trigger e;; ret (m, (sid, r)).

    Definition F_trigger : F ~> MemStateFreshT (itree Effout) :=
      fun R e sid m => r <- trigger e;; ret (m, (sid, r)).

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
    State.interp_state interp_memory_h.

    (* fmap throws away extra sid / provenance from state
       handler. This is fine because interp_memory_prop should include
       propositions that make sure ids and provenances are fresh when
       necessary.
     *)
    Lemma interp_memory_correct :
      forall {T} t (ms : MemState) (sid : store_id),
        interp_memory_prop eq t sid ms (@interp_memory T t sid ms).
    Proof.
      intros T t ms sid.
      unfold interp_memory_prop.
      unfold interp_memory.
      unfold State.interp_state.

    Admitted.
  End Interpreters.
End MemoryExecInterpreter.


Module MakeMemorySpecInterpreter (LP : LLVMParams) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MS : MemoryModelSpec LP MP MMSP) (MemExecM : MemoryExecMonad LP MP MMSP MS) <: MemorySpecInterpreter LP MP MMSP MS MemExecM.
  Include MemorySpecInterpreter LP MP MMSP MS MemExecM.
End MakeMemorySpecInterpreter.

Module MakeMemoryExecInterpreter (LP : LLVMParams) (MP : MemoryParams LP) (MMEP : MemoryModelExecPrimitives LP MP) (ME : MemoryModelExec LP MP MMEP) (SPEC_INTERP : MemorySpecInterpreter LP MP MMEP.MMSP MMEP.MemSpec MMEP.MemExecM) <: MemoryExecInterpreter LP MP MMEP ME SPEC_INTERP.
  Include MemoryExecInterpreter LP MP MMEP ME SPEC_INTERP.
End MakeMemoryExecInterpreter.
