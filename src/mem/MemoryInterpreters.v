From Coq Require Import
     Morphisms
     ZArith
     Lia
     Program.Equality.

From Vellvm.Semantics Require Import
     MemoryParams
     Memory.ErrSID
     LLVMParams
     LLVMEvents
     StoreId.

From Vellvm.Handlers Require Import
     MemoryModel
     MemPropT
     MemoryModules.Within.

From Vellvm.Utils Require Import
     Tactics
     InterpProp
     VellvmRelations
     StateMonads Raise Tactics ITreeMap.

From Vellvm.Theory Require Import
  ContainsUBExtra.

From ITree Require Import
     ITree
     Eq.Eqit
     Eq.EqAxiom
     Events.StateFacts.

Import HeterogeneousRelations.

From ExtLib Require Import
     Structures.Functor
     Structures.Monads.

(* Needs to be after ITree.Events.State *)
From Vellvm.Utils Require Import
     PropT InterpMemoryProp.

Require Import Paco.paco.

Import Basics.Basics.Monads.
Import MonadNotation.

Import MemoryAddress.
Import Error.

Set Implicit Arguments.
Set Contextual Implicit.

Ltac raise_abs :=
  let H := fresh "H" in
  intro H; unfold raise_oom, raise_ub, raise_error in H;
  cbn in H; unfold raiseOOM, raiseUB, LLVMEvents.raise in H;
  do 2 rewrite bind_trigger in H;
  do 2 red in H; unfold subevent in H; red in H;
  punfold H; inversion H; subst;
  match goal with
  | [ H : existT _ _ _ = existT _ _ _ |- _] => dependent destruction H
  end.


Module Type MemorySpecInterpreter (LP : LLVMParams) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MM : MemoryModelSpec LP MP MMSP) (MemExecM : MemoryExecMonad LP MP MMSP MM).
  Import MM.
  Import MMSP.
  Import MemExecM.
  Import LP.Events.
  Import LP.PROV.

  Section Interpreters.

    Context {E : Type -> Type}.

    Notation F := (PickUvalueE +' OOME +' UBE +' DebugE +' FailureE).

    Notation Effin := (E +' IntrinsicE +' MemoryE +' F).
    Notation Effout := (E +' F).

    Definition MemStateT M := stateT MemState M.
    Definition MemStateFreshT M := stateT store_id (MemStateT M).

    Definition MemStateFreshT_from_MemStateT {M X} `{Monad M} (mst : MemStateT M X) : MemStateFreshT M X :=
      fun sid => x <- mst;; ret (sid, x).

    (** MemMonad Instances *)
    #[global] Instance MemStateFreshT_Provenance M `{Monad M} : MonadProvenance Provenance (MemStateFreshT M).
    Proof using.
      split.
      exact (lift
               (ms <- get;;
                let (pr', ms') := mem_state_fresh_provenance ms in
                put ms';;
                ret pr')).
    Defined.

    #[global] Instance MemStateFreshT_MonadStoreId M `{Monad M} : MonadStoreId (MemStateFreshT M).
    Proof using.
      split.
      unfold MemStateFreshT.
      apply (sid <- get;;
             let sid' := BinNatDef.N.succ sid in
             put sid';;
             ret sid).
    Defined.

    #[global] Instance MemStateFreshT_MonadMemState M `{Monad M} : MonadMemState MemState (MemStateFreshT M).
    Proof using.
      split.
      - apply (lift get).
      - intros ms; apply (lift (put ms)).
    Defined.

    #[global] Instance MemState_StoreIdFreshness : StoreIdFreshness MemState.
    Proof using.
      split.
      apply used_store_id_prop.
    Defined.

    Definition MemStateFreshT_State := store_id.

    #[global] Instance MemState_ProvenanceFreshness : ProvenanceFreshness Provenance MemState.
     Proof using.
       split.
       - apply used_provenance_prop.
     Defined.

    #[global] Instance MemState_memory_MemStateMem : MemStateMem MemState memory_stack :=
      {| ms_get_memory := MemState_get_memory;
        ms_put_memory := MemState_put_memory;
        ms_get_put_memory := MemState_get_put_memory;
      |}.

    #[global] Instance MemStateFreshT_MonadT {M} `{Monad M} : MonadT (MemStateFreshT M) M.
    Proof using.
      unfold MemStateFreshT.
      unfold MemStateT.
      split.
      - intros t X.
        intros sid ms.
        apply (res <- X;; ret (ms, (sid, res))).
    Defined.

    (* M may be PropT or itree... *)
    Definition MemStateFreshT_run {A} {Eff} (ma : MemStateFreshT (itree Eff) A) (ms : MemState) (st : MemStateFreshT_State) : itree Eff (MemStateFreshT_State * (MemState * A)).
    Proof using.
      unfold MemStateFreshT in *.
      specialize (ma st ms).
      unfold MemStateFreshT_State.
      eapply fmap; [ |eauto].
      intros [ms' [s' x]].
      apply (s', (ms', x)).
    Defined.

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
  Proof using.
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
  Proof using.
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

    Import MonadEq1Laws.

    #[global] Instance MemStateFreshT_Eq1_ret_inv {Eff} `{FAIL: FailureE -< Eff} `{OOM: OOME -< Eff} `{UB: UBE -< Eff}
      : Eq1_ret_inv (MemStateFreshT (itree Eff)).
    Proof using.
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
    Proof using.
      unfold Proper, respectful.
      intros x y H2 x0 y0 H3 x1 y1 H4; subst.
      cbn. do 2 red.
      do 8 red in H2.
      rewrite H2.
      reflexivity.
    Qed.

    #[global] Instance MemStateFreshT_MemMonad:
      MemMonad (MemStateFreshT (itree F)) (itree F).
    Proof using.
      esplit with
        (MemMonad_run := fun A => @MemStateFreshT_run A F); try solve [typeclasses eauto].
      13-18:intros; raise_abs.

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

        split; [|split; [|split]].
        + red.
          intros sid' USED.
          apply VALID_SID in USED.
          lia.
        + lia.
        + lia.
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
        + unfold MemMonad_valid_state in *; auto.
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
    Defined.

    Definition E_trigger' : forall R, E R -> (MemStateT (PropT Effout) R) :=
      fun R e m => fun t => t ≈ r <- trigger e;; ret (m, r).

    Definition F_trigger' : forall R, F R -> (MemStateT (PropT Effout) R) :=
      fun R e m => fun t => t ≈ r <- trigger e;; ret (m, r).

    Definition E_trigger : forall R, E R -> (MemStateFreshT (PropT Effout) R) :=
      fun R e sid m => fun t => t ≈ r <- trigger e;; ret (m, (sid, r)).

    Definition F_trigger : forall R, F R -> (MemStateFreshT (PropT Effout) R) :=
      fun R e sid m => fun t => t ≈ r <- trigger e;; ret (m, (sid, r)).

    (* Should line up with exec_correct *)
    Definition MemPropT_lift_PropT_fresh {X} {EFF} `{UBE -< EFF} `{OOME -< EFF} `{FailureE -< EFF} (spec : MemPropT MemState X) :
      stateT store_id (stateT MemState (PropT EFF)) X.
    Proof.
      unfold PropT, MemPropT, stateT in *.

      refine
        (fun st ms t =>
           (* UB *)
           (exists msg_spec,
               spec ms (raise_ub msg_spec)) \/
             (* Error *)
             ((exists msg,
                  t ≈ (raise_error msg) /\
                    exists msg_spec, spec ms (raise_error msg_spec))) \/
             (* OOM *)
             (exists msg,
                 t ≈ (raise_oom msg) /\
                   exists msg_spec, spec ms (raise_oom msg_spec)) \/
             (* Success *)
             (exists st' ms' x,
                 MemMonad_valid_state ms st /\
                 t ≈ (ret (ms', (st', x))) /\
                   spec ms (ret (ms', x)) /\
                   MemMonad_valid_state ms' st')).
    Defined.

    (* TODO: get rid of this silly hack. *)
    Definition my_handle_memory_prop' :
      forall T : Type, MemoryE T -> MemStateT (PropT Effout) T.
    Proof using.
      intros T MemE.
      eapply MemPropT_lift_PropT.
      eapply handle_memory_prop; auto.
    Defined.

    Definition my_handle_intrinsic_prop' :
      forall T : Type, IntrinsicE T -> MemStateT (PropT Effout) T.
    Proof using.
      intros T IntE.
      eapply MemPropT_lift_PropT.
      eapply handle_intrinsic_prop; auto.
    Defined.

    Definition my_handle_memory_prop :
      forall T : Type, MemoryE T -> MemStateFreshT (PropT Effout) T.
    Proof using.
      intros T MemE.
      eapply MemPropT_lift_PropT_fresh.
      eapply handle_memory_prop; auto.
    Defined.

    Definition my_handle_intrinsic_prop :
      forall T : Type, IntrinsicE T -> MemStateFreshT (PropT Effout) T.
    Proof using.
      intros T IntE.
      unfold MemStateFreshT.
      unfold MemStateT.
      unfold PropT.
      unfold stateT.
      eapply MemPropT_lift_PropT_fresh.
      eapply handle_intrinsic_prop; auto.
    Defined.

    Definition memory_k_spec
               {T R : Type}
               (e : Effin T)
               (ta : itree Effout (MemState * (store_id * T)))
               (k2 : (MemState * (store_id * T)) -> itree Effout (MemState * (store_id * R)))
               (t2 : itree Effout (MemState * (store_id * R))) : Prop
      := contains_UB_Extra ta \/ eutt (prod_rel MM.MemState_eqv eq) t2 (bind ta k2).
(* /\
   Proper (prod_rel MM.MemState_eqv eq ==> eutt (prod_rel MM.MemState_eqv eq)) k2) *)

    #[global] Instance memory_k_spec_proper {A R2 : Type} e ta k2 :
      Proper
        (eutt eq ==> iff)
        (@memory_k_spec A R2 e ta k2).
    Proof using.
      unfold Proper, respectful.
      intros x y EQV.
      split; intros K_SPEC;
        red; red in K_SPEC; destruct K_SPEC as [UB | K_SPEC];
        eauto; right;
        first [rewrite EQV | rewrite <- EQV];
        eauto.
    Qed.

    #[global] Instance memory_k_spec_Proper_S1S2_Proper {A R2 : Type} e ta k2 :
      Proper
        (eutt (prod_rel MM.MemState_eqv (prod_rel eq eq)) ==> iff)
        (@memory_k_spec A R2 e ta k2).
    Proof using.
      unfold Proper, respectful.
      intros x y EQV.
      split; intros K_SPEC;
        red; red in K_SPEC; destruct K_SPEC as [UB | K_SPEC];
        eauto; right.
      - rewrite prod_rel_eq in EQV.
        rewrite <- EQV.
        auto.
      - rewrite prod_rel_eq in EQV.
        rewrite EQV.
        auto.
    Qed.

    #[global] Instance k_spec_Proper_S1S2_memory_k_spec : k_spec_Proper_S1S2 (@memory_k_spec) eq MM.MemState_eqv.
    Proof using.
      split.
      typeclasses eauto.
    Qed.

    Definition interp_memory_spec_h : forall T, Effin T -> MemStateFreshT (PropT Effout) T
      := case_ E_trigger (case_ my_handle_intrinsic_prop (case_ my_handle_memory_prop F_trigger)).

    #[global] Instance memory_k_spec_WF : @k_spec_WF store_id MemState _ _ interp_memory_spec_h (@memory_k_spec).
    Proof using.
      split.
      - (* k_spec_Proper *)
        typeclasses eauto.
      - (* k_spec_Correct *)
        red.
        intros T R2 e k2 t2 s1 s2 ta H_SPEC BIND.
        unfold memory_k_spec.
        right.
        rewrite BIND.
        reflexivity.
    Qed.

    Definition interp_memory_spec {R1 R2} (RR : R1 -> R2 -> Prop) :
      itree Effin R1 -> MemStateFreshT (PropT Effout) R2 :=
      fun (t : itree Effin R1) (sid : store_id) (ms : MemState) (t' : itree Effout (MemState * (store_id * R2))) =>
        interp_memory_prop (OOM:=OOME) interp_memory_spec_h (fun x '(ms', (sid', y)) => RR x y) (@memory_k_spec) t t'.

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

  Module MemTheory := MemoryModelTheory LP MP MMEP MM.
  Import MemTheory.

  Section Interpreters.

    Context {E : Type -> Type}.
    Notation E := ExternalCallE.
    Notation F := (PickUvalueE +' OOME +' UBE +' DebugE +' FailureE).

    Notation Effin := (E +' IntrinsicE +' MemoryE +' F).
    Notation Effout := (E +' F).

    (* TODO: Why do I have to duplicate this >_<? *)
    (** MemMonad Instances *)
    #[global] Instance MemStateFreshT_Provenance M `{Monad M} : MonadProvenance Provenance (MemStateFreshT M).
    Proof using.
      split.
      exact (lift
               (ms <- get;;
                let (pr', ms') := mem_state_fresh_provenance ms in
                put ms';;
                ret pr')).
    Defined.

    #[global] Instance MemStateFreshT_MonadStoreId M `{Monad M} : MonadStoreId (MemStateFreshT M).
    Proof using.
      split.
      unfold MemStateFreshT.
      apply (sid <- get;;
             let sid' := BinNatDef.N.succ sid in
             put sid';;
             ret sid).
    Defined.

    #[global] Instance MemStateFreshT_MonadMemState M `{Monad M} : MonadMemState MemState (MemStateFreshT M).
    Proof using.
      split.
      - apply (lift get).
      - intros ms; apply (lift (put ms)).
    Defined.

    #[global] Instance MemState_StoreIdFreshness : StoreIdFreshness MemState.
    Proof using.
      split.
      apply used_store_id_prop.
    Defined.

    Definition MemStateFreshT_State := store_id.

    #[global] Instance MemState_ProvenanceFreshness : ProvenanceFreshness Provenance MemState.
     Proof using.
       split.
       - apply used_provenance_prop.
     Defined.

    #[global] Instance MemStateFreshT_MonadT {M} `{Monad M} : MonadT (MemStateFreshT M) M.
    Proof using.
      unfold MemStateFreshT.
      unfold MemStateT.
      split.
      - intros t X.
        intros sid ms.
        apply (res <- X;; ret (ms, (sid, res))).
    Defined.

    (* M may be PropT or itree... *)
    Definition MemStateFreshT_run {A} {Eff} `{FailureE -< Eff} `{OOME -< Eff} `{UBE -< Eff} (ma : MemStateFreshT (itree Eff) A) (ms : MemState) (st : MemStateFreshT_State) : itree Eff (MemStateFreshT_State * (MemState * A)).
    Proof using.
      unfold MemStateFreshT in *.
      specialize (ma st ms).
      unfold MemStateFreshT_State.
      eapply fmap; [ |eauto].
      intros [ms' [s' x]].
      apply (s', (ms', x)).
    Defined.

    #[global] Instance MemStateFreshT_MemMonad :
      MemMonad (MemStateFreshT (itree Effout)) (itree Effout).
    Proof using.
      esplit with
        (MemMonad_run := fun A => @MemStateFreshT_run A Effout _ _ _); try solve [typeclasses eauto].
      13-18: intros; raise_abs.

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

        split; [|split; [|split]]; try lia.
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
        + unfold MemMonad_valid_state in *; auto.
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
    Defined.

    (** Handlers *)
    Definition E_trigger : E ~> MemStateFreshT (itree Effout) :=
      fun R e sid m => r <- trigger e;; ret (m, (sid, r)).

    Definition F_trigger : F ~> MemStateFreshT (itree Effout) :=
      fun R e sid m => r <- trigger e;; ret (m, (sid, r)).

    (* TODO: get rid of this silly hack. *)
    Definition my_handle_memory : MemoryE ~> MemStateFreshT (itree Effout) :=
      @handle_memory (MemStateFreshT (itree Effout)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MemStateFreshT_MemMonad.

    Definition my_handle_intrinsic : IntrinsicE ~> MemStateFreshT (itree Effout) :=
      @handle_intrinsic (MemStateFreshT (itree Effout)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MemStateFreshT_MemMonad.

    Definition interp_memory_h : Effin ~> MemStateFreshT (itree Effout)
      := case_ E_trigger (case_ my_handle_intrinsic (case_ my_handle_memory F_trigger)).

    Definition interp_memory :
      itree Effin ~> MemStateFreshT (itree Effout) :=
    State.interp_state interp_memory_h.

    (* Interp Laws for [interp_memory] *)
    Definition _interp_memory {E F R}
              (f : E ~> MemStateFreshT (itree F)) (ot : itreeF E R _)
      : MemStateFreshT (itree F) R := fun s sid =>
      match ot with
      | RetF r => Ret (sid, (s, r))
      | TauF t => Tau (State.interp_state f t s sid)
      | VisF _ e k => f _ e s sid >>= (fun '(sid', sx) => Tau (State.interp_state f (k (snd sx)) (fst sx) sid'))
      end.

    Lemma unfold_interp_memory {R} t s sid :
        eq_itree eq
          (interp_memory t s sid)
          (_interp_memory (R := R) interp_memory_h (observe t) s sid).
    Proof using.
      unfold interp_memory, State.interp_state,
        interp, Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_itree; cbn.
      rewrite unfold_iter; cbn.
      destruct observe; cbn.
      - rewrite 3 bind_ret_l. reflexivity.
      - rewrite 3 bind_ret_l. reflexivity.
      - rewrite bind_map, bind_bind; cbn.
        rewrite bind_bind. setoid_rewrite bind_ret_l.
        apply eqit_bind. reflexivity.
        intro; subst. rewrite bind_ret_l; cbn.
        destruct a; reflexivity.
    Qed.

    Lemma interp_memory_ret {R} s sid (r : R):
      (interp_memory (Ret r) s sid) ≅ (Ret (sid, (s, r))).
    Proof using.
      rewrite itree_eta. reflexivity.
    Qed.

    Lemma interp_memory_tau {R} t s sid :
      (interp_memory (T := R) (Tau t) s sid) ≅ Tau (interp_memory t s sid).
    Proof using.
      rewrite unfold_interp_memory; reflexivity.
    Qed.

    Lemma interp_memory_vis {T R} e k s sid :
      interp_memory (T := T) (Vis e k) s sid
        ≅ interp_memory_h e s sid >>= fun '(sid', sx) => Tau (interp_memory (k (snd sx)) (fst (B := R) sx) sid').
    Proof using.
      rewrite unfold_interp_memory; reflexivity.
    Qed.

    Lemma my_handle_intrinsic_prop_correct {T} i sid ms (VALID: MemMonad_valid_state ms sid) :
      my_handle_intrinsic_prop i sid ms (my_handle_intrinsic (T := T) i sid ms).
    Proof using.
      unfold my_handle_intrinsic_prop, my_handle_intrinsic.
      cbn.

      (* TODO: probably an easier more general lemma about
         [exec_correct] and [MemPropT_lift_PropT_fresh] *)
      epose proof @handle_intrinsic_correct (MemStateFreshT (itree Effout)) Effout
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T i (fun _ _ => True) as HANDLE_CORRECT.

      red in HANDLE_CORRECT.
      specialize (HANDLE_CORRECT ms sid).
      forward HANDLE_CORRECT.
      { auto.
      }

      specialize (HANDLE_CORRECT I).

      destruct HANDLE_CORRECT as [[ms' [ub_msg UB]] | HANDLE_CORRECT].
      { (* UB.. *)
        left.
        exists ub_msg; eauto.
      }

      (* Not necessarily UB *)
      destruct HANDLE_CORRECT as [exec_res [st' [ms' [EXEC [SPEC POST]]]]].
      cbn in *.
      red in EXEC, SPEC.
      destruct EXEC as [m2 [EXEC EXEC_IN]].
      cbn in EXEC.
      red in EXEC.

      cbn in EXEC_IN.
      red in EXEC_IN.

      destruct_err_ub_oom exec_res.

      { (* OOM *)
        cbn in *.
        destruct EXEC as [oom_msg EXEC].
        rewrite EXEC in EXEC_IN.

        setoid_rewrite (@rbm_raise_bind _ _ _ _ _ (RaiseBindM_OOM _)) in EXEC_IN.
        apply raiseOOM_map_itree_inv in EXEC_IN.

        red.
        right; right; left.
        exists oom_msg.
        split; auto.
        exists oom_x; auto.
      }

      { (* UB events *)
        red.
        left.
        exists ub_x.
        auto.
      }

      { (* Error *)
        cbn in *.
        destruct EXEC as [err_msg EXEC].
        rewrite EXEC in EXEC_IN.
        setoid_rewrite (@rbm_raise_bind _ _ _ _ _ (RaiseBindM_Fail _)) in EXEC_IN.
        apply raise_map_itree_inv in EXEC_IN.

        red.
        right; left.
        exists err_msg.
        split; auto.
        exists err_x; auto.
      }

      { (* Success *)
        subst.
        cbn in *.
        rewrite EXEC in EXEC_IN.
        rewrite bind_ret_l in EXEC_IN.
        apply itree_map_ret_inv in EXEC_IN.
        destruct EXEC_IN as [[ms'' [sid'' res]] [EXEC_IN RES_EQ]].
        inv RES_EQ.

        red.
        right; right; right.
        do 3 eexists.
        split; eauto.
        split; eauto.
        split; eauto.
        eapply POST.
        eauto.
      }
    Qed.

    (* TODO: Import result from [handle_memory_correct]*)
    Lemma my_handle_memory_prop_correct {T} m sid ms (VALID: MemMonad_valid_state ms sid) :
      my_handle_memory_prop m sid ms (my_handle_memory (T := T) m sid ms).
      unfold my_handle_memory_prop, my_handle_memory.
      cbn.

      (* TODO: probably an easier more general lemma about
         [exec_correct] and [MemPropT_lift_PropT_fresh] *)      
      epose proof @handle_memory_correct (MemStateFreshT (itree Effout)) Effout
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T m (fun _ _ => True) as HANDLE_CORRECT.

      red in HANDLE_CORRECT.
      specialize (HANDLE_CORRECT ms sid).
      forward HANDLE_CORRECT; auto.
      specialize (HANDLE_CORRECT I).

      destruct HANDLE_CORRECT as [[ms' [ub_msg UB]] | HANDLE_CORRECT].
      { (* UB.. *)
        left.
        exists ub_msg; eauto.
      }

      (* Not necessarily UB *)
      destruct HANDLE_CORRECT as [exec_res [st' [ms' [EXEC [SPEC POST]]]]].
      cbn in *.
      red in EXEC, SPEC.
      destruct EXEC as [m2 [EXEC EXEC_IN]].
      cbn in EXEC.
      red in EXEC.

      cbn in EXEC_IN.
      red in EXEC_IN.

      destruct_err_ub_oom exec_res.

      { (* OOM *)
        cbn in *.
        destruct EXEC as [oom_msg EXEC].
        rewrite EXEC in EXEC_IN.

        setoid_rewrite (@rbm_raise_bind _ _ _ _ _ (RaiseBindM_OOM _)) in EXEC_IN.
        apply raiseOOM_map_itree_inv in EXEC_IN.

        red.
        right; right; left.
        exists oom_msg.
        split; auto.
        exists oom_x; auto.
      }

      { (* UB events *)
        red.
        left.
        exists ub_x.
        auto.
      }

      { (* Error *)
        cbn in *.
        destruct EXEC as [err_msg EXEC].
        rewrite EXEC in EXEC_IN.
        setoid_rewrite (@rbm_raise_bind _ _ _ _ _ (RaiseBindM_Fail _)) in EXEC_IN.
        apply raise_map_itree_inv in EXEC_IN.

        red.
        right; left.
        exists err_msg.
        split; auto.
        exists err_x; auto.
      }

      { (* Success *)
        subst.
        cbn in *.
        rewrite EXEC in EXEC_IN.
        rewrite bind_ret_l in EXEC_IN.
        apply itree_map_ret_inv in EXEC_IN.
        destruct EXEC_IN as [[ms'' [sid'' res]] [EXEC_IN RES_EQ]].
        inv RES_EQ.

        red.
        right; right; right.
        do 3 eexists.
        split; eauto.
        split; eauto.
        split; eauto.
        eapply POST; eauto.
      }
    Qed.

    (* fmap throws away extra sid / provenance from state
       handler. This is fine because interp_memory_prop should include
       propositions that make sure ids and provenances are fresh when
       necessary.
     *)
    Lemma interp_memory_correct :
      forall {T} t (ms : MemState) (sid : store_id)
        (VALID: MemMonad_valid_state ms sid),
        interp_memory_spec eq t sid ms (@interp_memory T t sid ms).
    Proof using.
      intros T t ms sid VALID.
      red.
      unfold interp_memory_spec.
      unfold interp_memory.
      cbn.
      match goal with
      | |- InterpMemoryProp.interp_memory_prop _ _ _ _ ?i => remember i
      end.
      match goal with
      | [H : i = ?r |- _] => assert (i ≅ r) by (subst; reflexivity)
      end. clear Heqi.
      rename H into EQ.

      revert t i EQ.
      revert ms sid VALID.
      pcofix CIH.
      intros.
      pstep.
      red.

      unfold State.interp_state in EQ.
      force_rewrite: (itree_eta t) in EQ.
      force_rewrite: (itree_eta i) in EQ.
      genobs t ot.
      genobs i oi.
      clear t i Heqot Heqoi.
      hinduction ot before CIH; intros; subst.
      - force_rewrite: @interp_memory_ret in EQ.
        apply eqitree_inv_Ret_r in EQ.
        cbn in EQ; subst.
        constructor; auto.
      - pclearbot.
        force_rewrite: @interp_memory_tau in EQ. subst.
        apply eqitree_inv_Tau_r in EQ.
        destruct EQ as (?&?&?).
        cbn in H; subst.
        constructor.
        right.
        eapply CIH; eauto.
      - pclearbot.
        force_rewrite: @interp_memory_vis in EQ.
        cbn in *.
        symmetry in EQ.
        rewrite itree_eta'.
        remember ({| _observe := oi |}) as oi'.
        clear oi Heqoi'.
        (* I should only need `MemMonad_valid_state m s` in the successful cases...
           Not in the cases where UB / OOM / Error occurs...

           If UB / OOM / Error occurs, do I need CIH?
         *)
        destruct e.
        { (* Abstract E events that don't touch ms / sid *)
          cbn in *.
          eapply Interp_Memory_PropT_Vis
            with (k2:=(fun '(sid', sx) => (interp_memory (k (snd sx)) (fst sx) sid'))).
          2: {
            cbn.
            red.
            reflexivity.
          }
          2: {
            repeat red.
            right.
            rewrite <- EQ.
            cbn.
            eapply eutt_clo_bind.
            reflexivity.
            intros ? ? ?; subst.
            destruct u2.
            rewrite tau_eutt.
            reflexivity.
          }

          intros a b H H0 H1.
          apply Returns_bind_inversion in H0.
          destruct H0 as (?&?&?).
          apply Returns_ret_inv in H2; inv H2; auto.
          right.
          cbn.
          eapply CIH; eauto.
          reflexivity.
        }

        destruct s.
        { (* Intrinsics *)
          cbn in *.
          pose proof (@my_handle_intrinsic_prop_correct _ i _ _ VALID) as CORRECT.
          repeat red in CORRECT.
          destruct CORRECT.
          { (* UB case *)
            destruct H as (ub_msg & UB).
            eapply Interp_Memory_PropT_Vis
              with (ta:=(raise_ub ub_msg)).
            2: {
              repeat red.
              left.
              exists ub_msg.
              apply UB.
            }
            2: {
              repeat red.
              left.
              eapply FindUB.
              pstep; red; cbn.
              constructor.
              intros [].
            }

            intros a (?&?&?) RETa RETb AB; cbn in *; subst.
            unfold raiseUB in RETb.
            rewrite bind_trigger in RETb.

            eapply Returns_vis_inversion in RETb.
            destruct RETb as [[] _].
          }
          destruct H.
          { (* Error case *)
            destruct H as (err_msg & ERR).
            eapply Interp_Memory_PropT_Vis
              with (ta:=(raise_error err_msg))
                   (k2:=(fun '(sid', sx) => (interp_memory (k (snd sx)) (fst sx) sid'))).
            2: {
              repeat red.
              right. left.
              exists err_msg.
              split.
              reflexivity.
              apply ERR.
            }
            2: {
              repeat red.
              right.
              rewrite <- EQ.
              eapply eutt_clo_bind.
              apply ERR.
              intros ? ? ?; subst.
              destruct u2 as (?&?&?).
              cbn.
              rewrite tau_eutt.
              reflexivity.
            }

            intros a (?&?&?) RETa RETb AB; cbn in *; subst.
            unfold LLVMEvents.raise in RETb.
            rewrite bind_trigger in RETb.

            eapply Returns_vis_inversion in RETb.
            destruct RETb as [[] _].
          }

          destruct H.
          { (* OOM case *)
            destruct H as (oom_msg & OOM).
            eapply Interp_Memory_PropT_Vis
              with (ta:=(raise_oom oom_msg))
                   (k2:=(fun '(sid', sx) => (interp_memory (k (snd sx)) (fst sx) sid'))).
            2: {
              repeat red.
              right. right. left.
              exists oom_msg.
              split.
              reflexivity.
              apply OOM.
            }
            2: {
              repeat red.
              right.
              rewrite <- EQ.
              eapply eutt_clo_bind.
              apply OOM.
              intros ? ? ?; subst.
              destruct u2 as (?&?&?).
              cbn.
              rewrite tau_eutt.
              reflexivity.
            }

            intros a (?&?&?) RETa RETb AB; cbn in *; subst.
            unfold raiseOOM in RETb.
            rewrite bind_trigger in RETb.

            eapply Returns_vis_inversion in RETb.
            destruct RETb as [[] _].
          }

          { (* Success case *)
            destruct H as (sid' & ms' & x & VALID' & EXEC & SPEC); auto.
            eapply Interp_Memory_PropT_Vis
              with (ta:=ret (ms', (sid', x)))
                   (k2:=(fun '(sid', sx) => (interp_memory (k (snd sx)) (fst sx) sid'))).
            2: {
              repeat red.
              right. right. right.
              exists sid', ms', x.
              split; eauto.
              split; eauto.
              reflexivity.
            }
            2: {
              repeat red.
              right.
              rewrite <- EQ.
              eapply eutt_clo_bind.
              apply EXEC.
              intros ? ? ?; subst.
              destruct u2 as (?&?&?).
              cbn.
              rewrite tau_eutt.
              reflexivity.
            }

            intros a (?&?&?) RETa RETb AB; cbn in *; subst.
            apply Returns_ret_inv in RETb.
            inv RETb.
            right.
            eapply CIH.
            2: reflexivity.

            eapply SPEC.
          }
        }

        destruct s.
        { (* Memory events *)
          cbn in *.
          pose proof (@my_handle_memory_prop_correct _ m _ _ VALID) as CORRECT.
          repeat red in CORRECT.
          destruct CORRECT.
          { (* UB case *)
            destruct H as (ub_msg & UB).
            eapply Interp_Memory_PropT_Vis
              with (ta:=(raise_ub ub_msg)).
            2: {
              repeat red.
              left.
              exists ub_msg.
              apply UB.
            }
            2: {
              repeat red.
              left.
              eapply FindUB.
              pstep; red; cbn.
              constructor.
              intros [].
            }

            intros a (?&?&?) RETa RETb AB; cbn in *; subst.
            unfold raiseUB in RETb.
            rewrite bind_trigger in RETb.

            eapply Returns_vis_inversion in RETb.
            destruct RETb as [[] _].
          }
          destruct H.
          { (* Error case *)
            destruct H as (err_msg & ERR).
            eapply Interp_Memory_PropT_Vis
              with (ta:=(raise_error err_msg))
                   (k2:=(fun '(sid', sx) => (interp_memory (k (snd sx)) (fst sx) sid'))).
            2: {
              repeat red.
              right. left.
              exists err_msg.
              split.
              reflexivity.
              apply ERR.
            }
            2: {
              repeat red.
              right.
              rewrite <- EQ.
              eapply eutt_clo_bind.
              apply ERR.
              intros ? ? ?; subst.
              destruct u2 as (?&?&?).
              cbn.
              rewrite tau_eutt.
              reflexivity.
            }

            intros a (?&?&?) RETa RETb AB; cbn in *; subst.
            unfold LLVMEvents.raise in RETb.
            rewrite bind_trigger in RETb.

            eapply Returns_vis_inversion in RETb.
            destruct RETb as [[] _].
          }

          destruct H.
          { (* OOM case *)
            destruct H as (oom_msg & OOM).
            eapply Interp_Memory_PropT_Vis
              with (ta:=(raise_oom oom_msg))
                   (k2:=(fun '(sid', sx) => (interp_memory (k (snd sx)) (fst sx) sid'))).
            2: {
              repeat red.
              right. right. left.
              exists oom_msg.
              split.
              reflexivity.
              apply OOM.
            }
            2: {
              repeat red.
              right.
              rewrite <- EQ.
              eapply eutt_clo_bind.
              apply OOM.
              intros ? ? ?; subst.
              destruct u2 as (?&?&?).
              cbn.
              rewrite tau_eutt.
              reflexivity.
            }

            intros a (?&?&?) RETa RETb AB; cbn in *; subst.
            unfold raiseOOM in RETb.
            rewrite bind_trigger in RETb.

            eapply Returns_vis_inversion in RETb.
            destruct RETb as [[] _].
          }

          { (* Success case *)
            destruct H as (sid' & ms' & x & VALID' & EXEC & SPEC & VALID''); auto.
            eapply Interp_Memory_PropT_Vis
              with (ta:=ret (ms', (sid', x)))
                   (k2:=(fun '(sid', sx) => (interp_memory (k (snd sx)) (fst sx) sid'))).
            2: {
              repeat red.
              right. right. right.
              exists sid', ms', x.
              split.
              apply VALID'.
              split; eauto; reflexivity.
            }
            2: {
              repeat red.
              right.
              rewrite <- EQ.
              eapply eutt_clo_bind.
              apply EXEC.
              intros ? ? ?; subst.
              destruct u2 as (?&?&?).
              cbn.
              rewrite tau_eutt.
              reflexivity.
            }

            intros a (?&?&?) RETa RETb AB; cbn in *; subst.
            apply Returns_ret_inv in RETb.
            inv RETb.
            right.
            eapply CIH; eauto; reflexivity.
          }
        }

        { (* Abstract F events that don't touch ms / sid *)
          cbn in *.
          eapply Interp_Memory_PropT_Vis
            with (k2:=(fun '(sid', sx) => (interp_memory (k (snd sx)) (fst sx) sid'))).
          2: {
            cbn.
            red.
            reflexivity.
          }
          2: {
            repeat red.
            right.
            rewrite <- EQ.
            cbn.
            eapply eutt_clo_bind.
            reflexivity.
            intros ? ? ?; subst.
            destruct u2.
            rewrite tau_eutt.
            reflexivity.
          }

          intros a b H H0 H1.
          apply Returns_bind_inversion in H0.
          destruct H0 as (?&?&?).
          apply Returns_ret_inv in H2; inv H2; auto.
          right.
          cbn.
          eapply CIH; eauto.
          reflexivity.
        }

        Unshelve.
        all: eauto.
        intros [].
        intros [].
    Qed.

  End Interpreters.
End MemoryExecInterpreter.

Module MakeMemorySpecInterpreter (LP : LLVMParams) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MS : MemoryModelSpec LP MP MMSP) (MemExecM : MemoryExecMonad LP MP MMSP MS) <: MemorySpecInterpreter LP MP MMSP MS MemExecM.
  Include MemorySpecInterpreter LP MP MMSP MS MemExecM.
End MakeMemorySpecInterpreter.

Module MakeMemoryExecInterpreter (LP : LLVMParams) (MP : MemoryParams LP) (MMEP : MemoryModelExecPrimitives LP MP) (ME : MemoryModelExec LP MP MMEP) (SPEC_INTERP : MemorySpecInterpreter LP MP MMEP.MMSP MMEP.MemSpec MMEP.MemExecM) <: MemoryExecInterpreter LP MP MMEP ME SPEC_INTERP.
  Include MemoryExecInterpreter LP MP MMEP ME SPEC_INTERP.
End MakeMemoryExecInterpreter.
