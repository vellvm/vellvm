From Stdlib Require Import
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
  StateMonads Raise Tactics ITreeMap
  Error.

From Vellvm.Theory Require Import
  ContainsUBExtra.

Import HeterogeneousRelations.

From ExtLib Require Import
  Structures.Functor
  Structures.Monads.

(* Needs to be after ITree.Events.State *)
From Vellvm.Utils Require Import
  PropT InterpMemoryProp NoSpecEvent.

Require Import Paco.paco.

Import Basics.Basics.Monads.
Import MonadNotation.

Import MemoryAddress.

From ITree Require Import
  ITree
  Eq.Eqit
  Eq.EqAxiom
  Events.StateFacts.

From ITreeSpec Require Import
  ITreeSpecDefinition
  ITreeSpecFacts
  ITreeSpecCombinatorFacts.


Set Implicit Arguments.
Set Contextual Implicit.

Unset Universe Checking.

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

    Notation F := (PickUvalueE +' OOME +' LLVMExcE uvalue +' UBE +' DebugE +' FailureE).

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

    Definition E_trigger' : forall R, E R -> (MemStateT (itree_spec Effout) R) :=
      fun R e m =>
        r <- trigger e;; ret (m, r).

    Definition F_trigger' : forall R, F R -> (MemStateT (itree_spec Effout) R) :=
      fun R e m =>
        r <- trigger e;; ret (m, r).

    Definition E_trigger : forall R, E R -> (MemStateFreshT (itree_spec Effout) R) :=
      fun R e sid m =>
        r <- trigger e;; ret (m, (sid, r)).

    Definition F_trigger : forall R, F R -> (MemStateFreshT (itree_spec Effout) R) :=
      fun R e sid m =>
        r <- trigger e;; ret (m, (sid, r)).

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
      forall T : Type, MemoryE T -> stateT MemState (itree_spec Effout) T.
    Proof using.
      intros T MemE ms.
      eapply handle_memory_prop in ms; eauto.
      pose proof (err_ub_oom (MemState * T)).
      refine (Vis (@Spec_forall Effout {a : (err_ub_oom (MemState * T)) | ms a}) (fun (x : {a : (err_ub_oom (MemState * T)) | ms a}) => _)).
      destruct x.
      apply (lift_err_ub_oom ret x).
    Defined.

    Definition my_handle_intrinsic_prop' :
      forall T : Type, IntrinsicE T -> stateT MemState (itree_spec Effout) T.
    Proof using.
      intros T IntE ms.
      eapply handle_intrinsic_prop in ms; eauto.
      refine (Vis (@Spec_forall Effout {a : (err_ub_oom (MemState * T)) | ms a}) (fun (x : {a : (err_ub_oom (MemState * T)) | ms a}) => _)).
      destruct x.
      apply (lift_err_ub_oom ret x).
    Defined.

    Definition my_handle_memory_prop :
      forall T : Type, MemoryE T -> MemStateFreshT (itree_spec Effout) T.
    Proof using.
      (* TODO: May need to punt through MemMonad_valid_state like from MemPropT_lift_PropT_fresh *)
      intros T MemE sid ms.
      eapply handle_memory_prop in ms; eauto.
      refine (Vis (@Spec_forall Effout {a : (err_ub_oom (MemState * (store_id * T))) | ms (fmap (fun '(m, (sid, x)) => (m, x)) a)}) (fun (x : {a : (err_ub_oom (MemState * (store_id * T))) | ms (fmap (fun '(m, (sid, x)) => (m, x)) a)}) => _)).
      destruct x.
      apply (lift_err_ub_oom ret x).
    Defined.

    Definition my_handle_intrinsic_prop :
      forall T : Type, IntrinsicE T -> MemStateFreshT (itree_spec Effout) T.
    Proof using.
      (* TODO: May need to punt through MemMonad_valid_state like from MemPropT_lift_PropT_fresh *)
      intros T IntE sid ms.
      eapply handle_intrinsic_prop in ms; eauto.
      refine (Vis (@Spec_forall Effout {a : (err_ub_oom (MemState * (store_id * T))) | ms (fmap (fun '(m, (sid, x)) => (m, x)) a)}) (fun (x : {a : (err_ub_oom (MemState * (store_id * T))) | ms (fmap (fun '(m, (sid, x)) => (m, x)) a)}) => _)).
      destruct x.
      apply (lift_err_ub_oom ret x).
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

    Definition interp_memory_spec_h : forall T, Effin T -> MemStateFreshT (itree_spec Effout) T
      := case_ E_trigger (case_ my_handle_intrinsic_prop (case_ my_handle_memory_prop F_trigger)).

    (* #[global] Instance memory_k_spec_WF : @k_spec_WF store_id MemState _ _ interp_memory_spec_h (@memory_k_spec). *)
    (* Proof using. *)
    (*   split. *)
    (*   - (* k_spec_Proper *) *)
    (*     typeclasses eauto. *)
    (*   - (* k_spec_Correct *) *)
    (*     red. *)
    (*     intros T R2 e k2 t2 s1 s2 ta H_SPEC BIND. *)
    (*     unfold memory_k_spec. *)
    (*     right. *)
    (*     rewrite BIND. *)
    (*     reflexivity. *)
    (* Qed. *)

    Definition interp_memory_spec {R} :
      itree Effin R -> MemStateFreshT (itree_spec Effout) R :=
      fun (t : itree Effin R) => interp interp_memory_spec_h t.

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
    Notation F := (PickUvalueE +' OOME +' LLVMExcE uvalue +' UBE +' DebugE +' FailureE).

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

  Definition exec_correct_no_ub {MemM Eff} `{MM: MemMonad MemM (itree Eff)} {X} (pre : exec_correct_pre) (exec : MemM X) (spec : MemPropT MemState X) (post : exec_correct_post X) : Prop :=
    forall ms st,
      (MemMonad_valid_state ms st) ->
      pre ms st ->
        ( (* exists a behaviour in exec that lines up with spec.

               Technically this should be something along the lines of...

               "There is at least one behaviour in exec, and for every
               behaviour in exec it is within the spec"

               For our purposes exec is deterministic, so "exists"
               should be fine here for simplicity.
             *)
           exists (e : err_ub_oom X) (st' : store_id) (ms' : MemState),
             (* Had to manually supply typeclasses, but this within expression is: (e {{(st, ms)}} ∈ {{(st', ms')}} exec))

                 I.e., The executable is correct if forall behaviours
                 in the executable those behaviours are in the spec as
                 well, and if the executable returns successfully it
                 gives a valid store_id / MemState pair.
              *)
             let WEM := (Within_err_ub_oom_MemM (EQI:=(@MemMonad_eq1_runm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MM)) (EQV:=(@MemMonad_eq1_runm_equiv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MM))) in
             (@within MemM _ err_ub_oom (store_id * MemState)%type (store_id * MemState)%type WEM X exec (st, ms) e (st', ms')) /\
               (e {{ms}} ∈ {{ms'}} spec) /\ ((exists x, e = ret x) -> (MemMonad_valid_state ms' st' /\ (exists x, e = ret x /\ post ms st x ms' st')))).

  (* TODO: Move this *)
  #[global] Instance RAISE_UB_ITREE_SPEC_UB {E : Type -> Type} `{UBE -< E} : RAISE_UB (itree_spec E) :=
    { raise_ub := fun A e => raiseUB e
    }.

  (* TODO: Move this *)
  #[global] Instance RAISE_OOM_ITREE_SPEC_OOM {E : Type -> Type} `{OOME -< E} : RAISE_OOM (itree_spec E) :=
    { raise_oom := fun A e => raiseOOM e
    }.

  (* TODO: Move this *)
  Lemma to_itree_spec_raiseOOM :
    forall {E T} `{OOME -< E} oom_msg,
      @to_itree_spec E T (raiseOOM oom_msg) ≈ raiseOOM oom_msg.
  Proof.
    intros E0 T H oom_msg.
    unfold to_itree_spec, raiseOOM.
    repeat (rewrite TranslateFacts.translate_bind, TranslateFacts.translate_trigger).
    eapply eutt_clo_bind; [| intros []].
    reflexivity.
  Qed.

  (* TODO: Move this *)
  Lemma to_itree_spec_raiseUB :
    forall {E T} `{UBE -< E} msg,
      @to_itree_spec E T (raiseUB msg) ≈ raiseUB msg.
  Proof.
    intros E0 T H oom_msg.
    unfold to_itree_spec, raiseUB.
    repeat (rewrite TranslateFacts.translate_bind, TranslateFacts.translate_trigger).
    eapply eutt_clo_bind; [| intros []].
    reflexivity.
  Qed.

  (* TODO: Move this *)
  Lemma to_itree_spec_raise :
    forall {E T} `{FailureE -< E} msg,
      @to_itree_spec E T (LLVMEvents.raise msg) ≈ LLVMEvents.raise msg.
  Proof.
    intros E0 T H oom_msg.
    unfold to_itree_spec, LLVMEvents.raise.
    repeat (rewrite TranslateFacts.translate_bind, TranslateFacts.translate_trigger).
    eapply eutt_clo_bind; [| intros []].
    reflexivity.
  Qed.

  (* TODO: Move this *)
  Lemma to_itree_spec_ret :
    forall {E T} v,
      @to_itree_spec E T (ret v) ≅ ret v.
  Proof.
    intros E0 T v.
    unfold to_itree_spec.
    setoid_rewrite TranslateFacts.translate_ret.
    reflexivity.
  Qed.

  (*
  Definition to_spec_handler {F M} `{Functor M} `{Monad M}
    (h : (forall T : Type, F T -> M T)) : forall T : Type, SpecEvent F T -> M T.
    intros T X.
    apply h.
    refine (match X with
            | Spec_vis X e => e
            | Spec_forall A => _
            | Spec_exists A => _
            end).

    admit.
    admit.
    
    destruct X.

    (h : forall T, E T -> _ T)
   *)
  Definition exec_refines {E R} `{UBE -< E} `{OOME -< E} `{FailureE -< E} (spec exec : itree_spec E R) :=
    (* Refinement taking into account UB / OOM *)
    (exists ub_msg, strict_refines spec (raise_ub ub_msg)) \/
      (* Need this case because both sides could have different messages *)
      (exists oom_msg, exec ≈ raise_oom oom_msg) \/
      (* Need this case because both sides could have different messages *)
      (exists err1 err2, exec ≈ LLVMEvents.raise err1 /\ strict_refines spec (LLVMEvents.raise err2)) \/
      strict_refines spec exec.

  Lemma exec_refines_oom :
    forall {E R} `{UBE -< E} `{OOME -< E} `{FailureE -< E}
      (t : itree_spec E R) oom_msg,
      exec_refines t (raise_oom oom_msg).
  Proof.
    intros F R UB OOM FAIL t oom_msg.
    right; left.
    exists oom_msg.
    reflexivity.
  Qed.

  Lemma exec_refines_ub :
    forall {E R} `{UBE -< E} `{OOME -< E} `{FailureE -< E}
      (t : itree_spec E R) ub_msg,
      exec_refines (raise_ub ub_msg) t.
  Proof.
    intros F R UB OOM FAIL t ub_msg.
    left.
    exists ub_msg.
    reflexivity.
  Qed.

  #[global] Instance exec_refines_Proper_eutt {F R} `{UBE -< F} `{OOME -< F} `{FailureE -< F} :
    Proper (eutt eq ==> eutt eq ==> iff) (@exec_refines F R _ _ _).
  Proof.
    intros t1 t2 REF1 t3 t4 REF2.
    split; intros REF3.
    { destruct REF3 as [[ub UB] | [[oom OOM] | [[err1 [err2 ERR]] | SUCC]]].
      - left.
        exists ub.
        rewrite <- REF1; auto.
      - right; left.
        exists oom.
        rewrite <- REF2; auto.
      - right; right; left.
        exists err1, err2.
        rewrite <- REF2, <- REF1; auto.
      - right; right; right.
        rewrite <- REF2, <- REF1; auto.
    }
    { destruct REF3 as [[ub UB] | [[oom OOM] | [[err1 [err2 ERR]] | SUCC]]].
      - left.
        exists ub.
        rewrite REF1; auto.
      - right; left.
        exists oom.
        rewrite REF2; auto.
      - right; right; left.
        exists err1, err2.
        rewrite REF2, REF1; auto.
      - right; right; right.
        rewrite REF2, REF1; auto.
    }
  Qed.

    Lemma my_handle_intrinsic_prop_correct {T} (i : IntrinsicE T) sid ms (VALID: MemMonad_valid_state ms sid) :
      exec_refines
        (my_handle_intrinsic_prop i sid ms)
        (to_itree_spec (my_handle_intrinsic (T := T) i sid ms)).
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
        exists ub_msg.
        eapply padded_refines_forallL; cbn.
        Unshelve.
        2: {
          exists (raise_ub ub_msg).
          apply UB.
        }

        cbn.
        reflexivity.
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
        cbn in *; subst.
        destruct EXEC as [oom_msg EXEC].
        rewrite EXEC in EXEC_IN.

        setoid_rewrite (@rbm_raise_bind _ _ _ _ _ (RaiseBindM_OOM _)) in EXEC_IN.
        apply raiseOOM_map_itree_inv in EXEC_IN.

        red.
        right; left.
        exists oom_msg.
        cbn.
        rewrite EXEC_IN.
        apply to_itree_spec_raiseOOM.
      }

      { (* UB events *)
        red.
        left.
        exists ub_x.
        cbn.
        eapply padded_refines_forallL.
        Unshelve.
        2: {
          exists (raise_ub ub_x).
          cbn.
          auto.
        }

        cbn.
        reflexivity.
      }

      { (* Error *)
        cbn in *.
        destruct EXEC as [err_msg EXEC].
        rewrite EXEC in EXEC_IN.
        setoid_rewrite (@rbm_raise_bind _ _ _ _ _ (RaiseBindM_Fail _)) in EXEC_IN.
        apply raise_map_itree_inv in EXEC_IN.

        right; right; left.
        do 2 eexists.
        split.
        rewrite EXEC_IN.
        apply to_itree_spec_raise.

        eapply padded_refines_forallL.
        Unshelve.
        3: {
          exists (raise_error err_x).
          cbn.
          auto.
        }

        cbn.
        reflexivity.
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
        eapply padded_refines_forallL.
        rewrite EXEC_IN.
        rewrite to_itree_spec_ret.

        Unshelve.
        2: {
          exists (success_unERR_UB_OOM (ms', (st', exec_res0))).
          cbn; auto.
        }
        cbn.
        reflexivity.
      }
    Qed.

    (* TODO: Import result from [handle_memory_correct]*)
    Lemma my_handle_memory_prop_correct {T} m sid ms (VALID: MemMonad_valid_state ms sid) :
      exec_refines
        (my_handle_memory_prop m sid ms)
        (to_itree_spec (my_handle_memory (T := T) m sid ms)).
    Proof.
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
        eapply padded_refines_forallL.
        Unshelve.
        2: {
          exists (raise_ub ub_msg).
          apply UB.
        }

        cbn.
        reflexivity.
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
        right; left.
        exists oom_msg.
        rewrite EXEC_IN.
        apply to_itree_spec_raiseOOM.
      }

      { (* UB events *)
        red.
        left.
        exists ub_x.
        cbn.
        eapply padded_refines_forallL.
        Unshelve.
        2: {
          exists (raise_ub ub_x).
          cbn.
          apply SPEC.
        }

        cbn.
        reflexivity.
      }

      { (* Error *)
        cbn in *.
        destruct EXEC as [err_msg EXEC].
        rewrite EXEC in EXEC_IN.
        setoid_rewrite (@rbm_raise_bind _ _ _ _ _ (RaiseBindM_Fail _)) in EXEC_IN.
        apply raise_map_itree_inv in EXEC_IN.

        red.
        right; right; left.
        exists err_msg.
        exists err_x.
        split.
        rewrite EXEC_IN.
        apply to_itree_spec_raise.

        eapply padded_refines_forallL.
        Unshelve.
        2: {
          exists (ERR_unERR_UB_OOM err_x).
          cbn; auto.
        }

        cbn.
        reflexivity.
      }

      { (* Success *)
        subst.
        cbn in *.
        rewrite EXEC in EXEC_IN.
        rewrite bind_ret_l in EXEC_IN.
        apply itree_map_ret_inv in EXEC_IN.
        destruct EXEC_IN as [[ms'' [sid'' res]] [EXEC_IN RES_EQ]].
        inv RES_EQ.

        right; right; right.
        eapply padded_refines_forallL.
        rewrite EXEC_IN.
        rewrite to_itree_spec_ret.

        Unshelve.
        2: {
          exists (success_unERR_UB_OOM (ms', (st', exec_res0))).
          cbn; auto.
        }
        cbn.
        reflexivity.
      }
    Qed.

    Lemma exec_refines_handler_case :
      forall F D G
        `{UBE -< G} `{OOME -< G} `{FailureE -< G}
        (h1 : F ~> itree_spec G) (h2 : F ~> itree_spec G)
        (d1 : D ~> itree_spec G) (d2 : D ~> itree_spec G),
        (forall R (e : F R), exec_refines (h1 _ e) (h2 _ e)) ->
        (forall R (e : D R), exec_refines (d1 _ e) (d2 _ e)) ->
        (forall R (e : (F +' D) R),
            exec_refines ((case_ h1 d1) _ e) ((case_ h2 d2) _ e)).
    Proof.
      intros F D G H H0 H1 h1 h2 d1 d2 H2 H3 R e.
      destruct e; cbn; eauto.
    Qed.

    Lemma exec_refines_handler_case_memstatefresht :
      forall F D G
        `{UBE -< G} `{OOME -< G} `{FailureE -< G}
        (h1 : F ~> MemStateFreshT (itree_spec G)) (h2 : F ~> MemStateFreshT (itree_spec G))
        (d1 : D ~> MemStateFreshT (itree_spec G)) (d2 : D ~> MemStateFreshT (itree_spec G)),
        (forall R (e : F R) s ms, exec_refines (h1 _ e s ms) (h2 _ e s ms)) ->
        (forall R (e : D R) s ms, exec_refines (d1 _ e s ms) (d2 _ e s ms)) ->
        (forall R (e : (F +' D) R) (s : store_id) (ms : MemState),
            exec_refines (case_ h1 d1 _ e s ms) (case_ h2 d2 _ e s ms)).
    Proof.
      intros F D G H H0 H1 h1 h2 d1 d2 H2 H3 R e s ms.
      destruct e; cbn; eauto.
    Qed.

    Lemma E_trigger_spec_correct {T} e sid ms :
      exec_refines
        (SPEC_INTERP.E_trigger e sid ms)
        (to_itree_spec (E_trigger (T := T) e sid ms)).
    Proof.
      repeat right.
      unfold SPEC_INTERP.E_trigger, E_trigger.
      cbn.
      rewrite to_itree_spec_bind.
      eapply padded_refines_bind.
      setoid_rewrite to_itree_spec_trigger.
      reflexivity.
      intros r1 r2 H; subst.
      setoid_rewrite to_itree_spec_ret.
      reflexivity.
    Qed.

    Lemma F_trigger_spec_correct {T} e sid ms :
      exec_refines
        (SPEC_INTERP.F_trigger e sid ms)
        (to_itree_spec (F_trigger (T := T) e sid ms)).
    Proof.
      repeat right.
      cbn.
      rewrite to_itree_spec_bind.
      eapply padded_refines_bind.
      setoid_rewrite to_itree_spec_trigger.
      reflexivity.
      intros r1 r2 H; subst.
      setoid_rewrite to_itree_spec_ret.
      reflexivity.
    Qed.

    Lemma exec_refines_case_to_itree_spec_memstatefresht :
      forall F D G
        `{UBE -< G} `{OOME -< G} `{FailureE -< G}
        (h1 : F ~> MemStateFreshT (itree_spec G)) (h2 : F ~> MemStateFreshT (itree G))
        (d1 : D ~> MemStateFreshT (itree_spec G)) (d2 : D ~> MemStateFreshT (itree G)),
        (forall R (e : F R) s ms, exec_refines (h1 _ e s ms) (to_itree_spec (h2 _ e s ms))) ->
        (forall R (e : D R) s ms, exec_refines (d1 _ e s ms) (to_itree_spec (d2 _ e s ms))) ->
        (forall R (e : (F +' D) R) (s : store_id) (ms : MemState),
            exec_refines (case_ h1 d1 _ e s ms) (to_itree_spec (case_ h2 d2 _ e s ms))).
    Proof.
      intros F D G H H0 H1 h1 h2 d1 d2 H2 H3 R e s ms.
      destruct e; cbn; eauto.
    Qed.

    (* TODO: Prove this, should just need some lemmas about case_ *)
    Lemma interp_memory_spec_h_correct {T} e sid ms (VALID: MemMonad_valid_state ms sid) :
      exec_refines
        (interp_memory_spec_h e sid ms)
        (to_itree_spec (interp_memory_h (T := T) e sid ms)).
    Proof.
      eapply exec_refines_case_to_itree_spec_memstatefresht; intros.
      apply E_trigger_spec_correct.

      eapply exec_refines_case_to_itree_spec_memstatefresht; intros.
      eapply my_handle_intrinsic_prop_correct.
      (* Need to manage MemMonad_valid_state *)
      admit.

      eapply exec_refines_case_to_itree_spec_memstatefresht; intros.
      eapply my_handle_memory_prop_correct.
      (* Need to manage MemMonad_valid_state *)
      admit.

      apply F_trigger_spec_correct.
    Admitted.

    Definition to_itree_spec_MemStateFresh_handler'
      {G F : Type -> Type}
      (h : G ~> MemStateFreshT (itree F)) : (VisOnlyE G ~> MemStateFreshT (itree_spec F)).
      intros T e.
      destruct e.
      destruct s.
      destruct x; cbn in e; inversion e.
      apply h in e0.
      intros s ms.
      apply to_itree_spec.
      apply e0; auto.
    Defined.

    Definition to_itree_spec_MemStateFresh_handler
      {G F : Type -> Type}
      (h : G ~> MemStateFreshT (itree F)) : (SpecEvent G ~> MemStateFreshT (itree_spec F)).
      intros T e.
      intros sid ms.
      destruct e.
      - apply to_itree_spec.
        apply h; auto.
      - apply ITree.spin.
      - apply ITree.spin.
    Defined.


    Lemma interp_memstatefresh_ret :
      forall {E F : Type -> Type} {R : Type} (f : forall T : Type, E T -> MemStateFreshT (itree F) T)
        s ms (r : R),
        State.interp_state f (Ret r) s ms ≅ Ret (ms, (s, r)).
    Proof.
      intros E0 F R f s ms r.
      rewrite itree_eta. reflexivity.
    Qed.

    Lemma interp_memstatefresh_tau :
      forall {E F : Type -> Type} {R : Type} (f : forall T : Type, E T -> MemStateFreshT (itree F) T)
        s ms (t : itree E R),
        State.interp_state f (Tau t) s ms ≅ Tau (State.interp_state f t s ms).
    Proof.
      intros E0 F R f s ms r.
      rewrite itree_eta. reflexivity.
    Qed.

    Definition _interp_memstatefresh {E F R}
      (f : E ~> MemStateFreshT (itree F)) (ot : itreeF E R _)
      : MemStateFreshT (itree F) R := fun s ms =>
                                  match ot with
                                  | RetF r => Ret (ms, (s, r))
                                  | TauF t => Tau (State.interp_state f t s ms)
                                  | VisF _ e k => f _ e s ms >>= (fun sx => Tau (State.interp_state f (k (snd (snd sx))) (fst (snd sx)) (fst sx)))
                                  end.

    Lemma unfold_interp_memstatefresh {G F R} (h : G ~> MemStateFreshT (itree F))
      (t : itree G R) s ms :
      eq_itree eq
        (State.interp_state h t s ms)
        (_interp_memstatefresh h (observe t) s ms).
    Proof.
      unfold State.interp_state, interp, Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_itree; cbn.
      rewrite unfold_iter; cbn.
      destruct observe; cbn.
      - repeat rewrite bind_ret_l. reflexivity.
      - repeat rewrite bind_ret_l.
        reflexivity.
      - repeat rewrite bind_map, bind_bind; cbn. repeat setoid_rewrite bind_ret_l.
        rewrite bind_bind.
        apply eqit_bind. reflexivity.
        red.
        intros a.
        repeat setoid_rewrite bind_ret_l; cbn.
        reflexivity.
    Qed.

    Lemma interp_memstatefresh_vis :
      forall {E F : Type -> Type} {T U : Type} (e : E T) (k : T -> itree E U)
        (h : forall T0 : Type, E T0 -> MemStateFreshT (itree F) T0) s ms,
        State.interp_state h (Vis e k) s ms
          ≅ ITree.bind (h T e s ms) (fun sx : (MemState * (store_id * T)) => Tau (State.interp_state h (k (snd (snd sx))) (fst (snd sx)) (fst sx))).
    Proof.
      intros E0 F T U e k h s ms.
      setoid_rewrite unfold_interp_memstatefresh.
      cbn.
      setoid_rewrite unfold_interp_memstatefresh.
      reflexivity.
    Qed.

    #[global]
      Instance eutt_interp_state_MemFreshT_eq {G F: Type -> Type}
      (h : G ~> MemStateFreshT (itree F)) R :
      Proper (eutt eq ==> eq ==> eq ==> eutt eq) (@State.interp_state G _ _ _ _ _ h R).
    Proof.
      repeat intro. subst. Tactics.revert_until R.
      einit. ecofix CIH. intros.
      punfold H0. red in H0.
      rewrite (itree_eta_ x).
      rewrite (itree_eta_ y).
      genobs x ox.
      genobs y oy.
      clear x y Heqox Heqoy.
      induction H0; intros; subst; simpl; pclearbot.
      - rewrite interp_memstatefresh_ret.
        eret.
      - repeat rewrite interp_memstatefresh_tau.
        etau.
      - repeat rewrite interp_memstatefresh_vis.
        ebind.
        econstructor; [reflexivity|].
        intros; subst.
        etau. ebase.
      - repeat rewrite interp_memstatefresh_tau.
        rewrite tau_euttge; eauto.
        rewrite (itree_eta_ t1); eauto.
      - repeat rewrite interp_memstatefresh_tau.
        rewrite tau_euttge; eauto.
        rewrite (itree_eta_ t2); eauto.
    Qed.

    #[global]
      Instance eq_itree_interp_state_MemFreshT_eq {G F: Type -> Type}
      (h : G ~> MemStateFreshT (itree F)) R :
      Proper (eq_itree eq ==> eq ==> eq ==> eq_itree eq) (@State.interp_state G _ _ _ _ _ h R).
    Proof.
      ginit. gcofix CIH. intros; subst.
      rewrite !unfold_interp_memstatefresh.
      punfold H0; repeat red in H0.
      destruct H0; subst; pclearbot; try discriminate; cbn.
      - gstep; constructor; auto.
      - gstep; constructor; auto with paco.
      - guclo eqit_clo_bind. econstructor.
        + reflexivity.
        + intros [] _ []. gstep; constructor; auto with paco itree.
    Qed.

    Lemma to_itree_spec_iterp_MemStateFreshT :
      forall {E F : Type -> Type}
        (h : forall T, E T -> MemStateFreshT (itree F) T) {R} (t : itree E R) s ms,
        (@to_itree_spec F _ (@State.interp_state E _ _ _ _ _ h R t s ms)) ≈
          (State.interp_state (to_itree_spec_MemStateFresh_handler h) (to_itree_spec t) s ms).
    Proof.
      einit.
      ecofix CIH.
      intros E0 h t s ms.
      rewrite (itree_eta_ t).
      genobs t ot.
      clear t Heqot.
      hinduction ot before CIH; intros.
      - rewrite interp_memstatefresh_ret.
        setoid_rewrite to_itree_spec_ret.
        setoid_rewrite interp_memstatefresh_ret.
        eret.
      - setoid_rewrite interp_memstatefresh_tau.
        setoid_rewrite to_itree_spec_tau.
        setoid_rewrite interp_memstatefresh_tau.
        rewrite (itree_eta t).
        etau.
      - setoid_rewrite interp_memstatefresh_vis.
        setoid_rewrite to_itree_spec_vis.
        setoid_rewrite interp_memstatefresh_vis.
        cbn.
        rewrite to_itree_spec_bind.
        ebind.
        econstructor; [reflexivity|].
        intros u1 u2 H; subst.
        setoid_rewrite to_itree_spec_tau.
        etau.
    Qed.

    (* Lemma interp_handler_refine *)
    (*   {E1 E2 : Type -> Type} {R1 R2 : Type} *)
    (*   (pre : prerel E1 E2) (post : postrel E1 E2) (R1R2 : R1 -> R2 -> Prop) *)
    (*   (h1 : forall T : Type, SpecEvent E1 T -> MemStateFreshT (itree_spec E1) T) *)
    (*   (h2 : forall T : Type, SpecEvent E2 T -> MemStateFreshT (itree_spec E2) T) *)
    (*   t1 t2 s ms: *)
    (*   (* (* to_spec_post may not be quite right *) *) *)
    (*   (* (forall X Y (e1 : SpecEvent E1 X) (e2 : SpecEvent E2 Y) , *) *)
    (*   (*     padded_refines pre post (fun a b => to_spec_post post _ _ e1 a e2 b) *) *)
    (*   (*       (h1 X e1) (h2 Y e2)) -> *) *)
    (*   padded_refines pre post R1R2 t1 t2 -> *)
    (*   padded_refines pre post R1R2 (@State.interp_state E1 _ _ _ _ _ h1 _ t1 s ms) (interp h2 t2). *)
    (* Proof. *)
    (*   intros HREF REF. *)
    (*   unfold interp. *)
    (*   apply padded_refines_iter with (RR:=padded_refines pre post R1R2); auto. *)
    (*   clear t1 t2 REF. *)
    (*   intros t1 t2 REF. *)
    (*   rewrite (EqAxiom.itree_eta_ t1) in *. *)
    (*   rewrite (EqAxiom.itree_eta_ t2) in *. *)

    (*   genobs t1 ot1. *)
    (*   genobs t2 ot2. *)
    (*   clear t1 Heqot1 t2 Heqot2. *)
    (*   destruct ot1, ot2; cbn. *)
    (*   9: { *)
    (*     (* vis / vis *) *)
    (*     eapply padded_refines_map. *)
    (*     2: { *)
    (*       apply HREF. *)
    (*     } *)

    (*     intros r1 r2 POST. *)
    (*     cbn in POST. *)
    (*     left. *)
    (*     red. *)
    (*     change (pad (k r1)) with ((fun a => pad (k a)) r1). *)
    (*     change (pad (k0 r2)) with ((fun a => pad (k0 a)) r2). *)

    (*     punfold REF; red in REF; cbn in *. *)
    (*     eapply Spec_vis_inv with (k0 := (fun a => pad (k a))) (k1 := (fun a => pad (k0 a))) in REF; eauto. *)
    (*     eapply refines_weaken_post. *)
    (*     2: apply REF. *)
    (*     { intros X1 Y e1 x e2 y H. *)
    (*       cbn in *. *)
    (*       unfold to_spec_post in POST. *)
    (*       admit. *)
    (*     } *)
    (*     admit. *)
    (*     admit. *)
    (* Admitted. *)

    Import InterpFacts.
    Import ITreeSpecFacts.

    (* #[global] Instance grefinegen_cong_eqit {F R1 R2 RR1 RR2 RS} pre post r rg *)
    (*   (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y) *)
    (*   (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y): *)
    (*   Proper (eq_itree RR1 ==> eq_itree RR2 ==> flip impl) *)
    (*     (gpaco2 (@refines_ F F R1 R2 pre post RS) (refinesC RS pre post) r rg). *)
    (* Proof. *)
    (*   repeat intro. *)
    (*   guclo eqit_clo_trans. econstructor; cycle -3; eauto. *)
    (*   - eapply eqit_mon, H; eauto; discriminate. *)
    (*   - eapply eqit_mon, H0; eauto; discriminate. *)
    (* Abort. *)

    (* This may only hold for the padded version because of ITree.bind in the vis cases? *)
    Lemma strict_refines_unpadded_interp_to_itree_spec :
      forall {F R} h g (t : itree F R),
        (* Handler refinement *)
        (forall R (e1 : F R) (e2 : F R),
            strict_refines_unpadded (h _ e1) (g _ (to_SpecEvent e2))) ->
        @strict_refines_unpadded F R (interp h t) (interp g (to_itree_spec t)).
    Proof.
      intros F R h g t REF.
      rewrite (itree_eta_ t).
      genobs t ot; clear t Heqot.
      revert ot.
      setoid_rewrite unfold_interp.
      cbn.
      ginit.
      {
        gcofix CIH.
        intros ot.
        hinduction ot before r; intros.
        - gstep; red; cbn.
          constructor; auto.
        - gstep; red; cbn.
          constructor; auto with paco.
          (* Need to be able to do this rewrite... *)
          (* This relies on grefinegen_cong_eqit *)
          (* Why can't I rewrite? *)
          (* setoid_rewrite unfold_interp. *)
          pose proof (unfold_interp (f:= h) t) as UNFOLD.
          apply EqAxiom.bisimulation_is_eq in UNFOLD.
          rewrite UNFOLD; clear UNFOLD.

          pose proof (unfold_interp (f:=g) (translate (@to_SpecEvent F) t)) as UNFOLD.
          apply EqAxiom.bisimulation_is_eq in UNFOLD.
          setoid_rewrite UNFOLD; clear UNFOLD.

          gbase.
          guclo
          apply CIH.
        - paco2_mon_bot.
          econstructor.

          x > y

          x' > y' ===> x > y

          x'
          
          (* trying to show that t1 >= t2

             We want to do that by showing t1' >= t2'

             t1' has to be smaller than t1
             and t2' >= t2

           *)
          
          cbn.
          eapply refines_bind.
          
          guclo refines_clo_trans.
          cbn.
          econstructor.
          setoid_rewrite REF.
          apply REF.
          cbn.
          guclo.
          constructor.

        - gfinal.
          right.
          cbn.
          eapply paco2_mon_bot.
          eapply refines_bind.
          apply REF.

          intros r1 r2 H; subst.
          pstep; red; cbn.
          constructor; left.
          
          pstep; red.

          admit.

          intros x0 x1 x2 PR.
          apply PR.
      }
      admit.
    Abort.

    (* Lemma strict_refines_unpadded_to_itree_spec : *)
    (*   forall {F R} h g (t : itree F R), *)
    (*     (* Handler refinement *) *)
    (*     (forall R (e1 : F R) (e2 : F R), *)
    (*         strict_refines_unpadded (h _ e1) (to_itree_spec (g _ e2))) -> *)
    (*     @strict_refines_unpadded F R (interp h t) (to_itree_spec (interp g t)). *)
    (* Proof. *)
    (*   intros F R h g t REF. *)
    (*   setoid_rewrite to_itree_spec_iterp. *)
    (*   apply to_itree_spec_interp. *)
      
    (*   ginit. *)
    (*   2: { *)
    (*     revert t. *)
    (*     gcofix CIH. *)
    (*     rewrite !unfold_interp. *)

    (*     intros ot. *)
    (*     hinduction ot before R; intros. *)
    (*     - gstep; red; cbn; *)
    (*       constructor; auto. *)
    (*     - gstep; red; cbn; *)
    (*         constructor; auto. *)

          
    (*       gbase. *)
    (*       apply CIH. *)
        

    (*   } *)

        
    (* Qed. *)

    Lemma strict_refines_interp_to_itree_spec :
      forall {F R} h g (t : itree F R),
        (* Handler refinement *)
        (forall R (e1 : F R) (e2 : F R),
            strict_refines (h _ e1) (g _ (to_SpecEvent e2))) ->
        @strict_refines F R (interp h t) (interp g (to_itree_spec t)).
    Proof.
      intros F R h g t REF.
      rewrite (itree_eta_ t).
      genobs t ot; clear t Heqot.
      revert ot.
      setoid_rewrite unfold_interp.
      pcofix CIH.
      intros ot.
      hinduction ot before r; intros.
      - pstep; red; cbn.
        constructor; auto.
      - pstep; red; cbn.
        constructor; auto with paco.
        right.
        pose proof (unfold_interp (f:= h) t) as UNFOLD.
        apply EqAxiom.bisimulation_is_eq in UNFOLD.
        setoid_rewrite UNFOLD; clear UNFOLD.

        pose proof (unfold_interp (f:=g) (translate (@to_SpecEvent F) t)) as UNFOLD.
        apply EqAxiom.bisimulation_is_eq in UNFOLD.
        setoid_rewrite UNFOLD; clear UNFOLD.
        apply CIH.
      - cbn.
        pose proof (Padded.pad_bind (h X e) (fun x : X => Tau (interp h (k x)))) as BIND.
        apply EqAxiom.bisimulation_is_eq in BIND.
        setoid_rewrite BIND; clear BIND.

        pose proof (Padded.pad_bind (g X (to_SpecEvent e)) (fun x : X => Tau (interp g (translate (@to_SpecEvent F) (k x))))) as BIND.
        apply EqAxiom.bisimulation_is_eq in BIND.
        setoid_rewrite BIND; clear BIND.

        eapply paco2_mon.        
        eapply refines_bind.
        apply REF.

        intros r1 r2 H; subst.
        pstep; red; cbn.
        constructor.
        left.


        
        apply CIH.
        left.
        (* Need to be able to do this rewrite... *)
        (* This relies on grefinegen_cong_eqit *)
        (* Why can't I rewrite? *)
        (* setoid_rewrite unfold_interp. *)
        (* eapply grefinegen_cong_eqit; cbn. *)
        (* 3-4: setoid_rewrite unfold_interp. ; reflexivity. *)
        (* 1-2: intros; subst; auto. *)

        (* gbase. *)
        (* apply CIH. *)
        all: admit.
      - admit.



      
      cbn.
      ginit.
      2: {
        gcofix CIH.
        intros ot.
        hinduction ot before r; intros.
        - gstep; red; cbn.
          constructor; auto.
        - gstep; red; cbn.
          constructor; auto with paco.
          (* Need to be able to do this rewrite... *)
          (* This relies on grefinegen_cong_eqit *)
          (* Why can't I rewrite? *)
          (* setoid_rewrite unfold_interp. *)
          (* eapply grefinegen_cong_eqit; cbn. *)
          (* 3-4: setoid_rewrite unfold_interp. ; reflexivity. *)
          (* 1-2: intros; subst; auto. *)

          (* gbase. *)
        (* apply CIH. *)
          all: admit.
        - admit.
      }
      admit.
    Admitted.

    Lemma strict_refines_to_itree_spec_interp :
      forall {F R} h g (t : itree F R),
        (* Handler refinement *)
        (forall R (e1 : F R) (e2 : F R),
            strict_refines (h _ e1) (to_itree_spec (g _ e2))) ->
        @strict_refines F R (interp h t) (to_itree_spec (interp g t)).
    Proof.
      intros F R h g t REF.
      rewrite to_itree_spec_iterp.
      apply strict_refines_interp_to_itree_spec; auto.
    Qed.

    Theorem exec_refines_to_itree_spec_interp :
      forall {F G}
        `{UBE -< G} `{OOME -< G} `{FailureE -< G}
        (h : F ~> itree_spec G) (g : F ~> itree G),
        (* Handler refinement *)
        (forall R (e1 : F R) (e2 : F R),
            exec_refines (h _ e1) (to_itree_spec (g _ e2))) ->
        forall R (t : itree F R),
          exec_refines
            (interp h t)
            (to_itree_spec (interp g t)).
    Proof.
    Admitted.

    Theorem exec_refines_to_itree_spec_interp_MemStateFreshT :
      forall {F G}
        `{UBE -< G} `{OOME -< G} `{FailureE -< G}
        (h : F ~> MemStateFreshT (itree_spec G)) (g : F ~> MemStateFreshT (itree G)),
        (* Handler refinement *)
        (forall R (e : F R) s ms,
            exec_refines (h _ e s ms) (to_itree_spec (g _ e s ms))) ->
        forall R (t : itree F R) s ms,
          exec_refines
            (State.interp_state h t s ms)
            (to_itree_spec (State.interp_state g t s ms)).
    Proof.
    Admitted.
            
    (* Specification can contain UB and the implementation could OOM...
     *)
    Lemma interp_memory_correct :
      forall {T} t (ms : MemState) (sid : store_id)
        (VALID: MemMonad_valid_state ms sid),
        exec_refines
          (interp_memory_spec t sid ms)
          (to_itree_spec (@interp_memory T t sid ms)).
    Proof using.
      intros T t ms sid VALID.
      eapply exec_refines_to_itree_spec_interp_MemStateFreshT.
      intros R e s ms0.
      eapply interp_memory_spec_h_correct.

      (* May need to modify exec_refines_interp_MemStateFreshT to carry this through *)
      admit.
    Admitted.

  End Interpreters.
End MemoryExecInterpreter.

Module MakeMemorySpecInterpreter (LP : LLVMParams) (MP : MemoryParams LP) (MMSP : MemoryModelSpecPrimitives LP MP) (MS : MemoryModelSpec LP MP MMSP) (MemExecM : MemoryExecMonad LP MP MMSP MS) <: MemorySpecInterpreter LP MP MMSP MS MemExecM.
  Include MemorySpecInterpreter LP MP MMSP MS MemExecM.
End MakeMemorySpecInterpreter.

Module MakeMemoryExecInterpreter (LP : LLVMParams) (MP : MemoryParams LP) (MMEP : MemoryModelExecPrimitives LP MP) (ME : MemoryModelExec LP MP MMEP) (SPEC_INTERP : MemorySpecInterpreter LP MP MMEP.MMSP MMEP.MemSpec MMEP.MemExecM) <: MemoryExecInterpreter LP MP MMEP ME SPEC_INTERP.
  Include MemoryExecInterpreter LP MP MMEP ME SPEC_INTERP.
End MakeMemoryExecInterpreter.
