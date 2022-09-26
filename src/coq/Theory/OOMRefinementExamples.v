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
     ZArith
     Relations.

From ExtLib Require Import
     Monads.

Import MonadNotation.
Import DynamicTypes.

Require Import Morphisms.
Require Import Paco.paco.

Require Import Coq.Program.Equality.

(* TODO: Move all of this stuff *)
Lemma itree_map_ret_inv :
  forall Eff A B (f : A -> B) (t : itree Eff A) b,
    ITree.map f t ≈ ret b ->
    exists a, t ≈ ret a /\ f a = b.
Proof.
  intros * HM.
  punfold HM.
  cbn in *.
  red in HM.
  dependent induction HM.
  - setoid_rewrite (itree_eta t).
    unfold ITree.map,observe in x; cbn in x.
    destruct (observe t) eqn:EQ'; try now inv x.
    cbn in *; exists r; inv x; split; reflexivity.
  - unfold ITree.map,observe in x; cbn in x.
    setoid_rewrite (itree_eta t).
    destruct (observe t) eqn:EQ'; try now inv x.
    cbn in x.
    inv x.
    edestruct IHHM as (? & ? & ?).
    all: try reflexivity.
    exists x; split; auto.
    rewrite H, tau_eutt; reflexivity.
Qed.

Lemma interp_prop_vis :
  forall {E F X} (h_spec : E ~> PropT F) k_spec {R} (RR : relation R)
    (e : E X) kk t,
    interp_prop RR h_spec k_spec (Vis e kk) t <->
      (x <- h_spec X e;;
       interp_prop RR h_spec k_spec (kk x)) t. (* Do I need to use k_spec anywhere...? *)
Proof.
Admitted.

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

  (* TODO: Move this *)
  Import Relation_Definitions.
  #[global] Instance refine_OOM_h_eutt_Proper {T : Type} {RR : relation T} {E F}:
    Proper (eutt eq ==> eutt eq ==> iff) (@refine_OOM_h E F T RR).
  Proof.
    unfold Proper, respectful.
    intros x1 x2 X y1 y2 Y.
    split; intros REFINE.
  Admitted.

  #[global] Instance refine_OOM_h_eutt_RR_Proper {T : Type} {RR : relation T} {E F}:
    Proper (eutt RR ==> eutt RR ==> iff) (@refine_OOM_h E F T RR).
  Proof.
    unfold Proper, respectful.
    intros x1 x2 X y1 y2 Y.
    split; intros REFINE.
  Admitted.

  Lemma model_undef_h_oom :
    forall {R} {E F}
      `{FailureE -< E +' F} `{UBE -< E +' F} `{OOME -< E +' F} `{OOME -< E +' PickUvalueE +' F}
      oom_msg (t' : itree (E +' F) R),
      model_undef_h eq (raiseOOM oom_msg) t' ->
      t' ≈ raiseOOM oom_msg.
  Proof.
  Admitted.

  Lemma model_undef_h_ret_pure :
    forall {E F : Type -> Type}
      `{FAIL : FailureE -< E +' F}
      `{UB : UBE -< E +' F}
      `{OOM : OOME -< E +' F}
      {X} (x : X)
      (RR : relation X) `{REF : Reflexive X RR},
      model_undef_h RR (ret x) (ret x).
  Proof.
    intros E F FAIL UB OOM X x RR REF.
    unfold model_undef_h.
    apply interp_prop_ret_pure; auto.
  Qed.

  Lemma model_undef_h_ret_inv :
    forall {E F : Type -> Type}
      `{FAIL : FailureE -< E +' F}
      `{UB : UBE -< E +' F}
      `{OOM : OOME -< E +' F}
      {X} (x : X) (t : itree (E +' F) X),
      model_undef_h eq (ret x) t ->
      t ≈ Ret x.
  Proof.
    intros E F FAIL UB OOM X x t UNDEF.
    unfold model_undef_h in *.
    eapply interp_prop_ret_inv in UNDEF.
    destruct UNDEF as [r2 [EQ T']].
    subst.
    auto.
  Qed.

  Lemma interp_mcfg4_ret_inv :
    forall (x : dvalue) t genv lenv stack sid m,
      interp_mcfg4 eq eq (Ret x) genv (lenv, stack) sid m t ->
      eutt refine_res3 t (Ret (m, (sid, (lenv, stack, (genv, x))))).
  Proof.
    intros x t genv lenv stack sid m INTERP.
    unfold interp_mcfg4 in *.

    destruct INTERP as [t_pre [INTERP UNDEF]].
    unfold interp_memory_prop in INTERP.
    cbn in INTERP.
    go_in INTERP.

    eapply interp_prop_ret_inv in INTERP.
    destruct INTERP as [r2 [INTERP_TT EQ]].
    apply itree_map_ret_inv in EQ.
    destruct EQ as [[ms [sid' [lenv' [st res]]]] [TPRE RES]].
    inv RES.
    inv H.

    rewrite TPRE in UNDEF.
    eapply model_undef_h_ret_inv in UNDEF.
    rewrite UNDEF.

    apply eutt_Ret.
    repeat constructor; auto.
  Qed.

  Lemma interp_memorp_prop_ret_inv :
    forall {E F : Type -> Type}
      `{FAIL : FailureE -< F}
      `{UB : UBE -< F}
      `{OOM : OOME -< F}
      {X} (x : X) sid m (t : itree (E +' F) (MMEP.MMSP.MemState * (store_id * X))%type),
      interp_memory_prop eq (Ret x) sid m t ->
      Functor.fmap (fun '(_, (_, x)) => x) t ≈ Ret x.
  Proof.
    intros E F FAIL UB OOM X x sid m t INTERP.
    unfold interp_memory_prop in INTERP.
    apply interp_prop_ret_inv in INTERP.
    destruct INTERP as [r2 [EQ MAP]]; subst; auto.
  Qed.

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
      refine_L6 (interp_mcfg4 eq eq t_alloc genv (lenv, stack) sid m) (interp_mcfg4 eq eq t_ret genv (lenv, stack) sid m).
  Proof.
    intros genv lenv stack sid m.
    unfold refine_L6.
    intros t' INTERP.

    unfold t_ret in *.
    eapply interp_mcfg4_ret_inv in INTERP.
    exists (Ret5 genv (lenv, stack) sid m (DVALUE_I1 DynamicValues.Int1.one)).
    split.
    - cbn in *.

      (* TODO: Should make lemmas about ret, etc for interp_mcfg4 *)
      unfold interp_mcfg4 in *.
      unfold model_undef in *.

      exists (Ret5 genv (lenv, stack) sid m (DVALUE_I1 DynamicValues.Int1.one)).

      Import MMEP.MMSP.
      Import MemoryBigIntptr.MMEP.MMSP.
      epose proof allocate_dtyp_spec_can_always_succeed m m (mkMemState (ms_memory_stack m) (next_provenance (ms_provenance m))) (DTYPE_I 64) _ _ _ _ _ as (ms_final & addr & ALLOC).

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

        eapply interp_prop_vis.
        cbn.
        unfold bind_PropT.

        exists (ITree.map (fun '(_, (_, x)) => x) (Ret (lenv, (stack, DVALUE_Addr addr)))).
        exists (fun dv => ret (lenv, stack, (genv, DVALUE_I1 DynamicValues.Int1.one))).
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
          apply interp_prop_ret_pure; auto.
      + apply model_undef_h_ret_pure; auto.
    - rewrite INTERP.
      cbn.
      reflexivity.

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
      refine_L6 (interp_mcfg4 eq eq (interp_instr_E_to_L0 _ alloc_tree) genv (lenv, stack) sid m) (interp_mcfg4 eq eq (interp_instr_E_to_L0 _ ret_tree) genv (lenv, stack) sid m).
  Proof.
    intros genv lenv stack sid m.
    unfold refine_L6.
    intros t' INTERP.

    unfold interp_mcfg4 in *.
    unfold model_undef in *.

    destruct INTERP as [t_pre [INTERP UNDEF]].

    cbn in INTERP.
    go_in INTERP.
    cbn in INTERP.
    repeat rewrite bind_ret_l in INTERP.
    rewrite TranslateFacts.translate_ret in INTERP.
    repeat setoid_rewrite bind_ret_l in INTERP.
    cbn in INTERP.
    setoid_rewrite interp_ret in INTERP.
    setoid_rewrite interp_intrinsics_ret in INTERP.
    setoid_rewrite interp_global_ret in INTERP.
    setoid_rewrite interp_local_stack_ret in INTERP.

    eapply interp_memorp_prop_ret_inv in INTERP.
    eapply itree_map_ret_inv in INTERP.
    destruct INTERP as [[ms' [sid' [lenv' [stack' res]]]] [TPRE EQ]].
    inv EQ.

    rewrite TPRE in UNDEF.
    apply model_undef_h_ret_inv in UNDEF.

    (* TODO: Turn this into an interp_memory_prop lemma *)
    Import MMEP.MMSP.
    Import MemoryBigIntptr.MMEP.MMSP.
    Import MapMonadExtra.
    epose proof allocate_dtyp_spec_can_always_succeed m m (mkMemState (ms_memory_stack m) (next_provenance (ms_provenance m))) (DTYPE_I 64) _ _ _ _ _ as (ms_final & addr & ALLOC).


    exists (Ret5 genv (FMapAList.alist_add (Name "ptr") (UVALUE_Addr addr) lenv, stack) sid m (DVALUE_I1 DynamicValues.Int1.one)).
    split.
    - exists (Ret5 genv (FMapAList.alist_add (Name "ptr") (UVALUE_Addr addr) lenv, stack) sid m (DVALUE_I1 DynamicValues.Int1.one)).
      cbn in *.
      go.
      cbn.

      repeat setoid_rewrite bind_ret_l.
      repeat setoid_rewrite bind_bind.
      repeat setoid_rewrite bind_ret_l.

      setoid_rewrite translate_ret.
      setoid_rewrite bind_ret_l.
      cbn.

      split; [| apply model_undef_h_ret_pure; auto].

      (* LEMMA *)
      unfold interp_memory_prop.
      cbn.

      Opaque MMEP.MemSpec.allocate_dtyp_spec.

      rewrite interp_bind with (f:=@instr_E_to_L0);
        rewrite interp_trigger; cbn; rewrite subevent_subevent.
      go.
      rewrite bind_trigger.
      setoid_rewrite bind_ret_l.
      setoid_rewrite interp_local_stack_ret.
      setoid_rewrite bind_ret_l.

      eapply interp_prop_vis.
      cbn.
      unfold bind_PropT.

      (* was just ret r2... *)
      exists (ITree.map (fun '(_, (_, x)) => x) (Ret (lenv, (stack, DVALUE_Addr addr)))).
      exists (fun dv => ret (FMapAList.alist_add (Name "ptr") (UVALUE_Addr addr) lenv, stack, (genv, DVALUE_I1 DynamicValues.Int1.one))).
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
      * repeat rewrite map_ret.
        cbn.
        rewrite bind_ret_l.
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
        rewrite interp_ret.
        go.

        apply interp_prop_ret_pure; auto.
    - rewrite UNDEF.
      apply eutt_refine_oom_h; try typeclasses eauto.
      apply eutt_Ret; repeat constructor; auto.

      Unshelve.
      exact initial_provenance.
      exact 0%N.
      cbn.
      all: admit.
  Admitted.

  Lemma remove_alloc_ptoi_block :
    forall genv lenv stack sid m,
      refine_L6 (interp_mcfg4 eq eq (interp_instr_E_to_L0 _ ptoi_tree) genv (lenv, stack) sid m) (interp_mcfg4 eq eq (interp_instr_E_to_L0 _ ret_tree) genv (lenv, stack) sid m).
  Proof.
    intros genv lenv stack sid m.
    unfold refine_L6.
    intros t' INTERP.

    unfold interp_mcfg4 in *.
    unfold model_undef in *.

    destruct INTERP as [t_pre [INTERP UNDEF]].

    cbn in INTERP.
    go_in INTERP.
    cbn in INTERP.
    repeat rewrite bind_ret_l in INTERP.
    rewrite TranslateFacts.translate_ret in INTERP.
    repeat setoid_rewrite bind_ret_l in INTERP.
    cbn in INTERP.
    setoid_rewrite interp_ret in INTERP.
    setoid_rewrite interp_intrinsics_ret in INTERP.
    setoid_rewrite interp_global_ret in INTERP.
    setoid_rewrite interp_local_stack_ret in INTERP.


    eapply interp_memorp_prop_ret_inv in INTERP.
    eapply itree_map_ret_inv in INTERP.
    destruct INTERP as [[ms' [sid' [lenv' [stack' res]]]] [TPRE EQ]].
    inv EQ.

    rewrite TPRE in UNDEF.
    apply model_undef_h_ret_inv in UNDEF.

    epose proof allocate_dtyp_spec_can_always_succeed m _ _ (DTYPE_I 64) _ _ _ _ _ as (ms_final & addr & ALLOC).

    exists (Ret5 genv (FMapAList.alist_add (Name "i")
                                      (UVALUE_Conversion Ptrtoint DTYPE_Pointer (UVALUE_Addr addr) DTYPE_IPTR)
                                      (FMapAList.alist_add (Name "ptr") (UVALUE_Addr addr) lenv), stack)
            sid m (DVALUE_I1 DynamicValues.Int1.one)).
    split.
    - exists (Ret5 genv (FMapAList.alist_add (Name "i")
                                         (UVALUE_Conversion Ptrtoint DTYPE_Pointer (UVALUE_Addr addr) DTYPE_IPTR)
                                         (FMapAList.alist_add (Name "ptr") (UVALUE_Addr addr) lenv), stack)
              sid m (DVALUE_I1 DynamicValues.Int1.one)).


      cbn in *.
      go.
      cbn.

      repeat setoid_rewrite bind_ret_l.
      repeat setoid_rewrite bind_bind.
      repeat setoid_rewrite bind_ret_l.

      setoid_rewrite translate_ret.
      setoid_rewrite bind_ret_l.
      cbn.

      split; [| apply model_undef_h_ret_pure; auto].

      (* LEMMA *)
      unfold interp_memory_prop.
      cbn.

      Opaque MMEP.MemSpec.allocate_dtyp_spec.

      rewrite interp_bind with (f:=@instr_E_to_L0);
        rewrite interp_trigger; cbn; rewrite subevent_subevent.
      go.

      rewrite bind_trigger.
      eapply interp_prop_vis.
      cbn.
      unfold bind_PropT.

      (* was just ret r2... *)
      exists (ITree.map (fun '(_, (_, x)) => x) (Ret (lenv, (stack, DVALUE_Addr addr)))).
      exists (fun dv => ret (FMapAList.alist_add (Name "i")
                                         (UVALUE_Conversion Ptrtoint DTYPE_Pointer (UVALUE_Addr addr) DTYPE_IPTR)
                                         (FMapAList.alist_add (Name "ptr") (UVALUE_Addr addr) lenv),
                      stack, (genv, DVALUE_I1 DynamicValues.Int1.one))).
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
      * repeat rewrite map_ret.
        cbn.
        rewrite bind_ret_l.
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

        rewrite translate_trigger.
        rewrite translate_bind.
        rewrite bind_bind.
        setoid_rewrite translate_ret.
        setoid_rewrite bind_ret_l.

        rewrite translate_trigger.
        repeat setoid_rewrite subevent_subevent.

        rewrite interp_bind with (f:=@instr_E_to_L0);
          rewrite interp_trigger; cbn; rewrite subevent_subevent.
        go.

        rewrite map_ret.
        go.

        rewrite interp_bind with (f:=@instr_E_to_L0);
          rewrite interp_trigger; cbn; rewrite subevent_subevent.
        go.

        rewrite map_ret.
        go.

        rewrite interp_ret.
        go.

        apply interp_prop_ret_pure; auto.
    - rewrite UNDEF.
      apply eutt_refine_oom_h; try typeclasses eauto.
      apply eutt_Ret; repeat constructor; auto.

      Unshelve.
      exact initial_memory_state.
      exact initial_memory_state.
      exact initial_provenance.
      exact 0%N.
      cbn.
      all: admit.
  Admitted.

  (* TODO: move this? *)
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

      rewrite K in UNDEF.

      assert (t' ≈ raiseOOM err_msg) as T' by (eapply model_undef_h_oom; eauto).

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
      + rewrite T'.
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
  Import InterpretationStack.
  Import InterpreterStack64BitIntptr.
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

  Module MemTheory  := MemoryModelTheory LP MP MMEP MEM_MODEL.
  Import MemTheory.

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

  (* TODO: Move this *)
  Import Relation_Definitions.
  #[global] Instance refine_OOM_h_eutt_Proper {T : Type} {RR : relation T} {E F}:
    Proper (eutt eq ==> eutt eq ==> iff) (@refine_OOM_h E F T RR).
  Proof.
    unfold Proper, respectful.
    intros x1 x2 X y1 y2 Y.
    split; intros REFINE.
  Admitted.

  Lemma model_undef_h_oom :
    forall {R} {E F}
      `{FailureE -< E +' F} `{UBE -< E +' F} `{OOME -< E +' F} `{OOME -< E +' PickUvalueE +' F}
      oom_msg (t' : itree (E +' F) R),
      model_undef_h eq (raiseOOM oom_msg) t' ->
      t' ≈ raiseOOM oom_msg.
  Proof.
  Admitted.

  (* TODO: Move this, there are duplicates of this elsewhere too. *)
  Import TranslateFacts.
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

  (* Add allocation in the finite language *)
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
    rewrite interp_intrinsics_bind in INTERP.
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

      rewrite K in UNDEF.

      assert (t' ≈ raiseOOM err_msg) as T' by (eapply model_undef_h_oom; eauto).

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
      + rewrite T'.
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
  Qed.
End Finite.
