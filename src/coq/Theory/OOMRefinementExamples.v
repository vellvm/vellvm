From Vellvm Require Import
     TopLevel
     TopLevelRefinements
     Refinement
     Utils.Monads
     Utils.PropT
     Utils.Tactics
     Utils.MonadEq1Laws
     Utils.InterpProp
     Utils.InterpMemoryProp
     Utils.ITreeMap
     Utils.Raise
     Utils.Tactics
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
Import TranslateFacts.
Import StateFacts.
Import InterpFacts.

Require Import Morphisms.
Require Import Paco.paco.

Require Import Coq.Program.Equality.

(* This file contains examples of program transformations allowed by the new
    memory model:

  Most notably, the infinite memory model allows for dead allocation removal
  while the finite memory model does not. The main examples are as follows:

  1. Example [remove_alloc_block]
      Dead allocation removal (only allowed in infinite model):

      alloc_tree ⪯ ret_tree

  2. Example [remove_alloc_ptoi_block]
    Dead allocation and ptoi cast removal (only allowed in infinite model):

      ptoi_itree ⪯ ret_tree

  3. Example [add_alloc]
     Adding an allocation (allowed in both the infinite and finite model ):

      ret_tree ⪯ alloc_tree *)

Ltac force_go_hyps :=
  repeat
    (match goal with
    | [H : context [ITree.bind (ITree.bind _ _ ) _] |- _ ]
        => force_rewrite: @bind_bind in H; cbn in H
    | [H : context [ITree.bind (Ret _) _] |- _ ]
        => force_rewrite: @bind_ret_l in H; cbn in H
    | [H : context [interp _ (ITree.bind _ _) ] |- _ ]
        => force_rewrite: @interp_bind in H; cbn in H
    | [H : context [interp _ (Ret _) ] |- _ ]
        => force_rewrite: @interp_ret in H; cbn in H
    | [H : context [translate _ (Ret _) ] |- _ ]
        => force_rewrite: @translate_ret in H; cbn in H
      end).

Ltac force_go :=
  repeat
    (match goal with
    | |- context [ITree.bind (ITree.trigger _) _ ] => force_rewrite @bind_trigger
    | |- context [ITree.bind (ITree.bind _ _ ) _ ] => force_rewrite @bind_bind
    | |- context [ITree.bind (Ret _) _ ] => force_rewrite @bind_ret_l
    | |- context [interp _ (ITree.bind _ _) ] => force_rewrite @interp_bind
    | |- context [interp _ (Ret _) ] => force_rewrite @interp_ret
    | |- context [interp _ (Vis _ _) ] => force_rewrite @interp_vis
    | |- context [translate _ (Ret _) ] => force_rewrite @translate_ret
      end).


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
  Import LLVMEvents.
  Import LLVMAst.
  Import CFG.

  Import List.
  Import ListNotations.
  Require Import Coq.Strings.String.

  Import MMEP.MMSP.
  Import MemoryBigIntptr.MMEP.MMSP.

  #[global] Instance interp_mem_prop_Proper3 :
  forall {E}
      {R} (RR : R -> R -> Prop),
      Proper (eutt eq ==> eq ==> eq ==> eq ==> iff) (@interp_memory_prop E R R RR).
  Proof.
    intros E R RR.
    unfold interp_memory_prop.
    unfold Proper, respectful.
    intros.
    subst.
    split; intros INTERP.
    - rewrite <- H. eauto.
    - rewrite H. eauto.
  Qed.

  Lemma model_undef_h_oom :
    forall {R} oom_msg (t' : _ R),
      model_undef_h (E := ExternalCallE) (F := OOME +' UBE +' DebugE +' FailureE) eq (raiseOOM oom_msg) t' ->
      t' ≈ raiseOOM oom_msg.
  Proof.
    intros R.
    pcofix CIH.
    intros oom_msg t' Hmodel.
    punfold Hmodel.
    red in Hmodel.

    pstep; red.
    unfold raiseOOM in *.
    force_rewrite: @bind_trigger in Hmodel.
    force_rewrite @bind_trigger.

    remember (observe
                (vis (ThrowOOM oom_msg) (fun x : void => match x return (itree (ExternalCallE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE) R) with
                                                         end))).

    hinduction Hmodel before CIH; cbn; intros; inv Heqi; eauto; [solve [cbn in *; eapply EqTauL; auto] |]; try discriminate.

    dependent destruction H3.
    do 20 red in H.
    setoid_rewrite bind_trigger in H.
    rewrite H in H0.
    setoid_rewrite bind_vis in H0.
    setoid_rewrite bind_ret_l in H0.
    clear -H0.
    punfold H0.
    red in H0.
    cbn in *.
    remember (VisF (subevent void (resum IFun void (ThrowOOM oom_msg))) (fun x : void => k2 x)).
    hinduction H0 before i; intros; inv Heqi.
    - dependent destruction H1.
      econstructor; intros; contradiction.
    - econstructor; auto; eapply IHeqitF.
  Qed.

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

  Lemma interp_mcfg4_ret :
    forall R g l sid m (r : R),
      ℑs4 eq eq (ret r) g l sid m (Ret5 g l sid m r).
  Proof.
    intros.
    unfold interp_mcfg4, model_undef.
    setoid_rewrite interp_intrinsics_ret.
    setoid_rewrite interp_global_ret.
    unfold interp_local_stack.
    setoid_rewrite interp_state_ret.
    unfold interp_memory_prop.
    cbn.
    eexists (ret _).
    split.
    pstep; econstructor; eauto.
    2 : eapply model_undef_h_ret_pure; eauto.
    cbn. reflexivity.
  Qed.

  Lemma interp_mcfg4_ret_inv :
    forall R g l sid m (r : R) x,
      ℑs4 eq eq (ret r) g l sid m x ->
      (exists m' sid', ret (m := PropT _) (m', (sid', (l, (g, r)))) x) \/
        (exists A (e : OOME A) k, x ≈ vis e k)%type.
  Proof.
    intros.
    unfold interp_mcfg4, model_undef.
    destruct H as (?&?&?).
    setoid_rewrite interp_intrinsics_ret in H.
    setoid_rewrite interp_global_ret in H.
    unfold interp_local_stack in H.
    rewrite interp_state_ret in H.
    unfold interp_memory_prop in H.
    apply interp_memory_prop_ret_inv in H.
    destruct H as [(?&?&?) | (A&e&k&?)].
    { destruct x1 as (?&?&?).
      rewrite H1 in H0.
      apply interp_prop_ret_inv in H0.
      destruct H0 as (?&?&?). subst.
      cbn. left. exists m0, s. rewrite H2. reflexivity.
    }

    right.
    rewrite H in H0.
    clear H.
    red in H0.
    setoid_rewrite (itree_eta x) in H0.
    setoid_rewrite itree_eta.
    genobs x ox.
    clear x Heqox.

    punfold H0; red in H0; cbn in H0.
    dependent induction H0.
    - setoid_rewrite tau_eutt.
      setoid_rewrite itree_eta.
      eapply IHinterp_PropTF; eauto.
    - red in H; cbn in H; red in H.
      setoid_rewrite bind_ret_r in H.
      rewrite H in H0.
      setoid_rewrite bind_trigger in H0.

      punfold H0; red in H0; cbn in H0.
      dependent induction H0.
      + rewrite <- x.
        cbn.
        exists A. exists (resum IFun A e). exists k1.
        reflexivity.
      + rewrite <- x.
        cbn.
        setoid_rewrite tau_eutt.
        setoid_rewrite itree_eta.
        eapply IHeqitF; eauto.
  Qed.

  Definition alloc_code : code dtyp :=
    [ (IId (Name "ptr"), INSTR_Alloca (DTYPE_I 64%N) [])
    ].

  Definition ptoi_code : code dtyp :=
    [ (IId (Name "ptr"), INSTR_Alloca (DTYPE_I 64%N) []);
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

  Definition instr_E_to_L0 {T : Type} : instr_E T -> itree L0 T :=
    fun (e : instr_E T) =>
      match e with
      | inl1 call =>
          match call with
          | Call dt fv args =>
              raise "call"
          end
      | inr1 e0 =>
          trigger e0
      end.

  Definition interp_instr_E_to_L0 :=
    interp (@instr_E_to_L0).

  Lemma alloc_tree_simpl :
    interp_instr_E_to_L0 dvalue alloc_tree ≈
      Vis (subevent _ (Alloca (DTYPE_I 64) 1 None))
          (fun u => Vis (subevent _ (LocalWrite (Name "ptr") (dvalue_to_uvalue u)))
                     (fun _ => Ret (DVALUE_I1 DynamicValues.Int1.one))).

  Proof.
    unfold interp_instr_E_to_L0.
    unfold alloc_tree. cbn. go. cbn. go.
    unfold trigger. go.
    force_go. unfold instr_E_to_L0.
    cbn. force_go.
    eapply eqit_Vis.
    intros. force_go.
    rewrite bind_tau. go. rewrite tau_eutt.
    force_go. cbn. rewrite bind_trigger.
    eapply eqit_Vis.
    intros. force_go.
    rewrite bind_tau. go. rewrite tau_eutt.
    force_go. reflexivity.
  Qed.

  Lemma ptoi_tree_simpl :
    interp_instr_E_to_L0 dvalue ptoi_tree ≈
          Vis (subevent _ (Alloca (DTYPE_I 64) 1 None))
          (fun u => Vis (subevent _ (LocalWrite (Name "ptr") (dvalue_to_uvalue u)))
                      (fun x => Vis (subevent _ (LocalRead (Name "ptr")))
                                (fun u1 => Vis (subevent _ (LocalWrite (Name "i") (UVALUE_Conversion Ptrtoint DTYPE_Pointer u1 DTYPE_IPTR)))
                                            (fun _ => Ret (DVALUE_I1 DynamicValues.Int1.one))))).
  Proof.
    unfold interp_instr_E_to_L0.
    unfold ptoi_tree. cbn. go. cbn. go.
    unfold trigger. go.
    force_go. unfold instr_E_to_L0.
    cbn. force_go.
    eapply eqit_Vis.
    intros. force_go.
    rewrite bind_tau. go. rewrite tau_eutt.
    force_go. cbn. rewrite bind_trigger.
    eapply eqit_Vis.
    intros. force_go.
    rewrite bind_tau. go. rewrite tau_eutt.
    force_go. cbn. rewrite translate_vis.
    force_rewrite @bind_vis.
    force_rewrite @translate_vis.
    force_go. cbn. rewrite bind_trigger.

    eapply eqit_Vis.
    intros. force_go.
    rewrite bind_tau. go. rewrite tau_eutt.
    force_go. cbn. rewrite bind_trigger.

    eapply eqit_Vis.
    intros. force_go.
    rewrite bind_tau. go. rewrite tau_eutt.
    force_go. cbn. reflexivity.
  Qed.

  (* Few remarks about [L3_trace] used in [interp_mcfg4] *)
  Remark L3_trace_MemoryE:
    forall R X g l sid m (e : MemoryE X) (k : X -> itree L0 R) t,
      interp_memory_prop eq
        (vis e (fun x : X => interp_local_stack (interp_global (interp_intrinsics (k x)) g) l)) sid m t <->
      interp_memory_prop eq (interp_local_stack (interp_global (interp_intrinsics (vis e k)) g) l) sid m t.
  Proof.
    intros.
    rewrite interp_intrinsics_vis.
    cbn. rewrite interp_global_bind.
    rewrite interp_local_stack_bind.
    rewrite interp_global_trigger. cbn.
    rewrite bind_trigger.
    rewrite interp_local_stack_vis.
    rewrite bind_bind.
    cbn. rewrite bind_bind, bind_trigger.
    setoid_rewrite bind_ret_l.
    setoid_rewrite interp_local_stack_ret.
    setoid_rewrite bind_ret_l. cbn. reflexivity.
  Qed.

  Remark L3_trace_LocalWrite:
    forall R g l s sid m (k : unit -> itree L0 R) t id dv,
      interp_memory_prop eq
        (interp_local_stack (interp_global (interp_intrinsics (k tt)) g) (FMapAList.alist_add id dv l, s)) sid m t <->
      interp_memory_prop eq (interp_local_stack (interp_global (interp_intrinsics (vis (LocalWrite id dv) k)) g) (l, s)) sid m t.
  Proof.
    intros.
    rewrite interp_intrinsics_vis.
    cbn. rewrite interp_global_bind.
    rewrite interp_local_stack_bind.
    rewrite interp_global_trigger. cbn.
    rewrite bind_trigger.
    rewrite interp_local_stack_vis.
    rewrite bind_bind.
    cbn.
    setoid_rewrite interp_local_stack_ret.
    setoid_rewrite bind_ret_l.
    unfold handle_local. cbn.
    unfold handle_local_stack. cbn.
    cbn. unfold ITree.map. rewrite bind_ret_l.
    reflexivity.
  Qed.

  Remark L3_trace_LocalRead:
    forall R g l s sid m (k: _ -> itree L0 R) t id x,
      FMapAList.alist_find id l = ret x ->
      (interp_memory_prop eq (interp_local_stack (interp_global (interp_intrinsics (k (snd (l, s, x)))) g) (fst (l, s, x)))
        sid m t <->
      interp_memory_prop eq (interp_local_stack (interp_global (interp_intrinsics (vis (LocalRead id) k)) g) (l, s)) sid m t).
  Proof.
    intros.
    rewrite interp_intrinsics_vis.
    cbn. rewrite interp_global_bind.
    rewrite interp_local_stack_bind.
    rewrite interp_global_trigger. cbn.
    rewrite bind_trigger.
    rewrite interp_local_stack_vis.
    rewrite bind_bind.
    cbn.
    setoid_rewrite interp_local_stack_ret.
    setoid_rewrite bind_ret_l.
    unfold handle_local. cbn.
    unfold handle_local_stack. cbn.
    cbn. unfold ITree.map. rewrite H; cbn.
    do 2 rewrite bind_ret_l; reflexivity.
  Qed.

  Remark L3_trace_ret:
    forall R g l sid m r
      (t : itree (ExternalCallE +' LLVMParamsBigIntptr.Events.PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
            (_ * (store_id * (FMapAList.alist raw_id uvalue * Stack.stack * (FMapAList.alist raw_id dvalue * R))))),
      interp_memory_prop eq (Ret2 g l r) sid m t <->
      interp_memory_prop eq (interp_local_stack (interp_global (interp_intrinsics (ret r)) g) l) sid m t.
  Proof.
    intros.
    setoid_rewrite interp_intrinsics_ret.
    setoid_rewrite interp_global_ret.
    setoid_rewrite interp_local_stack_ret. reflexivity.
  Qed.

  Import MemTheory.

  (* remove allocation in infinite language *)
  Example remove_alloc_block :
    forall genv lenv stack sid m,
      refine_L6 (interp_mcfg4 eq eq (interp_instr_E_to_L0 _ alloc_tree) genv (lenv, stack) sid m)
                (interp_mcfg4 eq eq (interp_instr_E_to_L0 _ ret_tree) genv (lenv, stack) sid m).
  Proof.
    intros genv lenv stack sid m.
    unfold refine_L6.
    intros t' INTERP.

    unfold ret_tree, denote_program in INTERP.

    cbn in INTERP.
    unfold interp_instr_E_to_L0 in INTERP.

    force_go_hyps.
    apply interp_mcfg4_ret_inv in INTERP.
    destruct INTERP as [INTERP | OOM].
    2: {
      destruct OOM as [A [e [k EUTT]]].
      exists t'.
      split.
      - unfold interp_mcfg4.
        red.
        destruct e.
        exists (raiseOOM s).
        split.
        + unfold raiseOOM.
          eapply interp_mem_prop_Proper3.
          4: {
            eapply EqAxiom.bisimulation_is_eq.
            setoid_rewrite bind_trigger.
            reflexivity.
          }
          all: eauto.
          * reflexivity.
          * pstep; red; cbn.
            change
              (VisF (subevent void (ThrowOOM s))
                 (fun x : void =>
                    match
                      x
                      return
                      (itree (ExternalCallE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                         (MMEP.MMSP.MemState * (store_id * (local_env * Stack.stack * res_L1))))
                    with
                    end)) with
              (observe (Vis (subevent void (ThrowOOM s))
                          (fun x : void =>
                             match
                               x
                               return
                               (itree (ExternalCallE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                                  (MMEP.MMSP.MemState * (store_id * (local_env * @Stack.stack local_env * res_L1))))
                             with
                             end))).
            eapply Interp_Memory_PropT_Vis_OOM.
            reflexivity.
        + rewrite EUTT.
          red.
          pstep; red; cbn.
          change (VisF (subevent void (ThrowOOM s)) k) with (observe (Vis (subevent void (ThrowOOM s)) k)).
          econstructor.
          * intros [] _.
          * cbn. red.
            setoid_rewrite bind_ret_r.
            reflexivity.
          * setoid_rewrite bind_trigger.
            reflexivity.
      - reflexivity.
    }

    destruct INTERP as (?&?&?); do 4 red in H.

    epose proof allocate_dtyp_spec_can_always_succeed m m
     (mkMemState (ms_memory_stack m) (InfiniteAddresses.InfPROV.next_provenance (ms_provenance m)))
     (DTYPE_I 64) 1 _ _ _ _ _ as (ms_final & addr & ALLOC).
    Unshelve. 6 : intro H0; inv H0.
    2 : exact (ms_provenance m). 2,3 : shelve.
    2 : shelve.

    eexists (Ret5 genv (_, stack) sid ms_final _).
    split; cycle 1.
    { do 2 red. rewrite H.
      pstep; econstructor; eauto;
        repeat red; repeat econstructor; eauto. }

    clear H.

    eexists (Ret5 genv (_, stack) sid ms_final _).
    split; cycle 1.
    { eapply model_undef_h_ret_pure; typeclasses eauto. }

    rewrite alloc_tree_simpl.

    apply L3_trace_MemoryE.
    eapply (interp_memory_prop_vis _ _ _ _ _ (Ret _) (fun _ => Ret _))
      ; [ setoid_rewrite bind_ret_l; reflexivity |..].

    { cbn. unfold my_handle_memory_prop.
      unfold MemPropT_lift_PropT_fresh.
      right; right; right.
      exists sid, ms_final, (DVALUE_Addr addr).
      Unshelve.
      5 : exact (ms_final, (sid, DVALUE_Addr addr)).
      split; [ red; reflexivity |].
      6 : exact m. cbn in *.
      exists ms_final, addr. tauto.
      all:shelve. }

    intros. apply Returns_ret_inv in H0.
    destruct b as (?&?&?). inv H0; subst. cbn in *.
    eapply Returns_vis_inversion in H.
    destruct H as (?&?).
    apply Returns_ret_inv in H. subst.

    go.
    eapply L3_trace_LocalWrite.
    eapply L3_trace_ret.
    pstep; constructor; eauto.

    Unshelve.
    all : eauto.

  (* Remaining proof obligations are related to broken [MemMonad_valid_state] *)
  Admitted.

  Example remove_alloc_ptoi_block :
    forall genv lenv stack sid m,
      refine_L6
        (interp_mcfg4 eq eq (interp_instr_E_to_L0 _ ptoi_tree) genv (lenv, stack) sid m)
        (interp_mcfg4 eq eq (interp_instr_E_to_L0 _ ret_tree) genv (lenv, stack) sid m).
  Proof.
    intros genv lenv stack sid m.
    unfold refine_L6.
    intros t' INTERP.

    unfold ret_tree, denote_program in INTERP.

    cbn in INTERP.
    unfold interp_instr_E_to_L0 in INTERP.

    force_go_hyps.
    apply interp_mcfg4_ret_inv in INTERP.

    destruct INTERP as [INTERP | OOM].
    2: {
      destruct OOM as [A [e [k EUTT]]].
      exists t'.
      split.
      - unfold interp_mcfg4.
        red.
        destruct e.
        exists (raiseOOM s).
        split.
        + unfold raiseOOM.
          eapply interp_mem_prop_Proper3.
          4: {
            eapply EqAxiom.bisimulation_is_eq.
            setoid_rewrite bind_trigger.
            reflexivity.
          }
          all: eauto.
          * reflexivity.
          * pstep; red; cbn.
            change
              (VisF (subevent void (ThrowOOM s))
                 (fun x : void =>
                    match
                      x
                      return
                      (itree (ExternalCallE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                         (MMEP.MMSP.MemState * (store_id * (local_env * Stack.stack * res_L1))))
                    with
                    end)) with
              (observe (Vis (subevent void (ThrowOOM s))
                          (fun x : void =>
                             match
                               x
                               return
                               (itree (ExternalCallE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                                  (MMEP.MMSP.MemState * (store_id * (local_env * @Stack.stack local_env * res_L1))))
                             with
                             end))).
            eapply Interp_Memory_PropT_Vis_OOM.
            reflexivity.
        + rewrite EUTT.
          red.
          pstep; red; cbn.
          change (VisF (subevent void (ThrowOOM s)) k) with (observe (Vis (subevent void (ThrowOOM s)) k)).
          econstructor.
          * intros [] _.
          * cbn. red.
            setoid_rewrite bind_ret_r.
            reflexivity.
          * setoid_rewrite bind_trigger.
            reflexivity.
      - reflexivity.
    }

    destruct INTERP as (?&?&?); do 4 red in H.

    epose proof allocate_dtyp_spec_can_always_succeed m m
     (mkMemState (ms_memory_stack m) (InfiniteAddresses.InfPROV.next_provenance (ms_provenance m)))
     (DTYPE_I 64) 1 _ _ _ _ _ as (ms_final & addr & ALLOC).
    Unshelve. 6 : intro H0; inv H0.
    2 : exact (ms_provenance m). 2,3 : shelve.
    2 : shelve.

    eexists (Ret5 genv (_, stack) sid ms_final _).
    split; cycle 1.
    { do 2 red. rewrite H.
      pstep; econstructor; eauto;
        repeat red; repeat econstructor; eauto. }

    clear H.

    eexists (Ret5 genv (_, stack) sid ms_final _).
    split; cycle 1.
    { eapply model_undef_h_ret_pure; typeclasses eauto. }

    rewrite ptoi_tree_simpl.

    apply L3_trace_MemoryE.
    eapply (interp_memory_prop_vis _ _ _ _ _ (Ret _) (fun _ => Ret _))
      ; [ setoid_rewrite bind_ret_l; reflexivity |..].

    { cbn. unfold my_handle_memory_prop.
      unfold MemPropT_lift_PropT_fresh.
      right; right; right.
      exists sid, ms_final, (DVALUE_Addr addr).
      Unshelve.
      5 : exact (ms_final, (sid, DVALUE_Addr addr)).
      split; [ red; reflexivity |].
      6 : exact m. cbn in *.
      exists ms_final, addr. tauto.
      all:shelve. }

    intros. apply Returns_ret_inv in H0.
    destruct b as (?&?&?). inv H0; subst. cbn in *.
    eapply Returns_vis_inversion in H.
    destruct H as (?&?).
    apply Returns_ret_inv in H. subst.

    go.
    eapply L3_trace_LocalWrite.
    eapply L3_trace_LocalRead; [ reflexivity | ].
    eapply L3_trace_LocalWrite.
    eapply L3_trace_ret.
    pstep; constructor; eauto.

    Unshelve.
    all : eauto.

  (* Remaining proof obligations are related to broken [MemMonad_valid_state] *)
  Admitted.

  Lemma interp_memory_prop_vis_inv:
    forall E R X
      (e : (E +' LLVMParamsBigIntptr.Events.IntrinsicE +' LLVMParamsBigIntptr.Events.MemoryE +' LLVMParamsBigIntptr.Events.PickUvalueE +' OOME +' UBE +' DebugE +' FailureE) X)
      k sid m x,
      interp_memory_prop (E:=E) (R2 := R) eq (Vis e k) sid m x ->
      ((exists ta k2 s1 s2 ,
        x ≈ x <- ta;; k2 x /\
          interp_memory_prop_h e s1 s2 ta /\
          (forall (a : X) (b : MMEP.MMSP.MemState * (store_id * X)),
            @Returns (E +' IntrinsicE +' MemoryE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE) X a (trigger e) ->
            @Returns (E +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE) (MMEP.MMSP.MemState * (store_id * X)) b ta ->
            a = snd (snd b) ->
            interp_memory_prop (E := E) eq (k a) sid m (k2 b))) \/
        (exists A (e : OOME A) k, x ≈ vis e k)%type).
  Proof.
    intros.
    punfold H.
    red in H. cbn in H.
    setoid_rewrite (itree_eta x).
    remember (VisF e k).
    genobs x ox.
    clear x Heqox.
    hinduction H before sid; intros; inv Heqi; eauto.
    - specialize (IHinterp_memory_PropTF m eq_refl).
      destruct IHinterp_memory_PropTF as [(?&?&?&?&?&?&?) | (?&?&?&?)].
      2: {
        right.
        setoid_rewrite tau_eutt.
        rewrite <- itree_eta in H1.
        setoid_rewrite H1.
        exists x. exists x0. exists x1.
        reflexivity.
      }

      left.
      eexists _,_,_,_; split; eauto. rewrite tau_eutt.
      rewrite <- itree_eta in H1. eauto.
    - setoid_rewrite <- itree_eta.
      setoid_rewrite HT1.
      right.
      exists A. exists e0. exists k0.
      reflexivity.
    - dependent destruction H3.
      left.
      eexists _,_,_,_; split; eauto.
      + rewrite <- itree_eta; eauto.
      + split; eauto.
        intros. do 3 red.
        specialize (HK a b H1 H2 H3). pclearbot; auto.
  Qed.

  Lemma refine_OOM_h_model_undef_h_raise_OOM:
    forall R t1 oom_msg (k1 : R -> _) t3,
      refine_OOM_h (E := L4) refine_res3 t1 (raiseOOM oom_msg) ->
      model_undef_h eq (x <- Error.raise_oom oom_msg;; k1 x) t3 ->
      refine_OOM_h (E := L4) refine_res3 t1 t3.
  Proof.
    intros. punfold H. red in H.
    unfold Error.raise_oom, RAISE_OOM_ITREE_OOME, bind, Monad_itree, raiseOOM in *.
    force_rewrite: @bind_trigger in H0.
    force_rewrite: @bind_trigger in H.
    force_rewrite: @bind_vis in H0.
    red in H0. cbn in *. rewrite itree_eta, (itree_eta t3).
    do 2 red.
    punfold H0. red in H0; cbn in H0.
    remember (VisF (subevent void (ThrowOOM oom_msg))
            (fun x : void =>
             ITree.bind match x return (itree _ R) with
                        end (fun x0 : R => k1 x0))).
    remember (VisF (subevent void (ThrowOOM oom_msg))
           (fun x : void =>
            match
              x
              return
                (itree _
                   (LLVM.MEM.MMEP.MMSP.MemState * (store_id * (local_env * stack * res_L1))))
            with
            end)).
    hinduction H0 before i0; intros; inv Heqi.
    - pstep; constructor; eauto.
      specialize (IHinterp_PropTF eq_refl H eq_refl). punfold IHinterp_PropTF.
    - inv e.
    - dependent destruction H4.
      do 20 red in H.
      rewrite H in H0.
      setoid_rewrite bind_bind in H0.
      setoid_rewrite bind_trigger in H0.
      rewrite <- itree_eta. rewrite H0.
      pstep. eapply Interp_PropT_Vis_OOM.
      eapply eqit_Vis. intros; inv u.
      Unshelve. intros. inv H2.
  Qed.

  Lemma refine_OOM_h_model_undef_h_raise_ret:
    forall t1 t3 r,
      refine_OOM_h (E := L4) refine_res3 t1 (ret r) ->
      model_undef_h eq (ret r) t3 ->
      refine_OOM_h (E := L4) refine_res3 t1 t3.
  Proof.
    intros.
    eapply interp_prop_ret_inv in H0.
    destruct H0 as (?&?&?).
    subst. rewrite H1.
    eapply interp_prop_ret_inv in H.
    destruct H as (?&?&?).
    subst. rewrite H0.
    pstep; constructor; eauto.
  Qed.

  (* Add allocation in infinite language *)
  Example add_alloc :
    forall genv lenv stack sid m,
      refine_L6 (interp_mcfg4 eq eq (interp_instr_E_to_L0 _ ret_tree) genv (lenv, stack) sid m)
                (interp_mcfg4 eq eq (interp_instr_E_to_L0 _ alloc_tree) genv (lenv, stack) sid m).
  Proof.
    intros genv lenv stack sid m.
    unfold refine_L6.
    intros t' INTERP.

    unfold ret_tree, denote_program in INTERP.
    destruct INTERP as (?&?&?).
    rewrite alloc_tree_simpl in H.
    apply L3_trace_MemoryE in H.

    apply interp_memory_prop_vis_inv in H.
    destruct H as (alloc_t&k1&s1&ms1&EQ1&SPEC1&HK).
    rewrite EQ1 in H0. clear x EQ1.

    pose proof allocate_dtyp_spec_inv ms1 (DTYPE_I 64) as ALLOCINV.
    assert (abs : DTYPE_I 64 <> DTYPE_Void) by (intros abs; inv abs).
    specialize (ALLOCINV 1%N abs); eauto; clear abs.

    destruct SPEC1 as [ALLOC_UB | [ALLOC_ERR | [ALLOC_OOM | ALLOC_SUC]]].
    { (* UB *)
      destruct ALLOC_UB as [ub_msg [ALLOC_UB | [sab [a [ALLOC_UB []]]]]].
      specialize (ALLOCINV _ ALLOC_UB).
      destruct ALLOCINV as [[ms_final [ptr ALLOC_INV]] | [oom_msg ALLOC_INV]];
        inv ALLOC_INV. }
    { (* ERR *)
      destruct ALLOC_ERR as [err_msg [MAP [spec_msg [ALLOC_ERR | [sab [a [ALLOC_ERR []]]]]]]].
      apply ALLOCINV in ALLOC_ERR.
      destruct ALLOC_ERR as [[ms_final [ptr ALLOC_ERR]] | [oom_msg ALLOC_ERR]];
        inv ALLOC_ERR. }
    { (* OOM *)
      destruct ALLOC_OOM as [err_msg [MAP [spec_msg [ALLOC_OOM | [sab [a [ALLOC_OOM []]]]]]]].
      apply ALLOCINV in ALLOC_OOM. clear ALLOCINV.
      destruct ALLOC_OOM as [[ms_final [ptr ALLOC_OOM]] | [oom_msg ALLOC_OOM]];
        inv ALLOC_OOM.

      rewrite MAP in H0.
      exists (Ret5 genv (lenv, stack) sid m (DVALUE_I1 DynamicValues.Int1.one)).
      split; cycle 1.
      { clear -H0.
        eapply refine_OOM_h_model_undef_h_raise_OOM; eauto.
        eapply refine_oom_h_raise_oom; typeclasses eauto. }
      { unfold interp_instr_E_to_L0. unfold ret_tree. cbn.
        force_go. cbn. force_go.
        apply interp_mcfg4_ret. } }

    clear ALLOCINV.
    exists (Ret5 genv (lenv, stack) sid m (DVALUE_I1 DynamicValues.Int1.one)).
    destruct ALLOC_SUC as (?&?&?&?&?).
    rewrite H in H0; setoid_rewrite bind_ret_l in H0.
    split.
    { unfold interp_instr_E_to_L0. unfold ret_tree. cbn.
      force_go. cbn. force_go.
      apply interp_mcfg4_ret. }

    assert (alloca_returns:
             forall x, Returns
                    (E := ExternalCallE +'
                        LLVMParamsBigIntptr.Events.IntrinsicE +'
                        LLVMParamsBigIntptr.Events.MemoryE +'
                        LLVMParamsBigIntptr.Events.PickUvalueE +'
                        OOME +' UBE +' DebugE +' FailureE)
                                   x (trigger (Alloca (DTYPE_I 64) 1 None))).
    { intros. unfold trigger.
      eapply ReturnsVis; [ reflexivity | ].
      Unshelve. eapply ReturnsRet. reflexivity. }

    assert (alloc_t_returns : Returns (x0, (x, x1)) alloc_t).
    { rewrite H; apply ReturnsRet; reflexivity. }

    specialize (HK _ _ (alloca_returns x1) alloc_t_returns eq_refl).
    clear alloca_returns alloc_t_returns.

    eapply L3_trace_LocalWrite in HK.
    eapply L3_trace_ret in HK.
    apply interp_memory_prop_ret_inv in HK.
    destruct HK as (?&?&?).
    destruct x2 as (?&?&?&?).
    rewrite H3 in H0.

    inv H2.
    eapply refine_OOM_h_model_undef_h_raise_ret; eauto.
    pstep; repeat constructor; eauto.

    intros o CONTRA. inv CONTRA.
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
  Import LLVMEvents.
  Import LLVMAst.
  Import CFG.

  Import List.
  Import ListNotations.
  Require Import Coq.Strings.String.

  Module MemTheory  := MemoryModelTheory LP MP MMEP MEM_MODEL.
  Import MemTheory.

  Definition alloc_code : code dtyp :=
    [ (IId (Name "ptr"), INSTR_Alloca (DTYPE_I 64%N) [])
    ].

  Definition ptoi_code : code dtyp :=
    [ (IId (Name "ptr"), INSTR_Alloca (DTYPE_I 64%N) []);
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
    := trigger (Alloca (DTYPE_I 64%N) 1 None);; ret (DVALUE_I1 one).

  Definition t_ret : itree L0 dvalue
    := ret (DVALUE_I1 one).

  Definition instr_E_to_L0 {T : Type} : instr_E T -> itree L0 T :=
    fun (e : instr_E T) =>
      match e with
      | inl1 call =>
          match call with
          | Call dt fv args =>
              raise "call"
          end
      | inr1 e0 =>
          trigger e0
      end.

  Definition interp_instr_E_to_L0 :=
    interp (@instr_E_to_L0).

  #[global] Instance interp_mem_prop_Proper3 :
  forall {E}
      {R} (RR : R -> R -> Prop),
      Proper (eutt eq ==> eq ==> eq ==> eq ==> iff) (@interp_memory_prop E R R RR).
  Proof.
    intros E R RR.
    unfold interp_memory_prop.
    unfold Proper, respectful.
    intros.
    subst.
    split; intros INTERP.
    - rewrite <- H. eauto.
    - rewrite H. eauto.
  Qed.

  Lemma alloc_tree_simpl :
    interp_instr_E_to_L0 dvalue alloc_tree ≈
      Vis (subevent _ (Alloca (DTYPE_I 64) 1 None))
          (fun u => Vis (subevent _ (LocalWrite (Name "ptr") (dvalue_to_uvalue u)))
                     (fun _ => Ret (DVALUE_I1 DynamicValues.Int1.one))).
  Proof.
    unfold interp_instr_E_to_L0.
    unfold alloc_tree. cbn. go. cbn. go.
    unfold trigger. go.
    force_go. unfold instr_E_to_L0.
    cbn. force_go.
    eapply eqit_Vis.
    intros. force_go.
    rewrite bind_tau. go. rewrite tau_eutt.
    force_go. cbn. rewrite bind_trigger.
    eapply eqit_Vis.
    intros. force_go.
    rewrite bind_tau. go. rewrite tau_eutt.
    force_go. reflexivity.
  Qed.

  Lemma refine_OOM_h_model_undef_h_raise_OOM:
    forall R t1 oom_msg (k1 : R -> _) t3,
      refine_OOM_h (E := L4) refine_res3 t1 (raiseOOM oom_msg) ->
      model_undef_h eq (x <- Error.raise_oom oom_msg;; k1 x) t3 ->
      refine_OOM_h (E := L4) refine_res3 t1 t3.
  Proof.
    intros. punfold H. red in H.
    unfold Error.raise_oom, RAISE_OOM_ITREE_OOME, bind, Monad_itree, raiseOOM in *.
    force_rewrite: @bind_trigger in H0.
    force_rewrite: @bind_trigger in H.
    force_rewrite: @bind_vis in H0.
    red in H0. cbn in *. rewrite itree_eta, (itree_eta t3).
    do 2 red.
    punfold H0. red in H0; cbn in H0.
    remember (VisF (subevent void (ThrowOOM oom_msg))
            (fun x : void =>
             ITree.bind match x return (itree _ R) with
                        end (fun x0 : R => k1 x0))).
    remember (VisF (subevent void (ThrowOOM oom_msg))
           (fun x : void =>
            match
              x
              return
                (itree _
                   (LLVM.MEM.MMEP.MMSP.MemState * (store_id * (local_env * stack * res_L1))))
            with
            end)).
    hinduction H0 before i0; intros; inv Heqi.
    - pstep; constructor; eauto.
      specialize (IHinterp_PropTF eq_refl H eq_refl). punfold IHinterp_PropTF.
    - inv e.
    - dependent destruction H4.
      do 20 red in H.
      rewrite H in H0.
      setoid_rewrite bind_bind in H0.
      setoid_rewrite bind_trigger in H0.
      rewrite <- itree_eta. rewrite H0.
      pstep. eapply Interp_PropT_Vis_OOM.
      eapply eqit_Vis. intros; inv u.
      Unshelve. intros. inv H2.
  Qed.

  Lemma refine_OOM_h_model_undef_h_raise_ret:
    forall t1 t3 r,
      refine_OOM_h (E := L4) refine_res3 t1 (ret r) ->
      model_undef_h eq (ret r) t3 ->
      refine_OOM_h (E := L4) refine_res3 t1 t3.
  Proof.
    intros.
    eapply interp_prop_ret_inv in H0.
    destruct H0 as (?&?&?).
    subst. rewrite H1.
    eapply interp_prop_ret_inv in H.
    destruct H as (?&?&?).
    subst. rewrite H0.
    pstep; constructor; eauto.
  Qed.

  (* Few remarks about [L3_trace] used in [interp_mcfg4] *)
  Remark L3_trace_MemoryE:
    forall R X g l sid m (e : MemoryE X) (k : X -> itree L0 R) t,
      interp_memory_prop eq
            (vis e (fun x : X => interp_local_stack (interp_global (interp_intrinsics (k x)) g) l)) sid m t <->
      interp_memory_prop eq (interp_local_stack (interp_global (interp_intrinsics (vis e k)) g) l) sid m t.
  Proof.
    intros.
    rewrite interp_intrinsics_vis.
    cbn. rewrite interp_global_bind.
    rewrite interp_local_stack_bind.
    rewrite interp_global_trigger. cbn.
    rewrite bind_trigger.
    rewrite interp_local_stack_vis.
    rewrite bind_bind.
    cbn. rewrite bind_bind, bind_trigger.
    setoid_rewrite bind_ret_l.
    setoid_rewrite interp_local_stack_ret.
    setoid_rewrite bind_ret_l. cbn. reflexivity.
  Qed.

  Remark L3_trace_LocalWrite:
    forall R g l s sid m (k : unit -> itree L0 R) t id dv,
      interp_memory_prop eq
        (interp_local_stack (interp_global (interp_intrinsics (k tt)) g) (FMapAList.alist_add id dv l, s)) sid m t <->
      interp_memory_prop eq (interp_local_stack (interp_global (interp_intrinsics (vis (LocalWrite id dv) k)) g) (l, s)) sid m t.
  Proof.
    intros.
    rewrite interp_intrinsics_vis.
    cbn. rewrite interp_global_bind.
    rewrite interp_local_stack_bind.
    rewrite interp_global_trigger. cbn.
    rewrite bind_trigger.
    rewrite interp_local_stack_vis.
    rewrite bind_bind.
    cbn.
    setoid_rewrite interp_local_stack_ret.
    setoid_rewrite bind_ret_l.
    unfold handle_local. cbn.
    unfold handle_local_stack. cbn.
    cbn. unfold ITree.map. rewrite bind_ret_l.
    reflexivity.
  Qed.

  Remark L3_trace_LocalRead:
    forall R g l s sid m (k: _ -> itree L0 R) t id x,
      FMapAList.alist_find id l = ret x ->
      (interp_memory_prop eq (interp_local_stack (interp_global (interp_intrinsics (k (snd (l, s, x)))) g) (fst (l, s, x)))
        sid m t <->
      interp_memory_prop eq (interp_local_stack (interp_global (interp_intrinsics (vis (LocalRead id) k)) g) (l, s)) sid m t).
  Proof.
    intros.
    rewrite interp_intrinsics_vis.
    cbn. rewrite interp_global_bind.
    rewrite interp_local_stack_bind.
    rewrite interp_global_trigger. cbn.
    rewrite bind_trigger.
    rewrite interp_local_stack_vis.
    rewrite bind_bind.
    cbn.
    setoid_rewrite interp_local_stack_ret.
    setoid_rewrite bind_ret_l.
    unfold handle_local. cbn.
    unfold handle_local_stack. cbn.
    cbn. unfold ITree.map. rewrite H; cbn.
    do 2 rewrite bind_ret_l; reflexivity.
  Qed.

  Remark L3_trace_ret:
    forall R g l sid m (r : R)
       (t : itree (ExternalCallE +' LLVMParams64BitIntptr.Events.PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
         (MMEP.MMSP.MemState *
          (store_id * (FMapAList.alist raw_id uvalue * Stack.stack * (FMapAList.alist raw_id dvalue * R))))),
      interp_memory_prop eq (Ret2 g l r) sid m t <->
      interp_memory_prop eq (interp_local_stack (interp_global (interp_intrinsics (ret r)) g) l) sid m t.
  Proof.
    intros.
    setoid_rewrite interp_intrinsics_ret.
    setoid_rewrite interp_global_ret.
    setoid_rewrite interp_local_stack_ret. reflexivity.
  Qed.

  Lemma interp_memory_prop_vis_inv:
    forall E R X
      (e : (E +' LLVMParams64BitIntptr.Events.IntrinsicE +' LLVMParams64BitIntptr.Events.MemoryE +' LLVMParams64BitIntptr.Events.PickUvalueE +' OOME +' UBE +' DebugE +' FailureE) X)
      k sid m x,
      (forall (o : OOME X), e <> subevent _ o) ->
      interp_memory_prop (E:=E) (R2 := R) eq (Vis e k) sid m x ->
      (exists ta k2 s1 s2 ,
        x ≈ x <- ta;; k2 x /\
          interp_memory_prop_h e s1 s2 ta /\
          (forall (a : X) (b : MMEP.MMSP.MemState * (store_id * X)),
            @Returns (E +' IntrinsicE +' MemoryE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE) X a (trigger e) ->
            @Returns (E +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE) (MMEP.MMSP.MemState * (store_id * X)) b ta ->
            a = snd (snd b) ->
            interp_memory_prop (E := E) eq (k a) sid m (k2 b))).
  Proof.
    intros.
    rename H into NOOM.
    rename H0 into H.
    punfold H.
    red in H. cbn in H.
    setoid_rewrite (itree_eta x).
    remember (VisF e k).
    hinduction H before sid; intros; inv Heqi; eauto.
    - specialize (IHinterp_memory_PropTF m NOOM eq_refl).
      destruct IHinterp_memory_PropTF as (?&?&?&?&?&?&?).
      eexists _,_,_,_; split; eauto. rewrite tau_eutt.
      rewrite <- itree_eta in H1. eauto.
    - rewrite itree_eta in HT1.
      rewrite H0 in HT1.
      pinversion HT1; repeat subst_existT.
      specialize (NOOM e0).
      contradiction.
    - dependent destruction H3.
      eexists _,_,_,_; split; eauto.
      + rewrite <- itree_eta; eauto.
      + split; eauto.
        intros. do 3 red.
        specialize (HK a b H1 H2 H3). pclearbot; auto.
  Qed.

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

  Lemma interp_mcfg4_ret :
    forall R g l sid m (r : R),
      ℑs4 eq eq (ret r) g l sid m (Ret5 g l sid m r).
  Proof.
    intros.
    unfold interp_mcfg4, model_undef.
    setoid_rewrite interp_intrinsics_ret.
    setoid_rewrite interp_global_ret.
    unfold interp_local_stack.
    setoid_rewrite interp_state_ret.
    unfold interp_memory_prop.
    cbn.
    eexists (ret _).
    split.
    pstep; econstructor; eauto.
    2 : eapply model_undef_h_ret_pure; eauto.
    cbn. reflexivity.
  Qed.

  Lemma interp_mcfg4_ret_inv :
    forall R g l sid m (r : R) x,
      ℑs4 eq eq (ret r) g l sid m x ->
        exists m' sid', ret (m := PropT _) (m', (sid', (l, (g, r)))) x.
  Proof.
    intros.
    unfold interp_mcfg4, model_undef.
    destruct H as (?&?&?).
    setoid_rewrite interp_intrinsics_ret in H.
    setoid_rewrite interp_global_ret in H.
    unfold interp_local_stack in H.
    rewrite interp_state_ret in H.
    unfold interp_memory_prop in H.
    apply interp_memory_prop_ret_inv in H.
    destruct H as (?&?&?).
    destruct x1 as (?&?&?).
    rewrite H1 in H0.
    apply interp_prop_ret_inv in H0.
    destruct H0 as (?&?&?). subst.
    cbn. exists m0, s. rewrite H2. reflexivity.
  Qed.

  (* Add allocation in the finite language *)
  Example add_alloc :
    forall genv lenv stack sid m,
      refine_L6 (interp_mcfg4 eq eq (interp_instr_E_to_L0 _ ret_tree) genv (lenv, stack) sid m)
                (interp_mcfg4 eq eq (interp_instr_E_to_L0 _ alloc_tree) genv (lenv, stack) sid m).
  Proof.
    intros genv lenv stack sid m.
    unfold refine_L6.
    intros t' INTERP.

    unfold ret_tree, denote_program in INTERP.
    destruct INTERP as (?&?&?).
    rewrite alloc_tree_simpl in H.
    apply L3_trace_MemoryE in H.

    apply interp_memory_prop_vis_inv in H.
    destruct H as (alloc_t&k1&s1&ms1&EQ1&SPEC1&HK).
    rewrite EQ1 in H0. clear x EQ1.

    Import MemTheory.
    pose proof allocate_dtyp_spec_inv ms1 (DTYPE_I 64) as ALLOCINV.
    assert (abs : DTYPE_I 64 <> DTYPE_Void) by (intros abs; inv abs).
    specialize (ALLOCINV 1%N abs); eauto; clear abs.

    destruct SPEC1 as [ALLOC_UB | [ALLOC_ERR | [ALLOC_OOM | ALLOC_SUC]]].
    { (* UB *)
      destruct ALLOC_UB as [ub_msg [ALLOC_UB | [sab [a [ALLOC_UB []]]]]].
      specialize (ALLOCINV _ ALLOC_UB).
      destruct ALLOCINV as [[ms_final [ptr ALLOC_INV]] | [oom_msg ALLOC_INV]];
        inv ALLOC_INV. }
    { (* ERR *)
      destruct ALLOC_ERR as [err_msg [MAP [spec_msg [ALLOC_ERR | [sab [a [ALLOC_ERR []]]]]]]].
      apply ALLOCINV in ALLOC_ERR.
      destruct ALLOC_ERR as [[ms_final [ptr ALLOC_ERR]] | [oom_msg ALLOC_ERR]];
        inv ALLOC_ERR. }
    { (* OOM *)
      destruct ALLOC_OOM as [err_msg [MAP [spec_msg [ALLOC_OOM | [sab [a [ALLOC_OOM []]]]]]]].
      apply ALLOCINV in ALLOC_OOM. clear ALLOCINV.
      destruct ALLOC_OOM as [[ms_final [ptr ALLOC_OOM]] | [oom_msg ALLOC_OOM]];
        inv ALLOC_OOM.

      rewrite MAP in H0.
      exists (Ret5 genv (lenv, stack) sid m (DVALUE_I1 DynamicValues.Int1.one)).
      split; cycle 1.
      { clear -H0.
        eapply refine_OOM_h_model_undef_h_raise_OOM; eauto.
        eapply refine_oom_h_raise_oom; typeclasses eauto. }
      { unfold interp_instr_E_to_L0. unfold ret_tree. cbn.
        force_go. cbn. force_go.
        apply interp_mcfg4_ret. } }

    clear ALLOCINV.
    exists (Ret5 genv (lenv, stack) sid m (DVALUE_I1 DynamicValues.Int1.one)).
    destruct ALLOC_SUC as (?&?&?&?&?).
    rewrite H in H0; setoid_rewrite bind_ret_l in H0.
    split.
    { unfold interp_instr_E_to_L0. unfold ret_tree. cbn.
      force_go. cbn. force_go.
      apply interp_mcfg4_ret. }

    assert (alloca_returns:
             forall x, Returns
                    (E := ExternalCallE +'
                          LLVMParams64BitIntptr.Events.IntrinsicE +'
                          LLVMParams64BitIntptr.Events.MemoryE +'
                          LLVMParams64BitIntptr.Events.PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                    x (trigger (Alloca (DTYPE_I 64) 1 None))).
    { intros. unfold trigger.
      eapply ReturnsVis; [ reflexivity | ].
      Unshelve. eapply ReturnsRet. reflexivity. }

    assert (alloc_t_returns : Returns (x0, (x, x1)) alloc_t).
    { rewrite H; apply ReturnsRet; reflexivity. }

    specialize (HK _ _ (alloca_returns x1) alloc_t_returns eq_refl).
    clear alloca_returns alloc_t_returns.

    eapply L3_trace_LocalWrite in HK.
    eapply L3_trace_ret in HK.
    apply interp_memory_prop_ret_inv in HK.
    destruct HK as (?&?&?).
    destruct x2 as (?&?&?&?).
    rewrite H3 in H0.

    inv H2.
    eapply refine_OOM_h_model_undef_h_raise_ret; eauto.
    pstep; repeat constructor; eauto.

    intros o CONTRA; inv CONTRA.
  Qed.

End Finite.
