From Vellvm Require Import
     TopLevel
     TopLevelRefinements
     Refinement
     Utils.Monads
     Utils.PropT
     Utils.Tactics
     Utils.MonadEq1Laws
     Utils.InterpProp
     Utils.InterpPropOOM
     Utils.InterpMemoryProp
     Utils.ITreeMap
     Utils.Raise
     Utils.Tactics
     Utils.VellvmRelations
     Theory.DenotationTheory
     Theory.InterpreterMCFG
     Theory.ContainsUBExtra
     Handlers.MemoryModelImplementation
     Semantics.StoreId.

From ITree Require Import
     ITree
     Eq
     Basics.

Import HeterogeneousRelations.

From Coq Require Import
     ZArith
     Relations.

From ExtLib Require Import
     Monads.

Import MonadNotation.
Import DynamicTypes.
Import DynamicValues.
Import VellvmIntegers.
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
      Proper (eutt eq ==> eq ==> eq ==> eq ==> iff) (@interp_memory_spec E R R RR).
  Proof.
    intros E R RR.
    unfold interp_memory_spec.
    unfold Proper, respectful.
    intros.
    subst.
    split; intros INTERP.
    - rewrite <- H. eauto.
    - rewrite H. eauto.
  Qed.

  (* addition of contains_UB in k_spec broke this *)
  (* Lemma model_undef_h_oom : *)
  (*   forall {R} oom_msg (t' : _ R), *)
  (*     model_undef_h (E := ExternalCallE) (F := OOME +' UBE +' DebugE +' FailureE) eq (raiseOOM oom_msg) t' -> *)
  (*     t' ≈ raiseOOM oom_msg. *)
  (* Proof. *)
  (*   intros R. *)
  (*   pcofix CIH. *)
  (*   intros oom_msg t' Hmodel. *)
  (*   punfold Hmodel. *)
  (*   red in Hmodel. *)

  (*   pstep; red. *)
  (*   unfold raiseOOM in *. *)
  (*   force_rewrite: @bind_trigger in Hmodel. *)
  (*   force_rewrite @bind_trigger. *)

  (*   remember (observe *)
  (*               (vis (ThrowOOM (print_msg oom_msg)) (fun x : void => match x return (itree (ExternalCallE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE) R) with *)
  (*                                                        end))). *)

  (*   hinduction Hmodel before CIH; cbn; intros; inv Heqi; eauto; [solve [cbn in *; eapply EqTauL; auto] | | |]; try discriminate. *)
  (*   { destruct e, u. *)
  (*     pinversion HT1; subst_existT. *)
  (*     - unfold print_msg. *)
  (*       constructor. *)
  (*       intros []. *)
  (*     - inv CHECK0. *)
  (*   } *)

  (*   dependent destruction H1. *)
  (*   do 20 red in HSPEC. *)
  (*   setoid_rewrite bind_trigger in HSPEC. *)
  (*   red in KS. *)
  (*   rewrite HSPEC in HK. *)
  (*   setoid_rewrite bind_vis in H0. *)
  (*   setoid_rewrite bind_ret_l in H0. *)
  (*   clear -H0. *)
  (*   punfold H0. *)
  (*   red in H0. *)
  (*   cbn in *. *)
  (*   remember (VisF (subevent void (resum IFun void (ThrowOOM (print_msg oom_msg)))) (fun x : void => k2 x)). *)
  (*   hinduction H0 before i; intros; inv Heqi. *)
  (*   - dependent destruction H1. *)
  (*     econstructor; intros; contradiction. *)
  (*   - econstructor; auto; eapply IHeqitF. *)
  (* Qed. *)

  Lemma model_undef_h_ret_pure :
    forall {E F : Type -> Type}
      `{FAIL : FailureE -< E +' F}
      `{UB : UBE -< E +' F}
      `{OOM : OOME -< F}
      {X} (x : X)
      (RR : relation X) `{REF : Reflexive X RR},
      model_undef_h RR (ret x) (ret x).
  Proof.
    intros E F FAIL UB OOM X x RR REF.
    unfold model_undef_h.
    apply interp_prop_oom_ret_pure; auto.
  Qed.

  Lemma model_undef_h_ret_inv :
    forall {E F : Type -> Type}
      `{FAIL : FailureE -< E +' F}
      `{UB : UBE -< E +' F}
      `{OOMF : OOME -< F}
      {X} (x : X) (t : itree (E +' F) X),
      model_undef_h eq (ret x) t ->
      t ≈ Ret x \/ (exists (A : Type) (e : OOME A) (k : A -> itree (E +' F) X), t ≈ vis e k).
  Proof.
    intros E F FAIL UB OOM X x t UNDEF.
    unfold model_undef_h in *.
    eapply interp_prop_oom_ret_inv in UNDEF.
    destruct UNDEF as [[r2 [EQ T']] | OOM_CASE]; subst; eauto.
  Qed.

  Lemma interp_mcfg4_ret :
    forall R g l sid m (r : R),
      ℑs4 eq (MemoryBigIntptr.MMEP.MemSpec.MemState_eqv × eq) (ret r) g l sid m (Ret5 g l sid m r).
  Proof.
    intros.
    unfold interp_mcfg4, model_undef.
    setoid_rewrite interp_intrinsics_ret.
    setoid_rewrite interp_global_ret.
    unfold interp_local_stack.
    setoid_rewrite interp_state_ret.
    unfold interp_memory_spec.
    cbn.
    eexists (ret _).
    split.
    pstep; econstructor; eauto.
    2 : eapply model_undef_h_ret_pure; eauto.
    cbn. reflexivity.
    typeclasses eauto.
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
    unfold interp_memory_spec in H.
    apply interp_memory_prop_ret_inv in H.
    destruct H as [(?&?&?) | (A&e&k&?)].
    { destruct x1 as (?&?&?).
      rewrite H1 in H0.
      apply interp_prop_oom_ret_inv in H0.
      destruct H0 as [(?&?&?) | OOM_CASE]; subst; eauto.
      cbn. left. exists m0, s. rewrite H2.
      cbn.
      reflexivity.
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
      eapply IHinterp_prop_oomTF; eauto.
    - cbn.
      setoid_rewrite <- itree_eta.
      setoid_rewrite HT1.
      exists A0. exists e0. exists k2.
      reflexivity.
    - red in HSPEC; cbn in HSPEC; red in HSPEC.
      setoid_rewrite bind_ret_r in HSPEC.
      red in KS.
      rewrite HSPEC in KS.
      destruct KS as [UB | KS].
      { exfalso.
        destruct e.
        clear - UB.
        dependent induction UB.
        - pinversion H; subst; cbn in *.
          inv CHECK.
        - pinversion H; repeat subst_existT.
          setoid_rewrite resum_to_subevent in H5.
          rewrite subevent_subevent in H5.
          destruct e.
          inv H5.
          destruct s; inv H5.
          destruct x.
        - pinversion H; repeat subst_existT.
          setoid_rewrite resum_to_subevent in H4.
          repeat rewrite subevent_subevent in H4.
          inv H4.
      }

      setoid_rewrite bind_trigger in KS.

      punfold KS; red in KS; cbn in KS.
      dependent induction KS.
      + rewrite <- x.
        cbn.
        exists A. exists (resum IFun A e). exists k1.
        reflexivity.
      + rewrite <- x.
        cbn.
        setoid_rewrite tau_eutt.
        setoid_rewrite itree_eta.
        eapply IHKS; eauto.
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
                     (fun _ => Ret (DVALUE_I1 Int1.one))).

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
                               (fun u1 => u <- concretize_if_no_undef_or_poison (UVALUE_Conversion Ptrtoint DTYPE_Pointer u1 DTYPE_IPTR);;
                                       Vis (subevent _ (LocalWrite (Name "i") u))
                                         (fun _ => Ret (DVALUE_I1 Int1.one))))).
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
    force_go. cbn.
    rewrite interp_translate.
    eapply eqit_bind'.
    { (* TODO: Make this a lemma *)
      cbn.
      unfold concretize_if_no_undef_or_poison.
      cbn.
      break_match.
      - force_go. reflexivity.
      - force_go. cbn.
        setoid_rewrite concretize_uvalue_err_ub_oom_to_itree.
        remember (concretize_uvalue u1) as conc.
        Import Monad ITreeMonad.
        destruct_err_ub_oom conc.
        + setoid_rewrite raiseOOM_bind_itree.
          setoid_rewrite interp_trigger.
          rewrite interp_translate.
          unfold raiseOOM.
          setoid_rewrite bind_trigger.
          force_go; cbn.
          setoid_rewrite bind_trigger; cbn.
          eapply eqit_Vis.
          intros [].
        + setoid_rewrite raiseUB_bind_itree.
          rewrite interp_translate.
          unfold raiseUB.
          setoid_rewrite bind_trigger.
          force_go; cbn.
          setoid_rewrite bind_trigger; cbn.
          eapply eqit_Vis.
          intros [].
        + setoid_rewrite raise_bind_itree.
          rewrite interp_translate.
          unfold raise.
          setoid_rewrite bind_trigger.
          force_go; cbn.
          setoid_rewrite bind_trigger; cbn.
          eapply eqit_Vis.
          intros [].
        + cbn. go.
          rewrite translate_bind.
          rewrite interp_bind.
          setoid_rewrite translate_ret.
          setoid_rewrite interp_ret.
          rewrite interp_translate.
          cbn.
          eapply eqit_bind'.
          { rewrite interp_trigger_h.
          }
    }
    eapply eqit_clos_bind.
    rewrite bind_trigger.

    eapply eqit_Vis.
    intros. force_go.
    rewrite bind_tau. go. rewrite tau_eutt.
    force_go. cbn. reflexivity.
  Qed.

  (* Few remarks about [L3_trace] used in [interp_mcfg4] *)
  Remark L3_trace_MemoryE:
    forall R X g l sid m (e : MemoryE X) (k : X -> itree L0 R) t,
      interp_memory_spec eq
        (vis e (fun x : X => interp_local_stack (interp_global (interp_intrinsics (k x)) g) l)) sid m t <->
      interp_memory_spec eq (interp_local_stack (interp_global (interp_intrinsics (vis e k)) g) l) sid m t.
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
      interp_memory_spec eq
        (interp_local_stack (interp_global (interp_intrinsics (k tt)) g) (FMapAList.alist_add id dv l, s)) sid m t <->
      interp_memory_spec eq (interp_local_stack (interp_global (interp_intrinsics (vis (LocalWrite id dv) k)) g) (l, s)) sid m t.
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
      (interp_memory_spec eq (interp_local_stack (interp_global (interp_intrinsics (k (snd (l, s, x)))) g) (fst (l, s, x)))
        sid m t <->
      interp_memory_spec eq (interp_local_stack (interp_global (interp_intrinsics (vis (LocalRead id) k)) g) (l, s)) sid m t).
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
      interp_memory_spec eq (Ret2 g l r) sid m t <->
      interp_memory_spec eq (interp_local_stack (interp_global (interp_intrinsics (ret r)) g) l) sid m t.
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
      MMEP.MemExecM.MemMonad_valid_state m sid ->
      refine_L6 (interp_mcfg4 eq eq (interp_instr_E_to_L0 _ alloc_tree) genv (lenv, stack) sid m)
                (interp_mcfg4 eq eq (interp_instr_E_to_L0 _ ret_tree) genv (lenv, stack) sid m).
  Proof.
    intros genv lenv stack sid m VALID.
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
        exists (raiseOOM "").
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
              (VisF (subevent void (ThrowOOM (print_msg "")))
                 (fun x : void =>
                    match
                      x
                      return
                      (itree (ExternalCallE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                         (MMEP.MMSP.MemState * (store_id * (local_env * Stack.stack * res_L1))))
                    with
                    end)) with
              (observe (Vis (subevent void (ThrowOOM (print_msg "")))
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
          change (VisF (subevent void (ThrowOOM u)) k) with (observe (Vis (subevent void (ThrowOOM u)) k)).
          econstructor; eauto.
          reflexivity.
      - reflexivity.
    }

    destruct INTERP as (?&?&?); do 4 red in H.

    epose proof allocate_dtyp_spec_can_always_succeed m m
     (mkMemState (ms_memory_stack m) (InfiniteAddresses.InfPROV.next_provenance (ms_provenance m)))
     (DTYPE_I 64) 1 _ _ _ _ _ as (ms_final & addr & ALLOC).
    pose proof MemMonad_valid_state_exists ms_final as (sid_final&VALID_FINAL).
    Unshelve. 6 : intro H0; inv H0.
    2 : exact (PROV.next_provenance (ms_provenance m)). 2,3 : shelve.
    2 : shelve.

    repeat red in ALLOC.
    eexists (Ret5 genv ((FMapAList.alist_add (Name "ptr") (UVALUE_Addr addr) lenv), stack) sid ms_final _).
    split; cycle 1.
    { do 2 red.
      eapply interp_prop_oom_l_eutt_Proper; try typeclasses eauto.
      rewrite H; reflexivity.
      reflexivity.

      pstep; econstructor; eauto;
        repeat red; repeat econstructor; eauto. }

    clear H.

    eexists (Ret5 genv (_, stack) sid ms_final _).
    split; cycle 1.
    { eapply model_undef_h_ret_pure; typeclasses eauto. }

    rewrite alloc_tree_simpl.

    apply L3_trace_MemoryE.
    eapply (interp_memory_prop_vis _ _ _ _ _ _ (Ret _) _ (fun _ => Ret _))
      ; [ setoid_rewrite bind_ret_l; reflexivity |..].

    { cbn. unfold my_handle_memory_prop.
      unfold MemPropT_lift_PropT_fresh.
      right; right; right.
      exists sid_final, ms_final, (DVALUE_Addr addr).
      split.
      apply VALID.
      Unshelve.
      5 : exact (ms_final, (sid_final, DVALUE_Addr addr)).
      split; [ red; reflexivity |].
      2: exact sid.
      cbn in *.
      split.
      exists ms_final, addr. tauto.
      auto.

      - cbn.
        split.
        { red.
          intros USED.
          apply VALID in USED.
          apply N.lt_irrefl in USED; auto.
        }
        repeat (split; try reflexivity).
      - cbn.
        split; [|split; [|split; [|split; [|split; [|split]]]]]; try solve [red; reflexivity].
        + red.
          split; [|split].
          * intros pr H0.
            red; red in H0.
            cbn.
            unfold mem_state_provenance in *.
            etransitivity.
            apply H0.
            eapply PROV.provenance_lt_next_provenance.
          * intros CONTRA.
            red in CONTRA.
            unfold mem_state_provenance in *.
            apply PROV.provenance_lt_nrefl in CONTRA; auto.
          * red.
            cbn.
            apply PROV.provenance_lt_next_provenance.
        + red.
          split; red; reflexivity.
    }

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
  Qed.

  Example remove_alloc_ptoi_block :
    forall genv lenv stack sid m,
      MMEP.MemExecM.MemMonad_valid_state m sid ->
      refine_L6
        (interp_mcfg4 eq eq (interp_instr_E_to_L0 _ ptoi_tree) genv (lenv, stack) sid m)
        (interp_mcfg4 eq eq (interp_instr_E_to_L0 _ ret_tree) genv (lenv, stack) sid m).
  Proof.
    intros genv lenv stack sid m VALID.
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
        exists (raiseOOM "").
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
              (VisF (subevent void (ThrowOOM (print_msg "")))
                 (fun x : void =>
                    match
                      x
                      return
                      (itree (ExternalCallE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                         (MMEP.MMSP.MemState * (store_id * (local_env * Stack.stack * res_L1))))
                    with
                    end)) with
              (observe (Vis (subevent void (ThrowOOM (print_msg "")))
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
          change (VisF (subevent void (ThrowOOM u)) k) with (observe (Vis (subevent void (ThrowOOM u)) k)).
          econstructor; eauto.
          reflexivity.
      - reflexivity.
    }

    destruct INTERP as (?&?&?); do 4 red in H.

    epose proof allocate_dtyp_spec_can_always_succeed m m
     (mkMemState (ms_memory_stack m) (InfiniteAddresses.InfPROV.next_provenance (ms_provenance m)))
     (DTYPE_I 64) 1 _ _ _ _ _ as (ms_final & addr & ALLOC).
    pose proof MemMonad_valid_state_exists ms_final as (sid_final&VALID_FINAL).
    Unshelve. 6 : intro H0; inv H0.
    2 : exact (PROV.next_provenance (ms_provenance m)). 2,3 : shelve.
    2 : shelve.

    eexists (Ret5 genv (FMapAList.alist_add (Name "i")
     (UVALUE_Conversion Ptrtoint DTYPE_Pointer
        (snd (FMapAList.alist_add (Name "ptr") (UVALUE_Addr addr) lenv, stack, UVALUE_Addr addr))
        DTYPE_IPTR) (FMapAList.alist_add (Name "ptr") (UVALUE_Addr addr) lenv), stack) sid ms_final _).
    split; cycle 1.
    { do 2 red.
      eapply interp_prop_oom_l_eutt_Proper; try typeclasses eauto.
      rewrite H; reflexivity.
      reflexivity.
      pstep; econstructor; eauto;
        repeat red; repeat econstructor; eauto. }

    clear H.

    eexists (Ret5 genv (_, stack) sid ms_final _).
    split; cycle 1.
    { eapply model_undef_h_ret_pure; typeclasses eauto. }

    rewrite ptoi_tree_simpl.

    apply L3_trace_MemoryE.
    eapply (interp_memory_prop_vis _ _ _ _ _ _ (Ret _) _ (fun _ => Ret _))
      ; [ setoid_rewrite bind_ret_l; reflexivity |..].

    { cbn. unfold my_handle_memory_prop.
      unfold MemPropT_lift_PropT_fresh.
      right; right; right.
      exists sid_final, ms_final, (DVALUE_Addr addr).
      split.
      apply VALID.
      Unshelve.
      5 : exact (ms_final, (sid_final, DVALUE_Addr addr)).
      split; [ red; reflexivity |].
      2: exact sid.
      cbn in *.
      split.
      exists ms_final, addr. tauto.
      auto.

      - cbn.
        split.
        { red.
          intros USED.
          apply VALID in USED.
          apply N.lt_irrefl in USED; auto.
        }
        repeat (split; try reflexivity).
      - cbn.
        split; [|split; [|split; [|split; [|split; [|split]]]]]; try solve [red; reflexivity].
        + red.
          split; [|split].
          * intros pr H0.
            red; red in H0.
            cbn.
            unfold mem_state_provenance in *.
            etransitivity.
            apply H0.
            eapply PROV.provenance_lt_next_provenance.
          * intros CONTRA.
            red in CONTRA.
            unfold mem_state_provenance in *.
            apply PROV.provenance_lt_nrefl in CONTRA; auto.
          * red.
            cbn.
            apply PROV.provenance_lt_next_provenance.
        + red.
          split; red; reflexivity.
    }

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
  Qed.

  Lemma interp_memory_spec_vis_inv:
    forall E R X
      (e : (E +' LLVMParamsBigIntptr.Events.IntrinsicE +' LLVMParamsBigIntptr.Events.MemoryE +' LLVMParamsBigIntptr.Events.PickUvalueE +' OOME +' UBE +' DebugE +' FailureE) X)
      k sid m t,
      interp_memory_spec (E:=E) (R2 := R) eq (Vis e k) sid m t ->
      ((exists ta k2 s1 s2 ,
           eutt (MMEP.MemSpec.MemState_eqv × eq) t (a <- ta;; k2 a) /\
             interp_memory_spec_h e s1 s2 ta /\
             (forall (a : X) (b : MMEP.MMSP.MemState * (store_id * X)),
                 @Returns (E +' IntrinsicE +' MemoryE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE) X a (trigger e) ->
                 @Returns (E +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE) (MMEP.MMSP.MemState * (store_id * X)) b ta ->
                 a = snd (snd b) ->
                 interp_memory_spec (E := E) eq (k a) sid m (k2 b))) \/
         (exists ta s1 s2, interp_memory_spec_h e s1 s2 ta /\ contains_UB_Extra ta)%type \/
         (exists A (e : OOME A) k, t ≈ (vis e k)%type)).
  Proof.
    intros.
    punfold H.
    red in H. cbn in H.
    setoid_rewrite (itree_eta t).
    remember (VisF e k).
    genobs t ot.
    clear t Heqot.
    hinduction H before sid; intros; inv Heqi; eauto.
    - specialize (IHinterp_memory_PropTF m eq_refl).
      destruct IHinterp_memory_PropTF as [(?&?&?&?&?&?&?) | [(?&?&?&?) | (?&?&?&?)]].
      3: {
        (* OOM *)
        right.
        right.
        setoid_rewrite tau_eutt.
        rewrite <- itree_eta in H1.
        setoid_rewrite H1.
        exists x. exists x0. exists x1.
        reflexivity.
      }

      2: {
        (* UB *)
        right. left.
        exists x. exists x0. exists x1.
        auto.
      }

      left.
      eexists _,_,_,_; split; eauto. rewrite tau_eutt.
      rewrite <- itree_eta in H1. eauto.
    - setoid_rewrite <- itree_eta.
      setoid_rewrite HT1.
      right. right.
      exists A. exists e0. exists k0.
      reflexivity.
    - dependent destruction H1.
      red in KS; cbn in KS.
      destruct KS as [KS_UB | KS].
      { (* Interpretation of e contains UB *)
        right; left.
        exists ta. exists s1. exists s2.
        auto.
      }

      (* Interpretation of e does not contain UB *)
      left.
      eexists _,_,_,_; split; eauto.
      + rewrite <- itree_eta; eauto.

      + split; eauto.
        intros. do 3 red.
        specialize (HK a b H H0 H1). pclearbot; auto.
  Qed.

  Lemma refine_OOM_h_model_undef_h_raise_OOM:
    forall R t1 oom_msg (k1 : R -> _) t3,
      refine_OOM_h (E := L4) refine_res3 t1 (raiseOOM oom_msg) ->
      model_undef_h (prod_rel MemoryBigIntptr.MMEP.MemSpec.MemState_eqv eq) (x <- Error.raise_oom oom_msg;; k1 x) t3 ->
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
    remember (VisF (subevent void (ThrowOOM (print_msg oom_msg)))
            (fun x : void =>
             ITree.bind match x return (itree _ R) with
                        end (fun x0 : R => k1 x0))).
    remember (VisF (subevent void (ThrowOOM (print_msg oom_msg)))
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
      specialize (IHinterp_prop_oomTF eq_refl H eq_refl). punfold IHinterp_prop_oomTF.
    - inv CHECK.
    - pstep; red; cbn; eauto.
    - dependent destruction H2.
      cbn in HSPEC. red in HSPEC.
      red in KS.
      rewrite HSPEC in KS.
      destruct KS as [UB | KS].
      { exfalso.
        clear - UB.
        setoid_rewrite bind_trigger in UB.
        dependent induction UB.
        - pinversion H; subst; cbn in *.
          inv CHECK.
        - pinversion H; repeat subst_existT.
          setoid_rewrite resum_to_subevent in H5.
          rewrite subevent_subevent in H5.
          destruct e.
          inv H5.
          destruct s; inv H5.
          destruct x.
        - pinversion H; repeat subst_existT.
          setoid_rewrite resum_to_subevent in H4.
          repeat rewrite subevent_subevent in H4.
          inv H4.
      }

      setoid_rewrite bind_bind in KS.
      setoid_rewrite bind_trigger in KS.
      eapply interp_prop_oom_l_eutt_Proper; try typeclasses eauto.
      rewrite <- itree_eta, KS. reflexivity.
      reflexivity.
      pstep. eapply Interp_Prop_OomT_Vis_OOM_L; auto.
      eapply eqit_Vis. intros; inv u.
      Unshelve. intros. inv H0.
  Qed.

  Lemma refine_OOM_h_model_undef_h_raise_ret:
    forall t1 t3 r,
      refine_OOM_h (E := L4) refine_res3 t1 (ret r) ->
      model_undef_h (prod_rel MemoryBigIntptr.MMEP.MemSpec.MemState_eqv eq) (ret r) t3 ->
      refine_OOM_h (E := L4) refine_res3 t1 t3.
  Proof.
    intros.
    eapply interp_prop_oom_ret_inv in H0.
    rewrite H.
    destruct H0 as [(?&?&?) | OOM_CASE].
    2: {
      red.
      red.
      destruct OOM_CASE as (?&?&?&?).
      eapply interp_prop_oom_l_eutt_Proper; try typeclasses eauto.
      rewrite H0. reflexivity.
      reflexivity.
      pstep; red; cbn.
      observe_vis.
      eapply Interp_Prop_OomT_Vis_OOM_L; eauto.
      reflexivity.
    }

    subst. rewrite H1.
    red in H.
    inv H0.
    destruct r, x.
    cbn in *; subst.
    pstep; constructor; auto.
    red.
    repeat constructor; cbn; auto.
  Qed.

  (* Add allocation in infinite language *)
  Example add_alloc :
    forall genv lenv stack sid m,
      MemoryBigIntptr.MMEP.MemExecM.MemMonad_valid_state m sid ->
      refine_L6 (interp_mcfg4 eq (prod_rel MemoryBigIntptr.MMEP.MemSpec.MemState_eqv eq) (interp_instr_E_to_L0 _ ret_tree) genv (lenv, stack) sid m)
                (interp_mcfg4 eq (prod_rel MemoryBigIntptr.MMEP.MemSpec.MemState_eqv eq) (interp_instr_E_to_L0 _ alloc_tree) genv (lenv, stack) sid m).
  Proof.
    intros genv lenv stack sid m VALID.
    unfold refine_L6.
    intros t' INTERP.

    unfold ret_tree, denote_program in INTERP.
    destruct INTERP as (?&?&?).
    rewrite alloc_tree_simpl in H.
    apply L3_trace_MemoryE in H.

    (* Given `H`, what can `x` be? *)
    apply interp_memory_spec_vis_inv in H.
    destruct H as [(alloc_t&k1&s1&ms1&EQ1&SPEC1&HK) | [(ta&s1&s2&INTERP&UB) | (A&e&k&EUTT)]].
    3: { (* OOM *)
      exists t'.
      split.
      - unfold interp_mcfg4.
        red.
        destruct e.
        exists (raiseOOM "").
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
              (VisF (subevent void (ThrowOOM (print_msg "")))
                 (fun x : void =>
                    match
                      x
                      return
                      (itree (ExternalCallE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                         (MMEP.MMSP.MemState * (store_id * (local_env * Stack.stack * res_L1))))
                    with
                    end)) with
              (observe (Vis (subevent void (ThrowOOM (print_msg "")))
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
        + rewrite EUTT in H0.
          red in H0.
          punfold H0; red in H0; cbn in H0.
          dependent induction H0.
          { setoid_rewrite (itree_eta t').
            setoid_rewrite <- x.
            setoid_rewrite tau_eutt.
            eapply IHinterp_prop_oomTF; eauto.
          }

          { setoid_rewrite (itree_eta t').
            setoid_rewrite <- x.
            rewrite HT1.
            cbn.
            destruct e.
            pstep; red; cbn.
            observe_vis_r.
            eapply Interp_Prop_OomT_Vis_OOM_R; eauto.
            reflexivity.
          }

          cbn in HSPEC; red in HSPEC.
          setoid_rewrite bind_ret_r in HSPEC.
          red in KS.
          setoid_rewrite HSPEC in KS.

          destruct KS as [UB | KS].
          { exfalso.
            clear - UB.
            dependent induction UB.
            - pinversion H; subst; cbn in *.
              inv CHECK.
            - pinversion H; repeat subst_existT.
              setoid_rewrite resum_to_subevent in H5.
              rewrite subevent_subevent in H5.
              destruct e.
              inv H5.
              destruct s; inv H5.
              destruct x.
            - pinversion H; repeat subst_existT.
              setoid_rewrite resum_to_subevent in H4.
              repeat rewrite subevent_subevent in H4.
              inv H4.
          }

          setoid_rewrite bind_trigger in KS.
          rewrite (itree_eta t').
          setoid_rewrite <- x.
          rewrite <- itree_eta.
          rewrite KS.
          pstep; red; cbn.
          change
            (@VisF (ExternalCallE +' OOME +' UBE +' DebugE +' FailureE)
               (MMEP.MMSP.MemState * (store_id * (local_env * @Stack.stack local_env * res_L1)))
               (itree (ExternalCallE +' OOME +' UBE +' DebugE +' FailureE)
                  (MMEP.MMSP.MemState * (store_id * (local_env * @Stack.stack local_env * res_L1)))) void
               (@subevent (OOME +' UBE +' DebugE +' FailureE)
                  (ExternalCallE +' OOME +' UBE +' DebugE +' FailureE)
                  (@ReSum_inr (Type -> Type) IFun sum1 Cat_IFun Inr_sum1 (OOME +' UBE +' DebugE +' FailureE)
                     (OOME +' UBE +' DebugE +' FailureE) ExternalCallE
                     (@ReSum_id (Type -> Type) IFun Id_IFun (OOME +' UBE +' DebugE +' FailureE))) void
                  (@resum (Type -> Type) IFun OOME (OOME +' UBE +' DebugE +' FailureE)
                     (@ReSum_inl (Type -> Type) IFun sum1 Cat_IFun Inl_sum1 OOME OOME
                        (UBE +' DebugE +' FailureE) (@ReSum_id (Type -> Type) IFun Id_IFun OOME)) void
                     (ThrowOOM u))) (fun x1 : void => k2 x1)) with
            (observe (Vis
               (@subevent (OOME +' UBE +' DebugE +' FailureE)
                  (ExternalCallE +' OOME +' UBE +' DebugE +' FailureE)
                  (@ReSum_inr (Type -> Type) IFun sum1 Cat_IFun Inr_sum1 (OOME +' UBE +' DebugE +' FailureE)
                     (OOME +' UBE +' DebugE +' FailureE) ExternalCallE
                     (@ReSum_id (Type -> Type) IFun Id_IFun (OOME +' UBE +' DebugE +' FailureE))) void
                  (@resum (Type -> Type) IFun OOME (OOME +' UBE +' DebugE +' FailureE)
                     (@ReSum_inl (Type -> Type) IFun sum1 Cat_IFun Inl_sum1 OOME OOME
                        (UBE +' DebugE +' FailureE) (@ReSum_id (Type -> Type) IFun Id_IFun OOME)) void
                     (ThrowOOM u))) (fun x1 : void => k2 x1))).
          eapply Interp_Prop_OomT_Vis.
          * intros [] _.
          * cbn. red.
            setoid_rewrite bind_ret_r.
            reflexivity.
          * red.
            setoid_rewrite bind_trigger.
            unfold print_msg. destruct u.
            right.
            reflexivity.
      - reflexivity.
    }

    2: { (* UB *)
      exfalso.

      pose proof allocate_dtyp_spec_inv s2 (DTYPE_I 64) as ALLOCINV.
      assert (abs : DTYPE_I 64 <> DTYPE_Void) by (intros abs; inv abs).
      specialize (ALLOCINV 1%N abs); eauto; clear abs.

      destruct INTERP as [ALLOC_UB | [ALLOC_ERR | [ALLOC_OOM | ALLOC_SUC]]].
      { (* UB *)
        destruct ALLOC_UB as [ub_msg [ALLOC_UB | [sab [a [ALLOC_UB []]]]]].
        specialize (ALLOCINV _ ALLOC_UB).
        destruct ALLOCINV as [[ms_final [ptr ALLOC_INV]] | [oom_msg ALLOC_INV]];
          inv ALLOC_INV.
      }
      { (* ERR *)
        destruct ALLOC_ERR as [err_msg [MAP [spec_msg [ALLOC_ERR | [sab [a [ALLOC_ERR []]]]]]]].
        apply ALLOCINV in ALLOC_ERR.
        destruct ALLOC_ERR as [[ms_final [ptr ALLOC_ERR]] | [oom_msg ALLOC_ERR]];
          inv ALLOC_ERR.
      }
      { (* OOM *)
        destruct ALLOC_OOM as [err_msg [MAP [spec_msg [ALLOC_OOM | [sab [a [ALLOC_OOM []]]]]]]].
        apply ALLOCINV in ALLOC_OOM. clear ALLOCINV.
        destruct ALLOC_OOM as [[ms_final [ptr ALLOC_OOM]] | [oom_msg ALLOC_OOM]];
          inv ALLOC_OOM.

        rewrite MAP in UB.
        cbn in UB.

        eapply contains_UB_Extra_raiseOOM in UB; eauto.
        intros X e1 e2.
        repeat unfold resum, ReSum_id, id_, Id_IFun, ReSum_inr, ReSum_inl, inr_, inl_, cat, Cat_IFun, Inr_sum1, Inl_sum1.
        intros CONTRA; discriminate.
      }

      destruct ALLOC_SUC as (?&?&?&?&?&?&?); auto.
      rewrite H1 in UB.
      eapply ret_not_contains_UB_Extra in UB; eauto.
      reflexivity.
    }

    (* Why can't this just be a rewrite? *)
    eapply interp_prop_oom_Proper_eq in H0; try typeclasses eauto; eauto.
    2: symmetry; apply EQ1.
    clear x EQ1.

    pose proof allocate_dtyp_spec_inv ms1 (DTYPE_I 64) as ALLOCINV.
    assert (abs : DTYPE_I 64 <> DTYPE_Void) by (intros abs; inv abs).
    specialize (ALLOCINV 1%N abs); eauto; clear abs.

    repeat red in SPEC1.
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
      exists (Ret5 genv (lenv, stack) sid m (DVALUE_I1 Int1.one)).
      split; cycle 1.
      { clear - H0.
        eapply refine_OOM_h_model_undef_h_raise_OOM; eauto.
        eapply refine_oom_h_raise_oom; typeclasses eauto. }
      { unfold interp_instr_E_to_L0. unfold ret_tree. cbn.
        force_go. cbn. force_go.
        apply interp_mcfg4_ret. } }

    clear ALLOCINV.
    exists (Ret5 genv (lenv, stack) sid m (DVALUE_I1 Int1.one)).
    destruct ALLOC_SUC as (?&?&?&?&?&?&?).
    rewrite H1 in H0; setoid_rewrite bind_ret_l in H0.
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
    { rewrite H1; apply ReturnsRet; reflexivity. }

    specialize (HK _ _ (alloca_returns x1) alloc_t_returns eq_refl).
    clear alloca_returns alloc_t_returns.

    eapply L3_trace_LocalWrite in HK.
    eapply L3_trace_ret in HK.
    apply interp_memory_prop_ret_inv in HK.
    destruct HK as [(?&?&?) | OOM].
    2: {
      destruct OOM as (A&e&k&EUTT).
      do 3 red.

      rewrite EUTT in H0.
      red in H0.
      punfold H0; red in H0; cbn in H0.
      dependent induction H0.
      { setoid_rewrite (itree_eta t').
        eapply interp_prop_oom_Proper_eq; try typeclasses eauto; auto.
        setoid_rewrite <- x.
        rewrite tau_eutt; reflexivity.
        eapply IHinterp_prop_oomTF; eauto.
      }

      { setoid_rewrite (itree_eta t').
        eapply interp_prop_oom_Proper_eq; try typeclasses eauto; auto.
        setoid_rewrite <- x.
        rewrite HT1.
        cbn.
        reflexivity.
        destruct e.
        pstep; red; cbn.
        observe_vis.
        eapply Interp_Prop_OomT_Vis_OOM_L; eauto.
        reflexivity.
      }

      cbn in HSPEC; red in HSPEC.
      setoid_rewrite bind_ret_r in HSPEC.
      red in KS.
      setoid_rewrite HSPEC in KS.
      destruct KS as [UB | KS].
      { exfalso.
        clear - UB.
        dependent induction UB.
        - pinversion H; subst; cbn in *.
          inv CHECK.
        - pinversion H; repeat subst_existT.
          setoid_rewrite resum_to_subevent in H5.
          rewrite subevent_subevent in H5.
          destruct e.
          destruct e0; inv H5.
          destruct x.
        - pinversion H; repeat subst_existT.
          setoid_rewrite resum_to_subevent in H5.
          repeat rewrite subevent_subevent in H5.
          inv H5.
      }

      setoid_rewrite bind_trigger in KS.
      rewrite (itree_eta t').
      eapply interp_prop_oom_Proper_eq; try typeclasses eauto; auto.
      setoid_rewrite <- x.
      rewrite <- itree_eta.
      rewrite KS.
      reflexivity.

      pstep; red; cbn.
      rewrite itree_eta'.
      observe_vis.
      eapply Interp_Prop_OomT_Vis_OOM_L
        with (e:=(resum IFun A e))
             (k1:=(fun x3 : A => k2 x3));
        auto.
      reflexivity.
    }
    destruct x2 as (?&?&?&?&?).
    rewrite H5 in H0.

    inv H2.
    eapply refine_OOM_h_model_undef_h_raise_ret; eauto.
    pstep; repeat constructor; auto.
    cbn.
    inv H4.
    auto.
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
      Proper (eutt eq ==> eq ==> eq ==> eq ==> iff) (@interp_memory_spec E R R RR).
  Proof.
    intros E R RR.
    unfold interp_memory_spec.
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
                     (fun _ => Ret (DVALUE_I1 Int1.one))).
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
      model_undef_h (prod_rel Memory64BitIntptr.MMEP.MemSpec.MemState_eqv eq) (x <- Error.raise_oom oom_msg;; k1 x) t3 ->
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
    remember (VisF (subevent void (ThrowOOM (print_msg oom_msg)))
            (fun x : void =>
             ITree.bind match x return (itree _ R) with
                        end (fun x0 : R => k1 x0))).
    remember (VisF (subevent void (ThrowOOM (print_msg oom_msg)))
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
      specialize (IHinterp_prop_oomTF eq_refl H eq_refl). punfold IHinterp_prop_oomTF.
    - inv CHECK.
    - pstep; red; cbn; eauto.
    - dependent destruction H2.
      cbn in HSPEC. red in HSPEC.
      red in KS.
      rewrite HSPEC in KS.
      destruct KS as [UB | KS].
      { exfalso.
        clear - UB.
        setoid_rewrite bind_trigger in UB.
        dependent induction UB.
        - pinversion H; subst; cbn in *.
          inv CHECK.
        - pinversion H; repeat subst_existT.
          setoid_rewrite resum_to_subevent in H5.
          rewrite subevent_subevent in H5.
          destruct e.
          inv H5.
          destruct s; inv H5.
          destruct x.
        - pinversion H; repeat subst_existT.
          setoid_rewrite resum_to_subevent in H4.
          repeat rewrite subevent_subevent in H4.
          inv H4.
      }

      setoid_rewrite bind_bind in KS.
      setoid_rewrite bind_trigger in KS.
      eapply interp_prop_oom_l_eutt_Proper; try typeclasses eauto.
      rewrite <- itree_eta, KS. reflexivity.
      reflexivity.
      pstep. eapply Interp_Prop_OomT_Vis_OOM_L; auto.
      eapply eqit_Vis. intros; inv u.
      Unshelve. intros. inv H0.
  Qed.

  Lemma refine_OOM_h_model_undef_h_raise_ret:
    forall t1 t3 r,
      refine_OOM_h (E := L4) refine_res3 t1 (ret r) ->
      model_undef_h (prod_rel Memory64BitIntptr.MMEP.MemSpec.MemState_eqv eq) (ret r) t3 ->
      refine_OOM_h (E := L4) refine_res3 t1 t3.
  Proof.
    intros.
    eapply interp_prop_oom_ret_inv in H0.
    rewrite H.
    destruct H0 as [(?&?&?) | OOM_CASE].
    2: {
      red.
      red.
      destruct OOM_CASE as (?&?&?&?).
      eapply interp_prop_oom_l_eutt_Proper; try typeclasses eauto.
      rewrite H0. reflexivity.
      reflexivity.
      pstep; red; cbn.
      observe_vis.
      eapply Interp_Prop_OomT_Vis_OOM_L; eauto.
      reflexivity.
    }

    subst. rewrite H1.
    red in H.
    inv H0.
    destruct r, x.
    cbn in *; subst.
    pstep; constructor; auto.
    red.
    repeat constructor; cbn; auto.
  Qed.

  (* Few remarks about [L3_trace] used in [interp_mcfg4] *)
  Remark L3_trace_MemoryE:
    forall R X g l sid m (e : MemoryE X) (k : X -> itree L0 R) t,
      interp_memory_spec eq
            (vis e (fun x : X => interp_local_stack (interp_global (interp_intrinsics (k x)) g) l)) sid m t <->
      interp_memory_spec eq (interp_local_stack (interp_global (interp_intrinsics (vis e k)) g) l) sid m t.
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
      interp_memory_spec eq
        (interp_local_stack (interp_global (interp_intrinsics (k tt)) g) (FMapAList.alist_add id dv l, s)) sid m t <->
      interp_memory_spec eq (interp_local_stack (interp_global (interp_intrinsics (vis (LocalWrite id dv) k)) g) (l, s)) sid m t.
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
      (interp_memory_spec eq (interp_local_stack (interp_global (interp_intrinsics (k (snd (l, s, x)))) g) (fst (l, s, x)))
        sid m t <->
      interp_memory_spec eq (interp_local_stack (interp_global (interp_intrinsics (vis (LocalRead id) k)) g) (l, s)) sid m t).
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
      interp_memory_spec eq (Ret2 g l r) sid m t <->
      interp_memory_spec eq (interp_local_stack (interp_global (interp_intrinsics (ret r)) g) l) sid m t.
  Proof.
    intros.
    setoid_rewrite interp_intrinsics_ret.
    setoid_rewrite interp_global_ret.
    setoid_rewrite interp_local_stack_ret. reflexivity.
  Qed.

  Lemma interp_memory_spec_vis_inv:
    forall E R X
      (e : (E +' LLVMParams64BitIntptr.Events.IntrinsicE +' LLVMParams64BitIntptr.Events.MemoryE +' LLVMParams64BitIntptr.Events.PickUvalueE +' OOME +' UBE +' DebugE +' FailureE) X)
      k sid m t,
      interp_memory_spec (E:=E) (R2 := R) eq (Vis e k) sid m t ->
      ((exists ta k2 s1 s2 ,
           eutt (MMEP.MemSpec.MemState_eqv × eq) t (a <- ta;; k2 a) /\
             interp_memory_spec_h e s1 s2 ta /\
             (forall (a : X) (b : MMEP.MMSP.MemState * (store_id * X)),
                 @Returns (E +' IntrinsicE +' MemoryE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE) X a (trigger e) ->
                 @Returns (E +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE) (MMEP.MMSP.MemState * (store_id * X)) b ta ->
                 a = snd (snd b) ->
                 interp_memory_spec (E := E) eq (k a) sid m (k2 b))) \/
         (exists ta s1 s2, interp_memory_spec_h e s1 s2 ta /\ contains_UB_Extra ta)%type \/
         (exists A (e : OOME A) k, t ≈ (vis e k)%type)).
  Proof.
    intros.
    punfold H.
    red in H. cbn in H.
    setoid_rewrite (itree_eta t).
    remember (VisF e k).
    genobs t ot.
    clear t Heqot.
    hinduction H before sid; intros; inv Heqi; eauto.
    - specialize (IHinterp_memory_PropTF m eq_refl).
      destruct IHinterp_memory_PropTF as [(?&?&?&?&?&?&?) | [(?&?&?&?) | (?&?&?&?)]].
      3: {
        (* OOM *)
        right.
        right.
        setoid_rewrite tau_eutt.
        rewrite <- itree_eta in H1.
        setoid_rewrite H1.
        exists x. exists x0. exists x1.
        reflexivity.
      }

      2: {
        (* UB *)
        right. left.
        exists x. exists x0. exists x1.
        auto.
      }

      left.
      eexists _,_,_,_; split; eauto. rewrite tau_eutt.
      rewrite <- itree_eta in H1. eauto.
    - setoid_rewrite <- itree_eta.
      setoid_rewrite HT1.
      right. right.
      exists A. exists e0. exists k0.
      reflexivity.
    - dependent destruction H1.
      red in KS; cbn in KS.
      destruct KS as [KS_UB | KS].
      { (* Interpretation of e contains UB *)
        right; left.
        exists ta. exists s1. exists s2.
        auto.
      }

      (* Interpretation of e does not contain UB *)
      left.
      eexists _,_,_,_; split; eauto.
      + rewrite <- itree_eta; eauto.

      + split; eauto.
        intros. do 3 red.
        specialize (HK a b H H0 H1). pclearbot; auto.
  Qed.

  Lemma model_undef_h_ret_pure :
    forall {E F : Type -> Type}
      `{FAIL : FailureE -< E +' F}
      `{UB : UBE -< E +' F}
      `{OOM : OOME -< F}
      {X} (x : X)
      (RR : relation X) `{REF : Reflexive X RR},
      model_undef_h RR (ret x) (ret x).
  Proof.
    intros E F FAIL UB OOM X x RR REF.
    unfold model_undef_h.
    apply interp_prop_oom_ret_pure; auto.
  Qed.

  Lemma model_undef_h_ret_inv :
    forall {E F : Type -> Type}
      `{FAIL : FailureE -< E +' F}
      `{UB : UBE -< E +' F}
      `{OOMF : OOME -< F}
      {X} (x : X) (t : itree (E +' F) X),
      model_undef_h eq (ret x) t ->
      t ≈ Ret x \/ (exists (A : Type) (e : OOME A) (k : A -> itree (E +' F) X), t ≈ vis e k).
  Proof.
    intros E F FAIL UB OOM X x t UNDEF.
    unfold model_undef_h in *.
    eapply interp_prop_oom_ret_inv in UNDEF.
    destruct UNDEF as [[r2 [EQ T']] | OOM_CASE]; subst; eauto.
  Qed.

  Lemma interp_mcfg4_ret :
    forall R g l sid m (r : R),
      ℑs4 eq (Memory64BitIntptr.MMEP.MemSpec.MemState_eqv × eq) (ret r) g l sid m (Ret5 g l sid m r).
  Proof.
    intros.
    unfold interp_mcfg4, model_undef.
    setoid_rewrite interp_intrinsics_ret.
    setoid_rewrite interp_global_ret.
    unfold interp_local_stack.
    setoid_rewrite interp_state_ret.
    unfold interp_memory_spec.
    cbn.
    eexists (ret _).
    split.
    pstep; econstructor; eauto.
    2 : eapply model_undef_h_ret_pure; eauto.
    cbn. reflexivity.
    typeclasses eauto.
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
    unfold interp_memory_spec in H.
    apply interp_memory_prop_ret_inv in H.
    destruct H as [(?&?&?) | (A&e&k&?)].
    { destruct x1 as (?&?&?).
      rewrite H1 in H0.
      apply interp_prop_oom_ret_inv in H0.
      destruct H0 as [(?&?&?) | OOM_CASE]; subst; eauto.
      cbn. left. exists m0, s. rewrite H2.
      cbn.
      reflexivity.
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
      eapply IHinterp_prop_oomTF; eauto.
    - cbn.
      setoid_rewrite <- itree_eta.
      setoid_rewrite HT1.
      exists A0. exists e0. exists k2.
      reflexivity.
    - red in HSPEC; cbn in HSPEC; red in HSPEC.
      setoid_rewrite bind_ret_r in HSPEC.
      red in KS.
      rewrite HSPEC in KS.
      destruct KS as [UB | KS].
      { exfalso.
        destruct e.
        clear - UB.
        dependent induction UB.
        - pinversion H; subst; cbn in *.
          inv CHECK.
        - pinversion H; repeat subst_existT.
          setoid_rewrite resum_to_subevent in H5.
          rewrite subevent_subevent in H5.
          destruct e.
          inv H5.
          destruct s; inv H5.
          destruct x.
        - pinversion H; repeat subst_existT.
          setoid_rewrite resum_to_subevent in H4.
          repeat rewrite subevent_subevent in H4.
          inv H4.
      }

      setoid_rewrite bind_trigger in KS.

      punfold KS; red in KS; cbn in KS.
      dependent induction KS.
      + rewrite <- x.
        cbn.
        exists A. exists (resum IFun A e). exists k1.
        reflexivity.
      + rewrite <- x.
        cbn.
        setoid_rewrite tau_eutt.
        setoid_rewrite itree_eta.
        eapply IHKS; eauto.
  Qed.

  (* Add allocation in the finite language *)
  Example add_alloc :
    forall genv lenv stack sid m,
      refine_L6 (interp_mcfg4 eq (prod_rel Memory64BitIntptr.MMEP.MemSpec.MemState_eqv eq) (interp_instr_E_to_L0 _ ret_tree) genv (lenv, stack) sid m)
                (interp_mcfg4 eq (prod_rel Memory64BitIntptr.MMEP.MemSpec.MemState_eqv eq) (interp_instr_E_to_L0 _ alloc_tree) genv (lenv, stack) sid m).
  Proof.
    intros genv lenv stack sid m.
    unfold refine_L6.
    intros t' INTERP.

    unfold ret_tree, denote_program in INTERP.
    destruct INTERP as (?&?&?).
    rewrite alloc_tree_simpl in H.
    apply L3_trace_MemoryE in H.

    (* Given `H`, what can `x` be? *)
    apply interp_memory_spec_vis_inv in H.
    destruct H as [(alloc_t&k1&s1&ms1&EQ1&SPEC1&HK) | [(ta&s1&s2&INTERP&UB) | (A&e&k&EUTT)]].
    3: { (* OOM *)
      exists t'.
      split.
      - unfold interp_mcfg4.
        red.
        destruct e.
        exists (raiseOOM "").
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
              (VisF (subevent void (ThrowOOM (print_msg "")))
                 (fun x : void =>
                    match
                      x
                      return
                      (itree (ExternalCallE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                         (MMEP.MMSP.MemState * (store_id * (local_env * Stack.stack * res_L1))))
                    with
                    end)) with
              (observe (Vis (subevent void (ThrowOOM (print_msg "")))
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
        + rewrite EUTT in H0.
          red in H0.
          punfold H0; red in H0; cbn in H0.
          dependent induction H0.
          { setoid_rewrite (itree_eta t').
            setoid_rewrite <- x.
            setoid_rewrite tau_eutt.
            eapply IHinterp_prop_oomTF; eauto.
          }

          { setoid_rewrite (itree_eta t').
            setoid_rewrite <- x.
            rewrite HT1.
            cbn.
            destruct e.
            pstep; red; cbn.
            observe_vis_r.
            eapply Interp_Prop_OomT_Vis_OOM_R; eauto.
            reflexivity.
          }

          cbn in HSPEC; red in HSPEC.
          setoid_rewrite bind_ret_r in HSPEC.
          red in KS.
          setoid_rewrite HSPEC in KS.

          destruct KS as [UB | KS].
          { exfalso.
            clear - UB.
            dependent induction UB.
            - pinversion H; subst; cbn in *.
              inv CHECK.
            - pinversion H; repeat subst_existT.
              setoid_rewrite resum_to_subevent in H5.
              rewrite subevent_subevent in H5.
              destruct e.
              inv H5.
              destruct s; inv H5.
              destruct x.
            - pinversion H; repeat subst_existT.
              setoid_rewrite resum_to_subevent in H4.
              repeat rewrite subevent_subevent in H4.
              inv H4.
          }

          setoid_rewrite bind_trigger in KS.
          rewrite (itree_eta t').
          setoid_rewrite <- x.
          rewrite <- itree_eta.
          rewrite KS.
          pstep; red; cbn.
          change
            (@VisF (ExternalCallE +' OOME +' UBE +' DebugE +' FailureE)
               (MMEP.MMSP.MemState * (store_id * (local_env * @Stack.stack local_env * res_L1)))
               (itree (ExternalCallE +' OOME +' UBE +' DebugE +' FailureE)
                  (MMEP.MMSP.MemState * (store_id * (local_env * @Stack.stack local_env * res_L1)))) void
               (@subevent (OOME +' UBE +' DebugE +' FailureE)
                  (ExternalCallE +' OOME +' UBE +' DebugE +' FailureE)
                  (@ReSum_inr (Type -> Type) IFun sum1 Cat_IFun Inr_sum1 (OOME +' UBE +' DebugE +' FailureE)
                     (OOME +' UBE +' DebugE +' FailureE) ExternalCallE
                     (@ReSum_id (Type -> Type) IFun Id_IFun (OOME +' UBE +' DebugE +' FailureE))) void
                  (@resum (Type -> Type) IFun OOME (OOME +' UBE +' DebugE +' FailureE)
                     (@ReSum_inl (Type -> Type) IFun sum1 Cat_IFun Inl_sum1 OOME OOME
                        (UBE +' DebugE +' FailureE) (@ReSum_id (Type -> Type) IFun Id_IFun OOME)) void
                     (ThrowOOM u))) (fun x1 : void => k2 x1)) with
            (observe (Vis
               (@subevent (OOME +' UBE +' DebugE +' FailureE)
                  (ExternalCallE +' OOME +' UBE +' DebugE +' FailureE)
                  (@ReSum_inr (Type -> Type) IFun sum1 Cat_IFun Inr_sum1 (OOME +' UBE +' DebugE +' FailureE)
                     (OOME +' UBE +' DebugE +' FailureE) ExternalCallE
                     (@ReSum_id (Type -> Type) IFun Id_IFun (OOME +' UBE +' DebugE +' FailureE))) void
                  (@resum (Type -> Type) IFun OOME (OOME +' UBE +' DebugE +' FailureE)
                     (@ReSum_inl (Type -> Type) IFun sum1 Cat_IFun Inl_sum1 OOME OOME
                        (UBE +' DebugE +' FailureE) (@ReSum_id (Type -> Type) IFun Id_IFun OOME)) void
                     (ThrowOOM u))) (fun x1 : void => k2 x1))).
          eapply Interp_Prop_OomT_Vis.
          * intros [] _.
          * cbn. red.
            setoid_rewrite bind_ret_r.
            reflexivity.
          * red.
            setoid_rewrite bind_trigger.
            unfold print_msg. destruct u.
            right.
            reflexivity.
      - reflexivity.
    }

    2: { (* UB *)
      exfalso.

      pose proof allocate_dtyp_spec_inv s2 (DTYPE_I 64) as ALLOCINV.
      assert (abs : DTYPE_I 64 <> DTYPE_Void) by (intros abs; inv abs).
      specialize (ALLOCINV 1%N abs); eauto; clear abs.

      repeat red in INTERP.
      destruct INTERP as [ALLOC_UB | [ALLOC_ERR | [ALLOC_OOM | ALLOC_SUC]]].
      { (* UB *)
        destruct ALLOC_UB as [ub_msg [ALLOC_UB | [sab [a [ALLOC_UB []]]]]].
        specialize (ALLOCINV _ ALLOC_UB).
        destruct ALLOCINV as [[ms_final [ptr ALLOC_INV]] | [oom_msg ALLOC_INV]];
          inv ALLOC_INV.
      }
      { (* ERR *)
        destruct ALLOC_ERR as [err_msg [MAP [spec_msg [ALLOC_ERR | [sab [a [ALLOC_ERR []]]]]]]].
        apply ALLOCINV in ALLOC_ERR.
        destruct ALLOC_ERR as [[ms_final [ptr ALLOC_ERR]] | [oom_msg ALLOC_ERR]];
          inv ALLOC_ERR.
      }
      { (* OOM *)
        destruct ALLOC_OOM as [err_msg [MAP [spec_msg [ALLOC_OOM | [sab [a [ALLOC_OOM []]]]]]]].
        apply ALLOCINV in ALLOC_OOM. clear ALLOCINV.
        destruct ALLOC_OOM as [[ms_final [ptr ALLOC_OOM]] | [oom_msg ALLOC_OOM]];
          inv ALLOC_OOM.

        rewrite MAP in UB.
        cbn in UB.

        eapply contains_UB_Extra_raiseOOM in UB; eauto.
        intros X e1 e2.
        repeat unfold resum, ReSum_id, id_, Id_IFun, ReSum_inr, ReSum_inl, inr_, inl_, cat, Cat_IFun, Inr_sum1, Inl_sum1.
        intros CONTRA; discriminate.
      }

      destruct ALLOC_SUC as (?&?&?&?&?&?&?).
      rewrite H1 in UB.
      eapply ret_not_contains_UB_Extra in UB; eauto.
      reflexivity.
    }

    (* Why can't this just be a rewrite? *)
    eapply interp_prop_oom_Proper_eq in H0; try typeclasses eauto; eauto.
    2: symmetry; apply EQ1.
    clear x EQ1.

    pose proof allocate_dtyp_spec_inv ms1 (DTYPE_I 64) as ALLOCINV.
    assert (abs : DTYPE_I 64 <> DTYPE_Void) by (intros abs; inv abs).
    specialize (ALLOCINV 1%N abs); eauto; clear abs.

    repeat red in SPEC1.
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
      exists (Ret5 genv (lenv, stack) sid m (DVALUE_I1 Int1.one)).
      split; cycle 1.
      { clear - H0.
        eapply refine_OOM_h_model_undef_h_raise_OOM; eauto.
        eapply refine_oom_h_raise_oom; typeclasses eauto. }
      { unfold interp_instr_E_to_L0. unfold ret_tree. cbn.
        force_go. cbn. force_go.
        apply interp_mcfg4_ret. } }

    clear ALLOCINV.
    exists (Ret5 genv (lenv, stack) sid m (DVALUE_I1 Int1.one)).
    destruct ALLOC_SUC as (?&?&?&?&?&?&?).
    rewrite H1 in H0; setoid_rewrite bind_ret_l in H0.
    split.
    { unfold interp_instr_E_to_L0. unfold ret_tree. cbn.
      force_go. cbn. force_go.
      apply interp_mcfg4_ret. }

    assert (alloca_returns:
             forall x, Returns
                    (E := ExternalCallE +'
                        LLVMParams64BitIntptr.Events.IntrinsicE +'
                        LLVMParams64BitIntptr.Events.MemoryE +'
                        LLVMParams64BitIntptr.Events.PickUvalueE +'
                        OOME +' UBE +' DebugE +' FailureE)
                                   x (trigger (Alloca (DTYPE_I 64) 1 None))).
    { intros. unfold trigger.
      eapply ReturnsVis; [ reflexivity | ].
      Unshelve. eapply ReturnsRet. reflexivity. }

    assert (alloc_t_returns : Returns (x0, (x, x1)) alloc_t).
    { rewrite H1; apply ReturnsRet; reflexivity. }

    specialize (HK _ _ (alloca_returns x1) alloc_t_returns eq_refl).
    clear alloca_returns alloc_t_returns.

    eapply L3_trace_LocalWrite in HK.
    eapply L3_trace_ret in HK.
    apply interp_memory_prop_ret_inv in HK.
    destruct HK as [(?&?&?) | OOM].
    2: {
      destruct OOM as (A&e&k&EUTT).
      do 3 red.

      rewrite EUTT in H0.
      red in H0.
      punfold H0; red in H0; cbn in H0.
      dependent induction H0.
      { setoid_rewrite (itree_eta t').
        eapply interp_prop_oom_Proper_eq; try typeclasses eauto; auto.
        setoid_rewrite <- x.
        rewrite tau_eutt; reflexivity.
        eapply IHinterp_prop_oomTF; eauto.
      }

      { setoid_rewrite (itree_eta t').
        eapply interp_prop_oom_Proper_eq; try typeclasses eauto; auto.
        setoid_rewrite <- x.
        rewrite HT1.
        cbn.
        reflexivity.
        destruct e.
        pstep; red; cbn.
        observe_vis.
        eapply Interp_Prop_OomT_Vis_OOM_L; eauto.
        reflexivity.
      }

      cbn in HSPEC; red in HSPEC.
      setoid_rewrite bind_ret_r in HSPEC.
      red in KS.
      setoid_rewrite HSPEC in KS.
      destruct KS as [UB | KS].
      { exfalso.
        clear - UB.
        dependent induction UB.
        - pinversion H; subst; cbn in *.
          inv CHECK.
        - pinversion H; repeat subst_existT.
          setoid_rewrite resum_to_subevent in H5.
          rewrite subevent_subevent in H5.
          destruct e.
          destruct e0; inv H5.
          destruct x.
        - pinversion H; repeat subst_existT.
          setoid_rewrite resum_to_subevent in H5.
          repeat rewrite subevent_subevent in H5.
          inv H5.
      }

      setoid_rewrite bind_trigger in KS.
      rewrite (itree_eta t').
      eapply interp_prop_oom_Proper_eq; try typeclasses eauto; auto.
      setoid_rewrite <- x.
      rewrite <- itree_eta.
      rewrite KS.
      reflexivity.

      pstep; red; cbn.
      rewrite itree_eta'.
      observe_vis.
      eapply Interp_Prop_OomT_Vis_OOM_L
        with (e:=(resum IFun A e))
             (k1:=(fun x3 : A => k2 x3));
        auto.
      reflexivity.
    }
    destruct x2 as (?&?&?&?&?).
    rewrite H5 in H0.

    inv H2.
    eapply refine_OOM_h_model_undef_h_raise_ret; eauto.
    pstep; repeat constructor; auto.
    cbn.
    inv H4.
    auto.
  Qed.

End Finite.
