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

  Import TranslateFacts.
  Import StateFacts.

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
                (vis (ThrowOOM oom_msg) (fun x : void => match x return (itree _ R) with
                                                         end))).

    hinduction Hmodel before CIH; cbn; intros; inv Heqi; eauto; [ inv e | ].
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
          trigger (inr1 e0)
      end.

  Definition interp_instr_E_to_L0 :=
    interp (@instr_E_to_L0).

  Definition t_alloc : itree L0 dvalue
    := trigger (Alloca (DTYPE_I 64%N) 1%N None);; ret (DVALUE_I1 one).

  Definition t_ret : itree L0 dvalue
    := ret (DVALUE_I1 one).

  (* Remove allocation in infinite language *)
  Lemma remove_alloc:
    forall genv lenv stack sid m,
      refine_L6 (interp_mcfg4 eq eq t_alloc genv (lenv, stack) sid m) 
                (interp_mcfg4 eq eq t_ret genv (lenv, stack) sid m).
  Proof.
    intros genv lenv stack sid m.
    unfold refine_L6.
    intros t' INTERP.

    Import MMEP.MMSP.
    Import MemoryBigIntptr.MMEP.MMSP.
    epose proof allocate_dtyp_spec_can_always_succeed m m 
     (mkMemState (ms_memory_stack m) (next_provenance (ms_provenance m))) 
     (DTYPE_I 64) 1 _ _ _ _ _ as (ms_final & addr & ALLOC).
     Unshelve. 6 : intro H; inv H.
     2 : exact (ms_provenance m). 2,3 : shelve.
     2 : shelve.

    unfold t_ret in *.
    eapply interp_mcfg4_ret_inv in INTERP.
    exists (Ret5 genv (lenv, stack) sid ms_final (DVALUE_I1 DynamicValues.Int1.one)).
    split; cycle 1.
    - do 2 red. destruct INTERP as (?&?&?). do 4 red in H.
      rewrite H.
      pstep; econstructor; eauto.
      repeat red; repeat econstructor; eauto.
    - clear INTERP. do 2 red.
      exists (Ret5 genv (lenv, stack) sid ms_final (DVALUE_I1 DynamicValues.Int1.one)).

      split; cycle 1.
      + eapply model_undef_h_ret_pure; typeclasses eauto.
      + unfold t_alloc. cbn.
        go.
        rewrite bind_trigger.
        repeat setoid_rewrite bind_ret_l.
        setoid_rewrite interp_local_stack_ret.
        repeat setoid_rewrite bind_ret_l.

        (* LEMMA *)
        unfold interp_memory_prop; cbn.

        Opaque MMEP.MemSpec.allocate_dtyp_spec.

        eapply interp_memory_prop_vis.
        * cbn.
          Unshelve.
          2-4, 7-8:shelve.
          2 : exact (Ret (ms_final, (sid, DVALUE_Addr addr))).
          2 : { intros (m', (sid', dv')). exact (Ret (m', (sid', (lenv, stack, (genv, DVALUE_I1 DynamicValues.Int1.one))))). }
          rewrite bind_ret_l. reflexivity.
        * cbn. unfold my_handle_memory_prop.
          unfold MemPropT_lift_PropT_fresh.
          right; right; right.
          exists sid, ms_final, (DVALUE_Addr addr). split; [ red; reflexivity |]. Unshelve.
          6 : exact m. cbn in *.
          exists ms_final, addr. tauto.
          1-4:shelve.

        * intros. apply Returns_ret_inv in H0.
          destruct b as (?&?&?). inv H0; subst. cbn in *.
          eapply Returns_vis_inversion in H.
          destruct H as (?&?).
          apply Returns_ret_inv in H. subst.
          go. pstep; constructor; auto.

          Unshelve.
          all : eauto.
  (* Remaining proof obligations are related to broken [MemMonad_valid_state] *)
  Admitted.

  Example remove_alloc_block :
    forall genv lenv stack sid m,
      refine_L6 (interp_mcfg4 eq eq (interp_instr_E_to_L0 _ alloc_tree) genv (lenv, stack) sid m)
                (interp_mcfg4 eq eq (interp_instr_E_to_L0 _ ret_tree) genv (lenv, stack) sid m).
  Proof.
  Admitted.

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
    destruct INTERP as (?&?&?); do 4 red in H.

    epose proof allocate_dtyp_spec_can_always_succeed m m
     (mkMemState (ms_memory_stack m) (next_provenance (ms_provenance m)))
     (DTYPE_I 64) 1 _ _ _ _ _ as (ms_final & addr & ALLOC).
    Unshelve. 6 : intro H0; inv H0.
    2 : exact (ms_provenance m). 2,3 : shelve.
    2 : shelve.

    eexists (Ret5 genv (lenv, stack) sid ms_final _).
    split; cycle 1.
    { do 2 red. rewrite H.
      pstep; econstructor; eauto;
        repeat red; repeat econstructor; eauto. }

    clear H.

    eexists (Ret5 genv (lenv, stack) sid ms_final _).
    split; cycle 1.
    { eapply model_undef_h_ret_pure; typeclasses eauto. }

    rewrite ptoi_tree_simpl.
  Admitted.

  (* Add allocation in infinite language *)
  Example add_alloc :
    forall genv lenv stack sid m,
      refine_L6 (interp_mcfg4 eq eq (interp_instr_E_to_L0 _ ret_tree) genv (lenv, stack) sid m)
                (interp_mcfg4 eq eq (interp_instr_E_to_L0 _ alloc_tree) genv (lenv, stack) sid m).
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
    unfold interp_local_stack, interp_global, interp_intrinsics, interp_instr_E_to_L0 in INTERP.

    do 2 (cbn in INTERP; force_go_in INTERP).

  Admitted.

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

  (* Add allocation in the finite language *)
  Example add_alloc :
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
    (* go_in INTERP. *)

    (* rewrite bind_trigger in INTERP. *)
    (* repeat setoid_rewrite bind_ret_l in INTERP. *)
    (* setoid_rewrite interp_local_stack_ret in INTERP. *)
    (* repeat setoid_rewrite bind_ret_l in INTERP. *)

    (* setoid_rewrite interp_intrinsics_ret in INTERP. *)
    (* setoid_rewrite interp_global_ret in INTERP. *)
    (* setoid_rewrite interp_local_stack_ret in INTERP. *)
  Admitted.

End Finite.
