From ITree Require Import
     ITree
     ITreeFacts
     Events.State
     Events.StateFacts
     InterpFacts
     KTreeFacts
     Eq.Eq.

(* YZ TODO : Revisit the dependency w.r.t. Refinement *)
From Vellvm Require Import
     Util
     PropT
     DynamicTypes
     CFG
     Memory
     Refinement
     TopLevel
     LLVMAst
     InterpreterMCFG
     InterpreterCFG
     Handlers.Handlers
     LLVMEvents.

From ExtLib Require Import
     Structures.Functor.

From Coq Require Import
     RelationClasses
     Strings.String
     Logic
     Morphisms
     Relations
     List.

From ITree Require Import
     Basics.Monad
     Basics.MonadState.

Require Import Paco.paco.

Import ListNotations.
Import ITree.Basics.Basics.Monads.

Module R := Refinement.Make Memory.Addr LLVMEvents.
Import R. 

(**
   YZ: Trying to figure how to tidy up everything. This file is currently a holdall.
   In here, we have:
   * partial interpreters to each levels;
   * hierarchies of refinements of mcfgs and proofs of inclusions;
   * lemmas for each partial interpreter of commutation with bind and ret;
   * some misc proper instances;
   * admitted statement of inclusion of the intepreter into the model;
 **)


(** The module _Refinement.Make_ defines a series of refinements between
    [itree]s at the various signatures of events a Vellvm goes through during
    the chain of interpretations leading to the definition of the model.
    These refinements state set inclusion of the concretization of the
    returned under-defined values, but impose no constraints on the states.

    In this module, we show that these refinements define a chain of growing
    relations when composed with the bits of interpretations relating each
    level.

    Finally, this allows us to lift these relations on [itree]s to a growing
    chain of relations on [mcfg typ].
 *)

(** BEGIN TO MOVE *)
Lemma subrelation_R_TT:
  forall A (R : relation A), subrelation R TT.
Proof. firstorder. Qed.

Lemma subrelation_prod_left :
  forall A B (R R' : relation A) (R2 : relation B), subrelation R R' -> subrelation (R × R2) (R' × R2).
Proof.
  intros A B R R' R2 H.
  unfold subrelation in *.
  intros x y HRR2.
  inversion HRR2; firstorder.
Qed.

Lemma eutt_tt_to_eq_prod :
  forall X R (RR : relation R) E (t1 t2 : itree E (X * R)),
    eutt (eq × RR) t1 t2 -> eutt (TT × RR) t1 t2.
Proof.
  intros X R RR E t1 t2 Heutt.
  unfold eutt.
  apply (eqit_mon (eq × RR) (TT × RR) true true true true); trivial.
  intros x0 x1 PR.
  eapply subrelation_prod_left. apply subrelation_R_TT. all: apply PR.
Qed.


(* Instance runState_proper_eqit {E A env} : Proper (Monad.eqm ==> Logic.eq ==> eutt Logic.eq) (@runState E A env). *)
(* Proof. *)
(*   repeat intro; subst. unfold runState. *)
(*   unfold eqm, ITreeMonad.EqM_ITree in H. *)
(*   rewrite H; reflexivity. *)
(* Qed. *)

Global Instance interp_state_proper {T E F S}
         (h: forall T : Type, E T -> Monads.stateT S (itree F) T)
  : Proper (eutt Logic.eq ==> Monad.eqm) (State.interp_state h (T := T)).
Proof.
  einit. ecofix CIH. intros.

  rewrite !unfold_interp_state. punfold H0. red in H0.
  induction H0; intros; subst; simpl; pclearbot.
  - eret.
  - etau.
  - ebind. econstructor; [reflexivity|].
    intros; subst.
    etau. ebase.
  - rewrite tau_euttge, unfold_interp_state; eauto.
  - rewrite tau_euttge, unfold_interp_state; eauto.
Qed.



  
Hint Unfold TT : core.
Local Instance TT_equiv :
  forall A, Equivalence (@TT A).
Proof.
  intros A; split; repeat intro; auto.
Qed.

(** END TO MOVE *)

Section REFINEMENT.
  
(** We first prove that the [itree] refinement at level [i] entails the
    refinement at level [i+1] after running the [i+1] level of interpretation
 *)

Lemma refine_01: forall t1 t2 g,
    refine_L0 t1 t2 -> refine_L1 (interp_global t1 g) (interp_global t2 g).
Proof.
  intros t1 t2 g H.
  apply eutt_tt_to_eq_prod, eutt_interp_state; auto.
Qed.

Lemma refine_12 : forall t1 t2 l,
    refine_L1 t1 t2 -> refine_L2 (interp_local_stack (handle_local (v:=uvalue)) t1 l) (interp_local_stack (handle_local (v:=uvalue)) t2 l).
Proof.
  intros t1 t2 l H.
  apply eutt_tt_to_eq_prod, eutt_interp_state; auto.
Qed.

Lemma refine_23 : forall t1 t2 m,
    refine_L2 t1 t2 -> refine_L3 (interp_memory t1 m) (interp_memory t2 m).
Proof.
  intros t1 t2 m H.
  apply eutt_tt_to_eq_prod, eutt_interp_state; auto.
Qed.

(* Things are different for L4 and L5: we get into the [Prop] monad. *)
Lemma refine_34 : forall t1 t2,
    refine_L3 t1 t2 -> refine_L4 (model_undef refine_res3 t1) (model_undef refine_res3 t2).
Proof.
  intros t1 t2 H t Ht.
  exists t; split.
  - unfold model_undef in *.
    unfold L3 in *.
    match goal with |- PropT.interp_prop ?x _ _ _ _ => remember x as h end.
    eapply interp_prop_Proper_eq in Ht.
    apply Ht.
    + typeclasses eauto.
    + typeclasses eauto.
    + assumption.
    + reflexivity.
  - reflexivity.
Qed.

Lemma refine_45 : forall Pt1 Pt2,
    refine_L4 Pt1 Pt2 -> refine_L5 (model_UB refine_res3 Pt1) (model_UB refine_res3 Pt2).
Proof.
  intros Pt1 Pt2 HR t2 HM.
  exists t2; split; [| reflexivity].
  destruct HM as (t2' & HPt2 & HPT2).
  apply HR in HPt2; destruct HPt2 as (t1' & HPt1 & HPT1).
  exists t1'; split; auto.
  match type of HPT2 with | PropT.interp_prop ?h' ?t _ _ _ => remember h' as h end.
  eapply interp_prop_Proper_eq with (RR := refine_res3); eauto.
  - typeclasses eauto.
  - typeclasses eauto.
Qed.


  Variable ret_typ : dtyp.
  Variable entry : string.
  Variable args : list uvalue.
  Variable user_intrinsics: IS.intrinsic_definitions.

  Definition denote_vellvm_init := denote_vellvm ret_typ entry args.
  
(**
   In particular, we can therefore define top-level models
   short-circuiting the interpretation early.
 *)

Definition model_to_L1  (prog: mcfg dtyp) :=
  let L0_trace := denote_vellvm_init prog in
  interp_to_L1 user_intrinsics L0_trace [].

Definition model_to_L2 (prog: mcfg dtyp) :=
  let L0_trace := denote_vellvm_init prog in
  interp_to_L2 user_intrinsics L0_trace [] ([],[]).

Definition model_to_L3 (prog: mcfg dtyp) :=
  let L0_trace := denote_vellvm_init prog in
  interp_to_L3 user_intrinsics L0_trace [] ([],[]) empty_memory_stack.

Definition model_to_L4 (prog: mcfg dtyp) :=
  let L0_trace := denote_vellvm_init prog in
  interp_to_L4 (refine_res3) user_intrinsics L0_trace [] ([],[]) empty_memory_stack.

Definition model_to_L5 (prog: mcfg dtyp) :=
  let L0_trace := denote_vellvm_init prog in
  interp_to_L5 (refine_res3) user_intrinsics L0_trace [] ([],[]) empty_memory_stack.

(**
   Which leads to five notion of equivalence of [mcfg]s.
   Note that all reasoning is conducted after conversion to [mcfg] and
   normalization of types.
 *)
Definition refine_mcfg_L1 (p1 p2: mcfg dtyp): Prop :=
  R.refine_L1 (model_to_L1 p1) (model_to_L1 p2).

Definition refine_mcfg_L2 (p1 p2: mcfg dtyp): Prop :=
  R.refine_L2 (model_to_L2 p1) (model_to_L2 p2).

Definition refine_mcfg_L3 (p1 p2: mcfg dtyp): Prop :=
  R.refine_L3 (model_to_L3 p1) (model_to_L3 p2).

Definition refine_mcfg_L4 (p1 p2: mcfg dtyp): Prop :=
  R.refine_L4 (model_to_L4 p1) (model_to_L4 p2).

Definition refine_mcfg  (p1 p2: mcfg dtyp): Prop :=
  R.refine_L5 (model_to_L5 p1) (model_to_L5 p2).

(**
   The chain of refinements is monotone, legitimating the ability to
   conduct reasoning before interpretation when suitable.
 *)
Lemma refine_mcfg_L1_correct: forall p1 p2,
    refine_mcfg_L1 p1 p2 -> refine_mcfg p1 p2.
Proof.
  intros p1 p2 HR.
  apply refine_45, refine_34, refine_23, refine_12, HR.
Qed.

Lemma refine_mcfg_L2_correct: forall p1 p2,
    refine_mcfg_L2 p1 p2 -> refine_mcfg p1 p2.
Proof.
  intros p1 p2 HR.
  apply refine_45, refine_34, refine_23, HR.
Qed.

Lemma refine_mcfg_L3_correct: forall p1 p2,
    refine_mcfg_L3 p1 p2 -> refine_mcfg p1 p2.
Proof.
  intros p1 p2 HR.
  apply refine_45, refine_34, HR.
Qed.

Lemma refine_mcfg_L4_correct: forall p1 p2,
    refine_mcfg_L4 p1 p2 -> refine_mcfg p1 p2.
Proof.
  intros p1 p2 HR.
  apply refine_45, HR.
Qed.

(* MOVE *)
Ltac flatten_goal :=
  match goal with
  | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac flatten_hyp h :=
  match type of h with
  | context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac flatten_all :=
  match goal with
  | h: context[match ?x with | _ => _ end] |- _ => let Heq := fresh "Heq" in destruct x eqn:Heq
  | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.


Lemma UB_handler_correct: handler_correct UB_handler UB_exec.
Proof.
  unfold UB_handler. unfold UB_exec.
  unfold handler_correct.
  intros. auto.
Qed.  


Lemma refine_UB
  : forall E F `{LLVMEvents.FailureE -< E +' F} T TT (HR: Reflexive TT)
                      (x : _ -> Prop)
                      (y : itree (E +' LLVMEvents.UBE +' F) T),
      x y -> model_UB TT x (exec_UB y).
  Proof.
    intros E F H T TT HR x y H0.
    unfold model_UB. unfold exec_UB.
    exists y. split. assumption.
    apply interp_prop_correct_exec.
    intros.
    apply case_prop_handler_correct.
    unfold handler_correct. intros. reflexivity.
    apply case_prop_handler_correct.
    apply UB_handler_correct.
    unfold handler_correct. intros. reflexivity.
    assumption. reflexivity.
Qed.

Lemma Pick_handler_correct :
  forall E `{LLVMEvents.FailureE -< E} `{LLVMEvents.UBE -< E},
    handler_correct (@Pick_handler E _ _) concretize_picks.
Proof.  
  unfold handler_correct.
  intros.
  destruct e.
  cbn. apply PickD with (res := concretize_uvalue u).
  - apply Pick.concretize_u_concretize_uvalue.
  - reflexivity.
Qed.
  
Lemma refine_undef
  : forall (E F:Type -> Type) T TT (HR: Reflexive TT)  `{LLVMEvents.UBE -< F} `{LLVMEvents.FailureE -< F}
                      (x : itree _ T),
      model_undef TT x (@exec_undef E F _ _ _ x).
Proof.
  intros E F H H0 T TT HR x.
  cbn in *.
  unfold model_undef.
  unfold exec_undef.
  apply interp_prop_correct_exec.
  apply case_prop_handler_correct.
  unfold handler_correct. intros. reflexivity.
  apply case_prop_handler_correct.
  apply Pick_handler_correct.

  unfold handler_correct. intros. reflexivity.
  assumption. reflexivity.
Qed.

(**
   We prove that the interpreter belongs to the model.
 *)
Theorem interpreter_sound: forall p, model p (interpreter p).
Proof.
  intros p.
  unfold model, model_user.
  unfold interpreter, interpreter_user.
  unfold interp_to_L5.
  unfold interp_to_L5_exec.
  apply refine_UB.  auto.
  apply refine_undef. auto.
Qed.

End REFINEMENT.

(**
   Each interpreter commutes with [bind] and [ret].
 **)

(** We hence can also commute them at the various levels of interpretation *)

Lemma interp_to_L2_bind:
  forall ui {R S} (t: itree L0 R) (k: R -> itree L0 S) s1 s2,
    interp_to_L2 ui (ITree.bind t k) s1 s2 ≈
                 (ITree.bind (interp_to_L2 ui t s1 s2) (fun '(s1',(s2',x)) => interp_to_L2 ui (k x) s2' s1')).
Proof.
  intros.
  unfold interp_to_L2.
  rewrite interp_intrinsics_bind, interp_global_bind, interp_local_stack_bind.
  apply eutt_clo_bind with (UU := Logic.eq); [reflexivity | intros ? (? & ? & ?) ->; reflexivity].
Qed.

Lemma interp_to_L2_ret: forall ui (R : Type) s1 s2 (x : R), interp_to_L2 ui (Ret x) s1 s2 ≈ Ret (s2, (s1, x)).
Proof.
  intros; unfold interp_to_L2.
  rewrite interp_intrinsics_ret, interp_global_ret, interp_local_stack_ret; reflexivity.
Qed.

Definition interp_cfg {R: Type} (trace: itree instr_E R) g l m :=
  let uvalue_trace   := interp_intrinsics [] trace in
  let L1_trace       := interp_global uvalue_trace g in
  let L2_trace       := interp_local L1_trace l in
  let L3_trace       := interp_memory L2_trace m in
  let L4_trace       := model_undef Logic.eq L3_trace in
  let L5_trace       := model_UB Logic.eq L4_trace in
  L5_trace.

Definition model_to_L5_cfg (prog: cfg dtyp) :=
  let trace := D.denote_cfg prog in
  interp_cfg trace [] [] empty_memory_stack.

Definition refine_cfg_ret: relation (PropT L5 (memory_stack * (local_env * (global_env * uvalue)))) :=
  fun ts ts' => forall t, ts t -> exists t', ts' t' /\ eutt  (TT × (TT × (TT × refine_uvalue))) t t'.

(* Definition refine_cfg  (p1 p2: cfg dtyp): Prop := *)
(*   refine_cfg_ret (model_to_L5_cfg p1) (model_to_L5_cfg p2). *)

(* Reasoning lemmas for [denote_bks] *)

Section Denotation.
Import CatNotations.
Import Eq.

Lemma denote_bks_nil: forall s, D.denote_bks [] s ≈ ret (inl s).
Proof.
  intros s; unfold D.denote_bks.
  match goal with
  | |- CategoryOps.iter (C := ktree _) ?body ?s ≈ _ =>
    rewrite (unfold_iter body s)
  end.
  repeat (cbn; (rewrite bind_bind || rewrite bind_ret_l)).
  reflexivity.
Qed.

Lemma denote_bks_singleton :
  forall (b : LLVMAst.block dtyp) (bid : block_id) (nextblock : block_id),
    blk_id b = bid ->
    (snd (blk_term b)) = (TERM_Br_1 nextblock) ->
    (blk_id b) <> nextblock ->
    eutt (Logic.eq) (D.denote_bks [b] bid) (D.denote_block b).
Proof.
  intros b bid nextblock Heqid Heqterm Hneq.
  cbn.
  unfold D.denote_bks.
  rewrite KTreeFacts.unfold_iter_ktree.
  cbn.
  destruct (Eqv.eqv_dec_p (blk_id b) bid) eqn:Heq'; try contradiction.
  repeat rewrite bind_bind.
  rewrite Heqterm.
  cbn.
  apply eutt_eq_bind; intros ?; rewrite bind_ret_l.
  cbn.
  setoid_rewrite translate_ret.
  setoid_rewrite bind_ret_l.
  destruct (Eqv.eqv_dec_p (blk_id b) nextblock); try contradiction.
  repeat setoid_rewrite bind_ret_l. unfold Datatypes.id.
  reflexivity.
Qed.

Lemma denote_code_app :
  forall a b,
    D.denote_code (a ++ b)%list ≈ ITree.bind (D.denote_code a) (fun _ => D.denote_code b).
Proof.
  induction a; intros b.
  - cbn. rewrite 2 bind_ret_l.
    reflexivity.
  - simpl.
    unfold D.denote_code, map_monad_ in *.
    simpl in *.
    repeat rewrite bind_bind.
    specialize (IHa b).
    apply eutt_eq_bind; intros ().
    rewrite bind_bind.
    setoid_rewrite bind_ret_l.
    setoid_rewrite IHa.
    repeat rewrite bind_bind.
    setoid_rewrite bind_ret_l.
    reflexivity.
Qed.

Lemma denote_code_cons :
  forall a l,
    D.denote_code (a::l) ≈ ITree.bind (D.denote_instr a) (fun _ => D.denote_code l).
Proof.
  intros.
  rewrite list_cons_app, denote_code_app.
  cbn.
  repeat rewrite bind_bind.
  apply eutt_eq_bind; intros ().
  rewrite !bind_bind, !bind_ret_l.
  reflexivity.
Qed.

Lemma denote_code_nil :
    D.denote_code [] ≈ ret tt.
Proof.
  intros.
  cbn. rewrite bind_ret_l.
  reflexivity.
Qed.

Import MonadNotation.
Open Scope monad_scope.

Lemma denote_bks_unfold: forall bks bid b,
    find_block dtyp bks bid = Some b ->
    D.denote_bks bks bid ≈
    vob <- D.denote_block b ;;
    match vob with
    | inr v => ret (inr v)
    | inl bid_target =>
      match find_block DynamicTypes.dtyp bks bid_target with
      | None => ret (inl bid_target)
      | Some block_target =>
        dvs <- Util.map_monad
                (fun x => translate exp_E_to_instr_E (D.denote_phi bid x))
                (blk_phis block_target) ;;
        Util.map_monad (fun '(id,dv) => trigger (LocalWrite id dv)) dvs;;
        D.denote_bks bks bid_target
      end
    end.
Proof.
  intros.
  cbn. unfold D.denote_bks at 1.
  rewrite KTreeFacts.unfold_iter_ktree. cbn. rewrite bind_bind.
  rewrite H. cbn. rewrite !bind_bind.
  eapply eutt_eq_bind; intros ?.
  repeat rewrite bind_ret_l.
  eapply eutt_eq_bind; intros bov. 
  cbn. destruct bov. cbn.
  - destruct (find_block dtyp bks b0). cbn.
    + rewrite bind_bind. eapply eutt_clo_bind. reflexivity. intros.
      subst. rewrite bind_bind. eapply eutt_clo_bind. reflexivity.
      intros; subst. rewrite bind_ret_l. cbn.
      rewrite tau_eutt.
      reflexivity.
    + rewrite bind_ret_l; reflexivity.
  - rewrite bind_ret_l; reflexivity.
Qed.

Lemma denote_bks_unfold_not_in: forall bks bid,
    find_block dtyp bks bid = None ->
    D.denote_bks bks bid ≈ Ret (inl bid).
Proof.
  intros.
  unfold D.denote_bks.
  rewrite KTreeFacts.unfold_iter_ktree.
  rewrite H; cbn.
  rewrite bind_ret_l.
  reflexivity.
Qed.

End Denotation.
