From ITree Require Import
     ITree
     ITreeFacts
     Events.State
     Events.StateFacts
     InterpFacts
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
     Handlers.Handlers.

From ExtLib Require Import
     Structures.Functor.

From Coq Require Import
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

(* Instance interp_prop_Proper : *)
(*   forall R E F G (t : itree (E +' G) R) (RR : relation R) (h : (E +' F +' G) ~> PropT.PropT (itree (E +' G))), *)
(*     Proper (@eutt (E +' F +' G) _ _ RR ==> iff) (fun t' => @PropT.interp_prop (E +' F +' G) _ _ _ _ h _ t' t). *)
(* Proof. *)
(*   intros R E F G t RR h. *)
(*   intros t1 t2 Heutt. *)
(*   unfold PropT.PropT in h. unfold Ensembles.Ensemble in h. *)
(* Admitted. *)

(* This formulation should be easier to use *)
Instance interp_prop_Proper :
  forall R E F (RR : relation R) (h : E ~> PropT F),
    Proper (@eutt _ _ _ RR ==> eq ==> Basics.impl) (@interp_prop E _ h R).
Proof.
  intros R E F RR h.
  unfold interp_prop.
  intros t1 t2 Heutt.
  red.
  unfold impl.
  intros x y H H0. subst.
  unfold interp, Basics.iter, MonadIter_Prop.
  unfold iter. 
  eexists.  split.
  (* SAZ: I'm not sure this a very usable definition of iter_prop. *)
  (* We need either an induction or coinduction principle... *)
Admitted.

Hint Unfold TT : core.
Instance TT_equiv :
  forall A, Equivalence (@TT A).
Proof.
  intros A; split; repeat intro; auto.
Qed.

(** END TO MOVE *)


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
    refine_L3 t1 t2 -> refine_L4 (model_undef t1) (model_undef t2).
Proof.
  intros t1 t2 H t Ht.
  exists t; split.
  - unfold model_undef in *.
    unfold L3 in *.
    match goal with |- PropT.interp_prop ?x _ _ _ => remember x as h end.
    eapply interp_prop_Proper; eauto.
  - reflexivity.
Qed.

Lemma refine_45 : forall Pt1 Pt2,
    refine_L4 Pt1 Pt2 -> refine_L5 (model_UB Pt1) (model_UB Pt2).
Proof.
  intros Pt1 Pt2 HR t2 HM.
  exists t2; split; [| reflexivity].
  destruct HM as (t2' & HPt2 & HPT2).
  apply HR in HPt2; destruct HPt2 as (t1' & HPt1 & HPT1).
  exists t1'; split; auto.
  match type of HPT2 with | PropT.interp_prop ?h' ?t _ _ => remember h' as h end.
  eapply interp_prop_Proper; eauto.
Qed.

Section TopLevelInputs.
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
  interp_to_L4 user_intrinsics L0_trace [] ([],[]) empty_memory_stack.

Definition model_to_L5 (prog: mcfg dtyp) :=
  let L0_trace := denote_vellvm_init prog in
  interp_to_L5 user_intrinsics L0_trace [] ([],[]) empty_memory_stack.

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

(* Instance pick_handler_proper {E R} `{LLVMEvents.UBE -< E}: *)
(*   Proper (eq ==> eq_itree eq ==> iff) (@Pick_handler E _ R). *)
(* Admitted. *)


(* Lemma interp_prop_mon: *)
(*   forall {E F} (h h': E ~> (PropT (itree F))), *)
(*     (forall e t, h _ e t -> h' _ e t) -> *)
(*     forall t, interp_prop h _ t -> interp_prop h' _ t. *)


Definition handler_correct {E F} (h_spec: E ~> PropT F) (h: E ~> itree F) :=
    (forall T e, h_spec T e (h T e)).

  
Lemma interp_prop_correct_exec:
  forall {E F} (h_spec: E ~> PropT F) (h: E ~> itree F),
    handler_correct h_spec h ->
    forall R t, interp_prop h_spec R t (interp h t).
Proof.
  intros.
  eexists; split. 2: { (* SAZ: Not sure why [reflexivity] isn't enough here *)
                         unfold interp. unfold iter, Iter_Kleisli. reflexivity. }
  intros t'.
  destruct (observe t') eqn:EQ; cbn; rewrite EQ; try reflexivity.
  exists (h _ e); auto.
Qed.

Lemma case_prop_handler_correct:
  forall {E1 E2 F}
    (h1_spec: E1 ~> PropT F)
    (h2_spec: E2 ~> PropT F)
    (h1: E1 ~> itree F)
    (h2: E2 ~> itree F)
    (C1: handler_correct h1_spec h1)
    (C2: handler_correct h2_spec h2),
    handler_correct (case_ h1_spec h2_spec) (case_ h1 h2).
Proof.
  intros E1 E2 F h1_spec h2_spec h1 h2 C1 C2.
  unfold handler_correct in *.
  intros T e.
  destruct e. apply C1. apply C2.
Qed.

Lemma UB_handler_correct: handler_correct UB_handler UB_exec.
Proof.
  unfold UB_handler. unfold UB_exec.
  unfold handler_correct.
  intros. auto.
Qed.  


Definition prop_compose :=
  fun {F G : Type -> Type } {T : Type}
    (g_spec : F ~> PropT G) (PF: PropT F T) (g:itree G T) =>
    exists f : itree F T, PF f /\ (interp_prop g_spec) T f g.

(* Level 5 interpreter Prop to Prop *)
(* h_spec is the PickHandler *)
Definition handler_correct_prop
           {E F G}
           (h_spec: E ~> PropT F) (h: E ~> itree F)
           (g_spec: F ~> PropT G) (g: F ~> itree G)
  :=
    (forall T e,
        (prop_compose g_spec (h_spec T e))
          (interp g (h T e))).


(* L4 = ExternalCallE +' LLVMEvents.UBE +' LLVMEvents.DebugE +' LLVMEvents.FailureE *)

(* Check (case_ (E_trigger_prop (F:=LLVMEvents.DebugE +' LLVMEvents.FailureE)) (case_ UB_handler (F_trigger_prop (F:=LLVMEvents.DebugE +' LLVMEvents.FailureE)))). *)

(*
Check (@F_trigger_prop LLVMEvents.ExternalCallE (LLVMEvents.DebugE +' LLVMEvents.FailureE)).
Check (case_ (@E_trigger_prop LLVMEvents.ExternalCallE)
              (case_ UB_handler (@F_trigger_prop _ (LLVMEvents.DebugE +' LLVMEvents.FailureE))): PropT L4 ~> PropT L5).

Check  ((case_ E_trigger_prop (case_ UB_handler F_trigger_prop)) : L4 ~> PropT L5).
*)

(*
Lemma pickE_UB_correct `{LLVMEvents.UBE -< L4} `{LLVMEvents.FailureE -< L4} :
  handler_correct_prop
    (Pick_handler : PickE ~> PropT L4)
    (concretize_picks : PickE ~> itree L4)
    (case_ (E_trigger_prop (F:=LLVMEvents.DebugE +' LLVMEvents.FailureE)) (case_ UB_handler (F_trigger_prop (F:=LLVMEvents.DebugE +' LLVMEvents.FailureE))))
    (case_ (E_trigger (F:=LLVMEvents.DebugE +' LLVMEvents.FailureE))
           (case_ UB_exec (F_trigger (F:=LLVMEvents.DebugE +' LLVMEvents.FailureE)))).
Proof.
  unfold handler_correct_prop.
  intros.
  unfold prop_compose.
  destruct e.
  cbn.
  assert (P \/ ~P).
  { admit. (* TODO: Classical logic *) }
  destruct H1.
  - eexists (translate _ (concretize_uvalue u)).
    Unshelve. 2 :
    {  refine (fun T fu => _).
       destruct fu; auto. }
    cbn. split. 
  
Abort.    
*)  

Lemma refine_UB
  : forall E F `{LLVMEvents.FailureE -< E +' F} T
                      (x : _ -> Prop)
                      (y : itree (E +' LLVMEvents.UBE +' F) T),
      x y -> model_UB x (exec_UB y).
  Proof.
    intros E F H T x y H0.
    unfold model_UB. unfold exec_UB.
    exists y. split. assumption.
    apply interp_prop_correct_exec.
    intros.
    apply case_prop_handler_correct.
    unfold handler_correct. intros. reflexivity.
    apply case_prop_handler_correct.
    apply UB_handler_correct.
    unfold handler_correct. intros. reflexivity.
Qed.

Lemma Pick_handler_correct :
  forall E `{LLVMEvents.FailureE -< E} `{LLVMEvents.UBE -< E},
    handler_correct (@Pick_handler E _ _) concretize_picks.
Proof.  
  unfold handler_correct.
  intros.
  destruct e.
  cbn. apply PickD with (res := concretize_uvalue u).
  
Admitted.
  
Lemma refine_undef
  : forall (E F:Type -> Type) T `{LLVMEvents.FailureE -< E} `{LLVMEvents.UBE -< F}
                      (x : itree _ T),
      model_undef x (exec_undef x).
Proof.
  intros E F H H0 T x.
  cbn in *.
  unfold model_undef.
  unfold exec_undef.
  apply interp_prop_correct_exec.
  apply case_prop_handler_correct.
  unfold handler_correct. intros. reflexivity.
  apply case_prop_handler_correct.
  apply Pick_handler_correct.

  unfold handler_correct. intros. reflexivity.
Qed.

Lemma refine_both
  : forall T
      (x : itree (ExternalCallE +' PickE +' LLVMEvents.UBE +' LLVMEvents.DebugE +' LLVMEvents.FailureE) T),
    model_UB (model_undef x) (exec_UB (exec_undef x)).
Proof.
  intros T x.
  unfold model_undef.
  unfold exec_undef.
  unfold model_UB.
  eexists.  split.
  2 : { unfold exec_UB.
        unfold interp_prop, interp at 1, Basics.iter, MonadIter_Prop.
        eexists.  split.
  
Admitted.  

(**
   SAZ : Possible entry point here
   We should be able to prove that the interpreter belongs to the model.
 *)
Theorem interpreter_sound: forall p, model p (interpreter p).
Proof.
  intros p.
  unfold model, model_user.
  unfold interpreter, interpreter_user.
  unfold interp_to_L5.
  unfold interp_to_L5_exec.
  match goal with
  | [ |- model_UB (model_undef ?X) (exec_UB (exec_undef _))] => remember X as Y
  end.
  apply refine_both.
Qed.
  
(**
   Each interpreter commutes with [bind] and [ret].
 **)

(** We hence can also commute them at the various levels of interpretation *)

(** BEGIN MOVE *)


(* Instance runState_proper_eqit {E A env} : Proper (Monad.eqm ==> Logic.eq ==> eutt Logic.eq) (@runState E A env). *)
(* Proof. *)
(*   repeat intro; subst. unfold runState. *)
(*   unfold eqm, ITreeMonad.EqM_ITree in H. *)
(*   rewrite H; reflexivity. *)
(* Qed. *)

Instance interp_state_proper {T E F S}
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

(** END MOVE *)

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
  let L4_trace       := model_undef L3_trace in
  let L5_trace       := model_UB L4_trace in
  L5_trace.

Definition model_to_L5_cfg (prog: cfg dtyp) :=
  let trace := D.denote_cfg prog in
  interp_cfg trace [] [] empty_memory_stack.

Definition refine_cfg_ret: relation (PropT L5 (memory_stack * (local_env * (global_env * uvalue)))) :=
  fun ts ts' => forall t, ts t -> exists t', ts' t' /\ eutt  (TT × (TT × (TT × refine_uvalue))) t t'.

(* Definition refine_cfg  (p1 p2: cfg dtyp): Prop := *)
(*   refine_cfg_ret (model_to_L5_cfg p1) (model_to_L5_cfg p2). *)

End TopLevelInputs.
