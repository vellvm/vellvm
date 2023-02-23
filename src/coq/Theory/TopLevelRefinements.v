(* begin hide *)
From ITree Require Import
     ITree
     ITreeFacts
     Basics.HeterogeneousRelations
     Events.State
     Events.StateFacts
     InterpFacts
     KTreeFacts
     Eq.Eqit.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics
     Theory.Refinement
     Theory.InterpreterMCFG
     Theory.InterpreterCFG.

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
Import SemNotations.

Module R := Refinement.Make Memory.Addr LLVMEvents.
Import R. 
(* end hide *)

(**
   This file is currently a holdall.
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

Import AlistNotations.
Lemma alist_find_eq_dec_local_env : 
  forall k (m1 m2 : local_env),
    {m2 @ k = m1 @ k} + {m2 @ k <> m1 @ k}.
Proof.
  intros; eapply alist_find_eq_dec.
Qed.


#[global] Instance interp_state_proper {T E F S}
         (h: forall T : Type, E T -> Monads.stateT S (itree F) T)
  : Proper (eutt Logic.eq ==> Monad.eq1) (State.interp_state h (T := T)).
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

#[export] Hint Unfold TT : core.
#[global] Instance TT_equiv :
  forall A, Equivalence (@TT A).
Proof.
  intros A; split; repeat intro; auto.
Qed.

(** END TO MOVE *)

Section REFINEMENT.
  
  (** We first prove that the [itree] refinement at level [i] entails the
    refinement at level [i+1] after running the [i+1] level of interpretation
   *)

  (* Lemma 5.7 
     See the related definition of [refine_L0] in Refinement.v. (Search for Lemma 5.7)

     The similar results mentioned in the paper are listed below.
  *)
  Lemma refine_01: forall t1 t2 g,
    refine_L0 t1 t2 -> refine_L1 (interp_global t1 g) (interp_global t2 g).
  Proof.
    intros t1 t2 g H.
    apply eutt_tt_to_eq_prod, eutt_interp_state; auto.
  Qed.

  Lemma refine_12 : forall t1 t2 l,
      refine_L1 t1 t2 -> refine_L2 (interp_local_stack t1 l) (interp_local_stack t2 l).
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
      + apply prod_rel_refl; typeclasses eauto.
      + apply prod_rel_trans; typeclasses eauto.
      + assumption.
      + reflexivity.
    - reflexivity.
  Qed.

  (* The inclusion of refinement relations between 4 and 5 changes now *)
  Lemma refine_45 : forall Pt1 Pt2,
      refine_L4 Pt1 Pt2 -> refine_L5 Pt1 Pt2.
         (* (model_UB refine_res3 Pt1) (model_UB refine_res3 Pt2). *)
  Proof.
    intros Pt1 Pt2 HR t2 HM.
    apply HR in HM as (t1 & HPt1 & HPT1).
    exists t1; split; auto.
 Qed.

  Variable ret_typ : dtyp.
  Variable entry : string.
  Variable args : list uvalue.

  Definition denote_vellvm_init := denote_vellvm ret_typ entry args.
  
  (**
   In particular, we can therefore define top-level models
   short-circuiting the interpretation early.
   *)

  Definition model_to_L1  (prog: mcfg dtyp) :=
    let L0_trace := denote_vellvm_init prog in
    ℑs1 L0_trace [].

  Definition model_to_L2 (prog: mcfg dtyp) :=
    let L0_trace := denote_vellvm_init prog in
    ℑs2 L0_trace [] ([],[]).

  Definition model_to_L3 (prog: mcfg dtyp) :=
    let L0_trace := denote_vellvm_init prog in
    ℑs3 L0_trace [] ([],[]) empty_memory_stack.

  Definition model_to_L4 (prog: mcfg dtyp) :=
    let L0_trace := denote_vellvm_init prog in
    ℑs4 (refine_res3) L0_trace [] ([],[]) empty_memory_stack.

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
    R.refine_L5 (model_to_L4 p1) (model_to_L4 p2).

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

  Definition build_singleton {A} : A -> A -> Prop := eq.
  
  (**
   Theorem 5.8: We prove that the interpreter belongs to the model.
   *)
  Theorem interpreter_sound: forall p, 
    refine_L5 (model p) (build_singleton (interpreter p)).
  Proof.
    intros p.
    intros ? [].
    exists (interpreter p).
    split.
    - apply refine_undef. auto.
    - right.
      reflexivity.
 Qed.

End REFINEMENT.

(**
   Each interpreter commutes with [bind] and [ret].
 **)

(** We hence can also commute them at the various levels of interpretation *)

Lemma interp2_bind:
  forall {R S} (t: itree L0 R) (k: R -> itree L0 S) s1 s2,
    ℑs2 (ITree.bind t k) s1 s2 ≈
            (ITree.bind (ℑs2 t s1 s2) (fun '(s1',(s2',x)) => ℑs2 (k x) s2' s1')).
Proof.
  intros.
  unfold ℑs2.
  rewrite interp_intrinsics_bind, interp_global_bind, interp_local_stack_bind.
  apply eutt_clo_bind with (UU := Logic.eq); [reflexivity | intros ? (? & ? & ?) ->; reflexivity].
Qed.

Lemma interp2_ret:
  forall (R : Type) s1 s2 (x : R),
    ℑs2 (Ret x) s1 s2 ≈ Ret (s2, (s1, x)).
Proof.
  intros; unfold ℑs2.
  rewrite interp_intrinsics_ret, interp_global_ret, interp_local_stack_ret; reflexivity.
Qed.

Definition interp_cfg {R: Type} (trace: itree instr_E R) g l m :=
  let uvalue_trace   := interp_intrinsics trace in
  let L1_trace       := interp_global uvalue_trace g in
  let L2_trace       := interp_local L1_trace l in
  let L3_trace       := interp_memory L2_trace m in
  let L4_trace       := model_undef eq L3_trace in
  L4_trace.

Definition model_to_L4_cfg (prog: cfg dtyp) :=
  let trace := denote_cfg prog in
  interp_cfg trace [] [] empty_memory_stack.

Definition refine_cfg_ret: relation (PropT L5 (memory_stack * (local_env * (global_env * uvalue)))) :=
  fun ts ts' => forall t, ts t -> exists t', ts' t' /\ eutt  (TT × (TT × (TT × refine_uvalue))) t t'.

