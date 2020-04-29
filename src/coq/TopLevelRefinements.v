From ITree Require Import
     ITree
     ITreeFacts
     Events.State
     Events.StateFacts
     InterpFacts
     Eq.Eq.

From Vellvm Require Import
     Util
     PropT
     DynamicTypes
     CFG
     Memory
     Refinement
     Environment
     TopLevel
     LLVMAst
     Handlers.Intrinsics
     Handlers.Global
     Handlers.Local
     Handlers.Stack
     Handlers.UndefinedBehaviour.

From ExtLib Require Import
     Structures.Functor.

From Coq Require Import
     Strings.String
     Logic
     Morphisms
     Relations
     List.

Import ListNotations.
Import ITree.Basics.Basics.Monads.

Module R := Refinement.Make(Memory.A)(IO)(TopLevelEnv).
Import R.
Import TopLevelEnv.

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
  forall R E F G (RR : relation R) (h : (E +' F +' G) ~> PropT (E +' G)),
    Proper (@eutt (E +' F +' G) _ _ RR ==> eq ==> Basics.impl) (@interp_prop (E +' F +' G) _ h R).
Proof.
  intros R E F G RR h.
  intros t1 t2 Heutt.
  unfold PropT in h. 
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
    refine_L2 t1 t2 -> refine_L3 (M.interp_memory t1 m) (M.interp_memory t2 m).
Proof.
  intros t1 t2 m H.
  apply eutt_tt_to_eq_prod, eutt_interp_state; auto.
Qed.

(* Things are different for L4 and L5: we get into the [Prop] monad. *)
Lemma refine_34 : forall t1 t2,
    refine_L3 t1 t2 -> refine_L4 (P.model_undef t1) (P.model_undef t2).
Proof.
  intros t1 t2 H t Ht.
  exists t; split.
  - unfold P.model_undef in *.
    unfold IO.L3 in *.
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

(**
   We now define partial interpretations of the trees produced by the
   denotation of vellvm programs.
   The intent is to allow us to only interpret as many layers as needed
   to perform the required semantic reasoning, and lift for free the
   equivalence down the pipe.
   This gives us a _vertical_ notion of compositionality.
 *)

Definition interp_to_L1 {R} user_intrinsics (t: itree IO.L0 R) g :=
  let uvalue_trace       := INT.interp_intrinsics user_intrinsics t in
  let L1_trace           := interp_global uvalue_trace g in
  L1_trace.

Definition interp_to_L2 {R} user_intrinsics (t: itree IO.L0 R) g l :=
  let uvalue_trace   := INT.interp_intrinsics user_intrinsics t in
  let L1_trace       := interp_global uvalue_trace g in
  let L2_trace       := interp_local_stack (handle_local (v:=uvalue)) L1_trace l in
  L2_trace.

Definition interp_to_L3 {R} user_intrinsics (t: itree IO.L0 R) g l m :=
  let uvalue_trace   := INT.interp_intrinsics user_intrinsics t in
  let L1_trace       := interp_global uvalue_trace g in
  let L2_trace       := interp_local_stack (handle_local (v:=uvalue)) L1_trace l in
  let L3_trace       := M.interp_memory L2_trace m in
  L3_trace.

Definition interp_to_L4 {R} user_intrinsics (t: itree IO.L0 R) g l m :=
  let uvalue_trace   := INT.interp_intrinsics user_intrinsics t in
  let L1_trace       := interp_global uvalue_trace g in
  let L2_trace       := interp_local_stack (handle_local (v:=uvalue)) L1_trace l in
  let L3_trace       := M.interp_memory L2_trace m in
  let L4_trace       := P.model_undef L3_trace in
  L4_trace.

Ltac fold_L1 :=
    match goal with
      |- context[interp_global (INT.interp_intrinsics ?ui ?p) ?g] =>
      replace (interp_global (INT.interp_intrinsics ui p) g) with
        (interp_to_L1 ui p g) by reflexivity
    end.

Ltac fold_L2 :=
    match goal with
      |- context[interp_local_stack ?h
                (interp_global (INT.interp_intrinsics ?ui ?p) ?g) ?l] =>
      replace (interp_local_stack h (interp_global (INT.interp_intrinsics ui p) g) l) with
        (interp_to_L2 ui p g l) by reflexivity
    end.

Ltac fold_L3 :=
    match goal with
      |- context[
            M.interp_memory
              (interp_local_stack ?h
                (interp_global (INT.interp_intrinsics ?ui ?p) ?g) ?l) ?m] =>
      replace (M.interp_memory (interp_local_stack h (interp_global (INT.interp_intrinsics ui p) g) l) m) with
        (interp_to_L3 ui p g l m) by reflexivity
    end.

Ltac fold_L4 :=
    match goal with
      |- context[
            P.model_undef
              (M.interp_memory
                 (interp_local_stack ?h
                                     (interp_global (INT.interp_intrinsics ?ui ?p) ?g) ?l) ?m)] =>
      replace (P.model_undef (M.interp_memory (interp_local_stack h (interp_global (INT.interp_intrinsics ui p) g) l) m)) with
    (interp_to_L4 ui p g l m) by reflexivity
    end.

Ltac fold_L5 :=
    match goal with
      |- context[model_UB (P.model_undef (M.interp_memory (interp_local_stack ?h (interp_global (INT.interp_intrinsics ?ui ?p) ?g) ?l) ?m))] =>
      replace (model_UB (P.model_undef (M.interp_memory (interp_local_stack h (interp_global (INT.interp_intrinsics ui p) g) l) m))) with
    (interp_vellvm_model_user ui p g l m) by reflexivity
    end.

(**
   In particular, we can therefore define top-level models
   short-circuiting the interpretation early.
 *)
Definition model_to_L1 user_intrinsics (prog: mcfg dtyp) :=
  let uvalue_trace := denote_vellvm prog in
  interp_to_L1 user_intrinsics uvalue_trace [].

Definition model_to_L2 user_intrinsics (prog: mcfg dtyp) :=
  let uvalue_trace := denote_vellvm prog in
  interp_to_L2 user_intrinsics uvalue_trace [] ([],[]).

Definition model_to_L3 user_intrinsics (prog: mcfg dtyp) :=
  let uvalue_trace := denote_vellvm prog in
  interp_to_L3 user_intrinsics uvalue_trace [] ([],[]) ((M.empty, M.empty), [[]]).

Definition model_to_L4 user_intrinsics (prog: mcfg dtyp) :=
  let uvalue_trace := denote_vellvm prog in
  interp_to_L4 user_intrinsics uvalue_trace [] ([],[]) ((M.empty, M.empty), [[]]).

Definition model_to_L5 user_intrinsics (prog: mcfg dtyp) :=
  let uvalue_trace := denote_vellvm prog in
  interp_vellvm_model_user user_intrinsics uvalue_trace [] ([],[]) ((M.empty, M.empty), [[]]).

(**
   Which leads to five notion of equivalence of [mcfg]s.
   Note that all reasoning is conducted after conversion to [mcfg] and
   normalization of types.
 *)
Definition refine_mcfg_L1 user_intrinsics (p1 p2: mcfg dtyp): Prop :=
  R.refine_L1 (model_to_L1 user_intrinsics p1) (model_to_L1 user_intrinsics p2).

Definition refine_mcfg_L2 user_intrinsics (p1 p2: mcfg dtyp): Prop :=
  R.refine_L2 (model_to_L2 user_intrinsics p1) (model_to_L2 user_intrinsics p2).

Definition refine_mcfg_L3 user_intrinsics (p1 p2: mcfg dtyp): Prop :=
  R.refine_L3 (model_to_L3 user_intrinsics p1) (model_to_L3 user_intrinsics p2).

Definition refine_mcfg_L4 user_intrinsics (p1 p2: mcfg dtyp): Prop :=
  R.refine_L4 (model_to_L4 user_intrinsics p1) (model_to_L4 user_intrinsics p2).

Definition refine_mcfg user_intrinsics  (p1 p2: mcfg dtyp): Prop :=
  R.refine_L5 (model_to_L5 user_intrinsics p1) (model_to_L5 user_intrinsics p2).

(**
   The chain of refinements is monotone, legitimating the ability to
   conduct reasoning before interpretation when suitable.
 *)
Lemma refine_mcfg_L1_correct: forall user_intrinsics p1 p2,
    refine_mcfg_L1 user_intrinsics p1 p2 -> refine_mcfg user_intrinsics p1 p2.
Proof.
  intros ? p1 p2 HR.
  apply refine_45, refine_34, refine_23, refine_12, HR.
Qed.

Lemma refine_mcfg_L2_correct: forall user_intrinsics p1 p2,
    refine_mcfg_L2 user_intrinsics p1 p2 -> refine_mcfg user_intrinsics p1 p2.
Proof.
  intros ? p1 p2 HR.
  apply refine_45, refine_34, refine_23, HR.
Qed.

Lemma refine_mcfg_L3_correct: forall user_intrinsics p1 p2,
    refine_mcfg_L3 user_intrinsics p1 p2 -> refine_mcfg user_intrinsics p1 p2.
Proof.
  intros ? p1 p2 HR.
  apply refine_45, refine_34, HR.
Qed.

Lemma refine_mcfg_L4_correct: forall user_intrinsics p1 p2,
    refine_mcfg_L4 user_intrinsics p1 p2 -> refine_mcfg user_intrinsics p1 p2.
Proof.
  intros ? p1 p2 HR.
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

(* Lemma interp_prop_mon: *)
(*   forall {E F} (h h': E ~> (PropT (itree F))), *)
(*     (forall e t, h _ e t -> h' _ e t) -> *)
(*     forall t, interp_prop h _ t -> interp_prop h' _ t. *)

(* Lemma interp_prop_correct_exec: *)
(*   forall {E F} (h: E ~> (PropT (itree F))) (h': E ~> itree F), *)
(*     (forall e t, h _ e (h' _ t)) -> *)
(*     forall t, interp_prop h _ (interp h' t). *)

Lemma interp_prop_correct_exec:
  forall {E F} (h: E ~> PropT F) (h': E ~> itree F),
    (forall T e, h T e (h' T e)) ->
    forall R t, interp_prop h R t (interp h' t).
Proof.
  intros.
  eexists; split; [| reflexivity].
  intros t'.
  destruct (observe t') eqn:EQ; cbn; rewrite EQ; try reflexivity.
  exists (h' _ e); auto.
Qed.

Instance pick_handler_proper {E R} `{LLVMEvents.UBE -< E}:
  Proper (eq ==> eq_itree eq ==> iff) (@P.Pick_handler E _ R).
Admitted.

(**
   We should be able to prove that the interpreter belongs to the model.
 *)
Theorem interpreter_sound: forall p, model p (interpreter p).
Proof.
  intros p.
  unfold model, model_user, lift_sem_to_mcfg.
  flatten_goal.
  2:{
    unfold interpreter, interpreter_user.
    rewrite Heq.
    admit.
  }
  unfold interpreter, interpreter_user; rewrite Heq.
  unfold interp_vellvm_model_user, interp_vellvm_exec_user.
  match goal with |- model_UB _ (interp_UB ?t) => exists t end.
  split.
  2:{

    fold_L3.
    apply interp_prop_correct_exec.
    intros.
    subst.
    destruct e as [|e]; cbn; [reflexivity|].
    destruct e; cbn; [constructor | reflexivity].
  }
  fold_L3.
  apply interp_prop_correct_exec.
  intros.
  destruct e as [|e]; cbn; [reflexivity|].
  destruct e; cbn; [|reflexivity].

  (* Remains to prove refinement of pick handlers.
     Currently ~untrue due to the predicate
   *)
  (*
  destruct p0 as [uv P].
  destruct uv.
  all: try (simpl; setoid_rewrite translate_ret).
  { constructor; [| constructor; reflexivity].
    setoid_rewrite (translate_ret _ (DVALUE_Addr a)).
    eapply pick_handler_proper; [reflexivity | |].
    apply translate_ret.

    destruct uv; cbn; try rewrite translate_ret.
    *)
Admitted.

(**
   Each interpreter commutes with [bind] and [ret].
 **)

(** We hence can also commute them at the various levels of interpretation *)

(** BEGIN MOVE *)
From ITree Require Import
     Basics.Monad
     Basics.MonadState.

(* Instance runState_proper_eqit {E A env} : Proper (Monad.eqm ==> Logic.eq ==> eutt Logic.eq) (@runState E A env). *)
(* Proof. *)
(*   repeat intro; subst. unfold runState. *)
(*   unfold eqm, ITreeMonad.EqM_ITree in H. *)
(*   rewrite H; reflexivity. *)
(* Qed. *)

Require Import Paco.paco.
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
  forall ui {R S} (t: itree IO.L0 R) (k: R -> itree IO.L0 S) s1 s2,
    interp_to_L2 ui (ITree.bind t k) s1 s2 ≈
                 (ITree.bind (interp_to_L2 ui t s1 s2) (fun '(s1',(s2',x)) => interp_to_L2 ui (k x) s2' s1')).
Proof.
  intros.
  unfold interp_to_L2.
  rewrite INT.interp_intrinsics_bind, interp_global_bind, interp_local_stack_bind.
  apply eutt_clo_bind with (UU := Logic.eq); [reflexivity | intros ? (? & ? & ?) ->; reflexivity].
Qed.

Lemma interp_to_L2_ret: forall ui (R : Type) s1 s2 (x : R), interp_to_L2 ui (Ret x) s1 s2 ≈ Ret (s2, (s1, x)).
Proof.
  intros; unfold interp_to_L2.
  rewrite INT.interp_intrinsics_ret, interp_global_ret, interp_local_stack_ret; reflexivity.
Qed.

Definition interp_cfg {R: Type} (trace: itree IO.instr_E R) g l m :=
  let uvalue_trace       := INT.interp_intrinsics [] trace in
  let L1_trace       := interp_global uvalue_trace g in
  let L2_trace       := interp_local L1_trace l in
  let L3_trace       := M.interp_memory L2_trace m in
  let L4_trace       := P.model_undef L3_trace in
  let L5_trace       := model_UB L4_trace in
  L5_trace.

Definition model_to_L5_cfg (prog: cfg dtyp) :=
  let trace := D.denote_cfg prog in
  interp_cfg trace [] [] ((M.empty, M.empty), [[]]).

Definition refine_cfg_ret: relation (PropT IO.L5 (memory * (local_env * (global_env * uvalue)))) :=
  fun ts ts' => forall t, ts t -> exists t', ts' t' /\ eutt  (TT × (TT × (TT × refine_uvalue))) t t'.

(* Definition refine_cfg  (p1 p2: cfg dtyp): Prop := *)
(*   refine_cfg_ret (model_to_L5_cfg p1) (model_to_L5_cfg p2). *)

