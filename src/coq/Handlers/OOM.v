(* begin hide *)
From Coq Require Import
     Relations
     String
     RelationClasses
     Morphisms.

From ExtLib Require Import
     Structures.Monads.

From Vellvm Require Import
     Utils.RefineProp
     Utils.InterpProp
     Utils.Error
     Semantics.LLVMEvents.

From ITree Require Import
     ITree
     Eq.Eq.

From Paco Require Import paco.

Set Implicit Arguments.
Set Contextual Implicit.

Import MonadNotation.
Open Scope monad_scope.
(* end hide *)

(** * Handler for out of memory
  Definition of the propositional and executable handlers for out of memory (abort).
*)

From Vellvm Require Import
     Utils.PropT.

Section PARAMS_MODEL.
  Variable (E F: Type -> Type).
  Notation Effin := (E +' OOME +' F).
  Notation Effout := (E +' OOME +' F).

  Definition E_trigger_model_prop : E ~> PropT Effout :=
    fun R e => fun t => t = trigger e.

  Definition F_trigger_model_prop : F ~> PropT Effout :=
    fun R e => fun t => t = trigger e.

  (* Semantics of OOM *)

  (*    If the target tree has an out of memory event, then it is a *)
  (*    refinement of any source. *)

  (*    I.e., when refining a program the behaviour of the target should *)
  (*    agree with the source at all points, but may abort, running out *)
  (*    of memory at any point. *)
  (*  *)
  Definition OOM_handler : OOME ~> PropT Effout
    (* Any tree is accepted as long as OOM is raised *)
    := fun T oome source => True.

  Definition oom_k_spec
             {T R : Type}
             (e : Effin T)
             (ta : itree Effout T)
             (k2 : T -> itree Effout R)
             (t2 : itree Effout R) : Prop
    :=
    match e with
    | inr1 (inl1 oom) => True
    | _ => t2 ≈ (bind ta k2)
    end.

  #[global] Instance oom_k_spec_proper {T R : Type} {RR : R -> R -> Prop} :
    Proper
      (eq ==>
          eq ==>
          (fun k1 k2 : T -> itree Effout R =>
             forall x : T, eqit eq true true (k1 x) (k2 x)) ==> eq ==> iff)
      (oom_k_spec).
  Proof.
    unfold Proper, respectful.
    intros x y H x0 y0 H0 x2 y2 H2 x3 y3 H3; subst.
    split; cbn; auto; intros EQ; destruct y; red; cbn in EQ; try rewrite EQ.
    2, 4 : destruct s; auto; rewrite EQ.
    all : eapply eutt_clo_bind; [ reflexivity | intros; subst; eauto ; symmetry; eauto ].
  Qed .

  (* Qed. *)

  Definition refine_OOM_handler : Effin ~> PropT Effout
    := case_ E_trigger_model_prop (case_ OOM_handler F_trigger_model_prop).

  Definition refine_OOM_h {T} (RR : relation T) (source target : itree Effout T) : Prop
    := @interp_prop Effin Effout OOME _ _ (Basics.flip RR) target source.

  Definition refine_OOM {T} (RR : relation T) (sources : PropT Effout T) (target : itree Effout T) : Prop
    := exists source, sources source /\ refine_OOM_h RR source target.

  #[global] Instance refine_OOM_h_reflexive {R} {RR : relation R} `{Reflexive _ RR} : Reflexive (refine_OOM_h RR).
  Proof.
    unfold Reflexive.

    pcofix CIH. intros t.
    assert (t ≅ t) by reflexivity.
    punfold H0; red in H0; intros.
    pstep; red.
    hinduction H0 before t; try solve [constructor; auto]; try inv CHECK; intros.
    cbn.
    destruct e as [e | [ oom | f]].
    - change (VisF (inl1 e) k2) with (observe (Vis (inl1 e) k2)).
      eapply Interp_PropT_Vis; eauto.
      Unshelve. 2 : exact (fun x e => trigger e).
      setoid_rewrite bind_trigger; reflexivity.
    - change (VisF (inr1 (inl1 oom)) k2) with (observe (Vis (inr1 (inl1 oom)) k2)).
      eapply Interp_PropT_Vis_OOM. eapply eqit_Vis. intros; reflexivity.
    - change (VisF (inr1 (inr1 f)) k2) with (observe (Vis (inr1 (inr1 f)) k2)).
      eapply Interp_PropT_Vis; eauto.
      Unshelve. 2 : exact (fun x e => trigger e).
      setoid_rewrite bind_trigger; reflexivity.
  Qed.

  #[global] Instance refine_OOM_h_transitive {R} {RR : relation R} `{Transitive _ RR} : Transitive (refine_OOM_h RR).
  Proof.
    unfold Transitive.

    pcofix CIH. intros x y z EQl EQr.
    punfold EQl; punfold EQr; red in EQl, EQr.
    pstep; red.

    hinduction EQl before x; intros.
    - remember (RetF r1).
      hinduction EQr before x; intros; inv Heqi; eauto.
      rewrite itree_eta in H0; rewrite H2 in H0.
      change (RetF r2) with (observe (Ret r2) : itree' Effout _).
      eapply Interp_PropT_Vis; eauto.
      admit.
  Admitted.

End PARAMS_MODEL.

Section PARAMS_INTERP.
  Variable (E F: Type -> Type).
  Context `{FailureE -< F}.
  Notation Effin := (E +' OOME +' F).
  Notation Effout := (E +' OOME +' F).

  Definition OOM_exec_fail {E} `{FailureE -< E}: OOME ~> itree E :=
    fun _ e => match e with | ThrowOOM s => raise ("Abort (OOM): " ++ s) end.

  Definition OOM_exec {E} `{OOME -< E} : OOME ~> itree E :=
    fun R e => trigger e.

  Definition E_trigger :  E ~> itree Effout :=
    fun R e => r <- trigger e ;; ret r.

  Definition F_trigger : F ~> itree Effout :=
    fun R e => r <- trigger e ;; ret r.

  Definition exec_OOM :
    itree Effin ~> itree Effout :=
    interp ITree.trigger.

End PARAMS_INTERP.

Instance OOM_k_spec_WF E F : k_spec_WF (refine_OOM_handler (F:=F)) (@oom_k_spec E F).
Admitted.

Lemma eutt_refine_oom_h :
  forall {T} {E F} (RR : relation T) `{REF: Reflexive _ RR} `{TRANS : Transitive _ RR}
    (t1 t2 : itree (E +' OOME +' F) T),
    eutt RR t1 t2 ->
    refine_OOM_h RR t1 t2.
Proof.
  intros T E F RR REF TRANS t1 t2 H.
  (* apply eutt_flip in H. *)
  unfold refine_OOM_h.

  pose proof @interp_prop_Proper_eq.
  unfold Proper, respectful in H0.

  eapply H0; eauto.
  { apply eutt_flip. eauto. }

  apply interp_prop_refl; eauto.
  - intros X [e | [e | e]]; cbn; reflexivity.
  - apply oom_k_spec_correct_trigger.
Qed.

Lemma refine_oom_h_raise_oom :
  forall {T} {E F} (RR : relation T)
    `{REF : Reflexive T RR}
    `{TRANS : Transitive T RR}
    (source : itree (E +' OOME +' F) T)
    (oom_msg : string),
    refine_OOM_h RR source (raiseOOM oom_msg).
Proof.
  intros T E F RR REF TRANS source oom_msg.
  unfold refine_OOM_h.

  unfold raiseOOM.
  eapply interp_prop_eutt_Proper. 1: typeclasses eauto.
  rewrite bind_trigger. reflexivity. reflexivity.

  red.
  pstep.
  econstructor.

  (* Instantiate ta *)
  unshelve (instantiate (1:=_)).
  exact (source;; trigger (ThrowOOM "")).
  - cbn.
    unfold OOM_handler.
    auto.
  - cbn.
    intros a H.
    destruct a.
    Unshelve.
    intros [].
  - cbn; auto.
Qed.

#[global] Instance refine_OOM_h_eutt_Proper {T : Type} {RR : relation T} {E F}:
  Proper (eutt eq ==> eutt eq ==> iff) (@refine_OOM_h E F T RR).
Proof.
  unfold Proper, respectful.
  intros x y XY z w ZW.
  split; intros REF; subst.
  - unfold refine_OOM_h in *.
    rewrite ZW in REF.
    rewrite XY in REF.
    auto.
  - unfold refine_OOM_h in *.
    rewrite <- ZW in REF.
    rewrite <- XY in REF.
    auto.
Qed.


(* Instance Transitive_refine_OOM_h {E F T} {RR} : Transitive (@refine_OOM_h E F T RR). *)
(* Proof. *)
(*   unfold Transitive. *)
(*   intros x y z XY YZ. *)

(*   epose proof interp_prop_Proper3. *)
(*   epose proof interp_prop_Proper2. *)
(*   epose proof interp_prop_Proper. *)
(*   unfold Proper, respectful in *. *)


(*   pose proof (itree_eta x) as Ix. *)
(*   pose proof (itree_eta y) as Iy. *)
(*   pose proof (itree_eta z) as Iz. *)

(*   unfold refine_OOM_h in *. *)
(*   eapply H. *)
(*   3: eapply XY. *)
(*   all:eauto. *)


(*   destruct (observe z) eqn:Hz. *)
(*   - pstep. red. *)

(*     destruct (observe y) eqn:Hy. *)
(*     + unfold refine_OOM_h in *. *)

(*       assert (y = ret r1) by admit. *)
(*       rewrite H in YZ. *)
(*       rewrite H in XY. *)
(*       clear H. *)

(*       assert (z = ret r0) by admit. *)
(*       rewrite H in YZ. *)
(*       clear H. *)

(*       apply interp_prop_ret_inv in XY as (rx & RRx & REST). *)
(*       unfold flip in RRx. *)

(*       apply  *)
(*       replace y with (ret r1) in YZ. *)
(*       rewrite Ix in XY. *)


(*        to *)

(*       unfold interp_prop in *. *)
(*   epose proof interp_prop_Proper. *)
(*   unfold Proper, respectful in H. *)
(*   generalize dependent x. *)
(*   generalize depy, z. *)
(*   pcofix  *)
(*   unfold Basics.flip, Basics.impl in H. *)
(*   eapply H. *)
(*   admit. *)
(*   admit. *)
(* Qed. *)

(* Instance Transitive_refine_OOM_h {E F T} {RR} : Transitive (@refine_OOM_h E F T RR). *)
(* Proof. *)
(*   unfold Transitive. *)
(*   Require Import Paco.paco. *)

(*   pcofix CIH. *)
(*   intros x y z XY YZ. *)

(*   pose proof (itree_eta x) as Ix. *)
(*   pose proof (itree_eta y) as Iy. *)
(*   pose proof (itree_eta z) as Iz. *)

(*   destruct (observe z) eqn:Hz. *)
(*   - pstep. red. *)

(*     destruct (observe y) eqn:Hy. *)
(*     + unfold refine_OOM_h in *. *)

(*       assert (y = ret r1) by admit. *)
(*       rewrite H in YZ. *)
(*       rewrite H in XY. *)
(*       clear H. *)

(*       assert (z = ret r0) by admit. *)
(*       rewrite H in YZ. *)
(*       clear H. *)

(*       apply interp_prop_ret_inv in XY as (rx & RRx & REST). *)
(*       unfold flip in RRx. *)

(*       apply  *)
(*       replace y with (ret r1) in YZ. *)
(*       rewrite Ix in XY. *)


(*        to *)

(*       unfold interp_prop in *. *)
(*   epose proof interp_prop_Proper. *)
(*   unfold Proper, respectful in H. *)
(*   generalize dependent x. *)
(*   generalize depy, z. *)
(*   pcofix  *)
(*   unfold Basics.flip, Basics.impl in H. *)
(*   eapply H. *)
(*   admit. *)
(*   admit. *)
(* Qed. *)
