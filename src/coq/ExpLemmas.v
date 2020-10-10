From Coq Require Import
     Morphisms.

Require Import List.
Import ListNotations.
Require Import ZArith.

From ITree Require Import
     ITree
     Basics.Monad
     Eq.Eq
     TranslateFacts
     Interp.InterpFacts
     Events.State
     Events.StateFacts.

From Vellvm Require Import
     LLVMEvents
     LLVMAst
     Util
     DynamicTypes
     DynamicValues
     Handlers.Handlers
     Refinement
     TopLevel
     InterpreterCFG
     Tactics
     TypToDtyp
     AstLib
     InterpreterCFG
     PostConditions.


Import D.
Open Scope itree_scope.

Section Translations.

  (* Technicality: translations by [lookup_E_to_exp_E] and [exp_E_to_instr_E] leave these events unphased *)
  Lemma lookup_E_to_exp_E_Global : forall {X} (e : LLVMGEnvE X),
      lookup_E_to_exp_E (subevent X e) = subevent X e.
  Proof.
    reflexivity.
  Qed.

  Lemma exp_E_to_instr_E_Global : forall {X} (e : LLVMGEnvE X),
      exp_E_to_instr_E (subevent X e) = subevent X e.
  Proof.
    reflexivity.
  Qed.

  Lemma lookup_E_to_exp_E_Local : forall {X} (e : LLVMEnvE X),
      lookup_E_to_exp_E (subevent X e) = subevent X e.
  Proof.
    reflexivity.
  Qed.

  Lemma exp_E_to_instr_E_Local : forall {X} (e : LLVMEnvE X),
      exp_E_to_instr_E (subevent X e) = subevent X e.
  Proof.
    reflexivity.
  Qed.

  Lemma exp_E_to_instr_E_Memory : forall {X} (e : MemoryE X),
      exp_E_to_instr_E (subevent X e) = subevent X e.
  Proof.
    reflexivity.
  Qed.
  
End Translations.

Lemma denote_exp_GR :forall defs g l m id v τ,
    Maps.lookup id g = Some v ->
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some τ) (EXP_Ident (ID_Global id)))) g l m
    ≈
    Ret (m,(l,(g,dvalue_to_uvalue v))).
Proof.
  intros; cbn.
  rewrite !translate_bind.
  rewrite translate_trigger, lookup_E_to_exp_E_Global, subevent_subevent,
  translate_trigger, exp_E_to_instr_E_Global, subevent_subevent.
  rewrite interp_cfg_to_L3_bind.
  rewrite interp_cfg_to_L3_GR; cycle -1.
  eauto.
  rewrite bind_ret_l.
  rewrite !translate_ret.
  rewrite interp_cfg_to_L3_ret.
  reflexivity.
Qed.

Lemma denote_exp_LR :forall defs g l m id v τ,
    Maps.lookup id l = Some v ->
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some τ) (EXP_Ident (ID_Local id)))) g l m
    ≈
    Ret (m,(l,(g,v))).
Proof.
  intros; cbn.
  rewrite translate_trigger, lookup_E_to_exp_E_Local, subevent_subevent,
  translate_trigger, exp_E_to_instr_E_Local, subevent_subevent.
  rewrite interp_cfg_to_L3_LR; cycle -1.
  eauto.
  reflexivity.
Qed.

Definition pure {E R} (t : global_env -> local_env -> memory_stack -> itree E (memory_stack * (local_env * (global_env * R)))) : Prop :=
  forall g l m, t g l m ⤳ fun '(m',(l',(g',_))) => m' = m /\ l' = l /\ g' = g.

Require Import String.
Opaque append.

Lemma failure_is_pure : forall R s defs,
    pure (R := R) (interp_cfg_to_L3 defs (translate exp_E_to_instr_E (raise s))).
Proof.
  unfold pure, has_post, raise, Exception.throw; intros.
  rewrite translate_vis.
  unfold interp_cfg_to_L3.
  rewrite interp_intrinsics_vis.
  cbn; unfold Intrinsics.F_trigger; cbn; rewrite subevent_subevent.
  rewrite interp_global_bind, interp_global_trigger.
  cbn; rewrite subevent_subevent.
  rewrite !interp_local_bind, interp_local_trigger.
  cbn; rewrite subevent_subevent.
  rewrite !interp_memory_bind, interp_memory_trigger.
  cbn.
  apply eutt_eq_bind; intros (_ & ? & ? & []).
Qed.

Lemma UB_is_pure : forall R s defs,
    pure (R := R) (interp_cfg_to_L3 defs (translate exp_E_to_instr_E (raiseUB s))).
Proof.
  unfold pure, has_post, raiseUB; intros.
  rewrite translate_vis.
  unfold interp_cfg_to_L3.
  rewrite interp_intrinsics_vis.
  cbn; unfold Intrinsics.F_trigger; cbn; rewrite subevent_subevent.
  rewrite interp_global_bind, interp_global_trigger.
  cbn; rewrite subevent_subevent.
  rewrite !interp_local_bind, interp_local_trigger.
  cbn; rewrite subevent_subevent.
  rewrite !interp_memory_bind, interp_memory_trigger.
  cbn.
  apply eutt_eq_bind; intros (_ & ? & ? & []).
Qed.

Lemma translate_map_monad {E F A B} (l : list A) (ts : A -> itree E B) (h : E ~> F) :
  translate h (map_monad ts l) ≈ map_monad (fun a => translate h (ts a)) l.
Proof.
  induction l as [| a l IH].
  - cbn; rewrite translate_ret; reflexivity.
  - simpl; rewrite translate_bind.
    apply eutt_eq_bind; intros ?.
    rewrite !translate_bind, IH.
    setoid_rewrite translate_ret.
    reflexivity.
Qed.

Lemma interp_map_monad {E F A B} (l : list A) (ts : A -> itree E B) (h : E ~> itree F):
  interp h (map_monad ts l) ≈ map_monad (fun a => interp h (ts a)) l.
Proof.
  intros; induction l as [| a l IH]; simpl.
  - rewrite interp_ret; reflexivity.
  - rewrite interp_bind.
    apply eutt_eq_bind; intros ?; cbn.
    rewrite interp_bind, IH.
    apply eutt_eq_bind; intros ?; cbn.
    rewrite interp_ret; reflexivity.
Qed.

Lemma interp_state_map_monad {E F S A B} (l : list A) (ts : A -> itree E B) (h : E ~> Monads.stateT S (itree F)) (s : S):
  interp_state h (map_monad ts l) s ≈ map_monad (m := Monads.stateT S (itree F)) (fun a => interp_state h (ts a)) l s.
Proof.
  intros; revert s; induction l as [| a l IH]; simpl; intros s.
  - rewrite interp_state_ret; reflexivity.
  - rewrite interp_state_bind.
    apply eutt_eq_bind; intros []; cbn.
    rewrite interp_state_bind, IH.
    apply eutt_eq_bind; intros []; cbn.
    rewrite interp_state_ret; reflexivity.
Qed.

Lemma interp_cfg_to_L3_map_monad {A B} defs g l m (xs : list A) (ts : A -> itree _ B) : 
  interp_cfg_to_L3 defs (map_monad ts xs) g l m ≈
                   map_monad (m := Monads.stateT _ (Monads.stateT _ (Monads.stateT _ (itree _))))
                   (fun a => interp_cfg_to_L3 defs (ts a)) xs g l m.
Proof.
  intros; revert g l m; induction xs as [| a xs IH]; simpl; intros.
  - rewrite interp_cfg_to_L3_ret; reflexivity.
  - rewrite interp_cfg_to_L3_bind.
    apply eutt_eq_bind; intros (? & ? & ? & ?); cbn.
    rewrite interp_cfg_to_L3_bind, IH.
    apply eutt_eq_bind; intros (? & ? & ? & ?); cbn.
    rewrite interp_cfg_to_L3_ret; reflexivity.
Qed.

Lemma map_monad_eutt_state_ind :
  forall {E S A B} (I : S -> Prop) (f : A -> Monads.stateT S (itree E) B) (l : list A) s,
    (forall a s, In a l -> (f a s) ⤳ fun '(s,_) => I s) ->
    I s ->
    map_monad f l s ⤳ fun '(s,_) => I s.
Proof.
  induction l as [| a l IH]; intros s HB HI; simpl.
  - apply eutt_Ret; auto.
  - setoid_rewrite has_post_post_strong in HB.
    eapply eutt_clo_bind; [apply HB; left; auto |].
    intros [s' ?] [] [EQ ?]; inv EQ.
    simpl.
    setoid_rewrite has_post_post_strong in IH.
    eapply eutt_clo_bind; [apply IH |]; auto.
    intros; apply HB; right; auto.
    intros [s' ?] [] [EQ ?]; inv EQ; cbn; apply eutt_Ret; auto. 
Qed.

(* Lemma map_monad_L3_ind : *)
(*   forall {A B} (I : S -> Prop) (f : A -> Monads.stateT S (itree E) B) (l : list A) s, *)
(*     (forall a s, In a l -> (f a s) ⤳ fun '(s,_) => I s) -> *)
(*     I s -> *)
(*     map_monad f xs g l m ⤳ fun '(s,_) => I s. *)
(* Proof. *)
(*   induction l as [| a l IH]; intros s HB HI; simpl. *)
(*   - apply eutt_Ret; auto. *)
(*   - setoid_rewrite has_post_post_strong in HB. *)
(*     eapply eutt_clo_bind; [apply HB; left; auto |]. *)
(*     intros [s' ?] [] [EQ ?]; inv EQ. *)
(*     simpl. *)
(*     setoid_rewrite has_post_post_strong in IH. *)
(*     eapply eutt_clo_bind; [apply IH |]; auto. *)
(*     intros; apply HB; right; auto. *)
(*     intros [s' ?] [] [EQ ?]; inv EQ; cbn; apply eutt_Ret; auto.  *)
(* Qed. *)

Lemma expr_are_pure : forall defs o e, pure (interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp o e))).
Proof.
  intros; unfold pure, has_post.
  induction e; simpl; intros.

  - destruct id; cbn.
    + rewrite translate_bind, translate_trigger, lookup_E_to_exp_E_Global, subevent_subevent.
      rewrite translate_bind, translate_trigger, exp_E_to_instr_E_Global, subevent_subevent.
      rewrite interp_cfg_to_L3_bind. 
      unfold interp_cfg_to_L3.
      rewrite interp_intrinsics_trigger.
      cbn; unfold Intrinsics.F_trigger; cbn.
      rewrite interp_global_trigger.
      cbn.
      break_match_goal; cbn.
      * rewrite interp_local_ret, interp_memory_ret, bind_ret_l.
        rewrite !translate_ret, interp_intrinsics_ret, interp_global_ret, interp_local_ret, interp_memory_ret.
        apply eutt_Ret; intuition.
      * unfold raise, Exception.throw.
        rewrite interp_local_vis.
        cbn; rewrite !bind_bind.
        rewrite interp_memory_bind, interp_memory_trigger.
        cbn.
        rewrite !bind_bind.
        apply eutt_eq_bind; intros [].
    + rewrite translate_trigger, lookup_E_to_exp_E_Local, subevent_subevent.
      rewrite translate_trigger, exp_E_to_instr_E_Local, subevent_subevent.
      unfold interp_cfg_to_L3.
      rewrite interp_intrinsics_trigger.
      cbn; unfold Intrinsics.F_trigger; cbn.
      rewrite interp_global_trigger.
      cbn.
      rewrite interp_local_bind, interp_local_trigger.
      cbn.
      break_match_goal; cbn.
      * rewrite bind_ret_l,interp_local_ret, interp_memory_ret.
        apply eutt_Ret; intuition.
      * unfold raise, Exception.throw.
        rewrite interp_memory_bind, interp_memory_vis, !bind_bind.
        apply eutt_eq_bind; intros [? []].

  - destruct o; cbn; [| apply failure_is_pure].
    destruct d; simpl.
    all: match goal with |- context[raise _] => apply failure_is_pure | _ => idtac end.
    unfold denote_exp, lift_undef_or_err.
    cbn.
    break_match_goal; [apply UB_is_pure |].
    break_match_goal; [apply failure_is_pure|]. 
    rewrite translate_ret, interp_cfg_to_L3_ret; apply eutt_Ret; intuition.

  - destruct o; cbn; [| apply failure_is_pure].
    destruct d; simpl.
    all: match goal with |- context[raise _] => apply failure_is_pure | _ => idtac end.
    rewrite translate_ret, interp_cfg_to_L3_ret; apply eutt_Ret; intuition.

  - destruct o; cbn; [| apply failure_is_pure].
    destruct d; simpl.
    all: match goal with |- context[raise _] => apply failure_is_pure | _ => idtac end.
    rewrite translate_ret, interp_cfg_to_L3_ret; apply eutt_Ret; intuition.

  - destruct o; cbn; [| apply failure_is_pure].
    destruct d; simpl.
    all: match goal with |- context[raise _] => apply failure_is_pure | _ => idtac end.
    rewrite translate_ret, interp_cfg_to_L3_ret; apply eutt_Ret; intuition.
    rewrite translate_ret, interp_cfg_to_L3_ret; apply eutt_Ret; intuition.

  - destruct b; simpl; rewrite translate_ret, interp_cfg_to_L3_ret; apply eutt_Ret; intuition.

  - simpl; rewrite translate_ret, interp_cfg_to_L3_ret; apply eutt_Ret; intuition.

  - destruct o; cbn; [| apply failure_is_pure].
    apply failure_is_pure.

  - apply failure_is_pure.

  - destruct o; cbn; [| apply failure_is_pure].
    rewrite translate_ret, interp_cfg_to_L3_ret; apply eutt_Ret; intuition.

  - rewrite translate_bind, interp_cfg_to_L3_bind.
    rewrite translate_map_monad.
    rewrite interp_cfg_to_L3_map_monad.
    (* eapply eutt_clo_bind. *)
    (* Unshelve. *)


Admitted.

