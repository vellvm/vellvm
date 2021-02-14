From Coq Require Import
     Morphisms.

Require Import List.
Import ListNotations.
Require Import ZArith.
Require Import Coq.micromega.Lia.

From ITree Require Import
     ITree
     Basics.Monad
     Eq.Eq
     TranslateFacts
     Interp.InterpFacts
     Events.State
     Events.StateFacts.

From Vellvm Require Import
     Utils.Tactics
     Utils.Util
     Syntax.LLVMAst
     Syntax.AstLib
     Syntax.DynamicTypes
     Syntax.TypToDtyp
     Semantics.LLVMEvents
     Semantics.DynamicValues
     Semantics.TopLevel
     Handlers.Handlers
     Refinement
     Theory.InterpreterCFG
     Theory.InterpreterCFG
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

  Lemma exp_E_to_instr_E_Pick : forall {X} (e : PickE X),
      exp_E_to_instr_E (subevent X e) = subevent X e.
  Proof.
    reflexivity.
  Qed.

  Lemma exp_E_to_instr_E_UB : forall {X} (e : UBE X),
      exp_E_to_instr_E (subevent X e) = subevent X e.
  Proof.
    reflexivity.
  Qed.

  Lemma exp_E_to_instr_E_Fail : forall {X} (e : FailureE X),
      exp_E_to_instr_E (subevent X e) = subevent X e.
  Proof.
    reflexivity.
  Qed.

  Lemma _failure_UB_to_ExpE_UB : forall {X} (e : UBE X),
      _failure_UB_to_ExpE (subevent X e) = subevent X e.
  Proof.
    reflexivity.
  Qed.

  Lemma _failure_UB_to_ExpE_fail : forall {X} (e : FailureE X),
      _failure_UB_to_ExpE (subevent X e) = subevent X e.
  Proof.
    reflexivity.
  Qed.

End Translations.

Section ExpLemmas.

  Notation "'ℑ'" := interp_cfg_to_L3. 
  Notation "'Θ'" := (translate exp_E_to_instr_E).
  Notation "⟦ e : t ⟧" := (denote_exp t e).
  Notation "⟦ e : t ⟧" := (denote_exp (Some t) e).
  Notation "⟦ e ⟧" := (denote_exp None e).
  Import ITreeNotations.


  Lemma denote_exp_GR :forall g l m id v τ,
      Maps.lookup id g = Some v ->
      interp_cfg_to_L3 (translate exp_E_to_instr_E (denote_exp (Some τ) (EXP_Ident (ID_Global id)))) g l m
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

  Lemma denote_exp_LR :forall g l m id v τ,
      Maps.lookup id l = Some v ->
      interp_cfg_to_L3 (translate exp_E_to_instr_E (denote_exp (Some τ) (EXP_Ident (ID_Local id)))) g l m
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

  Lemma repr_intval (i: int64):
    DynamicValues.Int64.repr (Int64.intval i) = i.
  Proof.
    replace (Int64.intval i) with (Int64.unsigned i).
    -
      apply Int64.repr_unsigned.
    -
      destruct i.
      reflexivity.
  Qed.

  Lemma intval_to_from_nat_id:
    forall n, (Z.of_nat (Z.to_nat (Int64.intval n))) = Int64.intval n.
  Proof.
    intros.
    destruct n.
    cbn.  lia.
  Qed.

  Lemma denote_exp_i64 :forall t g l m,
      interp_cfg_to_L3
        (translate exp_E_to_instr_E
                   (denote_exp (Some (DTYPE_I 64))
                               (EXP_Integer (Integers.Int64.intval t))))
        g l m
        ≈
        Ret (m, (l, (g, UVALUE_I64 t))).
  Proof.
    intros; cbn.
    rewrite translate_ret, interp_cfg_to_L3_ret, repr_intval.
    reflexivity.
  Qed.

  Lemma denote_exp_i64_repr :forall t g l m,
      interp_cfg_to_L3
        (translate exp_E_to_instr_E
                   (denote_exp (Some (DTYPE_I 64))
                               (EXP_Integer t)))
        g l m
        ≈
        Ret (m, (l, (g, UVALUE_I64 (repr t)))).
  Proof.
    intros; unfold denote_exp; cbn.
    rewrite translate_ret, interp_cfg_to_L3_ret.
    reflexivity.
  Qed.

  Lemma denote_exp_double :forall t g l m,
      interp_cfg_to_L3
        (translate exp_E_to_instr_E
                   (denote_exp (Some DTYPE_Double)
                               (EXP_Double t)))
        g l m
        ≈
        Ret (m, (l, (g, UVALUE_Double t))).
  Proof.
    intros; unfold denote_exp; cbn.
    rewrite translate_ret, interp_cfg_to_L3_ret.
    reflexivity.
  Qed.

  Lemma denote_conversion_concrete :
    forall (conv : conversion_type) τ1 τ2 e g ρ m x a av,
      interp_cfg_to_L3 (translate exp_E_to_instr_E (denote_exp (Some τ1) e)) g ρ m
                       ≈
                       Ret (m, (ρ, (g, a)))
      ->
      uvalue_to_dvalue a = inr av ->
      eval_conv conv τ1 av τ2  = ret x ->
      interp_cfg_to_L3
        (translate exp_E_to_instr_E
                   (denote_exp None
                               (OP_Conversion conv τ1 e τ2))) g ρ m ≈ Ret (m, (ρ, (g, (dvalue_to_uvalue x)))).
  Proof.
    intros conv τ1 τ2 e g ρ m x a av A AV EVAL.

    cbn.
    rewrite translate_bind.
    rewrite interp_cfg_to_L3_bind.
    rewrite A.
    rewrite bind_ret_l.

    unfold uvalue_to_dvalue_uop.
    rewrite AV.
    cbn.

    rewrite EVAL.
    unfold ITree.map.
    cbn.
    rewrite bind_ret_l.

    repeat rewrite translate_ret.
    rewrite interp_cfg_to_L3_ret.
    reflexivity.
  Qed.

  Lemma uvalue_to_dvalue_list_concrete :
    forall fields dfields,
      (forall u : uvalue,
          List.In u fields ->
          (exists dv : dvalue, uvalue_to_dvalue u = inr dv) -> is_concrete u) ->
      map_monad uvalue_to_dvalue fields = inr dfields ->
      forallb is_concrete fields = true.
  Proof.
    induction fields; intros dfields H MAP; auto.

    cbn. apply andb_true_intro.
    split.
    - apply H.
      + apply in_eq.
      + inversion MAP.
        destruct (uvalue_to_dvalue a) eqn:Hdv; inversion H1.
        exists d. reflexivity.
    - inversion MAP.
      destruct (uvalue_to_dvalue a) eqn:Hdv; inversion H1.
      destruct (map_monad uvalue_to_dvalue fields) eqn:Hmap; inversion H2.

      assert (forall u : uvalue,
                 In u fields -> (exists dv : dvalue, uvalue_to_dvalue u = inr dv) -> is_concrete u) as BLAH.
      { intros u IN (dv & CONV).
        apply H.
        - cbn. auto.
        - exists dv. auto.
      }

      apply (IHfields l BLAH eq_refl).
  Qed.

  (* TODO: Move this *)
  Lemma uvalue_to_dvalue_is_concrete :
    forall uv dv,
      uvalue_to_dvalue uv = inr dv ->
      is_concrete uv.
  Proof.
    induction uv;
      intros dv CONV; cbn; inversion CONV; auto.
    - break_match; inversion H1.
      eapply uvalue_to_dvalue_list_concrete; eauto.
      intros u IN (dv' & CONV').
      eapply H; eauto.
    - break_match; inversion H1.
      eapply uvalue_to_dvalue_list_concrete; eauto.
      intros u IN (dv' & CONV').
      eapply H; eauto.
    - break_match; inversion H1.
      eapply uvalue_to_dvalue_list_concrete; eauto.
      intros u IN (dv' & CONV').
      eapply H; eauto.
    - break_match; inversion H1.
      eapply uvalue_to_dvalue_list_concrete; eauto.
      intros u IN (dv' & CONV').
      eapply H; eauto.
  Qed.

  Lemma denote_ibinop_concrete :
    forall (op : ibinop) τ e0 e1 g ρ m x a av b bv,
      interp_cfg_to_L3 (translate exp_E_to_instr_E (denote_exp (Some τ) e0)) g ρ m
                       ≈
                       Ret (m, (ρ, (g, a)))
      ->
      interp_cfg_to_L3 (translate exp_E_to_instr_E (denote_exp (Some τ) e1)) g ρ m
                       ≈
                       Ret (m, (ρ, (g, b))) ->
      uvalue_to_dvalue a = inr av ->
      uvalue_to_dvalue b = inr bv ->
      eval_iop op av bv  = ret x ->
      interp_cfg_to_L3
        (translate exp_E_to_instr_E
                   (denote_exp None
                               (OP_IBinop op τ e0 e1))) g ρ m ≈ Ret (m, (ρ, (g, (dvalue_to_uvalue x)))).
  Proof.
    intros * A B AV BV EVAL.

    (* First subexpression *)
    cbn.
    rewrite translate_bind.
    rewrite interp_cfg_to_L3_bind.
    rewrite A.
    rewrite bind_ret_l.

    (* Second subexpression *)
    rewrite translate_bind.
    rewrite interp_cfg_to_L3_bind.
    rewrite B.
    rewrite bind_ret_l.

    pose proof (uvalue_to_dvalue_is_concrete _ _ BV) as CONC.
    rewrite CONC.
    cbn. rewrite Bool.andb_false_r.

    unfold uvalue_to_dvalue_binop.
    rewrite AV, BV.
    cbn.

    rewrite EVAL.
    cbn.

    repeat rewrite translate_ret.
    rewrite interp_cfg_to_L3_ret.
    reflexivity.
  Qed.

  Lemma denote_fbinop_concrete :
    forall (op : fbinop) τ e0 e1 g ρ m x a av b bv params,
      interp_cfg_to_L3 (translate exp_E_to_instr_E (denote_exp (Some τ) e0)) g ρ m
                       ≈ 
                       Ret (m, (ρ, (g, a)))
      ->
      interp_cfg_to_L3 (translate exp_E_to_instr_E (denote_exp (Some τ) e1)) g ρ m
                       ≈
                       Ret (m, (ρ, (g, b)))
      ->
      uvalue_to_dvalue a = inr av ->
      uvalue_to_dvalue b = inr bv ->
      eval_fop op av bv  = ret x ->
      interp_cfg_to_L3
        (translate exp_E_to_instr_E
                   (denote_exp None
                               (OP_FBinop op params τ e0 e1))) g ρ m ≈ Ret (m, (ρ, (g, (dvalue_to_uvalue x)))).
  Proof.
    intros * A B AV BV EVAL.

    (* First subexpression *)
    cbn.
    rewrite translate_bind.
    rewrite interp_cfg_to_L3_bind.
    rewrite A.
    rewrite bind_ret_l.

    (* Second subexpression *)
    rewrite translate_bind.
    rewrite interp_cfg_to_L3_bind.
    rewrite B.
    rewrite bind_ret_l.

    pose proof (uvalue_to_dvalue_is_concrete _ _ BV) as CONC.
    rewrite CONC.
    cbn. rewrite Bool.andb_false_r.

    unfold uvalue_to_dvalue_binop.
    rewrite AV, BV.
    cbn.

    rewrite EVAL.
    cbn.

    repeat rewrite translate_ret.
    rewrite interp_cfg_to_L3_ret.
    reflexivity.
  Qed.

  Lemma denote_fcmp_concrete :
    forall (op : fcmp) τ e0 e1 g ρ m x a av b bv,
      interp_cfg_to_L3 (translate exp_E_to_instr_E (denote_exp (Some τ) e0)) g ρ m
                       ≈
                       Ret (m, (ρ, (g, a)))
      ->
      interp_cfg_to_L3 (translate exp_E_to_instr_E (denote_exp (Some τ) e1)) g ρ m
                       ≈
                       Ret (m, (ρ, (g, b)))
      ->
      uvalue_to_dvalue a = inr av ->
      uvalue_to_dvalue b = inr bv ->
      eval_fcmp op av bv  = ret x ->
      interp_cfg_to_L3
        (translate exp_E_to_instr_E
                   (denote_exp None
                               (OP_FCmp op τ e0 e1))) g ρ m ≈ Ret (m, (ρ, (g, (dvalue_to_uvalue x)))).
  Proof.
    intros * A B AV BV EVAL.

    (* First subexpression *)
    cbn.
    rewrite translate_bind.
    rewrite interp_cfg_to_L3_bind.
    rewrite A.
    rewrite bind_ret_l.

    (* Second subexpression *)
    rewrite translate_bind.
    rewrite interp_cfg_to_L3_bind.
    rewrite B.
    rewrite bind_ret_l.

    unfold uvalue_to_dvalue_binop.
    rewrite AV, BV.
    cbn.

    rewrite EVAL.
    cbn.

    repeat rewrite translate_ret.
    rewrite interp_cfg_to_L3_ret.
    reflexivity.
  Qed.

  Lemma denote_icmp_concrete :
    forall (op : icmp) τ e0 e1 g ρ m x a av b bv,
      interp_cfg_to_L3 (translate exp_E_to_instr_E (denote_exp (Some τ) e0)) g ρ m
                       ≈
                       Ret (m, (ρ, (g, a)))
      ->
      interp_cfg_to_L3 (translate exp_E_to_instr_E (denote_exp (Some τ) e1)) g ρ m
                       ≈
                       Ret (m, (ρ, (g, b)))
      ->
      uvalue_to_dvalue a = inr av ->
      uvalue_to_dvalue b = inr bv ->
      eval_icmp op av bv  = ret x ->
      interp_cfg_to_L3
        (translate exp_E_to_instr_E
                   (denote_exp None
                               (OP_ICmp op τ e0 e1))) g ρ m ≈ Ret (m, (ρ, (g, (dvalue_to_uvalue x)))).
  Proof.
    intros * A B AV BV EVAL.

    (* First subexpression *)
    cbn.
    rewrite translate_bind.
    rewrite interp_cfg_to_L3_bind.
    rewrite A.
    rewrite bind_ret_l.

    (* Second subexpression *)
    rewrite translate_bind.
    rewrite interp_cfg_to_L3_bind.
    rewrite B.
    rewrite bind_ret_l.

    unfold uvalue_to_dvalue_binop.
    rewrite AV, BV.
    cbn.

    rewrite EVAL.
    cbn.

    repeat rewrite translate_ret.
    rewrite interp_cfg_to_L3_ret.
    reflexivity.
  Qed.

  (* TODO MOVE *)
  Definition state_cfg : Type := memory_stack * (local_env * global_env).

  Definition state_cfg_T (T:Type): Type
    := memory_stack * (local_env * (global_env * T)).

  Definition state_cfgP := state_cfg -> Prop.
  Definition state_cfg_TP {T : Type} := state_cfg_T T -> Prop.
  Definition lift_state_cfgP {T : Type} (P : state_cfgP) : @state_cfg_TP T :=
    fun '(m,(l,(g,_))) => P (m,(l,g)).

  Notation "↑" :=  lift_state_cfgP.

  (* Expressions are "almost pure" computations:
   they depend on the memory, but do not modify any component on the state *)

  Definition pure_P g l m : state_cfgP := fun '(m',(l',g')) => m' = m /\ l' = l /\ g' = g.

  Definition pure {E R} (t : global_env -> local_env -> memory_stack -> itree E (memory_stack * (local_env * (global_env * R)))) : Prop :=
    forall g l m, t g l m ⤳ ↑ (pure_P g l m).

  Require Import String.
  Opaque append.

  Lemma failure_is_pure : forall R s,
      pure (R := R) (interp_cfg_to_L3 (translate exp_E_to_instr_E (raise s))).
  Proof.
    unfold pure, raise; intros.
    rewrite translate_bind,translate_trigger, exp_E_to_instr_E_Fail, subevent_subevent, interp_cfg_to_L3_bind.
    unfold interp_cfg_to_L3.
    rewrite interp_intrinsics_trigger.
    cbn.
    unfold Intrinsics.F_trigger; cbn.
    rewrite subevent_subevent.
    rewrite interp_global_trigger; cbn.
    rewrite subevent_subevent.
    rewrite interp_local_bind, interp_local_trigger; cbn.
    rewrite subevent_subevent, bind_bind.
    rewrite interp_memory_bind, interp_memory_trigger; cbn.
    rewrite subevent_subevent, !bind_bind.
    apply has_post_bind; intros [].
  Qed.

  Lemma interp_cfg_to_L3_pick : forall u P m l g,
      interp_cfg_to_L3 (trigger (pick u P)) g l m ≈ v <- trigger (pick u P);; Ret (m,(l,(g,v))).
  Proof.
    intros.
    unfold interp_cfg_to_L3.
    rewrite interp_intrinsics_trigger.
    cbn.
    unfold Intrinsics.F_trigger; cbn.
    rewrite subevent_subevent.
    rewrite interp_global_trigger; cbn.
    rewrite subevent_subevent.
    rewrite interp_local_bind, interp_local_trigger; cbn.
    rewrite subevent_subevent, bind_bind.
    rewrite interp_memory_bind, interp_memory_trigger; cbn.
    rewrite subevent_subevent, bind_bind.
    apply eutt_eq_bind; intros.
    rewrite bind_ret_l.
    rewrite interp_memory_bind, interp_memory_ret, bind_ret_l; cbn.
    rewrite interp_local_ret, interp_memory_ret.
    reflexivity.
  Qed.

  Lemma interp_cfg_to_L3_UB : forall s m l g,
      interp_cfg_to_L3 (trigger (ThrowUB s)) g l m ≈ v <- trigger (ThrowUB s);; Ret (m,(l,(g,v))).
  Proof.
    intros.
    unfold interp_cfg_to_L3.
    rewrite interp_intrinsics_trigger.
    cbn.
    unfold Intrinsics.F_trigger; cbn.
    rewrite subevent_subevent.
    rewrite interp_global_trigger; cbn.
    rewrite subevent_subevent.
    rewrite interp_local_bind, interp_local_trigger; cbn.
    rewrite subevent_subevent, bind_bind.
    rewrite interp_memory_bind, interp_memory_trigger; cbn.
    rewrite subevent_subevent, bind_bind.
    apply eutt_eq_bind; intros.
    rewrite bind_ret_l.
    rewrite interp_memory_bind, interp_memory_ret, bind_ret_l; cbn.
    rewrite interp_local_ret, interp_memory_ret.
    reflexivity.
  Qed.

  Lemma pick_is_pure : forall u P, pure (ℑ (Θ (trigger (pick u P)))).
  Proof.
    intros.
    unfold pure; intros. 
    rewrite translate_trigger.
    rewrite exp_E_to_instr_E_Pick, subevent_subevent.
    rewrite interp_cfg_to_L3_pick.
    apply has_post_bind.
    intros ?; apply eutt_Ret; cbn; auto.
  Qed.

  Lemma concretize_or_pick_is_pure : forall v P, pure (ℑ (Θ (concretize_or_pick v P))).
  Proof.
    intros.
    unfold pure; intros.
    unfold concretize_or_pick.
    break_match_goal; [| apply pick_is_pure].
    unfold lift_err.
    break_match_goal; [apply failure_is_pure |].
    cbn.
    rewrite !translate_ret, interp_cfg_to_L3_ret.
    apply eutt_Ret; cbn; auto.
  Qed.

  Lemma UB_is_pure : forall R s,
      pure (R := R) (interp_cfg_to_L3 (translate exp_E_to_instr_E (raiseUB s))).
  Proof.
    unfold pure, raiseUB; intros.
    rewrite translate_bind, translate_trigger, exp_E_to_instr_E_UB, subevent_subevent.
    rewrite interp_cfg_to_L3_bind, interp_cfg_to_L3_UB.
    apply has_post_bind.
    intros (? & ? & ? & []).
  Qed.

  Lemma translate_raiseUB : forall T s,
      translate _failure_UB_to_ExpE (raiseUB (X := T) s) ≈ raiseUB s.
  Proof.
    intros.
    unfold raiseUB; rewrite translate_bind, translate_trigger, _failure_UB_to_ExpE_UB, subevent_subevent.
    apply eutt_eq_bind; intros [].
  Qed.

  Lemma translate_raise : forall T s,
      translate _failure_UB_to_ExpE (raise (A := T) s) ≈ raise s. Proof.
                                                                    intros.
                                                                    unfold raise; rewrite translate_bind, translate_trigger, _failure_UB_to_ExpE_fail, subevent_subevent.
                                                                    apply eutt_eq_bind; intros [].
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

  Lemma interp_cfg_to_L3_map_monad {A B} g l m (xs : list A) (ts : A -> itree _ B) : 
    interp_cfg_to_L3 (map_monad ts xs) g l m ≈
                     map_monad (m := Monads.stateT _ (Monads.stateT _ (Monads.stateT _ (itree _))))
                     (fun a => interp_cfg_to_L3 (ts a)) xs g l m.
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
      (forall a s, In a l -> I s -> (f a s) ⤳ fun '(s,_) => I s) ->
      I s ->
      map_monad f l s ⤳ fun '(s,_) => I s.
  Proof.
    induction l as [| a l IH]; intros s HB HI; simpl.
    - apply eutt_Ret; auto.
    - setoid_rewrite has_post_post_strong in HB.
      eapply eutt_clo_bind; [apply HB; cbn; auto |].
      intros [s' ?] [] [EQ ?]; inv EQ.
      simpl.
      setoid_rewrite has_post_post_strong in IH.
      eapply eutt_clo_bind; [apply IH |]; auto.
      intros; apply HB; cbn; auto. 
      intros [s' ?] [] [EQ ?]; inv EQ; cbn; apply eutt_Ret; auto. 
  Qed.

  Lemma map_monad_eutt_state2_ind :
    forall {E S1 S2 A B} (I : S1 -> S2 -> Prop)
           (f : A -> Monads.stateT S1 (Monads.stateT S2 (itree E)) B)
           (l : list A) (s1 : S1) (s2 : S2), 
      (forall a s1 s2, In a l -> I s1 s2 -> (f a s1 s2) ⤳ fun '(s2',(s1',_)) => I s1' s2') ->
      I s1 s2 ->
      map_monad f l s1 s2 ⤳ fun '(s2',(s1',_)) => I s1' s2'.
  Proof.
    induction l as [| a l IH]; intros s1 s2 HB HI; simpl.
    - apply eutt_Ret; auto.
    - setoid_rewrite has_post_post_strong in HB.
      eapply eutt_clo_bind; [apply HB; cbn; auto |].
      intros (s2' & s1' & ?) (? & ? & ?) [EQ ?]; inv EQ.
      simpl.
      setoid_rewrite has_post_post_strong in IH.
      eapply eutt_clo_bind; [apply IH |]; auto.
      intros; apply HB; cbn; auto.
      intros (s1' & s2' & ?) (? & ? & ?) [EQ ?]; inv EQ; cbn; apply eutt_Ret; auto. 
  Qed.

  Lemma map_monad_eutt_state3_ind :
    forall {E S1 S2 S3 A B} (I : S1 -> S2 -> S3 -> Prop)
           (f : A -> Monads.stateT S1 (Monads.stateT S2 (Monads.stateT S3 (itree E))) B)
           (l : list A) (s1 : S1) (s2 : S2) (s3 : S3), 
      (forall a s1 s2 s3, In a l -> I s1 s2 s3 -> (f a s1 s2 s3) ⤳ fun '(s3', (s2',(s1',_))) => I s1' s2' s3') ->
      I s1 s2 s3 ->
      map_monad f l s1 s2 s3 ⤳ fun '(s3', (s2',(s1',_))) => I s1' s2' s3'.
  Proof.
    induction l as [| a l IH]; intros s1 s2 s3 HB HI; simpl.
    - apply eutt_Ret; auto.
    - setoid_rewrite has_post_post_strong in HB.
      eapply eutt_clo_bind; [apply HB; cbn; auto |].
      intros (s3' & s2' & s1' & ?) (? & ? & ? & ?) [EQ ?]; inv EQ.
      simpl.
      setoid_rewrite has_post_post_strong in IH.
      eapply eutt_clo_bind; [apply IH |]; auto.
      intros; apply HB; cbn; auto.
      intros (s1' & s2' & s3' & ?) (? & ? & ? & ?) [EQ ?]; inv EQ; cbn; apply eutt_Ret; auto. 
  Qed.

  Lemma interp_cfg_to_L3_GR_fail : forall id g l m,
      Maps.lookup id g = None ->
      interp_cfg_to_L3 (trigger (GlobalRead id)) g l m ≈
                       raise ("Could not look up global id " ++ CeresSerialize.to_string id).
  Proof.
    intros * LU.
    unfold interp_cfg_to_L3.
    rewrite interp_intrinsics_trigger.
    cbn.
    unfold Intrinsics.F_trigger; cbn; rewrite subevent_subevent.
    rewrite interp_global_trigger. 
    cbn in *; rewrite LU.
    unfold raise; cbn.
    rewrite interp_local_bind, interp_local_trigger; cbn; rewrite subevent_subevent, bind_bind.
    rewrite interp_memory_bind, interp_memory_trigger; cbn; rewrite subevent_subevent, bind_bind.
    apply eutt_eq_bind; intros [].
  Qed.

  Lemma interp_cfg_to_L3_LR_fail : forall id g l m,
      Maps.lookup id l = None ->
      interp_cfg_to_L3 (trigger (LocalRead id)) g l m ≈
                       raise ("Could not look up id " ++ CeresSerialize.to_string id).
  Proof.
    intros * LU.
    unfold interp_cfg_to_L3.
    rewrite interp_intrinsics_trigger.
    cbn.
    unfold Intrinsics.F_trigger; cbn; rewrite subevent_subevent.
    rewrite interp_global_trigger. 
    cbn in *; rewrite subevent_subevent.
    rewrite interp_local_bind, interp_local_trigger.
    cbn; rewrite LU.
    unfold raise; cbn; rewrite bind_bind.
    rewrite interp_memory_bind, interp_memory_trigger; cbn; rewrite subevent_subevent, bind_bind.
    apply eutt_eq_bind; intros [].
  Qed.

  Lemma expr_are_pure : forall o e, pure (interp_cfg_to_L3 (translate exp_E_to_instr_E (denote_exp o e))).
  Proof.
    intros; unfold pure.
    revert o; induction e; simpl; intros.

    - destruct id; cbn.
      + rewrite translate_bind, translate_trigger, lookup_E_to_exp_E_Global, subevent_subevent.
        rewrite translate_bind, translate_trigger, exp_E_to_instr_E_Global, subevent_subevent.
        destruct (Maps.lookup id g) eqn:EQ.
        * rewrite interp_cfg_to_L3_bind, interp_cfg_to_L3_GR; eauto.
          rewrite bind_ret_l, !translate_ret, interp_cfg_to_L3_ret.
          apply eutt_Ret; cbn; auto.
        * rewrite interp_cfg_to_L3_bind, interp_cfg_to_L3_GR_fail; auto.
          unfold raise; rewrite bind_bind.
          apply has_post_bind; intros [].
          
      + rewrite translate_trigger, lookup_E_to_exp_E_Local, subevent_subevent.
        destruct (Maps.lookup id l) eqn:EQ.
        * rewrite translate_trigger, exp_E_to_instr_E_Local, subevent_subevent, interp_cfg_to_L3_LR; eauto.
          apply eutt_Ret; cbn; auto.
        * rewrite translate_trigger, exp_E_to_instr_E_Local, subevent_subevent, interp_cfg_to_L3_LR_fail; auto. 
          unfold raise.
          apply has_post_bind; intros [].

    - destruct o; cbn; [| apply failure_is_pure].
      destruct d; simpl.
      all: match goal with |- context[raise _] => apply failure_is_pure | _ => idtac end.
      unfold denote_exp, lift_undef_or_err.
      cbn.
      break_match_goal; [apply UB_is_pure |].
      break_match_goal; [apply failure_is_pure|]. 
      rewrite translate_ret, interp_cfg_to_L3_ret; apply eutt_Ret; cbn; intuition.

    - destruct o; cbn; [| apply failure_is_pure].
      destruct d; simpl.
      all: match goal with |- context[raise _] => apply failure_is_pure | _ => idtac end.
      rewrite translate_ret, interp_cfg_to_L3_ret; apply eutt_Ret; cbn; intuition.

    - destruct o; cbn; [| apply failure_is_pure].
      destruct d; simpl.
      all: match goal with |- context[raise _] => apply failure_is_pure | _ => idtac end.
      rewrite translate_ret, interp_cfg_to_L3_ret; apply eutt_Ret; cbn; intuition.

    - destruct o; cbn; [| apply failure_is_pure].
      destruct d; simpl.
      all: match goal with |- context[raise _] => apply failure_is_pure | _ => idtac end.
      rewrite translate_ret, interp_cfg_to_L3_ret; apply eutt_Ret; cbn; intuition.
      rewrite translate_ret, interp_cfg_to_L3_ret; apply eutt_Ret; cbn; intuition.

    - destruct b; simpl; rewrite translate_ret, interp_cfg_to_L3_ret; apply eutt_Ret; cbn; intuition.

    - simpl; rewrite translate_ret, interp_cfg_to_L3_ret; apply eutt_Ret; cbn; intuition.

    - destruct o; cbn; [| apply failure_is_pure].
      apply failure_is_pure.

    - rewrite translate_bind, interp_cfg_to_L3_bind.
      rewrite translate_map_monad.
      rewrite interp_cfg_to_L3_map_monad.
      apply has_post_bind_strong with (S := ↑ (pure_P g l m)).
      + eapply has_post_weaken.
        apply (map_monad_eutt_state3_ind (fun g' l' m' => pure_P g l m (m',(l',g')))); [| cbn; intuition].
        * intros * IN (-> & -> & ->).
          destruct a; simpl in *.
          apply has_post_weaken with (↑ (pure_P g l m)).
          apply (H _ IN).
          intros (? & ? & ? & ?) (-> & -> & ->); auto.
        * intros (? & ? & ? & ?) (-> & -> & ->); cbn; auto.
      + intros (? & ? & ? & ?) (-> & -> & ->).
        simpl; rewrite translate_ret, interp_cfg_to_L3_ret; apply eutt_Ret; cbn; intuition.

    - destruct o; cbn; [| apply failure_is_pure].
      rewrite translate_ret, interp_cfg_to_L3_ret; apply eutt_Ret; cbn; intuition.

    - rewrite translate_bind, interp_cfg_to_L3_bind.
      rewrite translate_map_monad.
      rewrite interp_cfg_to_L3_map_monad.
      apply has_post_bind_strong with (S := ↑ (pure_P g l m)).
      + eapply has_post_weaken.
        apply (map_monad_eutt_state3_ind (fun g' l' m' => pure_P g l m (m',(l',g')))); [| cbn; intuition].
        * intros * IN (-> & -> & ->).
          destruct a; simpl in *.
          apply has_post_weaken with (↑ (pure_P g l m)).
          apply (H _ IN).
          intros (? & ? & ? & ?) (-> & -> & ->); auto.
        * intros (? & ? & ? & ?) (-> & -> & ->); cbn; auto.
      + intros (? & ? & ? & ?) (-> & -> & ->).
        simpl; rewrite translate_ret, interp_cfg_to_L3_ret; apply eutt_Ret; cbn; intuition.

    - destruct o; cbn; [| apply failure_is_pure].
      destruct d;
        match goal with
          |- context[denote_exp (Some (DTYPE_Packed_struct _))] => idtac 
        | _ => apply failure_is_pure
        end.
      simpl.
      rewrite translate_bind, interp_cfg_to_L3_bind.
      rewrite translate_map_monad.
      rewrite interp_cfg_to_L3_map_monad.
      apply has_post_bind_strong with (S := ↑ (pure_P g l m)).
      + eapply has_post_weaken.
        apply (map_monad_eutt_state3_ind (fun g' l' m' => pure_P g l m (m',(l',g')))); [| cbn; intuition].
        * intros * IN (-> & -> & ->).
          destruct a; simpl in *.
          apply has_post_weaken with (↑ (pure_P g l m)).
          apply (H _ IN).
          intros (? & ? & ? & ?) (-> & -> & ->); auto.
        * intros (? & ? & ? & ?) (-> & -> & ->); cbn; auto.
      + intros (? & ? & ? & ?) (-> & -> & ->).
        simpl; rewrite translate_ret, interp_cfg_to_L3_ret; apply eutt_Ret; cbn; intuition.


    - rewrite translate_bind, interp_cfg_to_L3_bind.
      rewrite translate_map_monad.
      rewrite interp_cfg_to_L3_map_monad.
      apply has_post_bind_strong with (S := ↑ (pure_P g l m)).
      + eapply has_post_weaken.
        apply (map_monad_eutt_state3_ind (fun g' l' m' => pure_P g l m (m',(l',g')))); [| cbn; intuition].
        * intros * IN (-> & -> & ->).
          destruct a; simpl in *.
          apply has_post_weaken with (↑ (pure_P g l m)).
          apply (H _ IN).
          intros (? & ? & ? & ?) (-> & -> & ->); auto.
        * intros (? & ? & ? & ?) (-> & -> & ->); cbn; auto.
      + intros (? & ? & ? & ?) (-> & -> & ->).
        simpl; rewrite translate_ret, interp_cfg_to_L3_ret; apply eutt_Ret; cbn; intuition.

    - rewrite translate_bind, interp_cfg_to_L3_bind.
      rewrite translate_map_monad.
      rewrite interp_cfg_to_L3_map_monad.
      apply has_post_bind_strong with (S := ↑ (pure_P g l m)).
      + eapply has_post_weaken.
        apply (map_monad_eutt_state3_ind (fun g' l' m' => pure_P g l m (m',(l',g')))); [| cbn; intuition].
        * intros * IN (-> & -> & ->).
          destruct a; simpl in *.
          apply has_post_weaken with (↑ (pure_P g l m)).
          apply (H _ IN).
          intros (? & ? & ? & ?) (-> & -> & ->); auto.
        * intros (? & ? & ? & ?) (-> & -> & ->); cbn; auto.
      + intros (? & ? & ? & ?) (-> & -> & ->).
        simpl; rewrite translate_ret, interp_cfg_to_L3_ret; apply eutt_Ret; cbn; intuition.

    - rewrite translate_bind, interp_cfg_to_L3_bind.
      eapply has_post_bind_strong.
      apply (IHe1 (Some t) g l m).
      intros (? & ? & ? & ?) (-> & -> & ->).
      rewrite translate_bind, interp_cfg_to_L3_bind.
      eapply has_post_bind_strong.
      apply (IHe2 (Some t) g l m).
      intros (? & ? & ? & ?) (-> & -> & ->).
      break_match_goal.
      + rewrite translate_bind, interp_cfg_to_L3_bind.
        apply has_post_bind_strong with (↑ (pure_P g l m)).
        * unfold concretize_or_pick.
          break_match_goal.
          cbn.
          {
            unfold lift_err.
            break_match_goal.
            apply failure_is_pure.
            rewrite translate_ret, interp_cfg_to_L3_ret.
            apply eutt_Ret; cbn; auto.
          }
          apply pick_is_pure.

        * intros (? & ? & ? & ?) (-> & -> & ->).
          unfold uvalue_to_dvalue_binop2.
          cbn; break_match_goal.
          rewrite translate_ret, interp_cfg_to_L3_ret.
          apply eutt_Ret; cbn; auto.
          break_match_hyp; inv_sum.
          break_match_goal.
          rewrite translate_raiseUB; apply UB_is_pure.
          break_match_goal.
          rewrite translate_raise; apply failure_is_pure.
          rewrite !translate_ret, interp_cfg_to_L3_ret.
          apply eutt_Ret; cbn; auto.

      + unfold uvalue_to_dvalue_binop.
        cbn.
        break_match_goal.
        rewrite !translate_ret, interp_cfg_to_L3_ret.
        apply eutt_Ret; cbn; auto.
        break_match_hyp; try inv_sum.
        break_match_hyp; try inv_sum.
        break_match_goal.
        rewrite translate_raiseUB; apply UB_is_pure.
        break_match_goal.
        rewrite translate_raise; apply failure_is_pure.
        rewrite !translate_ret, interp_cfg_to_L3_ret.
        apply eutt_Ret; cbn; auto.

    - rewrite translate_bind, interp_cfg_to_L3_bind.
      eapply has_post_bind_strong.
      apply (IHe1 (Some t) g l m).
      intros (? & ? & ? & ?) (-> & -> & ->).
      rewrite translate_bind, interp_cfg_to_L3_bind.
      eapply has_post_bind_strong.
      apply (IHe2 (Some t) g l m).
      intros (? & ? & ? & ?) (-> & -> & ->).
      unfold uvalue_to_dvalue_binop.
      cbn.
      break_match_goal.
      rewrite !translate_ret, interp_cfg_to_L3_ret.
      apply eutt_Ret; cbn; auto.
      break_match_hyp; try inv_sum.
      break_match_hyp; try inv_sum.
      break_match_goal.
      apply UB_is_pure.
      break_match_goal.
      apply failure_is_pure.
      rewrite !translate_ret, interp_cfg_to_L3_ret.
      apply eutt_Ret; cbn; auto.

    - rewrite translate_bind, interp_cfg_to_L3_bind.
      eapply has_post_bind_strong.
      apply (IHe1 (Some t) g l m).
      intros (? & ? & ? & ?) (-> & -> & ->).
      rewrite translate_bind, interp_cfg_to_L3_bind.
      eapply has_post_bind_strong.
      apply (IHe2 (Some t) g l m).
      intros (? & ? & ? & ?) (-> & -> & ->).
      break_match_goal.
      + rewrite translate_bind, interp_cfg_to_L3_bind.
        apply has_post_bind_strong with (↑ (pure_P g l m)).
        * unfold concretize_or_pick.
          break_match_goal.
          cbn.
          {
            unfold lift_err.
            break_match_goal.
            apply failure_is_pure.
            rewrite translate_ret, interp_cfg_to_L3_ret.
            apply eutt_Ret; cbn; auto.
          }
          apply pick_is_pure.

        * intros (? & ? & ? & ?) (-> & -> & ->).
          unfold uvalue_to_dvalue_binop2.
          cbn; break_match_goal.
          rewrite translate_ret, interp_cfg_to_L3_ret.
          apply eutt_Ret; cbn; auto.
          break_match_hyp; inv_sum.
          break_match_goal.
          rewrite translate_raiseUB; apply UB_is_pure.
          break_match_goal.
          rewrite translate_raise; apply failure_is_pure.
          rewrite !translate_ret, interp_cfg_to_L3_ret.
          apply eutt_Ret; cbn; auto.

      + unfold uvalue_to_dvalue_binop.
        cbn.
        break_match_goal.
        rewrite !translate_ret, interp_cfg_to_L3_ret.
        apply eutt_Ret; cbn; auto.
        break_match_hyp; try inv_sum.
        break_match_hyp; try inv_sum.
        break_match_goal.
        rewrite translate_raiseUB; apply UB_is_pure.
        break_match_goal.
        rewrite translate_raise; apply failure_is_pure.
        rewrite !translate_ret, interp_cfg_to_L3_ret.
        apply eutt_Ret; cbn; auto.

    - rewrite translate_bind, interp_cfg_to_L3_bind.
      eapply has_post_bind_strong.
      apply (IHe1 (Some t) g l m).
      intros (? & ? & ? & ?) (-> & -> & ->).
      rewrite translate_bind, interp_cfg_to_L3_bind.
      eapply has_post_bind_strong.
      apply (IHe2 (Some t) g l m).
      intros (? & ? & ? & ?) (-> & -> & ->).
      unfold uvalue_to_dvalue_binop.
      cbn.
      break_match_goal.
      rewrite !translate_ret, interp_cfg_to_L3_ret.
      apply eutt_Ret; cbn; auto.
      break_match_hyp; try inv_sum.
      break_match_hyp; try inv_sum.
      break_match_goal.
      apply UB_is_pure.
      break_match_goal.
      apply failure_is_pure.
      rewrite !translate_ret, interp_cfg_to_L3_ret.
      apply eutt_Ret; cbn; auto.

    - rewrite translate_bind, interp_cfg_to_L3_bind.
      eapply has_post_bind_strong.
      apply (IHe (Some t_from) g l m).
      intros (? & ? & ? & ?) (-> & -> & ->).
      unfold uvalue_to_dvalue_uop; cbn.
      break_match_goal.
      rewrite !translate_ret, interp_cfg_to_L3_ret.
      apply eutt_Ret; cbn; auto.
      break_match_hyp; try inv_sum.
      unfold ITree.map.
      rewrite !translate_bind, interp_cfg_to_L3_bind.
      apply has_post_bind_strong with (↑ (pure_P g l m)).
      + (* What's the right way to reason about eval_conv? *)
        admit.
      + intros (? & ? & ? & ?) (-> & -> & ->).
        rewrite !translate_ret, interp_cfg_to_L3_ret.
        apply eutt_Ret; cbn; auto.

    - destruct ptrval; cbn.
      rewrite translate_bind, interp_cfg_to_L3_bind.
      eapply has_post_bind_strong.
      apply (IHe (Some d) g l m).
      intros (? & ? & ? & ?) (-> & -> & ->).
      rewrite translate_bind, interp_cfg_to_L3_bind.
      rewrite translate_map_monad.
      rewrite interp_cfg_to_L3_map_monad.
      apply has_post_bind_strong with (S := ↑ (pure_P g l m)).
      + eapply has_post_weaken.
        apply (map_monad_eutt_state3_ind (fun g' l' m' => pure_P g l m (m',(l',g')))); [| cbn; intuition].
        * intros * IN (-> & -> & ->).
          destruct a; simpl in *.
          apply has_post_weaken with (↑ (pure_P g l m)).
          apply (H _ IN).
          intros (? & ? & ? & ?) (-> & -> & ->); auto.
        * intros (? & ? & ? & ?) (-> & -> & ->); cbn; auto.
      + intros (? & ? & ? & ?) (-> & -> & ->).
        break_match_goal.
        * rewrite translate_bind, interp_cfg_to_L3_bind.
          unfold concretize_or_pick.
          apply has_post_bind_strong with (↑ (pure_P g l m)).
          {
            break_match_goal.
            unfold lift_err.
            break_match_goal.
            apply failure_is_pure.
            cbn; rewrite translate_ret, interp_cfg_to_L3_ret; apply eutt_Ret; cbn; auto.
            apply pick_is_pure.
          }
          intros (? & ? & ? & ?) (-> & -> & ->).
          rewrite translate_bind, interp_cfg_to_L3_bind.
          rewrite translate_map_monad.
          rewrite interp_cfg_to_L3_map_monad.
          apply has_post_bind_strong with (S := ↑ (pure_P g l m)).
          { eapply has_post_weaken.
            apply (map_monad_eutt_state3_ind (fun g' l' m' => pure_P g l m (m',(l',g')))); [| cbn; intuition].
            * intros * IN (-> & -> & ->).
              break_match_goal.
              unfold lift_err.
              break_match_goal.
              apply failure_is_pure.
              cbn; rewrite translate_ret, interp_cfg_to_L3_ret; apply eutt_Ret; cbn; auto.
              apply pick_is_pure.
            * intros (? & ? & ? & ?) (-> & -> & ->); cbn; auto.
          }
          intros (? & ? & ? & ?) (-> & -> & ->); cbn; auto.
          unfold ITree.map. rewrite translate_bind, interp_cfg_to_L3_bind.
          rewrite translate_trigger, exp_E_to_instr_E_Memory, subevent_subevent.
          (* GEP... *)
          unfold interp_cfg_to_L3.
          rewrite interp_intrinsics_trigger.
          cbn.
          unfold Intrinsics.F_trigger; cbn.
          rewrite subevent_subevent.
          rewrite interp_global_trigger; cbn.
          rewrite subevent_subevent.
          rewrite interp_local_bind, interp_local_trigger; cbn.
          rewrite subevent_subevent, bind_bind.
          rewrite interp_memory_bind, interp_memory_trigger; cbn.
          rewrite !bind_bind.
          destruct d0; cbn; try (unfold raise; rewrite bind_bind; apply has_post_bind; intros []).
          break_match_goal; cbn; try (unfold raise; rewrite bind_bind; apply has_post_bind; intros []).
          rewrite !bind_ret_l.
          rewrite interp_local_ret, interp_memory_ret, bind_ret_l.
          rewrite translate_ret, interp_intrinsics_ret, interp_global_ret, interp_local_ret, interp_memory_ret. 
          apply eutt_Ret; cbn; auto.

        * unfold ITree.map; destruct p; cbn.
          rewrite translate_bind, interp_cfg_to_L3_bind.
          rewrite translate_trigger, exp_E_to_instr_E_Memory, subevent_subevent.
          (* GEP... *)
          unfold interp_cfg_to_L3.
          rewrite interp_intrinsics_trigger.
          cbn.
          unfold Intrinsics.F_trigger; cbn.
          rewrite subevent_subevent.
          rewrite interp_global_trigger; cbn.
          rewrite subevent_subevent.
          rewrite interp_local_bind, interp_local_trigger; cbn.
          rewrite subevent_subevent, bind_bind.
          rewrite interp_memory_bind, interp_memory_trigger; cbn.
          rewrite !bind_bind.
          destruct d0; cbn; try (unfold raise; rewrite bind_bind; apply has_post_bind; intros []).
          break_match_goal; cbn; try (unfold raise; rewrite bind_bind; apply has_post_bind; intros []).
          rewrite !bind_ret_l.
          rewrite interp_local_ret, interp_memory_ret, bind_ret_l.
          rewrite translate_ret, interp_intrinsics_ret, interp_global_ret, interp_local_ret, interp_memory_ret. 
          apply eutt_Ret; cbn; auto.

    - apply failure_is_pure.

    - apply failure_is_pure.

    - apply failure_is_pure.

    - destruct vec; cbn.
      rewrite translate_bind, interp_cfg_to_L3_bind.
      eapply has_post_bind_strong.
      apply (IHe (Some d) g l m).
      intros (? & ? & ? & ?) (-> & -> & ->).
      clear IHe.
      induction idxs as [| n idxs IH].
      + cbn.
        rewrite !translate_ret, interp_cfg_to_L3_ret.
        apply eutt_Ret; cbn; auto.
      + cbn.
        break_match_goal.
        apply UB_is_pure.
        break_match_goal.
        apply failure_is_pure.
        rewrite !translate_ret, interp_cfg_to_L3_ret.
        apply eutt_Ret; cbn; auto.
        
    - apply failure_is_pure.

    - destruct cnd,v1,v2; cbn.
      rewrite translate_bind, interp_cfg_to_L3_bind.
      eapply has_post_bind_strong; [apply IHe | ].
      intros (? & ? & ? & ?) (-> & -> & ->).
      rewrite translate_bind, interp_cfg_to_L3_bind.
      eapply has_post_bind_strong; [apply IHe0 |]. 
      intros (? & ? & ? & ?) (-> & -> & ->).
      rewrite translate_bind, interp_cfg_to_L3_bind.
      eapply has_post_bind_strong; [apply IHe1 |]. 
      intros (? & ? & ? & ?) (-> & -> & ->).
      break_match_goal.
      rewrite !translate_ret, interp_cfg_to_L3_ret.
      apply eutt_Ret; cbn; auto.
      unfold lift_undef_or_err.
      break_match_goal.
      break_match_goal.
      apply UB_is_pure.
      break_match_goal.
      apply failure_is_pure.
      rewrite !translate_ret, interp_cfg_to_L3_ret.
      apply eutt_Ret; cbn; auto.
      
    - destruct v; cbn.
      rewrite translate_bind, interp_cfg_to_L3_bind.
      eapply has_post_bind_strong.
      apply (IHe (Some d) g l m).
      intros (? & ? & ? & ?) (-> & -> & ->).
      clear IHe.
      rewrite translate_bind, interp_cfg_to_L3_bind.
      apply has_post_bind_strong with (↑ (pure_P g l m)).
      { unfold pick_your_poison;
          break_match_goal; cbn;
            match goal with
              |- context [Ret _] => rewrite !translate_ret, interp_cfg_to_L3_ret; apply eutt_Ret; cbn; auto
            | |- context [pick] => apply pick_is_pure
            | |- context [concretize_or_pick] => apply concretize_or_pick_is_pure
            end.
      }
      intros (? & ? & ? & ?) (-> & -> & ->).
      rewrite !translate_ret, interp_cfg_to_L3_ret.
      apply eutt_Ret; cbn; auto.
      
  Admitted.

End ExpLemmas.
