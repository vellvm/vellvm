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

Lemma denote_exp_i64 :forall defs t g l m,
    interp_cfg_to_L3 defs
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

Lemma denote_exp_i64_repr :forall defs t g l m,
    interp_cfg_to_L3 defs
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

Lemma denote_exp_double :forall defs t g l m,
    interp_cfg_to_L3 defs
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
  forall (conv : conversion_type) τ1 τ2 e g ρ m x a av defs,
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some τ1) e)) g ρ m
    ≈
    Ret (m, (ρ, (g, a)))
    ->
    uvalue_to_dvalue a = inr av ->
    eval_conv conv τ1 av τ2  = ret x ->
    interp_cfg_to_L3 defs
   (translate exp_E_to_instr_E
      (denote_exp None
         (OP_Conversion conv τ1 e τ2))) g ρ m ≈ Ret (m, (ρ, (g, (dvalue_to_uvalue x)))).
Proof.
  intros conv τ1 τ2 e g ρ m x a av defs A AV EVAL.

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
  forall (op : ibinop) τ e0 e1 g ρ m x a av b bv defs,
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some τ) e0)) g ρ m
    ≈
    Ret (m, (ρ, (g, a)))
    ->
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some τ) e1)) g ρ m
    ≈
    Ret (m, (ρ, (g, b))) ->
    uvalue_to_dvalue a = inr av ->
    uvalue_to_dvalue b = inr bv ->
    eval_iop op av bv  = ret x ->
    interp_cfg_to_L3 defs
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
  forall (op : fbinop) τ e0 e1 g ρ m x a av b bv defs params,
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some τ) e0)) g ρ m
    ≈ 
    Ret (m, (ρ, (g, a)))
    ->
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some τ) e1)) g ρ m
    ≈
    Ret (m, (ρ, (g, b)))
    ->
    uvalue_to_dvalue a = inr av ->
    uvalue_to_dvalue b = inr bv ->
    eval_fop op av bv  = ret x ->
   interp_cfg_to_L3 defs
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
  forall (op : fcmp) τ e0 e1 g ρ m x a av b bv defs,
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some τ) e0)) g ρ m
    ≈
    Ret (m, (ρ, (g, a)))
    ->
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some τ) e1)) g ρ m
    ≈
    Ret (m, (ρ, (g, b)))
    ->
    uvalue_to_dvalue a = inr av ->
    uvalue_to_dvalue b = inr bv ->
    eval_fcmp op av bv  = ret x ->
    interp_cfg_to_L3 defs
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
  forall (op : icmp) τ e0 e1 g ρ m x a av b bv defs,
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some τ) e0)) g ρ m
    ≈
    Ret (m, (ρ, (g, a)))
    ->
    interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some τ) e1)) g ρ m
    ≈
    Ret (m, (ρ, (g, b)))
    ->
    uvalue_to_dvalue a = inr av ->
    uvalue_to_dvalue b = inr bv ->
    eval_icmp op av bv  = ret x ->
    interp_cfg_to_L3 defs
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

(* Expressions are "almost pure" computations:
   they depend on the memory, but do not modify any component on the state *)

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

