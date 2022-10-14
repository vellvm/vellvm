(* begin hide *)
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
     Utilities
     Syntax
     Semantics
     Theory.StatePredicates
     Theory.Refinement
     Theory.InterpreterCFG
     Utils.PostConditions.

Open Scope itree_scope.
Import ITreeNotations.

(* end hide *)

(** * Lemmas related to the semantics of expressions
  This file contains essentially:
  - Proof rules specifying the behavior of expressions, allowing for symbolic execution in refinement proofs.
  - A proof that expressions that do not perform conversion are "pure", i.e. do not modify any part of the state.
 *)
Module ExpLemmas (IS : InterpreterStack) (TOP : LLVMTopLevel IS).
  Module CFGT := CFGTheory IS TOP.

  Export CFGT.
  Export TOP.
  Export IS.
  Export IS.LLVM.

  Module CFGL := CFG_LEVEL LP LLVM.
  Export CFGL.

  Import SemNotations.

  Section Translations.

    (* Technicality: translations by [lookup_E_to_exp_E] and [exp_E_to_instr_E] leave these events unphased *)

    Lemma LU_to_exp_Global : forall {X} (e : LLVMGEnvE X),
        subevent X (LU_to_exp (subevent X e)) = subevent X e.
    Proof.
      reflexivity.
    Qed.

    Lemma exp_to_instr_Global : forall {X} (e : LLVMGEnvE X),
        subevent X (exp_to_instr (subevent X e)) = subevent X e.
    Proof.
      reflexivity.
    Qed.

    Lemma LU_to_exp_Local : forall {X} (e : LLVMEnvE X),
        subevent X (LU_to_exp (subevent X e)) = subevent X e.
    Proof.
      reflexivity.
    Qed.

    Lemma exp_to_instr_Local : forall {X} (e : LLVMEnvE X),
        subevent X (exp_to_instr (subevent X e)) = subevent X e.
    Proof.
      reflexivity.
    Qed.

    Lemma exp_to_instr_Memory : forall {X} (e : MemoryE X),
        subevent X (exp_to_instr (subevent X e)) = subevent X e.
    Proof.
      reflexivity.
    Qed.

    Lemma exp_to_instr_Pick : forall {X} (e : PickE X),
        subevent X (exp_to_instr (subevent X e)) = subevent X e.
    Proof.
      reflexivity.
    Qed.

    Lemma exp_to_instr_UB : forall {X} (e : UBE X),
        subevent X (exp_to_instr (subevent X e)) = subevent X e.
    Proof.
      reflexivity.
    Qed.

    Lemma exp_to_instr_Fail : forall {X} (e : FailureE X),
        subevent X (exp_to_instr (subevent X e)) = subevent X e.
    Proof.
      reflexivity.
    Qed.

    Lemma FUB_to_exp_UB : forall {X} (e : UBE X),
        subevent X (FUB_to_exp (subevent X e)) = subevent X e.
    Proof.
      reflexivity.
    Qed.

    Lemma FUB_to_exp_Fail : forall {X} (e : FailureE X),
        subevent X (FUB_to_exp (subevent X e)) = subevent X e.
    Proof.
      reflexivity.
    Qed.

  End Translations.

  (* TO MOVE *)

  Lemma repr_intval (i: int64):
    DynamicValues.Int64.repr (Int64.intval i) = i.
  Proof.
    replace (Int64.intval i) with (Int64.unsigned i).
    - apply Int64.repr_unsigned.
    - destruct i.
      reflexivity.
  Qed.

  Lemma intval_to_from_nat_id:
    forall n, (Z.of_nat (Z.to_nat (Int64.intval n))) = Int64.intval n.
  Proof.
    intros.
    destruct n.
    cbn.  lia.
  Qed.

  Lemma uvalue_to_dvalue_list_concrete :
    forall fields dfields,
      (forall u : uvalue,
          In u fields ->
          (exists dv : dvalue, uvalue_to_dvalue u = inr dv) -> is_concrete u = true) ->
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
                 In u fields -> (exists dv : dvalue, uvalue_to_dvalue u = inr dv) -> is_concrete u = true) as BLAH.
      { intros u IN (dv & CONV).
        apply H.
        - cbn. auto.
        - exists dv. auto.
      }
      apply (IHfields l BLAH eq_refl).
  Qed.

  Lemma uvalue_to_dvalue_is_concrete :
    forall uv dv,
      uvalue_to_dvalue uv = inr dv ->
      is_concrete uv = true.
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

  Module ExpTactics.

    Hint Rewrite @bind_ret_l : rwexp.
    Hint Rewrite @translate_ret : rwexp.
    Hint Rewrite @interp_cfg2_ret : rwexp.
    Hint Rewrite @translate_bind : rwexp.
    Hint Rewrite @interp_cfg2_bind : rwexp.
    Hint Rewrite @translate_trigger : rwexp.

    Ltac simplify_translations :=
      do 2 try first [
          rewrite @LU_to_exp_Global |
          rewrite @exp_to_instr_Global |
          rewrite @LU_to_exp_Local |
          rewrite @exp_to_instr_Local |
          rewrite @exp_to_instr_Memory |
          rewrite @exp_to_instr_Pick |
          rewrite @exp_to_instr_UB |
          rewrite @exp_to_instr_Fail |
          rewrite @FUB_to_exp_UB |
          rewrite @FUB_to_exp_Fail].

    Ltac go :=
      autorewrite with rwexp;
      simplify_translations;
      autorewrite with rwexp.

    Ltac step :=
      match goal with
      | |- context [trigger (GlobalRead _)] =>
          match goal with
          | h: Maps.lookup _ _ = Some _ |- _ =>
              rewrite interp_cfg2_GR; [rewrite ?bind_ret_l | eauto]
          | h: Maps.lookup _ _ = None |- _ =>
              rewrite interp_cfg2_GR_fail; [rewrite ?bind_ret_l | eauto]
          end
      | |- context [trigger (LocalRead _)] =>
          match goal with
          | h: Maps.lookup _ _ = Some _ |- _ =>
              rewrite interp_cfg2_LR; [rewrite ?bind_ret_l | eauto]
          | h: Maps.lookup _ _ = None |- _ =>
              rewrite interp_cfg2_LR_fail; [rewrite ?bind_ret_l | eauto]
          end
      end.

  End ExpTactics.

  Import ExpTactics.

  Section ExpLemmas.
    
    Lemma denote_exp_GR :forall g l id v τ,
        Maps.lookup id g = Some v ->
        ⟦ EXP_Ident (ID_Global id) at τ ⟧e2 g l
                                         ≈
                                         Ret (l,(g,dvalue_to_uvalue v)).
    Proof.
      intros; cbn.
      go.
      step.
      go.
      reflexivity.
    Qed.

    Lemma denote_exp_LR :forall g l id v τ,
        Maps.lookup id l = Some v ->
        ⟦ EXP_Ident (ID_Local id) at τ ⟧e2 g l ≈ Ret (l,(g,v)).
    Proof.
      intros; cbn.
      go.
      step.
      go.
      reflexivity.
    Qed.

    Lemma denote_exp_i64 :forall t g l,
        ⟦ EXP_Integer (Integers.Int64.intval t) at (DTYPE_I 64) ⟧e2 g l
                                                                 ≈
                                                                 Ret (l, (g, UVALUE_I64 t)).
    Proof.
      intros; cbn.
      go.
      rewrite repr_intval.
      rewrite map_ret.
      go.
      reflexivity.
    Qed.

    Lemma denote_exp_i64_repr :forall t g l,
        ⟦ EXP_Integer t at (DTYPE_I 64) ⟧e2 g l
                                         ≈
                                         Ret (l, (g, UVALUE_I64 (repr t))).
    Proof.
      intros; cbn.
      go.
      rewrite map_ret.
      go.
      reflexivity.
    Qed.

    Lemma denote_exp_double :forall t g l,
        ⟦ EXP_Double t at DTYPE_Double ⟧e2 g l
                                        ≈
                                        Ret (l, (g, UVALUE_Double t)).
    Proof.
      intros; cbn.
      go.
      reflexivity.
    Qed.

    (* Lemma denote_conversion_concrete : *)
    (*   forall (conv : conversion_type) τ1 τ2 e g l m x a av, *)
    (*     ⟦ e at τ1 ⟧e3 g l m ≈ Ret3 g l m a -> *)
    (*     uvalue_to_dvalue a = inr av -> *)
    (*     eval_conv_pure conv τ1 av τ2  = ret x -> *)
    (*     ⟦OP_Conversion conv τ1 e τ2⟧e3 g l m *)
    (*     ≈ *)
    (*     Ret3 g l m (dvalue_to_uvalue x). *)
    (* Proof. *)
    (*   intros * He EQ Heval; cbn. *)
    (*   go. *)
    (*   rewrite He. *)
    (*   go. *)
    (*   unfold uvalue_to_dvalue_uop. *)
    (*   rewrite EQ. *)
    (*   cbn. *)
    (*   rewrite Heval. *)
    (*   unfold ITree.map; cbn. *)
    (*   go. *)
    (*   reflexivity. *)
    (* Qed. *)

    (*
    Lemma denote_ibinop_concrete :
      forall (op : ibinop) τ e0 e1 g l m x a av b bv,
        ⟦ e0 at τ ⟧e3 g l m ≈ Ret3 g l m a ->
        ⟦ e1 at τ ⟧e3 g l m ≈ Ret3 g l m b ->
        uvalue_to_dvalue a = inr av ->
        uvalue_to_dvalue b = inr bv ->
        @eval_iop err_ub_oom _ _ _ _ op av bv  = ret x ->
        ⟦ OP_IBinop op τ e0 e1 ⟧e3 g l m ≈ Ret3 g l m (dvalue_to_uvalue x).
    Proof.
      intros * A B AV BV EVAL.
      cbn.
      go.
      rewrite A.
      go.
      rewrite B.
      go.
      pose proof (uvalue_to_dvalue_is_concrete _ _ BV) as CONC.
      rewrite CONC.
      cbn. rewrite Bool.andb_false_r.
      unfold uvalue_to_dvalue_binop.
      rewrite AV, BV.
      cbn.
      setoid_rewrite EVAL.
      cbn.
      go.
      reflexivity.
    Qed.

    Lemma denote_fbinop_concrete :
      forall (op : fbinop) τ e0 e1 g l m x a av b bv params,
        ⟦ e0 at τ ⟧e3 g l m ≈ Ret3 g l m a ->
        ⟦ e1 at τ ⟧e3 g l m ≈ Ret3 g l m b ->
        uvalue_to_dvalue a = inr av ->
        uvalue_to_dvalue b = inr bv ->
        @eval_fop err_ub_oom _ _ _ op av bv  = ret x ->
        ⟦ OP_FBinop op params τ e0 e1 ⟧e3 g l m ≈ Ret3 g l m (dvalue_to_uvalue x).
    Proof.
      intros * A B AV BV EVAL.
      cbn.
      go.
      rewrite A.
      go.
      rewrite B.
      go.
      pose proof (uvalue_to_dvalue_is_concrete _ _ BV) as CONC.
      rewrite CONC.
      cbn. rewrite Bool.andb_false_r.
      unfold uvalue_to_dvalue_binop.
      rewrite AV, BV.
      cbn.
      rewrite EVAL.
      cbn. 
      go.
      reflexivity.
    Qed.

    Lemma denote_fcmp_concrete :
      forall (op : fcmp) τ e0 e1 g l m x a av b bv,
        ⟦ e0 at τ ⟧e3 g l m ≈ Ret3 g l m a ->
        ⟦ e1 at τ ⟧e3 g l m ≈ Ret3 g l m b ->
        uvalue_to_dvalue a = inr av ->
        uvalue_to_dvalue b = inr bv ->
        @eval_fcmp err_ub_oom _ _ op av bv  = ret x ->
        ⟦ OP_FCmp op τ e0 e1 ⟧e3 g l m ≈ Ret3 g l m (dvalue_to_uvalue x).
    Proof.
      intros * A B AV BV EVAL.
      cbn.
      go.
      rewrite A.
      go.
      rewrite B.
      go.
      unfold uvalue_to_dvalue_binop.
      rewrite AV, BV.
      cbn.
      setoid_rewrite EVAL.
      cbn.
      go.
      reflexivity.
    Qed.

    Lemma denote_icmp_concrete :
      forall (op : icmp) τ e0 e1 g l m x a av b bv,
        ⟦ e0 at τ ⟧e3 g l m ≈ Ret3 g l m a ->
        ⟦ e1 at τ ⟧e3 g l m ≈ Ret3 g l m b ->
        uvalue_to_dvalue a = inr av ->
        uvalue_to_dvalue b = inr bv ->
        @eval_icmp err_ub_oom _ _ op av bv  = ret x ->
        ⟦ OP_ICmp op τ e0 e1 ⟧e3 g l m ≈ Ret3 g l m (dvalue_to_uvalue x).
    Proof.
      intros * A B AV BV EVAL.
      cbn.
      go.
      rewrite A.
      go.
      rewrite B.
      go.
      unfold uvalue_to_dvalue_binop.
      rewrite AV, BV.
      cbn.
      rewrite EVAL.
      cbn.
      go.
      reflexivity.
    Qed.

     *)
  End ExpLemmas.

  (* Section ExpPure. *)

  (*   Import ITreeNotations. *)

  (*   (* Expressions are "almost pure" computations: *)
  (*  they depend on the memory, but do not modify any component on the state *) *)

  (*   Definition pure_P g l m : state_cfgP := fun '(m',(l',g')) => m' = m /\ l' = l /\ g' = g. *)

  (*   Definition pure {E R} (t : global_env -> local_env -> itree E (local_env * (global_env * R))) : Prop := *)
  (*     forall g l m, t g l m ⤳ ↑ (pure_P g l m). *)

  (*   Lemma failure_is_pure : forall R s, *)
  (*       pure (R := R) (interp_cfg3 (raise s)). *)
  (*   Proof. *)
  (*     unfold pure, raise; intros. *)
  (*     go. *)
  (*     unfold interp_cfg3. *)
  (*     rewrite interp_intrinsics_trigger. *)
  (*     cbn. *)
  (*     unfold Intrinsics.F_trigger; cbn. *)
  (*     rewrite subevent_subevent. *)
  (*     rewrite interp_global_trigger; cbn. *)
  (*     rewrite subevent_subevent. *)
  (*     rewrite interp_local_bind, interp_local_trigger; cbn. *)
  (*     rewrite subevent_subevent, bind_bind. *)
  (*     rewrite interp_memory_bind, interp_memory_trigger; cbn. *)
  (*     rewrite subevent_subevent, !bind_bind. *)
  (*     apply has_post_bind; intros []. *)
  (*   Qed. *)

  (*   Ltac step := *)
  (*     match goal with *)
  (*     | |- context [trigger (GlobalRead _)] => *)
  (*         match goal with *)
  (*         | h: Maps.lookup _ _ = Some _ |- _ => *)
  (*             rewrite interp_cfg3_GR; [rewrite ?bind_ret_l | eauto] *)
  (*         | h: Maps.lookup _ _ = None |- _ => *)
  (*             rewrite interp_cfg3_GR_fail; [rewrite ?bind_ret_l | eauto] *)
  (*         end *)
  (*     | |- context [trigger (LocalRead _)] => *)
  (*         match goal with *)
  (*         | h: Maps.lookup _ _ = Some _ |- _ => *)
  (*             rewrite interp_cfg3_LR; [rewrite ?bind_ret_l | eauto] *)
  (*         | h: Maps.lookup _ _ = None |- _ => *)
  (*             rewrite interp_cfg3_LR_fail; [rewrite ?bind_ret_l | eauto] *)
  (*         end *)
  (*     | |- context [trigger (pick_uvalue _ _)] => rewrite interp_cfg3_pick *)
  (*     | |- context [trigger (ThrowUB _)] => rewrite interp_cfg3_UB *)
  (*     end. *)

  (*   (* Lemma eval_conv_h_case : forall conv t1 x t2, *) *)
  (*   (*         (exists s, eval_conv_h conv t1 x t2 = raise s) \/ *) *)
  (*   (*         (exists v, eval_conv_h conv t1 x t2 = Ret v) \/ *) *)
  (*   (*         (exists z, eval_conv_h conv t1 x t2 = trigger (ItoP z)) \/ *) *)
  (*   (*         (exists z, eval_conv_h conv t1 x t2 = trigger (PtoI t2 z)). *) *)
  (*   (* Proof. *) *)
  (*   (*   intros. *) *)
  (*   (*   unfold eval_conv_h. *) *)
  (*   (*   break_match_goal; cbn in *; eauto. *) *)
  (*   (* Qed. *) *)

  (*   Lemma pick_is_pure : forall u P, pure (ℑ3 (trigger (pick_uvalue P u))). *)
  (*   Proof. *)
  (*     intros. *)
  (*     unfold pure; intros. *)
  (*     go. *)
  (*     step. *)
  (*     apply has_post_bind. *)
  (*     intros ?; apply eutt_Ret; cbn; auto. *)
  (*   Qed. *)

  (*   Lemma UB_is_pure : forall R s, *)
  (*       pure (R := R) (ℑ3 (raiseUB s)). *)
  (*   Proof. *)
  (*     unfold pure, raiseUB; intros. *)
  (*     go. *)
  (*     step. *)
  (*     apply has_post_bind. *)
  (*     intros (? & ? & ? & []). *)
  (*   Qed. *)

  (*   (* Lemma ItoP_is_pure : forall z, *) *)
  (*   (*     pure (ℑ3 (trigger (ItoP z))). *) *)
  (*   (* Proof. *) *)
  (*   (*   unfold pure; intros. *) *)
  (*   (*   unfold ℑ3. *) *)
  (*   (*   rewrite interp_intrinsics_trigger. *) *)
  (*   (*   cbn. rewrite interp_global_trigger. cbn. *) *)
  (*   (*   rewrite interp_local_bind. *) *)
  (*   (*   rewrite interp_local_trigger. *) *)
  (*   (*   cbn. rewrite bind_trigger. rewrite bind_vis. *) *)
  (*   (*   cbn. rewrite interp_memory_vis. cbn. *) *)
  (*   (*   break_match; *) *)
  (*   (*     try solve [unfold raise; rewrite ?bind_bind; apply has_post_bind; intros []; *) *)
  (*   (*   try apply failure_is_pure]. *) *)
  (*   (*   1 - 4 : break_match; *) *)
  (*   (*     try solve [unfold raise; rewrite ?bind_bind; apply has_post_bind; intros []; *) *)
  (*   (*   try apply failure_is_pure]. *) *)
  (*   (*   1 - 4 : try destruct p; cbn; setoid_rewrite bind_ret_l; *) *)
  (*   (*   rewrite interp_memory_bind; rewrite interp_memory_ret; *) *)
  (*   (*   cbn; rewrite bind_ret_l; *) *)
  (*   (*   try rewrite interp_local_ret; try rewrite interp_memory_ret; cbn; *) *)
  (*   (*     try apply eutt_Ret; cbn; auto. *) *)
  (*   (* Qed. *) *)

  (*   (* BEGIN TO MOVE *) *)
  (*   Lemma FUB_to_exp_raiseUB : forall T s, *)
  (*       translate FUB_to_exp (raiseUB (X := T) s) ≈ raiseUB s. *)
  (*   Proof. *)
  (*     unfold raiseUB; intros. *)
  (*     go. *)
  (*     apply eutt_eq_bind; intros []. *)
  (*   Qed. *)

  (*   Lemma exp_to_instr_raiseUB : forall T s, *)
  (*       translate exp_to_instr (raiseUB (X := T) s) ≈ raiseUB s. *)
  (*   Proof. *)
  (*     unfold raiseUB; intros. *)
  (*     go. *)
  (*     apply eutt_eq_bind; intros []. *)
  (*   Qed. *)

  (*   Lemma FUB_to_exp_raise : forall T s, *)
  (*       translate FUB_to_exp (raise (A := T) s) ≈ raise s. *)
  (*   Proof. *)
  (*     unfold raise; intros. *)
  (*     go.  *)
  (*     apply eutt_eq_bind; intros []. *)
  (*   Qed. *)

  (*   Lemma exp_to_instr_raise : forall T s, *)
  (*       translate exp_to_instr (raise (A := T) s) ≈ raise s. *)
  (*   Proof. *)
  (*     unfold raise; intros. *)
  (*     go.  *)
  (*     apply eutt_eq_bind; intros []. *)
  (*   Qed. *)

  (*   Lemma exp_to_instr_pick : forall P uv, *)
  (*       translate exp_to_instr (trigger (pick_uvalue P uv)) ≈ trigger (pick_uvalue P uv). *)
  (*   Proof. *)
  (*     intros. *)
  (*     go.  *)
  (*     reflexivity. *)
  (*   Qed. *)

  (*   Lemma concretize_or_pick_is_pure : forall v P, pure (ℑ3 (translate exp_to_instr (concretize_or_pick v P))). *)
  (*   Proof. *)
  (*     unfold pure; intros. *)
  (*     unfold concretize_or_pick. *)
  (*     break_match_goal; [| rewrite exp_to_instr_pick; apply pick_is_pure]. *)
  (*     unfold lift_err. *)
  (*     break_match_goal; [rewrite exp_to_instr_raise; apply failure_is_pure |]. *)
  (*     cbn. *)
  (*     go. *)
  (*     apply eutt_Ret; cbn; auto. *)
  (*   Qed. *)

  (*   Lemma translate_map_monad {E F A B} (l : list A) (ts : A -> itree E B) (h : E ~> F) : *)
  (*     translate h (map_monad ts l) ≈ map_monad (fun a => translate h (ts a)) l. *)
  (*   Proof. *)
  (*     induction l as [| a l IH]. *)
  (*     - cbn; go; reflexivity. *)
  (*     - cbn; go.  *)
  (*       apply eutt_eq_bind; intros ?. *)
  (*       go. *)
  (*       rewrite IH. *)
  (*       setoid_rewrite translate_ret. *)
  (*       reflexivity. *)
  (*   Qed. *)

  (*   Lemma interp_map_monad {E F A B} (l : list A) (ts : A -> itree E B) (h : E ~> itree F): *)
  (*     interp h (map_monad ts l) ≈ map_monad (fun a => interp h (ts a)) l. *)
  (*   Proof. *)
  (*     intros; induction l as [| a l IH]; simpl. *)
  (*     - rewrite interp_ret; reflexivity. *)
  (*     - rewrite interp_bind. *)
  (*       apply eutt_eq_bind; intros ?; cbn. *)
  (*       rewrite interp_bind, IH. *)
  (*       apply eutt_eq_bind; intros ?; cbn. *)
  (*       rewrite interp_ret; reflexivity. *)
  (*   Qed. *)

  (*   Lemma interp_state_map_monad {E F S A B} (l : list A) (ts : A -> itree E B) (h : E ~> Monads.stateT S (itree F)) (s : S): *)
  (*     interp_state h (map_monad ts l) s ≈ map_monad (m := Monads.stateT S (itree F)) (fun a => interp_state h (ts a)) l s. *)
  (*   Proof. *)
  (*     intros; revert s; induction l as [| a l IH]; simpl; intros s. *)
  (*     - rewrite interp_state_ret; reflexivity. *)
  (*     - rewrite interp_state_bind. *)
  (*       apply eutt_eq_bind; intros []; cbn. *)
  (*       rewrite interp_state_bind, IH. *)
  (*       apply eutt_eq_bind; intros []; cbn. *)
  (*       rewrite interp_state_ret; reflexivity. *)
  (*   Qed. *)

  (*   (* END TO MOVE *) *)

  (*   Lemma interp_cfg3_map_monad {A B} g l m (xs : list A) (ts : A -> itree _ B) :  *)
  (*     ℑ3 (map_monad ts xs) g l m ≈ *)
  (*        map_monad (m := Monads.stateT _ (Monads.stateT _ (Monads.stateT _ (itree _)))) *)
  (*        (fun a => ℑ3 (ts a)) xs g l m. *)
  (*   Proof. *)
  (*     intros; revert g l m; induction xs as [| a xs IH]; simpl; intros. *)
  (*     - rewrite interp_cfg3_ret; reflexivity. *)
  (*     - rewrite interp_cfg3_bind. *)
  (*       apply eutt_eq_bind; intros (? & ? & ? & ?); cbn. *)
  (*       rewrite interp_cfg3_bind, IH. *)
  (*       apply eutt_eq_bind; intros (? & ? & ? & ?); cbn. *)
  (*       rewrite interp_cfg3_ret; reflexivity. *)
  (*   Qed. *)

  (*   Lemma map_monad_eutt_state_ind : *)
  (*     forall {E S A B} (I : S -> Prop) (f : A -> Monads.stateT S (itree E) B) (l : list A) s, *)
  (*       (forall a s, In a l -> I s -> (f a s) ⤳ fun '(s,_) => I s) -> *)
  (*       I s -> *)
  (*       map_monad f l s ⤳ fun '(s,_) => I s. *)
  (*   Proof. *)
  (*     induction l as [| a l IH]; intros s HB HI; simpl. *)
  (*     - apply eutt_Ret; auto. *)
  (*     - setoid_rewrite has_post_post_strong in HB. *)
  (*       eapply eutt_clo_bind; [apply HB; cbn; auto |]. *)
  (*       intros [s' ?] [] [EQ ?]; inv EQ. *)
  (*       simpl. *)
  (*       setoid_rewrite has_post_post_strong in IH. *)
  (*       eapply eutt_clo_bind; [apply IH |]; auto. *)
  (*       intros; apply HB; cbn; auto.  *)
  (*       intros [s' ?] [] [EQ ?]; inv EQ; cbn; apply eutt_Ret; auto.  *)
  (*   Qed. *)

  (*   Lemma map_monad_eutt_state2_ind : *)
  (*     forall {E S1 S2 A B} (I : S1 -> S2 -> Prop) *)
  (*            (f : A -> Monads.stateT S1 (Monads.stateT S2 (itree E)) B) *)
  (*            (l : list A) (s1 : S1) (s2 : S2),  *)
  (*       (forall a s1 s2, In a l -> I s1 s2 -> (f a s1 s2) ⤳ fun '(s2',(s1',_)) => I s1' s2') -> *)
  (*       I s1 s2 -> *)
  (*       map_monad f l s1 s2 ⤳ fun '(s2',(s1',_)) => I s1' s2'. *)
  (*   Proof. *)
  (*     induction l as [| a l IH]; intros s1 s2 HB HI; simpl. *)
  (*     - apply eutt_Ret; auto. *)
  (*     - setoid_rewrite has_post_post_strong in HB. *)
  (*       eapply eutt_clo_bind; [apply HB; cbn; auto |]. *)
  (*       intros (s2' & s1' & ?) (? & ? & ?) [EQ ?]; inv EQ. *)
  (*       simpl. *)
  (*       setoid_rewrite has_post_post_strong in IH. *)
  (*       eapply eutt_clo_bind; [apply IH |]; auto. *)
  (*       intros; apply HB; cbn; auto. *)
  (*       intros (s1' & s2' & ?) (? & ? & ?) [EQ ?]; inv EQ; cbn; apply eutt_Ret; auto.  *)
  (*   Qed. *)

  (*   Lemma map_monad_eutt_state3_ind : *)
  (*     forall {E S1 S2 S3 A B} (I : S1 -> S2 -> S3 -> Prop) *)
  (*            (f : A -> Monads.stateT S1 (Monads.stateT S2 (Monads.stateT S3 (itree E))) B) *)
  (*            (l : list A) (s1 : S1) (s2 : S2) (s3 : S3),  *)
  (*       (forall a s1 s2 s3, In a l -> I s1 s2 s3 -> (f a s1 s2 s3) ⤳ fun '(s3', (s2',(s1',_))) => I s1' s2' s3') -> *)
  (*       I s1 s2 s3 -> *)
  (*       map_monad f l s1 s2 s3 ⤳ fun '(s3', (s2',(s1',_))) => I s1' s2' s3'. *)
  (*   Proof. *)
  (*     induction l as [| a l IH]; intros s1 s2 s3 HB HI; simpl. *)
  (*     - apply eutt_Ret; auto. *)
  (*     - setoid_rewrite has_post_post_strong in HB. *)
  (*       eapply eutt_clo_bind; [apply HB; cbn; auto |]. *)
  (*       intros (s3' & s2' & s1' & ?) (? & ? & ? & ?) [EQ ?]; inv EQ. *)
  (*       simpl. *)
  (*       setoid_rewrite has_post_post_strong in IH. *)
  (*       eapply eutt_clo_bind; [apply IH |]; auto. *)
  (*       intros; apply HB; cbn; auto. *)
  (*       intros (s1' & s2' & s3' & ?) (? & ? & ? & ?) [EQ ?]; inv EQ; cbn; apply eutt_Ret; auto.  *)
  (*   Qed. *)

  (*   Ltac trivial_cases := *)
  (*     try first [apply eutt_Ret; cbn; auto; fail | *)

  (*                 unfold raise; rewrite ?bind_bind; apply has_post_bind; intros [] | *)

  (*                 match goal with *)
  (*                   |- context [raise] => rewrite ?FUB_to_exp_raise, ?exp_to_instr_raise; *)
  (*                                         apply failure_is_pure *)
  (*                 end | *)

                  
  (*                 match goal with *)
  (*                   |- context [raiseUB] => rewrite ?FUB_to_exp_raiseUB, ?exp_to_instr_raiseUB;  *)
  (*                                           apply UB_is_pure *)
  (*                 end | *)
                  
  (*                 match goal with *)
  (*                   |- context [pick_uvalue] => rewrite ?exp_to_instr_pick; *)
  (*                                        apply pick_is_pure *)
  (*                 end  *)

  (*       ]. *)

  (*   Ltac intro_pure := intros (? & ? & ? & ?) (-> & -> & ->). *)

  (*   Lemma conv_to_exp_raise: forall (T : Type) (s : string), translate conv_to_exp (raise (A := T) s) ≈ raise s. *)
  (*   Proof. *)
  (*     unfold raise; intros. *)
  (*     go. *)
  (*     apply eutt_eq_bind; intros []. *)
  (*   Qed. *)

  (*   (* Lemma expr_are_pure : forall (o : option dtyp) e, pure ⟦ e at? o ⟧e3. *) *)
  (*   (* Proof with trivial_cases. *) *)
  (*   (*   intros; unfold pure. *) *)
  (*   (*   revert o; induction e; simpl; intros. *) *)

  (*   (*   - destruct id; cbn. *) *)
  (*   (*     + go. *) *)
  (*   (*       destruct (Maps.lookup id g) eqn:EQ. *) *)
  (*   (*       * step. *) *)
  (*   (*         go... *) *)
    
  (*   (*       * step... *) *)
    
  (*   (*     + go.  *) *)
  (*   (*       destruct (Maps.lookup id l) eqn:EQ. *) *)
  (*   (*       * step...  *) *)
  (*   (*       * step... *) *)
    
  (*   (*   - destruct o; cbn... *) *)
  (*   (*     destruct d; simpl... *) *)
  (*   (*     unfold denote_exp, lift_undef_or_err. *) *)
  (*   (*     cbn. *) *)
  (*   (*     break_match_goal...  *) *)
  (*   (*     break_match_goal... *) *)
  (*   (*     go... *) *)

  (*   (*   - destruct o; cbn... *) *)
  (*   (*     destruct d; simpl... *) *)
  (*   (*     go... *) *)

  (*   (*   - destruct o; cbn... *) *)
  (*   (*     destruct d; simpl... *) *)
  (*   (*     go... *) *)

  (*   (*   - destruct o; cbn... *) *)
  (*   (*     destruct d; simpl... *) *)
  (*   (*     go... *) *)
  (*   (*     go... *) *)

  (*   (*   - destruct b; simpl; go... *) *)

  (*   (*   - simpl; go... *) *)

  (*   (*   - destruct o; cbn... *) *)

  (*   (*   - go. *) *)
  (*   (*     rewrite translate_map_monad. *) *)
  (*   (*     rewrite interp_cfg3_map_monad. *) *)
  (*   (*     apply has_post_bind_strong with (S := ↑ (pure_P g l m)). *) *)
  (*   (*     + eapply has_post_weaken. *) *)
  (*   (*       apply (map_monad_eutt_state3_ind (fun g' l' m' => pure_P g l m (m',(l',g')))); [| cbn; intuition]. *) *)
  (*   (*       * intros * IN (-> & -> & ->). *) *)
  (*   (*         destruct a; simpl in *. *) *)
  (*   (*         apply has_post_weaken with (↑ (pure_P g l m)). *) *)
  (*   (*         apply (H _ IN). *) *)
  (*   (*         intro_pure; cbn; auto. *) *)
  (*   (*       * intro_pure; cbn; auto.  *) *)
  (*   (*     + intro_pure. *) *)
  (*   (*       go... *) *)

  (*   (*   - destruct o; cbn... *) *)
  (*   (*     go... *) *)

  (*   (*   - go. *) *)
  (*   (*     rewrite translate_map_monad. *) *)
  (*   (*     rewrite interp_cfg3_map_monad. *) *)
  (*   (*     apply has_post_bind_strong with (S := ↑ (pure_P g l m)). *) *)
  (*   (*     + eapply has_post_weaken. *) *)
  (*   (*       apply (map_monad_eutt_state3_ind (fun g' l' m' => pure_P g l m (m',(l',g')))); [| cbn; intuition]. *) *)
  (*   (*       * intros * IN (-> & -> & ->). *) *)
  (*   (*         destruct a; simpl in *. *) *)
  (*   (*         apply has_post_weaken with (↑ (pure_P g l m)). *) *)
  (*   (*         apply (H _ IN). *) *)
  (*   (*         intro_pure; auto. *) *)
  (*   (*       * intro_pure; cbn; auto. *) *)
  (*   (*     + intro_pure. *) *)
  (*   (*       go... *) *)

  (*   (*   - destruct o; cbn... *) *)
  (*   (*     destruct d; cbn... *) *)
  (*   (*     go. *) *)
  (*   (*     rewrite translate_map_monad. *) *)
  (*   (*     rewrite interp_cfg3_map_monad. *) *)
  (*   (*     apply has_post_bind_strong with (S := ↑ (pure_P g l m)). *) *)
  (*   (*     + eapply has_post_weaken. *) *)
  (*   (*       apply (map_monad_eutt_state3_ind (fun g' l' m' => pure_P g l m (m',(l',g')))); [| cbn; intuition]. *) *)
  (*   (*       * intros * IN (-> & -> & ->). *) *)
  (*   (*         destruct a; simpl in *. *) *)
  (*   (*         apply has_post_weaken with (↑ (pure_P g l m)). *) *)
  (*   (*         apply (H _ IN). *) *)
  (*   (*         intro_pure; auto. *) *)
  (*   (*       * intro_pure; cbn; auto. *) *)
  (*   (*     + intro_pure. *) *)
  (*   (*       go... *) *)

  (*   (*   - go. *) *)
  (*   (*     rewrite translate_map_monad. *) *)
  (*   (*     rewrite interp_cfg3_map_monad. *) *)
  (*   (*     apply has_post_bind_strong with (S := ↑ (pure_P g l m)). *) *)
  (*   (*     + eapply has_post_weaken. *) *)
  (*   (*       apply (map_monad_eutt_state3_ind (fun g' l' m' => pure_P g l m (m',(l',g')))); [| cbn; intuition]. *) *)
  (*   (*       * intros * IN (-> & -> & ->). *) *)
  (*   (*         destruct a; simpl in *. *) *)
  (*   (*         apply has_post_weaken with (↑ (pure_P g l m)). *) *)
  (*   (*         apply (H _ IN). *) *)
  (*   (*         intro_pure; auto. *) *)
  (*   (*       * intro_pure; cbn; auto. *) *)
  (*   (*     + intro_pure. *) *)
  (*   (*       go... *) *)

  (*   (*   - go. *) *)
  (*   (*     rewrite translate_map_monad. *) *)
  (*   (*     rewrite interp_cfg3_map_monad. *) *)
  (*   (*     apply has_post_bind_strong with (S := ↑ (pure_P g l m)). *) *)
  (*   (*     + eapply has_post_weaken. *) *)
  (*   (*       apply (map_monad_eutt_state3_ind (fun g' l' m' => pure_P g l m (m',(l',g')))); [| cbn; intuition]. *) *)
  (*   (*       * intros * IN (-> & -> & ->). *) *)
  (*   (*         destruct a; simpl in *. *) *)
  (*   (*         apply has_post_weaken with (↑ (pure_P g l m)). *) *)
  (*   (*         apply (H _ IN). *) *)
  (*   (*         intro_pure; auto. *) *)
  (*   (*       * intro_pure; cbn; auto. *) *)
  (*   (*     + intro_pure. *) *)
  (*   (*       go... *) *)

  (*   (*   - go. *) *)
  (*   (*     eapply has_post_bind_strong. *) *)
  (*   (*     apply (IHe1 (Some t) g l m). *) *)
  (*   (*     intros (? & ? & ? & ?) (-> & -> & ->). *) *)
  (*   (*     go. *) *)
  (*   (*     eapply has_post_bind_strong. *) *)
  (*   (*     apply (IHe2 (Some t) g l m). *) *)
  (*   (*     intro_pure. *) *)
  (*   (*     break_match_goal. *) *)
  (*   (*     + go. *) *)
  (*   (*       apply has_post_bind_strong with (↑ (pure_P g l m)). *) *)
  (*   (*       * unfold concretize_or_pick. *) *)
  (*   (*         break_match_goal... *) *)
  (*   (*         cbn. *) *)
  (*   (*         { *) *)
  (*   (*           unfold lift_err. *) *)
  (*   (*           break_match_goal... *) *)
  (*   (*           go... *) *)
  (*   (*         } *) *)

  (*   (*       * intro_pure. *) *)
  (*   (*         unfold uvalue_to_dvalue_binop2. *) *)
  (*   (*         cbn; break_match_goal... *) *)
  (*   (*         go... *) *)
  (*   (*         break_match_hyp; inv_sum. *) *)
  (*   (*         break_match_goal... *) *)
  (*   (*         break_match_goal... *) *)
  (*   (*         go... *) *)

  (*   (*     + unfold uvalue_to_dvalue_binop. *) *)
  (*   (*       cbn. *) *)
  (*   (*       break_match_goal. *) *)
  (*   (*       go... *) *)
  (*   (*       break_match_hyp; try inv_sum. *) *)
  (*   (*       break_match_hyp; try inv_sum. *) *)
  (*   (*       break_match_goal... *) *)
  (*   (*       break_match_goal... *) *)
  (*   (*       go... *) *)

  (*   (*   - go. *) *)
  (*   (*     eapply has_post_bind_strong. *) *)
  (*   (*     apply (IHe1 (Some t) g l m). *) *)
  (*   (*     intro_pure. *) *)
  (*   (*     go. *) *)
  (*   (*     eapply has_post_bind_strong. *) *)
  (*   (*     apply (IHe2 (Some t) g l m). *) *)
  (*   (*     intro_pure. *) *)
  (*   (*     unfold uvalue_to_dvalue_binop. *) *)
  (*   (*     cbn. *) *)
  (*   (*     break_match_goal. *) *)
  (*   (*     go... *) *)
  (*   (*     break_match_hyp; try inv_sum. *) *)
  (*   (*     break_match_hyp; try inv_sum. *) *)
  (*   (*     break_match_goal... *) *)
  (*   (*     break_match_goal... *) *)
  (*   (*     go... *) *)

  (*   (*   - go. *) *)
  (*   (*     eapply has_post_bind_strong. *) *)
  (*   (*     apply (IHe1 (Some t) g l m). *) *)
  (*   (*     intro_pure. *) *)
  (*   (*     go. *) *)
  (*   (*     eapply has_post_bind_strong. *) *)
  (*   (*     apply (IHe2 (Some t) g l m). *) *)
  (*   (*     intro_pure. *) *)
  (*   (*     break_match_goal. *) *)
  (*   (*     + go. *) *)
  (*   (*       apply has_post_bind_strong with (↑ (pure_P g l m)). *) *)
  (*   (*       * unfold concretize_or_pick. *) *)
  (*   (*         break_match_goal... *) *)
  (*   (*         cbn. *) *)
  (*   (*         { *) *)
  (*   (*           unfold lift_err. *) *)
  (*   (*           break_match_goal... *) *)
  (*   (*           go... *) *)
  (*   (*         } *) *)

  (*   (*       * intro_pure. *) *)
  (*   (*         unfold uvalue_to_dvalue_binop2. *) *)
  (*   (*         cbn; break_match_goal. *) *)
  (*   (*         go... *) *)
  (*   (*         break_match_hyp; inv_sum. *) *)
  (*   (*         break_match_goal... *) *)
  (*   (*         break_match_goal... *) *)
  (*   (*         go... *) *)

  (*   (*     + unfold uvalue_to_dvalue_binop. *) *)
  (*   (*       cbn. *) *)
  (*   (*       break_match_goal. *) *)
  (*   (*       go... *) *)
  (*   (*       break_match_hyp; try inv_sum. *) *)
  (*   (*       break_match_hyp; try inv_sum. *) *)
  (*   (*       break_match_goal... *) *)
  (*   (*       break_match_goal... *) *)
  (*   (*       go... *) *)

  (*   (*   - go. *) *)
  (*   (*     eapply has_post_bind_strong. *) *)
  (*   (*     apply (IHe1 (Some t) g l m). *) *)
  (*   (*     intro_pure. *) *)
  (*   (*     go. *) *)
  (*   (*     eapply has_post_bind_strong. *) *)
  (*   (*     apply (IHe2 (Some t) g l m). *) *)
  (*   (*     intro_pure. *) *)
  (*   (*     unfold uvalue_to_dvalue_binop. *) *)
  (*   (*     cbn. *) *)
  (*   (*     break_match_goal. *) *)
  (*   (*     go... *) *)
  (*   (*     break_match_hyp; try inv_sum. *) *)
  (*   (*     break_match_hyp; try inv_sum. *) *)
  (*   (*     break_match_goal... *) *)
  (*   (*     break_match_goal... *) *)
  (*   (*     go... *) *)

  (*   (*   - go. *) *)
  (*   (*     eapply has_post_bind_strong. *) *)
  (*   (*     apply (IHe (Some t_from) g l m). *) *)
  (*   (*     intro_pure. *) *)
  (*   (*     unfold uvalue_to_dvalue_uop; cbn. *) *)
  (*   (*     break_match_goal. *) *)
  (*   (*     go... *) *)
  (*   (*     break_match_hyp; try inv_sum. *) *)
  (*   (*     unfold ITree.map. *) *)
  (*   (*     go. *) *)
  (*   (*     apply has_post_bind_strong with (↑ (pure_P g l m)). *) *)

  (*   (*     + (* What's the right way to reason about eval_conv? *) *) *)
  (*   (*       unfold eval_conv. *) *)


  (*   (*       pose proof (eval_conv_h_case conv t_from d t_to). *) *)
  (*   (*       destruct H as [ (s & H) | [(v & H)| [ (z & H)| (z & H)]] ]. *) *)
  (*   (*       rewrite H. *) *)

  (*   (*       destruct t_from; cbn. *) *)
  (*   (*       1 - 16 : (rewrite conv_to_exp_raise; rewrite exp_to_instr_raise); trivial_cases. *) *)
  (*   (*       destruct d; cbn. *) *)
  (*   (*       1 - 14 : (rewrite conv_to_exp_raise; rewrite exp_to_instr_raise); trivial_cases. *) *)
  (*   (*       destruct t_from; cbn; rewrite H; go; trivial_cases. *) *)

  (*   (*       destruct d; cbn; go; trivial_cases. *) *)
  (*   (*       rewrite conv_to_exp_raise; rewrite exp_to_instr_raise; trivial_cases. *) *)

  (*   (*       destruct t_from; rewrite H; try rewrite conv_to_exp_ItoP; try apply ItoP_is_pure. *) *)
  (*   (*       destruct d; cbn; go; trivial_cases. *) *)

  (*   (*       1 - 13 : apply ItoP_is_pure. *) *)

  (*   (*       rewrite conv_to_exp_raise; rewrite exp_to_instr_raise. apply failure_is_pure. *) *)

  (*   (*       admit. *) *)
  (*   (*     + intro_pure. *) *)
  (*   (*             go... *) *)
  (*   (*   - destruct ptrval; cbn. *) *)
  (*   (*     rewrite translate_bind, interp_cfg3_bind. *) *)
  (*   (*     eapply has_post_bind_strong. *) *)
  (*   (*     apply (IHe (Some d) g l m). *) *)
  (*   (*     intro_pure. *) *)
  (*   (*     rewrite translate_bind, interp_cfg3_bind. *) *)
  (*   (*     rewrite translate_map_monad. *) *)
  (*   (*     rewrite interp_cfg3_map_monad. *) *)
  (*   (*     apply has_post_bind_strong with (S := ↑ (pure_P g l m)). *) *)
  (*   (*     + eapply has_post_weaken. *) *)
  (*   (*       apply (map_monad_eutt_state3_ind (fun g' l' m' => pure_P g l m (m',(l',g')))); [| cbn; intuition]. *) *)
  (*   (*       * intros * IN (-> & -> & ->). *) *)
  (*   (*         destruct a; simpl in *. *) *)
  (*   (*         apply has_post_weaken with (↑ (pure_P g l m)). *) *)
  (*   (*         apply (H _ IN). *) *)
  (*   (*         intro_pure; auto. *) *)
  (*   (*       * intro_pure; cbn; auto. *) *)
  (*   (*     + intro_pure. *) *)
  (*   (*       break_match_goal. *) *)
  (*   (*       * rewrite translate_bind, interp_cfg3_bind. *) *)
  (*   (*         unfold concretize_or_pick. *) *)
  (*   (*         apply has_post_bind_strong with (↑ (pure_P g l m)). *) *)
  (*   (*         { *) *)
  (*   (*           break_match_goal... *) *)
  (*   (*           unfold lift_err. *) *)
  (*   (*           break_match_goal... *) *)
  (*   (*           cbn; go...  *) *)
  (*   (*         } *) *)
  (*   (*         intro_pure. *) *)
  (*   (*         rewrite translate_bind, interp_cfg3_bind. *) *)
  (*   (*         rewrite translate_map_monad. *) *)
  (*   (*         rewrite interp_cfg3_map_monad. *) *)
  (*   (*         apply has_post_bind_strong with (S := ↑ (pure_P g l m)). *) *)
  (*   (*         { eapply has_post_weaken. *) *)
  (*   (*           apply (map_monad_eutt_state3_ind (fun g' l' m' => pure_P g l m (m',(l',g')))); [| cbn; intuition]. *) *)
  (*   (*           * intros * IN (-> & -> & ->). *) *)
  (*   (*             break_match_goal... *) *)
  (*   (*             unfold lift_err. *) *)
  (*   (*             break_match_goal... *) *)
  (*   (*             cbn; go...  *) *)
  (*   (*           * intro_pure; cbn; auto. *) *)
  (*   (*         } *) *)
  (*   (*         intro_pure; cbn; auto. *) *)
  (*   (*         unfold ITree.map; go.  *) *)
  (*   (*         (* GEP... *) *) *)
  (*   (*         unfold interp_cfg3. *) *)
  (*   (*         rewrite interp_intrinsics_trigger. *) *)
  (*   (*         cbn. *) *)
  (*   (*         unfold Intrinsics.F_trigger; cbn. *) *)
  (*   (*         rewrite subevent_subevent. *) *)
  (*   (*         rewrite interp_global_trigger; cbn. *) *)
  (*   (*         rewrite subevent_subevent. *) *)
  (*   (*         rewrite interp_local_bind, interp_local_trigger; cbn. *) *)
  (*   (*         rewrite subevent_subevent, bind_bind. *) *)
  (*   (*         rewrite interp_memory_bind, interp_memory_trigger; cbn. *) *)
  (*   (*         rewrite !bind_bind. *) *)
  (*   (*         destruct d0; cbn; try (unfold raise; rewrite bind_bind; apply has_post_bind; intros []). *) *)
  (*   (*         break_match_goal; cbn; try (unfold raise; rewrite bind_bind; apply has_post_bind; intros []). *) *)
  (*   (*         go.  *) *)
  (*   (*         rewrite interp_local_ret, interp_memory_ret, bind_ret_l. *) *)
  (*   (*         rewrite translate_ret, interp_intrinsics_ret, interp_global_ret, interp_local_ret, interp_memory_ret.  *) *)
  (*   (*         go... *) *)

  (*   (*       * unfold ITree.map; destruct p; cbn. *) *)
  (*   (*         go. *) *)
  (*   (*         (* GEP... *) *) *)
  (*   (*         unfold interp_cfg3. *) *)
  (*   (*         rewrite interp_intrinsics_trigger. *) *)
  (*   (*         cbn. *) *)
  (*   (*         unfold Intrinsics.F_trigger; cbn. *) *)
  (*   (*         rewrite subevent_subevent. *) *)
  (*   (*         rewrite interp_global_trigger; cbn. *) *)
  (*   (*         rewrite subevent_subevent. *) *)
  (*   (*         rewrite interp_local_bind, interp_local_trigger; cbn. *) *)
  (*   (*         rewrite subevent_subevent, bind_bind. *) *)
  (*   (*         rewrite interp_memory_bind, interp_memory_trigger; cbn. *) *)
  (*   (*         rewrite !bind_bind. *) *)
  (*   (*         destruct d0; cbn; try (unfold raise; rewrite bind_bind; apply has_post_bind; intros []). *) *)
  (*   (*         break_match_goal; cbn; try (unfold raise; rewrite bind_bind; apply has_post_bind; intros []). *) *)
  (*   (*         rewrite !bind_ret_l. *) *)
  (*   (*         rewrite interp_local_ret, interp_memory_ret, bind_ret_l. *) *)
  (*   (*         rewrite translate_ret, interp_intrinsics_ret, interp_global_ret, interp_local_ret, interp_memory_ret.  *) *)
  (*   (*         go... *) *)

  (*   (*   - auto... *) *)

  (*   (*   - auto... *) *)

  (*   (*   - auto... *) *)

  (*   (*   - destruct vec; cbn. *) *)
  (*   (*     go. *) *)
  (*   (*     eapply has_post_bind_strong. *) *)
  (*   (*     apply (IHe (Some d) g l m). *) *)
  (*   (*     intro_pure. *) *)
  (*   (*     clear IHe. *) *)
  (*   (*     induction idxs as [| n idxs IH]. *) *)
  (*   (*     + cbn. *) *)
  (*   (*       go... *) *)
  (*   (*     + cbn. *) *)
  (*   (*       break_match_goal... *) *)
  (*   (*       break_match_goal... *) *)
  (*   (*       go... *) *)
    
  (*   (*   - auto... *) *)

  (*   (*   - destruct cnd,v1,v2; cbn. *) *)
  (*   (*     go. *) *)
  (*   (*     eapply has_post_bind_strong; [apply IHe | ]. *) *)
  (*   (*     intro_pure. *) *)
  (*   (*     go. *) *)
  (*   (*     eapply has_post_bind_strong; [apply IHe0 |].  *) *)
  (*   (*     intro_pure. *) *)
  (*   (*     go. *) *)
  (*   (*     eapply has_post_bind_strong; [apply IHe1 |].  *) *)
  (*   (*     intro_pure. *) *)
  (*   (*     break_match_goal. *) *)
  (*   (*     go... *) *)
  (*   (*     unfold lift_undef_or_err. *) *)
  (*   (*     break_match_goal. *) *)
  (*   (*     break_match_goal... *) *)
  (*   (*     break_match_goal... *) *)
  (*   (*     go... *) *)
    
  (*   (*   - destruct v; cbn. *) *)
  (*   (*     go. *) *)
  (*   (*     eapply has_post_bind_strong. *) *)
  (*   (*     apply (IHe (Some d) g l m). *) *)
  (*   (*     intro_pure. *) *)
  (*   (*     clear IHe. *) *)
  (*   (*     go. *) *)
  (*   (*     apply has_post_bind_strong with (↑ (pure_P g l m)). *) *)
  (*   (*     { unfold pick_your_poison; *) *)
  (*   (*         break_match_goal; cbn; *) *)
  (*   (*           match goal with *) *)
  (*   (*             |- context [Ret _] => rewrite !translate_ret, interp_cfg3_ret; apply eutt_Ret; cbn; auto *) *)
  (*   (*           | |- context [concretize_or_pick] => apply concretize_or_pick_is_pure *) *)
  (*   (*           | _ => idtac *) *)
  (*   (*           end... *) *)
  (*   (*     } *) *)
  (*   (*     intros (? & ? & ? & ?) (-> & -> & ->). *) *)
  (*   (*     go... *) *)
    
  (*   (* Admitted. *) *)

  (* End ExpPure. *)
End ExpLemmas.
