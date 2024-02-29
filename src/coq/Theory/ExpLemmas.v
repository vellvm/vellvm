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
     Eq.Eqit
     TranslateFacts
     Interp.InterpFacts
     Events.State
     Events.StateFacts.

From TwoPhase Require Import
     Utilities
     Syntax
     Semantics
     Theory.StatePredicates
     Theory.InterpreterCFG
     TwoPhaseIntegers.

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
        subevent X (LU_to_exp (subevent X e)) = subevent (F:=exp_E) X e.
    Proof using.
      reflexivity.
    Qed.

    Lemma exp_to_instr_Global : forall {X} (e : LLVMGEnvE X),
        subevent X (exp_to_instr (subevent X e)) = subevent (F:=instr_E) X e.
    Proof using.
      reflexivity.
    Qed.

    Lemma LU_to_exp_Local : forall {X} (e : LLVMEnvE X),
        subevent X (LU_to_exp (subevent X e)) = subevent (F:=exp_E) X e.
    Proof using.
      reflexivity.
    Qed.

    Lemma exp_to_instr_Local : forall {X} (e : LLVMEnvE X),
        subevent X (exp_to_instr (subevent X e)) = subevent (F:=instr_E) X e.
    Proof using.
      reflexivity.
    Qed.

    Lemma exp_to_instr_Memory : forall {X} (e : MemoryE X),
        subevent X (exp_to_instr (subevent X e)) = subevent (F:=instr_E) X e.
    Proof using.
      reflexivity.
    Qed.

    Lemma exp_to_instr_Pick : forall {X} (e : PickE X),
        subevent X (exp_to_instr (subevent X e)) = subevent (F:=instr_E) X e.
    Proof using.
      reflexivity.
    Qed.

    Lemma exp_to_instr_UB : forall {X} (e : UBE X),
        subevent X (exp_to_instr (subevent X e)) = subevent (F:=instr_E) X e.
    Proof using.
      reflexivity.
    Qed.

    Lemma exp_to_instr_Fail : forall {X} (e : FailureE X),
        subevent X (exp_to_instr (subevent X e)) = subevent (F:=instr_E) X e.
    Proof using.
      reflexivity.
    Qed.

    Lemma FUB_to_exp_UB : forall {X} (e : UBE X),
        subevent X (FUB_to_exp (subevent X e)) = subevent (F:=exp_E) X e.
    Proof using.
      reflexivity.
    Qed.

    Lemma FUB_to_exp_Fail : forall {X} (e : FailureE X),
        subevent X (FUB_to_exp (subevent X e)) = subevent (F:=exp_E) X e.
    Proof using.
      reflexivity.
    Qed.

  End Translations.

  (* TO MOVE *)

  Lemma repr_intval (i: int64):
    Int64.repr (Int64.intval i) = i.
  Proof using.
    replace (Int64.intval i) with (Int64.unsigned i).
    - apply Int64.repr_unsigned.
    - destruct i.
      reflexivity.
  Qed.

  Lemma intval_to_from_nat_id:
    forall n, (Z.of_nat (Z.to_nat (Int64.intval n))) = Int64.intval n.
  Proof using.
    intros.
    destruct n.
    cbn.  lia.
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
    Proof using.
      intros; cbn.
      go.
      step.
      go.
      reflexivity.
    Qed.

    Lemma denote_exp_LR :forall g l id v τ,
        Maps.lookup id l = Some v ->
        ⟦ EXP_Ident (ID_Local id) at τ ⟧e2 g l ≈ Ret (l,(g,v)).
    Proof using.
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
    Proof using.
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
    Proof using.
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
    Proof using.
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
    (* Proof using. *)
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
    Proof using.
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
    Proof using.
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
    Proof using.
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
    Proof using.
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

End ExpLemmas.
