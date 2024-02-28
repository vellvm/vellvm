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

From Vellvm Require Import
     Utilities
     Syntax
     Semantics
     Theory.StatePredicates
     Theory.InterpreterCFG
     VellvmIntegers.

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

  (* TODO: This section is kind of duplicated, but I don't know where it should live *)
  Section uvalue_dvalue_to_uvalue_M.
    (* TODO: Move this *)
    Lemma map_monad_map_itree :
      forall {E} A B C
        (f : B -> itree E C)
        (g : A -> B)
        (xs : list A),
        eq_itree eq (map_monad f (map g xs)) (map_monad (fun x => f (g x)) xs).
    Proof.
      intros. induction xs.
      - simpl. reflexivity.
      - simpl.
        setoid_rewrite IHxs.
        reflexivity.
    Qed.

    (* TODO: Move this *)
    Lemma bind_helper_itree :
      forall {E} A B (m : itree E A) (f : A -> itree E B),
        eq_itree eq (bind m f) ((bind (bind m ret) f)).
    Proof.
      intros.
      setoid_rewrite Eqit.bind_ret_r.
      reflexivity.
    Qed.

    (* TODO: Move this *)
    Lemma map_monad_g_itree :
      forall {E} A B C (f : A -> itree E B) (g : list B -> C) (xs:list A) (zs : list B)
        (EQ2 : eq_itree eq (bind (map_monad f xs) (fun ys => ret ys)) (ret (zs))),
        eq_itree eq (bind (map_monad f xs) (fun ys => ret (g ys))) (ret (g zs)).
    Proof.
      intros.
      rewrite bind_helper_itree.
      rewrite EQ2.
      setoid_rewrite Eqit.bind_ret_l.
      reflexivity.
    Qed.

    Lemma map_monad_cons_ret_itree :
      forall {E} A B (f : A -> itree E B) (a:A) (xs:list A) (z : B) (zs : list B)
        (EQ2 : eq_itree eq (bind (map_monad f xs) (fun ys => ret ys)) (ret (zs))),
        eq_itree eq (bind (map_monad f xs) (fun ys => ret (z::ys))) (ret ((z::zs))).
    Proof.
      intros.
      apply map_monad_g_itree with (g := (fun ys => z::ys)).
      assumption.
    Qed.

    (* TODO: this is duplicated from EquivExpr *)
    Lemma uvalue_dvalue_to_uvalue_M :
      forall {E} `{O: OOME -< E} `{F: FailureE -< E} `{U: UBE -< E} d,
        eq_itree eq (concretize_uvalueM (itree E) (fun dt : dtyp =>
        @lift_err_RAISE_ERROR dvalue (itree E) (@Monad_itree E) (@RAISE_ERR_ITREE_FAILUREE E F)
          (default_dvalue_of_dtyp dt)) _ (fun (A : Type) (x : itree E A) => x) (dvalue_to_uvalue d)) (ret d).
    Proof.
      intros.
      induction d; simpl; try reflexivity.
      - rewrite map_monad_map_itree.
        apply map_monad_g_itree;
        induction fields; simpl; auto.
       + rewrite bind_ret_l.
         reflexivity.
       + rewrite H.
          setoid_rewrite bind_ret_l.
          rewrite bind_bind.
          setoid_rewrite bind_ret_l.
          apply map_monad_cons_ret_itree.
          exact a.
          apply IHfields.
          intros. apply H. apply in_cons. assumption.
          apply in_eq.

       (* TODO: automate this *)
      -  rewrite map_monad_map_itree;
          apply map_monad_g_itree;
          induction fields; simpl.
        + rewrite bind_ret_l.
          reflexivity.
        + rewrite H.
          setoid_rewrite bind_ret_l.
          rewrite bind_bind.
          setoid_rewrite bind_ret_l.
          apply map_monad_cons_ret_itree.
          exact a.
          apply IHfields.
          intros. apply H. apply in_cons. assumption.
          apply in_eq.


      - rewrite map_monad_map_itree;
          apply map_monad_g_itree;
          induction elts; simpl.
        + rewrite bind_ret_l.
          reflexivity.
        + rewrite H.
          setoid_rewrite bind_ret_l.
          rewrite bind_bind.
          setoid_rewrite bind_ret_l.
          apply map_monad_cons_ret_itree.
          exact a.
          apply IHelts.
          intros. apply H. apply in_cons. assumption.
          apply in_eq.


      - rewrite map_monad_map_itree;
          apply map_monad_g_itree;
          induction elts; simpl.
        + rewrite bind_ret_l.
          reflexivity.
        + rewrite H.
          setoid_rewrite bind_ret_l.
          rewrite bind_bind.
          setoid_rewrite bind_ret_l.
          apply map_monad_cons_ret_itree.
          exact a.
          apply IHelts.
          intros. apply H. apply in_cons. assumption.
          apply in_eq.
    Qed.
  End uvalue_dvalue_to_uvalue_M.

  Section ExpLemmas.
    (* TODO: Does this lemma belong here? *)
    Lemma concretize_if_no_undef_or_poison_dvalue_to_uvalue :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E} v,
        @eq_itree E _ _ eq (concretize_if_no_undef_or_poison (dvalue_to_uvalue v)) (ret (dvalue_to_uvalue v)).
    Proof.
      intros E O F U v.
      unfold concretize_if_no_undef_or_poison.
      break_match; try reflexivity.
      unfold concretize_uvalue.
      rewrite uvalue_dvalue_to_uvalue_M.
      setoid_rewrite bind_ret_l.
      reflexivity.
    Qed.

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
      rewrite concretize_if_no_undef_or_poison_dvalue_to_uvalue.
      go.
      cbn.
      rewrite translate_ret.
      go.
      reflexivity.
    Qed.

    (* This doesn't necessarily hold because we don't know if `v` was
       concretized eagerly. We should know that `v` is equivalent to
       the value on the left-hand-side, though.
     *)
    (* Lemma denote_exp_LR :forall g l id v τ, *)
    (*     Maps.lookup id l = Some v -> *)
    (*     ⟦ EXP_Ident (ID_Local id) at τ ⟧e2 g l ≈ Ret (l,(g,v)). *)
    (* Proof using. *)
    (*   intros; cbn. *)
    (*   go. *)
    (*   step. *)
    (*   go. *)
    (*   rewrite concretize_if_no_undef_or_poison_dvalue_to_uvalue. *)
    (*   go. *)
    (*   cbn. *)
    (*   rewrite translate_ret. *)
    (*   go. *)
    (*   reflexivity. *)
    (* Qed. *)

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
      rewrite concretize_if_no_undef_or_poison_dvalue_to_uvalue.
      go.
      cbn.
      rewrite translate_ret.
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
      rewrite concretize_if_no_undef_or_poison_dvalue_to_uvalue.
      go.
      cbn.
      rewrite translate_ret.
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
      cbn.
      go.
      cbn.
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
