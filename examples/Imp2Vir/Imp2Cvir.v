From Coq Require Import
     Lists.List
     Strings.String
     ZArith.
Import ListNotations.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.OptionMonad.
Import MonadNotation.

From Vellvm Require Import
     Syntax
     Utils.Tactics.
From tutorial Require Import Fin.

Require Import Imp Vec CompileExpr CvirCombinators CvirCombinatorsWF.

Open Scope Z_scope.

Section Imp2Cvir.

Fixpoint compile (next_reg : int) (s : stmt) (env: StringMap.t int)
: option (int * (StringMap.t int) * cvir 1 1) :=
  match s with
  | Skip => Some(next_reg, env, block_cvir [])
  | Assign x e =>
      '(next_reg, env, ir) <- compile_assign next_reg x e env;;
      ret (next_reg, env, block_cvir ir)
  | Seq l r =>
      '(next_reg, env, ir_l) <- compile next_reg l env;;
      '(next_reg, env, ir_r) <- compile next_reg r env;;
       ret (next_reg, env, seq_cvir ir_l ir_r)
  | While e b =>
      '(expr_reg, expr_ir) <- compile_expr next_reg e env;;
      '(next_reg, _, ir) <- compile (expr_reg + 1) b env;;
      let br := branch_cvir expr_ir (texp_i32 expr_reg) in
      let body := seq_cvir br ir in
      let body := focus_output_cvir body (exist _ 1%nat Nat.lt_1_2) in
      let ir := loop_cvir_open body in
      ret (next_reg, env, ir) : option (int * (StringMap.t int) * cvir 1 1)
  (*| If e l r =>
      '(expr_reg, expr_ir) <- compile_expr next_reg e env;;
      '(next_reg, _, ir_l) <- compile (expr_reg + 1) l env;;
      '(next_reg, _, ir_r) <- compile next_reg r env;;
      ret (next_reg, env, cond_cvir ir_l ir_r (texp_i32 expr_reg)
      )*)
  | _ => None
  end.

Theorem compile_WF : forall s next_reg env,
  match (compile next_reg s env) with
  | Some p => cvir_ids_WF (snd p)
  | None => True
  end.
Proof.
  induction s ; intros ; (destruct (compile next_reg _ env) eqn:? ; [| tauto ]) ; simpl in Heqo.
  - repeat break_match ; try discriminate.
    inversion Heqo.
    subst.
    apply block_cvir_id_WF.
  - repeat break_match ; try discriminate.
    inversion Heqo.
    subst.
    simpl in *.
    specialize (IHs1 next_reg env).
    rewrite Heqo0 in IHs1.
    specialize (IHs2 i t).
    rewrite Heqo1 in IHs2.
    apply (seq_cvir_id_WF 1 0) ; simpl in *; assumption.
  - discriminate Heqo.
  - repeat break_match ; try discriminate.
    inversion Heqo.
    subst.
    simpl in *.
    apply loop_cvir_open_id_WF.
    apply focus_output_cvir_id_WF.
    eapply (seq_cvir_id_WF 1 1 0 1). (* FIXME *)
    apply branch_cvir_id_WF.
    specialize (IHs (i + 1) env).
    rewrite Heqo1 in IHs.
    apply IHs.
  - inversion Heqo.
    apply block_cvir_id_WF.
Qed.

Definition compile_program (s : stmt) (env : StringMap.t int) :
  option program :=
  '(_, _, ir) <- compile 0 s env;;
  ret (compile_cvir ir).

Definition fact_ir := (compile_program (fact "a" "b" 5) (StringMap.empty int)).

Eval compute in fact_ir.

End Imp2Cvir.
