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
From tutorial Require Import Imp Fin.

Require Import Vec CompileExpr CvirCombinators CvirCombinatorsWF.

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
      '(cond_reg, expr_ir) <- compile_cond next_reg e env;;
      '(next_reg, _, ir) <- compile (cond_reg + 1) b env;;
      let br := branch_cvir expr_ir (texp_i1 cond_reg) in
      let body := seq_cvir br ir in
      let body := focus_output_cvir body (exist _ 1%nat Nat.lt_1_2) in
      let ir := loop_cvir_open body in
      ret (next_reg, env, ir) : option (int * (StringMap.t int) * cvir 1 1)
  | If e l r =>
      '(cond_reg, expr_ir) <- compile_cond next_reg e env;;
      '(next_reg, _, ir_l) <- compile (cond_reg + 1) l env;;
      '(next_reg, _, ir_r) <- compile next_reg r env;;
      let ir := branch_cvir expr_ir (texp_i1 cond_reg) : cvir 1 2 in
      let ir := seq_cvir ir ir_l : cvir 1 2 in
      let ir := seq_cvir ir ir_r : cvir 1 2 in
      let ir := join_cvir ir : cvir 1 1 in
      ret (next_reg, env, ir) : option (int * (StringMap.t int) * cvir 1 1)
  end.

Theorem compile_WF : forall s next_reg next_reg' env env' ir,
  compile next_reg s env = Some(next_reg', env', ir) -> cvir_ids_WF ir /\ unique_bid ir.
Proof.
  induction s ; intros ? ? ? ? ? Heqo ; simpl in Heqo.
  - repeat break_match ; try discriminate.
    inversion Heqo.
    subst.
    split; [apply block_cvir_id_WF | apply block_cvir_unique].
  - repeat break_match ; try discriminate.
    inversion Heqo.
    subst.
    simpl in *.
    apply IHs1 in Heqo0.
    apply IHs2 in Heqo1.
    split; [ apply (seq_cvir_id_WF 1 0) | apply (seq_cvir_unique 1 0)] ; simpl in * ; tauto.
  - repeat break_match ; try discriminate.
    inversion Heqo.
    subst.
    simpl in *.
    apply IHs1 in Heqo1.
    apply IHs2 in Heqo2.
    split; [ apply join_cvir_id_WF | apply join_cvir_unique ];
    [> apply (seq_cvir_id_WF 1 1) | apply (seq_cvir_unique 1 1)]; try tauto;
    (apply (seq_cvir_id_WF 1 1) + apply (seq_cvir_unique 1 1)); try tauto;
    (apply branch_cvir_id_WF + apply branch_cvir_unique).
  - repeat break_match ; try discriminate.
    inversion Heqo.
    subst.
    apply IHs in Heqo1.
    split; [ apply loop_cvir_open_id_WF | apply loop_cvir_open_unique ];
    [> apply focus_output_cvir_id_WF | apply focus_output_cvir_unique ];
    [> eapply (seq_cvir_id_WF 1 1) | eapply (seq_cvir_unique 1 1) ];
    (apply branch_cvir_id_WF + apply branch_cvir_unique + tauto).
  - inversion Heqo.
    split; [ apply block_cvir_id_WF | apply block_cvir_unique ].
Qed.

Definition compile_program (s : stmt) (env : StringMap.t int) :
  option program :=
  '(_, _, ir) <- compile 0 s env;;
  ret (compile_cvir ir).

Definition fact_ir := (compile_program (fact "a" "b" 5) (StringMap.empty int)).

Eval compute in fact_ir.

End Imp2Cvir.
