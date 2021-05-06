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
     Syntax.

Require Import Imp Vec CompileExpr CvirCombinators.

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
      let ir := loop_cvir_open body in
      let ir := mk_cvir (fun vi vo vt => (blocks ir) vi (rev vo) vt) in
      ret (next_reg, env, ir) : option (int * (StringMap.t int) * cvir 1 1)
  (*| If e l r =>
      '(expr_reg, expr_ir) <- compile_expr next_reg e env;;
      '(next_reg, _, ir_l) <- compile (expr_reg + 1) l env;;
      '(next_reg, _, ir_r) <- compile next_reg r env;;
      ret (next_reg, env, cond_cvir ir_l ir_r (texp_i32 expr_reg)
      )*)
  | _ => None
  end.

Definition compile_program (s : stmt) (env : StringMap.t int) :
  option program :=
  '(_, _, ir) <- compile 0 s env;;
  ret (compile_cvir ir).

Definition fact_ir := (compile_program (fact "a" "b" 5) (StringMap.empty int)).

Eval compute in fact_ir.

End Imp2Cvir.
