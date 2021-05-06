From Coq Require Import
     FSets.FMapList
     Lists.List
     Strings.String
     Structures.OrderedTypeEx
     ZArith.
Import ListNotations.

Module Import StringMap := Coq.FSets.FMapList.Make(String_as_OT).

From ExtLib Require Import
     Structures.Monads
     Data.Monads.OptionMonad.
Import MonadNotation.

From Vellvm Require Import
     Syntax.

Require Import Imp.

Open Scope Z_scope.

Section CompileExpr.

Definition texp_i32 (reg : int) : texp typ :=
  (TYPE_I 32, EXP_Ident (ID_Local (Anon reg)))
.

Definition texp_ptr (reg : int) : texp typ :=
  (TYPE_I 32, EXP_Ident (ID_Local (Anon reg)))
.

Definition compile_binop (reg1 reg2 reg:int) (op: ibinop): code typ :=
  [((IId (Anon reg)),
    INSTR_Op (OP_IBinop (LLVMAst.Add false false) (TYPE_I 32)
      (EXP_Ident (ID_Local (Anon reg1)))
      (EXP_Ident (ID_Local (Anon reg2)))))].

(** Expressions are compiled straightforwardly.
    The argument [next_reg] is the number of registers already introduced to compile
    the expression, and is used for the name of the next one.
    The result of the computation [compile_expr l e env] always ends up stored in [l].
 *)
Fixpoint compile_expr (next_reg:int) (e: expr) (env: StringMap.t int): option (int * code typ) :=
  match e with
  | Var x =>
    addr <- find x env;;
    ret (next_reg, [(IId (Anon next_reg), INSTR_Load false (TYPE_I 32) (texp_ptr addr) None)])
  | Lit n => Some(next_reg, [(IId (Anon next_reg), INSTR_Op (EXP_Integer (Z.of_nat n)))])
  | Plus e1 e2 =>
    '(reg1, instrs1) <- compile_expr next_reg e1 env;;
    '(reg2, instrs2) <- compile_expr (reg1 + 1)%Z e2 env;;
    ret (reg2 + 1, instrs1 ++ instrs2 ++ compile_binop reg1 reg2 (reg2 + 1) (Add false false))
  | Minus e1 e2 =>
    '(reg1, instrs1) <- compile_expr next_reg e1 env;;
    '(reg2, instrs2) <- compile_expr (reg1 + 1) e2 env;;
    ret (reg2 + 1, instrs1 ++ instrs2 ++ compile_binop reg1 reg2 (reg2 + 1) (Sub false false))
  | Mult e1 e2 =>
    '(reg1, instrs1) <- compile_expr next_reg e1 env;;
    '(reg2, instrs2) <- compile_expr (reg1 + 1) e2 env;;
    ret (reg2 + 1, instrs1 ++ instrs2 ++ compile_binop reg1 reg2 (reg2 + 1) (Mul false false))
  end.

Definition compile_assign (next_reg : int) (x: Imp.var) (e: expr) (env : StringMap.t int)
: option (int * (StringMap.t int) * code typ) :=
  '(expr_reg, ir) <- compile_expr next_reg e env;;
  ret match find x env with
  | Some id => ((expr_reg + 2), env,
      ir ++ [(IId (Anon (expr_reg + 1)), INSTR_Store false (texp_i32 expr_reg) (texp_ptr id) None)]
      )
  | None => (expr_reg + 3, add x next_reg env,
      ir ++ [(IId (Anon (expr_reg + 1)), INSTR_Alloca (TYPE_I 32) None None)] ++
      [(IId (Anon (expr_reg + 2)), INSTR_Store false (texp_i32 expr_reg) (texp_ptr (expr_reg + 1)) None)]
      )
  end.

End CompileExpr.
