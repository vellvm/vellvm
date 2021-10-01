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
From Imp2Vir Require Import Imp Fin.

Require Import Vec CompileExpr CvirCombinators CvirCombinatorsWF.

From Vellvm Require Import SurfaceSyntax.
Import VIR_Notations.

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
      let body := merge_cvir ir (block_cvir []) : cvir 2 2 in
      let body := seq_cvir br body in
      let ir := loop_cvir_open body in
      ret (next_reg, env, ir) : option (int * (StringMap.t int) * cvir 1 1)

    | If e l r =>
      '(cond_reg, expr_code) <- compile_cond next_reg e env;;
      '(next_reg, _, ir_l) <- compile (cond_reg + 1) l env;;
      '(next_reg, _, ir_r) <- compile next_reg r env;;
      let ir_cond := branch_cvir expr_code (texp_i1 cond_reg) : cvir 1 2 in
      let ir_body := merge_cvir ir_l ir_r in
      let ir := seq_cvir ir_cond ir_body in
      let ir := join_cvir ir : cvir 1 1 in
      ret (next_reg, env, ir) : option (int * (StringMap.t int) * cvir 1 1)
    end.

  Theorem compile_WF : forall s next_reg next_reg' env env' ir,
compile next_reg s env = Some(next_reg', env', ir) -> cvir_WF ir.
  Proof.
    induction s ; intros ? ? ? ? ? Heqo ; simpl in Heqo.
    - repeat break_match ; try discriminate.
      inversion Heqo.
      subst. apply block_cvir_WF.
    - repeat break_match ; try discriminate.
      inversion Heqo.
      subst.
      simpl in *.
      apply IHs1 in Heqo0.
      apply IHs2 in Heqo1.
      apply seq_cvir_WF ; assumption.
    - repeat break_match ; try discriminate.
      inversion Heqo.
      subst.
      simpl in *.
      apply IHs1 in Heqo1.
      apply IHs2 in Heqo2.
      apply join_cvir_WF.
      apply seq_cvir_WF.
      apply branch_cvir_WF.
      apply merge_cvir_WF with (ni1:= 1%nat) (no1:= 1%nat) (ir1:= c0) in Heqo2 ; assumption.
      (* I don't understand why `apply merge_cvir_WF`` doesn't work *)
    - repeat break_match ; try discriminate.
      inversion Heqo.
      subst.
      apply IHs in Heqo1.
      apply loop_open_cvir_WF.
      apply seq_cvir_WF.
      + apply branch_cvir_WF.
      + apply merge_cvir_WF with (ni1:= 1%nat) (no1:= 1%nat)
                                 (ni2:= 1%nat) (no2:= 1%nat)
                                 (ir1:= c0) (ir2:= (block_cvir [])) ;
          [ assumption | apply block_cvir_WF ].
    - inversion Heqo. apply block_cvir_WF.
Qed.

Definition compile_imp_cvir (ir : cvir 1 1) : program :=
  let ir := seq_cvir ir (ret_cvir nil (texp_i32 10)) in (* hack to print the result of fact *)
  let vt_seq := map Anon (map Z.of_nat (seq 2 (n_int ir))) in
  let blocks := (blocks ir) (cons (Anon 1) (empty raw_id)) (empty raw_id) vt_seq in
  let body := (entry_block, blocks) in
  let decl := mk_declaration
    (Name "main")
    (TYPE_Function (TYPE_I 32) [TYPE_I 64 ; TYPE_Pointer (TYPE_Pointer (TYPE_I 8))])
    (nil, nil) None None None None nil None None None
  in
  let def := mk_definition fnbody decl nil body in
  TLE_Definition def.

Definition compile_program (s : stmt) (env : StringMap.t int) :
  option program :=
  '(_, _, ir) <- compile 0 s env;;
  ret (compile_imp_cvir ir).



Definition fact_ir := (compile_program (fact "a" "b" 5) (StringMap.empty int)).
Definition infinite_loop_ir := (compile_program (infinite_loop) (StringMap.empty int)).
Definition if_ir := (compile_program (trivial_if "a" "b" 0) (StringMap.empty int)).
Definition seq_ir := (compile_program (trivial_seq "a" "b" 42) (StringMap.empty int)).
Definition nested_if_ir := (compile_program (nested_if "a" "b" 42 43) (StringMap.empty int)).
Definition nested_if2_ir := (compile_program (nested_if2 "a" "b" 42 43) (StringMap.empty int)).


(* Compute infinite_loop_ir. *)
(* Compute seq_ir. *)
(* Compute if_ir. *)
(* Compute nested_if_ir. *)
(* Compute nested_if2_ir. *)
(* Compute fact_ir. *)
End Imp2Cvir.
