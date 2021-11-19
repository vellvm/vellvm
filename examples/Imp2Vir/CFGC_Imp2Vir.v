From Coq Require Import
     Lists.List
     Strings.String
     FSets.FMapList
     Structures.OrderedTypeEx
     ZArith.
Module Import StringMap := Coq.FSets.FMapList.Make(String_as_OT).

From ExtLib Require Import
     Structures.Monads
     Data.Monads.OptionMonad.
Import MonadNotation.

From Vellvm Require Import
     Syntax
     SurfaceSyntax .

From Imp2Vir Require Import Imp CFGC_Combinators CFGC_Interface.


Import ListNotations.
Import VIR_Notations.
Notation ocfg := (ocfg typ).

Section FreshnessMonad.

(* TODO it is probable already defined somewhere in Vellvm *)
Definition OptionT (m : Type -> Type) : Type -> Type :=
  fun x => m (option x).

#[global] Instance optionT m `{Monad m} : Monad (OptionT m) :=
  {|
    ret := fun _ x => ret (Some x) ;
    bind :=  fun x y (c : m (option x)) (k : x -> m (option y)) =>
               t <- c ;;
               match t with
               | None => ret None
               | Some v => k v
               end
  |}.

End FreshnessMonad.

Section CompileExpr.

Definition texp_i1 (reg : int) : texp typ :=
  (TYPE_I 1, EXP_Ident (ID_Local (Anon reg))) .

Definition texp_i32 (reg : int) : texp typ :=
  (TYPE_I 32, EXP_Ident (ID_Local (Anon reg))) .

Definition texp_ptr (addr : int) : texp typ :=
  (TYPE_Pointer (TYPE_I 32), EXP_Ident (ID_Local (Anon addr))) .

Definition compile_binop (reg1 reg2 reg:int) (op: ibinop): code typ :=
  [(IId (Anon reg),
    INSTR_Op (OP_IBinop op (TYPE_I 32)
      (EXP_Ident (ID_Local (Anon reg1)))
      (EXP_Ident (ID_Local (Anon reg2)))))].

Fixpoint compile_expr (e: expr) (env: StringMap.t int):
  OptionT fresh (int * code typ) :=
  match e with
  | Var x =>
      (match (StringMap.find x env) with
       | None => ret (None)
       | Some addr =>
           next_reg <- freshReg ;;
           ret (Some (next_reg,
                       [(IId (Anon next_reg)
                          , INSTR_Load false (TYPE_I 32) (texp_ptr addr) None)]))
       end)
  | Lit n =>
      next_reg <- freshReg ;;
      ret (Some (next_reg,
                  ([(IId (Anon next_reg),
                      INSTR_Op
                        (OP_IBinop
                           (LLVMAst.Add false false)
                           (TYPE_I 32)
                           (EXP_Integer (Z.of_nat n))
                           (EXP_Integer (Z.of_nat 0))))])))
  | Plus e1 e2 =>
      ('(reg1, instrs1) <- compile_expr e1 env;;
       '(reg2, instrs2) <- compile_expr e2 env;;
       ret (reg2, instrs1 ++ instrs2 ++ compile_binop reg1 reg2 reg2 (LLVMAst.Add false false)))
  | Minus e1 e2 =>
      ('(reg1, instrs1) <- compile_expr e1 env;;
       '(reg2, instrs2) <- compile_expr e2 env;;
       ret (reg2, instrs1 ++ instrs2 ++ compile_binop reg1 reg2 reg2 (LLVMAst.Sub false false)))
  | Mult e1 e2 =>
      ('(reg1, instrs1) <- compile_expr e1 env;;
       '(reg2, instrs2) <- compile_expr e2 env;;
       ret (reg2, instrs1 ++ instrs2 ++ compile_binop reg1 reg2 reg2 (LLVMAst.Mul false false)))
  end.

Open Scope Z_scope.
Definition compile_assign (x: Imp.var) (e: expr) (env : StringMap.t int)
  : OptionT fresh ((StringMap.t int) * code typ) :=
  '(expr_reg, ir) <- compile_expr e env ;;
  match (StringMap.find x env) with
  | Some id =>
      reg <- freshReg ;;
      ret (Some
             (env, ir ++ [(IVoid reg,
                            INSTR_Store false
                                        (texp_i32 expr_reg) (texp_ptr id) None)]))
  | None =>
      reg1 <- freshReg ;;
      reg2 <- freshReg ;;
      ret (Some
             (StringMap.add x reg1 env,
               ir ++ [(IId (Anon reg1), INSTR_Alloca (TYPE_I 32) None None)] ++
                  [(IVoid reg2, INSTR_Store false (texp_i32 expr_reg) (texp_ptr reg1) None)]
          ))
  end.

Definition compile_cond (e : expr) (env : StringMap.t int)
  : OptionT fresh (int * (StringMap.t int) * code typ) :=
  '(expr_reg, ir) <- compile_expr e env;;
  reg <- freshReg ;;
  ret (Some (reg, env, ir ++
               [(IId (Anon (expr_reg + 1)),
                  INSTR_Op (OP_ICmp Ne (TYPE_I 32) (EXP_Ident (ID_Local (Anon expr_reg))) (EXP_Integer 0))
      )])).
Close Scope Z_scope.

End CompileExpr.


Section Imp2Vir.

Definition default_bid := Anon 0.

Fixpoint compile_imp (s : stmt) (env: StringMap.t int) :
  OptionT fresh ( (StringMap.t int) * dcfg ) :=
  match s with
  | Skip =>
      dg <- mk_block [] ;;
      ret (Some (env, dg))
  | Assign x e =>
      ('(env, c) <- compile_assign x e env ;;
       dg <- mk_block c ;;
       ret (Some (env, dg)))
  | Seq l r =>
      ( '(env1, dg1) <- compile_imp l env;;
        '(env2, dg2) <- compile_imp r env1;;
        let out1 := List.hd default_bid (fst (outs dg1)) in
        let in2 := List.hd default_bid (fst (ins dg2)) in
        'g <- mk_seq dg1 dg2 out1 in2 ;;
        ret (Some (env2, g)))
  | If e l r =>
      ('(cond_reg, env, expr_code) <- compile_cond e env ;;
       reg <- freshReg ;;
       '(env1, dgT) <- compile_imp l env;;
       '(env2, dgF) <- compile_imp r env1;;
       dgCond <- mk_block expr_code ;;
       let inT := List.hd default_bid (fst (ins dgT)) in
       let inF := List.hd default_bid (fst (ins dgF)) in
       dgBody <- mk_branch (texp_i1 cond_reg) dgT dgF inT inF ;;
       let outT := List.hd default_bid (fst (outs dgT)) in
       let outF := List.hd default_bid (fst (outs dgF)) in
       dgBody <- mk_join dgBody outT outF ;;
       let inCond := List.hd default_bid (fst (ins dgCond)) in
       let outBody := List.hd default_bid (fst (outs dgBody)) in
       dg <- mk_seq dgCond dgBody inCond outBody ;;
       ret (Some (env2, dg)))
  | While e b =>
      ('(cond_reg, env, expr_code) <- compile_cond e env ;;
       '(env1, dgB) <- compile_imp b env ;;
       let inB := List.hd default_bid (fst (ins dgB)) in
       let outB := List.hd default_bid (fst (outs dgB)) in
       'dg <- mk_while expr_code (texp_i1 cond_reg) dgB inB outB ;;
       ret (Some (env1, dg)))
  end.

Definition compile (s : stmt) :=
  snd (
      ('( _, (make_dcfg g _ _)) <- compile_imp s (StringMap.empty int);;
       (ret g))
        fresh_init).


Section Examples.
(** Examples *)
Definition fact_ir := (compile (Imp.fact "a" "b" 5)).
Definition infinite_loop_ir := (compile (infinite_loop)).
Definition if_ir := (compile (trivial_if "a" "b" 0)).
Definition seq_ir := (compile (trivial_seq "a" "b" 42)).
Definition nested_if_ir := (compile (nested_if "a" "b" 42 43)).
Definition nested_if2_ir := (compile (nested_if2 "a" "b" 42 43)).

Compute infinite_loop_ir.
Compute fact_ir.
Compute if_ir.
Compute seq_ir.
Compute nested_if_ir.
Compute nested_if2_ir.
End Examples.


(** WF compiler *)
Section Theory.

From Coq Require Import Lia.
From ExtLib Require Import FMapAList.
From Vellvm Require Import
     Semantics
     Theory
     Utils.Tactics.

From ITree Require Import
     ITree
     ITreeFacts.

Import SemNotations.
Import ITreeNotations.

From Imp2Vir Require Import CFGC_DenotationsCombinators.

(* TODO: wf_dcfg instead of wf_ocfg_bid and
          improve wf_dcfg such that it contains
          wf_ocfg_bid. *)
Theorem wf_compiler_aux : forall s env σ σ' cfg nenv ,
  (compile_imp s env) σ =
      (σ', Some (nenv, cfg)) -> wf_ocfg_bid (graph cfg).
Proof.
  intros s.
  induction s ; intros.
  - (* Assign *)
    cbn in H.
    repeat flatten_all ;
    inv H ; inv Heq; inv Heq2 ;
    apply wf_bid_cfg_block.
  - (* Seq *)
    admit.
  - (* If *)
    admit.
  - (* While *)
    admit. (* I need an invariant on the compiler *)
  - (* Skip *)
    cbn in H ; inv H ; repeat flatten_all ; inv H1.
    inv Heq ; apply wf_bid_cfg_block.
Admitted.



(** Correctness compiler *)

(* Relation between Imp env and vellvm env *)

Definition Rmem (vmap : StringMap.t int)(env : Imp.env) (venv : local_env) (vmem : memory_stack) : Prop :=
  forall k v, alist_find k env = Some v <-> (
    exists reg, StringMap.find k vmap = Some reg /\
      exists addr, alist_find (Anon reg) venv = Some (UVALUE_Addr addr) /\
        exists v32, read vmem addr (DTYPE_I (Npos 32%positive)) = inr (UVALUE_I32 v32) /\
          Int32.intval v32 = Z.of_nat v
  ).

Definition Rimpvir
  (vmap : StringMap.t int)
  (env1 : Imp.env * unit)
  (env2 : memory_stack * (local_env * (global_env * (block_id * block_id + uvalue)))) :
  Prop :=
  Rmem vmap (fst env1) (fst (snd env2)) (fst env2).

Theorem compile_correct : forall (σ : FST) env (p : stmt) (σ' : FST)
                            env' (o : dcfg) (input output : block_id)
                            mem from to genv lenv vmem,

  (* The environments of Imp and Vir are related *)
  Rmem env mem lenv vmem ->
  (* The compilation of p with env produce a new env' and an ir *)
  (compile_imp p env) σ =
      (σ', Some (env', o))  ->
  eutt (Rimpvir env')
       (interp_imp (denote_imp p) mem)
       (interp_cfg3 (denote_cfg (graph o) from to) genv lenv vmem).
Proof.
  intros.
  induction p.
  - (* Assign *)
    simpl in *.
    repeat (flatten_all) ; [| discriminate H0].
    inv H0.
    assert ( I_to : to = input ) by admit. (* I need to introduce an invariant here *)
    rewrite I_to ; clear I_to.
    admit.
  - (* Seq *)
    simpl in *.
    repeat (flatten_all) ; try discriminate.
    inv H0.
    admit.
  - (* If *) admit.
  - (* While *) admit.
  - (* Skip *)
    simpl in *.
    repeat flatten_all.
    inv H0.
    assert ( I_to : to = input ) by admit.
    (* I probably need to introduce an invariant here *)
    rewrite I_to ; clear I_to.
    admit.
Admitted.
End Theory.

End Imp2Vir.
