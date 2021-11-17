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

From Imp2Vir Require Import Imp CFGC_Combinators.


Import ListNotations.
Import VIR_Notations.
Notation ocfg := (ocfg typ).

Section FreshnessMonad.

(* Variable (name : nat -> block_id). *)
(* Hypothesis (nameInj_eq : forall n n', n = n' -> name n = name n' ). *)
(* Hypothesis (nameInj_neq : forall n n', n <> n' -> name n <> name n' ). *)
Definition mk_anon (n : nat) := Anon (Z.of_nat n).
Definition name := mk_anon.


(* Could be a fresh/state monad *)
Record FST :=
  mk_FST
    {
      counter_bid : nat ;
      counter_reg : int ;
    }.

Definition fresh_init : FST := mk_FST 0 0%Z.

Definition fresh : Type -> Type := fun X => FST -> (FST * X).

#[global] Instance freshM : Monad fresh :=
 {|
   ret := fun _ x s => (s,x);
   bind := fun _ _ c k s => let '(s',x) := c s in k x s'
 |}.

Definition freshLabel : fresh block_id :=
  fun '(mk_FST bid reg) => (mk_FST (S bid) reg , name bid).

Definition freshReg : fresh int :=
  fun '(mk_FST bid reg) => (mk_FST bid (reg+1) , reg).


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
      (match (find x env) with
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
  match (find x env) with
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
             (add x reg1 env,
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

Fixpoint compile_imp (s : stmt) (env: StringMap.t int) :
  OptionT fresh ( (StringMap.t int) * ocfg * block_id * block_id) :=
  match s with
  | Skip =>
      (input <- freshLabel ;;
       output <- freshLabel ;;
       let g := cfg_block [] input output in
       ret (Some (env, g, input, output)))
  | Assign x e =>
      ('(env, c) <- compile_assign x e env ;;
       input <- freshLabel ;;
       output <- freshLabel ;;
       let g := cfg_block c input output in
       ret (Some (env, g, input, output)))
  | Seq l r =>
      ( '(env1, g1, in1, out1) <- compile_imp l env;;
        '(env2, g2, in2, out2) <- compile_imp r env1;;
        ret (env2, (cfg_seq g1 g2 out1 in2), in1, out2))
  | If e l r =>
      ('(cond_reg, env, expr_code) <- compile_cond e env ;;
       reg <- freshReg ;;
       '(env1, gT, inT, outT) <- compile_imp l env;;
       '(env2, gF, inF, outF) <- compile_imp r env1;;
       input <- freshLabel ;;
       input_body <- freshLabel ;;
       out_code <- freshLabel ;;
       output <- freshLabel ;;
       let g_code := cfg_block expr_code input out_code in
       let g_body := cfg_branch (texp_i1 cond_reg) gT gF input_body inT inF in
       let g_body := cfg_join g_body output outT outF in
       let g := cfg_seq g_code g_body out_code input_body in
       ret (Some (env2, g, input, output)))
  | While e b =>
      ('(cond_reg, env, expr_code) <- compile_cond e env ;;
       '(env1, gB, inB, outB) <- compile_imp b env ;;
       input <- freshLabel ;;
       out0 <- freshLabel ;;
       output <- freshLabel ;;
       let g := cfg_while_loop expr_code (texp_i1 cond_reg) gB input inB output outB in
       ret (Some (env1, g, input, output))
      )
  end.

Definition compile (s : stmt) :=
  snd (
      ('( _, g, _, _) <- compile_imp s (StringMap.empty int);;
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


Theorem wf_compiler_aux : forall s env σ σ' input output cfg nenv ,
  (compile_imp s env) σ =
      (σ', Some (nenv, cfg, input, output)) -> wf_ocfg_bid cfg.
Proof.
  intros s.
  induction s ; intros.
  - (* Assign *)
  cbn in H.
  repeat flatten_all ;
  inv H ; inv Heq ; inv Heq4 ;
  apply wf_bid_cfg_block.
  - (* Seq *)
    cbn in H; repeat flatten_all ; try discriminate ; inv H.
    apply IHs1 in Heq.
    apply IHs2 in Heq4.
    apply wf_bid_cfg_seq ; try assumption.
    admit. admit. admit. (* I need an invariant on the compiler *)
  - (* If *)
    simpl in H. repeat (flatten_hyp H) ; try discriminate.
    inv H.
    apply wf_bid_cfg_seq ; try assumption.
    admit. 2 :{ admit. } 2 :{ admit. } 2 :{ admit. }
    apply wf_bid_cfg_join ; try assumption.
    admit. admit. admit. (* I need an invariant on the compiler *)
    apply IHs1 in Heq4. apply IHs2 in Heq9.
    apply wf_bid_cfg_branch ; try assumption.
    admit. admit. admit. (* I need an invariant on the compiler *)
  - (* While *)
    simpl in H; repeat flatten_all ; try discriminate ; inv H.
    apply IHs in Heq3.
    apply wf_bid_cfg_while_loop ; try assumption.
    admit. admit. admit. (* I need an invariant on the compiler *)
  - (* Skip *)
    cbn in H ; inv H ; repeat flatten_all ; inv H1 ; apply wf_bid_cfg_block.
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
                            env' (o : ocfg) (input output : block_id)
                            mem from to genv lenv vmem,

  (* The environments of Imp and Vir are related *)
  Rmem env mem lenv vmem ->
  (* The compilation of p with env produce a new env' and an ir *)
  (compile_imp p env) σ =
      (σ', Some (env', o, input, output))  ->
  eutt (Rimpvir env')
       (interp_imp (denote_imp p) mem)
       (interp_cfg3 (denote_cfg o from to) genv lenv vmem).
Proof.
  intros.
  induction p.
  - (* Assign *)
    simpl in *.
    repeat (flatten_all) ; [| discriminate H0].
    inv H0.
    assert ( I_to : to = input ) by admit. (* I need to introduce an invariant here *)
    rewrite I_to ; clear I_to.
    rewrite denote_cfg_block.
    2: {  admit. }
    rewrite interp_imp_bind.
    unfold compile_assign in Heq.
    repeat (flatten_all).
    inv Heq.
    repeat (flatten_all).
    inv H1.
    simpl in *.
    (* NOTE I probably need a theorem about compile_expr*)
    (* setoid_rewrite interp_cfg3_ret. *)
    admit.
    admit.
    admit.
  - (* Seq *)
    simpl in *.
    repeat (flatten_all) ; try discriminate.
    inv H0.
    rewrite denote_cfg_seq.
    admit.
    admit.
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
    rewrite denote_cfg_block.
    2: { admit. }
    rewrite interp_imp_ret.
    rewrite denote_code_nil.
    setoid_rewrite bind_ret_l.
    simpl.
    rewrite interp_cfg3_ret.
    apply eutt_Ret.
    constructor.
      * intros.
        simpl in H0. apply H,H0.
      * intros.
        destruct H0 as [reg [Hreg [ addr [Haddr [val [HValRead HValInt]]]]]].
        simpl in *.
        unfold Rmem in H.
        apply H.
        exists reg; intuition.
        exists addr; intuition.
        exists val; intuition.
Admitted.
End Theory.

End Imp2Vir.
