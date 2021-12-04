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

From Imp2Vir Require Import Imp CFGC_Combinators CFGC_CFLang CFGC_Utils.


Import ListNotations.
Import VIR_Notations.
Notation ocfg := (ocfg typ).

Section MonadTransformer.

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

End MonadTransformer.

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

Definition default_bid := Anon 0%Z.

Fixpoint compile_imp (s : stmt) (env: StringMap.t int) :
  OptionT fresh ( (StringMap.t int) * CFLang) :=
  match s with
  | Assign x e =>
      '(env, c) <- compile_assign x e env ;;
      ret (env, CBlock c)
  | Seq l r =>
      '(env1, c1) <- compile_imp l env;;
      '(env2, c2) <- compile_imp r env1;;
      ret (env2, CSeq c1 c2)
  | While e b =>
      '(cond_reg, env, expr_code) <- compile_cond e env ;;
      '(env1, cB) <- compile_imp b env ;;
      ret (env1, CWhile expr_code (texp_i1 cond_reg) cB)
  | Skip => ret (Some (env, CBlock []))
  | If e l r =>
      '(cond_reg, env, expr_code) <- compile_cond e env ;;
      '(env1, cT) <- compile_imp l env;;
      '(env2, cF) <- compile_imp r env1;;
      let ccond := CBlock expr_code in
      let cbody := CIfThenElse (texp_i1 cond_reg) cT cF in
      ret (env2, CSeq ccond cbody )
  end.

Definition compile (s : stmt) :=
  let '(σ, c) :=
    ('( _, c) <- compile_imp s (StringMap.empty int);;
     (ret c)) fresh_init in
  match c with
  | None => None
  | Some c =>
      let '(_, dg) := (evaluate c) σ in
      Some (graph dg)
  end.


Section Examples.
(** Examples *)
Open Scope string_scope.
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

Lemma wf_compiler_aux : forall s env σ σ' cfg nenv ,
  (compile_imp s env) σ = (σ', Some (nenv, cfg)) ->
  wf_dcfg (snd ((evaluate cfg) σ')).
Proof.
  induction s
  ; intros
  ; cbn in H
  ; repeat flatten_all
  ; eapply wf_evaluate'
  ; try reflexivity.
Qed.

Theorem wf_compiler : forall s g,
  compile s = Some g ->
  wf_ocfg_bid g.
Proof.
  intros.
  unfold compile in H.
  repeat flatten_all ; try discriminate.
  inv H.
  inv Heq.
  repeat flatten_all ; try discriminate.
  apply wf_dcfg_ocfg.
  apply wf_compiler_aux in Heq.
  inv H0.
  now rewrite Heq1 in Heq.
Qed.

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

(* TODO import theses tactics *)
(** Bind and translate rewritings *)
Hint Rewrite @bind_ret_l : rwbind.
Hint Rewrite @bind_bind : rwbind.
Hint Rewrite @translate_ret : rwtranslate.
Hint Rewrite @translate_bind : rwtranslate.
Hint Rewrite @translate_trigger : rwtranslate.

Ltac bstep := autorewrite with rwbind.
Ltac tstep := autorewrite with rwtranslate.
Ltac go := autorewrite with rwtranslate rwbind.

Ltac flatten := repeat (flatten_all ; simpl in *) .

Theorem compile_correct :
  forall (σ σ' : FST) env env'  (p : stmt) (o : CFLang) (dg : dcfg)
    (input output : block_id)
    mem from to genv lenv vmem,

  (* The environments of Imp and Vir are related *)
  Rmem env mem lenv vmem ->
  (* The compilation of p with env produce a new env' and an ir *)
  (compile_imp p env) σ = (σ', Some (env', o))  ->
  dg = (snd ((evaluate o) σ')) ->
  List.In to (inputs (graph dg)) ->
  eutt (Rimpvir env')
       (interp_imp (denote_imp p) mem)
       (interp_cfg3 (denote_dcfg dg from to) genv lenv vmem).
Proof.
  intros ; subst.
  induction p.
  - (* Assign *)
    simpl in *.
    repeat (flatten_all) ; [| discriminate H0].
    inv_pair ; simpl in *.
    unfold denote_cflang, denote_dcfg, mk_block in *; cbn.
    repeat flatten_all ; simpl in *.
    repeat flatten_all ; simpl in *.
    inv_pair. destruct H2 ; try contradiction ; subst.
    rewrite denote_cfg_block.
    admit.
    admit. (* The interface ensure this kind of properties *)

  - (* Seq *)
    simpl in *.
    repeat (flatten_all) ; try discriminate.
    inv_pair.
    unfold denote_cflang,denote_dcfg in *.
    repeat flatten_all ; simpl in *.
    unfold mk_seq in *.
    repeat flatten_all ; simpl in *.
    rewrite denote_cfg_seq.
    admit.
    eapply wf_evaluate_wf_seq ; eassumption.
    unfold cfg_seq in H2.
    rewrite inputs_app in H2.
    (* List.In to (inputs graph) *) admit.

  - (* If *)  (* very tedious, because several combinators *)
    simpl in *.
    repeat (flatten_all) ; try discriminate.
    inv_pair.
    unfold denote_cflang, denote_dcfg.
    simpl.
    repeat (flatten_all).
    unfold mk_seq.
    repeat (flatten_all); simpl in *.
    rewrite denote_cfg_seq. (* issue here *)
    admit. 
    eapply wf_evaluate_wf_seq ; admit.
    (* List.In to (inputs graph) *) admit.
  - (* While *)
    simpl in *.
    repeat (flatten_all) ; try discriminate.
    inv_pair.
    unfold denote_cflang,denote_dcfg.
    repeat flatten_all ; simpl in *.
    repeat flatten_all ; simpl in *.
    unfold mk_while in *.
    repeat flatten_all ; simpl in *.
    repeat flatten_all ; simpl in *.
    replace to with b by admit. (* NOTE HERE *)
    setoid_rewrite denote_cfg_while_loop.
    admit.
    eapply wf_evaluate_wf_while ; eassumption.
    (* has_post *) admit.

  - (* Skip *)
    simpl in *.
    repeat flatten_all.
    inv H0.
    unfold denote_cflang, denote_dcfg, mk_block ; cbn.
    repeat flatten_all ; simpl. (* NOTE HERE *)
    destruct (eqb_bid b to) eqn:E.
    2 : {
      rewrite eqb_bid_neq in E.
      admit. (* sohuld be identity here *)
    }
    rewrite eqb_bid_eq in E ; subst.
    rewrite denote_cfg_block .
    + setoid_rewrite denote_code_nil.
      simpl.
      bstep.
      rewrite interp_imp_ret.
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
    + admit. (* The interface should ensure this kind of properties *)
Admitted.
End Theory.

End Imp2Vir.
