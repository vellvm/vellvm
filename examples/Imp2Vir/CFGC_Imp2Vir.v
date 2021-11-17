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
     SurfaceSyntax .
Import VIR_Notations.

From Imp2Vir Require Import Imp CompileExpr CFGC_Combinators.


Section Imp2Vir.

(** Compiler IMP *)
Notation ocfg := (ocfg typ).


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
    }.

Definition fresh_init : FST := mk_FST 0.

Definition fresh : Type -> Type := fun X => FST -> (FST * X).

#[global] Instance freshM : Monad fresh :=
 {|
   ret := fun _ x s => (s,x);
   bind := fun _ _ c k s => let '(s',x) := c s in k x s'
 |}.

Definition freshLabel : fresh block_id :=
  fun '(mk_FST bid) => (mk_FST (S bid) , name bid).

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


Fixpoint compile_imp (next_reg : int) (s : stmt) (env: StringMap.t int) :
  OptionT fresh ( int * (StringMap.t int) * ocfg * block_id * block_id) :=
  match s with
  | Skip =>
      (input <- freshLabel ;;
       output <- freshLabel ;;
       let g := cfg_block [] input output in
       ret (Some (next_reg, env, g, input, output)))
  | Assign x e =>
      (match compile_assign next_reg x e env with
       | None => (ret None)
       | Some (next_reg, env, c) =>
           input <- freshLabel ;;
           output <- freshLabel ;;
           let g := cfg_block c input output in
           ret (Some (next_reg, env, g, input, output))
       end)
  | Seq l r =>
      ( '(next_reg1, env1, g1, in1, out1) <- compile_imp next_reg l env;;
        '(next_reg2, env2, g2, in2, out2) <- compile_imp next_reg1 r env1;;
        ret (next_reg2,env2,(cfg_seq g1 g2 out1 in2), in1, out2))
  | If e l r =>
      (match compile_cond next_reg e env with
       | None => ret None
       | Some (cond_reg, expr_code) =>
           '(next_reg1, env1, gT, inT, outT) <- compile_imp (cond_reg + 1) l env;;
           '(next_reg2, env2, gF, inF, outF) <- compile_imp next_reg1 r env1;;
           input <- freshLabel ;;
           input_body <- freshLabel ;;
           out_code <- freshLabel ;;
           output <- freshLabel ;;
           let g_code := cfg_block expr_code input out_code in
           let g_body := cfg_branch (texp_i1 cond_reg) gT gF input_body inT inF in
           let g_body := cfg_join g_body output outT outF in
           let g := cfg_seq g_code g_body out_code input_body in
           ret (Some (next_reg2, env2, g, input, output))
       end)
  | While e b =>
      (match compile_cond next_reg e env with
       | None => ret None
       | Some (cond_reg, expr_code) =>
           '(next_reg1, env1, gB, inB, outB) <- compile_imp (cond_reg + 1) b env ;;
           input <- freshLabel ;;
           out0 <- freshLabel ;;
           output <- freshLabel ;;
           let g := cfg_while_loop expr_code (texp_i1 cond_reg) gB input inB output outB in
           ret (Some (next_reg1, env1, g, input, output))
       end)
  end.

Definition compile (s : stmt) :=
  snd (
      ('(_, _, g, _, _) <- compile_imp 0 s (StringMap.empty int);;
       (ret g))
        fresh_init).


(** Examples *)
Definition fact_ir := (compile (fact "a" "b" 5)).
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



(** WF compiler *)
From Vellvm Require Import Utils.Tactics.

Theorem wf_compiler_aux : forall s reg env σ σ' input output cfg nreg nenv ,
  (compile_imp reg s env) σ =
      (σ', Some (nreg, nenv, cfg, input, output)) -> wf_ocfg_bid cfg.
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
    apply IHs2 in Heq5.
    apply wf_bid_cfg_seq ; try assumption.
    admit. admit. admit. (* I need an invariant on the compiler *)
  - (* If *)
    simpl in H. repeat (flatten_hyp H) ; try discriminate.
    inv H.
    apply wf_bid_cfg_seq ; try assumption.
    admit. 2 :{ admit. } 2 :{ admit. } 2 :{ admit. }
    apply wf_bid_cfg_join ; try assumption.
    admit. admit. admit. (* I need an invariant on the compiler *)
    apply IHs1 in Heq1. apply IHs2 in Heq7.
    apply wf_bid_cfg_branch ; try assumption.
    admit. admit. admit. (* I need an invariant on the compiler *)
  - (* While *)
    simpl in H; repeat flatten_all ; try discriminate ; inv H.
    apply IHs in Heq1.
    apply wf_bid_cfg_while_loop ; try assumption.
    admit. admit. admit. (* I need an invariant on the compiler *)
  - (* Skip *)
    cbn in H ; inv H ; repeat flatten_all ; inv H1 ; apply wf_bid_cfg_block.
Admitted.



(** Correctness compiler *)

From Coq Require Import Lia.
From ExtLib Require Import FMapAList.
From Vellvm Require Import
     Semantics
     Theory.
Import SemNotations.

From ITree Require Import
     ITree
     ITreeFacts.
Import ITreeNotations.

From Imp2Vir Require Import CFGC_DenotationsCombinators.

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

Theorem compile_correct : forall (next_reg : int) (σ : FST) env (p : stmt)
                            (next_reg' : int) (σ' : FST)
                            env' (o : ocfg) (input output : block_id)
                            mem from to genv lenv vmem,

  (* The environments of Imp and Vir are related *)
  Rmem env mem lenv vmem ->
  (* The compilation of p with env produce a new env' and an ir *)
  (compile_imp next_reg p env) σ =
      (σ', Some (next_reg', env', o, input, output))  ->
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


End Imp2Vir.
