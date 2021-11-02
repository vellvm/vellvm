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

From Imp2Vir Require Import Imp CompileExpr CFG_Combinators.


Section Imp2Vir.

(** Compiler IMP *)
Notation ocfg := (ocfg typ).


Variable (name : nat -> block_id).
Hypothesis (nameInj_eq : forall n n', n = n' -> name n = name n' ).
Hypothesis (nameInj_neq : forall n n', n <> n' -> name n <> name n' ).
(* Definition mk_anon (n : nat) := Anon (Z.of_nat n). *)
(* Definition name := mk_anon. *)



(* Could be a fresh/state monad *)
Record FST :=
  mk_FST
    {
      counter_reg : Z ;
      counter_bid : nat ;
      env : StringMap.t int
    }.

Definition fresh_init : FST := mk_FST 0%Z 0 (StringMap.empty int).

Definition fresh : Type -> Type := fun X => FST -> (FST * X).

#[global] Instance freshM : Monad fresh :=
 {|
  ret := fun _ x s => (s,x);
  bind := fun _ _ c k s => let '(s',x) := c s in k x s'
 |}.

Definition freshLab : fresh block_id :=
  fun '(mk_FST reg bid env) => (mk_FST reg (S bid) env , name bid).

Definition getReg : fresh Z :=
  fun '(mk_FST reg bid env) => (mk_FST reg bid env , reg).

Definition setReg (nreg : Z) : fresh _ :=
  fun '(mk_FST reg bid env) => (mk_FST nreg bid env , tt).

Definition getEnv : fresh (StringMap.t int) :=
  fun '(mk_FST reg bid env) => (mk_FST reg bid env , env).

Definition setEnv (nenv : StringMap.t int) : fresh _ :=
  fun '(mk_FST reg bid env) => (mk_FST reg bid nenv , tt).

Fixpoint compile_imp' (s : stmt) : fresh (option (ocfg * block_id * block_id)).
  refine (
      match s with
      | Skip => _
      | Assign x e => _
      | Seq l r => _
      | If e l r => _
      | While e b => _
      end).
  (* Assign *)
  refine (ret None).
  (* Seq *)
  refine (ret None).
  (* If *)
  refine (ret None).
  (* While *)
  refine (ret None).
  (* Skip *)
  refine (
      input <- freshLab ;;
      output <- freshLab ;;
      let g := cfg_block [] input output in
      ret (Some (g, input, output))
    ).
Admitted.

Fixpoint compile_imp (next_reg : int) (next_lab : nat) (s : stmt) (env: StringMap.t int)
  :  option (int * nat * (StringMap.t int) * (ocfg * block_id * block_id))
  :=
  match s with
  | Skip =>
      let input := name next_lab in
      let output := name (next_lab+1) in
      let g := cfg_block [] input output in
      Some (next_reg, (next_lab+2)%nat, env, (g, input, output))

  | Assign x e =>
      '(next_reg, env, c) <- compile_assign next_reg x e env ;;
      let input := name next_lab in
      let output := name (next_lab+1) in
      let g := cfg_block c input output in
      ret (next_reg, (next_lab+2)%nat, env , (cfg_block c input output, input , output))

  | Seq l r =>
      '(next_reg, next_lab, env, ir1) <- compile_imp next_reg next_lab l env;;
      '(next_reg, next_lab, env, ir2) <- compile_imp next_reg next_lab r env;;
      let '(g1, in1, out1) := ir1 in
      let '(g2, in2, out2) := ir2 in
      ret (next_reg, next_lab, env, ((cfg_seq g1 g2 out1 in2), in1, out2))

  | If e l r =>
    '(cond_reg, expr_code) <- compile_cond next_reg e env;;
    '(next_reg, next_lab, _, irT) <- compile_imp (cond_reg + 1) next_lab l env;;
    '(next_reg, next_lab, _, irF) <- compile_imp next_reg next_lab r env;;
    let '(gT, inT, outT) := irT in
    let '(gF, inF, outF) := irF in
    let input := name next_lab in
    let out0 := name (next_lab+1) in
    let output := name (next_lab+2) in
    let g0 := cfg_block expr_code input out0 in
    let g := cfg_branch (texp_i1 cond_reg) gT gF out0 inT inF in
    let g := cfg_join g output outT outF in
      ret (next_reg, (next_lab+2)%nat, env, (g, input, output))

  | While e b =>
    '(cond_reg, expr_code) <- compile_cond next_reg e env;;
    '(next_reg, next_lab, _, irB) <- compile_imp (cond_reg + 1) next_lab b env;;
    let '(gB, inB, outB) := irB in
    let input := name next_lab in
    let out0 := name (next_lab+1) in
    let output := name (next_lab+2) in
    let g := cfg_while_loop expr_code (texp_i1 cond_reg) gB input inB output outB in
    ret (next_reg, (next_lab+2)%nat, env, (g, input, output))
  end.

Definition compile (s : stmt) :=
  '(_, _, (g, _, _)) <- compile_imp 0 0 s (StringMap.empty int);;
  ret g.


(** Examples *)
Definition fact_ir := (compile (fact "a" "b" 5)).
Definition infinite_loop_ir := (compile (infinite_loop)).
Definition if_ir := (compile (trivial_if "a" "b" 0)).
Definition seq_ir := (compile (trivial_seq "a" "b" 42)).
Definition nested_if_ir := (compile (nested_if "a" "b" 42 43)).
Definition nested_if2_ir := (compile (nested_if2 "a" "b" 42 43)).

Compute infinite_loop_ir.
Compute seq_ir.
Compute if_ir.
Compute nested_if_ir.
Compute nested_if2_ir.
Compute fact_ir.





(** Correctness compiler *)

From Coq Require Import Lia.
From ExtLib Require Import FMapAList.
From Vellvm Require Import
     Utils.Tactics
     Semantics
     Theory.
Import SemNotations.

From ITree Require Import
     ITree
     ITreeFacts.
Import ITreeNotations.

From Imp2Vir Require Import DenotationsCombinators.

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

Theorem compile_correct : forall (next_reg : int) (next_label : nat) env (p : stmt)
                            (next_reg' : int) (next_label' : nat)
                            env' (o : ocfg) (input output : block_id)
                            mem from to genv lenv vmem,

  (* The environments of Imp and Vir are related *)
  Rmem env mem lenv vmem ->
  (* The compilation of p with env produce a new env' and an ir *)
  compile_imp next_reg next_label p env = Some(next_reg', next_label', env', (o,input,output)) ->

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
    assert ( I_to : to = (name next_label) ) by admit. (* I need to introduce an invariant here *)
    rewrite I_to ;
    rewrite denote_cfg_block.
    2: {apply nameInj_neq ; lia. }
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
  - (* Seq *) admit.
  - (* If *) admit.
  - (* While *) admit.
  - (* Skip *)
    simpl in *.
    inv H0.
    assert ( I_to : to = (name next_label) ) by admit. (* I need to introduce an invariant here *)
    rewrite I_to ;
    rewrite denote_cfg_block.
    2: { apply nameInj_neq ; lia. }
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
