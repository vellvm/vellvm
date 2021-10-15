From Coq Require Import
     Lia
     Lists.List
     Strings.String
     ZArith.

Import ListNotations.
Open Scope Z_scope.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.OptionMonad.
Import MonadNotation.

From Vellvm Require Import
     Syntax.

Require Import Imp CompileExpr.

Section compile_sir.

(* Imp to Sir to Vir *)

(** A structured intermediate representation. *)
Inductive sir : Type :=
| LBlock (b : code typ)
| LSeq (l1 l2 : sir)
| LCond (l1 l2 : sir) (c : texp typ)
| LCondLoop (l : sir) (c : texp typ)
.

Definition compile_assign (next_reg : int) (x: Imp.var) (e: expr) (env : StringMap.t int)
: option (int * (StringMap.t int) * code typ) :=
  '(expr_reg, ir) <- compile_expr next_reg e env;;
  ret match StringMap.find x env with
  | Some id => ((expr_reg + 2), env,
      ir ++ [(IId (Anon (expr_reg + 1)), INSTR_Store false (texp_i32 expr_reg) (texp_ptr id) None)]
      )
  | None => (expr_reg + 3, StringMap.add x next_reg env,
      ir ++ [(IId (Anon (expr_reg + 1)), INSTR_Alloca (TYPE_I 32) None None)] ++
      [(IId (Anon (expr_reg + 2)), INSTR_Store false (texp_i32 expr_reg) (texp_ptr (expr_reg + 1)) None)]
      )
  end.

Fixpoint compile (next_reg : int) (s : stmt) (env: StringMap.t int)
: option (int * (StringMap.t int) * sir) :=
  match s with
  | Skip => Some(next_reg, env, LBlock nil)
  | Assign x e =>
      '(next_reg, env, ir) <- compile_assign next_reg x e env;;
      ret (next_reg, env, LBlock ir)
  | Seq l r =>
      '(next_reg, env, sir_l) <- compile next_reg l env;;
      '(next_reg, env, sir_r) <- compile next_reg r env;;
       ret (next_reg, env, LSeq sir_l sir_r)
  | If e l r =>
      '(expr_reg, expr_ir) <- compile_expr next_reg e env;;
      '(next_reg, _, sir_l) <- compile (expr_reg + 1) l env;;
      '(next_reg, _, sir_r) <- compile next_reg r env;;
      ret (next_reg, env, LSeq
        (LBlock expr_ir)
        (LCond sir_l sir_r (texp_i32 expr_reg))
      )
  | While e b =>
      '(expr_reg, expr_ir) <- compile_expr next_reg e env;;
      '(next_reg, _, sir) <- compile (expr_reg + 1) b env;;
      '(expr_reg_post, expr_ir_post) <- compile_expr next_reg e env;;
      ret (expr_reg_post + 1, env, LSeq
        (LBlock expr_ir)
        (LCond
          (LCondLoop
            (LSeq sir (LBlock expr_ir_post))
            (texp_i32 expr_reg_post))
          (LBlock nil)
          (texp_i32 expr_reg)
        )
      )
  end.

Definition fact_ir := (compile 0 (fact "a" "b" 5) (StringMap.empty int)).

(* Eval compute in fact_ir. *)

Fixpoint compile_sir (next_block : int) (s : sir) : int * (terminator typ -> ocfg typ) :=
  match s with
  | LBlock b => ((next_block + 1), fun term => [mk_block (Anon next_block) nil b term None])
  | LSeq l1 l2 =>
      let (next_block1, l1) := compile_sir next_block l1 in
      let (next_block2, l2) := compile_sir next_block1 l2 in
      (next_block2, fun term => (l1 (TERM_Br_1 (Anon next_block1))) ++ l2 term)
  | LCond l1 l2 c =>
      let (next_block1, l1) := compile_sir (next_block + 1) l1 in
      let (next_block2, l2) := compile_sir next_block1 l2 in
      let cond_block := [mk_block
        (Anon next_block) nil nil (TERM_Br c (Anon (next_block + 1)) (Anon next_block1)) None
      ] in
      (next_block2, fun term => (cond_block ++ l1 term ++ l2 term))
  | LCondLoop l c =>
      let (break_block, l) := compile_sir next_block l in
      (
        (break_block + 1),
        fun term =>
          l (TERM_Br c (Anon next_block) (Anon break_block)) ++
          [mk_block (Anon break_block) nil nil term None]
      )
  end
.

Definition compile_sir_main (s : sir) : ocfg typ :=
  (snd (compile_sir 0 s) TERM_Ret_void).


Definition fact_ll := match fact_ir with
| None => (0, fun _ => nil)
| Some(_,_,l) => compile_sir 0 l
end.

(* Eval compute in fact_ll. *)

Property anon_blk_id :
  forall (l : sir) (b : block typ) (n : int) (term : terminator typ),
  List.In b (snd (compile_sir n l) term) ->
  exists (i : int), blk_id b = Anon i.
Proof.
  intros l b.
  induction l ; simpl in * ; intros.
  - destruct H ; try contradiction.
    rewrite <- H.
    exists n.
    reflexivity.
  - destruct (compile_sir n l1) eqn:? in H.
    destruct (compile_sir i l2) eqn:? in H.
    apply in_app_iff in H.
    destruct H.
    + eapply IHl1. rewrite Heqp. exact H.
    + eapply IHl2. rewrite Heqp0. exact H.
  - destruct (compile_sir (n + 1) l1) eqn:? in H.
    destruct (compile_sir i l2) eqn:? in H.
    destruct H.
    + rewrite<- H.
      exists n.
      reflexivity.
    + apply in_app_iff in H.
      destruct H.
      * eapply IHl1. rewrite Heqp. exact H.
      * eapply IHl2. rewrite Heqp0. exact H.
  - destruct (compile_sir n l) eqn:? in H.
    simpl in H.
    apply in_app_iff in H.
    destruct H.
    + eapply IHl.
      rewrite Heqp.
      exact H.
    + simpl in H.
      destruct H ; try contradiction.
      rewrite<- H.
      simpl.
      eauto.
Qed.

Property sir_non_empty :
  forall (l : sir) (n : int) (term : terminator typ),
  exists (b : block typ), List.In b (snd (compile_sir n l) term).
Proof.
  intros l.
  induction l ; simpl ; intros.
  - exists {| blk_id := Anon n; blk_phis := []; blk_code := b; blk_term := term; blk_comments := None |}.
    auto.
  - destruct (compile_sir n l1) eqn:?.
    destruct (compile_sir i l2) eqn:?.
    simpl.
    destruct (IHl2 i term).
    exists x.
    apply in_or_app.
    right.
    rewrite Heqp0 in H.
    simpl in H.
    exact H.
  - destruct (compile_sir (n+1) l1).
    destruct (compile_sir i l2).
    simpl.
    exists {|
      blk_id := Anon n;
      blk_phis := [];
      blk_code := [];
      blk_term := TERM_Br c (Anon (n + 1)) (Anon i);
      blk_comments := None
    |}.
    left.
    reflexivity.
  - destruct (compile_sir n l).
    simpl.
    exists {| blk_id := Anon i; blk_phis := []; blk_code := []; blk_term := term; blk_comments := None |}.
    apply in_or_app.
    right.
    simpl.
    auto.
Qed.

Property increasing_bid :
  forall (l : sir) (n : int),
    fst (compile_sir n l) > n.
Proof.
  induction l ; intros ; simpl in *.
  - lia.
  - specialize (IHl1 n).
    destruct (compile_sir n l1) in *.
    specialize (IHl2 i).
    destruct (compile_sir i l2) in *.
    simpl in *.
    lia.
  - specialize (IHl1 (n + 1)).
    destruct (compile_sir (n + 1) l1) in *.
    specialize (IHl2 i).
    destruct (compile_sir i l2) in *.
    simpl in *.
    lia.
  - specialize (IHl n).
    destruct (compile_sir n l) in *.
    simpl in *.
    lia.
Qed.

Property bid_in_range :
  forall (l : sir) (n : int) (term : terminator typ) (b : block typ),
  List.In b (snd (compile_sir n l) term) ->
  exists (i : int),
    blk_id b = Anon i /\
    i >= n /\
    fst (compile_sir n l) > i.
Proof.
  intros l.
  induction l ; intros ; simpl in *.
  - exists n.
    split.
    destruct H ; try contradiction.
    rewrite<- H.
    simpl.
    reflexivity.
    lia.
  - destruct (compile_sir n l1) eqn:? in *.
    destruct (compile_sir i l2) eqn:? in *.
    specialize (IHl1 n).
    specialize (IHl2 i).
    apply in_app_iff in H.
    rewrite Heqp in IHl1.
    rewrite Heqp0 in IHl2.
    simpl in *.
    destruct H.
    + apply IHl1 in H.
      destruct H.
      exists x.
      intuition.
      assert (Hi := increasing_bid l2 i).
        rewrite Heqp0 in Hi.
        simpl in *.
      lia.
    + apply IHl2 in H.
      destruct H.
      exists x.
      intuition.
      assert (Hi := increasing_bid l1 n).
      rewrite Heqp in Hi.
      simpl in *.
      lia.
  - specialize (IHl1 (n + 1)).
    destruct (compile_sir (n + 1) l1) eqn:? in *.
    specialize (IHl2 i).
    destruct (compile_sir i l2) eqn:? in *.
    simpl in *.
    destruct H.
    + exists n.
      rewrite<- H.
      intuition.
      assert (Hi := increasing_bid l1 (n + 1)).
      assert (Hi' := increasing_bid l2 i).
      rewrite Heqp in Hi.
      rewrite Heqp0 in Hi'.
      simpl in *.
      lia.
    + apply in_app_iff in H.
      destruct H.
      * apply IHl1 in H.
        destruct H.
        exists x.
        intuition.
        assert (Hi := increasing_bid l2 i).
        rewrite Heqp0 in Hi.
        simpl in Hi.
        lia.
      * apply IHl2 in H.
        destruct H.
        exists x.
        intuition.
        assert (Hi := increasing_bid l1 (n + 1)).
        rewrite Heqp in Hi.
        simpl in Hi.
        lia.
  - specialize (IHl n).
    destruct (compile_sir n l) eqn:? in *.
    apply in_app_iff in H.
    simpl in *.
    destruct H.
    + apply IHl in H.
      destruct H.
      exists x.
      intuition.
    + exists i.
      intuition.
      * rewrite<- H0. reflexivity.
      * assert (Hi := increasing_bid l n).
      rewrite Heqp in Hi.
      simpl in Hi.
      lia.
Qed.

Property unique_bid :
  forall (l : sir) (b1 b2 : block typ),
  blk_id b1 = blk_id b2 ->
  forall n,
  forall term,
  List.In b1 (snd (compile_sir n l) term) ->
  List.In b2 (snd (compile_sir n l) term) ->
  b1 = b2.
Proof.
  intros l b1 b2 Heq.
  induction l ; intros ; simpl in *.
  - destruct H ; try contradiction.
    destruct H0 ; try contradiction.
    subst.
    reflexivity.
  - specialize (IHl1 n).
    destruct (compile_sir n l1) eqn:? in *.
    specialize (IHl2 i).
    destruct (compile_sir i l2) eqn:? in *.
    simpl in *.
    apply in_app_iff in H, H0.
    destruct H, H0 ; try eauto.
    all: exfalso.
    all:
      eassert (H1 := bid_in_range _ _ _ _);
      eassert (H2 := bid_in_range _ _ _ _);
      rewrite Heqp in H1;
      rewrite Heqp0 in H2;
      simpl in H1, H2;
      apply H1 in H || apply H2 in H;
      apply H1 in H0 || apply H2 in H0;
      destruct H;
      destruct H0.
    all: intuition.
    all: replace (blk_id b1) in * ; replace (blk_id b2) in * ; injection Heq as Heq.
    all: lia.
  - specialize (IHl1 (n + 1)).
    destruct (compile_sir (n + 1) l1) eqn:? in *.
    specialize (IHl2 i).
    destruct (compile_sir i l2) eqn:? in *.
    eassert (Hinc1 := bid_in_range _ _ _).
    eassert (Hinc2 := bid_in_range _ _ _).
    rewrite Heqp in Hinc1.
    rewrite Heqp0 in Hinc2.
    destruct H, H0 ; subst ; simpl in *.
    + subst. reflexivity.
    + apply in_app_iff in i1.
      destruct i1.
      * apply Hinc1 in H.
        destruct H.
        intuition.
        destruct b2.
        simpl in *.
        subst.
        injection H0 as H0.
        exfalso.
        lia.
      * apply Hinc2 in H.
        destruct H.
        intuition.
        destruct b2.
        simpl in *.
        subst.
        injection H0 as H0.
        exfalso.
        eassert (H1 := increasing_bid _ _).
        rewrite Heqp in H1.
        simpl in H1.
        lia.
    + apply in_app_iff in i1.
      destruct i1.
      * apply Hinc1 in H.
        destruct H.
        intuition.
        destruct b1.
        simpl in *.
        subst.
        injection H0 as H0.
        exfalso.
        lia.
      * apply Hinc2 in H.
        destruct H.
        intuition.
        destruct b1.
        simpl in *.
        subst.
        injection H0 as H0.
        exfalso.
        eassert (H1 := increasing_bid _ _).
        rewrite Heqp in H1.
        simpl in H1.
        lia.
    + apply in_app_iff in i1, i2.
      destruct i1, i2.
      1: apply (IHl1 term) ; assumption.
      3: apply (IHl2 term) ; assumption.
      all: apply Hinc1 in H as H' || apply Hinc2 in H as H'.
      all: apply Hinc1 in H0 as H0' || apply Hinc2 in H0 as H0'.
      all: destruct H', H0'.
      all: intuition.
      all: destruct b1, b2.
      all: simpl in *.
      all: subst.
      all: injection H1 as H1.
      all: lia.
  - specialize (IHl n).
    destruct (compile_sir n l) eqn:? in *.
    apply in_app_iff in H, H0.
    simpl in *.
    destruct H, H0; intuition.
    1: exact (IHl _ H H0).
    3: subst; reflexivity.
    1: rename H into H0.
    all: eassert (Hinc := bid_in_range _ _ _); rewrite Heqp in Hinc.
    all: apply Hinc in H0.
    all: destruct H0; simpl in *.
    all: intuition.
    all: rewrite H0, <-H1 in Heq; simpl in Heq; injection Heq as Heq.
    all: lia.
Qed.

End compile_sir.
