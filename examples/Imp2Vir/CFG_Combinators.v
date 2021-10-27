From Coq Require Import
     Lists.List
     ZArith.

From Vellvm Require Import Syntax.

Import ListNotations.

From ExtLib Require Import Structures.Monads.
Import MonadNotation.

Section CFG_Combinators.

Notation code := (code typ).
Notation ocfg := (ocfg typ).
Notation exp := (texp typ).

(** Combinators over OCFG *)


(* Define an ocfg containing a unique block, labeled with /input/ and jumping to /output/ *)
Definition cfg_block (c : code) (input output : block_id) : ocfg :=
  [mk_block input [] c (TERM_Br_1 output) None].

(* Define an ocfg containing a unique block, labeled with /input/ and returning the expression /e/ *)
Definition cfg_ret (c : code) (e : exp) (input : block_id) : ocfg :=
  [mk_block input [] c (TERM_Ret e) None].


(* Given 2 ocfg and an expression /e/, conditionnal branch over theses graphs,
 and jumping to output *)
Definition cfg_branch (code_expr : code) (cond : exp)
           (gT gF : ocfg) (input inT inF : block_id) : ocfg :=
  let cond_block := [mk_block input [] code_expr (TERM_Br cond inT inF) None] in
  cond_block++gT++gF.

(* Given 2 ocfg, make them jump into the same block *)
Definition cfg_join (g : ocfg) (output out1 out2 : block_id) : ocfg :=
 let dead_block1 := [mk_block out1 [] [] (TERM_Br_1 output) None] in
 let dead_block2 := [mk_block out2 [] [] (TERM_Br_1 output) None] in
 g ++ dead_block1 ++ dead_block2.

(* Given 2 ocfg, sequence them g1 ;; g2 *)
Definition cfg_seq (g1 g2 : ocfg) (out1 in2 : block_id) : ocfg :=
  let dead_block := [mk_block out1 [] [] (TERM_Br_1 in2) None] in
  g1 ++ dead_block ++ g2.

(* Naive version ; maybe we could use cfg_block + cfg_branch + cfg_seq *)
Definition cfg_while_loop (code_expr : code) (cond : exp)
           (body : ocfg) (input inB output outB: block_id) : ocfg :=
  let dead_block := [mk_block outB [] [] (TERM_Br_1 input) None] in
  let cond_block := [mk_block input [] code_expr (TERM_Br cond inB output) None] in
  cond_block++body++dead_block.

(* Dedicated combinators for /for_loops/ *)
Definition cfg_for_loop (b e step : nat) (body : ocfg) (inb : block_id) : ocfg.
Admitted.


(** Semantic *)
From Vellvm Require Import
     Semantics
     Tactics
     Theory.SymbolicInterpreter.

From ITree Require Import
     ITree
     ITreeFacts
     Eq.

Import ITreeNotations.

Notation conv := (convert_typ []).
Definition denote_cfg g from to := denote_ocfg (conv g) (from,to).

From Vellvm Require Import Syntax.ScopeTheory.

Definition eq_bid b b' :=
  match b,b' with
  | Name s, Name s' => String.eqb s s'
  | Anon n, Anon n' => @RelDec.eq_dec int eq_dec_int n n'
  | Raw n, Raw n' => @RelDec.eq_dec int eq_dec_int n n'
  | _,_ => false
  end.

Lemma eqb_bid_eq : forall b b', eq_bid b b' = true <-> b=b'.
Proof.
  intros.
  split.
  - destruct b,b' ;
      try (intros ; simpl in H ; discriminate) ;
      simpl ; intros ; f_equal ;
      try (now apply String.eqb_eq) ;
      try (now apply Z.eqb_eq).
  - intros ; subst.
    destruct b' ; simpl ;
      try (now apply String.eqb_eq) ;
      try (now apply Z.eqb_eq).
Qed.

Lemma eqb_bid_neq : forall b b', eq_bid b b' = false <-> b<>b'.
Proof.
  intros.
  split.
  - destruct b,b' ;
      try (intros ; simpl in H ; discriminate) ;
      simpl ; intros ; intro ;
      try (apply String.eqb_neq in H);
      try (apply Z.eqb_neq in H);
        inv H0 ; contradiction.
  - intros ; subst.
    destruct b,b' ; simpl ; auto;
    try (apply String.eqb_neq) ;
      try (apply Z.eqb_neq) ;
      intro ; subst ;
    contradiction.
Qed.

Lemma eq_bid_comm : forall b b', eq_bid b b' = eq_bid b' b.
  intros.
  destruct b,b' ; simpl ; auto ;
    try (now apply String.eqb_sym) ;
    try (now apply Z.eqb_sym).
Qed.

Lemma eq_bid_refl : forall b, eq_bid b b = true.
  intros.
  destruct b ; simpl ; auto ;
    try (now apply String.eqb_refl) ;
    try (now apply Z.eqb_refl).
Qed.

Lemma eqv_dec_p_eq : forall b b' r,
    eq_bid b b' = r <-> (if Eqv.eqv_dec_p b b' then true else false) = r.
  intros.
  destruct r eqn:R.
  - destruct (Eqv.eqv_dec_p b b') eqn:E.
    + unfold Eqv.eqv,eqv_raw_id in e ; subst.
      now rewrite eq_bid_refl.
    + unfold Eqv.eqv,eqv_raw_id in n.
      rewrite eqb_bid_eq.
      split ; intros ; subst. contradiction. inversion H.
  - destruct (Eqv.eqv_dec_p b b') eqn:E.
    + unfold Eqv.eqv,eqv_raw_id in e ; subst.
    now rewrite eq_bid_refl.
    + unfold Eqv.eqv,eqv_raw_id in n ; subst.
      rewrite eqb_bid_neq.
      split ; intros ; auto.
Qed.

Lemma eqv_dec_p_refl : forall (b : block_id),
    (if Eqv.eqv_dec_p b b then true else false) = true.
Proof.
  intros.
  destruct (Eqv.eqv_dec_p b b) ; auto.
  unfold Eqv.eqv,eqv_raw_id in n ; auto.
Qed.

Lemma denote_cfg_block : forall (c : code) (input output : block_id) from to,
    input <> output ->
    eutt eq
         (denote_cfg (cfg_block c input output) from to)
         (if (eq_bid to input)
          then ret tt ;; denote_code (conv c) ;; ret (inl (input,output))
          else ret (inl (from,to))) .
Proof.
  intros.
  unfold denote_cfg.
  destruct (eq_bid to input) eqn:E.
  apply eqb_bid_eq in E ; subst.
  - unfold cfg_block.
    unfold denote_ocfg.
    set (b := (conv
                  {|
                     blk_id := input;
                     blk_phis := [];
                     blk_code := c;
                     blk_term := TERM_Br_1 output;
                     blk_comments := None
                  |})).
    setoid_rewrite DenotationTheory.denote_ocfg_unfold_in with (bk := b).
    + subst b.
      setoid_rewrite DenotationTheory.denote_block_unfold_cont.
      unfold Traversal.endo, Traversal.Endo_id.
      simpl.
      unfold tfmap, TFunctor_list ; simpl.
      rewrite DenotationTheory.denote_no_phis.
      rewrite eutt_eq_bind.
      reflexivity.
      intros. simpl.
      rewrite eutt_eq_bind .
      reflexivity.
      intros. simpl.
      rewrite translate_ret.
      unfold Traversal.endo, Traversal.Endo_id.
      assert (Hbind_ret : forall {E R1 R2} (k : R1 -> itree E R2) v
               , (x <- Ret v ;; k x) ≈ k v).
      { admit. (* easy, monad laws*) }
      rewrite Hbind_ret.
      setoid_rewrite DenotationTheory.denote_ocfg_unfold_not_in.
      reflexivity.
      simpl.
      unfold Traversal.endo, Traversal.Endo_id.
      rewrite <- eqb_bid_neq in H.
      rewrite eqv_dec_p_eq in H.
      unfold block_id in *.
      rewrite H. reflexivity.
    + cbn ; rewrite eqv_dec_p_refl ; reflexivity.
  - unfold cfg_block.
    unfold denote_ocfg.
    setoid_rewrite DenotationTheory.denote_ocfg_unfold_not_in.
    reflexivity.
    rewrite eq_bid_comm in E.
    apply eqv_dec_p_eq in E.
    simpl.
    unfold Traversal.endo, Traversal.Endo_id.
    unfold block_id in *. now rewrite E.
Admitted.



(** Compiler IMP *)
From Imp2Vir Require Import Imp.

Require Import CompileExpr.

Import MonadNotation.
Variable (name : nat -> block_id).

(* Could be a fresh/state monad *)

Fixpoint compile_imp (next_reg : int) (next_lab : nat) (s : stmt) (env: StringMap.t int)
  : option (int * nat * (StringMap.t int) * (ocfg * block_id * block_id)) :=
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
    let output := name (next_lab+1) in
    let g := cfg_branch expr_code (texp_i1 cond_reg) gT gF input inT inF in
    let g := cfg_join g output outT outF in
      ret (next_reg, (next_lab+2)%nat, env, (g, input, output))

  | While e b =>
    '(cond_reg, expr_code) <- compile_cond next_reg e env;;
    '(next_reg, next_lab, _, irB) <- compile_imp (cond_reg + 1) next_lab b env;;
    let '(gB, inB, outB) := irB in
    let input := name next_lab in
    let output := name (next_lab+1) in
    let g := cfg_while_loop expr_code (texp_i1 cond_reg) gB input inB output outB in
    ret (next_reg, (next_lab+2)%nat, env, (g, input, output))
  end.

Definition compile (s : stmt) :=
  '(_, _, (g, _, _)) <- compile_imp 0 0 s (StringMap.empty int);;
  ret g.


(** Examples *)
From Coq Require Import Strings.String.
From Vellvm Require Import SurfaceSyntax.
Import VIR_Notations.

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


End CFG_Combinators.
