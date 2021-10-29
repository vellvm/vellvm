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
Notation conv := (convert_typ []).

Definition texp_break (e : texp typ) : dtyp * exp dtyp :=
  let (t,e) := e in
  ((typ_to_dtyp [] t), (conv e)).

Notation texp := (texp typ).

(** Combinators over OCFG *)


(* Define an ocfg containing a unique block, labeled with /input/ and jumping to /output/ *)
Definition cfg_block (c : code) (input output : block_id) : ocfg :=
  [mk_block input [] c (TERM_Br_1 output) None].

(* Define an ocfg containing a unique block, labeled with /input/ and returning the expression /e/ *)
Definition cfg_ret (c : code) (e : texp) (input : block_id) : ocfg :=
  [mk_block input [] c (TERM_Ret e) None].

(* Given 2 ocfg and an expression /e/, conditionnal branch over theses graphs,
 and jumping to output *)
Definition cfg_branch (cond : texp)
           (gT gF : ocfg)
           (input inT inF : block_id) : ocfg :=
  let cond_block := [mk_block input [] [] (TERM_Br cond inT inF) None] in
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

Definition cfg_while_loop (code_expr : code) (cond : texp)
           (body : ocfg) (input inB output outB: block_id) : ocfg :=
  let dead_block := [mk_block outB [] [] (TERM_Br_1 input) None] in
  let cond_block := [mk_block input [] code_expr (TERM_Br cond inB output) None] in
  cond_block++body++dead_block.

(* Dedicated combinators for /for_loops/ *)
Definition cfg_for_loop (b e step : nat) (body : ocfg) (inb : block_id) : ocfg.
Admitted.


(** WF properties *)

Lemma inputs_app : forall (g1 g2 : ocfg), inputs (g1++g2) = inputs g1 ++ inputs g2.
Proof.
  intros.
  unfold inputs.
  apply Coqlib.list_append_map.
Qed.

Lemma inputs_seq : forall (g1 g2 : ocfg) (out1 in2 :  block_id),
    inputs (cfg_seq g1 g2 out1 in2) =
      inputs g1 ++ [out1] ++ inputs g2.
Proof.
  intros.
  unfold cfg_seq.
  apply inputs_app.
Qed.

Lemma In_singleton : forall {A} (x y : A),
    In x [y] -> x=y.
Proof.
  intros.
  cbn in H; intuition.
Qed.

Lemma List_norepet_singleton : forall {A} (x : A),
    Coqlib.list_norepet [x].
Proof.
  intros.
  apply Coqlib.list_norepet_cons ; auto.
  apply Coqlib.list_norepet_nil.
Qed.


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

Definition denote_cfg g from to := denote_ocfg (conv g) (from,to).

From Coq Require Import String.
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

Lemma find_block_none_singleton :
  forall c term phis b b' , b<>b' <->
   find_block
   (conv
      [{|
         blk_id := b;
         blk_phis := phis;
         blk_code := c;
         blk_term := term;
         blk_comments := None
         |}]) b' = None.
Proof.
  intros.
  split; intros.
  - apply find_block_not_in_inputs.
    simpl; intuition.
  - simpl in H.
    unfold endo, Endo_id in H.
    destruct (if Eqv.eqv_dec_p b b' then true else false) eqn:E.
    + discriminate.
    + now rewrite <- eqv_dec_p_eq in E ; rewrite <- eqb_bid_neq.
Qed.


(* Ltac denote_ *)

Lemma denote_cfg_block : forall (c : code) (input output : block_id) from,
    input <> output -> (* TODO should be a WF property of block *)
    eutt eq
         (denote_cfg (cfg_block c input output) from input)
          (denote_code (conv c) ;; ret (inl (input,output))).
Proof.
  intros.
  unfold cfg_block, denote_cfg.
  setoid_rewrite DenotationTheory.denote_ocfg_unfold_in with
    (bk := (conv
               {|
                  blk_id := input;
                   blk_phis := [];
                    blk_code := c;
                     blk_term := TERM_Br_1 output;
                      blk_comments := None
               |})).
  2: { cbn ; rewrite eqv_dec_p_refl ; reflexivity. }
  setoid_rewrite DenotationTheory.denote_block_unfold_cont.
  unfold Traversal.endo, Traversal.Endo_id ; simpl.
  rewrite DenotationTheory.denote_no_phis.
  rewrite bind_ret_l.
  rewrite eutt_eq_bind ; [reflexivity|].
  intros; simpl.
  rewrite translate_ret.
  rewrite bind_ret_l.
  rewrite DenotationTheory.denote_ocfg_unfold_not_in.
  2: { now apply find_block_none_singleton. }
  reflexivity.
Qed.

Lemma denote_cfg_ret : forall (c : code) (e : texp) (input : block_id) from,
    eutt eq
         (denote_cfg (cfg_ret c e input) from input)
         (let (t,e) := e in
         denote_code (conv c) ;;
         v <- translate exp_to_instr (denote_exp (Some (typ_to_dtyp [] t)) (conv e)) ;;
         ret (inr v)).
Proof.
  intros.
  unfold cfg_ret, denote_cfg.
  flatten_goal.
  rewrite DenotationTheory.denote_ocfg_unfold_in.
  2: { simpl ; now rewrite eqv_dec_p_refl.}
  setoid_rewrite DenotationTheory.denote_block_unfold.
  simpl.
  rewrite bind_bind.
  rewrite DenotationTheory.denote_no_phis.
  rewrite bind_ret_l.
  rewrite bind_bind.
  rewrite eutt_eq_bind ; [reflexivity|].
  intros ; cbn.
  rewrite translate_bind.
  rewrite bind_bind.
  unfold tfmap,TFunctor_texp in Heq.
  inv Heq.
  rewrite eutt_eq_bind ; [reflexivity|].
  intros ; cbn.
  setoid_rewrite translate_ret.
  setoid_rewrite bind_ret_l ; reflexivity.
Qed.

Lemma denote_cfg_branch :
  forall (cond : texp) (gT gF : ocfg) (input inT inF from input : block_id),
    input <> inT ->
    input <> inF ->
    no_reentrance (conv gT) (conv gF) ->
    eutt eq
         (denote_cfg (cfg_branch cond gT gF input inT inF) from input)
         (let (dt,e) := texp_break cond in
          dv <- translate exp_to_instr (
                            uv <-  (denote_exp (Some dt) e) ;;
                            concretize_or_pick uv True) ;;
          match dv with
          | DVALUE_I1 comparison_bit =>
              if equ comparison_bit Int1.one then
                 denote_cfg gT input inT
              else
                 denote_cfg gT input inF
          | DVALUE_Poison => raiseUB "Branching on poison."
          | _ => raise "Br got non-bool value"
          end).
Proof.
  intros.
  unfold cfg_branch, denote_cfg.
  From Vellvm Require Import Theory.
  rewrite (convert_typ_list_app _ (gT++gF) _).
  rewrite denote_ocfg_app.
  rewrite denote_ocfg_unfold_in with
    (bk := conv {|
                 blk_id := input0;
                  blk_phis := [];
                   blk_code := [];
                    blk_term := TERM_Br cond inT inF;
                     blk_comments := None
              |}).
  2: {
     simpl. rewrite eqv_dec_p_refl. reflexivity.
  }
  setoid_rewrite DenotationTheory.denote_block_unfold.
  simpl.
  rewrite DenotationTheory.denote_no_phis.
  setoid_rewrite DenotationTheory.denote_code_nil.
  repeat (rewrite bind_ret_l).
  (* unfold texp_break in Heq ; flatten_hyp Heq ; inv Heq. *)
  flatten_all.
  flatten_all.
  unfold texp_break in Heq0.
  flatten_all.
  unfold tfmap,TFunctor_texp in Heq.
  unfold conv in Heq0.
  unfold ConvertTyp_exp in Heq0.
  rewrite Heq in Heq0.
  inv Heq0. clear Heq.
  setoid_rewrite translate_bind.
  repeat (rewrite bind_bind).
  rewrite eutt_eq_bind ; [reflexivity|].
  intros ; simpl.
  setoid_rewrite translate_bind.
  repeat (rewrite bind_bind).
  rewrite eutt_eq_bind ; [reflexivity|].
  intros ; simpl.
  destruct u0 ;
    try (rewrite exp_to_instr_raise ; admit) ;
    try (rewrite exp_to_instr_raiseUB ; admit).
  destruct (Int1.eq x Int1.one) ;
    rewrite translate_ret ;
    rewrite bind_ret_l.
  - (* Side True*)
    rewrite Util.list_cons_app.
    rewrite denote_ocfg_unfold_not_in.
    2: { rewrite app_nil_r ; now rewrite <- find_block_none_singleton.}
    rewrite bind_ret_l.
    rewrite convert_typ_list_app.
    rewrite denote_ocfg_app ; try assumption.
    assert (HinT : In inT (inputs gT) \/ ~ In inT (inputs gT))
      by (apply Classical_Prop.classic).
    destruct HinT as [ HinT | HinT ].
    + (* inT is in gT *) admit.
    + (* inT is not in gT *)
Admitted.


Lemma denote_cfg_while_loop : Prop.
  refine (
        forall expr_code cond body input inB output outB from,
          eutt eq
               (denote_cfg (cfg_while_loop expr_code cond body input inB output outB)
                           from input)
                _).
Admitted.

Lemma no_reentrance_convert_typ:
  forall (env : list (ident * typ)) [g1 g2 : ocfg],
    no_reentrance g1 g2 -> no_reentrance (convert_typ env g1) (convert_typ env g2).
Admitted.


Lemma denote_void_block : forall bid target src com,
    denote_block
       {|
          blk_id := bid;
           blk_phis := [];
            blk_code := [];
             blk_term := TERM_Br_1 target;
              blk_comments := com
       |} src
       ≈ ret (inl target).
Proof.
  intros.
  rewrite DenotationTheory.denote_block_unfold.
  rewrite DenotationTheory.denote_no_phis.
  setoid_rewrite DenotationTheory.denote_code_nil.
  setoid_rewrite translate_ret.
  repeat (rewrite bind_ret_l).
  reflexivity.
Qed.

Ltac denote_block_void := try (rewrite denote_void_block ; simpl).

Lemma denote_cfg_join : forall (g : ocfg) (output out1 out2 : block_id) from to,
    free_in_cfg g output ->
    output <> out1 ->
    output <> out2 ->
    eutt eq
         (denote_cfg (cfg_join g output out1 out2) from to)
         (d <- denote_cfg g from to ;;
          match d with
          | inr dv => ret (inr dv)
          | inl (src,target) =>
              if (eq_bid target out1)
              then ret (inl (out1, output))
              else if (eq_bid target out2)
                   then ret (inl (out2, output))
                   else ret (inl (src,target))
          end).
Proof.
  intros.
  unfold denote_cfg.
  unfold cfg_join.
  rewrite (convert_typ_list_app g _ []).
  rewrite DenotationTheory.denote_ocfg_app.
  2: {
     apply no_reentrance_convert_typ.
     unfold no_reentrance.
     cbn.
     repeat (apply Coqlib.list_disjoint_cons_l ; auto).
     apply Util.list_disjoint_nil_l.}
  apply eutt_eq_bind.
  intros.
  destruct u as [ (src,target) | dv ] ; [| reflexivity].
  (* the result of the denotation of g is a jump to target, coming from src *)
  rewrite convert_typ_list_app.
  rewrite DenotationTheory.denote_ocfg_app.
  2: {apply no_reentrance_convert_typ. unfold no_reentrance. cbn.
      now apply Util.list_disjoint_singletons.
  }
  (* We have 3 cases: target = out1, target = out2 and neither of them *)
  flatten_goal.
  - (* Jump to out1 *)
    rewrite eqb_bid_eq in Heq ; subst.
    rewrite DenotationTheory.denote_ocfg_unfold_in
      with (bk:=
              {|
                 blk_id := out1;
                 blk_phis := [];
                 blk_code := [];
                 blk_term := TERM_Br_1 output;
                 blk_comments := None
              |}).
    2: { cbn; rewrite eqv_dec_p_refl; reflexivity. }
    + rewrite bind_bind.
      (* I need a lemma which denote automatically the empty block *)
      denote_block_void.
      rewrite bind_ret_l.
      rewrite DenotationTheory.denote_ocfg_unfold_not_in.
      2: { now apply find_block_none_singleton,not_eq_sym. } (* easy because out1 <> output *)
      rewrite bind_ret_l.
      rewrite DenotationTheory.denote_ocfg_unfold_not_in.
      2: { now apply find_block_none_singleton,not_eq_sym. } (* easy because out2 <> output  *)
      reflexivity.
  - flatten_goal.
    + (* Jump to out2 *)
      rewrite eqb_bid_eq in Heq0 ; subst.
      rewrite DenotationTheory.denote_ocfg_unfold_not_in.
      2: { apply eqb_bid_neq in Heq ; now apply find_block_none_singleton,not_eq_sym. }
      rewrite bind_ret_l.
      rewrite DenotationTheory.denote_ocfg_unfold_in
        with (bk:=
                {|
                   blk_id := out2;
                   blk_phis := [];
                   blk_code := [];
                   blk_term := TERM_Br_1 output;
                   blk_comments := None
                |}).
      2: { cbn; rewrite eqv_dec_p_refl; reflexivity. }
      denote_block_void.
      rewrite bind_ret_l.
      rewrite DenotationTheory.denote_ocfg_unfold_not_in.
      2: { now apply find_block_none_singleton,not_eq_sym. }
      reflexivity.
    + (* Neither out1 or out2 *)
      apply eqb_bid_neq in Heq,Heq0.
      rewrite DenotationTheory.denote_ocfg_unfold_not_in.
      2: { now apply find_block_none_singleton,not_eq_sym. }
      rewrite bind_ret_l.
      rewrite DenotationTheory.denote_ocfg_unfold_not_in.
      2: { now apply find_block_none_singleton,not_eq_sym. }
      reflexivity.
Qed.


(* TODO I think that some steps can be automatize, eg.
 - denote_ocfg_unfold_not_in (find_block proof)
 - denote_ocfg_unfold_in (find_block proof)
 - denote_ocfg_app (no_reentrance_proof) *)
Lemma denote_cfg_seq : forall g1 g2 out1 in2 from to,
    (* TODO I am not sure of the way to add theses hypothesis in the WF proofs *)
    wf_ocfg_bid g1 ->
    wf_ocfg_bid g2 ->
    no_duplicate_bid g1 g2 ->
    no_reentrance g1 g2 ->
    free_in_cfg g1 out1 -> (* cfg_seq cannot create a new block with an existing ID *)
    free_in_cfg g2 out1 -> (* cfg_seq cannot create a new block with an existing ID *)
    free_in_cfg g1 in2 -> (* in2 should be an input of g2, not g1 *)
    ~ In out1 (outputs g2) ->
    out1 <> in2 -> (* cfg_seq cannot create a new block with an existing ID *)
    In to (inputs g1) ->
    eutt eq
         (denote_cfg (cfg_seq g1 g2 out1 in2) from to)
         (d <- denote_cfg g1 from to ;;
          match d with
          | inr dv => ret (inr dv)
          | inl (src, target) =>
              if eq_bid target out1
              then denote_cfg g2 out1 in2
              else denote_cfg g2 src target
          end).
Proof.
  intros.
  unfold denote_cfg.
  unfold cfg_seq.
  assert (Hdis : In to (inputs g1) \/ ~ (In to (inputs g1))) by (apply Classical_Prop.classic).
  destruct Hdis as [ Hdis | Hdis ] ; [|contradiction].
  rewrite (convert_typ_list_app g1 _ []).
  rewrite DenotationTheory.denote_ocfg_app.
  2: {
     apply no_reentrance_convert_typ ;
     rewrite no_reentrance_app_r.
     split; auto.
     unfold no_reentrance; cbn.
     apply Util.list_disjoint_singleton_left ;
       now fold (free_in_cfg g1 in2).
  }
  (* denote g1 in both case *)
  rewrite eutt_eq_bind ; [reflexivity|].
  intros ; simpl.
  destruct u as [ (src,target) | dv ] eqn:U ; try (reflexivity).

  rewrite Util.list_cons_app.
  rewrite (convert_typ_list_app _ g2 []).
  rewrite DenotationTheory.denote_ocfg_app.
  2: {
     apply no_reentrance_convert_typ.
     unfold no_reentrance; cbn.
     now apply Util.list_disjoint_singleton_right.}

  (* jump to the next block - two cases *)
  assert (Htarget : target = out1 \/ target <> out1)
    by (apply Classical_Prop.classic) ;
  destruct Htarget as [ Htarget | Htarget ].
  - (* b = out1 ; we jump to the new block which is empty *)
    subst.
    assert (Heqb : eq_bid out1 out1 = true) by (now apply eqb_bid_eq) ;
    rewrite Heqb.
    rewrite DenotationTheory.denote_ocfg_unfold_in
      with (bk := {|
      blk_id := out1;
       blk_phis := [];
        blk_code := [];
         blk_term := TERM_Br_1 in2;
          blk_comments := None |}).
    2: {cbn; rewrite eqv_dec_p_refl ; reflexivity.}
    denote_block_void.
    rewrite bind_bind.
    simpl ; rewrite bind_ret_l.
    (* jump to in2 - which is not out1*)
    rewrite DenotationTheory.denote_ocfg_unfold_not_in.
    2: {
       apply find_block_not_in_inputs ; simpl.
       unfold endo, Endo_id; intuition.
    }
    now rewrite bind_ret_l.
  - (* b <> out1 ; we skip the empty block *)
    rewrite DenotationTheory.denote_ocfg_unfold_not_in.
    2: {
       apply find_block_not_in_inputs ; simpl.
       unfold endo, Endo_id; intuition.
    }
    rewrite <- eqb_bid_neq in Htarget;  rewrite Htarget.
    now rewrite bind_ret_l.
Qed.


(** Compiler IMP *)
From Imp2Vir Require Import Imp.

Require Import CompileExpr.
Print Scopes.
Open Scope monad_scope.
Import MonadNotation.
Variable (name : nat -> block_id).
Hypothesis (nameInj_eq : forall n n', n = n' -> name n = name n' ).
Hypothesis (nameInj_neq : forall n n', n <> n' -> name n <> name n' ).
(* Definition mk_anon (n : nat) := Anon (Z.of_nat n). *)
(* Definition name := mk_anon. *)

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


(** Correctness compiler *)

From Coq Require Import Lia.

From ExtLib Require Import FMapAList.

From Vellvm Require Import
     Handlers.Handlers
     Syntax.ScopeTheory
     Utils.AListFacts
     Utils.PostConditions
     Utils.Tactics
     Theory.



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

Import ITreeNotations.
Import SemNotations.

(* Fixpoint compile_imp (next_reg : int) (next_lab : nat) (s : stmt) (env: StringMap.t int) *)
(*   : option (int * nat * (StringMap.t int) * (ocfg * block_id * block_id)) := *)

Theorem compile_correct : forall (next_reg : int) (next_label : nat) env (p : stmt)
                            (next_reg' : int) (next_label' : nat)
                            env' (o : ocfg) (input output : block_id)
                            mem from to genv lenv vmem,

  (* The environments of Imp and Cvir are related *)
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
    rewrite denote_cfg_block.
    2: {apply nameInj_neq ; lia. }
    rewrite interp_imp_bind.
    flatten_goal.
    admit.
    (* NOTE how is that possible to have the same  *)
      setoid_rewrite interp_cfg3_ret.
    admit.
  - (* Seq *) admit.
  - (* If *) admit.
  - (* While *) admit.
  - (* Skip *)
    simpl in *.
    inv H0.
    rewrite denote_cfg_block.
    2: { apply nameInj_neq ; lia.}
    rewrite interp_imp_ret.
    destruct (eq_bid to (name next_label)).
    + rewrite denote_code_nil.
      rewrite bind_ret_l.
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
    + simpl.
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


End CFG_Combinators.
