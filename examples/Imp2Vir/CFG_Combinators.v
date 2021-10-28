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
    input <> output -> (* TODO should be a WF property of block *)
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
    setoid_rewrite DenotationTheory.denote_ocfg_unfold_in with (bk := (conv
                  {|
                     blk_id := input;
                     blk_phis := [];
                     blk_code := c;
                     blk_term := TERM_Br_1 output;
                     blk_comments := None
                  |})).
    + setoid_rewrite DenotationTheory.denote_block_unfold_cont.
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
      rewrite bind_ret_l.
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
Qed.



Lemma no_reentrance_convert_typ:
  forall (env : list (ident * typ)) [g1 g2 : ocfg],
    no_reentrance g1 g2 -> no_reentrance (convert_typ env g1) (convert_typ env g2).
Admitted.

Lemma find_block_none_singleton :
  forall b b' output, b<>b' <->
   find_block
   (conv
      [{|
         blk_id := b;
         blk_phis := [];
         blk_code := [];
         blk_term := TERM_Br_1 output;
         blk_comments := None
         |}]) b' = None.
Proof. Admitted.

Lemma denote_cfg_join : forall (g : ocfg) (output out1 out2 : block_id) from to,
    free_in_cfg g output ->
    output <> out1 ->
    output <> out2 ->
    out1 <> out2 ->
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
      rewrite DenotationTheory.denote_block_unfold.
      simpl.
      rewrite DenotationTheory.denote_no_phis.
      setoid_rewrite DenotationTheory.denote_code_nil.
      setoid_rewrite translate_ret.
      repeat (rewrite bind_ret_l).
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
      2: { now apply find_block_none_singleton. } (* easy because out1 <> out2 *)
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
      rewrite DenotationTheory.denote_block_unfold.
      simpl.
      rewrite DenotationTheory.denote_no_phis.
      setoid_rewrite DenotationTheory.denote_code_nil.
      setoid_rewrite translate_ret.
      repeat (rewrite bind_ret_l).
      rewrite DenotationTheory.denote_ocfg_unfold_not_in.
      2: { now apply find_block_none_singleton,not_eq_sym. } (* easy because out2 <> output  *)
      reflexivity.
    + (* Neither out1 or out2 *)
      apply eqb_bid_neq in Heq,Heq0.
      rewrite DenotationTheory.denote_ocfg_unfold_not_in.
      2: { now apply find_block_none_singleton,not_eq_sym. } (* easy because target <> out1  *)
      rewrite bind_ret_l.
      rewrite DenotationTheory.denote_ocfg_unfold_not_in.
      2: { now apply find_block_none_singleton,not_eq_sym.  } (* easy because target <> out2  *)
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
    free_in_cfg g1 out1 ->
    free_in_cfg g2 out1 ->
    free_in_cfg g1 in2 ->
    ~ In out1 (outputs g2) ->
    out1 <> in2 -> (* mandatory, or cfg_seq will create a new block with an existing ID *)
    to <> out1 -> (* can I relaxe this hypothesis ? *)
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
  assert (Hdis : In to (inputs g1)
                 \/ In to (inputs g2)
                 \/ ~ (In to (inputs (g1++g2)))).
  { rewrite inputs_app ; rewrite in_app_iff.
    apply or_assoc ; apply Classical_Prop.classic. }
  destruct Hdis as [ ? | [ ? | ? ]].
  
  - (* ENTRY IN g1 *)
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
    rewrite eutt_eq_bind. reflexivity.
    intros ; simpl.
    destruct u as [ (src,target) | dv ] eqn:U ; try (reflexivity).

    + (* jump to the next block *)
      assert (target = out1 \/ target <> out1). { apply Classical_Prop.classic. }
      rewrite Util.list_cons_app.
      rewrite (convert_typ_list_app _ g2 []).
      rewrite DenotationTheory.denote_ocfg_app.
      2: {
         apply no_reentrance_convert_typ.
         unfold no_reentrance; cbn.
         now apply Util.list_disjoint_singleton_right.}
      destruct H10.
      * (* b = out1 ; we jump to the new block which is empty *)
        subst.
        assert (eq_bid out1 out1 = true) by (now apply eqb_bid_eq).
        rewrite H10.
        (* cbn. *)
                rewrite DenotationTheory.denote_ocfg_unfold_in
        with (bk := {|
       blk_id := out1;
       blk_phis := [];
       blk_code := [];
       blk_term := TERM_Br_1 in2;
       blk_comments := None
     |}).
        ** rewrite bind_bind.
           rewrite DenotationTheory.denote_block_unfold.
           rewrite DenotationTheory.denote_no_phis.
           setoid_rewrite DenotationTheory.denote_code_nil.
           simpl.
           setoid_rewrite translate_ret.
           (* repeat (rewrite bind_ret_l). *)
           rewrite bind_ret_l.
           rewrite bind_ret_l.
           rewrite bind_ret_l.
           rewrite DenotationTheory.denote_ocfg_unfold_not_in.
           *** rewrite bind_ret_l. reflexivity.
           *** apply find_block_not_in_inputs. simpl.
               unfold endo, Endo_id. intuition.
        ** cbn.
           rewrite eqv_dec_p_refl.
           reflexivity.
      * (* b <> out1 ; we skip the empty block *)
        rewrite DenotationTheory.denote_ocfg_unfold_not_in.
        ** rewrite <- eqb_bid_neq in H10. rewrite H10.
           rewrite bind_ret_l  ; reflexivity.
        ** apply find_block_not_in_inputs.
           simpl. unfold endo, Endo_id. intuition.

  - (* ENTRY IN g2 *)
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
    + (* Skip g1 *)
      rewrite DenotationTheory.denote_ocfg_unfold_not_in ;
        try (apply find_block_free_id ;
             match goal with
             | h:context[no_duplicate_bid _ _] |- _ =>
                 (unfold no_duplicate_bid in h ;
                  apply Coqlib.list_disjoint_sym in h)
             end ;
             unfold free_in_cfg ;
             apply Coqlib.list_disjoint_notin with (l1 := (inputs g2)) ;
             [ rewrite inputs_convert_typ ; assumption | assumption]).
      rewrite DenotationTheory.denote_ocfg_unfold_not_in ;
        try (apply find_block_free_id ;
             match goal with
             | h:context[no_duplicate_bid _ _] |- _ =>
                 (unfold no_duplicate_bid in h ;
                  apply Coqlib.list_disjoint_sym in h)
             end ;
             unfold free_in_cfg ;
             apply Coqlib.list_disjoint_notin with (l1 := (inputs g2)) ;
             [ rewrite inputs_convert_typ ; assumption | assumption]).
      repeat (rewrite bind_ret_l).
      rewrite convert_typ_list_app ; rewrite DenotationTheory.denote_ocfg_app.
      2: {
         apply no_reentrance_convert_typ.
         unfold no_reentrance; cbn.
         now apply Util.list_disjoint_singleton_right.
      }
      * (* since to <> out1, return the identity and jump in g2 *)
        rewrite DenotationTheory.denote_ocfg_unfold_not_in.
        ** assert (eq_bid to out1 = false) by (now apply eqb_bid_neq).
           rewrite H10.
           rewrite bind_ret_l ; reflexivity.
        ** rewrite find_block_not_in_inputs; auto.
           simpl. intuition.

  - (* NO ENTRY - Identity*)
    rewrite DenotationTheory.denote_ocfg_unfold_not_in.
    + match goal with
      | h:context[ ~ (In ?t (inputs (?x++?y))) ] |- _ =>
          rewrite inputs_app in h ;
          let h' := fresh "H" in
          pose proof h as h' ;
          apply Util.not_in_app_l in h ;
          apply Util.not_in_app_r in h' ;
          apply free_in_convert_typ with (env := []) in h,h'
      end.
      rewrite DenotationTheory.denote_ocfg_unfold_not_in;
        try (now apply find_block_free_id).
      * rewrite bind_ret_l.
        assert (eq_bid to out1 = false) by (now apply eqb_bid_neq).
        rewrite H11.
        now rewrite DenotationTheory.denote_ocfg_unfold_not_in;
        try (now apply find_block_free_id).
    + apply find_block_free_id. apply free_in_convert_typ with (env := []).
      rewrite inputs_app in H9. apply free_in_cfg_app.
      split.
      now apply Util.not_in_app_l in H9.
      apply free_in_cfg_app ; unfold free_in_cfg.
      simpl ; intuition.
Qed.



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
