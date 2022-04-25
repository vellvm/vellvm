(* begin hide *)
From Coq Require Import List.
Import ListNotations.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     ITree
     Eq.Eqit
     TranslateFacts.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics
     Syntax.ScopeTheory
     Theory.DenotationTheory
     Theory.ExpLemmas
     Theory.InstrLemmas
     Theory.InterpreterCFG.

(* end hide *)


(** * Resolving block fetching
    To reduce [denote_bks bks (b_f,b_s)], one needs to find in [bks] the
    block associated to [b_s] in the association map via [find_block].
    We try to automate this tedious process as much as possible. More
    specifically, we automate it exactly when the label id looked up
    appears explicitly in [bks] up to reduction.

    To do so we simply crawl over the list until we find the identifier.
    In order to support open cfgs containing generic code, we assume that
    the [ocf] is well-formed in the sense of [wf_ocfg_bid], i.e. that
    all blocks have distinct identifiers. 
 *)

Ltac solve_find_block :=
  cbn;
  match goal with
  (* If the [ocfg] contains a single block, we are done exactly if it has the id we are looking for *)
    | |- find_block [_] _ = _ => apply find_block_eq; reflexivity
  (* Otherwise, if the [ocfg] has a head block, we:
     - first check if that's the one we are looking for
     - otherwise dismiss it, focus our well-formedness hypothesis similarly, and continue recursively.
     - if it is instead built by appending two sub-graphs, we call ourselves recursively in each branch,
     and don't forget to shape the well-formedness hypothesis in each case beforehand.
   *)
    | h: wf_ocfg_bid _ |- find_block (_ :: _) _ = _ =>
      first [apply find_block_eq; reflexivity |
             apply find_block_tail_wf; [eassumption | apply wf_ocfg_bid_cons in h; solve_find_block]]
    | h: wf_ocfg_bid _ |- find_block (_ ++ _) _ = _ =>
      first [apply find_block_app_l_wf; [eassumption | apply wf_ocfg_bid_app_l in h; solve_find_block] |
             apply find_block_app_r_wf; [eassumption | apply wf_ocfg_bid_app_r in h; solve_find_block]]
  end.

(** * Hiding the ambient CFG

    Consider that you are reasoning about a VIR open cfg [bks], which you are relating to some computation [P].
    Your goal will look something like:
                                  [eutt R (denote_ocfg bks (b_f, b_s)) P]
    Assuming for instance that the block [b_s] appears concretely in [bks] as [bk_s], you can step symbolically
    in the VIR part of the goal, resulting in (assuming a [bind] in the exception monad for clarity):
                    [eutt R (b_t <- denote_block bk_s b_f;; denote_ocfg bks (b_s,b_f)) P]
    At this point, you really only care about the semantics of [bk_s]. Yet, you are still displaying [bks] as
    a whole in your goal, a syntactic entity that can easily be dozen of lines long on simple exemples.

    To alleviate the pain, we introduce a little trick to hide the ambient [ocfg].
    The first idea is to move it in your context rather than your goal. This can be done naturally with a simple
    [remember], but you want to additionally box it so that it does not get undone by [subst].
    The second idea is to introduce two boxes, one used when the user is interested in looking at the graph, and
    one whose printing notation completely dismiss the argument.

    The tactic [hide_cfg] then takes care of wrapping it in a hidden box. This tactic performs the hiding whether
    the graph is apparent in the goal or in a visible box in the context.

    The tactic [show_cfg] moves the [ocfg] from a hidden box to a visible one.

 *)

Variant hidden_cfg  (T: Type) : Type := boxh_cfg (t: T).
Variant visible_cfg (T: Type) : Type := boxv_cfg (t: T).
Ltac hide_cfg :=
  match goal with
  | h : visible_cfg _ |- _ =>
    let EQ := fresh "VG" in
    destruct h as [EQ];
    apply boxh_cfg in EQ
  | |- context[denote_ocfg ?cfg _] =>
    remember cfg as G eqn:VG;
    apply boxh_cfg in VG
  end.
Ltac show_cfg :=
  match goal with
  | h: hidden_cfg _ |- _ =>
    let EQ := fresh "HG" in
    destruct h as [EQ];
    apply boxv_cfg in EQ
  end.
Notation "'hidden' G" := (hidden_cfg (G = _)) (only printing, at level 10).

(** * Entering a block

    The [vjmp] tactic exploits [solve_find_block] while being aware of the possibility of the graph to be
    hidden in order to perform automatically the symbolic step described in the comment [Hiding the ambient CFG].

    The tactic [vjmp] always performs the jump, tries to solve the lookup automatically, and present it to the user
    if it fails.

 *)

Ltac vjmp :=
  rewrite denote_ocfg_unfold_in; cycle 1;
  [match goal with
   | h: hidden_cfg _ |- _ => inv h
   | h: visible_cfg _ |- _ => inv h
   | _ => idtac
   end;
   cbn; rewrite ?convert_typ_ocfg_app;
   try solve_find_block |].

(** * Jumping out of a [ocfg]

    The [vjmp_out] is the alternative to [vjmp] in the case where we jump out of the graph.
    The tactic tries to trivially discharge the freshness of the block id in the graph, and
    presents to the user the goal otherwise.

*)

Ltac vjmp_out :=
  rewrite denote_ocfg_unfold_not_in; cycle 1;
  [apply find_block_free_id; eauto |]. 

(** * Symbolic stepper

    The equational theory of VIR allows an (interpret) denoted program to be stepped through.

    The basic idea for an elementary _contextual reduction_ simply relies on:
    - Prohibiting reduction of all [denote_] functions
    - Pattern match on the out-most syntactic construct to rewrite its denotation into a [bind]
    - Commute the interpreter with the newly introduce [bind]
    This contextual reduction is performed (at level of interpretation 3) by the tactic [vred_C3].

    By doing so, we end in one of three cases w.r.t. to the new head of the computation (in the
    sens of the first argument of the out-most [bind]:
    - we have a new composed syntactic component, i.e. a new context we can reduce further with the
      same process.
    - we have a concrete elementary syntactic component -- an expression, an instruction or a terminator.
      In this case we can perform a proper semantic step.
      * Tactic [vred_E3] performs this stepping for expressions. The tactic is slightly conservative: it
        does not support the GEP instruction, its current axiomatization being incomplete.
      * Tactic [vred_I3] performs this stepping for instructions.
        The tactic is partial at the moment.
      * Tactics [vred_BL3] (resp. [vred_BR3]) reduce a conditional branch terminator by picking
        the left (resp. right) branch.

    Since all these rules are (weak) bisimulation (i.e. based on [eq] as the return relation),
    note that we can perform this symbolic execution during any simulation proof.

 *)

Ltac vred_C3_k k :=
  (* Reduce annoying type conversion *)
  rewrite ?typ_to_dtyp_equation;
  match goal with
  | |- context[denote_block] =>
    (* Structural handling: block case *)
    first [rewrite denote_block_unfold_cont; cbn | rewrite denote_block_unfold; cbn];
    do k idtac "Reduced block"
  | |- context[denote_phis _ _]  =>
    (* Structural handling: phi case *)
    (* YZ: Currently no automation for non empty phis. TODO *)
    first [rewrite denote_no_phis];
    do k idtac "Reduced phis"
  | |- context[denote_code] =>
    (* Structural handling: code case *)
    first [rewrite denote_code_nil |
           rewrite denote_code_singleton |
           rewrite denote_code_cons |
           rewrite ?convert_typ_code_app, ?tfmap_list_app, denote_code_app];
    do k idtac "Reduced code"
  | |- context[denote_terminator] =>
    (* Structural handling: code case *)
    first [rewrite denote_term_br_1];
    do k idtac "Reduced direct jump"
   | |- context[denote_exp] => 
    (* Structural handling: expression case *)
    first [rewrite translate_trigger; (rewrite LU_to_exp_Local || rewrite LU_to_exp_Global);
           rewrite (* subevent_subevent, *) translate_trigger;
           (rewrite exp_to_instr_Local || rewrite exp_to_instr_Global)(* ; rewrite subevent_subevent *)];
    do k idtac "Reduced exp"
  | |- _ => do k idtac "no progress made"
  end;
  (* clean up *)
  rewrite 1?interp_cfg3_ret, 1?bind_ret_l;
  rewrite 1?interp_cfg3_bind, 1?bind_bind.

(* Stupid trick to have versions of the tactic supporting light debugging.
   [vred_C3D] additionally prints the branch it take.
 *)
Tactic Notation "vred_C3_k'" integer(k) := vred_C3_k k.
Tactic Notation "vred_C3" := vred_C3_k' 0.
Tactic Notation "vred_C3D" := vred_C3_k' 1.

Ltac vred_E3 :=
first [rewrite denote_exp_LR; cycle 1 |
         rewrite denote_exp_GR; cycle 1 |
         rewrite denote_exp_i64 |
         rewrite denote_exp_i64_repr |
         rewrite denote_exp_double |
         rewrite denote_ibinop_concrete; cycle 1; try reflexivity |
         rewrite denote_fbinop_concrete; cycle 1; try reflexivity |
         rewrite denote_icmp_concrete; cycle 1; try reflexivity |
         rewrite denote_fcmp_concrete; cycle 1; try reflexivity |
         rewrite denote_conversion_concrete; cycle 1 |
         idtac].

Ltac vred_I3 :=
  first [rewrite denote_instr_load; eauto; cycle 1 |
         rewrite denote_instr_intrinsic; cycle 1; try reflexivity |
         rewrite denote_instr_op; cycle 1 |
         idtac
        ].

Ltac vred_BL3 := rewrite denote_term_br_l;
                 [rewrite 1?interp_cfg3_ret, 1?bind_ret_l, 1?interp_cfg3_bind, 1?bind_bind |];
                 cycle 1.
Ltac vred_BR3 := rewrite denote_term_br_r;
                 [rewrite 1?interp_cfg3_ret, 1?bind_ret_l, 1?interp_cfg3_bind, 1?bind_bind |];
                 cycle 1.

Ltac vstep3 :=
  first [progress vred_E3 | vred_I3];
  rewrite 1?interp_cfg3_ret, 1?bind_ret_l;
  rewrite 1?interp_cfg3_bind, 1?bind_bind.


(** * Focusing during [eutt] proofs

    During a proof based on [eutt], the recurrent pattern consists in reducing the considered
    computations as sequences of computations using the equational theory of interest.
    This leads to situations where the goal is cluttered by continuations where only the prefix
    is currently of interest.

    The following tactics simply put in the context such continuations.

    We may want to hide the continuations altogether as is done for the [cfg].

 *)

Ltac focus_single_step_r :=
  match goal with
    |- eutt _ _ (ITree.bind _ ?x) => remember x
  end.

Ltac focus_single_step_l :=
  match goal with
    |- eutt _ (ITree.bind _ ?x) _ => remember x
  end.

Ltac focus_single_step :=
  match goal with
    |- eutt _ (ITree.bind _ ?x) (ITree.bind _ ?y) => remember x; remember y
  end.

(** * Hiding a side during [eutt] proofs

    General tactics to move to the context parts of an [eutt] goal.
 *)

Ltac eutt_hide_left_named H :=
  match goal with
    |- eutt _ ?t _ => remember t as H
  end.

(* with hypothesis name provided *)
Tactic Notation "eutt_hide_left" ident(hypname) :=
  eutt_hide_left_named hypname.

(* with hypothesis name auto-generated *)
Tactic Notation "eutt_hide_left" :=
  let H := fresh "EL" in
  eutt_hide_left_named H.

Ltac eutt_hide_right_named H :=
  match goal with
    |- eutt _ _ ?t => remember t as H
  end.

(* with hypothesis name provided *)
Tactic Notation "eutt_hide_right" ident(hypname) :=
  eutt_hide_right_named hypname.

(* with hypothesis name auto-generated *)
Tactic Notation "eutt_hide_right" :=
  let H := fresh "ER" in
  eutt_hide_right_named H.

Ltac eutt_hide_rel_named H :=
  match goal with
    |- eutt ?t _ _ => remember t as H
  end.

(* with hypothesis name provided *)
Tactic Notation "eutt_hide_rel" ident(hypname) :=
  eutt_hide_rel_named hypname.

(* with hypothesis name auto-generated *)
Tactic Notation "eutt_hide_rel" :=
  let H := fresh "ER" in
  eutt_hide_rel_named H.

