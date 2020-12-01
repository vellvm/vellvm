From Coq Require Import List.
Import ListNotations.

From Vellvm Require Import
     Utils.Tactics
     Syntax.LLVMAst
     Syntax.CFG
     Syntax.Scope
     Syntax.TypToDtyp
     Semantics.TopLevel
     Theory.DenotationTheory.

Import D.

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
    | h: wf_ocfg_bid _ |- find_block _ (_ ++ _) _ = _ =>
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
    The [vjmp] tactic exploits [solve_find_block] while being aware of the possiblity of the graph to be
    hidden in order to perform automatically the symbolic step described in the comment [Hiding the ambient CFG].

    

 *)
(*
(* TO MOVE *)
Lemma convert_typ_block_app : forall (a b : list (block typ)) env, (convert_typ env (a ++ b) = convert_typ env a ++ convert_typ env b)%list.
Proof.
  induction a as [| [] a IH]; cbn; intros; auto.
  rewrite IH; reflexivity.
Qed.


Ltac vjmp :=
  rewrite denote_ocfg_unfold_in; cycle 1;
  [match goal with
   | h: hidden_cfg _ |- _ => inv h
   | h: visible_cfg _ |- _ => inv h
   | _ => idtac
   end;
   cbn; rewrite ?convert_typ_block_app;
   try solve_find_block |].

Ltac vjmp_out :=
  rewrite denote_bks_unfold_not_in; cycle 1;
  [apply find_block_fresh_id; eauto |]. 



Ltac focus_single_step_v :=
  match goal with
    |- eutt _ _ (ITree.bind _ ?x) => remember x
  end.

Ltac focus_single_step_h :=
  match goal with
    |- eutt _ (ITree.bind _ ?x) _ => remember x
  end.

Ltac focus_single_step :=
  match goal with
    |- eutt _ (ITree.bind _ ?x) (ITree.bind _ ?y) => remember x; remember y
  end.

*)
