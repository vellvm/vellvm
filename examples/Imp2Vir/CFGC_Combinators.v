From Coq Require Import Lists.List.
Import ListNotations.

From Vellvm Require Import Syntax.

From Imp2Vir Require Import Utils.

Section CFG_Combinators.

Notation code := (code typ).
Notation ocfg := (ocfg typ).
Notation conv := (convert_typ []).
Notation texp := (texp typ).

Definition texp_break (e : texp) : dtyp * exp dtyp :=
  let (t,e) := e in
  ((typ_to_dtyp [] t), (conv e)).


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

(* While *)
Definition cfg_while_loop (code_expr : code) (cond : texp)
           (body : ocfg) (input inB output outB: block_id) : ocfg :=
  let dead_block := [mk_block outB [] [] (TERM_Br_1 input) None] in
  let cond_block := [mk_block input [] code_expr (TERM_Br cond inB output) None] in
  cond_block++body++dead_block.

(* Dedicated combinators for /for_loops/ *)
Definition cfg_for_loop (b e step : nat) (body : ocfg) (inb : block_id) : ocfg.
Admitted.


(** Misc lemmas on combinators *)
Lemma inputs_seq : forall (g1 g2 : ocfg) (out1 in2 :  block_id),
    inputs (cfg_seq g1 g2 out1 in2) =
      inputs g1 ++ [out1] ++ inputs g2.
Proof.
  intros.
  unfold cfg_seq.
  apply inputs_app.
Qed.


(** WF properties *)
(* TODO *)

End CFG_Combinators.
