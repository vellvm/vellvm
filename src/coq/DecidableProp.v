
Require Import ZArith.

(* CompCert dependencies *)
Require Import compcert.lib.Integers.

(* Vellvm dependencies *)
Require Import Vellvm.Ollvm_ast Vellvm.CFG Vellvm.StepSemantics Vellvm.Memory.
Require Import Vellvm.Classes.
Require Import Vellvm.AstLib.
Require Import Vellvm.DecidableEquality.

(** ** Basic Propositions *)

(*
Instance dec_compiled:
  forall elts c, Decidable (compiled_code (elts : list elt) (c : code)).
Proof.
  unfold Decidable.
  induction elts as [ | [bid | iid1 instr1 | iid1 term]]; intros [ | (iid2, instr2)];
    try solve [left; auto];
    try solve [right; intros H; inversion H; auto].
  specialize IHelts with l.
  destruct IHelts as [compile_eq | compile_neq];
    try solve [right; intros H; apply compile_neq; inversion H; auto].
  destruct (iid1 == iid2) as [iid_eq | iid_neq];
    destruct (instr1 == instr2) as [instr_eq | instr_neq];
    try solve [right; intros H;
               try (apply iid_neq);
               try (apply instr_neq);
               inversion H; subst; auto];
    try solve [left; rewrite iid_eq; rewrite instr_eq;
               constructor; auto].
Defined.
*)
Instance dec_is_Op : forall (i : instr), Decidable (is_Op i).
Proof.
  intros i; unfold Decidable; destruct i;
    try solve [right; intros H; inversion H; auto];
    try solve [left; constructor].
Defined.

Instance dec_is_Eff : forall (i : instr), Decidable (is_Eff i).
Proof.
  intros i; unfold Decidable; destruct i;
    try solve [right; intros H; inversion H; auto];
    try solve [left; constructor].
Defined.
