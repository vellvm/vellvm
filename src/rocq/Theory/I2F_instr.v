From Equations Require Import Equations.

From Stdlib Require Import Lia.

From ExtLib Require Import Structures.Monads.

From ITree Require Import ITree Eq HeterogeneousRelations.

From Vellvm Require Import
  Utils
  Syntax
  VellvmIntegers
  Integers
  DynamicValues
  EOU
  LLVMEvents
  Semantics.Operations
  Interfaces.IPtr
  Interfaces.Params
  Implementations.Address
  Implementations.Provenance
  Implementations.IPtrInfinite
  Implementations.IPtrFinite
  Implementations.Memory
  Implementations.ParamsV
  Denotation.

From Vellvm Require Import
  Theory.rutt_cutoff
  Theory.I2F.

From Paco Require Import paco.
  Ltac rstep :=
    first [apply ruttc_trigger |
            apply ruttc_trigger_cast |
            apply ruttc_ret 
      ].

Tactic Notation "rbind" uconstr(x) := eapply ruttc_bind with (RR := x).
Tactic Notation "erbind" := eapply ruttc_bind.

From Stdlib Require Import
  Program Setoid Morphisms List.

#[global]Instance ruttc_eq_itree {E1 E2 R1 R2 Rcutr Rcutl REv RAns RR} :
  Proper (eq_itree Logic.eq ==> eq_itree Logic.eq ==> flip impl) (@ruttc E1 E2 R1 R2 Rcutr Rcutl REv RAns RR).
Proof.
  intros ?? EQ1 ?? EQ2; rewrite EQ1,EQ2; intuition.
Qed.

Ltac cbnn := cbn; unfold resum, ReSum_id, id_, Id_IFun.
Ltac bind_exp := erbind; [apply I2F_denote_exp'| intros].

Lemma I2F_freeze' a b :
  I2F_dvalue a b ->
  I2F_refine_CFG I2F_dvalue (freeze a) (freeze b).
Proof with try now (rstep; cbnn; try (easy); eauto).
  (* automation is different in this file from the expression one, to understand *)
(*   intros HDV. *)
(*   induction HDV; cbn... *)

(*   all: eapply ruttc_bind; [apply ruttc_map_monad_gen; eauto |]; intros... *)
(* Qed.  *)
Admitted.

Lemma I2F_denote_instr :
  forall i va1 va2,
    option_rel I2F_Addr va1 va2 ->
      I2F_refine_CFG TT
        (@denote_instr PInf i va1) (@denote_instr PFin i va2).
  Proof with try now (rstep; cbnn; try (easy); eauto).
    intros [[x i] ?] ? ? HR.
    destruct i.
    - cbn; break_match...
    - cbn; break_match...
      subst.
      bind_exp.
      rbind TT...
      intros ???...
    - destruct x, fn.
      + cbn.
        rbind (Forall2 I2F_dvalue).
        { apply ruttc_map_monad.
          intros [] HIN.
          apply I2F_denote_exp'.
        }
        break_match...
        * intros.
          rewrite 2 Eqit.bind_bind.
          rbind (sum_rel I2F_dvalue I2F_dvalue)...
          intros * HR'.
          inv HR'.
          rbind (fun _ _ => False)...
          intros ?? [].
          rewrite 2 Eqit.bind_ret_l...
        * intros.
          rewrite 2 Eqit.bind_bind.
          bind_exp.
          rewrite 2 Eqit.bind_bind.
          rbind (sum_rel I2F_dvalue I2F_dvalue)...
          intros * HR'.
          inv HR'.
          rbind (fun _ _ => False)...
          intros ?? [].
          rewrite 2 Eqit.bind_ret_l...
      + cbn.
        rbind (Forall2 I2F_dvalue).
        { apply ruttc_map_monad.
          intros [] HIN.
          apply I2F_denote_exp'.
        }
        intros.
        break_match...
        * intros.
          rewrite 2 Eqit.bind_bind.
          rbind (sum_rel I2F_dvalue I2F_dvalue)...
          intros * HR'.
          inv HR'.
          rbind (fun _ _ => False)...
          intros ?? [].
          rewrite 2 Eqit.bind_ret_l...
        * intros.
          rewrite 2 Eqit.bind_bind.
          bind_exp.
          rewrite 2 Eqit.bind_bind.
          rbind (sum_rel I2F_dvalue I2F_dvalue)...
          intros * HR'.
          inv HR'.
          rbind (fun _ _ => False)...
          intros ?? [].
          rewrite 2 Eqit.bind_ret_l...
        
    - destruct x; cbn[denote_instr].
      2: rstep; constructor.
      admit.
      (* break_match_goal. *)
      (* + break_goal_fast. *)
      (*   cbn. rewrite 2 Eqit.bind_bind. *)
      (*   erbind; [apply I2F_denote_exp'| intros; rewrite ?Eqit.bind_bind]. *)
      (*   rbind I2F_dvalue. *)
      (*   { apply ruttc_trigger. *)
      (*     constructor; intuition. *)
      (*     2:{ cbn; intros... *)
      (*     admit. *)
      (*     (* cbn in *; unfold resum, ReSum_id, id_, Id_IFun. *) *)
      (*     (* intros ??; rewrite I2FA_Memory_equation_13. *) *)
      (*       (* in H0 *) *)
    - destruct x; cbn...
      destruct ptr.
      bind_exp.
      erbind; [rstep; [cbnn; easy |] |].
      cbnn; intros; simp I2FA_Memory in *; eauto.
      intros.
      erbind; [apply I2F_freeze'; auto | intros]...
    - destruct val,ptr, x; cbn...
      bind_exp.
      bind_exp.
      induction H0...
      6: rbind (fun _ _ => False); [|intros _ _ []]...
      all: rbind (fun _ _ => True); [rstep; cbnn; [constructor; intuition; constructor; auto| cbn; auto] | intros [] [] _ ]; cbn...
    -   
     
  Admitted.
 
