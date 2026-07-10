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

(* Can we avoid these duplications? *)
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

Lemma I2F_refine_lift' {R1 R2} (RR : R1 -> R2 -> Prop) (m1 : EOU R1) (m2 : EOU R2) :
  I2F_EOU RR m1 m2 ->
  I2F_refine_CFG RR (EOU_to_itree m1) (EOU_to_itree m2).
Proof.
  intros []; cbn.
  - pfold; constructor; auto.
  - apply ruttc_trigger_cast; easy.
  - pfold; red; cbn.
    apply EqCutL; constructor.
  - pfold; red; cbn.
    apply EqCutR; constructor.
Qed.

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
      erbind; [rstep; [cbnn; easy | cbnn; intros; simp I2FA_Memory in *; eauto] |].
      intros.
      erbind; [apply I2F_freeze'; auto | intros]...
    - destruct val,ptr, x; cbn...
      bind_exp.
      bind_exp.
      induction H0...
      6: rbind (fun _ _ => False); [|intros _ _ []]...
      all: rbind (fun _ _ => True); [rstep; cbnn; [constructor; intuition; constructor; auto| cbn; auto] | intros [] [] _ ]; cbn...
    - destruct x; cbn...
    - destruct x; cbn...
      unfold denote_cmpxchg.
      do 3 break_goal_fast.
      break_match_goal...
      do 3 bind_exp.
      erbind; [rstep; [cbnn; easy | cbnn; intros; simp I2FA_Memory in *; eauto] |].
      intros.
      erbind.
      apply I2F_refine_lift', I2F_eval_icmp; eauto.
      intros.
      induction H3...
      break_goal_fast...
      break_goal_fast...
      rbind (fun _ _ => True); [rstep; [cbnn; easy | cbnn; intros; simp I2FA_Memory in *; eauto] |].
      intros.
      rstep; [cbnn; simp I2FE_Local; intuition | eauto].
      repeat constructor; auto.
      rstep; [cbnn; simp I2FE_Local; intuition | eauto].
      repeat constructor; auto.
    - destruct x; cbn...
      unfold denote_atomicrmw.
      repeat break_goal_fast.
      bind_exp.
      bind_exp.
      erbind; [rstep; [cbnn; easy | cbnn; intros; simp I2FA_Memory in *; eauto] | intros].
      unfold denote_atomic_rmw_operation.
      break_goal_fast...
      
      cbn; erewrite 2 Eqit.bind_ret_l;
      rbind (fun _ _ => True); [rstep; cbnn; easy | intros];
        rbind (fun _ _ => True); [rstep; cbnn; easy | intros]...

      all: try (cbn; erbind; [apply I2F_refine_lift', I2F_eval_iop; eauto | intros];
      rbind (fun _ _ => True); [rstep; cbnn; easy | intros];
        rbind (fun _ _ => True); [rstep; cbnn; easy | intros])...

      2-5: rbind (fun _ _ => False); [|intros _ _ []]...
      4-11: rbind (fun _ _ => False); [|intros _ _ []]...
      { cbn; inversion H0...
        1,3-11: rbind (fun _ _ => False); [|intros _ _ []]...
        rbind I2F_dvalue.
        2: intros;
        rbind (fun _ _ => True); [rstep; cbnn; easy | intros];
        rbind (fun _ _ => True); [rstep; cbnn; easy | intros]...
        apply I2F_refine_lift'.
        pose proof @I2F_eval_iop _ (DVALUE_I sz i) _ (DVALUE_I sz i) And H1.
        forward H4; [constructor |].
        inv H4; repeat constructor.
        induction H7; repeat constructor.
        break_goal_fast; repeat constructor.
        subst; cbn; repeat constructor.
      }
      all: erbind; [apply I2F_refine_lift', I2F_eval_fop; eauto | intros].
      all: rbind (fun _ _ => True); [rstep; cbnn; easy | intros].
      all: rbind (fun _ _ => True); [rstep; cbnn; easy | intros]...
    - destruct x, va_list_and_arg_list; cbn.
      all: bind_exp.
      all: rbind I2F_dvalue; [rstep; [cbnn; easy | cbnn; intros; simp I2FA_Memory in *; eauto] | intros].
      all: rbind I2F_dvalue; [rstep; [cbnn; easy | cbnn; intros; simp I2FA_Memory in *; eauto] | intros].
      all: rewrite 2 Eqit.bind_ret_l.
      all: erbind; [apply I2F_refine_lift', I2F_eval_gep; eauto; repeat constructor | intros].
      all: rbind (fun _ _ => True); [rstep; cbnn; easy | intros]...
    - destruct x; cbn...
      rbind (option_rel I2F_dvalue); [|intros].
      rstep; cbnn; [easy | intros; simp I2FA_Stack in *].
      induction H...
Admitted.


