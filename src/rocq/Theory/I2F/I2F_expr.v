From Equations Require Import Equations.

From Stdlib Require Import Lia.

From ExtLib Require Import Structures.Monads.

From ITree Require Import
  ITree Eq.
 
From Vellvm Require Import
  Utils
  Syntax
  Semantics
  VellvmIntegers
  Integers
  Interfaces.IPtr
  Interfaces.Params
  Implementations.Pointer
  Implementations.Provenance
  Implementations.IPtrInfinite
  Implementations.IPtrFinite
  Implementations.Memory
  Implementations.ParamsV.

From Vellvm Require Import
  Utils.rutt_cutoff
  Theory.I2F.Refinement.

From Paco Require Import paco.

Ltac rstep :=
  first [apply ruttc_trigger |
          apply ruttc_trigger_cast |
          apply ruttc_ret 
    ].

Lemma I2F_freeze_base a b :
  I2F_dvalue_base a b ->
  I2F_refine (freeze_base a) (freeze_base b).
Proof.
  intros HDV.
  induction HDV; cbn.
  (inversion HDV; subst).
  cbn. eauto.
  cbn. cbn...
  induction H...
  all: eapply ruttc_bind; [apply ruttc_map_monad_gen; eauto |]; intros...
Qed. 

Lemma I2F_freeze a b :
  I2F_dvalue a b ->
  I2F_refine (freeze a) (freeze b).
Proof.
  intros HDV.
  induction HDV. cbn. cbn...
  induction H...
  all: eapply ruttc_bind; [apply ruttc_map_monad_gen; eauto |]; intros...
Qed. 

Lemma I2F_denote_exp :
  forall (e : exp dtyp) τ, I2F_refine (@denote_exp PInf τ e) (@denote_exp PFin τ e).
Proof with try now (rstep; try (easy); eauto).
  induction e.
  - intros; cbn.
    destruct id; cbn...
  - intros [d|]; cbn...
    apply I2F_refine_lift, I2F_denote_int_syntax_as_int.
  - intros [d|]; cbn...
    apply I2F_refine_lift, I2F_denote_float_syntax_as_float.
  - destruct b; intros ?; cbn...
  - intros; cbn... 
  - (* initializer *)
    intros [d|]; cbn...
    apply I2F_refine_lift, I2F_default_dvalue_of_dtyp.
  - cbn.
    intros. 
    eapply ruttc_bind.
    + apply ruttc_map_monad.
      intros [d e] HIN; now apply (H (d,e)).
    + intros * HF...
  - cbn; intros []...
  - cbn; intros []...
  - cbn.
    intros. 
    eapply ruttc_bind.
    + apply ruttc_map_monad.
      intros [d e] HIN; now apply (H (d,e)).
    + intros * HF...
  - (* EXP_Packed_struct: the [dtyp] guard is a pure, parameter-free
         computation, related to itself by reflexivity of [I2F_EOU] ---
         no case analysis on the type. *)
    cbn; intros.
    eapply ruttc_bind.
    + apply I2F_refine_lift, I2F_EOU_refl.
    + intros [] [] _.
      eapply ruttc_bind.
      * apply ruttc_map_monad.
        intros [d e] HIN; now apply (H (d,e)).
      * intros * HF...
  - cbn; intros.
    eapply ruttc_bind.
    + apply ruttc_map_monad.
      intros [d e] HIN; now apply (H (d,e)).
    + intros * HF...
  - cbn; intros.
    eapply ruttc_bind.
    + apply ruttc_map_monad.
      intros [d e] HIN; now apply (H (d,e)).
    + intros * HF...
  - cbn; intros.
    eapply ruttc_bind; [apply IHe1 | intros].
    eapply ruttc_bind; [apply IHe2 | intros].
    apply I2F_refine_lift.
    now apply I2F_eval_iop.
  - destruct v; cbn; intros.
    eapply ruttc_bind; [apply IHe | intros].
    apply I2F_refine_lift.
    now apply I2F_eval_fneg.
  - cbn; intros.
    eapply ruttc_bind; [apply IHe1 | intros].
    eapply ruttc_bind; [apply IHe2 | intros].
    apply I2F_refine_lift.
    now apply I2F_eval_icmp.
  - cbn; intros.
    eapply ruttc_bind; [apply IHe1 | intros].
    eapply ruttc_bind; [apply IHe2 | intros].
    apply I2F_refine_lift.
    now apply I2F_eval_fop.
  - cbn; intros.
    eapply ruttc_bind; [apply IHe1 | intros].
    eapply ruttc_bind; [apply IHe2 | intros].
    apply I2F_refine_lift.
    now apply I2F_eval_fcmp.
  - cbn; intros _.
    eapply ruttc_bind; [apply IHe | intros].
    apply I2F_refine_lift.
    now apply I2F_convert.
  - destruct ptrval; cbn; intros _.
    eapply ruttc_bind; [apply IHe | intros].
    eapply ruttc_bind.
    + apply ruttc_map_monad.
      intros [x y] HIN; now apply (H (x,y)).
    + intros; apply I2F_refine_lift.
      now apply I2F_eval_gep.
  - destruct vec, idx; cbn; intros _.
    eapply ruttc_bind; [apply IHe | intros].
    eapply ruttc_bind; [apply IHe0 | intros].
    apply I2F_refine_lift.
    now apply I2F_extract_element.
  - destruct vec, elt, idx; cbn; intros _.
    eapply ruttc_bind; [apply IHe | intros].
    rewrite 2 Eqit.bind_bind.
    eapply ruttc_bind; [apply IHe0 | intros].
    eapply ruttc_bind; [apply I2F_refine_lift,I2F_dvalue_to_dvalue_base; auto | intros].
    eapply ruttc_bind; [apply IHe1 | intros].
    apply I2F_refine_lift.
    apply I2F_insert_element; auto.
  - destruct vec1,vec2,idxmask; cbn; intros _.
    eapply ruttc_bind; [apply IHe | intros].
    eapply ruttc_bind; [apply IHe0 | intros].
    eapply ruttc_bind; [apply IHe1 | intros]...
  - destruct vec; cbn; intros _.
    eapply ruttc_bind; [apply IHe | intros].
    apply I2F_refine_lift.
    now apply I2F_extract_value.
  - destruct vec, elt; cbn; intros _.
    eapply ruttc_bind; [apply IHe | intros].
    eapply ruttc_bind; [apply IHe0 | intros].
    apply I2F_refine_lift.
    now apply I2F_insert_value.
  - destruct cnd,v1,v2; cbn; intros _.
    eapply ruttc_bind; [apply IHe | intros].
    eapply ruttc_bind; [apply IHe0 | intros].
    eapply ruttc_bind; [apply IHe1 | intros].
    apply I2F_refine_lift.
    now apply I2F_eval_select.
  - destruct v; cbn; intros _.
    eapply ruttc_bind; [apply IHe | intros].
    now apply I2F_freeze.
  - cbn; intros _...
  - cbn; intros _; destruct m...
    all: try now rstep; constructor; eauto.
    destruct tv; cbn.
    eapply H; eauto.
  - (* EXP_Splat: the vector-type accessor is a pure, parameter-free
         computation, related to itself by reflexivity of [I2F_EOU] ---
         no case analysis on the type. *)
    destruct elt; cbn; intros.
    eapply ruttc_bind.
    + apply I2F_refine_lift, I2F_EOU_refl.
    + intros [sz t'] ? <-; cbn.
      eapply ruttc_bind; [apply IHe |].
      intros; apply ruttc_ret.
      constructor.
      apply Forall2_repeat; auto.
Qed.

Lemma I2F_denote_exp' :
  forall e τ,
    I2F_refine_CFG I2F_dvalue (@denote_exp' PInf τ e) (@denote_exp' PFin τ e).
Proof. 
  unfold denote_exp', withCall.
  intros.
  unfold I2F_refine_CFG.
  eapply ruttc_translate_inr'; cycle -1.
  apply I2F_denote_exp.
  all:clear.
  - exact I2F_cutUB_CFG.
  - exact I2F_cutOOM_CFG.
  (* [rutt_cutoff.inr_prerel] of the (computing) sum is definitionally
       its right component *)
  - intros A B; split; intros e1 e2 HR.
    + now destruct HR.
    + now constructor.
  - intros A B; split; intros [e1 a] [e2 b] HR.
    + now destruct HR.
    + now constructor.
Qed.

