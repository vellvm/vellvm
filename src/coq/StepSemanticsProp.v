(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import ZArith List String Omega.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.Ollvm_ast Vellvm.AstLib Vellvm.CFG Vellvm.CFGProp.
Require Import Vellvm.StepSemantics.

Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.



Module StepSemanticsProp(A:ADDR).


  (*
  Lemma stepD_Op_inversion :
    forall CFG fn bid phis term,
      let slc := slc_pc fn bid phis term in
      forall cd1 e1 k1 id i pc2 e2 k2 
        (Hi: is_Op i)
        (HS1 : stepD CFG (slc ((id,i)::cd1), e1, k1) = Step (pc2, e2, k2)),
        pc2 = slc cd1.
  Proof.
    intros CFG fn0 bid phis term slc cd1 e1 k1 id i pc2 e2 k2 Hi HS1.
    inversion Hi.
    subst.
    simpl in HS1.
    destruct id; simpl in *.
    destruct (eval_op e1 None v); inversion HS1; auto.
    inversion HS1.
  Qed.

  
(* StepSemanticsProp.v *)
Lemma stepD_Eff_weakening :
  forall CFG fn bid phis term,
    let slc := slc_pc fn bid phis term in
    forall cd1 e1 k1 id i eff
      (Hi: is_Eff i)
      (HS1 : stepD CFG (slc ((id,i)::cd1), e1, k1) = Obs (Eff eff))
      cd2,
      stepD CFG (pc_app (slc ((id,i)::cd1)) cd2, e1, k1) = Obs (Eff (fmap (fun st => (pc_app (pc_of st) cd2, env_of st, stack_of st)) eff)).
Proof.
  intros CFG fn0 bid phis term slc cd1 e1 k1 id i eff Hi HS1 cd2.
  inversion Hi; subst; simpl in HS1; destruct id; simpl in *; inversion HS1; simpl.
  - reflexivity.
  - destruct p as [u ptr]; destruct (eval_op e1 (Some u) ptr).  simpl in HS1. inversion HS1. simpl in HS1.
    destruct v0; try solve [inversion HS1].
    simpl in *. inversion HS1.
    reflexivity.
  - destruct val as [t val]; destruct p as [u p].
    destruct (eval_op e1 (Some t) val); try solve [inversion HS1].
    destruct (eval_op e1 (Some u) p); try solve [inversion HS1].
    simpl in *.
    destruct v1; try solve [inversion HS1].
    inversion HS1.
    reflexivity.
Qed.    

(* StepSemanticsProp.v *)
Lemma stepD_Eff_Alloca_inversion :
  forall CFG fn bid phis term,
    let slc := slc_pc fn bid phis term in
    forall cd e k id t nb al eff
      (HS1 : stepD CFG (slc ((id,INSTR_Alloca t nb al)::cd), e, k) = Obs (Eff eff)),
    exists lid,
      id = IId lid /\
      eff = Alloca t (fun (a:value) => (slc cd, add_env lid a e, k)).
Proof.
  intros CFG fn0 bid phis term slc cd e k id t nb al eff HS1.
  simpl in HS1.
  inversion HS1.
  destruct id as [lid | lv].
  exists lid. split; auto. inversion H0.
  reflexivity.
  inversion H0.
Qed.

(* StepSemanticsProp.v *)
Lemma stepD_Eff_Load_inversion :
  forall CFG fn bid phis term,
    let slc := slc_pc fn bid phis term in
    forall cd e k id v t p al eff
      (HS1 : stepD CFG (slc ((id,INSTR_Load v t p al)::cd), e, k) = Obs (Eff eff)),
    exists lid a, 
      id = IId lid /\
      eff = (Load a (fun dv => (slc cd, add_env lid dv e, k))).
Proof.
  intros CFG fn0 bid phis term slc cd e k id v t p al eff HS1. 
  simpl in HS1.
  inversion HS1.
  destruct id as [lid | lv].
  exists lid.
  destruct p as [u p].
  destruct (eval_op e (Some u) p); try solve [inversion H0].
  destruct v0; try solve [inversion H0].
  simpl in H0.
  exists a. split; auto. inversion H0. reflexivity.
  inversion HS1.
Qed.

(* StepSemanticsProp.v *)
Lemma stepD_Eff_Store_inversion :
  forall CFG fn bid phis term,
    let slc := slc_pc fn bid phis term in
    forall cd e k id v val p al eff
      (HS1 : stepD CFG (slc ((id,INSTR_Store v val p al)::cd), e, k) = Obs (Eff eff)),
    exists vid a dv, 
      id = IVoid vid /\
      eff = (Store a dv (fun _ => (slc cd, e, k))).
Proof.
  intros CFG fn0 bid phis term slc cd e k id v val p al eff HS1. 
  simpl in HS1.
  destruct id as [lid | lvid].
  - inversion HS1.
  - exists lvid.
    destruct val as [u val].
    destruct p as [w p].
    destruct (eval_op e (Some u) val); try solve [inversion HS1].
    destruct (eval_op e (Some w) p); try solve [inversion HS1].
    simpl in HS1.
    destruct v1; try solve [inversion HS1].
    exists a. exists v0. inversion HS1.
     subst. split; auto.
Qed.

(* StepSemanticsProp.v *)
Lemma stepD_Op_weakening :
  forall CFG fn bid phis term,
    let slc := slc_pc fn bid phis term in
    forall id i cd1 e1 k1 pc2 e2 k2
    (Hi : is_Op i)
    (HS : stepD CFG (slc ((id,i)::cd1), e1, k1) = Step (pc2, e2, k2))
    cd2,
    stepD CFG (pc_app (slc ((id,i)::cd1)) cd2, e1, k1) = Step (pc_app pc2 cd2, e2, k2).
Proof.
  intros CFG fn0 bid phis term slc id i cd1 e1 k1 pc2 e2 k2 Hi HS cd2.
  inversion Hi.
  subst.
  simpl in HS.
  destruct id; simpl in *.
  destruct (eval_op e1 None v); inversion HS; auto.
  inversion HS.
Qed.
*)

End StepSemanticsProp.  

