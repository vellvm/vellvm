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
Require Import Vellvm.LLVMAst Vellvm.AstLib Vellvm.CFG Vellvm.CFGProp.
Require Import Vellvm.LLVMIO Vellvm.StepSemantics.

Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.



Module StepSemanticsProp(A:ADDR).
  Module SS := StepSemantics(A).
  Import SS.
  Import SS.DV.

Section Properties.
(* environment facts -------------------------------------------------------- 
  Lemma lookup_env_hd : forall id dv e, lookup_env (add_env id dv e) id = Ret dv.
  Proof.
    intros id dv e.  unfold lookup_env. 
    unfold add_env.
    apply ENV.find_1. apply ENV.add_1. reflexivity.
  Qed.  

  Lemma lookup_env_tl : forall id1 v1 e id2,
      id1 <> id2 -> lookup_env (add_env id1 v1 e) id2 = lookup_env e id2.
  Proof.
    unfold lookup_env.
    intros id1 v1 e id2 H.
    unfold add_env. 
    remember (ENV.find (elt:=value) id2 (ENV.add id1 v1 e)) as x.
    remember (ENV.find (elt:=value) id2 e) as y.
    destruct x; destruct y; auto.
    - symmetry in Heqx. rewrite <- ENVFacts.find_mapsto_iff in Heqx.
      symmetry in Heqy. rewrite <- ENVFacts.find_mapsto_iff in Heqy.
      rewrite ENVFacts.add_neq_mapsto_iff in Heqx; auto.
      assert (v = v0). { eapply ENVFacts.MapsTo_fun; eauto. }
                       subst; reflexivity.                 
    - symmetry in Heqx. rewrite <- ENVFacts.find_mapsto_iff in Heqx.
      symmetry in Heqy. rewrite <- ENVFacts.not_find_in_iff in Heqy.
      rewrite ENVFacts.add_neq_mapsto_iff in Heqx; auto.
      unfold ENV.In in Heqy. unfold ENV.Raw.In0 in Heqy. assert False. apply Heqy. exists v. apply Heqx. destruct H0.
    - symmetry in Heqx. rewrite <- ENVFacts.not_find_in_iff in Heqx.
      symmetry in Heqy. rewrite <- ENVFacts.find_mapsto_iff in Heqy.
      assert False. apply Heqx. unfold ENV.In.  unfold ENV.Raw.In0. exists v. apply ENV.add_2; auto. destruct H0.
  Qed.  


  Lemma lookup_add_env_inv :
    forall id1 v e id2 u
      (Hl: lookup_env (add_env id1 v e) id2 = Some u),
      (id1 = id2 /\ v = u) \/ (id1 <> id2 /\ lookup_env e id2 = Some u).
  Proof.
    intros id1 v e id2 u Hl.
    unfold add_env in Hl.
    unfold lookup_env in *.
    rewrite <- ENVFacts.find_mapsto_iff in Hl.
    apply ENVFacts.add_mapsto_iff in Hl.
    destruct Hl as [H | H].
    - left. assumption.
    - right. rewrite <- ENVFacts.find_mapsto_iff. assumption.
  Qed.      
 *)
  
  Definition pc_satisfies (CFG:mcfg) (p:pc) (P:cmd -> Prop) : Prop :=
    forall cmd, fetch CFG p = Some cmd -> P cmd.


  (* Move to AstLib.v ? *)
  Definition is_Op (i:instr) : Prop :=
    match i with
    | INSTR_Op _ => True
    | _ => False
    end.

  Definition is_Eff (i:instr) : Prop :=
    match i with 
    | INSTR_Alloca t nb a => True
    | INSTR_Load v t p a => True
    | INSTR_Store v val p a => True
    | _ => False    (* TODO: Think about call *)
    end.
  
  Definition is_Call (i:instr) : Prop :=
    match i with
    | INSTR_Call _ _ => True
    | _ => False
    end.
  
  Definition pc_non_call (CFG:mcfg) (p:pc) : Prop :=
    pc_satisfies CFG p (fun c => exists i, not (is_Call i) /\ c = Inst i).

  Ltac step_destruct :=
    repeat (match goal with
            | [ H : context[do _ <- trywith _ ?E; _] |- _ ] => destruct E; [simpl in H | solve [inversion H]]
            | [ H : context[do _ <- ?E; _] |- _ ] => destruct E; [solve [inversion H] | simpl in H]
            | [ H : context[match ?E with _ => _ end] |- _ ] => destruct E; try solve [inversion H]; simpl in H
            | [ H : Step (?p, _ , _) = Step (?q, _, _) |- Some ?p = Some ?q ] => inversion H; auto
            | [ H : ~ (is_Call (INSTR_Call _ _)) |- _ ] => simpl in H; contradiction
            end).

  (* Not true for Call *)
  (*
  Lemma step_pc_incr_inversion:
    forall CFG pc1 e1 k1 pc2 e2 k2
      (Hpc: pc_non_call CFG pc1)
      (Hstep: step CFG (pc1, e1, k1) = Step (pc2, e2, k2)),
      incr_pc CFG pc1 = Some pc2.
  Proof.
    (*
    intros CFG pc1 e1 k1 pc2 e2 k2 Hpc Hstep.
    simpl in Hstep.
    unfold pc_non_call in Hpc. unfold pc_satisfies in Hpc.
    destruct (fetch CFG pc1); try solve [inversion Hstep]; simpl in Hstep.
    specialize Hpc with (cmd0 := c). destruct Hpc as [i [Hi Hc]]; auto.
    subst.
    destruct (incr_pc CFG pc1); [simpl in Hstep | solve [inversion Hstep]].
    step_destruct.*)
    admit. (* TODO: fix up once the effects interface is stabilized *)
  Admitted.
*)
End Properties.

  
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

