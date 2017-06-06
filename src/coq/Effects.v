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
Require Import Program Classical.
Require Import paco.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

Module Type EffT.
  (* The effects interface is parameterized by the language's types and the 
   memory model's notion of addresses. *)
  Parameter typ : Set.
  Parameter addr : Set.
  Parameter value : Set.
  Parameter inj_addr: addr -> value.
End EffT.

Module Effects(ET:EffT).
Export ET.
  
(* TODO: Add other memory effects, such as synchronization operations *)
(* Notes: 
   - To allow the memory model to correctly model stack alloca deallocation,
     we would also have to expose the "Ret" instruction. 

   - What is the correct way to model global data? 
*)
Inductive effects (d:Type) : Type :=
| Alloca (t:typ)  (k:value -> d)        (* Stack allocation *)
| Load   (a:addr) (k:value -> d)
| Store  (a:addr) (v:value) (k:d)
| Call   (v:value) (args:list value) (k:value -> d)
.    

Definition effects_map {A B} (f:A -> B) (m:effects A) : effects B :=
  match m with
  | Alloca t g => Alloca t (fun a => f (g a))
  | Load a g  => Load a (fun dv => f (g dv))
  | Store a dv d => Store a dv (f d)
  | Call v args d => Call v args (fun dv => f (d dv))
  end.

Instance effects_functor : Functor effects := fun A => fun B => @effects_map A B.
Program Instance effects_functor_eq_laws : (@FunctorLaws effects) effects_functor (@eq).
Next Obligation.
  unfold fmap. unfold effects_functor. unfold effects_map. destruct a; reflexivity.
Defined.
Next Obligation.
  unfold fmap. unfold effects_functor. unfold effects_map. destruct a; reflexivity.
Defined.  

(* Observations of a computation X. *)
CoInductive Obs X :=
| Ret : X -> Obs X        (* Unfinished trace *)
| Fin : value -> Obs X    (* Finished trace *) 
| Err : string -> Obs X   (* Abort with an error *)
| Tau : Obs X -> Obs X    (* Internal step of computation *)
| Eff : effects (Obs X) -> Obs X    (* Externally visible step of computation *)
.

CoFixpoint obs_map {A B} (f:A -> B) (d:Obs A) : Obs B :=
  match d with
    | Ret a => Ret (f a)
    | Fin d => Fin d
    | Err s => Err s
    | Tau d' => Tau (obs_map f d')
    | Eff m => Eff (effects_map (obs_map f) m)
  end.

Instance Obs_functor : @Functor Obs := fun A => fun B => @obs_map A B.
(* A functor only up to stuttering equivalence. *)
(*
Program Instance OBS_functor_eq_laws : (@FunctorLaws D) OBS_functor (@obs_equiv).
*)


Definition id_match_obs {A} (d:Obs A) : Obs A :=
  match d with
    | Ret a => Ret a
    | Fin d => Fin d
    | Err s => Err s
    | Tau d' => Tau d'
    | Eff m => Eff m
  end.

Lemma id_obs_eq : forall A (d:Obs A),
  d = id_match_obs d.
Proof.
  destruct d; auto.
Qed.
Arguments id_obs_eq {_} _ .


Definition non_tau {A} (d:Obs A) : Prop :=
  match d with
  | Tau _ => False
  | _ => True
  end.

Definition tau {A} (d:Obs A) : Prop :=
  match d with
  | Tau _ => True
  | _ => False
  end.

(* Define a predicate that holds only of infinite Tau observations a.k.a. silent divergence *)
Inductive diverges_step {A} (div : Obs A -> Prop) : Obs A -> Prop :=
| div_tau : forall d, div d -> diverges_step div (Tau d)
.
Hint Constructors diverges_step.

Lemma diverges_step_mono : forall {A}, monotone1 (@diverges_step A).
Proof.
  intros A. pmonauto.
Qed.
Hint Resolve diverges_step_mono : paco.

Definition diverges {A} := paco1 (@diverges_step A) bot1.
Hint Unfold diverges.

(* observational equivalence ------------------------------------------------ *)
Section OBSERVATIONAL_EQUIVALENCE. 

  (*
  This relation doesn't allow any variation in the relations for the memory model.  
  A more parametric version would:
    - a state relation RA : A -> A -> Prop
    - have an address relation  RAddr : addr -> addr -> Prop  
    - have a value relation  RValue : value -> value -> Prop

  It builds in the "total" relation for error string observations:
     Err s1 ~~ Err s2   for any s1, s2     
     ( Could pass in E : string -> string -> Prop )
  *)


  Variable A : Type.
  Variable R : Obs A -> Obs A -> Prop.

  Inductive obs_equiv_mem_step  : effects (Obs A) -> effects (Obs A) -> Prop :=
  | obs_equiv_mem_Alloca : forall t f g, (forall (a:addr), R (f (inj_addr a)) (g (inj_addr a))) -> obs_equiv_mem_step (Alloca t f) (Alloca t g)
  | obs_equiv_mem_Load   : forall a f g, (forall (dv:value), R (f dv) (g dv)) -> obs_equiv_mem_step (Load a f) (Load a g)
  | obs_equiv_mem_Store  : forall a n d1 d2, (R d1 d2) -> obs_equiv_mem_step (Store a n d1) (Store a n d2)
  | obs_equiv_mem_Call   : forall v vs f g, (forall (dv:value), R (f dv) (g dv)) -> obs_equiv_mem_step (Call v vs f) (Call v vs g)
  .    

  Inductive obs_equiv_step : Obs A -> Obs A -> Prop :=
  | obs_equiv_step_ret : forall a, obs_equiv_step (Ret a) (Ret a)
  | obs_equiv_step_fin : forall v, obs_equiv_step (Fin v) (Fin v)
  | obs_equiv_step_err : forall s1 s2, obs_equiv_step (Err s1) (Err s2)
  | obs_equiv_step_tau : forall d1 d2 (equiv:R d1 d2), obs_equiv_step (Tau d1) (Tau d2)
  | obs_equiv_step_lft : forall d1 d2, obs_equiv_step d1 d2 -> obs_equiv_step (Tau d1) d2
  | obs_equiv_step_rgt : forall d1 d2, obs_equiv_step d1 d2 -> obs_equiv_step d1 (Tau d2)
  | obs_equiv_step_eff : forall m1 m2, obs_equiv_mem_step m1 m2 -> obs_equiv_step (Eff m1) (Eff m2)
  .
End OBSERVATIONAL_EQUIVALENCE.

Hint Constructors obs_equiv_mem_step obs_equiv_step.  (* obs_equiv *)

Lemma obs_equiv_mem_step_monotone A : forall (R1 R2:Obs A -> Obs A -> Prop)
                                        (HR: forall d1 d2, R1 d1 d2 -> R2 d1 d2) m1 m2
                                        (HM:obs_equiv_mem_step R1 m1 m2),
    obs_equiv_mem_step R2 m1 m2.
Proof.
  intros R1 R2 HR m1 m2 HM.
  dependent destruction HM; constructor; eauto.
Qed.  
Hint Resolve obs_equiv_mem_step_monotone : paco.  
                                        

Lemma obs_equiv_step_monotone A : monotone2 (@obs_equiv_step A).
Proof.
  unfold monotone2. intros. induction IN; eauto.
  eapply obs_equiv_step_eff. eapply obs_equiv_mem_step_monotone. exact LE. exact H.
Qed.
Hint Resolve obs_equiv_step_monotone : paco.

Definition obs_equiv {A} (p q: Obs A) := paco2 (@obs_equiv_step A) bot2 p q.
Hint Unfold obs_equiv.

Lemma obs_equiv_refl : forall {A}, reflexive (Obs A) obs_equiv.
Proof.
  intro A. pcofix CIH. intro d.
  pfold. destruct d; eauto.
  - destruct e; eauto. 
Qed.

Lemma obs_equiv_symm : forall {A}, symmetric (Obs A) obs_equiv.
Proof.
  intro. pcofix CIH.
  intros d1 d2 H.
  punfold H. 
  induction H; eauto; subst.
  - pfold. constructor. right. pclearbot.  eauto. 
  - pfold. constructor; auto. punfold IHobs_equiv_step.
  - pfold. constructor; auto. punfold IHobs_equiv_step.
  - pfold. constructor. inversion H; subst.
    + constructor. intro. specialize (H0 a). destruct H0.
      right. eapply CIH. eapply H0. inversion H0.
    + constructor. intro. specialize (H0 dv). destruct H0.
      right. eapply CIH. eapply H0. inversion H0.
    + constructor. right. eapply CIH. destruct H0; eauto. inversion H0. 
    + constructor. intro. specialize (H0 dv). destruct H0.
      right. eapply CIH. eapply H0. inversion H0.
Qed.

Lemma tau_head_dec : forall {A} (d:Obs A), (exists d', d = Tau d') \/ non_tau d.
Proof.
  intros.
  destruct d; try solve [right; simpl; auto].
  left. exists d. reflexivity.
Qed.  


Inductive tau_star {A} (P:Obs A -> Prop) : Obs A  -> Prop :=
| tau_star_zero : forall (d:Obs A), P d -> tau_star P d
| tau_star_tau  : forall (d:Obs A), tau_star P d -> tau_star P (Tau d)
.                                                       
Hint Constructors tau_star.

Lemma tau_star_monotone : forall {A}, monotone1 (@tau_star A).
Proof.
  intros A. unfold monotone1.
  intros x0 r r' IN LE.
  induction IN; auto.
Qed.  
Hint Resolve tau_star_monotone : paco.

(* This prediate relates two traces that agree on a non-tau step *)
Inductive obs_sync {A} (R: Obs A -> Obs A -> Prop) : Obs A -> Obs A -> Prop :=
| obs_sync_ret : forall a, obs_sync R (Ret a) (Ret a)
| obs_sync_fin : forall v, obs_sync R (Fin v) (Fin v)
| obs_sync_err : forall s1 s2, obs_sync R (Err s1) (Err s2)
| obs_sync_eff : forall m1 m2, obs_equiv_mem_step R m1 m2 -> obs_sync R (Eff m1) (Eff m2)
.
Hint Constructors obs_sync.

Lemma obs_sync_monotone : forall {A}, monotone2 (@obs_sync A).
Proof.
  intros A. unfold monotone2.
  intros x0 x1 r r' IN LE.
  induction IN; auto.
  induction H; constructor; auto.
Qed.

Inductive obs_equiv_big_step {A} (R:Obs A -> Obs A -> Prop) : Obs A -> Obs A -> Prop :=
| obs_equiv_big_diverge s1 s2 (DS1:diverges s1) (DS2:diverges s2) : obs_equiv_big_step R s1 s2
| obs_equiv_big_taus s1 s2 t1 t2
                     (TS1:tau_star (fun t => t = t1) s1)
                     (TS2:tau_star (fun t => t = t2) s2)
                     (HO: obs_sync R t1 t2) : obs_equiv_big_step R s1 s2
.                                                                 
Hint Constructors obs_equiv_big_step.

Lemma obs_equiv_big_step_monotone : forall {A}, monotone2 (@obs_equiv_big_step A).
Proof.
  intros A. unfold monotone2.
  intros x0 x1 r r' IN LE.
  induction IN; auto.
  eapply obs_equiv_big_taus. apply TS1. apply TS2.
  eapply obs_sync_monotone. apply HO. exact LE.
Qed.  
Hint Resolve obs_equiv_big_step_monotone : paco.

Definition obs_equiv_big {A} (d1 d2:Obs A) := paco2 obs_equiv_big_step bot2 d1 d2.
Hint Unfold obs_equiv_big.

Lemma obs_equiv_tau_lft : forall {A} (d1 d2:Obs A), obs_equiv d1 d2 -> obs_equiv (Tau d1) d2.
Proof.
  intros.
  pfold. apply obs_equiv_step_lft.
  punfold H.
Qed.  

Lemma obs_equiv_tau_rgt : forall {A} (d1 d2:Obs A), obs_equiv d1 d2 -> obs_equiv d1 (Tau d2).
Proof.
  intros.
  pfold. apply obs_equiv_step_rgt.
  punfold H.
Qed.  

Lemma obs_equiv_lft_inversion : forall {A} (d1 d2:Obs A), obs_equiv (Tau d1) d2 -> obs_equiv d1 d2.
Proof.
  intros A. intros d1 d2 H.
  punfold H. remember (Tau d1) as d. 
  induction H; try (solve [inversion Heqd; subst; clear Heqd]).
  - inversion Heqd. subst. apply obs_equiv_tau_rgt. pclearbot. punfold equiv.
  - inversion Heqd. subst. pfold. exact H.
  - subst. apply obs_equiv_tau_rgt. apply IHobs_equiv_step. reflexivity.
Qed.    

Lemma obs_equiv_rgt_inversion : forall {A} (d1 d2:Obs A), obs_equiv d1 (Tau d2) -> obs_equiv d1 d2.
Proof.
  intros.
  apply obs_equiv_symm. apply obs_equiv_symm in H. apply obs_equiv_lft_inversion. exact H.
Qed.  

Lemma sync_not_diverges : forall {A} (d:Obs A), tau_star non_tau d -> diverges d -> False.
Proof.
  intros A d HS.
  induction HS.
  - intros HD; dependent destruction d; punfold HD; inversion HD.
  - intros HD. apply IHHS. punfold HD. dependent destruction HD. pclearbot. apply H.
Qed.    

(* CLASSICAL! *)
Lemma sync_or_diverges : forall {A} (d:Obs A), tau_star non_tau d \/ diverges d.
Proof.
  intros A d.
  destruct (classic (tau_star non_tau d)); eauto.
  right. revert d H.
  pcofix CIH.
  intros d H.
  destruct d; try solve [exfalso; apply H; constructor; simpl; auto].
  pfold. econstructor. right. eauto.
Qed.

Lemma obs_equiv_diverges : forall {A} (d1 d2:Obs A) (EQ: obs_equiv d1 d2) (HD:diverges d1), diverges d2.
Proof.
  intros A.
  pcofix CIH.
  intros d1 d2 EQ.
  punfold EQ. induction EQ; intros HD; try solve [punfold HD; inversion HD].
  - punfold HD. inversion HD. pclearbot. subst.
    pfold. constructor. right. eauto.
  - punfold HD. inversion HD. subst. pclearbot. apply IHEQ. apply H0.
  - pfold. constructor. left. auto.
Qed.    

Lemma obs_equiv_sync : forall {A} (d1 d2:Obs A) (EQ:obs_equiv d1 d2) (HS:tau_star non_tau d1), tau_star non_tau d2.
Proof.
  intros A d1 d2 EQ HS.
  revert d2 EQ.
  induction HS; intros d2 EQ.
  - punfold EQ. induction EQ; auto.
    inversion H.
  - punfold EQ. dependent induction EQ.
    + apply tau_star_tau. apply IHHS. pclearbot. eauto.
    + apply IHHS. pfold. exact EQ.
    + apply tau_star_tau. eauto.
Qed.      

Lemma obs_equiv_diverges_or_sync : forall {A} (d1 d2:Obs A) (EQ:obs_equiv d1 d2),
    (diverges d1 /\ diverges d2) \/ (tau_star non_tau d1 /\ tau_star non_tau d2).
Proof.
  intros A d1 d2 EQ.
  destruct (@sync_or_diverges _ d1) as [HS | HD].
  - right. eauto using obs_equiv_sync.
  - left. eauto using obs_equiv_diverges.
Qed.    

Lemma obs_equiv_big_step_tau_left :  forall {A} R (d1 d2:Obs A)
                                       (HR: paco2 obs_equiv_big_step R d1 d2), paco2 obs_equiv_big_step R (Tau d1) d2.
Proof.
  intros A R d1 d2 HR.
  punfold HR.
  pfold.
  destruct HR.
  - apply obs_equiv_big_diverge; eauto. pfold. constructor. left. eauto.
  - eapply obs_equiv_big_taus; eauto.
Qed.

Lemma obs_equiv_big_step_tau_right :  forall {A} R (d1 d2:Obs A)
                                       (HR: paco2 obs_equiv_big_step R d1 d2), paco2 obs_equiv_big_step R d1 (Tau d2).
Proof.
  intros A R d1 d2 HR.
  punfold HR.
  pfold.
  destruct HR.
  - apply obs_equiv_big_diverge; eauto. pfold. constructor. left. eauto.
  - eapply obs_equiv_big_taus; eauto.
Qed.

Lemma obs_equiv_implies_obs_equiv_big: forall {A} (d1 d2:Obs A) (EQ:obs_equiv d1 d2), obs_equiv_big d1 d2.
Proof.
  intros A.
  pcofix CIH.
  intros d1 d2 EQ.
  destruct (@obs_equiv_diverges_or_sync _ d1 d2 EQ) as [[HD1 HD2]|[HS1 HS2]]; eauto.
  induction HS1.
  - induction HS2.
    + pfold. eapply obs_equiv_big_taus; try solve [eauto].
      punfold EQ. dependent destruction EQ; eauto; try solve [simpl in H; inversion H]; try solve [simpl in H0; inversion H0].
      constructor.
      apply obs_equiv_mem_step_monotone with (R1 := (upaco2 (obs_equiv_step (A:=A)) bot2)).
      intros d1 d2 H2. right.  eapply CIH. pclearbot. eapply H2.
      exact H.
    + eauto using obs_equiv_big_step_tau_right, obs_equiv_rgt_inversion.
  - eauto using obs_equiv_big_step_tau_left, obs_equiv_lft_inversion.
Qed.
      
Lemma obs_equiv_big_implies_obs_equiv : forall {A} (d1 d2:Obs A) (EQB:obs_equiv_big d1 d2), obs_equiv d1 d2.
Proof.
  intros A.
  pcofix CIH.
  intros d1 d2 EQB.
  punfold EQB. dependent destruction EQB.
  - punfold DS1. punfold DS2.
    dependent destruction DS1. dependent destruction DS2.
    pfold. econstructor; eauto. right. apply CIH. pclearbot.
    pfold. eapply obs_equiv_big_diverge; eauto.
  - dependent induction TS1; subst.
    + dependent induction TS2; subst.
      * pfold. dependent destruction HO; eauto.
        constructor. eapply obs_equiv_mem_step_monotone with (R1 := (upaco2 obs_equiv_big_step bot2)).
        intros. right. apply CIH. pclearbot. eauto.
        exact H.
      * pfold.  apply IHTS2 in HO. punfold HO.
    + pfold. constructor. apply IHTS1 in TS2; eauto. punfold TS2.
Qed.      

Lemma obs_sync_non_tau_left : forall {A} R (d1 d2:Obs A), obs_sync R d1 d2 -> non_tau d1.
Proof.
  intros A R d1 d2 H.
  dependent destruction H; simpl; auto.
Qed.

Lemma obs_sync_non_tau_right : forall {A} R (d1 d2:Obs A), obs_sync R d1 d2 -> non_tau d2.
Proof.
  intros A R d1 d2 H.
  dependent destruction H; simpl; auto.
Qed.

Lemma tau_star_non_tau_unique : forall {A} (d d1 d2:Obs A)
   (TS1:tau_star (fun s => s = d1) d)
   (TS2:tau_star (fun s => s = d2) d)
   (NT1:non_tau d1)
   (NT2:non_tau d2),
    d1 = d2.
Proof.
  intros A d d1 d2 TS1.
  revert d2.
  induction TS1; intros d2 TS2 ND1 ND2.
  - induction TS2; subst; eauto.
    + simpl in ND1. inversion ND1.
  - dependent destruction TS2; eauto.
    simpl in ND2. inversion ND2.
Qed.    

Lemma obs_equiv_mem_step_trans:
  forall {A} (R : relation (Obs A)) (TR:transitive _ R) m1 m2 m3,
    obs_equiv_mem_step R m1 m2 -> obs_equiv_mem_step R m2 m3 ->
    obs_equiv_mem_step R m1 m3.
Proof.
  intros A R TR m1 m2 m3 H12 H23.
  inversion H12; subst; inversion H23; subst; constructor; intros; eauto.
Qed.

Lemma obs_equiv_big_trans : forall {A} (d1 d2 d3:Obs A), obs_equiv_big d1 d2 -> obs_equiv_big d2 d3 -> obs_equiv_big d1 d3.
Proof.
  intros A.
  pcofix CIH.
  intros d1 d2 d3 EQB1 EQB2.
  punfold EQB1. punfold EQB2.
  destruct EQB1, EQB2; eauto.
  - exfalso. eapply sync_not_diverges, DS2.
    eapply tau_star_monotone. apply TS1.
    intros s PR. simpl in PR.  subst. eauto using obs_sync_non_tau_left.
  - exfalso. eapply sync_not_diverges, DS1.
    eapply tau_star_monotone. apply TS2.
    intros s PR. simpl in PR. subst. eauto using obs_sync_non_tau_right.
  - eapply tau_star_non_tau_unique in TS2; eauto using obs_sync_non_tau_left, obs_sync_non_tau_right.
    subst.
    pfold. eapply obs_equiv_big_taus; eauto.
    destruct HO; dependent destruction HO0; eauto.
    econstructor.

    dependent destruction H; dependent destruction H0.
    + constructor.  
      intros a. specialize H0 with (a:=a).  specialize H with (a:=a). pclearbot.
      right. eapply CIH; eauto.
    + constructor.  
      intros dv. specialize H0 with (dv:=dv).  specialize H with (dv:=dv). pclearbot.
      right. eapply CIH; eauto.
    + constructor.
      right. pclearbot. eauto.
    + constructor.
      intros dv. specialize H0 with (dv := dv). specialize H with (dv:=dv). pclearbot.
      right. eauto.
Qed.    
    

Lemma obs_equiv_trans : forall {A} (d1 d2 d3: Obs A), obs_equiv d1 d2 -> obs_equiv d2 d3 -> obs_equiv d1 d3.
Proof.
  eauto using obs_equiv_big_trans, obs_equiv_implies_obs_equiv_big, obs_equiv_big_implies_obs_equiv.
Qed.


Lemma obs_equiv_step_any_error_r : forall {A} r (d:Obs A) s1 s2,
    obs_equiv_step r d (Err s1) -> obs_equiv_step r d (Err s2).
Proof.
  intros A r d s1 s2 H.
  remember (Err s1) as d1.
  induction H; try solve [inversion Heqd1].
  - constructor.
  - subst. constructor. apply IHobs_equiv_step; auto.
Qed.    

Lemma obs_equiv_step_any_error_l : forall {A} r (d:Obs A) s1 s2,
    obs_equiv_step r (Err s1) d -> obs_equiv_step r (Err s2) d.
Proof.
  intros A r d s1 s2 H.
  remember (Err s1) as d1.
  induction H; try solve [inversion Heqd1].
  - constructor.
  - subst. constructor. apply IHobs_equiv_step; auto.
Qed.    


Section OBS_EQUIV_COIND.

  Variable A : Type.
  Variable R : Obs A -> Obs A -> Prop.

  Variables (p:Obs A) (q:Obs A).
  Hypothesis Hrpq : R p q.
  Hypothesis H : forall d1 d2,
    R d1 d2 -> obs_equiv_step R d1 d2.
  
  Theorem obs_equiv_coind :
    obs_equiv p q.
  Proof.
    revert p q Hrpq.
    pcofix CIH.
    intros ? ? Hr.
    apply H in Hr. revert r CIH. induction Hr; intros; subst; try solve [clear CIH; auto].
    - pfold. constructor. right. auto.
    - pfold. constructor. specialize (IHHr r CIH).
      punfold IHHr.
    - pfold. constructor. specialize (IHHr r CIH).
      punfold IHHr.
    - pfold.
      constructor. 
      inversion H0; subst.
      + constructor. intros. right. eauto. 
      + constructor. intros. right. eauto. 
      + constructor. right. eauto. 
      + constructor. intros. right. eauto.
  Qed.

End OBS_EQUIV_COIND.
Arguments obs_equiv_coind [_] _ [_ _] _ _.


(* This statement is false if d1 and d2 are inifinite Tau streams
    would have to weaken the conclusion to:
      (d1 = d2 /\ d1 = all_taus) \/ ... 
    this would probably require classical logic to prove.

Lemma obs_equiv_inversion : forall {A} (d1 d2:Obs A),
    obs_equiv d1 d2 ->  exists d1', exists d2', exists n, exists m,
            d1 = taus n d1' /\ d2 = taus m d2' /\ non_tau_head d1' /\ non_tau_head d2' /\ obs_equiv d1' d2'.
Proof.
Abort.  
*)


(* stuttering --------------------------------------------------------------- *)

Fixpoint taus {A} (n:nat) (d:Obs A) : Obs A :=
  match n with
  | 0 => d
  | S n => Tau (taus n d)
  end.

Lemma stutter_simpl : forall {A} (d1 d2: Obs A) n, obs_equiv (taus n d1) d2 -> obs_equiv d1 d2.
Proof.
  intros. induction n. punfold H.
  eapply IHn. simpl in H. eapply obs_equiv_lft_inversion. eapply H.
Qed.

Lemma stutter : forall {A} (d1 d2: Obs A) n m, obs_equiv (taus n d1) (taus m d2) -> obs_equiv d1 d2.
Proof.
  intros.
  eapply stutter_simpl.
  eapply obs_equiv_symm.
  eapply stutter_simpl.
  eapply obs_equiv_symm.
  eauto.
Qed.

(* error-free observations -------------------------------------------------- *)

(* Error predicate, which says whether an observation trace leads to an error *)
Inductive obs_error_free_mem_step {A} (R: Obs A -> Prop) : effects (Obs A) -> Prop :=
| obs_error_free_mem_Alloca : forall t f, (forall (a:addr), R (f (inj_addr a))) -> obs_error_free_mem_step R (Alloca t f)
| obs_error_free_mem_Load   : forall a f, (forall (dv:value), R (f dv)) -> obs_error_free_mem_step R (Load a f)
| obs_error_free_mem_Store  : forall a n d, R d -> obs_error_free_mem_step R (Store a n d)
| obs_error_free_mem_Call   : forall v vs f, (forall (dv:value), R (f dv)) -> obs_error_free_mem_step R (Call v vs f)
.                                                                                

(* No cases for Ret or Err --
   Ret means an "unfinished" computation (and shouldn't arise in the semantics of a CFG program)
   Err definitely has an error, which this predicate rules out
*)
Inductive obs_error_free_step {A} (R:Obs A -> Prop) : Obs A -> Prop :=
| obs_error_free_step_fin : forall v, obs_error_free_step R (Fin v)
| obs_error_free_step_tau : forall d, R d -> obs_error_free_step R (Tau d)
| obs_error_free_step_eff : forall m, obs_error_free_mem_step R m -> obs_error_free_step R (Eff m)
.                                                                             
Hint Constructors obs_error_free_mem_step obs_error_free_step.

Definition obs_error_free {A} := paco1 (@obs_error_free_step A) bot1.
Hint Unfold obs_error_free.

Lemma obs_error_free_gen_mon {A} : monotone1 (@obs_error_free_step A).
Proof.
  unfold monotone1. intros.
  induction IN; eauto.
  eapply obs_error_free_step_eff.
  induction H; constructor; auto.
Qed.
Hint Resolve obs_error_free_gen_mon : paco.


(* Note: for guardedness, bind Ret introduces extra Tau *)
(*
Definition bind {A B} (m:Obs A) (f:A -> Obs B) : Obs B :=
  (cofix bindf := fun m => 
     match m with
       | Ret a => Tau (f a)
       | Fin d => Fin d
       | Err s => Err s
       | Tau d' => Tau (bindf d')
       | Eff m => Eff (effects_map bindf m)
     end) m.
*)

CoFixpoint bind {A B} (m:Obs A) (f:A -> Obs B) : Obs B :=
  match m with
  | Ret a => Tau (f a)
  | Fin d => Fin d
  | Err s => Err s
  | Tau d' => Tau (bind d' f)
  | Eff e => Eff (effects_map (fun x => bind x f) e)
  end.

Lemma bind_id_eq : forall {A B} (m:Obs A) (f:A -> Obs B),
  bind m f =
  match (bind m f) with
  | Ret a => Ret a
  | Fin d => Fin d
  | Err s => Err s
  | Tau d' => Tau d'
  | Eff e => Eff e
  end.
Proof.
  intros.
  destruct (bind m f); auto.
Qed.  

Lemma binobs_unfold : forall {A B} (m:Obs A) (f:A -> Obs B),
    obs_equiv (bind m f)
    (match m with
    | Ret a => Tau (f a)
    | Fin d => Fin d
    | Err s => Err s
    | Tau d' => Tau (bind d' f)
    | Eff e => Eff (effects_map (fun m => bind m f) e)
    end).
Proof.
  intros A B m f. 
  destruct m; rewrite bind_id_eq; simpl; try eapply obs_equiv_refl.
Qed.
  
  
Program Instance Obs_monad : (@Monad Obs) (@Obs_functor) := _.
Next Obligation.
  split.
  - intros. apply Ret. exact X.
  - intros A B. apply bind.
Defined.


Ltac punfold' H := let x := fresh "_x_" in
  repeat red in H;
  let G := type of H in paco_class G (@pacounfold);
  intro x; match goal with [x:=?lem|-_] => clear x; eapply lem in H end.

End Effects.