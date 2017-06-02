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
| Tau : Obs X -> Obs X      (* Internal step of computation *)
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

Section UNFOLDING.

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

End UNFOLDING.

Arguments id_obs_eq {_} _ .


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

(*
  This relation doesn't allow any variation in the relations for the memory model.  A more parametric version would:
    - have an address relation  A : addr -> addr -> Prop  
    - have a value relation  V : value -> value -> Prop
*)
Inductive obs_equiv_mem_step {A} (R:Obs A -> Obs A -> Prop) : effects (Obs A) -> effects (Obs A) -> Prop :=
| obs_equiv_mem_Alloca : forall t f g, (forall (a:addr), R (f (inj_addr a)) (g (inj_addr a))) -> obs_equiv_mem_step R (Alloca t f) (Alloca t g)
| obs_equiv_mem_Load  : forall a f g, (forall (dv:value), R (f dv) (g dv)) -> obs_equiv_mem_step R (Load a f) (Load a g)
| obs_equiv_mem_Store : forall a n d1 d2, (R d1 d2) -> obs_equiv_mem_step R (Store a n d1) (Store a n d2)
| obs_equiv_mem_Call  : forall v vs f g, (forall (dv:value), R (f dv) (g dv)) -> obs_equiv_mem_step R (Call v vs f) (Call v vs g)
.    

Inductive obs_equiv_step {A} (R:Obs A -> Obs A -> Prop) : Obs A -> Obs A -> Prop :=
| obs_equiv_step_ret : forall a, obs_equiv_step R (Ret a) (Ret a)
| obs_equiv_step_fin : forall v, obs_equiv_step R (Fin v) (Fin v)
| obs_equiv_step_err : forall s1 s2, obs_equiv_step R (Err s1) (Err s2)
| obs_equiv_step_tau : forall d1 d2 (equiv:R d1 d2), obs_equiv_step R (Tau d1) (Tau d2)
| obs_equiv_step_lft : forall d1 d2, obs_equiv_step R d1 d2 -> obs_equiv_step R (Tau d1) d2
| obs_equiv_step_rgt : forall d1 d2, obs_equiv_step R d1 d2 -> obs_equiv_step R d1 (Tau d2)
| obs_equiv_step_eff : forall m1 m2, obs_equiv_mem_step R m1 m2 -> obs_equiv_step R (Eff m1) (Eff m2)
.    

Hint Constructors obs_equiv_mem_step obs_equiv_step.  (* obs_equiv *)

Lemma obs_equiv_gen_mon A : monotone2 (@obs_equiv_step A).
Proof.
  unfold monotone2. intros. induction IN; eauto.
  eapply obs_equiv_step_eff. induction H.
  - constructor. eauto.
  - constructor. eauto.
  - constructor. eauto.
  - constructor. eauto.
Qed.
Hint Resolve obs_equiv_gen_mon : paco.

Definition obs_equiv {A} (p q: Obs A) := paco2 (@obs_equiv_step A) bot2 p q.
Hint Unfold obs_equiv.

Fixpoint taus {A} (n:nat) (d:Obs A) : Obs A :=
  match n with
  | 0 => d
  | S n => Tau (taus n d)
  end.

Instance Obs_functor : @Functor Obs := fun A => fun B => @obs_map A B.


(* A functor only up to stuttering equivalence. *)
(*
Program Instance OBS_functor_eq_laws : (@FunctorLaws D) OBS_functor (@obs_equiv).
*)
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
  punfold H. remember (upaco2 obs_equiv_step bot2).
  induction H; eauto; subst.
  - pfold. constructor. right. eapply CIH.
    destruct equiv; eauto. inversion H. 
  - pfold. constructor. punfold IHobs_equiv_step.
  - pfold. constructor. punfold IHobs_equiv_step.
  - pfold. constructor. inversion H; subst.
    + constructor. intro. specialize (H0 a). destruct H0.
      right. eapply CIH. eapply H0. inversion H0.
    + constructor. intro. specialize (H0 dv). destruct H0.
      right. eapply CIH. eapply H0. inversion H0.
    + constructor. right. eapply CIH. destruct H0; eauto. inversion H0. 
    + constructor. intro. specialize (H0 dv). destruct H0.
      right. eapply CIH. eapply H0. inversion H0.
Qed.


Lemma obs_equiv_lft_inversion : forall {A} (d1 d2:Obs A), obs_equiv (Tau d1) d2 -> obs_equiv d1 d2.
Proof.
  intros A d1 d2 H.  punfold H. remember (Tau d1) as d. induction H; try (inversion Heqd; subst; clear Heqd).
  - pfold. constructor. pclearbot. 
    destruct equiv. eapply obs_equiv_gen_mon.
    eapply SIM. eapply LE.
  - pfold. eapply H.
  - pfold. constructor.
    apply IHobs_equiv_step in Heqd.
    punfold Heqd.
Qed. 

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


Lemma obs_equiv_step_transitive:  forall A R, transitive (Obs A) R -> transitive (Obs A) (obs_equiv_step R).
Proof.
  intros A.
  unfold relation. unfold transitive.
  intros R Ht.
  intros x y z H. generalize dependent z.
  induction H; intros z H1. 
  - remember (Ret a) as w. induction H1; inversion Heqw; eauto.
    subst. apply obs_equiv_step_rgt. exact H1.
  - remember (Fin v) as w. induction H1; inversion Heqw; eauto.
    subst. apply obs_equiv_step_rgt. exact H1.
  - remember (Err s2) as w. induction H1; inversion Heqw; eauto.
  - apply obs_equiv_step_lft. generalize dependent d1. remember (Tau d2) as w.
    induction H1; inversion Heqw; subst; intros d1 HR.
    apply obs_equiv_step_rgt. 
Abort.    
  


Lemma obs_equiv_trans : forall {A} (d1 d2 d3: Obs A), obs_equiv d1 d2 -> obs_equiv d2 d3 -> obs_equiv d1 d3.
Proof.
  intro A. pcofix CIH.
  intros d1 d2 d3 H1 H2.
  pfold.
  punfold H1. remember (upaco2 obs_equiv_step bot2) as R.
  generalize dependent d3.
  induction H1; intros d3 H2.
  - punfold H2. rewrite <- HeqR in H2. remember (Ret a) as d2.
    induction H2; try inversion Heqd2; eauto.
    apply obs_equiv_step_rgt. subst. apply IHobs_equiv_step in H.  exact H.
  - punfold H2. rewrite <- HeqR in H2. remember (Fin v) as d2.
    induction H2; try inversion Heqd2; eauto.
    apply obs_equiv_step_rgt. subst. apply IHobs_equiv_step in H. exact H.
  - punfold H2. rewrite <- HeqR in H2. remember (Err s2) as d2.
    induction H2; try inversion Heqd2; eauto.
  - punfold H2.
    rewrite <- HeqR in H2. remember (Tau d2) as d.
    induction H2; try inversion Heqd; subst; eauto.
    + pclearbot. destruct equiv. destruct equiv0.
    apply obs_equiv_step_tau. right. eapply CIH. pfold.
    eapply obs_equiv_gen_mon. apply SIM. eapply LE.
    pfold. eapply obs_equiv_gen_mon. eapply SIM0. eapply LE0.
    + pclearbot. destruct equiv. 
      apply obs_equiv_step_lft.  eapply obs_equiv_gen_mon.
Abort.
      

(* Note: for guardedness, bind Ret introduces extra Tau *)
Definition bind {A B} (m:Obs A) (f:A -> Obs B) : Obs B :=
  (cofix bindf := fun m => 
     match m with
       | Ret a => Tau (f a)
       | Fin d => Fin d
       | Err s => Err s
       | Tau d' => Tau (bindf d')
       | Eff m => Eff (effects_map bindf m)
     end) m.

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
  intros A B.
  pcofix CIH. intros m f.
  unfold bind.
  pfold. destruct m.
Abort.
  
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



End Effects.