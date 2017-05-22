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
| Call   (v:value) (k:value -> d)
.    

Definition effects_map {A B} (f:A -> B) (m:effects A) : effects B :=
  match m with
  | Alloca t g => Alloca t (fun a => f (g a))
  | Load a g  => Load a (fun dv => f (g dv))
  | Store a dv d => Store a dv (f d)
  | Call a d => Call a (fun dv => f (d dv))
  end.

Instance effects_functor : Functor effects := fun A => fun B => @effects_map A B.
Program Instance effects_functor_eq_laws : (@FunctorLaws effects) effects_functor (@eq).
Next Obligation.
  unfold fmap. unfold effects_functor. unfold effects_map. destruct a; reflexivity.
Defined.
Next Obligation.
  unfold fmap. unfold effects_functor. unfold effects_map. destruct a; reflexivity.
Defined.  

(* Domain of semantics *)
CoInductive D X :=
| Ret : X -> D X        (* Unfinished trace *)
| Fin : value -> D X    (* Finished trace *) 
| Err : string -> D X   (* Abort with an error *)
| Tau : D X -> D X      (* Internal step of computation *)
| Eff : effects (D X) -> D X    (* Externally visible step of computation *)
.

CoFixpoint d_map {A B} (f:A -> B) (d:D A) : D B :=
  match d with
    | Ret a => Ret (f a)
    | Fin d => Fin d
    | Err s => Err s
    | Tau d' => Tau (d_map f d')
    | Eff m => Eff (effects_map (d_map f) m)
  end.

Section UNFOLDING.

Definition id_match_d {A} (d:D A) : D A :=
  match d with
    | Ret a => Ret a
    | Fin d => Fin d
    | Err s => Err s
    | Tau d' => Tau d'
    | Eff m => Eff m
  end.

Lemma id_d_eq : forall A (d:D A),
  d = id_match_d d.
Proof.
  destruct d; auto.
Qed.

End UNFOLDING.

Arguments id_d_eq {_} _ .


(* Error predicate, which says whether an observation trace leads to an error allong *)
Inductive d_error_free_mem_step {A} (R: D A -> Prop) : effects (D A) -> Prop :=
| d_error_free_mem_Alloca : forall t f, (forall (a:addr), R (f (inj_addr a))) -> d_error_free_mem_step R (Alloca t f)
| d_error_free_mem_Load   : forall a f, (forall (dv:value), R (f dv)) -> d_error_free_mem_step R (Load a f)
| d_error_free_mem_Store  : forall a n d, R d -> d_error_free_mem_step R (Store a n d)
| d_error_free_mem_Call   : forall v f, (forall (dv:value), R (f dv)) -> d_error_free_mem_step R (Call v f)
.                                                                                

(* No cases for Ret or Err --
   Ret means an "unfinished" computation (and shouldn't arise in the semantics of a CFG program)
   Err definitely has an error, which this predicate rules out
*)
Inductive d_error_free_step {A} (R: D A -> Prop) : D A -> Prop :=
| d_error_free_step_fin : forall v, d_error_free_step R (Fin v)
| d_error_free_step_tau : forall d, R d -> d_error_free_step R (Tau d)
| d_error_free_step_eff : forall m, d_error_free_mem_step R m -> d_error_free_step R (Eff m)
.                                                                             
Hint Constructors d_error_free_mem_step d_error_free_step.

Definition d_error_free {A} := paco1 (@d_error_free_step A) bot1.
Hint Unfold d_error_free.

Lemma d_error_free_gen_mon {A} : monotone1 (@d_error_free_step A).
Proof.
  unfold monotone1. intros.
  induction IN; eauto.
  eapply d_error_free_step_eff.
  induction H; constructor; auto.
Qed.
Hint Resolve d_error_free_gen_mon : paco.

(*
  This relation doesn't allow any variation in the relations for the memory model.  A more parametric version would:
    - have an address relation  A : addr -> addr -> Prop  
    - have a value relation  V : value -> value -> Prop
*)
Inductive d_equiv_mem_step {A} (R: D A -> D A -> Prop) : effects (D A) -> effects (D A) -> Prop :=
| d_equiv_mem_Alloca : forall t f g, (forall (a:addr), R (f (inj_addr a)) (g (inj_addr a))) -> d_equiv_mem_step R (Alloca t f) (Alloca t g)
| d_equiv_mem_Load  : forall a f g, (forall (dv:value), R (f dv) (g dv)) -> d_equiv_mem_step R (Load a f) (Load a g)
| d_equiv_mem_Store : forall a n d1 d2, (R d1 d2) -> d_equiv_mem_step R (Store a n d1) (Store a n d2)
| d_equiv_mem_Call  : forall v f g, (forall (dv:value), R (f dv) (g dv)) -> d_equiv_mem_step R (Call v f) (Call v g)
.    

Inductive d_equiv_step {A} (R:D A -> D A -> Prop) : D A -> D A -> Prop :=
| d_equiv_step_ret : forall a, d_equiv_step R (Ret a) (Ret a)
| d_equiv_step_fin : forall v, d_equiv_step R (Fin v) (Fin v)
| d_equiv_step_err : forall s1 s2, d_equiv_step R (Err s1) (Err s2)
| d_equiv_step_tau : forall d1 d2, R d1 d2 -> d_equiv_step R (Tau d1) (Tau d2)
| d_equiv_step_lft : forall d1 d2, d_equiv_step R d1 d2 -> d_equiv_step R (Tau d1) d2
| d_equiv_step_rgt : forall d1 d2, d_equiv_step R d1 d2 -> d_equiv_step R d1 (Tau d2)
| d_equiv_step_eff : forall m1 m2, d_equiv_mem_step R m1 m2 -> d_equiv_step R (Eff m1) (Eff m2)
.    

Hint Constructors d_equiv_mem_step d_equiv_step.  (* d_equiv *)

Lemma d_equiv_gen_mon A : monotone2 (@d_equiv_step A).
Proof.
  unfold monotone2. intros. induction IN; eauto.
  eapply d_equiv_step_eff. induction H.
  - constructor. eauto.
  - constructor. eauto.
  - constructor. eauto.
  - constructor. eauto.
Qed.
Hint Resolve d_equiv_gen_mon : paco.

Definition d_equiv {A} (p q : D A) := paco2 (@d_equiv_step A) bot2 p q.
Hint Unfold d_equiv.


Inductive d_equiv_step' {A} (R:D A -> D A -> Prop) : D A -> D A -> Prop :=
| d_equiv_step'_ret : forall a, d_equiv_step' R (Ret a) (Ret a)
| d_equiv_step'_fin : forall v, d_equiv_step' R (Fin v) (Fin v)
| d_equiv_step'_err : forall s1 s2, d_equiv_step' R (Err s1) (Err s2)
| d_equiv_step'_tau : forall d1 d2, R d1 d2 -> d_equiv_step' R (Tau d1) (Tau d2)
| d_equiv_step'_lft : forall d1 d2, R d1 d2 -> d_equiv_step' R (Tau d1) d2
| d_equiv_step'_rgt : forall d1 d2, R d1 d2 -> d_equiv_step' R d1 (Tau d2)
| d_equiv_step'_eff : forall m1 m2, d_equiv_mem_step R m1 m2 -> d_equiv_step' R (Eff m1) (Eff m2)
.    

Hint Constructors d_equiv_step'.
Lemma d_equiv_gen_mon' A : monotone2 (@d_equiv_step' A).
Proof.
  unfold monotone2. intros. induction IN; eauto.
  eapply d_equiv_step'_eff. induction H.
  - constructor. eauto.
  - constructor. eauto.
  - constructor. eauto.
  - constructor. eauto.
Qed.
Hint Resolve d_equiv_gen_mon' : paco.

Definition d_equiv' {A} (p q : D A) := paco2 (@d_equiv_step' A) bot2 p q.
Hint Unfold d_equiv'.

Lemma d_equivalent : forall A (p q : D A), d_equiv p q -> d_equiv' p q.
Proof.
  intros A. 
  pcofix CIH. intros p q H.
  pfold.
  punfold H. remember (upaco2 d_equiv_step bot2).
  induction H; subst; eauto.
  - apply d_equiv_step'_tau. right. apply CIH. inversion H. apply H0. inversion H0.
  - apply d_equiv_step'_eff. remember (upaco2 d_equiv_step bot2).
    induction H.
    + constructor. intros. right. apply CIH. subst. specialize (H a). destruct H. exact H. inversion H.
    + constructor. intros. right. apply CIH. subst. specialize (H dv). destruct H. exact H. inversion H.
    + constructor. intros. right. apply CIH. subst. destruct H. exact H. inversion H.      
    + constructor. intros. right. apply CIH. subst. specialize (H dv). destruct H. exact H. inversion H.      
Qed.

Fixpoint taus {A} (n:nat) (d:D A) : D A :=
  match n with
  | 0 => d
  | S n => Tau (taus n d)
  end.

Lemma d_equivalent' : forall A (p q : D A), d_equiv' p q -> d_equiv p q.
Proof.
  intros A.
  pcofix CIH. intros p q H.
  pfold.  
  punfold H. simpl. remember (upaco2 d_equiv_step' bot2).
  destruct H; subst; eauto.
  + constructor. right. apply CIH. destruct H. exact H. inversion H.
  + constructor. destruct H. destruct H. destruct SIM; subst; eauto.
      * constructor. apply LE in H. right. apply CIH. destruct H. exact H. inversion H.
      * constructor. apply LE in H. destruct H. apply CIH in H. 
    

    
        


























































































      


Instance D_functor : @Functor D := fun A => fun B => @d_map A B.



(* Probably a functor only up to stuttering equivalence. *)
(*
Program Instance D_functor_eq_laws : (@FunctorLaws D) D_functor (@eq).
*)
Lemma d_equiv_refl : forall {A} (d : D A), d_equiv d d.
Proof.
  intro. pcofix CIH.
  intros. pfold. destruct d; eauto.
  destruct e; eauto. 
Qed.

Lemma d_equiv_symm : forall {A} (d1 d2 : D A), d_equiv d1 d2 -> d_equiv d2 d1.
Proof.
  intro. pcofix CIH.
  intros d1 d2 H.
  punfold H. remember (upaco2 d_equiv_step bot2).
  induction H; eauto; subst.
  - pfold. constructor. right. eapply CIH.
    destruct H; eauto. inversion H. 
  - pfold. constructor. punfold IHd_equiv_step.
  - pfold. constructor. punfold IHd_equiv_step.
  - pfold. constructor. inversion H; subst.
    + constructor. intro. specialize (H0 a). destruct H0.
      right. eapply CIH. eapply H0. inversion H0.
    + constructor. intro. specialize (H0 dv). destruct H0.
      right. eapply CIH. eapply H0. inversion H0.
    + constructor. right. eapply CIH. destruct H0; eauto. inversion H0. 
    + constructor. intro. specialize (H0 dv). destruct H0.
      right. eapply CIH. eapply H0. inversion H0.
Qed.

(* Note: for guardedness, bind Ret introduces extra Tau *)
Definition bind {A B} (f:A -> D B) : D A -> D B :=
  (cofix bindf := fun m => 
     match m with
       | Ret a => Tau (f a)
       | Fin d => Fin d
       | Err s => Err s
       | Tau d' => Tau (bindf d')
       | Eff m => Eff (effects_map bindf m)
     end).

Lemma bind_unfold : forall {A B} (m:D A) (f:A -> D B),
    d_equiv (bind f m)
    (match m with
    | Ret a => Tau (f a)
    | Fin d => Fin d
    | Err s => Err s
    | Tau d' => Tau (bind f d')
    | Eff e => Eff (effects_map (bind f) e)
    end).
Proof.
  intros A B.
  pcofix CIH. intros m f.
  pfold. rewrite (id_d_eq (bind f m)). simpl.
  destruct m; simpl; auto. apply d_equiv_step_tau. right.
  
  
  

Program Instance D_monad : (@Monad D) (@D_functor) := _.
Next Obligation.
  split.
  - intros. apply Ret. exact X.
  - intros A B. apply bind.
Defined.


Ltac punfold' H := let x := fresh "_x_" in
  repeat red in H;
  let G := type of H in paco_class G (@pacounfold);
  intro x; match goal with [x:=?lem|-_] => clear x; eapply lem in H end.


Section D_EQUIV_COIND.

  Variable A : Type.
  Variable R : D A -> D A -> Prop.

  Variables (p:D A) (q:D A).
  Hypothesis Hrpq : R p q.
  Hypothesis H : forall d1 d2,
    R d1 d2 -> d_equiv_step R d1 d2.
  
  Theorem d_equiv_coind :
    d_equiv p q.
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

End D_EQUIV_COIND.
Arguments d_equiv_coind [_] _ [_ _] _ _.


Lemma stutter_helper : forall {A} (d1 d2 : D A), d_equiv (Tau d1) d2 -> d_equiv d1 d2.
Proof.
  intros. punfold H. remember (Tau d1). induction H; try (solve [inversion Heqd]).
  - inversion Heqd; subst. pfold. constructor. unfold upaco2 in H.
    destruct H; inversion H. eapply d_equiv_gen_mon.
    eapply SIM. eapply LE.
  - inversion Heqd; subst. pfold. eapply H.
  - inversion Heqd; subst. pfold. constructor.
    eapply IHd_equiv_step in H0. punfold H0.
Qed. 

Lemma stutter_simpl : forall {A} (d1 d2 : D A) n, d_equiv (taus n d1) d2 -> d_equiv d1 d2.
Proof.
  intros. induction n. punfold H.
  eapply IHn. simpl in H. eapply stutter_helper. eapply H.
Qed.


Lemma stutter : forall {A} (d1 d2 : D A) n m, d_equiv (taus n d1) (taus m d2) -> d_equiv d1 d2.
Proof.
  intros.
  eapply stutter_simpl.
  eapply d_equiv_symm.
  eapply stutter_simpl.
  eapply d_equiv_symm.
  eauto.
Qed.

End Effects.