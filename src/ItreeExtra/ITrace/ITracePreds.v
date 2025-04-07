From Coq Require Import
     Morphisms
.

From ITree Require Import
     Axioms
     ITree
     ITreeFacts.

From ITree.Extra Require Import
     ITrace.ITraceDefinition
     ITrace.ITraceFacts
     ITrace.ITraceBind
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

(* Defines some useful predicates over ITraces *)

Variant trace_forallF {E : Type -> Type} {R : Type} (F : itrace E R -> Prop)
        (PE : forall A, EvAns E A -> Prop) (PR : R -> Prop) : itrace' E R -> Prop :=
  | trace_forall_ret (r : R) : PR r -> trace_forallF F PE PR (RetF r)
  | trace_forall_tau (b : itrace E R) : F b -> trace_forallF F PE PR (TauF b)
  | trace_forall_vis {A : Type} (e : EvAns E A) (k : A -> itrace E R) :
    PE A e -> (forall (a :A), F (k a) ) -> trace_forallF F PE PR (VisF e k)
.

#[global] Hint Constructors trace_forallF : itree.

Definition trace_forall_ {E R} PE PR F (b : itrace E R) :=
  trace_forallF F PE PR (observe b).

Lemma trace_forall_monot {E R} PE PR : monotone1 (@trace_forall_ E R PE PR).
Proof.
  repeat intro. red in IN. red. induction IN; auto with itree.
Qed.

#[global] Hint Resolve trace_forall_monot : paco.

Definition trace_forall {E R} PE PR := paco1 (@trace_forall_ E R PE PR) bot1.

Lemma trace_forall_proper_aux: forall (E : Type -> Type) (R : Type) (PE : forall A : Type, EvAns E A -> Prop)
                                 (PR : R -> Prop) (b1 b2 : itree (EvAns E) R),
    (b1 ≈ b2) -> trace_forall PE PR b1 -> trace_forall PE PR b2.
Proof.
  intros E R PE PR. pcofix CIH. intros b1 b2 Heutt Hforall.
  pfold. red. punfold Hforall. red in Hforall.
  punfold Heutt. red in Heutt. induction Heutt; subst; auto.
  - inv Hforall. auto with itree.
  - inv Hforall. pclearbot. constructor. right. eapply CIH; eauto.
  - inv Hforall. ddestruction. subst. pclearbot.
    constructor; auto. intros. right. eapply CIH; eauto with itree. apply H3.
  - apply IHHeutt. inv Hforall. pclearbot. punfold H0.
  - constructor. left. pfold. red. apply IHHeutt. auto.
Qed.

#[global] Instance trace_forall_proper_eutt {E R PE PR} : Proper (eutt eq ==> iff) (@trace_forall E R PE PR).
Proof.
  intros b1 b2 Heutt. split; intros.
  - eapply trace_forall_proper_aux; eauto.
  - symmetry in Heutt. eapply trace_forall_proper_aux; eauto.
Qed.

Lemma forall_spin : forall E R PE PR, trace_forall PE PR (@ITree.spin (EvAns E) R).
Proof.
  intros. pcofix CIH. pfold. red. cbn. constructor.
  right. auto.
Qed.

Inductive trace_inf_oftenF {E : Type -> Type} {R : Type} (PE : forall A, EvAns E A -> Prop)
          (F : itrace E R -> Prop) : itrace' E R -> Prop :=
| trace_inf_often_tau (b : itrace E R) : trace_inf_oftenF PE F (observe b) ->
                                         trace_inf_oftenF PE F (TauF b)
| trace_inf_often_vis_neg (e : EvAns E unit) (k : unit -> itrace E R) :
  trace_inf_oftenF PE F (observe (k tt)) -> trace_inf_oftenF PE F (VisF e k)
| trace_inf_often_vis_pos (e : EvAns E unit) (k : unit -> itrace E R) :
  F (k tt) -> PE unit e -> trace_inf_oftenF PE F (VisF e k)
.

#[global] Hint Constructors trace_inf_oftenF : itree.

Definition trace_inf_often_ {E R} PE F (b : itrace E R) :=
  trace_inf_oftenF PE F (observe b).

Lemma trace_inf_often_monot {E R} PE : monotone1 (@trace_inf_often_ E R PE).
Proof.
  repeat intro. red in IN. red. induction IN; auto with itree.
Qed.

#[global] Hint Resolve trace_inf_often_monot : paco.

Definition trace_inf_often {E R} PE := paco1 (@trace_inf_often_ E R PE) bot1.

Inductive front_and_last {E : Type -> Type} {R : Type} (PEF : forall A, EvAns E A -> Prop)
          (PEL : forall A, EvAns E A -> Prop) (PR : R -> Prop) : itrace E R -> Prop :=
| front_and_last_base (e : EvAns E unit) (r : R) (b : itree (EvAns E) R) :
  b ≈ Vis e (fun u => Ret r) -> PEL unit e -> PR r -> front_and_last PEF PEL PR b
| front_and_last_cons (e : EvAns E unit) (k : unit -> itrace E R) (b : itree (EvAns E) R ) :
  b ≈ Vis e k -> PEF unit e -> front_and_last PEF PEL PR (k tt) -> front_and_last PEF PEL PR b

.

Lemma fal_proper_aux: forall (E : Type -> Type) (R : Type) (PEF PEL : forall A : Type, EvAns E A -> Prop)
                        (PR : R -> Prop) (b1 b2 : itree (EvAns E) R),
    (b1 ≈ b2) -> front_and_last PEF PEL PR b1 -> front_and_last PEF PEL PR b2.
Proof.
  intros E R PEF PEL PR b1 b2 Heutt Hfal.
  generalize dependent b2. induction Hfal; intros.
  - eapply front_and_last_base; eauto.
    rewrite <- Heutt. auto.
  - eapply front_and_last_cons; eauto. rewrite <- Heutt. auto.
Qed.

#[global] Instance front_and_last_proper_eutt {E R PEF PEL PR} :
  Proper (eutt eq ==> iff) (@front_and_last E R PEF PEL PR).
Proof.
  intros b1 b2 Heutt. split; intros.
  - eapply fal_proper_aux; eauto.
  - symmetry in Heutt. eapply fal_proper_aux; eauto.
Qed.

Section StateMachine.
  (*Note that this state machine definition is not able to deal with empty event parameter types*)
  (*Nor can it encode predicates that can accept silent divergence under certain conditions *)
  (*Pretty sure it could be extended to handle that,but that is a job for another day*)
  Context {E : Type -> Type}.
  Context {R : Type}.
  Context (EvTrans : forall A, E A -> A -> forall B, E B -> B -> Prop).
  Context (RetTrans : forall A, E A -> A -> R -> Prop).

  Inductive state_machineF (PEv : forall A, E A -> A -> Prop) (PRet : R -> Prop)
            (F : (forall A, E A -> A -> Prop) -> (R -> Prop) -> itrace E R -> Prop) : itrace' E R -> Prop :=
  | smRet r : PRet r -> state_machineF PEv PRet F (RetF r)
  | smTau t : state_machineF PEv PRet F (observe t) -> state_machineF PEv PRet F (TauF t)
  | smVis A (e : E A) (a : A) (k : unit -> itrace E R) :
    PEv A e a -> F (EvTrans A e a) (RetTrans A e a) (k tt) -> state_machineF PEv PRet F (VisF (evans A e a) k)
  .

  Hint Constructors state_machineF : itree.

  Definition state_machine_ F PEv PRet (tr : itrace E R) :=
    state_machineF PEv PRet F (observe tr).

  Lemma monotone_state_machine : monotone3 state_machine_.
  Proof.
    red. intros. red. red in IN. induction IN; auto with itree.
  Qed.
  Hint Resolve trace_inf_often_monot : paco.
  Definition state_machine PEv PRet (tr : itrace E R) :  Prop := paco3 (state_machine_) bot3 PEv PRet tr.

  Lemma state_machine_proper_aux : forall PEv PRet (t1 t2 : itrace E R),
      (t1 ≈ t2) -> state_machine PEv PRet t1 -> state_machine PEv PRet t2.
  Proof.
    pcofix CIH. intros PEV PREt t1 t2 Heutt Hsm. pfold. red.
    punfold Hsm; try apply monotone_state_machine.
    punfold Heutt. red in Heutt. red in Hsm.
    induction Hsm.
    - remember (RetF r0) as ot1. induction Heutt; subst; auto with itree; try discriminate.
      injection Heqot1; intros; subst; auto with itree.
    - apply IHHsm. pstep_reverse. assert (Tau t ≈ t2); auto with itree.
      rewrite tau_eutt in H. auto.
    - remember (VisF (evans A e a) k ) as ot1. induction Heutt; subst; auto with itree; try discriminate.
      injection Heqot1; intros; subst. dependent destruction H1.
      subst. constructor; auto. right. pclearbot. eapply CIH; eauto with itree.
  Qed.

  #[global] Instance state_machine_proper_eutt {PEv PRet} : Proper (eutt eq ==> iff) (@state_machine PEv PRet).
  Proof.
    intros t1 t2 Heutt. split; intros; try eapply state_machine_proper_aux; eauto; symmetry; auto.
  Qed.

End StateMachine.
