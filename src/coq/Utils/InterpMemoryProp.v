(* begin hide *)
From ITree Require Import
     ITree
     ITreeFacts
     Basics.HeterogeneousRelations
     Events.State
     Events.StateFacts
     InterpFacts
     KTreeFacts
     Core.ITreeMonad
     CategoryKleisli
     CategoryKleisliFacts
     Eq.Eq.

From ExtLib Require Import
     Structures.Functor.

From Coq Require Import
     RelationClasses
     Strings.String
     Logic
     Morphisms
     Relations
     List
     Program.Tactics Program.Equality.
From ITree Require Import
     Basics.Monad
     Eq.EqAxiom.

From Vellvm Require Import
     Utils.PropT.
Require Import Paco.paco.

Import ListNotations.
Import ITree.Basics.Basics.Monads.

Import MonadNotation.
Import CatNotations.
Local Open Scope monad_scope.
Local Open Scope cat_scope.
(* end hide *)

#[global] Instance void1_unit {E} : void1 -< E.
  repeat intro; contradiction.
Qed.

Section interp_memory_prop.

  Context {S1 S2 : Type} {E F : Type -> Type}.

  Notation interp_memory_h_spec := (forall T, E T -> stateT S1 (stateT S2 (PropT F)) T).
  Notation stateful R := (S2 * (S1 * R))%type.

  Context (h_spec : interp_memory_h_spec) {R1 R2 : Type} (RR : stateful R1 -> stateful R2 -> Prop).

  Inductive interp_memory_PropTF
            (b1 b2 : bool) (sim : itree E (stateful R1) -> itree F (stateful R2) -> Prop)
            : itree' E (stateful R1) -> itree' F (stateful R2) -> Prop :=
  | Interp_Memory_PropT_Ret : forall (r1 : stateful R1) (r2 : stateful R2) (REL: RR r1 r2),
      interp_memory_PropTF b1 b2 sim (RetF r1) (RetF r2)

  | Interp_Memory_PropT_Tau : forall t1 t2 (HS: sim t1 t2),
      interp_memory_PropTF b1 b2 sim (TauF t1) (TauF t2)

  | Interp_Memory_PropT_TauL : forall t1 t2
                          (CHECK: is_true b1)
                          (HS: interp_memory_PropTF b1 b2 sim (observe t1) t2),
      interp_memory_PropTF b1 b2 sim (TauF t1) t2

  | Interp_Memory_PropT_TauR : forall t1 t2
                          (CHECK: is_true b2)
                          (HS: interp_memory_PropTF b1 b2 sim t1 (observe t2)),
      interp_memory_PropTF b1 b2 sim t1 (TauF t2)

  | Interp_Memory_PropT_Vis : forall A (e : E A)
                         (ta : itree F (stateful A))
                         t2 s1 s2
                         (k1 : A -> itree E (stateful R1))
                         (k2 : stateful A -> itree F (stateful R2))
                         (HK : forall a b, Returns a (trigger e) ->
                                    Returns b ta ->
                                    sim (k1 a) (k2 b)),
        h_spec _ e s1 s2 ta ->
        t2 ≈ ta >>= k2 ->
        interp_memory_PropTF b1 b2 sim (VisF e k1) (observe t2).

  Hint Constructors interp_memory_PropTF : core.

  Lemma interp_memory_PropTF_mono b1 b2 x0 x1 sim sim'
        (IN: interp_memory_PropTF b1 b2 sim x0 x1)
        (LE: sim <2= sim'):
    interp_memory_PropTF b1 b2 sim' x0 x1.
  Proof.
    intros. induction IN; eauto.
  Qed.

  Hint Resolve interp_memory_PropTF_mono : paco.

  Definition interp_memory_PropT_ b1 b2 sim t0 t1 :=
    interp_memory_PropTF b1 b2 sim (observe t0) (observe t1).
  Hint Unfold interp_memory_PropT_ : core.

  Lemma interp_memory_PropT__mono b1 b2 : monotone2 (interp_memory_PropT_ b1 b2).
  Proof.
    do 2 red. intros. eapply interp_memory_PropTF_mono; eauto.
  Qed.
  Hint Resolve interp_memory_PropT__mono : paco.

  Lemma interp_memory_PropT_idclo_mono: monotone2 (@id (itree E R1 -> itree F R2 -> Prop)).
  Proof. unfold id. eauto. Qed.
  Hint Resolve interp_memory_PropT_idclo_mono : paco.

  Definition interp_memory_prop' b1 b2 :=
    paco2 (interp_memory_PropT_ b1 b2) bot2.

  Definition interp_memory_prop :=
    interp_memory_prop' true true.

  #[global] Instance interp_memory_prop_eq_itree_Proper_impl :
    Proper (eq_itree eq ==> eq_itree eq ==> impl) interp_memory_prop.
  Proof.
    repeat intro.
    repeat intro. eapply bisimulation_is_eq in H, H0; subst; eauto.
  Qed.

  #[global] Instance interp_memory_prop_eq_itree_Proper :
    Proper (eq_itree eq ==> eq_itree eq ==> iff) interp_memory_prop.
  Proof.
    split; intros; [rewrite <- H, <- H0 | rewrite H, H0]; auto.
  Qed.

  #[global] Instance interp_memory_prop_eq_itree_Proper_flip_impl :
    Proper (eq_itree eq ==> eq_itree eq ==> flip impl) interp_memory_prop.
  Proof.
    pose proof interp_memory_prop_eq_itree_Proper as PROP.
    unfold Proper, respectful in *.
    intros x y H x0 y0 H0.
    do 2 red. intros INTERP.
    eapply PROP; eauto.
  Qed.

End interp_memory_prop.
