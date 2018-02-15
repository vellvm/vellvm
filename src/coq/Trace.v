(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import  Vellvm.Classes Vellvm.Util.
Require Import Program Classical.
Require Import paco.

Set Implicit Arguments.
Set Contextual Implicit.

(** An [M E X] is the denotation of a program as coinductive (possibly
    infinte) tree where the leaves are labeled with [X] and every node
    is either a [Tau] node with one child, or a branching node [Vis]
    with a visible event [E Y] that branches on the values of [Y]. *)
CoInductive M (Event : Type -> Type) X := 
| Ret (x:X)
| Vis {Y: Type} (e : Event Y) (k : Y -> M Event X)
| Tau (k: M Event X)
| Err (s:String.string)
.
(** Note: One could imagine an alternative definition with an explicit
    Bind constructor (and a Prim constructor), but this might not be
    as nice / might not work at all -- this way makes productivity
    easier to deal with.  (Also, this one can be turned into a real
    monad.)  We should compare at some point. *)

(** N.b. This is related to the Free Monad construction, which is not
    possible with Coq due to the positivity requirement. But when
    the functor that we want to build the Free Monad from is
    representable (or "Naperian", as it is called by Peter Hancock),
    we can use this encoding to avoid the problem.
    Update: that comment would apply only if we had
    [Event : Type -> Type] and [Vis (Event -> M Event X)].
    *)

(** [M] is known as the "Freer monad".
    "Freer Monads, More Extensible Effects",
    Oleg Kiselyov, Hiromi Ishii.
    The [Vis] constructor corresponds to a free functor construction
    also called Co-Yoneda or left Kan extension.
    Note that [Event] is meant to be an indexed type, and generally
    not a functor, but we have a monad in any case. *)

(** The existence of [spin] makes this not quite free:
    amounts more or less to an additional [Event Void]
    constructor.  *)

(** In order to unfold a cofixpoint we have to rewrite it with
    [matchM].  (Is this relevant only in proofs?  Maybe it should be
    defined near the Ltac that uses it.) *)
Definition idM E X (i: M E X) :=
  match i with 
  | Ret x => Ret x
  | Vis e k => Vis e k
  | Tau k => Tau k
  | Err s => Err s
  end.
Lemma matchM : forall E X (i: M E X), i = idM i.
Proof. destruct i; auto. Qed.

(** [M E] forms a [Monad] *)
(* N.b.: Possible variant: remove the Tau in the Ret case.  Not clear
   whether this is a global win (we have to then put some extra Taus
   in programs/specifications, which Joachim finds to be a breach of
   abstraction), but it makes this a monad. *)
Definition bindM {E X Y} (s: M E X) (t: X -> M E Y) : M E Y :=
  let cofix go (s : M E X) := 
      match s with
      | Ret x => Tau (t x)
      | Vis e k => Vis e (fun y => go (k y))
      | Tau k => Tau (go k)
      | Err s => Err s
      end
  in go s.

Definition mapM {E X Y} (f:X -> Y) (s: M E X) : M E Y :=
  let cofix go (s : M E X) :=
      match s with
      | Ret x => Ret (f x)
      | Vis e k => Vis e (fun y => go (k y))
      | Tau k => Tau (go k)
      | Err s => Err s
      end
  in go s.

Instance functor_M {E} : Functor (M E) := (@mapM E).
Instance monad_M {E} : (@Monad (M E)) (@mapM E) := { mret X x := Ret x; mbind := @bindM E }.

Module MonadVerif.

  
(* Monad laws:
   - return x >>= k   =   k x
   - s >>= return   =   w
   - s >>= (\x -> k x >>= h)   =   (s >>= k) >>= h
 *)

(** Get rid of absurd cases such as
    - forall t, Tau t <> Tau s
    - Tau t = Vis e k
 *)
Ltac dispatch_contra :=
  first
    [ let dispatch H tac := solve [exfalso; eapply H; tac] in
      match goal with
      | H : forall t, ?f t <> ?f ?s |- _ => dispatch H auto
      | H : forall t, ?f t <> ?s, _ : ?f ?u = ?s |- _ => dispatch H eauto
      end
    | discriminate
    ].

Inductive UnTau E X : M E X -> M E X -> Prop :=
| OneTau : forall s t, UnTau s t -> UnTau (Tau s) t
| NoTau : forall s, (forall t, ~(Tau t = s)) -> UnTau s s.

CoInductive EquivUpToTau E X :
  M E X -> M E X -> Prop :=
| EquivRet : forall x, EquivUpToTau (Ret x) (Ret x)
| EquivVis : forall Y (e : E Y) (k1 k2 : Y -> M E X),
    (forall y, EquivUpToTau (k1 y) (k2 y)) ->
    EquivUpToTau (Vis e k1) (Vis e k2)
(* Equality with spin is undecidable,
   but one can coinductively generate a proof with this. *)
| EquivTau : forall s t,
    EquivUpToTau s t -> EquivUpToTau (Tau s) (Tau t)
| EquivTauLeft : forall s s' t,
    (forall t', ~(Tau t' = t)) ->
    UnTau s s' ->
    EquivUpToTau s' t ->
    EquivUpToTau (Tau s) t
| EquivTauRight : forall s t t',
    (forall s', ~(Tau s' = s)) ->
    UnTau t t' ->
    EquivUpToTau s t' ->
    EquivUpToTau s (Tau t)
| EquivErr : forall s, EquivUpToTau (Err s) (Err s)
.

Lemma eutt_refl : forall E X (s : M E X),
    EquivUpToTau s s.
Proof.
  cofix.
  intros.
  destruct s; constructor;
    intros;
    apply eutt_refl.
Qed.

Lemma eutt_sym : forall E X (s t : M E X),
    EquivUpToTau s t -> EquivUpToTau t s.
Proof.
  cofix.
  intros.
  destruct H; try constructor.
  - intro y. apply eutt_sym. apply H.
  - apply eutt_sym. apply H.
  - econstructor. assumption. eassumption. apply eutt_sym. assumption.
  - econstructor. assumption. eassumption. apply eutt_sym. assumption.
Qed.

Lemma untau_notau : forall E X (s t : M E X), ~(UnTau s (Tau t)).
Proof.
  intros E X s t H.
  remember (Tau t) as t'.
  induction H.
  - auto.
  - eapply H; eauto.
Qed.

Lemma untau_untau : forall E X (s t : M E X),
    UnTau s t -> UnTau t t.
Proof.
  intros E X s t H.
  induction H.
  - auto.
  - constructor; assumption.
Qed.

Lemma untau_inj : forall E X (s s' s'' : M E X),
    UnTau s s' -> UnTau s s'' -> s' = s''.
Proof.
  intros E X s s' s'' H.
  induction H; intro H'; inversion H'.
  - auto.
  - dispatch_contra.
  - dispatch_contra.
  - reflexivity.
Qed.

Lemma eutt_untau : forall E X (s s' t : M E X),
    UnTau s s' -> EquivUpToTau s t ->
    exists t', UnTau t t' /\ EquivUpToTau s' t'.
Proof.
  intros E X s s' t HUnTau.
  generalize dependent t.
  induction HUnTau as [ s s' HUnTau IH | s HNoTau ]; intros t H.
  - inversion H as [ | | s1 t1 H1 | s1 s1' ? HtNoTau | | ].
    + apply IH in H1; destruct H1 as [t' H1]; destruct H1.
      eexists; split.
      * constructor; eassumption.
      * assumption.
    + eexists; split. constructor.
      * assumption.
      * replace s' with s1'.
        -- assumption.
        -- eapply untau_inj; eassumption.
    + dispatch_contra.
  - inversion H; subst.
    + eexists; split; constructor; assumption.
    + eexists; split; constructor.
      * intros t I. inversion I.
      * assumption.
    + dispatch_contra.
    + dispatch_contra.
    + eexists; split.
      * constructor. eassumption.
      * assumption.
    + eexists; split.
      * constructor. intros. unfold not. intros. inversion H0.
      * assumption.
Qed.

Lemma eutt_tau_2 : forall E X (s s' t t' : M E X),
    UnTau s s' -> UnTau t t' -> EquivUpToTau s' t' ->
    EquivUpToTau s t.
Proof.
  cofix.
  intros E X s s' t t' Hs Ht H.
  destruct Hs, Ht.
  - constructor.
    eapply eutt_tau_2; eassumption.
  - econstructor; eassumption.
  - econstructor; eassumption.
  - destruct H;
      try (constructor; assumption);
      dispatch_contra.
Qed.

Lemma eutt_untau_2 : forall E X (s s' t t' : M E X),
    UnTau s s' -> UnTau t t' -> EquivUpToTau s t ->
    EquivUpToTau s' t'.
Proof.
  intros E X s s' t t' Hs.
  generalize dependent t'.
  generalize dependent t.
  induction Hs as [ s s' | s He ].
  - intros t t' Ht H. inversion H; subst; inversion Ht; subst; try dispatch_contra.
    + eapply IHHs. eassumption. assumption.
    + replace s'0 with s' in *. assumption.
      eapply untau_inj; eassumption.
  - intros t t' Ht H.
    destruct H;
      inversion Ht;
      subst;
      try dispatch_contra.
    + constructor.
    + constructor; assumption.
    + replace t'0 with t' in *.
      * assumption.
      * eapply untau_inj; eassumption.
    + constructor.
Qed.

Lemma eutt_untau_trans : forall E X (s s' t : M E X),
    UnTau s s' -> EquivUpToTau s' t -> EquivUpToTau s t.
Proof.
  cofix.
  intros E X s s' t H I.
  destruct H.
  { inversion I; subst.
    - econstructor.
      + intros t' J; inversion J.
      + eassumption.
      + assumption.
    - econstructor.
      + intros t' J; inversion J.
      + eassumption.
      + assumption.
    - exfalso.
      apply (untau_notau H).
    - econstructor.
      + assumption.
      + eassumption.
      + assumption.
    - constructor.
      eapply eutt_untau_trans.
      + eassumption.
      + eapply eutt_tau_2.
        * eapply untau_untau. eassumption.
        * eassumption.
        * assumption.
    - econstructor.
      + intros t' J; inversion J.
      + eassumption.
      + assumption.
  }
  assumption.
Qed.

Import Logic.ProofIrrelevance.

Lemma vis_inj :
  forall E X Y (e e' : E Y)
         (k : Y -> M E X) (k' : Y -> M E X),
    Vis e k = Vis e' k' -> e = e'.
Proof.
Admitted.

Lemma eutt_trans : forall E X (s t u : M E X),
    EquivUpToTau s t -> EquivUpToTau t u -> EquivUpToTau s u.
Proof.
  cofix.
  intros E X s t u H1 H2.

  destruct H1 as [ | ? e1 ks kt | | | | ];
    inversion H2 as [ | ? e2 kt' ku | | t2 t2' u2 | | ].
  - (* Ret, Ret, Ret *) constructor.
  - (* Ret, Ret, Tau *) econstructor; try eassumption.
  - (* Vis, Vis, Vis *)
    (* induction Hk as [? Hk] using eq_sigT_rect. *) replace e2 with e1.
    + constructor.
      intro y.
      eapply eutt_trans.
      * auto.
      * replace kt with kt'.
        -- auto.
        -- apply inj_pair2 with (P := fun Y => Y -> M E X).
           auto.
    + symmetry. apply inj_pair2 with (P := E). auto.

  - (* Vis, Vis, Tau *) econstructor.
    + intros ? I. inversion I.
    + eassumption.
    + eapply eutt_trans.
      * constructor. eassumption.
      * assumption.

  - (* Tau, Tau, Tau *) econstructor.
    eapply eutt_trans; try eassumption.

  - (* Tau, Tau, ~Tau *)
    assert (I : exists s', UnTau s s' /\ EquivUpToTau t2' s').
    { apply eutt_untau with (s := t) (s' := t2').
      * assumption.
      * apply eutt_sym. assumption. }
    destruct I as [s' [I1 I2]].
    econstructor.
    + assumption.
    + eassumption.
    + eapply eutt_trans.
      * eapply eutt_sym; apply I2.
      * assumption.

  - (* Tau, Tau & ~Tau, Tau *)
    dispatch_contra.

  - (* Tau, Ret, Ret *)
    subst. eapply EquivTauLeft.
    * intros t' I; inversion I.
    * eassumption.
    * assumption.

  - (* Tau, Vis, Vis *)
    subst. eapply EquivTauLeft.
    * intros t' I; inversion I.
    * eassumption.
    * eapply eutt_trans; eassumption.

  - (* Tau, ~Tau & Tau, Tau *)
    dispatch_contra.
  - (* Tau, ~Tau & Tau, ~Tau *)
    dispatch_contra.

  - (* Tau, ~Tau, Tau *)
    constructor.
    eapply eutt_trans.
    + eapply eutt_untau_trans.
      * eassumption.
      * eassumption.
    + eapply eutt_sym.
      eapply eutt_untau_trans. eassumption.
      eapply eutt_sym.
      assumption.

  - subst. eapply EquivTauLeft.
    + intros t' I; inversion I.
    + eassumption.
    + assumption.

      
  - (* ~Tau, Tau, Tau *)
    assert (I : exists u', UnTau u u' /\ EquivUpToTau t' u').
    { eapply eutt_untau. apply OneTau. eassumption. eassumption. }
    destruct I as [u' [I ?]].
    destruct I.
    + econstructor.
      * assumption.
      * inversion H5. eassumption.
      * eapply eutt_trans; eassumption.
    + dispatch_contra.

  - (* ~Tau, Tau, ~Tau *)
    assert (I : t' = t2').
    { eapply untau_inj; eassumption. }
    rewrite <- I in *.
    inversion H1;
      inversion H5;
      subst;
      try assumption;
      try dispatch_contra.
    + inversion H12. subst.
      replace e0 with e.
      replace k0 with k2 in *.
      * constructor.
        intro y.
        eapply eutt_trans; eauto.
      * apply inj_pair2 with (P := fun Y => Y -> M E X); auto.
      * apply inj_pair2 with (P := E); auto.
    + exfalso. eapply untau_notau. eassumption.

  - (* ~Tau, Tau & ~Tau, Tau *)
    dispatch_contra.

  - subst. econstructor.
    + intros u I; inversion I.
    + eassumption.
    + assumption.

  - econstructor.
Qed.

Instance equiv_eutt {E} X : Equiv (M E X) := (@EquivUpToTau E X).

(* SAZ: 
Functoriality of (M E) probably holds only up to coinductively defined
bisimulation of eq.  Or, we should assume as an Aximo that eq coincides
with that bisimulation.
*)
Instance M_functor_eutt_laws {E} : (@FunctorLaws (M E)) (@mapM E) (@equiv_eutt E).
Proof.
Admitted.  

Program Instance M_monad_eutt_laws {E} : (@MonadLaws (M E)) (@functor_M E) (@monad_M E) _ _ _.
Next Obligation.
  Admitted.
Next Obligation.
  Admitted.
Next Obligation.
  Admitted.


End MonadVerif.

