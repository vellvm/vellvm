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
    infinite) tree where the leaves are labeled with [X] and every node
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

(* Properties of Traces ----------------------------------------------------- *)

Inductive equiv_step {E X} (equiv: M E X -> M E X -> Prop) :  M E X -> M E X -> Prop :=
| equiv_Ret : forall x, equiv_step equiv (Ret x) (Ret x)
| equiv_Vis : forall {Y} e k1 k2, (forall (v:Y), equiv (k1 v) (k2 v))
                             -> equiv_step equiv (Vis e k1) (Vis e k2)
| equiv_Tau : forall k1 k2, equiv k1 k2 -> equiv_step equiv (Tau k1) (Tau k2)
| equiv_Err : forall s1 s2, equiv_step equiv (Err s1) (Err s2)
.
Hint Constructors equiv_step.

Lemma equiv_step_mono {E X} : monotone2 (@equiv_step E X).
Proof.
  unfold monotone2. intros x0 x1 r r' IN LE. 
  induction IN; eauto.
Qed.
Hint Resolve equiv_step_mono : paco.

Definition equiv {E X} (s t : M E X) := paco2 equiv_step bot2 s t .
Hint Unfold equiv.


(* Properties of Traces ----------------------------------------------------- *)

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


Inductive eutt_step E X (eutt : M E X -> M E X -> Prop) : M E X -> M E X -> Prop :=
| EquivRet : forall x, eutt_step eutt (Ret x) (Ret x)
| EquivVis : forall Y (e : E Y) (k1 k2 : Y -> M E X),
    (forall y, eutt (k1 y) (k2 y)) ->
    eutt_step eutt (Vis e k1) (Vis e k2)
(* Equality with spin is undecidable,
   but one can coinductively generate a proof with this. *)
| EquivTau : forall s t,
    eutt s t -> eutt_step eutt (Tau s) (Tau t)
| EquivTauLeft : forall s s' t,
    (forall t', ~(Tau t' = t)) ->
    UnTau s s' ->
    eutt s' t ->
    eutt_step eutt (Tau s) t
| EquivTauRight : forall s t t',
    (forall s', ~(Tau s' = s)) ->
    UnTau t t' ->
    eutt s t' ->
    eutt_step eutt s (Tau t)
| EquivErr : forall s1 s2, eutt_step eutt (Err s1) (Err s2)
.
Hint Constructors eutt_step.

Lemma eutt_step_mono {E X} : monotone2 (@eutt_step E X).
Proof.
  unfold monotone2. intros x0 x1 r r' IN LE. 
  induction IN; eauto.
Qed.
Hint Resolve eutt_step_mono : paco.

Definition EquivUpToTau {E X} (s t : M E X) := paco2 (@eutt_step E X) bot2 s t .
Hint Unfold EquivUpToTau.


Lemma eutt_refl : forall E X (s : M E X),
    EquivUpToTau s s.
Proof.
  intros E X.
  pcofix eutt_refl.
  intros.
  pfold.
  destruct s; auto.
Qed.

Lemma eutt_sym : forall E X (s t : M E X),
    EquivUpToTau s t -> EquivUpToTau t s.
Proof.
  intros E X.
  pcofix eutt_sym.
  intros s t H0. 
  punfold H0. pfold.
  dependent induction H0; auto.
  - econstructor.
    intros y.
    assert (upaco2 (eutt_step (X:=X)) bot2 (k1 y) (k2 y)). apply H.
    right. apply eutt_sym. pfold. destruct H0. punfold H0. inversion H0.
  - econstructor. right. apply eutt_sym. pfold. destruct H. punfold H. inversion H.
  - econstructor. assumption. eassumption. right. apply eutt_sym. destruct H1. punfold H1. inversion H1.
  - econstructor. assumption. eassumption. right. apply eutt_sym. destruct H1. punfold H1. inversion H1.
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
  - punfold H. inversion H as [ | | s1 t1 H1 | s1 s1' ? HtNoTau | | ]; pclearbot.
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
  - punfold H. inversion H; pclearbot; subst.
    + eexists; split. constructor. assumption. pfold. constructor.
    + eexists; split. constructor. 
      * intros t I. inversion I.
      * pfold. assumption.
    + dispatch_contra.
    + dispatch_contra.
    + eexists; split.
      * constructor. eassumption.
      * assumption.
    + eexists; split.
      * constructor. intros. unfold not. intros. inversion H0.
      * pfold. assumption.
Qed.

Ltac eutt_mono :=
  repeat
    match goal with
    | [ H : EquivUpToTau ?T1 ?T2, r : M ?E ?X -> M ?E ?X -> Prop |- upaco2 _ ?r ?T1 ?T2] =>
      left
    | [ H : EquivUpToTau ?T1 ?T2, r : M ?E ?X -> M ?E ?X -> Prop |- paco2 _ ?r ?T1 ?T2] =>
      pfold
    | [ H : EquivUpToTau ?T1 ?T2, r : M ?E ?X -> M ?E ?X -> Prop |- eutt_step _ ?T1 ?T2] =>
      punfold H
    | [ H : eutt_step (upaco2 _ bot2) ?T1 ?T2, r : M ?E ?X -> M ?E ?X -> Prop |- eutt_step _ ?T1 ?T2] =>
      eapply eutt_step_mono; [eauto | intros]
    | [ PR : upaco2 ?R bot2 ?X0 ?X1 |- _ ] => pclearbot
    | [ PR : paco2 ?R bot2 ?X0 ?X1 |- upaco2 ?R ?r ?X0 ?X1 ] => left; eapply paco2_mon; eauto; intros; contradiction
    | [ PR : paco2 ?R bot2 ?X0 ?X1 |- paco2 ?R ?r ?X0 ?X1 ] => eapply paco2_mon; eauto; intros; contradiction
    | [ PR : paco2 ?R bot2 ?X0 ?X1 |- EquivUpToTau ?X0 ?X1 ] => eapply paco2_mon; eauto; intros; contradiction
    end.


Lemma eutt_tau_2 : forall E X (s s' t t' : M E X),
    UnTau s s' -> UnTau t t' -> EquivUpToTau s' t' ->
    EquivUpToTau s t.
Proof.
  intros E X.
  pcofix eutt_tau_2.
  intros s s' t t' Hs Ht H.
  destruct Hs, Ht; pfold.
  - constructor. right. eauto.
  - econstructor. eassumption. eassumption. eutt_mono.
  - econstructor. eassumption. eassumption. eutt_mono.
  - eutt_mono. 
Qed.    

Lemma eutt_untau_2 : forall E X (s s' t t' : M E X),
    UnTau s s' -> UnTau t t' -> EquivUpToTau s t ->
    EquivUpToTau s' t'.
Proof.
  intros E X s s' t t' Hs.
  generalize dependent t'.
  generalize dependent t.
  induction Hs as [ s s' | s He ].
  - intros t t' Ht H.
    inversion Ht; subst; punfold H; inversion H; subst; try dispatch_contra.
    + eapply IHHs. eassumption. eutt_mono.
    + replace s'0 with s' in *. eutt_mono. 
      eapply untau_inj; eassumption.
  - intros t t' Ht H.
    inversion Ht; subst; punfold H; inversion H; subst; try dispatch_contra.
    + replace t'0 with t' in *.
      * eutt_mono.
      * eapply untau_inj; eassumption.
Qed.

Lemma eutt_untau_trans : forall E X (s s' t : M E X),
    UnTau s s' -> EquivUpToTau s' t -> EquivUpToTau s t.
Proof.
  intros E X.
  pcofix eutt_untau_trans.
  intros s s' t H I.
  destruct H.
  * pfold. punfold I; inversion I; subst.
  - econstructor; eauto. 
  - econstructor; eauto. left. pfold.  eutt_mono.
  - exfalso. apply (untau_notau H).
  - econstructor; eauto. left. pfold. eutt_mono.
  - constructor. right. eapply eutt_untau_trans.
    + eassumption.
    + eapply eutt_tau_2.
      -- eapply untau_untau. eassumption.
      -- eassumption.
      -- eutt_mono.
  - econstructor; eauto.
  * eutt_mono.
Qed.      

Lemma vis_inj :
  forall E X Y (e e' : E Y)
         (k : Y -> M E X) (k' : Y -> M E X),
    Vis e k = Vis e' k' -> e = e'.
Proof.
  intros E X Y e e' k k' H.
  inversion H.
  apply inj_pair2 with (P := (fun Y : Type => E Y)).
  apply H1.
Qed.

Lemma eutt_err_t : forall E X s1 s2 (t : M E X) , EquivUpToTau (Err s1) t -> EquivUpToTau (Err s2) t.
Proof.
  intros E X.
  pcofix eutt_err_t.
  intros s1 s2 t H.
  punfold H. inversion H; subst.
  - pfold.  econstructor; eauto. right. apply eutt_err_t with (s1:=s1). eutt_mono.
  - pfold.  econstructor; eauto. 
Qed.  

Lemma eutt_trans : forall E X (s t u : M E X),
    EquivUpToTau s t -> EquivUpToTau t u -> EquivUpToTau s u.
Proof.
  intros E X.
  pcofix eutt_trans.
  intros s t u H1 H2.

  punfold H1. punfold H2.
  destruct H1 as [ | ? e1 ks kt | | | | ];
    inversion H2 as [ | ? e2 kt' ku | | t2 t2' u2 | | ]; pfold.
  - (* Ret, Ret, Ret *) constructor.
  - (* Ret, Ret, Tau *) econstructor; try eauto. eutt_mono.
  - (* Vis, Vis, Vis *)
    (* induction Hk as [? Hk] using eq_sigT_rect. *) replace e2 with e1.
    + constructor.
      intro y.
      right.
      eapply eutt_trans. 
      * specialize H with (y:=y). pclearbot. eauto.
      * replace kt with kt'.
        -- specialize H0 with (y:=y). pclearbot. eauto.
        -- apply inj_pair2 with (P := fun Y => Y -> M E X).
           auto.
    + symmetry. apply inj_pair2 with (P := E). auto.

  - (* Vis, Vis, Tau *) econstructor.
    + intros ? I. inversion I.
    + eassumption.
    + right. eapply eutt_trans.
      * pclearbot. eauto. 
      * pclearbot. assumption.

  - (* Tau, Tau, Tau *) econstructor.
    right. eapply eutt_trans; pclearbot; try eassumption.

  - (* Tau, Tau, ~Tau *)
    assert (I : exists s', UnTau s s' /\ EquivUpToTau t2' s').
    { apply eutt_untau with (s := t) (s' := t2').
      * assumption.
      * apply eutt_sym. pclearbot. assumption. }
    destruct I as [s' [I1 I2]].
    econstructor.
    + assumption.
    + eassumption.
    + right. eapply eutt_trans.
      * eapply eutt_sym; apply I2.
      * pclearbot. assumption.

  - (* Tau, Tau & ~Tau, Tau *)
    dispatch_contra.

  - (* Tau, Ret, Ret *)
    subst. eapply EquivTauLeft.
    * intros t' I; inversion I.
    * eassumption.
    * left. eutt_mono.

  - (* Tau, Vis, Vis *)
    subst. eapply EquivTauLeft.
    * intros t' I; inversion I.
    * eassumption.
    * right. eapply eutt_trans. pclearbot. eauto. pfold. assumption.

  - (* Tau, ~Tau & Tau, Tau *)
    dispatch_contra.
  - (* Tau, ~Tau & Tau, ~Tau *)
    dispatch_contra.

  - (* Tau, ~Tau, Tau *)
    constructor.
    right.
    eapply eutt_trans.
    + eapply eutt_untau_trans.
      * eassumption.
      * pclearbot. eassumption.
    + eapply eutt_sym.
      eapply eutt_untau_trans.
      * eassumption.
      * eapply eutt_sym. pclearbot. assumption.

  - subst. eapply EquivTauLeft.
    + intros t' I; inversion I.
    + eassumption.
    + right. eapply eutt_trans. pclearbot. apply H1. pfold. apply H2.

      
  - (* ~Tau, Tau, Tau *)
    assert (I : exists u', UnTau u u' /\ EquivUpToTau t' u').
    { eapply eutt_untau. apply OneTau. eassumption.  pfold. assumption. }
    destruct I as [u' [I ?]].
    destruct I.
    + econstructor.
      * assumption.
      * inversion H5. eassumption.
      * right. eapply eutt_trans. pclearbot. eassumption. assumption.
    + dispatch_contra.

  - (* ~Tau, Tau, ~Tau *)
    assert (I : t' = t2').
    { eapply untau_inj; eassumption. }
    rewrite <- I in *.
    pclearbot.
    punfold H1.
    punfold H5.
    inversion H1;
      inversion H5;
      pclearbot;
      subst;
      try assumption;
      try dispatch_contra.
    + eutt_mono.
    + inversion H12. subst.
      replace e0 with e.
      replace k0 with k2 in *.
      * constructor.
        intro y.
        right. specialize H8 with (y:=y). specialize H11 with (y:=y).
        apply eutt_trans with (t:=(k2 y));  eutt_mono.
      * apply inj_pair2 with (P := fun Y => Y -> M E X); auto.
      * apply inj_pair2 with (P := E); auto.
    + exfalso. eapply untau_notau. eassumption.
    + constructor.

  - (* ~Tau, Tau & ~Tau, Tau *)
    dispatch_contra.

  - subst. econstructor.
    + intros u I; inversion I.
    + eassumption.
    + assert (upaco2 (eutt_step (X:=X)) bot2 (Err s1) t') as H3.
      left. eapply eutt_err_t. eutt_mono. apply H1.
      left. pclearbot. eutt_mono.

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

