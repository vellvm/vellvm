(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import Coq.Init.Specif.
Require Import ProofIrrelevance.
Require Import Vellvm.Classes Vellvm.Util.
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

Definition idM {E X} (i: M E X) :=
  match i with 
  | Ret x => Ret x
  | Vis e k => Vis e k
  | Tau k => Tau k
  | Err s => Err s
  end.
Lemma matchM : forall {E X} (i: M E X), i = idM i.
Proof. destruct i; auto. Qed.

Module Core.

(** [M E] forms a [Monad] *)
Definition bind_body {E X Y}
           (s : M E X)
           (go : M E X -> M E Y)
           (t : X -> M E Y) : M E Y :=
  match s with
  | Ret x => t x
  | Vis e k => Vis e (fun y => go (k y))
  | Tau k => Tau (go k)
  | Err s => Err s
  end.

Definition bindM {E X Y} (s: M E X) (t: X -> M E Y) : M E Y :=
  (cofix go (s : M E X) :=
      bind_body s go t) s.

Lemma bind_def_core : forall {E X Y} s (k : X -> M E Y),
    bindM s k = bind_body s (fun s => bindM s k) k.
Proof.
  intros.
  rewrite matchM.
  destruct s; auto.
  simpl.
  rewrite (@matchM _ _ (k x)) at 2.
  auto.
Qed.

End Core.

(* This is (almost) the strongest bisimulation between two traces. It requires
   all of the Tau steps to line up, each of the visible events to match, and
   that the returned values are [=].  For convenience, we _do_ allow any error
   message to be considered equivalent to any other.  
*)
Inductive equiv_step {E X} (equiv: relation (M E X)) : relation (M E X) :=
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


Instance equiv_refl : Reflexive (@equiv E X).
Proof.
  intros E X.
  pcofix CH.
  intros x; destruct x; pfold; econstructor; eauto.
Qed.

Instance equiv_sym : Symmetric (@equiv E X).
Proof.
  intros E X.
  pcofix CH.
  intros x y H.
  punfold H. inversion H; subst; pfold; econstructor.
  - intros y. right. apply CH. specialize H0 with (v:=y). pclearbot. assumption.
  - right. apply CH. pclearbot. assumption.
Qed.

Instance equiv_transitive : Transitive (@equiv E X).
Proof.
  intros E X.
  pcofix CH.
  intros x y z Hxy Hyz. pinversion Hyz; subst; pinversion Hxy; subst; pfold.
  - constructor.
  - apply inj_pair2 in H3.
    apply inj_pair2 in H4.
    subst.
    constructor.
    intro y'.
    right.
    eapply CH; auto. specialize H2 with (v:=y'). pclearbot. eassumption.
    specialize H with (v:=y'). pclearbot. assumption.
  - constructor. right. eauto.
  - constructor.
Qed.

Global Instance equivEquivalence : Equivalence (@equiv E X).
Proof.
  constructor; typeclasses eauto.
Qed.

Lemma cong_bind {E X Y} :
  forall s (k k' : X -> M E Y),
    (forall x, equiv (k x) (k' x)) ->
    equiv (Core.bindM s k) (Core.bindM s k').
Proof.
  pcofix CH.
  intros s k k' H0. 
  do 2 rewrite Core.bind_def_core.
  destruct s; simpl.
  - eapply paco2_mon. apply H0. intros ? ? PR; inversion PR.
  - pfold. constructor. intros. right. eauto.
  - pfold. constructor. intros. right. eauto.
  - pfold. constructor.
Qed.

Definition bindM {E X Y} (s: M E X) (t: X -> M E Y) : M E Y :=
  Core.bindM s (fun x => Tau (t x)).

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

Lemma bind_def_core : forall E X Y s (k : X -> M E Y),
    Core.bindM s k = Core.bind_body s (fun s => Core.bindM s k) k.
Proof.
  intros.
  rewrite matchM.
  destruct s; auto.
  simpl.
  rewrite (@matchM _ _ (k x)) at 2.
  auto.
Qed.

Lemma bind_def E X Y :
  forall s (k : X -> M E Y),
    bindM s k = Core.bind_body s (fun s' => bindM s' k) (fun x => Tau (k x)).
Proof.
  unfold bindM.
  intros s k.
  rewrite bind_def_core.
  auto.
Qed.

(* Notes -------------------------------------------------------------------- *)

(* TODO: Compare / reconcile with Liyao's version from DeepWeb.  

   - Should we prove a more general library of "(bi)simulations up-to-R"?
   - Can we then 

   - Can we get some kind of monad library into the Coq Standard Library?

   - use paco for that library?

   - ask about the motivation for refactoring of the UnTau / eutt stuff
*)


(* Properties of Traces ----------------------------------------------------- *)

Section UpToTau.

  Variable E : Type -> Type.
  
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

Variable (X : Type) (R : relation X) (ER : Equivalence R).

Inductive UnTau : relation (M E X) :=
| OneTau : forall s t, UnTau s t -> UnTau (Tau s) t
| NoTau : forall s, UnTau s s.

Lemma untau_tau : forall s s',
    UnTau s (Tau s') -> UnTau s s'.
Proof.
  fix IH 3.
  intros s s' H.
  inversion_clear H as [ s0 s0' H0 | ].
  - constructor. apply IH. assumption.
  - repeat constructor.
Qed.

Lemma untau_trans : forall s t u,
    UnTau s t -> UnTau t u -> UnTau s u.
Proof.
  fix IH 4.
  intros s t u Hst Htu.
  inversion_clear Hst as [ s0 s0' Hst0 | ].
  - constructor. eapply IH; eauto.
  - auto.
Qed.


Inductive eutt_step (eutt ent : relation (M E X)) : relation (M E X) :=
| EquivTau : forall s t,
    eutt s t ->
    eutt_step eutt ent (Tau s) (Tau t)
| EquivTauExhaust : forall s s' t t',
    UnTau s s' ->
    UnTau t t' ->
    ent s' t' ->
    eutt_step eutt ent s t
.
Hint Constructors eutt_step.

Inductive ent_step (eutt ent : relation (M E X))  : relation (M E X) :=
| EquivRet : forall x x', R x x' -> ent_step eutt ent (Ret x) (Ret x')
| EquivVis : forall Y (e : E Y) (k1 k2 : Y -> M E X),
    (forall y, eutt (k1 y) (k2 y)) ->
    ent_step eutt ent (Vis e k1) (Vis e k2)
| EquivErr : forall s1 s2, ent_step eutt ent (Err s1) (Err s2)
.                               
Hint Constructors ent_step.

Lemma eutt_step_monotone : monotone2_2 eutt_step.
Proof.
  unfold monotone2_2. intros x0 x1 r_0 r_1 r'_0 r'_1 IN LE_0 LE_1.
  inversion IN; subst.
  - eapply EquivTau. eauto.
  - eapply EquivTauExhaust. apply H. apply H0. apply LE_1. assumption.
Qed.
Hint Resolve eutt_step_monotone : paco.


Lemma ent_step_monotone : monotone2_2 ent_step.
Proof.
  unfold monotone2_2. intros x0 x1 r_0 r_1 r'_0 r'_1 IN LE_0 LE_1.
  induction IN.
  - eapply EquivRet. assumption.
  - eapply EquivVis. intros y. apply LE_0. apply H.
  - eapply EquivErr.
Qed.
Hint Resolve ent_step_monotone : paco.


Definition eutt_strong (r1 r2 : relation (M E X)):= paco2_2_0 (@eutt_step) (@ent_step) r1 r2.
Hint Unfold eutt_strong.

Definition EquivUpToTau (s t : M E X) := (@eutt_strong bot2 bot2) s t .
Hint Unfold EquivUpToTau.

Definition ent_strong (r1 r2 : relation (M E X)) := paco2_2_1 (@eutt_step) (@ent_step) r1 r2.
Hint Unfold ent_strong.

Definition EquivNoTau (s t : M E X) := (@ent_strong bot2 bot2) s t.
Hint Unfold EquivNoTau.

Lemma eutt_refl : forall (s : M E X),
    EquivUpToTau s s.
Proof.
  pcofix eutt_refl.
  intros.
  pfold.
  destruct s; auto.
  - eapply EquivTauExhaust. eapply NoTau. eapply NoTau. left. pfold. eapply EquivRet. reflexivity.
  - eapply EquivTauExhaust. eapply NoTau. eapply NoTau. left. pfold. eapply EquivVis. intros.
    right. eapply eutt_refl.
  - eapply EquivTauExhaust. eapply NoTau. eapply NoTau. left. pfold. eapply EquivErr. 
Qed.

Lemma eutt_sym : forall (s t : M E X),
    EquivUpToTau s t -> EquivUpToTau t s.
Proof.
  pcofix eutt_sym.
  intros s t H0. 
  punfold H0. pfold.
  induction H0; eauto.
  - econstructor. pclearbot. right. eauto.
  - pclearbot. punfold H1.
    inversion H1; subst; eauto.
    + eapply EquivTauExhaust; eauto. left. pfold. eapply EquivRet. symmetry. assumption.
    + eapply EquivTauExhaust; eauto. left. pfold. eapply EquivVis. intros y.
      right. eapply eutt_sym. specialize H2 with (y:=y). pclearbot. eauto.
Qed.

Lemma eunt_sym : forall (s t : M E X),
    EquivNoTau s t -> EquivNoTau t s.
Proof.
  pcofix eunt_sym.
  intros s t H. 
  punfold H. pfold.
  inversion H; subst; eauto.
  - econstructor. symmetry. assumption.
  - econstructor. intros y. left. eapply paco2_2_0_mon. eapply eutt_sym.
    specialize H0 with (y:=y). pclearbot. eauto.
    intros ? ? PR; inversion PR. intros ? ? PR; inversion PR.
Qed.


Lemma equiv_is_eutt : forall (s s' : M E X),
    equiv s s' -> EquivUpToTau s s'.
Proof.
  pcofix CH.
  intros s s' H. pinversion H; subst; pfold.
  + econstructor. econstructor. econstructor. left. pfold. econstructor. reflexivity.
  + econstructor. econstructor. econstructor. left. pfold. econstructor. intros y.
    right. eapply CH.  specialize H0 with (v:=y). pclearbot. assumption.
  + econstructor. right. eapply CH. assumption.
  + econstructor. econstructor. econstructor. left. pfold. econstructor.
Qed.

Lemma pop_tau :
  forall (s t : M E X),
    EquivUpToTau s (Tau t) -> EquivUpToTau s t.
Proof.
  pcofix CH.
  intros s t H.
  pinversion H. pinversion H2; subst.
  - pfold. eapply EquivTau. right. eapply CH. pfold. econstructor. left. exact H3.
  - pfold. econstructor. eapply OneTau. eauto. eauto. left.
    eapply paco2_2_1_mon. eapply H5. intros ? ? HB; inversion HB. intros ? ? HB; inversion HB.
  - subst. pfold. pinversion H2; subst; inversion H1; subst.
    econstructor. eapply H0. eapply H5. 
    left. pfold. econstructor. eauto.
    econstructor. eapply H0. eapply H5.
    left. eapply paco2_2_1_mon. pfold.  econstructor. eapply H3. intros ? ? HB; inversion HB. intros ? ? HB; inversion HB.
    econstructor. eapply H0. eapply H4.
    left. eapply paco2_2_1_mon. pfold. apply H2. intros ? ? HB; inversion HB. intros ? ? HB; inversion HB.
Qed.
    
  
Lemma push_tau :
  forall (s t : M E X),
    EquivUpToTau s t -> EquivUpToTau s (Tau t).
Proof.
  pcofix CH.
  intros s t H.
  pinversion H.
  - pfold. constructor. right. apply CH. eauto.
  - pfold. econstructor; eauto. apply OneTau. eassumption. left.
    eapply paco2_2_1_mon. apply H2. intros ? ? PR; inversion PR. intros ? ? PR; inversion PR.
Qed.

Lemma tau_notau :
  forall (s t t' u' : M E X),
    EquivUpToTau s t ->
    UnTau t t' ->
    EquivNoTau t' u' ->
    exists s', UnTau s s' /\ EquivNoTau s' t'.
Proof.
  intros s t t' u' Hst Htt' Ht'u'.
  induction Htt'.
  - apply IHHtt'; auto.
    eapply pop_tau. eauto.
  - pdestruct Hst; pinversion Ht'u'; subst;
      exists s'; split; auto; inversion H0; subst; auto.
Qed.

Lemma eutt_untau : forall (s s' : M E X),
    UnTau s s' -> EquivUpToTau s s'.
Proof.
  intros s s' H.
  induction H.
  - apply eutt_sym.
    apply push_tau.
    apply eutt_sym.
    auto.
  - apply eutt_refl.
Qed.

Lemma untau_inj :
  forall (s s' s'' t' t'' : M E X),
    UnTau s s' ->
    UnTau s s'' ->
    EquivNoTau t' s' ->
    EquivNoTau s'' t'' ->
    s' = s''.
Proof.
  intros s s' s'' t' t'' H.
  induction H; intros H' Hts' Hst''; inversion H'; auto;
    (pinversion Hst''; pinversion Hts'; subst; discriminate).
Qed.


Lemma eutt_trans1:
    forall r1 r2 : M E X -> M E X -> Prop,
      (forall s t u : M E X, EquivNoTau s t -> EquivNoTau t u -> paco2_2_1 eutt_step ent_step r1 r2 s u) ->
      forall s t u : M E X, EquivUpToTau s t -> EquivUpToTau t u -> paco2_2_0 eutt_step ent_step r1 r2 s u.
  Proof.
    intros r1 r2 HN.
    pcofix CH2.
    intros s t u Hst Htu.
    pdestruct Hst.
    pinversion Htu; subst.
    - pfold. econstructor. right. eapply CH2. eapply H. eapply H1.

    - pfold. apply push_tau in H.
      pose (Hs1t1 := tau_notau H H0 H2).
      destruct Hs1t1 as [s0' [Hs1 Hs't2']].
      econstructor.
      + constructor; eassumption.
      + eassumption.
      + left. eapply paco2_2_1_mon. eapply HN. eapply Hs't2'. eapply H2. apply CH0. intros; eauto.
    - pfold.
      (* _, _ & Tau, Tau *)
      apply eutt_sym in Htu.
      apply eunt_sym in H1.
      pose (Ht1u := tau_notau Htu H0 H1).
      destruct Ht1u as [s0' [Hu Hs't1']].
      econstructor.
      + eassumption.
      + eassumption.
      + left.
        eapply paco2_2_1_mon.
        eapply HN; apply eunt_sym; eassumption. apply CH0. intros; eauto.
Qed.

Lemma eutt_trans2:
    forall r1 r2 : M E X -> M E X -> Prop,
      (forall s t u : M E X, EquivNoTau s t -> EquivNoTau t u -> r2 s u) ->
      forall s t u : M E X, EquivUpToTau s t -> EquivUpToTau t u -> paco2_2_0 eutt_step ent_step r1 r2 s u.
  Proof.
    intros r1 r2 HN.
    pcofix CH2.
    intros s t u Hst Htu.
    pdestruct Hst.
    pinversion Htu; subst.
    - pfold. econstructor. right. eapply CH2. eapply H. eapply H1.

    - pfold. apply push_tau in H.
      pose (Hs1t1 := tau_notau H H0 H2).
      destruct Hs1t1 as [s0' [Hs1 Hs't2']].
      econstructor.
      + constructor; eassumption.
      + eassumption.
      + right. eapply HN. eapply Hs't2'. eapply H2. 
    - pfold.
      (* _, _ & Tau, Tau *)
      apply eutt_sym in Htu.
      apply eunt_sym in H1.
      pose (Ht1u := tau_notau Htu H0 H1).
      destruct Ht1u as [s0' [Hu Hs't1']].
      econstructor.
      + eassumption.
      + eassumption.
      + right.
        eapply HN; apply eunt_sym; eassumption. 
Qed.

  
  Lemma ent_trans1:
    forall r1 r2 : M E X -> M E X -> Prop,
      (forall s t u : M E X, EquivUpToTau s t -> EquivUpToTau t u -> r1 s u) -> 
      forall s t u : M E X, EquivNoTau s t -> EquivNoTau t u -> paco2_2_1 eutt_step ent_step r1 r2 s u.
  Proof.
    intros r1 r2 HE.
    pcofix CH2.
    intros s t u Hst Htu.
    pdestruct Hst; pinversion Htu; subst.
    - pfold. econstructor. eapply transitivity. eapply H. eapply H1.
    - pfold. 
      apply inj_pair2 in H2. subst.
      apply inj_pair2 in H3. subst.
      econstructor. intros y.
      right. 
      specialize H with (y:=y). specialize H4 with (y:=y).
      pclearbot.
      eapply HE. 
      eauto. eauto.
    - pfold. econstructor.
  Qed.      

  Lemma ent_trans2:
    forall r1 r2 : M E X -> M E X -> Prop,
      (forall s t u : M E X, EquivUpToTau s t -> EquivUpToTau t u -> paco2_2_0 eutt_step ent_step r1 r2 s u) -> 
      forall s t u : M E X, EquivNoTau s t -> EquivNoTau t u -> paco2_2_1 eutt_step ent_step r1 r2 s u.
  Proof.
    intros r1 r2 HE.
    pcofix CH2.
    intros s t u Hst Htu.
    pdestruct Hst; pinversion Htu; subst.
    - pfold. econstructor. eapply transitivity. eapply H. eapply H1.
    - pfold. 
      apply inj_pair2 in H2. subst.
      apply inj_pair2 in H3. subst.
      econstructor. intros y.
      left.
      specialize H with (y:=y). specialize H4 with (y:=y).
      pclearbot.
      eapply paco2_2_0_mon.
      eapply HE. 
      eauto. eauto. intros; eauto. exact CH0.
    - pfold. econstructor.
  Qed.      

  
Lemma eutt_trans : Transitive (EquivUpToTau). 
Proof.
  pcofix CH.
  intros s t u Hst Htu.
  apply eutt_trans1 with (t:=t)(r1:=r)(r2:=bot2); eauto.
  pcofix CH2.
  intros.
  eapply ent_trans1 with (t:=t0)(r1:=r)(r2:=r0); eauto.
Qed.
  
Lemma ent_trans : Transitive (EquivNoTau).
Proof.
  pcofix CH.
  intros x y z H0 H1.
  apply ent_trans2 with (t:=y)(r1:=bot2)(r2:=r); eauto.
  pcofix CH2.
  intros; eapply eutt_trans2; eauto.
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

Definition eutt_step_strong 
  : forall (E : Type -> Type) (X : Type), (M E X -> M E X -> Prop) -> M E X -> M E X -> Prop :=
  fun E X R => @eutt_step E _ (fun x y => R x y /\ R (id <$> x) y).

Lemma eutt_step_strong_mono {E X} : monotone2 (@eutt_step_strong E X).
Proof.
  unfold monotone2. unfold eutt_step_strong.  intros x0 x1 r r' IN LE.  
  induction IN; eauto.
  - econstructor. intros. split. destruct (H y) as [H1 H2]. eauto.
    destruct (H y) as [H1 H2]. eauto.
  - econstructor. split. destruct H as [H1 H2]. eauto.
    destruct H as [H1 H2]. eauto.
  - econstructor; eauto. split. destruct H1 as [H2 H3]. eauto.
    destruct H1 as [H2 H3]. eauto.
  - econstructor; eauto. split. destruct H1 as [H2 H3]. eauto.
    destruct H1 as [H2 H3]. eauto.
Qed.
Hint Resolve eutt_step_strong_mono : paco.


Definition EquivUpToTau_Strong {E X} (s t : M E X) := paco2 (@eutt_step_strong E X) bot2 s t .
Hint Unfold EquivUpToTau_Strong.


Lemma pad_tau_left : forall {E X} (t : M E X), Tau t ≡ t.
Proof.
  intros E X.
  pcofix CH.
  intros t.
  pfold.
  destruct t.
  - econstructor. intros. dispatch_contra. eapply NoTau. dispatch_contra.
    left. pfold. econstructor.
  - econstructor. intros. dispatch_contra. eapply NoTau. dispatch_contra.
    left. pfold. econstructor. intros y. left. eapply paco2_mon. eapply eutt_refl.
    intros. inversion PR.
  - econstructor. right. eapply CH.
  - econstructor. intros. dispatch_contra. eapply NoTau. dispatch_contra.
    left. pfold. econstructor.
Qed.
    


(* SAZ: 
Functoriality of (M E) probably holds only up to coinductively defined
bisimulation of eq.  Or, we should assume as an Aximo that eq coincides
with that bisimulation.
*)
Instance M_functor_eutt_laws {E} : (@FunctorLaws (M E)) (@mapM E) (@equiv_eutt E).
Proof.
  split.
  * intros A. pcofix H.
    intros a.
    rewrite matchM. simpl.
    destruct a; pfold; econstructor.
  - intros. right. eapply H.
  - right. eapply H.

  * intros A B C f g a.
    generalize dependent a.
    pcofix CH.
    intros a.
    rewrite matchM.
    replace (g ∘ f <$> a) with (idM (g ∘ f <$> a)).
    destruct a; simpl; pfold.
    - econstructor.
    - econstructor. intros y. right.
      unfold fmap, functor_M, mapM in CH.
      eapply CH.
    - econstructor. right.
      unfold fmap, functor_M, mapM in CH.
      eapply CH.
    - econstructor.
    - rewrite <- matchM. reflexivity.
Qed.

Ltac monad_laws a :=
    let CH := fresh in
    let PR := fresh in 
    generalize dependent a;
    pcofix CH;
    intros a;
    rewrite matchM; destruct a; [
      eapply paco2_mon; [ eapply pad_tau_left | intros ? ? PR; inversion PR ]
    | pfold; econstructor; intros; right; eapply CH
    | pfold; econstructor; right; eapply CH
    | pfold; econstructor]
.

Program Instance M_monad_eutt_laws {E} : (@MonadLaws (M E)) (@functor_M E) (@monad_M E) _ _ _.
Next Obligation.
  monad_laws a.
Defined.  
Next Obligation.
    generalize dependent a;
    pcofix CH.
    intros a.
    rewrite matchM. simpl.
    eapply paco2_mon. eapply pad_tau_left. intros ? ? PR; inversion PR.
Defined.
Next Obligation.
  generalize dependent a.
  generalize dependent f.
  generalize dependent g.    
  pcofix CH.
  intros g f a.
  rewrite matchM.
  replace (bindM a (fun x : A => bindM (f x) g)) with (idM (bindM a (fun x : A => bindM (f x) g))).
  destruct a; simpl.
  - pfold. econstructor. left. eapply paco2_mon. eapply eutt_refl. intros ? ? PR; inversion PR.
  - pfold. econstructor. intros y. right.
    specialize CH with (g:=g)(f:=f)(a:=(k y)).
    eapply CH.
  - pfold. econstructor. right.
    specialize CH with (g:=g)(f:=f)(a:=a).
    eapply CH.
  - pfold. econstructor.
  - rewrite <- matchM. reflexivity.
Defined.    

Lemma bind_hom_1 {E X Y} : forall (x y : M E X) (f : X -> M E Y), x ≡ y -> (x ≫= f) ≡ (y ≫= f).
Proof.
  pcofix CH.
  intros x y f He.
  replace (x ≫= f) with (idM (x ≫= f)).
  replace (y ≫= f) with (idM (y ≫= f)).
  pdestruct He.
  - eapply paco2_mon. apply eutt_refl. intros ? ? PR; inversion PR.
  - pfold. econstructor. intros y. right.
    unfold mbind in CH. unfold monad_M in CH. unfold bindM in CH.
    eapply CH with (x := (k1 y))(y:=(k2 y))(f:=f).
    specialize H with (y:=y). pclearbot. apply H.
  - pfold. econstructor. right.
    unfold mbind in CH. unfold monad_M in CH. unfold bindM in CH.
    eapply CH with (x := s)(y:=t)(f:=f).
    eauto.
  - pfold. 
    pinversion H1; subst; simpl.
    * econstructor. left.
      eapply paco2_mon. eapply mret_mbind.
    
    
    
  

End MonadVerif.

