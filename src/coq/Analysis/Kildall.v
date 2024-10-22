(** * Kildall: Forward Dataflow Analysis *)

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** * Acknowledgements *)
(**
  This file is heavily based on:

      - lib/Lattice.v

      - backend/Kildall.v

  from the CompCert development,  modified to remove dependencies and
  optimizations.

*)

Require Import Equalities Orders.
Require Import FMaps.


From Vellvm.Analysis Require Import
     Iteration
     Lattice.


Module FMapProps (E:UsualDecidableType) (M:FMapInterface.WSfun E).

  #[local] Notation K := M.key.

  Section FMapProps.

  Variable V : Type.

  Definition find_default (m:M.t V) (k:K) (d:V) : V :=
    match M.find k m with
      | None => d
      | Some m => m
    end.

  Lemma find_default_neq : forall  m n1 n2 l d,
    n1 <> n2 ->
    find_default (M.add n1 l m) n2 d = find_default m n2 d.
  Proof.
    intros. unfold find_default.
    destruct (M.find n2 (M.add _ _ _)) eqn:Heq1, (M.find n2 m) eqn:Heq2.
    apply M.find_2 in Heq1. apply M.add_3 in Heq1; auto. apply M.find_1 in Heq1.
      rewrite Heq2 in Heq1. injection Heq1. auto.
    apply M.find_2 in Heq1. apply M.add_3 in Heq1; auto. apply M.find_1 in Heq1.
      rewrite Heq2 in Heq1. discriminate Heq1.
    apply M.find_2 in Heq2. eapply M.add_2 in Heq2; eauto. apply M.find_1 in Heq2.
      rewrite Heq2 in Heq1. discriminate Heq1.
    trivial.
  Qed.

  Lemma find_default_eq : forall m n1 n2 l d,
    n1 = n2 ->
    find_default (M.add n1 l m) n2 d = l.
  Proof.
    unfold find_default; intros.
    erewrite M.find_1. reflexivity. apply M.add_1; auto.
  Qed.

  End FMapProps.

End FMapProps.

Module Type FORWARD_SOLVER.

  Declare Module L : Lattice.SemiLattice.             (* domain of approximations *)
  Declare Module N : UsualDecidableType.  (* program points *)

  Declare Module NM : FMapInterface.WSfun N.
  Module FMP := FMapProps N NM.

  (* TODO: should it really always be top?!? *)
  Import (notations) L.
  Notation "a !! b" := (FMP.find_default _ a b L.top)
                         (at level 1, format "a !! b").
  Notation nlmap := (NM.t L.t).

  Parameter fixpoint: forall
    (succs: N.t -> list N.t)
    (trans: N.t -> L.t -> L.t)
    (inits: nlmap),
    option nlmap.

  Axiom fixpoint_solution : forall
      (succs: N.t -> list N.t)
      (trans: N.t -> L.t -> L.t)
      (inits: nlmap) res (n: N.t) (s: N.t),
    fixpoint succs trans inits = Some res ->
    NM.In n inits ->
    In s (succs n) ->
    res!!s <= trans n res!!n.

  Axiom fixpoint_entry : forall succs trans inits res n,
    fixpoint succs trans inits = Some res ->
    res!!n <= inits!!n.

  Axiom fixpoint_invariant : forall succs trans inits
    (P: N.t -> L.t -> Prop)
    (Pinits: forall n, P n inits!!n)
    (Ptrans: forall n ln s ls,
      In s (succs n) ->
      P n ln -> P s ls -> P s (L.meet ls (trans n ln))),
    forall res n, fixpoint succs trans inits = Some res -> P n res!!n.

End FORWARD_SOLVER.

Module ForwardSolver (PC:UsualDecidableType) (LAT: Lattice.SemiLattice) <:
                     FORWARD_SOLVER with Module L := LAT
                                    with Module N := PC.

  Module L := LAT.
  Module N := PC.
  Module LFacts := Lattice.SemiLatticeFacts L.
  Import (notations) L.


  (* TODO: can define a total order for PCs to use more efficient sets/maps *)
  Module NM := FMapWeakList.Make N.
  Module Import FMP := FMapProps N NM.
  Module NMFacts := FMapFacts.WFacts NM.

  Import (notations) L.
  Notation "a !! b" := (find_default _ a b L.top) (at level 1, format "a !! b").
  Notation nlmap := (NM.t L.t).

  Record state := mkst { lmap: NM.t L.t; wlist: list N.t }.

  Section KILDALL.

  Variable succs : N.t -> list N.t.
  Variable trans : N.t -> L.t -> L.t.
  Variable inits : nlmap.

  Definition prop_succ (out:L.t) (s:state) (n:N.t) : state :=
    let oldl := s.(lmap)!!n in
    let newl := L.meet oldl out in
    if L.eq_dec oldl newl
    then s else mkst (NM.add n newl s.(lmap)) (n::s.(wlist)).

  Definition step (s:state) : NM.t L.t + state :=
    match s.(wlist) with
      | nil => inl s.(lmap)
      | n::rem =>
        inr (fold_left (prop_succ (trans n s.(lmap)!!n))
                       (succs n) (mkst s.(lmap) rem))
    end.

  Definition make_init_state : state :=
    mkst inits (map (@fst _ _) (NM.elements inits)).

  Definition fixpoint := Iter.iterate step make_init_state.


  (* correctness *)

  Definition n_invar (s:state) (n:N.t) : Prop :=
    In n s.(wlist) \/ forall m, In m (succs n) ->
      s.(lmap)!!m <= trans n s.(lmap)!!n.

  Definition state_invar (s:state) : Prop :=
    forall n, NM.In n inits -> n_invar s n.

  Lemma prop_n_invar_pres : forall o s n n',
    n_invar s n -> n_invar (prop_succ o s n') n.
  Proof.
    unfold n_invar. intros.
    set (s' := prop_succ o s n'); unfold prop_succ in s'.
    destruct (L.eq_dec _ _); [solve [apply H]|].
    destruct H; [solve [simpl; intuition]|].
    destruct (N.eq_dec n n'); [solve [simpl; intuition]|].
    right. intros.
    destruct (N.eq_dec n' m); subst s'; simpl.
    - subst.
      rewrite
        -> (find_default_eq _ _ m),
        -> (find_default_neq _ _ m n) by auto.
      transitivity (lmap s)!!m.
      + apply LFacts.le_meet_l.
      + apply H. assumption.
    - rewrite find_default_neq, find_default_neq; auto.
  Qed.

  (* TO MOVE *)
  Lemma fold_left_1 : forall {A B: Type} (P:A -> Prop) (f:A -> B -> A) (bs : list B)
                         (Hpres : forall a b, In b bs -> P a -> P (f a b)),
      forall a a',
        a' = fold_left f bs a -> P a -> P a'.
  Proof.
    intros. subst a'. generalize dependent a.
    induction bs; simpl; intros. assumption.
    apply IHbs. intros. apply Hpres. right; auto. assumption.
    apply Hpres. left; auto. assumption.
  Qed.

  (* TO MOVE *)
  Lemma fold_left_2 : forall {A B: Type} (P:A -> B -> Prop)
                        (f:A -> B -> A)
                        (Hpres : forall a b b', P a b -> P (f a b') b)
                        (Hintr : forall a b, P (f a b) b),
      forall a a' bs b,
        a' = fold_left f bs a ->
        In b bs -> P a' b.
  Proof.
    intros. subst a'. generalize dependent a.
    induction bs as [|b']. contradiction.
    simpl; intros. destruct H0. subst b'.
    set (a' := fold_left _ _ _). pattern a'.
    eapply fold_left_1; eauto.
    subst; reflexivity.
    apply IHbs; assumption.
  Qed.

  Lemma prop_n_out : forall o ns s s' n,
    s' = fold_left (prop_succ o) ns s ->
    ~ In n (wlist s') ->
    trans n (lmap s')!!n == trans n (lmap s)!!n.
  Proof.
    intros o ns s s' n Heqs'. pattern s'.
    eapply fold_left_1; eauto.
    intros. set (r := prop_succ o a b) in *.
    unfold prop_succ in r. destruct (L.eq_dec _ _). apply H0; auto.
    destruct (N.eq_dec b n). contradict H1; simpl; auto.
      subst r. simpl in *. rewrite find_default_neq; auto.
   intro. reflexivity.
  Qed.

  Lemma step_state_invar : forall s s',
    state_invar s -> inr s' = step s -> state_invar s'.
  Proof.
    unfold step, state_invar; intros s s' Hinv Hstep.
    destruct (wlist s) eqn:Hwls. discriminate Hstep.
    injection Hstep; clear Hstep. intros Heqs' n.

    destruct (N.eq_dec t n).

    (* n_invar is restablished for n *)
    - subst t. unfold n_invar.
      destruct(in_dec N.eq_dec n (wlist s')) as [|Hwl]; [auto | right].
      intros m Hin. rewrite prop_n_out; eauto; simpl.
      generalize Hwl; clear Hwl. pattern s', m.

      eapply fold_left_2; eauto.
      + intros a b b'.
        set (r := prop_succ _ a b').
        intros. unfold prop_succ in r. destruct (L.eq_dec _ _). apply H0; auto.
        unfold r. simpl. destruct (N.eq_dec b' b).
        * rewrite find_default_eq; auto. apply LFacts.le_meet_r.
        * rewrite find_default_neq; auto. apply H0. contradict Hwl; simpl; auto.

      + intros a b.
        set (r := prop_succ _ a b).
        intros. unfold prop_succ in r. destruct (L.eq_dec _ _) as [Heq|].
        * subst r. rewrite Heq. apply LFacts.le_meet_r.
        * simpl. rewrite find_default_eq; auto. apply LFacts.le_meet_r.
    - (* n_invar is preserved for all successors ~= n *)
      intros Hin. pattern s'. eapply fold_left_1; eauto.
      intros. apply prop_n_invar_pres. assumption.
      unfold state_invar, n_invar in Hinv |- *.
      simpl. specialize (Hinv n). rewrite Hwls in Hinv. destruct Hinv.
      assumption. left. destruct H; intuition. right. apply H.
  Qed.

  Lemma fixpoint_solution: forall res n s,
    fixpoint = Some res ->
    NM.In n inits ->
    In s (succs n) ->
    res!!s <= trans n res!!n.
  Proof.
    unfold fixpoint; intros. pattern res.
    eapply Iter.iter_prop with
      (step:=step) (P:=state_invar) (a:=make_init_state); eauto.
    - intros a Ha.
    unfold step. destruct (wlist a) eqn:Heql.
      + specialize (Ha n). destruct Ha.
        * auto.
        * rewrite Heql in *. contradiction.
        * auto.
      + eapply step_state_invar. apply Ha.
        unfold step. rewrite Heql. auto.
    - left. simpl. apply in_map_iff.
      pose proof (NMFacts.elements_in_iff inits n0) as [He _].
      specialize (He H2). destruct He as [e Hine].
      apply InA_alt in Hine as [y [Heq Hk]].
      inversion Heq; eauto.
  Qed.

  (* monotonicity *)

  Definition le_nlmap (nl1 nl2: nlmap) : Prop :=
    forall n, nl1!!n <= nl2!!n.

  Lemma le_nlmap_refl : forall nl, le_nlmap nl nl.
  Proof.
    unfold le_nlmap. reflexivity.
  Qed.

  Instance le_nlmap_trans : Transitive le_nlmap.
    unfold Transitive, le_nlmap; intros. transitivity y !! n; auto.
  Qed.

  Hint Resolve LFacts.le_meet_l LFacts.le_meet_r : core .
    (* L.eq_equiv L.le_preorder L.le_poset L.eq_le_reflexive. *)
    (* Saw this in Relation_Definitions but it doesn't appear to work? *)

  Lemma prop_succ_le_nlmap: forall st out n,
    le_nlmap (prop_succ out st n).(lmap) st.(lmap).
  Proof.
    unfold le_nlmap, prop_succ; intros.
    destruct (L.eq_dec _ _). reflexivity.
    simpl. destruct (N.eq_dec n n0).
      subst. rewrite find_default_eq; auto.
      rewrite find_default_neq; auto. reflexivity.
  Qed.

  Lemma step_le_nlmap: forall st st',
    inr st' = step st ->
    le_nlmap st'.(lmap) st.(lmap).
  Proof.
    unfold step; intros. destruct (wlist st).
    discriminate. injection H. intro Heqs.
    pattern st'. eapply fold_left_1.
    intros. transitivity (lmap a).
       apply prop_succ_le_nlmap. assumption.
    apply Heqs. apply le_nlmap_refl.
  Qed.

  Lemma fixpoint_entry : forall res n,
    fixpoint = Some res -> res!!n <= inits!!n.
  Proof.
    unfold fixpoint. intros. pattern res.
    eapply Iter.iter_prop with (step:=step).
    - intros.
      destruct (step a) eqn:Hstep.
      + unfold step in Hstep. destruct (wlist a); try discriminate.
        injection Hstep. intro; subst t. apply H0.
      + simpl in *. transitivity (lmap a)!!n; [|assumption].
        apply step_le_nlmap. auto.
    - change inits with (lmap make_init_state).
      cbv beta. reflexivity.
    - apply H.
  Qed.

  Lemma fixpoint_invariant : forall
    (P: N.t -> L.t -> Prop)
    (Pinits: forall n, P n inits!!n)
    (Ptrans: forall n ln s ls,
      In s (succs n) ->
      P n ln -> P s ls -> P s (L.meet ls (trans n ln))),
    forall res n, fixpoint = Some res -> P n res!!n.
  Proof.
    intros until 2.
    unfold fixpoint. intros. pattern res.
    eapply Iter.iter_prop with (step:=step); eauto.

    intro. destruct (step a) eqn:Hstep.

    (* last step  Q implies P *)
    unfold step in Hstep. destruct (wlist a); try discriminate.
    instantiate (1:=fun s => forall n, P n s.(lmap)!!n).
    injection Hstep. intro; subst t. intros; auto.

    (* P preserved across step *)
    simpl. intros. unfold step in Hstep.
    destruct (wlist a); try discriminate.
    injection Hstep; clear Hstep; intro Heqs.

    pattern s. eapply fold_left_1 with (f:=prop_succ _); eauto.
    intros. unfold prop_succ.
    destruct (L.eq_dec _ _); simpl; auto.
    destruct (N.eq_dec b n0).
    rewrite find_default_eq; auto.
      subst b. apply Ptrans; auto.
    rewrite find_default_neq; auto.
    auto.
  Qed.

  End KILDALL.

End ForwardSolver.
