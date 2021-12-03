From Coq Require Import
     List
     ZArith
     Lia.
Import ListNotations.
From Vellvm Require Import
     Syntax
     Syntax.ScopeTheory
     Utils.Tactics.

Require Import Coqlib.
Require Import Util.
Require Import Datatypes.

Open Scope nat_scope.

(** Misc Tactics *)

(* Clone the hypothesis h *)
Ltac clone_hyp h :=
  let H := fresh "C" in
  assert (C := h).

(* Clone the hypothesis h as a new hypothesis s, and apply the theorem t *)
Ltac capply t h s :=
  assert (s := h) ; apply t in s.

Ltac ceapply t h s :=
  assert (s := h) ; eapply t in s.

Ltac inv_pair :=
  match goal with
  | h : (_,_) = (_, _) |- _ => inv h
  end.

(** Misc lemmas on list *)

Ltac break_list_hyp :=
  match goal with
  | h: context[List.In _ (_ ++ _)] |- _ => repeat (apply in_app_or in h)
  end.

Ltac break_list_goal :=
  try (rewrite Util.list_cons_app) ;
  try (
        match goal with
        | |- context[inputs (_ ++ _)] =>
            repeat (rewrite !ScopeTheory.inputs_app)
        | |- context[outputs (_ ++ _)] =>
            repeat (rewrite !ScopeTheory.outputs_app)
        end ) ;
  try (match goal with
       | |- context[List.In _ (_ ++ _)] => repeat (apply in_or_app)
       end).

Lemma In_singleton : forall {A} (x y : A),
    In x [y] <-> x=y.
Proof.
  intros.
  split ; intro.
  cbn in H; intuition.
  subst; apply in_eq.
Qed.

Lemma hd_In : forall {A} (d : A) (l : list A),
    (length l >= 1)%nat -> In (hd d l) l.
Proof.
  intros.
  induction l.
  now simpl in H.
  simpl ; now left.
Qed.

Lemma List_norepet_singleton : forall {A} (x : A),
    Coqlib.list_norepet [x].
Proof.
  intros.
  apply list_norepet_cons ; auto.
  apply list_norepet_nil.
Qed.

Lemma not_in_app : forall {T} {x : T} l1 l2,
    ~ In x (l1++l2) <-> ~ In x l1 /\ ~ In x l2.
Proof.
  intros.
  intuition.
  apply in_app in H0.
  destruct H0 ; [ now apply H1 | now apply H2].
Qed.

Lemma not_in_incl : forall {T} l l' (x : T),
    incl l' l ->
    ~ In x l ->
    ~ In x l'.
Proof.
  intros.
  unfold incl in H.
  intro. apply H in H1. contradiction.
Qed.

Lemma incl_In :
  forall {T} l sl (y: T), incl sl l -> In y sl -> In y l.
Proof.
  intros.
  now apply H.
Qed.

Lemma incl_disjoint : forall {A} (l1 sl1 l2 : list A),
    List.incl sl1 l1 ->
    list_disjoint l1 l2 ->
    list_disjoint sl1 l2.
Proof.
  intros * INCL DIS.
  unfold incl in INCL.
  induction l2.
  - apply list_disjoint_nil_r.
  - apply list_disjoint_cons_r.
    + unfold list_disjoint ; repeat intro.
      apply INCL in H.
      apply list_disjoint_cons_right in DIS.
      unfold list_disjoint in DIS.
      eapply DIS in H0 ; [|eassumption].
      contradiction.
    + intro. apply INCL in H.
      unfold list_disjoint in DIS.
      apply DIS with (y:=a) in H ; [contradiction|].
      apply in_cns ; intuition.
Qed.


Lemma length_incl : forall {T} (l sl : list T) n,
    (length sl >= n)%nat ->
    incl sl l ->
    (length l >= n)%nat.
Proof.
  (* intros. *)
  induction sl ; intros.
  - simpl in * ; lia .
  - simpl in *. apply IHsl.
Admitted.

Lemma list_norepet_cons' : forall {T} (l : list T) x,
    list_norepet (x :: l) -> list_norepet l.
Proof.
  intros.
  rewrite Util.list_cons_app in H.
  eapply list_norepet_append_right ; eassumption.
Qed.

(** Relation between block_id Definition and lemmas about relation between block_id *)
(* Equality and Inequality *)
Definition eqb_bid b b' :=
  match b,b' with
  | Name s, Name s' => String.eqb s s'
  | Anon n, Anon n' => @RelDec.eq_dec int eq_dec_int n n'
  | Raw n, Raw n' => @RelDec.eq_dec int eq_dec_int n n'
  | _ , _ => false
  end.

Lemma eqb_bid_eq : forall b b', eqb_bid b b' = true <-> b=b'.
Proof.
  intros.
  split.
  - destruct b,b' ;
      try (intros ; simpl in H ; discriminate) ;
      simpl ; intros ; f_equal ;
      try (now apply String.eqb_eq) ;
      try (now apply Z.eqb_eq).
  - intros ; subst.
    destruct b' ; simpl ;
      try (now apply String.eqb_eq) ;
      try (now apply Z.eqb_eq).
Qed.

Lemma eqb_bid_neq : forall b b', eqb_bid b b' = false <-> b<>b'.
Proof.
  intros.
  split.
  - destruct b,b' ;
      try (intros ; simpl in H ; discriminate) ;
      simpl ; intros ; intro ;
      try (apply String.eqb_neq in H);
      try (apply Z.eqb_neq in H);
      inv H0 ; contradiction.
  - intros ; subst.
    destruct b,b' ; simpl ; auto;
      try (apply String.eqb_neq) ;
      try (apply Z.eqb_neq) ;
      intro ; subst ;
      contradiction.
Qed.

Lemma eqb_bid_comm : forall b b', eqb_bid b b' = eqb_bid b' b.
  intros.
  destruct b,b' ; simpl ; auto ;
    try (now apply String.eqb_sym) ;
    try (now apply Z.eqb_sym).
Qed.

Lemma eqb_bid_refl : forall b, eqb_bid b b = true.
  intros.
  destruct b ; simpl ; auto ;
    try (now apply String.eqb_refl) ;
    try (now apply Z.eqb_refl).
Qed.

(* Less than  *)

Definition ltb_bid b b' :=
  match b,b' with
  | Anon n, Anon n' => (n <? n')%Z
  | _, _ => false
  end.

Definition lt_bid (b b': block_id) : Prop :=
  ltb_bid b b' = true.

Lemma ltb_bid_irrefl : forall a, ltb_bid a a = false.
  intros.
  unfold ltb_bid.
  destruct a ; try reflexivity.
  apply Z.ltb_irrefl.
Qed.

Lemma lt_bid_irrefl : forall a, ~ lt_bid a a.
  intros.
  unfold lt_bid.
  rewrite ltb_bid_irrefl.
  auto.
Qed.

Lemma lt_bid_trans : forall b1 b2 b3, lt_bid b1 b2 -> lt_bid b2 b3 -> lt_bid b1 b3.
Proof.
  intros.
  unfold lt_bid, ltb_bid in *.
  destruct b1,b2,b3 ; try auto ; try discriminate.
  rewrite Z.ltb_lt in *. eapply Z.lt_trans ; eassumption.
Qed.

Lemma ltb_bid_true : forall b1 b2, ltb_bid b1 b2 = true <-> lt_bid b1 b2.
Proof.
  intros.
  unfold lt_bid ; tauto.
Qed.

Lemma lt_bid_neq : forall b1 b2, lt_bid b1 b2 -> b1 <> b2.
Proof.
  repeat intro ; subst.
  now apply lt_bid_irrefl in H.
Qed.

Lemma lt_bid_neq' : forall b1 b2, lt_bid b1 b2 -> b2 <> b1.
Proof.
  repeat intro ; subst.
  now apply lt_bid_irrefl in H.
Qed.

(* NOTE need x and y to be Anon *)
Lemma lt_assym : forall x y, ltb_bid x y = false -> ltb_bid y x = true.
Proof.
  intros.
  unfold ltb_bid in *.
  destruct x, y; auto.
Admitted.

(* Less or equal than *)
Definition leb_bid b b' :=
  orb (ltb_bid b b') (eqb_bid b b').

Definition le_bid b b' := (leb_bid b b' = true).

Lemma leb_bid_refl : forall a, leb_bid a a = true.
  intros.
  unfold leb_bid.
  destruct a
  ; simpl
  ; try (now rewrite String.eqb_refl)
  ; try ( rewrite Z.eqb_refl )
  ; try reflexivity.
  apply Bool.orb_true_r.
Qed.

Lemma leb_bid_true : forall b1 b2, leb_bid b1 b2 = true <-> le_bid b1 b2.
Proof.
  intros.
  unfold le_bid ; tauto.
Qed.

Lemma le_bid_refl : forall a, le_bid a a.
  intros.
  unfold le_bid.
  apply leb_bid_refl.
Qed.

Lemma le_bid_trans : forall b1 b2 b3, le_bid b1 b2 -> le_bid b2 b3 -> le_bid b1 b3.
Proof.
  intros.
  unfold le_bid, leb_bid in *.
  apply Bool.orb_true_iff in H,H0 ; apply Bool.orb_true_iff.
  rewrite ltb_bid_true in * ; rewrite eqb_bid_eq in *.
  intuition ; try (subst ; intuition).
  left ; eapply lt_bid_trans ; eassumption.
Qed.

Lemma lt_le : forall b1 b2, lt_bid b1 b2 -> le_bid b1 b2.
Proof.
  intros.
  unfold le_bid, leb_bid, lt_bid in *.
  now rewrite H.
Qed.

Lemma lt_bid_trans_le : forall b1 b2 b3, le_bid b1 b2 -> lt_bid b2 b3 -> lt_bid b1 b3.
Proof.
  intros.
  unfold le_bid, leb_bid in *.
  apply Bool.orb_true_iff in H ; destruct H as [H | H] ;
  try rewrite ltb_bid_true in * ; try (rewrite eqb_bid_eq in * ; subst).
  - eapply lt_bid_trans ; eassumption.
  - assumption.
Qed.

Lemma lt_bid_trans_le2 : forall b1 b2 b3, lt_bid b1 b2 -> le_bid b2 b3 -> lt_bid b1 b3.
Proof.
  intros.
  unfold le_bid, leb_bid in *.
  apply Bool.orb_true_iff in H0 ; destruct H0 as [H0 | H0] ;
  try rewrite ltb_bid_true in * ; try (rewrite eqb_bid_eq in * ; subst).
  - eapply lt_bid_trans ; eassumption.
  - assumption.
Qed.

(*NOTE probably need x and y to be Anon *)
Lemma not_le_lt : forall x y, leb_bid x y = false -> ltb_bid y x = true.
Proof.
  intros.
  unfold leb_bid in H.
  apply Bool.orb_false_elim in H ; destruct H.
Admitted.

(* Max and min for block_id *)

Definition max b b' := if (leb_bid b b') then b' else b.
Definition min b b' := if (leb_bid b b') then b else b'.

Fixpoint max_bid' (l : list block_id) b :=
  match l with
  | [] => b
  | h :: t => max_bid' t (max b h)
  end.

Fixpoint min_bid' (l : list block_id) b :=
  match l with
  | [] => b
  | h :: t => min_bid' t (min b h)
  end.

Definition max_bid (l : list block_id) :=
  max_bid' l (hd (Anon 0%Z) l).

Definition min_bid (l : list block_id) :=
  min_bid' l (hd (Anon 0%Z) l).

Lemma max_refl : forall x, max x x = x.
Proof.
  intros.
  unfold max ; now rewrite leb_bid_refl.
Qed.

Lemma min_refl : forall x, min x x = x.
Proof.
  intros.
  unfold min ; now rewrite leb_bid_refl.
Qed.

Lemma le_min_max' : forall l dmin dmax,
    le_bid dmin dmax -> le_bid (min_bid' l dmin) (max_bid' l dmax).
Proof.
  intros.
  induction l.
  - now simpl.
  - simpl.
    destruct ( leb_bid dmin a ) eqn:Emin, ( leb_bid dmax a ) eqn:Emax.
    + admit.
    + admit.
    + admit.
    + admit.
Admitted.


Lemma le_min_max : forall l, le_bid (min_bid l) (max_bid l).
Proof.
  intros.
  unfold min_bid, max_bid.
  induction l.
  - simpl ; apply le_bid_refl.
  - simpl ; rewrite min_refl, max_refl.
    apply le_min_max'.  apply le_bid_refl.
Qed.

Lemma max_bid'_cons : forall l x d,
    le_bid x d ->
    le_bid x (max_bid' l d).
Proof.
  induction l ; intros ; simpl.
  assumption.
  destruct (leb_bid d a) eqn:E ; unfold max ; rewrite E.
  - apply IHl.
    unfold leb_bid in E.
    apply Bool.orb_prop in E ; destruct E as [E | E].
    rewrite ltb_bid_true in E.
    eapply lt_bid_trans_le in H; try eassumption. now apply lt_le.
    now rewrite eqb_bid_eq in E ; subst.
  - now apply IHl.
Qed.

Corollary max_bid'_cons_refl : forall x l,
    le_bid x (max_bid' l x).
Proof.
  intros.
  apply max_bid'_cons.
  apply leb_bid_refl.
Qed.

Lemma max_bid_in : forall l,
    l <> [] ->
    In (max_bid l) l.
Proof.
  unfold max_bid.
  induction l ; try contradiction ; intros.
  destruct l.
  - simpl. rewrite max_refl. now left.
  - simpl in *.
    rewrite max_refl in *.
    unfold max in *.
    destruct (leb_bid a b) eqn:E.
    + right. apply IHl. admit. (* easy *)
    + assert (b::l <> []) by admit. apply IHl in H0.
      destruct H0. admit. admit.
Admitted.

Lemma le_bid_max_cons_eq : forall x l, le_bid x (max_bid (x::l)).
Proof.
  intros.
  cbn.
  rewrite max_refl.
  apply max_bid'_cons_refl.
Qed.

Lemma max_bid_app : forall l1 l2,
    max_bid (l1++l2) = max (max_bid l1) (max_bid l2).
Proof.
  intros.
  unfold max.
Admitted.

Lemma max_bid_app' : forall l1 l2,
    max_bid (l1++l2) = (max_bid l1) \/ max_bid (l1++l2) = (max_bid l2).
Proof.
  intros.
  rewrite max_bid_app.
  unfold max.
  destruct (leb_bid (max_bid l1) (max_bid l2)) eqn:E ; intuition.
Qed.

Lemma le_bid_max_trans : forall x y z,
    le_bid x y ->
    le_bid x (max z y).
Proof.
  intros.
  unfold max.
  destruct (leb_bid z y) eqn:E ; try assumption.
  apply not_le_lt in E.
  assert (lt_bid y z ) by (now unfold lt_bid) ; clear E.
  apply lt_le.
  eapply lt_bid_trans_le in H0 ; eassumption.
Admitted.


Theorem max_bid_spec : forall l,
    Forall (fun b => le_bid b (max_bid l)) l.
Proof.
  induction l ; intros.
  - apply Forall_nil.
  - apply Forall_cons.
    + apply le_bid_max_cons_eq.
    + rewrite Forall_forall in *.
      intros * IN ; apply IHl in IN.
      rewrite Util.list_cons_app.
      rewrite max_bid_app. cbn.
      rewrite max_refl.
      now apply le_bid_max_trans.
Qed.

Lemma max_bid_spec' : forall l max,
    (max_bid l) = max ->
    Forall (fun b => le_bid b max) l.
Proof.
  intros.
  rewrite <- H.
  apply max_bid_spec.
Qed.

Lemma non_nil : forall {T} (l : list T),
    (length l >= 1)%nat ->
    exists h t, l = h::t.
Proof.
  intros.
  induction l.
  simpl in H ; lia.
  eexists.
  eexists. reflexivity.
Qed.

Lemma max_bid_spec_nn : forall l max,
    (length l >= 1)%nat ->
    (max_bid l) = max ->
    Forall (fun b => le_bid b max) l.
Proof.
  intros * ? <-.
  now apply max_bid_spec'.
Qed.

Lemma min_bid_app :
  forall l1 l2 : list block_id,
    min_bid (l1 ++ l2) = min (min_bid l1) (min_bid l2).
Admitted.

Theorem min_bid_spec : forall l,
    Forall (fun b => le_bid (min_bid l) b) l.
Admitted.

Lemma min_bid_spec' : forall l m,
    (min_bid l) = m ->
    Forall (fun b => le_bid m b) l.
Proof.
  intros.
  rewrite <- H.
  apply min_bid_spec.
Qed.

Lemma min_bid_spec_nn : forall l min,
    (length l >= 1)%nat ->
    (min_bid l) = min ->
    Forall (fun b => le_bid min b) l.
Proof.
  intros * ? <-.
  apply min_bid_spec.
Admitted.

Lemma max_max_commmute :
  forall n1 n2 m1 m2, max (max n1 n2) (max m1 m2) = max (max n1 m1) (max n2 m2).
Proof.
  intros.
  unfold max.
  destruct (leb_bid n1 n2) eqn:LE_N
  ; destruct (leb_bid m1 m2) eqn:LE_M
  ; destruct (leb_bid n1 m1) eqn:LE_1
  ; destruct (leb_bid n2 m2) eqn:LE_2
  ; destruct (leb_bid m1 n2) eqn:M1_N2
  ; destruct (leb_bid m2 n1) eqn:M2_N1
  ; destruct (leb_bid n1 m2) eqn:N1_M2
  ; destruct (leb_bid n1 m1) eqn:N2_M1
  ; try (rewrite LE_M)
  ; try (rewrite LE_N)
  ; try (rewrite LE_1)
  ; try (rewrite LE_2)
  ; try reflexivity
  ; rewrite leb_bid_true in *
  ; admit.
Admitted.

Lemma min_min_commmute :
  forall n1 n2 m1 m2, min (min n1 n2) (min m1 m2) = min (min n1 m1) (min n2 m2).
Proof.
  intros.
  unfold min.
  destruct (leb_bid n1 n2) eqn:LE_N
  ; destruct (leb_bid m1 m2) eqn:LE_M
  ; destruct (leb_bid n1 m1) eqn:LE_1
  ; destruct (leb_bid n2 m2) eqn:LE_2
  ; destruct (leb_bid m1 n2) eqn:M1_N2
  ; destruct (leb_bid m2 n1) eqn:M2_N1
  ; destruct (leb_bid n1 m2) eqn:N1_M2
  ; destruct (leb_bid n1 m1) eqn:N2_M1
  ; try (rewrite LE_M)
  ; try (rewrite LE_N)
  ; try (rewrite LE_1)
  ; try (rewrite LE_2)
  ; try reflexivity
  ; rewrite leb_bid_true in *
  ; admit.
Admitted.


Definition mk_anon (n : nat) := Anon (Z.of_nat n).
Lemma neq_mk_anon : forall n1 n2, mk_anon n1 <> mk_anon n2 <-> n1 <> n2.
Proof.
  intros.
  unfold mk_anon.
  split ; intro.
  - intros ->. now destruct H.
  - apply inj_neq in H.
    unfold Zne in H.
    intro.
    injection H0.
    intro.
    rewrite H1 in H .
    contradiction.
Qed.

Definition name := mk_anon.
Lemma neq_name : forall n1 n2, name n1 <> name n2 <-> n1 <> n2.
Proof.
  intros.
  unfold name. now apply neq_mk_anon.
Qed.

Definition is_anon (b : block_id) : Prop :=
  exists n, b = Anon n.

Lemma is_anon_name : forall n, is_anon (name n).
Proof.
  intros.
  unfold name, mk_anon.
  unfold is_anon.
  now eexists.
Qed.

Definition next_anon (b : block_id) :=
  match b with
  | Name s => Name s
  | Raw n => Raw (n+1)%Z
  | Anon n => Anon (n+1)%Z
  end.

Lemma next_anon_name : forall n, next_anon (name n) = name (n+1).
Proof.
  intros.
  unfold next_anon, name, mk_anon.
  rewrite Nat2Z.inj_add.
  reflexivity.
Qed.

Lemma lt_bid_S : forall n m,
    lt_bid m (name n) -> lt_bid m (name (S n)).
Proof.
  intros.
  unfold name, mk_anon in *.
  unfold lt_bid, ltb_bid in *.
  destruct m ; auto.
  rewrite Nat2Z.inj_succ.
  rewrite Zaux.Zlt_bool_true ; auto.
  lia.
Qed.

Lemma lt_bid_next : forall b, is_anon b -> lt_bid b (next_anon b).
Proof.
  intros.
  unfold next_anon, is_anon in *.
  destruct H ; subst.
  unfold lt_bid.
  unfold ltb_bid.
  lia.
Qed.

Lemma name_neq : forall cb cb',
    cb <> cb' -> (name cb <> name cb').
Proof.
  intros. intro.
  unfold name,mk_anon in H0.
  injection H0 ; intro.
  rewrite Nat2Z.inj_iff in H1.
  subst. contradiction.
Qed.

Lemma lt_bid_name : forall (n n' : nat),
    (n < n')%nat -> lt_bid (name n) (name n').
Proof.
  intros.
  unfold lt_bid, name, mk_anon.
  simpl.
  lia.
Qed.

Lemma le_bid_name : forall (n n' : nat),
    (n <= n')%nat -> le_bid (name n) (name n').
Proof.
  intros.
  unfold le_bid, leb_bid, name, mk_anon.
  simpl.
  lia.
Qed.

Lemma max_name : forall n1 n2, max (name n1) (name n2) = name (Max.max n1 n2).
Proof.
Admitted.

Lemma min_name : forall n1 n2, min (name n1) (name n2) = name (Min.min n1 n2).
Proof.
Admitted.

Theorem ord_list : forall l f,
    lt_bid (max_bid l) f ->
    ~ In f l.
Proof.
  induction l as [| x l' Hl' ] ; intros.
  - apply in_nil.
  - (* pose proof max_bid_spec'. *)
    apply not_in_cons.
    split.
    + apply lt_bid_neq'. eapply lt_bid_trans_le ; try eassumption. apply max_bid'_cons_refl.
    + eapply Hl'.
Admitted.

Lemma eqv_dec_p_eq : forall b b' r,
    eqb_bid b b' = r <-> (if Eqv.eqv_dec_p b b' then true else false) = r.
  intros.
  destruct r eqn:R.
  - destruct (Eqv.eqv_dec_p b b') eqn:E.
    + unfold Eqv.eqv,eqv_raw_id in e ; subst.
      now rewrite eqb_bid_refl.
    + unfold Eqv.eqv,eqv_raw_id in n.
      rewrite eqb_bid_eq.
      split ; intros ; subst. contradiction. inversion H.
  - destruct (Eqv.eqv_dec_p b b') eqn:E.
    + unfold Eqv.eqv,eqv_raw_id in e ; subst.
      now rewrite eqb_bid_refl.
    + unfold Eqv.eqv,eqv_raw_id in n ; subst.
      rewrite eqb_bid_neq.
      split ; intros ; auto.
Qed.

Lemma eqv_dec_p_refl : forall (b : block_id),
    (if Eqv.eqv_dec_p b b then true else false) = true.
Proof.
  intros.
  destruct (Eqv.eqv_dec_p b b) ; auto.
  unfold Eqv.eqv,eqv_raw_id in n ; auto.
Qed.

Lemma eqv_dec_p_eq_true : forall {T} b b' (xT xF : T),
    eqb_bid b b' = true -> (if Eqv.eqv_dec_p b b' then xT else xF) = xT.
Proof.
  intros ; destruct (Eqv.eqv_dec_p b b') eqn:E.
  - reflexivity.
  - unfold Eqv.eqv,eqv_raw_id in n ; subst.
    rewrite eqb_bid_eq in H. now apply n in H.
Qed.

Lemma eqv_dec_p_eq_false : forall {T} b b' (xT xF : T),
    eqb_bid b b' = false -> (if Eqv.eqv_dec_p b b' then xT else xF) = xF.
Proof.
  intros ; destruct (Eqv.eqv_dec_p b b') eqn:E.
  - unfold Eqv.eqv,eqv_raw_id in e ; subst.
    rewrite eqb_bid_neq in H. contradiction.
  - reflexivity.
Qed.

(** Definition and lemmas for remove specitic to block_id*)
Fixpoint remove_bid (x : block_id) (l : list block_id) :=
  match l with
  | [] => []
  | h::t => if (eqb_bid x h) then remove_bid x t else h::(remove_bid x t)
  end.

Lemma remove_spec : forall a l, ~ In a (remove_bid a l).
Proof.
  induction l.
  - simpl ; auto.
  - simpl.
    destruct (eqb_bid a a0) eqn:E.
    + assumption.
    + apply not_in_cons. rewrite eqb_bid_neq in E.
      intuition.
Qed.

Lemma remove_ListRemove :
  forall b l, remove_bid b l = List.remove Eqv.eqv_dec_p b l.
Proof.
  intros.
  induction l ; try reflexivity.
  simpl.
  destruct (eqb_bid b a) eqn:E ;
    match goal with
    | |- context[if (_ ?b1 ?b2) then ?xT else ?xF] =>
        try apply (eqv_dec_p_eq_true b1 b2 xT xF) in E
        ; try apply (eqv_dec_p_eq_false b1 b2 xT xF) in E
    end ; setoid_rewrite E.
  - assumption.
  - now f_equal.
Qed.

Lemma in_remove : forall l x y, List.In x (remove_bid y l) -> List.In x l.
Proof. intros.
       rewrite remove_ListRemove in H
       ; apply in_remove in H.
       intuition.
Qed.

Ltac in_list_rem :=
  match goal with
  | h: List.In _ _  |- _ => apply in_remove in h
  end.

Lemma remove_disjoint : forall (x : block_id) (l1 l2 : list block_id),
    l1 ⊍ l2 -> (remove_bid x l1) ⊍ l2.
Proof.
  intros.
  induction l1.
  now simpl.
  simpl.
  destruct (eqb_bid x a).
  - apply IHl1. now apply list_disjoint_cons_left in H.
  - apply list_disjoint_cons_l_iff in H ; destruct H.
    apply list_disjoint_cons_l.
    now apply IHl1. assumption.
Qed.

Lemma remove_notin : forall a l, ~ In a l -> (remove_bid a l) = l.
Proof.
  intros.
  rewrite remove_ListRemove.
  now apply notin_remove.
Qed.

Lemma remove_disjoint_remove : forall (x : block_id) (l1 l2 : list block_id),
    (remove_bid x l1) ⊍ (remove_bid x l2) <->
(remove_bid x l1) ⊍ l2.
Proof.
  induction l2 ; intros ; split ; simpl ; intros
  ; try apply list_disjoint_nil_r
  ; destruct (eqb_bid x a) eqn:E
  ; try (rewrite eqb_bid_eq in E ; subst)
  ; try (rewrite eqb_bid_neq in E).
  - apply list_disjoint_cons_r.
    apply IHl2 ; assumption.
    apply remove_spec.
  - apply list_disjoint_sym in H
    ; apply list_disjoint_cons_l_iff in H
    ; destruct H
    ; apply list_disjoint_sym in H.
    apply list_disjoint_cons_r
    ; [ apply IHl2 |]
    ; assumption.
  - apply list_disjoint_sym, remove_disjoint
    ; apply list_disjoint_sym.
    now apply list_disjoint_cons_right in H.
  - apply list_disjoint_sym in H
    ; apply list_disjoint_cons_l_iff in H
    ; destruct H
    ; apply list_disjoint_sym in H.
    apply list_disjoint_cons_r
    ; [ apply IHl2 |]
    ; assumption.
Qed.

Lemma remove_app:
  forall (x : block_id) (l1 l2 : list block_id),
    remove_bid x (l1 ++ l2) = remove_bid x l1 ++ remove_bid x l2.
Proof.
  intros.
  rewrite !remove_ListRemove.
  apply remove_app.
Qed.

Lemma remove_no_repet :
  forall a l,
    list_norepet (a::l) -> (remove_bid a (a::l)) = l.
Proof.
  intros.
  simpl.
  rewrite eqb_bid_refl.
  pose proof (remove_spec a l).
  assert (~ In a l).
  {
     intro.
     rewrite Util.list_cons_app in H ; apply list_norepet_app in H
     ; destruct H as [_ [_ ?]].
     unfold list_disjoint in H.
     assert (In a [a]) by (apply in_cns ; intuition).
     eapply H in H2 ; [|eassumption] ; contradiction.
  }
  apply remove_notin in H1.
  assumption.
Qed.

Lemma length_remove_hd_no_repet :
  forall l d,
    list_norepet l ->
    length (remove_bid (hd d l) l) = ((length l)-1)%nat.
Proof.
  intros.
  induction l. now simpl.
  apply remove_no_repet in H.
  replace (hd d (a :: l)) with a by now simpl.
  rewrite H.
  simpl ; lia.
Qed.

Lemma list_norepet_remove : forall l a,
    list_norepet l ->
    list_norepet (remove_bid a l).
Proof.
  intros.
  induction l ; try auto.
  simpl.
  destruct (eqb_bid a a0) ;
    [| apply list_norepet_cons ;
       [intro
        ; apply CFGC_Utils.in_remove in H0
        ; now inversion H|]]
  ; apply IHl
  ; rewrite list_cons_app in H
  ; eapply list_norepet_append_right
  ; eassumption.
Qed.


(* Misc lemmas related to vellvm *)

Lemma find_block_none_singleton :
  forall c term phis comm b b' , b<>b' <->
find_block
   (convert_typ []
                [{|
                      blk_id := b;
                   blk_phis := phis;
                   blk_code := c;
                   blk_term := term;
                   blk_comments := comm
                   |}]) b' = None.
Proof.
  intros.
  split; intros.
  - apply find_block_not_in_inputs.
    simpl; intuition.
  - simpl in H.
    unfold endo, Endo_id in H.
    destruct (if Eqv.eqv_dec_p b b' then true else false) eqn:E.
    + discriminate.
    + now rewrite <- eqv_dec_p_eq in E ; rewrite <- eqb_bid_neq.
Qed.



(* The following three are copied from vellvm,
   but with heterogeneous types T and T' for use with convert_typ *)

Lemma find_block_map_some' :
  forall {T T'} (f : block T -> block T') G b bk,
    (forall bk, blk_id (f bk) = blk_id bk) ->
    find_block G b = Some bk ->
    find_block (List.map f G) b = Some (f bk).
Proof.
  intros * ID; induction G as [| hd G IH]; intros FIND ; [inv FIND |].
  cbn in *.
  rewrite ID.
  break_match_goal; break_match_hyp; intuition.
  inv FIND; auto.
Qed.

Lemma find_block_map_none' :
  forall {T T'} (f : block T -> block T') G b,
    (forall bk, blk_id (f bk) = blk_id bk) ->
    find_block G b = None ->
    find_block (List.map f G) b = None.
Proof.
  intros * ID; induction G as [| hd G IH]; intros FIND; [reflexivity |].
  cbn in *.
  rewrite ID.
  break_match_goal; break_match_hyp; intuition.
  inv FIND; auto.
Qed.

Lemma find_block_map' :
  forall {T T'} (f : block T -> block T') G b,
    (forall bk, blk_id (f bk) = blk_id bk) ->
    find_block (List.map f G) b = option_map f (find_block G b).
Proof.
  intros.
  destruct (find_block G b) eqn:EQ.
  eapply find_block_map_some' in EQ; eauto.
  eapply find_block_map_none' in EQ; eauto.
Qed.

Lemma find_app :
  forall {A} (l1 l2 : list A) f x,
    List.find f (l1 ++ l2) = Some x ->
    List.find f l1 = Some x \/ List.find f l2 = Some x.
Proof.
  intros.
  induction l1.
  - now right.
  - simpl in *.
    break_match; tauto.
Qed.



Lemma find_block_app_wf :
  forall {T : Set} (x : block_id) [b : block T] (bs1 bs2 : ocfg T),
    wf_ocfg_bid (bs1 ++ bs2)%list ->
    find_block (bs1 ++ bs2) x = Some b ->
    find_block bs1 x = Some b \/ find_block bs2 x = Some b .
Proof.
  intros.
  unfold find_block in H0.
  now apply find_app.
Qed.

Lemma outputs_successors : forall {typ} (cfg : ocfg typ) o,
    List.In o (outputs cfg) ->
    exists bk, List.In bk cfg /\ List.In o (successors bk).
Proof.
  induction cfg; intros.
  - destruct H.
  - cbn in H. rewrite outputs_acc in H.
    apply List.in_app_iff in H. destruct H.
    + exists a. simpl. tauto.
    + apply IHcfg in H.
      destruct H. exists x.
      simpl. tauto.
Qed.

Lemma successors_outputs : forall {typ} (cfg : ocfg typ) o bk,
    List.In bk cfg ->
    List.In o (successors bk) ->
    List.In o (outputs cfg).
Proof.
  induction cfg; intros.
  - destruct H.
  - cbn. rewrite outputs_acc.
    apply List.in_app_iff.
    destruct H.
    + left. now subst a.
    + right. apply IHcfg in H0; assumption.
Qed.

Lemma convert_typ_inputs : forall bk,
    inputs (convert_typ nil bk) = inputs bk.
Proof.
  intros.
  unfold inputs, convert_typ, ConvertTyp_list, tfmap, TFunctor_list'.
  rewrite List.map_map.
  reflexivity.
Qed.

Lemma convert_typ_successors : forall (bk : block typ),
    successors (convert_typ nil bk) = successors bk.
Proof.
  intros.
  apply convert_typ_terminator_outputs.
Qed.

Notation conv := (convert_typ []).

Lemma find_block_some_conv :
  forall g bid bk,
    find_block g bid = Some bk ->
    find_block (conv g) bid = Some (conv bk).
Proof.
  intros.
  unfold conv in *.
  unfold ConvertTyp_list, tfmap, TFunctor_list'.
  apply (find_block_map_some' _ g bid bk) ; [|assumption].
  apply blk_id_convert_typ.
Qed.

Lemma find_block_none_conv :
  forall g bid,
    find_block g bid = None ->
    find_block (conv g) bid = None.
Proof.
  intros.
  unfold conv in *.
  unfold ConvertTyp_list, tfmap, TFunctor_list'.
  apply (find_block_map_none' _ g bid) ; [|assumption].
  apply blk_id_convert_typ.
Qed.


Ltac find_block_conv :=
  match goal with
  | h:context[ find_block _ _ = None ] |- _ =>
      apply find_block_none_conv in h
  | h:context[ find_block _ _ = Some _ ] |- _ =>
      apply find_block_some_conv in h
  end.


Lemma no_reentrance_conv :
  forall g1 g2,
    no_reentrance g1 g2 <-> no_reentrance (conv g1) (conv g2).
Proof.
  intros.
  unfold no_reentrance.
  now rewrite convert_typ_outputs, convert_typ_inputs.
Qed.

Lemma no_duplicate_bid_conv :
  forall g1 g2,
    no_duplicate_bid g1 g2 <-> no_duplicate_bid (conv g1) (conv g2).
Proof.
  intros.
  unfold no_duplicate_bid.
  now rewrite 2 convert_typ_inputs.
Qed.

Lemma independent_flows_conv :
  forall g1 g2,
    independent_flows g1 g2 <-> independent_flows (conv g1) (conv g2).
Proof.
  intros.
  unfold independent_flows.
  rewrite <- 2 no_reentrance_conv.
  now rewrite no_duplicate_bid_conv.
Qed.

Lemma inputs_app : forall {T} (g1 g2 : ocfg T), inputs (g1++g2) = inputs g1 ++ inputs g2.
Proof.
  intros.
  unfold inputs.
  apply Coqlib.list_append_map.
Qed.

Lemma typ_to_dtyp_pair :
  forall (t : typ) (e : exp typ),
    (typ_to_dtyp [] t, convert_typ [] e) = tfmap (typ_to_dtyp []) (t, e).
Proof.
  intros.
  now unfold tfmap, TFunctor_texp, convert_typ, ConvertTyp_exp, tfmap.
Qed.
