(* begin hide *)
From Coq Require Import
     Arith
     Lia.

(* Fake dependency due to [eutt_iter'']. To remove once the lemma is moved to the itree library *)
From Vellvm Require Import
     Utils.Tactics
     Utils.PropT.

From ITree Require Import
     ITree
     Eq.Eqit.

Set Implicit Arguments.
Set Strict Implicit.
Local Open Scope nat_scope.

Import ITreeNotations.
Local Open Scope itree.

(* end hide *)

(** * tfor: a bounded loop iterator for itrees *)

Section TFor.

  (* The combinator [tfor body from to x0] simply sequences the computation:
     x1 <- body from x0;;
     x2 <- body (S from) x1;;
     ...
     body (to - 1) x_{to-from-1}

     i.e. it informally corresponds to:

     acc <- x0; 
     for i = from, i < to, i++ do
         acc <- body i acc
     return acc
   *)

  Definition tfor {E X} (body : nat -> X -> itree E X) (from to : nat) : X -> itree E X :=
    fun x => ITree.iter (fun '(p,x) =>
                        if Nat.eqb p to
                        then Ret (inr x)
                        else
                          y <- (body p x);; Ret (inl (S p,y))
                     ) (from,x).

  (* [tfor] excludes the upper bound, hence [tfor body k k] does nothing *)
  Lemma tfor_0: forall {E A} k (body : nat -> A -> itree E A) a0,
      tfor body k k a0 ≈ Ret a0.
  Proof using.
    intros; unfold tfor; cbn.
    unfold iter, CategoryKleisli.Iter_Kleisli, Basics.iter, MonadIter_itree.
    rewrite unfold_iter, Nat.eqb_refl, bind_ret_l.
    reflexivity.
  Qed.

  (* One step unrolling of the combinator *)
  Lemma tfor_unroll: forall {E A} i j (body : nat -> A -> itree E A) a0,
      i < j ->
      tfor body i j a0 ≈
           a <- body i a0;; tfor body (S i) j a.
  Proof using.
    intros; unfold tfor; cbn.
    unfold iter, CategoryKleisli.Iter_Kleisli, Basics.iter, MonadIter_itree.
    rewrite unfold_iter at 1.
    pose proof Nat.eqb_neq i j as [_ EQ].
    rewrite EQ; try lia.
    rewrite bind_bind.
    apply eutt_eq_bind; intros ?; rewrite bind_ret_l, tau_eutt.
    reflexivity.
  Qed.

  (* We can always split a [tfor] into two sequential ones *)
  Lemma tfor_split: forall {E A} (body : nat -> A -> itree E A) i j k a0,
      i <= j ->
      j <= k ->
      tfor body i k a0 ≈
           a <- tfor body i j a0;; tfor body j k a.
  Proof using.
    intros * LE1 LE2.
    remember (j - i) as p; revert a0 i LE1 Heqp.
    induction p as [| p IH]; intros ? ? LE1 EQ.
    - replace i with j by lia.
      rewrite tfor_0, bind_ret_l.
      reflexivity.
    - rewrite tfor_unroll; [| lia].
      rewrite tfor_unroll; [| lia].
      rewrite bind_bind.
      apply eutt_eq_bind; intros ?.
      eapply IH; lia.
  Qed.

  (* We can substitute bodies under a [tfor] assuming that they are equivalent at all points.
     TODO: various stronger induction principles can be provided:
     - obviously restricting the range of indexes to the one iterated over
     - using a provided invariant constraining the accumulators.
   *)
  Lemma eutt_tfor: forall {E A} (body body' : nat -> A -> itree E A) i j a0,
      (forall k i, body i k ≈ body' i k) ->
      (tfor body i j a0) ≈ (tfor body' i j a0).
  Proof using.
    intros.
    unfold tfor, iter, CategoryKleisli.Iter_Kleisli, Basics.iter, MonadIter_itree.
    eapply KTreeFacts.eutt_iter.
    intros [].
    break_match_goal.
    reflexivity.
    cbn.
    rewrite H.
    reflexivity.
  Qed.

  (* If the body does not depend on the index, we can re-index freely the
     bounds we iterate over *)
  Lemma tfor_ss : forall {E A} i j (body : nat -> A -> itree E A) a0,
      (forall x i j, body i x ≈ body j x) ->
      i <= j ->
      tfor body (S i) (S j) a0 ≈ tfor body i j a0.
  Proof using.
    intros; unfold tfor; cbn.
    unfold iter, CategoryKleisli.Iter_Kleisli, Basics.iter, MonadIter_itree.
    apply eutt_iter'' with (RI1:=fun '(a,x) '(b, y) => a = S b /\ x = y) (RI2:=fun '(a,x) '(b, y) => a = S b /\ x = y); auto.
    intros [j1 acc1] [j2 acc2] H1.
    destruct H1. subst.
    cbn.
    pose proof (Nat.eq_dec j2 j) as [EQ | NEQ].

    - subst. rewrite Nat.eqb_refl.
      apply eutt_Ret.
      constructor; auto.
    -
      apply Nat.eqb_neq in NEQ.
      rewrite NEQ.
      eapply eutt_clo_bind.
      rewrite H.
      reflexivity.
      intros; subst.
      apply eutt_Ret.
      constructor; auto.
  Qed.


  Lemma tfor_ss_dep : forall {E A} i j (body body' : nat -> A -> itree E A) a0,
      (forall x i, body' (S i) x ≈ body i x) ->
      i <= j ->
      tfor body' (S i) (S j) a0 ≈ tfor body i j a0.
  Proof using.
    intros; unfold tfor; cbn.
    unfold iter, CategoryKleisli.Iter_Kleisli, Basics.iter, MonadIter_itree.
    eapply eutt_iter'' with
        (RI1:=fun '(a,x) '(b, y) => a = S b /\ x = y) (RI2:=fun '(a,x) '(b, y) => a = S b /\ x = y); auto.
    intros [j1 acc1] [j2 acc2] H1.
    destruct H1. subst.
    cbn.
    destruct (Nat.eq_dec j2 j) as [EQ | NEQ].
    - subst. cbn. rewrite Nat.eqb_refl.
      apply eutt_Ret.
      constructor; auto.
    - apply Nat.eqb_neq in NEQ.
      rewrite NEQ.
      eapply eutt_clo_bind.
      rewrite H.
      reflexivity.
      intros; subst.
      apply eutt_Ret.
      constructor; auto.
  Qed.

  (* If the body does not depend on the index, we can unroll to the left
     while chipping at the upper bound *)
  Lemma tfor_unroll_down: forall {E A} i j (body : nat -> A -> itree E A) a0,
      i < S j ->
      (forall x i j, body i x ≈ body j x) ->
      tfor body i (S j) a0 ≈
      a <- body i a0;; tfor body i j a.
  Proof using.
    intros E A i j. revert E A i.
    induction j; intros E A i body a0 H H0.
    - rewrite tfor_unroll; auto.
      eapply eutt_clo_bind; [reflexivity|].
      intros u1 u2 H1.
      subst.

      assert (i = 0) by lia; subst.
      repeat rewrite tfor_0.
      reflexivity.
    - rewrite tfor_unroll; auto.
      eapply eutt_clo_bind; [reflexivity|].
      intros u1 u2 H1.
      subst.

      assert (i <= S j) by lia.
      apply le_lt_eq_dec in H1.
      destruct H1.
      + rewrite IHj; [|lia|auto].
        rewrite tfor_unroll; [|lia].
        eapply eutt_clo_bind.
        erewrite H0; reflexivity.
        intros; subst.
        do 2 (rewrite tfor_ss; auto); [|lia].
        reflexivity.
      + subst.
        repeat rewrite tfor_0.
        reflexivity.
  Qed.

End TFor.
