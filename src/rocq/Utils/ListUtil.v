From Stdlib Require Import
  List Lia Program Recdef.

From ITree Require Import
     Basics.Monad.
Import Monads.

From Vellvm Require Import
  Numeric.Rocqlib.

Import ListNotations.
Import MonadNotation.
Open Scope monad.
Set Implicit Arguments.
Set Contextual Implicit.

(** * Collection of misc definitions and lemmas over lists *)

(** *** Standard lemmas over standard lists *)
Section Standard.
  
  Lemma In_cons_dec :
    forall {A} (a x : A) xs,
      (forall (x y : A), {x = y} + {x <> y}) ->
      In a (x :: xs) -> {a = x} + {In a xs}.
  Proof.
    intros A a x xs EQDEC H.
    destruct (EQDEC a x); subst.
    left. reflexivity.
    right.
    pose proof H as HIn.
    pose proof In_dec EQDEC a xs as [IN | NIN].
    auto.
    pose proof not_in_cons.
    assert (a <> x /\ ~ In a xs).
    auto.
    apply H0 in H1.
    contradiction.
  Qed.

  Lemma fold_right_forall : forall {A} (P : A -> Prop) (l:list A),
      List.fold_right (fun x b => P x /\ b) True l <-> Forall P l.
  Proof.
    intros A P l.
    induction l; split; intros; simpl in *; auto.
    - simpl in H.
      destruct H as [PA H].
      constructor; auto.
      apply IHl; auto.
    - inversion H. subst.
      split; auto.
      apply IHl; auto.
  Qed.      

  Lemma list_cons_app :
    forall {A} (x : A) l, x :: l = [x] ++ l.
  Proof using.
    cbn. reflexivity.
  Qed.

  Definition map_In {A B : Type} (l : list A) (f : forall (x : A), In x l -> B) : list B.
  Proof.
    induction l.
    - exact [].
    - refine (f a _ :: IHl _).
      + simpl. auto.
      + intros x H. apply (f x). simpl. auto.
  Defined.

  Lemma not_in_app_l : forall {A} (l1 l2 : list A) x,
      not (In x (l1 ++ l2)) ->
      not (In x l1).
  Proof using.
    intros * NIN abs; eapply NIN, in_or_app; auto.
  Qed.

  Lemma not_in_app_r : forall {A} (l1 l2 : list A) x,
      not (In x (l1 ++ l2)) ->
      not (In x l2).
  Proof using.
    intros * NIN abs; eapply NIN, in_or_app; auto.
  Qed.

  Lemma find_none_app:
    forall {A} (l1 l2 : list A) pred,
      find pred l1 = None ->
      find pred (l1 ++ l2) = find pred l2.
  Proof using.
    induction l1; intros l2 pred FIND.
    - reflexivity.
    - cbn in FIND; cbn.
      destruct (pred a); inversion FIND.
      auto.
  Qed.

  Lemma find_some_app:
    forall {A} (l1 l2 : list A) a pred,
      find pred l1 = Some a ->
      find pred (l1 ++ l2) = Some a.
  Proof using.
    induction l1 as [|x l1']; intros l2 a pred FIND.
    - inversion FIND.
    - cbn in FIND. destruct (pred x) eqn:PRED.
      + inversion FIND; cbn; subst.
        rewrite PRED. reflexivity.
      + cbn. rewrite PRED.
        auto.
  Qed.

  Definition option_pick_large {A} (leq : A -> A -> bool) (a b : option A) : option A
    := match a, b with
       | Some x, Some y =>
           if leq x y then b else a
       | Some a, _      => Some a
       | _, Some b      => Some b
       | None, None     => None
       end.

  Definition maximumByOpt {A} (leq : A -> A -> bool) (l : list A) : option A :=
    fold_left (option_pick_large leq) (map Some l) None.

  Definition rev_tail_rec {A} (xs : list A)
    := fold_left (fun acc x => x :: acc) xs [].

  Lemma list_sum_map :
    forall {X} (f : X -> nat) x xs,
      In x xs ->
      (list_sum (map f xs) >= f x)%nat.
  Proof.
    induction xs; intros In; [contradiction|].
    destruct In; subst.
    - cbn. lia.
    - cbn. specialize (IHxs H).
      unfold list_sum in IHxs.
      lia.
  Qed.

  Lemma forall_repeat_true:
    forall A (f : A -> Prop) n x, f x -> Forall (fun y : A => f y) (repeat x n).
  Proof.
    intros. induction n. cbn. constructor.
    constructor. auto. cbn. apply IHn.
  Qed.

  Fixpoint Zseq (start : Z) (len : nat) : list Z :=
    match len with
    | O => []
    | S x => start :: Zseq (Z.succ start) x
    end.

  Lemma Zseq_succ : forall off (n : N),
      Zseq off (N.to_nat (N.succ n)) = off :: Zseq (Z.succ off) (N.to_nat n).
  Proof.
    intros off n.
    rewrite Nnat.N2Nat.inj_succ; auto.
  Qed.
  
  Lemma Zseq_length :
    forall len off,
      Datatypes.length (Zseq off len) = len.
  Proof.
    induction len; intros; auto.
    cbn.
    congruence.
  Qed.
  
  Fixpoint Nseq (start : N) (len : nat) : list N :=
    match len with
    | O => []
    | S x => start :: Nseq (N.succ start) x
    end.
  
  Fixpoint drop {A} (n : N) (l : list A) : list A
    := match l with
       | [] => []
       | (x::xs) =>
           if N.eqb 0 n
           then l
           else drop (N.pred n) xs
       end.

  Fixpoint take {A} (n : N) (l : list A) : list A
    := match l with
       | [] => []
       | (x::xs) =>
           if N.eqb 0 n
           then []
           else x :: take (N.pred n) xs
       end.
  
  Definition repeatN {X} (n : N) (x : X) : list X
    := N.recursion
         []
         (fun n xs => x :: xs)
         n.

  Lemma drop_length_le :
    forall {A} (xs : list A) n,
      (length (drop n xs) <= length xs)%nat.
  Proof.
    intros A xs.
    induction xs;
      intros n;
      cbn; [lia|].
    destruct n; cbn; [lia|].
    rewrite IHxs.
    lia.
  Qed.

  Lemma drop_length_lt :
    forall {A} (xs : list A) n,
      (n >= 1)%N ->
      xs <> [] ->
      (length (drop n xs) < length xs)%nat.
  Proof.
    intros A xs.
    induction xs;
      intros n N XS;
      cbn; [contradiction|].
    destruct n; cbn; [lia|].
    pose proof drop_length_le xs (Pos.pred_N p).
    lia.
  Qed.

  Function split_every_pos {A} (n : positive) (xs : list A) { measure length xs }: list (list A)
    := match xs with
       | [] => []
       | (_::_) =>
           @take A (Npos n) xs :: split_every_pos n (@drop A (Npos n)%N xs)
       end.
  Proof.
    intros. apply drop_length_lt. lia.
    intros D. inversion D.
  Defined.

  (* Like split_every, but default to the empty list in the n=0 case *)
  Definition split_every_nil {A} (n : N) (xs : list A) : list (list A)
    := match n with
       | N0 => []
       | Npos n =>
           split_every_pos n xs
       end.

  Fixpoint zipWith {A B C} (f : A -> B -> C) (xs : list A) (ys : list B) : list C
    := match xs, ys with
       | [], _        => []
       | _, []        => []
       | a::xs', b::ys' => f a b :: zipWith f xs' ys'
       end.

  Definition zip {X Y} (xs : list X) (ys : list Y) := zipWith (fun a b => (a, b)) xs ys.

End Standard.

(** *** Alternate [find] and [filter] where the predicate is replaced by a partial map *)
Section FINDOPTION.
  Context {A B:Type}.

  Fixpoint find_option (f: A -> option B) (l:list A) : option B :=
    match l with
    | [] => None
    | x::xs => match f x with
             | None => find_option f xs
             | Some b => Some b
             end
    end.

  Fixpoint filter_option (f : A -> option B) (l:list A) : list B :=
    match l with
    | [] => []
    | x::xs => match f x with
             | None => filter_option f xs
             | Some y => y :: filter_option f xs
             end
    end.

  Definition map_option (f : A -> option B) : list A -> option (list B) :=
    fix loop l :=
      match l with
      | [] => Some []
      | a::l' =>
          match f a, loop l' with
          | Some b, Some bl => Some (b::bl)
          | _, _ => None
          end
      end.

End FINDOPTION.

(** *** Interactions between monadic computations and lists *)
Section monad.
  Variable m : Type -> Type.
  Variable M : Monad m.

  Fixpoint monad_fold_right {A B} (f : B -> A -> m B) (l:list A) (b : B) : m B :=
    match l with
    | [] => ret b
    | x::xs =>
        r <- monad_fold_right f xs b ;;
        f r x
    end.

  Definition monad_app_fst {A B C} (f : A -> m C) (p:A * B) : m (C * B)%type :=
    let '(x,y) := p in
    z <- f x ;;
    ret (z,y).

  Definition monad_app_snd {A B C} (f : B -> m C) (p:A * B) : m (A * C)%type :=
    let '(x,y) := p in
    z <- f y ;;
    ret (x,z).

  Definition map_monad {A B} (f:A -> m B) : list A -> m (list B) :=
    fix loop l :=
      match l with
      | [] => ret []
      | a::l' =>
          b <- f a ;;
          bs <- loop l' ;;
          ret (b::bs)
      end.

  Definition map_monad_ {A B}
    (f: A -> m B) (l: list A): m unit :=
    map_monad f l;; ret tt.

  Definition sequence {a} (ms : list (m a)) : m (list a)
    := map_monad id ms.

  Lemma sequence_cons :
    forall {a} (ma : m a) (mas : list (m a)),
      sequence (ma :: mas) =
        a <- ma;;
        rest <- sequence mas;;
        ret (a :: rest).
  Proof using.
    intros a ma mas.
    unfold sequence.
    cbn.
    unfold id.
    reflexivity.
  Qed.

  Fixpoint foldM {a b} (f : b -> a -> m b ) (acc : b) (l : list a) : m b
    := match l with
       | [] => ret acc
       | (x :: xs) =>
           b <- f acc x;;
           foldM f b xs
       end.

  Definition repeatM {A} (n : nat) (ma : m A) : m (list A)
    := sequence (repeat ma n).

  (* Helper for looping 2 argument evaluation over vectors, producing a vector *)

  Definition vec_loop {A : Type}
    (f : A -> A -> m A)
    (elts : list (A * A)) : m (list A) :=
    monad_fold_right (fun acc '(e1, e2) =>
                        val <- f e1 e2 ;;
                        ret (val :: acc)
      ) elts [].

End monad.
Arguments monad_fold_right {_ _ _ _}.
Arguments monad_app_fst {_ _ _ _ _}.
Arguments monad_app_snd {_ _ _ _ _}.
Arguments map_monad {_ _ _ _}.
Arguments map_monad_ {_ _ _ _}.
Arguments sequence {_ _ _}.
Arguments foldM {_ _ _ _}.
Arguments vec_loop {_ _ _}.
Definition repeatMN {A m} `{Monad m} (n : N) (ma : m A) : m (list A)
  := sequence (repeatN n ma).

(** *** Better behaved version of Forall that can be used in recursive functions *)
Section FORALL.
  
  Definition FORALL {A} (P : A -> Prop) (l : list A) :=
    List.fold_right (fun x b => P x /\ b) True l.

  Lemma FORALL_forall : forall {A} (P : A -> Prop) (l:list A),
      FORALL P l <-> Forall P l.
  Proof.
    intros. rewrite <- fold_right_forall. reflexivity.
  Qed.

  Lemma FORALL_dec : forall {A} (P : A -> Prop) (l:list A)
                       (H : forall a, In a l -> {P a} + {~ P a}),
      {FORALL P l} + {~ FORALL P l}.
  Proof.
    intros A P l.
    induction l; intros HD.
    - simpl. auto.
    - simpl.
      assert (In a (a::l)). {  constructor; reflexivity. }
      apply HD in H.
      assert (forall a, In a l -> {P a} + {~ P a}) as HX.
      { intros a0 HI. apply HD. right. assumption. }
      destruct H.
      destruct (IHl HX).
      + left; auto.
      + right. intros C. apply n. intuition auto with *.
      + right. intros C. apply n. intuition auto with *.
  Qed.

End FORALL.

Section DISJOINT.

  Infix "⊍" := list_disjoint (at level 60).

  Lemma list_disjoint_nil_l : forall {A} (l : list A),
      [] ⊍ l.
  Proof using.
    repeat intro; intuition.
  Qed.

  Lemma list_disjoint_nil_r : forall {A} (l : list A),
      l ⊍ [].
  Proof using.
    repeat intro; intuition.
  Qed.

  Lemma list_disjoint_cons_l_iff:
    forall (A: Type) (a: A) (l1 l2: list A),
      (a :: l1) ⊍ l2 <->
      (l1 ⊍ l2 /\ not (In a l2)).
  Proof using.
    split; intros H.
    - split; [eapply list_disjoint_cons_left; eauto |].
      intros abs; eapply H; eauto; constructor; reflexivity.
    - apply list_disjoint_cons_l; apply H.
  Qed.

  Lemma list_disjoint_singleton_left : forall {A} (l : list A) (x : A),
    [x] ⊍ l <-> not (In x l).
  Proof using.
    unfold list_disjoint; intros; split; intro H.
    intros * IN; eapply H in IN; [|left; eauto]; intuition.
    intros ? ? [] IN abs; [subst; intuition | intuition].
  Qed.

  Lemma list_disjoint_singleton_right : forall {A} (l : list A) (x : A),
      l ⊍ [x] <-> not (In x l).
  Proof using.
    unfold list_disjoint; intros; split; intro H.
    intros * IN; eapply H in IN; [|left; eauto]; intuition.
    intros ? ? IN [] abs; [subst; intuition | intuition].
  Qed.

  Lemma list_disjoint_app_l : forall {A} (l1 l2 l3 : list A),
      (l1 ++ l2) ⊍ l3 <->
      (l1 ⊍ l3 /\ l2 ⊍ l3).
  Proof using.
    intros; induction l1 as [| hd l1 IH]; cbn.
    - split; intros H.
      + split; auto using list_disjoint_nil_l.
      + apply H.
    - split; intros H.
      + apply list_disjoint_cons_l_iff in H as [H1 H2].
        apply IH in H1 as [? ?].
        split; auto.
        apply list_disjoint_cons_l; auto.
      + destruct H as [H1 H2].
        apply list_disjoint_cons_l_iff in H1 as [? ?].
        eapply list_disjoint_cons_l.
        apply IH; auto.
        auto.
  Qed.

  Lemma list_disjoint_app_r : forall {A} (l1 l2 l3 : list A),
      l1 ⊍ (l2 ++ l3) <->
      (l1 ⊍ l2 /\ l1 ⊍ l3).
  Proof using.
    intros; induction l1 as [| hd l1 IH]; cbn.
    - split; intros H.
      + split; auto using list_disjoint_nil_l.
      + auto using list_disjoint_nil_l.
    - split; intros H.
      + apply list_disjoint_cons_l_iff in H as [H1 H2].
        apply IH in H1 as [? ?].
        split.
        apply list_disjoint_cons_l; auto.
        eapply not_in_app_l; eauto.
        apply list_disjoint_cons_l; auto.
        eapply not_in_app_r; eauto.
      + destruct H as [H1 H2].
        apply list_disjoint_cons_l_iff in H1 as [? ?].
        apply list_disjoint_cons_l_iff in H2 as [? ?].
        eapply list_disjoint_cons_l.
        apply IH; auto.
        intros abs; apply in_app_or in abs as [|]; eauto.
  Qed.

  Lemma list_disjoint_singletons : forall {A} (x y : A),
      [x] ⊍ [y] <-> x <> y.
  Proof using.
    unfold list_disjoint; intros; split; intro H.
    apply H; constructor; auto.
    intros ? ? [] []; subst; auto.
  Qed.

  Lemma Forall_disjoint :
    forall {A} (l1 l2 : list A) (P1 P2 : A -> Prop),
      Forall P1 l1 ->
      Forall P2 l2 ->
      (forall x, P1 x -> ~(P2 x)) ->
      l1 ⊍ l2.
  Proof using.
    induction l1;
      intros l2 P1 P2 L1 L2 P1NP2.
    - intros ? ? CONTRA. inversion CONTRA.
    - apply Rocqlib.list_disjoint_cons_l.
      + eapply IHl1; eauto using Forall_inv_tail.
      + apply Forall_inv in L1.
        apply P1NP2 in L1.
        intros IN.
        eapply Forall_forall in L2; eauto.
  Qed.

End DISJOINT.
#[global] Infix "⊍" := list_disjoint (at level 60).
