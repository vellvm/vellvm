From Stdlib Require Import
  List Lia Program Recdef.

From ITree Require Import
     Basics.Monad Basics.HeterogeneousRelations.
Import Monads.

From Vellvm Require Import
  Utils.Tactics
  Numeric.Rocqlib.

Import ListNotations.
Import MonadNotation.
Open Scope monad.
Set Implicit Arguments.
Set Contextual Implicit.

Module N.
  (* Standard library things in [N] rather than [nat] *)
  
  Fixpoint length {A} (l : list A) : N :=
    match l with
    | [] => 0
    | _ :: l => 1 + length l
    end.
End N.
  
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

Section Forall2.

  Lemma Forall2_repeat {A B} (R : A -> B -> Prop) a b n :
    R a b -> Forall2 R (repeat a n) (repeat b n).
  Proof.
    induction n; cbn; intros; constructor; auto.
  Qed.

  Lemma Forall2_diag {A} P (l : list A):
    Forall2 P l l <-> Forall (fun a => P a a) l.
  Proof.
    split; intros HF.
    - revert HF; induction l as [| x l IH]; cbn; auto.
      intros HF; inv HF.
      constructor; auto.
    - revert HF; induction l as [| x l IH]; cbn; auto.
      intros HF; inv HF.
      constructor; auto.
  Qed.

  (* Pairwise-related lists combine to [prod_rel]-related pair lists. *)
  Lemma Forall2_combine {A1 A2 B1 B2} (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop) :
    forall l1 l2 k1 k2,
      Forall2 RA l1 l2 -> Forall2 RB k1 k2 ->
      Forall2 (prod_rel RA RB) (combine l1 k1) (combine l2 k2).
  Proof.
    intros l1 l2 k1 k2 F; revert k1 k2; induction F; cbn; intros k1 k2 FK; auto.
    destruct FK; cbn; auto.
  Qed.

  Lemma Forall2_length_N {A B} (R : A -> B -> Prop) :
    forall l1 l2, Forall2 R l1 l2 -> N.length l1 = N.length l2.
  Proof.
    intros l1 l2 F; induction F; cbn; auto.
    now rewrite IHF.
  Qed.

  Lemma Forall2_map2 {A B1 B2} (R : B1 -> B2 -> Prop) (f : A -> B1) (g : A -> B2) :
    forall l,
      (forall x, In x l -> R (f x) (g x)) ->
      Forall2 R (map f l) (map g l).
  Proof.
    induction l; intros H; cbn; constructor.
    - apply H; now left.
    - apply IHl; intros; apply H; now right.
  Qed.

    (* [Forall2] plumbing for the byte-list surgery of deserialization. *)

  Lemma Forall2_take {A B} (R : A -> B -> Prop) :
    forall l l', Forall2 R l l' -> forall n, Forall2 R (take n l) (take n l').
  Proof.
    intros l l' F; induction F; intros n; cbn; auto.
    break_match_goal; constructor; auto.
  Qed.

  Lemma Forall2_drop {A B} (R : A -> B -> Prop) :
    forall l l', Forall2 R l l' -> forall n, Forall2 R (drop n l) (drop n l').
  Proof.
    intros l l' F; induction F; intros n; cbn; auto.
    break_match_goal; [constructor; auto | auto].
  Qed.

  Lemma Forall2_repeatN {A B} (R : A -> B -> Prop) (a : A) (b : B) :
    R a b -> forall n, Forall2 R (repeatN n a) (repeatN n b).
  Proof.
    intros H n; induction n using N.peano_ind; unfold repeatN in *.
    - constructor.
    - rewrite !N.recursion_succ; try (repeat intro; subst; auto);
        try (constructor; auto).
  Qed.

  Lemma Forall2_eq {A} (l1 l2 : list A) :
    Forall2 eq l1 l2 -> l1 = l2.
  Proof.
    intros * HR; induction HR; subst; cbn; auto.
  Qed.

End Forall2.

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

  (* Not defined as [map_monad f l;; ret tt]: collecting the results makes
     every element executed so far a pending bind continuation, so each
     subsequent step of an itree-interpreted computation re-associates
     through all of them — O(n) per step, O(n²) for a straight-line block
     (see perf/locals-chain.ll). The direct sequencing fold keeps the
     pending-bind depth constant. *)
  Definition map_monad_ {A B}
    (f: A -> m B) (l: list A): m unit :=
    (fix loop l :=
       match l with
       | [] => ret tt
       | a::l' => f a;; loop l'
       end) l.

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

  Definition vec_loop {A B C: Type}
    (f : A -> B -> m C)
    (elts : list (A * B)) : m (list C) :=
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
Arguments vec_loop {_ _ _ _ _}.
Definition repeatMN {A m} `{Monad m} (n : N) (ma : m A) : m (list A)
  := sequence (repeatN n ma).

From ITree Require Import ITree Eq.
From Paco Require Import paco.
 
Section map_monad_itree.
  (* map_monad *)
 Lemma eqit_map_monad {E R1 R2 A1 A2 b1 b2}
    (RR: R1 -> R2 -> Prop)
    (f1 : A1 -> itree E R1) (f2 : A2 -> itree E R2)
    (l1 : list A1) (l2 : list A2)
    (HI : Forall2 (fun a1 a2 => eqit RR b1 b2 (f1 a1) (f2 a2)) l1 l2) :
    eqit (Forall2 RR) b1 b2
      (map_monad f1 l1)
      (map_monad f2 l2).
  Proof.
    induction HI; cbn.
    - now apply eqit_Ret.
    - eapply eqit_bind'; [apply H; now left |].
      intros r1 r2 HR.
      eapply eqit_bind'; [apply IHHI; intros; apply HIN; now right|].
      intros bs1 bs2 HBS.
      apply eqit_Ret.
      now constructor.
  Qed.

  (* map_monad *)
  Lemma eqit_map_monad' {E R A b1 b2}
    (f1 : A -> itree E R) (f2 : A -> itree E R)
    (l1 : list A) (l2 : list A)
    (HI : Forall2 (fun a1 a2 => eqit Logic.eq b1 b2 (f1 a1) (f2 a2)) l1 l2) :
    eqit Logic.eq b1 b2
      (map_monad f1 l1)
      (map_monad f2 l2).
  Proof.
    eapply (eqit_mon _ _ b1 b2 b1 b2); auto; [apply Forall2_eq | apply eqit_map_monad; eauto].
  Qed.

End map_monad_itree.
