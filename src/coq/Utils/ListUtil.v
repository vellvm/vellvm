From Coq Require Import String List Lia ZArith Program.Wf.

From Vellvm.Utils Require Import Error.

Import ListNotations.

(* TODO: Move. Also, do I really have to define this? *)
Fixpoint zipWith {A B C} (f : A -> B -> C) (xs : list A) (ys : list B) : list C
  := match xs, ys with
     | [], _        => []
     | _, []        => []
     | a::xs', b::ys' => f a b :: zipWith f xs' ys'
     end.

Definition zip {X Y} (xs : list X) (ys : list Y) := zipWith (fun a b => (a, b)) xs ys.

Lemma zip_In_both :
  forall {A} {B} xs ys (x : A) (y : B) ,
    In (x, y) (zip xs ys) ->
    In x xs /\ In y ys.
Proof.
  induction xs, ys;
    intros x y H; inversion H.
  - inversion H0; subst.
    intuition.
  - clear H.
    specialize (IHxs _ _ _ H0).
    intuition.
Qed.

Lemma map_In {A B : Type} (l : list A) (f : forall (x : A), In x l -> B) : list B.
Proof.
  induction l.
  - exact [].
  - refine (f a _ :: IHl _).
    + simpl. auto.
    + intros x H. apply (f x). simpl. auto.
Defined.

Lemma Forall_HIn {A : Type} (l : list A) (f : forall (x : A), In x l -> Prop) : Prop.
Proof.
  induction l.
  - exact True.
  - refine (f a _ /\ IHl _).
    + simpl. auto.
    + intros x H. apply (f x). simpl. auto.
Defined.

Lemma list_sum_map :
  forall {X} (f : X -> nat) x xs,
    In x xs ->
    list_sum (map f xs) >= f x.
Proof.
  induction xs; intros In; [contradiction|].
  destruct In; subst.
  - cbn. lia.
  - cbn. specialize (IHxs H).
    unfold list_sum in IHxs.
    lia.
Qed.

Fixpoint Zseq (start : Z) (len : nat) : list Z :=
  match len with
  | O => []
  | S x => start :: Zseq (Z.succ start) x
  end.

Fixpoint Nseq (start : N) (len : nat) : list N :=
  match len with
  | O => []
  | S x => start :: Nseq (N.succ start) x
  end.

Lemma cons_Nseq :
  forall len start,
    start :: Nseq (N.succ start) len = Nseq start (S len).
Proof.
  reflexivity.
Qed.

Lemma Nseq_app :
  forall len1 len2 start,
    Nseq start (len1 + len2) = Nseq start len1 ++ Nseq (start + (N.of_nat len1)) len2.
Proof.
  intro len1; induction len1 as [|len1' IHlen]; intros.
  - now rewrite N.add_0_r.
  - rewrite Nnat.Nat2N.inj_succ.
    rewrite <- N.add_succ_comm.
    cbn.
    rewrite IHlen.
    reflexivity.
Qed.

Lemma Nseq_S :
  forall len start,
    Nseq start (S len) = Nseq start len ++ [(start + N.of_nat len)%N].
Proof.
  intros len start.
  change [(start + N.of_nat len)%N] with (Nseq (start + N.of_nat len) 1).
  rewrite <- Nseq_app.
  rewrite <- plus_n_Sm, <- plus_n_O; reflexivity.
Qed.

Lemma Nseq_length :
  forall len start, length (Nseq start len) = len.
Proof.
  intro len; induction len; simpl; auto.
Qed.

Lemma Zseq_succ : forall off (n : N),
    Zseq off (N.to_nat (N.succ n)) = off :: Zseq (Z.succ off) (N.to_nat n).
Proof.
  intros off n.
  rewrite Nnat.N2Nat.inj_succ; auto.
Qed.

Lemma Zseq_succ_nat : forall off (n : nat),
    Zseq off (S n) = off :: Zseq (Z.succ off) n.
Proof.
  intros off n.
  auto.
Qed.

Lemma Zseq_length :
  forall len off,
    Datatypes.length (Zseq off len) = len.
Proof.
  induction len; intros; auto.
  cbn.
  congruence.
Qed.


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

Definition between {A} (lo hi : N) (l : list A) : list A
  := take (hi - lo) (drop lo l).

(* Filter elements in a list, giving an (ins * outs) tuple of lists. *)
Fixpoint filter_split {A} (pred : A -> bool) (xs : list A) : (list A * list A)
  := match xs with
     | [] => ([], [])
     | (x::xs) =>
       let '(ins, outs) := filter_split pred xs in
       if pred x
       then (x::ins, outs)
       else (ins, x::outs)
     end.

Lemma filter_split_in_length :
  forall {A} pred (xs ins outs : list A),
    filter_split pred xs = (ins, outs) ->
    length ins <= length xs.
Proof.
  intros A pred xs;
    induction xs; intros ins outs LEN.
  - cbn in LEN. inversion LEN.
    reflexivity.
  - cbn in LEN.
    destruct (pred a).
    + destruct (filter_split pred xs) as (in' & out') eqn:FILTER.
      inversion LEN; subst; cbn.
      apply le_n_S.
      eauto.
    + destruct (filter_split pred xs) as (in' & out') eqn:FILTER.
      inversion LEN; subst; cbn.
      eauto.
Qed.

Lemma filter_split_out_length :
  forall {A} pred (xs ins outs : list A),
    filter_split pred xs = (ins, outs) ->
    length outs <= length xs.
Proof.
  intros A pred xs;
    induction xs; intros ins outs LEN.
  - cbn in LEN. inversion LEN.
    reflexivity.
  - cbn in LEN.
    destruct (pred a).
    + destruct (filter_split pred xs) as (in' & out') eqn:FILTER.
      inversion LEN; subst; cbn.
      eauto.
    + destruct (filter_split pred xs) as (in' & out') eqn:FILTER.
      inversion LEN; subst; cbn.
      apply le_n_S.
      eauto.
Qed.

(* TODO: does this exist somewhere else? *)
Lemma app_prefix :
  forall {A} (a b c : list A),
    b = c -> a ++ b = a ++ c.
Proof.
  intros A a b c H.
  induction a.
  - cbn; auto.
  - cbn. rewrite IHa.
    reflexivity.
Qed.

Lemma skipn_length_app :
  forall {A} (xs ys : list A),
    skipn (Datatypes.length xs) (xs ++ ys) = ys.
Proof.
  intros A xs ys.
  induction xs; cbn; auto.
Qed.

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

Program Fixpoint split_every_pos {A} (n : positive) (xs : list A) {measure (length xs)} : list (list A)
  := match xs with
     | [] => []
     | _ =>
       take (Npos n) xs :: split_every_pos n (drop (Npos n) xs)
     end.
Next Obligation.
  destruct xs; try contradiction.
  apply drop_length_lt; auto; lia.
Qed.

Definition split_every {A} (n : N) (xs : list A) : err (list (list A))
  := match n with
     | N0 => failwith "split_every: called with n = 0."
     | Npos n =>
       inr (split_every_pos n xs)
     end.

Lemma fold_sum_acc :
  forall {A} (dts : list A) n (f : A -> N),
    (fold_left (fun (acc : N) (x : A) => acc + f x) dts n =
     n + fold_left (fun (acc : N) (x : A) => acc + f x) dts 0)%N.
Proof.
  induction dts; intros n f.
  - cbn. rewrite N.add_0_r. reflexivity.
  - cbn. rewrite IHdts at 1. rewrite (IHdts (f a)).
    rewrite N.add_assoc.
    reflexivity.
Qed.

Definition repeatN {X} (n : N) (x : X) : list X
  := N.recursion
       []
       (fun n xs => x :: xs)
       n.

Lemma repeatN_succ :
  forall {X} sz (x : X),
    repeatN (N.succ sz) x = x :: repeatN sz x.
Proof.
  intros X sz.
  induction sz using N.peano_ind; intros x; auto.
  unfold repeatN.
  rewrite N.recursion_succ; eauto.
  intuition.
Qed.

Lemma In_repeatN :
  forall {X} sz (x elt : X),
    In elt (repeatN sz x) ->
    elt = x.
Proof.
  intros X sz.
  induction sz using N.peano_ind; intros x elt H.
  - inversion H.
  - rewrite repeatN_succ in H.
    cbn in H.
    inversion H; auto.
Qed.

Lemma Forall_HIn_cons:
  forall {X} (x : X) (xs : list X) f,
    Forall_HIn (x::xs) (fun x HIn => f x) ->
    Forall_HIn (xs) (fun x HIn => f x).
Proof.
  intros X x xs f H.
  apply H.
Qed.
