From Coq Require Import
  String
  List
  Lia
  ZArith.

Require Import Coq.Logic.ProofIrrelevance.

From Vellvm.Utils Require Import
  Error
  Util
  Monads.

From ExtLib Require Import
     Structures.Monads.

Import ListNotations.
Import MonadNotation.

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
             | Some y => y::(filter_option f xs)
             end
    end.

End FINDOPTION.


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

Lemma Nth_map_iff :
  forall {X Y} (f : X -> Y) xs i y,
    Util.Nth (map f xs) i y <-> (exists x, f x = y /\ Util.Nth xs i x).
Proof.
Admitted.

Lemma map_inj :
  forall {X Y} (f : X -> Y) xs1 xs2,
    (forall a b, In a xs1 -> In b xs2 -> f a = f b -> a = b) ->
    map f xs1 = map f xs2 ->
    xs1 = xs2.
Proof.
  intros X Y f.
  induction xs1, xs2; intros INJ MAP; auto; inversion MAP.

  apply INJ in H0; subst; cbn; auto.
  apply IHxs1 in H1; subst; cbn; auto.
  intros a b H H0 H2.
  apply INJ; cbn; auto.
Qed.

Lemma map_In {A B : Type} (l : list A) (f : forall (x : A), In x l -> B) : list B.
Proof.
  induction l.
  - exact [].
  - refine (f a _ :: IHl _).
    + simpl. auto.
    + intros x H. apply (f x). simpl. auto.
Defined.

Lemma map_In_cons :
  forall {X Y} xs (x : X) (f : forall (a : X), In a (x::xs) -> Y),
    map_In (x::xs) f = f x (or_introl eq_refl) :: map_In xs (fun x IN => f x (or_intror IN)).
Proof.
  cbn.
  reflexivity.
Qed.

Lemma Forall_HIn {A : Type} (l : list A) (f : forall (x : A), In x l -> Prop) : Prop.
Proof.
  induction l.
  - exact True.
  - refine (f a _ /\ IHl _).
    + simpl. auto.
    + intros x H. apply (f x). simpl. auto.
Defined.

Program Fixpoint Forall2_HIn {A B : Type}
  (xs : list A) (ys : list B) (R : forall a b, In a xs -> In b ys -> Prop) : Prop :=
  match xs, ys with
  | [], [] => True
  | (x::xs), (y::ys) =>
      R x y _ _ /\ Forall2_HIn xs ys (fun x y IN1 IN2 => R x y _ _)
  | _, _ =>
      False
  end.
Next Obligation.
  exact (or_introl eq_refl).
Defined.
Next Obligation.
  exact (or_introl eq_refl).
Defined.
Next Obligation.
  exact (or_intror IN1).
Defined.
Next Obligation.
  exact (or_intror IN2).
Defined.
Next Obligation.
  split.
  intros x xs0 y ys0 CONTRA.
  inversion CONTRA.
  inversion H1.

  intros [_ CONTRA].
  inversion CONTRA.
Defined.
Next Obligation.
  split.
  intros x xs0 y ys0 [_ CONTRA].
  inversion CONTRA.

  intros [CONTRA _].
  inversion CONTRA.
Defined.

Lemma Forall2_HIn_cons {A B : Type} :
  forall (xs : list A) (ys : list B) x y (R : forall a b, In a (x :: xs) -> In b (y :: ys) -> Prop),
  R x y (or_introl eq_refl) (or_introl eq_refl) ->
  Forall2_HIn xs ys (fun x y IN1 IN2 => R x y (or_intror IN1) (or_intror IN2)) ->
  Forall2_HIn (x::xs) (y::ys) R.
Proof.
  induction xs, ys; intros x y R HR ALL.
  - cbn; split; auto.
  - cbn in ALL.
    contradiction.
  - cbn in ALL.
    contradiction.
  - cbn in *.
    auto.
Qed.

Lemma Forall2_HIn_forall :
  forall {A B} al bl (P : forall (x : A) (y : B), In x al -> In y bl -> Prop),
    Forall2_HIn al bl P <->
      (length al = length bl /\
         forall i a b (NA : Util.Nth al i a) (NB : Util.Nth bl i b),
         exists IN1 IN2, P a b IN1 IN2).
Proof.
  induction al; simpl; intros.
  - destruct bl.
    split; [intro H; inversion H; subst | intros [H ?]].
    + split; auto; intros ? ? ? Hnth ?; destruct i; simpl in Hnth;
        inversion Hnth.
    + inversion H; auto.
    + split; intros CONTRA; try contradiction.
      inversion CONTRA. inversion H.
  - destruct bl; simpl; [split; [intro H | intros [H ?]]; inversion H|].
    split; [intro H | intros [H ?]]; inversion H; subst.
    + rewrite IHal in *; destruct H1; split; auto; intros i a1 b1 Ha1 Hb1.
      destruct i; eauto.
      * inversion Ha1; inversion Hb1; subst; auto.
        do 2 eexists.
        apply H0.
      * inversion Ha1; inversion Hb1; subst; auto.
        specialize (H2 i _ _ H4 H5) as [IN1 [IN2 PP]].
        exists (or_intror IN1).
        exists (or_intror IN2).
        auto.
    + constructor.
      * specialize (H0 0%nat a b eq_refl eq_refl).
        destruct H0 as [IN1 [IN2 PP]].
        cbn in *.
        rewrite proof_irrelevance at 1.
        rewrite proof_irrelevance at 1.
        eauto.
      * rewrite IHal; split; auto; intros.
        specialize (H0 (S i) _ _ NA NB).
        destruct H0 as [IN1 [IN2 PP]].

        pose proof Util.Nth_In NA.
        pose proof Util.Nth_In NB.

        exists H0. exists H1.
        rewrite proof_irrelevance at 1.
        rewrite proof_irrelevance at 1.
        eauto.
Qed.

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

Lemma in_Zseq :
  forall len start n,
    In n (Zseq start len) <-> (start <= n < start + Z.of_nat len)%Z.
Proof.
  intros len start.
  revert start. induction len as [|len IHlen]; simpl; intros start.
  - intros n. lia.
  - intros n.
    split.
    + intros [IN | IN].
      * subst. lia.
      * pose proof (IHlen (Z.succ start) n) as [A B].
        specialize (A IN).
        lia.
    + intros BOUND.
      destruct (Z.eq_dec start n) as [EQ | NEQ]; auto.
      right.

      pose proof (IHlen (Z.succ start) n) as [A B].
      assert ((Z.succ start <= n < Z.succ start + Z.of_nat len)%Z) as BOUND' by lia.
      specialize (B BOUND').
      auto.
Qed.

Lemma Zseq_nil_len :
  forall start len,
    Zseq start len = [] ->
    len = 0%nat.
Proof.
  intros start len SEQ.
  destruct len; cbn in *; auto.
  inversion SEQ.
Qed.

Lemma Zlength_map :
  forall {X Y} (l : list X) (f : X -> Y),
    Zlength (map f l) = Zlength l.
Proof.
  intros X Y.
  induction l; intros f.
  - reflexivity.
  - rewrite map_cons.
    repeat rewrite Zlength_cons.
    rewrite IHl.
    auto.
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

Lemma Forall_HIn_cons':
  forall {X} (x : X) (xs : list X) f,
    Forall_HIn (x::xs) (fun x HIn => f x HIn) ->
    Forall_HIn (xs) (fun x HIn => f x (or_intror HIn)).
Proof.
  intros X x xs f H.
  apply H.
Qed.

Lemma Forall_HIn_cons_elem:
  forall {X} (x : X) (xs : list X) f,
    Forall_HIn (x::xs) (fun x HIn => f x HIn) ->
    f x (or_introl eq_refl).
Proof.
  intros X x xs f H.
  apply H.
Qed.

Lemma not_Forall_HIn_cons:
  forall {X} (x : X) (xs : list X) (f : forall y : X, List.In y (x :: xs) -> Prop),
    ~Forall_HIn (xs) (fun (x : X) (H : List.In x xs) => f x (or_intror H)) ->
    ~Forall_HIn (x::xs) f.
Proof.
  intros X x xs.
  revert x.
  induction xs; intros x f H.
  - cbn in H; contradiction.
  - intros FORALL.
    apply H.
    apply Forall_HIn_cons'.
    apply FORALL.
Qed.

Lemma not_Forall_HIn_cons_elem :
  forall {X} (x : X) (xs : list X) (f : forall y : X, List.In y (x :: xs) -> Prop),
  ~ f x (or_introl eq_refl) ->
  ~Forall_HIn (x::xs) f.
Proof.
  intros X x xs.
  revert x.
  induction xs; intros x f H.
  - cbn. intros [CONTRA _].
    contradiction.
  - intros FORALL.
    apply H.
    apply Forall_HIn_cons_elem in FORALL.
    auto.
Qed.

Lemma Forall_HIn_dec :
  forall {A} (l : list A) f,
  (forall (u : A) (In : List.In u l), {f u In} + {~ f u In}) ->
  {Forall_HIn l f} + {~Forall_HIn l f}.
Proof.
  intros A l.
  induction l; intros f EQDEC.
  left; cbn; auto.

  remember (fun (x : A) (H : List.In x l) => f x (or_intror H)) as fl.

  assert (forall (u : A) (In : List.In u l), {fl u In} + {~ fl u In}) as FLDEC.
  { subst.
    intros u In.
    apply EQDEC.
  }

  specialize (IHl fl FLDEC).

  assert (List.In a (a :: l)) as Ainl.
  { left; auto.
  }

  pose proof (EQDEC a (or_introl eq_refl)) as [af | naf]; destruct IHl.
  - left; split; subst; cbn; auto.
  - right.
    apply not_Forall_HIn_cons. subst.
    auto.
  - right.
    apply not_Forall_HIn_cons_elem.
    auto.
  - right.
    apply not_Forall_HIn_cons_elem.
    auto.
Qed.

Lemma forall_repeat_true:
  forall A (f : A -> Prop) n x, f x -> Forall (fun y : A => f y) (repeat x n).
Proof.
  intros. induction n. cbn. constructor.
  constructor. auto. cbn. apply IHn.
Qed.

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

Lemma Forall_HIn_cons_inv :
  forall {X} (x : X) (xs : list X) (f : X -> Prop),
    f x ->
    Forall_HIn xs (fun x _ => f x) ->
    Forall_HIn (x::xs) (fun x _ => f x).
Proof.
  intros X x xs f Hfx Hfxs.
  constructor; auto.
Qed.

Definition option_pick_large {A} (leq : A -> A -> bool) (a b : option A) : option A
  := match a, b with
     | Some x, Some y =>
         if leq x y then b else a
     | Some a, _      => Some a
     | _, Some b      => Some b
     | None, None     => None
     end.

Definition option_pick_small {A} (leq : A -> A -> bool) (a b : option A) : option A
  := match a, b with
     | Some x, Some y =>
         if leq x y then a else b
     | Some a, _      => Some a
     | _, Some b      => Some b
     | None, None     => None
     end.

Definition maximumBy {A} (leq : A -> A -> bool) (def : A) (l : list A) : A :=
  fold_left (fun a b => if leq a b then b else a) l def.

Definition maximumByOpt {A} (leq : A -> A -> bool) (l : list A) : option A :=
  fold_left (option_pick_large leq) (map Some l) None.

Definition nextLargest {A} (leq : A -> A -> bool) (n : A) (def : A) (l : list A) : A :=
  fold_left (fun a b => if leq n a && leq a b then a else b)%bool l def.

Definition nextOrMaximum {A} (leq : A -> A -> bool) (n : A) (def : A) (l : list A) : A :=
  let max := maximumBy leq def l
  in fold_left (fun a b => if leq n b && leq a b then a else b)%bool l max.

Definition nextOrMaximumOpt {A} (leq : A -> A -> bool) (n : A) (l : list A) : option A :=
  let max := maximumByOpt leq l
  in fold_left (fun a b => if leq n b then option_pick_small leq a (Some b) else a) l max.

Lemma Nth_last :
  forall {A} (l : list A) x,
    Nth (l ++ [x]) (length l) x.
Proof.
  intros A l x.
  induction l; cbn; auto.
Qed.

Lemma Nth_ix_lt_length :
  forall {X} ix (xs : list X) x,
    Nth xs ix x ->
    (ix < length xs)%nat.
Proof.
  intros X.
  induction ix; intros xs x NTH.
  - cbn in *.
    destruct xs; inversion NTH.
    cbn; lia.
  - destruct xs.
    cbn in *; inversion NTH.
    cbn in *.
    eapply IHix in NTH.
    lia.
Qed.

Lemma Nth_ix_lt_Zlength :
  forall {X} ix (xs : list X) x,
    Nth xs ix x ->
    (Z.of_nat ix < Zlength xs)%Z.
Proof.
  intros X ix xs x NTH.
  eapply Nth_ix_lt_length in NTH; eauto.
  rewrite Zlength_correct.
  lia.
Qed.

(* TODO: do these induction principles exist already? *)
Lemma nat_strong_ind :
  forall (P: nat -> Prop)
    (BASE: P 0)
    (IH: forall (n : nat), (forall (m : nat), m <= n -> P m) -> P (S n)),
  forall n, P n.
Proof.
  intros P BASE IH n.
  destruct n.
  - apply BASE.
  - apply IH.
    induction n; intros m LE.
    + assert (m=0) by lia; subst; auto.
    + assert (m <= n \/ m = S n) as [LE' | EQ] by lia;
        subst; auto.
Qed.

Lemma length_strong_ind:
  forall (X : Type) (P : list X -> Prop)
    (BASE: P nil)
    (IH: forall (n : nat) (xs: list X), (forall (xs : list X), length xs <= n -> P xs) -> length xs = S n -> P xs),
  forall l, P l.
Proof.
  intros X P BASE IH.
  assert (forall n l, length l <= n -> P l) as IHLEN.
  { induction n using nat_strong_ind; intros l LEN; auto.
    assert (length l = 0) as LEN' by lia.
    apply length_zero_iff_nil in LEN'; subst; auto.

    assert (length l <= n \/ length l = S n) as [LEQ | EQ] by lia;
      eauto.
  }

  intros l.
  eapply IHLEN.
  reflexivity.
Qed.

Definition repeatMN {A m} `{Monad m} (n : N) (ma : m A) : m (list A)
  := sequence (repeatN n ma).

Lemma repeatMN_succ :
  forall {A M} `{MM : Monad M} n (m : M A),
    repeatMN (N.succ n) m =
      a <- m;;
      rest <- repeatMN n m;;
      ret (a::rest).
Proof.
  intros A M MM n m.
  unfold repeatMN.
  rewrite repeatN_succ.
  rewrite sequence_cons.
  reflexivity.
Qed.

Lemma concat_length :
  forall {X} (xxs : list (list X)) len
    (INL : forall xs, In xs xxs -> length xs = len),
    length (concat xxs) = len * (length xxs).
Proof.
  intros X xxs.
  induction xxs; intros len INL.
  - cbn; lia.
  - rewrite concat_cons.
    rewrite app_length.
    cbn.
    rewrite INL; cbn; eauto.
    erewrite IHxxs.
    2: {
      intros xs H.
      eapply INL.
      cbn; auto.
    }

    lia.
Qed.

Lemma sequence_OOM_length :
  forall {A} (ms : list (OOM A)) xs,
    sequence ms = NoOom xs ->
    length ms = length xs.
Proof.
  intros A.
  induction ms; intros xs SEQUENCE.
  - cbn in *; inversion SEQUENCE; auto.
  - cbn in *.
    unfold id in *.
    destruct a eqn:H; inversion SEQUENCE; subst.
    destruct (map_monad (fun x : OOM A => x) ms) eqn:SEQ; inversion H1; subst.
    apply IHms in SEQ.
    cbn; auto.
Qed.

Lemma sequence_OOM_In :
  forall {A} (ms : list (OOM A)) xs x,
    sequence ms = NoOom xs ->
    In (NoOom x) ms ->
    In x xs.
Proof.
  intros A.
  induction ms; intros xs x SEQUENCE IN.
  - inversion IN.
  - inversion IN; subst.
    + cbn in *.
      destruct (map_monad id ms) eqn:MAP; inversion SEQUENCE; subst.
      cbn; auto.
    + cbn in *.
      destruct a; cbn in *; [|inversion SEQUENCE].
      destruct (map_monad id ms) eqn:MAP; inversion SEQUENCE; subst.
      right.
      eauto.
Qed.

Lemma sequence_OOM_NoOom_In :
  forall {A} (ms : list (OOM A)) (xs : list A),
    sequence ms = NoOom xs ->
    forall (oom_msg : string), ~ In (Oom oom_msg) ms.
Proof.
  intros A.
  induction ms; intros xs SEQUENCE msg IN.
  - inversion IN.
  - inversion IN; subst.
    + cbn in *.
      inversion SEQUENCE.
    + cbn in *.
      destruct a; inversion SEQUENCE.
      destruct (map_monad id ms) eqn:MAP; inversion SEQUENCE; subst.
      eapply IHms in H; eauto.
Qed.

Lemma Nth_exists :
  forall {X} (xs : list X) n,
    n < length xs ->
    exists x, Nth xs n x.
Proof.
  intros X xs.
  induction xs; intros n LEN.
  - cbn in *; lia.
  - cbn in LEN.
    destruct n.
    + exists a; cbn; auto.
    + cbn.
      apply IHxs.
      lia.
Qed.

Lemma In_Nth :
  forall {X} xs (x : X),
    In x xs -> exists i, Util.Nth xs i x.
Proof.
  induction xs; intros x IN.
  - inversion IN.
  - destruct IN; subst.
    + exists (0%nat). cbn. auto.
    + apply IHxs in H as [i H].
      exists (S i).
      cbn; auto.
Qed.

Lemma repeat_S :
  forall X (x : X) n,
    repeat x (S n) = x :: repeat x n.
Proof.
  intros X x n.
  reflexivity.
Qed.
