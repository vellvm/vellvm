From Coq Require Import
  String
  List
  Lia
  ZArith
  Program
  Program.Wf.

Require Import Coq.Logic.ProofIrrelevance.

From Vellvm.Utils Require Import
  Error
  Util
  Monads
  Tactics.

From ExtLib Require Import
  Structures.Monads
  Structures.Foldable
  Data.List.

Import ListNotations.
Import MonadNotation.

Require Import Recdef.

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
    intuition auto with *.
  - clear H.
    specialize (IHxs _ _ _ H0).
    intuition auto with *.
Qed.

Lemma Nth_map_iff :
  forall {X Y} (f : X -> Y) xs i y,
    Util.Nth (map f xs) i y <-> (exists x, f x = y /\ Util.Nth xs i x).
Proof.
  intros X Y f xs.
  induction xs; intros i y.
  - cbn.
    split; intros H.
    + destruct i; cbn in *; discriminate.
    + destruct H as (x&FXY&H).
      destruct i; cbn in *; discriminate.
  - cbn.
    split; intros H.
    + destruct i; cbn in *; inv H; eauto.
      eapply IHxs; eauto.
    + destruct H as (x&FXY&H).
      destruct i; cbn in *; inv H; eauto.
      eapply IHxs; eauto.
Qed.

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
  intros x xs0 ?y ys0 CONTRA.
  inversion CONTRA.
  inversion H.

  intros [_ CONTRA].
  inversion CONTRA.
Defined.
Next Obligation.
  split.
  intros x xs0 ?y ys0 [_ CONTRA].
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

Lemma Forall2_map_eq :
  forall {A B} (f : A -> B) l1 l2,
    Forall2 (fun a b => f a = b) l1 l2 ->
    map f l1 = l2.
Proof.
  intros A B f l1 l2 ALL.
  induction ALL; auto.
  rewrite map_cons.
  congruence.
Qed.

Lemma Forall2_flip :
  forall {A B} (P : A -> B -> Prop) l1 l2,
    Forall2 P l1 l2 <-> Forall2 (flip P) l2 l1.
Proof.
  intros A B f l1 l2.
  split; intros ALL;
    induction ALL; auto.
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

Fixpoint split_n {A} (n:nat) (l : list A) : err (list A * list A) :=
  match n with
  | 0 => ret ([], l)
  | S n =>
      match l with
      | [] => raise "split_n: list too short"%string
      | x::xs =>
          '(l1, l2) <- split_n n xs ;;
          ret (x::l1, l2)
      end
  end.

Lemma split_n_app : forall {A} (l1 l2: list A),
    split_n (length l1) (l1 ++ l2) = ret (l1, l2).
Proof.
  induction l1; intros; simpl; auto.
  break_match_goal.
  rewrite IHl1 in Heqs. inversion Heqs.
  destruct p.
  rewrite IHl1 in Heqs.
  inversion Heqs; subst.
  auto.
Qed.

Lemma split_n_correct : forall {A} n (l1 l2 l3 : list A),
    split_n n l1 = inr (l2, l3) <-> length l2 = n /\ l1 = l2 ++ l3.
Proof.
  intros A n l1 l2 l3.
  split; intros H.
  - revert l1 l2 l3 H.
    induction n; intros l1 l2 l3 H; inversion H; subst; simpl in *; auto.
    repeat break_match_hyp_inv.
    cbn.
    destruct (IHn _ _ _ Heqs) as [EQ1 EQ2].
    rewrite EQ1. rewrite EQ2. auto.
  - destruct H as [EQ1 EQ2].
    revert n l1 l3 EQ1 EQ2.
    induction l2; intros n l1 l3 EQ1 EQ2; simpl in *; subst.
    + reflexivity.
    + cbn.
      break_match_goal.
      * rewrite split_n_app in Heqs. inversion Heqs.
      * destruct p.
        rewrite split_n_app in Heqs. inversion Heqs.
        subst.
        reflexivity.
Qed.

Lemma split_n_Forall : forall {A} (P:A -> Prop) n (l1 l2 l3 : list A),
    split_n n l1 = ret (l2, l3) ->
    Forall P l1 <-> (Forall P l2 /\ Forall P l3).
Proof.
  intros A P n l1 l2 l3 H.
  split; intros HF.
  - revert n l2 l3 H.
    induction HF; intros n l2 l3 HS.
    + destruct n; inversion HS; subst.
      split; constructor.
    + destruct n; inversion HS; subst.
      * split; constructor; auto.
      * break_match_hyp_inv.
        destruct p. inversion H2; subst.
        apply IHHF in Heqs. destruct Heqs.
        split. constructor; auto. auto.
  - revert l1 l2 l3 H HF.
    induction n; intros l1 l2 l3 H [HF1 HF2]; inversion H; subst; auto.
    repeat break_match_hyp_inv.
    inversion HF1; subst.
    constructor; auto.
    eapply IHn; eauto.
Qed.

Lemma split_n_Forall2 : forall {A B} (P:A -> B -> Prop) n (l1 l2 l3 : list A) (m1 m2 m3 : list B),
    split_n n l1 = ret (l2, l3) ->
    split_n n m1 = ret (m2, m3) ->    
    Forall2 P l1 m1 <-> (Forall2 P l2 m2 /\ Forall2 P l3 m3).
Proof.
  intros A B P n l1 l2 l3 m1 m2 m3 HL HM.
  split; intros HF.
  - revert n l2 l3 m2 m3 HL HM.
    induction HF; intros n l2 l3 m2 m3 HS HSm.
    + destruct n; inversion HS; subst.
      inversion HSm; subst.
      split; constructor.
    + destruct n; inversion HS; subst.
      inversion HSm; subst.
      * split; constructor; auto.
      * inversion HSm.
        repeat break_match_hyp_inv.
        specialize (IHHF _ _ _ _ _ Heqs0 Heqs). destruct IHHF.
        split. constructor; auto. auto.
  - revert l1 l2 l3 m1 m2 m3 HL HM HF.
    induction n; intros l1 l2 l3 m1 m2 m3 HL HM [HF1 HF2]; inversion HL; inversion HM; subst; auto.
    repeat break_match_hyp_inv.
    inversion HF1; subst.
    constructor; auto.
    eapply IHn; eauto.
Qed.

Lemma split_n_Forall2_exists1 : forall {A B} (P:A -> B -> Prop) n (l1 l2 l3 : list A) m1,
    split_n n l1 = ret (l2, l3) ->
    Forall2 P l1 m1 ->
    exists m2 m3,
      (split_n n m1 = ret (m2, m3)) /\
        (Forall2 P l2 m2) /\ (Forall2 P l3 m3).
Proof.
  intros A B P n.
  induction n; intros l1 l2 l3 m1 HS HF.
  - inversion HS; subst.
    * exists []. exists m1. split; auto.
  - inversion HS; subst.
    repeat break_match_hyp_inv.
    inversion HF; subst.
    destruct (IHn _ _ _ _ Heqs H3) as [m2 [m3 [S [F1 F2]]]].
    exists (y::m2). exists m3.
    split; auto. cbn.  rewrite S. reflexivity.
Qed.

Lemma split_n_Forall2_exists2 : forall {A B} (P:A -> B -> Prop) n (l1 : list A) (m1 m2 m3: list B),
    split_n n m1 = ret (m2, m3) ->
    Forall2 P l1 m1 ->
    exists l2 l3,
      (split_n n l1 = ret (l2, l3)) /\
        (Forall2 P l2 m2) /\ (Forall2 P l3 m3).
Proof.
  intros A B P n.
  induction n; intros l1 m1 m2 m3 HS HF.
  - inversion HS; subst.
    * exists []. exists l1. split; auto.
  - inversion HS; subst.
    repeat break_match_hyp_inv.
    inversion HF; subst.
    destruct (IHn _ _ _ _ Heqs H3) as [l2' [l3' [S [F1 F2]]]].
    exists (x::l2'). exists l3'.
    split; auto. cbn.  rewrite S. reflexivity.
Qed.

Lemma split_n_err : forall {A} n (l:list A),
    (exists s, split_n n l = inl s) <->
      length l < n.
Proof.
  intros. split.
  - revert l.
    induction n; intros.
    + destruct H as [s EQ].
      inversion EQ.
    + destruct H as [s EQ].
      destruct l.
      * cbn. lia.
      * cbn in *.
        break_match_hyp_inv.
        -- assert (exists s, split_n n l = inl s).
           { eexists; eauto. } 
           apply IHn in H. lia.
        -- destruct p. inversion H0.
  - revert n.
    induction l; intros.
    + destruct n; cbn in *.
      * lia.
      * eexists. reflexivity.
    + cbn in H.
      destruct n.
      -- lia.
      -- cbn.
         break_match_goal.
      * eexists. reflexivity.
      * destruct p. 
        assert (length l < n) by lia.
        destruct (IHl _ H0) as [s HS].
        rewrite HS in Heqs. inversion Heqs.
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

Lemma split_every_pos_empty_equiv : forall {A} l p,
    split_every_pos A p l = [] <-> l = [].
Proof using.
  split.
  - intros. rewrite split_every_pos_equation in H.
    induction l.
    + reflexivity.
    + discriminate.
  - intros; subst. reflexivity.
Qed.

Lemma list_take_drop : forall {A} (l : list A) n,
    l <> [] -> l = (take n l) ++ drop n l.
Proof using.
  intros.
  generalize dependent n.
  induction l.
  - destruct H. reflexivity.
  - induction l.
    + intros n. induction n.
      ++ reflexivity.
      ++ reflexivity.
    + intros n. induction n.
      ++ reflexivity.
      ++ simpl. f_equal.
         apply IHl.
         intros D. discriminate.
Qed.

Lemma split_every_pos_nonempty_equiv : forall {A} (l : list A) p,
    split_every_pos A p l = take (N.pos p) l :: split_every_pos A p (drop (N.pos p) l)<-> l <> [].
Proof using.
  split.
  - intros. induction l.
    + discriminate.
    + intros D. discriminate.
  - intros. induction l.
    + destruct H; reflexivity.
    + rewrite split_every_pos_equation at 1.
      reflexivity.
Qed.

Lemma split_every_pos_nonempty_take_drop : forall {A} (l : list A) xs xss p,
    split_every_pos A p l = xs :: xss ->
      xs = take (N.pos p) l /\ xss = split_every_pos A p (drop (N.pos p) l).
Proof using.
  intros. rewrite split_every_pos_equation in H. induction l; try discriminate.
  injection H. intros; subst. auto.
Qed.

Lemma split_every_pos_nonempty_inv : forall {A} (l : list A) xs xss p,
    split_every_pos A p l = xs :: xss -> l <> [].
Proof using.
  intros A l.
  induction l.
  - discriminate.
  - intros. intros D. discriminate.
Qed.

Definition split_every {A} (n : N) (xs : list A) : err (list (list A))
  := match n with
     | N0 => failwith "split_every: called with n = 0."
     | Npos n =>
         inr (split_every_pos A n xs)
     end.

(* Like split_every, but default to the empty list in the n=0 case *)
Definition split_every_nil {A} (n : N) (xs : list A) : list (list A)
  := match n with
     | N0 => []
     | Npos n =>
         split_every_pos A n xs
     end.

Lemma split_every_empty :
  forall {A} n,
    n <> 0%N ->
    split_every n [] = inr ([]: list (list A)).
Proof using.
  intros. destruct n; try contradiction.
  unfold split_every. f_equal.
Qed.

Lemma split_every_nil_empty :
  forall {A} n,
    split_every_nil n [] = ([]: list (list A)).
Proof using.
  intros. destruct n; auto.
Qed.

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
  intuition auto with *.
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

Lemma In_cons_right :
  forall {A} {l : list A} {a x xs}
         (EQ : l = x :: xs) (HIn : In a xs),
    In a l.
Proof.
  intros A l x xs EQ a HIn.
  subst.
  cbn.
  right.
  auto.
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

Lemma double_list_ind :
  forall {X Y}
         (P: list X -> list Y -> Prop)
         (NilNil : P nil nil)
         (NilCons : forall y ys, P nil ys -> P nil (y :: ys))
         (ConsNil : forall x xs, P xs nil -> P (x :: xs) nil)
         (ConsCons : forall x xs y ys, P xs ys -> P (x :: xs) (y :: ys)),
  forall xs ys, P xs ys.
Proof.
  intros X Y P NilNil NilCons ConsNil ConsCons xs.
  induction xs; induction ys.
  - apply NilNil.
  - apply NilCons.
    apply IHys.
  - apply ConsNil.
    apply IHxs.
  - apply ConsCons.
    apply IHxs.
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

Lemma map_repeat :
  forall {A B} (f : A -> B) a sz,
    map f (repeat a sz) = repeat (f a) sz.
Proof.
  intros A B f a sz.
  induction sz.
  - cbn; auto.
  - cbn. rewrite IHsz; auto.
Qed.

Fixpoint combine_lists_err {A B:Type} (l1:list A) (l2:list B) : err (list (A * B)) :=
  match l1, l2 with
  | [], [] => ret []
  | x::xs, y::ys =>
      l <- combine_lists_err xs ys ;;
      ret ((x,y)::l)
  | _, _ =>
      (* YZ: This should be a failure, but we first need to have a proper
          story to handle main arguments since at the moment we expect exactly
          argc and argv, and feed default values to them *)
      (* failwith "combine_lists_err: different length lists" *)
      ret []
  end.

Lemma combine_lists_err_inl_contra :
  forall {X Y} (xs : list X) (ys : list Y) msg,
    ~ (combine_lists_err xs ys = inl msg).
Proof.
  intros X Y.
  induction xs, ys; intros msg CONTRA;
    inversion CONTRA.
  destruct (combine_lists_err xs ys) eqn:COMB.
  apply IHxs in COMB; auto.
  inversion H0.
Qed.

Lemma combine_lists_err_length_eq :
  forall {A B C D} xs1 ys1 xs2 ys2 zs1 zs2,
    @combine_lists_err A B xs1 ys1 = inr zs1 ->
    @combine_lists_err C D xs2 ys2 = inr zs2 ->
    length ys1 = length ys2 ->
    length xs1 = length xs2 ->
    length zs1 = length zs2.
Proof.
  intros A B C D.
  induction xs1, ys1, xs2, ys2;
    intros zs1 zs2
      COMB1 COMB2 LEN1 LEN2;
    try solve [cbn in *;
               inversion COMB1; inversion COMB2;
               auto
              | inversion LEN1; inversion LEN2
      ].
  cbn in *.

  destruct (combine_lists_err xs1 ys1) eqn:COMB1';
    inversion COMB1.

  destruct (combine_lists_err xs2 ys2) eqn:COMB2';
    inversion COMB2.
  cbn.
  apply Nat.succ_inj_wd.
  eapply IHxs1; eauto.
Qed.

Lemma combine_lists_err_Nth :
  forall {X Y} xs ys (x : X) (y : Y) zs i,
    Nth xs i x ->
    Nth ys i y ->
    combine_lists_err xs ys = inr zs ->
    Nth zs i (x, y).
Proof.
  intros X Y.
  induction xs, ys;
    intros x' y' zs i NTH_xs NTH_ys COMB;
    cbn in *;
    try
      solve [ apply not_Nth_nil in NTH_xs; contradiction
            | apply not_Nth_nil in NTH_ys; contradiction
      ].

  destruct (combine_lists_err xs ys) eqn:COMB';
    inversion COMB.

  destruct i.
  - cbn in *.
    inversion NTH_xs; inversion NTH_ys.
    reflexivity.
  - cbn in *.
    eauto.
Qed.

Lemma combine_lists_err_Nth_inv :
  forall {X Y} xs ys (x : X) (y : Y) zs i,
    Nth zs i (x, y) ->
    combine_lists_err xs ys = inr zs ->
    Nth xs i x /\ Nth ys i y.
Proof.
  intros X Y.
  induction xs, ys;
    intros x' y' zs i NTH COMB;
    try
      solve [ cbn in COMB; inversion COMB; subst;
              apply not_Nth_nil in NTH; contradiction
      ].

  cbn in *.
  destruct (combine_lists_err xs ys) eqn:COMB';
    inversion COMB.

  destruct i.
  - cbn in *.
    inversion NTH; subst.
    inversion H1; subst.
    auto.
  - cbn in *; subst.
    eauto.
Qed.

Lemma map_In_length :
  forall {X Y} (l : list X) (f : forall (x : X), In x l -> Y),
    length (map_In l f) = length l.
Proof.
  induction l; intros f.
  - cbn. auto.
  - rewrite map_In_cons.
    cbn.
    congruence.
Qed.

Lemma Nth_map_In_iff:
  forall {X Y : Type} (xs : list X) (f : forall x : X, In x xs -> Y) (i : nat) (y : Y),
    Nth (map_In xs f) i y <-> (exists (x : X) IN, f x IN = y /\ Nth xs i x).
Proof.
Admitted.

Lemma in_map_In :
  forall {A B} l x (f : forall (a : A) (INA : In a l), B) (INX : In x l),
    In (f x INX) (map_In l f).
Proof.
  intros A B l; induction l; firstorder (subst; auto).
  rewrite map_In_cons.
  cbn.
  destruct INX; subst; auto.
  right.
  specialize (IHl x (fun (x0 : A) (IN : In x0 l) => f x0 (or_intror IN)) i).
  cbn in IHl.
  auto.
Qed.

Lemma in_map_In' :
  forall {A B} l x (f : forall (a : A), B) (INX : In x l),
    In (f x) (map_In l (fun x (INX : In x l) => f x)).
Proof.
  intros A B l; induction l; firstorder (subst; auto).
Qed.

Variant FalseT : Type := .

Fixpoint InT {A} (a:A) (l:list A) : Type :=
  match l with
  | [] => FalseT
  | b :: m => (b = a) + (InT a m)
  end.

Lemma Nth_eq :
  forall {X} xs1 xs2,
    (forall (i : nat) (a b : X), Util.Nth xs1 i a -> Util.Nth xs2 i b -> a = b) ->
    Datatypes.length xs1 = Datatypes.length xs2 ->
    xs1 = xs2.
Proof.
  intros X xs1.
  induction xs1, xs2; intros NTHEQ LEN; auto.
  - inversion LEN.
  - inversion LEN.
  - cbn in *.
    pose proof (NTHEQ 0%nat a x).
    forward H; auto.
    forward H; auto.
    subst.

    erewrite IHxs1; eauto.
    intros i a b H H0.
    apply NTHEQ with (i:=S i); cbn; auto.
Qed.

(* TODO: Move this *)
Theorem repeat_spec_InT {X} n (x : X) y:
  InT y (repeat x n) -> y=x.
Proof.
  induction n as [|k Hrec]; simpl; destruct 1; auto.
Qed.

(* TODO: Move this *)
Lemma nth_error_InT {X} l n (x : X) : nth_error l n = Some x -> InT x l.
Proof.
  revert n. induction l as [|a l IH]; intros [|n]; simpl; try easy.
  - injection 1; auto.
  - eauto.
Qed.

Lemma Nth_InT :
  forall {X} (xs : list X) i (x : X),
    Util.Nth xs i x ->
    InT x xs.
Proof.
  intros X xs i x NTH.
  unfold Util.Nth in *.
  eapply nth_error_InT; eauto.
Qed.

(* TODO: Move this *)
Lemma list_sum_map_InT :
  forall {X} (f : X -> nat) x xs,
    InT x xs ->
    (list_sum (map f xs) >= f x)%nat.
Proof.
  induction xs; intros In; [contradiction|].
  destruct In; subst.
  - cbn. lia.
  - cbn. specialize (IHxs i).
    unfold list_sum in IHxs.
    lia.
Qed.

(* TODO: Move this *)
Lemma In_InT :
  forall {X} (x : X) xs,
    InT x xs -> In x xs.
Proof.
  intros X x xs X0.
  induction xs.
  - inversion X0.
  - cbn in *.
    destruct X0; subst; auto.
Qed.

Lemma Forall_HIn_eq : forall A (l:list A) (f g : forall (x:A), In x l -> Prop),
    (forall x H1 H2, f x H1 = g x H2) ->
    Forall_HIn l f = Forall_HIn l g.
Proof.
  induction l; intros; simpl; try reflexivity.
  erewrite H. erewrite IHl. reflexivity.
  intros.
  erewrite H. reflexivity.
Qed.

(* Program Fixpoint zipWith_In' {A B ACC : Type} *)
(*   (xs : list A) (ys : list B) (acc : ACC) *)
(*   (f : forall x y, In x xs -> In y ys -> ACC -> ACC) *)
(*   (f_left : forall x, In x xs -> ACC -> ACC) *)
(*   (f_right : forall y, In y ys -> ACC -> ACC) *)
(*   {measure (length xs + length ys)} *)
(*   : ACC := *)
(*   match xs as xs' return (xs = xs' -> ACC) with *)
(*   | [] => *)
(*       fun Heq_xs => *)
(*         (match ys as ys' return (ys = ys' -> ACC) with *)
(*          | [] => *)
(*              fun Heq_ys => *)
(*                acc *)
(*          | (y::ys') => *)
(*              fun Heq_ys => *)
(*                let acc' := f_right y (@eq_ind (list B) (y :: ys') (fun l => In y l) (or_introl eq_refl) ys (eq_sym Heq_ys)) acc in *)
(*                let f' : forall (x : A) y', In x [] -> In y' ys' -> ACC -> ACC  := *)
(*                  fun x y INx INy acc' => *)
(*                    match INx with *)
(*                    end in *)
(*                let f_left' : forall x, In x [] -> ACC -> ACC := *)
(*                  fun x INx acc' => *)
(*                    match INx with *)
(*                    end in *)
(*                let f_right' : forall y', In y' ys' -> ACC -> ACC := *)
(*                  fun y' INy acc' => *)
(*                    f_right y' (@eq_ind (list B) (y :: ys') (fun l => In y' l) (or_intror INy) ys (eq_sym Heq_ys)) acc' in *)
(*                zipWith_In' [] ys' acc' f' f_left' f_right' *)
(*          end eq_refl) *)
(*   | (x::xs') => *)
(*       fun Heq_xs => *)
(*         (match ys as ys' return (ys = ys' -> ACC) with *)
(*          | [] => *)
(*              fun Heq_ys => *)
(*                let acc' := f_left x (@eq_ind (list A) (x :: xs') (fun l => In x l) (or_introl eq_refl) xs (eq_sym Heq_xs)) acc in *)
(*                let f' : forall x (y : B), In x xs' -> In y [] -> ACC -> ACC  := *)
(*                  fun x y INx INy acc' => *)
(*                    match INy with *)
(*                    end in *)
(*                let f_left' : forall x', In x' xs' -> ACC -> ACC := *)
(*                  fun x' INx acc' => *)
(*                    f_left x' (@eq_ind (list A) (x :: xs') (fun l => In x' l) (or_intror INx) xs (eq_sym Heq_xs)) acc' in *)
(*                let f_right' : forall y, In y [] -> ACC -> ACC := *)
(*                  fun y INy acc' => *)
(*                    match INy with *)
(*                    end in *)
(*                zipWith_In' xs' [] acc' f' f_left' f_right' *)
(*          | (y::ys') => *)
(*              fun Heq_ys => *)
(*                let acc' := f x y (@eq_ind (list A) (x :: xs') (fun l => In x l) (or_introl eq_refl) xs (eq_sym Heq_xs)) (@eq_ind (list B) (y :: ys') (fun l => In y l) (or_introl eq_refl) ys (eq_sym Heq_ys)) acc in *)
(*                let f' : forall x (y : B), In x xs' -> In y ys' -> ACC -> ACC  := *)
(*                  fun x' y' INx INy acc' => *)
(*                    f x' y' (@eq_ind (list A) (x :: xs') (fun l => In x' l) (or_intror INx) xs (eq_sym Heq_xs)) (@eq_ind (list B) (y :: ys') (fun l => In y' l) (or_intror INy) ys (eq_sym Heq_ys)) acc' in *)
(*                let f_left' : forall x', In x' xs' -> ACC -> ACC := *)
(*                  fun x' INx acc' => *)
(*                    f_left x' (@eq_ind (list A) (x :: xs') (fun l => In x' l) (or_intror INx) xs (eq_sym Heq_xs)) acc' in *)
(*                let f_right' : forall y', In y' ys' -> ACC -> ACC := *)
(*                  fun y' INy acc' => *)
(*                    f_right y' (@eq_ind (list B) (y :: ys') (fun l => In y' l) (or_intror INy) ys (eq_sym Heq_ys)) acc' in *)
(*                zipWith_In' xs' ys' acc' f' f_left' f_right' *)
(*          end eq_refl) *)
(*   end eq_refl. *)
(* Next Obligation. *)
(*   cbn. *)
(*   lia. *)
(* Defined. *)

(* Lemma zipWith_In'_equation *)
(*   {A B ACC : Type} *)
(*   (xs : list A) (ys : list B) (acc : ACC) *)
(*   (f : forall x y, In x xs -> In y ys -> ACC -> ACC) *)
(*   (f_left : forall x, In x xs -> ACC -> ACC) *)
(*   (f_right : forall y, In y ys -> ACC -> ACC) : *)
(*   @zipWith_In' A B ACC xs ys acc f f_left f_right = *)
(*     match xs as xs' return (xs = xs' -> ACC) with *)
(*     | [] => *)
(*         fun Heq_xs => *)
(*           (match ys as ys' return (ys = ys' -> ACC) with *)
(*            | [] => *)
(*                fun Heq_ys => *)
(*                  acc *)
(*            | (y::ys') => *)
(*                fun Heq_ys => *)
(*                  let acc' := f_right y (@eq_ind (list B) (y :: ys') (fun l => In y l) (or_introl eq_refl) ys (eq_sym Heq_ys)) acc in *)
(*                  let f' : forall (x : A) y', In x [] -> In y' ys' -> ACC -> ACC  := *)
(*                    fun x y INx INy acc' => *)
(*                      match INx with *)
(*                      end in *)
(*                  let f_left' : forall x, In x [] -> ACC -> ACC := *)
(*                    fun x INx acc' => *)
(*                      match INx with *)
(*                      end in *)
(*                  let f_right' : forall y', In y' ys' -> ACC -> ACC := *)
(*                    fun y' INy acc' => *)
(*                      f_right y' (@eq_ind (list B) (y :: ys') (fun l => In y' l) (or_intror INy) ys (eq_sym Heq_ys)) acc' in *)
(*                  zipWith_In' [] ys' acc' f' f_left' f_right' *)
(*            end eq_refl) *)
(*     | (x::xs') => *)
(*         fun Heq_xs => *)
(*           (match ys as ys' return (ys = ys' -> ACC) with *)
(*            | [] => *)
(*                fun Heq_ys => *)
(*                  let acc' := f_left x (@eq_ind (list A) (x :: xs') (fun l => In x l) (or_introl eq_refl) xs (eq_sym Heq_xs)) acc in *)
(*                  let f' : forall x (y : B), In x xs' -> In y [] -> ACC -> ACC  := *)
(*                    fun x y INx INy acc' => *)
(*                      match INy with *)
(*                      end in *)
(*                  let f_left' : forall x', In x' xs' -> ACC -> ACC := *)
(*                    fun x' INx acc' => *)
(*                      f_left x' (@eq_ind (list A) (x :: xs') (fun l => In x' l) (or_intror INx) xs (eq_sym Heq_xs)) acc' in *)
(*                  let f_right' : forall y, In y [] -> ACC -> ACC := *)
(*                    fun y INy acc' => *)
(*                      match INy with *)
(*                      end in *)
(*                  zipWith_In' xs' [] acc' f' f_left' f_right' *)
(*            | (y::ys') => *)
(*                fun Heq_ys => *)
(*                  let acc' := f x y (@eq_ind (list A) (x :: xs') (fun l => In x l) (or_introl eq_refl) xs (eq_sym Heq_xs)) (@eq_ind (list B) (y :: ys') (fun l => In y l) (or_introl eq_refl) ys (eq_sym Heq_ys)) acc in *)
(*                  let f' : forall x (y : B), In x xs' -> In y ys' -> ACC -> ACC  := *)
(*                    fun x' y' INx INy acc' => *)
(*                      f x' y' (@eq_ind (list A) (x :: xs') (fun l => In x' l) (or_intror INx) xs (eq_sym Heq_xs)) (@eq_ind (list B) (y :: ys') (fun l => In y' l) (or_intror INy) ys (eq_sym Heq_ys)) acc' in *)
(*                  let f_left' : forall x', In x' xs' -> ACC -> ACC := *)
(*                    fun x' INx acc' => *)
(*                      f_left x' (@eq_ind (list A) (x :: xs') (fun l => In x' l) (or_intror INx) xs (eq_sym Heq_xs)) acc' in *)
(*                  let f_right' : forall y', In y' ys' -> ACC -> ACC := *)
(*                    fun y' INy acc' => *)
(*                      f_right y' (@eq_ind (list B) (y :: ys') (fun l => In y' l) (or_intror INy) ys (eq_sym Heq_ys)) acc' in *)
(*                  zipWith_In' xs' ys' acc' f' f_left' f_right' *)
(*            end eq_refl) *)
(*     end eq_refl. *)
(* Proof. *)
(* Admitted. *)

Lemma forallb_cons :
  forall {A} f x (xs : list A),
    forallb f (x :: xs) = andb (f x) (forallb f xs).
Proof.
  intros A f x xs.
  cbn.
  reflexivity.
Qed.

Lemma forallb_map_In_eq : forall A (l:list A) (f g : forall (x:A), In x l -> bool),
    (forall x H1 H2, f x H1 = g x H2) ->
    forallb id (map_In l f) = forallb id (map_In l g).
Proof.
  induction l; intros; simpl; try reflexivity.
  erewrite H. erewrite IHl. reflexivity.
  intros.
  erewrite H. reflexivity.
Qed.

Lemma allb_forallb :
  forall {A} (f : A -> bool) (xs : list A),
    allb f xs = forallb f xs.
Proof.
  induction xs; auto.
Qed.


  (* TODO: move this / does this exist somewhere else? *)
  Lemma nat_strong_rect :
    forall (P: nat -> Type)
      (BASE: P 0%nat)
      (IH: forall (n : nat), (forall (m : nat), m <= n -> P m)%nat -> P (S n)),
    forall n, P n.
  Proof.
    intros P BASE IH n.
    destruct n.
    - apply BASE.
    - apply IH.
      induction n; intros m LE.
      + assert (m=0)%nat by lia; subst; auto.
      + assert (m <= n \/ m = S n)%nat by lia.
        pose proof Nat.leb_spec0 m n.
        inv H0; subst; auto.
        pose proof Nat.eqb_spec m (S n).
        inv H0; subst; auto.
        exfalso.
        lia.
  Qed.


Lemma length_strong_rect:
  forall (X : Type) (P : list X -> Type)
         (BASE: P nil)
         (IH: forall (n : nat) (xs: list X), (forall (xs : list X), length xs <= n -> P xs)%nat -> length xs = S n -> P xs),
  forall l, P l.
Proof.
  intros X P BASE IH.
  assert (forall n l, length l <= n -> P l)%nat as IHLEN.
  { induction n using nat_strong_rect; intros l LEN; auto.
    assert (length l = 0)%nat as LEN' by lia.
    apply length_zero_iff_nil in LEN'; subst; auto.

      assert (length l <= n \/ length l = S n)%nat by lia.
      pose proof Nat.leb_spec0 (length l) n.
      inv H0; subst; eauto.
      pose proof Nat.eqb_spec (length l) (S n).
      inv H0; subst; eauto.
      lia.
    }

  intros l.
  eapply IHLEN.
  reflexivity.
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

(* Some facts missing from the list library.  Used in my example below. *)
Lemma Exists_In : forall {A} P (l : list A),
    Exists P l <-> exists a, In a l /\ P a.
Proof.
  intros.
  split; intros H. 
  - induction H.
    + exists x. split; auto. left; auto.
    +  destruct IHExists as [a [HI HP]].
       exists a. split; auto. right. assumption.
  - destruct H as [x [HI HP]].
    induction l.
    + inversion HI.
    + destruct HI.
      * subst. left. assumption.
      * right. apply IHl. assumption.
Qed.

Lemma Forall2_In : forall {A B} P (a:A) l1 (l2 : list B),
    In a l1 ->
    Forall2 P l1 l2 ->
    exists b, In b l2 /\ P a b.
Proof.
  induction l1; intros.
  - inversion H.
  - inversion H0; subst.
    inversion H; subst.
    + exists y. split; auto. left. auto.
    + specialize (IHl1 _ H1 H5).
      destruct IHl1 as [b [HI HP]].
      exists b.
      split; auto.
      right. assumption.
Qed.


Lemma Forall2_map_impl {A B C} : forall (P:A -> C -> Prop) (Q:B -> C -> Prop) (f:A -> B),
    (forall a c, P a c -> Q (f a) c) ->
    forall (l1 : list A) (l2 : list C) , Forall2 P l1 l2 -> Forall2 Q (map f l1) l2.
Proof.
  intros ? ? ? Himpl ? ? Hforall.
  induction Hforall; cbn; constructor; eauto.
Qed.

Lemma Forall2_map_r {A B C} : forall (P: A -> B -> Prop) (f:C -> B),
  forall (l1 : list A) (l2 : list C) , Forall2 P l1 (map f l2) <-> Forall2 (fun x y => P x (f y)) l1 l2.
Proof.
  intros P f l1 l2.
  split; intros H.
  - remember (map f l2) as l3.
    revert l2 Heql3.
    induction H; intros l2 EQ.
    + symmetry in EQ.
      apply map_eq_nil in EQ. subst.
      constructor.
    + symmetry in EQ.
      apply map_eq_cons in EQ.
      destruct EQ as [c [tl [EQ1 [EQ2 M]]]].
      subst.
      constructor; auto.
  - induction H; simpl; auto.
Qed.

Lemma Forall2_map_l {A B C} : forall (P: A -> B -> Prop) (f:C -> A),
  forall (l1 : list C) (l2 : list B) , Forall2 P (map f l1) l2 <-> Forall2 (fun x y => P (f x) y) l1 l2.
Proof.
  intros P f l1 l2.
  split; intros H.
  - remember (map f l1) as l3.
    revert l1 Heql3.
    induction H; intros l1 EQ.
    + symmetry in EQ.
      apply map_eq_nil in EQ. subst.
      constructor.
    + symmetry in EQ.
      apply map_eq_cons in EQ.
      destruct EQ as [c [tl [EQ1 [EQ2 M]]]].
      subst.
      constructor; auto.
  - induction H; simpl; auto.
Qed.

Lemma Forall2_eq {A} : 
  forall (l1 : list A) (l2 : list A) , Forall2 eq l1 l2 <-> l1 = l2.
Proof.
  intros l1 l2.
  split; intros H.
  - induction H; subst; auto.
  - revert l2 H.
    induction l1; intros l2 EQ; subst; auto.
Qed.

Lemma Forall2_ext_m : forall {A B} (f : A -> OOM B)
                             xs ys1 ys2,
    Forall2 (fun a b => f a = NoOom b) xs ys1 ->
    Forall2 (fun a b => f a = NoOom b) xs ys2 ->
    ys1 = ys2.
Proof.
  intros A B f xs ys1 ys2 H H0. 
  revert ys2 H0.
  induction H; intros ys2 F; inversion F; subst; auto.
  rewrite H in H3. inversion H3; subst.
  rewrite (IHForall2 l'0 H5).
  reflexivity.
Qed.

Lemma Forall2_inj_l :
  forall A B (f : A -> B) (g : A -> B) (l1 l2 : list A) (l : list B)
         (HINJ : forall a, In a l1 -> forall a', f a = g a' -> a' = a )
         (HL1: Forall2 (fun a b => f a = b) l1 l)
         (HL2: Forall2 (fun a b => g a = b) l2 l),
    l1 = l2.
Proof.
  intros A B f g l1 l2 l HINJ HL1.
  revert l2.
  induction HL1; intros l2 HL2; inversion HL2; subst; auto.
  assert (In x (x::l)) by (left; auto).
  eapply (HINJ x) with (a':=x0) in H; auto; subst.
  forward IHHL1.
  - intros; subst. eapply HINJ; eauto. right.  assumption.
  - rewrite (IHHL1 l0 H4).
    reflexivity.
Qed.

Lemma Forall2_inj_OOM_l :
  forall A B (f : A -> OOM B) (g : A -> OOM B) (l1 l2 : list A) (l : list B)
         (HINJ : forall a, In a l1 -> forall a' b, f a = NoOom b -> g a' = NoOom b -> a' = a )
         (HL1: Forall2 (fun a b => f a = NoOom b) l1 l)
         (HL2: Forall2 (fun a b => g a = NoOom b) l2 l),
    l1 = l2.
Proof.
  intros A B f g l1 l2 l HINJ HEQ1 HEQ2.
  rewrite <- (Forall2_map_r (fun a b => f a = b) NoOom) in HEQ1.
  rewrite <- (Forall2_map_r (fun a b => g a = b) NoOom) in HEQ2.
  eapply Forall2_inj_l; eauto.
  intros.
  rewrite (Forall2_map_r (fun a b => f a = b) NoOom) in HEQ1.
  destruct (Forall2_In _ a _ _ H HEQ1) as [b [_ HB]].
  eapply HINJ; eauto.
  rewrite <- H0.
  auto.
Qed.


Lemma Forall2_repeat_OOM : forall {A B} (f : A -> OOM B) (a:A) (b:B) n (l:list B),
    f a = ret b ->
    Forall2 (fun a b => f a = ret b) (repeat a n) l ->
    l = repeat b n.
Proof.
  intros A B f a b n l EQ F. 
  revert l EQ F.
  induction n; intros; cbn in *.
  - inversion F. reflexivity.
  - inversion F; subst.
    rewrite EQ in H1. inversion H1; subst.
    rewrite (IHn l'); auto.
Qed.

(* Better behaved version of Forall that can be used in recursive functions *)
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


Inductive Forall2T {A B : Type} (f : A -> B -> Type) : list A -> list B -> Type :=
| Forall2T_nil : Forall2T f [] []
| Forall2T_cons : forall a b l1 l2, (f a b) * Forall2T f l1 l2 -> Forall2T f (a::l1) (b::l2).

Lemma map_monad_oom_Forall2T : forall {A B : Type} (f : A -> OOM B) (l : list A) (res : list B),
    map_monad f l = NoOom res -> Forall2T (fun (a : A) (b : B) => f a = NoOom b) l res.
Proof.
  induction l; intros.
  - cbn in H. inversion H; subst. constructor.
  - cbn in H.
    repeat break_match_hyp_inv.
    constructor. split; auto.
Qed.

Lemma Forall2T_InT_r :
  forall {A B} (f : A -> B -> Type) (l1 : list A) (l2 : list B),
    Forall2T f l1 l2 -> forall b,
      InT b l2 -> { a : A & f a b * InT a l1}%type.
Proof.
  intros A B.
  fix IH 4.
  intros f l1 l2 H; inversion H; subst; clear H; intros x HX.
  - inversion HX.
  - inversion HX; subst.
    + destruct X as [HF HL].
      exists a. split; auto. left. auto.
    + destruct X as [_ HL].
      destruct (IH _ _ _ HL x X0) as [c [HFC HR]].
      exists c. split; auto. right. assumption.
Qed.


(*
  Lemma Forall2T_map_r1 {A B C} : forall (P: A -> B -> Prop) (f:C -> B),
      forall (l1 : list A) (l2 : list C) , Forall2T (fun x y => P x (f y)) l1 l2 -> Forall2T P l1 (map f l2).
  Proof.
    intros P f l1 l2 H.
    induction H; simpl; auto.
    constructor.
    constructor. 

  
  Lemma Forall2T_map_r {A B C} : forall (P: A -> B -> Prop) (f:C -> B),
      forall (l1 : list A) (l2 : list C) , Forall2T P l1 (map f l2) -> Forall2T (fun x y => P x (f y)) l1 l2.
  Proof.
    intros P f l1 l2.
    split; intros H.
    - remember (map f l2) as l3.
      revert l2 Heql3.
      induction H; intros l2 EQ.
      + symmetry in EQ.
        apply map_eq_nil in EQ. subst.
        constructor.
      + symmetry in EQ.
        apply map_eq_cons in EQ.
        destruct EQ as [c [tl [EQ1 [EQ2 M]]]].
        subst.
        constructor; auto.
    - induction H; simpl; auto.
  Qed.

  Lemma Forall2_map_l {A B C} : forall (P: A -> B -> Prop) (f:C -> A),
      forall (l1 : list C) (l2 : list B) , Forall2 P (map f l1) l2 <-> Forall2 (fun x y => P (f x) y) l1 l2.
  Proof.
    intros P f l1 l2.
    split; intros H.
    - remember (map f l1) as l3.
      revert l1 Heql3.
      induction H; intros l1 EQ.
      + symmetry in EQ.
        apply map_eq_nil in EQ. subst.
        constructor.
      + symmetry in EQ.
        apply map_eq_cons in EQ.
        destruct EQ as [c [tl [EQ1 [EQ2 M]]]].
        subst.
        constructor; auto.
    - induction H; simpl; auto.
  Qed.

  Lemma Forall2_eq {A} : 
      forall (l1 : list A) (l2 : list A) , Forall2 eq l1 l2 <-> l1 = l2.
  Proof.
    intros l1 l2.
    split; intros H.
    - induction H; subst; auto.
    - revert l2 H.
      induction l1; intros l2 EQ; subst; auto.
  Qed.

  Lemma Forall2_ext_m : forall {A B} (f : A -> OOM B)
      xs ys1 ys2,
        Forall2 (fun a b => f a = NoOom b) xs ys1 ->
        Forall2 (fun a b => f a = NoOom b) xs ys2 ->
        ys1 = ys2.
  Proof.
    intros A B f xs ys1 ys2 H H0. 
    revert ys2 H0.
    induction H; intros ys2 F; inversion F; subst; auto.
    rewrite H in H3. inversion H3; subst.
    rewrite (IHForall2 l'0 H5).
    reflexivity.
  Qed.
 *)

Lemma nth_error_cons :
  forall {X} (x : X) xs n res,
    nth_error xs n = res ->
    nth_error (x::xs) (S n) = res.
Proof.
  intros X x xs n res H.
  cbn; auto.
Qed.

Lemma double_list_rect :
  forall {X Y}
         (P: (list X * list Y) -> Type)
         (NilNil : P (nil, nil))
         (NilCons : forall y ys, P (nil, ys) -> P (nil, (y :: ys)))
         (ConsNil : forall x xs, P (xs, nil) -> P ((x :: xs), nil))
         (ConsCons : forall x xs y ys, P (xs, ys) -> P ((x :: xs), (y :: ys))),
  forall l, P l.
Proof.
  intros X Y P NilNil NilCons ConsNil ConsCons l.
  destruct l as [xs ys].
  revert ys.
  induction xs; induction ys.
  - apply NilNil.
  - apply NilCons.
    apply IHys.
  - apply ConsNil.
    apply IHxs.
  - apply ConsCons.
    apply IHxs.
Qed.



(* TODO: Move this to listutils or something *)
Lemma Forall2_take :
  forall {X Y} amount (xs : list X) (ys : list Y) P,
    Forall2 P xs ys ->
    Forall2 P (take amount xs) (take amount ys).
Proof.
  intros X Y amount xs ys P ALL.
  generalize dependent amount.
  induction ALL; intros amount.
  - cbn; auto.
  - destruct amount; cbn; auto.
Qed.

(* TODO: Move this to listutils or something *)
Lemma Forall2_drop :
  forall {X Y} amount (xs : list X) (ys : list Y) P,
    Forall2 P xs ys ->
    Forall2 P (drop amount xs) (drop amount ys).
Proof.
  intros X Y amount xs ys P ALL.
  generalize dependent amount.
  induction ALL; intros amount.
  - cbn; auto.
  - destruct amount; cbn; auto.
Qed.

(* TODO: Move this to listutils or something *)
Lemma Forall2_between :
  forall {X Y} (xs : list X) (ys : list Y) P start finish,
    Forall2 P xs ys ->
    Forall2 P (between start finish xs) (between start finish ys).
Proof.
  unfold between.
  intros X Y xs ys P start finish ALL.
  apply Forall2_take.
  apply Forall2_drop.
  auto.
Qed.

(* TODO: Move this to listutils or something *)
Lemma take_length :
  forall {X} (xs : list X) amount,
    (amount <= N.of_nat (length xs))%N ->
    length (take amount xs) = N.to_nat amount.
Proof.
  intros X xs.
  induction xs; intros amount LE.
  - destruct amount; cbn in *; auto.
    lia.
  - induction amount using N.peano_ind.
    + cbn in *; auto.
    + cbn.
      break_match_goal;
        break_match_hyp_inv; auto.

      cbn in *.
      rewrite IHxs;
        lia.
Qed.

(* TODO: Move this to listutils or something *)
Lemma drop_length :
  forall {X} (xs : list X) amount,
    (amount <= N.of_nat (length xs))%N ->
    length (drop amount xs) = (length xs - N.to_nat amount)%nat.
Proof.
  intros X xs.
  induction xs; intros amount LE.
  - destruct amount; cbn in *; auto.
  - induction amount using N.peano_ind.
    + cbn in *; auto.
    + cbn.
      break_match_goal;
        break_match_hyp_inv; auto.
      break_match_goal.
      lia.
      cbn in *.
      rewrite IHxs;
        lia.
Qed.

(* TODO: Move this to listutils or something *)
Lemma between_length :
  forall {X} (xs : list X) start finish,
    (start <= finish)%N ->
    (finish <= N.of_nat (length xs))%N ->
    length (between start finish xs) = N.to_nat (finish - start).
Proof.
  intros X xs start finish START_LE FINISH_LE.
  unfold between.
  apply take_length.
  pose proof drop_length xs start as DROP.
  forward DROP; lia.
Qed.

Lemma Forall2_In_exists2:
  forall {A B : Type} (f : A -> B -> Prop) (l1 : list A) (l2 : list B) (y : B),
    Forall2 f l1 l2 -> In y l2 -> exists x : A, In x l1 /\ f x y.
Proof.
  intros.
  induction H.
  - inversion H0.
  - inversion H0.
    + subst. exists x. split; auto. left; auto.
    + subst. destruct (IHForall2 H2) as [z [HI Hz]].
      exists z. split; auto. right; auto.
Qed.

Lemma list_nonempty_equiv : forall {A} (l : list A),
    l <> [] <-> exists x xs, l = x::xs.
Proof using.
  split.
  - intros. induction l.
    + destruct H. reflexivity.
    + exists a. exists l. reflexivity.
  - intros. destruct H as (x&xs&H).
    subst. discriminate.
Qed.

Lemma split_every_Forall2 :
  forall {A B} (P : A -> B -> Prop) xs ys xs' ys' n,
    Forall2 P xs ys ->
    split_every n xs = inr xs' ->
    split_every n ys = inr ys' ->
    Forall2 (Forall2 P) xs' ys'.
Proof.
  intros A B P xs ys xs' ys' n ALL SPLITX SPLITY.
  generalize dependent xs'.
  generalize dependent ys'.
  induction n.
  - intros. discriminate.
  - intros. unfold split_every in *. injection SPLITX. injection SPLITY.
    intros. clear SPLITX; clear SPLITY.
    rename H into SPLITY.
    rename H0 into SPLITX.
    generalize dependent ys.
    generalize dependent ys'.
    generalize dependent SPLITX.
    generalize dependent xs.
    generalize dependent p.
    induction xs'.
    + intros.
      apply split_every_pos_empty_equiv in SPLITX.
      subst. inversion ALL. constructor.
    + intros.
      generalize dependent xs.
      generalize dependent SPLITY.
      generalize dependent ys.
      generalize dependent p.
      induction ys'.
      ++
        intros.
        apply split_every_pos_empty_equiv in SPLITY.
        apply split_every_pos_nonempty_inv in SPLITX.
        apply list_nonempty_equiv in SPLITX.
        destruct SPLITX as (c&cs&SPLITX).
        subst. inversion ALL.
      ++ intros.
         apply split_every_pos_nonempty_take_drop in SPLITX; destruct SPLITX.
         apply split_every_pos_nonempty_take_drop in SPLITY; destruct SPLITY.
         subst.
         simpl in *.
         constructor.
         +++ apply Forall2_take. auto.
         +++ assert (H : split_every_pos A p (drop (N.pos p) xs) = split_every_pos A p (drop (N.pos p) xs)) by reflexivity.
             apply (IHxs' p (drop (N.pos p) xs) H (split_every_pos B p (drop (N.pos p) ys)) (drop (N.pos p) ys)).
             { apply Forall2_drop. auto. }
             { reflexivity. }
Qed.

Lemma split_every_nil_Forall2 :
  forall {A B} (P : A -> B -> Prop) xs ys xs' ys' n,
    Forall2 P xs ys ->
    split_every_nil n xs = xs' ->
    split_every_nil n ys = ys' ->
    Forall2 (Forall2 P) xs' ys'.
Proof.
  intros A B P xs ys xs' ys' n ALL SPLITX SPLITY.
  generalize dependent xs'.
  generalize dependent ys'.
  induction n.
  - intros.
    cbn in *.
    subst.
    constructor.
  - intros. unfold split_every in *.
    generalize dependent ys.
    generalize dependent ys'.
    generalize dependent SPLITX.
    generalize dependent xs.
    generalize dependent p.
    induction xs'.
    + intros.
      apply split_every_pos_empty_equiv in SPLITX.
      subst. inversion ALL. constructor.
    + intros.
      generalize dependent xs.
      generalize dependent SPLITY.
      generalize dependent ys.
      generalize dependent p.
      induction ys'.
      ++
        intros.
        apply split_every_pos_empty_equiv in SPLITY.
        apply split_every_pos_nonempty_inv in SPLITX.
        apply list_nonempty_equiv in SPLITX.
        destruct SPLITX as (c&cs&SPLITX).
        subst. inversion ALL.
      ++ intros.
         apply split_every_pos_nonempty_take_drop in SPLITX; destruct SPLITX.
         apply split_every_pos_nonempty_take_drop in SPLITY; destruct SPLITY.
         subst.
         simpl in *.
         constructor.
         +++ apply Forall2_take. auto.
         +++ assert (H : split_every_pos A p (drop (N.pos p) xs) = split_every_pos A p (drop (N.pos p) xs)) by reflexivity.
             apply (IHxs' p (drop (N.pos p) xs) H (split_every_pos B p (drop (N.pos p) ys)) (drop (N.pos p) ys)).
             { apply Forall2_drop. auto. }
             { reflexivity. }
Qed.

Lemma split_every_n_succeeds :
  forall {A B} (xs : list A) (ys : list B) n xs',
    split_every n xs = inr xs' ->
    exists ys', split_every n ys = inr ys'.
Proof.
  intros A B xs ys n xs' H.
  unfold split_every in *.
  destruct n; inv H.
  eexists; reflexivity.
Qed.

Lemma Forall_repeatN:
  forall (A : Type) (f : A -> Prop) (n : N) (x : A), f x -> Forall (fun y : A => f y) (repeatN n x).
Proof.
  intros. induction n using N.peano_ind.
  - cbn. constructor.
  - rewrite repeatN_succ.
    constructor. auto. apply IHn.
Qed.

Import Monoid.
#[global] Instance Foldable_list {a} : Foldable (list a) a.
split.
intros m M conv l.
apply (fold_left (fun acc x => monoid_plus M (conv x) acc) l (monoid_unit M)).
Defined.
