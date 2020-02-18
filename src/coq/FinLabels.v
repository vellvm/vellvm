From ITree Require Import
     ITree
     ITreeFacts
     Basics.Category
     Basics.CategorySub.

From Vellvm Require Import
     Util
     LLVMAst
     AstLib.

From Coq Require Import
     Arith
     List.
Import ListNotations.

(*
  In order to specify at the type level the interface an open control flow graph exposes,
  we need to work over a type of finite [block_id].
  This in term will allow us to work over the subcategory of [ktrees] when denoting such
  open control flow graphs, allowing us in term to define sound combinators.
  In contrast with the [asm] language from the [itree] tutorial, we work with non-canonical names.
 *)

Definition fin (l : list block_id) : Type := { x : (block_id * nat) | nth_error l (snd x) = Some (fst x) }.

(* Definition fin_single (bid: block_id) : fin [bid] := exist _ bid (or_introl (eq_refl)). *)

Lemma fin_nil {A} : fin [] -> A.
Proof.
  intros [[] ?].
  rewrite nth_error_nil in e.
  inversion e.
Qed.

(* [fin nil] is isomorphic to the empty set, it's the initial object of the subcategory *)
Instance FinInitial {E} : Initial (sub (ktree E) fin) [] := fun _ => fin_nil.

Program Definition split_fin_sum (a b : list block_id)
  : fin (a ++ b) -> (fin a) + (fin b) :=
  fun x =>
    match lt_dec (snd (proj1_sig x)) (length a) with
    | left Pf => inl (exist _ (proj1_sig x) _)
    | right Pf => inr (exist _ (fst (proj1_sig x),(snd (proj1_sig x) - length a)) _)
    end.
Next Obligation.
  destruct x as [[] ?]; cbn in *; rewrite nth_error_app1 in e; auto.
Defined.
Next Obligation.
  destruct x as [[] ?]; cbn in *; rewrite nth_error_app2 in e; auto with arith.
  generalize Pf; intros H; apply not_lt in H; auto.
Defined.

(* Might want this to compute *)
Lemma nth_error_mono_l: forall {A} (l l': list A) n x,
    nth_error l n = Some x ->
    nth_error (l ++ l') n = Some x.
Proof.
  induction l as [| a l IH]; cbn; intros l' n x H.
  - rewrite nth_error_nil in H; inversion H.
  - destruct n as [| n]; cbn in *; auto.
Defined.

Lemma nth_error_mono_r: forall {A} (l l': list A) n x,
    nth_error l' n = Some x ->
    nth_error (l ++ l') (length l + n) = Some x.
Proof.
  induction l as [| a l IH]; cbn; intros l' n x H; auto.
Defined.

Definition L (a b: list block_id): fin a -> fin (a ++ b) :=
  fun x =>
    match x with
    | exist (x,n) pf => exist _ (x,n) (nth_error_mono_l _ _ _ _ pf)
    end.

Definition R (a b: list block_id): fin b -> fin (a ++ b).
  intros [[] ?].
  refine (exist _ (b0, length a + n) _).
  apply nth_error_mono_r; assumption.
Defined.

Definition merge_fin_sum (a b: list block_id) : fin a + fin b -> fin (a ++ b) :=
  fun v =>
    match v with
    | inl v => L a b v
    | inr v => R a b v
    end.

Lemma nth_error_unique: forall {A: Type}
                          (eqdec: forall x y : A, {x = y} + {x <> y})
                          n (l: list A) x
                          (wit1 wit2: nth_error l n = Some x),
    wit1 = wit2.
Proof.
  induction n as [| n IH]; cbn; intros.
  - destruct l; cbn in *.
    inv wit1.
    inversion wit1.
    subst.
    apply Eqdep_dec.UIP_dec.
    decide equality.
  - destruct l; [inversion wit1 |].
    apply IH.
Qed.

Lemma unique_fin : forall n (i j : fin n),
    proj1_sig i = proj1_sig j -> i = j.
Proof.
  intros ? [] [] w. simpl in w; destruct w. f_equal.
  apply nth_error_unique.
  apply RawIDOrd.eq_dec.
Qed.

Require Import Lia.

Lemma merge_split:
  forall (a b: list block_id) (x : fin (a ++ b)),
    merge_fin_sum a b (split_fin_sum a b x) = x.
Proof.
  intros a b [[] Pf]. unfold split_fin_sum; simpl.
  destruct (lt_dec n (length a)) eqn:EQ.
  - cbn; apply unique_fin; reflexivity.
  - cbn; apply unique_fin.
    cbn; generalize n0; intros ineq; apply not_lt in ineq.
    f_equal.
    lia.
Qed.

Lemma split_merge:
  forall (a b : list block_id) (x : fin a + fin b), split_fin_sum a b (merge_fin_sum a b x) = x.
Proof.
  intros a b [[] | []]; unfold split_fin_sum; destruct x as [bk k]; cbn in *.
  - destruct lt_dec; cbn.
    f_equal; apply unique_fin; simpl; reflexivity.
    exfalso; cbn in *; apply nth_error_in in e; lia.
  - destruct lt_dec; cbn.
    exfalso; cbn in *; apply nth_error_in in e; lia.
    f_equal; apply unique_fin; simpl.
    f_equal; lia.
Qed.

Instance ToBifunctor_ktree_fin {E} : ToBifunctor (ktree E) fin sum (@app _) :=
  fun n m y => Ret (split_fin_sum n m y).

Instance FromBifunctor_ktree_fin {E} : FromBifunctor (ktree E) fin sum (@app _) :=
  fun n m y => Ret (merge_fin_sum n m y).

Instance IsoBif_ktree_fin {E}
  : forall a b, Iso (ktree E) (a := fin (app a b)) to_bif from_bif.
Proof.
  unfold to_bif, ToBifunctor_ktree_fin, from_bif, FromBifunctor_ktree_fin.
  constructor; intros x.
  - unfold cat, Cat_sub, Cat_Kleisli. cbn. rewrite bind_ret_l.
    apply eqit_Ret, merge_split.
  - unfold cat, Cat_sub, Cat_Kleisli. cbn. rewrite bind_ret_l.
    apply eqit_Ret, split_merge.
Qed.

Instance ToBifunctor_Fun_fin : ToBifunctor Fun fin sum (@app _) :=
  fun n m y => split_fin_sum n m y.

Instance FromBifunctor_Fun_fin : FromBifunctor Fun fin sum (@app _) :=
  fun n m y => merge_fin_sum n m y.

Instance IsoBif_Fun_fin
  : forall a b, Iso Fun (a := fin (app a b)) to_bif from_bif.
Proof.
  constructor; intros x.
  - apply merge_split.
  - apply split_merge.
Qed.

Instance InitialObject_ktree_fin {E} : InitialObject (sub (ktree E) fin) [].
Proof.
  intros n f x; apply fin_nil; auto.
Qed.
