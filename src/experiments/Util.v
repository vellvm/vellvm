Require Import Ensembles.
Require Export List.
Require Export Arith.
Require Import Sorted.
Require Export Coqlib.
Require Import Program.Tactics.
Require Import Permutation.
Require Export CoqEqDec.
Import RelationClasses.
Export ListNotations.

Set Implicit Arguments.

Close Scope Z.

Lemma conjI1 : forall (P1 P2 : Prop), P1 -> (P1 -> P2) -> P1 /\ P2.
Proof. auto. Qed.

Definition fun_upd A B {_ : EqDec_eq A} (f : A -> B) x y z :=
  if eq_dec z x then y else f z.

Instance list_eq A (_ : EqDec_eq A) : EqDec_eq (list A).
Proof. eq_dec_inst. Qed.

Inductive Forall3 {A B C:Type} (R:A -> B -> C -> Prop) 
: list A -> list B -> list C -> Prop :=
| Forall3_nil : Forall3 R nil nil nil
| Forall3_cons : forall x y z l m n, 
  R x y z -> Forall3 R l m n -> Forall3 R (x::l) (y::m) (z::n).

Fixpoint replicate A (a:A) (n:nat) : list A :=
  match n with
  | O => nil
  | S n' => a :: replicate a n'
  end.

Fixpoint flatten A (ll: list (list A)): list A :=
  match ll with
  | nil => nil
  | hd :: tl => hd ++ flatten tl
  end.

Fixpoint remdups A {A_eq : EqDec_eq A} (l : list A) : list A :=
  match l with
  | [] => []
  | x :: rest => if in_dec A_eq x rest then remdups rest else x :: remdups rest
  end.

(* The clarify and clarsimp tactics. *)
Lemma prod_eq : forall {A B} (x1 x2 : A) (y1 y2 : B), x1 = x2 -> y1 = y2 ->
  (x1, y1) = (x2, y2).
Proof. congruence. Qed.

Lemma prod_eq_iff : forall {A B} (x1 x2 : A) (y1 y2 : B), ((x1, y1) = (x2, y2))
  <-> (x1 = x2 /\ y1 = y2).
Proof.
  split.
  - intro H; inversion H; auto.
  - intro H; destruct H; subst; auto.
Qed.

Lemma eq_dec_refl: forall {A B} {E : EqDec_eq A} (a : A) (b c : B), 
  (if eq_dec a a then b else c) = b.
Proof.
  intros; destruct (eq_dec a a); auto.
  contradiction n; auto.
Qed.

Corollary beq_refl : forall {A B} {E : EqDec_eq A} (a : A) (b c : B), 
  (if beq a a then b else c) = b.
Proof. unfold beq; intros; rewrite eq_dec_refl; auto. Qed.

Import Bool.
Hint Rewrite andb_true_iff andb_false_iff orb_true_iff orb_false_iff
  andb_true_l andb_true_r andb_false_l andb_false_r andb_diag
  orb_true_l orb_true_r orb_false_l orb_false_r orb_diag NPeano.Nat.eqb_refl :
  util.

Lemma must_be_Some : forall (A B : Type) (a : option A) (f : A -> option B) c, 
  match a with Some b => f b | None => None end = Some c <->
  exists b, a = Some b /\ f b = Some c.
Proof. 
  intros; destruct a; split; intros; try discriminate; eauto 3;
    destruct H as [? [H ?]]; inversion H; auto.
Qed.

Lemma must_be_None : forall (A B : Type) (a : option A) (f : A -> B) c, 
  match a with Some b => Some (f b) | None => c end = None <->
  a = None /\ c = None.
Proof. 
  intros; destruct a; split; intros; try discriminate; eauto 3;
    destruct H as [? ?]; inversion H; auto.
Qed.

Lemma match_match : forall (A : Type) (a : option A), 
  match a with Some b => Some b | None => None end = a.
Proof. intros; destruct a; auto. Qed.

Hint Rewrite must_be_Some must_be_None match_match : util.

(* General useful tactic; solve obvious goals and simplify, quickly. *)
Ltac clarify_once n := intros; unfold value in *; clear_dups;
repeat match goal with
| [H : True |- _] => clear H
| [|- (?a, ?b) = (?c, ?d)] => repeat (*first [setoid_rewrite prod_eq_iff
  | rewrite prod_eq_iff]*) apply prod_eq; auto
(* The former should work, and is preferable because it doesn't produce new
   goals. Unfortunately, there are many situations in which both rewrite
   and setoid_rewrite fail for reasons I don't understand. *)
| [H : ?a = ?b, H' : ?b = ?a |- _] => clear H
| [H : context[if eq_dec ?a ?a then ?b else ?c] |- _] => rewrite eq_dec_refl in H
| [|- context[if eq_dec ?a ?a then ?b else ?c]] => rewrite eq_dec_refl
| [H : context[if beq ?a ?a then ?b else ?c] |- _] => rewrite beq_refl in H
| [|- context[if beq ?a ?a then ?b else ?c]] => rewrite beq_refl
| [H: exists x, ?P |- _] => destruct H as [? H]
| [H: ?P /\ ?Q |- _] => let H1 := fresh H "1" in let H2 := fresh H "2" in
    destruct H as [H1 H2]; try (clear H)
| [H: Some ?x = Some ?y |- _] => inversion H; clear H
| [H: (?a, ?b) = (?c, ?d) |- _] => inversion H; clear H
| [H: ?a :: ?b = ?c :: ?d |- _] => inversion H; clear H
| [H : ?a = ?a |- _] => clear H
| [H : ?a = ?a -> ?P |- _] => specialize (H eq_refl)
(*| [H : forall x, ?a = ?b -> ?P |- _] => specialize (H _ eq_refl)
| [H : forall x1 x2, ?a = ?b -> ?P |- _] => specialize (H _ _ eq_refl)
| [H : forall x1 x2 x3, ?a = ?b -> ?P |- _] => specialize (H _ _ _ eq_refl)
| [H : forall x1 x2 x3 x4, ?a = ?b -> ?P |- _] => specialize (H _ _ _ _ eq_refl)
| [H : forall x1 x2 x3 x4 x5, ?a = ?b -> ?P |- _] => specialize (H _ _ _ _ _ eq_refl)*)
(* This is useful when right, but can eliminate non-trivial equality hypotheses
   by instantiating them trivially. *)
| [H : ?a <> ?a |- _] => contradiction H; apply eq_refl
| [H : ?P -> ?Q, H' : ?P |- _] => specialize (H H')
| [H : ?P \/ False |- _] => destruct H; [| exfalso; auto]
| [H : False \/ ?P |- _] => destruct H; [exfalso; auto |]
| [H : ?P \/ ?Q \/ False |- _] => let H' := fresh in assert (P \/ Q) as H' by (destruct H as [? | [? | ?]]; [left; auto | right; auto | exfalso; auto]); 
    clear H; rename H' into H
| [H : ?P \/ ?P |- _] => let H' := fresh in assert P as H' by (destruct H; auto); clear H; rename H' into H
| [H : ?a = Some ?b |- context[match ?a with Some c => _ | None => _ end]] => rewrite H
| [H1 : ?b = true, H2 : ?b = false |- _] => first [setoid_rewrite H1 in H2 
  | rewrite H1 in H2]; discriminate
| [H1 : ?b = Some ?c, H2 : ?b = None |- _] => first [setoid_rewrite H1 in H2 
  | rewrite H1 in H2]; discriminate
| [H : match ?a with Some b => ?f | None => None end = Some ?c |- _]
  => first [setoid_rewrite must_be_Some in H | rewrite must_be_Some in H]
| [H : match ?a with Some b => ?f b | None => None end = None |- _] =>
     first [setoid_rewrite must_be_None in H | rewrite must_be_None in H]
| [H : context[match ?a with Some b => Some b | None => None end] |- _] =>
     first [setoid_rewrite match_match in H | rewrite match_match in H]
| [|- ?P /\ ?Q] => match n with O => fail 
  | S ?n' => first [split; [solve [auto; clarify_once n'] |] | 
                    split; [| solve [auto; clarify_once n']]] end
| [H : ?P \/ ?Q |- _] => match n with O => fail 
  | S ?n' => first [destruct H as [H | H]; [solve [auto; clarify_once n'] |] | 
                    destruct H as [H | H]; [| solve [auto; clarify_once n']]] end
| [H: context[if ?a then ?b else ?c] |- _] => match n with O => fail 
  | S ?n' => let cond := fresh "cond" in 
    first [destruct a eqn: cond; [solve [auto; clarify_once n'] |] | 
           destruct a eqn: cond; [| solve [auto; clarify_once n']]] end
| [|- context[if ?a then ?b else ?c]] => match n with O => fail 
  | S ?n' => let cond := fresh "cond" in 
    first [destruct a eqn: cond; [solve [auto; clarify_once n'] |] | 
           destruct a eqn: cond; [| solve [auto; clarify_once n']]] end
| [H : ?X -> _ |- _] => let H' := fresh in assert X as H' 
    by auto; specialize (H H'); clear H'
end; simpl in *; try subst; try discriminate; try contradiction; auto.
(* It would be really nice if clarify didn't instantiate metavariables.
   However, congruence seems to be the only tactic that will solve x = x but
   not ?x = x, and it doesn't solve many other obvious things. Is there a
   "auto that doesn't instantiate metavariables?" It seems not. *)
Ltac clarify_n n := repeat clarify_once n.
Ltac clarify := repeat clarify_once (S O).

Ltac clarsimp := repeat (try clarify; repeat rewrite <- app_assoc in *; 
  autorewrite with core util list in *; try clarify;
  repeat match goal with 
  | [H : ?a = ?b, H' : context[?a] |- _] => first [rewrite H in H' | 
      setoid_rewrite H in H']
  | [H : ?a = ?b |- context[?a]] => first [rewrite H | setoid_rewrite H] end;
  clarify).

Definition nil_dec A (l : list A) : {l = []} + {l <> []}.
Proof. destruct l; [left | right]; clarify. Defined.

Lemma find_success : forall A P (l : list A) x, find P l = Some x ->
  In x l /\ P x = true.
Proof. intros; induction l; inversion H; clarify. Qed.

Lemma find_succeeds : forall A P (l : list A) x, In x l -> P x = true -> 
  exists y, find P l = Some y.
Proof.
  intros; induction l; clarify.
  destruct (P a) eqn: is_P; clarify; eauto.
Qed.
Hint Resolve find_success find_succeeds.

Lemma find_fail: forall A (f : A -> bool) (l : list A),
  find f l = None <-> Forall (fun x : A => f x = false) l.
Proof.
  induction l; split; clarify.
  - constructor; auto; rewrite <- IHl; auto.
  - inversion H; clarify; rewrite IHl; auto.
Qed.

Lemma app_eq_inv : forall A (l1 l2 l1' l2' : list A)
  (Hlen : length l1 = length l1') (Heq : l1 ++ l2 = l1' ++ l2'),
  l1 = l1' /\ l2 = l2'.
Proof.
  induction l1; destruct l1'; clarify.
  inversion Hlen; specialize (IHl1 _ _ _ H0 H1); clarify.
Qed.

Lemma app_eq_inv_ge : forall A (l1 l2 l1' l2' : list A)
  (Heq : l1 ++ l2 = l1' ++ l2') (Hgt : length l1 <= length l1'),
  exists l', l2 = l' ++ l2' /\ l1' = l1 ++ l'.
Proof.
  induction l1; clarify; eauto.
  destruct l1'; clarify; [omega|].
  exploit IHl1; eauto; clarify; eauto; omega.
Qed.

Lemma find_app: forall A f (l l' : list A), find f (l ++ l') =
  match find f l with Some x => Some x | None => find f l' end.
Proof. induction l; clarify. Qed.
Hint Rewrite find_app : list.

Hint Rewrite nth_error_nil : list.
Hint Resolve lt_0_Sn lt_n_S lt_irrefl.

Lemma nth_error_single : forall A (x : A) i,
  nth_error [x] i = match i with 0 => Some x | _ => None end.
Proof. destruct i; clarsimp. Qed.
Hint Rewrite nth_error_single : util.

Ltac use H := lapply H; clear H; [intro H | clarify].

Lemma find_spec : forall A (f : A -> bool) l x,
  (find f l = Some x) <-> (exists i, nth_error l i = Some x /\ f x = true /\
    forall j y, j < i -> nth_error l j = Some y -> f y = false).
Proof.
  induction l; clarify.
  { split; clarsimp. }
  destruct (f a) eqn: Ha.
  - split; intro Hfind; clarify.
    + exists 0; clarify; omega.
    + destruct x0; clarify.
      specialize (Hfind22 0 a); clarify.
  - rewrite IHl; split; intro Hfind; clarify.
    + exists (S x0); clarify.
      destruct j; clarify.
      specialize (Hfind22 j y); use Hfind22; clarify; omega.
    + destruct x0; clarify.
      exists x0; clarify; eauto.
Qed.

Lemma partition_In1: forall A (x : A) f l, In x (fst (partition f l)) <-> In x l /\ f x = true.
Proof.
  induction l; clarify.
  - split; clarify.
  - destruct (partition f l) eqn: part; simpl in *.
    destruct (f a) eqn: prop; clarify; rewrite IHl; clarify; split; clarify.
Qed.

Lemma partition_In2: forall A (x : A) f l, In x (snd (partition f l)) <-> In x l /\ f x = false.
Proof.
  induction l; clarify.
  - split; clarify.
  - destruct (partition f l) eqn: part; simpl.
    destruct (f a) eqn: prop; clarify; rewrite IHl.
    + split; clarify; destruct H; clarify.
    + split; clarify; destruct H; clarify.
Qed.

Lemma partition_filter : forall A f (l : list A),
  partition f l = (filter f l, filter (fun x => negb (f x)) l).
Proof.
  induction l; clarsimp.
Qed.

Lemma exists_not_None : forall A (x : option A), (exists y, x = Some y) <-> (x <> None).
Proof. intros; destruct x; split; clarify; eauto. Qed.

Hint Rewrite minus_diag : util.

Lemma lt_dec_eq : forall A i (a b : A), (if lt_dec i i then a else b) = b.
Proof.
  intros; destruct (lt_dec i i); [omega | auto].
Qed.

Lemma lt_dec_S : forall A i (a b : A), (if lt_dec (S i) i then a else b) = b.
Proof.
  intros; destruct (lt_dec (S i) i); [omega | auto].
Qed.
Hint Rewrite lt_dec_eq lt_dec_S : util.

Lemma lt_dec_plus_l : forall A i j (a b : A),
  (if lt_dec i (i + S j) then a else b) = a.
Proof. intros; destruct (lt_dec i (i + S j)); [auto | omega]. Qed.
        
Lemma lt_dec_plus_r : forall A i j (a b : A),
  (if lt_dec (i + j) i then a else b) = b.
Proof. intros; destruct (lt_dec (i + j) i); [omega | auto]. Qed.
Hint Rewrite lt_dec_plus_l lt_dec_plus_r : util.
Hint Rewrite minus_plus NPeano.Nat.add_sub NPeano.Nat.add_1_r : util.

Lemma lt_dec_mono : forall A i j (a b : A), 
  (if lt_dec (S i) (S j) then a else b) = if lt_dec i j then a else b.
Proof.
  intros; destruct (lt_dec (S i) (S j)), (lt_dec i j); auto; omega.
Qed.

Lemma minus_comm : forall a b c, a >= b + c -> a - b - c = a - c - b.
Proof. intros; omega. Qed.

Lemma plus_minus_comm : forall a b c, a >= c -> a + b - c = a - c + b.
Proof. intros; omega. Qed.

Lemma minus_distr : forall a b c (Hge : a >= b) (Hle : c <= b),
  a - (b - c) = a - b + c.
Proof. intros; omega. Qed.

Lemma minus_lt_compat : forall a b c (Hle : c <= a),
  a < b <-> a - c < b - c.
Proof. intros; omega. Qed.

Lemma lt_plus : forall a b, ~a + b < a.
Proof. intros; omega. Qed.

Lemma nth_error_app : forall A n (l l' : list A),
  nth_error (l ++ l') n = if lt_dec n (length l) then nth_error l n
    else nth_error l' (n - length l).
Proof.
  induction n; destruct l; clarify.
  rewrite lt_dec_mono; auto.
Qed.

Corollary nth_error_split : forall A (l l' : list A) x,
  nth_error (l ++ x :: l') (length l) = Some x.
Proof. intros; rewrite nth_error_app; clarsimp. Qed.

Lemma nth_error_plus : forall A (l1 l2 : list A) i,
  nth_error (l1 ++ l2) (length l1 + i) = nth_error l2 i.
Proof.
  intros; rewrite nth_error_app, lt_dec_plus_r, minus_plus; auto.
Qed.

Lemma nth_flatten_split : forall A l (i : nat) (x : A)
  (Hnth : nth_error (flatten l) i = Some x),
  exists l1 lx l2 i', l = l1 ++ lx :: l2 /\ nth_error lx i' = Some x /\
    i = length (flatten l1) + i'.
Proof.
  induction l; clarsimp.
  rewrite nth_error_app in Hnth; destruct (lt_dec i (length a)).
  - exists [], a, l, i; clarify.
  - specialize (IHl _ _ Hnth); clarify.
    exists (a :: x0), x1, x2, x3; clarify.
    rewrite app_length; omega.
Qed.

Lemma split_app : forall A (l1 l2 : list A) x,
  l1 ++ x :: l2 = (l1 ++ [x]) ++ l2.
Proof. clarsimp. Qed.

Lemma firstn_nil : forall A n, firstn n (nil(A := A)) = [].
Proof. destruct n; auto. Qed.

Lemma skipn_nil : forall A n, skipn n (nil(A := A)) = [].
Proof. destruct n; auto. Qed.

Hint Rewrite firstn_nil skipn_nil firstn_length : list.

Hint Rewrite NPeano.Nat.sub_0_r : util.
Lemma skipn_length : forall A n (l : list A), length (skipn n l) =
  length l - n.
Proof.
  induction n; clarsimp.
  destruct l; clarify.
Qed.
Hint Rewrite skipn_length : list.  

Lemma skipn_all : forall A n (l : list A) (Hle : length l <= n),
  skipn n l = [].
Proof.
  induction n; destruct l; clarify.
  - omega.
  - apply IHn; omega.
Qed.

Corollary skipn_length' : forall A (l : list A), skipn (length l) l = [].
Proof. intros; apply skipn_all; auto. Qed.

Lemma nth_error_lt : forall A (l : list A) n a,
  nth_error l n = Some a -> lt n (length l).
Proof.
  induction l; intros; destruct n; simpl in *; inversion H; subst.
  - omega.
  - specialize (IHl _ _ H); omega.
Qed.

Lemma skipn_nth : forall A n (l : list A) i, nth_error (skipn n l) i =
  nth_error l (i + n).
Proof.
  intros; destruct (lt_dec n (length l)).
  - rewrite <- (firstn_skipn n l) at 2.
    rewrite nth_error_app.
    rewrite List.firstn_length.
    generalize (Min.min_spec n (length l)); intros [? | ?]; clarsimp; omega.
  - rewrite skipn_all; clarsimp; [|omega].
    destruct (nth_error l (i + n)) eqn: Hnth; auto.
    generalize (nth_error_lt _ _ Hnth); omega.
Qed.

Lemma skipn_skipn : forall A j i (l : list A),
  skipn i (skipn j l) = skipn (j + i) l.
Proof. induction j; destruct l; clarsimp. Qed.

Lemma firstn_app : forall A n (l l' : list A), firstn n (l ++ l') =
  firstn n l ++ firstn (n - length l) l'.
Proof.
  induction n; clarify.
  destruct l; clarify.
  rewrite IHn; auto.
Qed.

Lemma skipn_app : forall A n (l l' : list A), skipn n (l ++ l') =
  skipn n l ++ skipn (n - length l) l'.
Proof.
  induction n; clarify.
  destruct l; clarify.
Qed.

Hint Rewrite firstn_app skipn_app : list.

Hint Rewrite plus_0_r : util.

Lemma firstn_firstn : forall A n n' (l : list A), firstn n (firstn n' l) =
  firstn (min n n') l.
Proof.
  induction n; destruct n', l; clarify.
  rewrite IHn; auto.
Qed.

Corollary firstn_n : forall A n (l : list A), firstn n (firstn n l) =
  firstn n l.
Proof. intros; rewrite firstn_firstn, Min.min_idempotent; auto. Qed.
Hint Rewrite firstn_n : list.

Lemma firstn_length' : forall A n (l : list A) (Hge : length l <= n),
  firstn n l = l.
Proof.
  induction n; destruct l; clarify; try omega.
  rewrite IHn; auto; omega.
Qed.

Lemma nth_error_firstn : forall A n (l : list A) i,
  nth_error (firstn n l) i = if lt_dec i n then nth_error l i else None.
Proof.
  induction n; clarsimp.
  destruct l, i; clarsimp.
  rewrite lt_dec_mono; auto.
Qed.

Lemma skipn_but_one : forall A (l : list A) x
  (Hnth : nth_error l (length l - 1) = Some x),
  skipn (length l - 1) l = [x].
Proof.
  induction l using rev_ind; clarify.
  rewrite app_length; clarsimp.
  rewrite nth_error_split in Hnth; clarify.
  rewrite skipn_all; auto.
Qed.

Lemma skipn_n : forall A n (l : list A) x (Hnth : nth_error l n = Some x),
  skipn n l = x :: skipn (S n) l.
Proof. induction n; destruct l; clarify. Qed.

Lemma in_nth_error : forall A (l : list A) x, In x l ->
  exists n, n < length l /\ nth_error l n = Some x.
Proof.
  induction l; clarify.
  destruct H; clarify.
  - exists O; split; clarify.
  - specialize (IHl _ H); destruct IHl as [n ?]; exists (S n); clarify.
Qed.

Lemma in_nth : forall A (x : A) l d, In x l ->
  exists i, i < length l /\ nth i l d = x.
Proof.
  induction l; clarify.
  destruct H; clarify.
  - exists 0; auto.
  - specialize (IHl d H); destruct IHl as [i ?].
    exists (S i); clarify.
Qed.

Lemma in_nth_iff : forall A (l : list A) x,
  In x l <-> exists n, nth_error l n = Some x.
Proof.
  split; clarify.
  - exploit in_nth_error; eauto; clarify; eauto.
  - eapply nth_error_in; eauto.
Qed.

Lemma find_nth_error : forall A (l : list A) P x,
  find P l = Some x -> exists n, n < length l /\
    nth_error l n = Some x /\ P x = true.
Proof.
  intros; exploit @find_success; eauto; clarify.
  exploit @in_nth_error; eauto; clarify; eauto.
Qed.

Hint Rewrite beq_nat_true_iff : util.

Lemma Forall_app : forall A P (l l': list A), Forall P (l ++ l') <->
  Forall P l /\ Forall P l'.
Proof.
  intros; induction l; clarify; split; clarsimp.
  - inversion H; clarify.
    rewrite IHl in *; clarify.
  - inversion H1; clarify; constructor; auto.
    rewrite IHl; clarify.
Qed.

Lemma Forall_snoc: forall A (P : A -> Prop) x xs,
  Forall P (xs ++ [x]) <-> P x /\ Forall P xs.
Proof.
  intros; induction xs; intros; split; clarify.
  - inversion H; auto.
  - inversion H; clarify.
    rewrite IHxs in *; clarify.
  - inversion H2; clarify.
    constructor; auto.
    rewrite IHxs; auto.
Qed.

Lemma Forall_rev : forall A P (l : list A), Forall P (rev l) <->
  Forall P l.
Proof.
  intros; induction l; clarify; split; clarify.
  - rewrite Forall_app in H; clarify.
    rewrite IHl in *; inversion H2; constructor; auto.
  - inversion H; rewrite Forall_app; rewrite IHl; clarify.
Qed.

Lemma Forall_skipn : forall A P (l : list A) n (Hforall : Forall P l),
  Forall P (skipn n l).
Proof.
  intros; rewrite <- (firstn_skipn n), Forall_app in Hforall; clarify.
Qed.

Definition Exists_dec : forall A (P : A -> Prop) l
  (Hdec : forall x, In x l -> {P x} + {~P x}),
  {Exists P l} + {Forall (fun x => ~P x) l}.
Proof.
  induction l; clarify.
  specialize (Hdec a); clarify.
  destruct Hdec; [left; auto|].
  destruct IHl; [left | right]; auto.
Qed.

Fixpoint subset A {A_eq : EqDec_eq A} (l l' : list A) :=
  match l with
  | [] => true
  | a :: rest => if In_dec A_eq a l' then subset rest l' else false
  end.

Lemma subset_spec : forall A (A_eq : EqDec_eq A) l l',
  subset l l' = true <-> forall x, In x l -> In x l'.
Proof.
  induction l; split; clarify.
  - rewrite IHl in H; auto.
  - rewrite IHl; auto.
Qed.

Definition set_eq A {A_eq : EqDec_eq A} l l' := subset l l' && subset l' l.

Lemma set_eq_spec : forall A (A_eq : EqDec_eq A) l l',
  set_eq l l' = true <-> forall x, In x l <-> In x l'.
Proof.
  unfold set_eq; split; unfold andb; clarify.
  - rewrite subset_spec in *; split; auto.
  - assert (subset l l' = true).
    + rewrite subset_spec; intro x; specialize (H x); destruct H; auto.
    + clarify.
      rewrite subset_spec; intro x; specialize (H x); destruct H; auto.
Qed.

Lemma subset_cons : forall A (A_eq : EqDec_eq A) l (x : A) l',
  implb (subset l l') (subset l (x :: l')) = true.
Proof. induction l; clarify. Qed.

Lemma subset_mono : forall A (A_eq : EqDec_eq A) l (x : A) l' (Hin : In x l'),
  subset l (x :: l') = subset l l'.
Proof.
  induction l; clarify.
  destruct (A_eq x a); clarify.
Qed.

Lemma subset_false : forall A (A_eq : EqDec_eq A) (l l' : list A),
  subset l l' = false -> exists x, In x l /\ ~In x l'.
Proof.
  induction l; clarify.
  destruct (in_dec _ a l'); clarify; eauto.
  specialize (IHl l'); clarify; eauto.
Qed.

Lemma set_eq_false : forall A (A_eq : EqDec_eq A) (l l' : list A),
  set_eq l l' = false ->
  exists x, In x l /\ ~In x l' \/ In x l' /\ ~In x l.
Proof.
  unfold set_eq, andb; intros.
  destruct (subset l l') eqn: Hsub; clarify; exploit subset_false; eauto;
    clarify; eauto.
Qed.

Lemma nth_error_rev_iff : forall A (l : list A) i x (Hlt : i < length l),
  nth_error (rev l) (length l - i - 1) = Some x <-> nth_error l i = Some x.
Proof.
  induction l.
  { split; clarsimp. }
  clarify; rewrite nth_error_app; destruct i; clarsimp.
  - reflexivity.
  - destruct (lt_dec (length l - i - 1) (length l)); [apply IHl|]; omega.
Qed.      

Corollary nth_error_rev : forall A (l : list A) i x
  (Hnth : nth_error l i = Some x),
  nth_error (rev l) (length l - i - 1) = Some x.
Proof. intros; rewrite nth_error_rev_iff; auto; eapply nth_error_lt; eauto. Qed.

Corollary nth_error_rev' : forall A (l : list A) i x
  (Hnth : nth_error (rev l) i = Some x),
  nth_error l (length l - i - 1) = Some x.
Proof.
  intros; rewrite <- (rev_involutive l), rev_length; apply nth_error_rev; auto.
Qed.

Lemma Sorted_app : forall A R (l1 l2 : list A),
  Sorted R (l1 ++ l2) -> Sorted R l1 /\ Sorted R l2.
Proof.
  induction l1; clarify.
  inversion H; clarify.
  exploit IHl1; eauto; clarify.
  constructor; auto.
  inversion H3; destruct l1; clarify.
Qed.

Lemma Sorted_all : forall A (R : A -> A -> Prop) (T : Transitive R)
  x l (HR : HdRel R x l) (Hsort : Sorted R l),
  Forall (fun y => R x y) l.
Proof.
  induction l; clarify.
  inversion HR; inversion Hsort; clarify.
  constructor; auto.
  apply IHl; auto.
  destruct l; clarify; constructor.
  inversion H5; clarify.
  etransitivity; eauto.
Qed.

Lemma Sorted_inj : forall A R (T : Transitive R) (l : list A)
  (Hsort : Sorted R l) i j (Hlt : i < j)
  a b (Ha : nth_error l i = Some a) (Hb : nth_error l j = Some b),
  R a b.
Proof.
  induction l; clarsimp.
  inversion Hsort; clarify.
  destruct i, j; clarify; try omega.
  - exploit nth_error_lt; eauto; intro.
    destruct l; clarify; [omega|].
    exploit Sorted_all; eauto; intro Hall.
    exploit nth_error_in; eauto; intro Hin.
    rewrite Forall_forall in Hall; apply Hall; auto.
  - apply (IHl i j); auto; omega.
Qed.
      
Lemma Sorted_last : forall A R (T : Transitive R) (l : list A) x
  (Hsort : Sorted R (l ++ [x])),
  Forall (fun y => R y x) l.
Proof.
  intros; rewrite Forall_forall; intros.
  exploit in_nth_error; eauto; clarify.
  exploit Sorted_inj; eauto.
  - rewrite nth_error_app; clarify.
  - apply nth_error_split.
Qed.

Fixpoint list_max_aux l m :=
  match l with
  | [] => m
  | i :: rest => list_max_aux rest (max m i)
  end.
Definition list_max l := list_max_aux l 0.

Lemma list_max_aux_mono : forall l m, m <= list_max_aux l m.
Proof.
  induction l; clarify.
  etransitivity; [apply Max.le_max_l | apply IHl].
Qed.

Lemma list_max_aux_spec : forall l m,
  list_max_aux l m = m /\ Forall (fun i => i < m) l \/ 
  In (list_max_aux l m) l /\ Forall (fun i => i <= list_max_aux l m) l.
Proof.
  induction l; clarify.
  specialize (IHl (max m a)).
  destruct (le_dec m a).
  - rewrite Max.max_r in *; auto.
    right; destruct IHl; clarsimp.
    + constructor; auto.
      eapply Forall_impl; eauto; clarify; omega.
    + constructor; auto.
      apply list_max_aux_mono.
  - rewrite Max.max_l in *; try omega.
    destruct IHl; clarsimp.
    + left; clarify; constructor; auto; omega.
    + right; clarify; constructor; auto.
      transitivity m; [omega | apply list_max_aux_mono].
Qed.

Lemma list_max_spec : forall l, l = [] \/ In (list_max l) l /\
  Forall (fun i => i <= list_max l) l.
Proof.
  intro; generalize (list_max_aux_spec l 0); intros [? | ?]; auto.
  destruct l; clarify.
  inversion H2; omega.
Qed.

Fixpoint interval n m := 
  match m with
  | O => []
  | S j => if le_lt_dec n j then interval n j ++ [j] else []
  end.

Lemma interval_lt : forall m n, Forall (fun x => lt x m) (interval n m).
Proof.
  induction m; simpl; auto; intros.
  destruct (le_lt_dec n m); auto.
  rewrite Forall_app; split; auto.
  eapply Forall_impl; eauto; auto.
Qed.

Lemma interval_ge : forall m n, Forall (fun x => ge x n) (interval n m).
Proof.
  induction m; simpl; auto; intros.
  destruct (le_lt_dec n m); auto.
  rewrite Forall_app; split; auto.
Qed.

Lemma interval_nil : forall n, interval n n = [].
Proof.
  intro; destruct n; auto; unfold interval.
  destruct (le_lt_dec (S n) n); auto; omega.
Qed.

Lemma interval_alt : forall m n, interval n m = 
  if lt_dec n m then n :: interval (S n) m else [].
Proof.
  induction m; auto; intro.
  unfold interval at 1; fold interval.
  destruct (le_lt_dec n m); destruct (lt_dec n (S m)); auto; try omega.
  rewrite IHm.
  destruct (lt_dec n m).
  - unfold interval at 2; fold interval.
    destruct (le_lt_dec (S n) m); auto; omega.
  - rewrite Lt.le_lt_or_eq_iff in *; destruct l; [contradiction | subst].
    rewrite interval_nil; auto.
Qed.

Lemma interval_length : forall m n, length (interval n m) = minus m n.
Proof.
  induction m; auto; intro; simpl.
  destruct (le_lt_dec n m).
  - rewrite app_length, IHm; simpl.
    destruct n; omega.
  - destruct n; simpl; omega.
Qed.        

Lemma interval_in_iff : forall i j k, In k (interval i j) <-> i <= k < j.
Proof.
  intros; induction j; clarify; [omega|].
  destruct (le_lt_dec i j); clarify; [|omega].
  rewrite in_app, IHj; clarify; omega.
Qed.

Corollary interval_in : forall i j k (Hk : i <= k < j), In k (interval i j).
Proof. intros; rewrite interval_in_iff; auto. Qed.
  
Opaque minus.

Lemma nth_error_interval : forall k i j, nth_error (interval i j) k =
  if lt_dec k (j - i) then Some (i + k) else None.
Proof.
  induction j; [clarsimp | clarify].
  destruct (le_lt_dec i j); destruct (lt_dec k (S j - i)); try omega.
  - rewrite nth_error_app, interval_length, IHj; clarify.
    assert (k = j - i) as Heq by omega; rewrite Heq, minus_diag;
      rewrite <- le_plus_minus; auto.
  - rewrite nth_error_app, interval_length; destruct (lt_dec k (j - i));
      [omega|].
    destruct (k - (j - i)) eqn: Hminus; [omega | clarsimp].
  - clarsimp.
Qed.
  
Lemma interval_plus : forall k i j, i <= j -> interval i (j + k) =
  interval i j ++ interval j (j + k).
Proof.
  induction k; clarify.
  - rewrite plus_0_r; rewrite interval_nil; clarsimp.
  - rewrite <- plus_n_Sm; simpl.
    destruct (le_lt_dec j (j + k)); [|omega].
    destruct (le_lt_dec i (j + k)); [|omega].
    rewrite IHk; clarsimp.
Qed.

Lemma interval_shift : forall j i k, k <= i -> interval i j =
  map (fun x => x + k) (interval (i - k) (j - k)).
Proof.
  induction j; clarify.
  destruct (le_lt_dec i j).
  - erewrite IHj; eauto.
    rewrite <- minus_Sn_m; simpl; [|omega].
    destruct (le_lt_dec (i - k) (j - k)); [|omega].
    rewrite map_app; clarify.
    rewrite NPeano.Nat.sub_add; auto; omega.
  - destruct (le_lt_dec k j).
    + rewrite <- minus_Sn_m; clarify; omega.
    + assert (S j - k = 0) by omega; clarsimp.
Qed.

Lemma NoDup_inj : forall A (l : list A) i j x (Hdistinct : NoDup l)
  (Hi : nth_error l i = Some x) (Hj : nth_error l j = Some x), i = j.
Proof.
  induction l; clarsimp.
  inversion Hdistinct; clarify.
  destruct i; clarify.
  - destruct j; clarify; exploit nth_error_in; eauto; clarify.
  - destruct j; clarify; [exploit nth_error_in; eauto; clarify|].
    exploit IHl; eauto.
Qed.

Corollary NoDup_inj_iff : forall A (l : list A), NoDup l <->
  forall i j x (Hi : nth_error l i = Some x) (Hj : nth_error l j = Some x),
  i = j.
Proof.
  intros; split; intros; [eapply NoDup_inj; eauto|].
  induction l; clarify; constructor; auto.
  - intro; exploit in_nth_error; eauto; clarify.
    specialize (H 0 (S x) a); clarify.
  - apply IHl; clarify.
    specialize (H (S i) (S j) x); clarify.
Qed.

Hint Resolve NoDup_nil.

Lemma NoDup_app : forall A (l1 l2 : list A), NoDup (l1 ++ l2) <->
  NoDup l1 /\ NoDup l2 /\ forall x, In x l1 -> ~In x l2.
Proof.
  induction l1; split; clarify.
  - inversion H; clarify.
    rewrite IHl1 in *; split; rewrite in_app in *; clarify.
    constructor; auto.
  - inversion H1; clarify.
    constructor.
    + rewrite in_app; intro; clarify.
      exploit H22; eauto.
    + rewrite IHl1; clarify.
Qed.

Lemma NoDup_filter : forall A f (l : list A) (Hnodup : NoDup l),
  NoDup (filter f l).
Proof.
  induction l; clarify.
  inversion Hnodup; clarify.
  constructor; auto.
  rewrite filter_In; intro; clarify.
Qed.

Lemma nth_error_split' : forall A l n (a : A), nth_error l n = Some a ->
  exists l1 l2, length l1 = n /\ l = l1 ++ a :: l2.
Proof.
  induction l; intros; destruct n; clarify.
  - exists []; clarify; eauto.
  - exploit IHl; eauto; clarify.
    exists (a :: x); clarify; eauto.
Qed.

Lemma nth_error_succeeds : forall A (l : list A) n, lt n (length l) ->
  exists a, nth_error l n = Some a.
Proof.
  induction l; simpl; intros.
  - inversion H.
  - destruct n; simpl; eauto.
    apply IHl; omega.
Qed.

Lemma NoDup_snoc : forall A l (a : A) (Hdistinct : NoDup l)
  (Hin : ~In a l), NoDup (l ++ [a]).
Proof.
  induction l; clarify.
  - constructor; auto.
  - inversion Hdistinct; clarify.
    exploit IHl; eauto; constructor; auto.
    rewrite in_app; intro; clarify.
Qed.      

Lemma interval_distinct : forall m n, NoDup (interval n m).
Proof.
  induction m; clarify; auto.
  apply NoDup_snoc; auto.
  generalize (interval_lt m n); intro Hlt.
  intro Hin; rewrite Forall_forall in Hlt; specialize (Hlt _ Hin); omega.
Qed.

Fixpoint replace {A:Type} (l:list A) (n:nat) (a:A) : list A :=
  match n, l with
    | O, _::l' => a::l'
    | S n', a'::l' => a'::replace l' n' a
    | _, [] => []
  end.

Lemma replace_spec : forall A l l' n (a a' : A), length l = n ->
  replace (l ++ a :: l') n a' = l ++ a' :: l'.
Proof.
  induction l; clarify; rewrite IHl; auto.
Qed.  

Lemma replace_length : forall A l n (a : A),
  length (replace l n a) = length l.
Proof.
  induction l; simpl; intros.
  - destruct n; auto.
  - destruct n; simpl; auto.
Qed.

Lemma replace_same : forall A l n (a : A) a',
  replace (replace l n a) n a' = replace l n a'.
Proof.
  induction l; clarify; destruct n; clarify.
  rewrite IHl; auto.
Qed.

Lemma replace_replace : forall A l n (a : A) n' a' (Hdiff : n <> n'),
  replace (replace l n a) n' a' = replace (replace l n' a') n a.
Proof.
  induction l; clarify; destruct n, n'; clarify.
  rewrite IHl; auto.
Qed.

Lemma nth_error_replace : forall A l n (a : A) n' (Hn : lt n (length l)),
  nth_error (replace l n a) n' = if eq_dec n n' then Some a
                                 else nth_error l n'.
Proof.
  induction l; intros; try (solve [inversion Hn]); simpl in *.
  destruct n, n'; clarify.
  rewrite IHl; [|omega]; destruct (eq_dec n n'); clarify.
  inversion e; clarify.
Qed.

Lemma nth_error_replace_2 : forall A l n (a : A) n' (Hneq : n' <> n),
  nth_error (replace l n a) n' = nth_error l n'.
Proof.
  induction l; clarify.
  destruct n, n'; clarify.
Qed.

Lemma replace_idem : forall A l n (a : A) (Hnth : nth_error l n = Some a),
  replace l n a = l.
Proof.  
  induction l; destruct n; clarify.
  rewrite IHl; auto.
Qed.

Lemma replace_over : forall A l n (a : A) (Hnlt : ~lt n (length l)),
  replace l n a = l.
Proof.
  induction l; intros; destruct n; clarify; try omega.
  rewrite IHl; auto; omega.
Qed.

Lemma Forall_replace : forall A n l (x : A) P
  (Hl : Forall P l) (Hx : P x), Forall P (replace l n x).
Proof.
  induction n; clarify; destruct l; clarify.
  - inversion Hl; clarify.
  - inversion Hl; clarify.
Qed.

Lemma find_drop : forall A l (x : A) l' P, P x = false ->
  find P (l ++ x :: l') = find P (l ++ l').
Proof. induction l; clarify. Qed.

Lemma Forall2_impl : forall {A B} (P Q : A -> B -> Prop) l1 l2
  (Himpl : forall a b, P a b -> Q a b), Forall2 P l1 l2 -> Forall2 Q l1 l2.
Proof. intros; induction H; auto. Qed.

Lemma Forall2_impl' : forall {A B} (P Q : A -> B -> Prop) l1 l2
  (Himpl : forall a b, In a l1 -> P a b -> Q a b), 
  Forall2 P l1 l2 -> Forall2 Q l1 l2.
Proof. 
  intros; induction H; auto.
  constructor.
  - apply Himpl; simpl; auto.
  - apply IHForall2. intros; apply Himpl; simpl; auto.
Qed.

Lemma Forall2_length : forall {A B} (P : A -> B -> Prop) l1 l2,
  Forall2 P l1 l2 -> length l1 = length l2.
Proof. intros; induction H; simpl; auto. Qed.

Lemma replicate_length : forall A n (a : A), length (replicate a n) = n.
Proof. induction n; simpl; auto. Qed.

Lemma in_replicate : forall A n (a x : A), In x (replicate a n) -> x = a.
Proof. induction n; clarify. Qed.

Lemma nth_error_replicate : forall A n (a : A) n',
  nth_error (replicate a n) n' = if lt_dec n' n then Some a else None.
Proof.
  induction n; clarify; destruct n'; clarify.
  rewrite lt_dec_mono; clarify.
Qed.

Lemma flatten_in : forall A (x : A) ll,
  In x (flatten ll) <-> exists l, In x l /\ In l ll.
Proof.
  induction ll; [split|]; clarify.
  rewrite in_app, IHll; split; clarify; eauto.
  destruct H; clarify; eauto.
Qed.

Lemma flatten_app : forall A (l1 l2 : list (list A)),
  flatten (l1 ++ l2) = flatten l1 ++ flatten l2.
Proof.
  induction l1; clarify.
  rewrite IHl1; clarsimp.
Qed.

Lemma remdups_in : forall A {A_eq : EqDec_eq A} (x : A) (l : list A),
  In x (remdups l) <-> In x l.
Proof.
  induction l; clarify; [reflexivity|].
  destruct (in_dec A_eq a l); clarify; rewrite IHl; split; clarify.
Qed.

Lemma remdups_NoDup : forall A {A_eq : EqDec_eq A} (l : list A),
  NoDup (remdups l).
Proof.
  induction l; clarify; constructor; auto.
  rewrite remdups_in; auto.
Qed.

Lemma NoDup_remdups : forall A (A_eq : EqDec_eq A) (l : list A)
  (HNoDup : NoDup l), remdups l = l.
Proof.
  induction l; clarify.
  inversion HNoDup; clarsimp.
Qed.

Lemma remdups_NoDup_app : forall A (A_eq : EqDec_eq A) (l1 l2 : list A)
  (HNoDup : NoDup l2), exists l1', remdups (l1 ++ l2) = l1' ++ l2 /\
  forall x, In x l1 -> ~In x l2 -> In x l1'.
Proof.
  induction l1; clarify.
  - exists []; rewrite NoDup_remdups; auto.
  - specialize (IHl1 _ HNoDup); destruct IHl1 as [l1' [IHl1 ?]].
    destruct (in_dec _ a (l1 ++ l2)); clarify.
    + do 2 eexists; eauto; clarify.
      rewrite in_app in *; clarify.
    + exists (a :: l1'); clarsimp.
Qed.

Lemma Forall_remdups : forall A (A_eq : EqDec_eq A) P (l : list A),
  Forall P (remdups l) <-> Forall P l.
Proof.
  intros; repeat rewrite Forall_forall.
  setoid_rewrite remdups_in; reflexivity.
Qed.

Lemma filter_length : forall A (f : A -> bool) l,
  length (filter f l) <= length l.
Proof. induction l; clarify; omega. Qed.

Lemma filter_filter_1 : forall A (f g : A -> bool) l
  (Himpl : Forall (fun x => implb (f x) (g x) = true) l),
  filter f (filter g l) = filter f l.
Proof.
  induction l; clarify.
  rewrite Forall_forall in *; clarify.
  specialize (Himpl a); clarify.
  destruct (f a) eqn: Hf; clarify.
  rewrite IHl; auto.
Qed.

Lemma filter_filter_2 : forall A (f g : A -> bool) l
  (Himpl : Forall (fun x => implb (f x) (g x) = true) l),
  filter g (filter f l) = filter f l.
Proof.
  induction l; clarify.
  rewrite Forall_forall in *; clarify.
  specialize (Himpl a); clarify.
  destruct (f a) eqn: Hf; clarify.
  rewrite IHl; auto.
Qed.

Lemma filter_ext : forall A f g (l : list A)
  (Hext : Forall (fun x => f x = g x) l), filter f l = filter g l.
Proof.
  induction l; clarify.
  inversion Hext; clarsimp.
Qed.

Lemma filter_filter: forall A f g (l : list A),
  filter f (filter g l) = filter (fun x => f x && g x) l.
Proof.
  induction l; clarify.
  destruct (g a); clarsimp; rewrite IHl; auto.
Qed.

Corollary filter_comm : forall A f g (l : list A),
  filter f (filter g l) = filter g (filter f l).
Proof.
  intros; repeat rewrite filter_filter; apply filter_ext.
  rewrite Forall_forall; intros; rewrite andb_comm; auto.
Qed.

Lemma filter_idem : forall A f (l : list A), filter f (filter f l) =
  filter f l.
Proof.
  intros; rewrite filter_filter_1; auto.
  rewrite Forall_forall; unfold implb; clarify.
Qed.

Lemma filter_all : forall A (f : A -> bool) l
  (Hall : Forall (fun x => f x = true) l), filter f l = l.
Proof.
  induction l; clarify.
  inversion Hall; clarsimp.
Qed.

Lemma filter_none_iff : forall A (f : A -> bool) l,
  filter f l = [] <-> Forall (fun x => f x = false) l.
Proof.
  induction l; split; clarify.
  - constructor; [|rewrite <- IHl]; auto.
  - inversion H; clarify.
    rewrite IHl; auto.
Qed.

Corollary filter_none : forall A (f : A -> bool) l
  (Hnone : Forall (fun x => f x = false) l), filter f l = [].
Proof. intros; rewrite filter_none_iff; auto. Qed.

Lemma Forall_filter : forall {A} l (f : A -> bool) P,
  Forall P l -> Forall P (filter f l).
Proof.
  induction l; clarify.
  inversion H; clarify.
Qed.

Lemma filter_Forall : forall {A} l (f : A -> bool) (P : A -> Prop)
  (Himpl : forall x, f x = true -> P x), Forall P (filter f l).
Proof.
  induction l; clarify.
Qed.

Lemma Forall_filter_impl : forall A P f (l : list A)
  (Hall : Forall P (filter f l)) (Himpl : forall x, f x = false -> P x),
  Forall P l.
Proof.
  induction l; clarify.
  inversion Hall; clarify.
Qed.

Lemma filter_app : forall A (f : A -> bool) l1 l2,
  filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
  induction l1; clarify.
  rewrite IHl1; auto.
Qed.

Lemma nth_filter_split : forall A (f : A -> bool) l i x,
  nth_error (filter f l) i = Some x ->
  exists l1 l2, l = l1 ++ x :: l2 /\ i = length (filter f l1) /\
                filter f l = filter f l1 ++ x :: filter f l2.
Proof.
  induction l; clarsimp.
  destruct (f a) eqn: Hf; clarify.
  - destruct i; clarify.
    + exists []; clarify; eauto.
    + exploit IHl; eauto; intros [l1 [l2 ?]].
      exists (a :: l1), l2; clarify.
      rewrite filter_app; clarify.
      exploit nth_error_in; eauto; rewrite filter_In; clarify.
  - exploit IHl; eauto; intros [l1 [l2 ?]].
    exists (a :: l1), l2; clarify.
Qed.

Lemma find_filter : forall A (f g : A -> bool) l
  (Himpl : forall x, implb (f x) (g x) = true),
  find f (filter g l) = find f l.
Proof.
  induction l; clarify.
  specialize (Himpl a); destruct (f a) eqn: Ha; clarify.
Qed.    

Lemma remdups_filter : forall A {A_eq : EqDec_eq A} f (l : list A),
  remdups (filter f l) = filter f (remdups l).
Proof.
  induction l; clarify.
  destruct (f a) eqn: Ha; clarify.
  destruct (in_dec A_eq a l); clarify.
  - contradiction n; rewrite filter_In; auto.
  - destruct (in_dec A_eq a (filter f l)); clarsimp.
    rewrite filter_In in *; clarify.
Qed.

Corollary remdups_drop_hd : forall A {A_eq : EqDec_eq A} (l : list A) h t
  (Hhd : remdups l = h :: t),
  remdups (filter (fun x => negb (beq x h)) l) = t.
Proof.
  intros; rewrite remdups_filter.
  generalize (remdups_NoDup l); intro Hunique; clarsimp.
  inversion Hunique; unfold beq; clarify.
  apply filter_all; rewrite Forall_forall; clarify.
Qed.

Lemma map_filter : forall {A B} (f : A -> B) p l
  p' (Hp : Forall (fun x => p' (f x) = p x) l),
  map f (filter p l) = filter p' (map f l).
Proof.
  induction l; clarify.
  inversion Hp; clarify.
  destruct (p a); clarify.
  erewrite IHl; eauto.
Qed.

Lemma filter_hd : forall A (f : A -> bool) l h t (Hhd : filter f l = h :: t),
  f h = true /\ exists l1 l2, l = l1 ++ h :: l2 /\ 
    Forall (fun x => f x = false) l1 /\ filter f l2 = t.
Proof.
  induction l; clarify.
  destruct (f a) eqn: Ha; clarify.
  - repeat eexists; eauto; clarify.
  - specialize (IHl _ _ Hhd); clarify.
    exists (a :: x); repeat eexists; constructor; auto.
Qed.

Fixpoint find_index A (f : A -> bool) l :=
  match l with
  | [] => None
  | x :: rest => if f x then Some 0
      else match find_index f rest with Some n => Some (S n) | None => None end
  end.

Lemma find_index_spec : forall A (f : A -> bool) l i,
  find_index f l = Some i <->
  exists x, nth_error l i = Some x /\ f x = true /\ forall j x', j < i ->
    nth_error l j = Some x' -> f x' = false.
Proof.
  induction l; clarify.
  { split; clarsimp. }
  destruct (f a) eqn: Ha.
  - split; clarify.
    + exists a; clarify; omega.
    + destruct i; clarify.
      specialize (H22 0 a); clarify.
  - destruct (find_index f l) eqn: Hfind.
    + destruct i; clarify; [split; clarify|].
      specialize (IHl i).
      transitivity (Some n = Some i); [split; clarify|].
      rewrite IHl; split; clarify; exists x; clarify; [|eauto].
      destruct j; clarify.
      eapply H22; eauto; omega.
    + split; clarify.
      destruct i; clarify.
      specialize (IHl i); destruct IHl as [_ IHl]; use IHl; clarify.
      exists x; clarify.
      specialize (H22 (S j) x'); clarify.
Qed.      

Lemma find_find_index : forall A f (l : list A) x, find f l = Some x <->
  exists i, find_index f l = Some i /\ nth_error l i = Some x.
Proof.
  setoid_rewrite find_spec; setoid_rewrite find_index_spec; split; clarsimp;
    eexists; eauto.
Qed.

Lemma find_index_fail : forall A (f : A -> bool) l,
  find_index f l = None <-> Forall (fun x => f x = false) l.
Proof.
  induction l; clarify.
  { split; clarify. }
  destruct (f a) eqn: Ha; clarsimp.
  - split; clarify.
    inversion H; clarify.
  - rewrite IHl; split; clarify.
    inversion H; auto.
Qed.

Lemma find_index_filter : forall A (f : A -> bool) l i
  (Hfind : find_index f l = Some i),
  exists x, nth_error l i = Some x /\ 
            filter f l = x :: filter f (skipn (S i) l).
Proof. induction l; clarify; eauto. Qed.

Lemma find_index_filter_none : forall A (f : A -> bool) l
  (Hfail : find_index f l = None), filter f l = [].
Proof.
  intros; rewrite find_index_fail in Hfail; apply filter_none; auto.
Qed.

Lemma find_index_app : forall A (f : A -> bool) l1 l2,
  find_index f (l1 ++ l2) =
  match find_index f l1 with
  | Some i => Some i
  | None =>
      match find_index f l2 with
      | Some i => Some (length l1 + i)
      | None => None
      end
  end.
Proof.
  induction l1; clarsimp.
  rewrite IHl1.
  destruct (find_index f l1); clarify.
  destruct (find_index f l2); clarify.
Qed.

Fixpoint find_match A (f : A -> bool) l l' i :=
  match i with
  | O => match find_index f l' with Some n => n | _ => 0 end
  | S i' =>
      match l with
      | [] => 0
      | x :: rest => if f x then
          match find_index f l' with
          | Some n => find_match f rest (skipn (S n) l') i' + S n
          | None => 0
          end else find_match f rest l' i'
      end
  end.

Lemma find_match_valid : forall A (f : A -> bool) l l' i a
  (Hnth : nth_error l i = Some a) (Ha : f a = true)
  (Hfilter : filter f l' = filter f l),
  nth_error l' (find_match f l l' i) = Some a.
Proof.
  induction l; clarify.
  destruct i; clarify.
  - destruct (find_index f l') eqn: Hfind.
    + exploit find_index_filter; eauto; clarsimp.
    + rewrite find_index_filter_none in Hfilter; clarify.
  - destruct (find_index f l') eqn: Hfind.
    + exploit find_index_filter; eauto; intros [x [Hx Hfil]].
      rewrite Hfil in Hfilter; clarify.
      specialize (IHl _ _ _ Hnth Ha H1).
      generalize (skipn_nth (S n) l'); intro Hskip; rewrite Hskip in IHl;
        clarify.
    + rewrite find_index_filter_none in Hfilter; clarify.
Qed.      

Lemma find_match_index : forall A (f : A -> bool) l l' i i'
  (Hfind : find_index f l = Some i) (Hfind' : find_index f l' = Some i'),
  find_match f l l' i = i'.
Proof. induction l; clarify. Qed.

Lemma find_match_index_lt : forall A (f : A -> bool) l l' i i' n
  (Hfind : find_index f l = Some i) (Hfind' : find_index f l' = Some i')
  (Hlt : n <= i), find_match f l l' n = i'.
Proof.
  induction l; clarify.
  destruct n; clarify.
  destruct (f a) eqn: Ha; clarify; [omega|].
  eapply IHl; eauto; omega.
Qed.

Hint Rewrite NPeano.Nat.sub_succ : util.

Lemma find_match_index' : forall A (f : A -> bool) l l' i i' n
  (Hfind : find_index f l = Some i) (Hfind' : find_index f l' = Some i')
  (Hlt : i < n),
  find_match f l l' n = find_match f (skipn (S i) l) (skipn (S i') l') (n - S i)
    + S i'.
Proof.
  induction l; clarify.
  destruct n; [omega | clarify].
  destruct (f a) eqn: Ha; clarsimp.
  apply IHl; auto; omega.
Qed.

Lemma find_match_index_none : forall A (f : A -> bool) l l' i
  (Hfail : find_index f l' = None), find_match f l l' i = 0.
Proof.
  induction l; clarsimp.
  destruct i; clarify.
Qed.  

Lemma find_match_inv : forall A (f : A -> bool) i l l' a
  (Hnth : nth_error l i = Some a) (Ha : f a = true)
  (Hfilter : filter f l' = filter f l),
  find_match f l' l (find_match f l l' i) = i.
Proof.
  induction i using lt_wf_ind; intros.
  destruct (find_index f l) eqn: Hfind.
  destruct (find_index f l') eqn: Hfind'.
  destruct (le_lt_dec i n).
  - generalize (find_match_index_lt _ _ _ Hfind Hfind' l0); intro H1;
      rewrite H1.
    apply find_match_index; auto.
    destruct (eq_dec i n); clarify.
    rewrite find_index_spec in Hfind; clarify.
    specialize (Hfind22 i a); use Hfind22; [clarify | omega].
  - generalize (find_match_index' _ _ _ Hfind Hfind' l0); intro H1; rewrite H1.
    erewrite find_match_index'; eauto; [|omega].
    rewrite NPeano.Nat.add_sub.
    erewrite H; eauto; try omega.
    + rewrite skipn_nth.
      rewrite <- plus_minus_comm; clarsimp.
    + generalize (find_index_filter _ _ Hfind), (find_index_filter _ _ Hfind'); 
        clarsimp.
  - rewrite find_index_filter_none in Hfilter; clarify.
    exploit find_index_filter; eauto; intros [? [? Hfil]].
    rewrite Hfil in Hfilter; clarify.
  - rewrite find_index_fail in Hfind.
    rewrite Forall_forall in Hfind; exploit nth_error_in; eauto; intro Hin;
      specialize (Hfind _ Hin); clarify.
Qed.

Lemma find_match_mono : forall A (f : A -> bool) i j l l' a b
  (Hi : nth_error l i = Some a) (Ha : f a = true)
  (Hi : nth_error l j = Some b) (Ha : f b = true)
  (Hfilter : filter f l' = filter f l),
  i < j <-> find_match f l l' i < find_match f l l' j.
Proof.
  induction i using lt_wf_ind; intros.
  destruct (find_index f l) eqn: Hfind.
  destruct (find_index f l') eqn: Hfind'.
  destruct (le_lt_dec i n).
  - generalize (find_match_index_lt _ _ _ Hfind Hfind' l0); intro H1;
      rewrite H1.
    generalize (find_index_spec f l n); intros [Hlt _]; clarify.
    destruct (lt_dec i n); [exploit Hlt22; eauto; clarify|].
    destruct (eq_dec i j); [subst; omega|].
    destruct (le_lt_dec j n).
    { specialize (Hlt22 j b); use Hlt22; [clarify | omega]. }
    split; try omega.
    generalize (find_match_index' _ _ _ Hfind Hfind' l1); intro H2;
      rewrite H2; omega.
  - erewrite find_match_index'; eauto.
    destruct (le_lt_dec j n).
    { generalize (find_match_index_lt _ _ _ Hfind Hfind' l1); intro H1;
        rewrite H1; omega. }
    generalize (find_match_index' _ _ _ Hfind Hfind' l1); intro H2;
      rewrite H2.
    transitivity (i - S n < j - S n); [omega|].
    rewrite <- NPeano.Nat.add_lt_mono_r; eapply H; try (rewrite skipn_nth;
      rewrite <- plus_minus_comm, NPeano.Nat.add_sub); eauto; try omega.
    generalize (find_index_filter _ _ Hfind),
      (find_index_filter _ _ Hfind'); clarsimp.
  - rewrite find_index_filter_none in Hfilter; auto.
    exploit find_index_filter; eauto; intros [? [? Hfil]].
    rewrite Hfil in Hfilter; clarify.
  - rewrite find_index_fail in Hfind.
    rewrite Forall_forall in Hfind; exploit nth_error_in; eauto; intro Hin;
      specialize (Hfind _ Hin); clarify.
Qed.

Lemma firstn_length : forall A (l : list A), firstn (length l) l = l.
Proof. induction l; clarsimp. Qed.
Hint Rewrite firstn_length : list.

Lemma firstn_comm : forall A n m (l : list A), firstn n (firstn m l) =
  firstn m (firstn n l).
Proof.
  intros; repeat rewrite firstn_firstn; rewrite Min.min_comm; auto.
Qed.

Lemma removelast_app : forall A (l1 l2 : list A), removelast (l1 ++ l2) =
  firstn (length l1 + length l2 - 1) l1 ++ removelast l2.
Proof.
  induction l1; clarsimp.
  destruct (l1 ++ l2) eqn: Hl.
  - destruct l1; clarify.
  - rewrite <- Hl, IHl1.
    rewrite <- app_length, Hl; clarsimp.
Qed.

Lemma last_snoc : forall A (l : list A) x d,
  last (l ++ [x]) d = x.
Proof.
  induction l; clarify.
  destruct (l ++ [x]) eqn: Hl.
  - destruct l; clarify.
  - rewrite <- Hl; auto.
Qed.

Lemma removelast_snoc : forall A (l : list A) x,
  removelast (l ++ [x]) = l.
Proof.
  intros; rewrite removelast_app; clarsimp.
Qed.
        
Lemma Permutation_NoDup : forall A (l l' : list A) (Hdistinct : NoDup l)
  (Hperm : Permutation l l'), NoDup l'.
Proof.
  intros; induction Hperm; auto.
  - inversion Hdistinct; constructor; clarify.
    intro; contradiction H1; eapply Permutation_in; [|eauto].
    symmetry; auto.
  - inversion Hdistinct; clarify.
    inversion H2; clarify.
    constructor; [intro | constructor]; clarify.
Qed.

Lemma Permutation_in_iff : forall A (l l' : list A) x
  (Hperm : Permutation l l'), In x l <-> In x l'.
Proof. split; intro; [|symmetry in Hperm]; eapply Permutation_in; eauto. Qed.

Lemma interval_perm_nth : forall i j l (Hperm : Permutation (interval i j) l)
  k, In k l <-> i <= k < j.
Proof.
  intros.
  erewrite <- Permutation_in_iff, interval_in_iff; [reflexivity | eauto].
Qed.
  
Corollary interval_perm_in : forall i j l
  (Hperm : Permutation (interval i j) l) k (Hk : i <= k < j), In k l.
Proof. intros; rewrite interval_perm_nth; eauto. Qed.

(* Ensembles *)
Arguments Union [_] _ _ _.
Arguments Setminus [_] _ _ _.
Arguments Add [_] _ _ _.
Arguments Subtract [_] _ _ _.
Arguments Singleton [_] _ _.
Arguments Empty_set {_} _.

Lemma set_ext : forall A (S1 S2 : Ensemble A)
  (Hext : forall e, S1 e <-> S2 e), S1 = S2.
Proof.
  intros; apply Extensionality_Ensembles; split; repeat intro;
    rewrite Hext in *; auto.
Qed.

Lemma Union_spec : forall A S1 S2 (x : A), Union S1 S2 x <-> S1 x \/ S2 x.
Proof.
  split; intro.
  - inversion H; auto.
  - destruct H; [apply Union_introl | apply Union_intror]; auto.
Qed.

Lemma Singleton_spec : forall A (x y : A), Singleton x y <-> y = x.
Proof.
  split; intro Hin.
  - inversion Hin; auto.
  - subst; constructor.
Qed.

Lemma Add_spec : forall A S (x y : A), Add S x y <-> S y \/ y = x.
Proof.
  setoid_rewrite Union_spec; setoid_rewrite Singleton_spec; reflexivity.
Qed.

Lemma Union_Empty : forall A (S : Ensemble A), Union S Empty_set = S.
Proof.
  intros; apply set_ext; intro; rewrite Union_spec; split; clarify.
Qed.

Lemma Setminus_spec : forall A S1 S2 (x : A),
  Setminus S1 S2 x <-> S1 x /\ ~S2 x.
Proof.
  split; intro.
  - inversion H; auto.
  - constructor; clarify.
Qed.

Lemma Empty_Minus : forall A (S : Ensemble A), Setminus Empty_set S = Empty_set.
Proof.
  intros; apply set_ext; intro; rewrite Setminus_spec; split; clarify.
Qed.

Definition set_of A (l : list A) x := In x l.

Lemma set_of_nil : forall A, set_of [] = (@Empty_set A).
Proof.
  intro; apply set_ext; split; clarify.
Qed.

Lemma Minus_Empty : forall A (S : Ensemble A), Setminus S Empty_set = S.
Proof.
  intros; apply set_ext; intro; rewrite Setminus_spec; split; clarify.
  intro Hin; inversion Hin.
Qed.

Arguments Included [_] _ _.

Lemma set_of_single : forall A (x : A), set_of [x] = Singleton x.
Proof.
  intros; apply set_ext; intro; rewrite Singleton_spec; split; clarify.
Qed.

Lemma set_of_cons : forall A (x : A) l, set_of (x :: l) = Add (set_of l) x.
Proof.
  intros; apply set_ext; intro; rewrite Add_spec; split; clarify.
Qed.

Lemma set_of_app : forall A (l1 l2 : list A), set_of (l1 ++ l2) =
  Union (set_of l1) (set_of l2).
Proof.
  intros; apply set_ext; intro; rewrite Union_spec; setoid_rewrite in_app;
    reflexivity.
Qed.

Lemma Subtract_spec : forall A S (x y : A),
  Subtract S x y <-> S y /\ y <> x.
Proof.
  intros; unfold Subtract; rewrite Setminus_spec, Singleton_spec; reflexivity.
Qed.

Lemma Subtract_Add : forall A S (x : A) (Hout : ~S x),
  Subtract (Add S x) x = S.
Proof.
  intros; apply set_ext; intro; rewrite Subtract_spec, Add_spec; split; clarify.
  intro; clarify.
Qed.

Lemma Add_Subtract_comm : forall A S (x y : A) (Hneq : x <> y),
  Add (Subtract S x) y = Subtract (Add S y) x.
Proof.
  intros; apply set_ext; split; intros;
    rewrite Add_spec, Subtract_spec, Add_spec in *; clarify.
Qed.

Lemma Subtract_comm : forall A S (x y : A), Subtract (Subtract S x) y =
  Subtract (Subtract S y) x.
Proof.
  intros; apply set_ext; intro; repeat rewrite Subtract_spec in *; split;
    clarify.
Qed.

Lemma Union_assoc : forall A (S1 S2 S3 : Ensemble A), Union (Union S1 S2) S3 =
  Union S1 (Union S2 S3).
Proof.
  intros; apply set_ext; intro; repeat rewrite Union_spec; split; clarify.
Qed.

Lemma Union_comm : forall A (S1 S2 : Ensemble A), Union S1 S2 = Union S2 S1.
Proof.
  intros; apply set_ext; intro; repeat rewrite Union_spec; split; clarify.
Qed.

Lemma Empty_Union : forall A (S : Ensemble A), Union Empty_set S = S.
Proof.
  intros; apply set_ext; intro; rewrite Union_spec; split; clarify.
Qed.

Lemma Union_Add : forall A (x : A) S1 S2, Union (Add S1 x) S2 =
  Union S1 (Add S2 x).
Proof.
  intros; apply set_ext; intro; repeat rewrite Union_spec, Add_spec;
    split; clarify.
Qed.

Lemma Incl_Union : forall A (S1 S2 : Ensemble A),
  Included S1 (Union S1 S2).
Proof.
  repeat intro; setoid_rewrite Union_spec; auto.
Qed.

Lemma Incl_Single : forall A (e : A) S,
  Included (Singleton e) S <-> S e.
Proof.
  split; intro.
  - apply H; constructor.
  - intros ? Hin; inversion Hin; clarify.
Qed.

Lemma Included_Minus : forall A (S1 S2 : Ensemble A)
  (Hdec : forall x, S1 x \/ ~S1 x),
   Included S1 S2 -> S2 = Union S1 (Setminus S2 S1).
Proof.
  intros; apply set_ext; intro; rewrite Union_spec, Setminus_spec;
  split; clarify.
  - specialize (Hdec e); clarify.
  - specialize (Hdec e); clarify.
    apply H; auto.
Qed.

Lemma Union_Single : forall A (e : A) S, Union (Singleton e) S = Add S e.
Proof.
  intros; apply set_ext; intro; rewrite Union_spec, Add_spec, Singleton_spec;
  split; clarify.
Qed.

Lemma skipn_map : forall A B n (f : A -> B) l,
  skipn n (map f l) = map f (skipn n l).
Proof.
  induction n; clarify.
  destruct l; clarify.
Qed.

(* Potentially infinite lists - better than streams? *)
Section IList.

  Variable A : Type.

  CoInductive ilist :=
  | inil : ilist
  | icons : A -> ilist -> ilist.

  Fixpoint iapp l s :=
    match l with
    | [] => s
    | x :: rest => icons x (iapp rest s)
    end.

  Fixpoint inth l n :=
    match l with
    | inil => None
    | icons x rest =>
        match n with
        | O => Some x
        | S n' => inth rest n'
        end
    end.

  Lemma inth_lt : forall n m l a (Hn : inth l n = Some a) (Hlt : m < n),
    exists b, inth l m = Some b.
  Proof.
    induction n; clarify; [omega|].
    destruct l; clarify.
    destruct m; clarify; eauto.
    eapply IHn; eauto; omega.
  Qed.

  Lemma iapp_nth : forall l s n, inth (iapp l s) n =
    if lt_dec n (length l) then nth_error l n else inth s (n - length l).
  Proof.
    induction l; clarify.
    - rewrite <- minus_n_O; auto.
    - destruct n; clarify.
      rewrite IHl, lt_dec_mono; auto.
  Qed.

  Lemma iapp_inter : forall l1 l2 l3 i
    (Hi : length l1 <= i < length l1 + length l2),
    inth (iapp l1 (iapp l2 l3)) i = nth_error l2 (i - length l1).
  Proof.
    intros; rewrite iapp_nth.
    destruct (lt_dec i (length l1)); [omega|].
    rewrite iapp_nth.
    destruct (lt_dec (i - length l1) (length l2)); [auto | omega].
  Qed.    
    
  Lemma inth_split : forall n l x (Hnth : inth l n = Some x),
    exists l1 l2, length l1 = n /\ l = iapp l1 (icons x l2).
  Proof.
    induction n; destruct l; clarify.
    - exists []; clarify; eauto.
    - specialize (IHn _ _ Hnth); clarify.
      exists (a :: x0); clarify; eauto.
  Qed.

  Lemma iapp_split_nth : forall l1 l2 x n x',
    inth (iapp l1 (icons x l2)) n = if eq_dec n (length l1) then Some x
    else inth (iapp l1 (icons x' l2)) n.
  Proof.
    intros; repeat rewrite iapp_nth; destruct (lt_dec n (length l1)); clarify;
      try omega.
    destruct (eq_dec n (length l1)); clarify.
    - rewrite minus_diag; auto.
    - destruct (n - length l1) eqn: Hminus; clarify; omega.
  Qed.

  Lemma inth_nil : forall n, inth inil n = None.
  Proof. destruct n; auto. Qed.

  Lemma iapp_app : forall l l' s, iapp l (iapp l' s) = iapp (l ++ l') s.
  Proof.
    induction l; clarify.
    rewrite IHl; auto.
  Qed.

  Fixpoint itake n s :=
    match s with
    | inil => []
    | icons x rest =>
        match n with
        | O => []
        | S n' => x :: itake n' rest
        end
    end.

  Lemma itake_snoc : forall n s a (Hnth : inth s n = Some a),
    itake (S n) s = itake n s ++ [a].
  Proof.
    induction n; clarify; destruct s; clarify.
    erewrite IHn; eauto.
  Qed.

  Lemma itake_0 : forall l, itake 0 l = [].
  Proof. clarify. Qed.
  Hint Rewrite itake_0 : list.

  Lemma itake_nth : forall n s i, nth_error (itake n s) i =
    if lt_dec i n then inth s i else None.
  Proof.
    induction n; destruct i, s; clarify.
    rewrite IHn, lt_dec_mono; auto.
  Qed.

  Lemma inth_take : forall i l a (Hnth : inth l i = Some a),
    length (itake (S i) l) = S i.
  Proof.
    induction i; intros; destruct l; clarify.
    erewrite IHi; eauto.
  Qed.

  Lemma itake_length : forall n s, length (itake n s) <= n.
  Proof.
    induction n; destruct s; clarify.
    - omega.
    - specialize (IHn s); omega.
  Qed.

  Lemma iapp_take : forall n l s, itake n (iapp l s) =
    firstn n l ++ itake (n - length l) s.
  Proof.
    induction n; destruct l; clarsimp.
    rewrite IHn; auto.
  Qed.

  Lemma itake_nil : forall n, itake n inil = [].
  Proof. destruct n; auto. Qed.

  Lemma firstn_itake : forall n l n', firstn n (itake n' l) =
    itake (min n n') l.
  Proof.
    induction n; destruct n', l; clarify.
    rewrite IHn; auto.
  Qed.

  Fixpoint idrop n s :=
    match s with
    | inil => inil
    | icons x rest =>
        match n with
        | O => icons x rest
        | S n' => idrop n' rest
        end
    end.

  Lemma idrop_nth : forall n l i, inth (idrop n l) i = inth l (n + i).
  Proof.
    induction n; destruct l; clarify.
    destruct i; auto.
  Qed.  

  Lemma iapp_drop : forall n l s, idrop n (iapp l s) =
    if lt_dec n (length l) then iapp (skipn n l) s else idrop (n - length l) s.
  Proof.
    induction n; destruct l; clarify.
    rewrite IHn, lt_dec_mono; auto.
  Qed.

  Lemma itake_drop : forall n l, l = iapp (itake n l) (idrop n l).
  Proof.
    induction n; destruct l; clarify.
    rewrite <- IHn; auto.
  Qed.

  Lemma idrop_nil : forall n, idrop n inil = inil.
  Proof. destruct n; auto. Qed.

  Fixpoint iset_nth n a s :=
    match s with
    | inil => inil
    | icons x rest =>
        match n with
        | O => icons a rest
        | S n' => icons x (iset_nth n' a rest)
        end
    end.

  Lemma iset_nth_nth : forall n a s i (Hne : i <> n),
    inth (iset_nth n a s) i = inth s i.
  Proof. induction n; clarify; destruct s, i; clarify. Qed.

  CoInductive iprefix : ilist -> ilist -> Prop :=
  | prefix_nil : forall l, iprefix inil l
  | prefix_cons : forall a l l' (Hpre : iprefix l l'),
      iprefix (icons a l) (icons a l').

  Fixpoint to_ilist l :=
    match l with
    | [] => inil
    | x :: rest => icons x (to_ilist rest)
    end.

  Lemma to_ilist_app : forall l l', to_ilist (l ++ l') = iapp l (to_ilist l').
  Proof.
    induction l; clarify.
    rewrite IHl; auto.
  Qed.

  Corollary iapp_nil_ilist : forall l, iapp l inil = to_ilist l.
  Proof.
    intros; rewrite (app_nil_end l) at 2; rewrite to_ilist_app; auto.
  Qed.

  Lemma inth_nth_error : forall l n, inth (to_ilist l) n = nth_error l n.
  Proof.
    intros; rewrite <- iapp_nil_ilist, iapp_nth.
    destruct (lt_dec n (length l)); auto; rewrite inth_nil.
    destruct (nth_error l n) eqn: Hnth; auto.
    generalize (nth_error_lt _ _ Hnth); clarify.
  Qed.

  Lemma itake_firstn : forall l n, itake n (to_ilist l) = firstn n l.
  Proof.
    intros; rewrite <- iapp_nil_ilist, iapp_take, itake_nil; clarsimp.
  Qed.

  Lemma idrop_skipn : forall l n, idrop n (to_ilist l) = to_ilist (skipn n l).
  Proof.
    intros; rewrite <- iapp_nil_ilist, iapp_drop, idrop_nil.
    destruct (lt_dec n (length l)).
    - apply iapp_nil_ilist.
    - rewrite skipn_all; [auto | omega].
  Qed.

  Lemma to_ilist_inj : forall l1 l2, to_ilist l1 = to_ilist l2 -> l1 = l2.
  Proof.
    induction l1; destruct l2; clarify.
    inversion H; clarify.
    exploit IHl1; eauto; clarify.
  Qed.

  Lemma to_ilist_app_inv : forall l1 l2 l, to_ilist l = iapp l1 l2 ->
    exists l2', l = l1 ++ l2' /\ l2 = to_ilist l2'.
  Proof.
    induction l1; clarify; eauto.
    destruct l; clarify.
    inversion H; clarify.
    exploit IHl1; eauto; clarify; eauto.
  Qed.

  Lemma iapp_prefix : forall l l', iprefix (to_ilist l) (iapp l l').
  Proof.
    cofix; intros.
    destruct l; simpl.
    - apply prefix_nil.
    - apply prefix_cons; auto.    
  Qed.

  Corollary app_prefix : forall l l', iprefix (to_ilist l) (to_ilist (l ++ l')).
  Proof. intros; rewrite to_ilist_app; apply iapp_prefix. Qed.

  Lemma prefix_mono : forall l l1 l2 (Hprefix : iprefix l1 l2),
    iprefix (iapp l l1) (iapp l l2).
  Proof.
    induction l; clarify.
    constructor; eauto.
  Qed.

  Lemma iprefix_app_inv : forall l1 l2 l (Hprefix : iprefix l (iapp l1 l2)),
    (exists n, l = to_ilist (firstn n l1)) \/
    (exists l2', l = iapp l1 l2' /\ iprefix l2' l2).
  Proof.
    induction l1; clarify; eauto.
    inversion Hprefix; clarify.
    - left; exists 0; auto.
    - specialize (IHl1 _ _ Hpre); destruct IHl1; clarify; eauto.
      left; exists (S x); auto.
  Qed.

  Lemma iprefix_list_inv : forall l l' (Hprefix : iprefix (to_ilist l) l'),
    exists l'', l' = iapp l l''.
  Proof.
    induction l; clarify; eauto.
    inversion Hprefix; clarify.
    exploit IHl; eauto; clarify; eauto.
  Qed.    

  Lemma iprefix_list_inv' : forall l' l (Hprefix : iprefix l (to_ilist l')),
    exists l1, l = to_ilist l1 /\ exists l2, l' = l1 ++ l2.
  Proof.
    induction l'; clarify; inversion Hprefix; clarify.
    - exists nil; clarify; eauto.
    - exists nil; clarify; eauto.
    - specialize (IHl' _ Hpre); clarify.
      exists (a :: x); clarify; eauto.
  Qed.    

  Corollary iprefix_lists_inv : forall l l',
    iprefix (to_ilist l) (to_ilist l') <-> exists l'', l' = l ++ l''.
  Proof.
    intros; split; clarify.
    - exploit iprefix_list_inv'; eauto; clarify.
      exploit to_ilist_inj; eauto; clarify; eauto.
    - apply app_prefix.
  Qed.    

  Global Instance iprefix_refl : Reflexive iprefix.
  Proof.
    unfold Reflexive; cofix; intros.
    destruct x; constructor; eauto.
  Qed.

  Global Instance iprefix_trans : Transitive iprefix.
  Proof.
    unfold Transitive; cofix; intros.
    inversion H0; inversion H; clarify.
    - constructor.
    - inversion H4; clarify.
      constructor; eauto.
  Qed.

  Lemma prefix_filter : forall f (l1 l2 : list A)
    (Hpre : iprefix (to_ilist l1) (to_ilist l2)),
    iprefix (to_ilist (filter f l1)) (to_ilist (filter f l2)).
  Proof.
    induction l1; clarify; inversion Hpre; try constructor; destruct l2;
      clarify.
    inversion H; clarify.
    constructor; auto.
  Qed.

  Inductive iIn x : ilist -> Prop :=
  | in_hd : forall l, iIn x (icons x l)
  | in_tl : forall a l (Hin : iIn x l), iIn x (icons a l).

  Lemma not_in_inil : forall x, ~iIn x inil.
  Proof. repeat intro; inversion H. Qed.

  Lemma inth_in : forall n l x (Hnth : inth l n = Some x), iIn x l.
  Proof.
    induction n; destruct l; clarify; constructor; eauto.
  Qed.

End IList.
Arguments inil [_].

Lemma prefix_map : forall {A B} (f : A -> B) (l1 l2 : list A)
  (Hpre : iprefix (to_ilist l1) (to_ilist l2)),
  iprefix (to_ilist (map f l1)) (to_ilist (map f l2)).
Proof.
  induction l1; clarify; inversion Hpre; try constructor; destruct l2;
    clarify.
  inversion H; clarify.
  constructor; auto.
Qed.

Lemma prefix_flatten : forall {A} (l1 l2 : list (list A))
  (Hpre : iprefix (to_ilist l1) (to_ilist l2)),
  iprefix (to_ilist (flatten l1)) (to_ilist (flatten l2)).
Proof.
  induction l1; clarify; inversion Hpre; try constructor; destruct l2;
    clarify.
  inversion H; clarify.
  repeat rewrite <- iapp_nil_ilist in *; repeat rewrite <- iapp_app;
    apply prefix_mono.
  setoid_rewrite <- iapp_nil_ilist in IHl1; apply IHl1; auto.
Qed.
Hint Resolve prefix_map prefix_flatten prefix_filter.

Hint Rewrite inth_nth_error inth_nil itake_firstn idrop_skipn : list.

CoFixpoint imap A B (f : A -> B) l :=
  match l with
  | inil => inil
  | icons x rest => icons (f x) (imap f rest)
  end.

(* Is this of any use? *)
CoInductive iflatten A : ilist (list A) -> ilist A -> Prop :=
| flatten_nil : iflatten inil inil
| flatten_cons : forall l rest rest' (Hrest : iflatten rest rest'),
    iflatten (icons l rest) (iapp l rest').