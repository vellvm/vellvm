From Vellvm Require Import
     Utils.Tactics.

Require Coqlib.
From Coq Require Import
     micromega.Lia
     Ascii
     Strings.String
     Arith.Arith
     ZArith
     Nat
     PeanoNat
     Psatz.
Require Import FunInd Recdef.

Section nat_Show.
  #[local] Open Scope string.
  #[local] Open Scope nat.
  Definition get_last_digit (n: nat): string :=
    match n mod 10 with
    | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
    | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
    end.

  Function string_of_nat_aux (acc: string) (n : nat) {measure id n}: string :=
    let acc' := get_last_digit n ++ acc in
    match n / 10 with
    | 0 => acc'
    | n' => string_of_nat_aux acc' n'
    end.
  intros _ n m ineq.
  unfold id; simpl.
  destruct n as [| n]; [simpl in *; easy |].
  rewrite <- ineq; apply Nat.div_lt; lia.
  Defined.

  Definition string_of_nat := string_of_nat_aux "".

  Lemma mod_div_eq: forall a b q,
      q <> 0 ->
      a mod q = b mod q ->
      a / q = b / q ->
      a = b.
  Proof using.
    intros.
    rewrite (Nat.div_mod a q); auto.
    rewrite (Nat.div_mod b q); auto.
  Qed.

  Lemma get_last_digit_inj: forall n m,
      n <> m ->
      n/10 = m/10 ->
      get_last_digit n <>
      get_last_digit m.
  Proof using.
    intros n m ineq eq.
    unfold get_last_digit.
    do 9 (flatten_goal; [repeat flatten_goal; try easy; exfalso; apply ineq,(mod_div_eq n m 10); lia |]).
    subst.
    do 9 (flatten_goal; [easy |]).
    subst.
    exfalso.
    destruct n8.
    2: generalize (Nat.mod_upper_bound n 10 (ltac:(auto))); intros EQ; rewrite Heq in EQ; lia. 
    destruct n9.
    2: generalize (Nat.mod_upper_bound m 10 (ltac:(auto))); intros EQ; rewrite Heq0 in EQ; lia. 
    exfalso; apply ineq,(mod_div_eq n m 10); lia.
  Qed.

  Lemma append_EmptyString: forall s,
      s ++ "" = s.
  Proof using.
    induction s as [| c s IH]; simpl; auto.
    rewrite IH; auto.
  Qed.

  Lemma append_String: forall s c s',
      s ++ String c s' = (s ++ String c "") ++ s'.
  Proof using.
    induction s as [| c' s IH]; simpl; intros c s'; auto.
    f_equal.
    apply IH.
  Qed.

  Lemma append_char_simplify_r: forall s s' c,
      s ++ String c "" = s' ++ String c "" ->
      s = s'.
  Proof using.
    induction s as [| c s IH]; intros [| c' s']; simpl; intros tl eq; auto.
    - inv eq.
      destruct s'; inv H1.
    - inv eq.
      destruct s; inv H1.
    - inv eq.
      f_equal.
      eapply IH; eauto.
  Qed.

  Lemma append_simplify_r: forall s2 s1 s1',
      s1 ++ s2 = s1' ++ s2 ->
      s1 = s1'.
  Proof using.
    induction s2 as [| c s2 IH].
    - intros s1 s1' H; rewrite 2 append_EmptyString in H; auto. 
    - intros s1 s1' H.
      rewrite append_String in H.
      rewrite (append_String s1' c s2) in H.
      apply IH,append_char_simplify_r in H.
      assumption.
  Qed.

  Lemma append_simplify_l: forall s1 s2 s2',
      s1 ++ s2 = s1 ++ s2' ->
      s2 = s2'.
  Proof using.
    induction s1 as [| c s1 IH]; simpl; intros s2 s2' eq; auto.
    inv eq; apply IH; auto.
  Qed.

  Lemma append_assoc: forall s1 s2 s3,
      s1 ++ s2 ++ s3 = (s1 ++ s2) ++ s3.
  Proof using.
    induction s1 as [| c s1 IH]; simpl; intros; [reflexivity |].
    rewrite IH; reflexivity.
  Qed.

  Lemma string_of_nat_aux_prepends:
    forall n acc,
    exists hd, hd <> "" /\ string_of_nat_aux acc n = hd ++ acc.
  Proof using.
    induction n using (well_founded_induction lt_wf).
    intros acc.
    rewrite string_of_nat_aux_equation.
    flatten_goal.
    { eexists; split; [| reflexivity].
      unfold get_last_digit.
      do 9 (flatten_goal; [easy |]); easy.
    }
    edestruct (H (S n0)) as (hd & ineq & eq).
    - rewrite <- Heq; apply Nat.div_lt.
      { destruct n; [inv Heq| auto with arith]. }
      auto with arith.
    - rewrite eq.
      rewrite append_assoc.
      exists (hd ++ get_last_digit n); split; auto.
      clear - ineq.
      intros abs; apply ineq.
      destruct hd; [reflexivity | inv abs].
  Qed.

  Lemma get_last_digit_len1: forall n,
      String.length (get_last_digit n) = 1.
  Proof using.
    intros n; unfold get_last_digit.
    do 9 (flatten_goal; [reflexivity |]); reflexivity.
  Qed.

  Lemma length_append:
    forall s s', String.length (s ++ s') = String.length s + String.length s'.
  Proof using.
    induction s as [| c s IH]; intros s'; simpl; [reflexivity | rewrite IH; reflexivity].
  Qed.

  Lemma length_nonEmpty:
    forall s, s <> "" -> String.length s > 0.
  Proof using.
    intros []; [intros abs; easy | intros _; simpl; auto with arith].
  Qed.

  Lemma append_same_length_eq_l:
    forall s1 s1' s2 s2',
      s1 ++ s2 = s1' ++ s2' ->
      String.length s1 = String.length s1' ->
      s1 = s1'.
  Proof using.
    induction s1 as [| c1 s1 IH]; simpl; intros.
    - destruct s1'; [reflexivity | inv H0]. 
    - destruct s1' as [| c1' s1']; [inv H0 |].
      simpl in *.
      inv H0.
      inv H.
      f_equal.
      eapply IH; eauto.
  Qed.

  Lemma append_same_length_eq_r:
    forall s1 s1' s2 s2',
      s1 ++ s2 = s1' ++ s2' ->
      String.length s2 = String.length s2' ->
      s2 = s2'.
  Proof using.
    intros.
    assert (String.length s1 = String.length s1').
    { generalize (length_append s1 s2).
      intros ?.
      rewrite H0,H, length_append in H1. 
      lia.
    }
    eapply append_same_length_eq_l in H1; eauto.
    subst.
    eapply append_simplify_l; eauto. 
  Qed.

  Ltac eq_fun H f :=
    match type of H with
    | ?x1 = ?x2 => assert (f x1 = f x2) by (rewrite H; reflexivity)
    end.

  Lemma append_same_length_eq_r':
    forall s1 s1' s2 s2',
      s1 ++ s2 = s1' ++ s2' ->
      String.length s2 = String.length s2' ->
      s1 = s1'.
  Proof using.
    intros.
    generalize H; intros H'; apply append_same_length_eq_r in H'; auto; subst.
    eapply append_same_length_eq_l; eauto.
    eq_fun H String.length.
    rewrite 2 length_append in H1.
    lia.
  Qed.

  Lemma string_of_nat_aux_inj: forall n m acc,
      n <> m ->
      string_of_nat_aux acc n <>
      string_of_nat_aux acc m.
  Proof using.
    induction n using (well_founded_induction lt_wf).
    intros m acc ineq.
    rewrite 2 string_of_nat_aux_equation.
    flatten_goal.
    - flatten_goal.
      + intros abs.
        apply (get_last_digit_inj n m); try lia.
        apply append_simplify_r in abs; auto.
      + destruct (string_of_nat_aux_prepends (S n0) (get_last_digit m ++ acc)) as (hd & nonnil & ->). 
        intros abs. 
        match type of abs with
        | ?s1 = ?s2 => assert (abs':String.length s1 = String.length s2) by (rewrite abs; reflexivity)
        end.
        rewrite 3 length_append, 2 get_last_digit_len1 in abs'.
        clear - abs' nonnil.
        apply length_nonEmpty in nonnil; simpl in *.
        lia.
    - flatten_goal.
      + destruct (string_of_nat_aux_prepends (S n0) (get_last_digit n ++ acc)) as (hd & nonnil & ->). 
        intros abs. 
        match type of abs with
        | ?s1 = ?s2 => assert (abs':String.length s1 = String.length s2) by (rewrite abs; reflexivity)
        end.
        rewrite 3 length_append, 2 get_last_digit_len1 in abs'.
        clear - abs' nonnil.
        apply length_nonEmpty in nonnil; simpl in *.
        lia.
      + destruct (Nat.eq_decidable (n mod 10) (m mod 10)).
        * replace (get_last_digit m) with (get_last_digit n).
          2:unfold get_last_digit; rewrite H0; reflexivity.
          destruct (Nat.eq_decidable n0 n1).
          { subst. exfalso.
            eapply ineq, (mod_div_eq n m 10); lia.
          }
          apply H.
          rewrite <- Heq; apply Nat.div_lt.
          { destruct n; [inv Heq| auto with arith]. }
          auto with arith.
          auto.
        * destruct (string_of_nat_aux_prepends (S n0) (get_last_digit n ++ acc)) as (hd & nonnil & ->).
          destruct (string_of_nat_aux_prepends (S n1) (get_last_digit m ++ acc)) as (hd' & nonnil' & ->). 
          intros abs.
          rewrite 2 append_assoc in abs.
          apply append_simplify_r in abs.
          apply append_same_length_eq_r in abs; [| rewrite 2get_last_digit_len1; reflexivity].
          clear -abs H0.
          unfold get_last_digit in abs.
          apply H0; clear H0.
          do 9 (flatten_all; [do 9 (flatten_all; try easy) |]).
          do 9 (flatten_all; try easy).         
          subst.
          assert (tmp:10 <> 0) by lia.
          destruct n8; [| generalize (Nat.mod_upper_bound n 10 tmp); intros ineq; rewrite Heq in ineq; lia].
          destruct n17; [easy| generalize (Nat.mod_upper_bound m 10 tmp); intros ineq; rewrite Heq8 in ineq; lia].
  Qed.          

  Lemma string_of_nat_inj: forall n m,
      n <> m ->
      string_of_nat n <>
      string_of_nat m.
  Proof using.
    intros n m; unfold string_of_nat; apply string_of_nat_aux_inj.
  Qed.

  Definition string_of_Z (n: Z) : string :=
    match n with
    | Z0 => "0"
    | Zpos p => string_of_nat (Pos.to_nat p)
    | Zneg p => "-" ++ string_of_nat (Pos.to_nat p)
    end.

  Lemma get_last_digit_0_iff:
    forall n, get_last_digit n = "0" <-> n mod 10 =  0.
  Proof using.
    intros n; split; intros H.
    - unfold get_last_digit in H.
      flatten_hyp H; [subst; reflexivity |].
      do 8 (flatten_hyp H; [inv H |]); inv H.
    - unfold get_last_digit; rewrite H; reflexivity.
  Qed.

  Lemma string_of_nat_0_iff:
    forall n, string_of_nat n = "0" <-> n = 0.
  Proof using.
    intros n; split; intros H.
    - destruct n as [|n]; [reflexivity | exfalso].
      unfold string_of_nat in H; rewrite string_of_nat_aux_equation in H.
      flatten_hyp H.
      + rewrite append_EmptyString in H.
        rewrite get_last_digit_0_iff in H.
        generalize (Nat.Div0.mod_eq (S n) 10).
        rewrite H, Heq; simpl; intros abs; inv abs.
      + rewrite append_EmptyString in H; destruct (string_of_nat_aux_prepends (S n0) (get_last_digit (S n))) as (hd & eq & eq'). 
        rewrite H in eq'.
        replace "0" with ("" ++ "0") in eq' by reflexivity.
        apply append_same_length_eq_r' in eq' ; [| rewrite get_last_digit_len1; reflexivity].
        subst; tauto.
    - subst; reflexivity. 
  Qed.

  Lemma pos_to_nat_inj:
    forall p p',
      p <> p' ->
      Pos.to_nat p <> Pos.to_nat p'.
  Proof using.
    intros; intro abs; apply Pos2Nat.inj in abs; easy. 
  Qed.

  Lemma string_of_nat_aux_hd_get_last_digit:
    forall n c s acc, string_of_nat_aux acc n = String c s -> exists n', String c "" = get_last_digit n'.
  Proof using.
    intros n c.
    induction n using (well_founded_induction lt_wf).
    intros s acc EQ.
    unfold string_of_nat in EQ.
    rewrite string_of_nat_aux_equation in EQ.
    flatten_hyp EQ.
    - replace (String c s) with (String c "" ++ s) in EQ by reflexivity.
      apply append_same_length_eq_l in EQ; [| rewrite get_last_digit_len1; reflexivity].
      rewrite <- EQ; eauto.
    - apply H in EQ; [assumption |].
      rewrite <- Heq; apply Nat.div_lt.
      { destruct n; [inv Heq| auto with arith]. }
      auto with arith.
  Qed.

  Lemma string_of_nat_hd_get_last_digit:
    forall n c s, string_of_nat n = String c s -> exists n', String c "" = get_last_digit n'.
  Proof using.
    intros; eapply string_of_nat_aux_hd_get_last_digit; eauto.
  Qed.

  Lemma string_of_Z_inj: forall n m,
      n <> m ->
      string_of_Z n <>
      string_of_Z m.
  Proof using.
    intros n m ineq.
    destruct n, m; simpl; try easy.
    try (intros abs; symmetry in abs; rewrite string_of_nat_0_iff in abs; lia).
    try (intros abs; rewrite string_of_nat_0_iff in abs; lia).
    {apply string_of_nat_inj, pos_to_nat_inj; intros abs; apply ineq; rewrite abs; reflexivity. }
    { destruct (string_of_nat (Pos.to_nat p)) as [| c s] eqn:EQ; [easy |].
      apply string_of_nat_hd_get_last_digit in EQ; destruct EQ as [? EQ].
      intros abs; inv abs.
      unfold get_last_digit in EQ.
      do 9 (flatten_hyp EQ; [inv EQ |]); inv EQ.
    }
    { destruct (string_of_nat (Pos.to_nat p0)) as [| c s] eqn:EQ; [easy |].
      apply string_of_nat_hd_get_last_digit in EQ; destruct EQ as [? EQ].
      intros abs; inv abs.
      unfold get_last_digit in EQ.
      do 9 (flatten_hyp EQ; [inv EQ |]); inv EQ.
    }
    {intros abs; inv abs.
     generalize H0.
     apply string_of_nat_inj, pos_to_nat_inj; intros abs; apply ineq; rewrite abs; reflexivity. }
  Qed.

  (* Things are much simpler otherwise with a binary representation... *)
  Fixpoint string_of_nat_bin (n: nat): string :=
    match n with
    | O => ""
    | S n => String (ascii_of_nat 49) (string_of_nat_bin n)
    end.

  Lemma string_of_nat_bin_inj:
    forall (n m: nat), n <> m -> string_of_nat_bin n <> string_of_nat_bin m.
  Proof using.
    induction n as [| n IH]; simpl; intros m ineq.
    - destruct m as [| m]; [lia | intros abs; inversion abs].
    - destruct m as [| m]; [intros abs; inversion abs |].
      simpl; intros abs; inversion abs; subst; clear abs.
      apply (IH m); auto.
  Qed.

End nat_Show.

From Coq Require Import
     List
     Lia
     RelationClasses.
Import ListNotations.

Set Implicit Arguments.


(* Arithmetic --------------------------------------------------------------- *)


Lemma pred_minus_S : forall m n,
  pred m - n = m - S n.
Proof using.
  induction m; auto.
Qed.

(* Relations ---------------------------------------------------------------- *)

Inductive rtc {A} (R:A -> A -> Prop) : A -> A -> Prop :=
| rtc_refl : forall a, rtc R a a
| rtc_step : forall a b c, R a b -> rtc R b c -> rtc R a c.

#[global] Instance rtc_Transitive {A} {R} : Transitive (@rtc A R).
Proof using.
  unfold Transitive; intros.
  induction H. auto. econstructor; eauto.
Qed.

Arguments rtc [_] _ _ _.

Notation "R ^*" := (rtc R) (at level 1, format "R ^*").


(* Lists -------------------------------------------------------------------- *)

Lemma Forall_map_impl {A B} : forall (P:A -> Prop) (Q:B -> Prop) (f:A -> B),
    (forall a, P a -> Q (f a)) ->
    forall l : list A, Forall P l -> Forall Q (map f l).
Proof using.
  intros ? ? ? Himpl ? Hforall.
  rewrite Forall_forall in *. intros ? Hin.
  apply in_map_iff in Hin as [? [? ?]]; subst.
  apply Himpl. apply Hforall. assumption.
Qed.

Fixpoint map2 {A B C:Type} (f:A -> B -> C) (la:list A) (lb:list B) : list C :=
  match la, lb with
    | [], _ | _, [] => []
    | a::la', b::lb' => f a b :: map2 f la' lb'
  end.

Lemma Forall2_impl : forall {A B} (P Q : A -> B -> Prop) l1 l2
  (Himpl : forall a b, P a b -> Q a b), Forall2 P l1 l2 -> Forall2 Q l1 l2.
Proof using. intros; induction H; auto. Qed.

Lemma Forall2_impl' : forall {A B} (P Q : A -> B -> Prop) l1 l2
  (Himpl : forall a b, In a l1 -> P a b -> Q a b), 
  Forall2 P l1 l2 -> Forall2 Q l1 l2.
Proof using. 
  intros; induction H; auto.
  constructor.
  - apply Himpl; simpl; auto.
  - apply IHForall2. intros; apply Himpl; simpl; auto.
Qed.

Lemma Forall2_length : forall {A B} (P : A -> B -> Prop) l1 l2,
  Forall2 P l1 l2 -> length l1 = length l2.
Proof using. intros; induction H; simpl; auto. Qed.


Inductive Forall3 (A B C : Type) (R : A -> B -> C -> Prop) 
  : list A -> list B -> list C -> Prop :=
  | Forall3_nil : Forall3 R [] [] []
  | Forall3_cons : forall x y z l m n,
                   R x y z -> Forall3 R l m n -> Forall3 R (x :: l) (y :: m) (z :: n).

Definition forall2b {A B} (f : A -> B ->bool) (l:list A) (m:list B) : bool :=
  let fix loop l m :=
  match l, m with
  | [], [] => true
  | a::l',b::m' => andb (f a b) (loop l' m')
  | _, _ => false
  end in loop l m.

Definition Nth {A:Type} (l:list A) (n:nat) (a:A) : Prop := nth_error l n = Some a.

Arguments Nth _ _ _ _ /. 

Lemma not_Nth_nil : forall X n (x:X),
  ~ Nth [] n x.
Proof using.
  destruct n; discriminate. 
Qed.

#[export] Hint Resolve not_Nth_nil : core.

Lemma Nth_nth_default : forall X l n (a:X) d,
  Nth l n a ->
  nth_default d l n = a.
Proof using.
  induction l; simpl; intros.
  destruct n; inversion H.
  unfold nth_default. rewrite H; auto.
Qed.

Lemma Nth_map : forall (A B:Type) (f:A -> B) l n a b
  (Hnth : Nth l n a)
  (Heq : b = f a),
  Nth (map f l) n b.
Proof using.
  induction l; intros; subst.
  destruct n; inversion Hnth.
  destruct n. inversion Hnth. simpl; auto. 
  inversion Hnth; eapply IHl; eauto.
Qed.

Fixpoint Forall_dec {A} (P : A -> Prop) (p_dec:forall a, {P a} + {~ P a})
  (l:list A) : {Forall P l} + {~ Forall P l}.
  refine match l with
           | [] => left _
           | a::l' => match p_dec a, Forall_dec _ P p_dec l' with
                        | left Ha , left Hl' => left _
                        | _, _ => right _
                      end
         end; auto.
  - intro contra. inversion contra; subst. contradiction.
  - intro contra. inversion contra; subst. contradiction.
Defined.
Arguments Forall_dec {_ _} _ _.

Lemma Forall_Nth : forall (A:Type) l P (a:A) n,
  Forall P l ->
  Nth l n a ->
  P a.
Proof using.
  intros. generalize dependent l.
  induction n; intros.
  inversion H; inversion H0; subst. discriminate.
  inversion H5; subst. inversion H; auto.
  destruct l. inversion H0.
  inversion H; eauto.
Qed.
  
Lemma Nth_Forall2_Nth : forall n (A B:Type) l1 l2 P (b:B),
  Nth l2 n b ->
  Forall2 P l1 l2 ->
  exists (a:A), (Nth l1 n a) /\ P a b.
Proof using.
  induction n; intros.
  destruct l2. inversion H.
  inversion H0; subst.
  inversion H; subst.
  simpl; intuition eauto.
  inversion H0; subst. inversion H.
  simpl in *.
  ecase IHn; eauto.
Qed.

Lemma Forall2_Nth_left : forall {A B:Type} n l1 l2 R (a:A),
    Nth l1 n a ->
    Forall2 R l1 l2 ->
    exists (b:B), (Nth l2 n b) /\ R a b.
Proof using.
  induction n as [| n IH]; cbn; intros.
  destruct l1; inv H0; inv_option.
  eexists; eauto.
  destruct l1; inv H0; try inv_option.
  edestruct IH; eauto.
Qed.

Lemma Forall2_Nth_right : forall {A B:Type} n l1 l2 R (b:B),
    Nth l2 n b ->
    Forall2 R l1 l2 ->
    exists (a:A), (Nth l1 n a) /\ R a b.
Proof using.
  induction n as [| n IH]; cbn; intros.
  destruct l1; inv H0; inv_option.
  eexists; eauto.
  destruct l1; inv H0; try inv_option.
  edestruct IH; eauto.
Qed.

Lemma Forall2_Nth : forall {A B:Type} n l1 l2 R (a:A) (b : B),
    Nth l1 n a ->
    Nth l2 n b ->
    Forall2 R l1 l2 ->
    R a b.
Proof using.
  induction n as [| n IH]; cbn; intros.
  destruct l1; inv H1; repeat inv_option; auto.
  destruct l1; inv H1; repeat inv_option; auto.
  eapply IH; eauto.
Qed.

Lemma Forall_map_eq : forall A B (f g : A -> B) l
  (Hall : Forall (fun x => f x = g x) l),
  map f l = map g l.
Proof using.
  induction l; auto; intro.
  inversion Hall; simpl.
  rewrite H1, IHl; auto.
Qed.

Fixpoint replace {A:Type} (l:list A) (n:nat) (a:A) : list A :=
  match n, l with
    | O, _::l' => a::l'
    | S n', a'::l' => a'::replace l' n' a
    | _, [] => []
  end.

Lemma replace_length : forall {A} l n (a : A),
  length (replace l n a) = length l.
Proof using.
  induction l; simpl; intros.
  - destruct n; auto.
  - destruct n; simpl; auto.
Qed.

Lemma Nth_replace : forall {A} l n (a : A), n < length l ->
  Nth (replace l n a) n a.
Proof using.
  induction l; simpl; intros.
  - inversion H.
  - destruct n; simpl; try constructor.
    unfold Nth; simpl; apply IHl; lia.
Qed.

Lemma nth_error_replace : forall {A} l n (a : A) n' (Hn : n < length l),
  nth_error (replace l n a) n' = if Nat.eqb n n' then Some a
                                 else nth_error l n'.
Proof using.
  induction l; intros; try (solve [inversion Hn]); simpl in *.
  destruct n; destruct n'; auto; simpl.
  apply IHl; lia.
Qed.

Lemma replace_over : forall {A} l n (a : A) (Hnlt : ~n < length l),
  replace l n a = l.
Proof using.
  induction l; intros; destruct n; simpl in *; auto; try lia.
  rewrite IHl; auto; lia.
Qed.

Lemma list_cons_app :
  forall {A} (x : A) l, x :: l = [x] ++ l.
Proof using.
  cbn. reflexivity.
Qed.

(* replicate ---------------------------------------------------------------- *)

Fixpoint replicate {A} (a:A) (n:nat) : list A :=
  match n with
  | O => nil
  | S n' => a :: replicate a n'
  end.

Lemma replicate_length : forall {A} n (a : A), length (replicate a n) = n.
Proof using. induction n; simpl; auto. Qed.

Lemma replicate_Nth : forall {A} n (a : A) n' (Hlt : n' < n),
  Nth (replicate a n) n' a.
Proof using.
  induction n; simpl; intros; [inversion Hlt|].
  destruct n'; auto.
  simpl; apply IHn; lia.
Qed.


(* Intervals ---------------------------------------------------------------- *)

Fixpoint interval n m := 
  match m with
  | O => []
  | S j => if le_lt_dec n j then interval n j ++ [j] else []
  end.

Lemma Forall_app : forall {A} P (l l': list A),
  Forall P (l ++ l') <-> Forall P l /\ Forall P l'.
Proof using.
  induction l; simpl; intros.
  - split; auto; intros [? ?]; auto.
  - split; [intro H | intros [H ?]]; inversion H; subst.
    + rewrite IHl in *; destruct H3; auto.
    + constructor; auto; rewrite IHl; auto.
Qed.


Lemma interval_lt : forall m n, Forall (fun x => x < m) (interval n m).
Proof using.
  induction m; simpl; auto; intros.
  destruct (le_lt_dec n m); auto.
  rewrite Forall_app; split; auto.
  eapply Forall_impl; eauto; auto.
Qed.

Lemma interval_ge : forall m n, Forall (fun x => x >= n) (interval n m).
Proof using.
  induction m; simpl; auto; intros.
  destruct (le_lt_dec n m); auto.
  rewrite Forall_app; split; auto.
Qed.

Lemma interval_nil : forall n, interval n n = [].
Proof using.
  intro; destruct n; auto; unfold interval.
  destruct (le_lt_dec (S n) n); auto; lia.
Qed.

Lemma interval_alt : forall m n, interval n m = 
  if lt_dec n m then n :: interval (S n) m else [].
Proof using.
  induction m; auto; intro.
  unfold interval at 1; fold interval.
  destruct (le_lt_dec n m); destruct (lt_dec n (S m)); auto; try lia.
  rewrite IHm.
  destruct (lt_dec n m).
  - unfold interval at 2; fold interval.
    destruct (le_lt_dec (S n) m); auto; lia.
  - apply le_lt_eq_dec in l; destruct l; [contradiction | subst].
    rewrite interval_nil; auto.
Qed.

Lemma interval_length : forall m n, length (interval n m) = m - n.
Proof using.
  induction m; auto; intro; simpl.
  destruct (le_lt_dec n m).
  - rewrite app_length, IHm; simpl.
    destruct n; lia.
  - destruct n; simpl; lia.
Qed.        

Lemma nth_error_nil : forall A n, nth_error ([] : list A) n = None.
Proof using.
  induction n; auto.
Qed.

Lemma nth_error_In : forall {A} l n (a : A), nth_error l n = Some a -> In a l.
Proof using.
  induction l; intros; destruct n; simpl in *; inversion H; eauto.      
Qed.

Lemma in_nth_error : forall A (x : A) l, In x l ->
  exists n, nth_error l n = Some x.
Proof using.
  induction l; simpl; intros.
  - inversion H.
  - destruct H.
    + exists 0; subst; auto.
    + specialize (IHl H); destruct IHl as (n & ?); exists (S n); auto.
Qed.

Lemma nth_error_in : forall {A} (l : list A) n a,
  nth_error l n = Some a -> n < length l.
Proof using.
  induction l; intros; destruct n; simpl in *; inversion H; subst.
  - lia.
  - specialize (IHl _ _ H); lia.
Qed.

Lemma nth_error_succeeds : forall {A} (l : list A) n, n < length l ->
  exists a, nth_error l n = Some a.
Proof using.
  induction l; simpl; intros.
  - inversion H.
  - destruct n; simpl; eauto.
    apply IHl; lia.
Qed.

Fixpoint distinct {A} (l : list A) :=
  match l with
  | [] => True
  | a :: rest => ~In a rest /\ distinct rest
  end.



Lemma distinct_inj : forall {A} l i j (a : A) (Hdistinct : distinct l)
  (Hi : Nth l i a) (Hj : Nth l j a), i = j.
Proof using.
  induction l; simpl; intros; unfold Nth in *; destruct i; simpl in *;
  inversion Hi; subst; destruct j; simpl in *; inversion Hj; subst;
  destruct Hdistinct as [Hin ?]; eauto.
  - contradiction Hin; eapply nth_error_In; eauto.
  - contradiction Hin; eapply nth_error_In; eauto.
Qed.

Lemma distinct_snoc : forall {A} l (a : A) (Hdistinct : distinct l)
  (Hin : ~In a l), distinct (l ++ [a]).
Proof using.
  induction l; simpl; intros; auto.
  destruct Hdistinct; split; eauto; intro Hin'.
  rewrite in_app_iff in *; simpl in *; destruct Hin' as [? | [? | ?]];
    auto.
Qed.      

Lemma interval_distinct : forall m n, distinct (interval n m).
Proof using.
  induction m; simpl; intros; auto.
  destruct (le_lt_dec n m); simpl; auto.
  apply distinct_snoc; auto.
  generalize (interval_lt m n); intro Hlt.
  intro Hin; rewrite Forall_forall in Hlt; specialize (Hlt _ Hin); lia.
Qed.


Lemma Nth_app1 : forall {A} l n (a : A) (Hnth : Nth l n a) l', 
  Nth (l ++ l') n a.
Proof using.
  induction l; simpl; intros; destruct n; unfold Nth in *; simpl in *;
    inversion Hnth; subst; auto.
  erewrite IHl; eauto.
Qed.

Lemma Nth_app2 : forall {A} l n (a : A) (Hnth : Nth l n a) l',
  Nth (l' ++ l) (n + length l') a.
Proof using.
  induction l'; simpl; intros.
  - rewrite <- plus_n_O; auto.
  - rewrite <- plus_n_Sm; unfold Nth; simpl; auto.
Qed.

Lemma Nth_app : forall {A} (l l' : list A) n a (Hnth : Nth (l ++ l') n a),
  if lt_dec n (length l) then Nth l n a else Nth l' (n - length l) a.
Proof using.
  induction l; simpl; intros.
  - rewrite Nat.sub_0_r; auto.
  - destruct n; simpl in *; auto.
    specialize (IHl _ _ _ Hnth); destruct (lt_dec n (length l));
      destruct (lt_dec (S n) (S (length l))); auto; lia.
Qed.

Lemma Nth_In :
  forall {X} (xs : list X) i (x : X),
    Nth xs i x ->
    In x xs.
Proof using.
  intros X xs i x NTH.
  unfold Nth in *.
  eapply nth_error_In; eauto.
Qed.

Lemma Nth_list_nth_z :
  forall {X} (ix : nat) (xs : list X) (x : X),
    Nth xs ix x ->
    Coqlib.list_nth_z xs (Z.of_nat ix) = Some x.
Proof using.
  intros X ix xs.
  revert ix.
  induction xs; intros ix x NTH.
  - destruct ix; cbn in NTH; inv NTH.
  - cbn in *.
    destruct ix.
    + cbn in *; inv NTH; auto.
    + cbn in NTH.
      apply IHxs in NTH.
      replace (Z.pred (Z.of_nat (S ix))) with (Z.of_nat ix) by lia.
      cbn; auto.
Qed.

Lemma interval_Nth : forall m n i (Hlt : i < m - n),
  Nth (interval n m) i (i + n).
Proof using.
  induction m; simpl; intros.
  - inversion Hlt.
  - destruct (lt_dec i (m - n)).
    + specialize (IHm _ _ l).
      destruct (le_lt_dec n m); try lia.
      apply Nth_app1; auto.
    + destruct (le_lt_dec n m).
      * generalize (@Nth_app2 _ [m] 0); unfold Nth; simpl; intro.
        specialize (H _ eq_refl (interval n m)).
        rewrite interval_length in H.
        assert (i = m - n) as Hi by (destruct n; lia).
        rewrite Hi; assert (m - n + n = m) as Hm by lia; rewrite Hm; auto.
      * destruct n; lia.
Qed.

    
Lemma Forall2_forall : forall {A B} (P : A -> B -> Prop) al bl,
  Forall2 P al bl <-> (length al = length bl /\ 
                       forall i a b, Nth al i a -> Nth bl i b -> P a b).
Proof using.
  induction al; simpl; intros.
  - split; [intro H; inversion H; subst | intros [H ?]].
    + split; auto; intros ? ? ? Hnth ?; destruct i; simpl in Hnth; 
      inversion Hnth.
    + destruct bl; inversion H; auto.
  - destruct bl; simpl; [split; [intro H | intros [H ?]]; inversion H|].
    split; [intro H | intros [H ?]]; inversion H; subst.
    + rewrite IHal in *; destruct H5; split; auto; intros i a1 b1 Ha1 Hb1.
      destruct i; simpl in *; eauto.
      inversion Ha1; inversion Hb1; subst; auto.
    + constructor.
      * specialize (H0 0); simpl in *; eauto.
      * rewrite IHal; split; auto; intros.
        specialize (H0 (S i)); simpl in H0; auto.
Qed.  

Opaque minus.
Lemma interval_shift : forall j i k, k <= i -> interval i j =
  map (fun x => x + k) (interval (i - k) (j - k)).
Proof using.
  induction j; simpl; auto; intros.
  destruct (Compare_dec.le_lt_dec i j).
  - erewrite IHj; eauto.
    rewrite Nat.sub_succ_l; simpl; [|lia].
    destruct (Compare_dec.le_lt_dec (i - k) (j - k)); [|lia].
    rewrite map_app; simpl.
    rewrite Nat.sub_add; auto; lia.
  - destruct (Compare_dec.le_lt_dec k j).
    + rewrite Nat.sub_succ_l; simpl; try lia.
      destruct (Compare_dec.le_lt_dec (i - k) (j - k)); auto; try lia.
    + assert (S j - k = 0) as Heq by lia; rewrite Heq; auto.
Qed.
Transparent minus.

Corollary interval_S : forall j i, interval (S i) (S j) =
  map S (interval i j).
Proof using.
  intros.
  rewrite interval_shift with (k := 1); [simpl | lia].
  repeat rewrite Nat.sub_0_r.
  apply map_ext; intro; lia.
Qed.

Lemma flat_map_map : forall A B C (f : B -> list C) (g : A -> B) l,
  flat_map f (map g l) = flat_map (fun x => f (g x)) l.
Proof using.
  induction l; auto; simpl.
  rewrite IHl; auto.
Qed.

Lemma flat_map_ext : forall A B (f g : A -> list B),
  (forall a, f a = g a) -> forall l, flat_map f l = flat_map g l.
Proof using.
  induction l; auto; simpl.
  rewrite H, IHl; auto.
Qed.

Lemma interval_in_iff : forall i j k, In k (interval i j) <-> i <= k < j.
Proof using.
  intros; induction j; simpl; [lia|].
  destruct (Compare_dec.le_lt_dec i j); simpl; [|lia].
  rewrite in_app_iff, IHj; simpl; lia.
Qed.


Lemma app_nth_error1: forall (A : Type) (l l' : list A) (n : nat),
  n < length l -> nth_error (l ++ l') n = nth_error l n.
Proof using.
  induction l; simpl; intros.
  inversion H.
  destruct n eqn:Heqn; auto.
  eapply IHl; lia.
Qed.

Lemma app_nth_error2 : forall (A : Type) (l l' : list A) (n : nat),
    length l <= n -> nth_error (l ++ l') n = nth_error l' (n - length l).
Proof using.
  induction l; simpl; intros.
  auto with arith.
  destruct n eqn:Heqn.
  inversion H.
  simpl.
  eapply IHl; auto with arith.
Qed.

Lemma nth_error_nth : forall A l n (d:A),
      n < length l ->
      nth_error l n = Some (nth n l d).
Proof using.
  induction l.
  inversion 1. simpl. intros.
  destruct n eqn:Heqn.
  auto. simpl. eapply IHl. lia.
Qed.

Section REMOVE.

Variables (A:Type) (dec:forall (x y : A), {x = y} + {x <> y}).

Lemma remove_not_In : forall l x y,
  In x l ->
  x <> y ->
  In x (remove dec y l).
Proof using.
  induction l; intros.
  - inversion H.
  - inversion H; subst.
    + simpl. destruct (dec y x). contradict H0; auto. left; auto.
    + simpl. destruct (dec y a); subst; auto.
      right. apply IHl; auto.
Qed.
  
Lemma remove_length_le : forall l x,
  length (remove dec x l) <= length l.
Proof using.
  induction l; intros; auto.
  simpl. destruct (dec x a); simpl; auto.
  specialize (IHl x). lia.
Qed.

Lemma remove_length : forall l x,
  In x l ->
  length (remove dec x l) < length l.
Proof using.
  induction l; intros.
  - inversion H.
  - inversion H. 
    + subst. simpl. destruct (dec x x) as [_ | contra].
      unfold Peano.lt. eapply le_n_S. apply remove_length_le.
      contradict contra; auto.
    + simpl. specialize (IHl x H0). 
      destruct (dec x a); subst; simpl; lia.
Qed.

End REMOVE.



(* util *)
Lemma rev_nil_rev : forall A (l:list A),
  [] = rev l ->
  l = [].
Proof using.
  intros. destruct l; auto.
  simpl in H. destruct (rev l); simpl in H; inversion H.
Qed.

Lemma nth_map_inv : forall A B (f:A -> B) l b n,
  nth_error (map f l) n = Some b ->
  exists a, nth_error l n = Some a /\ f a = b.
Proof using.
  induction l; simpl; intros.
  - destruct n; inversion H.
  - destruct n; inversion H; subst.
    eexists; intuition eauto.
    ecase IHl as [? [? ?]]; eauto. 
Qed.


Fixpoint trim {A} (lo:list (option A)) : list A :=
  match lo with
  | [] | None::_ => []
  | Some a::lo' => a::trim lo'
  end.

(* alternate definition of nth to appease termination checker *)
Definition nth_f {A B} (d:B) (f:A->B) (n:nat) (l:list A) : B :=
  let fix loop n l {struct l} :=
      match n, l with
      | _, [] => d
      | O, a::l' => f a
      | S n', _::l' => loop n' l'
      end
  in loop n l.

Lemma nth_f_nth_error : forall A B (d:B) (f:A->B) l n,
  nth_f d f n l = match nth_error l n with
                 | None => d
                 | Some a => f a
                 end.
Proof using.
  induction l; intros; destruct n; simpl; auto.
Qed.    


(* to appease termination checker *)
(* Definition assoc_f {A B C} (a_dec:forall a b:A, {a = b} + {a <> b}) *)
(*            (d:C) (f:B -> C) (a:A) (l:list (A * B)) : C := *)
(*   let fix rec l := *)
(*       match l with *)
(*       | [] => d *)
(*       | (a',b)::l' => if a_dec a a' then f b else rec l' *)
(*       end in *)
(*   rec l. *)

(*   Lemma assoc_f__assoc : forall A B C l a_dec d (f:B->C) (a:A), *)
(*       assoc_f a_dec d f a l = *)
(*       match assoc a_dec a l with *)
(*       | None => d *)
(*       | Some b => f b *)
(*       end. *)
(*   Proof using. *)
(*     induction l; intros. *)
(*     - auto. *)
(*     - simpl. destruct a. destruct (a_dec a0 a). *)
(*       auto. *)
(*       apply IHl. *)
(*   Qed. *)

Require Import ExtLib.Programming.Eqv.
Require Import ExtLib.Core.RelDec.

Section With_Eqv_Rel_Dec.

  Context {A B : Type}.
  Context {RD:RelDec (@eq A)} {RDC:RelDec_Correct RD}.

  Lemma eq_dec_eq: forall a,
    rel_dec a a = true.
  Proof using A RD RDC.
    intros.
    rewrite rel_dec_correct.
    reflexivity.
  Qed.

  Lemma eq_dec_neq: forall a b,
      a <> b ->
      rel_dec a b = false.
  Proof using A RD RDC.
    intros.
    rewrite <- neg_rel_dec_correct.
    apply H.
  Qed.

  Fixpoint assoc (a:A) (l:list (A * B)) : option B :=
    match l with
    | [] => None
    | (a',b)::l' => if rel_dec a a' then Some b else assoc a l'
    end.

  Lemma assoc_hd: forall a b tl,
      assoc a ((a,b)::tl) = Some b.
  Proof using All.
    intros; cbn.
    rewrite eq_dec_eq; reflexivity.
  Qed.

  Lemma assoc_tl : forall (a c:A) (b:B) l 
                     (Hneq : a <> c),
      assoc a ((c,b)::l) =
      assoc a l.
  Proof using All.
    intros; cbn.
    rewrite eq_dec_neq; auto.
  Qed.

  (* Lemma assoc_cons_inv : *)
  (*   forall A B (a c:A) (b d:B) l a_dec *)
  (*     (Hl: assoc a_dec a ((c,b)::l) = Some d), *)
  (*     (a = c /\ b = d) \/ (a <> c /\ assoc a_dec a l = Some d). *)
  (* Proof using. *)
  (*   intros A B a c b d l a_dec Hl. *)
  (*   simpl in Hl. *)
  (*   destruct (a_dec a c). *)
  (*   left. inversion Hl. tauto. *)
  (*   right. tauto. *)
  (* Qed.     *)
  
  (* Lemma assoc_In_snd : forall A B (l:list (A * B)) eq_dec a b, *)
  (*     assoc eq_dec a l = Some b -> *)
  (*     In b (map (@snd _ _) l). *)
  (* Proof using. *)
  (*   induction l; intros; simpl in *. *)
  (*   - inversion H. *)
  (*   - destruct a. destruct (eq_dec _ _). *)
  (*     + inversion_clear H; subst. auto. *)
  (*     + right. eauto. *)
  (* Qed. *)

  (* Lemma assoc_In : forall A B (l:list (A * B)) eq_dec a b, *)
  (*     assoc eq_dec a l = Some b -> *)
  (*     In (a,b) l. *)
  (* Proof using. *)
  (*   induction l; intros; simpl in *. *)
  (*   - inversion H. *)
  (*   - destruct a. destruct (eq_dec _ _). *)
  (*     + inversion_clear H; subst. auto. *)
  (*     + right. eauto. *)
  (* Qed. *)

  (* Lemma assoc_succeeds : forall {A B} (a_dec : forall a b : A, {a = b} + {a <> b}) *)
  (*                          a l, In a (map (fst(B := B)) l) -> exists x, assoc a_dec a l = Some x. *)
  (* Proof using. *)
  (*   induction l; simpl; intros. *)
  (*   - contradiction. *)
  (*   - destruct a0; simpl in *. *)
  (*     destruct (a_dec a a0); eauto. *)
  (*     apply IHl; destruct H; auto. *)
  (*     contradiction n; auto. *)
  (* Qed. *)

End With_Eqv_Rel_Dec.

#[global] Instance string_eqv_dec : Eqv string := eq. 


(*
Theorem assoc_map :
  forall A B C eq_dec (x : A) (f : B -> C) l,
    assoc eq_dec x (map (fun p => (fst p, f (snd p))) l) =
    'v <- assoc eq_dec x l; Some (f v).
Proof using.
  intros; induction l; eauto.
  simpl. destruct a; simpl. rewrite IHl.
  destruct (eq_dec x a); simpl; eauto.
Qed.
*)


Lemma map_nth_error_none :
  forall A B  (l : list A) (f : A -> B) (n : nat),
  nth_error l n = None -> nth_error (map f l) n = None.
Proof using.
  induction l; simpl; intros.
  - destruct n; auto.
  - destruct n. inversion H.
    simpl. apply IHl; auto.
Qed.  

Lemma nth_error_out:
  forall A (l : list A) (n : nat),
  nth_error l n = None -> length l <= n.
Proof using.
  induction l; simpl; intros.
  - lia.
  - destruct n. inversion H. simpl in H. apply IHl in H. lia.
Qed.

Lemma map_ext_in : forall A B (f g : A -> B) l,
  (forall a, In a l -> f a = g a) -> 
  map f l = map g l.
Proof using.
  induction l; auto. intros Heq.
  simpl. f_equal. apply Heq. simpl; auto. 
  apply IHl. intros ? Hin. apply Heq. simpl; auto.
Qed.


Ltac destruct_Forall_cons :=
  match goal with
    | H : Forall _ (_::_) |- _ => inversion H; subst; clear H
  end.
#[export] Hint Extern 2 => destruct_Forall_cons : inversions.

Definition snoc {A} (a:A) (l:list A) : list A :=
  l ++ [a].

Lemma snoc_nonnil : forall A l (a : A), snoc a l <> [].
Proof using.
  unfold snoc; repeat intro.
  generalize (app_eq_nil _ _ H); intros (? & X); inversion X.
Qed.

Definition map_option {A B} (f:A -> option B) : list A -> option (list B) :=
  fix loop l :=
      match l with
      | [] => Some []
      | a::l' =>
        match f a, loop l' with
        | Some b, Some bl => Some (b::bl)
        | _, _ => None
        end
      end.

Lemma map_option_map : forall A B C (f:A -> option B) (g:C -> A) (l:list C),
    map_option f (map g l) = map_option (fun x => f (g x)) l.
Proof using.
  intros A B C f g l.
  induction l; simpl.
  - reflexivity.
  - destruct (f (g a)).
    +  rewrite IHl. reflexivity.
    + reflexivity.
Qed.      

Lemma map_option_nth : forall A B (f : A -> option B) l l',
  map_option f l = Some l' ->
  forall i x', nth_error l' i = Some x' <-> exists x, nth_error l i = Some x /\
    f x = Some x'.
Proof using.
  induction l; simpl; intros.
  - inversion H; split.
    + rewrite nth_error_nil; discriminate.
    + intros (? & ? & ?); rewrite nth_error_nil in *; discriminate.
  - destruct (f a) eqn: Ha; [|discriminate].
    destruct (map_option f l) eqn: Hl'; [|discriminate].
    inversion H; subst.
    specialize (IHl _ eq_refl).
    destruct i; simpl; auto.
    split.
    + intro Hx; inversion Hx; subst; eauto.
    + intros (? & Hx & ?); inversion Hx; subst.
      rewrite Ha in *; auto.
Qed.

Lemma map_option_length : forall A B (f : A -> option B) l l',
  map_option f l = Some l' -> length l' = length l.
Proof using.
  induction l; simpl; intros.
  - inversion H; auto.
  - destruct (f a); [|discriminate].
    destruct (map_option f l) eqn: Hl'; [|discriminate].
    inversion H; subst.
    simpl; rewrite IHl; auto.
Qed.

(*
Definition map_option_snd {A B C} (f : B -> option C) (p:A * B) : option (A * C) :=
  let '(x,y) := p in
  'z <- f y;
    Some (x,z).


*)

Fixpoint find_map {A B} (f : A -> option B) (l : list A) : option B :=
  match l with
  | [] => None
  | x::xs => match (f x) with
            | None => find_map f xs
            | Some ans => Some ans
            end
  end.


Definition opt_compose {A B C} (g:B -> C) (f:A -> option B) : A -> option C :=
  fun a => option_map g (f a).

Fixpoint option_iter {A} (f:A -> option A) (a:A) (n:nat) : option A :=
  match n with
  | 0 => Some a
  | S n' => match f a with
            | Some a' => option_iter f a' n'
            | None => None
            end
  end.

Arguments option_map {_ _} _ _.

Lemma option_map_id : forall A (a : option A), option_map id a = a.
Proof using.
  unfold option_map; destruct a; auto.
Qed.

Lemma option_map_ext : forall A B (f g:A->B),
  (forall a, f a = g a) ->
  forall oa, option_map f oa = option_map g oa.
Proof using.
  intros. destruct oa. simpl. rewrite H; auto. auto.
Qed.

Lemma option_map_some_inv {A B} : forall (o:option A) (f : A -> B) (b:B),
  option_map f o = Some b ->
  exists a, o = Some a /\ f a = b.
Proof using.
  destruct o; simpl; intros; inversion H; eauto.
Qed.

Definition option_prop {A} (P: A -> Prop) (a:option A) :=
  match a with
    | None => True
    | Some a' => P a'
  end.

Definition option_bind {A B} (m:option A) (f:A -> option B) : option B :=
  match m with
  | Some a => f a
  | None => None
  end.

Definition option_bind2 {A B C} (m: option (A * B)) (f: A -> B -> option C) : option C :=
  match m with
  | Some (a, b) => f a b
  | None => None
  end.

Module OptionNotations.

  Notation "'do' x <- m ; f" := (option_bind m (fun x => f)) 
    (at level 200, x name, m at level 100, f at level 200).

  Notation "'do' x , y <- m ; f" := (option_bind2 m (fun x y => f))
    (at level 200, x name, y name, m at level 100, f at level 200).

End OptionNotations.

Tactic Notation "not_var" constr(t) :=
  try (is_var t; fail 1 "not_var").

Create HintDb inversions.
Tactic Notation "iauto" := auto 10 with inversions.
Tactic Notation "ieauto" := eauto 10 with inversions.

Definition map_prod {A B C D} (p:A * B) (f:A -> C) (g:B -> D) : (C * D) :=
  (f (fst p), g (snd p)).

Definition flip := @Basics.flip.
Definition comp := @Basics.compose.

Notation "g `o` f" := (Basics.compose g f) 
  (at level 40, left associativity).

Lemma map_prod_distr_comp : forall A B C D E F
  (p:A * B) (f1:A -> C) (f2:B -> D) (g1:C -> E) (g2:D -> F),
  map_prod (map_prod p f1 f2) g1 g2 =
  map_prod p (g1 `o` f1) (g2 `o` f2).
Proof using.
  unfold map_prod, Basics.compose. auto.
Qed.

Definition map_snd {A B C} (f:B -> C) : list (A * B) -> list (A * C) :=
  map (fun ab : A * B => let (a, b) := ab in (a, f b)).

Import OptionNotations.

Lemma option_bind_assoc {A B C} : forall (o:option A) (p:A -> option B) (q:B -> option C),
   (do y <- (do x <- o; p x); q y) = (do x <- o; do y <- p x; q y).
Proof using.
  intros. destruct o; auto.
Qed.

Lemma option_bind_some_inv {A B} : forall (o:option A) (p:A -> option B) (b:B),
  (do x <- o; p x) = Some b ->
  exists a, o = Some a /\ p a = Some b.
Proof using.
  intros. destruct o. eexists. eauto. inversion H.
Qed.

Lemma option_bind_None : forall A B (m : option A),
  (do x <- m; (None(A := B))) = None.
Proof using.
  destruct m; auto.
Qed.

Lemma option_bind_some : forall A (m : option A),
  (do x <- m; Some x) = m.
Proof using.
  destruct m; auto.
Qed.

Tactic Notation "inv_bind" hyp(H) :=
  repeat rewrite option_bind_assoc in H;
    match type of H with
    | option_bind ?o ?p = Some ?b => 
      let hy := fresh H in
      destruct o eqn:hy; [|discriminate]; simpl in H
    end.

From Vellvm Require Import
     Numeric.Coqlib.
 
Infix "⊍" := list_disjoint (at level 60).

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

Section DisjointLists.

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
    - apply Coqlib.list_disjoint_cons_l.
      + eapply IHl1; eauto using Forall_inv_tail.
      + apply Forall_inv in L1.
        apply P1NP2 in L1.
        intros IN.
        eapply Forall_forall in L2; eauto.
  Qed.

End DisjointLists.

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

Definition guard_opt (x : bool) : option unit
  := if x then Some tt else None.

Lemma exists_in_bounds_le_lt :
  forall (lower upper x : Z),
    lower <= x < upper ->
    exists ix, 0 <= ix < (upper - lower) /\ x = lower + ix.
Proof using.
  intros lower upper x [LE LT].
  exists (x - lower).
  split; lia.
Qed.
