(* This file is imported from the itree tutorial *)

(** * Utilities for the compiler tutorial *)

(** This file should not be required to be read for
    understanding the remaining of the tutorial.
    It however contains no hidden black magic. Its
    main content is the following:
    - a few simple generic tactics;
    - a collection of facts about ExtLib's association
    lists [alist] that should probably be moved over ExtLib;
    - a function converting [nat] to their decimal representation
    as [string], and an unreasonably painful proof of the injectivity
    of this function.
    - a [traverse_] function.
*)

(* begin hide *)
From Coq Require Import
     Ascii
     Strings.String
     List
     Arith.Arith
     ZArith
     Nat 
     Psatz.

From ExtLib Require Import
     Core.RelDec
     Programming.Show
     Data.Map.FMapAList.
(* end hide *)

Ltac flatten_goal :=
  match goal with
  | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac flatten_hyp h :=
  match type of h with
  | context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac flatten_all :=
  match goal with
  | h: context[match ?x with | _ => _ end] |- _ => let Heq := fresh "Heq" in destruct x eqn:Heq
  | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac inv h := inversion h; subst; clear h.

Section alistFacts.


  (* Generic facts about alists. To eventually move to ExtLib. *)

  Arguments alist_find {_ _ _ _}.

  Definition alist_In {K R RD V} k m v := @alist_find K R RD V k m = Some v.

  Arguments alist_add {_ _ _ _}.
  Arguments alist_find {_ _ _ _}.
  Arguments alist_remove {_ _ _ _}. 

  Context {K V: Type}.
  Context {RR : @RelDec K (@eq K)}.
  Context {RRC : @RelDec_Correct K (@eq K) RR}.
  
  Lemma In_add_eq:
    forall k v (m: alist K V),
      alist_In k (alist_add k v m) v.
  Proof.
    intros; unfold alist_add, alist_In; simpl; flatten_goal; [reflexivity | rewrite <- neg_rel_dec_correct in Heq; tauto]. 
  Qed.

  (* A removed key is not contained in the resulting map *)
  Lemma not_In_remove:
    forall (m : alist K V) (k : K) (v: V),
      ~ alist_In k (alist_remove k m) v.
  Proof.
    induction m as [| [k1 v1] m IH]; intros.
    - simpl; intros abs; inv abs. 
    - simpl; flatten_goal.
      + unfold alist_In; simpl.
        rewrite Bool.negb_true_iff in Heq; rewrite Heq.
        intros abs; eapply IH; eassumption.
      + rewrite Bool.negb_false_iff, rel_dec_correct in Heq; subst.
        intros abs; eapply IH; eauto. 
  Qed.

  (* Removing a key does not alter other keys *)
  Lemma In_In_remove_ineq:
    forall (m : alist K V) (k : K) (v : V) (k' : K),
      k <> k' ->
      alist_In k m v ->
      alist_In k (alist_remove k' m) v.
  Proof.
    induction m as [| [? ?] m IH]; intros ?k ?v ?k' ineq IN; [inversion IN |].
    simpl.
    flatten_goal.
    - unfold alist_In in *; simpl in *.
      rewrite Bool.negb_true_iff, <- neg_rel_dec_correct in Heq.
      flatten_goal; auto.
    - unfold alist_In in *; simpl in *.
      rewrite Bool.negb_false_iff, rel_dec_correct in Heq; subst.
      flatten_hyp IN; [rewrite rel_dec_correct in Heq; subst; tauto | eapply IH; eauto].
  Qed.       

  Lemma In_remove_In_ineq:
    forall (m : alist K V) (k : K) (v : V) (k' : K),
      alist_In k (alist_remove k' m) v ->
      alist_In k m v.
  Proof.
    induction m as [| [? ?] m IH]; intros ?k ?v ?k' IN; [inversion IN |].
    simpl in IN; flatten_hyp IN.
    - unfold alist_In in *; simpl in *.
      flatten_all; auto.
      eapply IH; eauto.
    -rewrite Bool.negb_false_iff, rel_dec_correct in Heq; subst.
     unfold alist_In; simpl. 
     flatten_goal; [rewrite rel_dec_correct in Heq; subst |].
     exfalso; eapply not_In_remove; eauto.
     eapply IH; eauto.
  Qed.       

  Lemma In_remove_In_ineq_iff:
    forall (m : alist K V) (k : K) (v : V) (k' : K),
      k <> k' ->
      alist_In k (alist_remove k' m) v <->
      alist_In k m v.
  Proof.
    intros; split; eauto using In_In_remove_ineq, In_remove_In_ineq.
  Qed.       

  (* Adding a value to a key does not alter other keys *)
  Lemma In_In_add_ineq:
    forall k v k' v' (m: alist K V),
      k <> k' ->
      alist_In k m v ->
      alist_In k (alist_add k' v' m) v.
  Proof.
    intros.
    unfold alist_In; simpl; flatten_goal; [rewrite rel_dec_correct in Heq; subst; tauto |].
    apply In_In_remove_ineq; auto.
  Qed.

  Lemma In_add_In_ineq:
    forall k v k' v' (m: alist K V),
      k <> k' ->
      alist_In k (alist_add k' v' m) v ->
      alist_In k m v. 
  Proof.
    intros k v k' v' m ineq IN.
    unfold alist_In in IN; simpl in IN; flatten_hyp IN; [rewrite rel_dec_correct in Heq; subst; tauto |].
    eapply In_remove_In_ineq; eauto.
  Qed.

  Lemma In_add_ineq_iff: 
    forall m (v v' : V) (k k' : K),
      k <> k' ->
      alist_In k m v <-> alist_In k (alist_add k' v' m) v.
  Proof.
    intros; split; eauto using In_In_add_ineq, In_add_In_ineq.
  Qed.

  (* alist_find fails iff no value is associated to the key in the map *)
  Lemma alist_find_None:
    forall k (m: alist K V),
      (forall v, ~ In (k,v) m) <-> alist_find k m = None.
  Proof.
    induction m as [| [k1 v1] m IH]; [simpl; easy |].
    simpl; split; intros H. 
    - flatten_goal; [rewrite rel_dec_correct in Heq; subst; exfalso | rewrite <- neg_rel_dec_correct in Heq].
      apply (H v1); left; reflexivity.
      apply IH; intros v abs; apply (H v); right; assumption.
    - intros v; flatten_hyp H; [inv H | rewrite <- IH in H].
      intros [EQ | abs]; [inv EQ; rewrite <- neg_rel_dec_correct in Heq; tauto | apply (H v); assumption]. 
  Qed.

  Lemma alist_In_add_eq : forall m (k:K) (v n:V), alist_In k (alist_add k n m) v -> n = v.
  Proof.
    destruct m as [| [k1 v1]]; intros.
    - unfold alist_add in H.
      unfold alist_In in H. simpl in H.
      destruct (k ?[ eq ] k); inversion H; auto.
    - unfold alist_add in H.
      unfold alist_In in H.
      simpl in H.
      destruct (k ?[ eq ] k). inversion H; auto.
      pose proof (@not_In_remove ((k1,v1)::m)).
      unfold alist_In in H0. simpl in H0.
      apply H0 in H.
      contradiction.
  Qed.

  Lemma alist_find_remove_none:
    forall (m : list (K*V)) (k1 k2 : K), k2 <> k1 -> alist_find k1 (alist_remove k2 m) = None -> alist_find k1 m = None.
  Proof.
    induction m as [| [? ?] m IH]; intros ?k1 ?k2 ineq HF; simpl in *.
    - reflexivity.
    - destruct (rel_dec_p k1 k).
      + subst. eapply rel_dec_neq_false in ineq; eauto. rewrite ineq in HF. simpl in HF.
        assert (k = k) by reflexivity.
        apply rel_dec_correct in H. rewrite H in HF. inversion HF.
      + destruct (rel_dec_p k2 k); simpl in *.
        apply rel_dec_correct in e. rewrite e in HF. simpl in HF.
        eapply rel_dec_neq_false in n; eauto. rewrite n. eapply IH. apply ineq. assumption.
        eapply rel_dec_neq_false in n0; eauto. rewrite n0 in HF. simpl in HF.
        eapply rel_dec_neq_false in n; eauto. rewrite n in *. eapply IH. apply ineq. assumption.
  Qed.
    
  Lemma alist_find_add_none:
    forall m (k r :K) (v:V), 
    alist_find k (alist_add r v m) = None ->
    alist_find k m = None.
  Proof.
    destruct m as [| [k1 v1]]; intros.
    - reflexivity.
    - simpl in *.
      remember (k ?[ eq ] r) as x.
      destruct x.  inversion H.
      remember (r ?[ eq] k1) as y.
      destruct y. simpl in *. symmetry in Heqy. rewrite rel_dec_correct in Heqy. subst.
      rewrite <- Heqx.
      apply (alist_find_remove_none _ k k1); auto.
      rewrite rel_dec_sym in Heqx; eauto.
      apply neg_rel_dec_correct. symmetry in Heqx. assumption.
      simpl in H.
      destruct (k ?[ eq ] k1); auto.
      apply (alist_find_remove_none _ k r); auto.
      rewrite rel_dec_sym in Heqx; eauto.
      apply neg_rel_dec_correct. symmetry in Heqx. assumption.
  Qed.      

  
  Lemma alist_find_neq : forall m (k r:K) (v:V), k <> r -> alist_find k (alist_add r v m) = alist_find k m.
  Proof.
    intros.
    remember (alist_find k (alist_add r v m)) as x.
    destruct x.
    - symmetry in Heqx. apply In_add_In_ineq in Heqx; auto.
    - symmetry in Heqx. symmetry. eapply alist_find_add_none. apply Heqx.
 Qed.
  
  
End alistFacts.
Arguments alist_find {_ _ _ _}.
Arguments alist_add {_ _ _ _}.
Arguments alist_find {_ _ _ _}.
Arguments alist_remove {_ _ _ _}. 
Require Import FunInd Recdef.

Section nat_Show.
  Local Open Scope string.

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
  Proof.
    intros.
    rewrite (NPeano.Nat.div_mod a q); auto.
    rewrite (NPeano.Nat.div_mod b q); auto.
  Qed.

  Lemma get_last_digit_inj: forall n m,
      n <> m ->
      n/10 = m/10 ->
      get_last_digit n <>
      get_last_digit m.
  Proof.
    intros n m ineq eq.
    unfold get_last_digit.
    do 9 (flatten_goal; [repeat flatten_goal; try easy; exfalso; apply ineq,(mod_div_eq n m 10); lia |]).
    subst.
    do 9 (flatten_goal; [easy |]).
    subst.
    exfalso.
    destruct n8.
    2: generalize (NPeano.Nat.mod_upper_bound n 10 (ltac:(auto))); intros EQ; rewrite Heq in EQ; lia. 
    destruct n9.
    2: generalize (NPeano.Nat.mod_upper_bound m 10 (ltac:(auto))); intros EQ; rewrite Heq0 in EQ; lia. 
    exfalso; apply ineq,(mod_div_eq n m 10); lia.
  Qed.

  Lemma append_EmptyString: forall s,
      s ++ "" = s.
  Proof.
    induction s as [| c s IH]; simpl; auto.
    rewrite IH; auto.
  Qed.

  Lemma append_String: forall s c s',
      s ++ String c s' = (s ++ String c "") ++ s'.
  Proof.
    induction s as [| c' s IH]; simpl; intros c s'; auto.
    f_equal.
    apply IH.
  Qed.

  Lemma append_char_simplify_r: forall s s' c,
      s ++ String c "" = s' ++ String c "" ->
      s = s'.
  Proof.
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
  Proof.
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
  Proof.
    induction s1 as [| c s1 IH]; simpl; intros s2 s2' eq; auto.
    inv eq; apply IH; auto.
  Qed.

  Lemma append_assoc: forall s1 s2 s3,
      s1 ++ s2 ++ s3 = (s1 ++ s2) ++ s3.
  Proof.
    induction s1 as [| c s1 IH]; simpl; intros; [reflexivity |].
    rewrite IH; reflexivity.
  Qed.

  Lemma string_of_nat_aux_prepends:
    forall n acc,
    exists hd, hd <> "" /\ string_of_nat_aux acc n = hd ++ acc.
  Proof.
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
  Proof.
    intros n; unfold get_last_digit.
    do 9 (flatten_goal; [reflexivity |]); reflexivity.
  Qed.

  Lemma length_append:
    forall s s', String.length (s ++ s') = String.length s + String.length s'.
  Proof.
    induction s as [| c s IH]; intros s'; simpl; [reflexivity | rewrite IH; reflexivity].
  Qed.

  Lemma length_nonEmpty:
    forall s, s <> "" -> String.length s > 0.
  Proof.
    intros []; [intros abs; easy | intros _; simpl; auto with arith].
  Qed.

  Lemma append_same_length_eq_l:
    forall s1 s1' s2 s2',
      s1 ++ s2 = s1' ++ s2' ->
      String.length s1 = String.length s1' ->
      s1 = s1'.
  Proof.
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
  Proof.
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
  Proof.
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
  Proof.
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
  Proof.
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
  Proof.
    intros n; split; intros H.
    - unfold get_last_digit in H.
      flatten_hyp H; [subst; reflexivity |].
      do 8 (flatten_hyp H; [inv H |]); inv H.
    - unfold get_last_digit; rewrite H; reflexivity.
  Qed.

  Lemma string_of_nat_0_iff:
    forall n, string_of_nat n = "0" <-> n = 0.
  Proof.
    intros n; split; intros H.
    - destruct n as [|n]; [reflexivity | exfalso].
      unfold string_of_nat in H; rewrite string_of_nat_aux_equation in H.
      flatten_hyp H.
      + rewrite append_EmptyString in H.
        rewrite get_last_digit_0_iff in H.
        generalize (Nat.mod_eq (S n) 10 (ltac:(lia))).
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
  Proof.
    intros; intro abs; apply Pos2Nat.inj in abs; easy. 
  Qed.

  Lemma string_of_nat_aux_hd_get_last_digit:
    forall n c s acc, string_of_nat_aux acc n = String c s -> exists n', String c "" = get_last_digit n'.
  Proof.
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
  Proof.
    intros; eapply string_of_nat_aux_hd_get_last_digit; eauto.
  Qed.

  Lemma string_of_Z_inj: forall n m,
      n <> m ->
      string_of_Z n <>
      string_of_Z m.
  Proof.
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

  Fixpoint nat_to_string (n: nat): string :=
    match n with
    | O => ""
    | S n => String (ascii_of_nat 49) (nat_to_string n)
    end.

  Lemma nat_to_string_inj:
    forall (n m: nat), n <> m -> nat_to_string n <> nat_to_string m.
  Proof.
    induction n as [| n IH]; simpl; intros m ineq.
    - destruct m as [| m]; [lia | intros abs; inversion abs].
    - destruct m as [| m]; [intros abs; inversion abs |].
      simpl; intros abs; inversion abs; subst; clear abs.
      apply (IH m); auto.
  Qed.

End nat_Show.

From ExtLib Require Import
     Structures.Monad.
Import MonadNotation.

(* Should go ext-lib *)
Definition traverse_ {A: Type} {M: Type -> Type} `{Monad M} (f: A -> M unit): list A -> M unit :=
  fix traverse__ l: M unit :=
    match l with
    | nil => ret tt
    | a::l => (f a;; traverse__ l)%monad
    end.

