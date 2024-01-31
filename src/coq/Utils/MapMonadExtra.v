From Coq Require Import
  String
  List
  Morphisms.

Require Import Coq.Logic.ProofIrrelevance.

From ITree Require Import
  Basics.Monad.

From Vellvm Require Import
  Utils.Util
  Utils.ListUtil
  Utils.Error
  Utils.MonadReturnsLaws

  Utils.MonadEq1Laws
  Utils.Tactics.

Require Import Lia.
Require Import FunctionalExtensionality.

Import Monads.

Import MonadNotation.
Import ListNotations.

Open Scope monad.
Open Scope monad_scope.

Definition map_monad2  {M} `{Monad M} `{RAISE_ERROR M} {A B C} (f : A -> B -> M C) : list A -> list B -> M (list C) :=
      fix go l1 l2 :=
        match l1 with
        | [] =>
            match l2 with
            | [] => ret []
            | _ => raise_error "map_monad2: length mismatch"%string
            end
        | x::xs =>
            match l2 with
            | [] => raise_error "map_monad2: length mismatch"%string
            | y::ys =>
                z <- f x y ;;
                zs <- go xs ys ;;
                ret (z::zs)
            end
        end.


Section MonadContext.
  Context (M : Type -> Type).
  Context {HM: Monad M}.
  Context {EQM : Monad.Eq1 M}.
  Context {EE : Eq1Equivalence M}.
  Context {LAWS : @Monad.MonadLawsE M EQM HM}.
  Context {MRET : @MonadReturns M HM EQM}.
  Context {MRETSTR : @MonadReturnsStrongBindInv M HM EQM MRET}.
  Context {EQRET : @Eq1_ret_inv M EQM HM}.
  Context {MRETPROPER : @MonadReturnsProper M HM EQM MRET}.
  Context {MRETPROPERFLIP : @MonadReturns_ProperFlip M HM EQM MRET}.
  Context {BINDRETINV : forall {A B} (m : M A) (k : A -> M B) (v : B)
                          (HRET : EQM _ (a <- m ;; k a) (ret v)),
    exists b, EQM _ (m) (ret b) /\ EQM _ (k b) (ret v)}.

  Existing Instance EQM.
  Existing Instance LAWS.
  Existing Instance MRETPROPER.
  Existing Instance MRETPROPERFLIP.

Lemma map_monad_unfold :
  forall {A B : Type} (x : A) (xs : list A)
    (f : A -> M B),
    map_monad f (x :: xs) =
    b <- f x;;
    bs <- map_monad (fun (x0 : A) => f x0) xs;;
    ret (b :: bs).
Proof using.
  intros A B x xs f.
  induction xs; cbn; auto.
Qed.

Lemma map_monad_length :
  forall {A B}  (xs : list A) (f : A -> M B) res,
    MReturns res (map_monad f xs) ->
    length xs = length res.
Proof using EQM HM LAWS M MRET MRETSTR.
  intros A B xs.
  induction xs; intros f res Hmap.
  - cbn in Hmap.
    apply MReturns_ret_inv in Hmap; subst; auto.
  - rewrite map_monad_unfold in Hmap.
    destruct LAWS.
    destruct MRETSTR.

    pose proof Hmap as RET.
    apply MReturns_strong_bind_inv in RET as (b & Hb & RET).
    apply MReturns_strong_bind_inv in RET as (bs & Hbs & RET).

    apply MReturns_ret_inv in RET.
    subst.

    apply IHxs in Hbs.
    cbn.
    lia.
Qed.

(* TODO: can I generalize this? *)
Lemma map_monad_err_In :
  forall {A B} (f : A -> err B) l res x,
    map_monad f l = ret res ->
    In x res ->
    exists y, f y = ret x /\ In y l.
Proof using.
  intros A B f l res x MAP IN.
  generalize dependent l.
  induction res; intros l MAP.
  - inversion IN.
  - inversion IN; subst.
    + destruct l as [| h ls].
      * cbn in MAP.
        inv MAP.
      * exists h.
        cbn in MAP.
        break_match_hyp; [|break_match_hyp]; inv MAP.
        split; cbn; auto.
    + destruct l as [| h ls].
      * cbn in MAP.
        inv MAP.
      * cbn in MAP.
        break_match_hyp; [|break_match_hyp]; inv MAP.
        epose proof (IHres H ls Heqs0) as [y [HF INy]].
        exists y; split; cbn; eauto.
Qed.

Lemma map_monad_err_In' :
  forall {A B : Type} (f : A -> err B) (l : list A) (res : list B) (y : A),
    In y l ->
    map_monad f l = ret res -> exists x, ret x = f y /\ In x res.
Proof using EQM EQRET HM LAWS M MRET MRETPROPER MRETPROPERFLIP MRETSTR.
  intros A B f l.
  induction l; intros res y IN MAP.
  - inversion IN.
  - inversion IN; subst.
    + cbn in MAP.
      break_match_hyp; inv MAP.
      exists b; split; auto.

      break_match_hyp; inv H0.
      left; auto.
    + cbn in MAP.
      break_match_hyp; inv MAP.
      break_match_hyp; inv H1.

      epose proof (IHl l0 _ H eq_refl) as [b' [RET IN']].
      exists b'; split; firstorder.
Qed.

(* TODO: can I generalize this? *)
Lemma map_monad_err_Nth :
  forall {A B} (f : A -> err B) l res x n,
    map_monad f l = ret res ->
    Util.Nth res n x ->
    exists y, f y = ret x /\ Util.Nth l n y.
Proof using.
  intros A B f l res x n MAP NTH.
  generalize dependent l. generalize dependent n. revert x.
  induction res; intros x n NTH l MAP.
  - inversion NTH.
    rewrite nth_error_nil in *; inv H0.
  - cbn in NTH.
    induction n.
    + cbn in NTH.
      inv NTH.

      destruct l as [| h ls].
      * cbn in MAP.
        inv MAP.
      * exists h.
        cbn in MAP.
        break_match_hyp; [|break_match_hyp]; inv MAP.
        split; cbn; auto.

    + cbn in NTH.
      destruct l as [| h ls].
      * cbn in MAP.
        inv MAP.
      * cbn in MAP.
        break_match_hyp; [|break_match_hyp]; inv MAP.
        epose proof (IHres _ _ NTH ls Heqs0) as [y [HF INy]].
        exists y; split; cbn; eauto.
Qed.

(* TODO: can I generalize this? *)
Lemma map_monad_err_succeeds :
  forall {A B} (f : A -> err B) l,
    (forall a, In a l -> exists b, f a = ret b) ->
    exists res, map_monad f l = ret res.
Proof using.
  intros A B f l IN.
  generalize dependent l.
  induction l; intros IN.
  - exists [].
    reflexivity.
  - cbn.
    forward IHl.
    { intros a0 IN'.
      eapply IN.
      right; auto.
    }

    specialize (IN a).
    forward IN; cbn; auto.
    destruct IN as (b & IN).
    destruct IHl as (res & IHl).

    exists (b :: res).
    rewrite IHl, IN.
    cbn.
    reflexivity.
Qed.

(* TODO: can I generalize this? *)
Lemma map_monad_err_fail :
  forall {A B} (f : A -> err B) l b,
    map_monad f l = inl b ->
    exists a, In a l /\ f a = inl b.
Proof using.
  intros A B f l b MAP.
  generalize dependent b.
  generalize dependent l.
  induction l; intros b MAP.
  - cbn in MAP.
    inv MAP.
  - cbn.
    cbn in MAP.
    destruct (f a) eqn:Hfa; inv MAP.
    + exists a. split; auto.
    + rename H0 into MAP.
      destruct (map_monad f l) eqn:HMAP; inv MAP.
      specialize (IHl b eq_refl) as [a' [IN FA]].
      exists a'. tauto.
Qed.

Lemma map_monad_err_twin_fail :
  forall {s1 s2 : string}
    {X Y Z} {xs : list X} {f : X -> err Y} {g : X -> err Z}
    (MAPM1 : map_monad f xs = inl s1)
    (MAPM2 : map_monad g xs = inl s2)
    (SAME_ERROR : forall x s, f x = inl s <-> g x = inl s),
    s1 = s2.
Proof using.
  intros s1 s2 X Y Z xs.
  induction xs; intros f g MAPM1 MAPM2 SAME_ERROR.
  - cbn in *.
    inv MAPM1.
  - cbn in *.
    break_match_hyp_inv; break_match_hyp_inv.
    + apply SAME_ERROR in Heqs0.
      rewrite Heqs0 in Heqs; inv Heqs; auto.
    + clear H0.
      apply SAME_ERROR in Heqs.
      rewrite Heqs0 in Heqs; inv Heqs; auto.
    + break_match_hyp_inv.
      * apply SAME_ERROR in Heqs1.
        rewrite Heqs1 in Heqs; inv Heqs; auto.
      * break_match_hyp_inv.
        eapply IHxs; eauto.
Qed.

Lemma map_monad_err_twin_fail' :
  forall {s1 s2 : string}
    {X Y Z W} {xs : list X} {ys : list Y} {f : X -> err Z} {g : Y -> err W}
    (MAPM1 : map_monad f xs = inl s1)
    (MAPM2 : map_monad g ys = inl s2)
    (SAME_ERROR : forall n x y s,
        Util.Nth xs n x ->
        Util.Nth ys n y ->
        f x = inl s <-> g y = inl s),
    s1 = s2.
Proof using.
  intros s1 s2 X Y Z W xs ys.
  remember (xs, ys) as ZIP.
  replace xs with (fst ZIP) in * by (subst; auto).
  replace ys with (snd ZIP) in * by (inv HeqZIP; cbn; auto).
  clear xs ys HeqZIP.
  induction ZIP using double_list_rect; intros f g MAPM1 MAPM2 SAME_ERROR;
    try solve
      [ cbn in *;
        solve
          [ inv MAPM1
          | inv MAPM2
          ]
      ].

  cbn in *.
  break_match_hyp_inv; break_match_hyp_inv.
  - specialize (SAME_ERROR 0%nat x y s1 eq_refl eq_refl).
    apply SAME_ERROR in Heqs0.
    rewrite Heqs in Heqs0; inv Heqs0; auto.
  - specialize (SAME_ERROR 0%nat x y s2 eq_refl eq_refl).
    apply SAME_ERROR in Heqs.
    rewrite Heqs in Heqs0; inv Heqs0; auto.
  - break_match_hyp_inv.
    + eapply (SAME_ERROR 0%nat) in Heqs1; cbn; eauto.
      rewrite Heqs in Heqs1; inv Heqs1.
    + break_match_hyp_inv.
      eapply IHZIP; eauto.
      intros n x0 y0 s H H0.
      eapply SAME_ERROR;
        apply nth_error_cons; eauto.
Qed.

Lemma map_monad_map :
  forall A B C
    (f : B -> M C)
    (g : A -> B)
    (xs : list A),
    (map_monad f (map g xs)) ≈ (map_monad (fun x => f (g x)) xs).
Proof using EE EQM HM LAWS M.
  intros. induction xs.
  - simpl. reflexivity.
  - simpl.
    setoid_rewrite IHxs.
    reflexivity.
Qed.

Lemma bind_helper :
  forall A B (m : M A) (f : A -> M B),
    (bind m f) ≈ ((bind (bind m ret) f)).
Proof using EE EQM HM LAWS M.
  intros.
  rewrite bind_ret_r.
  reflexivity.
Qed.

Lemma bind_f_assoc :
  forall A B C (a: A) (f : A -> M B) (g : B -> C),
    eq1 (bind (f a) (fun y => ret (g y)))
        (bind (bind (f a) ret) (fun y => ret (g y))).
Proof using EE EQM HM LAWS M.
  intros. rewrite bind_bind. setoid_rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma map_monad_g :
  forall A B C (f : A -> M B) (g : list B -> C) (xs:list A) (zs : list B)
    (EQ2 : (bind (map_monad f xs) (fun ys => ret ys)) ≈ (ret (zs))),
    (bind (map_monad f xs) (fun ys => ret (g ys))) ≈ (ret (g zs)).
Proof using EE EQM HM LAWS M.
  intros.
  rewrite bind_helper.
  rewrite EQ2.
  rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma map_monad_cons_ret :
  forall A B (f : A -> M B) (a:A) (xs:list A) (z : B) (zs : list B)
    (EQ2 : (bind (map_monad f xs) (fun ys => ret ys)) ≈  (ret (zs))),
    (bind (map_monad f xs) (fun ys => ret (z::ys))) ≈ (ret ((z::zs))).
Proof using EE EQM HM LAWS M.
  intros.
  apply map_monad_g with (g := (fun ys => z::ys)).
  assumption.
Qed.

Lemma map_monad_append_ret :
  forall A B (f : A -> M B) (xs:list A) (ws : list B) (zs : list B)
    (EQ2 : eq1 (bind (map_monad f xs) (fun ys => ret ys))
               (ret (zs))),
    (bind (map_monad f xs) (fun ys => ret (ws ++ ys)%list))
      ≈
      (ret ((ws ++ zs)%list)).
Proof using EE EQM HM LAWS M.
  intros.
  apply map_monad_g with (g := (fun ys => ws ++ ys)).
  assumption.
Qed.

Lemma map_monad_app
      {A B} (f:A -> M B) (l0 l1:list A):
  map_monad f (l0++l1) ≈
  bs1 <- map_monad f l0;;
  bs2 <- map_monad f l1;;
  ret (bs1 ++ bs2).
Proof using EE EQM HM LAWS M.
  induction l0 as [| a l0 IH]; simpl; intros.
  - cbn; rewrite bind_ret_l, bind_ret_r.
    reflexivity.
  - cbn.
    setoid_rewrite IH.
    repeat setoid_rewrite bind_bind.
    setoid_rewrite bind_ret_l.
    reflexivity.
Qed.

(* FIXME TODO: This is poorly named and doesn't make sense as a lemma. *)
Lemma map_monad_In {A B} (l : list A) (f: forall (x : A), In x l -> M B) : M (list B).
Proof using HM M.
  induction l.
  - exact (ret []).
  - refine (b <- f a _;; bs <- IHl _;; ret (b::bs)).
    + cbn; auto.
    + intros x Hin.
      apply (f x).
      cbn; auto.
Defined.

(* FIXME TODO: This is poorly named and doesn't make sense as a lemma. *)
Lemma map_monad_In_unfold :
  forall {A B} (x : A) (xs : list A) (f : forall (elt:A), In elt (x::xs) -> M B),
    map_monad_In (x::xs) f = b <- f x (or_introl eq_refl);;
                            bs <- map_monad_In xs (fun x HIn => f x (or_intror HIn));;
                            ret (b :: bs).
Proof using.
  intros A B x xs f.
  induction xs; cbn; auto.
Qed.

Lemma map_monad_cons
      {A B} (f:A -> M B) (x:A) (l:list A) :
  (map_monad f (x::l)) ≈
  b <- f x;;
  bs2 <- map_monad f l;;
  ret (b :: bs2).
Proof using EE EQM HM M.
  intros. reflexivity.
Qed.

Lemma map_monad_nil
      {A B} (f:A -> M B) :
  (map_monad f []) ≈ ret [].
Proof using EE EQM HM M.
  intros. reflexivity.
Qed.

Lemma map_monad_ret_l : forall {A} (l : list A),
    map_monad ret l ≈ ret l.
Proof using EE EQM HM LAWS M.
  intros. destruct LAWS.
  induction l.
  - apply map_monad_nil.
  - rewrite map_monad_cons.
    rewrite bind_ret_l. rewrite IHl. rewrite bind_ret_l. reflexivity.
Qed.

Lemma id_ret : forall A B (g: A -> B) (x: A),
    id (g x) = g x.
Proof using.
  intros. unfold id. reflexivity. Qed.

Lemma sequence : forall {A} (l : list A),
      sequence (map ret l) ≈ ret l.
Proof using EE EQM HM LAWS M.
  intros. induction l.
  - simpl. reflexivity.
  - rewrite map_cons. simpl. setoid_rewrite map_monad_map. rewrite id_ret.
    rewrite <- map_monad_cons. rewrite map_monad_ret_l. reflexivity.
Qed.

Lemma map_monad_ret_nil_inv_reverse {A B} (f : A -> M B) (l : list A) :
    (l = []) ->
    MReturns [] (map_monad f l).
Proof using EE EQM HM M MRET MRETPROPER MRETPROPERFLIP MRETSTR.
  intros. induction l. unfold map_monad.
  - destruct MRET. apply MReturns_ret. reflexivity.
  - rewrite H. inversion H.
Qed.

Lemma map_monad_ret_nil_inv :
  forall {A B} (f : A -> M B) (l : list A)
  (HRet : MReturns [] (map_monad f l)),
  l = [].
Proof using EQM HM LAWS M MRET MRETSTR.
  intros.
  apply map_monad_length in HRet.
  simpl in HRet.
  assert (H: length l = 0 -> l = []). { intros. induction l. reflexivity. inversion HRet. }
  apply H in HRet. assumption.
Qed.

Lemma map_monad_ret_nil_inv_pure :
  forall {A B} (f : A -> M B) (l : list A)
  (HEq : map_monad f l ≈ ret []),
  l = [].
Proof using EE EQM HM LAWS M MRET MRETPROPER MRETSTR.
  intros.
  apply (map_monad_ret_nil_inv f).
  (* SHOULD BE ABLE TO DO: rewrite HEq at this point -- typeclasses are not set up correctly. *)
  destruct MRETPROPER.
  eapply MReturns_Proper.
  apply HEq.
  apply MReturns_ret. reflexivity.
Qed.

(* what is the difference between this and
map_monad_cons_ret? *)
Lemma map_monad_ret_cons :
  forall {A B} (a : A) (b : B) (f : A -> M B) (l1 : list A) (l2 : list B)
    (H : map_monad f (a :: l1) ≈ ret (b :: l2)),
    map_monad f l1 ≈ ret l2.
Proof using BINDRETINV EQM EQRET HM M.
  intros. simpl in H. apply BINDRETINV in H. repeat destruct H.
  apply BINDRETINV in H0. repeat destruct H0. apply EQRET in H1.
  inversion H1.
  subst. apply H0.
Qed.

Lemma map_monad_head :
  forall {A B} (a : A) (b : B) (f : A -> M B) (l1 : list A) (l2 : list B)
    (H : map_monad f (a :: l1) ≈ ret (b :: l2)),
    f a ≈ ret b.
Proof using BINDRETINV EQM EQRET HM M.
  intros. simpl in H. apply BINDRETINV in H. repeat destruct H.
  apply BINDRETINV in H0. repeat destruct H0. apply EQRET in H1.
  inversion H1.
  subst. apply H.
Qed.

Lemma map_monad_MReturns_cons :
  forall {A B} (a1 a2 : A) (b : B) (f : A -> M B) (l2 : list A) (l1 : list B)
    (H : MReturns (b :: l1) (map_monad f (a2 :: l2))),
    MReturns l1 (map_monad f l2).
Proof using EQM HM M MRET MRETSTR.
  intros.
  destruct MRETSTR. simpl in H. apply MReturns_strong_bind_inv in H.
  repeat destruct H. apply MReturns_strong_bind_inv in H0. repeat destruct H0.
  apply MReturns_ret_inv in H1. inversion H1. subst.
  apply H0.
Qed.


Lemma map_monad_MReturns_head :
  forall {A B} (a : A) (b : B) (f : A -> M B) (l1 : list A) (l2 : list B)
    (H : MReturns (b :: l2) (map_monad f (a :: l1))),
    MReturns b (f a).
Proof using EQM HM M MRET MRETSTR.
  intros.
  destruct MRETSTR. simpl in H. apply MReturns_strong_bind_inv in H.
  repeat destruct H. apply MReturns_strong_bind_inv in H0. repeat destruct H0.
  apply MReturns_ret_inv in H1. inversion H1. subst.
  apply H.
Qed.


Lemma map_monad_In_inv_pure :
  forall {A B} (f : A -> M B) (x : A) (y : B) (l1 : list A) (l2 : list B)
    (HIn: In y l2)
    (HEq: map_monad f l1 ≈ ret l2),
    exists x, In x l1 /\ f x ≈ ret y.
Proof using BINDRETINV EQM EQRET HM M MRET MRETSTR.
  intros. generalize dependent l1.
  destruct MRETSTR.
  induction l2.
  - inversion HIn.
  - intros.
    inversion HIn.
    * subst.
      destruct l1.
    + cbn in HIn. apply eq1_ret_ret in HEq. inversion HEq. auto.
    + apply map_monad_head in HEq. exists a. split. apply in_eq. apply HEq.
    * specialize (IHl2 H). destruct l1.
    + apply eq1_ret_ret in HEq. inversion HEq. auto.
    + specialize (IHl2 l1). apply map_monad_ret_cons in HEq.
      apply IHl2 in HEq. repeat destruct HEq. exists x0. split.
      apply in_cons. apply H0. apply H0.
Qed.

Lemma map_monad_In_inv :
  forall {A B} (f : A -> M B) (x : A) (y : B) (l1 : list A) (l2 : list B)
    (HIn: In y l2)
    (HEq: MReturns l2 (map_monad f l1)),
    exists x, In x l1 /\ (MReturns y (f x)).
Proof using EQM HM M MRET MRETSTR.
  intros. generalize dependent l1.
  destruct MRETSTR.
  induction l2.
  - inversion HIn.
  - intros.
    inversion HIn.
    * destruct l1.
    + apply MReturns_ret_inv in HEq. inversion HEq.
    + assert (HEq' := HEq). apply map_monad_MReturns_cons in HEq.
      apply map_monad_MReturns_head in HEq'. subst. exists a0.
      split. apply in_eq. assumption. assumption.
      * destruct l1.
    + apply MReturns_ret_inv in HEq. inversion HEq.
    + specialize (IHl2 H l1). apply map_monad_MReturns_cons in HEq.
      specialize (IHl2 HEq). repeat destruct IHl2. exists x0.
      split. apply in_cons. apply H0. apply H0. auto.
Qed.

Definition commutative_maps {A} (g f : A -> M A) :=
  forall B a b (k : A -> A -> M B),
    (y <- g a ;; z <- f b ;; k y z) ≈ (z <- f b ;; y <- g a ;; k y z).

Lemma map_comm_lemma : forall {A B} (b : A) (xs : list A) (g : A -> M A) (f : A -> M A) (k : A -> list A -> M B) (HC : commutative_maps g f),
    (bs <- map_monad g xs ;; x <- f b ;; k x bs) ≈
      (x <- f b ;;  bs <- map_monad g xs ;; k x bs).
Proof using EE EQM HM LAWS M.
  destruct LAWS.
  induction xs.
  + intros. simpl. rewrite bind_ret_l.
    setoid_rewrite bind_ret_l. reflexivity.
  + intros. setoid_rewrite map_monad_cons.
    rewrite bind_bind. setoid_rewrite bind_bind.
    setoid_rewrite bind_bind. setoid_rewrite bind_ret_l.
    unfold commutative_maps in HC. rewrite <- HC.
    setoid_rewrite IHxs. reflexivity.
    assumption.
Qed.


Lemma map_monad_commutative_maps :
  forall A (xs : list A) (g : A -> M A) (f : A -> M A)
    (HC : commutative_maps g f),
    (ys <- map_monad g xs ;; map_monad f ys)
      ≈
    map_monad (fun x => y <- (g x) ;; f y) xs.
Proof using EE EQM HM LAWS M.
  intros A xs. induction xs.
  + intros. simpl. rewrite bind_ret_l.
    apply map_monad_nil.
  + intros. rewrite map_monad_cons. rewrite bind_bind.
    setoid_rewrite map_monad_cons.
    rewrite bind_bind.
    setoid_rewrite bind_bind.
    setoid_rewrite bind_ret_l.
    setoid_rewrite map_monad_cons.
    unfold commutative_maps in HC.
    setoid_rewrite map_comm_lemma.
    setoid_rewrite <- IHxs.
    setoid_rewrite bind_bind.
    reflexivity. auto. auto.
Qed.

Lemma foldM_cons :
  forall {A B} (a : A) (b : B) (f : B -> A -> M B) (al : list A),
    foldM f b (a :: al) ≈ b' <- f b a;; foldM f b' al.
Proof using EE EQM HM LAWS M.
  intros.
  induction al.
  destruct LAWS.
  - simpl. rewrite bind_ret_r. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma foldM_app :
  forall {A B} (l1 l2 : list A) (b : B) (f : B -> A -> M B),
    foldM f b (l1 ++ l2) ≈ a1 <- foldM f b l1 ;; foldM f a1 l2.
Proof using EE EQM HM LAWS M.
  intros. generalize dependent b.
  induction l1.
  + intros. simpl. rewrite bind_ret_l. reflexivity.
  + intros. simpl. rewrite bind_bind.
    setoid_rewrite IHl1. reflexivity.
Qed.

Lemma foldM_nil :
  forall {A B} (l1 : list A) (b : B) (f : B -> A -> M B),
    foldM f b [] ≈ ret b.
Proof using EE EQM HM M.
  intros. reflexivity.
Qed.

Lemma cons_app :
  forall {A} (l : list A) (a : A),
    a :: l = [a] ++ l.
Proof using. intros. reflexivity. Qed.

Lemma cons_app_assoc :
  forall A (k y0 : list A) (y : A),
    k ++ y :: y0 = (k ++ [y]) ++ y0.
Proof using. intros. rewrite <- Lists.List.app_assoc. reflexivity. Qed.

Ltac rewrite_under_bind H :=
  repeat (apply Proper_bind; [reflexivity |]; repeat intro); rewrite H.

Lemma foldM_implements_lemma :
  forall {A B} (l : list A) (k : list B) (f : A -> M B),
    l' <- map_monad f l ;; ret (k ++ l') ≈ foldM (fun x y => t <- f y ;; ret (x ++ [t])) k l.
Proof using EE EQM EQRET HM LAWS M.
  intros. generalize dependent k. induction l.
  + simpl. intros. rewrite bind_ret_l. rewrite Lists.List.app_nil_r. reflexivity.
  + simpl. intros. repeat setoid_rewrite bind_bind.
    setoid_rewrite bind_ret_l. setoid_rewrite <- IHl.
    pose proof @cons_app_assoc as Hassoc.
    destruct LAWS. destruct EQRET.
    rewrite_under_bind cons_app_assoc.
    reflexivity.
Qed.

Lemma foldM_implements_map_monad :
  forall {A B} (l : list A) (f : A -> M B),
     map_monad f l ≈ foldM (fun x y => t <- f y ;; ret (x ++ [t])) [] l.
Proof using EE EQM EQRET HM LAWS M.
  intros. rewrite <- foldM_implements_lemma. simpl. rewrite bind_ret_r. reflexivity.
Qed.

Lemma foldM_map :
  forall {A B} (l : list B) (b : B) (f : B -> A -> M B) (g : B -> A),
    foldM f b (map g l) ≈ foldM (fun x y => f x (g y)) b l.
Proof using EE EQM HM LAWS M.
  intros. generalize dependent b. induction l.
  + simpl. reflexivity.
  + simpl. intros. setoid_rewrite IHl. reflexivity.
Qed.

End MonadContext.
Arguments map_monad_In {_ _ _ _}.
Arguments map_monad_In_unfold {_ _ _ _}.
Arguments map_monad_length {_ _ _ _ _ _ _ _}.
Arguments map_monad_app {_ _ _ _ _ _ _}.
Arguments map_monad_err_In' {_ _ _ _ _ _ _ _ _}.
Arguments map_monad_cons_ret {_ _ _ _ _ _ _}.
Arguments map_monad_cons_ret {_ _ _ _ _ _ _}.
Arguments map_monad_map {_ _ _ _ _ _ _ _}.
Arguments map_monad_g {_ _ _ _ _ _ _ _}.

(* TODO: move / generalize these *)
Lemma map_monad_err_nil :
  forall {A B} (f : A -> err B) res,
    map_monad f [] = inr res <-> res = [].
Proof using.
  intros A B f res.
  split; intros MAP.
  - cbn in MAP. inv MAP.
    auto.
  - inv MAP.
    cbn; auto.
Qed.

Lemma map_monad_oom_nil :
  forall {A B} (f : A -> OOM B) res,
    map_monad f [] = NoOom res <-> res = [].
Proof using.
  intros A B f res.
  split; intros MAP.
  - cbn in MAP. inv MAP.
    auto.
  - inv MAP.
    cbn; auto.
Qed.

(* TODO: move / generalize these *)
Lemma map_monad_err_Forall2 :
  forall {A B} (f : A -> err B) l res,
    map_monad f l = inr res <->
      Forall2 (fun a b => f a = inr b) l res.
Proof using.
  intros A B f.
  induction l; intros res.
  - split; intros MAP.
    + cbn in *.
      inv MAP.
      auto.
    + inv MAP.
      reflexivity.
  - split; intros MAP.
    + rewrite map_monad_unfold in MAP.
      cbn in *.
      break_match_hyp; inv MAP.
      break_match_hyp; inv H0.

      pose proof (IHl l0) as FORALL.
      constructor; auto.
      eapply FORALL. reflexivity.
    + inv MAP.
      eapply IHl in H3.
      cbn.
      rewrite H1, H3.
      reflexivity.
Qed.

(* TODO: move / generalize these *)
Lemma map_monad_oom_Forall2 :
  forall {A B} (f : A -> OOM B) l res,
    map_monad f l = NoOom res <->
      Forall2 (fun a b => f a = NoOom b) l res.
Proof using.
  intros A B f.
  induction l; intros res.
  - split; intros MAP.
    + cbn in *.
      inv MAP.
      auto.
    + inv MAP.
      reflexivity.
  - split; intros MAP.
    + rewrite map_monad_unfold in MAP.
      cbn in *.
      break_match_hyp; inv MAP.
      break_match_hyp; inv H0.

      pose proof (IHl l0) as FORALL.
      constructor; auto.
      eapply FORALL. reflexivity.
    + inv MAP.
      eapply IHl in H3.
      cbn.
      rewrite H1, H3.
      reflexivity.
Qed.

Lemma map_monad_eqv :
  forall {M} `{MM: Monad M} {A B C} (f1 : A -> M C) (f2 : B -> M C) l1 l2 res,
    map_monad f1 l1 = res ->
    Forall2 (fun a b => f1 a = f2 b) l1 l2 ->
    map_monad f2 l2 = res.
Proof using.
  intros M MM0 A B C f1 f2 l1 l2 res MAP1 ZIP.
  revert MAP1. revert res.
  induction ZIP; intros res MAP1.
  - cbn in *; auto.
  - cbn in *.
    rewrite <- H.
    erewrite IHZIP; eauto.
Qed.

(* TODO: can I generalize this? *)
Lemma map_monad_OOM_Nth :
  forall {A B} (f : A -> OOM B) l res x n,
    map_monad f l = ret res ->
    Util.Nth res n x ->
    exists y, f y = ret x /\ Util.Nth l n y.
Proof using.
  intros A B f l res x n MAP NTH.
  generalize dependent l. generalize dependent n. revert x.
  induction res; intros x n NTH l MAP.
  - inversion NTH.
    rewrite nth_error_nil in *; inv H0.
  - cbn in NTH.
    induction n.
    + cbn in NTH.
      inv NTH.

      destruct l as [| h ls].
      * cbn in MAP.
        inv MAP.
      * exists h.
        cbn in MAP.
        break_match_hyp; inv MAP.
        break_match_hyp; inv H0.
        split; cbn; auto.

    + cbn in NTH.
      destruct l as [| h ls].
      * cbn in MAP.
        inv MAP.
      * cbn in MAP.
        break_match_hyp; [break_match_hyp|]; inv MAP.
        epose proof (IHres _ _ NTH ls Heqo0) as [y [HF INy]].
        exists y; split; cbn; eauto.
Qed.

(* TODO: can I generalize this? *)
Lemma map_monad_OOM_fail :
  forall {A B} (f : A -> OOM B) l b,
    map_monad f l = Oom b ->
    exists a, In a l /\ f a = Oom b.
Proof using.
  intros A B f l b MAP.
  generalize dependent b.
  generalize dependent l.
  induction l; intros b MAP.
  - cbn in MAP.
    inv MAP.
  - cbn.
    cbn in MAP.
    destruct (f a) eqn:Hfa; inv MAP.
    + rename H0 into MAP.
      destruct (map_monad f l) eqn:HMAP; inv MAP.
      specialize (IHl b eq_refl) as [a' [IN FA]].
      exists a'. tauto.
    + exists a. split; auto.
Qed.

Lemma map_monad_In_cons
  {M} `{MM : Monad M}
  {A B} l (x:A) (f: forall (a : A), In a (x::l) -> M B) :
  (map_monad_In (x::l) f) =
    (b <- f x (or_introl eq_refl);;
     bs2 <- map_monad_In l (fun x HIn => f x (or_intror HIn));;
     ret (b :: bs2)).
Proof using.
  reflexivity.
Qed.

Lemma map_monad_In_OOM_fail :
  forall {A B} l (f : forall (a : A), In a l -> OOM B) b,
    map_monad_In l f = Oom b ->
    exists a (HIn : In a l), f a HIn = Oom b.
Proof using.
  intros A B l f b MAP.
  generalize dependent b.
  generalize dependent l.
  induction l; intros f b MAP.
  - cbn in MAP.
    inv MAP.
  - rewrite map_monad_In_cons in MAP.
    cbn in *.
    destruct (f a (or_introl eq_refl)) eqn:Hfa; inv MAP;
      setoid_rewrite Hfa in H0; inv H0.
    + rename H1 into MAP.
      destruct (map_monad_In l (fun (x : A) (HIn : In x l) => f x (or_intror HIn))) eqn:HMAP; inv MAP.
      specialize (IHl (fun (x : A) (HIn : In x l) => f x (or_intror HIn)) b HMAP) as [a' [IN FA]].
      exists a'. exists (or_intror IN). auto.
    + exists a. exists (or_introl eq_refl). auto.
Qed.

Lemma map_monad_In_OOM_fail' :
  forall {A B} l (f : forall (a : A), In a l -> OOM B),
    (exists a b (HIn : In a l), f a HIn = Oom b) ->
    (exists s, map_monad_In l f = Oom s).
Proof using.
  intros A B l f FAIL.
  generalize dependent l.
  induction l; intros f FAIL.
  - cbn in FAIL.
    destruct FAIL as [_ [_ [CONTRA _]]].
    contradiction.
  - destruct FAIL as [a0 [b [HIn FAIL]]].
    destruct HIn.
    + subst.
      rewrite map_monad_In_cons.
      cbn.
      setoid_rewrite FAIL.
      eauto.
    + rewrite map_monad_In_cons.
      cbn.
      break_match_goal.
      * specialize (IHl (fun (x : A) (HIn : In x l) => f x (or_intror HIn))).
        forward IHl; eauto.
        destruct IHl as [s IHl].
        exists s.
        rewrite IHl.
        auto.
      * exists s; auto.
Qed.

Lemma map_monad_In_oom_forall2 :
  forall {A B} l (f : forall (a : A), In a l -> OOM B) res,
    map_monad_In l f = NoOom res <->
      Forall2_HIn l res (fun a b INA INB => f a INA = NoOom b).
Proof using.
  intros A B.
  induction l; intros f res.
  - split; intros MAP.
    + cbn in *.
      inv MAP.
      auto.
    + cbn in *.
      break_match_hyp; tauto.
  - split; intros MAP.
    + rewrite map_monad_In_unfold in MAP.
      cbn in *.
      break_match_hyp; inv MAP.
      break_match_hyp; inv H0.

      pose proof (IHl (fun (x : A) (HIn : In x l) => f x (or_intror HIn)) l0) as FORALL.
      constructor; auto.
      eapply FORALL. eauto.
    + rewrite map_monad_In_cons.
      cbn in *.
      break_match_hyp; try contradiction.
      cbn in *.
      destruct MAP as [FA MAP].
      rewrite FA.

      pose proof (IHl (fun (x : A) (HIn : In x l) => f x (or_intror HIn)) l0) as FORALL.
      apply FORALL in MAP.
      rewrite MAP.
      auto.
Qed.

Lemma map_monad_In_OOM_succeeds' :
  forall {A B} l (f : forall (a : A), In a l -> OOM B) res,
    map_monad_In l f = ret res ->
    (forall a (HIn : In a l), exists b, f a HIn = ret b).
Proof using.
  intros A B.
  induction l; intros f res MAP.
  - intros _ [].
  - rewrite map_monad_In_cons in MAP.
    cbn in *.
    break_match_hyp; inv MAP.
    rename H0 into MAP.
    break_match_hyp; inv MAP.

    intros a0 [HIn | HIn]; subst.
    + exists b; auto.
    + apply IHl with (a:=a0) (HIn:=HIn) in Heqo0.
      auto.
Qed.

Lemma map_monad_In_OOM_repeat_success :
  forall {A B} sz x (f : forall (a : A), In a (repeat x sz) -> OOM B) res y
    (INx : In x (repeat x sz)),
    map_monad_In (repeat x sz) f = ret res ->
    f x INx = NoOom y ->
    res = repeat y sz.
Proof using.
  intros A B sz.
  induction sz; intros x f res y INx MAP F.
  - inv INx.
  - cbn.
    unfold repeat in MAP.
    rewrite map_monad_In_cons in MAP.
    cbn in MAP.
    assert (INx = or_introl eq_refl) by apply proof_irrelevance.
    subst.
    rewrite F in MAP.
    break_match_hyp; inv MAP.
    specialize (IHsz x).
    destruct sz.
    + cbn in *. inv Heqo.
      reflexivity.
    + eapply IHsz in Heqo.
      rewrite Heqo; eauto.
      erewrite (proof_irrelevance _ (or_introl eq_refl)) in F; eauto.

      Unshelve.
      cbn; auto.
Qed.

Lemma map_monad_In_err_fail :
  forall {A B} l (f : forall (a : A), In a l -> err B) b,
    map_monad_In l f = inl b ->
    exists a (HIn : In a l), f a HIn = inl b.
Proof using.
  intros A B l f b MAP.
  generalize dependent b.
  generalize dependent l.
  induction l; intros f b MAP.
  - cbn in MAP.
    inv MAP.
  - rewrite map_monad_In_cons in MAP.
    cbn in *.
    destruct (f a (or_introl eq_refl)) eqn:Hfa; inv MAP;
      setoid_rewrite Hfa in H0; inv H0.
    + exists a. exists (or_introl eq_refl). auto.
    + rename H1 into MAP.
      destruct (map_monad_In l (fun (x : A) (HIn : In x l) => f x (or_intror HIn))) eqn:HMAP; inv MAP.
      specialize (IHl (fun (x : A) (HIn : In x l) => f x (or_intror HIn)) b HMAP) as [a' [IN FA]].
      exists a'. exists (or_intror IN). auto.
Qed.

Lemma map_monad_In_err_fail' :
  forall {A B} l (f : forall (a : A), In a l -> err B),
    (exists a b (HIn : In a l), f a HIn = inl b) ->
    (exists s, map_monad_In l f = inl s).
Proof using.
  intros A B l f FAIL.
  generalize dependent l.
  induction l; intros f FAIL.
  - cbn in FAIL.
    destruct FAIL as [_ [_ [CONTRA _]]].
    contradiction.
  - destruct FAIL as [a0 [b [HIn FAIL]]].
    destruct HIn.
    + subst.
      rewrite map_monad_In_cons.
      cbn.
      setoid_rewrite FAIL.
      eauto.
    + rewrite map_monad_In_cons.
      cbn.
      break_match_goal.
      * exists s; auto.
      * specialize (IHl (fun (x : A) (HIn : In x l) => f x (or_intror HIn))).
        forward IHl; eauto.
        destruct IHl as [s IHl].
        exists s.
        rewrite IHl.
        auto.
Qed.

Lemma map_monad_In_err_forall2 :
  forall {A B} l (f : forall (a : A), In a l -> err B) res,
    map_monad_In l f = inr res <->
      Forall2_HIn l res (fun a b INA INB => f a INA = inr b).
Proof using.
  intros A B.
  induction l; intros f res.
  - split; intros MAP.
    + cbn in *.
      inv MAP.
      auto.
    + cbn in *.
      break_match_hyp; tauto.
  - split; intros MAP.
    + rewrite map_monad_In_unfold in MAP.
      cbn in *.
      break_match_hyp; inv MAP.
      break_match_hyp; inv H0.

      pose proof (IHl (fun (x : A) (HIn : In x l) => f x (or_intror HIn)) l0) as FORALL.
      constructor; auto.
      eapply FORALL. eauto.
    + rewrite map_monad_In_cons.
      cbn in *.
      break_match_hyp; try contradiction.
      cbn in *.
      destruct MAP as [FA MAP].
      rewrite FA.

      pose proof (IHl (fun (x : A) (HIn : In x l) => f x (or_intror HIn)) l0) as FORALL.
      apply FORALL in MAP.
      rewrite MAP.
      auto.
Qed.

Lemma map_monad_In_err_succeeds' :
  forall {A B} l (f : forall (a : A), In a l -> err B) res,
    map_monad_In l f = ret res ->
    (forall a (HIn : In a l), exists b, f a HIn = ret b).
Proof using.
  intros A B.
  induction l; intros f res MAP.
  - intros _ [].
  - rewrite map_monad_In_cons in MAP.
    cbn in *.
    break_match_hyp; inv MAP.
    rename H0 into MAP.
    break_match_hyp; inv MAP.

    intros a0 [HIn | HIn]; subst.
    + exists b; auto.
    + apply IHl with (a:=a0) (HIn:=HIn) in Heqs0.
      auto.
Qed.

Lemma map_monad_In_map :
  forall {M : Type -> Type} {HM : Monad M} {EQM : Monad.Eq1 M},
    Monad.Eq1Equivalence M ->
    Monad.MonadLawsE M ->
    forall (A B C : Type) (xs : list A) (g : A -> B) (f : forall (b : B) (HIn : In b (map g xs)), M C),
      Monad.eq1 (map_monad_In (map g xs) f) (map_monad_In xs (fun (x : A) IN => f (g x) (in_map g xs x IN))).
Proof using.
  intros. induction xs.
  - simpl. reflexivity.
  - simpl.
    setoid_rewrite IHxs.
    cbn.
    assert (f (g a) (or_introl eq_refl) = f (g a) (in_map g (a :: xs) a (or_introl eq_refl))).
    { apply f_equal.
      apply proof_irrelevance.
    }
Abort.

Lemma map_monad_map_monad_In :
  forall {M A B} `{HM : Monad M} xs (f : A -> M B),
    map_monad f xs = map_monad_In xs (fun x _ => f x).
Proof using.
  intros M A B HM xs.
  induction xs; intros f.
  - cbn. reflexivity.
  - rewrite map_monad_unfold, map_monad_In_cons.
    rewrite IHxs.
    reflexivity.
Qed.

Lemma map_monad_map_err :
  forall (A B C : Type) (xs : list A) (g : A -> B) (f : B -> err C),
    map_monad f (map g xs) = map_monad (fun (x : A) => f (g x)) xs.
Proof using.
  intros. induction xs.
  - simpl. reflexivity.
  - simpl.
    break_match; auto.
    setoid_rewrite IHxs.
    reflexivity.
Qed.

Lemma map_monad_map_oom :
  forall (A B C : Type) (xs : list A) (g : A -> B) (f : B -> OOM C),
    map_monad f (map g xs) = map_monad (fun (x : A) => f (g x)) xs.
Proof using.
  intros. induction xs.
  - simpl. reflexivity.
  - simpl.
    break_match; auto.
    setoid_rewrite IHxs.
    reflexivity.
Qed.

Lemma map_monad_In_OOM_nil_inv :
  forall {A B : Type} (l : list A) (f : forall a : A, In a l -> OOM B),
    map_monad_In l f = ret [] -> l = [].
Proof using.
  intros A B l f H.
  induction l; auto.

  rewrite map_monad_In_cons in H.
  cbn in H.
  break_match_hyp; inv H.
  break_match_hyp; inv H1.
Qed.

Lemma map_monad_In_OOM_cons_inv :
  forall {A B : Type} (l : list A) (f : forall a : A, In a l -> OOM B) r res,
    map_monad_In l f = ret (r :: res) ->
    exists x xs HInx (EQ : l = x :: xs),
      f x HInx = ret r /\
        map_monad_In xs (fun a HIn => f a (In_cons_right EQ HIn)) = ret res.
Proof using.
  intros A B l.
  induction l; intros f r res H.
  - cbn in *.
    inv H.
  - rewrite map_monad_In_cons in H.
    cbn in H.
    break_match_hyp; inv H.
    break_match_hyp; inv H1.
    exists a.
    exists l.
    exists (or_introl eq_refl).
    exists eq_refl.
    split; auto.
    cbn.

    assert ((fun (x : A) (HIn : In x l) => f x (or_intror HIn)) =
              (fun (a0 : A) (HIn : In a0 l) => f a0 (In_cons_right eq_refl HIn))).
    { eapply functional_extensionality_dep.
      intros x.
      eapply functional_extensionality_dep.
      intros x0.
      assert (or_intror x0 = @In_cons_right A (a :: l) x a l (@eq_refl (list A) (a :: l)) x0) as PROOFS.
      { apply proof_irrelevance.
      }

      rewrite PROOFS.
      reflexivity.
    }
    rewrite <- H.
    auto.
Qed.


Lemma map_monad_err_forall2_HIn:
  forall {A B : Type} (f : A -> err B) (l : list A) (res : list B),
    map_monad f l = inr res <->
      Forall2_HIn l res (fun (a : A) (b : B) (INA : In a l) (INB : In b res) => f a = inr b).
Proof using.
Admitted.

Lemma map_monad_err_length :
  forall {A B} l (f : A -> err B) res,
    map_monad f l = inr res ->
    length l = length res.
Proof using.
  intros A B l.
  induction l; intros f res H.
  - rewrite map_monad_err_nil in H; subst; auto.
  - rewrite map_monad_unfold in H.
    cbn in *.
    break_match_hyp; inv H.
    break_match_hyp; inv H1.
    apply IHl in Heqs0.
    cbn.
    auto.
Qed.

Lemma map_monad_oom_length :
  forall {A B} l (f : A -> OOM B) res,
    map_monad f l = NoOom res ->
    length l = length res.
Proof using.
  intros A B l.
  induction l; intros f res H.
  - rewrite map_monad_oom_nil in H; subst; auto.
  - rewrite map_monad_unfold in H.
    cbn in *.
    break_match_hyp; inv H.
    break_match_hyp; inv H1.
    apply IHl in Heqo0.
    cbn.
    auto.
Qed.

Lemma map_monad_err_nil_inv :
  forall {A B} (f : A -> err B) l,
    map_monad f l = inr [] ->
    l = [].
Proof using.
  intros A B f l H.
  induction l; cbn; auto.
  cbn in H.
  break_match_hyp; inv H.
  break_match_hyp; inv H1.
Qed.

Lemma map_monad_err_cons :
  forall {A B} (f : A -> err B) x xs res,
    map_monad f (x :: xs) = inr res ->
    exists b bs, res = b :: bs.
Proof using.
  intros A B f x xs res H.
  cbn in H.
  break_match_hyp; inv H.
  break_match_hyp; inv H1.
  exists b. exists l.
  reflexivity.
Qed.

Lemma map_monad_err_cons_inv :
  forall {A B} (f : A -> err B) b bs l,
    map_monad f l = inr (b :: bs) ->
    exists x xs, l = x :: xs.
Proof using.
  intros A B f b bs l H.
  induction l; cbn in *.
  - inv H.
  - break_match_hyp; inv H.
    break_match_hyp; inv H1.
    exists a. exists l.
    reflexivity.
Qed.

(* TODO: can I generalize this? *)
Lemma map_monad_oom_succeeds :
  forall {A B} (f : A -> OOM B) l,
    (forall a, In a l -> exists b, f a = ret b) ->
    exists res, map_monad f l = ret res.
Proof using.
  intros A B f l IN.
  generalize dependent l.
  induction l; intros IN.
  - exists [].
    reflexivity.
  - cbn.
    forward IHl.
    { intros a0 IN'.
      eapply IN.
      right; auto.
    }

    specialize (IN a).
    forward IN; cbn; auto.
    destruct IN as (b & IN).
    destruct IHl as (res & IHl).

    exists (b :: res).
    rewrite IHl, IN.
    cbn.
    reflexivity.
Qed.

Lemma map_monad_oom_In :
  forall {A B : Type} (f : A -> OOM B) (l : list A) (res : list B),
    map_monad f l = ret res -> forall (x : B),
    In x res -> exists y : A, f y = ret x /\ In y l.
Proof using.
  intros A B f l res HMAPM x IN.
  pose proof In_Nth _ _ IN as (n&NTH).
  pose proof map_monad_OOM_Nth _ _ _ _ _ HMAPM NTH as (y&FY&NTHy).
  exists y.
  split; auto.
  eapply Util.Nth_In; eauto.
Qed.

Lemma map_monad_InT {M : Type -> Type} `{HM : Monad M} {A B} (l : list A) (f: forall (x : A), InT x l -> M B) : M (list B).
Proof using.
  induction l.
  - exact (ret []).
  - refine (b <- f a _;; bs <- IHl _;; ret (b::bs)).
    + cbn; auto.
    + intros x Hin.
      apply (f x).
      cbn; auto.
Defined.

Lemma map_monad_InT_unfold :
  forall {M} `{HM : Monad M} {A B} (x : A) (xs : list A) (f : forall (elt:A), InT elt (x::xs) -> M B),
    map_monad_InT (x::xs) f = b <- f x (inl eq_refl);;
                             bs <- map_monad_InT xs (fun x HIn => f x (inr HIn));;
                             ret (b :: bs).
Proof using.
  intros M HM A B x xs f.
  induction xs; cbn; auto.
Qed.

Lemma map_monad_InT_cons
  {M} `{MM : Monad M}
  {A B} l (x:A) (f: forall (a : A), InT a (x::l) -> M B) :
  (map_monad_InT (x::l) f) =
    (b <- f x (inl eq_refl);;
     bs2 <- map_monad_InT l (fun x HIn => f x (inr HIn));;
     ret (b :: bs2)).
Proof using.
  reflexivity.
Qed.

Lemma map_monad_map_monad_InT :
  forall {M} {A B} `{HM : Monad M} xs (f : A -> M B),
    @map_monad M HM A B f xs = @map_monad_InT M HM A B xs (fun x HIn => f x).
Proof using.
  intros M A B HM xs.
  induction xs; intros f.
  - cbn. reflexivity.
  - rewrite map_monad_unfold, map_monad_InT_cons.
    rewrite IHxs.
    reflexivity.
Qed.


Lemma map_monad_InT_OOM_fail :
  forall {A B} l (f : forall (a : A), InT a l -> OOM B) b,
    map_monad_InT l f = Oom b ->
    exists a (HIn : InT a l), f a HIn = Oom b.
Proof using.
  intros A B l f b MAP.
  generalize dependent b.
  generalize dependent l.
  induction l; intros f b MAP.
  - cbn in MAP.
    inv MAP.
  - rewrite map_monad_InT_cons in MAP.
    cbn in *.
    destruct (f a (inl eq_refl)) eqn:Hfa; inv MAP;
      setoid_rewrite Hfa in H0; inv H0.
    + rename H1 into MAP.
      destruct (map_monad_InT l (fun (x : A) (HIn : InT x l) => f x (inr HIn))) eqn:HMAP; inv MAP.
      specialize (IHl (fun (x : A) (HIn : InT x l) => f x (inr HIn)) b HMAP) as [a' [IN FA]].
      exists a'. exists (inr IN). auto.
    + exists a. exists (inl eq_refl). auto.
Qed.

Lemma map_monad_InT_OOM_failT :
  forall {A B} l (f : forall (a : A), InT a l -> OOM B) b,
    map_monad_InT l f = Oom b ->
    {a & {HIn : InT a l & f a HIn = Oom b}}.
Proof using.
  intros A B l f b MAP.
  generalize dependent b.
  generalize dependent l.
  induction l; intros f b MAP.
  - cbn in MAP.
    inv MAP.
  - rewrite map_monad_InT_cons in MAP.
    cbn in *.
    destruct (f a (inl eq_refl)) eqn:Hfa; inv MAP;
      setoid_rewrite Hfa in H0; inv H0.
    + rename H1 into MAP.
      destruct (map_monad_InT l (fun (x : A) (HIn : InT x l) => f x (inr HIn))) eqn:HMAP; inv MAP.
      specialize (IHl (fun (x : A) (HIn : InT x l) => f x (inr HIn)) b HMAP) as [a' [IN FA]].
      exists a'. exists (inr IN). auto.
    + exists a. exists (inl eq_refl). auto.
Qed.

Lemma map_monad_InT_OOM_succeeds' :
  forall {A B} l (f : forall (a : A), InT a l -> OOM B) res,
    map_monad_InT l f = ret res ->
    (forall a (HIn : InT a l), exists b, f a HIn = ret b).
Proof using.
  intros A B.
  induction l; intros f res MAP.
  - intros _ [].
  - rewrite map_monad_InT_cons in MAP.
    cbn in *.
    break_match_hyp; inv MAP.
    rename H0 into MAP.
    break_match_hyp; inv MAP.

    intros a0 [HIn | HIn]; subst.
    + exists b; auto.
    + apply IHl with (a:=a0) (HIn:=HIn) in Heqo0.
      auto.
Qed.

Lemma map_monad_InT_OOM_repeat_success :
  forall {A B} sz x (f : forall (a : A), InT a (repeat x sz) -> OOM B) res y,
    map_monad_InT (repeat x sz) f = ret res ->
    (forall INx : InT x (repeat x sz), f x INx = NoOom y) ->
    res = repeat y sz.
Proof using.
  intros A B sz.
  induction sz; intros x f res y MAP F.
  - cbn in *.
    inv MAP.
    reflexivity.
  - cbn.
    unfold repeat in MAP.
    rewrite map_monad_InT_cons in MAP.
    cbn in MAP.
    cbn in *.
    break_match_hyp; inv MAP.
    break_match_hyp; inv H0.

    pose proof (F (inl eq_refl)).
    setoid_rewrite Heqo in H.
    inv H.

    cbn.
    erewrite <- IHsz; eauto.

    intros INx.
    cbn.
    eauto.
Qed.

Lemma map_monad_InT_OOM_nil_inv :
  forall {A B : Type} (l : list A) (f : forall a : A, InT a l -> OOM B),
    map_monad_InT l f = ret [] -> l = [].
Proof using.
  intros A B l f H.
  induction l; auto.

  rewrite map_monad_InT_cons in H.
  cbn in H.
  break_match_hyp; inv H.
  break_match_hyp; inv H1.
Qed.

Lemma map_monad_err_InT :
  forall {A B} (f : A -> err B) l res x,
    map_monad f l = ret res ->
    InT x res ->
    {y & ((f y = ret x) * (InT y l))%type}.
Proof using.
  intros A B f l res x MAP IN.
  generalize dependent l.
  induction res; intros l MAP.
  - inversion IN.
  - inversion IN; subst.
    + destruct l as [| h ls].
      * cbn in MAP.
        inv MAP.
      * exists h.
        cbn in MAP.
        break_match_hyp; [|break_match_hyp]; inv MAP.
        split; cbn; auto.
    + destruct l as [| h ls].
      * cbn in MAP.
        inv MAP.
      * cbn in MAP.
        break_match_hyp; [|break_match_hyp]; inv MAP.
        epose proof (IHres X ls Heqs0) as [y [HF INy]].
        exists y; split; cbn; eauto.
Qed.

Lemma map_monad_InT_OOM_Nth :
  forall {A B : Type}
    (l : list A)
    (f : forall (a : A), InT a l -> OOM B)
    (res : list B) (x : B)
    (n : nat),
    map_monad_InT l f = ret res ->
    Util.Nth res n x ->
    exists (y : A) (HIN: InT y l), f y HIN = ret x /\ Util.Nth l n y.
Proof using.
  intros A B l f res x n MAP NTH.
  generalize dependent l. generalize dependent n. revert x.
  induction res; intros x n NTH l f MAP.
  - inversion NTH.
    rewrite nth_error_nil in *; inv H0.
  - cbn in NTH.
    induction n.
    + cbn in NTH.
      inv NTH.

      destruct l as [| h ls].
      * cbn in MAP.
        inv MAP.
      * exists h.
        exists (inl eq_refl).
        cbn in MAP.
        break_match_hyp; inv MAP.
        break_match_hyp; inv H0.
        split; cbn; auto.
    + cbn in NTH.
      destruct l as [| h ls].
      * cbn in MAP.
        inv MAP.
      * rewrite map_monad_InT_unfold in MAP.
        cbn in MAP.
        break_match_hyp; inv MAP.
        break_match_hyp; inv H0.
        epose proof (IHres _ _ NTH ls _ Heqo0) as [y [IN [HF INy]]].
        exists y; exists (inr IN); split; cbn; eauto.
Qed.

Lemma map_monad_InT_OOM_Nth' :
  forall {A B : Type}
    (l : list A)
    (f : forall (a : A), InT a l -> OOM B)
    (res : list B) (x : A)
    (n : nat),
    map_monad_InT l f = ret res ->
    Util.Nth l n x ->
    exists (y : B) (HIN : InT x l), f x HIN = ret y /\ Util.Nth res n y.
Proof using.
  intros A B l f res x n MAP NTH.
  generalize dependent res. generalize dependent n. revert x.
  induction l; intros x n NTH res MAP.
  - cbn in *.
    rewrite Util.nth_error_nil in NTH; discriminate.
  - cbn in NTH.
    induction n.
    + cbn in NTH.
      inv NTH.

      destruct res.
      * cbn in *.
        repeat break_match_hyp_inv.
      * rewrite map_monad_InT_unfold in MAP.
        cbn in *.
        repeat break_match_hyp_inv.
        exists b. exists (inl eq_refl).
        split; auto.
    + cbn in NTH.
      destruct res.
      * cbn in MAP.
        repeat break_match_hyp_inv.
      * rewrite map_monad_InT_unfold in MAP.
        cbn in MAP.
        repeat break_match_hyp_inv.
        epose proof (IHl _ _ _ NTH res Heqo0) as [y [IN [HF INy]]].
        exists y; exists (inr IN); split; cbn; eauto.
Qed.

Lemma map_monad_InT_oom_In :
  forall {A B : Type}
    (l : list A)
    (f : forall (a : A), InT a l -> OOM B)
    (res : list B) (x : B),
    map_monad_InT l f = ret res ->
    In x res -> exists (y : A) (HIN : InT y l), f y HIN = ret x.
Proof using.
  intros A B f l res x HMAPM IN.
  pose proof In_Nth _ _ IN as (n&NTH).
  pose proof map_monad_InT_OOM_Nth _ _ _ _ _ HMAPM NTH as (y&IN'&FY&NTHy).
  exists y.
  exists IN'.
  auto.
Qed.

Lemma InT_cons_right :
  forall {A} {l : list A} {a x xs}
    (EQ : l = x :: xs) (HIn : InT a xs),
    InT a l.
Proof using.
  intros A l x xs EQ a HIn.
  subst.
  cbn.
  right.
  auto.
Defined.

Lemma InT_map_impl : forall {X Y} (f : X -> Y) l {y : Y},
    InT y (map f l) -> {x & ((f x = y) * (InT x l))%type}.
Proof using.
  intros X Y f l.
  induction l; firstorder (subst; auto).
Qed.

Lemma InT_map_flip : forall {X Y} (f : X -> Y) l {y : Y},
    {x & ((f x = y) * (InT x l))%type} -> InT y (map f l).
Proof using.
  intros X Y f l.
  induction l; firstorder (subst; auto).
Qed.

Require Import FunctionalExtensionality.
Lemma map_monad_InT_OOM_cons_inv :
  forall {A B : Type} (l : list A) (f : forall a : A, InT a l -> OOM B) r res,
    map_monad_InT l f = ret (r :: res) ->
    exists x xs HInx (EQ : l = x :: xs),
      f x HInx = ret r /\
        map_monad_InT xs (fun a HIn => f a (InT_cons_right EQ HIn)) = ret res.
Proof using.
  intros A B l.
  induction l; intros f r res H.
  - cbn in *.
    inv H.
  - rewrite map_monad_InT_cons in H.
    cbn in H.
    break_match_hyp; inv H.
    break_match_hyp; inv H1.
    exists a.
    exists l.
    exists (inl eq_refl).
    exists eq_refl.
    split; auto.
Qed.

Lemma InT_Nth :
  forall {X} xs (x : X),
    InT x xs -> exists i, Util.Nth xs i x.
Proof using.
  induction xs; intros x IN.
  - inversion IN.
  - destruct IN; subst.
    + exists (0%nat). cbn. auto.
    + apply IHxs in i as [i H].
      exists (S i).
      cbn; auto.
Qed.
