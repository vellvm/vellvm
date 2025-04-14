From Stdlib Require Export
     Morphisms
     Setoid
     Program.Equality
     Lists.List
     Logic.EqdepFacts
     Eqdep EqdepFacts
     Sorting.Sorted
     Sorting.Permutation
     micromega.Lia.

From ITree Require Import
     Basics.HeterogeneousRelations
     Basics.QuantType
     Core.ITreeDefinition
     Eq.Eqit
     Ref.MRecSpec
     Ref.SpecMFacts
     Ref.Automation
     Ref.RecSpecFix
     Ref.RecFixSpecTotal.

     Ref.EnTreeSpecDefinition
     Ref.EnTreeSpecFacts
     Ref.EnTreeSpecCombinatorFacts
     Ref.SpecM


From Coq Require Export Wellfounded Arith.Wf_nat Arith.Compare_dec Arith.Lt.

Import Monad.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope entree_scope.
Variant void : Set := .
Variant errorE := err.
#[global] Instance err_enc : EncodingType errorE := fun _ => void.

Definition subEq {A} (Pre : A -> Prop) : Rel A A := fun a b => a = b /\ Pre a.
Definition subPostRelEq {E} `{EncodingType E} (Post : forall (e : E), encodes e -> Prop) : PostRel E E :=
  fun e1 e2 x y => PostRelEq e1 e2 x y /\ Post e1 x.

Section sortEx.
Context {E : Type} `{enc : EncodingType E}.
Context `{res_err : ReSum errorE E} `{res_ret_err : @ReSumRet errorE E err_enc enc res_err }.

Definition is_nil {A} (l : list A) : entree_spec E bool  :=
  match l with | nil => Ret true | _ => Ret false end.


Instance throw_inst1 : ReSum errorE (SpecEvent E) :=
  fun e => Spec_vis (resum e).

Instance throw_inst2 : ReSumRet errorE (SpecEvent E) :=
  fun e x => res_ret_err e x.

Definition throw {A} : entree_spec E A :=
  v <- trigger err;; match v: void with end.

Definition head {A} (l : list A) : entree_spec E A :=
  match l with
  | nil => throw
  | h :: _ => Ret h end.

Definition tail {A} (l : list A) : entree_spec E (list A) :=
  match l with
  | nil => throw
  | _ :: t => Ret t end.

End sortEx.

#[global] Instance ReSum_inr (E1 E2 E3 : Type) (res : ReSum E2 E3) : ReSum E2 (E1 + E3) :=
  fun e => inr (res e).
Instance ReSumRet_inr (E1 E2 E3 : Type) `{EncodingType E1} `{EncodingType E2}
         `{EncodingType E3}
         (res : ReSum E2 E3) (resret : ReSumRet E2 E3) : 
  ReSumRet E2 (E1 + E3) :=
  fun e x => resret e x.

Definition dec_length {A : Type} (l1 l2 : list A) :=
  length l1 < length l2.

Lemma dec_length_wf A : well_founded (@dec_length A).
Proof.
  eapply well_founded_lt_compat.
  unfold dec_length. eauto.
Qed.

Definition dec_either_length {A} (pr1 pr2 : list A * list A) :=
  length (fst pr1) < length (fst pr2) /\ length (snd pr1) = length (snd pr2) \/
  length (fst pr1) = length (fst pr2) /\ length (snd pr1) < length (snd pr2).

Lemma wf_dec_either_length A : well_founded (@dec_either_length A).
Proof.
  apply wf_union.
  - intros [z1 z2] [y1 y2] [] [x1 x2] []; simpl in *.
    exists (z1, x2); simpl; split; try easy.
    + rewrite <- H0. exact H2.
    + rewrite H1. exact H.
  - eapply wf_incl; [| apply well_founded_ltof ].
    intros ? ? []. exact H.
  - eapply wf_incl; [| apply well_founded_ltof ].
    intros ? ? []. exact H0.
Qed.

Definition rdec_merge {A} (p1 p2 : list A * list A)  :=
  let '(l1,l2) := p1 in
  let '(l3, l4) := p2 in
  length l1 < length l3 /\ 
    length l2 = length l4 \/
  length l1 = length l3 /\ 
    length l2 < length l4.

Lemma rdec_merge_wf A : well_founded (@rdec_merge A).
Proof.
  eapply wf_incl; try apply wf_dec_either_length.
  red. intros [? ?] [? ?] H. auto.
Qed.

Definition sorted : list nat -> Prop :=
  Sorted (Nat.le).

Section halve.
Context {E : Type} `{enc : EncodingType E}.
Context `{res_err : ReSum errorE E} `{res_ret_err : @ReSumRet errorE E err_enc enc res_err }.

Definition halve : list nat -> entree_spec E (list nat * list nat) :=
  rec_fix_spec (fun rec l1 =>
                 b1 <- is_nil l1;;
                 if b1 : bool
                 then Ret (nil, nil)
                 else l2 <- tail l1;;
                      b2 <- is_nil l2;;
                      if b2 : bool
                      then
                        Ret (l1, nil)
                      else
                        x <- head l1;;
                        y <- head l2;;
                        l3 <- tail l2;;
                        '(l4,l5) <- rec l3;;
                        Ret (x::l4, y::l5)).


(* splits a list in half using th monadic, recursion operator rec_fix_spec. 
   The calling the rec function argument corresponds to recursive calls to the halve function *)


Definition halve_pre (l : list nat) := True.
Definition halve_post (l : list nat) p :=
  let '(l1,l2) := p in
  Permutation l (l1 ++ l2) /\
    (length l1 >= length l2 /\ 
       (length l > length l1 \/ 
          1 >= length l)).

Definition halve_post_rel : PostRel (callE (list nat) (list nat * list nat)) (callE (list nat) (list nat * list nat)) :=
  subPostRelEq (fun '(MRecSpec.Call _ _ l) '(l1, l2) => halve_post l (l1,l2)).

Lemma halve_inv_aux:
  forall d1 d2 : callE (list nat) (list nat * list nat),
    d1 = d2 ->
    padded_refines (HeterogeneousRelations.sum_rel eq eq) (SumPostRel halve_post_rel PostRelEq)
                   (halve_post_rel d1 d2)
                   (calling'
                      (fun l1 : list nat =>
                         b1 <- is_nil l1;;
                         (if b1
                          then Ret (nil, nil)
                          else
                            l2 <- tail l1;;
                            b2 <- is_nil l2;;
                            (if b2
                             then Ret (l1, nil)
                             else
                               x <- head l1;;
                               y <- head l2;;
                               l3 <- tail l2;; x0 <- call_spec l3;; (let (l4, l5) := x0 : list nat * list nat in Ret (x :: l4, y :: l5))))) d1)
                   (calling'
                      (fun a : list nat =>
                         _ <- assume_spec (halve_pre a);;
                         n <- exists_spec nat;;
                         _ <-
                           trepeat n
                                   (a' <- exists_spec (list nat);;
                                    _ <- assert_spec (halve_pre a' /\ dec_length a' a);; call_spec a');;
                         b <- exists_spec (list nat * list nat);; _ <- assert_spec (halve_post a b);; ret b) d2).
Proof.
  intros [l1] [l2] Heq. injection Heq. intros. subst. rename l2 into l.
  cbn. destruct l; try destruct l; cbn; repeat rewrite Eqit.bind_ret_l.
  - quantr. intros _. quantr. exists 0. setoid_rewrite Eqit.bind_ret_l.
    quantr. exists (nil, nil). quantr. split. auto. cbn. lia.
    apply padded_refines_ret. split. constructor. split. auto. cbn. lia.
  - cbn. repeat rewrite Eqit.bind_ret_l. quantr. intros _. quantr.
    exists 0. cbn. rewrite Eqit.bind_ret_l. quantr. exists (n :: nil, nil).
    quantr. split. auto. cbn. lia.
    apply padded_refines_ret. split. constructor. split. auto. cbn. lia.
  - cbn. repeat rewrite Eqit.bind_ret_l. quantr.
    intros _. quantr. exists 1. cbn. repeat rewrite Eqit.bind_bind.
    quantr. exists l. rewrite Eqit.bind_bind. quantr. split. constructor.
    red. cbn. lia. eapply padded_refines_bind.
    apply padded_refines_vis. constructor. auto.
    cbn. intros. cbv in a, b. apply padded_refines_ret.
    dependent destruction H. destruct H. dependent destruction H.
    destruct b. Unshelve.
    3 : { exact (fun p1 p2 => p1 = p2 /\ halve_post l p1). }
    cbn. split; auto.
    cbn. intros [l3 l4] [l1 l2] [Heq' HHalve]. injection Heq'. intros. subst.
    rewrite Eqit.bind_ret_l. quantr. exists (n :: l1, n0 :: l2).
    quantr.
    split.
    { cbn. setoid_rewrite Permutation_app_comm. cbn. rewrite Permutation_app_comm.
      destruct HHalve. rewrite H. reflexivity. }
    cbn. destruct HHalve. apply Permutation_length in H. rewrite app_length in H.
    lia. apply padded_refines_ret.
    split. constructor. split. 
    { cbn. setoid_rewrite Permutation_app_comm. cbn. rewrite Permutation_app_comm.
      destruct HHalve. rewrite H. reflexivity. }
    cbn. destruct HHalve. apply Permutation_length in H. rewrite app_length in H.
    lia.
Qed.
Lemma halve_correct l : strict_refines (halve l) (total_spec' halve_pre halve_post l).
Proof.
   rewrite <- total_spec_fix_refines_total_spec' with (Rdec := dec_length).
   2 : apply dec_length_wf.
   eapply padded_refines_interp_mrec_spec with (RPreInv := eq) (RPostInv := halve_post_rel);
     try eapply halve_inv_aux.
   eapply padded_refines_monot; try eapply halve_inv_aux; eauto.
   intros. destruct PR. dependent destruction H. auto.
Qed.
       

End halve.


Section merge.
Context {E : Type} `{enc : EncodingType E}.
Context `{res_err : ReSum errorE E} `{res_ret_err : @ReSumRet errorE E err_enc enc res_err }.

Definition merge : (list nat * list nat) -> entree_spec E (list nat) :=
  rec_fix_spec (fun rec '(l1,l2) => (* ... *)
                  b1 <- is_nil l1;;
                  b2 <- is_nil l2;;
                  if b1 : bool then
                    Ret l2
                  else if b2 : bool then
                    Ret l1
                  else
                    x <- head l1;;
                    tx <- tail l1;;
                    y <- head l2;;
                    ty <- tail l2;;
                    if Nat.leb x y then
                      l <- rec (tx, y::ty);;
                      Ret (x :: l)
                    else
                      l <- rec (x::tx, ty);;
                      Ret (y::l)).

Definition merge_pre p :=
  let '(l1,l2) := p in
  sorted l1 /\ sorted l2.
Definition merge_post '(l1,l2) l :=
  sorted l /\ Permutation l (l1 ++ l2).

Definition merge_pre_call : Rel (callE (list nat * list nat) (list nat)) (callE (list nat * list nat) (list nat)) 
  :=  subEq (fun '(MRecSpec.Call _ _ c) => merge_pre c ).

Definition merge_post_call : PostRel (callE (list nat * list nat) (list nat)) (callE (list nat * list nat) (list nat)) := subPostRelEq (fun '(MRecSpec.Call _ _ c) l => merge_post c l ).

Lemma sorted_fst_and_tail x y xs :
  sorted (x :: y :: xs) -> sorted (x :: xs).
Proof.
  intro; inversion H; subst.
  destruct xs.
  - constructor. constructor. constructor.
  - inversion H3; subst.
    constructor; eauto. inversion H3. subst.
    inversion H2. auto.
    constructor. inversion H2. subst. inversion H6.
    transitivity y; eauto.
Qed.

Lemma sorted_cons_all x xs : sorted xs ->
  (forall x', In x' xs -> x <= x') -> sorted (x :: xs).
Proof.
  destruct xs.
  - constructor; constructor.
  - intros. constructor. auto.
    constructor. apply H0. constructor. auto.
Qed.


Lemma sorted_head x xs :
  sorted (x :: xs) -> (forall x', In x' xs -> x <= x').
Proof.
  revert x; induction xs; intros.
  - contradiction H0.
  - destruct H0; subst.
    + inversion H; subst. inversion H3. subst. eauto.
    + apply IHxs; eauto.
      eapply sorted_fst_and_tail; eauto.
Qed.

Lemma sorted_cons_perm_app x xs y ys xys :
  Permutation xys (xs ++ (y :: ys)) -> sorted xys ->
  x <= y -> sorted (x :: xs) -> sorted (y :: ys) -> sorted (x :: xys).
Proof.
  intros. apply sorted_cons_all; eauto; intros.
  eapply Permutation_in in H4; eauto.
  apply in_app_or in H4; destruct H4.
  - eapply sorted_head in H2; eauto.
  - revert x' H4. eapply sorted_head.
    constructor; eauto.
Qed.


Lemma merge_correct_aux:
  forall d1 d2 : callE (list nat * list nat) (list nat),
    d1 = d2 ->
    padded_refines (HeterogeneousRelations.sum_rel eq eq) (SumPostRel merge_post_call PostRelEq)
                   (merge_post_call d1 d2)
                   (calling'
                      (fun '(l1, l2) =>
                         b1 <- is_nil l1;;
                         b2 <- is_nil l2;;
                         (if b1
                          then Ret l2
                          else
                            if b2
                            then Ret l1
                            else
                              x <- head l1;;
                              tx <- tail l1;;
                              y <- head l2;;
                              ty <- tail l2;;
                              (if x <=? y
                               then l <- call_spec (tx, y :: ty);; Ret (x :: l)
                               else l <- call_spec (x :: tx, ty);; Ret (y :: l)))) d1)
                   (calling'
                      (fun a : list nat * list nat =>
                         _ <- assume_spec (merge_pre a);;
                         n <- exists_spec nat;;
                         _ <-
                           trepeat n
                                   (a' <- exists_spec (list nat * list nat);;
                                    _ <- assert_spec (merge_pre a' /\ rdec_merge a' a);; call_spec a');;
                         b <- exists_spec (list nat);; _ <- assert_spec (merge_post a b);; ret b) d2).
Proof.
  intros [ [l1 l2] ] [[l3 l4]] Heq. injection Heq as Heq. subst.
  cbn. rename l3 into l1. rename l4 into l2. destruct l1; destruct l2; cbn.
  - repeat rewrite Eqit.bind_ret_l. quantr. intros. quantr. exists 0.
    cbn. rewrite Eqit.bind_ret_l. apply padded_refines_exists_specr. 
    exists nil. quantr. split; auto. tauto. apply padded_refines_ret. split. constructor.
    red. split; auto. constructor.
  - repeat rewrite Eqit.bind_ret_l. quantr. intros.
    quantr. exists 0. cbn. rewrite Eqit.bind_ret_l. quantr. exists (n :: l2).
    quantr. destruct H. split; auto. apply padded_refines_ret. split; auto. constructor.
    split; auto. tauto.
  - repeat rewrite Eqit.bind_ret_l. quantr. intros [H1 H2].
    quantr. exists 0. cbn. rewrite Eqit.bind_ret_l. quantr. exists (n :: l1).
    quantr. split; auto. rewrite Permutation_app_comm. reflexivity. apply padded_refines_ret.
    constructor. constructor. split; auto. rewrite Permutation_app_comm. auto.
  - repeat rewrite Eqit.bind_ret_l. rename n0 into m. quantr. intros [Hl1 Hl2].
    quantr. exists 1. cbn. repeat rewrite Eqit.bind_bind.
    destruct (n <=? m) eqn : Hnm.
    + quantr. exists (l1, m :: l2). rewrite Eqit.bind_bind. 
      quantr.
      {
        split. split; auto.  apply Sorted_inv in Hl1. tauto.
        red. cbn. lia.
      }
      eapply padded_refines_bind. apply padded_refines_vis.
      constructor. auto. cbn. intros. 
      apply padded_refines_ret. unfold resum, ReSum_id in H.
      dependent destruction H. red in H. destruct H. dependent destruction H.
      Unshelve. cbv in b.
      3 : { exact (fun x y => x = y /\ merge_post (l1, m :: l2) x). }
      cbn. split; auto.
      intros l3 l4 Hl34. cbn in Hl34. repeat rewrite Eqit.bind_ret_l.
      quantr. exists (n :: l3). decompose record Hl34. subst. quantr. split; auto.
      apply Nat.leb_le in Hnm.
      eapply sorted_cons_perm_app; eauto.
      apply padded_refines_ret. split. constructor. split; auto.
      eapply sorted_cons_perm_app; eauto. apply Nat.leb_le. auto.
      rewrite H2. auto.
   + quantr. exists (n :: l1, l2). rewrite Eqit.bind_bind. 
      quantr.
      {
        split. split; auto.  apply Sorted_inv in Hl2. tauto.
        red. cbn. lia.
      }
      eapply padded_refines_bind. apply padded_refines_vis.
      constructor. auto. cbn. intros. 
      apply padded_refines_ret. unfold resum, ReSum_id in H.
      dependent destruction H. red in H. destruct H. dependent destruction H.
      Unshelve. cbv in b.
      3 : { exact (fun x y => x = y /\ merge_post (n :: l1, l2) x). }
      cbn. split; auto.
      intros l3 l4 Hl34. cbn in Hl34. repeat rewrite Eqit.bind_ret_l.
      quantr. exists (m :: l3). decompose record Hl34. subst. quantr. split; auto.
      {
        eapply sorted_cons_perm_app; try apply Hl1 ; try apply Hl2; auto.
        - rewrite H2. setoid_rewrite Permutation_app_comm. cbn.
          rewrite Permutation_app_comm. reflexivity.
        - apply Compare_dec.leb_iff_conv in Hnm. lia.
      }
      rewrite H2. setoid_rewrite Permutation_app_comm at 2. cbn. rewrite Permutation_app_comm.
      apply perm_swap.
      apply padded_refines_ret. split. constructor. split.
      {
        eapply sorted_cons_perm_app; try apply Hl1 ; try apply Hl2; auto.
        - rewrite H2. setoid_rewrite Permutation_app_comm. cbn.
          rewrite Permutation_app_comm. reflexivity.
        - apply Compare_dec.leb_iff_conv in Hnm. lia.
      }
      rewrite H2. cbn. setoid_rewrite Permutation_app_comm at 2.
      cbn. rewrite Permutation_app_comm. constructor.
Qed.


Lemma merge_correct l1 l2 : strict_refines (merge (l1,l2)) (total_spec' merge_pre merge_post (l1,l2)).
Proof.
  idtac. rewrite <- total_spec_fix_refines_total_spec' with (Rdec := rdec_merge).
  2 : apply rdec_merge_wf.
  eapply padded_refines_interp_mrec_spec with (RPreInv := eq)
                                              (RPostInv := merge_post_call);
    try eapply merge_correct_aux.
  eapply padded_refines_monot; try eapply merge_correct_aux; eauto.
  intros. repeat dependent destruction PR. dependent destruction H. auto.
Qed.


End merge.



Section sort.
Context {E : Type} `{enc : EncodingType E}.
Context `{res_err : ReSum errorE E} `{res_ret_err : @ReSumRet errorE E err_enc enc res_err }.

Definition sort : list nat -> entree_spec E (list nat) :=
  rec_fix_spec ( fun rec l =>
                  b1 <- is_nil l;;
                  if b1 : bool then
                    Ret nil
                  else
                    '(l1, l2) <- halve l;;
                    b2 <- is_nil l2;;
                    if b2 : bool then
                      Ret l1
                    else
                      l1s <- rec l1;;
                      l2s <- rec l2;;
                      merge (l1s, l2s)).


Definition sort_pre (l : list nat) := True.
Definition sort_post (l1 l2 : list nat) :=
  sorted l2 /\
  Permutation l1 l2.

Definition sort_post_rel : PostRel (callE (list nat) (list nat)) (callE (list nat) (list nat)) :=
  subPostRelEq (fun '(MRecSpec.Call _ _ l1) l2 => sort_post l1 l2).

Lemma sorted_length1:
  forall l1 : list nat, length l1 = 1 -> sorted l1.
Proof.
  intros l1. intros. destruct l1. constructor.
  cbn in H. injection H. intros. destruct l1; cbn in *;  try discriminate.
  constructor. auto. constructor.
Qed.

Lemma sort_correct_aux:
  forall l : list nat,
    padded_refines (HeterogeneousRelations.sum_rel eq eq) (SumPostRel sort_post_rel PostRelEq)
                   (sort_post_rel (MRecSpec.Call (list nat) (list nat) l) (MRecSpec.Call (list nat) (list nat) l))
                   (calling'
                      (fun l0 : list nat =>
                         b1 <- is_nil l0;;
                         (if b1
                          then Ret nil
                          else
                            x <- halve l0;;
                            (let (l1, l2) := x in
                             b2 <- is_nil l2;;
                             (if b2 then Ret l1 else l1s <- call_spec l1;; l2s <- call_spec l2;; merge (l1s, l2s)))))
                      (MRecSpec.Call (list nat) (list nat) l))
                   (calling'
                      (fun a : list nat =>
                         _ <- assume_spec (sort_pre a);;
                         n <- exists_spec nat;;
                         _ <-
                           trepeat n
                                   (a' <- exists_spec (list nat);;
                                    _ <- assert_spec (sort_pre a' /\ dec_length a' a);; call_spec a');;
                         b <- exists_spec (list nat);; _ <- assert_spec (sort_post a b);; ret b)
                      (MRecSpec.Call (list nat) (list nat) l)).
Proof.
  intros l. cbn.
  quantr. intros.
    destruct l.
    + cbn. rewrite Eqit.bind_ret_l. quantr. exists 0. cbn. quantr. exists nil.
      quantr. split. constructor. constructor.
      apply padded_refines_ret. constructor. constructor. split; constructor.
    + cbn. rewrite Eqit.bind_ret_l. rewrite halve_correct.
      cbn. rewrite Eqit.bind_bind. quantl. constructor.
      rewrite Eqit.bind_bind. quantl. intros [l1 l2].
      rewrite Eqit.bind_bind. quantl. intros [Hperm Hsize].
      rewrite Eqit.bind_ret_l. destruct l2; cbn.
      * rewrite Eqit.bind_ret_l. quantr. exists 0. cbn. rewrite Eqit.bind_ret_l.
        cbn in Hsize. assert (length l1 = 1).
        { rewrite Permutation_app_comm in Hperm. cbn in Hperm.
          setoid_rewrite <- Hperm in Hsize. rewrite <- Hperm. cbn in *. lia.
        }
        quantr. exists l1.
        quantr.
        split. 
        apply sorted_length1. auto.
        rewrite Hperm. rewrite Permutation_app_comm. cbn. reflexivity.
        apply padded_refines_ret. constructor.
        constructor. split. apply sorted_length1. auto.
        rewrite Hperm. rewrite Permutation_app_comm. auto.
      * rewrite Eqit.bind_ret_l. quantr. exists 2. cbn.
        repeat rewrite Eqit.bind_bind. quantr. exists l1.
        rewrite Eqit.bind_bind. quantr.
        split; auto. red. cbn in Hsize. cbn.
        {
          rewrite Permutation_app_comm in Hperm. cbn in Hperm.
          apply Permutation_length in Hperm. cbn in *.
          rewrite Hperm. rewrite app_length. lia.
        }
        eapply padded_refines_bind.
        eapply padded_refines_vis. constructor. auto.
        intros. apply padded_refines_ret. 
        repeat dependent destruction H0. Unshelve.
        3 : { exact (subEq (sort_post l1)). }
        split; auto.
        intros. destruct H0. subst. rename r2 into l1s.
  
        repeat rewrite Eqit.bind_bind. quantr. exists (n0 :: l2).
        rewrite Eqit.bind_bind. quantr.
        split. constructor.
        {
          red. cbn. cbn in *. rewrite Permutation_app_comm in Hperm. cbn in Hperm.
          apply Permutation_length in Hperm.
          cbn in Hperm. injection Hperm as Hperm. rewrite Hperm. 
          rewrite app_length. lia.
        }
        eapply padded_refines_bind.
        eapply padded_refines_vis. constructor. auto.
        intros. repeat dependent destruction H0. apply padded_refines_ret.
        Unshelve.
        3 : { exact (subEq (sort_post (n0 :: l2))). }
        split; auto.
        intros. destruct H0. subst. rename r2 into l2s.
        rewrite Eqit.bind_ret_l.
        rewrite merge_correct. cbn.
        quantl.
        { destruct H1. destruct H2. auto. }
        quantl. intros ls. quantl. intros [Hsortf Hpermf].
        quantr. exists ls. quantr.
        split. auto.
        rewrite Hpermf. destruct H1. destruct H2.
        rewrite <- H1. rewrite <- H3. auto.
        apply padded_refines_ret. split. constructor.
        split. auto. rewrite Hperm. destruct H1. destruct H2.
        rewrite H1. rewrite H3. symmetry. auto.
Qed.

(*I forgot to include the invariants in the relation *)
Lemma sort_correct l : strict_refines (sort l) (total_spec' sort_pre sort_post l).
Proof.
  rewrite <- total_spec_fix_refines_total_spec' with (Rdec := dec_length).
  2 : apply dec_length_wf. unfold total_spec_fix.
  eapply padded_refines_interp_mrec_spec with (RPreInv := eq) (RPostInv := sort_post_rel).
  - intros [?] [?] ?; subst. injection H. intros. subst. eapply sort_correct_aux.
  - eapply padded_refines_monot; try eapply sort_correct_aux; auto.
    intros. destruct PR. dependent destruction H. auto.
Qed.

End sort.

Variant serverE : Type :=
  | sendE : list nat -> serverE
  | rcvE : serverE.

Instance server_enc : EncodingType serverE :=
  fun e => match e with
        | sendE _ => unit
        | rcvE => list nat end.

Section server.
Context {E : Type} `{enc : EncodingType E}.
Context `{res_err : ReSum errorE E} `{res_ret_err : @ReSumRet errorE E err_enc enc res_err }.
Context `{res_srvr : ReSum serverE E} `{res_ret_srvr : @ ReSumRet serverE E server_enc enc res_srvr}.


Definition server_impl : unit -> entree_spec E void :=
  rec_fix_spec (fun rec _ => 
                  l <- trigger rcvE;;
                  ls <- sort l;;
                  trigger (sendE ls);;
                  rec tt
               ).

Definition server_spec : unit -> entree_spec E void :=
  rec_fix_spec (fun rec _ =>
                  l <- trigger rcvE;;
                  ls <- exists_spec (list nat);;
                  assert_spec (Permutation l ls);;
                  assert_spec (sorted ls);;
                  trigger (sendE ls);;
                  rec tt).



Theorem server_correct : strict_refines (server_impl tt) (server_spec tt).
Proof.
  eapply padded_refines_interp_mrec_spec with (RPreInv := eq) (RPostInv := PostRelEq).
  - intros [[]] [[]] _. cbn. eapply padded_refines_bind with (RR := eq).
    + apply padded_refines_vis. constructor. auto. intros. dependent destruction H.
      dependent destruction H. apply padded_refines_ret. auto.
    + intros l1 l2 H. subst. rewrite sort_correct.
      cbn. rewrite Eqit.bind_bind. quantl. red. auto.
      rewrite Eqit.bind_bind. quantl. intros ls. rewrite Eqit.bind_bind.
      quantl. unfold sort_post. intros [Hsort Hperm]. rewrite Eqit.bind_ret_l.
      quantr. exists ls. quantr. auto. quantr. auto. eapply padded_refines_bind.
      eapply padded_refines_vis. constructor. auto. intros.
      apply padded_refines_ret. dependent destruction H.
      dependent destruction H. reflexivity.
      intros. subst. apply padded_refines_vis. constructor. auto.
      intros. repeat dependent destruction H. apply padded_refines_ret. constructor.
  - cbn. setoid_rewrite sort_correct.
    eapply padded_refines_bind with (RR := eq).
    + apply padded_refines_vis. constructor. auto. intros. dependent destruction H.
      dependent destruction H. apply padded_refines_ret. auto.
    + intros. subst. cbn. rewrite Eqit.bind_bind. quantl. constructor.
      rewrite Eqit.bind_bind. quantl. intros ls. rewrite Eqit.bind_bind.
      quantl. intros [Hsort Hperm]. rewrite Eqit.bind_ret_l.
      quantr. exists ls. quantr. auto. quantr. auto. eapply padded_refines_bind.
      eapply padded_refines_vis. constructor. auto. intros.
      apply padded_refines_ret. dependent destruction H.
      dependent destruction H. reflexivity.
      intros. subst. apply padded_refines_vis. constructor. auto.
      intros. repeat dependent destruction H. apply padded_refines_ret. constructor.
Qed.

End server.

