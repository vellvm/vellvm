From Coq Require Import
     List
     Morphisms.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.EitherMonad
     Data.Monads.IdentityMonad.

From ITree Require Import
     Basics.Monad.

From Vellvm Require Import
     Utils.Util
     Utils.Error
     Utils.MonadReturnsLaws
     
     Utils.MonadEq1Laws
     Utils.Tactics.

Require Import Lia.

Import Monads.

Import MonadNotation.
Import ListNotations.

Open Scope monad.
Open Scope monad_scope.

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
Proof.
  intros A B x xs f.
  induction xs; cbn; auto.
Qed.

  
Lemma map_monad_length :
  forall {A B}  (xs : list A) (f : A -> M B) res,
    MReturns res (map_monad f xs) ->
    length xs = length res.
Proof.
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
Proof.
  intros A B f l res x MAP IN.
  generalize dependent l.
  induction res; intros l MAP.
  - inversion IN.
  - inversion IN; subst.
    + destruct l as [_ | h ls].
      * cbn in MAP.
        inv MAP.
      * exists h.
        cbn in MAP.
        break_match_hyp; [|break_match_hyp]; inv MAP.
        split; cbn; auto.
    + destruct l as [_ | h ls].
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
Proof.
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
Proof.
  intros A B f l res x n MAP NTH.
  generalize dependent l. generalize dependent n. revert x.
  induction res; intros x n NTH l MAP.
  - inversion NTH.
    rewrite nth_error_nil in *; inv H0.
  - cbn in NTH.
    induction n.
    + cbn in NTH.
      inv NTH.

      destruct l as [_ | h ls].
      * cbn in MAP.
        inv MAP.
      * exists h.
        cbn in MAP.
        break_match_hyp; [|break_match_hyp]; inv MAP.
        split; cbn; auto.

    + cbn in NTH.
      destruct l as [_ | h ls].
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
Proof.
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

Lemma map_monad_map :
  forall A B C 
    (f : B -> M C)
    (g : A -> B)
    (xs : list A),
    (map_monad f (map g xs)) ≈ (map_monad (fun x => f ( g x) ) xs).
Proof.
  intros. induction xs.
  - simpl. reflexivity.
  - simpl. 
    setoid_rewrite IHxs.
    reflexivity.
Qed.


Lemma bind_helper :
  forall A B (m : M A) (f : A -> M B), 
    (bind m f) ≈ ((bind (bind m ret) f)).
Proof.
  intros.
  rewrite bind_ret_r.
  reflexivity.
Qed.



Lemma bind_f_assoc :
  forall A B C (a: A) (f : A -> M B) (g : B -> C),
    eq1 (bind (f a) (fun y => ret (g y)))
        (bind (bind (f a) ret) (fun y => ret (g y))).
Proof.
  intros. rewrite bind_bind. setoid_rewrite bind_ret_l.
  reflexivity.
Qed.



(* more general form of the two above; do we need those two? *) 
Lemma map_monad_g :
  forall A B C (f : A -> M B) (g : list B -> C) (xs:list A) (zs : list B)
    (EQ2 : (bind (map_monad f xs) (fun ys => ret ys)) ≈ (ret (zs))),
    (bind (map_monad f xs) (fun ys => ret (g ys))) ≈ (ret (g zs)).
Proof.
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
Proof.
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
Proof.
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
Proof.
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
Proof.
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
Proof.
  intros A B x xs f.
  induction xs; cbn; auto.
Qed.

Lemma map_monad_cons
      {A B} (f:A -> M B) (x:A) (l:list A) :
  (map_monad f (x::l)) ≈
  b <- f x;;
  bs2 <- map_monad f l;;
  ret (b :: bs2).
Proof.
  intros. reflexivity. Qed. 

Lemma map_monad_nil 
      {A B} (f:A -> M B) :
  (map_monad f []) ≈ ret [].
Proof.
  intros. reflexivity. Qed.

Lemma map_monad_ret_l : forall {A} (l : list A),
    map_monad ret l ≈ ret l.
Proof.
  intros. destruct LAWS.
  induction l.
  - apply map_monad_nil.
  - rewrite map_monad_cons.
    rewrite bind_ret_l. rewrite IHl. rewrite bind_ret_l. reflexivity. Qed.

Lemma id_ret : forall A B (g: A -> B) (x: A),
    id (g x) = g x.
Proof.
  intros. unfold id. reflexivity. Qed.
  
Lemma sequence : forall {A} (l : list A),
      sequence (map ret l) ≈ ret l.
Proof. intros. induction l.
       - simpl. reflexivity. 
       - rewrite map_cons. simpl. setoid_rewrite map_monad_map. rewrite id_ret.
         rewrite <- map_monad_cons. rewrite map_monad_ret_l. reflexivity. Qed.


Lemma map_monad_ret_nil_inv_reverse {A B} (f : A -> M B) (l : list A) :  
    (l = []) -> 
    MReturns [] (map_monad f l).
Proof.
  intros. induction l. unfold map_monad.
  - destruct MRET. apply MReturns_ret. reflexivity.
  - rewrite H. inversion H. 
Qed. 
     
  
Lemma map_monad_ret_nil_inv :
  forall {A B} (f : A -> M B) (l : list A)
  (HRet : MReturns [] (map_monad f l)),
  l = [].
Proof.
  intros. 
  apply map_monad_length in HRet.
  simpl in HRet. 
  assert (H: length l = 0 -> l = []). { intros. induction l. reflexivity. inversion HRet.}
  apply H in HRet. assumption.
Qed.

Lemma map_monad_ret_nil_inv_pure :
  forall {A B} (f : A -> M B) (l : list A)
  (HEq : map_monad f l ≈ ret []),
  l = [].
Proof.
  intros.
  apply (map_monad_ret_nil_inv f).
  (* SHOULD BE ABLE TO DO: rewrite HEq at this point -- typeclasses are not set up correctly. *)
  destruct MRETPROPER.
  eapply MReturns_Proper.
  apply HEq.
  apply MReturns_ret. reflexivity.
Qed.


Lemma map_monad_ret_cons :
  forall {A B} (a : A) (b : B) (f : A -> M B) (l1 : list A) (l2 : list B)
    (H : map_monad f (a :: l1) ≈ ret (b :: l2)),
    map_monad f l1 ≈ ret l2.
Proof.
  intros. simpl in H. apply BINDRETINV in H. repeat destruct H.
  apply BINDRETINV in H0. repeat destruct H0. apply EQRET in H1.
  inversion H1.
  subst. apply H0.
  Qed. 

Lemma map_monad_head :
  forall {A B} (a : A) (b : B) (f : A -> M B) (l1 : list A) (l2 : list B)
    (H : map_monad f (a :: l1) ≈ ret (b :: l2)),
    f a ≈ ret b.
Proof.
  intros. simpl in H. apply BINDRETINV in H. repeat destruct H.
  apply BINDRETINV in H0. repeat destruct H0. apply EQRET in H1.
  inversion H1.
  subst. apply H.
Qed.

Lemma map_monad_MReturns_cons :
  forall {A B} (a1 a2 : A) (b : B) (f : A -> M B) (l2 : list A) (l1 : list B)
    (H : MReturns (b :: l1) (map_monad f (a2 :: l2))),
    MReturns l1 (map_monad f l2).
Proof.
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
Proof.
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
Proof.
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
Proof.
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
  forall {B} a b (k : A -> A -> M B),
    (y <- g a ;; z <- f b ;; k y z) ≈ (z <- f b ;; y <- g a ;; k y z).

Lemma map_comm_lemma : forall {A B} (b : A) (xs : list A) (g : A -> M A) (f : A -> M A) (k : A -> list A -> M B) (HC : commutative_maps g f), 
    (bs <- map_monad g xs ;; x <- f b ;; k x bs) ≈
      (x <- f b ;;  bs <- map_monad g xs ;; k x bs).
Proof.
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
Proof.
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


