From Coq Require Import
         List
         Lia
.

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


(* An rosetree datatype that uses a list of its own type recursively. *)

Unset Elimination Schemes.
Inductive rosetree (A:Type) :=
| CBase (n:A)
| CList (l:list (rosetree A)).
Arguments CBase {A} _.
Arguments CList {A} _.


(* First, define a recursion principle that gives better reasoning principles. *)
Section rosetree_ind.
  Variable A : Type.
  Variable P : rosetree A -> Prop.

  Hypothesis H_CBase :
    forall (a:A), P (CBase a).

  Hypothesis IH_CList :
    forall l, (forall e, In e l -> P e) -> P (CList l).

  Lemma rosetree_ind : forall e, P e.
  Proof.
    fix IH 1.
    remember P as P0 in IH.
    destruct e; auto; subst.
    - apply IH_CList.
      revert l.
      fix IHL 1.
      intros [ | e1 l1]. 
      + intros.  inversion H.
      + intros e' [<- |Hin].
        apply IH.
        eapply IHL.
        apply Hin.
  Qed.
End rosetree_ind.      

Check rosetree_ind.


(* Here is an analog for doing a computational fold over [rosetree].  I'm not sure 
   how useful it is, since you probably want to use [Fixpoint] to define functions.
*)
Section rosetree_rect.
  Variable A : Type. 
  Variable P : rosetree A -> Type.

  Hypothesis H_CBase :
    forall (n:A), P (CBase n).

  Hypothesis IH_CList :
    forall l, (forall i e, nth_error l i = Some e -> P e) -> P (CList l).

  Lemma rosetree_rect : forall e,  P e.
  Proof.
    fix IH 1.
    destruct e; intros.
    - apply H_CBase.
    - apply IH_CList.
      revert l.
      fix IHL 1. (* NOTE: doing induction on the list here doesn't work. *)
      intros [ | e1 l1]. 
      + intros.
        apply  nth_error_In in H. inversion H.
        
      + intros i e EQ.
        destruct i.
        * simpl in EQ. inversion EQ.
          rewrite <- H0. (* !!! NOTE: You must rewrite in this direction because otherwise *)
          (*                  the types don't line up correctly!  What counts as a "substructure" isn't *)
          (*                  taken modulo '='. *)
          (*                *)
          apply IH.
        * simpl in EQ.
          eapply IHL.
          apply EQ.
  Qed.
End rosetree_rect.
  
Fixpoint sum_rosetree (e:rosetree nat) : nat :=
  match e with
  | CBase n => n
  | CList l => List.fold_right (fun e acc => acc + sum_rosetree e) 0 l
  end.

Inductive rel : rosetree nat -> rosetree nat -> Prop := 
| RB :
  forall x,
    rel (CBase x) (CBase (x + x))
| RL :
  forall l1 l2,
    List.Forall2 rel l1 l2 ->
    rel (CList l1) (CList l2).

Section rel_ind.
  Variable P : rosetree nat -> rosetree nat -> Prop.
  Hypothesis IH_RB :
    forall x, P (CBase x) (CBase (x + x)).
  Hypothesis IH_RL :
    forall l1 l2,
      Forall2 P l1 l2 ->
      P (CList l1) (CList l2).

  Lemma rel_ind : forall (e1 e2 : rosetree nat) (REL: rel e1 e2), P e1 e2.
  Proof.
    fix IH 1.
    remember P as P0 in IH.
    destruct e1; destruct e2; intros; inversion REL; auto; subst.
    - apply IH_RL.
      revert l l0 REL H1.
      fix IHL 1.
      intros l1 l2 REL H.
      destruct l1. 
      + inversion H. subst.
        apply Forall2_nil.
      + inversion H. subst.
        eapply Forall2_cons.
        apply IH.
        assumption.
        eapply IHL.
        constructor.
        assumption.
        assumption.
  Qed.

End rel_ind.

Check rel_ind.

Inductive contains {A} (a:A) : rosetree A -> Prop :=
| RI_CBase : contains a (CBase a)
| RI_CList : forall l, List.Exists (contains a) l -> contains a (CList l).


Lemma contains_doubled : forall n e1 e2,
    rel e1 e2 ->
    contains n e1 ->
    contains (n + n) e2.
Proof.
  intros n e1 e2 REL.
  induction REL; intros.
  - inversion H.
    subst. constructor.
  - inversion H0.
    subst.
    apply Exists_In in H2.
    destruct H2 as [a [HIN HR]].
    constructor.
    apply Exists_In.
    eapply Forall2_In in H; eauto.
    destruct H as [b [HI HP]].
    exists b. split; auto.
Qed.

Lemma list_sum_doubled :
  forall {A} (l1 l2 : list A) (f : A -> nat),
    Forall2 (fun a b => f b = f a + f a) l1 l2 ->
    List.fold_right (fun e acc => acc + f e) 0 l2 =
      (List.fold_right (fun e acc => acc + f e) 0 l1) + (List.fold_right (fun e acc => acc + f e) 0 l1).
Proof.
  induction l1; intros.
  - inversion H.
    subst.
    reflexivity.
  - inversion H; subst.
    simpl.
    rewrite IHl1; auto.
    lia.
Qed.
    
Lemma rel_sum_doubled : forall e1 e2,
    rel e1 e2 ->
    sum_rosetree e2 = (sum_rosetree e1) + (sum_rosetree e1).
Proof.
  intros e1 e2 REL.
  induction REL; intros.
  - simpl. reflexivity.
  - simpl.
    apply list_sum_doubled.
    assumption.
Qed.    

(** MONADS *)
From ExtLib Require Import
     Structures.Monads
     Data.Monads.EitherMonad.


From Vellvm Require Import
     Utilities
     Utils.MapMonadExtra
     Utils.MonadEq1Laws
     Utils.MonadReturnsLaws.

Import MonadNotation.

Fixpoint mfold_rosetree {A B} {M} `{Monad M}
  (CBase_f : A -> M B)
  (CList_f : list B -> M B)
  (e : rosetree A) : M B :=
  match e with
  | CBase a => CBase_f a

  | CList l =>
      l' <- map_monad (mfold_rosetree CBase_f CList_f) l ;;
      CList_f l'
  end.

Check @mfold_rosetree.

Inductive rosetree_P {A} (P: A -> Prop) : rosetree A -> Prop :=
| P_CBase : forall a, P a -> rosetree_P P (CBase a)
| P_CList : forall l, List.Forall (rosetree_P P) l -> rosetree_P P (CList l).



Section mfold_rosetree_ind.
  
  Context {A B} {M} `{HM: Monad M} `{HL: Monad.MonadLawsE M} (P : A -> Prop) (R : M B -> Prop).
  Variable (R_Proper : forall m1 m2, Monad.eq1 m1 m2 -> R m2 -> R m1).
  Variable (CBase_f : A -> M B).
  Variable (CList_f : list B -> M B).
  Variable (HBase : forall a, P a -> R (CBase_f a)).
  Variable (HBind : forall (l : list (rosetree A)),
               (Forall (rosetree_P P) l) -> 
               (R (l' <- (map_monad (mfold_rosetree CBase_f CList_f) l) ;; CList_f l'))).

  Lemma mfold_rosetree_ind :
    forall (e : rosetree A),
      rosetree_P P e ->
      R (mfold_rosetree CBase_f CList_f e).
  Proof.
    destruct HL.
    induction e; intros.
    - cbn.
      inversion H. subst.
      apply HBase.
      assumption.
    - cbn.
      inversion H0.
      subst.
      apply HBind.
      assumption.
  Qed.

  Lemma helper : 
    forall (f : rosetree A -> M B)
      (HF: forall e, (rosetree_P P e) -> R (f e))
      (CList_f_nil : R (CList_f nil))
      (CList_f_mono :
        forall (e : rosetree A)
          (l : list (rosetree A)),
          R (f e) ->
          R (l' <- map_monad f l ;; CList_f l') ->
          R (y <- f e;; l' <- (bs <- map_monad f l;; ret (y :: bs));; CList_f l')
      )
      l,
      Forall (rosetree_P P) l ->
      R (l' <- map_monad f l ;; CList_f l').
  Proof.
    destruct HL.
    intros.
    induction l.
    - simpl.
      eapply R_Proper.
      apply bind_ret_l.
      apply CList_f_nil.
    - simpl.
      eapply R_Proper.
      apply bind_bind.
      simpl.
      inversion H. subst.
      apply CList_f_mono.
      + apply HF.
        assumption.
      + apply IHl.
        assumption.
  Qed.
End mfold_rosetree_ind.

Section R_monotonic.
  Context {A B:Type} {M} `{HM: Monad M} (R : M B -> Prop).
  Context `{HL: Monad.MonadLawsE M} .
  Variable (R_Proper : forall m1 m2, Monad.eq1 m1 m2 -> R m2 -> R m1).
  Variable (CBase_f : A -> M B).
  Variable (CList_f : list B -> M B).
  Variable (f : rosetree A -> M B).
  
  Record monotonic' : Prop := {
    r_mono_nil: R (CList_f nil) ;
    r_mono_cons:
      (forall (e : rosetree A) (l : list (rosetree A)),
          R (f e) ->
          R (l' <- map_monad f l;; CList_f l') ->
          R (y <- f e;; l' <- (bs <- map_monad f l;; ret (y :: bs));; CList_f l'))
    }.
End R_monotonic.


Section mmap_rosetree.
  Context {A B} {M} `{HM: Monad M} `{HL: Monad.MonadLawsE M} (P : A -> Prop) (R : M (rosetree B) -> Prop).
  Variable (R_Proper : forall m1 m2, Monad.eq1 m1 m2 -> R m2 -> R m1).
  Variable f : A -> M B.
  Definition rosetree_map_base := fun a => b <- f a ;; ret (CBase b).
  Definition rosetree_map_list := fun (l:list (rosetree B)) => ret (CList l).

  Variable HBase : forall (a:A), P a -> R (rosetree_map_base a).
  
  Definition mmap_rosetree (e : rosetree A) : M (rosetree B) :=
    @mfold_rosetree A (rosetree B) M _
      rosetree_map_base
      rosetree_map_list
      e.

  Lemma mmap_rosetree_helper :
      forall 
      (HF: forall e, (rosetree_P P e) -> R (mmap_rosetree e))
      (CList_f_nil : R (ret (CList nil)))
      (CList_f_mono :
        forall (e : rosetree A)
          (l : list (rosetree A)),
          R (mmap_rosetree e) ->
          R (l' <- map_monad mmap_rosetree l ;; ret (CList l')) ->
          R (y <- mmap_rosetree e;; l' <- (bs <- map_monad mmap_rosetree l;; ret (y :: bs));; ret (CList l'))
      )
      l,
      Forall (rosetree_P P) l ->
      R (l' <- map_monad mmap_rosetree l ;; ret (CList l')).
  Proof.
    intros.
    eapply helper; eauto.
  Qed.


  Definition rosetree_monotonic  := forall (g : (rosetree A) -> M (rosetree B)),
      @monotonic' A (rosetree B) M R _ rosetree_map_list g.

  Lemma monotonic_implies_R :
    rosetree_monotonic ->
    forall (e:rosetree A),
      rosetree_P P e ->
      (R (mmap_rosetree e)).
  Proof.
    destruct HL; clear HL.
    intros MONO.
    induction e.
    - intros; simpl. apply HBase. inversion H; subst; auto.
    - revert H.
      induction l; intros.
      + simpl.
        eapply R_Proper.
        apply bind_ret_l.
        destruct (MONO mmap_rosetree).
        assumption.
      + unfold mmap_rosetree.
        simpl. 
        eapply R_Proper.
        apply bind_bind.
        specialize (MONO mmap_rosetree).
        destruct MONO.
        apply r_mono_cons0.
        specialize (H a).
        apply H.
        * left; auto.
        * inversion H0; subst; auto. inversion H2; subst; auto.
        * unfold mmap_rosetree in IHl.
          simpl in IHl.
          apply IHl.
          intros.
          apply H. right. assumption. assumption.
          inversion H0; subst.
          constructor.
          inversion H2; subst; auto.
  Qed.        

End map_monad_ind.

Check @monotonic_implies_R.

  
Section error_monad_rosetree.

  Definition error_on0 : nat -> option nat := fun x => if Nat.eqb x 0 then error else ret x.

  Definition error_on0_rosetree : rosetree nat -> option (rosetree nat) := mmap_rosetree error_on0.

  Definition R (e : rosetree nat) : option (rosetree nat) -> Prop :=    
    fun oe => forall e', oe = Some e' -> e = e'.
  
  Lemma em_R : forall e, @rosetree_monotonic nat nat _ _ (R e).
  Proof.
    intros e.
    unfold rosetree_monotonic.
    intros.
    split.
    - red.
      
      
  Lemma em_R : forall e e', error_on0_rosetree e = Some e' -> e = e'.
  Proof.


  
  

            
