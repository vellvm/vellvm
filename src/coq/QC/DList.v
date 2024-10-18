From ExtLib Require Export Functor Monad Applicative.
From Coq Require Import List String.
Import ListNotations Ascii.
Local Open Scope string_scope.

Section TRList.
  Definition revTR {A} : list A -> list A :=
    @rev' A.
  
  Fixpoint appTR_aux {A} (l1 l2 acc : list A) : list A :=
    match l1 with
    | [] => rev_append acc l2
    | x :: xs => appTR_aux xs l2 (x :: acc)
    end.

  Definition appTR {A} (l1 l2 : list A) : list A :=
    appTR_aux l1 l2 [].

  Lemma appTR_nil_r {A} : forall (l : list A), appTR l [] = l.
  Proof.
    intros l. induction l; unfold appTR in *; simpl; auto.
    unfold appTR_aux in *; cbn in *.
  Admitted.
  
  Fixpoint repeatTR_aux {A} (a : A) (n : nat) (acc : list A) : list A :=
    match n with
    | 0 => acc
    | S n' => repeatTR_aux a (n') (a::acc)
    end.

  Definition repeatTR {A} (a : A) (n : nat) : list A :=
    repeatTR_aux a n [].

  Definition fold_rightTR {A B} (f : A -> B -> B) (init : B) (l : list A) : B :=
    fold_left (fun b a => f a b) (revTR l) init.
  
End TRList.

Module TRList_Notation.
  Delimit Scope list_scope with list.
  Notation "l1 +++ l2" := (appTR l1 l2) (right associativity, at level 60) : list_scope.
End TRList_Notation.
Import TRList_Notation.

Section DList.
  Definition DList (A : Type) := list A -> list A.

  Definition DList_to_list {A} (dl : DList A) : list A
    := dl [].

  Definition DList_append {A} (dl1 dl2 : DList A) : DList A
    := fun xs => dl1 (dl2 xs).

  Definition DList_singleton {A} (a : A) : DList A
    := cons a.

  Definition DList_cons {A} (a : A) (dl : DList A) : DList A
    := DList_append (DList_singleton a) dl.

  Definition DList_snoc {A} (a : A) (dl : DList A) : DList A
    := DList_append dl (DList_singleton a).

  Definition DList_empty {A} : DList A
    := fun xs => xs.

  (* TODO: I think the original version (commented out) is O(n) runtime due to the use of fold_left *)
  Definition DList_from_list {A} (l : list A) : DList A
    (* := fold_left (fun x s => DList_append x (DList_singleton s)) l DList_empty. *)
    := fun l2 => (l +++ l2)%list.
  
  Definition DList_map {A B} (f : A -> B) (dl : DList A) : DList B
    := fold_left (fun acc a => DList_cons (f a) acc) (DList_to_list dl) (@DList_empty B) .

  Definition concat {A} (l : list (DList A)) : DList A
    := fold_left DList_append l DList_empty.

  Definition replicate {A} (n : nat) (a : A) : DList A
    := fold_left (fun acc x => DList_cons x acc) (repeatTR a n) DList_empty .

  #[global] Instance Functor_DList : Functor DList.
  Proof.
    split.
    intros A B X X0.
    eapply DList_map; eauto.
  Defined.

  Definition DList_fold_right {A B} (f : A -> B -> B) (z: B) (dl : DList A) : B
    := fold_rightTR f z (DList_to_list dl).

  Definition DList_fold_left {A B} (f : B -> A -> B) (dl : DList A) (z : B) : B
    := List.fold_left f (DList_to_list dl) z.

  Definition DList_join {A} (ls : list (DList A)) :=
    fold_left DList_append ls DList_empty.

  #[global] Instance Monad_DList : Monad DList.
  Proof.
    split.
    intros T t. eapply DList_singleton; eauto.
    intros T U ts f.
    apply (@DList_fold_right T).
    - refine (fun t => _).
      apply DList_append.
      exact (f t).
    - apply DList_empty.
    - apply ts.
  Defined.

  #[global] Instance Applicative_DList : Applicative DList.
  Proof.
    split.
    intros T t. eapply DList_singleton; eauto.
    intros T U dlab dla.
    eapply bind.
    - apply dlab.
    - intros f.
      eapply bind.
      + apply dla.
      + intros t.
        apply ret.
        exact (f t).
  Defined. 

End DList.

Section Lemmas.
  Definition wf_DList {A} (dl : DList A) :=
    exists l, dl l = (dl [] ++ l)%list.
  
  Lemma DList_to_from_list {A} : forall (l : list A),
      DList_to_list (DList_from_list l) = l.
  Proof.
    intros l; unfold DList_from_list, DList_to_list. cbn. apply appTR_nil_r.
  Qed.

  (* Lemma DList_from_to_list {A} : forall (dl : DList A) (l : list A), *)
  (*     DList_from_list (DList_to_list dl) l = dl l. *)
  (* Proof. *)
  (*   intros dl l; unfold DList_from_list, DList_to_list, DList in *; cbn. *)

  Lemma DList_empty_list {A : Type} :
    @DList_empty A [] = [].
  Proof.
    unfold DList_empty; auto.
  Qed.

  Lemma DList_singleton_eq {A : Type} : forall (a : A),
      DList_to_list (DList_singleton a) = [a].
  Proof.
    intros a; unfold DList_to_list, DList_singleton; auto.
  Qed.

  Lemma DList_cons_eq {A} : forall (dl : DList A) (a : A),
      DList_to_list (DList_cons a dl)  = a :: (DList_to_list dl).
  Proof.
    intros dl a; unfold DList_to_list, DList_cons, DList_append, DList_singleton; auto.
  Qed.

  Lemma DList_append_eq {A} : forall (dl : DList A) (dl2 : DList A),
      DList_to_list (DList_append dl dl2) = dl (DList_to_list dl2).
  Proof.
    intros dl dl2. unfold DList_to_list, DList_append; auto.
  Qed.

End Lemmas.

Section DString.

  Definition DString := DList ascii.

  (* TODO: move this? *)
  Fixpoint string_fold_left {A} (f : A -> ascii -> A) (s:string) (acc:A) : A :=
    match s with
    | EmptyString => acc
    | String ch s =>
        string_fold_left f s (f acc ch)
    end.

  Definition rev_string (s : string) : string
    := string_fold_left (fun acc x => String x acc) s EmptyString.

  (* TODO: move this? *)
  Definition rev_tail_rec {X} (xs : list X)
    := fold_left (fun acc x => x :: acc) xs [].

  Definition string_of_list_ascii_tail_rec (s : list ascii) : string
    := rev_string (fold_left (fun acc ch => String ch acc) s EmptyString).

  Definition list_ascii_of_string_tail_rec (s : string) : list ascii
    := rev_tail_rec (string_fold_left (fun acc ch => ch :: acc) s []).

  Definition DString_to_string (ds : DString) : string :=
    string_of_list_ascii_tail_rec (ds []).

  Definition string_to_DString (s : string) : DString := appTR (list_ascii_of_string_tail_rec s).

  Definition list_to_DString (ls : list string) : DString :=
    fold_left (fun x s => DList_append x (string_to_DString s)) ls DList_empty.

  Definition EmptyDString := string_to_DString EmptyString.

  (* Fixpoint concat_DString_aux (ls : list DString) (sep acc : DString) := *)
  (*   match ls with *)
  (*   | [] => EmptyDString *)
  (*   | x :: nil => x *)
  (*   | x :: y :: [] => *)
  (*       DList_append (DList_append x sep) y *)
  (*   | x :: y :: xs => *)
        
  
  (* Fixpoint concat_DString (sep : DString) (ls : list DString) := *)
  (*   match ls with *)
  (*   | nil => EmptyDString *)
  (*   | cons x nil => x *)
  (*   | cons x (cons y []) => *)
  (*       DList_append (DList_append x sep) y *)
  (*   | cons x (cons y xs) => *)
  (*       DList_append (DList_append (DList_append (DList_append x sep) y) sep) *)
  (*   end. *)
  Fixpoint concat_DString (sep : DString) (ls : list DString) :=
    match ls with
    | nil => EmptyDString
    | cons x nil => x
    | cons x xs => DList_append (DList_append x sep) (concat_DString sep xs)
    end.

End DString.
