From ExtLib Require Export Functor.
From Coq Require Import List String.
Import ListNotations Ascii.
Local Open Scope string_scope.

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

  Definition DList_empty {A} : DList A
    := fun xs => xs.

  Definition DList_from_list {A} (l : list A) : DList A
    := fold_left (fun x s => DList_append x (DList_singleton s)) l DList_empty.
  
  Definition DList_map {A B} (f : A -> B) (dl : DList A) : DList B
    := fold_right (fun a => DList_cons (f a)) (@DList_empty B) (DList_to_list dl).

  #[global] Instance DList_Functor : Functor DList.
  Proof.
    split.
    intros A B X X0.
    eapply DList_map; eauto.
  Defined.

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

  Definition string_to_DString (s : string) : DString := app (list_ascii_of_string_tail_rec s).

  Definition list_to_DString (ls : list string) : DString :=
    fold_left (fun x s => DList_append x (string_to_DString s)) ls DList_empty.

  Definition EmptyDString := string_to_DString EmptyString.

  Fixpoint concat_DString (sep : DString) (ls : list DString) :=
    match ls with
    | nil => EmptyDString
    | cons x nil => x
    | cons x xs => DList_append (DList_append x sep) (concat_DString sep xs)
    end.

  Definition DList_join {A} (ls : list (DList A)) :=
    fold_left DList_append ls DList_empty.

End DList.

Definition example1 : DList nat := DList_cons 1 DList_empty.
