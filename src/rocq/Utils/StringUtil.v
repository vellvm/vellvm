From Stdlib Require Import String Ascii List.
From Vellvm.Utils Require Import ListUtil.
Import ListNotations.

Fixpoint string_fold_left {A} (f : A -> ascii -> A) (s:string) (acc:A) : A :=
  match s with
  | EmptyString => acc
  | String ch s =>
      string_fold_left f s (f acc ch)
  end.

Definition rev_string (s : string) : string
  := string_fold_left (fun acc x => String x acc) s EmptyString.

Definition string_of_list_ascii_tail_rec (s : list ascii) : string
  := rev_string (fold_left (fun acc ch => String ch acc) s EmptyString).

Definition list_ascii_of_string_tail_rec (s : string) : list ascii
  := rev_tail_rec (string_fold_left (fun acc ch => ch :: acc) s []).

