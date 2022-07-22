From Coq Require Import
     FSets.FMapAVL
     FSets.FSetAVL
     FSetProperties
     FMapFacts
     ZArith
     List
     Lia.

From Vellvm Require Import
     Utils.MonadRefactored
     Utils.MonadRefactoredTheory
     ListUtil.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.OptionMonad.

Import ListNotations.
Import MonadNotation.

(* N maps *)
Module NM := FMapAVL.Make(Coq.Structures.OrderedTypeEx.N_as_OT).
Definition NMap := NM.t.

Fixpoint NM_from_list {A} (kvs : list (N * A)) : NMap A
  := match kvs with
     | [] => @NM.empty _
     | ((k, v)::xs) => @NM.add _ k v (NM_from_list xs)
     end.

(* N sets *)
Module NS := FSetAVL.Make(Coq.Structures.OrderedTypeEx.N_as_OT).
Definition NSet := NS.t.

Fixpoint NS_from_list (kvs : list N) : NSet
  := match kvs with
     | [] => NS.empty
     | (x::xs) => NS.add x (NS_from_list xs)
     end.

Fixpoint NM_find_many {A} (xs : list N) (nm : NMap A) : option (list A)
  := match xs with
     | [] => ret []
     | (x::xs) =>
       elt  <- NM.find x nm;;
       elts <- NM_find_many xs nm;;
       ret (elt :: elts)
     end.
