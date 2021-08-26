From Coq Require Import
     List.

From ExtLib Require Import
     Structures.Monads.

From ITree Require Import
     Basics.Monad. 

Import MonadNotation.
Import ListNotations.

Open Scope monad.

Fixpoint foldM {a b} {M} `{Monad M} (f : b -> a -> M b ) (acc : b) (l : list a) : M b
  := match l with
     | [] => ret acc
     | (x :: xs) =>
       b <- f acc x;;
       foldM f b xs
     end.

Lemma map_monad_In {m : Type -> Type} {H : Monad m} {A B} (l : list A) (f: forall (x : A), In x l -> m B) : m (list B).
Proof.
  induction l.
  - exact (ret []).
  - refine (b <- f a _;; bs <- IHl _;; ret (b::bs)).
    + cbn; auto.
    + intros x Hin.
      apply (f x).
      cbn; auto.
Defined.

(* Lemma map_monad_In_app *)
(*       {m : Type -> Type} *)
(*       {Mm : Monad m} *)
(*       {EqMm : Eq1 m} *)
(*       {HEQP: Eq1Equivalence m} *)
(*       {ML: MonadLawsE m} *)
(*       {A B} (l0 l1:list A) (f: forall l (x : A), In x l -> m B): *)
(*   map_monad_In (l0++l1) (f (l0++l1)) ≈ *)
(*   bs1 <- map_monad_In l0 (f l0);; *)
(*   bs2 <- map_monad_In l1 (f l1);; *)
(*   ret (bs1 ++ bs2). *)
(* Proof. *)
(*   induction l0 as [| a l0 IH]; simpl; intros. *)
(*   - cbn; rewrite bind_ret_l, bind_ret_r. *)
(*     reflexivity. *)
(*   - cbn. *)
(*     setoid_rewrite IH. *)
(*     repeat setoid_rewrite bind_bind. *)
(*     setoid_rewrite bind_ret_l. *)
(*     reflexivity. *)
(* Qed. *)

(* map_monad_In elts (fun elt Hin => serialize_sbytes elt t);; *)
