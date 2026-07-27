From Stdlib Require Import
  String List NArith.
From ExtLib Require Import
  Structures.Monads.
From Vellvm.Utils Require Import
  ListUtil Tactics.

Import MonadNotation.
Open Scope monad.

Variant EOU {X : Type} : Type :=
  | raise_error (s : string): EOU
  | raise_oom (s : string) : EOU
  | raise_ub (s : string) : EOU
  | raise_ret (x : X) : EOU.
Arguments EOU: clear implicits.

#[global] Instance EOU_monad : Monad EOU :=
  {| ret := @raise_ret ;
    bind _ _ c k :=
      match c with
      | raise_oom s => raise_oom s
      | raise_ub  s => raise_ub s
      | raise_error s => raise_error s
      | raise_ret x => k x
      end
  |}.

Lemma map_monad_EOU_Forall2 :
  forall {A B} (f : A -> EOU B) l res,
    map_monad f l = ret res <->
      Forall2 (fun a b => f a = ret b) l res.
Proof.
  induction l as [| a l IH]; cbn; intros ?.
  - split.
    + intros EQ; inv EQ; auto.
    + intros F; inv F; auto.
  - split.
    + intros EQ; break_match_hyp; abs_eq.
      break_match_hyp; abs_eq.
      inv EQ.
      apply Forall2_cons; auto.
      now apply IH.
    + intros HF; inv HF.
      rw_match.
      apply IH in H3.
      rw_match; auto.
Qed.

Lemma map_monad_EOU_success A B (f : A -> EOU B) (l : list A) b :
  map_monad f l = ret b ->
  forall a, In a l -> exists b, f a = ret b.
Proof.
  intros EQ; apply map_monad_EOU_Forall2 in EQ.
  induction EQ.
  - cbn; easy.
  - intros ? [<- | IN]; eauto.
Qed.

Definition option_ub {X : Type} (s : string) (x : option X) :=
  match x with
  | None => raise_ub s
  | Some v => ret v
  end.

(* [seq_map_monad_acc] (the tail-recursive builder used by [intptr_seq],
   see [IPtr.v]) agrees with [map_monad] over [Nseq] on [EOU]. Proved
   directly against [EOU]'s concrete (non-recursive) [bind] by case
   analysis, rather than generically over an arbitrary [MonadLaws]
   instance: [bind]'s continuation argument is buried under a binder in
   the induction, and plain [rewrite]/[setoid_rewrite] on an abstract
   [Monad]/[MonadLaws] don't get through it cleanly, whereas destructing
   the concrete [EOU] value trivializes each case (the accumulator swap
   that would otherwise need its own lemma is just [rev_append]'s
   defining equation, so [reflexivity] gets it for free here). *)
Lemma seq_map_monad_acc_go_eq :
  forall {A} (f : N -> EOU A) (len : nat) (acc : list A) (cur : N),
    seq_map_monad_acc_go f acc cur len =
      bs <- map_monad f (Nseq cur len);;
      ret (rev_append acc bs).
Proof.
  induction len as [| k IH]; intros acc cur; cbn.
  - reflexivity.
  - destruct (f cur) eqn:Hf; cbn; try reflexivity.
    rewrite IH.
    destruct (map_monad f (Nseq (N.succ cur) k)) eqn:Hmap; reflexivity.
Qed.

Lemma seq_map_monad_acc_eq :
  forall {A} (f : N -> EOU A) (start : N) (len : nat),
    seq_map_monad_acc f start len = map_monad f (Nseq start len).
Proof.
  intros; unfold seq_map_monad_acc.
  rewrite seq_map_monad_acc_go_eq.
  destruct (map_monad f (Nseq start len)); reflexivity.
Qed.

