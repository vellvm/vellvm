From Stdlib Require Import
  String List.
From ExtLib Require Import
  Structures.Monads.
From Vellvm.Utils Require Import
  ListUtil Tactics.
Import MonadNotation.

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

(* This function may essentially compute poison, but without a dvalue to embed it into yet.
     We take an adhoc lightweigh way to handle this currently with the following option return type.
     It is also tied to how we treat the behavior of running map_monad to extract a list of bytes:
     currently we want it to result into a Poison dvalue if any byte resulted in poison.
     We are likely to follow a finer grained approach soon.
 *)
Notation MaybePoison := option.
Notation Pois := None.
Notation NoPois := Some.
Definition EOUP Z := EOU (option Z).

#[global] Instance EOUP_Monad : Monad EOUP :=
  {| ret _ a := ret (NoPois a) ;
    bind _ _ c k := 
      bind (m := EOU) c (fun pov => match pov with
                                 | Pois => ret Pois
                                 | NoPois a => k a
                                 end)
  |}.

#[local] Open Scope monad_scope.

Definition catch_pois {A} {Z} (z_default:Z) (c : EOUP A) (k : A -> EOU Z) : EOU Z := 
  x <- (c : EOU _) ;;
  match x with
  | Pois => ret z_default
  | NoPois v => k v
  end.

