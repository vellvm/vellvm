(* TODO: License / Which Version of Imp? *)


(** * Imp: Simple Imperative Programs *)

(** FULL: This file presents a variant of the Imp programming language 
    adapted from the Software Foundations book.  It is the source
    language that will be compiled to the Vminus intermediate language
    in this development.
*)

Require Import Equalities Arith.
Require Import Vminus.Atom Vminus.Env.
Require Import Vminus.Sequences.

(** *** Identifiers *)

(** FULL: To simplify the compilation process, this variant of Imp uses 
    [Atom.t] values as variable identifiers.  [Atom.t] is also used by
    the [Vminus] language, so making them the same avoids the need to
    use some kind of mapping from source to target identifiers.

    This is a slight deviation from the earlier presentation that took
    [id] to be constructed via [Id : nat -> id].  

    The reason to use [Atom.t] is that this type supports the
    generation of "fresh" identifiers, a feature needed in
    implementing a compiler.  
*)
(** TERSE: One difference in this version of Imp: identifiers are given by [Atom.t].
*)

Definition id := Atom.t.

(** TERSE:     This is a slight deviation from the earlier presentation that took
    [id] to be constructed via [Id : nat -> id].  
*)

(** *** Arithmetic expressions *)
(** Arithmetic expressions are just the same as in Imp. *)

Inductive aexp : Type := 
  | ANum   : nat -> aexp
  | AId    : id -> aexp
  | APlus  : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult  : aexp -> aexp -> aexp.

(** *** Boolean expressions *)
(** Boolean expressions are also just the same as in Imp.  Since (as
    we'll see) Vminus doesn't support boolean values natively, we'll
    have to compile these to natural numbers. *)

Inductive bexp : Type := 
  | BTrue  : bexp
  | BFalse : bexp
  | BEq    : aexp -> aexp -> bexp
  | BLe    : aexp -> aexp -> bexp
  | BNot   : bexp -> bexp
  | BAnd   : bexp -> bexp -> bexp.

(** *** Commands *)
(** The commands are just the same as in Imp. *)

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.


(** *** Notation *)
Notation "'SKIP'" := 
  CSkip : imp_scope.
Notation "X '::=' a" := 
  (CAss X a) (at level 60) : imp_scope.
Notation "c1 ;; c2" := 
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" := 
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" := 
  (CIf e1 e2 e3) (at level 80, right associativity) : imp_scope.

(* FIX: Add an example program *)
(** *** An Example:
<<
X ::= 5;;
Y ::= 1;;
WHILE (BNot (Beq (AId X) (ANum 0))) DO
  Y ::= AMult (AId Y) (AId X);;         (* Y = Y * X *)
  X ::= AMinus (AId X) (ANum 1)         (* X = X - 1 *)
END
>>
*)

(** ** Operational Semantics *)

(** The _state_ of an Imp program maps Atoms to natural numbers. *)

Module State := Make_Env Atom.

Local Open Scope imp_scope.
Definition state := State.t nat.
Definition update := @State.update nat.


(** *** Arithmetic evaluation *)
(** Arithmetic and boolean expressions are evaluated in a given 
    state. *)

Fixpoint aeval (e : aexp) (st : state) : nat :=
  match e with
  | ANum n        => n
  | AId X         => st X
  | APlus a1 a2   => (aeval a1 st) + (aeval a2 st)
  | AMinus a1 a2  => (aeval a1 st) - (aeval a2 st)
  | AMult a1 a2   => (aeval a1 st) * (aeval a2 st)
  end.


(** *** Boolean evaluation *)
Fixpoint beval (e : bexp) (st : state) : bool :=
  match e with 
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval a1 st) (aeval a2 st)
  | BLe a1 a2   => leb (aeval a1 st) (aeval a2 st)
  | BNot b1     => negb (beval b1 st)
  | BAnd b1 b2  => andb (beval b1 st) (beval b2 st)
  end.


(** *** Small step evaluation relation *)

Inductive step : (com * state) -> (com * state) -> Prop :=
| S_Ass : forall st i a n,
    aeval a st = n ->
    step (i ::= a, st) (SKIP, update st i n)

| S_Seq : forall st st' c1 c1' c2,
    step (c1, st) (c1', st') ->
    step (c1 ;; c2, st) (c1' ;; c2, st')

| S_SeqSkip : forall st c2,
    step (SKIP ;; c2, st) (c2, st)

| S_IfTrue : forall st c1 c2 e,
    beval e st = true -> 
    step (IFB e THEN c1 ELSE c2 FI, st) (c1, st)

| S_IfFalse : forall st c1 c2 e,
    beval e st = false ->
    step (IFB e THEN c1 ELSE c2 FI, st) (c2, st)

| S_While : forall st c e,
    step (WHILE e DO c END, st) 
         (IFB e THEN (c ;; WHILE e DO c END) ELSE SKIP FI, st).


Definition imp_step_star := star step.

(** Imp Evaluator **)

Fixpoint imp_eval1 (c: com) (st: state) (fuel : nat) : option state :=
  match fuel with
  | 0 => None
  | S n' => 
    match c with
    | (i ::= a) => Some (update st i (aeval a st))
    | c1 ;; c2 =>
      match imp_eval1 c1 st n' with
      | Some st' => imp_eval1 c2 st' n'
      | None => None
      end
    | SKIP => Some st
    | IFB e THEN c1 ELSE c2 FI =>
      if beval e st then imp_eval1 c1 st n' else imp_eval1 c2 st n'
    | WHILE e DO c END =>
      if beval e st then imp_eval1 (c ;; WHILE e DO c END) st n'
      else Some st
    end
  end.

Fixpoint imp_eval2 (c: com) (st: state) (fuel: nat) : option state :=
  match fuel with
  | 0 => None
  | S n' =>
    match c with
    | (i ::= a) => Some (update st i (aeval a st))
    | c1 ;; c2 =>
      match c1 with
      | SKIP => imp_eval2 c2 st n'
      | _ => 
        match imp_eval2 c1 st n' with
        | Some st' => imp_eval2 c2 st' n'
        | None => None
        end
      end
    | SKIP => None
    | IFB e THEN c1 ELSE c2 FI =>
      if beval e st then imp_eval2 c1 st n' else imp_eval2 c2 st n'
    | WHILE e DO c END =>
      if beval e st then imp_eval2 (c ;; WHILE e DO c END) st n'
      else Some st
    end
  end.

Fixpoint imp_eval (c: com) (st: state) (fuel: nat) : option state :=
  match fuel with
  | 0 => None
  | S n' =>
    match c with
    | (i ::= a) => Some (update st i (aeval a st))
    | c1 ;; c2 =>
      match c1 with
      | SKIP => imp_eval c2 st n'
      | _ => 
        match imp_eval c1 st n' with
        | Some st' => imp_eval c2 st' n'
        | None => None
        end
      end
    | SKIP => None
    | IFB e THEN c1 ELSE c2 FI =>
      if beval e st then imp_eval c1 st n' else imp_eval c2 st n'
    | WHILE e DO c END =>
      if beval e st then imp_eval (c ;; WHILE e DO c END) st n'
      else None
    end
  end.

  