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

Lemma imp_step_star_seq_append:
  forall p1 p2, imp_step_star p1 p2 ->
           forall c1 c2 c st1 st2,
             p1 = (c1, st1) -> p2 = (c2, st2) ->
             imp_step_star (c1 ;; c, st1) (c2 ;; c, st2).
Proof.
  intros p1 p2 imp_step_p1.
  induction imp_step_p1 as 
      [[c1' st1'] | [c1' st1'] [c_step st_step] [c_final st_final]];
    intros c1 c2 c st st2 p1_eq p2_eq; inversion p1_eq; inversion p2_eq; subst.
  - apply star_refl.
  - apply star_step with (b := (c_step ;; c, st_step)).
    apply S_Seq.
    trivial.
    apply IHimp_step_p1; reflexivity.
Qed.

Lemma imp_step_star_trans: forall c1 c2 st1 st2 st,
  imp_step_star (c1, st1) (SKIP, st) ->
  imp_step_star (c2, st) (SKIP, st2) ->
  imp_step_star (c1 ;; c2, st1) (SKIP, st2).
Proof.
  intros c1 c2 st1 st2 st imp1 imp2; unfold imp_step_star in *.
  inversion imp1; subst.
  - eapply star_step. 
    apply S_SeqSkip.
    trivial.
  - apply star_trans with (b := (SKIP ;; c2, st)).
    apply imp_step_star_seq_append with (p1 := (c1, st1)) (p2 := (SKIP, st));
      trivial.
    eapply star_step.
    apply S_SeqSkip.
    trivial.
Qed.

Lemma imp_step_star_seq_inversion:
  forall p1 p2, imp_step_star p1 p2 ->
           forall c1 c2 sta stc,
             p1 = (c1 ;; c2, sta) ->
             p2 = (SKIP, stc) ->
             exists stb, imp_step_star (c1, sta) (SKIP, stb) /\
                    imp_step_star (SKIP ;; c2, stb) (SKIP, stc).
Proof.
  intros p1 p2 imp_step_p1.
  induction imp_step_p1 as [| [cseq' sta'] p [skip' stc'] Hstep];
    intros c1 c2 sta stc p1_eq p2_eq; 
    try solve [rewrite p1_eq in p2_eq; inversion p2_eq].
  inversion p1_eq; inversion p2_eq; subst.
  clear p1_eq; clear p2_eq.
  destruct c1.
  - inversion Hstep as
        [ | sta' ? ? ? ? H | sta' c2' [c2_eq sta_eq] p_eq | | | ];
      [inversion H | idtac].
    subst.
    exists sta.
    split; [apply star_refl | idtac].
    eapply star_step; [apply S_SeqSkip | trivial].
  - inversion Hstep.
    rename H3 into step_sta.
    inversion step_sta.
    exists (update sta i (aeval a sta)).
    subst.
    split; auto.
    eapply star_step; [apply step_sta | apply star_refl].
  - inversion Hstep.
    rename st' into one_step_after_sta;
      rename c1' into c11';
      rename H0 into p_eq;
      rename H3 into step_c1_1.
    rewrite <- p_eq in Hstep.
    clear H1 H2 c0.
    generalize
      (IHimp_step_p1 c11' c2 one_step_after_sta stc (symmetry p_eq) eq_refl);
      intros IH.
    inversion IH as [stb [imp1 imp2]].
    exists stb.
    split; 
      [eapply star_step; 
       [apply step_c1_1 | apply imp1] | 
       apply imp2].
  - inversion Hstep.
    rename st' into one_step_after_sta; 
      rename c1' into c1';
      rename H3 into step_c1;
      rename H0 into p_eq.
    clear H1 H2 c0.
    generalize
      (IHimp_step_p1 c1' c2 one_step_after_sta stc (symmetry p_eq) eq_refl);
      intros IH.
    inversion IH as [stb [imp1 imp2]].
    exists stb.
    split; 
      [eapply star_step; 
       [apply step_c1 | apply imp1] | 
       apply imp2].
  - inversion Hstep.
    rename st' into one_step_after_sta; 
      rename c1' into c1';
      rename H3 into step_c1;
      rename H0 into p_eq.
    clear H H1 H2 c0.
    generalize
      (IHimp_step_p1 c1' c2 one_step_after_sta stc (symmetry p_eq) eq_refl);
      intros IH.
    inversion IH as [stb [imp1 imp2]].
    exists stb.
    split; 
      [eapply star_step; 
       [apply step_c1 | apply imp1] | 
       apply imp2].
Qed.

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

Ltac cases_on_imp_eval :=
  match goal with
  | H: match ?imp_eval with
          | Some _ => _
          | None => _ 
       end = _ |- _ =>
    destruct imp_eval as [middle_st | ] eqn:middle_st_eq;
    try solve [inversion H]
  end.

Theorem imp_eval_sound: forall fuel c st st',
    imp_eval c st fuel = Some st' -> imp_step_star (c, st) (SKIP, st').
Proof.
  induction fuel as [| n]; intros c st st' eval_ok;
    try solve [inversion eval_ok].
  destruct c.
  { simpl in eval_ok; inversion eval_ok. }
  { simpl in eval_ok; inversion eval_ok; subst.
    eapply star_step.
    apply S_Ass.
    reflexivity.
    apply star_refl.
  }
  { simpl in eval_ok.
    destruct c1;
      try solve [eapply star_step;
                 [apply S_SeqSkip |
                  apply IHn;
                  trivial]];
      try solve [cases_on_imp_eval;
                 generalize (IHn _ _ _ middle_st_eq); intros imp_single_step;
                 eapply imp_step_star_trans;
                 [apply imp_single_step |
                  apply IHn;
                  trivial]].
  } 
  { simpl in eval_ok.
    destruct (beval b st) eqn:eval_b;
      apply IHn in eval_ok.
    - eapply star_step; [apply S_IfTrue; trivial | trivial].
    - eapply star_step; [apply S_IfFalse; trivial | trivial].      
  }      
  { simpl in eval_ok.
    destruct (beval b st) eqn:eval_b;
      try solve [inversion eval_ok].
    apply IHn in eval_ok.
    eapply (imp_step_star_seq_inversion _ _) in eval_ok;
      [idtac | reflexivity | reflexivity].
    inversion eval_ok as [st_after_iter [after_one_iter the_rest]].
    eapply star_trans; [idtac | apply the_rest].
    eapply star_step; [apply S_While | idtac].
    eapply star_step; [apply S_IfTrue; trivial | idtac].
    apply (imp_step_star_seq_append _ _ after_one_iter); reflexivity.
  }     
Qed.


  