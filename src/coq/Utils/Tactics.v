(* begin hide *)
From Coq Require Import
     String.

From ITree Require Import
     Eq.EqAxiom.
(* end hide *)

Ltac force_rewrite H :=
  let HB := fresh "HB" in
  pose proof @H as HB; eapply bisimulation_is_eq in HB; rewrite HB; clear HB.

Tactic Notation "force_rewrite:" constr(H) "in" hyp(H') :=
  let HB := fresh "HB" in
  pose proof @H as HB; eapply bisimulation_is_eq in HB; rewrite HB in H'; clear HB.

Ltac flatten_goal :=
  match goal with
  | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac flatten_hyp h :=
  match type of h with
  | context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac flatten_all :=
  match goal with
  | h: context[match ?x with | _ => _ end] |- _ => let Heq := fresh "Heq" in destruct x eqn:Heq
  | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac inv H := inversion H; try subst; clear H.

Global Tactic Notation "intros !" := repeat intro.

(* inv by name of the Inductive relation *)
Ltac invn f :=
    match goal with
    | [ id: f |- _ ] => inv id
    | [ id: f _ |- _ ] => inv id
    | [ id: f _ _ |- _ ] => inv id
    | [ id: f _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => inv id
    end.

(* destruct by name of the Inductive relation *)
Ltac destructn f :=
    match goal with
    | [ id: f |- _ ] => destruct id
    | [ id: f _ |- _ ] => destruct id
    | [ id: f _ _ |- _ ] => destruct id
    | [ id: f _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => destruct id
    end.

(* apply by name of the Inductive relation *)
Ltac appn f :=
    match goal with
    | [ id: f |- _ ] => apply id
    | [ id: f _ |- _ ] => apply id
    | [ id: f _ _ |- _ ] => apply id
    | [ id: f _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => apply id
    end.

(* eapply by name of the Inductive relation *)
Ltac eappn f :=
    match goal with
    | [ id: f |- _ ] => eapply id
    | [ id: f _ |- _ ] => eapply id
    | [ id: f _ _ |- _ ] => eapply id
    | [ id: f _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => eapply id
    end.

(** [break_match_hyp] looks for a [match] construct in some
    hypothesis, and destructs the discriminee, while retaining the
    information about the discriminee's value leading to the branch
    being taken. *)
Ltac break_match_hyp :=
  match goal with
    | [ H : context [ match ?X with _ => _ end ] |- _] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

Ltac break_match_hyp_inv :=
  match goal with
  | [ H : context [ match ?X with _ => _ end ] |- _] =>
      match type of X with
      | sumbool _ _ => destruct X
      | _ => destruct X eqn:?
      end;
      inv H
  end.

(** [break_match_goal] looks for a [match] construct in your goal, and
    destructs the discriminee, while retaining the information about
    the discriminee's value leading to the branch being taken. *)
Ltac break_match_goal :=
  match goal with
    | [ |- context [ match ?X with _ => _ end ] ] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

(** [break_match] breaks a match, either in a hypothesis or in your
    goal. *)
Ltac break_match := break_match_goal || break_match_hyp.

(** [break_let] breaks a destructuring [let] for a pair. *)
Ltac break_let :=
  match goal with
    | [ H : context [ (let (_,_) := ?X in _) ] |- _ ] => destruct X eqn:?
    | [ |- context [ (let (_,_) := ?X in _) ] ] => destruct X eqn:?
  end.

Ltac inv_option :=
  match goal with
  | h: Some _ = Some _ |-  _ => inv h
  | h: None   = Some _ |-  _ => inv h
  | h: Some _ = None   |-  _ => inv h
  | h: None   = None   |-  _ => inv h
  end.

Ltac inv_sum :=
  match goal with
  | h: inl _ = inl _ |-  _ => inv h
  | h: inr _ = inr _ |-  _ => inv h
  | h: inl _ = inr _ |-  _ => inv h
  | h: inr _ = inl _ |-  _ => inv h
  end.

Ltac break_sum :=
  match goal with
  | v: _ + _ |- _ => destruct v
  end.

From ITree Require Import
     ITree
     Eq.Eqit.

Ltac bind_ret_r1 :=
  match goal with
    |- eutt _ ?t ?s => let x := fresh in
                     remember s as x;
                     rewrite <- (bind_ret_r t); subst x
  end.

Ltac bind_ret_r2 :=
  match goal with
    |- eutt _ ?t ?s => let x := fresh in
                     remember t as x;
                     rewrite <- (bind_ret_r s); subst x
  end.

Ltac forward H :=
  let H' := fresh in
  match type of H with
  | ?P -> _ => assert P as H'; [| specialize (H H'); clear H']
  end.

(* Simple specialization of [eqit_Ret] to [eutt] so that users of the library do not need to know about [eqit] *)
Ltac ret_bind_l_left v :=
  match goal with
    |- eutt _ ?t _ =>
    rewrite <- (bind_ret_l v (fun _ => t))
  end.

Ltac simpl_match_hyp h :=
  match type of h with
    context[match ?x with | _ => _ end] =>
    match goal with
    | EQ: x = _ |- _ => rewrite EQ in h
    | EQ: _ = x |- _ => rewrite <- EQ in h
    end
  end.
Tactic Notation "simpl_match" "in" hyp(h) := simpl_match_hyp h.

Ltac destruct_unit :=
  match goal with
  | x : unit |- _ => destruct x
  end.

(** [break_inner_match' t] tries to destruct the innermost [match] it
    find in [t]. *)
Ltac break_inner_match' t :=
 match t with
   | context[match ?X with _ => _ end] =>
     break_inner_match' X || destruct X eqn:?
   | _ => destruct t eqn:?
 end.

(** [break_inner_match_goal] tries to destruct the innermost [match] it
    find in your goal. *)
Ltac break_inner_match_goal :=
 match goal with
   | [ |- context[match ?X with _ => _ end] ] =>
     break_inner_match' X
 end.

(** [break_inner_match_hyp] tries to destruct the innermost [match] it
    find in a hypothesis. *)
Ltac break_inner_match_hyp :=
 match goal with
   | [ H : context[match ?X with _ => _ end] |- _ ] =>
     break_inner_match' X
 end.

(** [break_inner_match] tries to destruct the innermost [match] it
    find in your goal or a hypothesis. *)
Ltac break_inner_match := break_inner_match_goal || break_inner_match_hyp.

Ltac forwardr H H' :=
  match type of H with
  | ?P -> _ => assert P as H'; [| specialize (H H')]
  end.
Tactic Notation "forwardr" ident(H) ident(H') := forwardr H H'.

Ltac match_rewrite :=
  match goal with
  | H : (?X = ?v) |-
    context [ match ?X with | _ => _ end] =>
    rewrite H
  end.

Ltac inv_eqs :=
  repeat 
    match goal with
    | h : ?x = ?x |- _ => clear h
    | h : _ = ?x |- _ => subst x
    | h : ?x = ?x /\ _ |- _ => destruct h as [_ ?]
    | h : _ = _ /\ _ |- _ => (destruct h as [<- ?] || destruct h as [?EQ ?])
    end.

Ltac splits :=
  repeat match goal with
           |- _ /\ _ => split
         end.

Ltac abs_by H :=
  exfalso; eapply H; now eauto.

Variant Box (T: Type): Type := box (t: T).
(* Protects from "direct" pattern matching but not from context one *)
Ltac protect H := apply box in H.
Ltac hide_string_hyp' H :=
  match type of H with
  | context [String ?x ?y] =>
    let msg := fresh "msg" in
    let eqmsg := fresh "EQ_msg" in
    remember (String x y) as msg eqn:eqmsg; protect eqmsg
  end.

Ltac hide_strings' :=
  repeat (
      match goal with
      | h: Box _ |- _ => idtac
      | h: context [String ?x ?y] |- _ =>
        let msg := fresh "msg" in
        let eqmsg := fresh "EQ_msg" in
        remember (String x y) as msg eqn:eqmsg;
        protect eqmsg
      | |- context [String ?x ?y] =>
        let msg := fresh "msg" in
        let eqmsg := fresh "EQ_msg" in
        remember (String x y) as msg eqn:eqmsg;
        protect eqmsg
      end).

Ltac forget_strings :=
  repeat (
      match goal with
      | h: context [String ?x ?y] |- _ =>
        let msg := fresh "msg" in
        generalize (String x y) as msg
      | |- context [String ?x ?y] =>
        let msg := fresh "msg" in
        generalize (String x y) as msg
      end).

Ltac break_and :=
  repeat match goal with
         | h: _ * _ |- _ => destruct h
         end.

Variant hidden_cont  (T: Type) : Type := boxh_cont (t: T).
Variant visible_cont (T: Type) : Type := boxv_cont (t: T).
Ltac hide_cont :=
  match goal with
  | h : visible_cont _ |- _ =>
    let EQ := fresh "HK" in
    destruct h as [EQ];
    apply boxh_cont in EQ
  | |- context[ITree.bind _ ?k] =>
    remember k as K eqn:VK;
    apply boxh_cont in VK
  end.
Ltac show_cont :=
  match goal with
  | h: hidden_cont _ |- _ =>
    let EQ := fresh "VK" in
    destruct h as [EQ];
    apply boxv_cont in EQ
  end.
Notation "'hidden' K" := (hidden_cont (K = _)) (only printing, at level 10).
Ltac subst_cont :=
  match goal with
  | h: hidden_cont _ |- _ =>
    destruct h; subst
  | h: visible_cont _ |- _ =>
    destruct h; subst
  end.
