(* begin hide *)
From ITree Require Import
     ITree
     Basics
     Eq.Eqit.

Import ITreeNotations.
(* end hide *)

Section Pure.

  Variable E : Type -> Type.
  Notation rel A B := (A -> B -> Prop).
  Notation "'(' p ',' q ')' '{{' Q '}}'" := (eutt Q p q).
  Notation prog := (itree E).

  Lemma consequence_pure:
    forall {A1 A2 B1 B2}
      (R: rel A1 B1) (Q: rel A2 B2)
      (p1: prog A1) (p2: prog A2) (q1: prog B1) (q2: prog B2),
      
      (p1,q1){{R}} ->
      (p2,q2){{Q}} ->
      (* --------------- *)
      (p1;;p2,q1;;q2){{Q}}. 

  Proof using.
    intros.
    eapply eutt_clo_bind; eauto.
  Qed.

  Lemma consequence_pure_bind:
    forall {A1 A2 B1 B2}
      (R: rel A1 B1) (Q: rel A2 B2)
      (p1: prog A1) (p2: A1 -> prog A2) (q1: prog B1) (q2: B1 -> prog B2),
      
      (p1,q1){{R}} ->
      (forall a b, R a b -> (p2 a,q2 b){{Q}}) ->
      (* ----------------------------- *)
      (x <- p1;;p2 x, x <- q1;;q2 x){{Q}}. 

  Proof using.
    intros.
    eapply eutt_clo_bind; eauto.
  Qed.

  
End Pure.

Section State.

  Import ITree.Basics.Basics.Monads.
  (* Domains of states *)
  Variable σ1 σ2: Type.
  Variable E: Type -> Type.
  Notation rel A B := (A -> B -> Prop).
  Notation "'{{' P '}}' '(' p ',' q ')' '{{' Q '}}'" :=
    (forall s1 s2, P s1 s2 -> eutt Q (p (fst s1)) (q (fst s2))).
  Notation prog σ := (stateT σ (itree E)). 

  Definition lift_state_rel (R: rel σ1 σ2): rel (σ1 * unit) (σ2 * unit) :=
    fun '(s1,_) '(s2,_) => R s1 s2.
  Notation "↑" := lift_state_rel.

  Lemma consequence_state:
    forall {A1 A2 B1 B2}
      (R: rel σ1 σ2)
      (Q: rel (σ1 * A1) (σ2 * B1))
      (S: rel (σ1 * A2) (σ2 * B2))
      (p1: prog σ1 A1) (p2: prog σ1 A2) (q1: prog σ2 B1) (q2: prog σ2 B2),


      {{↑R}} (p1,q1) {{Q}} ->
      {{Q}}  (p2,q2) {{S}} ->
   (* ---------------------------------- *)
      {{↑R}}
        (fun s1 => '(s2,_) <- p1 s1;; p2 s2,
         fun s1 => '(s2,_) <- q1 s1;; q2 s2)
      {{S}}.
  Proof using.
    intros * H1 H2.
    intros s1 s2 PRE; specialize (H1 _ _ PRE).
    destruct s1 as [s1 []], s2 as [s2 []]; cbn.
    eapply eutt_clo_bind; eauto.
    intros [s1' ?] [s2' ?] PRE'.
    apply (H2 _ _ PRE').
  Qed.

  Definition REL {A B} (Q : rel (σ1 * A) (σ2 * B)) (a:A) (b:B) : rel (σ1 * A) (σ2 * B) :=
    fun '(s1, a') '(s2, b') => a = a' /\ b = b' /\ Q (s1, a) (s2, b).
  
  Lemma consequence_state_bind:
    forall {A1 A2 B1 B2}
      (R: rel σ1 σ2)
      (Q: rel (σ1 * A1) (σ2 * B1))
      (S: rel (σ1 * A2) (σ2 * B2))
      (p1: prog σ1 A1) (p2: A1 -> prog σ1 A2) (q1: prog σ2 B1) (q2: B1 -> prog σ2 B2),
      {{↑R}}(p1,q1){{Q}} ->
      (forall a b, {{REL Q a b}}(p2 a, q2 b){{S}}) -> 
      {{↑R}}
        (fun s1 => '(s2,a1) <- p1 s1;; p2 a1 s2,
                fun s1 => '(s2,b1) <- q1 s1;; q2 b1 s2)
        {{S}}.
  Proof using.
    intros * H1 H2.
    intros s1 s2 PRE; specialize (H1 _ _ PRE).
    destruct s1 as [s1 []], s2 as [s2 []]; cbn.
    eapply eutt_clo_bind; eauto.
    intros [s1' ?] [s2' ?] PRE'.
    specialize (H2 a b (s1', a) (s2', b)). cbn in H2.
    apply H2. repeat split; auto.
  Qed.

  (* Alternative solution for the general bind case. Looks needlessly more complex at first glance *)
  Notation "'[[' P ']]' '(' p ',' q ')' '[[' Q ']]'" :=
    (forall s1 s2, P s1 s2 -> eutt Q (p (snd s1) (fst s1)) (q (snd s2) (fst s2))).
  
  Lemma consequence_state_bind':
    forall {A1 A2 B1 B2}
      (R: rel σ1 σ2)
      (Q: rel (σ1 * A1) (σ2 * B1))
      (S: rel (σ1 * A2) (σ2 * B2))
      (p1: prog σ1 A1) (p2: A1 -> prog σ1 A2) (q1: prog σ2 B1) (q2: B1 -> prog σ2 B2),
      [[↑ R]] (fun _ => p1, fun _ => q1) [[Q]] ->
      [[ Q ]] (p2, q2) [[S]] ->
      (* ---------------------------------- *)
      [[↑R]]
        (fun _ s1 => '(s2,a) <- p1 s1 ;; p2 a s2,
                  fun _ s1 => '(s2,b) <- q1 s1 ;; q2 b s2)
        [[S]].
  Proof using.
    intros * H1 H2.
    intros s1 s2 PRE; specialize (H1 _ _ PRE).
    destruct s1 as [s1 ()], s2 as [s2 ()]; cbn.
    eapply eutt_clo_bind; eauto.
    intros [s1' ?] [s2' ?] PRE'.
    apply (H2 _ _ PRE').
  Qed.

End State.

