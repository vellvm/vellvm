From Coq Require Import Ensembles Setoid Morphisms RelationClasses Logic.Classical_Prop.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad
     Structures.MonadTrans
     Data.Monads.EitherMonad.

From ITree Require Import
     Basics.Basics
     ITreeDefinition
     Eq.Eq
     Eq.UpToTaus
     ITree
     Basics.Monad
     Core.ITreeMonad
     CategoryKleisli
     CategoryKleisliFacts
     KTree
     KTreeFacts.

From Paco Require Import paco.

Import MonadNotation.
Import CatNotations.
Local Open Scope monad_scope.
Local Open Scope cat_scope.

Section PropMonad.

  Definition PropT (E: Type -> Type) (X: Type): Type :=
    itree E X -> Prop.

  Global Instance Functor_Prop {E}
    : Functor (PropT E) :=
    {| fmap := fun A B f PA b => exists (a: itree E A), PA a /\ b = fmap f a |}.

  Inductive Returns {E} {A: Type} (a: A) : itree E A -> Prop :=
  | ReturnsRet: forall t, t ≈ Ret a -> Returns a t
  | ReturnsTau: forall t u, t ≈ Tau u -> Returns a u -> Returns a t
  | ReturnsVis: forall {X} (e: E X) (x: X) t k, t ≈ Vis e k -> Returns a (k x) -> Returns a t
  .
  Hint Constructors Returns: core.

  Definition subtree {E} {A B} (ta : itree E A) (tb : itree E B) := exists (k : A -> itree E B), tb ≈ bind ta k.

  Definition bind_PropT {E} :=
    fun A B (PA: PropT E A) (K: A -> PropT E B) (tb: itree E B) =>
      exists (ta: itree E A) (k: A -> itree E B),
        PA ta /\
        tb ≈ bind ta k /\
        (forall a, Returns a ta -> K a (k a)).

  Definition bind_PropT_stronger {E} :=
    fun A B (PA: PropT E A) (K: A -> PropT E B) (tb: itree E B) =>
      exists (ta: itree E A) (k: A -> itree E B),
        PA ta /\
        tb ≈ bind ta k /\
        (forall a, Returns a ta -> K a (k a)).


  
  (* BOGUS "CAST" to test hypotheses in bind_bind *)
  Lemma bind_PropT_bind_PropT_stronger {E}:
    forall A B PA K (tb : itree E B), bind_PropT A B PA K tb <-> bind_PropT_stronger A B PA K tb.
  Proof.
  Admitted.

  
  Definition bind_PropT' {E} := 
    fun A B (PA: PropT E A) (K: A -> PropT E B) (tb: itree E B) =>
      exists (ta: itree E A),  PA ta /\
                          ((exists (k: A -> itree E B),
                               (forall a, Returns a ta -> K a (k a))
                               /\ tb ≈ bind ta k)
                           \/ (forall k, (forall a, K a (k a)) /\ tb ≈ bind ta k)).

  (* Definition bind_PropT {E} := *)
  (*   fun A B (PA: PropT E A) (K: A -> PropT E B) (tb: itree E B) => *)
  (*     exists (ta: itree E A) (k: A -> itree E B), *)
  (*       (exists a, Returns a ta /\ *)
  (*             PA ta /\ tb ≈ bind ta k /\ *)
  (*             (forall a', Returns a' ta -> K a' (k a'))). *)
        (* (~ (exists a, Returns a ta)).  *)
  (* SAZ: Here is the proof that the two version of bind are logically equivalent, so
     it should not matter which one we use. Since bind_PropT has fewer cases, we should
     use it.*)
  Lemma bind_PropT_bind_PropT' {E}:
    forall A B PA K (tb : itree E B), bind_PropT A B PA K tb <-> bind_PropT' A B PA K tb.
  Proof.
    intros. split.
    intros.
    - red. red in H.
      destruct H as (ta & ka & HPA & eq & HR).
      exists ta. split; auto.
      left.  exists ka. split; auto.
    - intros.
      red. red in H.
      destruct H as  (ta & EQ1 & [(k & KA & EQ2) | HX]).
      + exists ta. exists k. auto.
      + exists ta. exists (fun _ => ITree.spin).
        split; auto.
        specialize (HX (fun _ => ITree.spin)).
        destruct HX as (HA & H).
        split; auto.
  Qed.

  Definition eutt_closed {E X} (P: itree E X -> Prop): Prop :=
    Proper (eutt eq ==> iff) P.

  Global Polymorphic Instance EqM_PropT {E} : EqM (PropT E) :=
    fun a PA PA' =>
      (forall x y, x ≈ y -> (PA x <-> PA' y)) /\
      eutt_closed PA /\ eutt_closed PA'.

  Global Instance Monad_Prop {E} : Monad (PropT E) :=
    {|
      ret := fun _ x y => y ≈ ret x
      ; bind := bind_PropT
    |}.

  Inductive iter_ {I E R} (F : (I -> PropT E (I + R)) -> (I + R) -> itree E R -> Prop)
            (body : I -> PropT E (I + R)) (i : I + R)
            (t : itree E R) : Prop :=
  | step_done : forall r, i = inr r ->
                     iter_ F body i t
  | step_iter : forall (j : I) (k : I -> itree E (I + R)),
                  i = inl j ->
                  t ≈ iter k j ->
                  (forall x, body x (k x)) ->
                  iter_ F body i t.

  (* Definition iter__ {I E R} *)
  (*            (body : I -> PropT E (I + R)) (i : I + R) (t : itree E R) : Prop := *)
  (*   paco3 iter_ bot3 body i t. *)

  (* Definition iter_PropT {E R I} : (I -> PropT E (I + R)) -> I -> itree E R -> Prop := *)
  (*   fun step i => iter__ step (inl i). *)

  (* Global Polymorphic Instance MonadIter_Prop {E} : MonadIter (PropT E) := *)
  (*   @iter_PropT E. *)
  (* Global Instance IterUnfold_PropT {E} : IterUnfold (Kleisli (PropT E)) sum. *)
  (* Proof. *)
  (*   constructor. *)
  (*   intros x y EQ. split. *)
  (*   - intros H. repeat red. *)
  (*     inversion H. admit. *)
  (*   - generalize dependent x. *)
  (*     generalize dependent y. *)
  (*     pcofix CIH. intros. *)
  (*     pstep. epose proof @step_iter. *)
  (*     repeat red in H0. edestruct H0 as (? & ? & ? & ? & ?). *)
  (*     clear H0. *)
  (*     specialize (H _ _ _ (upaco3 iter_ r) f (inl a0)). *)
  (*     specialize (H x a0). *)
  (*     eapply H. reflexivity. rewrite EQ. rewrite H2. admit. *)
  (*     intros. repeat red in H3. *)
  (*   intros x y EQ. *)
  (*   split. *)
  (*   intros H.  *)

  Definition iter_cont {I E R} (step' : I -> itree E (I + R)) :
    I + R -> itree E R :=
      (ITree._iter (fun t : itree E R => Tau t) (ITree.iter step')).

  Global Polymorphic Instance MonadIter_Prop {E} : MonadIter (PropT E) :=
    fun R I (step : I -> PropT E (I + R)) i =>
      fun (r : itree E R) =>
        (exists (step' : I -> (itree E (I + R)%type)),
                ITree.bind (step' i) (@iter_cont I E R step') ≈ r /\
                (forall j, step j (step' j))).

(* exists a, Returns a (step' i) /\ *)
(* \/ (~ (exists a, Returns a r) /\ step i r). *)

  From ITree Require Import Basics.CategoryTheory.
  From Coq Require Import Program.Tactics.

  Lemma eqit_bind_Returns_inv {E} {R S T} (RS : R -> S -> Prop) 
        (t : itree E T)  (k1: T -> itree E R) (k2 : T -> itree E S) :
    (eutt RS  (ITree.bind t k1) (ITree.bind t k2)) ->
    (forall r, Returns r t -> eutt RS (k1 r) (k2 r)).
  Proof.
    intros EQIT r HRET.
    revert R S RS k1 k2 EQIT.
    induction HRET; intros.
    - rewrite H in EQIT.
      do 2 rewrite Eq.bind_ret_l in EQIT.
      assumption.
    - rewrite tau_eutt in H. rewrite H in EQIT.
      eapply IHHRET; eauto.
    - rewrite H in EQIT.
      do 2 rewrite Eq.bind_vis in EQIT.
      repeat red in EQIT. punfold EQIT.
      inversion EQIT.
      apply inj_pair2 in H2.
      apply inj_pair2 in H3.
      apply inj_pair2 in H4.
      apply inj_pair2 in H5.
      subst.
      eapply IHHRET.
      specialize (REL x).
      red in REL.
      pclearbot.
      apply REL.
  Qed.

  Lemma bind_Returns_l {E A B} :
    forall a (ma : itree E A) (k : A -> itree E B),
    Returns a ma ->
    ITree.bind ma k ≈ k a.
  Proof.
  Admitted.


  Definition divergent {E A} (ta : itree E A) := (forall k , ta ≈ bind ta k).

  Lemma Returns_divergent {E A}:
    (forall (ta : itree E A), not (exists a, Returns a ta) -> divergent ta).
  Proof.
    intros. red. intros. red in H.
    unfold bind, Monad_itree.
    generalize dependent ta. pcofix CIH. cbn. pstep. unfold eqit_.
    intros. remember (observe ta). destruct i.
    - destruct H0. assert (ta ≈ Ret r0). rewrite Heqi.
      rewrite <- itree_eta. reflexivity. exists r0. constructor. auto.
    - intros. rewrite unfold_bind_. cbn. rewrite <- Heqi. cbn.
      constructor. right. apply CIH. intros. destruct H. destruct H0.
      assert (ta ≈ Tau t). rewrite Heqi. rewrite <- itree_eta; reflexivity.
      eapply ReturnsTau in H; eauto.
    - rewrite unfold_bind_. cbn. rewrite <- Heqi. cbn. constructor. intros.
      unfold id. right. apply CIH. intros. destruct H. destruct H0.
      assert (ta ≈ Vis e k0). rewrite Heqi. rewrite <- itree_eta; reflexivity.
      eapply ReturnsVis in H; eauto.
  Qed.

  Definition divergent_cont {E A B} (ta : itree E A) :=
    (forall (k1 : A -> itree E B) (k2 : A -> itree E B) , bind ta k1 ≈ bind ta k2).

  Lemma Returns_divergent_cont {E A B}:
    (forall (ta : itree E A), not (exists a, Returns a ta) -> @divergent_cont _ A B ta).
  Proof.
  Admitted.

  Global Instance IterUnfold_PropT {E} : IterUnfold (Kleisli (PropT E)) sum.
  Proof.
    intros A B f. split; [ intros x y EQ | ]; split.
    - intros H. repeat red in H. repeat red.
      destruct H as (step & H).
      exists (step a). exists (iter_cont step).
      destruct H as (BIND & PRED). split. auto.
      split. rewrite <- EQ.
      rewrite BIND. reflexivity.
      intros. repeat red.
      destruct a0.
      + cbn. repeat red. unfold iter_cont.
        setoid_rewrite tau_eutt at 2.
        exists step.
        setoid_rewrite unfold_iter. split; auto. reflexivity.
      + cbn. reflexivity.
    - intros H. repeat red in H. repeat red.
      destruct H as (FIRST & CONT & PRED_FIRST & EQ_Y & PRED).
      unfold iter_cont.
      setoid_rewrite EQ. clear EQ x.
      assert ((exists a, Returns a FIRST) \/ ~ (exists a, Returns a FIRST)).
      apply classic.
      destruct H.
      + destruct H.
        specialize (PRED _ H).
        setoid_rewrite EQ_Y. clear EQ_Y.
        cbn. setoid_rewrite bind_Returns_l. 2 : exact H.
        repeat red in PRED. destruct x.
        * repeat red in PRED.
          destruct PRED as (step & H_BIND & H_PRED).
          unfold iter_cont in H_BIND.
          setoid_rewrite <- H_BIND.
          (* We want an unfolded version of step. *)
          eexists ?[step]. split; auto. admit.
        * cbn in PRED. setoid_rewrite PRED. admit.
      + apply (Returns_divergent_cont (B := B)) in H. red in H.
        cbn in H. setoid_rewrite EQ_Y. cbn. setoid_rewrite <- H.
        (* It doesn't make sense in terms of unfolding a loop body, that
           the first part must return a value...
         *)
        exists (fun x => FIRST). split; auto. admit.
    - repeat intro. repeat red. intuition.
      repeat red in H0.
      repeat red. setoid_rewrite <- H. auto.
      repeat red in H0.
      repeat red. setoid_rewrite H. auto.
    - repeat intro. repeat red. intuition.
      repeat red in H0.
      repeat red. setoid_rewrite <- H. auto.
      repeat red in H0.
      repeat red. setoid_rewrite H. auto.
  Admitted.

  (* SAZ: maybe define directly by coinduction  *)
  (* Global Polymorphic Instance MonadIter_Prop {E} : MonadIter (PropT E) := *)
  (*   fun R I (step : I -> PropT E (I + R)) i => *)
  (*     fun (r : itree E R) => *)
  (*       (exists step' : I * nat -> (itree E (I + R)%type), *)
  (*           (forall (j : I) (n : nat), *)
  (*              (* a, *) *)
  (*               (* Returns a (step' (j, n)) -> *) *)
  (*                 step j (step' (j, n))) /\ *)
  (*           (let body := *)
  (*             fun '(x, k) => *)
  (*               bind (step' (x, k)) *)
  (*                 (fun ir : I + R => *)
  (*                   match ir with *)
  (*                   | inl i0 => ret (inl (i0, S k)) *)
  (*                   | inr r0 => ret (inr r0) *)
  (*                   end) in *)

  (*            CategoryOps.iter body (i, 0)) ≈ r). *)

  Definition interp_prop {E F} (h : E ~> PropT F) :
    itree E ~> PropT F := interp h.

  Definition singletonT {E}: itree E ~> PropT E :=
    fun R t t' => t' ≈ t.

End PropMonad.


Section IterLaws.


  Lemma Returns_divergent' {E A B}:
    (forall (ta : itree E A) (tb : itree E B),
        not (exists a, Returns a ta) -> not (exists b, Returns b tb) ->
        forall (k : A -> itree E B), tb ≈ bind ta k).
  Proof.
    intros. red. intros. red in H.
    unfold bind, Monad_itree.
    generalize dependent ta. pcofix CIH. cbn. pstep. unfold eqit_.
    intros. remember (observe ta). destruct i.
    - destruct H0. assert (ta ≈ Ret r0). rewrite Heqi.
      rewrite <- itree_eta. reflexivity.
  Admitted.

  Ltac simpl_iter :=
      unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree.

  Definition g {a b : Type} {E} (x0 : a * nat -> itree E (a + b)) (a1 : a)
    := (fun '(x, k) =>
            bind (x0 (x, k))
                (fun ir : a + b =>
                    match ir with
                    | inl i0 => ret (inl (i0, k))
                    | inr r0 => ret (inr r0)
                    end)).

  Definition f {a b : Type} {E} : a * nat  -> itree E (a * nat + b) :=
    fun '(x, k) => ret (inl ((x, S k))).

  Lemma iter_succ_dinatural:
    forall {a b : Type} {E} (x0 : a * nat -> itree E (a + b)) (a1 : a),
      iter (C := Kleisli (itree E)) (bif := sum)
           (f >>> case_ (g x0 a1) inr_)
       ⩯
       f >>> case_ (iter (C := Kleisli (itree E)) (bif := sum) ((g x0 a1) >>> (case_ f inr_))) (id_ _).
  Proof.
    intros. rewrite iter_dinatural. reflexivity.
  Qed.

  Lemma iter_eq_start_index:
    forall (a b : Type) (E : Type -> Type) (x0 : a * nat -> itree E (a + b)) (a1 : a),
      iter (C := Kleisli (itree E)) (bif := sum)
        (fun '(x, k) =>
            bind (x0 (x, S k))
                (fun ir : a + b =>
                    match ir with
                    | inl i0 => ret (inl (i0, S k))
                    | inr r0 => ret (inr r0)
                    end)) (a1, 0)
        ≈ iter (C := Kleisli (itree E)) (bif := sum)
        (fun '(x', k) =>
            bind (x0 (x', k))
                (fun ir : a + b =>
                    match ir with
                    | inl i0 => ret (inl (i0, S k))
                    | inr r0 => ret (inr r0)
                    end)) (a1, 1).
  Proof.
    intros a b m x0 a1.
    pose proof (iter_succ_dinatural x0 a1) as H0.
    specialize (H0 (a1, 0)).
    unfold f at 1, g at 1 in H0.
    unfold cat at 1, Cat_Kleisli at 1 in H0.
    match goal with
    | H : ?body1 ≈ _ |- ?body2 ≈ _ => remember body1 as s1;
                                                 remember body2 as s2
    end.
    assert (s1 ≈ s2). {
      subst.
      match goal with
      | |- iter ?body1 _ ≈ iter ?body2 _ => remember body1 as k1;
                                            remember body2 as k2
      end.
      assert (iter k1 ⩯ iter k2). {
        eapply iterative_proper_iter.
        subst. do 3 red. intros.
        destruct a0; rewrite bind_ret_l; cbn.
        reflexivity.
      }
      do 3 red in H.
      apply H.
    }
    rewrite <- H. subst. clear H. rewrite H0.
    unfold f, g.
    unfold cat, Cat_Kleisli. rewrite bind_ret_l.
    cbn.
    match goal with
    | |- iter ?body1 _ ≈ iter ?body2 _ => remember body1 as i1; remember body2 as i2
     end.
    assert (iter i1 ⩯ iter i2). {
      eapply iterative_proper_iter.
      subst.
      do 3 red. intros.
      destruct a0. rewrite Eq.bind_bind.
      eapply eutt_clo_bind. reflexivity.
      intros. rewrite H. destruct u2;
      rewrite Eq.bind_ret_l; cbn; reflexivity.
    }
    do 3 red in H.
    apply H.
  Qed.

  Lemma simplify_bind_match {E A B}:
    forall x BODY,
     ITree.bind
       match x with
       | inl i0 => Ret (inl (i0, 1))
       | inr r0 => Ret (inr r0)
       end
       (ITree._iter (fun t : itree E B => Tau t)
          (ITree.iter
             (fun '(x, k) =>
              ITree.bind (BODY (x, k))
                (fun ir : A + B =>
                 match ir with
                 | inl i0 => Ret (inl (i0, S k))
                 | inr r0 => Ret (inr r0)
                 end))))
      ≈
      match x with
      | inl l =>
          (ITree.iter
              (fun '(x0, k) =>
              ITree.bind (BODY (x0, k))
                (fun ir : A + B =>
                  match ir with
                  | inl i0 => Ret (inl (i0, S k))
                  | inr r0 => Ret (inr r0)
                  end))) (l, 1)
      | inr r => Ret r end.
  Proof.
    intros. destruct x. rewrite Eq.bind_ret_l. cbn. rewrite tau_eutt.
    reflexivity. rewrite Eq.bind_ret_l. reflexivity.
  Qed.

  Global Instance IterUnfold_PropT {E} : IterUnfold (Kleisli (PropT E)) sum.
    intros A B Pstep a.
    repeat red. split; [ intros x y EQ | ]; split.
  - (* Show that there is some looping itree body that Pstep can unfold into. *)
    intros LOOP. repeat red. repeat red in LOOP.
    setoid_rewrite <- EQ. clear EQ y.
    destruct LOOP as (BODY & PROP & RESULT).
    exists (BODY (a, 0)).
    exists (fun x : A + B =>
         match x with
         | inl l =>
              (ITree.iter
                  (fun '(x0, k) =>
                  ITree.bind (BODY (x0, k))
                    (fun ir : A + B =>
                      match ir with
                      | inl i0 => Ret (inl (i0, S k))
                      | inr r0 => Ret (inr r0)
                      end))) (l, 1)
         | inr r => Ret r end).
    split. auto. split.
    + (* Proposition holds over first part of computation. *)
      rewrite <- RESULT. simpl_iter.
      rewrite unfold_iter. cbn. rewrite Eq.bind_bind.
      eapply eutt_clo_bind. reflexivity.
      intros. rewrite <- H. destruct u1. rewrite Eq.bind_ret_l.
      cbn. rewrite tau_eutt. reflexivity.
      rewrite Eq.bind_ret_l. cbn. reflexivity.
    + (* There is some continuation that satisfies the computation. *)
      intros ab RET. repeat red.
      destruct ab eqn: H_ab.
      * (* Keep loopin' *)
        cbn. repeat red.
        exists (fun x : A * nat => BODY (fst x, S( snd x ))). split; auto.
        simpl_iter. cbn.
        (* rewrite Eq.bind_ret_l. cbn. rewrite tau_eutt. *)
        pose proof iter_eq_start_index.
        unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree in H.
        specialize (H _ _ _ BODY). apply H.
      * cbn. reflexivity.
  - (* An unfolded PropT implies a folded loop. *)
    (*      cat Pstep (case_ (iter Pstep) (id_ B)) a y -> iter Pstep a x      *)
    cbn. unfold bind_PropT.

    intros UNFOLD. repeat red. setoid_rewrite EQ. clear EQ x.
    destruct UNFOLD as (FIRST & CONTINUATION & FIRST_PROP & BIND_EQ &
                        CONT_PROP).
    (* Perhaps Returns should be a coinductive proposition?  =>
       Tried short experiment above, was not working out cleanly..
       Not convinced that a coinductive definition will give us more expressive
       power. We seem to be missing some other kind of information.
     *)

    simpl_iter. setoid_rewrite unfold_iter.
    setoid_rewrite BIND_EQ.
    eexists ?[step'].
    assert ((?step' (a, 0)) ≈ FIRST) as H. admit.
    split.
    (* IDEA? : Don't hold propositions holding over all index j, but
       up to a finite unfolding of the step' body. *)
    + intros.
      admit.
    + cbn. rewrite Eq.bind_bind.
      setoid_rewrite simplify_bind_match.
      eapply eutt_clo_bind. rewrite H. reflexivity.
      repeat intro. clear H0.
      destruct u1.
      * rewrite unfold_iter.
        rewrite Eq.bind_bind.
        destruct (observe FIRST) eqn: OBSERVE_STEP; cbn.
        -- admit.
        -- admit.
        -- admit.
      * exfalso. (* Should never be reached.... *) admit.
   (* + eapply eutt_clo_bind. reflexivity. intros. rewrite H. *)
   (*    clear H u1. destruct u2. *)
   (*    * rewrite Eq.bind_ret_l. cbn. rewrite tau_eutt. *)
   (*      rewrite unfold_iter. cbn. rewrite Eq.bind_bind. *)

    (* If we unfold a loop, the idea should be that the unfolded part is going
     * to ... terminate, right? It isn't necessarily a return, though. *)
    (* assert (FIRST_SHOULD_RETURN: exists a : A + B, Returns a FIRST). admit. *)
    (* destruct FIRST_SHOULD_RETURN as (AB & RETURN_FIRST). *)
    (* specialize (CONT_PROP _ RETURN_FIRST). *)

    (* I think that what we need to do, actually, is to encode "Returns" in
       the iter instance. This is because the definition of "iter" needs to
       coincide with how "bind" is defined for PropT.

       Let's think about how to define an "iterative PropT", by example.

     *)

    (* ... For this direction, it seems necessary to index the loop body, since
     the unfolded iter case is strictly more expressive than the folded body.

     Another idea suggestion, from Yannick: try expressing with (option itree),
     intuitively this makes a lot of sense since the empty predicate cannot
     be expressed by an itree, and there might be indices in the loop body
     that map to the empty predicate.
     *)
  - repeat intro. repeat red.
    simpl_iter. unfold MonadIter_Prop. setoid_rewrite H.
    auto.
  - repeat intro. repeat red.
    unfold cat, Cat_Kleisli. cbn. unfold bind_PropT.
    intuition.
    setoid_rewrite <- H. auto.
    setoid_rewrite H. auto.
  Admitted.


  Global Instance IterDinatural_PropT {E} : IterDinatural (Kleisli (PropT E)) sum.
  intros A B C f g.
  split; [intros x y EQ | ]; split.
  - intros H. repeat red. repeat red in H. setoid_rewrite <- EQ. clear EQ y.
    destruct H as (STEP & FST & CONT).
    repeat red in FST.
    specialize (FST a 0).
    edestruct FST as (ta & k & H_fa & H_step & H_cont). clear FST.
    exists ta.
    unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree in CONT.
    rewrite unfold_iter in CONT. cbn in CONT.
    rewrite Eq.bind_bind in CONT.
    (* exists (fun bc => ITree.bind *)
    (*             (match r with *)
    (*                inl *)
    (*             ) *)
    (*   ) *)
    (* bind t *)
    (* exists *)
    admit.
  - admit.
  - repeat red. intros. intuition.
    repeat red. setoid_rewrite <- H. auto.
    repeat red. setoid_rewrite H. auto.
  - repeat red. intros. intuition.
    repeat red. setoid_rewrite <- H. auto.
    repeat red. setoid_rewrite H. auto.
  Admitted.

  Global Instance IterCodiagonal_PropT {E} :  IterCodiagonal (Kleisli (PropT E)) sum.
  Admitted.


End IterLaws.  


Section MonadLaws.

  Global Instance Returns_eutt {E A} a: Proper (eutt eq ==> iff) (@Returns E A a).
  Proof.
    repeat intro; split; intros HRet.
    - revert y H. induction HRet; intros.
      constructor; rewrite <- H, H0; reflexivity.
      apply IHHRet, eqit_inv_tauL; auto.
      rewrite <- H0. rewrite H. reflexivity.
      econstructor 3; [rewrite <- H0, H; reflexivity | apply IHHRet; reflexivity].
    - revert x H; induction HRet; intros ? EQ.
      constructor; rewrite EQ; eauto.
      apply IHHRet, eqit_inv_tauR; auto.
      rewrite EQ. rewrite <- H. reflexivity.
      econstructor 3; [rewrite EQ, H; reflexivity | apply IHHRet; reflexivity].
  Qed.


  Definition EqM_PropT' {E} : EqM (PropT E) :=
    fun a PA PA' =>
      (forall x, (PA x -> exists y, x ≈ y /\ PA' y)) /\
      (forall y, (PA' y -> exists x, x ≈ y /\ PA x)) /\
      eutt_closed PA /\ eutt_closed PA'.

  Lemma EqM_PropT'_Eqm_PropT : forall E a PA PA', @EqM_PropT E a PA PA' -> EqM_PropT' a PA PA'.
  Proof.
    intros.
    red.
    red in H.
    destruct H as (HXY & EPA & EPA').
    split.
    intros.
    exists x. split; [reflexivity|]. specialize (HXY x x).  apply HXY. reflexivity. assumption.
    split; try tauto.
    intros. 
    exists y. split; [reflexivity|]. specialize (HXY y y).  apply HXY. reflexivity. assumption.
 Qed.

  
  Lemma eutt_ret_vis_abs: forall {X Y E} (x: X) (e: E Y) k, Ret x ≈ Vis e k -> False.
  Proof.
    intros.
    punfold H; inv H.
  Qed.

  Lemma Returns_Ret_ : forall E A (a x : A) (t:itree E A), t ≈ Ret x -> Returns a t -> x = a.
  Proof.
    intros E A a x t eq H. 
    induction H.
    - rewrite eq in H. eapply eutt_inv_ret. apply H.
     - rewrite tau_eutt in H. rewrite <- H in IHReturns. apply IHReturns. assumption.
    - rewrite eq in H. apply eqit_inv_ret_vis in H. contradiction.
  Qed.

  Lemma Returns_Ret :  forall E A (a x : A), Returns a ((Ret x) : itree E A) -> x = a.
  Proof.
    intros.  eapply Returns_Ret_. 2: eassumption. reflexivity.
  Qed.

  Lemma ret_bind: forall {E} (a b : Type) (f : a -> PropT E b) (x : a),
      eutt_closed (f x) ->
      eqm (bind (ret x) f) (f x).
  Proof.
    intros.
    split; [| split].
    - intros t t' eq; split; intros eqtt'.
      * cbn in *.
        repeat red in eqtt'.
        destruct eqtt' as (ta & k & EQ1 & EQ2 & KA).
      + unfold bind, Monad_itree in EQ2. rewrite EQ1, Eq.bind_ret_l, eq in EQ2.
        eapply H; [apply EQ2 | apply KA].
        constructor 1; eauto.
     * cbn.
       exists (Ret x), (fun _ => t); split; [reflexivity|]; split.
        + unfold bind, Monad_itree. rewrite Eq.bind_ret_l; reflexivity.
        + intros.
          apply Returns_Ret in H0. subst. red in H. rewrite eq.
          assumption.

    - intros t t' EQ; cbn; split; intros HX.
      * destruct HX as (ta & k & EQ1 & EQ2 & KA).
        exists (Ret x), (fun _ => t); split; [reflexivity |]; split.
        --  unfold bind, Monad_itree. rewrite Eq.bind_ret_l. symmetry. assumption.
        -- 
          intros ? RET; inv RET.
          2: { rewrite tau_eutt in H0. rewrite <- H0 in H1. apply Returns_Ret in H1. subst.
               red in H. rewrite EQ2. rewrite EQ1.
               unfold bind, Monad_itree.
               rewrite Eq.bind_ret_l. apply KA. rewrite EQ1. constructor. reflexivity. }
          2: exfalso; eapply eutt_ret_vis_abs; eauto.
          apply eqit_inv_ret in H0; subst.
          eapply H. rewrite EQ1 in EQ2.
          unfold bind, Monad_itree in EQ2.
             rewrite Eq.bind_ret_l in EQ2. apply EQ2.
             apply KA; rewrite EQ1; constructor; reflexivity.

      * destruct HX as (ta & k & EQ1 & EQ2 & KA).
        exists (Ret x), (fun _ => t); split; [reflexivity |]; split.
        --  unfold bind, Monad_itree. rewrite Eq.bind_ret_l. reflexivity.
        -- 
          intros ? RET; inv RET.
          2: { rewrite tau_eutt in H0. rewrite <- H0 in H1. apply Returns_Ret in H1. subst.
               red in H. rewrite EQ. rewrite EQ2. rewrite EQ1.
               unfold bind, Monad_itree.
               rewrite Eq.bind_ret_l. apply KA; rewrite EQ1; constructor 1; reflexivity. 
          }
          2: exfalso; eapply eutt_ret_vis_abs; eauto.
          
          apply eqit_inv_ret in H0; subst.
          red in H.
          rewrite EQ, EQ2, EQ1.
          unfold bind, Monad_itree.
          rewrite Eq.bind_ret_l.
          apply KA; rewrite EQ1; constructor; reflexivity.
    - assumption.
  Qed.
  
  Section ReturnsBind.

    Context {E : Type -> Type} {R S : Type}. 

    Import ITreeNotations.
    Local Open Scope itree.

    Inductive eqit_Returns_bind_clo b1 b2 (r : itree E R -> itree E S -> Prop) :
      itree E R -> itree E S -> Prop :=
    | pbc_intro_h U (t1 t2: itree E U) (k1 : U -> itree E R) (k2 : U -> itree E S)
                  (EQV: eqit eq b1 b2 t1 t2)
                  (REL: forall u, Returns u t1 -> r (k1 u) (k2 u))
      : eqit_Returns_bind_clo b1 b2 r (ITree.bind t1 k1) (ITree.bind t2 k2)
    .
    Hint Constructors eqit_Returns_bind_clo: core.

    Lemma eqit_Returns_clo_bind  (RS : R -> S -> Prop) b1 b2 vclo
          (MON: monotone2 vclo)
          (CMP: compose (eqitC RS b1 b2) vclo <3= compose vclo (eqitC RS b1 b2))
          (ID: id <3= vclo):
      eqit_Returns_bind_clo b1 b2 <3= gupaco2 (eqit_ RS b1 b2 vclo) (eqitC RS b1 b2).
    Proof.
      gcofix CIH. intros. destruct PR.
      guclo eqit_clo_trans.
      econstructor; auto_ctrans_eq; try (rewrite (itree_eta (x <- _;; _ x)), unfold_bind; reflexivity).
      punfold EQV. unfold_eqit.
      genobs t1 ot1.
      genobs t2 ot2.
      hinduction EQV before CIH; intros; pclearbot.
      - guclo eqit_clo_trans.
        econstructor; auto_ctrans_eq; try (rewrite <- !itree_eta; reflexivity).
        gbase; cbn.
        apply REL0.
        rewrite itree_eta, <- Heqot1; constructor; reflexivity.
      - gstep. econstructor.
        gbase.
        apply CIH.
        constructor; auto.
        intros u HR.
        apply REL0.
        rewrite itree_eta,  <- Heqot1.  econstructor 2. reflexivity. assumption.
      - gstep. econstructor.
        intros; apply ID; unfold id.
        gbase.
        apply CIH.
        constructor; auto.
        intros ? HR; apply REL0.
        rewrite itree_eta, <- Heqot1.
        econstructor 3; eauto; reflexivity.
      - destruct b1; try discriminate.
        guclo eqit_clo_trans.
        econstructor.
        3:{ eapply IHEQV; eauto.
            intros ? HR; apply REL.
            rewrite itree_eta, <- Heqot1; econstructor 2. reflexivity. eauto.
        }
        3,4:auto_ctrans_eq.
        2: reflexivity.
        eapply eqit_tauL. rewrite unfold_bind, <-itree_eta. reflexivity.
      - destruct b2; try discriminate.
        guclo eqit_clo_trans.
        econstructor; auto_ctrans_eq; cycle -1; eauto; try reflexivity.
        eapply eqit_tauL. rewrite unfold_bind, <-itree_eta. reflexivity.
    Qed.

  End ReturnsBind.

    Lemma eqit_Returns_bind' {E} {R} {T} b1 b2
          (t1 t2: itree E T) (k1 k2: T -> itree E R) :
      eqit eq b1 b2 t1 t2 ->
      (forall r, Returns r t1 -> eqit eq b1 b2 (k1 r) (k2 r)) ->
      @eqit E _ _ eq b1 b2 (ITree.bind t1 k1) (ITree.bind t2 k2).
    Proof.
      intros. ginit. guclo (@eqit_Returns_clo_bind E R R eq). unfold eqit in *.
      econstructor; eauto with paco.
    Qed.

    Lemma eqit_Returns_bind'' {E} {R S} {T} (RS : R -> S -> Prop) b1 b2
          (t1 t2: itree E T) (k1: T -> itree E R) (k2 : T -> itree E S) :
      eqit eq b1 b2 t1 t2 ->
      (forall r, Returns r t1 -> eqit RS b1 b2 (k1 r) (k2 r)) ->
      @eqit E _ _ RS b1 b2 (ITree.bind t1 k1) (ITree.bind t2 k2).
    Proof.
      intros. ginit. guclo (@eqit_Returns_clo_bind E R S RS). unfold eqit in *.
      econstructor; eauto with paco.
    Qed.


   Global Instance bind_PropT_Proper {E} {A B} :
     Proper (eqm ==> (eq ==> eqm) ==> eutt eq ==> iff) (@bind_PropT E A B).
   Proof.
     repeat red; intros PA1 PA2 EQP K1 K2 EQK t1 t2 EQt; split; intros H.
     - destruct H as (ta & k & HA & eq & HK).
       red.
       exists ta, k. split.
       + destruct EQP. apply (H ta ta). reflexivity. assumption.
       + split. rewrite <- EQt. assumption. intros.
         repeat red in EQK.  specialize (EQK a a eq_refl). destruct EQK.
         rewrite <- H0. apply HK. assumption. reflexivity.
    -  destruct H as (ta & k & HA & eq & HK).
       red.
       exists ta, k. split.
       + destruct EQP. apply (H ta ta). reflexivity. assumption.
       + split. rewrite EQt. assumption. intros.
         repeat red in EQK.  specialize (EQK a a eq_refl). destruct EQK.
         rewrite H0. apply HK. assumption. reflexivity.
   Qed.

   Global Instance bind_Propt_Proper2 {E} {A B} (PA : PropT E A) (K : A -> PropT E B) :
     Proper (eutt eq ==> flip impl) (bind PA K).
   Proof.
     repeat red.
     intros.
     repeat red in H0.
     destruct H0 as (ta & k & HA & eq & HK).
     exists ta, k. split; auto. split. rewrite H; auto. assumption.
   Qed.

   
  Definition agrees_itree {E} {A} (ta1 : itree E A) (ta2 : itree E (A -> Prop)) :=
    eutt (fun a p => p a) ta1 ta2.
  
  Definition bind_stronger {E} := 
    fun A B (PA: PropT E A) (K: A -> PropT E B) (tb: itree E B) =>
      exists (ta: itree E A),  PA ta /\
                          (exists (k: A -> itree E B),
                               (agrees_itree (fmap k ta) (fmap K ta)
                               /\ tb ≈ bind ta k)).


  
  Lemma agree_itree_Returns : forall E A B (ta : itree E A) (K : A -> PropT E B) (k : A -> itree E B),
      (forall a, Returns a ta -> K a (k a)) <-> (agrees_itree (fmap k ta) (fmap K ta)).
  Proof.
    intros.
    split; intros.
    - cbn. red.
      unfold ITree.map.
      eapply eqit_Returns_bind''.
      + reflexivity.
      + intros. apply eqit_Ret. apply H. assumption.
    - revert B K k H.
      induction H0.
      + intros. cbn in H0. unfold agrees_itree in H0.
        unfold ITree.map in H0.
        rewrite H in H0.
        do 2 rewrite Eq.bind_ret_l in H0.
        apply Eq.eqit_Ret in H0. assumption.
      + intros.
        rewrite tau_eutt in H.
        unfold agrees_itree in H1.
        setoid_rewrite H in H1.
        eapply IHReturns. unfold agrees_itree.
        apply H1.
      + intros.
        apply IHReturns; clear IHReturns.
        unfold agrees_itree in *.
        setoid_rewrite H in H1.
        cbn in *. unfold ITree.map in *.
        repeat red in H1.
        punfold H1.
        inversion H1. cbn in *.
        subst.
        apply inj_pair2 in H4.
        apply inj_pair2 in H5.
        apply inj_pair2 in H6.
        apply inj_pair2 in H7.
        subst.
        
        
        apply eqit_Returns_bind''.
        * reflexivity.
        * intros. subst.
          apply Eq.eqit_Ret.
          specialize (REL x).
          red in REL. 
          pclearbot.
          apply eqit_bind_Returns_inv  with (r0:=r) in REL; auto.
          apply eqit_Ret in REL.
          assumption.
  Qed.
          
  
  Lemma distinguish_bind {E} {A B}
        (a : A)
        (ma : itree E A)
        (k1 k2 : A -> itree E B)
        (HRET : Returns a ma)
        (NEQ: ~((k1 a) ≈ (k2 a))) : 
    not ((ITree.bind ma k1) ≈ (ITree.bind ma k2)).
  Proof.
    intro HI.
    apply NEQ. clear NEQ.
    revert k1 k2 HI.
    induction HRET; intros.
    - rewrite H in HI. cbn in HI. rewrite Eq.bind_ret_l in HI. rewrite Eq.bind_ret_l in HI.
      assumption.
    - apply IHHRET. unfold bind, Monad_itree in HI.
      rewrite H in HI.
      do 2 rewrite Eq.bind_tau in HI.
      do 2 rewrite tau_eutt in HI. apply HI.
    - apply IHHRET. rewrite H in HI.
      do 2 rewrite bind_vis in HI.
      apply eqit_inv_vis in HI.
      destruct HI as (_ & HI).
      apply HI.
  Qed.
  

  Lemma not_Returns {E} {A B} : inhabited B ->
    forall (ta: itree E A), (exists tb, forall (k : A -> itree E B), tb ≈ bind ta k) -> forall (a:A), ~ Returns a ta.
  Proof.
    intros IB ta HX a HRet; inversion IB; clear IB.
    revert HX.
    induction HRet; intros (tb & HK).
    - setoid_rewrite H in HK.
      unfold bind, Monad_itree in HK.
      setoid_rewrite Eq.bind_ret_l in HK.
      pose (HK (fun _ => ret X)) as t2. cbn in t2.
      pose (HK (fun _ => ITree.spin)) as t3. cbn in t3.
      assert (Ret X ≈ (ITree.spin : itree E B)).
      rewrite <- t2. rewrite <- t3. reflexivity. apply eutt_Ret_spin_abs in H0. 
      auto.
    - apply IHHRet.
      exists tb. intros. 
      specialize (HK k).
      rewrite HK. unfold bind, Monad_itree.
      rewrite H. 
      rewrite bind_tau. apply tau_eutt.
    - setoid_rewrite H in HK; clear H t.
      pose (HK (fun _ => ret X)) as t2. cbn in t2.
      pose (HK (fun _ => ITree.spin)) as t3. cbn in t3.
      assert (ITree.bind (Vis e k) (fun _ : A => Ret X) ≈ ITree.bind (Vis e k) (fun _ : A => ITree.spin)).
      rewrite <- t2. rewrite <- t3.
      reflexivity.
      rewrite bind_vis in H. rewrite bind_vis in H.
      apply eqit_inv_vis in H.
      destruct H as (_ & H).
      specialize (H x).
      revert H.
      change (~((ITree.bind (k x) ( fun _ : A => Ret X)) ≈ ITree.bind (k x) (fun _ : A => ITree.spin))).
      eapply distinguish_bind. apply HRet.
      intro H. apply eutt_Ret_spin_abs in H. auto.
  Qed.      

  
  Lemma bind_ret: forall {E} (A : Type) (PA : PropT E A),
      eutt_closed PA ->
      eqm (bind PA (fun x => ret x)) PA.
  Proof.
    intros.
    split; [| split].
    + intros t t' eq; split; intros eqtt'.
      * cbn in *.
        destruct eqtt' as (ta & k & HPA & EQ & HRET).
        eapply H; [symmetry; eauto | clear eq t'].
        eapply H; [eauto | clear EQ t].
        eapply H; eauto.
        rewrite <- (bind_ret_r _ ta) at 2.
        apply eqit_Returns_bind'; [reflexivity |].
          intros.
          rewrite (HRET r); auto.
          reflexivity.
          
      * cbn.
        exists t', (fun x => Ret x); split; [auto|]; split.
        unfold bind, Monad_itree. rewrite Eq.bind_ret_r; auto.
        intros; reflexivity.
        
    + intros x y EQ; split; intros eqtt'. 
      * cbn in *.
        destruct eqtt' as (ta & k & HPA & EQ' & HRET).
        exists ta, k; split; [auto|]; split; auto.
        rewrite <- EQ; auto.

      * cbn in *.
        destruct eqtt' as (ta & k & HPA & EQ' & HRET).
        exists ta, k; split; [auto|]; split; auto.
        rewrite EQ; auto.
    + auto.
  Qed.

  Lemma Returns_bind: forall {E A B} (t: itree E A) (k: A -> itree E B) a b,
      Returns a t ->
      Returns b (k a) ->
      Returns b (bind t k).
  Proof.
    intros E A B t k a b HRA HRB; induction HRA.
    - cbn; rewrite H, Eq.bind_ret_l; auto.
    - cbn in *. rewrite H. rewrite (eqit_tauL true u u); [| reflexivity]; auto. 
    - cbn in *; rewrite H, bind_vis.
      eapply (ReturnsVis b e); [reflexivity | cbn; eauto].
  Qed.

  Lemma Returns_bind_inversion_ : forall {E A B} (u : itree E B) (t : itree E A) (k : A -> itree E B) b,
      Returns b u ->
      u ≈ (bind t k) ->
      exists a, Returns a t /\ Returns b (k a).
  Proof.
    intros E A B u t k b HR eq. 
    revert A t k eq.
    induction HR; intros.
    - rewrite eq in H.
      apply eutt_inv_bind_ret in H.
      destruct H as (a & HEQ & HK).
      exists a. split. rewrite HEQ. constructor. reflexivity. rewrite HK. constructor. reflexivity.
    - rewrite tau_eutt in H.
      eapply IHHR. rewrite <- H. assumption.
    - rewrite eq in H; clear eq.
      apply eutt_inv_bind_vis in H.
      destruct H as [(kx & HV & eq2) | (a & HRA & KA)].
      + setoid_rewrite HV.
        specialize (eq2 x).
        setoid_rewrite <- eq2 in IHHR.
        specialize (IHHR _ (kx x) k0).
        assert (ITree.bind (kx x) k0 ≈ bind (kx x) k0) by reflexivity.
        apply IHHR in H.
        destruct H as (a & HRet & HK).
        exists a. split.  econstructor 3. reflexivity. apply HRet. assumption.
      + exists a. split.
        rewrite HRA. constructor 1. reflexivity.
        specialize (IHHR _ (ret x) k).
        assert (k x ≈ bind (ret x) k).
        { rewrite bind_ret_l. reflexivity. }
        apply IHHR  in H. rewrite KA.
        destruct H as (x' & _ & HX).
        econstructor 3. reflexivity.  apply HX.
  Qed.

  Lemma Returns_bind_inversion : forall {E A B} (u : itree E B) (t : itree E A) (k : A -> itree E B) b,
      Returns b (bind t k) ->
      exists a, Returns a t /\ Returns b (k a).
  Proof.
    intros.
    eapply Returns_bind_inversion_. apply H. reflexivity.
  Qed.

  Lemma Returns_vis_inversion_ : forall {E A B} (u : itree E B) (e : E A) (k : A -> itree E B) b,
      Returns b u ->
      u ≈ (Vis e k) ->
      exists a, Returns b (k a).
  Proof.
    intros E A B u e k b HR eq. 
    revert A e k eq.
    induction HR; intros.
    - rewrite H in eq.
      apply eutt_inv_ret_vis in eq. inversion eq.
    - rewrite tau_eutt in H.
      eapply IHHR. rewrite <- H. apply eq.
    - rewrite eq in H; clear eq.
      punfold H.
      repeat red in H.
      simpl in H.
      inversion H. subst.
      apply inj_pair2 in H2.
      apply inj_pair2 in H3.
      apply inj_pair2 in H6.
      apply inj_pair2 in H5.
      subst.
      assert (Vis e k0 ≈ Vis e k).
      red. red. pfold. red. apply H.
      apply eqit_inv_vis in H0.
      destruct H0 as (_ & HX).
      exists x. specialize (HX x).
      rewrite HX. assumption.
  Qed.

  Lemma Returns_vis_inversion : forall {E A B} (e : E A) (k : A -> itree E B) b,
      Returns b (Vis e k) ->
      exists a, Returns b (k a).
  Proof.
    intros.
    eapply Returns_vis_inversion_. apply H. reflexivity.
  Qed.
  

  Definition EQ_REL {E A} (ta : itree E A) : A -> A -> Prop :=
    fun a b => a = b /\ Returns a ta.

  Lemma Symmteric_EQ_REL {E A} (ta : itree E A) : Symmetric (EQ_REL ta).
  Proof.
    repeat red.
    intros a b (EQ & H).
    split.
    - symmetry. assumption.
    - subst; auto.
  Qed.

  Lemma Transitive_EQ_REL {E A} (ta : itree E A) : Transitive (EQ_REL ta).
  Proof.
    repeat red.
    intros a b c (EQ1 & H1) (EQ2 & H2).
    split.
    - rewrite EQ1. assumption.
    - assumption.
  Qed.

  Instance EQ_REL_Proper {E A} : Proper (eutt eq ==> eq ==> eq ==> iff) (@EQ_REL E A).
  Proof.
    repeat red.
    intros. subst.
    split; intros; unfold EQ_REL in *.
    - split. destruct H0. assumption. destruct H0.
      intros. rewrite <- H. assumption.
    - destruct H0.
      split. assumption.
      intros. rewrite H. assumption.
  Qed.
    
  Definition eq_relation {A} (R S : A -> A -> Prop) :=
    R <2= S /\ S <2= R.
  
  Instance eutt_EQ_REL_Proper {E} {A} :
    Proper (eq_relation ==> eutt eq ==> @eutt E A A eq ==> iff) (eutt).
  Proof.
    repeat red.
    intros; split; intros.
    -  rewrite <- H0. rewrite <- H1.
       clear H0 H1.
       destruct H.
       eapply eqit_mon; eauto.
    - rewrite H0, H1.
      destruct H.
      eapply eqit_mon; eauto.
  Qed.
  
  Lemma eutt_EQ_REL_Reflexive_ {E} {A} (ta : itree E A) :
    forall R, (EQ_REL ta) <2= R ->
    eutt R ta ta.
  Proof.
    revert ta.
    ginit. gcofix CIH. intros ta HEQ.
    gstep. red.
    genobs ta obs.
    destruct obs.
    - econstructor. apply HEQ. red. split; auto. rewrite itree_eta. rewrite <- Heqobs. constructor 1. reflexivity.
    - econstructor. gbase. apply CIH.
      setoid_rewrite itree_eta in HEQ.
      destruct (observe ta); inversion Heqobs. subst.
      assert (Tau t0 ≈ t0) by apply tau_eutt.
      setoid_rewrite H in HEQ. 
      auto.
    - econstructor.  intros. red. gbase. apply CIH.
      intros. apply HEQ.
      rewrite itree_eta. rewrite <- Heqobs.
      red in PR. destruct PR.
      red. split; auto.
      econstructor 3. reflexivity. apply H0.
  Qed.

  Lemma eutt_EQ_REL_Reflexive {E} {A} (ta : itree E A) : eutt (EQ_REL ta) ta ta.
  Proof.
    apply eutt_EQ_REL_Reflexive_.
    auto.
  Qed.

  
  (* From Coq.Logic.ChoiceFacts *)
Definition GuardedFunctionalChoice_on {A B} :=
  forall P : A -> Prop, forall R : A -> B -> Prop,
    inhabited B ->
    (forall x : A, P x -> exists y : B, R x y) ->
    (exists f : A->B, forall x, P x -> R x (f x)).
Axiom guarded_choice : forall {A B}, @GuardedFunctionalChoice_on A B.


Definition RET_EQ {E} {A} (ta : itree E A) : A -> A -> Prop :=
  fun x y => Returns x ta /\ Returns y ta.


(*
Lemma commute {E} {A B} (ta : itree E A) 
forall x : A,
       Returns x ta ->
       exists k0 : B -> itree E C,
         KB x (kab x) /\ k x ≈ bind (kab x) k0 /\ (forall a : B, Returns a (kab x) -> KC a (k0 a))
         ->
         exists k0 : B -> itree E C,
forall x : A,
       Returns x ta ->
         KB x (kab x) /\ k x ≈ bind (kab x) k0 /\ (forall a : B, Returns a (kab x) -> KC a (k0 a))
*)

Section BIND_BIND_COUNTEREXAMPLE.

  Inductive ND : Type -> Type :=
  | Pick : ND bool.

  Definition PA : PropT ND bool := fun (ta : itree ND bool) => ta ≈ trigger Pick.

  Definition KB : bool -> PropT ND bool :=
    fun b => PA.

  Definition KC : bool -> PropT ND bool :=
    fun b => if b then (fun tc : itree ND bool => (tc ≈ ret true) \/ (tc ≈ ret false)) else (fun tc : itree ND bool => tc ≈ ITree.spin).

  Definition t : itree ND bool :=
    bind (trigger Pick) (fun (b:bool) => if b
                               then bind (trigger Pick) (fun (x:bool) => if x then ret true else ITree.spin)
                               else bind (trigger Pick) (fun (x:bool)  => if x then ret false else ITree.spin)).

  Lemma bind_right_assoc : bind PA (fun a => bind (KB a) KC) t.
  Proof.
    repeat red.
    exists (trigger Pick).
    exists (fun (b:bool) => if b
             then (bind (trigger Pick) (fun (x:bool) => if x then ret true else ITree.spin))
             else (bind (trigger Pick) (fun (x:bool) => if x then ret false else ITree.spin))).            
    split; auto.
    red. reflexivity.
    split. reflexivity.
    intros. repeat red. exists (trigger Pick).
    exists (fun (x:bool) => if a
                 then (if x then ret true else ITree.spin)
                 else (if x then ret false else ITree.spin)).
    split.
    red. red.  reflexivity.
    split.
    destruct a.
    - reflexivity.
    - reflexivity.
    - intros.
      destruct a0.
      destruct a.
      red. left. reflexivity.
      red. right. reflexivity.
      destruct a.
      red. reflexivity. red.  reflexivity.
  Qed.

  Lemma not_bind_left_assoc : ~ (bind (bind PA KB) KC t).
  Proof.
    intro H.
    repeat red in H.
    destruct H as (ta & k & HB & HEQ & HRET).
    destruct HB as (tb & kb & HX & HEQ' & HRET').
    red in HX.
    rewrite HX in *.
    setoid_rewrite HX in HRET'.
    clear tb HX.
    rewrite HEQ' in HEQ.
    unfold t in HEQ.
    unfold bind, Monad_itree in HEQ.
    rewrite Eq.bind_bind in HEQ.
    assert (forall r, Returns r (trigger Pick) -> eutt eq ((fun b : bool =>
           if b
           then ITree.bind (trigger Pick) (fun x : bool => if x then ret true else ITree.spin)
           else ITree.bind (trigger Pick) (fun x : bool => if x then ret false else ITree.spin)) r) ((fun r : bool => ITree.bind (kb r) k) r)).
    apply eqit_bind_Returns_inv. apply HEQ.
    assert (Returns true (trigger Pick)).
    { unfold trigger. econstructor 3. reflexivity. constructor 1. reflexivity. }
    assert (Returns false (trigger Pick)).
    { unfold trigger. econstructor 3. reflexivity. constructor 1. reflexivity. }
    assert (Returns true (trigger Pick)).
    { unfold trigger. econstructor 3. reflexivity. constructor 1. reflexivity. }
    assert (Returns false (trigger Pick)).
    { unfold trigger. econstructor 3. reflexivity. constructor 1. reflexivity. }
    apply H in H0.
    apply H in H1.
    apply HRET' in H2.
    apply HRET' in H3.
    red in H2. red in H3. red in H2. red in H3.
    rewrite H2 in H0.
    rewrite H3 in H1.
    rewrite <- H0 in H1.
    apply eqit_bind_Returns_inv with (r := true) in H1 .
    apply eqit_inv_ret in H1. inversion H1.
    { unfold trigger. econstructor 3. reflexivity. constructor 1. reflexivity. }
Qed.
    
Lemma bind_bind_counterexample: 
      (* eutt_closed PA -> *)
    exists t, bind PA (fun a => bind (KB a) KC) t /\ ~ (bind (bind PA KB) KC t).
Proof.
  exists t.
  split.
  apply bind_right_assoc.
  apply not_bind_left_assoc.
Qed.  

End BIND_BIND_COUNTEREXAMPLE.



Lemma bind_bind: forall {E}
                   (A B C : Type) (PA : PropT E A)
                   (KB : A -> PropT E B) (KC : B -> PropT E C)
                   (PQOK : eutt_closed PA)
                   (KBP : Proper (eq ==> eqm) KB)
                   (KCP : Proper (eq ==> eqm) KC)
                   (t : itree E C),
      (bind (bind PA KB) KC) t -> (bind PA (fun a => bind (KB a) KC)) t.
  Proof.
    (* PA ~a> KB a ~b> KC b *)
    intros E A B C PA KB KC PQOK KBP KCP t eqtt'. 
        red in eqtt'.
        destruct eqtt' as (tb & kbc & (HBC & EQc & HRkbc)).
        destruct HBC as (ta & kab & HTA & EQb & HRkab).
        red. exists ta. exists (fun a => ITree.bind (kab a) kbc).
        split; [auto|]; split.
        * setoid_rewrite EQc; clear EQc.
          setoid_rewrite EQb. setoid_rewrite EQb in HRkbc; clear EQb tb.
          unfold bind, Monad_itree.
          rewrite Eq.bind_bind. reflexivity.
        * intros a HRet.
          exists (kab a), kbc.
          split; [auto|];split.
          -- reflexivity.
          -- intros b HRET. apply HRkbc. rewrite EQb. eapply Returns_bind; eauto.
  Qed.
  


End MonadLaws.
