From ExtLib Require Import
     Data.List
     Structures.Monad.

From Paco Require Import paco.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts.

From ITree.Extra Require Import
     Dijkstra.DijkstraMonad
     Dijkstra.PureITreeBasics
     Dijkstra.DelaySpecMonad
     Dijkstra.StateSpecT.

Import Monads.
Import MonadNotation.
#[local] Open Scope monad_scope.
#[local] Open Scope delayspec_scope.

(* Defines a specification monad for the state transform of the Delay monad. Also includes encodings for pre post condition specifications. *)

Section StateDelaySpec.

  Context (St : Type).

  Definition StateDelaySpec := StateSpecT St DelaySpec.

  Definition StateDelaySpecOrder := StateSpecTOrder St DelaySpec.

  Definition StateDelaySpecOrderedLaws := StateSpecTOrderedLaws St DelaySpec.

  Definition StateDelaySpecEq := StateSpecTEq St DelaySpec.

  Definition StateDelaySpecMonadLaws := StateSpecTMonadLaws St DelaySpec.

  Definition StateDelay := StateSpecT St Delay.

  Definition StateDelayObs := EffectObsStateT St DelaySpec Delay.

  Definition StateDelayMonadMorph := MonadMorphimStateT St DelaySpec Delay.

  Definition PrePost A : Type := (Delay (St * A) -> Prop ) * (St -> Prop).

  Definition PrePostRef {A : Type} (m : StateDelay A) (pp : PrePost A) : Prop :=
    let '(post,pre) := pp in
    forall s, pre s -> post (m s).

  Program Definition encode {A : Type} (pp : PrePost A) : StateDelaySpec A :=
    let '(post,pre) := pp in
    fun s p => pre s /\ (forall r, post r -> p r).

  Definition verify_cond {A : Type} := DijkstraProp StateDelay StateDelaySpec StateDelayObs A.

  Lemma encode_correct : forall (A : Type) (pre : St -> Prop) (post : Delay (St * A) -> Prop)
                                (m : StateDelay A),
      resp_eutt post -> (PrePostRef m (post,pre) <-> verify_cond (encode (post,pre)) m).
  Proof.
    intros. cbn. unfold verify_cond, DijkstraProp.
    split; intros.
    - repeat red. simpl. intros. destruct p as [p Hp]. simpl in H1. destruct H1 as [Hpre Himp].
      auto.
    - repeat red in H0. simpl in H0.
      set (exist _ post H) as p. enough ((m s) ∈ p); auto.
      apply H0. auto.
  Qed.

  Definition PrePostPair A : Type := PrePost A * PrePost A.

  Definition PrePostPairRef {A : Type} (pppp : PrePostPair A) (m : StateDelay A) :=
    let '((post0, pre0), (post1, pre1)) := pppp in
    forall s, (pre0 s -> post0 (m s)) /\ (pre1 s -> post1 (m s)) .

  Program Definition encode_pair {A : Type} (pppp : PrePostPair A) : StateDelaySpec A:=
    let '((post0, pre0), (post1, pre1)) := pppp in
    fun s (p : DelaySpecInput (St * A)) =>
      (pre0 s /\ (forall r, post0 r -> p r)) \/ (pre1 s /\ forall r, post1 r -> p r).
  Next Obligation.
  destruct H0 as [H0 | H1].
  - destruct H0 as [Hp Hr]. left. auto.
  - destruct H1 as [Hp Hr]. right. auto.
  Qed.

  Lemma encode_pair_correct : forall (A : Type) (pre0 pre1 : St -> Prop)
                                          (post0 post1 : Delay (St * A) -> Prop ) (m : StateDelay A),
      let pp : PrePostPair A := ((post0,pre0),(post1,pre1)) in
      resp_eutt post0 -> resp_eutt post1 ->
      (PrePostPairRef pp m <-> verify_cond (encode_pair pp) m).
  Proof.
    intros. cbn. unfold verify_cond, DijkstraProp. split; intros.
    - repeat red. simpl. intros. destruct p as [p Hrp].
      specialize (H1 s). destruct H1.
      destruct H2 as [ [Hs Hp] | [Hs Hp]  ]; simpl in *; auto.
    - repeat red in H1. simpl in *.
      split; intros.
      + set (exist _ post0 H) as p. enough ((m s) ∈ p ); auto.
        apply H1. left. split; auto.
      + set (exist _ post1 H0) as p. enough ((m s) ∈ p ); auto.
        apply H1. right. split; auto.
  Qed.

  Definition PrePostList A : Type := list (PrePost A).

  Definition PrePostListRef {A : Type} (ppl : PrePostList A) (m : StateDelay A) :=
    forall s, List.Forall (fun pp : PrePost A=> let (post,pre) := pp in pre s -> post (m s) ) ppl.

  Program Definition encode_list {A : Type} (ppl : PrePostList A) : StateDelaySpec A :=
    fun s (p : DelaySpecInput (St * A) ) =>
      List.Exists (fun pp : PrePost A => let (post,pre) := pp in pre s /\ forall r, post r -> p r) ppl.
  Next Obligation.
    induction H0; eauto.
    destruct x as [post pre]. destruct H0 as [Hs Hr]. left. auto.
  Qed.


  Lemma enocde_list_correct : forall (A : Type) (ppl : PrePostList A) (m : StateDelay A),
      List.Forall (fun pp => resp_eutt (fst pp) ) ppl->
      (PrePostListRef ppl m <-> verify_cond (encode_list ppl) m).
  Proof.
    intros. unfold verify_cond, DijkstraProp. split; intros.
    - repeat red. intros. destruct p as [p Hp]. red in H0.
      specialize (H0 s) as Hrefine. unfold encode_list in H1. simpl in *.
      induction ppl.
      + inversion H1.
      + destruct a as [post pre].
        inversion H1; subst.
        * destruct H3. auto.
          assert ((pre s -> post (m s)) ); auto.
          intros. inversion Hrefine; subst; auto.
        * apply IHppl; auto.
          -- inversion H; auto.
          -- intros. specialize (H0 s0). inversion H0. auto.
          -- specialize (H0 s). inversion H0. auto.
    - unfold encode_list in H0. simpl in *. repeat red. repeat red in H0. simpl in *. intros.
      induction ppl; auto.
      destruct a as [post pre]. specialize (H0 s) as Henc.
      assert (Heutt : resp_eutt post).
      { inversion H. auto. }
      set (exist _ post Heutt) as p. specialize (Henc p) as Hencp.
      constructor; intros.
      + enough ((m s) ∈ p ); auto. apply Hencp.
        left. split; auto.
      + apply IHppl; auto.
        * inversion H. auto.
        * clear IHppl. intros. apply H0. eauto.
  Qed.

  Definition DynPrePost A : Type := (St -> Prop) * (St -> Delay (St * A) -> Prop).

  Definition DynPrePostRef {A : Type} (pp : DynPrePost A) (m : StateDelay A) :=
    let (pre,post) := pp in
    forall s, pre s -> post s (m s).

  Program Definition encode_dyn {A : Type} (pp : DynPrePost A) : StateDelaySpec A :=
    let (pre,post) := pp in
    fun s p => pre s /\ forall r, post s r -> p r.

  Lemma encode_dyn_correct : forall (A : Type) (pre : St -> Prop) (post : St -> Delay (St * A) -> Prop ) (m : StateDelay A),
      (forall s, resp_eutt (post s)) -> (DynPrePostRef (pre,post) m <-> verify_cond (encode_dyn (pre,post) ) m).
    Proof.
      intros. unfold verify_cond, DijkstraProp. split; intros.
      - repeat red. red in H0. intros. destruct p as [p Hp]. simpl in *.
        destruct H1 as [Hs Hr]. auto.
      - repeat red in H0. red. intros.
        set (exist _ (post s) (H s) ) as p. specialize (H0 s p).
        unfold p in H0. simpl in *. auto.
    Qed.

  Definition DynPrePostListRef {A : Type} (ppl : list (DynPrePost A)) (m : StateDelay A) : Prop :=
    Forall (fun pp => DynPrePostRef pp m) ppl.

  Program Definition encode_list_dyn {A : Type} (ppl : list (DynPrePost A)) : StateDelaySpec A :=
    fun s p => List.Exists (fun pp : DynPrePost A => let (pre,post) := pp in pre s /\ forall r, post s r -> p r ) ppl.
  Next Obligation.
    induction H0; eauto. left. destruct x as [pre post]. destruct H0 as [Hs Hr].
    split; auto.
  Qed.

  Lemma enocde_list_dyn_correct : forall (A : Type) (ppl : list (DynPrePost A) ) (m : StateDelay A),
      List.Forall (fun pp => forall s, resp_eutt (snd pp s) ) ppl->
      (DynPrePostListRef ppl m <-> verify_cond (encode_list_dyn ppl) m).
  Proof.
    intros. unfold verify_cond, DijkstraProp. split; intros.
    - repeat red. intros. destruct p as [p Hp]. simpl in H1. red in H0. rename H0 into Hrefine.
      unfold DynPrePostRef in Hrefine.
      induction ppl.
      + inversion H1.
      + destruct a as [pre post].
        inversion H1; subst.
        * destruct H2.
          assert ((pre s -> post s (m s)) ); auto.
          intros. inversion Hrefine; subst; auto.
        * apply IHppl; auto.
          -- inversion H; auto.
          -- intros. inversion Hrefine; auto.
    - unfold encode_list in H0. simpl in *. repeat red. repeat red in H0. simpl in *. intros.
      induction ppl; auto.
      destruct a as [pre post].
      assert (Heutt : forall s, resp_eutt (post s)).
      { inversion H. auto. }
      constructor; intros.
      + red. intros. set (exist _ (post s) (Heutt s)) as p.
        specialize (H0 s p). enough ((m s) ∈ p); auto. apply H0.
        left. split; auto.
      + apply IHppl; auto.
        * inversion H. auto.
        * clear IHppl. intros.
          specialize (H0 s p). apply H0. eauto.
  Qed.

  Lemma combine_prepost_aux : forall (A B : Type) (pre1 pre2 : St -> Prop)
                (post1 : Delay (St * A) -> Prop ) (post2 : Delay (St * B) -> Prop)
    (m : StateDelay A) (f : A -> StateDelay B),
    verify_cond (encode (post1,pre1) ) m ->
    (forall (a : A) (s : St), (* this condition is not exactly what i want*)
        post1 (Ret (s,a) ) -> post2 (f a s) ) ->
    (post1 ITree.spin -> post2 ITree.spin) ->
    resp_eutt post1 ->
    verify_cond (encode (post2, pre1) ) (bind m f).
  Proof.
    intros. repeat red in H. repeat red. intros.
    destruct p as [p Hp]. simpl in *.
    destruct H3.
    destruct (eutt_reta_or_div (m s)); basic_solve.
    - destruct a as [s' a].
      cbn in H5. rewrite <- H5, bind_ret_l; cbn. apply H4, H0. rewrite H5.
      apply (H s (exist _ post1 H2)); auto.
    - apply div_spin_eutt in H5.
      rewrite H5, <- spin_bind. apply H4, H1. rewrite <- H5. apply (H s (exist _ post1 H2)); auto.
  Qed.

  Lemma combine_prepost : forall (A B : Type) (pre1 pre2 : St -> Prop)
                (post1 : Delay (St * A) -> Prop ) (post2 : Delay (St * B) -> Prop)
    (m : StateDelay A) (f : A -> StateDelay B),
    verify_cond (encode (post1,pre1) ) m ->
    (forall a s, post1 (Ret (s,a)) -> pre2 s)  ->
    (forall a, verify_cond (encode (post2,pre2) ) (f a)  ) ->
    (post1 ITree.spin -> post2 ITree.spin) ->
    resp_eutt post1 ->
    resp_eutt post2 ->
    verify_cond (encode (post2, pre1) ) (bind m f).
  Proof.
    intros.
    eapply combine_prepost_aux; eauto.
    intros.
    specialize (H1 a) as Hpp2. repeat red in Hpp2.
    specialize (Hpp2 s (exist _ post2 H4) ). simpl in *.
    apply Hpp2. split; eauto.
  Qed.

End StateDelaySpec.
