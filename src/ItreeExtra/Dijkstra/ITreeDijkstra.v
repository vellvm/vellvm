From Coq Require Import
     Morphisms.

From ExtLib Require Import
     Structures.Monad.

From Paco Require Import paco.

From ITree Require Import
     Axioms
     ITree
     ITreeFacts
     Props.Infinite
     Props.EuttNoRet.

From ITree.Extra Require Import
     Dijkstra.DijkstraMonad
     Dijkstra.PureITreeBasics
     Dijkstra.DelaySpecMonad.

Import Monads.
Import MonadNotation.

#[local] Open Scope monad_scope.
#[local] Open Scope delayspec_scope.

Section ITreeDijkstra.

  Context (E : Type -> Type).

  Definition ITDInput (A : Type) := {p : itree E A -> Prop | resp_eutt p}.

  Definition ITreeSpec (A : Type) := {w : ITDInput A -> Prop |
                forall (p p' : ITDInput A), (forall t, t ∈ p -> t ∈ p') -> w p -> w p' }.

  Program Definition ret_itree (A : Type) (a : A) : ITreeSpec A := fun p => p (Ret a).

  Instance proper_itree_spec {R} {p : ITDInput R}: Proper (eutt eq ==> iff) (proj1_sig p).
  Proof.
    intros ? ? ?. destruct p as [p Hp]. simpl. split; intros; eapply Hp; eauto.
    symmetry. auto.
  Qed.

  Program Definition bind_ex (A B: Type) (w: ITreeSpec A) (g : A -> ITreeSpec B) : ITreeSpec B :=
    fun p  =>
      w (fun t => (exists a, may_converge a t /\ g a p) \/ (all_infinite t /\  p (noret_cast t)) ).
  Next Obligation.
  Proof.
    repeat red. split; intros; basic_solve.
    - left. exists a. rewrite H in H0. auto.
    - right. rewrite <- H at 1. split; auto.
      destruct p as [p Hp]; simpl in *.
      specialize (all_infinite_euttNoRet H0 H).
      intros.
      specialize (noret_cast_nop H0) as Ht1.
      rewrite H in H0. specialize (noret_cast_nop H0) as Ht2.
      eapply Hp; eauto.
      symmetry in H.
      eapply noret_cast_cast; eauto.
    - left. exists a. split; auto. rewrite H. auto.
    - right. rewrite H at 1. split; auto.
      destruct p as [p Hp]; simpl in *.
      eapply Hp; eauto.
      eapply noret_cast_cast; eauto.
      rewrite H. auto.
  Qed.
  Next Obligation.
  Proof.
    destruct w as [w Hw]. simpl in *.  eapply Hw; try apply H0.
    intros. simpl in *.
    destruct p as [p Hp]. destruct p' as [p' Hp']. simpl in *.
    basic_solve.
    - left. exists a. split; auto. destruct (g a) as [ga Hga]. simpl in *.
      eapply Hga; try apply H2.
      simpl. auto.
    - right. split; auto.
  Qed.

  Instance ItreeSpecEq : Eq1 ITreeSpec :=
    fun _ w1 w2 => forall p, p ∈ w1 <-> p ∈ w2.

  Instance ItreeSpecEquiv {A : Type} : Equivalence (ItreeSpecEq A).
  Proof.
    constructor; red; intros; red; try tauto.
    - red in H. intros. rewrite H. reflexivity.
    - intros. red in H. red in H0. rewrite H. rewrite H0.
      reflexivity.
  Qed.

  Instance ItreeSpecMonad : Monad ITreeSpec :=
    {
      ret := ret_itree;
      bind := bind_ex;
    }.

  (*
  Program Instance ItreeSpecMonadLaws : MonadLaws ITreeSpec.
  Next Obligation.
    (*bind_ret*)
    repeat red. cbn. intros. split; intros; basic_solve.
    - apply invert_ret in H. subst. auto.
    - pinversion H.
    - left. exists x. split; auto. constructor. reflexivity.
  Qed.
  Next Obligation.
    (*ret_bind*)
    repeat red. cbn. intros. split; intros; basic_solve.
    - destruct x as [w Hw]. simpl in *. eapply Hw; try apply H.
      intros. simpl in *. basic_solve.
      +

        (*PROBLEM: if p just respects eutt, then p (ret a0) might mean
          p expects no events
          consider p := fun t => exists a, t ~ ret a
          but the evidence may_converge a0 t does not force t to be a Ret
          the issue seems to be that
         *)

        (*
          The obvious solution is to further restrict predicates from resp eutt
          to respecting possible convergence. This is a bad solution,
          we want to be able to do something like have a predicate that
          accepts all trees that print 5 and then return 6. This would be
          an illegal predicate
         *)
        inversion H0; subst.
        * rewrite H2. auto.
        * rewrite H2. admit.
      + apply noret_cast_nop in H0.
        rewrite H0. auto.
    - destruct x as [w Hw]. simpl in *. eapply Hw; try apply H.
      intros. simpl. destruct (classic_converge _ t).
      + left. basic_solve. exists a0. split; auto.
        (*basically same problem as before, this time we know p t, but
          that might be reliant on some visible event behavior*)
        admit.
      + right. split; auto. apply noret_cast_nop in H1.
        rewrite <- H1. auto.
  Admitted.
  Next Obligation.
    (*bind_bind*)
    repeat red. destruct x as [w Hw]. cbn. intros. split; intros; basic_solve.
    - eapply Hw; try apply H. simpl in *. intros. basic_solve.
      + left. exists a0. auto.
      + exfalso. clear H H2 Hw w.
        eapply all_infinite_imp_not_conv; try apply H1.
        eapply euttNoRet_all_infinite. apply euttNoRet_sym.
        apply noret_bind_nop. auto.
      + right. split; auto.
        destruct p as [p Hp]. simpl in *. clear H.
        eapply Hp; try apply H2.
        apply euttNoRet_subrel.
        rewrite bind_bind.
        apply euttNoRet_trans with (t2 := t).
        * apply euttNoRet_sym. apply noret_bind_nop. auto.
        * apply noret_bind_nop. auto.
    - eapply Hw; try apply H. simpl in *. intros. basic_solve.
      + left. exists a0. auto.
      + right. split; auto. right. split.
        * apply euttNoRet_all_infinite with (t2 := t); auto.
          apply euttNoRet_sym. apply noret_bind_nop. auto.
        * destruct p as [p Hp]. simpl in *. clear H.
          eapply Hp; try apply H1. rewrite bind_bind.
          apply euttNoRet_subrel.
          apply euttNoRet_trans with (t2 := t); try apply noret_bind_nop; auto.
          apply euttNoRet_sym. apply noret_bind_nop. auto.
  Qed.
  *)

  Inductive Ev : Type :=
    ev (A : Type ) (e : E A) (a : A).

  Variant streamF {A : Type} {F : Type} : Type :=
    | NilF
    | ConsF (h : A) (t : F).

  CoInductive stream (A : Type) : Type := go {_observe : @streamF A (stream A) } .

  Notation stream' A := (@streamF A (stream A)).

  Definition Nil {A} : stream A:=
    {| _observe := NilF |}.

  Definition Cons {A} (h : A) (t : stream A) := {| _observe := ConsF h t |}.

  Definition observe_stream {A} : stream A -> stream' A := @_observe A.

  Variant is_infF {A : Type}  (F : stream A -> Prop) : stream' A -> Prop :=
    is_inf_cons (h : A) (t : stream A) : F t -> is_infF F (ConsF h t).

  Hint Constructors is_infF : itree.

  Definition is_inf_ {A : Type} (F : stream A -> Prop) : stream A -> Prop :=
    fun s => is_infF F (observe_stream s).

  Definition is_inf {A : Type} := paco1 (@is_inf_ A) bot1.

  Lemma is_inf_monot {A} : monotone1 (@is_inf_ A).
  Proof.
    red. intros. red in IN. red. induction IN; auto with itree.
  Qed.

  Hint Resolve is_inf_monot : paco.


  CoFixpoint app' {A : Type} (osl: stream' A) (sr : stream A) : stream A :=
    match osl with
    | NilF => sr
    | ConsF h t => Cons h (app' (observe_stream t) sr)
    end.

  Definition app {A : Type} (sl : stream A) : stream A -> stream A :=
    app' (observe_stream sl).

  Variant bisimF {A : Type} (F : stream A -> stream A -> Prop) : stream' A -> stream' A -> Prop :=
    | bisimNil : bisimF F NilF NilF
    | bisimConsF (h : A) (s1 s2 : stream A) : F s1 s2 -> bisimF F (ConsF h s1) (ConsF h s2).

  Hint Constructors bisimF : itree.

  Definition bisim_ {A : Type} (F : stream A -> stream A -> Prop) : stream A -> stream A -> Prop :=
    fun s1 s2 => bisimF F (observe_stream s1) (observe_stream s2).

  Definition bisim {A : Type} := paco2 (@bisim_ A) bot2.

  Lemma bisim_monot {A} : monotone2 (@bisim_ A).
  Proof.
    red. intros. red in IN. red. induction IN; auto with itree.
  Qed.

  Hint Resolve bisim_monot : paco.

  Instance bisim_equiv {A} : Equivalence (@bisim A).
  Proof.
    constructor; red.
    - pcofix CIH. intros. pfold. red. destruct (observe_stream x); auto with itree.
    - pcofix CIH. intros.
      pfold. red.
      pinversion H0; subst; auto with itree.
    - pcofix CIH. intros. pfold. red.
      pinversion H0; pinversion H1; auto with itree.
      + rewrite <- H in H3. discriminate.
      + rewrite <- H2 in H5. discriminate.
      + rewrite <- H2 in H4. injection H4; intros; subst.
        constructor. right. eauto.
   Qed.

  Instance proper_bisim_app {A} : Proper (@bisim A ==> bisim ==> bisim) app.
  Proof.
    repeat red. pcofix CIH.  intros s1 s2 H12 s3 s4 H34.
    pfold. red. unfold app. pinversion H12.
    - simpl. destruct s3. destruct s4. pinversion H34; simpl in *; subst; auto with itree.
      constructor. left. apply pacobot2. auto.
    - cbn. constructor. right. apply CIH; auto.
  Qed.

  Instance proper_bisim_inf_imp {A} : Proper (@bisim A ==> impl) is_inf.
  Proof.
    repeat red. pcofix CIH.
    intros s1 s2 H12 H. pfold. red. punfold H. red in H.
    punfold H12. red in H12. inversion H12; subst; auto.
    - rewrite <- H1 in H. inversion H.
    - inversion H. subst. pclearbot.
      constructor. right. eapply CIH; eauto.
      rewrite <- H3 in H0. injection H0 as H0 . subst. auto.
  Qed.

  Instance proper_bisim_inf {A} : Proper (@bisim A ==> iff) (is_inf).
  Proof.
    split; try apply proper_bisim_inf_imp; auto.
    apply bisim_equiv. auto.
  Qed.

  Lemma app_inf : forall (A : Type) (s1 s2 : stream A), is_inf s1 -> bisim (app s1 s2) s1.
  Proof.
    intros A. pcofix CIH. intros s1 s2 Hinf. pfold. unfold app.
    pinversion Hinf.
    red. cbn. rewrite <- H. constructor. right. apply CIH; auto.
  Qed.

  Variant forall_streamF {A : Type} (P : A -> Prop) (F : stream A -> Prop) : stream' A -> Prop :=
    | forall_nil : forall_streamF P F NilF
    | forall_cons (h : A) (t : stream A) : P h -> F t -> forall_streamF P F (ConsF h t).

  Hint Constructors forall_streamF : itree.

  Definition forall_stream_ {A : Type} (P : A -> Prop) (F : stream A -> Prop) : stream A -> Prop :=
    fun s => forall_streamF P F (observe_stream s).

  Lemma forall_stream_monot (A : Type) (P : A -> Prop) : monotone1 (forall_stream_ P).
  Proof.
    red. intros. red. red in IN. destruct IN; auto with itree.
  Qed.

  Hint Resolve forall_stream_monot : paco.

  Definition forall_stream {A : Type} (P : A -> Prop) := paco1 (forall_stream_ P) bot1.

  Inductive inf_manyF {A : Type} (P : A -> Prop) (F : stream A -> Prop) : stream' A -> Prop :=
    | cons_search (h : A) (t : stream A) : inf_manyF P F (observe_stream t) -> inf_manyF P F (ConsF h t)
    | cons_found (h : A) (t : stream A) : P h -> F t -> inf_manyF P F (ConsF h t)
  .

  Hint Constructors inf_manyF : itree.

  Definition inf_many_ {A : Type} (P : A -> Prop) (F : stream A -> Prop) : stream A -> Prop :=
    fun s => inf_manyF P F (observe_stream s).

  Lemma inf_many_monot (A : Type) (P : A -> Prop) : monotone1 (inf_many_ P).
  Proof.
    red. intros. red in IN. red. induction IN; auto with itree.
  Qed.

  Hint Resolve inf_many_monot : paco.

  Definition inf_many {A : Type} (P : A -> Prop) := paco1 (inf_many_ P) bot1.

  Lemma inf_many_inf : forall (A : Type) (P : A -> Prop) (s : stream A),
      inf_many P s -> is_inf s.
  Proof.
    intros A P. pcofix CIH. intros s Him.
    punfold Him. red in Him. pfold. red.
    induction Him; auto with itree. pclearbot.
    auto with itree.
  Qed.

  Lemma inf_and_forall : forall (A : Type) (P : A -> Prop) (s : stream A),
      is_inf s -> forall_stream P s -> inf_many P s.
  Proof.
    intros A P. pcofix CIH. intros s Hinf Hforall.
    pfold. red. punfold Hinf. red in Hinf. punfold Hforall.
    red in Hforall. inversion Hinf.
    inversion Hforall.
    - rewrite <- H in H2. discriminate.
    - pclearbot. rewrite <- H in H1. injection H1 as H1. subst.
      apply cons_found; auto.
  Qed.

  (*bisim is proper under app*)

  (*need a way to relate trees across event types if they never use it*)

  Definition rel_eventless {E1 E2 R} (t1 : itree E1 R) (t2 : itree E2 R) : Prop := False.

  Inductive eqitEF {E1 E2 : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop)
            (sim : itree E1 R1 -> itree E2 R2 -> Prop) : itree' E1 R1 -> itree' E2 R2 -> Prop :=
    | EqERet : forall r1 r2, RR r1 r2 -> eqitEF RR sim (RetF r1) (RetF r2)
    | EqETau : forall (t1 : itree E1 R1) (t2 : itree E2 R2),
        sim t1 t2 ->
        eqitEF RR sim (TauF t1) (TauF t2)
    | EqETauL : forall (t1 : itree E1 R1) (ot2 : itree' E2 R2),
        eqitEF RR sim (observe t1) ot2 ->
        eqitEF RR sim (TauF t1) ot2
    | EqETauR : forall (ot1 : itree' E1 R1) (t2 : itree E2 R2),
        eqitEF RR sim ot1 (observe t2) ->
        eqitEF RR sim ot1 (TauF t2).

  Hint Constructors eqitEF : itree.

  Definition eqitE_ (E1 E2 : Type -> Type) (R1 R2 : Type) (RR : R1 -> R2 -> Prop)
             (sim : itree E1 R1 -> itree E2 R2 -> Prop)
             (t1 : itree E1 R1) (t2 : itree E2 R2)
    := eqitEF RR sim (observe t1) (observe t2).

  Definition eqitE {E1 E2} {R1 R2} RR := paco2 (eqitE_ E1 E2 R1 R2 RR) bot2.

  Lemma eqitE_monot {E1 E2 R1 R2 RR} : monotone2  (@eqitE_ E1 E2 R1 R2 RR).
  Proof.
    repeat red. intros. rename x0 into t1. rename x1 into t2.
    induction IN; eauto with itree.
  Qed.

  Hint Resolve eqitE_monot : paco.

  Definition equivE {E1 E2} {R} : itree E1 R -> itree E2 R -> Prop := eqitE eq.

  Variant eventlessF {E : Type -> Type} {R : Type} (F : itree E R -> Prop) : itree' E R -> Prop :=
    | eventlessRet (r : R) : eventlessF F (RetF r)
    | eventlessTau (t : itree E R) : F t -> eventlessF F (TauF t).

  Hint Constructors eventlessF : itree.

  Definition eventless_ {E : Type -> Type} {R : Type} (F : itree E R -> Prop)
    : itree E R -> Prop := fun t => eventlessF F (observe t).

  Hint Unfold eventless_ : itree.

  Definition eventless {E : Type -> Type} {R : Type} : itree E R -> Prop :=
    paco1 (eventless_) bot1.

  Lemma eventless_monot {E1 R} : monotone1 (@eventless_ E1 R).
  Proof.
    red. intros. red in IN. red. inversion IN; auto with itree.
  Qed.

  Hint Resolve eventless_monot : paco.

  Instance proper_eventless_imp {E1 R} : Proper (eutt eq ==> impl) (@eventless E1 R) .
  Proof.
    repeat red. pcofix CIH.
    intros t1 t2 Heutt Hev.
    pfold. punfold Heutt.  red.
    unfold_eqit. assert (Hev' : eventless t1); auto. punfold Hev.
    dependent induction Heutt; subst; auto with itree.
    - rewrite <- x. auto with itree.
    - rewrite <- x. constructor. right. eapply CIH; eauto.
      specialize (itree_eta t1) as Ht1. rewrite <- x0 in Ht1.
      rewrite Ht1. rewrite tau_eutt. pclearbot. auto.
    - red in Hev. inversion Hev; subst.
      + rewrite <- H0 in x0. discriminate.
      + rewrite <- H in x0. discriminate.
    - red in Hev. rewrite <- x in Hev. inversion Hev; subst.
      pclearbot. eapply IHHeutt; try apply H0; eauto. red.
      punfold H0.
    - rewrite <- x. constructor. right. eapply CIH; eauto with itree.
  Qed.

  Instance proper_eventless {E1 R} : Proper (eutt eq ==> iff) (@eventless E1 R).
  Proof.
    intros t1 t2 Heutt. split; intros Hev.
    - rewrite <- Heutt. auto.
    - symmetry in Heutt. rewrite <- Heutt. auto.
  Qed.

  Lemma eutt_eventless : forall (E1 : Type -> Type) (R1 R2 : Type) (RR : R1 -> R2 -> Prop)
                 (t1 : itree E1 R1) (t2 : itree E1 R2),
      eventless t1 -> eutt RR t1 t2 -> eqitE RR t1 t2.
  Proof.
    intros E1 R1 R2 RR. pcofix CIH. intros.
    punfold H1. unfold_eqit. pfold. red. dependent induction H1; auto.
    - rewrite <- x0. rewrite <- x. constructor. auto.
    - rewrite <- x0. rewrite <- x.
      constructor. right.
      specialize (itree_eta t1) as Ht1. specialize (itree_eta t2) as Ht2.
      rewrite <- x0 in Ht1. rewrite <- x in Ht2.
      assert (t1 ≈ m1). { rewrite Ht1. rewrite tau_eutt. reflexivity. }
      assert (t2 ≈ m2). { rewrite Ht2. rewrite tau_eutt. reflexivity. }
      pclearbot.
      apply CIH; auto.
      rewrite <- H. auto.
    - exfalso. pinversion H0.
      + rewrite <- H1 in x0. discriminate.
      + rewrite <- H in x0. discriminate.
    - rewrite <- x. constructor.
      specialize (itree_eta t1) as Ht1. rewrite <- x in Ht1.
      rewrite Ht1 in H0. pinversion H0.
      subst. eapply IHeqitF; try apply H2; eauto.
    - rewrite <- x. constructor. eapply IHeqitF; eauto.
  Qed.

  Lemma eventless_div : forall (R : Type) (t : itree E R),
      eventless t -> all_infinite t -> t ≈ ITree.spin.
  Proof.
    intros R. pcofix CIH. intros.
    pinversion H0.
    - specialize (itree_eta t) as Ht. rewrite <- H2 in Ht.
      rewrite Ht in H1. pinversion H1.
    - pfold. red. cbn. rewrite <- H.
      red in H0. rewrite <- H in H0.
      constructor.
      right. apply CIH; auto.
      specialize (itree_eta t) as Ht. rewrite <- H in Ht.
      rewrite Ht in H1. punfold H1. red in H1. cbn in H1.
      inversion H1. subst. pclearbot. auto.
  Qed.

  Lemma eventless_ret : forall (R : Type) (t : itree E R) (r : R),
      eventless t -> may_converge r t -> t ≈ Ret r.
  Proof.
    intros R t r.
    intros. induction H0; auto. rewrite H0 in H.
    pinversion H.
  Qed.

  Lemma eqitE_imp_eutt : forall (E : Type -> Type) (R1 R2 : Type) (RR : R1 -> R2 -> Prop)
                                (t1 : itree E R1) (t2 : itree E R2),
      eqitE RR t1 t2 -> eutt RR t1 t2.
  Proof.
    intros E1 R1 R2 RR. pcofix CIH.
    intros t1 t2 Heq. pfold. punfold Heq.
    red. red in Heq. induction Heq; auto with itree.
    pclearbot. constructor. right. apply CIH. auto.
  Qed.

  Lemma eqitE_imp_eventlessl : forall (E1 E2 : Type -> Type) (R1 R2 : Type)
                                      (RR : R1 -> R2 -> Prop)
                                      (t1 : itree E1 R1) (t2 : itree E2 R2),
      eqitE RR t1 t2 -> eventless t1.
  Proof.
    intros E1 E2 R1 R2 RR. pcofix CIH.
    intros. punfold H0. red in H0.
    pfold. red. induction H0; eauto with itree.
    pclearbot.
    constructor. right. eapply CIH; eauto.
  Qed.

  Lemma eqitE_imp_eventlessr : forall (E1 E2 : Type -> Type) (R1 R2 : Type)
                                      (RR : R1 -> R2 -> Prop)
                                      (t1 : itree E1 R1) (t2 : itree E2 R2),
      eqitE RR t1 t2 -> eventless t2.
  Proof.
    intros E1 E2 R1 R2 RR. pcofix CIH.
    intros. punfold H0. red in H0.
    pfold. red. induction H0; eauto with itree.
    pclearbot.
    constructor. right. eapply CIH; eauto.
  Qed.

  Lemma eventless_spin : forall (E1 : Type -> Type) (R : Type),
      eventless (@ITree.spin E1 R).
  Proof.
    intros E1 R. pcofix CIH. pfold. red. cbn. constructor.
    right. auto.
  Qed.

  CoFixpoint remove_events' {E1 E2 : Type -> Type} {A : Type}
              (t : itree' E1 A) : itree E2 A :=
    match t with
    | RetF r => Ret r
    | TauF t' => Tau (remove_events' (observe t'))
    | VisF _ _ => ITree.spin end.

  Definition remove_events {E1 E2 A} (t : itree E1 A) : itree E2 A :=
    remove_events' (observe t).

  Lemma remove_events_eventless_equivE : forall (E1 E2 : Type -> Type) (A : Type)
                                         (t : itree E1 A),
      eventless t -> @equivE E1 E2 A t (remove_events t).
  Proof.
    intros E1 E2 A. pcofix CIH. intros.
    pfold. red. pinversion H0.
    - cbn. unfold remove_events. rewrite <- H1. cbn. auto with itree.
    - unfold remove_events. rewrite <- H. cbn. constructor. right. apply CIH.
      auto.
  Qed.

  Lemma remove_events_eventless : forall (E1 E2: Type -> Type) (A : Type)
                                         (t : itree E1 A),
      eventless (@remove_events E1 E2 A t).
  Proof.
    intros E1 E2 A. pcofix CIH. intros.
    pfold. red. unfold remove_events. destruct (observe t) eqn : Heq.
    - cbn. constructor.
    - cbn. constructor. right. apply CIH.
    - cbn. constructor. left. apply pacobot1, eventless_spin.
  Qed.

  Lemma delay_eventless : forall (A : Type) (d : Delay A),
      eventless d.
  Proof.
    intros A. pcofix CIH. intros.
    pfold. red. destruct (observe d); auto with itree.
    destruct e.
  Qed.

  (* TODO need to get this done at some point*)
  Lemma eqitE_inv_Tau : forall (E1 E2 : Type -> Type) (R1 R2 : Type) (RR : R1 -> R2 -> Prop)
            (t1 : itree E1 R1) (t2 : itree E2 R2),
            eqitE RR (Tau t1) (Tau t2) -> eqitE RR t1 t2.
  Proof.
    intros E1 E2 R1 R2 RR.

    pcofix CIH. intros.
    punfold H0. red in H0. simpl in H0.
    pfold. red. remember (TauF t1) as tt1.
    remember (TauF t2) as tt2. genobs t1 ot1.
    genobs t2 ot2. induction H0; try discriminate.
    - pclearbot. injection Heqtt1 as Heqtt1. injection Heqtt2 as Heqtt2. subst.
      punfold H. red in H. auto. eapply eqitE_monot; eauto.
      intros. pclearbot. left. eapply paco2_mon; try apply PR. intros. contradiction.
   Abort.

  Lemma inv_remove_events : forall (E1 E2 : Type -> Type) (R : Type)
                                   (t1 : itree E1 R) (t2 : itree E2 R),
      eventless t1 -> eventless t2 -> @remove_events E1 E2 R t1 ≈ @remove_events E2 E2 R t2 ->
      equivE t1 t2.
  Proof.
    intros E1 E2 R. pcofix CIH.
    intros t1 t2 Hev1 Hev2 Heutt. pfold. red.
    punfold Heutt. unfold_eqit. dependent induction Heutt; subst.
    - unfold remove_events in x0, x.
      destruct (observe t1); destruct (observe t2); try discriminate.
      constructor. cbn in *. injection x0. injection x. intros. subst. auto.
    - unfold remove_events in x0, x.
      destruct (observe t1) eqn : Heq1; destruct (observe t2) eqn : Heq2; try discriminate.
      + cbn in *. constructor.
        injection x0. injection x. intros. subst. pclearbot.
        right. apply CIH; auto.
        * specialize (itree_eta t1) as Ht1. rewrite Heq1 in Ht1.
          assert (t ≈ t1).
          { rewrite Ht1. rewrite tau_eutt. reflexivity. }
          rewrite H. auto.
        * specialize (itree_eta t2) as Ht2. rewrite Heq2 in Ht2.
          assert (t0 ≈ t2).
          { rewrite Ht2. rewrite tau_eutt. reflexivity. }
          rewrite H. auto.
      + pinversion Hev2.
        * rewrite Heq2 in H0. discriminate.
        * rewrite Heq2 in H. discriminate.
      + pinversion Hev1.
        * rewrite Heq1 in H0. discriminate.
        * rewrite Heq1 in H. discriminate.
      + pinversion Hev1.
        * rewrite Heq1 in H0. discriminate.
        * rewrite Heq1 in H. discriminate.
    - unfold remove_events in *. destruct (observe t1); cbn in x0; discriminate.
    - unfold remove_events in x. destruct (observe t1) eqn : Heq; cbn in *; try discriminate.
      + injection x as x. constructor.
        apply IHHeutt; auto.
        * specialize (itree_eta t1) as Ht1. rewrite Heq in Ht1.
          assert (t ≈ t1).
          { rewrite Ht1. rewrite tau_eutt. reflexivity. }
           rewrite  H. auto.
        * unfold remove_events. rewrite x. auto.
      + exfalso. specialize (itree_eta t1) as Ht1. rewrite Heq in Ht1.
        rewrite Ht1 in Hev1. pinversion Hev1.
    - unfold remove_events in x. destruct (observe t2) eqn : Heq; cbn in *; try discriminate.
      + injection x as x. constructor.
        apply IHHeutt; auto.
        * specialize (itree_eta t2) as Ht2. rewrite Heq in Ht2.
          assert (t ≈ t2).
          { rewrite Ht2. rewrite tau_eutt. reflexivity. }
          rewrite H. auto.
        * unfold remove_events. rewrite x. auto.
      + exfalso. specialize (itree_eta t2) as Ht2. rewrite Heq in Ht2.
        rewrite Ht2 in Hev2. pinversion Hev2.
  Qed.

  Lemma remove_events_eqitE : forall (E1 E2 E3 E4 : Type -> Type) (R1 R2 : Type)
                                      (RR : R1 -> R2 -> Prop)
                                      (t1 : itree E1 R1) (t2 : itree E2 R2),
      eqitE RR t1 t2 -> eqitE RR (@remove_events E1 E3 R1 t1) (@remove_events E2 E4 R2 t2).
  Proof.
    intros E1 E2 E3 E4 R1 R2 RR. pcofix CIH. intros.
    punfold H0. red in H0. pfold. red. unfold remove_events.
    induction H0; cbn; auto with itree.
    pclearbot. constructor. right. apply CIH; auto.
  Qed.

  Lemma eqitE_trans : forall (E1 E2 E3 : Type -> Type) (R : Type)
                             (t1 : itree E1 R) (t2 : itree E2 R) (t3 : itree E3 R),
      equivE t1 t2 -> equivE t2 t3 -> equivE t1 t3.
  Proof.
    intros E1 E2 E3 R t1 t2 t3 Ht12 Ht23.
    assert (Ht1 : eventless t1).
    { eapply eqitE_imp_eventlessl; eauto. }
    assert (Ht2 : eventless t2).
    { eapply eqitE_imp_eventlessl; eauto. }
    assert (Ht3 : eventless t3).
    { eapply eqitE_imp_eventlessr; eauto. }
    apply inv_remove_events; auto.
    assert (remove_events t1 ≈ @remove_events E2 E3 _ t2).
    {
      apply eqitE_imp_eutt. apply remove_events_eqitE. auto.
    }
    assert (remove_events t2 ≈ @remove_events E3 E3 _ t3).
    {
      apply eqitE_imp_eutt. apply remove_events_eqitE. auto.
    }
    rewrite H. auto.
  Qed.

  Lemma equivE_sym : forall (E1 E2 : Type -> Type) (R : Type)
                            (t1 : itree E1 R) (t2 : itree E2 R),
      equivE t1 t2 -> equivE t2 t1.
  Proof.
    intros E1 E2 R. pcofix CIH. intros.
    punfold H0. red in H0. pfold. red.
    induction H0; eauto with itree.
    pclearbot. constructor. right. apply CIH; auto.
  Qed.


  Instance proper_eutt_equivE_imp {E1 E2} {R} : Proper (eutt eq ==> (eutt eq) ==> impl) (@equivE E1 E2 R).
  Proof.
    intros t1 t2 Ht12 t3 t4 Ht34. intro.
    apply eqitE_imp_eventlessl in H as Ht1.
    apply eqitE_imp_eventlessr in H as Ht3.
    assert (Ht2 : eventless t2).
    { rewrite <- Ht12. auto. }
    assert (Ht4 : eventless t4).
    { rewrite <- Ht34. auto. }
    apply eqitE_trans with (t2 := t1).
    - symmetry in Ht12. red. apply eutt_eventless; auto.
    - apply eqitE_trans with (t2 := t3); auto.
      apply eutt_eventless; auto.
  Qed.

  Instance proper_eutt_equivE  {E1 E2} {R}  :Proper (  eutt eq ==> (eutt eq) ==> iff) (@equivE E1 E2 R).
  Proof.
    split; intros.
    - rewrite <- H. rewrite <- H0. auto.
    - symmetry in H. symmetry in H0.
      rewrite <- H. rewrite <- H0. auto.
  Qed.


  (*could also use an eventless predicate*)

  (*gets the idea across, obviously I want to pacoize this*)
  (*this is a key part of an effect observation from *)
  CoInductive itree_includes' {R : Type} : itree E R -> stream Ev -> Delay R -> Prop :=
    | includes_base (t : itree E R) (d : Delay R) : equivE t d -> itree_includes' t Nil d
    | cont_vis {A} (e : E A) (a : A) (k : A -> itree E R) (t : itree E R) (s : stream Ev ) (d : Delay R) :
        Vis e k ≈ t ->
        itree_includes' (k a) s d -> itree_includes' t (Cons (ev A e a) s ) (Tau d).

  Variant itree_includesF {R : Type} (F : itree E R -> stream Ev -> Delay R -> Prop) :
    itree E R -> stream Ev -> Delay R -> Prop :=
    | includes_baseF (t : itree E R) (d : Delay R) : equivE t d -> itree_includesF F t Nil d
    | cont_visF {A} (e : E A) (a : A) (k : A -> itree E R) (t : itree E R) (s : stream Ev) (d : Delay R) :
        Vis e k ≈ t ->
        F (k a) s d -> itree_includesF F t (Cons (ev A e a) s) (Tau d).

  Definition itree_includes {R : Type} : itree E R -> stream Ev -> Delay R -> Prop :=
    paco3 (@itree_includesF R) bot3.

End ITreeDijkstra.

Section RetBindCounter.

  Variant Sound : Type -> Prop :=
    Ring : Sound unit.

  (* Program Definition ret_itree (A : Type) (a : A) : ITreeSpec A := fun p => p (Ret a). *)

  (* Program Definition bind_ex (A B: Type) (w: ITreeSpec A) (g : A -> ITreeSpec B) : ITreeSpec B :=
    fun p  =>
      w (fun t => (exists a, may_converge a t /\ g a p) \/ (all_infinite t /\  p (noret_cast t)) ).
*)

  (* ret_bind : forall (a : Type) (x : DelaySpec a), bind x (fun y : a => ret y) ≈ x*)

  Program Definition p : ITDInput Sound unit := fun t => t ≈ Vis Ring (fun _ => Ret tt).
  Next Obligation.
    repeat red. intros. split; rewrite H; auto.
  Qed.


(*PROBLEM: if p just respects eutt, then p (ret a0) might mean
          p expects no events
          consider p := fun t => exists a, t ~ ret a
          but the evidence may_converge a0 t does not force t to be a Ret
          the issue seems to be that
         *)

        (*
          The obvious solution is to further restrict predicates from resp eutt
          to respecting possible convergence. This is a bad solution,
          we want to be able to do something like have a predicate that
          accepts all trees that print 5 and then return 6. This would be
          an illegal predicate
         *)

  Program Definition w : ITreeSpec Sound unit := fun p => p (Vis Ring (fun _ => Ret tt) ).
  (*This proof is hideous for a few reasons but it is a good start,
    and great confirmation that our whole IBranch excursion wasn't a
    soul crushing waste of time
   *)
  Lemma bind_ret_failure : ~ forall p, p ∈ w -> p ∈ (bind_ex Sound _ _ w (fun a => ret_itree Sound _ a) ).
  Proof.
    cbn. intros Hcontra.
    specialize (Hcontra p).
    assert (p ∋ Vis Ring (fun _ => Ret tt)).
    {
      unfold p. cbn. reflexivity.
    }
    apply Hcontra in H. clear Hcontra. basic_solve.
    - unfold p in H0. cbn in H0. pinversion H0.
    - clear H0. pinversion H; try apply all_infiniteF_mono'. ddestruction.
      specialize (H1 tt). punfold H1; try apply all_infiniteF_mono'.
      inv H1.
  Qed.

End RetBindCounter.
