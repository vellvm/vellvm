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
     Dijkstra.DelaySpecMonad
     ITrace.ITraceDefinition
     ITrace.ITraceFacts
     ITrace.ITraceBind
     ITrace.ITracePreds.

Import Monads.
Import MonadNotation.

#[local] Open Scope monad_scope.
#[local] Open Scope delayspec_scope.

(** Contains TraceSpec, the type family of Specification Monads for uninterpretted ITrees. Also contains the effect observation from ITrees into TraceSpec and the proof that it is a monad morphism *)

Section TraceSpec.
  Context (E : Type -> Type).

  Definition TraceSpecInput (A : Type) := {p : itrace E A -> Prop | resp_eutt p}.

  Instance proper_eutt_spec_in {A} {p : TraceSpecInput A} : Proper (@eutt _ A A eq ==> iff) (proj1_sig p).
  Proof.
    intros b1 b2 Heutt. destruct p as [p Hp]. simpl. split; intros;
    eapply Hp; try apply H; auto. symmetry. auto.
  Qed.

  Definition TraceSpec (A : Type) := ev_list E -> {w : TraceSpecInput A -> Prop |
                                      forall (p p' : TraceSpecInput A), (forall b, b ∈ p -> b ∈ p') -> w p -> w p'  }.

  #[global] Instance EqM_TraceSpec : Eq1 TraceSpec := fun _ w1 w2 => forall log p, w1 log ∋ p <-> w2 log ∋ p.
  #[global] Instance EqMTS_equiv {R}: Equivalence (EqM_TraceSpec R).
  Proof.
    do 2 constructor; unfold EqM_TraceSpec in *; intros; try apply H0; try apply H; auto.
    apply H0. auto.
  Qed.


  (* look over this code *)
  (* https://github.com/FStarLang/FStar/blob/dm4all/examples/dm4all/IORWLocal.fst *)

  Notation "↑ log" := (ev_list_to_stream log) (at level 30).

  Program Definition ret_ts1 {A : Type} (a : A) : TraceSpec A := fun log p => p ( Ret a).

  Program Definition ret_ts2 {A : Type} (a : A) : TraceSpec A := fun log p => p (↑log ++ Ret a).


  (* RE : forall A B, E1 A -> A -> E2 B -> B -> Prop
     (forall a1 a2, RE e1 a1 e2 a2 -> corec (k1 a1) (k2 a2)) -> eutt VisF e1 k1 VisF e2 k2

*)

  Program Definition bind_ts1_all {A B : Type} (w : TraceSpec A) (g : A -> TraceSpec B) :=
    fun log p => w log (fun b : itree (EvAns E) A  => (forall a log', b ≈ (↑log' ++ Ret a) -> g a log' p ) /\ (all_infinite b -> p (noret_cast b) )  ).
  Next Obligation.
    intros b1 b2 Heutt. split; intros; split; basic_solve.
    - apply H. rewrite Heutt. auto.
    - rewrite <- Heutt. apply H1. rewrite Heutt. auto.
    - apply H. rewrite <- Heutt. auto.
    - rewrite Heutt. apply H1. rewrite <- Heutt. auto.
  Qed.

  Program Definition bind_ts1 {A B : Type} (w : TraceSpec A) (g : A -> TraceSpec B) : TraceSpec B :=
    fun log p => w log (fun b : itree (EvAns E) A => (exists a, exists log', b ≈ (↑log' ++ Ret a)  /\ g a log' p) \/
                                 (all_infinite b /\ p (noret_cast b )) ).
  Next Obligation.
    intros b1 b2 Heutt. split; intros; basic_solve.
    - left. exists a. exists log'.
      rewrite <- Heutt. auto.
    - right. rewrite <- Heutt. auto.
    - left. exists a. exists log'. rewrite Heutt.
      auto.
    - right. rewrite Heutt. auto.
  Qed.
  Next Obligation.
    destruct (w log) as [wl Hwl]. simpl in *.
    eapply Hwl; try apply H0. simpl. clear H0. intros.
    basic_solve.
    - left. exists a. exists log'. split; auto.
      destruct (g a log') as [gal Hgal]. simpl in *.
      eapply Hgal; try apply H1. auto.
    - right. auto.
 Qed.

  #[global] Instance TraceSpecMonad : Monad TraceSpec :=
    {
      ret := @ret_ts2;
      bind := @bind_ts1;
    }.

  (*If initial logs are allow to be inf, and b in inf then for any a there is some log,
    b = log ++ ret a, even if b never actually returns it, this is problematic, so I will
    restrict it, I think this restriction is justifiable*)

  Lemma apply_monot : forall (A : Type) (w : TraceSpec A) (log : ev_list E) (p p' : TraceSpecInput A),
      (forall b, p ∋ b -> p' ∋ b) -> w log ∋ p -> w log ∋ p'.
  Proof.
    intros. destruct (w log) as [w' Hw'].
    simpl in *. eauto.
  Qed.

  #[global] Program Instance TraceSpecMonadLaws : MonadLawsE TraceSpec.
  Next Obligation.
    rename x into a.
    red. red. cbn. split; intros; basic_solve.
    - apply inv_append_eutt in H. destruct H. subst. auto.
    - exfalso. assert (may_converge a (↑ log ++ Ret a) ).
      { apply may_converge_append. apply finite_list_to_stream. }
      eapply all_infinite_not_converge; eauto.
    - left. exists a. exists log. split; auto. reflexivity.
  Qed.
  Next Obligation.
    rename x into w. red. red. cbn. split; intros; basic_solve.
    - eapply apply_monot; try apply H. clear H.
      simpl. intros. basic_solve.
      + rewrite H. auto.
      + apply noret_cast_nop in H.
        rewrite H. auto.
    - eapply apply_monot; try apply H. clear H.
      intros. simpl. destruct (classic_converge_itrace b).
      + basic_solve. left. exists r. exists log0. split.
        * symmetry. auto.
        * rewrite H0. auto.
      + right. split; auto. rewrite noret_cast_nop in H; auto.
  Qed.
  Next Obligation.
    rename x into w.
    red. red. cbn. split; intros; basic_solve.
    - eapply apply_monot; try apply H. clear H. simpl. intros.
      basic_solve.
      + left. exists a. exists log'. auto.
      + exfalso.
        assert (may_converge a (↑log' ++ Ret a) ).
        { apply may_converge_append. apply finite_list_to_stream. }
        assert (all_infinite (@noret_cast (EvAns E) A A b) ).
        { apply all_infinite_bind. auto. }
        rewrite <- H0 in H2. unfold noret_cast in H3. cbn in H3.
        eapply all_infinite_not_converge with (r := a) ; eauto.
        apply all_infinite_bind. auto.
      + right. split; auto.
        destruct p as [p Hp]. simpl in *. eapply Hp; try apply H1.
        eapply eutt_clo_bind with (UU := fun a b => False); intuition.
        apply noret_bind_nop. auto.
    - eapply apply_monot; try apply H. clear H. simpl. intros.
      basic_solve.
      + left. exists a. exists log'. auto.
      + right. split; auto. right. split.
        * apply all_infinite_bind. auto.
        * destruct p as [p Hp]. simpl in *. eapply Hp; try apply H0.
          eapply eutt_clo_bind with (UU := fun a b => False); intuition.
          apply euttNoRet_sym. apply noret_bind_nop. auto.
   Qed.
  Next Obligation.
    intros w1 w2 Hw k1 k2 Hk. do 2 red in Hw. do 3 red in Hk.
    repeat red. unfold bind_ts1. simpl. split; intros.
    - rewrite <- Hw. destruct (w1 log) as [w1l Hw1l]; simpl in *. eapply Hw1l; try apply H;
      simpl. intros. basic_solve; auto.
      left. exists a. exists log'. split; auto. rewrite <- Hk. auto.
    - rewrite Hw. destruct (w2 log) as [w2l Hw2l]; simpl in *. eapply Hw2l; try apply H;
      simpl. intros. basic_solve; auto.
      left. exists a. exists log'. split; auto. rewrite Hk. auto.
  Qed.


  Program Definition obs_trace (A : Type) (t : itree E A) : TraceSpec A :=
    fun log p => forall b, b ⊑ t -> p (↑log ++ b).

  #[global] Instance TraceSpecObs : EffectObs (itree E) TraceSpec := obs_trace.

  Lemma bind_split_diverge:
    forall (A B : Type) (log : ev_list E) (p : TraceSpecInput B) (b : itrace E B)
      (b' : itree (EvAns E) A) (g' : A -> itree (EvAns E) B),
      (ITree.bind b' g' ≈ b)%itree ->
      all_infinite (↑ log ++ b') ->
      p ∋ ITree.bind (↑ log ++ b') (fun _ : A => ITree.spin) -> p ∋ ↑ log ++ b.
  Proof.
    intros A B log p b b' g' Hsplit Hdiv Hp.
    rewrite <- Hsplit.
    enough (↑ log ++ ITree.bind b' g' ≈ ITree.bind (↑ log ++ b') (fun _ => ITree.spin)).
    { rewrite H. auto. }
    unfold append. rewrite bind_bind.
    eapply eutt_clo_bind with (RR := eq) (UU := eq); try reflexivity.
    intros. apply euttNoRet_subrel. eapply euttNoRet_trans with (t2 := b').
    + apply euttNoRet_sym. apply noret_bind_nop. eapply all_infinite_bind_append; eauto.
    + apply noret_bind_nop. eapply all_infinite_bind_append; eauto.
  Qed.

  #[global] Instance TraceSpecMorph : MonadMorphism (itree E) TraceSpec TraceSpecObs.
  Proof.
    constructor.
    - intros. repeat red. unfold obs, TraceSpecObs. cbn. split; intros.
      + apply H. apply trace_refine_ret.
      + apply trace_refine_ret_inv_l in H0.
        rewrite H0. auto.
    - intros. repeat red. cbn.
      split; intros.
      + destruct (classic_converge_itrace b); basic_solve.
        * left. exists r. setoid_rewrite <- H1.
          exists (log ++ log0)%list. split.
          ++ rewrite append_assoc. reflexivity.
          ++ intros bf Hbf.
             set (fun r : A => bf) as g.
             assert ( ITree.bind b g ≈ (↑log0 ++ bf) ).
             {
               rewrite <- H1. unfold append. rewrite bind_bind.
               setoid_rewrite bind_ret_l. unfold g. reflexivity.
             }
             rewrite append_assoc. rewrite <- H2. apply H.
             unfold g. apply trace_refine_converge_bind with (r := r); auto.
             rewrite <- H1. apply may_converge_append. apply finite_list_to_stream.
        * right. split.
          ++ apply append_div; auto.
          ++ unfold append.
             rewrite bind_bind. apply H.
             apply trace_refine_diverge_bind; auto.
     + apply decompose_trace_refine_bind in H0 as Hbind.
       basic_solve. apply H in H2 as ?H. destruct (classic_converge_itrace b'); basic_solve.
       *
         (* easily convince myself that H is unused without needing the refactor rest*)
         clear H. assert (H : True); auto.

         assert (Hbind : (ITree.bind b' g' ⊑ ITree.bind m f)).
         { rewrite H1. auto. }
         rewrite <- H4 in H1.
         setoid_rewrite bind_bind in H1.
         setoid_rewrite bind_ret_l in H1.
         assert (↑ log0 ++ (g' r) ≈ b)%itree; auto. clear H1.
         specialize (H5 (g' r) ).  rewrite <- H6 in H0.


         assert (↑log ++ b ≈ ↑log' ++ g' r /\ a = r)%itree.
         {
           rewrite <- H6. rewrite <- H4 in H3.
           rewrite <- append_assoc. rewrite <- append_assoc in H3. apply inv_append_eutt in H3.
           destruct H3. subst. split; reflexivity.
         }
         destruct H1 as [Hevsplit ?]. subst. rewrite Hevsplit.
         (*Hevsplit : log ++ n ≈ log' ++ g' r*)
         apply H5.
         (* then need to show g' r ⊑ f r*)
         rewrite H6 in H0.
         (* comes from trace_refine_bind_cont_inv
            because b' converges to r and b' >>= g' ⊑ m >>= f
          *)
         apply trace_refine_bind_cont_inv with (r:= r) in Hbind; auto.
         rewrite <- H4. eapply may_converge_append. apply finite_list_to_stream.
       * eapply bind_split_diverge; eauto.
       * assert (may_converge a b').
         { eapply may_converge_two_list; eauto. }
         exfalso. eapply all_infinite_not_converge; eauto.
       * eapply bind_split_diverge; eauto.
  Qed.

  #[global] Instance TraceSpecOrder : OrderM TraceSpec :=
    fun _ w1 w2 => forall log p, p ∈ (w2 log) -> p ∈ (w1 log).

  #[global] Instance TraceSpecOrderLaws : OrderedMonad TraceSpec.
  Proof.
    constructor.
    - intros. repeat red. auto.
    - intros. repeat red in H. repeat red in H0.
      repeat red. intros. apply H. apply H0. auto.
    - intros. repeat red in H0. repeat red in H. repeat red. intros. repeat red in H1.
      eapply H. destruct (w2 log) as [w2' Hw2]. cbn. eapply Hw2; try apply H1.
      intros. cbn in *. basic_solve.
      + left. exists a. exists log'. split; auto.
        eapply H0. auto.
      + right. auto.
  Qed.

  (* This verifies that an itree abides by a trace specification across all of its branching paths.

     This is a soundness property, and does *NOT* verify that the
     itree is complete, i.e., it doesn't ensure that the itree can
     exhibit every trace.
   *)
  Definition verify_cond {A : Type} : TraceSpec A -> itree E A -> Prop :=
    DijkstraProp (itree E) TraceSpec TraceSpecObs A.

  (* For any trace in the spec, the trace exists in the itree t *)
  Definition complete_cond {A : Type} (spec : TraceSpec A) (t : itree E A) : Prop :=
    (* Should log just be nil here? *)
    forall log p b,
      proj1_sig (spec log) p ->
      proj1_sig p b ->
      b ⊑ t.

  Definition sound_and_complete_cond {A : Type} (spec : TraceSpec A) (t : itree E A) : Prop :=
    verify_cond spec t /\ complete_cond spec t.

  Program Definition encode {A : Type} (post : itrace E A -> Prop) (pre : ev_list E -> Prop) : TraceSpec A :=
    fun log p => pre log /\ forall b, post (↑ log ++ b) -> p (↑ log ++ b).

  Program Definition encode_dyn {A : Type} (post : ev_list E -> itrace E A -> Prop) (pre : ev_list E -> Prop) : TraceSpec A :=
    fun log p => pre log /\ forall b, post log (↑ log ++ b) -> p (↑ log ++ b).

End TraceSpec.

Arguments TraceSpecMonad {E}.
Arguments TraceSpecMonadLaws {E}.
Arguments TraceSpecOrder {E}.
Arguments TraceSpecOrderLaws {E}.
Arguments TraceSpecObs {E}.
Arguments TraceSpecMorph {E}.

Section NonDetExample.

Variant NonDet : Type -> Prop :=
  Decide : NonDet bool.

Definition decide_ex : itree NonDet unit :=
  ITree.iter (fun _ => ITree.bind (trigger Decide) (fun b : bool => if b then Ret (inl tt) else Ret (inr tt) )) tt.

Definition decide_ex_pre : ev_list NonDet -> Prop := fun log => log = nil.

Variant is_bool (b : bool) : forall A, EvAns NonDet A -> Prop :=
  | is_bool_matches : is_bool b unit (evans bool Decide b)
.

Hint Constructors is_bool : itree.

Definition fal_decide_ex : itrace NonDet unit -> Prop :=
  front_and_last (is_bool true) (is_bool false) (fun _ => True).

Definition decide_ex_post : itrace NonDet unit -> Prop :=
  fun b => (all_infinite b -> trace_forall (is_bool true) (fun _ => True) b) /\
        (may_converge tt b -> fal_decide_ex b).

Lemma decide_ex_satisfies_spec : verify_cond NonDet (encode NonDet decide_ex_post decide_ex_pre ) decide_ex.
Proof.
  repeat red. cbn. intros. destruct H as [Hlog H].
  red in Hlog. apply H. clear H. subst. cbn. red. split; intros.
  - unfold append in *. rewrite bind_ret_l in H. rewrite bind_ret_l.
    unfold decide_ex in *.
    generalize dependent b. pcofix CIH. intros b Hb Hdiv.
    pfold. red.
    rewrite unfold_iter in Hb at 1. rewrite bind_bind in Hb.
    apply bind_trigger_refine in Hb as Hb'; try (exists true; auto).
    basic_solve. destruct a.
    + rewrite bind_ret_l in H0. cbn in H0. rewrite tau_eutt in H0.
      punfold H. red in H. cbn in H. clear Hb.
      enough (paco1 (trace_forall_ (is_bool true) (fun _ => True) ) r b).
      { punfold H1. }
      dependent induction H.
      *  pfold. red. rewrite <- x. constructor; auto with itree. intros.
        destruct a. right. pclearbot. eapply CIH.
        ++ assert (k1 tt ≈ k' tt)%itree; try apply REL.
           rewrite H. auto.
        ++ apply simpobs in x. rewrite x in Hdiv. pinversion Hdiv.
           ddestruction. apply H1.
      *  pfold. red. rewrite <- x. constructor. left.  eapply IHeqitF; eauto.
         apply simpobs in x. rewrite x in Hdiv. rewrite tau_eutt in Hdiv. auto.
   + rewrite bind_ret_l in H0. cbn in H0. apply trace_refine_ret_inv_l in H0.
     rewrite H in Hdiv. pinversion Hdiv. ddestruction.
     specialize (H2 tt).
     rewrite H0 in H2. pinversion H2.
  - red. rewrite append_nil. rewrite append_nil in H. unfold decide_ex in *.
    induction H.
    + exfalso. rewrite H in H0. rewrite unfold_iter in H0.
      rewrite bind_bind in H0. rewrite bind_trigger in H0.
      revert H0; apply refine_ret_vis_contra.
    + rewrite H. destruct e; try contradiction.
      destruct b. destruct ev. destruct ans.
      * eapply front_and_last_cons; eauto; try reflexivity. apply IHmay_converge.
        clear IHmay_converge. rewrite unfold_iter in H0. rewrite bind_bind in H0.
        rewrite H in H0. eapply bind_trigger_refine in H0; try (exists true; auto).
        basic_solve.
        pinversion H0. ddestruction.
        assert (k tt ≈ k' tt)%itree; try apply REL. rewrite bind_ret_l in H2.
        cbn in *. rewrite tau_eutt in H2. rewrite H3. auto.
      * clear IHmay_converge. rewrite unfold_iter in H0. rewrite bind_bind in H0.
        rewrite H in H0. eapply bind_trigger_refine in H0; try (exists true; auto).
        basic_solve.
        pinversion H0. ddestruction.
        rewrite bind_ret_l in H2. cbn in H2.
        apply trace_refine_ret_inv_l in H2.
        eapply front_and_last_base with (r := tt); eauto with itree.
        pfold. red. cbn. constructor. intros. left.
        rewrite <- H2. destruct v. auto.
  Qed.

End NonDetExample.
