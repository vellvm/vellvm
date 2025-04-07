From Coq Require Import
     Arith
     String.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Core.RelDec
     Data.Map.FMapAList.

From Paco Require Import paco.

From ITree Require Import
     Axioms
     ITree
     ITreeFacts
     Eq.Rutt
     Events.MapDefault
     Events.State
     Events.StateFacts.

From ITree.Extra Require Import
     ITrace.ITraceDefinition
     ITrace.ITraceFacts
     ITrace.ITracePreds
     Dijkstra.DelaySpecMonad
     Dijkstra.DijkstraMonad
     Dijkstra.TracesIT
     Dijkstra.StateSpecT.

Import Monads.
Import MonadNotation.
#[local] Open Scope monad_scope.

Definition env := alist string nat.

Variant StateE : Type -> Type :=
  | GetE : string -> StateE nat
  | PutE : string -> nat -> StateE unit
.

Variant IO : Type -> Type :=
  | Read : IO nat
  | Write : nat -> IO unit
.
Notation stateiotree A := (itree (StateE +' IO) A).

Definition StateIOSpec : Type -> Type := StateSpecT env (TraceSpec IO).

Definition SIOSpecOrder := StateSpecTOrder env (TraceSpec IO).

Definition SIOSpecOrderLaws := StateSpecTOrderedLaws env (TraceSpec IO).

Definition SIOSpecEq  := StateSpecTEq env (TraceSpec IO).

Definition SIOObs := EffectObsStateT env (TraceSpec IO) (itree IO).

Definition SIOMorph :=MonadMorphimStateT env (TraceSpec IO) (itree IO).

Definition verify_cond {A : Type} := DijkstraProp (stateT env (itree IO)) StateIOSpec SIOObs A.

(*Predicate on initial state and initial log*)
Definition StateIOSpecPre : Type := env -> ev_list IO -> Prop.
(*Predicate on final log and possible return value*)
Definition StateIOSpecPost (A : Type) : Type := itrace IO (env * A) -> Prop.

Program Definition encode {A} (pre : StateIOSpecPre) (post : StateIOSpecPost A) : StateIOSpec A :=
  fun s log p => pre s log /\ (forall tr, post tr -> p tr).


Section PrintMults.
  Variable X Y : string.
  Context (HXY : X <> Y).
  (*this part has some pretty basic errors*)
  Variant write_next_mult  (n : nat) : forall B, IO B -> B -> Prop :=
    | wnm : write_next_mult n unit (Write n) tt.

  Definition wnm_ev (next : nat) A  (io : IO A) (_ : A) : forall B, IO B -> B -> Prop :=
    match io with
    | Write n => write_next_mult (next + n)
    | Read => bot3 end.

  Variant writes_n (n : nat) : forall A, IO A -> A -> Prop :=
    | wn : writes_n n unit (Write n) tt.

  Definition mults_n {R : Type} (n : nat) (tr : itrace IO R) := state_machine (wnm_ev n) bot4 (writes_n 0) bot1 tr.

  CoFixpoint mults_of_n_from_m {R : Type} (n m : nat) : itrace IO R:=
    Vis (evans unit (Write m) tt) (fun _ => mults_of_n_from_m n (n + m) ).

  Definition mults_of_n {R : Type} (n : nat) : itrace IO R :=
    mults_of_n_from_m n 0.

  Definition print_mults_pre : StateIOSpecPre :=
    fun s log => log = nil /\  lookup_default Y 0 s = 0.

  (*Is there going to be a problem introducing k?*)
  Definition print_mults_post : StateIOSpecPost unit :=
    fun tr => exists n k, (tr ≈ Vis (evans _ Read n) k /\ (mults_of_n n) ≈ (k tt))%itree.

  Definition print_mults : stateiotree unit :=
   x <- trigger Read;;
   trigger (PutE X x);;
   ITree.iter ( fun _ : unit =>
    y <- trigger (GetE Y);;
    trigger (Write y);;
    x <- trigger (GetE X);;
    trigger (PutE Y (y + x));;
    Ret (inl tt)
   ) tt.


  Definition add (V : string) (v : nat) (s : env) : env :=
    alist_add _ V v s.

  Definition handleIOStateE (A : Type) (ev : (StateE +' IO) A) : stateT env (itree IO) A :=
    fun s =>
    match ev with
    | inl1 ev' =>
      match ev' with
      | GetE V => Ret (s, lookup_default V 0 s)
      | PutE V v => Ret (Maps.add V v s, tt) end
    | inr1 ev' => Vis ev' (fun x => Ret (s,x) )
    end.

  Ltac unf_res := unfold resum, ReSum_id, id_, Id_IFun in *.

  Lemma lookup_eq : forall (s : env) (x : string) (v d : nat),
    lookup_default x d (Maps.add x v s) = v.
  Proof.
    intros. assert (Maps.mapsto x v (Maps.add x v s) ).
    { apply Maps.mapsto_add_eq; try reflexivity. }
    eapply Maps.mapsto_lookup in H. unfold lookup_default. rewrite H. auto.
  Qed.

  Lemma lookup_nin : forall (x : string) (s : env), (forall v : nat, ~ Maps.mapsto x v s) -> Maps.lookup x s = None.
  Proof.
    intros. red in s. red in s. generalize dependent x. induction s; intros; auto.
    - cbn. destruct a as [y v]. destruct (Strings.String.string_dec x y).
      + subst. exfalso. eapply H. red. cbn. red. cbn.
        rewrite RelDec.rel_dec_eq_true; auto. apply RelDec_Correct_string.
      + rewrite RelDec.rel_dec_neq_false; auto; try apply RelDec_Correct_string.
        unfold Maps.lookup in IHs. cbn in *. apply IHs; auto. intros.
        intro Hcontra. eapply H. red. cbn.
        rewrite RelDec.rel_dec_neq_false; eauto; try apply RelDec_Correct_string.
  Qed.

  Lemma lookup_neq : forall (s : env) (x y: string) (v d: nat), x <> y ->
                                                          lookup_default x d (Maps.add y v s)  = lookup_default x d s.
  Proof.

    intros.
    destruct (classic (exists v', Maps.mapsto x v' s)).
    - destruct H0 as [v' Hv'].
      assert (Maps.mapsto x v' (Maps.add y v s)).
      {
        eapply Maps.mapsto_add_neq in Hv'; eauto.
      }
      apply Maps.mapsto_lookup in H0. apply Maps.mapsto_lookup in Hv'. unfold lookup_default.
      rewrite Hv'. rewrite H0. auto.
    - assert (forall v',~ Maps.mapsto x v' s).
      { intros v' Hc. apply H0. exists v'. auto. }
      clear H0. apply lookup_nin in H1 as Hs. unfold lookup_default.
      rewrite Hs.
      assert (forall v', ~Maps.mapsto x v' (Maps.add y v s)).
      {
        intros v' Hcontra. apply Maps.mapsto_add_neq in Hcontra; auto.
        eapply H1; eauto.
      }
      apply lookup_nin in H0 as Hs'. rewrite Hs'. auto.
  Qed.

  Ltac prove_arg H :=
    let H' := fresh H in
    match type of H with ?P -> _ => assert (H' : P); try (specialize (H H'); clear H') end.

  Lemma print_mults_sats_spec :
    verify_cond (encode print_mults_pre print_mults_post) (interp_state handleIOStateE print_mults).
  Proof.
    repeat red. simpl. intros s log [p Hp] [Hpre H'] b Href. simpl in *.
    apply H'. clear H'. unfold print_mults_pre in Hpre.
    destruct Hpre as [Hlog Henv]. subst.
    unfold print_mults_post. setoid_rewrite append_nil.
    unfold print_mults in Href. setoid_rewrite interp_state_bind in Href.
    setoid_rewrite interp_state_trigger in Href.
    setoid_rewrite bind_vis in Href.
    apply trace_refine_vis in Href as Hbhd. basic_solve.
    rewrite Hbhd in Href. setoid_rewrite Hbhd.
    destruct e0.
    2 : destruct ev; assert void; try apply Hempty; try constructor; contradiction.
    assert (A = nat).
    {
      destruct ev; auto. cbn in *. pinversion Href. ddestruction; subst.
      cbn in *. inversion H1; auto.
    }
    subst. rename ans into n. exists n.
    match type of Href with
    _ ⊑ Vis _ ?k => remember k as kp end.
    exists k0. split.
    {
      simpl in Href. clear Henv. unf_res.
      pinversion Href. ddestruction; subst. inversion H1. ddestruction; subst. reflexivity.
    }
    clear Hp p Hbhd b.
    assert (k0 tt ⊑ kp n).
    { clear Heqkp. pinversion Href. ddestruction; subst.
      unfold resum, ReSum_id, id_, Id_IFun in *. inversion H1. ddestruction; subst.
      assert (RAnsRef IO unit nat (evans nat Read n) tt Read n); auto with itree.
      apply H6 in H. pclearbot. auto.
    }
    clear Href ev. subst. rewrite bind_ret_l in H. simpl in *. rewrite interp_state_bind in H.
    rewrite interp_state_trigger in H. simpl in *. rewrite bind_ret_l in H.
    simpl in *.
    specialize (@interp_state_iter' (StateE +' IO) ) as Hiter.
    unfold state_eq in Hiter. rewrite Hiter in H. clear Hiter.

    remember (Maps.add X n s) as si.
    assert (si = alist_add RelDec_string X n s); try (subst; auto; fail).
    rewrite <- H0 in H. clear H0.
    unfold mults_of_n.
    remember 0 as next_to_write.

    (*set up invariant for the coind hyp*)
    assert (lookup_default Y 0 si = next_to_write).
    { subst. rewrite lookup_neq; auto. }
    assert(lookup_default X 0 si = n).
    { subst. apply lookup_eq. }
    clear Heqsi Heqnext_to_write Henv s.
    generalize dependent si.
    remember (k0 tt) as tr. clear Heqtr k0.
    generalize dependent tr.
    generalize dependent next_to_write.

    pcofix CIH.
    (*This coinductive hypothesis looks good*)
    intros.
    rename H1 into HX.
    pfold. red.
    (*should be able to learn that observe tr is what we need*)

    (*This block shows how to proceed through the loop body*)
    rename H0 into H.
    unfold Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_itree in H.
    rewrite unfold_iter in H.
    match type of H with _ ⊑ ITree.bind _ ?k0 => remember k0 as k end.

    setoid_rewrite bind_bind in H.
    rewrite bind_trigger in H.
    setoid_rewrite interp_state_vis in H.
    cbn in H. rewrite bind_ret_l in H. rewrite tau_eutt in H.
    setoid_rewrite bind_trigger in H.
    rewrite interp_state_vis in H. cbn in H.
    rewrite bind_vis in H.
    rewrite bind_vis in H.
    setoid_rewrite bind_ret_l in H.
    unf_res.
    punfold H. red in H. cbn in *.
    dependent induction H.
    2:{ rewrite <- x. constructor; auto. eapply IHruttF; eauto; reflexivity. }
    inversion H; ddestruction; subst; ddestruction; try contradiction.
    subst. specialize (H0 tt tt).
    destruct a.
    prove_arg H0; auto with itree. pclearbot.
    match type of H0 with
      paco2 _ bot2 ?tr ?t => assert (Hk1 : tr ⊑ t); auto end.
    rewrite <- x. constructor; auto.
    intros [].
    clear x tr. right.
    remember (lookup_default X 0 si) as n.
    remember (lookup_default Y 0 si) as m.
    eapply CIH with (Maps.add Y (n + m) si); try apply lookup_eq.
    2: { rewrite lookup_neq; subst; auto. }
    rewrite tau_eutt in Hk1. setoid_rewrite bind_trigger in Hk1.
    setoid_rewrite interp_state_vis in Hk1. cbn in *.
    rewrite bind_ret_l in Hk1. rewrite tau_eutt in Hk1.
    setoid_rewrite bind_vis in Hk1.
    setoid_rewrite interp_state_vis in Hk1. cbn in *.
    rewrite bind_ret_l in Hk1. rewrite bind_ret_l in Hk1.
    rewrite tau_eutt in Hk1. cbn in *.
    rewrite interp_state_ret in Hk1. rewrite bind_ret_l in Hk1.
    cbn in *.
    rewrite tau_eutt in Hk1.
    unfold Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_itree.
    match goal with
      H : _ ⊑ ITree.iter _ (?s1, _) |- _ ⊑ ITree.iter _ (?s2, _) =>
      enough (Hseq : s2 = s1) end; try rewrite Hseq; auto.
    subst. rewrite Nat.add_comm. auto.
  Qed.

End PrintMults.
