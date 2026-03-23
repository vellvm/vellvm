From Stdlib Require Import
  Lia
  ZArith
  String
  List
  Program.Equality.

From ITree Require Import
  ITree
  HeterogeneousRelations
  Rutt
  TranslateFacts
  Eqit.

From ExtLib Require Import
  Structures.Monads
  Structures.Functor.

Require Import Paco.paco.

From Vellvm.Semantics Require Import
  MemoryAddress
  VellvmIntegers
  DynamicValues
  InterpretationStack
  TopLevel
  LLVMEvents.

From Vellvm.Semantics.InfiniteToFinite.Conversions Require Import
  BaseConversions
  DvalueConversions
  EventConversions.

From Vellvm.Utils Require Import
  Error
  Tactics
  Monads
  MapMonadExtra
  OOMRutt
  OOMRuttProps
  AListFacts
  PropT
  VellvmRelations
  ErrUbOomProp
  ErrOomPoison
  Oomable
  Poisonable.

Import MonadNotation.
Import ListNotations.


(* TODO: Move this and use this *)
Ltac destruct_err_oom_poison x :=
  destruct x as [[[[[?err_x | ?x] | ?oom_x] | ?poison_x]]] eqn:?Hx.

(* TODO: move / generalize these *)
Lemma map_monad_ErrUbOomProp_forall2 :
  forall {A B} (f : A -> ErrUbOomProp B) l res,
    @map_monad ErrUbOomProp Monad_ErrUbOomProp _ _ f l (ret res) <->
      Forall2 (fun a b => f a (ret b)) l res.
Proof.
  intros A B f.
  induction l; intros res.
  - split; intros MAP.
    + cbn in *.
      inv MAP.
      auto.
    + inv MAP.
      reflexivity.
  - split; intros MAP.
    + rewrite map_monad_unfold in MAP.
      cbn in MAP.
      repeat red in MAP.
      destruct MAP as (?&?&?&?&?).

      cbn in H0.
      destruct_err_ub_oom x; cbn in *; subst; inv H0.

      destruct H1 as [[] | H1].
      specialize (H1 x1 eq_refl).
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      cbn in H1.

      destruct_err_ub_oom x; cbn in *; subst; inv H1;
        rewrite <- H5 in H3; inv H3.

      destruct H2 as [[] | H2].
      specialize (H2 x3 eq_refl).
      rewrite <- H2 in H5.
      cbn in H5.
      rewrite H2 in H5.
      rewrite <- H2 in H4.
      cbn in H4.
      inv H4.

      constructor.
      2: {
        apply IHl.
        apply H0.
      }

      auto.
    + inv MAP.
      rewrite map_monad_unfold.
      repeat red.
      exists (ret y).
      exists (fun x => ret (x :: l')).

      apply IHl in H3.
      split; eauto.
      split; eauto.

      right.
      intros a0 H.
      cbn in H; subst.
      repeat red.
      exists (ret l').
      exists (fun l => ret (a0 :: l)).
      split; eauto.
      split; cbn; eauto.
Qed.

(* TODO: Move this *)
Lemma map_monad_ErrUbOomProp_length :
  forall {A B : Type} {xs : list A} {f : A -> ErrUbOomProp B} {res},
    @map_monad ErrUbOomProp Monad_ErrUbOomProp A B f xs (ret res) ->
    length xs = length res.
Proof.
  intros A B xs f res MAP.
  generalize dependent res.
  induction xs; intros res MAP.
  - cbn in *; inv MAP; reflexivity.
  - rewrite map_monad_unfold in MAP.
    repeat red in MAP.
    destruct MAP as (?&?&?&?&?).
    destruct_err_ub_oom x; subst; cbn in H0; inv H0.
    destruct H1 as [[] | H1].
    specialize (H1 x1 eq_refl).
    repeat red in H1.
    destruct H1 as (?&?&?&?&?).
    destruct_err_ub_oom x; cbn in H1; rewrite <- H1 in H3; inv H3.
    cbn in *.
    destruct H2 as [[] | H2].
    specialize (H2 _ eq_refl).
    rewrite <- H2 in H1.
    cbn in H1.
    rewrite <- H2 in H5.
    cbn in H5.
    inv H5.
    cbn.
    apply IHxs in H0.
    lia.
Qed.

(* TODO: can I generalize this? *)
(* TODO: Move this *)
Lemma map_monad_ErrUbOomProp_ub :
  forall {A B} (f : A -> ErrUbOomProp B) l res,
    @map_monad ErrUbOomProp Monad_ErrUbOomProp _ _ f l (raise_ub res) ->
    exists a, In a l /\ f a (raise_ub res).
Proof.
  intros A B f l b MAP.
  generalize dependent b.
  generalize dependent l.
  induction l; intros b MAP.
  - cbn in MAP.
    inv MAP.
  - cbn.
    cbn in MAP.
    repeat red in MAP.
    destruct MAP as (?&?&?&?&?).
    destruct_err_ub_oom x; subst; cbn in H0; inv H0.
    + clear H1.
      exists a; split; eauto.
    + destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; subst; cbn in H1, H3; inv H3.
      * eapply IHl in H0; eauto.
        destruct H0 as (?&?&?).
        exists x.
        split; eauto.
      * destruct H2 as [[] | H2].
        specialize (H2 x3).
        forward H2; [cbn; auto|].
        rewrite <- H2 in H5.
        inv H5.
Qed.

(* TODO: Move this *)
Lemma map_monad_orutt :
  forall {V} (elts : list V) {OOM E1 E2} `{OOME : OOM -< E2} {R1 R2} (pre : prerel E1 E2) (post : postrel E1 E2) (RR: R1 -> R2 -> Prop) (denote1 : V -> itree E1 R1) (denote2 : V -> itree E2 R2),
    (forall e,
        orutt pre post RR (denote1 e) (denote2 e) (OOM:=OOM)) ->
    orutt pre post (Forall2 RR) (map_monad denote1 elts) (map_monad denote2 elts) (OOM:=OOM).
Proof.
  intros V elts.
  induction elts; intros OOM E1 E2 OOME R1 R2 pre post RR denote1 denote2 H.
  - cbn.
    apply orutt_Ret.
    constructor.
  - cbn.
    eapply orutt_bind; eauto.
    intros r1 r2 H0.
    eapply orutt_bind; eauto.
    intros r0 r3 H1.
    eapply orutt_Ret.
    constructor; auto.
Qed.

(* TODO: move this *)
Lemma map_monad_orutt2 :
  forall {V1 V2} (elts1 : list V1) (elts2 : list V2) {OOM E1 E2} `{OOME : OOM -< E2} {R1 R2} (pre : prerel E1 E2) (post : postrel E1 E2) (VV : V1 -> V2 -> Prop) (RR: R1 -> R2 -> Prop) (denote1 : V1 -> itree E1 R1) (denote2 : V2 -> itree E2 R2),
    (Forall2 VV elts1 elts2) ->
    (forall e1 e2,
        VV e1 e2 ->
        orutt pre post RR (denote1 e1) (denote2 e2) (OOM:=OOM)) ->
    orutt pre post (Forall2 RR) (map_monad denote1 elts1) (map_monad denote2 elts2) (OOM:=OOM).
Proof.
  intros V1 V2 elts1 elts2 OOM E1 E2 OOME R1 R2 pre post VV RR denote1 denote2 VVS H.
  induction VVS.
  - cbn.
    apply orutt_Ret.
    constructor.
  - repeat rewrite map_monad_unfold.
    eapply orutt_bind; eauto.

    intros r1 r2 H1.
    eapply orutt_bind; eauto.

    intros r0 r3 H2.
    eapply orutt_Ret.
    constructor; auto.
Qed.

#[global] Hint Resolve
  map_monad_orutt
  map_monad_orutt2 : ORUTT.

Lemma ErrOOMPoison_bind_ret_inv :
  forall {A B} ma k res,
    @bind ErrOOMPoison
      (@EitherMonad.Monad_eitherT ERR_MESSAGE (OomableT Poisonable)
         (@Monad_OomableT Poisonable MonadPoisonable))
      A B
      ma k = ret res ->
    exists a, ma = ret a /\ k a = ret res.
Proof.
  intros A B ma k res H.
  destruct ma, unEitherT, unMkOomableT; inv H.
  repeat break_match_hyp_inv.
  exists a.
  split; auto.
  destruct (k a), unEitherT, unMkOomableT; inv H1.
  reflexivity.
Qed.

Lemma ErrOOMPoison_bind_raise_poison_inv :
  forall {A B} ma k dt,
    @bind ErrOOMPoison
      (@EitherMonad.Monad_eitherT ERR_MESSAGE (OomableT Poisonable)
         (@Monad_OomableT Poisonable MonadPoisonable))
      A B
      ma k = raise_poison dt ->
    ma = raise_poison dt \/ exists a, ma = ret a /\ k a = raise_poison dt.
Proof.
  intros A B ma k res H.
  destruct ma, unEitherT, unMkOomableT; inv H.
  repeat break_match_hyp_inv.
  - right.
    exists a.
    split; auto.
    cbn.
    destruct (k a), unEitherT, unMkOomableT; inv H1.
    reflexivity.
  - left.
    cbn.
    reflexivity.
Qed.

Lemma ErrOOMPoison_bind_raise_oom_inv :
  forall {A B} ma k dt,
    @bind ErrOOMPoison
      (@EitherMonad.Monad_eitherT ERR_MESSAGE (OomableT Poisonable)
         (@Monad_OomableT Poisonable MonadPoisonable))
      A B
      ma k = raise_oomable dt ->
    ma = raise_oomable dt \/ exists a, ma = ret a /\ k a = raise_oomable dt.
Proof.
  intros A B ma k res H.
  destruct ma, unEitherT, unMkOomableT; inv H.
  repeat break_match_hyp_inv.
  - right.
    exists a.
    split; auto.
    cbn.
    destruct (k a), unEitherT, unMkOomableT; inv H1.
    reflexivity.
  - left.
    cbn.
    reflexivity.
Qed.

(* TODO: Move this and consider making err_ub_oom use eq for Eq1... *)
Lemma err_ub_oom_bind_ret_l_eq :
  forall {A B} (x : A) (k : A -> err_ub_oom B),
    x <- ret x;;
    k x = k x.
Proof.
  intros A B x k.
  cbn.
  remember (k x) as kx.
  destruct_err_ub_oom kx; auto.
Qed.

#[global] Hint Extern 1 (forall _ _, subevent _ _ <> subevent _ _) => solve [intros * CONTRA; inv CONTRA] : ORUTT.
#[global] Hint Extern 1 (forall _ _ _, _ <> subevent _ _) => solve [intros * CONTRA; inv CONTRA] : ORUTT.
#[global] Hint Extern 1 (forall _ _,  _ _ <> subevent _ _) => solve [intros * CONTRA; inv CONTRA] : ORUTT.
#[global] Hint Extern 1 (_ -< _) => typeclasses eauto : core.
#[global] Hint Extern 1 (forall x y, x=y -> (orutt _ _ _ (bind _ _) (bind _ _))) => intros ? ? ?; subst : ORUTT.
#[global] Hint Extern 1 (forall _ _ , ReSum_inl _ _ _ _ _ _ _ <> subevent _ _) => solve [intros * CONTRA; inv CONTRA] : ORUTT.

#[global] Hint Unfold
  subevent resum ReSum_inr ReSum_inl
  ReSum_sum ReSum_id id_ Id_IFun case_
  Case_sum1 case_sum1 cat Cat_IFun inr_
  Inr_sum1 inl_ Inl_sum1
  : SUBEVENTS.
