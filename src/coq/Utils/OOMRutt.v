From Coq Require Import
     Morphisms.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Basics.Tacs
     Axioms
     ITree
     Eq
     Eq.Rutt
     Basics.

From Paco Require Import paco.

From Vellvm Require Import
  Utils.PropT.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

(* TODO: Move this? *)
Ltac inj_pair2_existT :=
  repeat
      match goal with
      | H : _ |- _ => apply inj_pair2 in H
      end.

Ltac subst_existT :=
  inj_pair2_existT; subst.

Section ORuttF.

  Context {E1 E2 OOM : Type -> Type}.
  Context {OOME : OOM -< E2}.
  Context {R1 R2 : Type}.
  Context (REv : forall (A B : Type), E1 A -> E2 B -> Prop ).
  Context (RAns : forall (A B : Type), E1 A -> A -> E2 B -> B -> Prop ).
  Context (RR : R1 -> R2 -> Prop).
  Arguments REv {A} {B}.
  Arguments RAns {A} {B}.

  Inductive oruttF (sim : itree E1 R1 -> itree E2 R2 -> Prop) : itree' E1 R1 -> itree' E2 R2 -> Prop :=
  | EqRet : forall (r1 : R1) (r2 : R2),
      RR r1 r2 ->
      oruttF sim (RetF r1) (RetF r2)
  | EqTau : forall (m1 : itree E1 R1) (m2 : itree E2 R2),
      sim m1 m2 ->
      oruttF sim (TauF m1) (TauF m2)
  | EqVis : forall (A B : Type) (e1 : E1 A) (e2 : E2 B ) (k1 : A -> itree E1 R1) (k2 : B -> itree E2 R2),
      REv e1 e2 ->
      (forall (a : A) (b : B), RAns e1 a e2 b -> sim (k1 a) (k2 b)) ->
      (forall (o : OOM B), e2 <> subevent _ o) ->
      oruttF sim (VisF e1 k1) (VisF e2 k2)
  | EqVisOOM : forall A (e : OOM A) t1 (k2 : A -> _),
      (* If t2 is some OOM event, then any t1 on the left will do. *)
      oruttF sim t1 (VisF (subevent _ e) k2)
  | EqTauL : forall (t1 : itree E1 R1) (ot2 : itree' E2 R2),
      oruttF sim (observe t1) ot2 ->
      oruttF sim (TauF t1) ot2
  | EqTauR : forall (ot1 : itree' E1 R1) (t2 : itree E2 R2),
      oruttF sim ot1 (observe t2) ->
      oruttF sim ot1 (TauF t2).
  Hint Constructors oruttF : itree.

  Definition orutt_ (sim : itree E1 R1 -> itree E2 R2 -> Prop)
             (t1 : itree E1 R1) (t2 : itree E2 R2) :=
    oruttF sim (observe t1) (observe t2).
  Hint Unfold orutt_ : itree.

  Lemma orutt_monot : monotone2 orutt_.
  Proof using.
    red. intros. red; induction IN; eauto with itree.
  Qed.

  Definition orutt : itree E1 R1 -> itree E2 R2 -> Prop := paco2 orutt_ bot2.
  Hint Unfold orutt : itree.

  Lemma oruttF_inv_VisF_r {sim} t1 U2 (e2: E2 U2) (k2: U2 -> _):
    oruttF sim t1 (VisF e2 k2) ->
    (exists U1 (e1: E1 U1) k1, t1 = VisF e1 k1 /\
      forall v1 v2, RAns e1 v1 e2 v2 -> sim (k1 v1) (k2 v2))
    \/
    (exists t1', t1 = TauF t1' /\
              oruttF sim (observe t1') (VisF e2 k2))
    \/
      (exists (o : OOM U2),
          e2 = subevent _ o).
  Proof using.
    refine (fun H =>
      match H in oruttF _ _ t2 return
        match t2 return Prop with
        | VisF e2 k2 => _
        | _ => True
        end
      with
      | EqVis _ _ _ _ _ _ _ _ _ _ => _
      | _ => _
      end); try exact I.
    - left; eauto.
    - right; right.
      exists o.
      reflexivity.
    - destruct i0; eauto.
  Qed.

  Lemma oruttF_inv_VisF {sim}
      U1 U2 (e1 : E1 U1) (e2 : E2 U2) (k1 : U1 -> _) (k2 : U2 -> _)
    : oruttF sim (VisF e1 k1) (VisF e2 k2) ->
      (forall (o : OOM U2), ~ (e2 = subevent _ o)) ->
      forall v1 v2, RAns e1 v1 e2 v2 -> sim (k1 v1) (k2 v2).
  Proof using.
    intros H NOOOM.
    inversion H;
      subst_existT.

    assumption.

    specialize (NOOOM e0).
    exfalso.
    apply NOOOM.
    reflexivity.
  Qed.

  Ltac unfold_orutt :=
    (try match goal with [|- orutt_ _ _ _ _ _ _ _ ] => red end);
    (repeat match goal with [H: orutt_ _ _ _ _ _ _ _ |- _ ] => red in H end).

  Lemma fold_oruttF:
    forall (t1: itree E1 R1) (t2: itree E2 R2) ot1 ot2,
    oruttF (upaco2 orutt_ bot2) ot1 ot2 ->
    ot1 = observe t1 ->
    ot2 = observe t2 ->
    orutt t1 t2.
  Proof using.
    intros * eq -> ->; pfold; auto.
  Qed.
End ORuttF.

Tactic Notation "fold_oruttF" hyp(H) :=
  try punfold H;
  try red in H;
  match type of H with
  | oruttF ?_REV ?_RANS ?_RR (upaco2 (orutt_ ?_REV ?_RANS ?_RR) bot2) ?_OT1 ?_OT2 =>
      match _OT1 with
      | observe _ => idtac
      | ?_OT1 => rewrite (itree_eta' _OT1) in H
      end;
      match _OT2 with
      | observe _ => idtac
      | ?_OT2 => rewrite (itree_eta' _OT2) in H
      end;
      eapply fold_oruttF in H; [| eauto | eauto]
  end.

#[global] Hint Resolve orutt_monot : paco.

Section ConstructionInversion.
Variables (E1 E2 OOM: Type -> Type).
Context {OOME : OOM -< E2}.
Variables (R1 R2: Type).
Variable (REv: forall T1 T2, E1 T1 -> E2 T2 -> Prop).
Variable (RAns: forall T1 T2, E1 T1 -> T1 -> E2 T2 -> T2 -> Prop).
Variable (RR: R1 -> R2 -> Prop).

Lemma orutt_Ret r1 r2:
  RR r1 r2 ->
  @orutt E1 E2 OOM OOME R1 R2 REv RAns RR (Ret r1: itree E1 R1) (Ret r2: itree E2 R2).
Proof using. intros. pstep; constructor; auto. Qed.

Lemma orutt_inv_Ret r1 r2:
  @orutt E1 E2 OOM OOME R1 R2 REv RAns RR (Ret r1) (Ret r2) -> RR r1 r2.
Proof using.
  intros. punfold H. inv H. eauto.
Qed.

Lemma orutt_inv_Ret_l r1 t2:
  @orutt E1 E2 OOM OOME R1 R2 REv RAns RR (Ret r1) t2 ->
  (exists r2, t2 ≳ Ret r2 /\ RR r1 r2) \/
    (exists X (o : OOM X) k2,
        t2 ≈ vis o k2).
Proof using.
  intros Hrutt; punfold Hrutt; red in Hrutt; cbn in Hrutt.
  setoid_rewrite (itree_eta t2). remember (RetF r1) as ot1; revert Heqot1.
  induction Hrutt; intros; try discriminate.
  - inversion Heqot1; subst. left; exists r2; split; [reflexivity|auto].
  - right.
    exists A, e.
    exists k2.
    reflexivity.
  - destruct (IHHrutt Heqot1) as [[r2 [H1 H2]] | [X [o [k2 OOM']]]].
    + left; exists r2; split; auto.
      rewrite <- itree_eta in H1. now rewrite tau_euttge.
    + right.
      exists X.
      exists o.
      exists k2.

      rewrite tau_eutt.
      rewrite itree_eta; auto.      
Qed.

Lemma orutt_inv_Ret_r t1 r2:
  @orutt E1 E2 OOM OOME R1 R2 REv RAns RR t1 (Ret r2) -> exists r1, t1 ≳ Ret r1 /\ RR r1 r2.
Proof using.
  intros Hrutt; punfold Hrutt; red in Hrutt; cbn in Hrutt.
  setoid_rewrite (itree_eta t1). remember (RetF r2) as ot2; revert Heqot2.
  induction Hrutt; intros; try discriminate.
  - inversion Heqot2; subst. exists r1. split; [reflexivity|auto].
  - destruct (IHHrutt Heqot2) as [r1 [H1 H2]]. exists r1; split; auto.
    rewrite <- itree_eta in H1. now rewrite tau_euttge.
Qed.

Lemma orutt_inv_Tau_l t1 t2 :
  @orutt E1 E2 OOM OOME R1 R2 REv RAns RR (Tau t1) t2 ->
  @orutt E1 E2 OOM OOME R1 R2 REv RAns RR t1 t2.
Proof using.
  intros. punfold H. red in H. simpl in *.
  remember (TauF t1) as tt1. genobs t2 ot2.
  hinduction H before t1; intros; try discriminate.
  - inv Heqtt1. pclearbot. pstep. red. simpobs. econstructor; eauto. pstep_reverse.
  - subst.
    pfold.
    red.
    rewrite <- Heqot2.
    constructor.
  - inv Heqtt1. punfold_reverse H.
  - subst.
    red in IHoruttF. pstep. red; simpobs. econstructor; eauto. pstep_reverse.
Qed.

Lemma orutt_add_Tau_l t1 t2 :
  @orutt E1 E2 OOM OOME R1 R2 REv RAns RR t1 t2 -> @orutt E1 E2 OOM OOME R1 R2 REv RAns RR (Tau t1) t2.
Proof using.
  intros. pfold. red. cbn. constructor. pstep_reverse.
Qed.

Lemma orutt_inv_Tau_r t1 t2 :
  @orutt E1 E2 OOM OOME R1 R2 REv RAns RR t1 (Tau t2) -> @orutt E1 E2 OOM OOME R1 R2 REv RAns RR t1 t2.
Proof using.
  intros. punfold H. red in H. simpl in *.
  pstep. red. remember (TauF t2) as tt2 eqn:Ett2 in H.
  revert t2 Ett2; induction H; try discriminate; intros; inversion Ett2; subst; auto.
  - pclearbot. constructor. pstep_reverse.
  - constructor. eapply IHoruttF; eauto.
Qed.

Lemma orutt_add_Tau_r t1 t2 :
  @orutt E1 E2 OOM OOME R1 R2 REv RAns RR t1 t2 -> @orutt E1 E2 OOM OOME R1 R2 REv RAns RR t1 (Tau t2).
Proof using.
  intros. pfold. red. cbn. constructor. pstep_reverse.
Qed.

Lemma orutt_inv_Tau t1 t2 :
  @orutt E1 E2 OOM OOME R1 R2 REv RAns RR (Tau t1) (Tau t2) -> @orutt E1 E2 OOM OOME R1 R2 REv RAns RR t1 t2.
Proof using.
  intros; apply orutt_inv_Tau_r, orutt_inv_Tau_l; assumption.
Qed.

Lemma orutt_Vis {T1 T2} (e1: E1 T1) (e2: E2 T2)
    (k1: T1 -> itree E1 R1) (k2: T2 -> itree E2 R2):
  REv _ _ e1 e2 ->
  (forall t1 t2, RAns _ _ e1 t1 e2 t2 -> @orutt E1 E2 OOM OOME R1 R2 REv RAns RR (k1 t1) (k2 t2)) ->
  (forall o : OOM T2, e2 <> subevent T2 o) ->
  @orutt E1 E2 OOM OOME R1 R2 REv RAns RR (Vis e1 k1) (Vis e2 k2).
Proof using.
  intros He Hk. pstep; constructor; auto.
  intros; left. apply Hk; auto.
Qed.

Lemma orutt_inv_Vis_l {U1} (e1: E1 U1) k1 t2:
  @orutt E1 E2 OOM OOME R1 R2 REv RAns RR (Vis e1 k1) t2 ->
  (exists U2 (e2: E2 U2) k2,
    t2 ≈ Vis e2 k2 /\
    REv _ _ e1 e2 /\
      (forall v1 v2, RAns _ _ e1 v1 e2 v2 -> @orutt E1 E2 OOM OOME R1 R2 REv RAns RR (k1 v1) (k2 v2))) \/
    (exists U2 (o : OOM U2) k2,
        t2 ≈ Vis (subevent _ o) k2).
Proof using.
  intros Hrutt; punfold Hrutt; red in Hrutt; cbn in Hrutt.
  setoid_rewrite (itree_eta t2). remember (VisF e1 k1) as ot1; revert Heqot1.
  induction Hrutt; intros; try discriminate; subst.
  - inversion Heqot1; subst A. inversion_sigma; rewrite <- eq_rect_eq in *;
      subst; rename B into U2.
    left.
    exists U2, e2, k2; split. reflexivity. split; auto.
    intros v1 v2 HAns. specialize (H0 v1 v2 HAns). red in H0. now pclearbot.
  - right.
    exists A, e, k2.
    reflexivity.
  - destruct (IHHrutt eq_refl) as [(U2 & e2 & k2 & Ht0 & HAns) | [X [o [k2 OOM']]]].
    + left.
      rewrite <- itree_eta in Ht0.
      exists U2, e2, k2; split; auto. now rewrite tau_eutt.
    + right.
      exists _, o, k2.
      rewrite tau_eutt.
      rewrite itree_eta; auto.
Qed.

Lemma orutt_inv_Vis_r {U2} t1 (e2: E2 U2) k2:
  @orutt E1 E2 OOM OOME R1 R2 REv RAns RR t1 (Vis e2 k2) ->
  (exists U1 (e1: E1 U1) k1,
      t1 ≈ Vis e1 k1 /\
        REv U1 U2 e1 e2 /\
        (forall v1 v2, RAns _ _ e1 v1 e2 v2 -> @orutt E1 E2 OOM OOME R1 R2 REv RAns RR (k1 v1) (k2 v2))) \/
    (exists (o : OOM U2),
        e2 = subevent _ o).
Proof using.
  intros Hrutt; punfold Hrutt; red in Hrutt; cbn in Hrutt.
  setoid_rewrite (itree_eta t1). remember (VisF e2 k2) as ot2; revert Heqot2.
  induction Hrutt; intros; try discriminate; subst.
  - inversion Heqot2; subst B. inversion_sigma; rewrite <- eq_rect_eq in *;
      subst; rename A into U1.
    left.
    exists U1, e1, k1; split. reflexivity. split; auto.
    intros v1 v2 HAns. specialize (H0 v1 v2 HAns). red in H0. now pclearbot.
  - dependent destruction Heqot2.
    right.
    exists e. reflexivity.
  - destruct (IHHrutt eq_refl) as [(U1 & e1 & k1 & Ht0 & HAns) | [o EQ]].
    + rewrite <- itree_eta in Ht0.
      left.
      exists U1, e1, k1; split; auto. now rewrite tau_eutt.
    + right.
      exists o; auto.
Qed.

Lemma orutt_inv_Vis U1 U2 (e1: E1 U1) (e2: E2 U2)
    (k1: U1 -> itree E1 R1) (k2: U2 -> itree E2 R2):
  @orutt E1 E2 OOM OOME R1 R2 REv RAns RR (Vis e1 k1) (Vis e2 k2) ->
  ((forall u1 u2, RAns U1 U2 e1 u1 e2 u2 -> @orutt E1 E2 OOM OOME R1 R2 REv RAns RR (k1 u1) (k2 u2)) \/    
    (exists (o : OOM U2),
        e2 = subevent _ o)).
Proof using.
  intros H.
  pinversion H; subst_existT.
  - left.
    intros u1 u2 H0.
    apply oruttF_inv_VisF with (v1 := u1) (v2 := u2) in H. pclearbot; auto.

    intros o CONTRA;
      eapply H8; eauto.

    auto.
  - right.
    eexists; eauto.
Qed.
End ConstructionInversion.

(*replicate this proof for the models functor*)
(* Validity of the up-to [euttge] principle *)
Lemma euttge_trans_clo_wcompat E1 E2 OOM OOME R1 R2 (REv : forall A B, E1 A -> E2 B -> Prop)
      (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop ) (RR : R1 -> R2 -> Prop) :
  wcompatible2 (@orutt_ E1 E2 OOM OOME R1 R2 REv RAns RR) (euttge_trans_clo RR).
Proof using.
  constructor; eauto with paco.
  { red. intros. eapply euttge_trans_clo_mon; eauto. }
  intros.
  destruct PR. punfold EQVl. punfold EQVr. unfold_eqit.
  hinduction REL before r; intros; clear t1' t2'.
  - remember (RetF r1) as x. red.
    hinduction EQVl before r; intros; subst; try inv Heqx; eauto; (try constructor; eauto).
    remember (RetF r3) as x. hinduction EQVr before r; intros; subst; try inv Heqx; (try constructor; eauto).
  - red. remember (TauF m1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; ( try (constructor; eauto; fail )).
    remember (TauF m3) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; (try (constructor; eauto; fail)).
    pclearbot. constructor. gclo. econstructor; eauto with paco.
  - remember (VisF e1 k1) as x. red.
    hinduction EQVl before r; intros; subst; try discriminate; try (constructor; eauto; fail).
    remember (VisF e2 k3) as y.
    hinduction EQVr before r; intros; subst; try discriminate; try (constructor; eauto; fail).
    dependent destruction Heqx.
    dependent destruction Heqy.
    constructor; auto. intros. apply H0 in H2. pclearbot.
    apply gpaco2_clo.
    econstructor; eauto with itree.
  - remember (VisF (subevent A e) k2) as y. red.    
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; (try (constructor; eauto; fail)).

    subst_existT.
    constructor.
  - remember (TauF t1) as x. red.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; (try (constructor; eauto; fail)).
    pclearbot. punfold REL. constructor. eapply IHREL; eauto.
  - remember (TauF t2) as y. red.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; (try (constructor; eauto; fail)).
    pclearbot. punfold REL. constructor. eapply IHREL; eauto.
Qed.

#[global] Hint Resolve euttge_trans_clo_wcompat : paco.

(* The validity of the up-to [euttge] entails we can rewrite under [euttge]
   and hence also [eq_itree] during coinductive proofs of [orutt]
*)
#[global] Instance gorutt_cong_eqit {R1 R2 : Type} {E1 E2 OOM : Type -> Type} OOME {REv : forall A B, E1 A -> E2 B -> Prop}
       {RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop} {RR1 RR2} {RS : R1 -> R2 -> Prop} r rg
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y) :
  Proper (eq_itree RR1 ==> eq_itree RR2 ==> flip impl)
         (gpaco2 (@orutt_ E1 E2 OOM OOME R1 R2 REv RAns RS) (euttge_trans_clo RS) r rg).
Proof using.
  repeat intro. gclo. econstructor; eauto;
    try eapply eqit_mon; try apply H; try apply H0; auto.
Qed.

#[global] Instance gorutt_cong_euttge {R1 R2 : Type} {E1 E2 OOM : Type -> Type} OOME {REv : forall A B, E1 A -> E2 B -> Prop}
       {RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop} {RR1 RR2} {RS : R1 -> R2 -> Prop} r rg
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y) :
  Proper (euttge RR1 ==> euttge RR2 ==> flip impl)
         (gpaco2 (@orutt_  E1 E2 OOM OOME R1 R2 REv RAns RS) (euttge_trans_clo RS) r rg).
Proof using.
  repeat intro. gclo. econstructor; eauto.
Qed.

(* Provide these explicitly since typeclasses eauto cannot infer them *)

#[global] Instance gorutt_cong_eqit_eq {R1 R2 : Type} {E1 E2 OOM : Type -> Type} OOME {REv : forall A B, E1 A -> E2 B -> Prop}
      {RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop} {RS : R1 -> R2 -> Prop} r rg:
    Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (gpaco2 (@orutt_ E1 E2 OOM OOME R1 R2 REv RAns RS) (euttge_trans_clo RS) r rg).
Proof using.
  apply gorutt_cong_eqit; now intros * ->.
Qed.

#[global] Instance gorutt_cong_euttge_eq {R1 R2 : Type} {E1 E2 OOM : Type -> Type} OOME {REv : forall A B, E1 A -> E2 B -> Prop}
      {RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop} {RS : R1 -> R2 -> Prop} r rg:
    Proper (euttge eq ==> euttge eq ==> flip impl)
         (gpaco2 (@orutt_ E1 E2 OOM OOME R1 R2 REv RAns RS) (euttge_trans_clo RS) r rg).
Proof using.
  apply gorutt_cong_euttge; now intros * ->.
Qed.
