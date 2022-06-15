From Coq Require Import
     List
     Morphisms.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.EitherMonad
     Data.Monads.IdentityMonad.

From ITree Require Import
     Basics.Monad.

From Vellvm Require Import
     Utils.Util
     Utils.Error
     Utils.MonadReturnsLaws
     Utils.MonadEq1Laws
     Utils.Tactics.

Require Import Lia.

Import Monads.

Import MonadNotation.
Import ListNotations.

Open Scope monad.


Lemma map_monad_length :
  forall {A B M} `{HM: Monad M} `{EQM : Monad.Eq1 M} `{LAWS : @Monad.MonadLawsE M EQM HM} `{MRET : @MonadReturns M HM EQM} `{MRETSTR : @MonadReturnsStrongBindInv M HM EQM MRET} `{EQRET : @Eq1_ret_inv M EQM HM} (xs : list A) (f : A -> M B) res,
    MReturns res (map_monad f xs) ->
    length xs = length res.
Proof.
  intros A B M HM EQ LAWS MRET MRETSTR EQRET xs.
  induction xs; intros f res Hmap.
  - cbn in Hmap.
    apply MReturns_ret_inv in Hmap; subst; auto.
  - rewrite map_monad_unfold in Hmap.
    destruct LAWS.
    destruct MRETSTR.

    pose proof Hmap as RET.
    apply MReturns_strong_bind_inv in RET as (b & Hb & RET).
    apply MReturns_strong_bind_inv in RET as (bs & Hbs & RET).

    apply MReturns_ret_inv in RET.
    subst.

    apply IHxs in Hbs.
    cbn.
    lia.
Qed.

(* TODO: can I generalize this? *)
Lemma map_monad_err_In :
  forall {A B} (f : A -> err B) l res x,
    Util.map_monad f l = ret res ->
    In x res ->
    exists y, f y = ret x /\ In y l.
Proof.
  intros A B f l res x MAP IN.
  generalize dependent l.
  induction res; intros l MAP.
  - inversion IN.
  - inversion IN; subst.
    + destruct l as [_ | h ls].
      * cbn in MAP.
        inv MAP.
      * exists h.
        cbn in MAP.
        break_match_hyp; [|break_match_hyp]; inv MAP.
        split; cbn; auto.
    + destruct l as [_ | h ls].
      * cbn in MAP.
        inv MAP.
      * cbn in MAP.
        break_match_hyp; [|break_match_hyp]; inv MAP.
        epose proof (IHres H ls Heqs0) as [y [HF INy]].
        exists y; split; cbn; eauto.
Qed.

Lemma map_monad_err_In' :
  forall {A B : Type} (f : A -> err B) (l : list A) (res : list B) (y : A),
    In y l ->
    Util.map_monad f l = ret res -> exists x, ret x = f y /\ In x res.
Proof.
  intros A B f l.
  induction l; intros res y IN MAP.
  - inversion IN.
  - inversion IN; subst.
    + cbn in MAP.
      break_match_hyp; inv MAP.
      exists b; split; auto.

      break_match_hyp; inv H0.
      left; auto.
    + cbn in MAP.
      break_match_hyp; inv MAP.
      break_match_hyp; inv H1.

      epose proof (IHl l0 _ H eq_refl) as [b' [RET IN']].
      exists b'; split; firstorder.
Qed.

(* TODO: can I generalize this? *)
Lemma map_monad_err_Nth :
  forall {A B} (f : A -> err B) l res x n,
    Util.map_monad f l = ret res ->
    Util.Nth res n x ->
    exists y, f y = ret x /\ Util.Nth l n y.
Proof.
  intros A B f l res x n MAP NTH.
  generalize dependent l. generalize dependent n. revert x.
  induction res; intros x n NTH l MAP.
  - inversion NTH.
    rewrite nth_error_nil in *; inv H0.
  - cbn in NTH.
    induction n.
    + cbn in NTH.
      inv NTH.

      destruct l as [_ | h ls].
      * cbn in MAP.
        inv MAP.
      * exists h.
        cbn in MAP.
        break_match_hyp; [|break_match_hyp]; inv MAP.
        split; cbn; auto.

    + cbn in NTH.
      destruct l as [_ | h ls].
      * cbn in MAP.
        inv MAP.
      * cbn in MAP.
        break_match_hyp; [|break_match_hyp]; inv MAP.
        epose proof (IHres _ _ NTH ls Heqs0) as [y [HF INy]].
        exists y; split; cbn; eauto.
Qed.

(* TODO: can I generalize this? *)
Lemma map_monad_err_succeeds :
  forall {A B} (f : A -> err B) l,
    (forall a, In a l -> exists b, f a = ret b) ->
    exists res, Util.map_monad f l = ret res.
Proof.
  intros A B f l IN.
  generalize dependent l.
  induction l; intros IN.
  - exists [].
    reflexivity.
  - cbn.
    forward IHl.
    { intros a0 IN'.
      eapply IN.
      right; auto.
    }

    specialize (IN a).
    forward IN; cbn; auto.
    destruct IN as (b & IN).
    destruct IHl as (res & IHl).

    exists (b :: res).
    rewrite IHl, IN.
    cbn.
    reflexivity.
Qed.
