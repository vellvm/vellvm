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
     Utils.MonadReturnsLaws
     Utils.MonadEq1Laws.

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
