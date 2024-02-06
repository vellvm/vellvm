(* begin hide *)
From ITree Require Import
     Eq.Eqit
     ITree
     FailFacts
     Events.Exception.

From Vellvm Require Import 
     Utils.PostConditions
     Utils.PropT
     Utils.TFor
     Utils.Tactics.



From ExtLib Require Import
     Structures.Monad.

From Coq Require Import
     Morphisms Lia.

Import ITreeNotations.
Local Open Scope itree.
(* end hide *)

(** * Reasoning about successful computations

  Compilers are typically only required to preserve the behavior of valid programs.
  Correctness statements are therefore phrased in terms "for any program c, if c
  has a well defined semantics, then ...".
  Having a well defined semantics when manipulating an operational semantics is 
  typically expressed as never reaching a blocking state, or an error state.
  In this file, we develop the necessary machinery to express and reason about 
  this same fact in an itree-based semantics.

  We choose here to assume that failure is represented using the [exceptT] domain of
  events, and to interpret this failure into a trivial option monad. 
  The property of "well definedness" of a computation is then expressed after interpretation
  using the [has_post] unary logic developed in [./Utils/PostConditions.v]: it simply asserts
  that the computation does not fail (see [no_failure]).

  Interestingly, this requires to process [eutt]-based equations forward as opposed to 
  backward: we know for an hypothesis an evidence of the form [has_post (x <- c;; k) P]
  and need to deduce information about [c] and [k]. It so happens that one needs to be
  a little bit more careful when processing monadic equivalences forward than backward:
  we use to this end notably [eutt_clo_bind_returns].

  This approach is heavily used in the Helix development.

*)

(* For some reason the new definition of [ecofix] in itrees loops here.
  We redefine the old one for now.
*)
Require Import Paco.pacotac_internal.

 Tactic Notation "ecofix" ident(CIH) "with" ident(gL) ident(gH) :=
   repeat red;
   paco_pre2;
   eapply euttG_cofix;
   paco_post2 CIH with gL;
   paco_post2 CIH with gH.

 Tactic Notation "ecofix" ident(CIH) := ecofix CIH with gL gH.

Section ITreeUtilities.

(* TODO: move to itree *)
Lemma interp_state_iter :
  forall {A R S : Type} (E F : Type -> Type) (s0 : S) (a0 : A) (h : E ~> Monads.stateT S (itree F)) f,
    State.interp_state (E := E) (T := R) h (ITree.iter f a0) s0 ≈
                 @Basics.iter _ MonadIter_stateT0 _ _ (fun a s => State.interp_state h (f a) s) a0 s0.
Proof using.
  unfold iter, CategoryKleisli.Iter_Kleisli, Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_itree in *; cbn.
  einit. ecofix CIH; intros.
  rewrite 2 unfold_iter; cbn.
  rewrite !Eqit.bind_bind.
  setoid_rewrite bind_ret_l.
  rewrite StateFacts.interp_state_bind.
  ebind; econstructor; eauto.
  - reflexivity.
  - intros [s' []] _ []; cbn.
    + rewrite StateFacts.interp_state_tau.
      estep.
    + rewrite StateFacts.interp_state_ret; apply reflexivity.
Qed.

Lemma interp_fail_iter :
  forall {A R : Type} (E F : Type -> Type) (a0 : A) (h : E ~> failT (itree F)) f,
    interp_fail (E := E) (T := R) h (ITree.iter f a0) ≈
                @Basics.iter _ failT_iter _ _ (fun a => interp_fail h (f a)) a0.
Proof using.
  unfold Basics.iter, failT_iter, Basics.iter, MonadIter_itree in *; cbn.
  einit. ecofix CIH; intros *.
  rewrite 2 unfold_iter; cbn.
  rewrite !Eqit.bind_bind.
  rewrite interp_fail_bind.
  ebind; econstructor; eauto.
  reflexivity.
  intros [[a1|r1]|] [[a2|r2]|] EQ; inv EQ.
  - rewrite bind_ret_l.
    rewrite interp_fail_tau.
    estep.
  - rewrite bind_ret_l, interp_fail_ret.
    eret.
  - rewrite bind_ret_l.
    eret.
Qed.

Lemma translate_iter :
  forall {A R : Type} (E F : Type -> Type) (a0 : A) (h : E ~> F) f,
    translate (E := E) (F := F) (T := R) h (ITree.iter f a0) ≈
              ITree.iter (fun a => translate h (f a)) a0.
Proof using.
  intros; revert a0.
  einit; ecofix CIH; intros.
  rewrite 2 unfold_iter; cbn.
  rewrite TranslateFacts.translate_bind.
  ebind; econstructor; eauto.
  - reflexivity.
  - intros [|] [] EQ; inv EQ.
    + rewrite TranslateFacts.translate_tau; estep.
    + rewrite TranslateFacts.translate_ret; apply reflexivity.
Qed.

End ITreeUtilities.

(* We don't care in this context about having an informative failure, 
  we just dive into the option monad.
   *)
Section Handle_Fail.

  Definition h_fail {T E} : exceptE T ~> failT (itree E) :=
    fun _ _ => Ret None.

  Definition trigger_fail {E} : E ~> failT (itree E)
    := fun _ e => Vis e (fun x => Ret (Some x)).

  (* TODO: Use [over], or possibly [exceptE -< E] *)
  Definition run_fail {E T}
    : itree (exceptE T +' E) ~> failT (itree E)
    := interp_fail (case_ h_fail trigger_fail).

End Handle_Fail.

Lemma post_returns : forall {E X} (t : itree E X), t ⤳ fun a => Returns a t.
Proof using.
  intros; eapply eqit_mon; eauto.
  2: eapply PropT.eutt_Returns.
  intros ? ? [<- ?]; auto.
Qed.

Lemma eutt_clo_bind_returns {E R1 R2 RR U1 U2 UU}
      (t1 : itree E U1) (t2 : itree E U2)
      (k1 : U1 -> itree E R1) (k2 : U2 -> itree E R2)
      (EQT: @eutt E U1 U2 UU t1 t2)
      (EQK: forall u1 u2, UU u1 u2 -> Returns u1 t1 -> Returns u2 t2 -> eutt RR (k1 u1) (k2 u2)):
  eutt RR (x <- t1;; k1 x) (x <- t2;; k2 x).
Proof using.
  intros; eapply eutt_post_bind_gen; eauto using post_returns.
Qed.

Section No_Failure.

  (* We are often interested in assuming that a computation does not fail.
     This file develop ways to assert and reason about such a fact assuming that
     the tree has been interpreted into the [failT (itree E)] monad.
     Note: nothing in this file is specific to Vellvm, it should eventually be
     moved to the itree library.
   *)

  Definition no_failure {E X} (t : itree E (option X)) : Prop :=
    t ⤳ fun x => ~ x = None.

  Global Instance no_failure_eutt {E X} : Proper (eutt eq ==> iff) (@no_failure E X).
  Proof using.
    intros t s EQ; unfold no_failure; split; intros ?; [rewrite <- EQ | rewrite EQ]; auto.
  Qed.

  (* This is a non-trivial proof, not a direct consequence of an inversion lemma.
     This states essentially that if `no_failure` holds at the end of the execution,
     then it is an invariant of the execution.
   *)
  Lemma no_failure_bind_prefix : forall {E X Y} (t : itree E (option X)) (k : X -> itree E (option Y)),
      no_failure (bind (m := failT (itree E)) t k) ->
      no_failure t.
  Proof using.
    unfold no_failure,has_post; intros E X Y.
    einit; ecofix CIH.
    intros * NOFAIL.
    cbn in NOFAIL. rewrite unfold_bind in NOFAIL.
    rewrite itree_eta.
    destruct (observe t) eqn:EQt.
    - eret.
      cbn in *.
      destruct r; [intros abs; inv abs | exfalso]. 
      apply eutt_Ret in NOFAIL; apply NOFAIL; auto.
    - estep.
      cbn in *.
      ebase; right; eapply CIH.
      rewrite <- tau_eutt; eauto.
    - estep.
      cbn in *.
      intros ?; ebase.
      right; eapply CIH0.
      eapply eqit_inv_Vis in NOFAIL; eauto.
  Qed.

  Lemma no_failure_bind_cont : forall {E X Y} (t : _ X) (k : X -> _ Y),
      no_failure (bind (m := failT (itree E)) t k) ->
      forall u, Returns (E := E) (Some u) t -> 
              no_failure (k u).
  Proof using.
    intros * NOFAIL * ISRET.
    unfold no_failure in *.
    cbn in *.
    eapply PropT.eqit_bind_Returns_inv in NOFAIL; eauto. 
    apply NOFAIL.
  Qed.

  Lemma no_failure_Ret :
    forall E T X x, @no_failure E X (@run_fail E T X (Ret x)).
  Proof using.
    intros.
    unfold run_fail, no_failure.
    cbn.
    rewrite interp_fail_Ret.
    apply eutt_Ret; intros abs; inv abs.
  Qed.

  Lemma failure_throw : forall E Err X (s: Err),
      ~ no_failure (E := E) (X := X) (@run_fail E Err X (throw (E := _ +' E) s)).
  Proof using.
    intros * abs.
    unfold no_failure, throw, run_fail in *.
    rewrite interp_fail_vis in abs.
    cbn in *.
    unfold h_fail in *; rewrite  !bind_ret_l in abs.
    eapply eutt_Ret in abs.
    apply abs; auto.
  Qed.

  (* The following lemmas reason about [tfor] in the specific case where the body goes 
   into the failure monad.
   They are quite a bit ugly as intrinsically [tfor] unfolds using the itree [bind] while
   [no_failure] relies on the failT [bind]. Improving the situation will require to 
   develop better general monadic reasoning principles rather than re-internalize things
   into the [itree E] monad forcibly.
   *)
  Lemma tfor_fail_None : forall {E A} i j (body : nat -> A -> itree E (option A)),
      (i <= j)%nat ->
      tfor (fun k x => match x with
                    | Some a0 => body k a0
                    | None => Ret None
                    end) i j None ≈ Ret None.
  Proof using.
    intros E A i j body; remember (j - i)%nat as k; revert i Heqk; induction k as [| k IH].
    - intros i EQ INEQ; replace j with i by lia; rewrite tfor_0; reflexivity. 
    - intros i EQ INEQ.
      rewrite tfor_unroll; [|lia].
      rewrite bind_ret_l, IH; [reflexivity | lia | lia].
  Qed.

  (* One step unrolling of the combinator *)
  Lemma tfor_unroll_fail: forall {E A} i j (body : nat -> A -> itree E (option A)) a0,
      (i < j)%nat ->
      tfor (fun k x => match x with
                    | Some a0 => body k a0
                    | None => Ret None
                    end) i j a0 ≈
           bind (m := failT (itree E))
           (match a0 with
            | Some a0 => body i a0
            | None => Ret None
            end) (fun a =>
                    tfor (fun k x =>
                            match x with
                            | Some a0 => body k a0
                            | None => Ret None
                            end) (S i) j (Some a)).
  Proof using.
    intros *.
    remember (j - i)%nat as k.
    revert i Heqk a0.
    induction k as [| k IH].
    - lia.
    - intros i EQ a0 INEQ.
      rewrite tfor_unroll; auto.
      cbn.
      destruct a0 as [a0 |]; cycle 1.
      + rewrite !bind_ret_l.
        rewrite tfor_fail_None; [reflexivity | lia].
      + apply eutt_eq_bind.
        intros [a1|]; cycle 1.
        * rewrite tfor_fail_None; [reflexivity | lia].
        * destruct (PeanoNat.Nat.eq_dec (S i) j).
          {
            subst.
            rewrite tfor_0; reflexivity.
          }
          destruct k; [lia |].
          rewrite (IH (S i)); [| lia | lia].
          reflexivity.
  Qed.

  Lemma no_failure_tfor : forall {E A} (body : nat -> A -> itree E (option A)) n m a0,
      no_failure (tfor (fun k x => match x with
                                | Some a => body k a
                                | None => Ret None
                                end) n m a0) ->
      forall k a,
        (n <= k < m)%nat ->
        Returns (Some a) (tfor (fun k x => match x with
                                        | Some a => body k a
                                        | None => Ret None
                                        end) n k a0) ->
        no_failure (body k a).
  Proof using.
    intros E A body n m.
    remember (m - n)%nat as j.
    revert n Heqj.
    induction j as [| j IH].
    - intros n EQ a0 NOFAIL k a [INEQ1 INEQ2] RET.
      assert (n = m) by lia; subst.
      lia.
    - intros n EQ a0 NOFAIL k a [INEQ1 INEQ2] RET.
      destruct (PeanoNat.Nat.eq_dec k n). 
      + subst.
        clear INEQ1.
        rewrite tfor_unroll_fail in NOFAIL; [| auto].
        rewrite tfor_0 in RET.
        apply Returns_Ret in RET.
        subst.
        apply no_failure_bind_prefix in NOFAIL; auto.
      + specialize (IH (S n)).
        forward IH; [lia |].
        rewrite tfor_unroll_fail in NOFAIL; [| lia].
        rewrite tfor_unroll_fail in RET; [| lia].
        cbn in RET.
        apply Returns_bind_inversion in RET.
        destruct RET as (a1 & RET1 & RET2).
        destruct a0 as [a0|]; cycle 1.
        { cbn in *.
          rewrite bind_ret_l in NOFAIL.
          apply eutt_Ret in NOFAIL; contradiction NOFAIL; auto.
        }
        cbn in *.
        destruct a1 as [a1|]; cycle 1.
        {
          apply Returns_Ret in RET2.
          inv RET2.
        }
        apply no_failure_bind_cont with (u := a1) in NOFAIL; auto.
        eapply IH; eauto.
        lia.
  Qed.

End No_Failure.

