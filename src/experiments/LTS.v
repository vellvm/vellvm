Require Import List.
Import ListNotations.
Require Import Coqlib.
Require Import Util.

Definition step_rel (S L : Type) := S -> list L -> S -> Prop.

Inductive rtc {S L : Type} (step : step_rel S L) : step_rel S L :=
| rtc_refl : forall s, rtc step s [] s
| rtc_step : forall s l s' l' s'' (Hstep : step s l s')
                    (Htrans : rtc step s' l' s''), rtc step s (l ++ l') s''.
Hint Resolve rtc_refl.

Lemma rtc_step_silent : forall {S L} (step : step_rel S L) s s' l' s'' 
  (Hstep : step s [] s') (Htrans : rtc step s' l' s''), rtc step s l' s''.
Proof. 
  intros; exploit @rtc_step.
  - apply Hstep.
  - eauto.
  - clarify.
Qed.

Lemma rtc_rev_step : forall {S L} (step : step_rel S L) s l s' l' s'' 
  (Htrans : rtc step s l s') (Hstep : step s' l' s''), 
  rtc step s (l ++ l') s''.
Proof.
  intros; induction Htrans; clarify.
  - exploit @rtc_step; eauto; clarify.
    autorewrite with list in H; auto.
  - rewrite app_assoc_reverse; eapply rtc_step; eauto.
Qed.

Lemma rtc_rev_cases : forall {S L} (step : step_rel S L) s l s'
  (Hrtc : rtc step s l s'), (s = s' /\ l = []) \/ (exists l' l'' s'',
  rtc step s l' s'' /\ step s'' l'' s' /\ l = l' ++ l'').
Proof.
  intros; induction Hrtc; clarify.
  right; destruct IHHrtc; clarify.
  - eexists; eexists; eexists; split; [apply rtc_refl | split; eauto].
    autorewrite with list; auto.
  - exists (l ++ x); repeat eexists;
      [eapply rtc_step; eauto | eauto | rewrite app_assoc_reverse; clarify].
Qed.

Definition traces_from {S L : Type} (step : step_rel S L) (s : S) 
  (tr : list L) := exists s', rtc step s tr s'.

Definition similar {S L} (init init' : S -> Prop) step step' 
  (T : list L -> Prop) s s' := 
  exists (R : S -> S -> Prop), (forall s s' l, R s s' -> 
     (traces_from step s l \/ traces_from step' s' l) -> T l) /\
  (forall s0, init s0 -> exists s0', init' s0' /\ R s0 s0') /\
  (forall s s' l s2, R s s' /\ step s l s2 -> T l /\ exists s2', 
     step' s' l s2' /\ R s2 s2') /\ R s s'.

