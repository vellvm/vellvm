Require Import Equalities Arith.
Require Import Vminus.Atom Vminus.Env.
Require Import Vminus.Sequences.

Require Import Vminus.Imp.

Local Open Scope imp_scope.

Lemma imp_step_star_seq_append:
  forall p1 p2, imp_step_star p1 p2 ->
           forall c1 c2 c st1 st2,
             p1 = (c1, st1) -> p2 = (c2, st2) ->
             imp_step_star (c1 ;; c, st1) (c2 ;; c, st2).
Proof.
  intros p1 p2 imp_step_p1.
  induction imp_step_p1 as 
      [[c1' st1'] | [c1' st1'] [c_step st_step] [c_final st_final]];
    intros c1 c2 c st st2 p1_eq p2_eq; inversion p1_eq; inversion p2_eq; subst.
  - apply star_refl.
  - apply star_step with (b := (c_step ;; c, st_step)).
    apply S_Seq.
    trivial.
    apply IHimp_step_p1; reflexivity.
Qed.

Lemma imp_step_star_trans: forall c1 c2 st1 st2 st,
  imp_step_star (c1, st1) (SKIP, st) ->
  imp_step_star (c2, st) (SKIP, st2) ->
  imp_step_star (c1 ;; c2, st1) (SKIP, st2).
Proof.
  intros c1 c2 st1 st2 st imp1 imp2; unfold imp_step_star in *.
  inversion imp1; subst.
  - eapply star_step. 
    apply S_SeqSkip.
    trivial.
  - apply star_trans with (b := (SKIP ;; c2, st)).
    apply imp_step_star_seq_append with (p1 := (c1, st1)) (p2 := (SKIP, st));
      trivial.
    eapply star_step.
    apply S_SeqSkip.
    trivial.
Qed.

Lemma imp_step_star_seq_inversion:
  forall p1 p2, imp_step_star p1 p2 ->
           forall c1 c2 sta stc,
             p1 = (c1 ;; c2, sta) ->
             p2 = (SKIP, stc) ->
             exists stb, imp_step_star (c1, sta) (SKIP, stb) /\
                    imp_step_star (SKIP ;; c2, stb) (SKIP, stc).
Proof.
  intros p1 p2 imp_step_p1.
  induction imp_step_p1 as [| [cseq' sta'] p [skip' stc'] Hstep];
    intros c1 c2 sta stc p1_eq p2_eq; 
    try solve [rewrite p1_eq in p2_eq; inversion p2_eq].
  inversion p1_eq; inversion p2_eq; subst.
  clear p1_eq; clear p2_eq.
  destruct c1.
  - inversion Hstep as
        [ | sta' ? ? ? ? H | sta' c2' [c2_eq sta_eq] p_eq | | | ];
      [inversion H | idtac].
    subst.
    exists sta.
    split; [apply star_refl | idtac].
    eapply star_step; [apply S_SeqSkip | trivial].
  - inversion Hstep.
    rename H3 into step_sta.
    inversion step_sta.
    exists (update sta i (aeval a sta)).
    subst.
    split; auto.
    eapply star_step; [apply step_sta | apply star_refl].
  - inversion Hstep.
    rename st' into one_step_after_sta;
      rename c1' into c11';
      rename H0 into p_eq;
      rename H3 into step_c1_1.
    rewrite <- p_eq in Hstep.
    clear H1 H2 c0.
    generalize
      (IHimp_step_p1 c11' c2 one_step_after_sta stc (symmetry p_eq) eq_refl);
      intros IH.
    inversion IH as [stb [imp1 imp2]].
    exists stb.
    split; 
      [eapply star_step; 
       [apply step_c1_1 | apply imp1] | 
       apply imp2].
  - inversion Hstep.
    rename st' into one_step_after_sta; 
      rename c1' into c1';
      rename H3 into step_c1;
      rename H0 into p_eq.
    clear H1 H2 c0.
    generalize
      (IHimp_step_p1 c1' c2 one_step_after_sta stc (symmetry p_eq) eq_refl);
      intros IH.
    inversion IH as [stb [imp1 imp2]].
    exists stb.
    split; 
      [eapply star_step; 
       [apply step_c1 | apply imp1] | 
       apply imp2].
  - inversion Hstep.
    rename st' into one_step_after_sta; 
      rename c1' into c1';
      rename H3 into step_c1;
      rename H0 into p_eq.
    clear H H1 H2 c0.
    generalize
      (IHimp_step_p1 c1' c2 one_step_after_sta stc (symmetry p_eq) eq_refl);
      intros IH.
    inversion IH as [stb [imp1 imp2]].
    exists stb.
    split; 
      [eapply star_step; 
       [apply step_c1 | apply imp1] | 
       apply imp2].
Qed.

Ltac cases_on_imp_eval :=
  match goal with
  | H: match ?imp_eval with
          | Some _ => _
          | None => _ 
       end = _ |- _ =>
    destruct imp_eval as [middle_st | ] eqn:middle_st_eq;
    try solve [inversion H]
  end.

Theorem imp_eval_sound: forall fuel c st st',
    imp_eval c st fuel = Some st' -> imp_step_star (c, st) (SKIP, st').
Proof.
  induction fuel as [| n]; intros c st st' eval_ok;
    try solve [inversion eval_ok].
  destruct c.
  { simpl in eval_ok; inversion eval_ok. }
  { simpl in eval_ok; inversion eval_ok; subst.
    eapply star_step.
    apply S_Ass.
    reflexivity.
    apply star_refl.
  }
  { simpl in eval_ok.
    destruct c1;
      try solve [eapply star_step;
                 [apply S_SeqSkip |
                  apply IHn;
                  trivial]];
      try solve [cases_on_imp_eval;
                 generalize (IHn _ _ _ middle_st_eq); intros imp_single_step;
                 eapply imp_step_star_trans;
                 [apply imp_single_step |
                  apply IHn;
                  trivial]].
  } 
  { simpl in eval_ok.
    destruct (beval b st) eqn:eval_b;
      apply IHn in eval_ok.
    - eapply star_step; [apply S_IfTrue; trivial | trivial].
    - eapply star_step; [apply S_IfFalse; trivial | trivial].      
  }      
  { simpl in eval_ok.
    destruct (beval b st) eqn:eval_b;
      try solve [inversion eval_ok].
    apply IHn in eval_ok.
    eapply (imp_step_star_seq_inversion _ _) in eval_ok;
      [idtac | reflexivity | reflexivity].
    inversion eval_ok as [st_after_iter [after_one_iter the_rest]].
    eapply star_trans; [idtac | apply the_rest].
    eapply star_step; [apply S_While | idtac].
    eapply star_step; [apply S_IfTrue; trivial | idtac].
    apply (imp_step_star_seq_append _ _ after_one_iter); reflexivity.
  }     
Qed.
