From TwoPhase Require Import
  Semantics.TopLevel
  Utils.Tactics
  Util.

From ITree Require Import
  Basics.HeterogeneousRelations.

From Coq Require Import
  List.

(* Typeclass? *)
(* Deterministic...? *)
(* Inversion? *)
Definition R2_injective
  {R1 R2} (RR : R1 -> R2 -> Prop) : Prop :=
  forall (r1 : R1) (r2 : R2) a b,
    RR r1 r2 ->
    RR a b ->
    a = r1 <-> b = r2.

Definition R2_deterministic
  {R1 R2} (RR : R1 -> R2 -> Prop) : Prop :=
  forall (r1 : R1) (r2 : R2) a b,
    RR r1 r2 ->
    RR a b ->
    a = r1 -> b = r2.

Lemma assoc_similar_lookup :
  forall {A B C D}
    `{RDA : @RelDec.RelDec A eq}
    `{RDC : @RelDec.RelDec C eq}
    `{RDCA : @RelDec.RelDec_Correct _ _ RDA}
    `{RDCC : @RelDec.RelDec_Correct _ _ RDC}
    (RAC : A -> C -> Prop)
    (RBD : B -> D -> Prop)
    (xs : list (A * B)%type)
    (ys : list (C * D)%type)
    a b,
    R2_injective RAC ->
    Forall2 (prod_rel RAC RBD) xs ys ->
    assoc a xs = Some b ->
    exists c d i,
      assoc c ys = Some d /\
        Nth xs i (a, b) /\
        Nth ys i (c, d).
Proof.
  intros A B C D RDA RDC RDCA RDCC RAC RBD xs.
  induction xs, ys; intros a' b' RINJ ALL ASSOC.
  - cbn in *; inv ASSOC.
  - cbn in *; inv ASSOC.
  - inv ALL.
  - inv ALL.
    cbn in ASSOC.
    destruct a.
    break_match_hyp.
    + assert (a' = a) as AA by
          (eapply RelDec.rel_dec_correct; eauto);
        subst.

      inv ASSOC.
      destruct p.
      inv H2.
      cbn in *.

      red in RINJ.
      exists c. exists d. exists 0%nat.
      rewrite RelDec.rel_dec_eq_true; auto.
    + specialize (IHxs _ _ _ RINJ H4 ASSOC).
      destruct IHxs as [c [d [i [ASSOC' [NTH1 NTH2]]]]].
      exists c. exists d. exists (S i).
      cbn.
      break_inner_match_goal.
      subst.
      cbn in *.
      break_inner_match_goal.
      { (* c = c0 *)
        (* Should be a contradiction using RINJ, Heqb0, and Heqb1 *)
        inv H2.
        cbn in *.

        assert (c = c0) as CC by
            (eapply RelDec.rel_dec_correct; eauto).

        red in RINJ.
        apply Forall2_forall in H4 as [LEN NTH].
        specialize (NTH _ _ _ NTH1 NTH2).
        inv NTH.
        cbn in *.

        assert (a' = a).
        { eapply RINJ; eauto. }
        subst.

        eapply RelDec.neg_rel_dec_correct in Heqb0.
        contradiction.
      }

      tauto.
Qed.

Lemma assoc_similar_no_lookup :
  forall {A B C D}
    `{RDA : @RelDec.RelDec A eq}
    `{RDC : @RelDec.RelDec C eq}
    `{RDCA : @RelDec.RelDec_Correct _ _ RDA}
    `{RDCC : @RelDec.RelDec_Correct _ _ RDC}
    (RAC : A -> C -> Prop)
    (RBD : B -> D -> Prop)
    (xs : list (A * B)%type)
    (ys : list (C * D)%type)
    a,
    R2_injective RAC ->
    Forall2 (prod_rel RAC RBD) xs ys ->
    assoc a xs = None ->
    forall c,
      RAC a c ->
      assoc c ys = None.
Proof.
  intros A B C D RDA RDC RDCA RDCC RAC RBD xs.
  induction xs, ys; intros a' RINJ ALL ASSOC.
  - cbn in *; auto.
  - cbn in *; inv ALL.
  - inv ALL.
  - inv ALL.
    cbn in ASSOC.
    destruct a.
    break_match_hyp.
    + inv ASSOC.
    + specialize (IHxs _ _ RINJ H4 ASSOC).
      intros c H.
      specialize (IHxs _ H).
      inv H2.
      cbn in *.
      destruct p; cbn in *.
      break_match.
      { assert (c = c0) as CC by
            (eapply RelDec.rel_dec_correct; eauto).
        subst.
        exfalso.

        red in RINJ.
        pose proof RINJ _ _ _ _ H fst_rel.
        apply RelDec.neg_rel_dec_correct in Heqb0.
        apply Heqb0.
        symmetry; apply H0; auto.
      }
      auto.
Qed.
