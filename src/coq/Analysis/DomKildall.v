(** * DomKildall: Dominators via Kildall *)
(** * Computing Dominators *)
(** Implementation via fixpoint iteration. *)

Require Import Coq.Program.Equality.
Require Import Equalities.
From Vellvm Require Import
     Analysis.Dom
     Analysis.Dom
     Analysis.Kildall
     Utils.Util.
Require Import FSets FMaps.

Module Type GRAPH_CMP (G: GRAPH).
 Parameter succs : G.t -> G.V -> list G.V.
 Parameter enum_vs : G.t -> list G.V.
End GRAPH_CMP.

Module AlgdomKildall (PC:UsualDecidableType) (Import G: GRAPH with Definition V := PC.t)
                     (Import GC:GRAPH_CMP G)
       <: Algdom G.

  Module Import GS := Spec G.
  Module N := PC.
  Module E := PC.                   (* FIX: clean up all these module aliases *)
  Module NS := FSetWeakList.Make N.


  Module L := BoundedSet NS.
  Module Import K := ! ForwardSolver N L.  (* FIX: some suprising inlining here without ! *)
  Module NM := K.NM.                       (* FIX: fix up sharing? *)

  (* Module Import FMP := FMapProps N NM. *)
  Module FMF := FMapFacts.WFacts_fun N NM.
  Module FSF := FSetFacts.WFacts_fun N NS.

  (* FIX: simplify this ...  *)
  (* Parameter succs : G.t -> N.t -> list N.t. *)
  Axiom succs_compat : forall g n s, edge g n s <-> In s (succs g n).
  Axiom succs_compat2 : forall g n s, In s (succs g n) -> mem g s.

  (* Parameter enum_vs : G.t -> list N.t. *)
  Axiom enum_vs_compat : forall g n, mem g n <-> In n (enum_vs g).

  (* this follows directly from wf_cfg *)
  Axiom entry_not_sdom : forall g v, ~ SDom g v (entry g).


  Definition trans (n: N.t) (l:L.t) : L.t :=
    L.union (L.singleton n) l.

  Definition inits (g:G.t) : NM.t L.t :=
    NM.add (entry g) L.top
    (fold_right (fun n g => NM.add n L.bot g) (NM.empty L.t) (enum_vs g) ).

  Definition calc_sdom (g:G.t) : option (N.t -> L.t) :=
    let nmo := K.fixpoint (succs g) trans (inits g) in
    match nmo with
      | None => None
      | Some nm => Some (fun n => nm!!n)
    end.

  Lemma entry_sound : forall g sdom,
    calc_sdom g = Some sdom ->
    sdom (entry g) == L.top.
  Proof.
    unfold calc_sdom. intros. 
    destruct (K.fixpoint _ _ _) eqn:Heqk; try discriminate H.
    injection H. intro. clear H. subst sdom.
    set (r := t0!!(entry g)). cut (L.le L.top r).
    destruct r; try inversion 1. simpl.
    intro Hsub. red. intro a. split;
    intro; exfalso; eapply FSF.empty_iff; eauto.

    replace L.top with ((inits g)!!(entry g)).
    eapply K.fixpoint_entry. apply Heqk.
    unfold inits. rewrite FMP.find_default_eq; auto.
  Qed.

  Lemma successors_sound : forall g sdom n1 n2,
    calc_sdom g = Some sdom ->
    mem g n1 -> mem g n2 -> edge g n1 n2 -> 
    L.union (L.singleton n1) (sdom n1) <= sdom n2.
  Proof.
    unfold calc_sdom. intros.
    destruct (K.fixpoint _ _ _) eqn:Heqk; try discriminate H.
    injection H. intro. clear H. subst sdom.

    set (trans n o := L.union (L.singleton n) o).
    change (L.union (L.singleton n1) t0!!n1)
           with (trans n1 t0!!n1).
    eapply K.fixpoint_solution. 
    eauto. 

    unfold inits. destruct (N.eq_dec n1 (entry g)).
    apply FMF.add_in_iff; auto. apply FMF.add_neq_in_iff; auto.

    (* separate lemma? *)
    apply enum_vs_compat in H0. set (f g n := NM.add n L.bot g).
    assert (In n1 (enum_vs g) \/ NM.In n1 (NM.empty L.t)) 
           as Hin by exact (or_introl H0).
    generalize (enum_vs g) (NM.empty L.t) Hin.
    induction l; simpl. intuition.
    intros to Hin'. destruct Hin' as [[? | ?] | ?]; subst; auto.
    apply FMF.add_in_iff; auto.
    destruct (N.eq_dec a n1).
      subst.
      apply FMF.add_in_iff; auto. apply FMF.add_neq_in_iff; auto.
      lapply (IHl to). intros.
      apply FMF.add_in_iff; auto.
      right; auto.
    apply succs_compat; auto.
  Qed.

  (* Include AlgdomProperties G. *)

  Lemma complete : forall g sdom n1 n2,
    calc_sdom g = Some sdom ->
    SDom g n1 n2 -> L.In n1 (sdom n2).
  Proof.
    intros. pose proof entry_sound _ _ H as Hentry.
    unfold calc_sdom in *.
    destruct (K.fixpoint _ _ _) as [res|] eqn:heqk; try discriminate H.
    injection H. intro. clear H. subst sdom.

    generalize H0. clear H0. pattern n2, res!!n2.
    eapply K.fixpoint_invariant; eauto.

    intros. destruct (N.eq_dec (entry g) n).
    subst n. contradict H0. 
    apply entry_not_sdom. unfold inits. 
    rewrite FMP.find_default_neq; auto. unfold FMP.find_default.
    destruct (NM.find _ _) as [l'|] eqn:Heq; simpl; auto.

    induction (enum_vs g); simpl in *.
    rewrite FMF.empty_o in Heq. inversion Heq.
    rewrite <- FMF.find_mapsto_iff in Heq.
    rewrite FMF.add_mapsto_iff in Heq.
    destruct Heq as [[eq1 eq2] | [neq1 hyp]]; subst; simpl in *; auto.
    apply IHl. rewrite FMF.find_mapsto_iff in hyp.
    apply hyp.

    (* step preserves completeness *)
    intros. unfold trans.

    pose proof (succs_compat2 _ _ _ H) as Hmem.
    apply succs_compat in H.
    
    destruct ls eqn:Heqls, ln eqn:Heqln; simpl; auto.
    apply FSF.inter_iff. split. apply H1; auto.
    apply FSF.union_iff.
    destruct (N.eq_dec n1 n). left. apply FSF.singleton_iff; auto.
    right. apply H0. red; split; auto.
    eapply dom_step with (v2:=s); auto. 
    
    apply H1; auto.

    apply FSF.union_iff.
    destruct (N.eq_dec n1 n). left. apply FSF.singleton_iff; auto.
    right. apply H0. red; split; auto. 
    eapply dom_step with (v2:=s); auto.

  Qed.

End AlgdomKildall.

