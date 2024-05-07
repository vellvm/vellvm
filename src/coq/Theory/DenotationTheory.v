(* begin hide *)
From stdpp Require Import base gmap fin_maps tactics.
(* ssreflect. *)

From Coq Require Import
     String
     List.

From ITree Require Import
     ITree
     ITreeFacts
     Basics.HeterogeneousRelations.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics.LLVMParams
     Semantics.Denotation
     Syntax.ScopeTheory
     Utils.PostConditions
     Utils.ITreeRaise.
Import LLVMEvents.

#[export] Remove Hints Eqv.EqvWF_Build : typeclass_instances.

Set Implicit Arguments.
Set Strict Implicit.

Import MonadNotation.
Open Scope list_scope.
Open Scope monad_scope.
Open Scope itree.
(* Import ITreeNotations. *)
(* Import EitherMonad. *)
(* Import IdentityMonad. *)
Import ListNotations.

(* end hide *)

(* TO MOVE *)
Lemma eq_itree_eq_bind : forall E R1 R2 RR U (t: itree E U) (k1: U -> itree E R1) (k2: U -> itree E R2),
    (forall u, eq_itree RR (k1 u) (k2 u)) -> eq_itree RR (ITree.bind t k1) (ITree.bind t k2).
Proof.
  intros.
  apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
  intros ? ? ->; apply H.
Qed.

Lemma euttge_clo_bind {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop) {U1 U2 UU} t1 t2 k1 k2
      (EQT: @euttge E U1 U2 UU t1 t2)
      (EQK: forall u1 u2, UU u1 u2 -> euttge RR (k1 u1) (k2 u2)):
  euttge RR (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  eapply eqit_bind'; eauto.
Qed.

Lemma euttge_eq_bind : forall E R1 R2 RR U (t: itree E U) (k1: U -> itree E R1) (k2: U -> itree E R2),
    (forall u, euttge RR (k1 u) (k2 u)) -> euttge RR (ITree.bind t k1) (ITree.bind t k2).
Proof.
  intros.
  apply euttge_clo_bind with (UU := Logic.eq); [reflexivity |].
  intros ? ? ->; apply H.
Qed.

Tactic Notation "ibind" := (eapply eutt_clo_bind || eapply eq_itree_clo_bind || eapply euttge_clo_bind).
Tactic Notation "ibind=" :=
  (apply eutt_eq_bind || eapply eq_itree_eq_bind || eapply euttge_eq_bind).
Tactic Notation "ibind" "with" uconstr(R) :=
  (eapply eutt_clo_bind with (UU := R)
 || eapply eq_itree_clo_bind with (UU := R)
 || eapply euttge_clo_bind with (UU := R)).

(* END TO MOVE *)

(** * Structural equations at the representation level

We prove here the equational theory that holds independently of the
interpretation of events.
These equations are expressed in terms of [eutt eq] over uninterpreted trees.
They derive from the [itree] combinators used to compute the uninterpreted
representation VIR's syntax.

In particular, notice that since [interp] is a iterative-monad morphism that respects
[eutt eq], these equations get transported at all levels of interpretations.

*)
Module Type DenotationTheory (LP : LLVMParams).
  Module D := Denotation LP.
  Import D.
  Import LP.

  Import SemNotations.

  Open Scope list_scope.

  Module DenoteTactics.

    Hint Rewrite @bind_ret_l : rwexp.
    Hint Rewrite @bind_bind : rwexp.
    Hint Rewrite @translate_ret : rwexp.
    Hint Rewrite @translate_bind : rwexp.
    Hint Rewrite @translate_trigger : rwexp.

    Ltac go :=
      (match goal with
      |- eutt _ ?t ?u =>
        let fresh := fresh in
        remember t as fresh;
        autorewrite with rwexp;
        subst fresh;
        remember u as fresh;
        autorewrite with rwexp;
        subst fresh
      end) ||
      (match goal with
      |- eq_itree _ ?t ?u =>
        let fresh := fresh in
        remember t as fresh;
        autorewrite with rwexp;
        subst fresh;
        remember u as fresh;
        autorewrite with rwexp;
        subst fresh
      end) ||
      (match goal with
        |- eqit _ _ _ ?t ?u =>
        let fresh := fresh in
        remember t as fresh;
        autorewrite with rwexp;
        subst fresh;
        remember u as fresh;
        autorewrite with rwexp;
        subst fresh
      end) ||
    autorewrite with rwexp.
    Tactic Notation "go*" := cbn; go.
    Tactic Notation "go**" := repeat (cbn; go).

  End DenoteTactics.
  Import DenoteTactics.

  (** [denote_code]
     - ⟦ [] ⟧c     ≈ Ret tt               [denote_code_nil]
     - ⟦ [i] ⟧c    ≈ ⟦ i ⟧i               [denote_code_singleton]
     - ⟦ i :: c ⟧c ≈ (⟦ i ⟧i ;; ⟦ c ⟧c)   [denote_code_cons]
     - ⟦ a ++ b ⟧c ≈ (⟦ a ⟧c ;; ⟦ b ⟧c)   [denote_code_app]
   *)

  Lemma denote_code_nil :
    ⟦ [] ⟧c ≈ Ret tt.
  Proof.
    by go*.
  Qed.

  Lemma denote_code_app_eq_itree :
    forall a b,
      ⟦ a ++ b ⟧c ≅ (⟦ a ⟧c ;; ⟦ b ⟧c).
  Proof.
    induction a; intros b.
    - by cbn; go.
    - cbn in *.
      go.
      ibind=; intros [].
      go.
      setoid_rewrite bind_ret_l.
      rewrite IHa.
      by go.
  Qed.

  Lemma denote_code_app :
    forall a b,
      ⟦ a ++ b ⟧c ≈ (⟦ a ⟧c ;; ⟦ b ⟧c).
  Proof.
    intros; by rewrite denote_code_app_eq_itree.
  Qed.

  Lemma denote_code_cons :
    forall i c,
      ⟦ i :: c ⟧c ≈ (⟦ i ⟧i ;; ⟦ c ⟧c).
  Proof.
    intros.
    go*.
    ibind=; intros [].
    go*.
    by setoid_rewrite bind_ret_l.
  Qed.

  Lemma denote_code_singleton :
    forall i,
      ⟦ [i] ⟧c ≈ ⟦ i ⟧i.
  Proof.
    intros a.
    rewrite denote_code_cons.
    bind_ret_r2.
    ibind=; intros [].
    apply denote_code_nil.
  Qed.

  (** [denote_phi]
      - ⟦ (x, Phi τ ({[bid := e]} ∪ tl)) ⟧Φ bid ≈ (uv <- ⟦ e at τ ⟧e; Ret (x,uv)).
   *)

  Lemma denote_phi_in : forall bid e x τ args,
      args !! bid = Some e ->
      ⟦ (x, Phi τ args) ⟧Φ bid ≈ (uv <- ⟦ e at τ ⟧e; Ret (x,uv)).
  Proof.
    intros; cbn.
    by simplify_map_eq.
  Qed.

  Lemma denote_phi_cup_l : forall bid x τ args args',
      args !! bid = None ->
      ⟦ (x, Phi τ (args ∪ args')) ⟧Φ bid ≈ ⟦ (x, Phi τ args') ⟧Φ bid.
  Proof.
    intros; cbn.
    by rewrite lookup_union_r.
  Qed.

  Lemma denote_phi_cup_r : forall bid x τ args args',
      args' !! bid = None ->
      ⟦ (x, Phi τ (args ∪ args')) ⟧Φ bid ≈ ⟦ (x, Phi τ args) ⟧Φ bid.
  Proof.
    intros; cbn.
    by rewrite lookup_union_l.
  Qed.

  Lemma denote_phi_add : forall bid e x τ tl,
      ⟦ (x, Phi τ ({[bid := e]} ∪ tl)) ⟧Φ bid ≈ (uv <- ⟦ e at τ ⟧e; Ret (x,uv)).
  Proof.
    intros; cbn.
    by simplify_map_eq.
  Qed.

  Lemma denote_phi_add_ne : forall bid bid' e x τ tl,
      bid <> bid' ->
      ⟦ (x, Phi τ ({[bid' := e ]} ∪ tl)) ⟧Φ bid ≈ ⟦ (x, Phi τ tl) ⟧Φ bid.
  Proof.
    intros; cbn.
    rewrite lookup_union_r; [done | by simplify_map_eq].
  Qed.

  (** [denote_phis]
   *)

  Lemma denote_phis_nil : forall x,
      ⟦ [] ⟧Φs x ≈ Ret tt.
  Proof.
    intros.
    go*.
    by go*.
  Qed.

  (* This only holds after interpretation: we can't justify the commutation of writes at this level
  Lemma denote_phis_cons : forall b φ φs,
      ⟦φ :: φs⟧Φs b ≈
     (v <- ⟦φ⟧Φ b;
      ⟦φs⟧Φs b;;
      trigger (LocalWrite (fst v) (snd v)))
  .
  Proof.
    intros ???; revert φ; induction φs as [| φhd φs IH].
    - intros [? []].
      go*.
      ibind=; intros []; go*.
      go**.
      bind_ret_r2.
      by ibind=; intros []; go*.
    - intros [? []].
      cbn.
      rewrite bind_bind.
      ibind=; intros [].
      specialize (IH φhd); cbn in IH.
      rewrite IH.
      go**.
      ibind=; intros []; go*.
      ibind=; intros vs; go**.
      repeat setoid_rewrite bind_bind.
      repeat setoid_rewrite bind_ret_l.
      cbn.
      cbn in IH.

      match goal with
        |- context[raise ?s] => generalize s
      end.
      intros s.
      cbn.
      match goal with
        |- context[raise ?s] => generalize s
      end.
      intros s'.
      rewrite ?bind_bind.
      apply eutt_eq_bind.
      intros [].
      rewrite ?bind_bind, ?bind_ret_l.
      cbn.
      cbn in IH.
  Admitted.
 *)


  (** [denote_block] *)
  Lemma denote_block_unfold_cont :
    forall {R} phis c t s origin (k : _ -> itree _ R),
      ⟦ mk_block phis c t s ⟧b origin >>= k
    ≈
     (⟦ phis ⟧Φs origin;;
      ⟦ c ⟧c;;
      ⟦ t ⟧t >>= k).
  Proof.
    by intros; cbn; repeat setoid_rewrite bind_bind.
  Qed.

  Lemma denote_block_unfold :
    forall phis c t s origin,
      ⟦ mk_block phis c t s ⟧b origin ≈
     (⟦ phis ⟧Φs origin;;
      ⟦ c ⟧c;;
      ⟦ t ⟧t).
  Proof.
    done.
  Qed.

  (** [denote_ocfg] *)
  Lemma denote_ocfg_empty: forall s, ⟦ ∅ ⟧bs s ≈ Ret (inl s).
  Proof.
    intros []; unfold denote_ocfg.
    setoid_rewrite unfold_iter.
    simplify_map_eq.
    by go*.
  Qed.

  Lemma denote_ocfg_in_eq_itree: forall bks bid_from bid_src bk,
      bks !! bid_src = Some bk ->
      ⟦ bks ⟧bs (bid_from, bid_src) ≅
     (vob <- ⟦ bk ⟧b bid_from ;
      match vob with
      | inr v => Ret (inr v)
      | inl bid_target => Tau (⟦ bks ⟧bs (bid_src, bid_target))
      end).
  Proof.
    intros * lu.
    cbn. unfold denote_ocfg at 1.
    setoid_rewrite unfold_iter_ktree.
    rewrite lu.
    go*.
    repeat (ibind=; intros ?).
    break_sum; go*; [| done].
    by apply eqit_Tau.
  Qed.

  Lemma denote_ocfg_in_euttge: forall bks bid_from bid_src bk,
      bks !! bid_src = Some bk ->
      ⟦ bks ⟧bs (bid_from, bid_src) ≳
     (vob <- ⟦ bk ⟧b bid_from ;
      match vob with
      | inr v => Ret (inr v)
      | inl bid_target => ⟦ bks ⟧bs (bid_src, bid_target)
      end).
  Proof.
    intros * lu.
    rewrite denote_ocfg_in_eq_itree; eauto.
    ibind=; intros ?.
    break_sum; go*; [| done].
    by rewrite tau_euttge.
  Qed.

  Lemma denote_ocfg_in: forall bks bid_from bid_src bk,
      bks !! bid_src = Some bk ->
      ⟦ bks ⟧bs (bid_from, bid_src)
     ≈
     (vob <- ⟦ bk ⟧b bid_from ;
      match vob with
      | inr v => Ret (inr v)
      | inl bid_target => ⟦ bks ⟧bs (bid_src, bid_target)
      end).
  Proof.
    intros * lu.
    by rewrite denote_ocfg_in_euttge.
  Qed.

  Lemma denote_ocfg_nin_eq_itree: forall bks bid_from bid_src,
      bks !! bid_src = None ->
      ⟦ bks ⟧bs (bid_from, bid_src) ≅ Ret (inl (bid_from,bid_src)).
  Proof.
    intros * lu.
    unfold denote_ocfg.
    rewrite unfold_iter_ktree, lu.
    by go*.
  Qed.

  Lemma denote_ocfg_nin: forall bks bid_from bid_src,
      bks !! bid_src = None ->
      ⟦ bks ⟧bs (bid_from, bid_src) ≈ Ret (inl (bid_from,bid_src)).
  Proof.
    intros * lu.
    by rewrite denote_ocfg_nin_eq_itree.
  Qed.

  Lemma denote_ocfg_unfold: forall bks bid_from bid_src,
      ⟦ bks ⟧bs (bid_from, bid_src) ≅
    (match bks !! bid_src with
      | Some bk => vob <- ⟦ bk ⟧b bid_from ;
                  match vob with
                  | inr v => Ret (inr v)
                  | inl bid_target => Tau (⟦ bks ⟧bs (bid_src, bid_target))
                  end
      | None => Ret (inl (bid_from,bid_src))
      end).
  Proof.
    intros *.
    break_match_goal.
    - by rewrite denote_ocfg_in_eq_itree.
    - by rewrite denote_ocfg_nin_eq_itree.
  Qed.

  Section Outputs.

    (** * outputs soundness *)

    Lemma raise_has_all_posts : forall {E X} `{FailureE -< E} s Q,
        @raise E X _ s ⤳ Q.
    Proof.
      unfold raise; intros.
      apply has_post_bind; intros [].
    Qed.

    Lemma raiseUB_has_all_posts : forall {E X} `{UBE -< E} s Q,
        @raiseUB E _ X s ⤳ Q.
    Proof.
      unfold raise; intros.
      apply has_post_bind; intros [].
    Qed.

    Lemma raise_has_all_posts_cont : forall {E X Y} `{FailureE -< E} s (k : X -> itree E Y) Q,
         (x <- @raise E X _ s; k x) ⤳ Q.
    Proof.
      intros.
      rewrite raise_bind_itree.
      apply raise_has_all_posts.
    Qed.
    Lemma raiseUB_has_all_posts_cont : forall {E X Y} `{UBE -< E} s (k : X -> itree E Y) Q,
         (x <- @raiseUB E _ X s; k x) ⤳ Q.
    Proof.
      intros.
      rewrite raiseUB_bind_itree.
      apply raiseUB_has_all_posts.
    Qed.

    Lemma select_switch_in :
      forall x default_dest brs id,
        select_switch x default_dest brs = inr id ->
        id = default_dest \/ In id (List.map snd brs).
    Proof.
      intros x default_dest brs id SELECT.
      induction brs.
      - inversion SELECT; auto.
      - cbn in SELECT.
        break_match_hyp.
        break_match_hyp; inversion SELECT;
          break_match_hyp; inversion SELECT;
          subst;
          break_match_hyp; inversion SELECT; subst; cbn; tauto.
    Qed.

    Ltac hpbind  := apply has_post_bind; intros ?.
    Ltac ehpbind := eapply has_post_bind_strong.
    Ltac uehpbind := unshelve eapply has_post_bind_strong.
    Tactic Notation "hpbind" "with" uconstr(t) := apply has_post_bind_strong with t.
    Ltac hpret  := apply eutt_Ret.
    Ltac hpabs  :=
       try (apply raise_has_all_posts || apply raiseUB_has_all_posts ||
             apply raise_has_all_posts_cont || apply raiseUB_has_all_posts_cont
        ).

    Lemma has_post_map_monad :
      forall {E} {A B} (f : A -> itree E B) (P : B -> Prop) (l : list A),
        (forall x, List.In x l -> f x ⤳ P) ->
        map_monad f l ⤳ Forall P.
    Proof.
      intros * IH'.
      induction l as [| t l IH].
      - by hpret.
      - go*.
        hpbind with P; [apply IH'; by left | ].
        intros ? HP.
        hpbind with (Forall P); [apply IH; intros; apply IH'; right; auto | ].
        intros ? HP'; hpret.
        by apply Forall_cons.
    Qed.

    Ltac hpmap  := apply has_post_map_monad.

    Tactic Notation "break_err" "as" ident(H) :=
      match goal with
        |- context[lift_err _ ?x] => destruct x eqn:H; cbn [lift_err]
      end .
    Ltac break_err := let H := fresh in break_err as H.

    Tactic Notation "hperr" "as" ident(H) := break_err as H; [hpabs |].
    Tactic Notation "hperr" := let H := fresh in hperr as H.

    Import ITree.
    Import Events.DV.

    Lemma denote_terminator_exits_in_outputs :
      forall term,
        ⟦ term ⟧t ⤳ sum_pred (fun id => id ∈ terminator_outputs term) TT.
    Proof with set_solver.
      intros term; destruct term eqn:Hterm; cbn; try (hpabs || hpret; set_solver).
      - destruct v.
        hpbind.
        hpret...
      - destruct v; cbn.
        hpbind.
        hpbind.
        break_match_goal; hpabs.
        break_match_goal; hpret...
      - destruct v; cbn.
        hpbind.
        hpbind.
        break_match_goal; hpabs.
        clear Hterm term.

        hpbind with (Forall (fun id => In (snd id) (List.map snd brs))).
        + hpmap.
          intros [[] ?] ?.
          case_match; hpabs.
          case_match; go; hpret.
          subst.
          all: by apply in_map with (f := snd) in H.
        + intros ? FORALL.
          hperr as Hswitch.
          hpret; cbn.
          apply select_switch_in in Hswitch.
          destruct_or?.
          set_solver.
          (* The remaining of this proof should not be so messy. Why [gset_semi_set] is not visible earlier? *)
          apply Coqlib.list_in_map_inv in Hswitch as ([? ?] & -> & IN).
          rewrite Forall_forall in FORALL.
          apply FORALL in IN.
          cbn in *.
          apply elem_of_list_In in IN.
          eapply elem_of_list_to_set in IN.
          apply elem_of_union_r.
          apply IN.
          Unshelve.
          apply gset_semi_set.
    Qed.

    Definition exits_in_outputs {t} ocfg : block_id * block_id + uvalue -> Prop :=
      sum_pred (fun fto => snd fto ∈ @outputs t ocfg) TT.

    Lemma denote_bk_exits_in_outputs :
      forall b from,
        ⟦ b ⟧b from ⤳ sum_pred (fun id => id ∈ successors b) TT.
    Proof.
      intros; cbn.
      repeat hpbind.
      apply denote_terminator_exits_in_outputs.
    Qed.

    (* Given a predicate [Qb] on pairs of block ids (the origin for phi-nodes and the input)
   and a predicate [Qv] on values, we establish that both hold after the denotation of an open_cfg if:
   - [Qb] holds at the initial entry point
   - [Qb] and [Qv] are preserved by the denotation of any blocks in the open cfg, assuming [Qb]
     *)
    Lemma denote_ocfg_has_post_strong :
      forall (bks : ocfg _) fto (Qb : block_id * block_id -> Prop) (Qv : uvalue -> Prop)
        (INIT : Qb fto)
        (IND : forall fto (b : block dtyp),
            Qb fto ->
            bks !! snd fto = Some b ->
            ⟦ b ⟧b (fst fto) ⤳ sum_pred (fun to => Qb (snd fto, to)) Qv),
        ⟦ bks ⟧bs fto ⤳ sum_pred Qb Qv.
    Proof.
      intros * INIT IND.
      eapply has_post_iter_strong; eauto.
      intros [f to] PRE.
      flatten_goal.
      - specialize (IND (f,to) b).
        eapply eutt_post_bind; [apply IND |]; auto.
        intros [id | v]; cbn; intros ?; apply eutt_Ret; auto.
      - apply eutt_Ret; auto.
    Qed.

    (* A weaker but sometimes easier to use modular way to prove postconditions of open cfgs:
   - assuming that all blocks in the open cfg admits as postconditions [sum_pred Qb Qv]
   - and assuming that we indeed enter the [open_cfg]
   then we get [Qb/Qv], and ignore the origin of the jump.
     *)
    Lemma denote_ocfg_has_post :
      forall (bks : ocfg _) fto (Qb : block_id -> Prop) (Qv : uvalue -> Prop)
        (ENTER : snd fto ∈ inputs bks)
        (IND : forall fto (b : block dtyp),
            bks !! snd fto = Some b ->
            ⟦ b ⟧b (fst fto) ⤳ sum_pred Qb Qv),
        ⟦ bks ⟧bs fto ⤳ sum_pred (prod_pred TT Qb) Qv.
    Proof.
      intros * IN IND.
      apply has_post_iter_strong with (Inv := fun x => snd x ∈ inputs bks \/ Qb (snd x))
      ; eauto.
      intros [f to] HYP.
      flatten_goal.
      - specialize (IND (f,to) b).
        eapply eutt_post_bind; [apply IND |]; auto.
        intros [id | v]; cbn; intros ?; apply eutt_Ret; cbn; auto.
      - apply eutt_Ret.
        split; auto.
        destruct HYP as [abs | POST]; auto.
        apply find_block_in_inputs in abs as [? abs]; cbn in abs; rewrite abs in Heq; inv Heq.
    Qed.

    Lemma denote_ocfg_exits_in_outputs :
      forall bks fto,
        snd fto ∈ inputs bks ->
        ⟦ bks ⟧bs fto ⤳ exits_in_outputs bks.
    Proof.
      intros * IN.
      apply has_post_weaken with (P := sum_pred (prod_pred TT (fun b => b ∈ outputs bks)) TT).
      2: intros [[]|] ?; cbn in *; intuition.
      apply denote_ocfg_has_post; eauto.
      intros.
      eapply has_post_weaken.
      eapply denote_bk_exits_in_outputs.
      intros []; cbn; intuition.
      by eapply outputs_elem_of.
    Qed.

  End Outputs.

  (** * denote_ocfg  *)

  Lemma denote_ocfg_union_no_edges :
    forall (bks1 bks2 : ocfg _) fto,
      bks1 !! snd fto = None ->
      no_reentrance bks1 bks2 ->
      ⟦ bks1 ∪ bks2 ⟧bs fto ≈ ⟦ bks2 ⟧bs fto.
  Proof.
    intros bks1 bks2 [f to] FIND NOBACK.
    apply (@KTreeFacts.eutt_iter_gen _ _ _ (fun fto fto' => fto' = fto /\ bks1 !! snd fto = None)); auto.
    clear f to FIND; intros fto fto' [-> FIND]; destruct fto as [f to] .
    cbn in *.
    rewrite lookup_union_r; auto.
    case_match eqn:FIND_L2.
    - eapply eutt_post_bind.
      apply denote_bk_exits_in_outputs.
      intros [id | v] ?; cbn; apply eutt_Ret; eauto.
      eapply inl_morphism; split; auto.
      cbn. cbn in *.
      eapply free_out_of_inputs,no_reentrance_not_in; eauto.
      eapply outputs_elem_of; eauto.
    - apply eutt_Ret; right; auto.
  Qed.

  Lemma denote_ocfg_union :
    forall bks1 bks2 fto,
      no_reentrance bks1 bks2 ->
      ⟦ bks1 ∪ bks2 ⟧bs fto ≈
     ('x <- ⟦ bks1 ⟧bs fto;
      match x with
      | inl fto2 => ⟦ bks2 ⟧bs fto2
      | inr v => Ret (inr v)
      end).
  Proof.
    intros * NOBACK.
    revert fto.
    einit.
    ecofix CIH.
    intros [f to].
    case (bks1 !! to) eqn:FIND.
    - rewrite 2 denote_ocfg_unfold.
      simplify_map_eq.
      go.
      ebind; econstructor; [reflexivity | intros ??<-].
      case_match.
      rewrite bind_tau; etau.
      by go.
    - efinal.
      rewrite denote_ocfg_union_no_edges; auto.
      by rewrite (denote_ocfg_nin bks1); auto; go*.
  Qed.

  Lemma denote_ocfg_flow_left :
    forall ocfg1 ocfg2 fto,
      independent_flows ocfg1 ocfg2 ->
      snd fto ∈ inputs ocfg1 ->
      ⟦ ocfg1 ∪ ocfg2 ⟧bs fto ≈
      ⟦ ocfg1 ⟧bs fto.
  Proof.
    intros * INDEP IN.
    rewrite denote_ocfg_union; [| auto using independent_flows_no_reentrance_l].
    bind_ret_r2.

    eapply eutt_post_bind; [apply denote_ocfg_exits_in_outputs; eauto |].
    intros [[f to] | ?] EXIT; [| reflexivity].
    rewrite denote_ocfg_nin; [reflexivity |].
    cbn in *.
    apply free_out_of_inputs.
    eapply no_reentrance_not_in; eauto.
    apply INDEP.
  Qed.

  Lemma denote_ocfg_flow_right :
    forall ocfg1 ocfg2 fto,
      independent_flows ocfg1 ocfg2 ->
      snd fto ∈ inputs ocfg2 ->
      ⟦ ocfg1 ∪ ocfg2 ⟧bs fto ≈ ⟦ ocfg2 ⟧bs fto.
  Proof.
    intros * INDEP IN.
    rewrite denote_ocfg_union; [| auto using independent_flows_no_reentrance_l].
    destruct fto as [f to]; cbn in *.
    rewrite denote_ocfg_nin.
    by go.
    eapply free_out_of_inputs, disjoint_inputs_l; eauto using independent_flows_disjoint.
  Qed.

  Opaque denote_block.
  Lemma denote_ocfg_prefix :
    forall (prefix bks' postfix bks : ocfg dtyp) (from to: block_id),
      bks = (prefix ∪ bks' ∪ postfix) ->
      prefix ##ₘ bks' ->
      ⟦ bks ⟧bs (from, to) ≈
     ('x <- ⟦ bks' ⟧bs (from, to);
      match x with
      | inl x => ⟦ bks ⟧bs x
      | inr x => Ret (inr x)
      end)
  .
  Proof.
    intros * ->; revert from to.
    einit.
    ecofix CIH.
    clear CIHH.
    intros * DISJ.
    case (bks' !! to) as [bk |] eqn:EQ.
    - unfold denote_ocfg at 1 3.
      setoid_rewrite KTreeFacts.unfold_iter_ktree.
      go**.
      assert (EQ': (prefix ∪ bks' ∪ postfix) !! to = Some bk) by (by simplify_map_eq).
      rewrite EQ, EQ'; go**.
      eapply euttG_bind; econstructor; [reflexivity | intros [] ? <-].
      + go*.
        rewrite bind_tau; etau.
      + by go.
    - edrop.
      rewrite (denote_ocfg_nin bks'); auto.
      by go*.
  Qed.
  Transparent denote_block.
End DenotationTheory.

Module Make (LP : LLVMParams) : DenotationTheory LP.
  Include DenotationTheory LP.
End Make.

(* Module DenotationTheoryBigIntptr := Make LLVMParamsBigIntptr. InterpreterStackBigIntptr TopLevelBigIntptr. *)
(* Module DenotationTheory64BitIntptr := Make InterpreterStack64BitIntptr TopLevel64BitIntptr. *)

(* begin hide *)
From stdpp Require Import base gmap fin_maps tactics.
(* ssreflect. *)

From Coq Require Import
     String
     List.

From ITree Require Import
     ITree
     ITreeFacts
     Basics.HeterogeneousRelations.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics.LLVMParams
     Semantics.Denotation
     Syntax.ScopeTheory
     Utils.PostConditions
     Utils.ITreeRaise.
Import LLVMEvents.

#[export] Remove Hints Eqv.EqvWF_Build : typeclass_instances.

Set Implicit Arguments.
Set Strict Implicit.

Import MonadNotation.
Open Scope list_scope.
Open Scope monad_scope.
Open Scope itree.
(* Import ITreeNotations. *)
(* Import EitherMonad. *)
(* Import IdentityMonad. *)
Import ListNotations.

(* end hide *)

(* TO MOVE *)
Lemma eq_itree_eq_bind : forall E R1 R2 RR U (t: itree E U) (k1: U -> itree E R1) (k2: U -> itree E R2),
    (forall u, eq_itree RR (k1 u) (k2 u)) -> eq_itree RR (ITree.bind t k1) (ITree.bind t k2).
Proof.
  intros.
  apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
  intros ? ? ->; apply H.
Qed.

Lemma euttge_clo_bind {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop) {U1 U2 UU} t1 t2 k1 k2
      (EQT: @euttge E U1 U2 UU t1 t2)
      (EQK: forall u1 u2, UU u1 u2 -> euttge RR (k1 u1) (k2 u2)):
  euttge RR (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  eapply eqit_bind'; eauto.
Qed.

Lemma euttge_eq_bind : forall E R1 R2 RR U (t: itree E U) (k1: U -> itree E R1) (k2: U -> itree E R2),
    (forall u, euttge RR (k1 u) (k2 u)) -> euttge RR (ITree.bind t k1) (ITree.bind t k2).
Proof.
  intros.
  apply euttge_clo_bind with (UU := Logic.eq); [reflexivity |].
  intros ? ? ->; apply H.
Qed.

Tactic Notation "ibind" := (eapply eutt_clo_bind || eapply eq_itree_clo_bind || eapply euttge_clo_bind).
Tactic Notation "ibind=" :=
  (apply eutt_eq_bind || eapply eq_itree_eq_bind || eapply euttge_eq_bind).
Tactic Notation "ibind" "with" uconstr(R) :=
  (eapply eutt_clo_bind with (UU := R)
 || eapply eq_itree_clo_bind with (UU := R)
 || eapply euttge_clo_bind with (UU := R)).

(* END TO MOVE *)

(** * Structural equations at the representation level

We prove here the equational theory that holds independently of the
interpretation of events.
These equations are expressed in terms of [eutt eq] over uninterpreted trees.
They derive from the [itree] combinators used to compute the uninterpreted
representation VIR's syntax.

In particular, notice that since [interp] is a iterative-monad morphism that respects
[eutt eq], these equations get transported at all levels of interpretations.

*)
Module Type DenotationTheory (LP : LLVMParams).
  Module D := Denotation LP.
  Import D.
  Import LP.

  Import SemNotations.

  Open Scope list_scope.

  Module DenoteTactics.

    Hint Rewrite @bind_ret_l : rwexp.
    Hint Rewrite @bind_bind : rwexp.
    Hint Rewrite @translate_ret : rwexp.
    Hint Rewrite @translate_bind : rwexp.
    Hint Rewrite @translate_trigger : rwexp.

    Ltac go :=
      (match goal with
      |- eutt _ ?t ?u =>
        let fresh := fresh in
        remember t as fresh;
        autorewrite with rwexp;
        subst fresh;
        remember u as fresh;
        autorewrite with rwexp;
        subst fresh
      end) ||
      (match goal with
      |- eq_itree _ ?t ?u =>
        let fresh := fresh in
        remember t as fresh;
        autorewrite with rwexp;
        subst fresh;
        remember u as fresh;
        autorewrite with rwexp;
        subst fresh
      end) ||
      (match goal with
        |- eqit _ _ _ ?t ?u =>
        let fresh := fresh in
        remember t as fresh;
        autorewrite with rwexp;
        subst fresh;
        remember u as fresh;
        autorewrite with rwexp;
        subst fresh
      end) ||
    autorewrite with rwexp.
    Tactic Notation "go*" := cbn; go.
    Tactic Notation "go**" := repeat (cbn; go).

  End DenoteTactics.
  Import DenoteTactics.

  (** [denote_code]
     - ⟦ [] ⟧c     ≈ Ret tt               [denote_code_nil]
     - ⟦ [i] ⟧c    ≈ ⟦ i ⟧i               [denote_code_singleton]
     - ⟦ i :: c ⟧c ≈ (⟦ i ⟧i ;; ⟦ c ⟧c)   [denote_code_cons]
     - ⟦ a ++ b ⟧c ≈ (⟦ a ⟧c ;; ⟦ b ⟧c)   [denote_code_app]
   *)

  Lemma denote_code_nil :
    ⟦ [] ⟧c ≈ Ret tt.
  Proof.
    by go*.
  Qed.

  Lemma denote_code_app_eq_itree :
    forall a b,
      ⟦ a ++ b ⟧c ≅ (⟦ a ⟧c ;; ⟦ b ⟧c).
  Proof.
    induction a; intros b.
    - by cbn; go.
    - cbn in *.
      go.
      ibind=; intros [].
      go.
      setoid_rewrite bind_ret_l.
      rewrite IHa.
      by go.
  Qed.

  Lemma denote_code_app :
    forall a b,
      ⟦ a ++ b ⟧c ≈ (⟦ a ⟧c ;; ⟦ b ⟧c).
  Proof.
    intros; by rewrite denote_code_app_eq_itree.
  Qed.

  Lemma denote_code_cons :
    forall i c,
      ⟦ i :: c ⟧c ≈ (⟦ i ⟧i ;; ⟦ c ⟧c).
  Proof.
    intros.
    go*.
    ibind=; intros [].
    go*.
    by setoid_rewrite bind_ret_l.
  Qed.

  Lemma denote_code_singleton :
    forall i,
      ⟦ [i] ⟧c ≈ ⟦ i ⟧i.
  Proof.
    intros a.
    rewrite denote_code_cons.
    bind_ret_r2.
    ibind=; intros [].
    apply denote_code_nil.
  Qed.

  (** [denote_phi]
      - ⟦ (x, Phi τ ({[bid := e]} ∪ tl)) ⟧Φ bid ≈ (uv <- ⟦ e at τ ⟧e; Ret (x,uv)).
   *)

  Lemma denote_phi_in : forall bid e x τ args,
      args !! bid = Some e ->
      ⟦ (x, Phi τ args) ⟧Φ bid ≈ (uv <- ⟦ e at τ ⟧e; Ret (x,uv)).
  Proof.
    intros; cbn.
    by simplify_map_eq.
  Qed.

  Lemma denote_phi_cup_l : forall bid x τ args args',
      args !! bid = None ->
      ⟦ (x, Phi τ (args ∪ args')) ⟧Φ bid ≈ ⟦ (x, Phi τ args') ⟧Φ bid.
  Proof.
    intros; cbn.
    by rewrite lookup_union_r.
  Qed.

  Lemma denote_phi_cup_r : forall bid x τ args args',
      args' !! bid = None ->
      ⟦ (x, Phi τ (args ∪ args')) ⟧Φ bid ≈ ⟦ (x, Phi τ args) ⟧Φ bid.
  Proof.
    intros; cbn.
    by rewrite lookup_union_l.
  Qed.

  Lemma denote_phi_add : forall bid e x τ tl,
      ⟦ (x, Phi τ ({[bid := e]} ∪ tl)) ⟧Φ bid ≈ (uv <- ⟦ e at τ ⟧e; Ret (x,uv)).
  Proof.
    intros; cbn.
    by simplify_map_eq.
  Qed.

  Lemma denote_phi_add_ne : forall bid bid' e x τ tl,
      bid <> bid' ->
      ⟦ (x, Phi τ ({[bid' := e ]} ∪ tl)) ⟧Φ bid ≈ ⟦ (x, Phi τ tl) ⟧Φ bid.
  Proof.
    intros; cbn.
    rewrite lookup_union_r; [done | by simplify_map_eq].
  Qed.

  (** [denote_phis]
   *)

  Lemma denote_phis_nil : forall x,
      ⟦ [] ⟧Φs x ≈ Ret tt.
  Proof.
    intros.
    go*.
    by go*.
  Qed.

  (* This only holds after interpretation: we can't justify the commutation of writes at this level
  Lemma denote_phis_cons : forall b φ φs,
      ⟦φ :: φs⟧Φs b ≈
     (v <- ⟦φ⟧Φ b;
      ⟦φs⟧Φs b;;
      trigger (LocalWrite (fst v) (snd v)))
  .
  Proof.
    intros ???; revert φ; induction φs as [| φhd φs IH].
    - intros [? []].
      go*.
      ibind=; intros []; go*.
      go**.
      bind_ret_r2.
      by ibind=; intros []; go*.
    - intros [? []].
      cbn.
      rewrite bind_bind.
      ibind=; intros [].
      specialize (IH φhd); cbn in IH.
      rewrite IH.
      go**.
      ibind=; intros []; go*.
      ibind=; intros vs; go**.
      repeat setoid_rewrite bind_bind.
      repeat setoid_rewrite bind_ret_l.
      cbn.
      cbn in IH.

      match goal with
        |- context[raise ?s] => generalize s
      end.
      intros s.
      cbn.
      match goal with
        |- context[raise ?s] => generalize s
      end.
      intros s'.
      rewrite ?bind_bind.
      apply eutt_eq_bind.
      intros [].
      rewrite ?bind_bind, ?bind_ret_l.
      cbn.
      cbn in IH.
  Admitted.
 *)


  (** [denote_block] *)
  Lemma denote_block_unfold_cont :
    forall {R} phis c t s origin (k : _ -> itree _ R),
      ⟦ mk_block phis c t s ⟧b origin >>= k
    ≈
     (⟦ phis ⟧Φs origin;;
      ⟦ c ⟧c;;
      ⟦ t ⟧t >>= k).
  Proof.
    by intros; cbn; repeat setoid_rewrite bind_bind.
  Qed.

  Lemma denote_block_unfold :
    forall phis c t s origin,
      ⟦ mk_block phis c t s ⟧b origin ≈
     (⟦ phis ⟧Φs origin;;
      ⟦ c ⟧c;;
      ⟦ t ⟧t).
  Proof.
    done.
  Qed.

  (** [denote_ocfg] *)
  Lemma denote_ocfg_empty: forall s, ⟦ ∅ ⟧bs s ≈ Ret (inl s).
  Proof.
    intros []; unfold denote_ocfg.
    setoid_rewrite unfold_iter.
    simplify_map_eq.
    by go*.
  Qed.

  Lemma denote_ocfg_in_eq_itree: forall bks bid_from bid_src bk,
      bks !! bid_src = Some bk ->
      ⟦ bks ⟧bs (bid_from, bid_src) ≅
     (vob <- ⟦ bk ⟧b bid_from ;
      match vob with
      | inr v => Ret (inr v)
      | inl bid_target => Tau (⟦ bks ⟧bs (bid_src, bid_target))
      end).
  Proof.
    intros * lu.
    cbn. unfold denote_ocfg at 1.
    setoid_rewrite unfold_iter_ktree.
    rewrite lu.
    go*.
    repeat (ibind=; intros ?).
    break_sum; go*; [| done].
    by apply eqit_Tau.
  Qed.

  Lemma denote_ocfg_in_euttge: forall bks bid_from bid_src bk,
      bks !! bid_src = Some bk ->
      ⟦ bks ⟧bs (bid_from, bid_src) ≳
     (vob <- ⟦ bk ⟧b bid_from ;
      match vob with
      | inr v => Ret (inr v)
      | inl bid_target => ⟦ bks ⟧bs (bid_src, bid_target)
      end).
  Proof.
    intros * lu.
    rewrite denote_ocfg_in_eq_itree; eauto.
    ibind=; intros ?.
    break_sum; go*; [| done].
    by rewrite tau_euttge.
  Qed.

  Lemma denote_ocfg_in: forall bks bid_from bid_src bk,
      bks !! bid_src = Some bk ->
      ⟦ bks ⟧bs (bid_from, bid_src)
     ≈
     (vob <- ⟦ bk ⟧b bid_from ;
      match vob with
      | inr v => Ret (inr v)
      | inl bid_target => ⟦ bks ⟧bs (bid_src, bid_target)
      end).
  Proof.
    intros * lu.
    by rewrite denote_ocfg_in_euttge.
  Qed.

  Lemma denote_ocfg_nin_eq_itree: forall bks bid_from bid_src,
      bks !! bid_src = None ->
      ⟦ bks ⟧bs (bid_from, bid_src) ≅ Ret (inl (bid_from,bid_src)).
  Proof.
    intros * lu.
    unfold denote_ocfg.
    rewrite unfold_iter_ktree, lu.
    by go*.
  Qed.

  Lemma denote_ocfg_nin: forall bks bid_from bid_src,
      bks !! bid_src = None ->
      ⟦ bks ⟧bs (bid_from, bid_src) ≈ Ret (inl (bid_from,bid_src)).
  Proof.
    intros * lu.
    by rewrite denote_ocfg_nin_eq_itree.
  Qed.

  Lemma denote_ocfg_unfold: forall bks bid_from bid_src,
      ⟦ bks ⟧bs (bid_from, bid_src) ≅
    (match bks !! bid_src with
      | Some bk => vob <- ⟦ bk ⟧b bid_from ;
                  match vob with
                  | inr v => Ret (inr v)
                  | inl bid_target => Tau (⟦ bks ⟧bs (bid_src, bid_target))
                  end
      | None => Ret (inl (bid_from,bid_src))
      end).
  Proof.
    intros *.
    break_match_goal.
    - by rewrite denote_ocfg_in_eq_itree.
    - by rewrite denote_ocfg_nin_eq_itree.
  Qed.

  Section Outputs.

    (** * outputs soundness *)

    Lemma raise_has_all_posts : forall {E X} `{FailureE -< E} s Q,
        @raise E X _ s ⤳ Q.
    Proof.
      unfold raise; intros.
      apply has_post_bind; intros [].
    Qed.

    Lemma raiseUB_has_all_posts : forall {E X} `{UBE -< E} s Q,
        @raiseUB E _ X s ⤳ Q.
    Proof.
      unfold raise; intros.
      apply has_post_bind; intros [].
    Qed.

    Lemma raise_has_all_posts_cont : forall {E X Y} `{FailureE -< E} s (k : X -> itree E Y) Q,
         (x <- @raise E X _ s; k x) ⤳ Q.
    Proof.
      intros.
      rewrite raise_bind_itree.
      apply raise_has_all_posts.
    Qed.
    Lemma raiseUB_has_all_posts_cont : forall {E X Y} `{UBE -< E} s (k : X -> itree E Y) Q,
         (x <- @raiseUB E _ X s; k x) ⤳ Q.
    Proof.
      intros.
      rewrite raiseUB_bind_itree.
      apply raiseUB_has_all_posts.
    Qed.

    Lemma select_switch_in :
      forall x default_dest brs id,
        select_switch x default_dest brs = inr id ->
        id = default_dest \/ In id (List.map snd brs).
    Proof.
      intros x default_dest brs id SELECT.
      induction brs.
      - inversion SELECT; auto.
      - cbn in SELECT.
        break_match_hyp.
        break_match_hyp; inversion SELECT;
          break_match_hyp; inversion SELECT;
          subst;
          break_match_hyp; inversion SELECT; subst; cbn; tauto.
    Qed.

    Ltac hpbind  := apply has_post_bind; intros ?.
    Ltac ehpbind := eapply has_post_bind_strong.
    Ltac uehpbind := unshelve eapply has_post_bind_strong.
    Tactic Notation "hpbind" "with" uconstr(t) := apply has_post_bind_strong with t.
    Ltac hpret  := apply eutt_Ret.
    Ltac hpabs  :=
       try (apply raise_has_all_posts || apply raiseUB_has_all_posts ||
             apply raise_has_all_posts_cont || apply raiseUB_has_all_posts_cont
        ).

    Lemma has_post_map_monad :
      forall {E} {A B} (f : A -> itree E B) (P : B -> Prop) (l : list A),
        (forall x, List.In x l -> f x ⤳ P) ->
        map_monad f l ⤳ Forall P.
    Proof.
      intros * IH'.
      induction l as [| t l IH].
      - by hpret.
      - go*.
        hpbind with P; [apply IH'; by left | ].
        intros ? HP.
        hpbind with (Forall P); [apply IH; intros; apply IH'; right; auto | ].
        intros ? HP'; hpret.
        by apply Forall_cons.
    Qed.

    Ltac hpmap  := apply has_post_map_monad.

    Tactic Notation "break_err" "as" ident(H) :=
      match goal with
        |- context[lift_err _ ?x] => destruct x eqn:H; cbn [lift_err]
      end .
    Ltac break_err := let H := fresh in break_err as H.

    Tactic Notation "hperr" "as" ident(H) := break_err as H; [hpabs |].
    Tactic Notation "hperr" := let H := fresh in hperr as H.

    Import ITree.
    Import Events.DV.

    Lemma denote_terminator_exits_in_outputs :
      forall term,
        ⟦ term ⟧t ⤳ sum_pred (fun id => id ∈ terminator_outputs term) TT.
    Proof with set_solver.
      intros term; destruct term eqn:Hterm; cbn; try (hpabs || hpret; set_solver).
      - destruct v.
        hpbind.
        hpret...
      - destruct v; cbn.
        hpbind.
        hpbind.
        break_match_goal; hpabs.
        break_match_goal; hpret...
      - destruct v; cbn.
        hpbind.
        hpbind.
        break_match_goal; hpabs.
        clear Hterm term.

        hpbind with (Forall (fun id => In (snd id) (List.map snd brs))).
        + hpmap.
          intros [[] ?] ?.
          case_match; hpabs.
          case_match; go; hpret.
          subst.
          all: by apply in_map with (f := snd) in H.
        + intros ? FORALL.
          hperr as Hswitch.
          hpret; cbn.
          apply select_switch_in in Hswitch.
          destruct_or?.
          set_solver.
          (* The remaining of this proof should not be so messy. Why [gset_semi_set] is not visible earlier? *)
          apply Coqlib.list_in_map_inv in Hswitch as ([? ?] & -> & IN).
          rewrite Forall_forall in FORALL.
          apply FORALL in IN.
          cbn in *.
          apply elem_of_list_In in IN.
          eapply elem_of_list_to_set in IN.
          apply elem_of_union_r.
          apply IN.
          Unshelve.
          apply gset_semi_set.
    Qed.

    Definition exits_in_outputs {t} ocfg : block_id * block_id + uvalue -> Prop :=
      sum_pred (fun fto => snd fto ∈ @outputs t ocfg) TT.

    Lemma denote_bk_exits_in_outputs :
      forall b from,
        ⟦ b ⟧b from ⤳ sum_pred (fun id => id ∈ successors b) TT.
    Proof.
      intros; cbn.
      repeat hpbind.
      apply denote_terminator_exits_in_outputs.
    Qed.

    (* Given a predicate [Qb] on pairs of block ids (the origin for phi-nodes and the input)
   and a predicate [Qv] on values, we establish that both hold after the denotation of an open_cfg if:
   - [Qb] holds at the initial entry point
   - [Qb] and [Qv] are preserved by the denotation of any blocks in the open cfg, assuming [Qb]
     *)
    Lemma denote_ocfg_has_post_strong :
      forall (bks : ocfg _) fto (Qb : block_id * block_id -> Prop) (Qv : uvalue -> Prop)
        (INIT : Qb fto)
        (IND : forall fto (b : block dtyp),
            Qb fto ->
            bks !! snd fto = Some b ->
            ⟦ b ⟧b (fst fto) ⤳ sum_pred (fun to => Qb (snd fto, to)) Qv),
        ⟦ bks ⟧bs fto ⤳ sum_pred Qb Qv.
    Proof.
      intros * INIT IND.
      eapply has_post_iter_strong; eauto.
      intros [f to] PRE.
      flatten_goal.
      - specialize (IND (f,to) b).
        eapply eutt_post_bind; [apply IND |]; auto.
        intros [id | v]; cbn; intros ?; apply eutt_Ret; auto.
      - apply eutt_Ret; auto.
    Qed.

    (* A weaker but sometimes easier to use modular way to prove postconditions of open cfgs:
   - assuming that all blocks in the open cfg admits as postconditions [sum_pred Qb Qv]
   - and assuming that we indeed enter the [open_cfg]
   then we get [Qb/Qv], and ignore the origin of the jump.
     *)
    Lemma denote_ocfg_has_post :
      forall (bks : ocfg _) fto (Qb : block_id -> Prop) (Qv : uvalue -> Prop)
        (ENTER : snd fto ∈ inputs bks)
        (IND : forall fto (b : block dtyp),
            bks !! snd fto = Some b ->
            ⟦ b ⟧b (fst fto) ⤳ sum_pred Qb Qv),
        ⟦ bks ⟧bs fto ⤳ sum_pred (prod_pred TT Qb) Qv.
    Proof.
      intros * IN IND.
      apply has_post_iter_strong with (Inv := fun x => snd x ∈ inputs bks \/ Qb (snd x))
      ; eauto.
      intros [f to] HYP.
      flatten_goal.
      - specialize (IND (f,to) b).
        eapply eutt_post_bind; [apply IND |]; auto.
        intros [id | v]; cbn; intros ?; apply eutt_Ret; cbn; auto.
      - apply eutt_Ret.
        split; auto.
        destruct HYP as [abs | POST]; auto.
        apply find_block_in_inputs in abs as [? abs]; cbn in abs; rewrite abs in Heq; inv Heq.
    Qed.

    Lemma denote_ocfg_exits_in_outputs :
      forall bks fto,
        snd fto ∈ inputs bks ->
        ⟦ bks ⟧bs fto ⤳ exits_in_outputs bks.
    Proof.
      intros * IN.
      apply has_post_weaken with (P := sum_pred (prod_pred TT (fun b => b ∈ outputs bks)) TT).
      2: intros [[]|] ?; cbn in *; intuition.
      apply denote_ocfg_has_post; eauto.
      intros.
      eapply has_post_weaken.
      eapply denote_bk_exits_in_outputs.
      intros []; cbn; intuition.
      by eapply outputs_elem_of.
    Qed.

  End Outputs.

  (** * denote_ocfg  *)

  Lemma denote_ocfg_union_no_edges :
    forall (bks1 bks2 : ocfg _) fto,
      bks1 !! snd fto = None ->
      no_reentrance bks1 bks2 ->
      ⟦ bks1 ∪ bks2 ⟧bs fto ≈ ⟦ bks2 ⟧bs fto.
  Proof.
    intros bks1 bks2 [f to] FIND NOBACK.
    apply (@KTreeFacts.eutt_iter_gen _ _ _ (fun fto fto' => fto' = fto /\ bks1 !! snd fto = None)); auto.
    clear f to FIND; intros fto fto' [-> FIND]; destruct fto as [f to] .
    cbn in *.
    rewrite lookup_union_r; auto.
    case_match eqn:FIND_L2.
    - eapply eutt_post_bind.
      apply denote_bk_exits_in_outputs.
      intros [id | v] ?; cbn; apply eutt_Ret; eauto.
      eapply inl_morphism; split; auto.
      cbn. cbn in *.
      eapply free_out_of_inputs,no_reentrance_not_in; eauto.
      eapply outputs_elem_of; eauto.
    - apply eutt_Ret; right; auto.
  Qed.

  Lemma denote_ocfg_union :
    forall bks1 bks2 fto,
      no_reentrance bks1 bks2 ->
      ⟦ bks1 ∪ bks2 ⟧bs fto ≈
     ('x <- ⟦ bks1 ⟧bs fto;
      match x with
      | inl fto2 => ⟦ bks2 ⟧bs fto2
      | inr v => Ret (inr v)
      end).
  Proof.
    intros * NOBACK.
    revert fto.
    einit.
    ecofix CIH.
    intros [f to].
    case (bks1 !! to) eqn:FIND.
    - rewrite 2 denote_ocfg_unfold.
      simplify_map_eq.
      go.
      ebind; econstructor; [reflexivity | intros ??<-].
      case_match.
      rewrite bind_tau; etau.
      by go.
    - efinal.
      rewrite denote_ocfg_union_no_edges; auto.
      by rewrite (denote_ocfg_nin bks1); auto; go*.
  Qed.

  Lemma denote_ocfg_flow_left :
    forall ocfg1 ocfg2 fto,
      independent_flows ocfg1 ocfg2 ->
      snd fto ∈ inputs ocfg1 ->
      ⟦ ocfg1 ∪ ocfg2 ⟧bs fto ≈
      ⟦ ocfg1 ⟧bs fto.
  Proof.
    intros * INDEP IN.
    rewrite denote_ocfg_union; [| auto using independent_flows_no_reentrance_l].
    bind_ret_r2.

    eapply eutt_post_bind; [apply denote_ocfg_exits_in_outputs; eauto |].
    intros [[f to] | ?] EXIT; [| reflexivity].
    rewrite denote_ocfg_nin; [reflexivity |].
    cbn in *.
    apply free_out_of_inputs.
    eapply no_reentrance_not_in; eauto.
    apply INDEP.
  Qed.

  Lemma denote_ocfg_flow_right :
    forall ocfg1 ocfg2 fto,
      independent_flows ocfg1 ocfg2 ->
      snd fto ∈ inputs ocfg2 ->
      ⟦ ocfg1 ∪ ocfg2 ⟧bs fto ≈ ⟦ ocfg2 ⟧bs fto.
  Proof.
    intros * INDEP IN.
    rewrite denote_ocfg_union; [| auto using independent_flows_no_reentrance_l].
    destruct fto as [f to]; cbn in *.
    rewrite denote_ocfg_nin.
    by go.
    eapply free_out_of_inputs, disjoint_inputs_l; eauto using independent_flows_disjoint.
  Qed.

  Opaque denote_block.
  Lemma denote_ocfg_prefix :
    forall (prefix bks' postfix bks : ocfg dtyp) (from to: block_id),
      bks = (prefix ∪ bks' ∪ postfix) ->
      prefix ##ₘ bks' ->
      ⟦ bks ⟧bs (from, to) ≈
     ('x <- ⟦ bks' ⟧bs (from, to);
      match x with
      | inl x => ⟦ bks ⟧bs x
      | inr x => Ret (inr x)
      end)
  .
  Proof.
    intros * ->; revert from to.
    einit.
    ecofix CIH.
    clear CIHH.
    intros * DISJ.
    case (bks' !! to) as [bk |] eqn:EQ.
    - unfold denote_ocfg at 1 3.
      setoid_rewrite KTreeFacts.unfold_iter_ktree.
      go**.
      assert (EQ': (prefix ∪ bks' ∪ postfix) !! to = Some bk) by (by simplify_map_eq).
      rewrite EQ, EQ'; go**.
      eapply euttG_bind; econstructor; [reflexivity | intros [] ? <-].
      + go*.
        rewrite bind_tau; etau.
      + by go.
    - edrop.
      rewrite (denote_ocfg_nin bks'); auto.
      by go*.
  Qed.
  Transparent denote_block.
End DenotationTheory.

Module Make (LP : LLVMParams) : DenotationTheory LP.
  Include DenotationTheory LP.
End Make.

(* Module DenotationTheoryBigIntptr := Make LLVMParamsBigIntptr. InterpreterStackBigIntptr TopLevelBigIntptr. *)
(* Module DenotationTheory64BitIntptr := Make InterpreterStack64BitIntptr TopLevel64BitIntptr. *)
