(* begin hide *)

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
     Semantics
     Syntax.ScopeTheory
     Utils.PostConditions
     Utils.ITreeRaise.

#[export] Remove Hints Eqv.EqvWF_Build : typeclass_instances.

Set Implicit Arguments.
Set Strict Implicit.

Import MonadNotation.
Open Scope list_scope.
Open Scope monad_scope.
Open Scope itree.
Import ITreeNotations.
Import EitherMonad.
Import IdentityMonad.
Import ListNotations.

(* end hide *)

(** * Structural equations at the representation level

We prove here the equational theory that holds independently of the
interpretation of events.
These equations are expressed in terms of [eutt eq] over uninterpreted trees.
They derive from the [itree] combinators used to compute the uninterpreted
representation VIR's syntax.

In particular, notice that since [interp] is a iterative-monad morphism that respects
[eutt eq], these equations get transported at all levels of interpretations.

*)
Module Type DenotationTheory (IS : InterpreterStack) (TOP : LLVMTopLevel IS).
  Export TOP.
  Export IS.
  Export IS.LLVM.

  Import SemNotations.

  Open Scope list_scope.

  Module DenoteTactics.

    Hint Rewrite @bind_ret_l : rwexp.
    Hint Rewrite @bind_bind : rwexp.
    Hint Rewrite @translate_ret : rwexp.
    Hint Rewrite @translate_bind : rwexp.
    Hint Rewrite @translate_trigger : rwexp.

    Ltac go := autorewrite with rwexp.

  End DenoteTactics.
  Import DenoteTactics.

  (** [denote_code] *)

  Lemma denote_code_nil vararg :
    ⟦ [] ⟧c vararg ≈ Ret tt.
  Proof using.
    intros.
    cbn.
    go.
    reflexivity.
  Qed.

  Lemma denote_code_app :
    forall vararg a b,
      ⟦ a ++ b ⟧c vararg ≈ ⟦ a ⟧c vararg;;  ⟦ b ⟧c vararg.
  Proof using.
    intros vararg.
    induction a; intros b.
    - cbn; go; reflexivity.
    - cbn in *.
      go.
      apply eutt_eq_bind; intros ().
      go.
      setoid_rewrite bind_ret_l.
      rewrite IHa.
      go.
      reflexivity.
  Qed.

  Lemma denote_code_app_eq_itree :
    forall vararg a b,
      ⟦ a ++ b ⟧c vararg ≅ ITree.bind (⟦ a ⟧c vararg) (fun _ => ⟦ b ⟧c vararg).
  Proof using.
    induction a; intros b.
    - cbn.
      go.
      eapply eq_itree_clo_bind with (UU := eq); [reflexivity | intros ? ? ->; reflexivity].
    - cbn in *.
      go.
      eapply eq_itree_clo_bind with (UU := eq); [reflexivity | intros ? ? ->].
      setoid_rewrite bind_ret_l.
      setoid_rewrite bind_bind.
      setoid_rewrite bind_ret_l.
      rewrite IHa.
      setoid_rewrite bind_bind.
      eapply eq_itree_clo_bind with (UU := eq); [reflexivity | intros ? ? ->].
      setoid_rewrite bind_ret_l.
      eapply eq_itree_clo_bind with (UU := eq); [reflexivity | intros ? ? ->].
      reflexivity.
  Qed.

  Lemma denote_code_cons :
    forall vararg i c,
      ⟦ i::c ⟧c vararg ≈  ⟦ i ⟧i vararg;; ⟦ c ⟧c vararg.
  Proof using.
    intros.
    cbn.
    go.
    apply eutt_eq_bind; intros ().
    go.
    setoid_rewrite bind_ret_l.
    reflexivity.
  Qed.

  Lemma denote_code_singleton :
    forall vararg i,
      ⟦ [i] ⟧c vararg ≈ ⟦ i ⟧i vararg.
  Proof using.
    intros vararg a.
    cbn.
    go.
    bind_ret_r2.
    apply eutt_eq_bind; intros [].
    go.
    reflexivity.
  Qed.

  (** [denote_phi] *)
  (* TODO: make a choice about it and move *)
  Opaque assoc.
  Lemma denote_phi_hd : forall bid e id τ tl,
      ⟦ (id, Phi τ ((bid,e)::tl)) ⟧Φ bid ≈ uv <- ⟦ e at τ ⟧e;; Ret (id,uv).
  Proof using.
    intros; cbn.
    rewrite assoc_hd; reflexivity.
  Qed.

  Lemma denote_phi_tl : forall bid bid' e id τ tl,
      bid <> bid' ->
      ⟦ (id, Phi τ ((bid',e)::tl)) ⟧Φ bid ≈ ⟦ (id, Phi τ tl) ⟧Φ bid.
  Proof using.
    intros; cbn.
    rewrite assoc_tl; auto; reflexivity.
  Qed.

  Lemma denote_no_phis : forall x,
      ⟦ [] ⟧Φs x ≈ Ret tt.
  Proof using.
    intros.
    cbn. go.
    cbn; go.
    unfold denote_phis; cbn.
    reflexivity.
  Qed.

  (** [denote_block] *)
  Lemma denote_block_unfold_cont :
    forall {R} vararg id phis c t s origin (k : _ -> itree _ R),
      ⟦ mk_block id phis c t s ⟧b origin vararg >>= k
                                ≈
                                ⟦ phis ⟧Φs origin;;
      ⟦ c ⟧c vararg ;;
      translate exp_to_instr ⟦ t ⟧t >>= k.
  Proof using.
    intros; cbn; repeat setoid_rewrite bind_bind.
    reflexivity.
  Qed.

  Lemma denote_block_unfold :
    forall vararg id phis c t s origin,
      ⟦ mk_block id phis c t s ⟧b origin vararg ≈
                                ⟦ phis ⟧Φs origin;;
      ⟦ c ⟧c vararg;;
      translate exp_to_instr ⟦ t ⟧t.
  Proof using.
    intros; cbn; reflexivity.
  Qed.

  (** [denote_ocfg] *)
  Lemma denote_ocfg_nil: forall vararg s, ⟦ [] ⟧bs vararg s ≈ Ret (inl s).
  Proof using.
    intros vararg []; unfold denote_ocfg.
    match goal with
    | |- CategoryOps.iter (C := ktree _) ?body ?s ≈ _ =>
        rewrite (unfold_iter body s)
    end.
    cbn; go.
    reflexivity.
  Qed.

  Lemma denote_ocfg_unfold_in: forall vararg bks bid_from bid_src bk,
      find_block bks bid_src = Some bk ->
      ⟦ bks ⟧bs vararg (bid_from, bid_src) ≈
             vob <- ⟦ bk ⟧b bid_from vararg ;;
      match vob with
      | inr v => Ret (inr v)
      | inl bid_target => ⟦ bks ⟧bs vararg (bid_src, bid_target)
      end.
  Proof using.
    intros * GET_BK.
    cbn. unfold denote_ocfg at 1.
    rewrite KTreeFacts.unfold_iter_ktree. cbn.
    rewrite GET_BK.
    repeat setoid_rewrite bind_bind.
    repeat (apply eutt_eq_bind; intros ?).
    break_sum; rewrite bind_ret_l; [|reflexivity].
    rewrite tau_eutt; reflexivity.
  Qed.

  Lemma denote_ocfg_unfold_not_in: forall vararg bks bid_from bid_src,
      find_block bks bid_src = None ->
      ⟦ bks ⟧bs vararg (bid_from, bid_src) ≈ Ret (inl (bid_from,bid_src)).
  Proof using.
    intros * GET_BK.
    unfold denote_ocfg.
    rewrite KTreeFacts.unfold_iter_ktree.
    rewrite GET_BK; cbn.
    rewrite bind_ret_l.
    reflexivity.
  Qed.

  Lemma denote_ocfg_unfold_in_euttge: forall vararg bks bid_from bid_src bk,
      find_block bks bid_src = Some bk ->
      ⟦ bks ⟧bs vararg (bid_from, bid_src) ≳
             vob <- ⟦ bk ⟧b bid_from vararg ;;
      match vob with
      | inr v => Ret (inr v)
      | inl bid_target => ⟦ bks ⟧bs vararg (bid_src, bid_target)
      end.
  Proof using.
    intros * GET_BK.
    cbn. unfold denote_ocfg at 1.
    rewrite KTreeFacts.unfold_iter_ktree. cbn.
    rewrite GET_BK.
    repeat setoid_rewrite bind_bind.
    repeat (eapply eqit_bind; [reflexivity | intros ?]).
    break_sum; rewrite bind_ret_l; [|reflexivity].
    rewrite tau_euttge; reflexivity.
  Qed.

  Lemma denote_ocfg_unfold_in_eq_itree: forall vararg bks bid_from bid_src bk,
      find_block bks bid_src = Some bk ->
      ⟦ bks ⟧bs vararg (bid_from, bid_src) ≅
             vob <- ⟦ bk ⟧b bid_from vararg ;;
      match vob with
      | inr v => Ret (inr v)
      | inl bid_target => Tau (⟦ bks ⟧bs vararg (bid_src, bid_target))
      end.
  Proof using.
    intros * GET_BK.
    cbn. unfold denote_ocfg at 1.
    rewrite KTreeFacts.unfold_iter_ktree. cbn.
    rewrite GET_BK.
    repeat setoid_rewrite bind_bind.
    repeat (eapply eqit_bind; [reflexivity | intros ?]).
    break_sum; rewrite bind_ret_l; [|reflexivity].
    apply eqit_Tau.
    reflexivity.
  Qed.

  Lemma denote_ocfg_unfold_not_in_eq_itree: forall vararg bks bid_from bid_src,
      find_block bks bid_src = None ->
      ⟦ bks ⟧bs vararg (bid_from, bid_src) ≅ Ret (inl (bid_from,bid_src)).
  Proof using.
    intros * GET_BK.
    unfold denote_ocfg.
    rewrite KTreeFacts.unfold_iter_ktree.
    rewrite GET_BK; cbn.
    rewrite bind_ret_l.
    reflexivity.
  Qed.

  Lemma denote_ocfg_unfold_eq_itree: forall vararg bks bid_from bid_src,
      ⟦ bks ⟧bs vararg (bid_from, bid_src) ≅
             match find_block bks bid_src with
             | Some bk => vob <- ⟦ bk ⟧b bid_from vararg ;;
                          match vob with
                          | inr v => Ret (inr v)
                          | inl bid_target => Tau (⟦ bks ⟧bs vararg (bid_src, bid_target))
                          end
             | None => Ret (inl (bid_from,bid_src))
             end.
  Proof using.
    intros *.
    break_match_goal.
    - rewrite denote_ocfg_unfold_in_eq_itree; eauto; reflexivity.
    - rewrite denote_ocfg_unfold_not_in_eq_itree; eauto; reflexivity.
  Qed.

  Section Outputs.

    (** * outputs soundness *)

    Lemma raise_has_all_posts : forall {E X} `{FailureE -< E} s Q,
        @raise E X _ s ⤳ Q.
    Proof using.
      unfold raise; intros.
      apply has_post_bind; intros [].
    Qed.

    Lemma raiseUB_has_all_posts : forall {E X} `{UBE -< E} s Q,
        @raiseUB E _ X s ⤳ Q.
    Proof using.
      unfold raise; intros.
      apply has_post_bind; intros [].
    Qed.

    Lemma unEither_eta : forall {T m A} (x : eitherT T m A), {|unEitherT := unEitherT x|} = x.
    Proof using.
      intros.
      destruct x.
      f_equal.
    Qed.

    Lemma unIdent_eta : forall {A} (x : ident A), {|unIdent := unIdent x|} = x.
    Proof using.
      intros.
      destruct x.
      f_equal.
    Qed.

    Lemma select_switch_in :
      forall x default_dest brs id,
        select_switch x default_dest brs = inr id ->
        id = default_dest \/ In id (List.map snd brs).
    Proof using.
      intros x default_dest brs id SELECT.
      induction brs.
      - inversion SELECT; auto.
      - cbn in SELECT.
        break_match_hyp; subst;
        break_match_hyp; inversion SELECT; subst;
          break_match_hyp; inversion SELECT; subst;
          break_match_hyp; inversion SELECT; subst;
          cbn in *;
          break_match_hyp_inv;
          tauto.
    Qed.

    Lemma denote_terminator_exits_in_outputs :
      forall term,
        ⟦ term ⟧t ⤳ sum_pred (fun id => In id (terminator_outputs term)) TT.
    Proof using.
      intros term; destruct term eqn:Hterm; cbn; try (apply raise_has_all_posts || apply eutt_Ret; cbn; eauto).
      - destruct v.
        apply has_post_bind; intros ?.
        apply eutt_Ret; cbn; eauto.
      - destruct v; cbn.
        apply has_post_bind; intros ?.
        apply has_post_bind; intros ?.
        break_match_goal; try (apply raise_has_all_posts || apply raiseUB_has_all_posts); subst.
        break_match_goal; try (apply raise_has_all_posts || apply raiseUB_has_all_posts); subst.
        break_match_goal; apply eutt_Ret; cbn; eauto.
      - destruct v; cbn.
        apply has_post_bind; intros ?.
        apply has_post_bind; intros ?.
        break_match_goal;
          try (apply raise_has_all_posts || apply raiseUB_has_all_posts).

        clear Hterm.
        clear term.

        eapply has_post_bind_strong with
          (S := fun switches =>
                  Forall
                    (fun id => In id (List.map snd brs))
                    (List.map snd switches)).

        + induction brs; cbn.
          * apply eutt_Ret. cbn.
            apply Forall_nil.
          * break_match_goal; subst.
            break_match_goal; subst.

            repeat break_match_goal;
              try (cbn; go; setoid_rewrite raise_bind_itree; apply raise_has_all_posts).

            go.
            eapply eutt_clo_bind; eauto.
            intros u1 u2 H.
            apply eutt_Ret.
            cbn.
            cbn in H.
            apply Forall_cons; eauto.
            apply Forall_impl with (P := fun id => In id (List.map snd brs)); eauto.

        + intros x1 H.
          destruct (select_switch x0 default_dest x1) eqn:HSwitch; cbn.
          apply raise_has_all_posts.
          apply select_switch_in in HSwitch.
          apply eutt_Ret; cbn.
          destruct HSwitch; auto; right.
          eapply Forall_forall in H; eauto.
      - apply raiseUB_has_all_posts.
    Qed.

    Definition exits_in_outputs {t} ocfg : block_id * block_id + uvalue -> Prop :=
      sum_pred (fun fto => In (snd fto) (@outputs t ocfg)) TT.

    Lemma denote_bk_exits_in_outputs :
      forall vararg b from,
        ⟦ b ⟧b from vararg ⤳ sum_pred (fun id => In id (successors b)) TT.
    Proof using.
      intros.
      cbn.
      apply has_post_bind; intros [].
      apply has_post_bind; intros [].
      apply has_post_translate.
      apply denote_terminator_exits_in_outputs.
    Qed.

    (* Given a predicate [Qb] on pairs of block ids (the origin for phi-nodes and the input)
   and a predicate [Qv] on values, we establish that both hold after the denotation of an open_cfg if:
   - [Qb] holds at the initial entry point
   - [Qb] and [Qv] are preserved by the denotation of any blocks in the open cfg, assuming [Qb]
     *)
    Lemma denote_ocfg_has_post_strong :
      forall vararg (bks : ocfg _) fto (Qb : block_id * block_id -> Prop) (Qv : uvalue -> Prop)
        (INIT : Qb fto)
        (IND : forall fto (b : block dtyp),
            Qb fto ->
            find_block bks (snd fto) = Some b ->
            ⟦ b ⟧b (fst fto) vararg ⤳ sum_pred (fun to => Qb (snd fto, to)) Qv),
        ⟦ bks ⟧bs vararg fto ⤳ sum_pred Qb Qv.
    Proof using.
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
      forall vararg (bks : ocfg _) fto (Qb : block_id -> Prop) (Qv : uvalue -> Prop)
        (ENTER : In (snd fto) (inputs bks))
        (IND : forall fto (b : block dtyp),
            find_block bks (snd fto) = Some b ->
            ⟦ b ⟧b (fst fto) vararg ⤳ sum_pred Qb Qv),
        ⟦ bks ⟧bs vararg fto ⤳ sum_pred (prod_pred TT Qb) Qv.
    Proof using.
      intros * IN IND.
      apply has_post_iter_strong with (Inv := fun x => In (snd x) (inputs bks) \/ Qb (snd x))
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
      forall vararg bks fto,
        In (snd fto) (inputs bks) ->
        ⟦ bks ⟧bs vararg fto ⤳ exits_in_outputs bks.
    Proof using.
      intros * IN.
      apply has_post_weaken with (P := sum_pred (prod_pred TT (fun b => In b (outputs bks))) TT).
      2: intros [[]|] ?; cbn in *; intuition.
      apply denote_ocfg_has_post; eauto.
      intros.
      eapply has_post_weaken.
      eapply denote_bk_exits_in_outputs.
      intros []; cbn; intuition.
      eapply In_bk_outputs; eauto.
    Qed.

  End Outputs.

  (** * denote_ocfg  *)

  Lemma denote_ocfg_app_no_edges :
    forall vararg (bks1 bks2 : ocfg _) fto,
      find_block bks1 (snd fto) = None ->
      no_reentrance bks1 bks2 ->
      ⟦ bks1 ++ bks2 ⟧bs vararg fto ≈ ⟦ bks2 ⟧bs vararg fto.
  Proof using.
    intros vararg bks1 bks2 [f to] FIND NOBACK.
    apply (@KTreeFacts.eutt_iter_gen _ _ _ (fun fto fto' => fto' = fto /\ find_block bks1 (snd fto) = None)); auto.
    clear f to FIND; intros fto fto' [-> FIND]; destruct fto as [f to] .
    cbn in *.
    epose proof (find_block_none_app _ bks2 _ FIND) as FIND_L1L2.
    rewrite FIND_L1L2.
    destruct (find_block bks2 to) eqn:FIND_L2.
    - eapply eutt_post_bind.
      apply denote_bk_exits_in_outputs.
      intros [id | v] ?; cbn; apply eutt_Ret; eauto.
      eapply inl_morphism; split; auto.
      eapply find_block_not_in_inputs,no_reentrance_not_in; eauto.
      eapply In_bk_outputs; eauto.

    - apply eutt_Ret; right; auto.
  Qed.

  Lemma denote_ocfg_app :
    forall vararg bks1 bks2 fto,
      no_reentrance bks1 bks2 ->
      ⟦ bks1 ++ bks2 ⟧bs vararg fto ≈
                      'x <- ⟦ bks1 ⟧bs vararg fto;;
      match x with
      | inl fto2 => ⟦ bks2 ⟧bs vararg fto2
      | inr v => Ret (inr v)
      end.
  Proof using.
    intros * NOBACK.
    revert fto.
    einit.
    ecofix CIH.
    intros [f to].
    destruct (find_block bks1 to) eqn:FIND.
    - unfold denote_ocfg.
      unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree.
      match goal with
        |- euttG _ _ _ _ _ ?t _ => remember t; rewrite unfold_iter; subst
      end.
      rewrite unfold_iter; cbn.
      match_rewrite.
      rewrite !bind_bind.
      pose proof find_block_some_app bks1 bks2 to FIND as FIND_APP.
      rewrite FIND_APP.
      cbn.
      rewrite !bind_bind.
      match goal with
        |- euttG _ _ _ _ _ ?t _ => remember t
      end.
      subst; ebind; econstructor; [reflexivity | intros ? ? <-].
      ebind; econstructor; [reflexivity | intros ? ? <-].
      ebind; econstructor; [reflexivity | intros ? ? <-].
      destruct u2 as [bid | v].
      + rewrite !bind_ret_l.
        rewrite bind_tau.
        etau.
      + rewrite !bind_ret_l.
        eret.
    - efinal.
      rewrite denote_ocfg_app_no_edges; auto.
      rewrite denote_ocfg_unfold_not_in with (bks := bks1); auto.
      rewrite bind_ret_l; reflexivity.
  Qed.

  Lemma denote_ocfg_flow_left :
    forall vararg ocfg1 ocfg2 fto,
      independent_flows ocfg1 ocfg2 ->
      In (snd fto) (inputs ocfg1) ->
      ⟦ ocfg1 ++ ocfg2 ⟧bs vararg fto ≈
                        ⟦ ocfg1 ⟧bs vararg fto.
  Proof using.
    intros * INDEP IN.
    rewrite denote_ocfg_app; [| auto using independent_flows_no_reentrance_l].
    bind_ret_r2.

    eapply eutt_post_bind; [apply denote_ocfg_exits_in_outputs; eauto |].
    intros [[f to] | ?] EXIT; [| reflexivity].
    rewrite denote_ocfg_unfold_not_in; [reflexivity |].
    cbn in *.
    apply find_block_not_in_inputs.
    eapply no_reentrance_not_in; eauto.
    apply INDEP.
  Qed.

  Lemma denote_ocfg_flow_right :
    forall vararg ocfg1 ocfg2 fto,
      independent_flows ocfg1 ocfg2 ->
      In (snd fto) (inputs ocfg2) ->
      ⟦ ocfg1 ++ ocfg2 ⟧bs vararg fto ≈
                        ⟦ ocfg2 ⟧bs vararg fto.
  Proof using.
    intros * INDEP IN.
    rewrite denote_ocfg_app; [| auto using independent_flows_no_reentrance_l].
    destruct fto as [f to]; cbn in *.
    rewrite denote_ocfg_unfold_not_in.
    rewrite bind_ret_l; reflexivity.
    eapply find_block_not_in_inputs, no_duplicate_bid_not_in_l; eauto using independent_flows_no_duplicate_bid.
  Qed.

  Opaque denote_block.
  Lemma denote_ocfg_prefix :
    forall vararg (prefix bks' postfix bks : ocfg dtyp) (from to: block_id),
      bks = (prefix ++ bks' ++ postfix) ->
      wf_ocfg_bid bks ->
      ⟦ bks ⟧bs vararg (from, to) ≈
             'x <- ⟦ bks' ⟧bs vararg (from, to);;
      match x with
      | inl x => ⟦ bks ⟧bs vararg x
      | inr x => Ret (inr x)
      end
  .
  Proof using.
    intros * ->; revert from to.
    einit.
    ecofix CIH.
    clear CIHH.
    intros * WF.
    destruct (find_block bks' to) as [bk |] eqn:EQ.
    - unfold denote_ocfg at 1 3.
      setoid_rewrite KTreeFacts.unfold_iter_ktree.
      cbn; rewrite !bind_bind.
      assert (find_block (prefix ++ bks' ++ postfix) to = Some bk).
      {
        erewrite find_block_app_r_wf; eauto.
        erewrite find_block_app_l_wf; eauto.
        eapply wf_ocfg_bid_app_r; eauto.
      }
      do 2 match_rewrite.
      rewrite !bind_bind.
      eapply euttG_bind; econstructor; [reflexivity | intros [] ? <-].
      + rewrite !bind_ret_l; cbn.
        rewrite bind_tau; etau.
      + rewrite !bind_ret_l.
        reflexivity.
    - edrop.
      rewrite (denote_ocfg_unfold_not_in vararg bks'); auto.
      rewrite bind_ret_l.
      reflexivity.
  Qed.
  Transparent denote_block.
End DenotationTheory.

Module Make (IS : InterpreterStack) (TOP : LLVMTopLevel IS) : DenotationTheory IS TOP.
  Include DenotationTheory IS TOP.
End Make.

Module DenotationTheoryBigIntptr := Make InterpreterStackBigIntptr TopLevelBigIntptr.
Module DenotationTheory64BitIntptr := Make InterpreterStack64BitIntptr TopLevel64BitIntptr.
