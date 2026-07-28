From ITree Require Import
  ITree
  ITreeFacts
  Basics.HeterogeneousRelations HasPost.

From Vellvm Require Import
  Utils
  Syntax
  Semantics
  ScopeTheory
.
Open Scope list.
(* These two imports give priority to the concrete
   itree definitions and notations for bind/ret
 *)
Import Eqit.
Import ITreeNotations.
Import HasPostNotations.

(** * Structural equations at the representation level

We prove here the equational theory that holds independently of the
interpretation of events.
These equations are expressed in terms of [eutt eq] over uninterpreted trees.
They derive from the [itree] combinators used to compute the uninterpreted
representation VIR's syntax.

In particular, notice that since [interp] is a iterative-monad morphism that respects
[eutt eq], these equations get transported at all levels of interpretations.

 *)

Section withParams.

  Context {Pa: Params}.

  Import SemNotations.

  #[local] Hint Rewrite @bind_ret_l : rwexp.
  #[local] Hint Rewrite @bind_bind : rwexp.
  #[local] Hint Rewrite @translate_ret : rwexp.
  #[local] Hint Rewrite @translate_bind : rwexp.
  #[local] Hint Rewrite @translate_trigger : rwexp.
  #[local] Ltac go := autorewrite with rwexp.
  #[local] Tactic Notation "go!" := repeat go.
  #[local] Ltac solve := go; easy.
  #[local] Ltac eqbind :=
    first [
        apply eutt_eq_bind; intros |
        eapply eq_itree_clo_bind with (UU := eq); [reflexivity | intros ? ? ->]
      ].
  
  (** [denote_code] *)

  Lemma denote_code_nil vararg :
    ⟦ [] ⟧c vararg ≅ Ret tt.
  Proof with solve.
    cbn...
  Qed.

  Lemma denote_code_app :
    forall vararg a b,
      ⟦ a ++ b ⟧c vararg ≅ ⟦ a ⟧c vararg;; ⟦ b ⟧c vararg.
  Proof with solve.
    intros vararg.
    induction a as [| i a IH]; intros b.
    - cbn...
    - cbn; go.
      eqbind.
      unfold denote_code in IH; rewrite IH...
  Qed.

  Lemma denote_code_cons :
    forall vararg i c,
      ⟦ i :: c ⟧c vararg ≅ ⟦ i ⟧i vararg;; ⟦ c ⟧c vararg.
  Proof with solve.
    intros...
  Qed.

  Lemma denote_code_singleton :
    forall vararg i,
      ⟦ [i] ⟧c vararg ≅ ⟦ i ⟧i vararg.
  Proof with solve.
    intros vararg a.
    cbn; go.
    bind_ret_r2.
    eqbind.
    destruct u2; reflexivity.
  Qed.

  (** [denote_phi] *)
  (* TODO: make a choice about it and move *)
  Arguments assoc : simpl never.
  Lemma denote_phi_hd : forall bid e id τ tl,
      ⟦ (id, Phi τ ((bid,e)::tl), []) ⟧Φ bid
     ≈ uv <- ⟦ e at τ ⟧e';; Ret (id,uv).
  Proof with solve.
    intros; cbn.
    rewrite assoc_hd...
  Qed.

  Lemma denote_phi_tl : forall bid bid' e id τ tl,
      bid <> bid' ->
      ⟦ (id, Phi τ ((bid',e)::tl), []) ⟧Φ bid ≈ ⟦ (id, Phi τ tl, []) ⟧Φ bid.
  Proof with solve.
    intros; cbn.
    rewrite assoc_tl...
  Qed.

  Lemma denote_no_phis : forall x,
      ⟦ [] ⟧Φs x ≈ Ret tt.
  Proof with solve.
    intros.
    cbn; go.
    cbn; go...
  Qed.

  (** [denote_block] *)
  Lemma denote_block_unfold_cont :
    forall {R} vararg id phis c t s origin (k : _ -> itree _ R),
      ⟦ mk_block id phis c t s ⟧b origin vararg >>= k
        ≈
      ⟦ phis ⟧Φs origin;; ⟦ c ⟧c vararg ;; ⟦ t ⟧t >>= k.
  Proof with solve.
    intros; cbn; repeat setoid_rewrite bind_bind...
  Qed.

  Lemma denote_block_unfold :
    forall vararg id phis c t s origin,
      ⟦ mk_block id phis c t s ⟧b origin vararg
        ≈
      ⟦ phis ⟧Φs origin;; ⟦ c ⟧c vararg;; ⟦ t ⟧t.
  Proof with solve.
    intros...
  Qed.

  (** [denote_ocfg] *)
  Lemma denote_ocfg_nil :
    forall vararg s,
      ⟦ [] ⟧bs vararg s
        ≈
      Ret (inl s).
  Proof with solve.
    intros vararg []; unfold denote_ocfg, denote_ocfg_map.
    rewrite unfold_iter; cbn...
  Qed.

  Lemma denote_ocfg_unfold_in: forall vararg bks bid_from bid_src bk,
      find_block bks bid_src = Some bk ->
      ⟦ bks ⟧bs vararg (bid_from, bid_src)
        ≈
      vob <- ⟦ bk ⟧b bid_from vararg ;;
      match vob with
      | inr v => Ret (inr v)
      | inl bid_target => ⟦ bks ⟧bs vararg (bid_src, bid_target)
      end.
  Proof with solve.
    intros * GET_BK; cbn.
    unfold denote_ocfg, denote_ocfg_map at 1.
    rewrite unfold_iter; cbn.
    rewrite ocfg_map_find_block,GET_BK.
    go!.
    (* For some reason the rewrite in the right handside fails
       with vanilla rewrite *)
    repeat setoid_rewrite bind_bind.
    repeat eqbind.
    break_sum; go; [rewrite tau_eutt |]...
  Qed.

  Lemma denote_ocfg_unfold_not_in: forall vararg bks bid_from bid_src,
      find_block bks bid_src = None ->
      ⟦ bks ⟧bs vararg (bid_from, bid_src) ≈ Ret (inl (bid_from,bid_src)).
  Proof with solve.
    intros * GET_BK.
    unfold denote_ocfg, denote_ocfg_map.
    rewrite unfold_iter; cbn.
    rewrite ocfg_map_find_block,GET_BK; go...
  Qed.

  Lemma denote_ocfg_unfold_in_euttge: forall vararg bks bid_from bid_src bk,
      find_block bks bid_src = Some bk ->
      ⟦ bks ⟧bs vararg (bid_from, bid_src) ≳
             vob <- ⟦ bk ⟧b bid_from vararg ;;
      match vob with
      | inr v => Ret (inr v)
      | inl bid_target => ⟦ bks ⟧bs vararg (bid_src, bid_target)
      end.
  Proof with solve.
    intros * GET_BK.
    unfold denote_ocfg, denote_ocfg_map.
    rewrite unfold_iter; cbn.
    rewrite ocfg_map_find_block,GET_BK; go.
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
  Proof with solve.
    intros * GET_BK.
    unfold denote_ocfg, denote_ocfg_map.
    rewrite unfold_iter; cbn.
    rewrite ocfg_map_find_block,GET_BK; go.
    repeat setoid_rewrite bind_bind.
    repeat eqbind.
    break_sum; go...
  Qed.

  Lemma denote_ocfg_unfold_not_in_eq_itree: forall vararg bks bid_from bid_src,
      find_block bks bid_src = None ->
      ⟦ bks ⟧bs vararg (bid_from, bid_src) ≅ Ret (inl (bid_from,bid_src)).
  Proof with solve.
    intros * GET_BK.
    unfold denote_ocfg, denote_ocfg_map.
    rewrite unfold_iter; cbn.
    rewrite ocfg_map_find_block,GET_BK; go...
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
  Proof with solve.
    intros *.
    break_match_goal.
    - rewrite denote_ocfg_unfold_in_eq_itree...
    - rewrite denote_ocfg_unfold_not_in_eq_itree...
  Qed.

  (* TODO : move *)
  Lemma has_post_trigger_cast {E : Type -> Type} (e : E void) A P :
    @trigger_cast' E A e ⤳ P.
  Proof.
    eapply has_post_bind_weak; intros [].
  Qed.

  Lemma has_post_ret {E R} (r : R) P :
    P r ->
    has_post (E := E) (ret r) P.
  Proof.
    intros; now apply eutt_Ret.
  Qed.
  
  Section Outputs.

    (** * outputs soundness *)
    
    Lemma raise_has_all_posts : forall {E X} `{FailureE -< E} s Q,
        @raise E X _ s ⤳ Q.
    Proof.
      intros; apply has_post_trigger_cast.
    Qed.

    Lemma raiseUB_has_all_posts : forall {E X} `{UBE -< E} s Q,
        @raiseUB E _ X s ⤳ Q.
    Proof.
      intros; apply has_post_trigger_cast.
    Qed.

    Lemma raiseOOM_has_all_posts : forall {E X} `{OOME -< E} s Q,
        @raiseOOM E _ X s ⤳ Q.
    Proof.
      intros; apply has_post_trigger_cast.
    Qed.

    Lemma raiseLLVM_has_all_posts `{Params} : forall {E X} `{LLVMExcE -< E} exc Q,
        @raiseLLVM _ E X _ exc ⤳ Q.
    Proof.
      intros; apply has_post_trigger_cast.
    Qed.

    #[local] Ltac bind := apply has_post_bind_weak; intros ?.
    #[local] Ltac ret := apply has_post_ret; auto.
    #[local] Ltac abs :=
      try (apply raise_has_all_posts ||
           apply raiseOOM_has_all_posts ||
           apply raiseUB_has_all_posts ||
           apply raiseLLVM_has_all_posts).
    #[local] Notation TT1 := (fun _ => True).
    #[local] Infix "⊕"  := (sum_pred) (at level 10). 
    #[local] Infix "⊗"  := (prod_pred) (at level 10). 
    
    (* A quite trivial invariant: terminators may only return
       target block ids which appeared syntactically in their
       code.
     *)
    Lemma denote_terminator_exits_in_outputs :
      forall term,
        ⟦ term ⟧t ⤳
          (fun id => In id (let '(_, t, _) := term in terminator_outputs t))
          ⊕ TT1.
    Proof.
      intros term.
      destruct term as [p ?].
      destruct p as [id term].
      destruct term eqn:Hterm; cbn; abs; try ret.
      - (* Ret *)
        break_match_goal.
        bind; ret.
      - (* Br *)
        break_match_goal.
        bind.
        repeat (break_match_goal; abs); ret.
      - (* Switch *)
        break_match_goal.
        bind.
        break_match_goal; abs.
        subst.
        apply has_post_bind with
          (S := fun id => id = default_dest \/ In id (List.map snd brs));
          [| intros ? [|]; ret].
        break_match_goal; abs.
        revert x0 Heqe0.
        induction brs as [| [[? ?] id1] args IH].
        + cbn; intros * EQ; inv EQ; ret.
        + cbn; intros.
          break_match_hyp; try easy.
          inv Heqe0.
          specialize (IH _ eq_refl).
          repeat (cbn; break_match_goal; subst; abs).
          ret.
          eapply has_post_weaken; [apply IH |].
          intros ? [|]; eauto. 
      - (* Resume *)
        break_match_goal.
        bind; abs.
      - (* Invoke *)
        break_match_goal.
        do 3 bind.
        break_match_goal.
        + bind; ret.
        + break_match_goal.
          bind; ret.
          bind; ret.
    Qed.

    Lemma denote_bk_exits_in_outputs :
      forall vararg b from,
        ⟦ b ⟧b from vararg ⤳ (fun id => In id (successors b)) ⊕ TT1.
    Proof.
      intros.
      cbn.
      bind.
      bind.
      apply denote_terminator_exits_in_outputs.
    Qed.

    (* Given a predicate [Qb] on pairs of block ids (the origin for phi-nodes and the input)
   and a predicate [Qv] on values, we establish that both hold after the denotation of an open_cfg if:
   - [Qb] holds at the initial entry point
   - [Qb] and [Qv] are preserved by the denotation of any blocks in the open cfg, assuming [Qb]
     *)
    Lemma denote_ocfg_has_post_strong :
      forall vararg (bks : ocfg _) fto (Qb : block_id * block_id -> Prop) (Qv : dvalue -> Prop)
        (INIT : Qb fto)
        (IND : forall fto (b : block dtyp),
            Qb fto ->
            find_block bks (snd fto) = Some b ->
            ⟦ b ⟧b (fst fto) vararg ⤳ sum_pred (fun to => Qb (snd fto, to)) Qv),
        ⟦ bks ⟧bs vararg fto ⤳ sum_pred Qb Qv.
    Proof.
      intros * INIT IND.
      eapply has_post_iter_strong; eauto.
      intros [f to] PRE.
      break_match_goal; [| ret].
      specialize (IND (f,to) b).
      eapply has_post_bind. apply IND; auto; rewrite <- ocfg_map_find_block; auto.
      intros [id | v]; cbn; intros ?; ret.
    Qed.

    (* A weaker but sometimes easier to use modular way to prove postconditions of open cfgs:
   - assuming that all blocks in the open cfg admits as postconditions [sum_pred Qb Qv]
   - and assuming that we indeed enter the [open_cfg]
   then we get [Qb/Qv], and ignore the origin of the jump.
     *)
    Lemma denote_ocfg_has_post :
      forall vararg (bks : ocfg _) fto (Qb : block_id -> Prop) (Qv : dvalue -> Prop)
        (ENTER : In (snd fto) (inputs bks))
        (IND : forall fto (b : block dtyp),
            find_block bks (snd fto) = Some b ->
            ⟦ b ⟧b (fst fto) vararg ⤳ sum_pred Qb Qv),
        ⟦ bks ⟧bs vararg fto ⤳ (TT1 ⊗ Qb) ⊕ Qv.
    Proof.
      intros * IN IND.
      apply has_post_iter_strong with (Inv := fun x => In (snd x) (inputs bks) \/ Qb (snd x))
      ; eauto.
      intros [f to] HYP.
      break_match_goal.
      - specialize (IND (f,to) b).
        eapply has_post_bind.
        apply IND; auto; rewrite <- ocfg_map_find_block; auto.
        intros [id | v]; cbn; intros ?; ret.
      - ret.
        split; auto.
        destruct HYP as [abs | POST]; auto.
        rewrite ocfg_map_find_block in Heqo.
        apply find_block_in_inputs in abs as [? abs].
        cbn in abs; rewrite abs in Heqo; inv Heqo.
    Qed.

    Definition exits_in_outputs {t} ocfg : block_id * block_id + dvalue -> Prop :=
      (fun fto => In (snd fto) (@outputs t ocfg)) ⊕ TT1.

    Lemma denote_ocfg_exits_in_outputs :
      forall vararg bks fto,
        In (snd fto) (inputs bks) ->
        ⟦ bks ⟧bs vararg fto ⤳ exits_in_outputs bks.
    Proof.
      intros * IN.
      apply has_post_weaken with (P := sum_pred (prod_pred TT1 (fun b => In b (outputs bks))) TT1).
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
  Proof.
    intros vararg bks1 bks2 [f to] FIND NOBACK.
    apply (@KTreeFacts.eutt_iter_gen _ _ _ (fun fto fto' => fto' = fto /\ find_block bks1 (snd fto) = None)); auto.
    clear f to FIND; intros fto fto' [-> FIND]; destruct fto as [f to] .
    cbn in *.
    epose proof (find_block_none_app _ bks2 _ FIND) as FIND_L1L2.
    rewrite 2 ocfg_map_find_block, FIND_L1L2.
    destruct (find_block bks2 to) eqn:FIND_L2.
    - eapply eutt_post_bind_eq.
      apply denote_bk_exits_in_outputs.
      intros [id | v] ?; cbn; apply eutt_Ret; eauto.
      eapply inl_morphism; split; auto.
      eapply find_block_not_in_inputs,no_reentrance_not_in; eauto.
      eapply In_bk_outputs; eauto.
    - apply eutt_Ret; right; auto.
  Qed.

  Arguments denote_block : simpl never.
  Lemma denote_ocfg_app :
    forall vararg bks1 bks2 fto,
      no_reentrance bks1 bks2 ->
      ⟦ bks1 ++ bks2 ⟧bs vararg fto
        ≈
        'x <- ⟦ bks1 ⟧bs vararg fto;;
      match x with
      | inl fto2 => ⟦ bks2 ⟧bs vararg fto2
      | inr v => Ret (inr v)
      end.
  Proof.
    intros * NOBACK.
    revert fto.
    einit.
    ecofix CIH.
    intros [f to].
    destruct (find_block bks1 to) eqn:FIND.
    - unfold denote_ocfg, denote_ocfg_map.
      setoid_rewrite unfold_iter.
      cbn. go.
      rewrite 2 ocfg_map_find_block, !FIND.
      go.
      pose proof find_block_some_app bks1 bks2 to FIND as FIND_APP.
      rewrite FIND_APP.
      cbn; go.
      ebind; econstructor; [reflexivity | intros ? ? <-].
      break_match_goal; [| go; estep].
      go.
      rewrite bind_tau.
      etau.
    - efinal.
      rewrite denote_ocfg_app_no_edges; auto.
      rewrite denote_ocfg_unfold_not_in with (bks := bks1); auto.
      rewrite bind_ret_l; reflexivity.
  Qed.

  Lemma denote_ocfg_flow_left :
    forall vararg ocfg1 ocfg2 fto,
      independent_flows ocfg1 ocfg2 ->
      In (snd fto) (inputs ocfg1) ->
      ⟦ ocfg1 ++ ocfg2 ⟧bs vararg fto
        ≈
      ⟦ ocfg1 ⟧bs vararg fto.
  Proof.
    intros * INDEP IN.
    rewrite denote_ocfg_app; [| auto using independent_flows_no_reentrance_l].
    bind_ret_r2.
    eapply eutt_post_bind_eq; [apply denote_ocfg_exits_in_outputs; eauto |].
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
      ⟦ ocfg1 ++ ocfg2 ⟧bs vararg fto
        ≈
      ⟦ ocfg2 ⟧bs vararg fto.
  Proof.
    intros * INDEP IN.
    rewrite denote_ocfg_app; [| auto using independent_flows_no_reentrance_l].
    destruct fto as [f to]; cbn in *.
    rewrite denote_ocfg_unfold_not_in.
    rewrite bind_ret_l; reflexivity.
    eapply find_block_not_in_inputs, no_duplicate_bid_not_in_l; eauto using independent_flows_no_duplicate_bid.
  Qed.

  Lemma denote_ocfg_prefix :
    forall vararg (prefix bks' postfix bks : ocfg dtyp) (from to: block_id),
      bks = (prefix ++ bks' ++ postfix) ->
      wf_ocfg_bid bks ->
      ⟦ bks ⟧bs vararg (from, to)
        ≈
      'x <- ⟦ bks' ⟧bs vararg (from, to);;
      match x with
      | inl x => ⟦ bks ⟧bs vararg x
      | inr x => Ret (inr x)
      end
  .
  Proof.
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
      rewrite 2 ocfg_map_find_block.
      do 2 match_rewrite.
      go.
      ebind; econstructor; [reflexivity | intros [] ? <-].
      + go.
        rewrite bind_tau; etau.
      + go; reflexivity.
    - edrop.
      rewrite (denote_ocfg_unfold_not_in vararg bks'); auto.
      rewrite bind_ret_l.
      reflexivity.
  Qed.

End withParams.
