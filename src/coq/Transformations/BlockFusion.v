(* begin hide *)
From Coq Require Import
     Lia
     String
     Morphisms.

Require Import Paco.paco.

Require Import List.
Import ListNotations.
Require Import ZArith.

From ITree Require Import
     ITree
     Basics.Monad
     Eq.Eqit
     InterpFacts
     TranslateFacts.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics
     Theory
     Utils.PostConditions.

Opaque append.
Import ListSet.

#[export] Remove Hints Eqv.EqvWF_Build : typeclass_instances.

Set Implicit Arguments.
Set Strict Implicit.

Import ListNotations.
Open Scope bool.
Import SemNotations.
(* end hide *)

(** * BlockFusion
  Definition and proof of correctness of a simple optimization pass fusing
  two blocks [b1] and [b2] together when [b1] performs a direct jump to
  [b2], and [b1] is the only entry point to [b2].
*)

Section RemoveBlock.

  Fixpoint remove_block {T} (G : ocfg T) (b : block_id) : ocfg T :=
    match G with
    | [] => []
    | bk :: G => if Eqv.eqv_dec b bk.(blk_id) then G else bk:: remove_block G b
    end.

  Infix "∖" := remove_block (right associativity, at level 60).

  Lemma remove_block_find_block_eq : forall {T} b (G : ocfg T),
      wf_ocfg_bid G ->
      find_block (G ∖ b) b = None.
  Proof.
    induction G as [| bk G IH].
    reflexivity.
    intros WF.
    simpl remove_block.
    break_match_goal.
    break_match_hyp; intuition.
    subst.
    eapply wf_ocfg_cons_not_in_tail; eauto.
    cbn.
    break_match_goal.
    break_match_hyp; intuition.
    break_match_hyp; intuition.
    apply IH.
    eapply wf_ocfg_bid_cons; eauto.
  Qed.

  Lemma remove_block_find_block_ineq : forall {T} b b' (G : ocfg T),
      b <> b' ->
      find_block (G ∖ b) b' = find_block G b'. 
  Proof.
    induction G as [| bk G IH].
    reflexivity.
    intros INEQ.
    simpl remove_block.
    break_match_goal.
    break_match_hyp; intuition.
    subst; rewrite find_block_ineq; auto.
    break_match_hyp; intuition.
    cbn; break_match_goal; auto.
  Qed.

  Lemma remove_block_remove_inputs:
    forall {T} (G : ocfg T) b b',
      In b' (inputs (G ∖ b)) ->
      In b' (inputs G).
  Proof.
    induction G as [| bk G IH]; intros * IN; [inv IN |].
    cbn in IN.
    break_match_hyp.
    - right; auto. 
    - destruct IN as [EQ | IN].
      subst; left; reflexivity.
      right; eapply IH; eauto.
  Qed.

  Lemma wf_ocfg_bid_remove_block :
    forall {T} (G : ocfg T) b,
      wf_ocfg_bid G ->
      wf_ocfg_bid (G ∖ b).
  Proof.
    intros *; induction G as [| bk G IH]; intro WF; auto.
    cbn.
    break_match_goal.
    eapply wf_ocfg_bid_cons; eauto.
    apply wf_ocfg_bid_cons'.
    2: eapply IH,wf_ocfg_bid_cons; eauto.
    inv WF.
    intros IN; apply remove_block_remove_inputs in IN; auto.
  Qed.

  Lemma map_remove_block : forall {T} (f : block T -> block T) (G : ocfg T) b,
      (forall bk, blk_id (f bk) = blk_id bk) ->
      map f (G ∖ b) = (map f G) ∖ b.
  Proof.
    induction G as [| bk G IH]; intros * ID; [reflexivity |].
    cbn.
    break_match_goal.
    break_match_goal; auto.
    rewrite ID in Heqb1.
    rewrite Heqb0 in Heqb1; inv Heqb1.
    break_match_goal; auto.
    rewrite ID in Heqb1.
    rewrite Heqb0 in Heqb1; inv Heqb1.
    cbn.
    rewrite IH; auto.
  Qed.

End RemoveBlock.

Infix "∖" := remove_block (right associativity, at level 60).

Section BlockFusion.

  (* If a block has a unique predecessor, its phi-nodes can be trivially converted to straight code.
     Wrote it a bit carelessly as total right now. Assumes that it is only called on a block having
     indeed a single predecessor, among a well formed graph: we therefore should always have when
     called that all lists under a [Phi] constructor are exactly singletons.
     Actually trickier: by doing this conversion, we are linearizing a set of assignments that were
     computed in parallel. It is sound because with a unique predecessor it shouldn't be possible to
     have a recursive dependency in your phi-nodes, but it might be tricky to argue/capture formally.
     To keep an eye on it.
   *)
  Definition phi_to_code {T} (Φs : list (local_id * phi T)) : code T :=
    fold_left (fun acc '(id, Phi τ l) =>
                 match l with
                 | [(_,e)] => acc ++ [(IId id, INSTR_Op e)] (* Keeping the order should not matter, but if we can spare the argument later... *)
                 | _ => (* This is a failure case, it should not happen if called in the expected context *)
                   acc
                 end) Φs [].

  Definition block_fusions (b_s b_t : block dtyp) : block dtyp :=
    {|
    blk_id         := b_s.(blk_id);
    blk_phis       := b_s.(blk_phis);
    blk_code       := b_s.(blk_code) ++ b_t.(blk_code);
    blk_term       := b_t.(blk_term);
    blk_comments   := None (* TODO: proper propagation of comments *)
    |}.

  Definition has_no_phi (b : block dtyp) : bool := match b.(blk_phis) with | [] => true | _ => false end.

  Definition update_provenance (old new id : block_id) : block_id :=
    if Eqv.eqv_dec old id then new else id.

  Definition update_provenance_phi {T} (old new : block_id) (φ : phi T) : phi T :=
    match φ with
    | Phi τ exps => Phi τ (map (fun '(id,e) => (update_provenance old new id, e)) exps)
    end.

  Definition update_provenance_block {T} (old new : block_id) (bk : block T) : block T :=
    {|
    blk_id         := bk.(blk_id);
    blk_phis       := map (fun '(x,φ) => (x,update_provenance_phi old new φ)) bk.(blk_phis);
    blk_code       := bk.(blk_code);
    blk_term       := bk.(blk_term);
    blk_comments   := None (* TODO: proper propagation of comments *)
    |}.   

  Definition update_provenance_ocfg {T} (old new : block_id) (bks : ocfg T) : ocfg T :=
    map (update_provenance_block old new) bks.

  (* Let's start gently: we perform at most one fusion.
     To perform all available fusions we'll need notably to be a bit more clever
     w.r.t. to termination.
   *)
  Fixpoint block_fusion_rec (G : ocfg dtyp) (bks : ocfg dtyp) : ocfg dtyp * option (block_id * block_id) :=
    (* We scan the blocks in sequence until... *)
    match bks with
    | [] => (G,None)
    | bk_s :: bks =>
      match bk_s.(blk_term) with
      | TERM_Br_1 b_t =>
        (* ... We find a block [bk_s] with a direct jump to some [b_t]. *)
        match find_block G b_t with
        (* If this direct jump is internal to the [ocfg] considered... *)
        | Some bk_t =>
          (* And if
           - It is not a degenerate self-referential direct loop
           - [bk_s] is the only predecessor of [b_t]
           - [b_t] has no phi-node
           *)
          if Eqv.neg_eqv_dec b_t bk_s.(blk_id) &&
             (length (predecessors b_t G) =? 1)%nat &&
             has_no_phi bk_t
          then
            (* We therefore:
               - remove the two block [bk_s] and [bk_t] getting fused
               - add their fusion
               - update the phi-nodes so that anyone expecting a jump from [bk_t]
               now expects one from [bk_s] 
             *)
            (update_provenance_ocfg
               b_t bk_s.(blk_id) ((block_fusions bk_s bk_t) :: ((G ∖ bk_s.(blk_id)) ∖ b_t)),
             Some (bk_s.(blk_id),b_t))
          else block_fusion_rec G bks
        | None => block_fusion_rec G bks
        end
      | _ => block_fusion_rec G bks
      end
    end.

  Definition block_fusion : ocfg dtyp -> ocfg dtyp * option (block_id * block_id) :=
    fun G => block_fusion_rec G G.

  (* The restriction [src <> G.(init)] is artificial due to a slight lazyness in the current semantics:
     the semantics of a [cfg] starts the denotation of its graph pretending to come from its initial block.
     We should reserve instead an unused dummy label, or have sources be options.
   *)
  Definition block_fusion_cfg (G : cfg dtyp) : cfg dtyp :=
    match block_fusion G.(blks) with
    | (_, None) => G
    | (bks', Some (src,tgt)) =>
      if Eqv.eqv_dec src G.(init) || Eqv.eqv_dec tgt G.(init)
      then G
      else {|
          init := G.(init);
          blks := bks';
          args := G.(args)
        |}
    end.

End BlockFusion.

Section BlockFusionCorrect.

  Lemma block_fusion_some_rec:
    forall G bks' bks pre f1 f2,
      wf_ocfg_bid G ->
      G = pre ++ bks ->
      block_fusion_rec G bks = (bks', Some (f1,f2)) ->
      f1 <> f2 /\
      exists b1 b2,
        find_block G f1 = Some b1 /\
        blk_term b1 = TERM_Br_1 f2 /\
        find_block G f2 = Some b2 /\
        (forall b, find_block G b.(blk_id) = Some b -> In f2 (successors b) -> b.(blk_id) = f1) /\
        has_no_phi b2 = true /\
        find_block bks' f1 = Some (update_provenance_block f2 f1 (block_fusions b1 b2)) /\
        find_block bks' f2 = None /\
        (forall f bk, f <> f1 -> f <> f2 -> find_block G f = Some bk -> find_block bks' f = Some (update_provenance_block f2 f1 bk)) /\
        (forall f, f <> f1 -> f <> f2 -> find_block G f = None -> find_block bks' f = None).
  Proof.
    intros * WF; revert pre.
    induction bks as [| bk bks IH]; intros * -> GETF; [inv GETF |].
    cbn in GETF.
    break_match_hyp; try (destruct (IH (pre ++ [bk])) as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?); eauto using app_snoc_app; fail).
    break_match_hyp; try (destruct (IH (pre ++ [bk])) as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?); eauto using app_snoc_app; fail).
    break_match_hyp; try (destruct (IH (pre ++ [bk])) as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?); eauto using app_snoc_app; fail).
    clear IH.
    inv GETF.
    apply andb_prop in Heqb0 as [Heqb NOPHI].
    apply andb_prop in Heqb as [INEQ SINGLEPRED].
    split.

    - intros <-.
      unfold Eqv.neg_eqv_dec in *.
      rewrite RelDec.rel_dec_eq_true in INEQ; [inv INEQ | |].
      typeclasses eauto.
      reflexivity.

    - exists bk, b.
      repeat split.

      + apply find_block_app_r_wf; auto.
        apply find_block_eq; auto.

      + auto.

      + auto.

      + intros * LU IN.
        rewrite predecessors_app,predecessors_cons in SINGLEPRED.
        rename bk into bk1, b into bk2, b0 into bk.
        assert (EQ1: predecessors f2 [bk1] = [bk1.(blk_id)]).
        {
          cbn.
          unfold is_predecessor, successors. 
          rewrite Heqt; cbn.
          break_match_goal; intuition.
          break_match_hyp; intuition.
        }          
        rewrite !app_length, EQ1 in SINGLEPRED.
        cbn in SINGLEPRED.
        assert (EQ2: predecessors f2 bks = []).
        { destruct (predecessors f2 bks ); auto.
          cbn in SINGLEPRED.
          symmetry in SINGLEPRED; apply beq_nat_eq in SINGLEPRED.
          lia.
        }
        assert (EQ3: predecessors f2 pre = []).
        { destruct (predecessors f2 pre); auto.
          cbn in SINGLEPRED.
          symmetry in SINGLEPRED; apply beq_nat_eq in SINGLEPRED.
          lia.
        }
        apply successor_predecessor with (G := pre ++ bk1 :: bks) in IN; auto.
        rewrite predecessors_app,EQ3, app_nil_r in IN.
        rewrite predecessors_cons, EQ2, app_nil_l in IN.
        rewrite EQ1 in IN.
        inv IN; intuition.

      + auto.

      + cbn.
        break_match_goal; auto.
        break_match_hyp; intuition.

      + rename bk into src, b into tgt.
        cbn.
        unfold Eqv.neg_eqv_dec in INEQ.
        break_match_goal.
        { break_match_hyp; intuition.
          do 2 red in e; subst.
          apply Bool.negb_true_iff in INEQ.
          apply RelDec.neg_rel_dec_correct in INEQ.
          exfalso; apply INEQ; do 2 red; reflexivity.
        }

        rewrite map_remove_block; auto.
        apply remove_block_find_block_eq.          
        apply wf_ocfg_map; auto.
        apply wf_ocfg_bid_remove_block; auto.

      + intros f bk' INEQ1 INEQ2 FIND.
        cbn.
        break_match_goal.
        * break_match_hyp; intuition.
        * break_match_hyp; intuition.
          match goal with
            |- ?x = _ => replace x with (find_block (map (update_provenance_block f2 (blk_id bk)) (((pre ++ bk :: bks) ∖ blk_id bk) ∖ f2)) f) by reflexivity
          end.
          rewrite map_remove_block; auto.
          rewrite remove_block_find_block_ineq; auto.
          rewrite map_remove_block; auto.
          rewrite remove_block_find_block_ineq; auto.
          apply find_block_map_some; auto.

      + intros f INEQ1 INEQ2 FIND.
        cbn.
        break_match_goal.
        * break_match_hyp; intuition.
        * break_match_hyp; intuition.
          match goal with
            |- ?x = _ => replace x with (find_block (map (update_provenance_block f2 (blk_id bk)) (((pre ++ bk :: bks) ∖ blk_id bk) ∖ f2)) f) by reflexivity
          end.
          rewrite map_remove_block; auto.
          rewrite remove_block_find_block_ineq; auto.
          rewrite map_remove_block; auto.
          rewrite remove_block_find_block_ineq; auto.
          apply find_block_map_none; auto.

  Qed.

  Lemma block_fusion_some:
    forall G G' f1 f2,
      wf_ocfg_bid G ->
      block_fusion G = (G', Some (f1,f2)) ->

      f1 <> f2 /\
      exists b1 b2,
        find_block G f1 = Some b1 /\
        blk_term b1 = TERM_Br_1 f2 /\
        find_block G f2 = Some b2 /\
        (forall b, find_block G b.(blk_id) = Some b -> In f2 (successors b) -> b.(blk_id) = f1) /\
        has_no_phi b2 = true /\
        find_block G' f1 = Some (update_provenance_block f2 f1 (block_fusions b1 b2)) /\
        find_block G' f2 = None /\
        (forall f bk, f <> f1 -> f <> f2 -> find_block G f = Some bk -> find_block G' f = Some (update_provenance_block f2 f1 bk)) /\
        (forall f, f <> f1 -> f <> f2 -> find_block G f = None -> find_block G' f = None).
  Proof.
    intros * WF FUSE.
    pose proof block_fusion_some_rec G [] WF eq_refl FUSE.
    apply H.
  Qed.

  Lemma block_fusion_none_id_rec :
    forall G G' bks pre,
      G = pre ++ bks ->
      block_fusion_rec G bks = (G',None) ->	
      G' = G.
  Proof.
    induction bks as [| bk bks IH]; intros * -> FUSE.
    - cbn in FUSE; rewrite app_nil_r in FUSE |- *; inv FUSE; reflexivity.
    - cbn in *.
      break_match_hyp; auto; try (apply IH with (pre ++ [bk]) in FUSE; eauto using app_snoc_app; fail).
      break_match_hyp; auto; try (apply IH with (pre ++ [bk]) in FUSE; eauto using app_snoc_app; fail).
      break_match_hyp; auto; try (apply IH with (pre ++ [bk]) in FUSE; eauto using app_snoc_app; fail).
      inv FUSE.
  Qed.

  Lemma block_fusion_none_id :
    forall G G',
      block_fusion G = (G', None) ->	
      G' = G.
  Proof.
    intros; eapply block_fusion_none_id_rec with (pre := []); eauto; reflexivity. 
  Qed.

  Lemma update_provenance_find_block :
    forall {T} (G : ocfg T) old new to,
      find_block (update_provenance_ocfg old new G) to = option_map (update_provenance_block old new) (find_block G to).
  Proof.
    intros.
    apply find_block_map; auto.
  Qed.

  Lemma map_monad_eq_itree_map_ind :
    forall {E A B} (f g : A -> itree E B) (h : A -> A) (l : list A),
      (forall a, In a l -> f a ≅ g (h a)) ->
      map_monad f l ≅ map_monad g (map h l).
  Proof.
    induction l as [| x l IH]; intros EQ; [reflexivity | cbn].
    apply eq_itree_clo_bind with (UU := eq).
    apply EQ; left; auto.
    intros ? ? <-.
    rewrite IH.
    reflexivity.
    intros; apply EQ; right; auto.
  Qed.

  Lemma update_provenance_eq : forall old new,
      update_provenance old new old = new.
  Proof.
    intros.
    unfold update_provenance.
    break_match_goal; auto.
    unfold Eqv.eqv_dec,RelDec.rel_dec in Heqb; cbn in *; break_match_hyp; intuition.
  Qed.

  Lemma update_provenance_ineq : forall old new to,
      to <> old ->
      update_provenance old new to = to.
  Proof.
    intros.
    unfold update_provenance.
    break_match_goal; auto.
    unfold Eqv.eqv_dec,RelDec.rel_dec in Heqb; cbn in *; break_match_hyp; intuition.
  Qed.
  
  Lemma assoc_update_provenance :
    forall old new (args : list (block_id * exp dtyp)) x,
      ~ In new (map fst args) ->
      x <> new ->
      assoc x args = assoc (update_provenance old new x) (map (fun '(id, e) => (update_provenance old new id, e)) args).
  Proof.
    induction args as [| [x1 ?] args IH]; [reflexivity |].
    intros x NIN INEQx.
    destruct (Eqv.eqv_dec_p x1 old) as [EQ | INEQ].
    - (* x1 = old *)
      do 2 red in EQ.
      cbn.
      subst.
      rewrite update_provenance_eq.
      destruct (Eqv.eqv_dec_p x old) as [EQ' | INEQ'].
      + (* x1 = old /\ x = old *)
        do 2 red in EQ'.
        subst.
        rewrite update_provenance_eq.
        cbn.
        rewrite !eq_dec_eq.
        reflexivity.
      + (* x1 = old /\ x <> old *)
        rewrite update_provenance_ineq; auto.
        unfold Eqv.eqv, eqv_raw_id in INEQ'.
        rewrite RelDec.rel_dec_neq_false; auto; [| typeclasses eauto].
        rewrite RelDec.rel_dec_neq_false; auto; [| typeclasses eauto].
        rewrite IH; auto.
        rewrite update_provenance_ineq; auto.
        intros abs; apply NIN; right; auto.
    - (* x1 <> old *)
      unfold Eqv.eqv, eqv_raw_id in INEQ.
      destruct (Eqv.eqv_dec_p x old) as [EQ' | INEQ'].
      + (* x1 <> old /\ x = old *)
        do 2 red in EQ'.
        subst.
        rewrite update_provenance_eq.
        cbn.
        rewrite RelDec.rel_dec_neq_false; auto; [| typeclasses eauto].
        rewrite update_provenance_ineq; auto.
        cbn in *.
        rewrite RelDec.rel_dec_neq_false; auto; [| typeclasses eauto].
        rewrite IH; auto.
        rewrite update_provenance_eq; auto.
      + (* x1 <> old /\ x <> old *)
        rewrite update_provenance_ineq; auto.
        unfold Eqv.eqv, eqv_raw_id in INEQ'.
        cbn.
        rewrite update_provenance_ineq; auto.
        break_match_goal; auto.
        rewrite IH; auto.
        rewrite update_provenance_ineq; auto.
        intros ?; apply NIN; cbn; auto.
  Qed.

  Definition phis_block_id_not_in {T} b (φs : list (local_id * phi T)) :=
    forall φ, In φ φs -> ~ In b (phi_sources (snd φ)).

  Definition block_phis_block_id_not_in {T} b (bk : block T) :=
    phis_block_id_not_in b bk.(blk_phis).   

  Lemma update_provenance_phis_eq_itree :
    forall phis old new f,
      f <> new ->
      phis_block_id_not_in new phis ->
      ⟦ phis ⟧Φs f ≅ ⟦ map (fun '(x, φ) => (x, update_provenance_phi old new φ)) phis ⟧Φs (update_provenance old new f).
  Proof.
    intros * INEQ PHIN.
    unfold denote_phis.
    cbn.
    apply eq_itree_clo_bind with (UU := eq).
    apply map_monad_eq_itree_map_ind.
    - intros [? []] IN.
      cbn.
      apply PHIN in IN; cbn in IN.
      rewrite <- assoc_update_provenance; auto.
      reflexivity.
    - intros ? ? <-.
      reflexivity.
  Qed.

  Arguments denote_phis : simpl never.
  Lemma update_provenance_block_eq_itree :
    forall bk old new f,
      f <> new ->
      block_phis_block_id_not_in new bk ->
      ⟦ bk ⟧b f ≅ ⟦ update_provenance_block old new bk ⟧b (update_provenance old new f).
  Proof.
    intros.
    unfold denote_block.
    cbn.
    rewrite <- update_provenance_phis_eq_itree; auto.
    reflexivity.
  Qed.

  Definition ocfg_phis_not_id b (G : ocfg dtyp) :=
    forall bk, In bk G ->
          block_phis_block_id_not_in b bk.

  Lemma phis_not_id_ocfg_to_bk : forall b G b' bk,
      find_block G b' = Some bk ->
      ocfg_phis_not_id b G ->
      block_phis_block_id_not_in b bk.
  Proof.
    intros * FIND WF.
    apply find_block_In' in FIND.
    apply WF; auto.
  Qed.

  Lemma block_fusion_correct_some :
    forall G G' f to b1 b2,
      wf_ocfg_bid G ->                       (* All label ids in G are unique *)
      ocfg_phis_not_id b1 G ->               (* No phi node should refer to b1 since it won't jump anywhere but b2 *)
      block_fusion G = (G', Some (b1,b2)) -> (* Two blocks are indeed fused *)
      to <> b2 ->                             (* I don't start the execution in the middle of the fused block *)
      f <>  b1 ->                             (* and hence cannot come from the upper part of the fused block *)
      eutt (fun res1 res2 =>
              match res1, res2 with
              | inl (f1,to1), inl (f2,to2) => f2 = update_provenance b2 b1 f1 /\ to1 = to2
              | inr v1, inr v2 => v1 = v2
              | _, _ => False
              end
           )
           (⟦ G ⟧bs (f,to))
           (⟦ G' ⟧bs (update_provenance b2 b1 f,to)).
  Proof.
    intros * WF PHIS FUSED; revert f to.
    apply block_fusion_some in FUSED; auto; destruct FUSED as (INEQ & bk1 & bk2 & LU1 & TERM & LU2 & PRED & NOPHI & LU3 & LU4 & LU5).
    einit.
    ecofix CIH.
    intros * INEQ' INEQ''.

    (* Two cases: are we starting the evaluation from the block b1 being fused with b2? *)
    destruct (Eqv.eqv_dec_p to b1).
    - (* Yes we are: b1 = to *)
      (* We will match the evaluation of b1 followed by b2 against the fused block *)
      do 2 red in e; subst b1.
      rewrite 2 denote_ocfg_unfold_in_eq_itree; eauto.
      unfold block_fusions.
      cbn.
      rewrite !bind_bind.
      Opaque denote_phis.
      setoid_rewrite denote_code_app_eq_itree.
      repeat setoid_rewrite bind_bind.
      (* Match the phis *)
      ebind; econstructor.
      { rewrite <- update_provenance_phis_eq_itree; auto.
        reflexivity.
        eapply phis_not_id_ocfg_to_bk; eauto.
      }
      intros ? ? <-.
      (* Match the code from b1 *)
      ebind; econstructor; [reflexivity | intros ? ? <-].
      repeat setoid_rewrite bind_ret_l.
      (* Constant jump on the left *)
      rewrite TERM.
      cbn; rewrite translate_ret, !bind_ret_l.
      (* We dismiss the extra tau guard on the left, we'll use the symmetric pair after b2 *)
      rewrite tau_euttge.
      rewrite denote_ocfg_unfold_in_eq_itree; eauto.
      unfold denote_block.
      (* No phis in b2 *)
      unfold has_no_phi in *.
      destruct (blk_phis bk2) eqn:NOPHI'; [clear NOPHI| inversion NOPHI].
      Transparent denote_phis.
      unfold denote_phis; cbn; rewrite bind_ret_l, !bind_bind.
      cbn; rewrite !bind_ret_l, !bind_bind; cbn.
      (* Match the code from b2 *)
      ebind; econstructor; [reflexivity | intros ? ? <-].
      rewrite bind_ret_l.
      (* Match the final jump. We'll need to justify that the destination is not b2:
         to do that, we pull out the fact that it has to be in the outputs of the terminator.
       *)
      pose proof denote_terminator_exits_in_outputs (blk_term bk2) as EXIT;
        apply has_post_post_strong in EXIT.
      ebind; econstructor; [apply eutt_translate_gen, EXIT | clear EXIT; intros ? ? [<- EXIT]].
      (* We either jump or return. In the latter case, it's trivial *)
      destruct u3 as [next | ?]; [| eret].
      (* Here is the guard for our coinductive call *)
      etau.
      ebase; right.
      specialize (CIHL b2 next).
      rewrite update_provenance_eq in CIHL.
      apply CIHL; auto.
      (* Remains to prove we did not jump in the middle of the fused block *)
      cbn in *.
      destruct (Eqv.eqv_dec_p next b2); auto.
      do 2 red in e; subst b2.
      pose proof find_block_has_id _ _ LU2; subst.
      apply PRED in EXIT; auto.
      
    - (* For any other block, we simply match the denotation of the blocks one against another *)
      rewrite 2 denote_ocfg_unfold_eq_itree.

      Opaque denote_phis.
      Opaque denote_block.
      destruct LU5 as [H H'].
      assert (forall f, f <> b1 -> f <> b2 -> find_block G' f = option_map (update_provenance_block b2 b1) (find_block G f)).
      {
        intros.
        destruct (find_block G f0) eqn:EQ.
        - apply H in EQ; auto. 
        - apply H' in EQ; auto. 
      }
      clear H H'.
      rewrite H0; auto.
      break_match_goal; cbn.
      +
        pose proof denote_bk_exits_in_outputs b f as EXIT;
          apply has_post_post_strong in EXIT.
        ebind; econstructor; [| clear EXIT].
        { rewrite <- update_provenance_block_eq_itree; auto.
          apply EXIT.
          eapply phis_not_id_ocfg_to_bk; eauto.
        }
        intros ? ? [<- EXIT].
        destruct u1 as [b_next | ?]; [| eret].
        etau.
        ebase.
        right.
        specialize (CIHL to b_next).
        rewrite update_provenance_ineq in CIHL; auto.
        apply CIHL; auto.
        cbn in EXIT.
        destruct (Eqv.eqv_dec_p b_next b2); auto.
        do 2 red in e; subst.
        pose proof find_block_has_id _ _ LU1; subst.
        pose proof find_block_has_id _ _ Heqo; subst.
        apply PRED in EXIT; subst; auto.

      + eret.
  Qed.

  Lemma block_fusion_correct_none :
    forall G G' f to, 
      block_fusion G = (G',None) ->
      ⟦ G ⟧bs (f,to) ≈ ⟦ G' ⟧bs (f,to).
  Proof.
    intros * FUSE.
    pose proof block_fusion_none_id G FUSE; subst.
    reflexivity.
  Qed.

   (* If the closed graph is well formed, and the fusion indeed fuses [src] with [tgt],
   then [src] cannot appear in any phi node *)
  Lemma wf_cfg_src_not_in_phis: forall G bks' src tgt,
      wf_cfg G ->
      block_fusion (blks G) = (bks', Some (src, tgt)) ->
      ocfg_phis_not_id src (blks G).
  Proof.
    intros * [WF1 WF2] FUSE.
    intros bk IN [x phi] IN'.
    rewrite (WF2 _ src _ _ IN IN').
    apply block_fusion_some in FUSE; auto.
    destruct FUSE as (INEQ & bk1 & bk2 & LU1 & TERM & LU2 & PRED & NOPHI & LU3 & LU4 & LU5).
    intros ABS.
    eapply predecessor_successor in ABS; eauto. 
    unfold successors in ABS; rewrite TERM in ABS; destruct ABS as [EQ | []].
    subst tgt.
    rewrite wf_ocfg_bid_In_is_found in LU2; auto; inv LU2.
    unfold has_no_phi in NOPHI.
    break_match_hyp; intuition.
  Qed.

  Arguments denote_block : simpl never.
  Arguments append : simpl never.

  Theorem block_fusion_cfg_correct :
    forall (G : cfg dtyp),
      wf_cfg G ->
      ⟦ G ⟧cfg ≈ ⟦ block_fusion_cfg G ⟧cfg.
  Proof.
    intros G [WF1 WF2].
    unfold denote_cfg.
    simpl bind.
    unfold block_fusion_cfg.
    destruct (block_fusion G.(blks)) as [bks' [[src tgt] |]] eqn:EQ. 
    - break_match_goal; [reflexivity |].
      simpl.
      apply Bool.orb_false_elim in Heqb as [INEQ1 INEQ2].
      unfold Eqv.eqv_dec in *.
      rewrite <- RelDec.neg_rel_dec_correct in INEQ1.
      rewrite <- RelDec.neg_rel_dec_correct in INEQ2.
      eapply block_fusion_correct_some with (f := G.(init)) (to := G.(init)) in EQ; auto.
      rewrite update_provenance_ineq in EQ; auto. 
      eapply eutt_clo_bind; [apply EQ |].
      intros [[]|?] [[]|?] INV; try now inv INV.
      subst; reflexivity.
      eapply wf_cfg_src_not_in_phis; eauto.
      constructor; auto.
    - reflexivity.
  Qed.

End BlockFusionCorrect.

