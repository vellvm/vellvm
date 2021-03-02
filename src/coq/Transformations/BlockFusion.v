From Coq Require Import
     Lia
     String
     Morphisms.

Require Import List.
Import ListNotations.
Require Import ZArith.

From ITree Require Import
     ITree
     Basics.Monad
     Eq.Eq
     InterpFacts
     TranslateFacts.

From Vellvm Require Import
     Utils.Util
     Utils.Tactics
     Utils.PostConditions
     Syntax.Scope
     Syntax.LLVMAst
     Syntax.CFG
     Syntax.AstLib
     Syntax.DynamicTypes
     Semantics.LLVMEvents
     Semantics.InterpretationStack
     Semantics.TopLevel
     Theory.DenotationTheory
     Transformations.Peephole.

Opaque append.
Import ListSet.

Remove Hints Eqv.EqvWF_Build : typeclass_instances.

Set Implicit Arguments.
Set Strict Implicit.

Import ListNotations.
Open Scope bool.

(* NOTE: Might be worth it to represent [ocfg] as sets of blocks rather than lists, with an efficient implementation of sets *)

(* NOTE: This is stupidly inefficient to recompute the predecessor like that
   everytime we need it of course, just a temporary stub
 *)

Definition raw_id_in := in_dec raw_id_eq_dec.

Infix "∈" := (set_mem raw_id_eq_dec) (at level 70).

Fixpoint remove_block {T} (G : ocfg T) (b : block_id) : ocfg T :=
  match G with
  | [] => []
  | bk :: G => if Eqv.eqv_dec b bk.(blk_id) then G else bk:: remove_block G b
  end.

Infix "∖" := remove_block.

(* Test whether b ∈ successors(bk), i.e.
  [is_predecessor b bk] iff [bk] is a predecessor to [b].
 *)
Definition is_predecessor {T} (b : block_id) (bk : block T) : bool :=
  if raw_id_in b (successors bk) then true else false.

(* Computes the set of predecessors of [b] in [G] *)

Definition predecessors (b : block_id) (G : ocfg dtyp) : list block_id :=
  fold_left (fun acc bk => if is_predecessor b bk then bk.(blk_id) :: acc else acc) G [].

Lemma app_snoc_app : forall {A} (l l' : list A) x,
    (l ++ [x]) ++ l' = l ++ (x :: l').
Proof.
  induction l as [| y l IH]; [reflexivity | cbn; intros].
  f_equal; apply IH.
Qed.

Lemma predecessors_app :
  forall bks bks' f,
    predecessors f (bks ++ bks') = predecessors f bks' ++ predecessors f bks.
Proof.
  induction bks' as [| bk bks' IH] using rev_ind.
  - intros; cbn; rewrite !app_nil_r; reflexivity.
  - intros.
    unfold predecessors.
    rewrite app_assoc.
    rewrite 2 (fold_left_app _ _ [bk]). 
    simpl.
    break_match_goal.
    + cbn; f_equal.
      apply IH.
    + apply IH.
Qed.

Lemma predecessors_cons :
  forall bks bk f,
    predecessors f (bk :: bks) = predecessors f bks ++ predecessors f [bk].
Proof.
  intros.
  rewrite list_cons_app, predecessors_app.
  reflexivity.
Qed.


Lemma find_block_has_id : forall {T} (G : ocfg T) b bk,
    find_block G b = Some bk ->
    b = bk.(blk_id).
Proof.
  induction G as [| bkh G IH].
  - intros * LU; inv LU.
  - intros * LU.
    cbn in LU.
    break_match_hyp.
    + inv LU; break_match_hyp; intuition.
    + apply IH.
      apply LU.
Qed.

Lemma find_block_In : forall {T} G (bk : block T),
    find_block G bk.(blk_id) = Some bk ->
    In bk G.
Proof.
  induction G as [| x G IH]; intros * FIND; [inv FIND |].
  cbn in FIND; break_match_hyp; auto.
  inv FIND; left; reflexivity.
  right; apply IH; auto.
Qed.

Lemma successor_predecessor :
  forall (G : ocfg dtyp) (source : block dtyp) target,
    In target (successors source) ->
    find_block G source.(blk_id) = Some source ->
    In source.(blk_id) (predecessors target G).
Proof.
  intros * IN FIND.
  apply find_block_In in FIND; revert FIND.
  induction G as [| bki G IH]; intros * FIND. 
  - inv FIND.
  - destruct FIND as [EQ | FIND].
    + subst.
      clear IH.
      rewrite predecessors_cons.
      apply in_or_app; right.
      cbn.
      unfold successors in IN.
      unfold is_predecessor.
      break_match_goal.
      left; auto.
      break_match_hyp; intuition.
    + rewrite predecessors_cons.
      apply in_or_app; left.
      apply IH; auto.
Qed.

Lemma wf_ocfg_commut :
  forall {T} (G G' : ocfg T),
    wf_ocfg_bid (G ++ G') ->
    wf_ocfg_bid (G' ++ G).
Proof.
  intros.
  red; rewrite inputs_app; apply Coqlib.list_norepet_append_commut; rewrite <- inputs_app; apply H.
Qed.

Lemma wf_ocfg_commut_hd :
  forall {T} (bk bk' : block T) G,
    wf_ocfg_bid (bk::bk'::G) ->
    wf_ocfg_bid (bk'::bk::G).
Proof.
  intros * WF.
  inv WF.
  inv H2.
  constructor.
  2: constructor; auto.
  - intros [EQ | IN]; auto.
    apply H1; left; auto.
  - intros IN; auto.
    eapply H1; right; auto.
Qed.

Lemma wf_ocfg_cons_not_in_tail :
  forall {T} (bk : block T) G,
    wf_ocfg_bid (bk :: G) ->
    find_block G bk.(blk_id) = None.
Proof.
  induction G as [| x G IH]; intros; [reflexivity |].
  cbn; break_match_goal.
  - break_match_hyp; intuition.
    do 2 red in e.
    exfalso; clear Heqb.
    red in H.
    cbn in H.
    rewrite e in H.
    inv H.
    eapply H2; left; reflexivity.
  - break_match_hyp; intuition.
    apply IH.
    apply wf_ocfg_commut_hd in H.
    eapply wf_ocfg_bid_cons; eauto.
Qed.


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

Lemma wf_ocfg_map : forall {T} (f : block T -> block T) (G : ocfg T),
    (forall bk, blk_id (f bk) = blk_id bk) ->
    wf_ocfg_bid G <-> wf_ocfg_bid (map f G).
Proof.
  intros.
  unfold wf_ocfg_bid, inputs.
  rewrite List.map_map.
  replace (map (fun x : block T => blk_id (f x)) G) with (map blk_id G); [reflexivity |].
  apply map_ext.
  intros; rewrite H; auto.
Qed.

Lemma find_block_map_some :
  forall {T} (f : block T -> block T) G b bk,
    (forall bk, blk_id (f bk) = blk_id bk) ->
    find_block G b = Some bk ->
    find_block (map f G) b = Some (f bk).
Proof.
  intros * ID; induction G as [| hd G IH]; intros FIND ; [inv FIND |].
  cbn in *.
  rewrite ID. 
  break_match_goal; break_match_hyp; intuition.
  inv FIND; auto.
Qed.

Lemma find_block_map_none :
  forall {T} (f : block T -> block T) G b,
    (forall bk, blk_id (f bk) = blk_id bk) ->
    find_block G b = None ->
    find_block (map f G) b = None.
Proof.
  intros * ID; induction G as [| hd G IH]; intros FIND; [reflexivity |].
  cbn in *.
  rewrite ID. 
  break_match_goal; break_match_hyp; intuition.
  inv FIND; auto.
Qed.

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

  (* We should be able to handle phi-nodes if there is a unique predecessor, but let's not worry for it for now *)
  (*
  Definition block_fusions (b_s b_t : block dtyp) : block dtyp :=
    {|
    blk_id         := b_s.(blk_id);
    blk_phis       := b_s.(blk_phis);
    blk_code       := b_s.(blk_code) ++ phi_to_code b_t.(blk_phis) ++ b_t.(blk_code);
    blk_term       := b_t.(blk_term);
    blk_comments   := None (* TODO: proper propagation of comments *)
    |}.
   *)

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

Import SemNotations.
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

  Lemma denote_code_app :
    forall a b,
      ⟦ a ++ b ⟧c ≅ ITree.bind ⟦ a ⟧c (fun _ => ⟦ b ⟧c).
  Proof.
    induction a; intros b.
    - cbn.
      cbn.
      rewrite !bind_ret_l.
      eapply eq_itree_clo_bind with (UU := eq); [reflexivity | intros ? ? ->; reflexivity].
    - cbn in *.
      rewrite !bind_bind.
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

  Arguments denote_phis: simpl never.

  Import ITreeNotations.
  Lemma denote_ocfg_unfold_in_euttge: forall bks bid_from bid_src bk,
      find_block bks bid_src = Some bk ->
      ⟦ bks ⟧bs (bid_from, bid_src) ≳
             vob <- ⟦ bk ⟧b bid_from ;;
      match vob with
      | inr v => Ret (inr v)
      | inl bid_target => ⟦ bks ⟧bs (bid_src, bid_target)
      end.
  Proof.
    intros * GET_BK.
    cbn. unfold denote_ocfg at 1.
    rewrite KTreeFacts.unfold_iter_ktree. cbn.
    rewrite GET_BK.
    repeat setoid_rewrite bind_bind.
    repeat (eapply eqit_bind; [intros ? |reflexivity]).
    break_sum; rewrite bind_ret_l; [|reflexivity].
    rewrite tau_euttge; reflexivity.
  Qed.

  Lemma denote_ocfg_unfold_in_eq_itree: forall bks bid_from bid_src bk,
      find_block bks bid_src = Some bk ->
      ⟦ bks ⟧bs (bid_from, bid_src) ≅
             vob <- ⟦ bk ⟧b bid_from ;;
      match vob with
      | inr v => Ret (inr v)
      | inl bid_target => Tau (⟦ bks ⟧bs (bid_src, bid_target))
      end.
  Proof.
    intros * GET_BK.
    cbn. unfold denote_ocfg at 1.
    rewrite KTreeFacts.unfold_iter_ktree. cbn.
    rewrite GET_BK.
    repeat setoid_rewrite bind_bind.
    repeat (eapply eqit_bind; [intros ? |reflexivity]).
    break_sum; rewrite bind_ret_l; [|reflexivity].
    apply eqit_Tau.
    reflexivity.
  Qed.

  Lemma denote_ocfg_unfold_not_in_eq_itree: forall bks bid_from bid_src,
      find_block bks bid_src = None ->
      ⟦ bks ⟧bs (bid_from, bid_src) ≅ Ret (inl (bid_from,bid_src)).
  Proof.
    intros * GET_BK.
    unfold denote_ocfg.
    rewrite KTreeFacts.unfold_iter_ktree.
    rewrite GET_BK; cbn.
    rewrite bind_ret_l.
    reflexivity.
  Qed.

  Lemma denote_ocfg_unfold_eq_itree: forall bks bid_from bid_src,
      ⟦ bks ⟧bs (bid_from, bid_src) ≅
             match find_block bks bid_src with
             | Some bk => vob <- ⟦ bk ⟧b bid_from ;;
                         match vob with
                         | inr v => Ret (inr v)
                         | inl bid_target => Tau (⟦ bks ⟧bs (bid_src, bid_target))
                         end
             | None => Ret (inl (bid_from,bid_src))
             end.
  Proof.
    intros *.
    break_match_goal.
    - rewrite denote_ocfg_unfold_in_eq_itree; eauto; reflexivity.
    - rewrite denote_ocfg_unfold_not_in_eq_itree; eauto; reflexivity.
  Qed.

  Require Import Paco.paco.

  Lemma has_post_eq_itree_aux : forall {E X} (t : itree E X) (Q : X -> Prop),
      has_post_strong t Q ->
      eq_itree (fun 'x y => x = y /\ Q x) t t.
  Proof.
    intros.
    unfold has_post_strong in *.
    rewrite itree_eta in *.
    genobs t ot.
    revert t ot H Heqot.
    ginit.
    gcofix CIH.
    intros.
    pose proof H0 as EQ.
    punfold H0.
    red in H0. cbn in H0.
    subst ot.
    induction H0.
    - gstep; constructor; intuition; subst; auto.
    - gstep; constructor.
      rewrite itree_eta.
      gbase.
      eapply CIH; eauto.
      rewrite <- tau_eutt at 1 2.
      rewrite (itree_eta m2) in EQ.
      apply EQ.
    - gstep. constructor.
      intros; red.
      rewrite (itree_eta (k2 v)).
      gbase.
      eapply CIH; eauto.
      unfold eutt in EQ; rewrite <- eqit_Vis in EQ.
      specialize (EQ v).
      rewrite (itree_eta (k2 v)) in EQ.
      apply EQ.
    - apply IHeqitF; auto.
    - gstep; constructor.
      rewrite itree_eta.
      gbase.
      eapply CIH; eauto.
      rewrite <- tau_eutt at 1 2.
      rewrite (itree_eta t2) in EQ.
      apply EQ.
  Qed.

  Lemma has_post_eq_itree : forall {E X} (t : itree E X) (Q : X -> Prop),
      has_post t Q ->
      eq_itree (fun 'x y => x = y /\ Q x) t t.
  Proof.
    intros; apply has_post_post_strong in H; apply has_post_eq_itree_aux; auto.
  Qed.

  Lemma find_block_map :
    forall {T} (f : block T -> block T) G b,
      (forall bk, blk_id (f bk) = blk_id bk) ->
      find_block (map f G) b = option_map f (find_block G b).
  Proof.
    intros.
    destruct (find_block G b) eqn:EQ.
    eapply find_block_map_some in EQ; eauto.
    eapply find_block_map_none in EQ; eauto.
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

  Definition phi_sources {T} (φ : phi T) : list block_id :=
    let '(Phi _ l) := φ in
    map fst l.

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

  Lemma find_block_In' : forall {T} G b (bk : block T),
      find_block G b = Some bk ->
      In bk G.
  Proof.
    intros * LU; pose proof find_block_has_id _ _ LU; subst; apply find_block_In; auto.
  Qed.

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
      setoid_rewrite denote_code_app.
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
      specialize (CIH b2 next).
      rewrite update_provenance_eq in CIH.
      apply CIH; auto.
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
        specialize (CIH to b_next).
        rewrite update_provenance_ineq in CIH; auto.
        apply CIH; auto.
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

  (* Over a closed graph, phi nodes should expect exactly jumps from their predecessors:
     - For any block [bk] in the graph
     - For any phi node [phi] in this block
     - the sources of [phi] and the predecessors of [bk] are in bijection
   *)
  Definition wf_ocfg_phis (G : ocfg dtyp) :=
    forall bk pred x phi,
      In bk G ->
      In (x,phi) bk.(blk_phis) ->
      (In pred (phi_sources phi) <-> In pred (predecessors bk.(blk_id) G)).

  Record wf_cfg (G : cfg dtyp): Prop := WF_CFG
                                      {
                                        wf_cfg_bid : wf_ocfg_bid G.(blks);
                                        wf_cfg_phis : wf_ocfg_phis G.(blks)
                                      }.
  
  Lemma wf_ocfg_bid_find_block_unique :
    forall (bks : ocfg dtyp) bk1 b1 bk2,
      wf_ocfg_bid bks ->
      find_block bks b1 = Some bk1 ->
      find_block bks b1 = Some bk2 ->
      bk1 = bk2.
  Proof.
    induction bks as [| bk bks IH]; intros * WF FIND1 FIND2; [inv FIND1 |].
    cbn in *.
    break_match_hyp.
    inv FIND1; inv FIND2; auto.
    break_match_hyp; intuition.
    eapply IH; eauto.
    eapply wf_ocfg_bid_cons; eauto. 
  Qed.

  Lemma In_find_block :
    forall (bks : ocfg dtyp) bk,
      In bk bks ->
      exists bk', find_block bks bk.(blk_id) = Some bk'.
  Proof.
    induction bks as [| x bks IH]; intros * IN; [inv IN | ].
    destruct (Eqv.eqv_dec_p x.(blk_id) bk.(blk_id)).
    - do 2 red in e; exists x; rewrite find_block_eq; auto. 
    - rewrite find_block_ineq; [| auto].
      apply IH.
      destruct IN; auto. 
      exfalso; subst; eapply n; reflexivity.
  Qed.

  Lemma wf_ocfg_bid_In_is_found :
    forall (bks : ocfg dtyp) bk, 
      wf_ocfg_bid bks ->
      In bk bks ->
      find_block bks bk.(blk_id) = Some bk.
  Proof.
    induction bks as [| x bks IH]; intros * WF IN; [inv IN |].
    destruct (Eqv.eqv_dec_p x.(blk_id) bk.(blk_id)).
    - rewrite find_block_eq; auto.
      destruct IN as [-> | IN]; auto.
      apply wf_ocfg_bid_cons_not_in in WF.
      exfalso; apply WF.
      do 2 red in e; rewrite e.
      eapply in_map; auto.
    - rewrite find_block_ineq; [| auto].
      apply IH.
      eapply wf_ocfg_bid_cons; eauto.
      destruct IN; auto. 
      exfalso; subst; eapply n; reflexivity.
  Qed.

  Definition predecessors_aux (b : block_id) (G : ocfg dtyp) acc :=
    fold_left (fun acc bk => if is_predecessor b bk then bk.(blk_id) :: acc else acc) G acc.
  
  Lemma In_predecessors_is_predecessor_aux :
    forall (G : ocfg dtyp) acc (src tgt : block_id), 
      In src (predecessors_aux tgt G acc) ->
      (In src acc \/ exists bk, In bk G /\ src = bk.(blk_id) /\ is_predecessor tgt bk).
  Proof.
    intros *; revert acc; induction G as [| bk G IH]; intros acc IN; [left; auto |].
    cbn in IN.
    break_match_hyp.
    - edestruct IH as [INACC | (bk' & INbk & -> & PRED)]; eauto.
      + destruct INACC as [<- | ?]; [| left; auto].
        right; exists bk; intuition.
      + right.
        exists bk'; intuition.
    - edestruct IH as [INACC | (bk' & INbk & -> & PRED)]; eauto.
      right; exists bk'; intuition.
  Qed.

 Lemma In_predecessors_is_predecessor :
    forall (G : ocfg dtyp) (src tgt : block_id), 
      In src (predecessors tgt G) ->
      exists bk, In bk G /\ src = bk.(blk_id) /\ is_predecessor tgt bk.
  Proof.
    intros * IN.
    edestruct In_predecessors_is_predecessor_aux as [INACC | (bk' & INbk & -> & PRED)]; eauto.
    inv INACC.
  Qed.

  Lemma predecessor_successor :
    forall (G : ocfg dtyp) (source target : block_id) (bk : block dtyp),
      wf_ocfg_bid G ->
      In source (predecessors target G) ->
      find_block G source = Some bk ->
      In target (successors bk).
  Proof.
    intros * WF IN FIND.
    pose proof In_predecessors_is_predecessor _ _ _ IN as (bk' & IN' & -> & ISPRED).
    apply wf_ocfg_bid_In_is_found in IN'; auto.
    rewrite FIND in IN'; inv IN'.
    unfold is_predecessor in ISPRED.
    break_match_hyp; intuition.
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
  Lemma block_fusion_cfg_correct :
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

