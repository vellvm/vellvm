From Coq Require Import
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
     Semantics.InterpretationStack
     Semantics.TopLevel
     Theory.DenotationTheory
     Transformations.Peephole.

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

Fixpoint remove_block {T} (G : ocfg T) (bk : block T) : ocfg T :=
  match G with
  | [] => []
  | bk' :: G => if Eqv.eqv_dec bk.(blk_id) bk'.(blk_id) then G else bk':: remove_block G bk
  end.

Infix "∖" := remove_block.

(* Test whether b ∈ successors(bk), i.e.
  [is_predecessor b bk] iff [bk] is a predecessor to [b].
 *)
Definition is_predecessor {T} (b : block_id) (bk : block T) : bool :=
  if raw_id_in b (successors bk) then true else false.

(* Computes the set of predecessors of [b] in [G] *)
Definition predecessors (b : block_id) (G : ocfg dtyp) : set block_id :=
  fold_left (fun acc bk => if is_predecessor b bk then bk.(blk_id) ::: acc else acc) G ∅.

Section LoopFusion.

  (* If a block has a unique predecessor, its phi-nodes can be trivially converted to straight code.
     Wrote it a bit carelessly as total right now. Assumes that it is only called on a block having
     indeed a single predecessor, among a well formed graph: we therefore should always have when
     called that all lists under a [Phi] constructor are exactly singletons.
     Actually trickier: by doing this conversion, we are linearizing a set of assignments that were
     computed in parallel. It is sound because with a unique predecessor it shouldn't be possible to
     have a recursive dependency in your phi-nodes, but it might be tricky to argue/capture formally.
     To keep an eye on it.
   *)
  (* YZ: Why does the phi node carries this typing information [τ] again? *)
  Definition phi_to_code {T} (Φs : list (local_id * phi T)) : code T :=
    fold_left (fun acc '(id, Phi τ l) =>
                 match l with
                 | [(_,e)] => acc ++ [(IId id, INSTR_Op e)] (* Keeping the order should not matter, but if we can spare the argument later... *)
                 | _ => (* This is a failure case, it should not happen if called in the expected context *)
                   acc
                 end) Φs [].

  (* We should be able to handle phi-nodes if there is a unique predecessor, but let's not worry for it for now *)
  (*
  Definition fusion_blocks (b_s b_t : block dtyp) : block dtyp :=
    {|
    blk_id         := b_s.(blk_id);
    blk_phis       := b_s.(blk_phis);
    blk_code       := b_s.(blk_code) ++ phi_to_code b_t.(blk_phis) ++ b_t.(blk_code);
    blk_term       := b_t.(blk_term);
    blk_comments   := None (* TODO: proper propagation of comments *)
    |}.
   *)

  Definition fusion_blocks (b_s b_t : block dtyp) : block dtyp :=
    {|
    blk_id         := b_s.(blk_id);
    blk_phis       := b_s.(blk_phis);
    blk_code       := b_s.(blk_code) ++ b_t.(blk_code);
    blk_term       := b_t.(blk_term);
    blk_comments   := None (* TODO: proper propagation of comments *)
    |}.

  Definition has_no_phi (b : block dtyp) : bool := match b.(blk_phis) with | [] => true | _ => false end.

  (* Let's start easy: we perform at most one fusion.
     To perform all available fusions we need to be a bit more clever w.r.t. to termination.
   *)
  Fixpoint fusion_block_aux (G : ocfg dtyp) (bks : ocfg dtyp) : ocfg dtyp :=
    (* We scan the blocks in sequence until... *)
    match bks with
    | [] => []
    | bk_s :: bks =>
      match bk_s.(blk_term) with
      | TERM_Br_1 b_t =>
        (* ... We find a block with a direct jump. *)
        match find_block G b_t with
        (* If this direct jump is internal to the [ocfg] considered... *)
        | Some bk_t =>
        (* And if [bk_s] is the only predecessor of this block *)
          if andb (Eqv.neg_eqv_dec b_t bk_s.(blk_id)) (andb (length (predecessors b_t G) =? 1) (has_no_phi bk_t))
          then (fusion_blocks bk_s bk_t) :: ((G ∖ bk_s) ∖ bk_t)
          else fusion_block_aux G bks
        | None => fusion_block_aux G bks
        end
      | _ => fusion_block_aux G bks
      end
    end.

  Definition fusion_block : ocfg dtyp -> ocfg dtyp :=
    fun G => fusion_block_aux G G.

End LoopFusion.

Import SemNotations.
Section LoopFusionCorrect.

  Lemma fusion_block_out : forall G to,
    find_block G to = None ->
    find_block (fusion_block G) to = None.
  Proof.
  Admitted.

  Fixpoint get_fused_block_aux (G bks : ocfg dtyp) : option (block_id * block_id) :=
    match bks with
    | [] => None
    | bk_s :: bks =>
      match bk_s.(blk_term) with
      | TERM_Br_1 b_t =>
        match find_block G b_t with
        | Some bk_t =>
          if andb (length (predecessors b_t G) =? 1) (has_no_phi bk_t)
          then Some (bk_s.(blk_id),b_t)
          else get_fused_block_aux G bks
        | None => get_fused_block_aux G bks
        end
      | _ => get_fused_block_aux G bks
      end
    end.

  Definition get_fused_block G := get_fused_block_aux G G.

  Lemma fusion_block_is_block_touched:
    forall G to,
      find_block G to = find_block (fusion_block G) to \/
      (match get_fused_block G with
       | Some (x,y) => to = x \/ to = y
       | None => False
       end).
  Proof.
  Admitted.

  Lemma fusion_block_changed_block:
    forall G f1 f2,
      get_fused_block G = Some (f1,f2) ->
      f1 <> f2 /\
      exists b1 b2,
        find_block G f1 = Some b1 /\
        blk_term b1 = TERM_Br_1 f2 /\
        find_block G f2 = Some b2 /\
        has_no_phi b2 = true /\
        find_block (fusion_block G) f1 = Some (fusion_blocks b1 b2) /\
        find_block (fusion_block G) f2 = None /\
        (forall f, f <> f1 -> f <> f2 -> find_block G f = find_block (fusion_block G) f).
  Proof.
  Admitted.

  Lemma fusion_block_unchanged :
    forall G, 
      get_fused_block G = None ->
      forall f, find_block G f = find_block (fusion_block G) f.
  Proof.
  Admitted.

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

Lemma fusion_block_correct :
  forall G f to b1 b2,
    get_fused_block G = Some (b1,b2) ->
    to <> b2 ->
    ⟦ G ⟧bs (f,to) ≈ ⟦ fusion_block G ⟧bs (f,to).
Proof.
  intros * FUSED; revert f to.
  apply fusion_block_changed_block in FUSED; destruct FUSED as (INEQ & bk1 & bk2 & LU1 & TERM & LU2 & NOPHI & LU3 & LU4 & LU5).
  unfold denote_ocfg.
  (* setoid_rewrite KTreeFacts.unfold_iter_ktree. *)
  einit.
  ecofix CIH.
  intros * INEQ'.
  destruct (Eqv.eqv_dec_p to b1).
  - do 2 red in e; subst b1.
    setoid_rewrite KTreeFacts.unfold_iter_ktree.
    rewrite LU1, LU3.
    unfold fusion_blocks.
    cbn.
    rewrite !bind_bind.
    setoid_rewrite denote_code_app.
    repeat setoid_rewrite bind_bind.
    ebind; econstructor; [reflexivity | intros ? ? <-].
    ebind; econstructor; [reflexivity | intros ? ? <-].
    repeat setoid_rewrite bind_ret_l.
    ebind; econstructor; [reflexivity | intros ? ? <-].
    rewrite TERM.
    cbn; rewrite translate_ret, !bind_ret_l.
    rewrite tau_euttge. 
    rewrite KTreeFacts.unfold_iter_ktree, LU2.
    rewrite !bind_bind.
    unfold has_no_phi in *.
    destruct (blk_phis bk2) eqn:NOPHI'; [clear NOPHI| inversion NOPHI].
    unfold denote_phis; cbn; rewrite bind_ret_l, !bind_bind.
    cbn; rewrite !bind_ret_l, !bind_bind; cbn.
    ebind; econstructor; [reflexivity | intros ? ? <-].
    rewrite bind_ret_l.
    ebind; econstructor; [reflexivity | intros ? ? <-].
    destruct u4.
    + rewrite !bind_ret_l.
      etau.
      ebase.
      right.
      clear - CIH.
      specialize (CIH b2 b).
      cbn in CIH.
      unfold denote_phis in CIH.
      cbn in *.
      Fail apply CIH.
      (* Problem: we need to update the phi nodes of the target of
         the fused block!*)
      admit.
    + rewrite !bind_ret_l.
      reflexivity.
  - setoid_rewrite KTreeFacts.unfold_iter_ktree.
    rewrite <- LU5; auto.
    ebind; econstructor; [reflexivity | intros ? ? <-].
    destruct u1; [| reflexivity].
    etau.
    ebase.
    right.
    destruct p.
    apply CIH.
    (* Easy argument on which label can be jumped to *)
    admit.
Admitted.    
