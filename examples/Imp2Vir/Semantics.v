From Coq Require Import
     Lia
     String
     ZArith.

From ExtLib Require Import FMapAList.

From ITree Require Import
     ITree
     ITreeFacts.

From Vellvm Require Import
     Handlers.Handlers
     Semantics
     Syntax
     Syntax.ScopeTheory.
From Imp2Vir Require Import Fin Imp.

Require Import Vec Unique CvirCombinators CvirCombinatorsWF CompileExpr Imp2Cvir.

Definition Rmem (env : Imp.env) (vmap : StringMap.t int) (venv : local_env) (vmem : memory_stack) : Prop :=
  forall k v, alist_find k env = Some v <-> (
    exists reg, StringMap.find k vmap = Some reg /\
      exists addr, alist_find (Anon reg) venv = Some (UVALUE_Addr addr) /\
        exists v32, read vmem addr (DTYPE_I (Npos 32%positive)) = inr (UVALUE_I32 v32) /\
          Int32.intval v32 = Z.of_nat v
  ).

Definition R
  (vmap : StringMap.t int)
  (env1 : Imp.env * unit)
  (env2 : memory_stack * (local_env * (global_env * (block_id * block_id + uvalue)))) :
  Prop :=
  Rmem (fst env1) vmap (fst (snd env2)) (fst env2).

(* Denotation of a [cvir] construct.
  Note: we should be able to take any three disjoint sets 
  of names [vi,vo,vt] to feed our [ir].
  One way is to take as a "canonical" name the first integers:
  this is what the current version does with [build_map].
  Another would be to be parameterized by three such sets ---
  lemmas about it would assume that they are disjoint.
  We currently suspect that the later formulation might be
  necessary to express generic lemmas, even if "at the top level"
  we will always use the canonical naming. It is not yet clear though. 
*)
Definition build_map a b :=
  map Anon (map Z.of_nat (seq a b)).

Definition denote_cvir {ni no} (ir : cvir ni no) (bid : fin ni) bid' :=
  let vi := build_map 0 ni in
  let vo := build_map ni no in
  let vt := build_map (ni + no) (n_int ir) in
  denote_ocfg (convert_typ nil (blocks ir vi vo vt)) (bid', nth vi bid).

(* In particular: can we have a reasoning principle to prove that two
  cvir are related?
  That is a lemma that would allow us to conclude something along the lines of:
  [eutt R (denote_cvir ir1 n org) (denote_cvir ir2 m org)]
  by chosing an invariant I and having two proof obligations:
  - I holds initially (of n m and org?)
  - If we start from arguments in I, then we prove something about
  ir1.(blocks) and ir2.(blocks) at these arguments.

This lemma would likely be based on and ressemble the low level lemma on [iter],
but could be more precise since we are here considering bodies of a specific shape:

Lemma eutt_iter_gen :
forall {F : Type -> Type} {A B : Type} {R : A -> A -> Prop} {S : B -> B -> Prop},
  forall body1 body2,
   (forall a a', R a a' -> eutt (sum_rel R S) (body1 a) (body2 a')) ->
   forall  a a', R a a' -> eutt S (iter body1 a) (iter body2 a')

The drafted proof below of [denote_cvir_merge] uses [eutt_iter_gen] but
leads to some non-trivial arithmetic and reasoning on renaming.
Maybe using this hypothetical higher level lemma could sooth the pain.
 *)

(* The following lemmas should be true *)
Lemma firstn_build_map : forall i n m,
firstn n (build_map i (n + m)) = build_map i n.
Admitted.

Lemma skipn_build_map : forall i n m,
skipn n (build_map i (n + m)) = build_map (i + n) m.
Admitted.

From Coq Require Import Morphisms.
Require Import ITree.Basics.HeterogeneousRelations.
Import ITreeNotations.
Import SemNotations.

(*  *)
Theorem denote_cvir_merge : forall ni1 no1 ni2 no2 (ir1 : cvir ni1 no1) (ir2 : cvir ni2 no2) bid bid',
  cvir_ids_WF ir1 ->
  cvir_ids_WF ir2 ->
  unique_bid ir1 ->
  unique_bid ir2 ->
  eutt eq
    (denote_cvir (merge_cvir ir1 ir2) bid bid')
    (match split_fin_sum ni1 ni2 bid with
    | inl bid1 => denote_cvir ir1 bid1 bid'
    | inr bid2 => denote_cvir ir2 bid2 bid'
    end).
Proof.
  intros * WF11 WF12 WF21 WF22.
  (* case analysis on which subgraph we are in: *)
  destruct (split_fin_sum ni1 ni2 bid) eqn:Eq. 
  - rename f into bid1. 
    unfold denote_cvir.
    unfold merge_cvir.
    cbn.
    rewrite !firstn_build_map.
    rewrite !skipn_build_map.
    (* the invariant on the block identifiers we encounter during the computation *)
    set (I := (fun (fto fto' : block_id * block_id) =>
        ( exists k, snd fto' = Anon (Z.of_nat k) /\
                    snd fto = Anon (Z.of_nat k)  /\
                    k < ni1
         ) \/
        (exists k, snd fto' = Anon (Z.of_nat k) /\ 
                   snd fto  = Anon (Z.of_nat (k + ni2 + no2)) /\ 
                   k >= ni1 + no1 
                   (* Need for upper bound: k < ni1 + no1 + nt1? *)
    ))%nat).
    (* we apply [eutt_iter_gen] with this invariant *)
    apply (@KTreeFacts.eutt_iter_gen _ _ _ I). 
    + (* We need to prove that it is indeed an invariant *)
      simpl bind.
      intros [? ?b1] [? ?b2] HI.
      destruct HI as [HI | HI].
      * destruct HI as (k & EQ1 & EQ2 & INEQ); cbn in * |-.
        (* 
  Step 1: renaming and lookups
 
  find_block
      (convert_typ nil
         (blocks ir1 (build_map 0 ni1) (build_map (ni1 + ni2) no1)
            (build_map (ni1 + ni2 + (no1 + no2)) (n_int ir1)) ++
          blocks ir2 (build_map (0 + ni1) ni2)
            (build_map (ni1 + ni2 + no1) no2)
            (build_map (ni1 + ni2 + (no1 + no2) + n_int ir1) (n_int ir2)))%list)
      b1 = Some bk_src1

find_block
      (convert_typ nil
         (blocks ir1 (build_map 0 ni1) (build_map ni1 no1)
            (build_map (ni1 + no1) (n_int ir1)))) b2 = Some bk_src2

  bk_src2 = rename_bk (to_write ) bk_src1

  Step 2 : correctness of renaming
    eutt (sum_rel rename_bid eq) bk (rename_bk bk)
 *)
        admit.
      * admit.
    + (* The invariant holds initially *)
      admit.
- admit.
Admitted.


  (*
  Approach started by Nicolas:

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
*)

(* 
I (_, x)
  nth vnth vi bigi bid

  I : (block_id * block_id) -> (block_id * block_id) -> Prop
  I ids1 ids2 -> eutt I ([|G1[snd ids1]|] (fst ids1)) ([|G1[snd ids2]|] (fst ids2))
  I idsinit2 idsinit2
  ---------
  G1 idsinit2 ~ G2 idsinit2


  simpl.
  destruct (split_fin_sum _ _ _).
Admitted.
*)

Definition sym_fin {n1 n2 n3 : nat} (f : fin (n1 + (n2 + n3))) : fin (n1 + (n3 + n2)) :=
  match split_fin_sum _ _ f with
  | inl l => L (n3 + n2) l
  | inr r => Fin.R n1 (
    match split_fin_sum _ _ r with
    | inl l => Fin.R _ l
    | inr r => L _ r
    end
  )
  end.

Theorem denote_cvir_sym_i : forall {ni1 ni2 ni3 no : nat} (ir : cvir (ni1 + (ni2 + ni3)) no) bid bid',
  cvir_ids_WF ir ->
  unique_bid ir ->
  eutt eq
    (denote_cvir ir bid bid')
    (denote_cvir (sym_i_cvir ir) (sym_fin bid) bid').
Admitted.

Theorem denote_cvir_relabel : forall ni no (ir : cvir ni no) vi vi' vo vo' vt vt' (bid : fin ni) bid',
  cvir_ids_WF ir ->
  unique_bid ir ->
  unique_vector (vi ++ vo ++ vt) ->
  unique_vector (vi' ++ vo' ++ vt') ->
  eutt eq
    (denote_ocfg (convert_typ nil (blocks ir vi vo vt)) (bid', nth vi bid))
    (denote_ocfg (convert_typ nil (blocks ir vi' vo' vt')) (bid', nth vi' bid)).
Admitted.

Theorem compile_seq_correct : forall next_reg l r env next_reg' env' ir mem bid genv lenv vmem,
  compile next_reg (Seq l r) env = Some(next_reg', env', ir) ->
  eutt (R env)
  (interp_imp (denote_imp (Seq l r)) mem)
  (interp_cfg3 (denote_cvir ir f0 bid) genv lenv vmem).
Admitted.

