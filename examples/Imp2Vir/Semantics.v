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
From tutorial Require Import Fin Imp.

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

Definition denote_cvir {ni no} (ir : cvir ni no) (bid : fin ni) bid' :=
  let vi := map Anon (map Z.of_nat (seq 0 ni)) in
  let vo := map Anon (map Z.of_nat (seq ni no)) in
  let vt := map Anon (map Z.of_nat (seq (ni + no) (n_int ir))) in
  denote_ocfg (convert_typ nil (blocks ir vi vo vt)) (bid', nth vi bid).

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
  intros.
  unfold denote_cvir.
  simpl.
  destruct (split_fin_sum _ _ _).
Admitted.

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
