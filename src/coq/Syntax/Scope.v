(* begin hide *)
From Coq Require Import
     List.
Import ListNotations.

From Vellvm Require Import
     Numeric.Coqlib
     Utils.Util
     Utils.Tactics
     Syntax.LLVMAst
     Syntax.CFG
     Syntax.TypToDtyp.

From ExtLib Require Import List.
(* end hide *)

(** * Scoping
    We define through this file several functions and predicates having to do with the scope
    of VIR programs, w.r.t. both block identifiers and local variables.
    We unfortunately inherit from LLVM IR a fully named representation of variables, forcing
    on us fairly heavy sanity checks.
    - [inputs]: input labels of an [ocfg]
    - [outputs]: output labels of an [ocfg]
    - [wf_ocfg_bid]: no duplicate block identifiers


 *)

(** * Well-formedness w.r.t. block identifiers
    An [ocfg] should not admit any collisions w.r.t. to its labels.
 *)
Section LABELS_OPERATIONS.

  Context {T : Set}.

  (** * inputs
     Collect the list of input labels in an open control flow graph.
     Denoting an [ocfg] starting from a label out of this static list
     always results in the identity.
   *)
  Definition inputs (ocfg : @ocfg T) :=
    map blk_id ocfg.

  (** * outputs
     Collect the list of output labels in an open control flow graph.
     Denoting an [ocfg] starting from a label that belongs to its [inputs]
     will always result in a label in the static [output] list, or in a value.
   *)
  Definition terminator_outputs (term : terminator T) : list block_id
    := match term with
       | TERM_Ret v => []
       | TERM_Ret_void => []
       | TERM_Br v br1 br2 => [br1; br2]
       | TERM_Br_1 br => [br]
       | TERM_Switch v default_dest brs => default_dest :: map snd brs
       | TERM_IndirectBr v brs => brs
       | TERM_Resume v => []
       | TERM_Invoke fnptrval args to_label unwind_label => [to_label; unwind_label]
       | TERM_Unreachable => []
       end.

  Definition successors (bk : block T) : list block_id :=
    terminator_outputs (blk_term bk).

  Definition outputs (bks : ocfg T) : list block_id
    := fold_left (fun acc bk => acc ++ successors bk) bks [].

  Lemma raw_id_eq_dec : forall (x y : raw_id), {x = y} + {x <> y}.
  Proof.
    intros. destruct (Eqv.eqv_dec_p x y); auto.
  Qed.

  Definition raw_id_in := in_dec raw_id_eq_dec.

  (* Test whether b ∈ successors(bk), i.e.
  [is_predecessor b bk] iff [bk] is a predecessor to [b].
   *)
  Definition is_predecessor (b : block_id) (bk : block T) : bool :=
    if raw_id_in b (successors bk) then true else false.

  (* Computes the set of predecessors of [b] in [G] *)

  Definition predecessors (b : block_id) (G : ocfg T) : list block_id :=
    fold_left (fun acc bk => if is_predecessor b bk then bk.(blk_id) :: acc else acc) G [].

  (** * well-formed
      All labels in an open cfg are distinct.
      Quite natural sanity condition ensuring that despite the representation of
      the open cfg as a list of block, the order of the blocks in this list is
      irrelevant.
   *)
  Definition wf_ocfg_bid (bks : ocfg T) : Prop :=
    list_norepet (inputs bks).

  (** * no reentrance
      Generally speaking, all blocks in an open cfg are mutually recursive,
      we therefore can never discard part of the graph without further assumption.
      We would however still like to capture the idea that two parts of the graph
      represent two distinct computations that are executed in sequence.
      This is expressed by observing that the second sub-graph cannot jump back
      into the first one, i.e. that the [outputs] of the former do not intersect
      with the [inputs] of the latter.

      Under this assumption, the first part of the graph can be safely discarded
      once the second part is reached: cf [DenotationTheory.denote_ocfg_app_no_edges] 
      notably.
   *)
  Definition no_reentrance (bks1 bks2 : ocfg T) : Prop :=
    outputs bks2 ⊍ inputs bks1.

  (** * no_duplicate_bid
      Checks that the inputs of two sub-graphs are disjoint. This condition ensures
      that the well formedness of the two computations entails the one of their join.
   *)
  Definition no_duplicate_bid (bks1 bks2 : ocfg T) : Prop :=
    inputs bks1 ⊍ inputs bks2.

  (** * independent
      While [no_reentrance] captures two sequential computations,
      [independent_flows] captures two completely disjoint sub-graphs.
      This typically allows us to reason in a modular fashion about
      the branches of a conditional.
   *)
  Definition independent_flows (bks1 bks2 : ocfg T) : Prop :=
    no_reentrance bks1 bks2 /\ 
    no_reentrance bks2 bks1 /\
    no_duplicate_bid bks1 bks2.

  Definition free_in_cfg (cfg : ocfg T ) (id : block_id) : Prop :=
    not (In id (inputs cfg)).

  Definition phi_sources (φ : phi T) : list block_id :=
    let '(Phi _ l) := φ in map fst l.

  (* Over a closed graph, phi nodes should expect exactly jumps from their predecessors:
     - For any block [bk] in the graph
     - For any phi node [phi] in this block
     - the sources of [phi] and the predecessors of [bk] are in bijection
   *)
  Definition wf_ocfg_phis (G : ocfg T) :=
    forall bk pred x phi,
      In bk G ->
      In (x,phi) bk.(blk_phis) ->
      (In pred (phi_sources phi) <-> In pred (predecessors bk.(blk_id) G)).

  Record wf_cfg (G : cfg T): Prop :=
    WF_CFG
      {
        wf_cfg_bid : wf_ocfg_bid G.(blks);
        wf_cfg_phis : wf_ocfg_phis G.(blks)
      }.

End LABELS_OPERATIONS.

Section DEF_SITES_OPERATIONS.

  Context {T : Set}.

  Definition def_sites_instr_id (id : instr_id) : list raw_id :=
    match id with
    | IId id => [id]
    | _ => []
    end.

  Definition def_sites_code {T} (c : code T) : list raw_id :=
    List.fold_right (fun '(id,_) acc => match id with | IId id => id :: acc | _ => acc end) [] c.


End DEF_SITES_OPERATIONS.

