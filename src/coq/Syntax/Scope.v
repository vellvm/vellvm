(* begin hide *)
From Coq Require Import
     List.
Import ListNotations.
From stdpp Require Import fin_maps fin_map_dom gmap mapset.
From Vellvm Require Import
     Numeric.Coqlib
     Utilities
     Syntax.LLVMAst
     Syntax.AstLib
     Syntax.CFG
     Syntax.TypToDtyp.

(* end hide *)

(** * Scoping
    We define through this file several functions and predicates having to do with the scope
    of VIR programs, w.r.t. both block identifiers and local variables.
    We unfortunately inherit from LLVM IR a fully named representation of variables, forcing
    on us fairly heavy sanity checks.
    - [inputs]: input labels of an [ocfg]
    - [outputs]: output labels of an [ocfg]
    - [wf_ocfg_bid]: no duplicate block identifiers
    - [uses]: use sites of pieces of syntax
    - [def_sites]: definition sites of pieces of syntax
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
  Definition inputs (ocfg : @ocfg T) := dom ocfg.

  (** * outputs
     Collect the list of output labels in an open control flow graph.
     Denoting an [ocfg] starting from a label that belongs to its [inputs]
     will always result in a label in the static [output] list, or in a value.
   *)
  Definition terminator_outputs (term : terminator T) : gset block_id
    := match term with
       | TERM_Ret v => ∅
       | TERM_Ret_void => ∅
       | TERM_Br v br1 br2 => {[br1; br2]}
       | TERM_Br_1 br => {[br]}
       | TERM_Switch v default_dest brs => {[default_dest]} ∪ list_to_set (map snd brs)
       | TERM_IndirectBr v brs => list_to_set brs
       | TERM_Resume v => ∅
       | TERM_Invoke fnptrval args to_label unwind_label => {[to_label; unwind_label]}
       | TERM_Unreachable => ∅
       end.

  Definition successors (bk : block T) : gset block_id :=
    terminator_outputs (blk_term bk).

  Definition outputs (bks : ocfg T) : gset block_id
    := map_fold (fun _ bk acc => acc ∪ successors bk) ∅ bks.

  (* Definition raw_id_in := elem_of_list_dec (A := raw_id). *)

  (* Test whether b ∈ successors(bk), i.e.
  [is_predecessor b bk] iff [bk] is a predecessor to [b].
   *)
  Definition is_predecessor (b : block_id) (bk : block T) : bool :=
    if decide (elem_of b (successors bk)) then true else false.

  (* Computes the set of predecessors of [b] in [G].
   *)

  Definition predecessors (b : block_id) (bks : ocfg T) : list block_id :=
    map_fold (fun k bk acc => if is_predecessor b bk then k :: acc else acc) [] bks.

  (* Now by construction since we represent graphs as finmaps *)
  (*
  (** * well-formed
      All labels in an open cfg are distinct.
      Quite natural sanity condition ensuring that despite the representation of
      the open cfg as a list of block, the order of the blocks in this list is
      irrelevant.
   *)
  Definition wf_ocfg_bid (bks : ocfg T) : Prop :=
    list_norepet (inputs bks).
   *)

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
    outputs bks2 ## inputs bks1.

  (** * no_duplicate_bid
      Checks that the inputs of two sub-graphs are disjoint. This condition ensures
      that the well formedness of the two computations entails the one of their join.
   *)
  Definition no_duplicate_bid (bks1 bks2 : ocfg T) : Prop :=
    inputs bks1 ## inputs bks2.

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
    ~ (elem_of id (inputs cfg)).

  Definition phi_sources (φ : phi T) : gset block_id :=
    let '(Phi _ l) := φ in list_to_set (map fst l).

  (* Over a closed graph, phi nodes should expect exactly jumps from their predecessors:
     - For any block [bk] in the graph
     - For any phi node [phi] in this block
     - the sources of [phi] and the predecessors of [bk] are in bijection
   *)
  Definition wf_ocfg_phis (bks : ocfg T) : Prop :=
    map_Forall
      (fun id bk => forall x φ pred, elem_of (x,φ) bk.(blk_phis) ->
                             (elem_of pred (phi_sources φ) <-> elem_of pred (predecessors id bks)))
      bks.

  Record wf_cfg (G : cfg T): Prop :=
    WF_CFG
      {
        (* wf_cfg_bid : wf_ocfg_bid G.(blks); *)
        wf_cfg_phis : wf_ocfg_phis G.(blks)
      }.

End LABELS_OPERATIONS.

(** Note : I'm toying with the concepts and trying to get familiar with everything.
    Once things are a bit settled, we need to use a more efficient implementation of
    sets ([MSetRBT.v] for instance)
 *)


(* From Coq Require Import ListSet. *)

(* Module SetNotations. *)

(*   Infix "+++" := (set_union raw_id_eq_dec) (right associativity, at level 60). *)
(*   Infix ":::" := (set_add raw_id_eq_dec) (right associativity, at level 60). *)
(*   Infix "∖"    := (set_diff raw_id_eq_dec) (right associativity, at level 60). *)
(*   Notation "∅" := (empty_set _). *)

(*   Definition set_flat_map {A} (f : A -> set raw_id) := *)
(*     fix flat_map (l:set A) : set raw_id := *)
(*       match l with *)
(*       | nil => nil *)
(*       | cons x t => (f x) +++ (flat_map t) *)
(*       end. *)

(* End SetNotations. *)

(* Import SetNotations. *)

Section REGISTER_OPERATIONS.

  Definition set_flat_map_list {A B} `{EqDecision B, Countable B} (f : A -> gset B) (l : list A) : gset B :=
    foldl (fun acc x => f x ∪ acc) ∅ l.

  Section Defs.

    (** * Definition sites
      Simple static collection of all variables assigned to in a piece of syntax.
     *)
    Class Def_sites (A : Type) := { def_sites: A -> gset raw_id }.

    #[global] Instance instr_id_defs : Def_sites instr_id :=
      {| def_sites := fun id =>
                        match id with
                        | IId id => {[id]}
                        | _ => ∅
                        end |}
    .

    #[global] Instance code_defs {T} : Def_sites (code T) :=
      {| def_sites := set_flat_map_list (fun x => def_sites (fst x)) |}.

    #[global] Instance block_def_sites {T} : Def_sites (block T) :=
      {| def_sites := fun bk => list_to_set (map fst bk.(blk_phis)) ∪
                             def_sites bk.(blk_code) |}.

    #[global] Instance ocfg_def_sites {T} : Def_sites (ocfg T) :=
      {| def_sites := map_fold (fun k bk acc => def_sites bk ∪ acc) ∅ |}.

    #[global] Instance cfg_def_sites {T} : Def_sites (cfg T) :=
      {| def_sites := fun cfg => def_sites cfg.(blks) |}.

  End Defs.

  Section Uses.

    (** * Use sites
        Simple static collection of all local variables read in a piece of syntax.
     *)

    Class Use_sites (A : Type) := { use_sites: A -> gset raw_id }.

    #[global] Instance ident_use_sites : Use_sites ident :=
      {| use_sites := fun id => match id with | ID_Local id => {[id]} | ID_Global _ => ∅ end |}.

    #[global] Instance exp_use_sites {T} : Use_sites (exp T) :=
      {| use_sites :=
          fix f e := match e with
                     | EXP_Ident id
                       => use_sites id

                     | EXP_Integer _
                     | EXP_Float _
                     | EXP_Double _
                     | EXP_Hex _
                     | EXP_Bool _
                     | EXP_Null
                     | EXP_Zero_initializer
                     | EXP_Cstring _
                     | EXP_Undef
                       => ∅

                     | OP_Conversion _ _ e _
                     | OP_ExtractValue (_,e) _
                     | OP_Freeze (_,e)
                       => f e

                     | OP_IBinop _ _ e1 e2
                     | OP_ICmp _ _ e1 e2
                     | OP_FBinop _ _ _ e1 e2
                     | OP_FCmp _ _ e1 e2
                     | OP_ExtractElement (_,e1) (_,e2)
                     | OP_InsertValue (_,e1) (_,e2) _
                       => f e1 ∪ f e2

                     | OP_InsertElement (_,e1) (_,e2) (_,e3)
                     | OP_ShuffleVector (_,e1) (_,e2) (_,e3)
                     | OP_Select (_,e1) (_,e2) (_,e3)
                       => f e1 ∪ f e2 ∪ f e3

                     | EXP_Struct l
                     | EXP_Packed_struct l
                     | EXP_Array l
                     | EXP_Vector l
                       => set_flat_map_list (fun x => f (snd x)) l

                     | OP_GetElementPtr _ (_,e) l
                       => f e ∪ set_flat_map_list (fun x => f (snd x)) l
                     end
      |}.

    #[global] Instance texp_use_sites {T} : Use_sites (texp T) := {| use_sites := fun x => use_sites (snd x) |}.
    #[global] Instance option_use_sites {T} `{Use_sites T} : Use_sites (option T) := {| use_sites := fun x => match x with | Some e => use_sites e | None => ∅ end |}.

    #[global] Instance instr_use_sites {T} : Use_sites (instr T) :=
      {| use_sites := fun i => match i with
                            | INSTR_Op e => use_sites e
                            | INSTR_Call e l _ =>
                                use_sites (e:texp T) ∪
                                  set_flat_map_list (fun x => use_sites (fst x)) l
                            | INSTR_Load  _ e _
                              => use_sites e
                            | INSTR_Store e1 e2 _
                              => use_sites e1 ∪ use_sites e2
                            | INSTR_Alloca _ _
                            | INSTR_Fence _ _
                            | INSTR_AtomicCmpXchg _
                            | INSTR_AtomicRMW _
                            | INSTR_VAArg _ _
                            | INSTR_LandingPad
                            | INSTR_Comment _
                              => ∅
                            end
      |}.

    #[global] Instance code_use_sites {T} : Use_sites (code T) :=
      {| use_sites := set_flat_map_list (fun x => use_sites (snd x)) |}.

    #[global] Instance term_use_sites {T} : Use_sites (terminator T) :=
      {| use_sites := fun t => match t with
                               | TERM_Ret e
                               | TERM_Br e _ _
                               | TERM_IndirectBr e _
                               | TERM_Resume e
                                 => use_sites e

                               | TERM_Switch e _ l =>
                                 use_sites e

                               | TERM_Ret_void
                               | TERM_Br_1 _
                               | TERM_Unreachable
                                 => ∅

                               | TERM_Invoke _ l _ _ =>
                                 set_flat_map_list (fun x => use_sites (fst x)) l
                               end
      |}.

    #[global] Instance phi_use_sites {T} : Use_sites (phi T) :=
      {| use_sites := fun '(Phi _ l) => set_flat_map_list (fun x => use_sites (snd x)) l |}.

    #[global] Instance block_use_sites {T} : Use_sites (block T) :=
      {| use_sites bk :=
          set_flat_map_list (fun x => use_sites (snd x)) bk.(blk_phis)
        ∪ use_sites bk.(blk_code)
        ∪ use_sites bk.(blk_term) |}.

    #[global] Instance ocfg_use_sites {T} : Use_sites (ocfg T) :=
      {| use_sites := map_fold (fun k bk acc => use_sites bk ∪ acc) ∅ |}.

    #[global] Instance cfg_use_sites {T} : Use_sites (cfg T) :=
      {| use_sites := fun cfg => list_to_set cfg.(args) ∪ use_sites cfg.(blks) |}.

  End Uses.

End REGISTER_OPERATIONS.
