Require Import List.
Import ListNotations.

From Vellvm Require Import
     Utils.Util
     Syntax.CFG
     Syntax.DynamicTypes
     Syntax.LLVMAst
     Syntax.AstLib
     Syntax.Scope
     Analysis.Dom
     Analysis.DomKildall.

(* Note : Would it make sense to define a modular notion of dominance tree?
   A.k.a. : Can we define the dominance tree on an open cfg parameterized by
   an entry point (or an entry interface ?).
 *)

(** * GRAPH instance for dominance calculation *)

Definition mem_id (g:cfg dtyp) (u: block_id): Prop :=
  match find_block (blks g) u with
  | Some _ => True
  | _ => False
  end.

Definition succ_id (g:cfg dtyp) (u: block_id) (v: block_id) : Prop :=
  match find_block (blks g) u with
  | None => False
  | Some i => In v (successors i)
  end.

Definition succ_id_cmp (g:cfg dtyp) (u: block_id): list block_id :=
  match find_block (blks g) u with
  | None => []
  | Some i => successors i
  end.

Definition inputs_cfg (g : cfg dtyp) : list block_id :=
  inputs g.(blks).

Module idGraph <: GRAPH.
  Definition t := cfg dtyp.
  Definition V := block_id.
  Definition eq_dec_V := raw_id_eq_dec.
  Definition entry (g : cfg dtyp) := init g.
  Definition edge := succ_id.
  Definition mem := mem_id.
End idGraph.

Module idGraphCmp <: GRAPH_CMP idGraph.
  Definition succs   := succ_id_cmp.
  Definition enum_vs := inputs_cfg.
End idGraphCmp.

(** Instantiate the dominance spec for this graph *)
Module Export Dominance := Dom.Spec idGraph.
Module Export Kildall := AlgdomKildall AstLib.RawIDOrd idGraph idGraphCmp.

