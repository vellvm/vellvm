From Coq Require Import
     Morphisms.

Require Import List.
Import ListNotations.
Require Import ZArith.

From ITree Require Import
     ITree
     Basics.Monad
     Eq.Eq.

From Vellvm Require Import
     Syntax.Scope
     Syntax.LLVMAst
     Syntax.CFG
     Syntax.DynamicTypes
     Transformations.Peephole.

Import ListSet.

Remove Hints Eqv.EqvWF_Build : typeclass_instances.

Set Implicit Arguments.
Set Strict Implicit.

Import ListNotations.
Open Scope bool.

(* NOTE: Might be worse it to represent [ocfg] as sets of blocks rather than lists, with an efficient implementation of sets *)

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

  Definition fusion_blocks (b_s b_t : block dtyp) : block dtyp :=
    {|
    blk_id         := b_s.(blk_id);
    blk_phis       := b_s.(blk_phis);
    blk_code       := b_s.(blk_code) ++ phi_to_code b_t.(blk_phis) ++ b_t.(blk_code);
    blk_term       := b_t.(blk_term);
    blk_comments   := None (* TODO: proper propagation of comments *)
    |}.

  (* Let's start easy: we perform at most one fusion.
     To perform all available fusions we need to be a bit more clever w.r.t. to termination.
   *)
  Fixpoint loop_fusion_aux (G : ocfg dtyp) (bks : ocfg dtyp) : ocfg dtyp :=
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
          if length (predecessors b_t G) =? 1 
          then (fusion_blocks bk_s bk_t) :: ((G ∖ bk_s) ∖ bk_t)
          else loop_fusion_aux G bks
        | None => loop_fusion_aux G bks
        end
      | _ => loop_fusion_aux G bks
      end
    end.

  Definition loop_fusion : ocfg dtyp -> ocfg dtyp :=
    fun G => loop_fusion_aux G G.

End LoopFusion.

