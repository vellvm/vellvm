Require Import Vminus.Util.
Require Import Vminus.Vminus.

(** ** Well-formed Control-flow Graphs *)

(** FULL: Given the abstract characterization of program points, we need to
    relate them to the control-flow instructions of the program's CFG.
    We do this via a collection of well-formedness predicates that
    ensure that each program point maps to a single instruction and
    that the instruction defines a unique local identifier.  (Thus
    satisfying the 'single static assignment' part of the SSA
    representation.)
 *)

(** TERSE:
    - Relate program points to the control-flow instructions.
    - Each pc maps to a single instruction.
    - Each instruction defines a unique uid.
*)

(** A module signature defining well-formed control-flow graphs. *)

Module Type CFG.
  Parameter t : Type.
  Local Notation cfg := t.

(** *** Basic parameters of the model *)

  (** Well-formed control-flow-graphs. *)

  Parameter wf_cfg : cfg -> Prop.

  (** Well-formed program points. *)

  Parameter wf_pc : cfg -> pc -> Prop.

  (** *** *)

  (** The entry block of the control-flow graph. *)

  Parameter entry_block : cfg -> lbl.

  (** Is the program point a block terminator? *)

  Parameter tmn_pc : cfg -> pc -> Prop.

  (** *** Program point properties *)

  (** Program points are associated with unique instructions. *)

  Parameter insn_at_pc : cfg -> pc -> insn -> Prop.
  
  Parameter fetch : cfg -> pc -> option insn.
  
  Definition uid_at_pc (g:cfg) (p:pc) (uid:uid) : Prop :=
    exists c, insn_at_pc g p (uid, c).


  Axiom insn_at_pc_fetch :
    forall g pc i, wf_cfg g ->
              insn_at_pc g pc i <-> fetch g pc = Some i.

  Axiom insn_at_pc_func : forall g, wf_cfg g ->
    functional (insn_at_pc g).

  Axiom uid_at_pc_inj : forall g, wf_cfg g ->
    injective (uid_at_pc g).

  Axiom wf_pc_insn : forall g, wf_cfg g ->
    forall p, wf_pc g p -> exists i, insn_at_pc g p i.

  (** *** Block properties *)

  (** There is an instruction in the entry block. *)

  Axiom wf_entry : forall g, wf_cfg g ->
    wf_pc g (block_entry (entry_block g)).

  (** Every block has a terminator. *)

  Axiom wf_pc_tmn : forall g, wf_cfg g ->
    forall p, wf_pc g p -> exists p', tmn_pc g p' /\ le_pc p p'.

  (** There are no "gaps" in the pc labels. *)

  Axiom wf_pc_le_tmn : forall g, wf_cfg g ->
    forall p', tmn_pc g p' -> forall p, le_pc p p' -> wf_pc g p.

End CFG.
