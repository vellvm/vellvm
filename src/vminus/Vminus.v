(** * Vminus: A Simple SSA Intermediate Representation *)

(** FULL: This file defines the syntax and semantics for Vminus, an
    intermediate representation that is intended to capture the
    essence of LLVM's IR.  In particular, this language represents
    code as a _control flow graph_ whose blocks contain instructions
    in _static single assignment_ form.  This means that each
    instruction _defines_ (at most) one local identifier and that
    those identifiers are _immutable_.  To make this work in practice,
    SSA representations introduce the notation of _phi functions_,
    whose value is determined by the run-time control flow of the
    program.

    To support mutable state, Vminus also has Imp-style global
    identifiers.
*)

(** TERSE: Vminus is a highly simplified model of the LLVM IR that 
    features:
    - programs represented as _control flow graphs_ 
    - SSA _single static assignment_ form
      - uniquely defined _immutable local identifiers_ 
      - _phi functions_ 
    - Mutable, global state with [load] and [store] operations, as in IMP.
*)

Require Import Arith List.
Import ListNotations.

Require Import Vminus.Atom Vminus.Dom Vminus.Env Vminus.Imp Vminus.Util.

(* ####################################################### *)
(** ** Vminus Overview *)

(** See the course slides for a high-level overview of the concepts of
    the Vminus IR.

    The remainder of this section defines the syntax, operational
    semantics, and typing (well-formedness) rules for Vminus in Coq.  
*)


(* ####################################################### *)
(** *** Vminus labels, identifiers, and addresses.  *)


(** Basic block labels *)

(* QuickChick Note: Setting transparent ascription for Lbl and Uid 
   because they cannot be generated outside of the module. To refactor.
*)

(* Module Lbl : ATOM := Atom. *)
Module Lbl := Atom.
Notation lbl := Lbl.t.

Definition eq_dec_lbl : forall l1 l2 : lbl, {l1 = l2} + {~(l1 = l2)}.
Proof. apply Atom.eq_dec. Defined.
  
(** Local unique identifiers *)

(* Module Uid : ATOM := Atom. *)
Module Uid := Atom.
Notation uid := Uid.t.

Definition eq_dec_uid : forall uid1 uid2 : uid, {uid1 = uid2} + {~(uid1 = uid2)}.
Proof. apply Atom.eq_dec. Defined.

(** Mutable (integer) addresses *)

(* HIDE: Note, cannot ascribe Var : ATOM because var fails to
   be considered equivalent to Imp.id  *)
Module Addr := Atom. 
Notation addr := Addr.t.

Definition eq_dec_addr :
  forall addr1 addr2 : addr, {addr1 = addr2} + {~(addr1 = addr2)}.
Proof. apply Atom.eq_dec. Defined.


(** *** Values and Binary Operations *)

(** Values are just local identifiers or natural numbers *)

Inductive val : Set :=
 | val_uid  : uid -> val
 | val_nat : nat -> val.

Definition eq_dec_val: forall val1 val2: val, {val1 = val2} + {~(val1 = val2)}.
Proof.
  intros [uid1 | n1] [uid2 | n2];
    try solve [right; intros H; inversion H].
  destruct (eq_dec_uid uid1 uid2) as [uid_eq | uid_neq];
    try solve [right; intros H; inversion H; apply uid_neq; trivial];
    left; rewrite uid_eq; reflexivity.
  destruct (Nat.eq_dec n1 n2) as [n_eq | n_neq];
    try solve [right; intros H; inversion H; apply n_neq; trivial];
    left; rewrite n_eq; reflexivity.
Defined.

(** All Vminus operations are binary arithmetic forms.  There are no
    unary operations, nor are there assembly-language-like [move]
    instructions.
*)

Inductive bop : Set := 
 | bop_add 
 | bop_sub 
 | bop_mul
 | bop_eq  
 | bop_le  
 | bop_and.

Definition eq_dec_bop: forall bop1 bop2: bop, {bop1 = bop2} + {~(bop1 = bop2)}.
Proof.
  intros [] [];
    try solve [right; intros H; inversion H];
    try solve [left; reflexivity].
Defined.

(** *** Basic block terminators *)

(** Each basic block is a sequence of commands (defined next) ending
    in a _terminator_, which is just a control flow operation.  
    Terminators cannot appear in the middle of a well-formed basic block.   
*)

Inductive tmn : Set :=
| tmn_jmp : lbl -> tmn                  (* unconditional jump *)
| tmn_cbr : val -> lbl -> lbl -> tmn    (* conditional branch *)
| tmn_ret : tmn.                        (* return *)

Definition eq_dec_tmn: forall tmn1 tmn2: tmn, {tmn1 = tmn2} + {~(tmn1 = tmn2)}.
Proof.
  intros [jmp_lbl1 | v1 if1 else1 |]
         [jmp_lbl2 | v2 if2 else2 |];
    try solve [right; intros H; inversion H];
    try solve [left; reflexivity].
  destruct (eq_dec_lbl jmp_lbl1 jmp_lbl2) as [Heq | Hneq];
    try solve [right; intros H; inversion H; apply Hneq; trivial];
    try solve [left; subst; reflexivity].
  destruct (eq_dec_val v1 v2) as [v_eq | v_neq];
    try solve [right; intros H; inversion H; apply v_neq; trivial];
    try solve [left; subst; reflexivity].
  destruct (eq_dec_lbl if1 if2) as [if_eq | if_neq];
    try solve [right; intros H; inversion H; apply if_neq; trivial];
    try solve [left; subst; reflexivity].
  destruct (eq_dec_lbl else1 else2) as [else_eq | else_neq];
    try solve [right; intros H; inversion H; apply else_neq; trivial];
    try solve [left; subst; reflexivity].
Defined.  

(** *** Commands *)

(** Vminus has only a few commands: binary operations, phi nodes,
terminators, and [load] and [store] operations. *)

(** Each [phiarg] associates a value with a predessor block. *)

Definition phiarg := (lbl * val)%type.

Definition eq_dec_phiarg:
  forall phiarg1 phiarg2: phiarg, {phiarg1 = phiarg2} + {~(phiarg1 = phiarg2)}.
Proof.
  intros [lbl1 val1] [lbl2 val2].
  destruct (eq_dec_lbl lbl1 lbl2) as [lbl_eq | lbl_neq];
    try solve [right; intros H; inversion H; apply lbl_neq; trivial];
    try solve [left; subst; reflexivity].
  destruct (eq_dec_val val1 val2) as [val_eq | val_neq];
    try solve [right; intros H; inversion H; apply val_neq; trivial];
    try solve [left; subst; reflexivity].
Defined.

Definition eq_dec_list_phiarg:
  forall l1 l2 : list phiarg, {l1 = l2} + {~(l1 = l2)}.
Proof.
  induction l1 as [| pa1 phiargs1].
  - destruct l2; [left; reflexivity | right; intros H; inversion H].
  - destruct l2 as [| pa2 phiargs2];
      try solve [right; intros H; inversion H].
    destruct (eq_dec_phiarg pa1 pa2) as [pa_eq | pa_neq];
      try solve [right; intros H; inversion H; apply pa_neq; trivial];
      try solve [left; subst; reflexivity].
    subst.
    specialize IHphiargs1 with (l2 := phiargs2).
    destruct IHphiargs1 as [phiargs_eq | phiargs_neq];
      try solve [right; intros H; inversion H; apply phiargs_neq; trivial].
    left; subst; reflexivity.
Defined.
    
(** Vminus Commands *)

Inductive cmd : Set :=
| cmd_bop   : bop -> val -> val -> cmd
| cmd_phi   : list phiarg -> cmd
| cmd_tmn   : tmn -> cmd
| cmd_load  : addr -> cmd
| cmd_store : addr -> val -> cmd.

Definition eq_dec_cmd: forall cmd1 cmd2: cmd, {cmd1 = cmd2} + {~(cmd1 = cmd2)}.
Proof.
  intros [bop1 val1 right_val1 | phiargs1 | tmn1 | addr1 |
          addr1 val1]
         [bop2 val2 right_val2 | phiargs2 | tmn2 | addr2 |
          addr2 val2];
    try solve [right; intros H; inversion H];
    try (destruct (eq_dec_list_phiarg phiargs1 phiargs2)
          as [phiargs_eq | phiargs_neq];
         try solve [left; subst; reflexivity];
         try solve [right; intros H; inversion H; apply phiargs_neq; trivial]);
    try (destruct (eq_dec_tmn tmn1 tmn2) as [tmn_eq | tmn_neq];
         try solve [left; subst; reflexivity];
         try solve [right; intros H; inversion H; apply tmn_neq; trivial]);
    try (destruct (eq_dec_addr addr1 addr2) as [addr_eq | addr_neq];
         try solve [left; subst; reflexivity];
         try solve [right; intros H; inversion H; apply addr_neq; trivial];
         try
           (destruct (eq_dec_val val1 val2) as [val_eq | val_neq];
            try solve [right; intros H; inversion H;
                       apply val_neq; trivial];
            try solve [left; subst; reflexivity])).
  - destruct (eq_dec_bop bop1 bop2) as [bop_eq | bop_neq];
      try solve [right; intros H; inversion H; apply bop_neq; trivial].
    destruct (eq_dec_val val1 val2) as [val_eq | val_neq];
      try solve [right; intros H; inversion H; apply val_neq; trivial];
      destruct (eq_dec_val right_val1 right_val2)
        as [right_val_eq | right_val_neq];
      try solve [right; intros H;
                 inversion H; apply right_val_neq; trivial].
    subst; left; reflexivity.
Defined.  

(** An instruction associates a unique local identifier with one of the
    above commands. *)

Definition insn := (uid * cmd)%type.

Definition eq_dec_insn:
  forall insn1 insn2: insn, {insn1 = insn2} + {~(insn1 = insn2)}.
Proof.
  intros [uid1 cmd1] [uid2 cmd2].
  destruct (eq_dec_uid uid1 uid2) as [uid_eq | uid_neq];
    try solve [right; intros H; inversion H; apply uid_neq; trivial].
  destruct (eq_dec_cmd cmd1 cmd2) as [cmd_eq | cmd_neq];
    try solve [right; intros H; inversion H; apply cmd_neq; trivial].
  subst; left; reflexivity.
Defined. 


(* ####################################################### *)

(** *** Useful information about instructions *)

Definition insn_uses (i:insn) : list val :=
(* FOLD *)
  match i with
    | (_, cmd_bop _ v1 v2) => [v1; v2]
    | (_, cmd_tmn (tmn_cbr v _ _)) => [v]
    | (_, cmd_store _ v) => [v]
(* TODO:     | (_, cmd_phi pas) => map (@snd _ _) pas *)
    | _ => []
  end.
(* /FOLD *)

Definition insn_lbls (i:insn) : list lbl :=
(* FOLD *)
  match i with 
    | (_, cmd_tmn (tmn_jmp l)) => [l]
    | (_, cmd_tmn (tmn_cbr _ l1 l2)) => [l1; l2]
    | _ => []
  end.
(* /FOLD *)

Definition insn_phis (i:insn) : list phiarg :=
(* FOLD *)
  match i with
    | (_, cmd_phi pas) => pas
    | _ => []
  end.
(* /FOLD *)

Definition is_tmn (i:insn) : Prop := 
(* FOLD *)
  match i with (_, cmd_tmn _) => True | _ => False end.
(* /FOLD *)

Definition is_phi (i:insn) : Prop := 
(* FOLD *)
  match i with (_, cmd_phi _) => True | _ => False end.
(* /FOLD *)

Definition defs_uid (i:insn) : Prop :=
(* FOLD *)
  match i with
    | (_, cmd_tmn _) | (_, cmd_store _ _) => False | _ => True
  end.
(* /FOLD *)

(** ** Program points *)

(** FULL: Vminus programs are structured into _control-flow graphs_
    (CFG), which, conceptually, are graphs whose _nodes_ are basic
    blocks and whose _edges_ are determined by the control structure
    of the program.  A block [b1] terminated by a jump to [b2]
    requires and edge from [b1] to [b2] in the CFG.  Similarly a block
    terminated by a branch to either [b2] or [b3] has two successors
    edges.

    To characterize this structure abstractly, we define a notion of
    _program point_ [pc], which is a location of an instruction in the
    control-flow graph.  A [pc] is given by a block label and offset.
    The program points within a single block increase by offset order;
    program points in two different blocks are connected by the
    control structure as determined above.
*)
(** TERSE: Vminus programs are _control-flow graphs_ that have:
    - _Program points_ [pc] given by block labels and an offset.
    - Successor edges determined by offset within a block and the control flow operations between blocks. 
*)   

(** Program points (a.k.a. "program counters"). *)

Definition pc := (lbl * nat)%type.
Definition lbl_of : pc -> lbl       := @fst _ _.

(** Increment a [pc] _within_ a block. *)

Definition incr_pc (p:pc) : pc :=
  let (l, n) := p in (l, S n).

(** (Total) Ordering on [pc]s within the same block *)

Inductive le_pc : pc -> pc -> Prop :=
| let_pc_intro : forall l n1 n2,
    n1 <= n2 -> le_pc (l, n1) (l, n2).

Definition lt_pc (p1 p2:pc) : Prop :=
  le_pc p1 (incr_pc p2).

Definition eq_dec_pc: forall p1 p2: pc, {p1 = p2} + {~(p1 = p2)}.
Proof.
  intros (lbl1, offset1) (lbl2, offset2).
  destruct (eq_dec_lbl lbl1 lbl2) as [lbl_eq | lbl_neq];
    try solve [right; intros H; inversion H;
               exfalso; apply lbl_neq; trivial];
  destruct (Nat.eq_dec offset1 offset2) as [offset_eq | offset_neq];
    try solve [right; intros H; inversion H; apply offset_neq; trivial];
    left; subst; reflexivity.
Defined.

(** The entry point of a block is offset [0]. *)

Definition block_entry (l:lbl) : pc := (l, 0).
Definition entry_of_pc (p:pc)  : pc := block_entry (fst p).


(** * COMMENTED OUT *)
(*
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
*)

(** * Commented out 
(** ** Vminus Operational Semantics *)
Module Make (Import Cfg:CFG).

Module Opsem.

  (** *** The state of a Vminus program: *)

  Module Locals := Make_Env(Uid).
  Module Memory := Make_Env(Addr).
  Notation loc := (Locals.t (option nat)).
  Notation mem := (Memory.t nat).
  Notation update := Locals.update.

  Record state := mkst { st_mem  : mem
                       ; st_pc   : pc
                       ; st_loc  : loc
                       ; st_ppc  : pc     (* predecessor pc *)
                       ; st_ploc : loc    (* predecessor locals *) 
                       }.

  (** *** Evaluating values. *)

  (** Simply look up the uid in the locals state. (May fail!) *)
  
  Definition eval_val (loc:loc) (v:val) : option nat :=
    match v with
      | val_nat n => Some n
      | val_uid i => loc i
    end.

  (** *** Evaluating binary operations. *)

  Definition b2n (b:bool) := if b then 1 else 0.
  Definition n2b (n:nat) := if n then false else true.

  Definition bop_denote (bop:bop) : nat -> nat -> nat :=
    match bop with
      | bop_add => plus
      | bop_sub => minus
      | bop_mul => mult
      | bop_eq => fun n m => b2n (beq_nat n m)
      | bop_le => fun n m => b2n (leb n m)
      | bop_and => fun n m => b2n (n2b n && n2b m)
    end.

  Definition eval_bop (loc:loc) (bop:bop) (v1 v2:val) : option nat :=
    match eval_val loc v1, eval_val loc v2 with
      | Some n1, Some n2 => Some (bop_denote bop n1 n2) 
      | _, _ => None
    end.

  (** *** Phi nodes *)
  (** Look up the predecessor label in the phi arg list. *)

  Definition eval_phi (loc:loc) (l:lbl) (pas:list phiarg) 
    : option nat :=
    match assoc Lbl.eq_dec l pas with
      | Some v => eval_val loc v
      | None => None
    end.

  (** *** Control transfers. *)
  
  (** Given the current locals and the terminator, determine
      the label of the next block to jump to. *)

  Definition eval_tmn (loc:loc) (t:tmn) : option lbl :=
    match t with
      | tmn_jmp l => Some l
      | tmn_cbr v l1 l2 =>
          match eval_val loc v with
            | Some n => Some (if n then l2 else l1)
            | None => None
          end
      | _ => None
    end.

  (** *** Small-step, relational operational semantics *)

  Inductive step (g:Cfg.t) : state -> state -> Prop :=

  | step_bop : forall mem pc loc bop v1 v2 uid n ppc ploc,
      insn_at_pc g pc (uid, cmd_bop bop v1 v2) ->
      Some n = eval_bop loc bop v1 v2 ->
      step g (mkst mem pc loc ppc ploc) 
             (mkst mem (incr_pc pc) 
                       (update loc uid (Some n)) ppc ploc)

  (** Evaluate the right-hand side in the predecessor's 
     local environment. [lbl_of ppc] is the control-flow 
     edge that we jumped from. *)
  | step_phi : forall mem pc loc pas uid n ppc ploc,
      insn_at_pc g pc (uid, cmd_phi pas) ->
      Some n = eval_phi ploc (lbl_of ppc) pas ->
      step g (mkst mem pc loc ppc ploc)
             (mkst mem (incr_pc pc) 
                       (update loc uid (Some n)) ppc ploc)

  (** Find the successor block (if any), update the pc. 
      Record the current pc and locals as the "predecessor" state. *)
  | step_tmn : forall mem pc l' loc tmn uid ppc ploc, 
      insn_at_pc g pc (uid, cmd_tmn tmn) ->
      Some l' = eval_tmn loc tmn ->
      step g (mkst mem pc loc ppc ploc)
             (mkst mem (block_entry l') loc pc loc)

  (** Loads and stores **)
  | step_load : forall mem pc loc uid addr ppc ploc,
      insn_at_pc g pc (uid, cmd_load addr) ->
      step g (mkst mem pc loc ppc ploc)
             (mkst mem (incr_pc pc) 
                       (update loc uid (Some (mem addr))) ppc ploc)

  | step_store : forall mem pc loc uid addr v n ppc ploc,
      insn_at_pc g pc (uid, cmd_store addr v) ->
      Some n = eval_val loc v ->
      step g (mkst mem pc loc ppc ploc)
             (mkst (Memory.update mem addr n) 
                   (incr_pc pc) loc ppc ploc).
  



 (** Definition of the initial state. *)

  Definition init_state (g:Cfg.t) (m: mem) : state :=
    (mkst m
          (block_entry (entry_block g))
          (Locals.empty None)
          (block_entry (entry_block g))
          (Locals.empty None)).

End Opsem.


(** ** Typing *)
(** FULL: The only ways in which a Vminus program can "go wrong" are
    by accessing a local variable that hasn't been defined or jumping
    to a label that isn't in the CFG.  Therefore, its typing
    constraints ensure that each instruction only mentions local
    identifiers that are in scope according to the domination
    structure of the control-flow graph and that all mentioned labels
    are associated with blocks defined in the CFG.  *)

(** TERSE:
    The type system for Vminus ensures that:
    - All local variables are defined.
    - All jump targets are legal.
*)

Module Typing.


  (** *** GRAPH instance for dominance calculation *)

  (** Edge relation *)

  Inductive succ_pc (g:Cfg.t) : pc -> pc -> Prop :=
  | succ_pc_S : forall p,
      succ_pc g p (incr_pc p)
  | succ_pc_J : forall p l i,
      insn_at_pc g p i ->
      In l (insn_lbls i) ->
      succ_pc g p (block_entry l).

  (** Graph of program points *)

  Module PcGraph <: GRAPH.
    Definition t := Cfg.t.
    Definition V := pc.
    Definition entry g := block_entry (entry_block g).
    Definition Succ := succ_pc.
    Definition Mem := wf_pc.
  End PcGraph.

  Module Export Dom := Dom.Spec PcGraph.

  (** *** Definitions for Well-formed SSA programs. *)

  (** FULL: Most of the Vminus instructions define the uid associated
  with their program point.  Some (like [store] and the [tmn]s)
  do not. *)
  (** TERSE: The command at the given [pc] defines uid. *)

  Definition def_at_pc (g:Cfg.t) (p:pc) (uid:uid) : Prop :=
    exists c, insn_at_pc g p (uid, c) /\ defs_uid (uid, c). 

  (** The definition of [uid] strictly dominates the pc. *)
 
  Definition uid_sdom_pc (g:Cfg.t) (uid:uid) (p:pc) : Prop :=
    exists p', def_at_pc g p' uid /\ SDom g p' p.

  (** All uses of a [uid] must be strictly dominated by
      their definitions. *)

  Definition wf_use (g:Cfg.t) (i:insn) (p:pc) : Prop :=
    forall uid, In (val_uid uid) (insn_uses i) -> uid_sdom_pc g uid p.

  (** All jump targets must be legal block labels. *)

  Definition wf_lbl (g:Cfg.t) (i:insn) : Prop :=
    forall l, In l (insn_lbls i) -> wf_pc g (block_entry l).

  (** *** Well-formed phi nodes *)

  (**  Consider [ %x = phi [lbl1:v1, ...,lbln:vn] ].  This is well formed
       when every predecessor block with terminator program point p' 
       has a label associated with value v.  Moreover, if v is a uid then
       the definition of the uid strictly dominates p'.
  *)

  Definition wf_phi_args (g:Cfg.t) (i:insn) (p:pc) : Prop :=
    forall pred, succ_pc g pred (entry_of_pc p) ->
      (exists v, In (lbl_of pred, v) (insn_phis i)) /\
      (forall uid, In (lbl_of pred, val_uid uid) (insn_phis i) -> 
          uid_sdom_pc g uid pred).

  Definition wf_phi_pred (g:Cfg.t) (i:insn) (p:pc) : Prop :=
    forall l v, In (l, v) (insn_phis i) ->
      (exists pred, succ_pc g pred (entry_of_pc p) /\ lbl_of pred = l).

  Definition wf_phi (g:Cfg.t) (i:insn) (p:pc) : Prop :=
    is_phi i -> wf_phi_args g i p
             /\ wf_phi_pred g i p
             /\ insn_phis i <> [].

  (** *** Well-formed instructions *)

  Inductive wf_insn (g:Cfg.t) : insn -> pc -> Prop :=
  | wf_insn_intro : forall i p,
      wf_use g i p ->
      wf_lbl g i ->
      wf_phi g i p ->
      wf_insn g i p.

  Inductive wf_prog (g:Cfg.t) : Prop :=
  | wf_prog_intro : forall
      (Hwfcfg : wf_cfg g)
      (Hwfis : forall p i, insn_at_pc g p i -> wf_insn g i p)
      (Hwftmn : forall p' i, tmn_pc g p' -> insn_at_pc g p' i -> is_tmn i)
      (Hwfentry : forall p, ~ succ_pc g p (block_entry (entry_block g))),
      wf_prog g.

End Typing.

(** ** Correctness *)

Module OpsemCorrect.
  Import Typing Opsem.

(** First, some utilities. *)
(* HIDE *)
(*
  Lemma insn_at_pc_inj : forall g, wf_cfg g ->
    injective (insn_at_pc g).
(* FOLD *)
  Proof.
    intros g Hwfc. specialize (uid_at_pc_inj g Hwfc).
    unfold injective, uid_at_pc. intros.
    destruct b; eauto.
  Qed.
(* /FOLD *)
*)
(* /HIDE *)

(* HIDE *)
  (* LATER: Arguably the next two lemmas could go in the CFG module. *)
(* /HIDE *)

  Lemma uid_at_pc_func : forall g, wf_cfg g ->
    functional (uid_at_pc g).
(* FOLD *)
  Proof.
    intros g Hwfc. specialize (insn_at_pc_func g Hwfc).
    unfold functional, uid_at_pc. intros.
    destruct H0 as [c1 ?]. destruct H1 as [c2 ?].
    cut ((b1,c1) = (b2,c2)). inversion 1; auto.
    eauto.
  Qed.
(* /FOLD *)

  Lemma eq_pc_uid : forall g pc id1 id2 c1 c2,
    wf_prog g ->
    insn_at_pc g pc (id1, c1) ->
    insn_at_pc g pc (id2, c2) ->
    id1 = id2.
(* FOLD *)
  Proof.
    intros. inversion H. pose proof (uid_at_pc_func g Hwfcfg).
    unfold functional in H2. eapply H2; red; eauto.
  Qed.
(* /FOLD *)

(* HIDE *)
  Unset Printing Records.
(* /HIDE *)


  (** *** Dominance relation *)

  (** A more convenient form for typing rules *)

  Lemma uid_sdom_step : forall g uid' uid pc1 pc2 c,
    wf_prog g ->
    uid' <> uid ->
    wf_pc g pc2 ->
    succ_pc g pc1 pc2 ->
    insn_at_pc g pc1 (uid, c) ->
    uid_sdom_pc g uid' pc2 ->
    uid_sdom_pc g uid' pc1.
(* FOLD *)
  Proof.
    unfold uid_sdom_pc. 
    intros g uid' uid pc1 pc2 c Hwff Hneq Hpc Hsucc Hi [pc' [Hdef Hdom]]. 
    exists pc'. split. assumption. 
    split. contradict Hneq. subst pc'. 
    destruct Hdef as [? [? ?]]; eapply eq_pc_uid; eauto. 
    inversion Hwff; eapply dom_step; eauto. 
  Qed.
(* /FOLD *)

  (** ** Progress & Preservation *)

  (** Extend well-formedness definitions to include all components of 
  the state. *)

  Definition wf_loc (g:Cfg.t) (p:pc) (loc:loc) : Prop :=
  forall uid, uid_sdom_pc g uid p -> exists n, loc uid = Some n.

  Definition at_entry (g:Cfg.t) (p:pc) : Prop :=
    entry_of_pc p = block_entry (entry_block g).

  Inductive wf_state (g:Cfg.t) : state -> Prop :=
  | wf_state_intro : forall st
      (Hwfpc: wf_pc g st.(st_pc))
      (Hwfloc: wf_loc g st.(st_pc) st.(st_loc))
      (Hwfppc: at_entry g st.(st_pc) \/ 
                 succ_pc g st.(st_ppc) (entry_of_pc st.(st_pc)))
      (Hwfploc: at_entry g st.(st_pc) \/ 
                  wf_loc g st.(st_ppc) st.(st_ploc)),
      wf_state g st.

  (** Initial state is well formed *)

  Lemma wf_init_state : 
    forall g m, wf_prog g ->
    wf_state g (init_state g m).
(* FOLD *)
  Proof.
    intros g m Hprog. inversion Hprog. 
    apply wf_entry in Hwfcfg.
    econstructor. auto.
    red. simpl. intros. red in H. destruct H as [? [? [? ?]]].
    red in H1. contradict H0.
    cut (In x [block_entry (entry_block g)]). simpl. intuition.
    eapply H1. econstructor. auto.
    left. unfold init_state, at_entry, entry_of_pc. auto.
    left. unfold init_state, at_entry, entry_of_pc. auto.
  Qed.
(* /FOLD *)  


  (** *** Progress helper lemmas. *)

  (** There are no phi nodes in the entry block. *)

  Lemma at_entry_not_phi : forall g st i,
    wf_prog g ->
    at_entry g st.(st_pc) ->
    insn_at_pc g st.(st_pc) i ->
    ~ is_phi i.
(* FOLD *)
   Proof.
     intros g st i Hprog Hentry Hinsn. 
     destruct Hprog as [_ ? _ ?].
     specialize (Hwfis _ _ Hinsn). inversion Hwfis; subst.
     intro Hphi. specialize (H1 Hphi). destruct H1 as [? [? ?]].
     destruct (insn_phis i) eqn:His. contradiction H3; auto.
     assert (In p (insn_phis i)) as Hin. rewrite His. left; auto.
     destruct p. apply H2 in Hin. destruct Hin as [pred [Hpred Ht0]].
     specialize (Hwfentry pred). contradict Hwfentry. 
     rewrite <- Hentry; auto.
   Qed.
(* /FOLD *)  

  (** In a well-formed program with well-formed locals, evaluating
  a value is never undefined. *)

  Lemma eval_val__wf_loc : forall g pc loc i v,
    wf_prog g ->
    wf_loc g pc loc ->
    insn_at_pc g pc i ->
    In v (insn_uses i) ->
    exists n, eval_val loc v = Some n.
(* FOLD *)
  Proof.
    intros ? ? ? ? v Hwff Hwfloc Hi ?. 
    destruct v as [uid | n].
    simpl. inversion Hwff as [_ ? _]. apply Hwfis in Hi. 
    destruct Hi as [? ? Huse]. specialize (Huse uid). 
    lapply Huse; auto.
    simpl; eauto.
  Qed.
(* /FOLD *)  

  (** ** Progress *)

  Definition FinalState (g:Cfg.t) (s:state) : Prop :=
    exists uid, insn_at_pc g s.(st_pc) (uid, cmd_tmn tmn_ret).
  
  Lemma progress : forall g s,
    wf_prog g -> wf_state g s ->
    FinalState g s \/ exists s', step g s s'.
(* FOLD *)
  Proof.
    intros g s Hwff Hwfs.
    inversion Hwfs as [? Hwfpc]; subst. inversion Hwff.
    pose proof (wf_pc_insn g Hwfcfg _ Hwfpc) as [[i c] Hi].
    rename s into j. set (s:=j) in *. destruct j. 
    destruct c.
  
    - (* Case "cmd_bop". *)
    eelim (eval_val__wf_loc) with (v:=v) (loc:=st_loc0); eauto; simpl; auto.
    eelim (eval_val__wf_loc) with (v:=v0) (loc:=st_loc0); eauto; simpl; auto.
    intros n1 Heqn1 n2 Heqn2.
    right. eexists. eapply step_bop; eauto. unfold eval_bop.
    rewrite Heqn1, Heqn2. reflexivity. 

    - (* Case "cmd_phi". *)
    right. specialize (Hwfis _ _ Hi). inversion Hwfis; subst.
    
    destruct Hwfppc as [|Hwfppc]. 
    exfalso; eapply at_entry_not_phi; eauto. simpl; trivial.
    destruct Hwfploc as [|Hwfploc]. 
    exfalso; eapply at_entry_not_phi; eauto. simpl; trivial.

    destruct (H1 I) as [Hphi _]. clear H1.
    specialize (Hphi st_ppc0 Hwfppc). destruct Hphi as [[v Hin] Hdom].

    cut (exists v, assoc Lbl.eq_dec (lbl_of st_ppc0) l = Some v). intros [v' Hv].
    cut (exists n, eval_val st_ploc0 v' = Some n). intros [n Hn].
    eexists. eapply step_phi. eauto. unfold eval_phi.
    rewrite Hv. rewrite Hn. reflexivity.
  
    destruct v' as [i' | n']. simpl in *. apply Hwfploc. apply Hdom. 
    eapply assoc_in. apply Hv. simpl; eauto.
    eapply in_assoc_some. apply Hin.
  
    - (* Case "cmd_tmn". *)
    destruct t0.
    * (*  SCase "tmn_jmp". *)
      right. eexists. eapply step_tmn. eauto. reflexivity.

    * (* SCase "tmn_cbr". *)
      cut (exists n, eval_val st_loc0 v = Some n). intros [n Heqn].
      right. eexists. eapply step_tmn. eauto. simpl. rewrite Heqn. reflexivity.
      eapply eval_val__wf_loc; eauto. simpl; auto.

    * (* SCase "tmn_ret". *)
      left. red; eauto. 

    - (* Case "cmd_load". *)
    right. eexists. apply step_load; eauto.

    - (* Case "cmd_store". *)
    right. cut (exists n1, eval_val st_loc0 v = Some n1). 
    intros [n1 Heqn1]. eexists. eapply step_store. eauto. eauto.
    eapply eval_val__wf_loc; eauto. simpl; auto.
  Qed.
(* /FOLD *)

  (** *** Some first steps towards preservation. *)

  Lemma wf_pc_incr : forall g p i,
    wf_prog g ->
    wf_pc g p ->
    insn_at_pc g p i ->
    ~ is_tmn i ->
    wf_pc g (incr_pc p).
(* FOLD *)
  Proof.
    intros. inversion H. 
    apply (wf_pc_tmn g Hwfcfg) in H0 as [pt [Ht Hle]].
    eapply wf_pc_le_tmn; eauto.
    inversion Hle; subst. destruct H0.
    contradict H2. eapply Hwftmn; eauto. 
    constructor; auto with arith.
  Qed.
(* /FOLD *)

  Lemma eval_tmn_in_lbls : forall l loc t uid,
    Some l = eval_tmn loc t -> In l (insn_lbls (uid, cmd_tmn t)).
(* FOLD *)
  Proof.
    intros.
    destruct t0; simpl in *.
    inversion H; auto.
    destruct (eval_val loc v). injection H. 
      destruct n; eauto.
      discriminate H. discriminate H.
  Qed.
(* /FOLD *)

  (** *** More preservation helpers*)

  Lemma not_def_sdom_step : forall g p1 p2 i uid,
    wf_prog g ->
    wf_pc g p2 ->
    insn_at_pc g p1 i ->
    ~ defs_uid i ->
    succ_pc g p1 p2 ->
    uid_sdom_pc g uid p2 ->
    uid_sdom_pc g uid p1.
(* FOLD *)
  Proof. 
    destruct i; intros. inversion H4 as [? [[? [? Ht]] ?]].
    eapply uid_sdom_step; eauto. 
    contradict Ht. subst t0. assert (x = p1). 
    inversion H; eapply uid_at_pc_inj; try red; eauto. subst x.
    replace (uid, x0) with (uid, c); trivial. 
    inversion H; eapply insn_at_pc_func; eauto.
  Qed.
(* /FOLD *)    

  Lemma wf_loc_succ : forall g p1 p2 loc uid n c,
   wf_prog g ->
   wf_pc g p2 ->
   insn_at_pc g p1 (uid, c) ->
   succ_pc g p1 p2 ->
   wf_loc g p1 loc ->
   wf_loc g p2 (update loc uid (Some n)).
(* FOLD *)
  Proof.
    intros. red; intros. destruct (Uid.eq_dec uid0 uid). subst.
    rewrite Locals.update_eq; eauto. reflexivity.
    rewrite Locals.update_neq; eauto. apply H3.
    eapply uid_sdom_step; eauto. 
  Qed.
(* /FOLD *)

  (** ** Preservation *)

  Lemma preservation : forall g s s',
    wf_prog g ->
    wf_state g s -> step g s s' -> wf_state g s'.
(* FOLD *)
  Proof.
    intros g _ s' Hwff [s Hwfpc Hwfloc] Hstep.
    inversion Hstep; subst; simpl in *.
  
    - (* Case "step_bop". *)
    assert (wf_pc g (incr_pc pc0)) as Hwfpc' by (eapply wf_pc_incr; eauto).
    constructor; simpl; try solve [destruct pc0; auto].
    eapply wf_loc_succ; eauto. constructor.

    - (* Case "step_phi". *)
    assert (wf_pc g (incr_pc pc0)) as Hwfpc' by (eapply wf_pc_incr; eauto).
    constructor; simpl; try solve [destruct pc0; auto].
    eapply wf_loc_succ; eauto. constructor.
  
    - (* Case "step_tmn". *)
    assert (wf_pc g (l', 0)) as Hwfpc'.
      inversion Hwff as [_ Hwfi _]. specialize (Hwfi _ _ H).
      inversion Hwfi. red in H2. apply H2. 
      eauto. eapply eval_tmn_in_lbls. eauto.

    assert (succ_pc g pc0 (l', 0)) as Hsucc.
      econstructor. eauto. eapply eval_tmn_in_lbls. eauto.
    constructor; simpl; eauto. red; intros. apply Hwfloc.
    eapply not_def_sdom_step; eauto.

    - (* Case "step_load". *)
    assert (wf_pc g (incr_pc pc0)) as Hwfpc' by (eapply wf_pc_incr; eauto).
    constructor; simpl; try solve [destruct pc0; auto].
    eapply wf_loc_succ; eauto. constructor.

    - (* Case "step_store". *)
    assert (wf_pc g (incr_pc pc0)) as Hwfpc' by (eapply wf_pc_incr; eauto).
    constructor; simpl; try solve [destruct pc0; auto].
    red; intros. apply Hwfloc. eapply not_def_sdom_step; eauto. constructor.
  Qed.
(* /FOLD *)  

(* HIDE *)
Lemma step_deterministic : forall g s s1 s2, wf_prog g -> wf_state g s ->
  step g s s1 -> step g s s2 -> s1 = s2.
(* FOLD *)
Proof.
    intros g s s1 s2 Hwfprog Hwfs Hs1 Hs2.
    inversion Hwfs as [? Hwfpc]; subst. inversion Hwfprog.
    inversion Hs1; subst; simpl in *.

    - (* Case "step_bop". *)
    inversion Hs2; subst; simpl in *.
    assert ((uid, cmd_bop bop0 v1 v2) = (uid0, cmd_bop bop1 v0 v3)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.
    rewrite <- H8 in H0. inversion H0; subst. auto.

    assert ((uid, cmd_bop bop0 v1 v2) = (uid0, cmd_phi pas)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.

    assert ((uid, cmd_bop bop0 v1 v2) = (uid0, cmd_tmn tmn0)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.

    assert ((uid, cmd_bop bop0 v1 v2) = (uid0, cmd_load addr)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.
    
    assert ((uid, cmd_bop bop0 v1 v2) = (uid0, cmd_store addr v)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.
    
    - (* Case "step_phi". *)
    inversion Hs2; subst; simpl in *.

    assert ((uid, cmd_phi pas) = (uid0, cmd_bop bop0 v1 v2)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.

    assert ((uid, cmd_phi pas) = (uid0, cmd_phi pas0)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.
    rewrite <- H8 in H0. inversion H0; subst; auto.

    assert ((uid, cmd_phi pas) = (uid0, cmd_tmn tmn0)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.

    assert ((uid, cmd_phi pas) = (uid0, cmd_load addr)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.
    
    assert ((uid, cmd_phi pas) = (uid0, cmd_store addr v)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.

    - (* Case "step_tmn". *)
    inversion Hs2; subst; simpl in *.

    assert ((uid, cmd_tmn tmn0) = (uid0, cmd_bop bop0 v1 v2)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.

    assert ((uid, cmd_tmn tmn0) = (uid0, cmd_phi pas)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.

    assert ((uid, cmd_tmn tmn0) = (uid0, cmd_tmn tmn1)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.
    rewrite <- H8 in H0. inversion H0; subst; auto.

    assert ((uid, cmd_tmn tmn0) = (uid0, cmd_load addr)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.
    
    assert ((uid, cmd_tmn tmn0) = (uid0, cmd_store addr v)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.

    - (* Case "step_load". *)
    inversion Hs2; subst; simpl in *.

    assert ((uid, cmd_load addr) = (uid0, cmd_bop bop0 v1 v2)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H0; subst.

    assert ((uid, cmd_load addr) = (uid0, cmd_phi pas)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H0; subst.

    assert ((uid, cmd_load addr) = (uid0, cmd_tmn tmn0)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H0; subst.

    assert ((uid, cmd_load addr) = (uid0, cmd_load addr0)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H0; subst.
    auto.

    assert ((uid, cmd_load addr) = (uid0, cmd_store addr0 v)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H0; subst.


    - (* "step_store". *)
    inversion Hs2; subst; simpl in *.

    assert ((uid, cmd_store addr v) = (uid0, cmd_bop bop0 v1 v2)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.

    assert ((uid, cmd_store addr v) = (uid0, cmd_phi pas)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.

    assert ((uid, cmd_store addr v) = (uid0, cmd_tmn tmn0)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.

    assert ((uid, cmd_store addr v) = (uid0, cmd_load addr0)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.

    assert ((uid, cmd_store addr v) = (uid0, cmd_store addr0 v0)).
    apply (insn_at_pc_func g Hwfcfg pc0); auto. inversion H1; subst.
    rewrite <- H8 in H0. inversion H0. subst; auto.
Qed.  
(* /FOLD *)
(* /HIDE *)

End OpsemCorrect.

Export Opsem Typing OpsemCorrect.

End Make.
*)

(** * Commented out 
(** *** List-based CFG Implementation *)

(**  One possible implementation of cfgs *)

Module ListCFG <: CFG.
  Definition block := (lbl * list insn)%type.
  Definition t := (lbl * list block)%type.
  Local Notation cfg := t.

  Definition entry_block : cfg -> lbl := @fst _ _.

  Inductive wf_cfg' : cfg -> Prop :=
    wf_cfg_intro : forall l bs,
    NoDup (map (@fst _ _) bs) ->
    NoDup (flat_map (fun b => map (@fst _ _) (snd b)) bs) ->
    In l (map (@fst _ _) bs) ->
    ~ In [] (map (@snd _ _) bs) ->
    wf_cfg' (l, bs).

  (* hack around some limitation re inductive types & parameters *)
  Definition wf_cfg := wf_cfg'.

  Lemma wf_cfg_block_len : forall g, wf_cfg g ->
    forall l is, In (l, is) (snd g) -> length is <> 0.
  Proof.
    inversion 1. intros. destruct is; simpl; auto. 
    contradict H2. 
    eapply in_map with (f:=@snd _ _) in H5. auto.
  Qed.

  Definition wf_pc (g:cfg) (p:pc) : Prop :=
    let (l, n) := p in
    exists is i, In (l, is) (snd g) /\ Nth i is n.

  Definition tmn_pc (g:cfg) (p:pc) : Prop :=
    let (l, n) := p in
    exists is, In (l, is) (snd g) /\ n = pred (length is).

  Definition insn_at_pc (g:cfg) (p:pc) (i:insn) : Prop :=
    let (l, n) := p in
    exists is, In (l, is) (snd g) /\ Nth i is n.
    
  Definition uid_at_pc (g:cfg) (p:pc) (uid:uid) : Prop :=
    exists c, insn_at_pc g p (uid, c).

  Lemma wf_pc_insn : forall g, wf_cfg g ->
    forall p, wf_pc g p -> exists i, insn_at_pc g p i.
  Proof.
    unfold wf_pc, insn_at_pc. destruct p; intros. 
    decompose [ex and] H0. eauto.
  Qed.

  Lemma wf_pc_tmn : forall g, wf_cfg g ->
    forall p, wf_pc g p -> exists p', tmn_pc g p' /\ le_pc p p'.
  Proof.
    unfold wf_pc, tmn_pc. destruct p. intros.
    decompose [ex and] H0. 
    exists (t0, pred (length x)). split. eauto.
    constructor. 
    apply PeanoNat.Nat.lt_le_pred.
    eapply Nth_length; eauto.
  Qed.

  Lemma wf_pc_le_tmn : forall g, wf_cfg g ->
    forall p', tmn_pc g p' -> forall p, le_pc p p' -> wf_pc g p.
  Proof.
    unfold wf_pc, tmn_pc. intros. destruct p, p'.
    decompose [ex and] H0. exists x.

    destruct x. apply wf_cfg_block_len in H3; auto. contradict H3; auto.
    inversion H1; subst. apply le_lt_n_Sm in H5. 
    erewrite <- S_pred in H5. 
    apply length_Nth in H5 as [? ?]. 
    eexists. split; eauto. eauto.
  Qed.

  Lemma wf_entry : forall g, wf_cfg g ->
    wf_pc g (block_entry (entry_block g)).
  Proof.
    unfold wf_pc. inversion 1. simpl.
    apply in_map_iff in H2 as [[? ?] [? ?]].
    destruct l0.
    exfalso. pose proof (wf_cfg_block_len g H t0 []) as contra. 
    subst g; simpl in *. apply contra; auto.
    eexists. eexists. 
    simpl in *. subst l. split; eauto.
    simpl; eauto.
  Qed.

  Lemma insn_at_pc_func : forall g, wf_cfg g ->
    functional (insn_at_pc g).
  Proof. 
    unfold functional, insn_at_pc. inversion 1. destruct a.
    intros b1 b2 [is1 [Hin1 Hnth1]] [is2 [Hin2 Hnth2]].
    cut (is1 = is2). intro; subst is2. eapply Nth_eq; eauto.
    eapply NoDup_assoc_func; eauto.
  Qed.

  Lemma uid_at_pc_inj : forall g, wf_cfg g ->
    injective (uid_at_pc g).
  Proof.
    unfold injective, uid_at_pc, insn_at_pc. inversion 1.
    intros [l1 n1] [l2 n2] uid [c1 [is1 [Hin1 Hnth1]]] [c2 [is2 [Hin2 Hnth2]]].
    cut ((l1, is1) = (l2, is2)).
    intro Heq. inversion Heq; clear Heq. f_equal.
    eapply NoDup_flat_map__NoDup in H1; eauto.
    change is1 with (snd (l1, is1)) in Hnth1.
    change is2 with (snd (l2, is2)) in Hnth2.
    subst; eapply NoDup_nth_inj; eauto. 

    set (f1 b := map (@fst _ _) (snd b)) in *.
    apply (NoDup_flat_map (l1, is1) (l2, is2) uid f1 bs); auto.
    unfold f1; simpl. 
    apply in_map_iff. exists (uid, c1); eauto using Nth_In.
    apply in_map_iff. exists (uid, c2); eauto using Nth_In.
  Qed.

  (** ** Working with ListCFG. *)

  (** Adds the given instruction list as a block labeled [l]. *)

  Definition update (bs:list block) (l:lbl) (is:list insn) : list block :=
    (l, is)::bs.

  (** Lookup the block in the list. *)

  Definition lookup (bs:list block) (l:lbl) : option (list insn) :=
    assoc Lbl.eq_dec l bs.

  (** ** Simple lemmas about CFG modifications. *)

  Lemma update_eq :
    forall (is : list insn) (l1 l2 : lbl) (bs : list block),
      l1 = l2 -> lookup (update bs l1 is) l2 = Some is.
  (* FOLD *)
  Proof.
    intros; unfold update, lookup.
    subst. simpl. destruct (Lbl.eq_dec l2 l2); tauto.
  Qed.
  (* /FOLD *)

  Lemma update_neq :
    forall (l1 l2 : lbl) (is : list insn) (bs: list block),
      l1 <> l2 -> lookup (update bs l1 is) l2 = lookup bs l2.
  (* FOLD *)
  Proof.
    intros; subst; simpl.
    destruct (Lbl.eq_dec l2 l1); subst; tauto.
  Qed.
  (* /FOLD *)

  (* Added *)
  Fixpoint find_block {A : Type} (lst : list (lbl * A)) (trgt_label : lbl) :=
    match lst with
    | [] => None
    | (label, data) :: other_blks =>
      if Lbl.eq_dec label trgt_label then
        Some data 
      else find_block other_blks trgt_label
    end.
      
  Definition fetch (g : cfg) (p: pc): option insn :=
    let '(entry_label, blocks) := g in
    let '(trgt_block, offset) := p in
    match (find_block blocks trgt_block) with
    | Some found_block => nth_error found_block offset
    | None => None
    end.
  
  Lemma find_block_ok: forall (blks: list (lbl * list insn)) found_instrs (label: lbl),
      NoDup (List.map fst blks) -> 
      find_block blks label = Some found_instrs <->
      In (label, found_instrs) blks.
  Proof.
    intros blks found_instrs label nodups.
    induction blks as [| blk other_blks].
    { simpl; split; intros H; inversion H. }
    { simpl; destruct blk as [this_label this_insns].
      destruct (Lbl.eq_dec this_label label) as [label_eq | label_neq].
      { split; intros H;
          [inversion H as [found_this] | idtac].
        - subst; left; auto.
        - destruct H as [found_here | found_in_others].
          + inversion found_here; subst; trivial.
          + simpl in nodups.
            (* Want the following as lemma *)
            replace (this_label :: map fst other_blks) with
                ([] ++ (this_label :: map fst other_blks)) in nodups
              by auto.
            apply NoDup_remove in nodups.
            inversion nodups as [? not_found_in_others].
            apply in_map with (f := fst) in found_in_others.
            simpl in found_in_others.
            contradiction not_found_in_others.
            simpl; subst; apply found_in_others.
      } 
      { simpl in nodups.
        replace (this_label :: map fst other_blks) with
            ([] ++ (this_label :: map fst other_blks)) in nodups
          by auto.
        apply NoDup_remove in nodups.
        inversion nodups as [nodups_in_others this_label_in_others].
        generalize (IHother_blks nodups_in_others) as IH; intros IH.
        rewrite IH.
        split; auto.
        intros [Hcontra | ?]; auto.
        contradiction label_neq.
        inversion Hcontra; auto.
      }
    } 
  Qed.
      
  Lemma find_block_iff_in_cfg: forall entry_label blks trgt_label trgt_offset i,
      NoDup (map fst blks) -> 
      fetch (entry_label, blks) (trgt_label, trgt_offset) = Some i <->
      exists instrs, In (trgt_label, instrs) blks /\ Nth i instrs trgt_offset.
  Proof.
    intros entry_label blks trgt_label trgt_offset i nodup.
    unfold fetch.
    destruct (find_block blks trgt_label) eqn:found.
    { apply find_block_ok in found; auto.
      split.
      { intros H; exists l; split; trivial.
        rewrite nth_error_iff_Nth in H.
        trivial.
      }
      { intros [instrs [trgt_blk_found trgt_instr_found]].
        rewrite <- nth_error_iff_Nth in trgt_instr_found.
        replace l with instrs; auto.
        eapply NoDup_assoc_func.
        apply nodup.
        apply trgt_blk_found.
        trivial.
      }         
    } 
    { split; intros H; [inversion H | idtac].
      destruct H as [instrs [trgt_label_found trgt_instr_found]].
      rewrite <- nth_error_iff_Nth in trgt_instr_found.
      rewrite <- find_block_ok in trgt_label_found; auto.
      rewrite trgt_label_found in found; inversion found.
    }
  Qed.
  
  (* Added *)
  Lemma insn_at_pc_fetch :
    forall g pc i, wf_cfg g ->
              insn_at_pc g pc i <-> fetch g pc = Some i.
  Proof.
    intros [l blks] pc i wf_g.
    inversion wf_g as
        [l' blks' nodup nodup_uid l_in_blks blks_not_empty [l_l' blks_blk]].
    destruct pc as [curr_label curr_offset].
    rewrite find_block_iff_in_cfg; auto.
    simpl.
    split; auto.
  Qed.      
    
End ListCFG.
*)
