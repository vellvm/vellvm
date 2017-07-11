(** ** QuickChick infrastructure for Vminus **)

Require Import List.
Import ListNotations.
Require Import Arith.
Require Import String.

Require Import QuickChick.QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

Require Import Vminus.Atom.
Require Import Vminus.ListCFG.
Require Import Vminus.Vminus.

Require Import Vminus.AtomGen.

(** lbl, uid, addr **)

Instance gen_lbl : Gen lbl :=
  {| arbitrary := gen_fresh fresh_store |}.

Instance shrink_lbl : Shrink lbl := {| shrink x := [] |}.

Instance show_lbl : Show lbl :=
  {| show x :=
       ("lbl "%string ++ show x ++ "")%string |}.
  
Instance gen_uid : Gen uid :=
  {| arbitrary := gen_fresh fresh_store |}.

Instance shrink_uid : Shrink uid := {| shrink x := [] |}.

Instance show_uid : Show uid :=
  {| show x :=
       ("uid "%string ++ show x ++ "")%string |}.

Instance gen_addr : Gen addr :=
  {| arbitrary := gen_fresh fresh_store |}.

Instance shrink_addr : Shrink addr := {| shrink x := [] |}.

Instance show_addr : Show addr :=
  {| show x :=
       ("addr "%string ++ show x ++ "")%string |}.

(** Values and commands **)

Derive Arbitrary for val.
Derive Show for val.

(* Sample (@arbitrary val _). *)

Derive Arbitrary for bop.
Derive Show for bop.

(* Sample (@arbitrary bop _). *)

Derive Arbitrary for tmn.
Derive Show for tmn.

(* Sample (@arbitrary tmn _). *)

Instance gen_phiarg : Gen phiarg.
Proof. unfold phiarg. auto with typeclass_instances. Defined.

Instance shrink_phiarg : Shrink phiarg.
Proof. unfold phiarg. auto with typeclass_instances. Defined.

Instance show_phiarg : Show phiarg.
Proof. unfold phiarg. auto with typeclass_instances. Defined.

Derive Arbitrary for cmd.
Derive Show for cmd.

(* Sample (@arbitrary cmd _). *)

Instance gen_insn : Gen insn.
Proof. unfold insn. auto with typeclass_instances. Defined.

Instance shrink_insn : Shrink insn.
Proof. unfold insn. auto with typeclass_instances. Defined.

Instance show_insn : Show insn :=
  {| show instr :=
       let '(uid, cmd) := instr in
       "(uid " ++ show uid ++ ", " ++ show cmd
  |}.

(** Program counters and CFG **)

Instance gen_pc : Gen pc.
Proof.
  unfold pc. auto with typeclass_instances. Defined.

Instance shrink_pc : Shrink pc.
Proof. unfold pc. auto with typeclass_instances. Defined.

Instance show_pc : Show pc :=
  {| show p :=
       let '(lbl, offset) := p in
       "(blk " ++ (show lbl) ++ ", ofs " 
               ++ show_nat offset ++ ")"
  |}.

Instance gen_block : Gen ListCFG.block.
Proof. unfold ListCFG.block. auto with typeclass_instances. Defined.

Instance shrink_block : Shrink ListCFG.block.
Proof. unfold ListCFG.block. auto with typeclass_instances. Defined.

Instance show_block : Show ListCFG.block.
Proof. unfold ListCFG.block. auto with typeclass_instances. Defined.

Instance gen_cfg : Gen ListCFG.t.
Proof. unfold ListCFG.t. auto with typeclass_instances. Defined.

Instance shrink_cfg : Shrink ListCFG.t.
Proof. unfold ListCFG.t. auto with typeclass_instances. Defined.

Instance show_cfg : Show ListCFG.t :=
  {| show cfg :=
       let '(entry_label, blks) := cfg in
       "(entry " ++ show entry_label ++ ", blks: " ++
                 (List.fold_left
                    (fun accum blk =>
                       let '(lbl, insns) := blk in
                       "lbl " ++ show lbl ++ ": " ++
                              (show insns))
                    blks "")
  |}.

(* Sample (@arbitrary ListCFG.t _). *)


