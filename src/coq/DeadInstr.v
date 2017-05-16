(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import ZArith List String Omega.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.Ollvm_ast Vellvm.AstLib Vellvm.CFG.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Set Implicit Arguments.
Set Contextual Implicit.

Require Import Vellvm.Effects.


Class RemoveInstr X := remove_instr : instr_id -> X -> X.

Definition remove_instr_block (id:instr_id) (b:block) : block :=
  {| blk_id := blk_id b;
     blk_instrs := List.filter (fun x => negb (if (fst x == id) then true else false)) (blk_instrs b);
     blk_term := blk_term b;
     blk_term_id := blk_term_id b;
  |}.
Instance rem_instr_block : RemoveInstr block := remove_instr_block.

Definition remove_instr_defn (id:instr_id) (d:definition (list block)) : definition (list block) :=
  {|
    df_prototype   := (df_prototype d);
    df_args        := (df_args d);
    df_instrs      := List.map (remove_instr id) (df_instrs d);
  |}.

Instance rem_instr_defn : RemoveInstr (definition (list block)) := remove_instr_defn.

Definition remove_instr_tle (id:instr_id) (tle:toplevel_entity (list block)) : toplevel_entity (list block) :=
  match tle with
  | TLE_Definition d => TLE_Definition (remove_instr id d)
  | _ => tle
  end.

Instance rem_instr_tle : RemoveInstr (toplevel_entity (list block)) := remove_instr_tle.

(*
Definition dead (g:cfg) (inst:instr_id) : Prop :=
  match inst with
  | IVoid _ => False
  | IId id => forall pt, ~ (cmd_uses_local g pt id)
  end.
*)

