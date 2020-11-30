(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import Ascii Strings.String.
From Vellvm Require Import
     Syntax.LLVMAst.
Open Scope string_scope.


Definition mangle_raw_id (id:raw_id) : raw_id :=
  match id with
  | Anon n => id
  | Name s => Name (append "_vellvm" s)
  | Raw n => id
  end.

Definition mangle_ident (id:ident) : ident :=
  match id with
  | ID_Global i => ID_Global (mangle_raw_id i)
  | ID_Local i => ID_Local (mangle_raw_id i)
  end.

Section WithT.
  Variable (T : Set).


Definition mangle_instr (i:instr_id * instr T) : (instr_id * instr T) :=
  match i with
  | _ => i
  end.

Definition mangle_block (blk:block T) : block T :=
  blk.

Definition mangle_blocks (blks: block T * list (block T)) : block T * list (block T) :=
  let '(entry, body) := blks in 
  (mangle_block entry, List.map mangle_block body).

Definition mangle_definition (d:definition T (block T * list (block T))) : definition T (block T * list (block T)) :=
  mk_definition _
  (df_prototype d)
  (df_args d)
  (mangle_blocks (df_instrs d))
.


Definition mangle_toplevel_entity (tle : toplevel_entity T (block T * list (block T))) : toplevel_entity T (block T * list (block T)) :=
  match tle with
  | TLE_Definition d => TLE_Definition (mangle_definition d)
  | _ => tle
  end.

Definition transform (prog: list (toplevel_entity T (block T * list (block T)))) : list (toplevel_entity T (block T * list (block T))) :=
  List.map mangle_toplevel_entity prog.

End WithT.
