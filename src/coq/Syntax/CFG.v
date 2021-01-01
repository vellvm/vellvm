(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

(* begin hide *)
Require Import Equalities.

From Coq Require Import ZArith List String Omega.

From Vellvm Require Import
        Syntax.LLVMAst
        Syntax.AstLib
        Utils.Util.

From ExtLib Require Import
     Core.RelDec
     Programming.Eqv
     Structures.Monads
     Data.Monads.OptionMonad.

Require Import Ceres.Ceres.

Import ListNotations.
Import EqvNotation.
Import MonadNotation.
Open Scope monad_scope.
(* end hide *)

(** * VIR internal AST

    Internally, a VIR program is represented as an element of the [mcfg] type.

    This file also provides the function [mcfg_of_tle] allowing to convert a
    [toplevel_entities (block T * list (block T))], i.e. the output of the
    parser, into a [mcfg], i.e. the input to the semantics.

    Before being fed to the semantics, a last step of pre-processing will be
    required: the conversion of types. This step is performed in the [TypToDtyp]
    module.
*)

(* control flow graphs (CFGs) ----------------------------------------------- *)
Section CFG.
  Variable (T:Set).

  Inductive cmd : Set :=
  | Inst (i:instr T)
  | Term (t:terminator T)
  .

  (** * Open cfg
      A potentially open cfg ([ocfg]) is simply a list of blocks.
   *)
  Definition ocfg := list (block T).

  (** * cfg
      Each function definition corresponds to a control-flow graph
   - init is the entry block
   - blks is a list of labeled blocks
   - args is the list of identifiers brought into scope by this function
   *)
  Record cfg := mkCFG
                  {
                    init : block_id;
                    blks : ocfg;
                    args : list raw_id;
                  }.

  Record modul {FnBody:Set} : Set :=
    mk_modul
      {
        m_name: option string;
        m_target: option string;
        m_datalayout: option string;
        m_type_defs: list (ident * T);
        m_globals: list (global T);
        m_declarations: list (declaration T);
        m_definitions: list (@definition T FnBody);
      }.

  (** * mcfg
      An [mcfg] is a module where each function body has been converted to a cfg.
      This structure is the internal representation of a VIR program.
   *)
  Definition mcfg : Set := @modul cfg.

  (* We now define the conversion from the output of the parser to the internal
     structure of a [mcfg].
     The process is fairly simple, it simply consists in two steps:
     1. dispatching the various toplevel entities into their internal representation
     inside of the structure of [modul], as performed by [modul_of_toplevel_entities]
     2. building proper [cfg]s out of the bare non-empty list of [block] provided by
     the parser, as performed by [mcfg_of_modul]
     Finally, [mcfg_of_tle] composes both functions with their parameters specialized
     to get a direct translation from the output of the parser to the input format
     of the semantics (before conversion of types).
   *)

  Definition target_of {X} (tle : toplevel_entity T X) : option string :=
    match tle with
    | TLE_Target tgt => Some tgt
    | _ => None
    end.

  Definition datalayout_of {X} (tle : toplevel_entity T X) : option string :=
    match tle with
    | TLE_Datalayout l => Some l
    | _ => None
    end.

  Definition filename_of {X} (tle : toplevel_entity T X) : option string :=
    match tle with
    | TLE_Source_filename l => Some l
    | _ => None
    end.

  Definition globals_of {X} (tle : toplevel_entity T X) : list (global T) :=
    match tle with
    | TLE_Global g => [g]
    | _ => []
    end.

  Definition declarations_of {X} (tle : toplevel_entity T X) : list (declaration T) :=
    match tle with
    | TLE_Declaration d => [d]
    | _ => []
    end.

  Definition definitions_of {X} (tle : toplevel_entity T X) : list (definition T X) :=
    match tle with
    | TLE_Definition d => [d]
    | _ => []
    end.

  Definition type_defs_of {X} (tle : toplevel_entity T X) : list (ident * T) :=
    match tle with
    | TLE_Type_decl id t => [(id,t)]
    | _ => []
    end.

  Definition modul_of_toplevel_entities {X} (tles : toplevel_entities T X) : @modul X :=
    {|
      m_name := find_map filename_of tles;
      m_target := find_map target_of tles;
      m_datalayout := find_map datalayout_of tles;
      m_type_defs := flat_map type_defs_of tles;
      m_globals := flat_map globals_of tles;
      m_declarations := flat_map declarations_of tles;
      m_definitions := flat_map definitions_of tles;
    |}.

  Definition init_of_definition (d : definition T (block T * list (block T))) : block_id :=
    blk_id (fst (df_instrs d)).

  Definition cfg_of_definition (d : definition T (block T * list (block T))) : cfg :=
    {| init := init_of_definition d;
       blks := fst (df_instrs d) :: snd (df_instrs d);
       args := df_args d;
    |}.

  Definition mcfg_of_modul (m : @modul (block T * list (block T))) : mcfg :=
    let defns := map (fun d => {|
                          df_prototype := df_prototype d;
                          df_args := df_args d;
                          df_instrs := cfg_of_definition d
                        |}) (m_definitions m)
    in
    {|
      m_name := m_name m;
      m_target := m_target m;
      m_datalayout := m_datalayout m;
      m_type_defs := m_type_defs m;
      m_globals := m_globals m;
      m_declarations := m_declarations m;
      m_definitions := defns
    |}.

  (* Utility to lookup by id a block from a list of blocks *)
  Definition find_block (bs: list (block T)) block_id : option (block T) :=
    find (fun b => if (blk_id b) ~=? block_id then true else false) bs.

End CFG.

Arguments modul_of_toplevel_entities {T X}.
Arguments mcfg_of_modul {T}.

(* Conversion of the output of the parser to the [mcfg] structure manipulated internally *)
Definition mcfg_of_tle (p : toplevel_entities typ (block typ * list (block typ))) :=
  mcfg_of_modul (modul_of_toplevel_entities p).

Arguments modul {_} _.
Arguments mk_modul {_ _}.
Arguments m_name {_ _}.
Arguments m_target {_ _}.
Arguments m_datalayout {_ _}.
Arguments m_type_defs {_ _}.
Arguments m_globals {_ _}.
Arguments m_declarations {_ _}.
Arguments m_definitions {_ _}.
Arguments mkCFG {_}.
Arguments find_block {_}.
Arguments blks {_}.
Arguments init {_}.
Arguments args {_}.
