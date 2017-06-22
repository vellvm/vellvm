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
Require Import Vellvm.AstLib Vellvm.Ollvm_ast.
Require Import Vellvm.Classes.
Require Import Vellvm.Util.
Import ListNotations.

(* program counter is a function plus instruction id ------------------------ *)

(*
Record pc :=
  mk_pc {
      fn  : function_id;
      ins : pt;
    }.

Instance string_of_pc : StringOf pc :=
  fun p => "@" ++ (string_of_raw_id (fn p)) ++ ":" ++ (string_of_instr_id (ins p)).

Require Import Equalities.
Module PC <: UsualDecidableTypeFull.
  Definition t := pc.
  Include HasUsualEq.
  Include UsualIsEq.
  Include UsualIsEqOrig.
  
  Lemma eq_dec : forall (x y : pc), {x = y} + {x <> y}.
  Proof.
    intros x y.
    destruct x as [xf xi]; destruct y as [yf yi].
    destruct (xf == yf).
      + destruct (xi == yi).
        * subst. left. reflexivity.
        * right. unfold not. intros. apply n. inversion H. auto.
      + right. unfold not. intros. apply n. inversion H. auto.
  Defined.

  Include HasEqDec2Bool.
  
End PC.
Instance eq_dec_pc : eq_dec pc := PC.eq_dec.


(* control flow graphs (CFGs) ----------------------------------------------- *)

Inductive cmd : Set :=
| Step  (i:instr) (next:pt)
| Jump  (bn:block_id) (t:terminator)
.                    
*)

(*
Inductive block_entry : Set :=
| Phis (entry:pt) (phis : list (local_id * instr)) (next:pt)
.
*)

(* each function definition corresponds to a control-flow graph *)
Record cfg := mkCFG
{
  init : block_id;
  blks : block_id -> option block;
  glbl : list ident;   (* identifiers defined on entry to this CFG, 
                          including globals and local function parameters *)
}.

(* An mcfg is a module where each function body has been converted to a cfg *)
Definition mcfg : Set := modul cfg.

Definition find_defn {X:Set} (fid:function_id) (d:definition X) : option (definition X) :=
  if (ident_of d) == (ID_Global fid) then Some d else None.

Definition find_function {X:Set} (CFG : modul X) (fid:function_id) : option (definition X) :=
  find_map (find_defn fid) (m_definitions CFG).

(*
Definition fetch (CFG : mcfg) (p:pc) :=
  'fdefn <- find_function CFG (fn p);
  (code (df_instrs fdefn) (ins p)).

(* creating CFGs from syntax ------------------------------------------------ *)

Definition fallthrough term_id (is : list (instr_id * instr)) : instr_id :=
  match is with
  | [] => term_id
  | (next, _)::_ => next
  end.

Definition blk_entry (b:block) := fallthrough (blk_term_id b) (blk_instrs b). 

Definition init_of_definition d : option pt :=
  match (df_instrs d) with
  | [] => None
  | b :: _ => Some (blk_entry b)
  end.

Fixpoint phis_from_block entry term_id (b : list (instr_id * instr)) : option block_entry :=
  match b with
    | (IId iid, INSTR_Phi i v as ins) :: t =>
       'rest <- phis_from_block entry term_id t;
        match rest with
          | Phis _ phis p => Some (Phis entry ((iid, ins)::phis) p) 
        end
    | (IVoid _, INSTR_Phi i v as ins) :: t => None
    | (next, _) :: _ => Some (Phis entry [] next)
    | [] => Some (Phis entry [] term_id)
  end.


Fixpoint block_to_phis (b:block) : option block_entry :=
  phis_from_block (blk_entry b) (blk_term_id b) (blk_instrs b).
*)
  
Fixpoint lookup_block bs block_id : option block :=
  find (fun b => if (blk_id b) == block_id then true else false) bs.


Fixpoint lookup_instr (p:instr_id) (insns : code) : code :=
  match insns with
  | [] =>  []
  | (x,ins)::rest =>
    if p == x then
      insns
    else
      lookup_instr p rest
  end.

(*
Definition cmd_from_block (p:pt) (b:block) : option cmd :=
  if (blk_term_id b == p) then
    Some (Jump (blk_id b) (blk_term b))
  else
    lookup_instr p (blk_term_id b) (blk_instrs b).


Fixpoint cmd_from_blocks (p:pt) (bs:list block) : option cmd := 
match bs with
  | [] => None
  | b :: bs =>
    match cmd_from_block p b with
    | None => cmd_from_blocks p bs
    | Some cmd => Some cmd
    end
  end.
*)
(*
Definition code_of_definition (d:definition (list block)) (p:pt) : option cmd :=
  cmd_from_blocks p (df_instrs d).
  
Definition blks_of_definition (d:definition (list block)) block_id : option pt :=
  'b <- lookup_block (df_instrs d) block_id;
  Some (fallthrough (blk_term_id b) (blk_instrs b)).

Definition phis_of_definition (d:definition (list block)) block_id : option block_entry :=
  'b <- lookup_block (df_instrs d) block_id;
  block_to_phis b.
*)

Definition init_of_definition d : option block_id :=
  match (df_instrs d) with
  | [] => None
  | b :: _ => Some (blk_id b)
  end.


Definition cfg_of_definition (g:list ident) (d:definition (list block)) : option cfg :=
  'init <- init_of_definition d;
    let args := List.map (fun x => ID_Local x) (df_args d) in
    Some {| init := init;
            blks := lookup_block (df_instrs d);
            glbl := g++args;
         |}.


Definition mcfg_of_modul (m:modul (list block)) : option mcfg :=
  let glbls := globals m in
  'defns <- map_option
                (fun d =>
                   'cfg <- cfg_of_definition glbls d;
                     Some {|
                       df_prototype := df_prototype d;
                       df_args := df_args d;
                       df_instrs := cfg
                       |}) (m_definitions m) ;
  Some {|
    m_name := m_name m;
    m_target := m_target m;
    m_datalayout := m_datalayout m;
    m_globals := m_globals m;
    m_declarations := m_declarations m;
    m_definitions := defns
  |}.

