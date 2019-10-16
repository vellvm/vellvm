(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import Equalities.
From Coq Require Import ZArith List String Omega.
Require Import Vellvm.AstLib Vellvm.LLVMAst.
Require Import Vellvm.Util.
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

(* SAZ: The notion of pc, and many other things in this file is now obsolete *)
(* program counter denotes an instruction with a block of a function -------- *)
Record pc :=
  mk_pc {
      fn : function_id;
      bk : block_id;
      pt : instr_id;
    }.

Section hiding_notations.
  Local Open Scope sexp_scope.
  Global Instance serialize_pc : Serialize pc :=
    fun p => [Raw "@" ; to_sexp (fn p) ; Raw ":" ; to_sexp (bk p) ; Raw ":" ; to_sexp (pt p)].
End hiding_notations.


Ltac unfold_eqv :=
  repeat (unfold eqv in *; unfold eqv_raw_id in *; unfold eqv_instr_id in *).

Module PC <: UsualDecidableTypeFull.
  Definition t := pc.
  Include HasUsualEq.
  Include UsualIsEq.
  Include UsualIsEqOrig.


  Lemma eq_dec : forall (x y : pc), {x = y} + {x <> y}.
  Proof.
    intros x y.
    destruct x as [xf xi xp]; destruct y as [yf yi yp].
    destruct (xf ~=? yf); unfold_eqv.
    - destruct (xi ~=? yi); unfold_eqv.
     + destruct (xp ~=? yp); unfold_eqv.
        * subst. left. reflexivity.
        * right. unfold not. intros. apply n. inversion H. auto.
     + right. unfold not. intros. apply n. inversion H. auto.
    - right. unfold not. intros. apply n. inversion H. auto.
  Defined.

  Include HasEqDec2Bool.

End PC.
Instance eq_dec_pc : RelDec (@eq pc) := RelDec_from_dec (@eq pc) PC.eq_dec.


(* control flow graphs (CFGs) ----------------------------------------------- *)
Section CFG.
  Variable (T:Set).

(* TODO: rename Step to Inst *)
Inductive cmd : Set :=
| Inst (i:instr T)
| Term (t:terminator T)
.


(* each function definition corresponds to a control-flow graph
   - init is the entry block
   - blks is a list of labeled blocks
   - args is the list of identifiers brought into scope by this function
*)
Record cfg := mkCFG
{
  init : block_id;
  blks : list (block T);
  args : list ident;
}.

(* An mcfg is a module where each function body has been converted to a cfg *)
Definition mcfg : Set := modul T cfg.

Definition find_defn {X:Set} (fid:function_id) (d:definition T X) : option (definition T X) :=
  if (ident_of d) ~=? (ID_Global fid) then Some d else None.

Definition find_function (CFG : mcfg) (fid:function_id) : option (definition T cfg) :=
  find_map (find_defn fid) (m_definitions T _ CFG).


Definition fallthrough (cd: (code T)) term_id : instr_id :=
  match cd with
  | [] => term_id
  | (next, _)::_ => next
  end.

Definition blk_term_id b := fst (blk_term T b).
Definition blk_terminator b := snd (blk_term T b).

Definition blk_entry_id (b:block T) : instr_id := fallthrough (blk_code T b) (blk_term_id b).

Definition blk_entry_pc (fid:function_id) (b:block T) :=
  mk_pc fid (blk_id T b) (blk_entry_id b).

Definition blk_term_pc (fid:function_id) (b:block T) :=
  mk_pc fid (blk_id T b) (blk_term_id b).

Fixpoint find_block bs block_id : option (block T) :=
  find (fun b => if (blk_id T b) ~=? block_id then true else false) bs.

Fixpoint find_instr (cd : (code T)) (p:instr_id) (t:instr_id) : option (cmd * option instr_id) :=
  match cd with
  | [] =>  None
  | (x,i)::cd =>
    if p ~=? x then
      Some (Inst i, Some (fallthrough cd t))
    else
      find_instr cd p t
  end.

Definition block_to_cmd (b:block T) (iid:instr_id) : option (cmd * option instr_id) :=
  let term_id := blk_term_id b in
  if term_id ~=? iid then
    Some (Term (snd (blk_term T b)), None)
  else
    find_instr (blk_code T b) iid term_id
.

(*
Definition fetch (CFG : mcfg) (p:pc) : option cmd:=
  let 'mk_pc fid bid iid := p in
  cfg <- find_function CFG fid ;;
  blk <- find_block (blks (df_instrs T cfg)) bid ;;
  '(c, _) <- block_to_cmd blk iid ;;
  ret c.

Definition incr_pc (CFG:mcfg) (p:pc) : option pc :=
  let 'mk_pc fid bid iid := p in
  cfg <- find_function CFG fid ;;
  blk <- find_block (blks (df_instrs T cfg)) bid ;;
  '(c, n) <- block_to_cmd blk iid ;;
  iid_next <- n ;;
  ret (mk_pc fid bid iid_next).
*)

Inductive block_entry : Set :=
| BlockEntry (phis:list (local_id * (phi T))) (p:pc).

Definition block_to_entry (fid:function_id) (b:block T) : block_entry :=
  BlockEntry (blk_phis T b) (blk_entry_pc fid b).

Definition find_block_entry (CFG:mcfg) (fid:function_id) (bid:block_id) : option block_entry :=
  cfg <- find_function CFG fid ;;
  blk <- find_block (blks (df_instrs T _ cfg)) bid ;;
  ret (block_to_entry fid blk).

Inductive function_entry : Set :=
| FunctionEntry (args:list local_id) (p:pc).


Definition find_function_entry (CFG:mcfg) (fid:function_id) : option function_entry :=
  dfn <- find_function CFG fid ;;
  let cfg := df_instrs T _ dfn in
  blk <- find_block (blks cfg) (init cfg) ;;
  ret (FunctionEntry (df_args T _ dfn) (mk_pc fid (init cfg) (blk_entry_id blk))).


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
  match (df_instrs T _ d) with
  | [] => None
  | b :: _ => Some (blk_id T b)
  end.


Definition cfg_of_definition (d:definition T (list (block T))) : option cfg :=
  init <- init_of_definition d ;;
  let args := List.map (fun x => ID_Local x) (df_args T _ d) in
    Some {| init := init;
            blks := df_instrs T _ d;
            args := args;
         |}.


Definition mcfg_of_modul (m:modul T (list (block T))) : option mcfg :=
  defns <- map_option
                (fun d =>
                   cfg <- cfg_of_definition d ;;
                     Some {|
                       df_prototype := df_prototype T _ d;
                       df_args := df_args T _ d;
                       df_instrs := cfg
                       |}) (m_definitions T _ m) ;;
  Some {|
    m_name := m_name T _ m;
    m_target := m_target T _ m;
    m_datalayout := m_datalayout _ _ m;
    m_type_defs := m_type_defs _ _ m;
    m_globals := m_globals _ _ m;
    m_declarations := m_declarations _ _ m;
    m_definitions := defns
  |}.

(*  ------------------------------------------------------------------------- *)
End CFG.
