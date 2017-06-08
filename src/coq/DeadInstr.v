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
Require Import Program.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.Ollvm_ast Vellvm.AstLib Vellvm.CFG Vellvm.CFGProp.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Set Implicit Arguments.
Set Contextual Implicit.

Require Import Vellvm.Memory.
Import SS.

Definition optimization := definition (list block) -> definition (list block).

Definition optimize (m:modul (list block)) (o:optimization) : modul (list block) :=
 {|
  m_name := (m_name m);
  m_target := (m_target m);
  m_datalayout := (m_datalayout m);
  m_globals := (m_globals m);
  m_declarations := (m_declarations m);
  m_definitions := map o (m_definitions m);
  |}.


(*

Definition correct (P : modul (list block) -> Prop) (o:optimization) :=
  forall (m:modul (list block)) m_semantic m_opt_semantic,
    P m ->
    mcfg_of_modul m = Some m_semantic ->
    mcfg_of_modul (optimize m o) = Some m_opt_semantic ->
    forall (s:state),
      E.obs_error_free (sem m_semantic s) ->
      E.obs_equiv (sem m_semantic s) (sem m_opt_semantic s).
      
Class RemoveInstr X := remove_instr : instr_id -> X -> X.

Definition remove_instr_block (id:instr_id) (b:block) : block :=
  {| blk_id := blk_id b;
     blk_instrs := List.filter (fun x => negb (if (fst x == id) then false else true)) (blk_instrs b);
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

Definition dead (g:cfg) (inst:instr_id) : Prop :=
  match inst with
  | IVoid _ => False
  | IId id => forall pt, ~ (cmd_uses_local g pt id)
  end.

Inductive remove_instr_applies (inst:instr_id) (d:definition (list block)) : Prop :=
| remove_instr_applies_intro:
    forall glbls g, cfg_of_definition glbls d = Some g ->
               dead g inst ->
               remove_instr_applies inst d.

Definition remove_instr_applies_module (instr:instr_id) (m:modul (list block)) : Prop :=
  Forall (remove_instr_applies instr) (m_definitions m).

Require Import paco.

(*
Lemma obs_error_free_inv :
  forall (m:mcfg) (s:state), 
    E.obs_error_free (sem m s) ->
    (exists dv, sem m s = E.Fin dv) \/
    (exists s', stepD m s = E.Ret s' /\ E.obs_error_free (sem m s')).
Proof.
  intros m s H.
  punfold H. remember (upaco1 obs_error_free_step bot1). remember (sem m s) as d. induction H. 
  - left. exists v. reflexivity.
  - rewrite sem_match_id in Heqd. unfold sem in Heqd.
    unfold bind in Heqd. 
    destruct (stepD m s).
    + right. exists s0. split; eauto. subst. inversion Heqd. pclearbot. punfold H. subst. pfold. apply H.
    + inversion Heqd.
    + inversion Heqd.
    + 
Abort.    
*)  
    

Lemma remove_instr_correct:
  forall (instr:instr_id), correct (remove_instr_applies_module instr) (remove_instr_defn instr).
Proof.
  intros instr.
  unfold correct.
  intros m m_semantic m_opt_semantic Happlies H0 H1 s Herr. revert s Herr.
  pcofix CIH.
  intros s Herr.
  
Abort.
  
  
*)
