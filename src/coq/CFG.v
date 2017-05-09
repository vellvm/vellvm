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
Require Import Vellvm.AstLib Vellvm.Ollvm_ast Vellvm.Dom.
Require Import Vellvm.Classes.
Import ListNotations.

Definition pt := instr_id.

(* program counter is a function plus instruction id ------------------------ *)

Record pc :=
  mk_pc {
      fn  : function_id;
      ins : pt;
    }.

Definition string_of_pc p : string :=
  "@" ++ (string_of_raw_id (fn p)) ++ (* ":" ++ (string_of_raw_id (bn p)) ++ *) ":" ++ (string_of_instr_id (ins p)).


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
  Qed.

  Include HasEqDec2Bool.
  
End PC.
Instance eq_dec_pc : eq_dec pc := PC.eq_dec.


(* control flow graphs (CFGs) ----------------------------------------------- *)

Inductive cmd : Set :=
| Step  (i:instr) (next:pt)
| Jump  (bn:block_id) (t:terminator)
.                    

Inductive block_entry : Set :=
| Phis (phis : list (local_id * instr)) (next:pt)
.

(* each function definition corresponds to a control-flow graph *)
Record cfg := mkCFG
{
  init : pt;
  code : pt -> option cmd; 
  blks : block_id -> option instr_id;
  phis : block_id -> option block_entry;
}.


(* structurally well-formed CFGs 
   - the initial pt denotes a command  
   - fallthrough closure: each fallthrough pt maps to a command 
   - jump closure: each label used in a terminator leads to a
     block within the same function body.
*)

Definition pt_exists (CFG : cfg) (p:pt) : Prop :=
  exists cmd, (code CFG p) = Some cmd.

Definition lbls (t:terminator) : list block_id :=
  match t with
  | TERM_Ret _        
  | TERM_Ret_void   => []
  | TERM_Br _ l1 l2 => [l1; l2] 
  | TERM_Br_1 l => [l] 
  | TERM_Switch _ l brs => l::(List.map (fun x => snd x) brs)
  | TERM_IndirectBr _ brs => brs
  | TERM_Resume _    => []
  | TERM_Invoke  _ _ l1 l2 => [l1; l2] 
  end.

Definition is_phi (i:instr) : Prop :=
  match i with
   | INSTR_Phi _ _ => True
   | _ => False
  end.


(** Edge relation *)
Inductive succ_pt (g:cfg) : pt -> pt -> Prop :=
| succ_pt_S : forall p i q,
    (code g) p = Some (Step i q) ->
    succ_pt g p q
| succ_pt_J : forall p b t l q,
    (code g) p = Some (Jump b t) ->
    In l (lbls t) ->
    (blks g) l = Some q ->
    succ_pt g p q.

(*
    (blks g) (fn p) l = Some (Phis ((x,ins)::tl) q) ->
    succ_pt g p (mk_pt (fn p) (IId x))
| succ_pt_Jnophi: forall p b t l q,
    (code g) p = Some (Jump b t) ->
    In l (lbls t) ->
    (blks g) (fn p) l = Some (Phis [] q) ->
    succ_pt g p q.
*)

Inductive wf_phis (CFG : cfg) (q : pt) : pt -> list (local_id * instr) -> Prop :=
| wf_phis_nil : wf_phis CFG q q []
| wf_phis_cons :
    forall p p' x t args rest,
    (code CFG p) = Some (Step (INSTR_Phi t args) p') ->
    wf_phis CFG q p' rest ->
    wf_phis CFG q p ((x, INSTR_Phi t args) :: rest) .
            
Definition wf_cfg (CFG : cfg) : Prop :=
  pt_exists CFG (init CFG) 
  /\ (forall p q i, (code CFG p) = Some (Step i q) -> pt_exists CFG q)
  /\ (forall p bn t, (code CFG p) = Some (Jump bn t) ->
               Forall (fun bn => exists p', exists xs, exists q,
                             (blks CFG bn) = Some p' 
                             /\ (phis CFG bn) = Some (Phis xs q) 
                             /\ wf_phis CFG q p' xs
                             /\ pt_exists CFG q
                      )
                      (lbls t)).

Lemma wf_cfg_succ_pt : forall g p1 p2, wf_cfg g -> pt_exists g p1 -> succ_pt g p1 p2 -> pt_exists g p2.
Proof.
  intros g p1 p2 H H0 H1.
  destruct H as [Hinit [HStep HJump]].
  inversion H1; subst.
  - eapply HStep. apply H.
  - apply HJump in H.
    eapply Forall_forall in H.
    Focus 2. apply H2.
    destruct H as [p' [xs [q [Ha [Hb [Hc Hd]]]]]].
    rewrite H3 in Ha. inversion Ha. subst.
    induction Hc.
    * exact Hd.
    * exists (Step (INSTR_Phi t0 args) p').
      exact H.
Qed.      



(* creating CFGs from syntax ------------------------------------------------ *)
         
Fixpoint lookup_function_definition ets f : option definition :=
  match ets with
  | [] => None
  | (TLE_Definition d) :: ts =>
    if (dc_name (df_prototype d)) == f then
      Some d
    else
      lookup_function_definition ts f
  | _ :: ts => lookup_function_definition ts f
  end.
                                                 
Fixpoint init_of_definition d : option pt :=
  match (df_instrs d) with
  | [] => None
  | b :: _ => Some (match blk_instrs b with
                   | [] => blk_term_id b
                   | (iid, _) :: t => iid
                   end)
  end.


Fixpoint phis_from_block term_id (b : list (instr_id * instr)) : option block_entry :=
  match b with
    | (IId iid, INSTR_Phi i v as ins) :: t =>
       'rest <- phis_from_block term_id t;
        match rest with
          | Phis phis p => Some (Phis ((iid, ins)::phis) p) 
        end
    | (IVoid _, INSTR_Phi i v as ins) :: t => None
    | (next, _) :: _ => Some (Phis [] next)
    | [] => Some (Phis [] term_id)
  end.

Fixpoint lookup_block bs block_id : option block :=
  find (fun b => if (blk_id b) == block_id then true else false) bs.

Fixpoint block_to_phis (b:block) : option block_entry :=
  phis_from_block (blk_term_id b) (blk_instrs b).
  
Definition fallthrough term_id (is : list (instr_id * instr)) : instr_id :=
  match is with
  | [] => term_id
  | (next, _)::_ => next
  end.

Fixpoint lookup_instr (p:pt) term_id (insns : list (instr_id * instr)) : option cmd :=
  match insns with
  | [] =>  None
  | (x,ins)::rest =>
    if p == x then
      Some (Step ins (fallthrough term_id rest))
    else
      lookup_instr p term_id rest
  end.

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

Definition code_of_definition (d:definition) (p:pt) : option cmd :=
  cmd_from_blocks p (df_instrs d).
  

Definition blks_of_definition (d:definition) block_id : option pt :=
  'b <- lookup_block (df_instrs d) block_id;
  Some (fallthrough (blk_term_id b) (blk_instrs b)).

Definition phis_of_definition (d:definition) block_id : option block_entry :=
  'b <- lookup_block (df_instrs d) block_id;
  block_to_phis b.

Definition cfg_of_definition (d:definition) : option cfg :=
  'init <- init_of_definition d;
    Some {| init := init;
            code := code_of_definition d;
            blks := blks_of_definition d;
            phis := phis_of_definition d
         |}.
            
Definition fcfg := function_id -> option (list ident * cfg).

Fixpoint entities_to_funs ets fid : option (list ident * cfg) :=
  'd <- lookup_function_definition ets fid;
  'cfg <- cfg_of_definition d;
  Some (map (fun x => ID_Local x) (df_args d), cfg).


(*

Module Wellformedness.


  (** *** GRAPH instance for dominance calculation *)


  (** Graph of program points *)

  Module PcGraph <: GRAPH.
    Definition t := cfg.
    Definition V := pt.
    Definition entry g := init g.
    Definition Succ := succ_pt.
    Definition Mem := pt_exists.
  End PcGraph.

  Module Export Dom := Dom.Spec PcGraph.

  (** *** Definitions for Well-formed SSA programs. *)

  (** FULL: Most of the Vminus instructions define the uid associated
  with their program point.  Some (like [store] and the [tmn]s)
  do not. *)
  (** TERSE: The command at the given [pc] defines uid. *)

  Definition def_at_pc (g:cfg) (p:pt) (uid:uid) : Prop :=
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
    forall pred, succ_pt g pred (entry_of_pc p) ->
      (exists v, In (lbl_of pred, v) (insn_phis i)) /\
      (forall uid, In (lbl_of pred, val_uid uid) (insn_phis i) -> 
          uid_sdom_pc g uid pred).

  Definition wf_phi_pred (g:Cfg.t) (i:insn) (p:pc) : Prop :=
    forall l v, In (l, v) (insn_phis i) ->
      (exists pred, succ_pt g pred (entry_of_pc p) /\ lbl_of pred = l).

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
      (Hwfentry : forall p, ~ succ_pt g p (block_entry (entry_block g))),
      wf_prog g.

End Wellformedness.
*)