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
  "@" ++ (string_of_raw_id (fn p)) ++ ":" ++ (string_of_instr_id (ins p)).


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
| Phis (entry:pt) (phis : list (local_id * instr)) (next:pt)
.

(* each function definition corresponds to a control-flow graph *)
Record cfg := mkCFG
{
  init : pt;
  code : pt -> option cmd; 
  phis : block_id -> option block_entry;
  glbl : list ident;   (* identifiers defined on entry to this CFG, 
                          including globals and local function parameters *)
}.

(* When does a cfg program point define a given local_id. *)
Definition pt_defines (p:pt) (lid:local_id) :=
  match p with
  | IId id => if id == lid then True else False
  | IVoid _ => False
  end.

(* Which identifiers does an instruction use? *)
Fixpoint value_uses (v:value) : list ident :=
  match v with
  | SV (VALUE_Ident _ id) => [id]
  | SV (VALUE_Integer _ _)
  | SV (VALUE_Float _ _ )
  | SV (VALUE_Bool _ _)
  | SV (VALUE_Null _)
  | SV (VALUE_Zero_initializer _)
  | SV (VALUE_Cstring _ _)
  | SV (VALUE_None _)
  | SV (VALUE_Undef _) => []

  | SV (VALUE_Struct _ l)
  | SV (VALUE_Packed_struct _ l)
  | SV (VALUE_Array _ l)
  | SV (VALUE_Vector _ l) => List.flat_map (fun x => value_uses (snd x)) l
  | SV (OP_IBinop _ _ _ v1 v2) 
  | SV (OP_ICmp _ _ _ v1 v2)
  | SV (OP_FBinop _ _ _ _ v1 v2) 
  | SV (OP_FCmp _ _ _ v1 v2) => (value_uses v1) ++ (value_uses v2)
  | SV (OP_Conversion _ _ _ v _) => value_uses v
  | SV (OP_GetElementPtr _ _ (_,ptr) idxs) => (value_uses ptr) ++ (List.flat_map (fun x => value_uses (snd x)) idxs)
  | SV (OP_ExtractElement _  (_,vec) (_,idx)) => (value_uses vec) ++ (value_uses idx)
  | SV (OP_InsertElement _ (_,vec) (_,elt) (_,idx)) => (value_uses vec) ++ (value_uses elt) ++ (value_uses idx)
  | SV (OP_ShuffleVector _ (_, vec1) (_,vec2) (_,idxmask)) => (value_uses vec1) ++ (value_uses vec2) ++ (value_uses idxmask)
  | SV (OP_ExtractValue _ (_,vec) _) => value_uses vec
  | SV (OP_InsertValue _ (_,vec) (_,elt) _) => (value_uses vec) ++ (value_uses elt)
  | SV (OP_Select _ (_,cnd) (_,v1) (_,v2)) => (value_uses cnd) ++ (value_uses v1) ++ (value_uses v2)
  end.

Definition tvalue_uses (tv:tvalue) : list ident := value_uses (snd tv).

(* over-approximation: may include the same identifier more than once *)
Definition instr_uses (i:instr) : (list ident) :=
  match i with
  | INSTR_Op op => value_uses op                         
  | INSTR_Call (_, fid) args => [fid] ++ (List.flat_map tvalue_uses args)
  | INSTR_Phi  t args => List.flat_map (fun x => value_uses (snd x)) args
  | INSTR_Alloca t None align => []
  | INSTR_Alloca t (Some tv) align => tvalue_uses tv
  | INSTR_Load  volatile t ptr align => tvalue_uses ptr
  | INSTR_Store volatile val ptr align => (tvalue_uses val) ++ (tvalue_uses ptr)
  | INSTR_Fence 
  | INSTR_AtomicCmpXchg
  | INSTR_AtomicRMW
  | INSTR_Unreachable
  | INSTR_VAArg
  | INSTR_LandingPad => []
  end.

Definition terminator_uses (t:terminator) : list ident :=
  match t with
  | TERM_Ret tv => tvalue_uses tv
  | TERM_Ret_void => []
  | TERM_Br tv _ _ => tvalue_uses tv
  | TERM_Br_1  _ => []
  | TERM_Switch  tv _ brs => (tvalue_uses tv) ++ (List.flat_map (fun x => tvalue_uses (fst x)) brs)
  | TERM_IndirectBr tv _ => tvalue_uses tv
  | TERM_Resume tv => tvalue_uses tv
  | TERM_Invoke (_,fid) args _ _ => [fid] ++ (List.flat_map tvalue_uses args)
  end.

(* Which labels does a terminator mention *)
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


(* Well-formed SSA-form CFGs 
   - the initial pt denotes a command  
   - fallthrough closure: each fallthrough pt maps to a command 
   - jump closure: each label used in a terminator leads to a
     block within the same function body.
   - every use of an identifier is dominated by the id's definition
   - no identifier is defined multiple times
*)
Definition pt_exists (CFG : cfg) (p:pt) : Prop :=
  exists cmd, (code CFG p) = Some cmd.


(** Edge relation *)
Inductive edge_pt (g:cfg) : pt -> pt -> Prop :=
| edge_pt_S : forall p i q,
    (code g) p = Some (Step i q) ->
    edge_pt g p q
| edge_pt_J : forall p b t l q xs r,
    (code g) p = Some (Jump b t) ->
    In l (lbls t) ->
    (phis g) l = Some (Phis q xs r) ->
    edge_pt g p q.

(** *** GRAPH instance for dominance calculation *)
(** Graph of program points *)

Module PtGraph <: GRAPH.
  Definition t := cfg.
  Definition V := pt.
  Definition entry g := init g.
  Definition edge := edge_pt.
  Definition mem := pt_exists.
End PtGraph.

Module Export Dom := Dom.Spec PtGraph.


(** *** Definitions for Well-formed SSA programs. *)

(** Most of the LLVM instructions define the uid associated
  with their program point.  Some (like [store], [void] calls, and the [terminator]s)
  do not. *)
Definition def_at_pt (g:cfg) (p:pt) (lid:local_id) : Prop :=
  pt_exists g p /\ pt_defines p lid.

(** The definition of id dominates its use at point pt *)
Inductive well_scoped_use_at_pt (g:cfg) (p:pt) : ident -> Prop :=
| ws_global : forall id, In id (glbl g) -> pt_exists g p -> well_scoped_use_at_pt g p id
| ws_local : forall lid p', def_at_pt g p' lid -> SDom g p' p -> well_scoped_use_at_pt g p (ID_Local lid).

(** All uses of a [uid] must be strictly dominated by their definitions. *)
Definition wf_use (g:cfg) (ids:list ident) (p:pt) : Prop :=
  forall id, In id ids -> well_scoped_use_at_pt g p id.


(** *** Well-formed phi nodes *)
(**  Consider [ %x = phi [lbl1:v1, ...,lbln:vn] ].  This is well formed
     when every predecessor block with terminator program point p' 
     has a label associated with value v.  Moreover, if v uses an id then
     the definition of the uid strictly dominates p'.
*)

Definition wf_phi_args (g:cfg) (entry:pt) (args:list (block_id * value)) :=
  forall pred, edge_pt g pred entry ->
          exists b t, (code g) pred = Some (Jump b t) /\
                 exists v, In (b,v) args /\ wf_use g (value_uses v) pred.

Inductive wf_phis (CFG : cfg) (entry:pt) (q : pt) : pt -> list (local_id * instr) -> Prop :=
| wf_phis_nil : pt_exists CFG q ->
                wf_phis CFG entry q q []

| wf_phis_cons :
    forall p p' x t args rest,
    (code CFG p) = Some (Step (INSTR_Phi t args) p') ->
    wf_phi_args CFG entry args ->
    wf_phis CFG entry q p' rest ->
    wf_phis CFG entry q p ((x, INSTR_Phi t args) :: rest) .

Inductive wf_cmd (g:cfg) (p:pt) : cmd -> Prop :=
| wf_step : forall (i:instr) (q:pt)
              (Hq : pt_exists g q)
              (Huse: wf_use g (instr_uses i) p),
    wf_cmd g p (Step i q)

| wf_jump : forall (bn:block_id) (t:terminator)
              (Huse: wf_use g (terminator_uses t) p)
              (Hlbls: Forall (fun tgt => exists p', exists xs, exists q,
                             (phis g tgt) = Some (Phis p' xs q) 
                             /\ wf_phis g p' q p' xs
                      )
                      (lbls t)),
    wf_cmd g p (Jump bn t).


(* TODO: do we have to worry about locals shadowing function parameters? 
   Could add: forall lid, In (ID_Local lid) (glbl CFG) -> (code CFG) (IId lid) = None

   - also, somewhere probably need that globals and function parameters are distinct
 *)

Definition wf_cfg (CFG : cfg) : Prop :=
  pt_exists CFG (init CFG)
  /\ forall p, ~ edge_pt CFG p (init CFG)            
  /\ (forall p cmd, (code CFG p) = Some cmd -> wf_cmd CFG p cmd)
.

(*
  Definition wf_phi_args (g:Cfg.t) (i:insn) (p:pc) : Prop :=
    forall pred, edge_pt g pred (entry_of_pc p) ->
      (exists v, In (lbl_of pred, v) (insn_phis i)) /\
      (forall uid, In (lbl_of pred, val_uid uid) (insn_phis i) -> 
          uid_sdom_pc g uid pred).

  Definition wf_phi_pred (g:Cfg.t) (i:insn) (p:pc) : Prop :=
    forall l v, In (l, v) (insn_phis i) ->
      (exists pred, edge_pt g pred (entry_of_pc p) /\ lbl_of pred = l).

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
      (Hwfentry : forall p, ~ edge_pt g p (block_entry (entry_block g))),
      wf_prog g.


            
Lemma wf_cfg_edge_pt : forall g p1 p2,
    wf_cfg g -> pt_exists g p1 -> edge_pt g p1 p2 -> pt_exists g p2.
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
*)





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
  
Fixpoint lookup_block bs block_id : option block :=
  find (fun b => if (blk_id b) == block_id then true else false) bs.

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

Definition cfg_of_definition (g:list ident) (d:definition) : option cfg :=
  'init <- init_of_definition d;
    Some {| init := init;
            code := code_of_definition d;
            phis := phis_of_definition d;
            glbl := g;
         |}.
            
Definition fcfg := function_id -> option (list local_id * cfg).

Definition globals_of (tle : toplevel_entity) : list ident :=
  match tle with
  | TLE_Declaration d => [ID_Global (dc_name d)]
  | TLE_Definition d => [ID_Global (dc_name (df_prototype d))]
  | TLE_Global g => [ID_Global (g_ident g)]
  | _ => []
  end.

Definition globals (ets : list toplevel_entity) : list ident :=
  List.fold_right (fun tle acc => (globals_of tle) ++ acc) [] ets.

Fixpoint entities_to_funs ets fid : option (list local_id * cfg) :=
  'd <- lookup_function_definition ets fid;
    let args := List.map (fun x => ID_Local x) (df_args d) in
    let g := globals ets in
    'cfg <- cfg_of_definition (g++args) d;
    Some (df_args d, cfg).

