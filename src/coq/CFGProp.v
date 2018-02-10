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
Require Import Vellvm.Ollvm_ast Vellvm.CFG Vellvm.Dom.
Require Import Vellvm.Classes.
Require Vellvm.AstLib.
Import ListNotations.
Open Scope list_scope.

(* invariants of the CFG machine -------------------------------------------- *)

Lemma incr_pc_in_block: forall CFG p1 p2, incr_pc CFG p1 = Some p2 -> (fn p1 = fn p2) /\ (bk p1 = bk p2).
Proof.
  intros CFG p1 p2 H.
  unfold incr_pc in H.
  destruct p1.
  destruct (find_function CFG fn); simpl in H; try solve [inversion H].
  destruct (find_block (blks (df_instrs d)) bk); simpl in H; try solve [inversion H].
  destruct (block_to_cmd b pt); simpl in H; try solve [inversion H].
  destruct p. destruct o; try inversion H.
  simpl. split; reflexivity.
Qed.  

Lemma find_block_same_fid : forall CFG fid br phis p,
    find_block_entry CFG fid br = Some (BlockEntry phis p) -> (fn p) = fid.
Proof.
  intros CFG fid br phis p H.
  unfold find_block_entry in H.
  destruct (find_function CFG fid); simpl in H; try solve [inversion H].
  destruct (find_block (blks (df_instrs d)) br); simpl in H; try solve [inversion H].
  destruct b. unfold block_to_entry in H. simpl in H. inversion H.
  simpl. reflexivity.
Qed.  
  
    

(* syntactic structure ------------------------------------------------------ *)

Inductive CFG_has_code_at (CFG:mcfg) (P:pc -> Prop) : pc -> code -> Prop :=
| has_code_nil :
    forall p, P p -> CFG_has_code_at CFG P p []
| has_code_cons :
    forall p iid instr pc_next cd
      (HF: fetch CFG p = Some (Inst instr))
      (Hiid: (pt p) = iid)
      (Hincr: incr_pc CFG p = Some pc_next)
      (Hcd: CFG_has_code_at CFG P pc_next cd),
      CFG_has_code_at CFG P p ((iid,instr)::cd).
Hint Constructors CFG_has_code_at.

Lemma CFG_has_code_app :
  forall CFG P (cd1 cd2:code) (pc1 pc2:pc)
    (H1: CFG_has_code_at CFG (fun p => p = pc2) pc1 cd1)
    (H2: CFG_has_code_at CFG P pc2 cd2),
    CFG_has_code_at CFG P pc1 (cd1 ++ cd2).
Proof.
  intros CFG P cd1 cd2 pc1 pc2 H1.
  remember (fun p => p = pc2) as Q.
  revert cd2.
  induction H1; intros cd2 H2; simpl in *; auto.
  - subst. subst. auto.
  - eapply has_code_cons; eauto.
Qed.    

Lemma CFG_has_code_app_inv :
  forall CFG P pc1 (cd1 cd2:code)
    (H:CFG_has_code_at CFG P pc1 (cd1 ++ cd2)),
  exists pc2,
    CFG_has_code_at CFG (fun p => p = pc2) pc1 cd1 /\
    CFG_has_code_at CFG P pc2 cd2.
Proof.
  intros CFG P pc1 cd1.
  revert pc1.
  induction cd1; intros pc1 cd2 H; inversion H; subst; simpl in *; auto.
  - exists pc1. split; eauto.
  - exists pc1. subst. split; eauto.
  - apply IHcd1 in Hcd.
    destruct Hcd as [pc2 [HA HB]].
    exists pc2. split; eauto.
Qed.


Definition CFG_has_pc (CFG:mcfg) (p:pc) : Prop :=
  exists cmd, fetch CFG p = Some cmd.

Definition CFG_fun_has_block_id (CFG:mcfg) (fid:function_id) (bid:block_id) phis (p:pc) : Prop :=
  find_block_entry CFG fid bid = Some (BlockEntry phis p) /\ CFG_has_pc CFG p. 


Inductive CFG_fun_has_terminator_lbls (CFG:mcfg) (fid:function_id) : terminator -> Prop :=
| lbls_Ret : forall v, CFG_fun_has_terminator_lbls CFG fid (TERM_Ret v)
| lbls_Ret_void : CFG_fun_has_terminator_lbls CFG fid TERM_Ret_void
| lbls_TERM_Br :
    forall v br1 phis1 p1 br2 phis2 p2
      (Hbr1 : CFG_fun_has_block_id CFG fid br1 phis1 p1)
      (Hbr2 : CFG_fun_has_block_id CFG fid br2 phis2 p2),
      CFG_fun_has_terminator_lbls CFG fid (TERM_Br v br1 br2)
| lbls_TERM_Br_1 :
    forall br phis p
      (Hbr : CFG_fun_has_block_id CFG fid br phis p),
      CFG_fun_has_terminator_lbls CFG fid (TERM_Br_1 br)
| lbls_Resume : forall v, CFG_fun_has_terminator_lbls CFG fid (TERM_Resume v)
.
(* TODO:  Add these cases:
  | TERM_Switch     (v:tvalue) (default_dest:block_id) (brs: list (tvalue * block_id))
  | TERM_IndirectBr 
  | TERM_Invoke     (fnptrval:tident) (args:list tvalue) (to_label:block_id) (unwind_label:block_id)
  .
*)


Inductive CFG_has_terminator_at (CFG:mcfg) : pc -> instr_id -> terminator -> Prop :=
| CFG_has_termintator_intro :
    forall p iid t
      (HF: fetch CFG p = Some (Term t))
      (Hiid: (pt p) = iid)
      (Hbrs: CFG_fun_has_terminator_lbls CFG (fn p) t),
      CFG_has_terminator_at CFG p iid t.


Inductive CFG_fun_has_block (CFG:mcfg) (fid:function_id) (b:block) phis : Prop :=
| CFG_fun_has_block_intro:
    forall
      (HFind: find_block_entry CFG fid (blk_id b) = Some (BlockEntry phis (blk_entry_pc fid b)))      
      (Hcode: CFG_has_code_at CFG (fun q => q = blk_term_pc fid b) (blk_entry_pc fid b) (blk_code b))
      (Hterm: CFG_has_terminator_at CFG (blk_term_pc fid b) (blk_term_id b) (blk_terminator b))
    ,
      CFG_fun_has_block CFG fid b phis.


Definition CFG_fun_has_blocks (CFG:mcfg) (fid:function_id) (bs:list block) : Prop :=
  Forall (fun b => exists phis, CFG_fun_has_block CFG fid b phis /\ CFG_fun_has_terminator_lbls CFG fid (snd (blk_term b))) bs.


(* well formedness ---------------------------------------------------------- *)
(*
(* When does a cfg program point define a given local_id. *)
Definition pt_defines (p:pt) (lid:local_id) :=
  match p with
  | IId id => if id == lid then True else False
  | IVoid _ => False
  end.
*)

(* Which identifiers does an instruction use? *)
Fixpoint value_uses (v:value) : list ident :=
  match v with
  | VALUE_Ident id => [id]
  | VALUE_Integer _
  | VALUE_Float _ 
  | VALUE_Hex _        
  | VALUE_Bool _
  | VALUE_Null
  | VALUE_Zero_initializer
  | VALUE_Cstring _
  | VALUE_Undef => []

  | VALUE_Struct l
  | VALUE_Packed_struct l
  | VALUE_Array l
  | VALUE_Vector l => List.flat_map (fun x => value_uses (snd x)) l
  | OP_IBinop _ _ v1 v2
  | OP_ICmp _ _ v1 v2
  | OP_FBinop _ _ _ v1 v2
  | OP_FCmp _ _ v1 v2 => (value_uses v1) ++ (value_uses v2)
  | OP_Conversion _ _ v _ => value_uses v
  | OP_GetElementPtr _ (_,ptr) idxs => (value_uses ptr) ++ (List.flat_map (fun x => value_uses (snd x)) idxs)
  | OP_ExtractElement  (_,vec) (_,idx) => (value_uses vec) ++ (value_uses idx)
  | OP_InsertElement (_,vec) (_,elt) (_,idx) => (value_uses vec) ++ (value_uses elt) ++ (value_uses idx)
  | OP_ShuffleVector (_, vec1) (_,vec2) (_,idxmask) => (value_uses vec1) ++ (value_uses vec2) ++ (value_uses idxmask)
  | OP_ExtractValue (_,vec) _ => value_uses vec
  | OP_InsertValue (_,vec) (_,elt) _ => (value_uses vec) ++ (value_uses elt)
  | OP_Select (_,cnd) (_,v1) (_,v2) => (value_uses cnd) ++ (value_uses v1) ++ (value_uses v2)
  end.

Definition tvalue_uses (tv:tvalue) : list ident := value_uses (snd tv).

Definition phi_uses (i:phi) : (list ident) :=
  match i with
  | Phi  t args => List.flat_map (fun x => value_uses (snd x)) args
  end.

(* over-approximation: may include the same identifier more than once *)
Definition instr_uses (i:instr) : (list ident) :=
  match i with
  | INSTR_Op op => value_uses op                         
  | INSTR_Call (_, fid) args => [fid] ++ (List.flat_map tvalue_uses args)
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

(*
Definition cmd_uses_local (g:cfg) (p:pt) (id:local_id) : Prop :=
  match (code g) p with
  | Some (Step ins _) => In (ID_Local id) (instr_uses ins)
  | Some (Jump _ t) => In (ID_Local id) (terminator_uses t)
  | None => False
  end.
*)             

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

(*

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
  Definition eq_dec_V := AstLib.eq_dec_instr_id.
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

            
Lemma wf_cfg_edge_pt : forall g p1 p2,
    wf_cfg g -> pt_exists g p1 -> edge_pt g p1 p2 -> pt_exists g p2.
Proof.
  intros g p1 p2 H H0 H1.
  destruct H as [Hinit [Hintro Hcmd]].
  inversion H1; subst.
  - apply Hcmd in H. inversion H. exact Hq.
  - apply Hcmd in H.
    inversion H. subst. 
    eapply Forall_forall in Hlbls.
    Focus 2. apply H2.
    destruct Hlbls as [p' [xs' [q [Ha Hb]]]].
    rewrite H3 in Ha. inversion Ha. subst.
    induction Hb.
    * exact H4.
    * exists (Step (INSTR_Phi t0 args) p'0).
      exact H4.
Unshelve. auto.
Qed.      


(* domination trees --------------------------------------------------------- *)

  (* Quite hard to prove this:
      - need to know that Dom can be definied equivalently by quantifying over 
        all acyclic paths from entry
      - need to know that there are a finite number of acyclic paths (and hence can
        be enumerated)  DFS
      - would work better with adjacency list representation of the graph

  *)
  Lemma dom_dec : forall (g:cfg) (v1 v2 : pt), {Dom g v1 v2} + {~Dom g v1 v2}.
  Proof.
    intros g v1 v2.
  Admitted.
  

  Inductive vtree (A:Type) : Type :=
  | vnode (v:A) (cs:list (vtree A)).

  Arguments vnode {A} _ _.
  
  Inductive dom_tree (g:cfg) : instr_id -> (vtree instr_id) -> Prop :=
  | dom_tree_intro:
      forall (v:instr_id) (cs:list (vtree instr_id)), 
        (forall u, IDom g v u -> exists (t:vtree instr_id), In t cs /\ dom_tree g u t) ->
        (forall t, In t cs -> exists u, IDom g v u /\ dom_tree g u t) ->
        dom_tree g v (vnode v cs). 

  Lemma dom_tree_exists : forall (g:cfg), exists (t:vtree instr_id), dom_tree g (init g) t.
  Admitted.



*)