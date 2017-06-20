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
  | SV (VALUE_Ident id) => [id]
  | SV (VALUE_Integer _)
  | SV (VALUE_Float _ )
  | SV (VALUE_Bool _)
  | SV (VALUE_Null)
  | SV (VALUE_Zero_initializer)
  | SV (VALUE_Cstring _)
  | SV (VALUE_None)
  | SV (VALUE_Undef) => []

  | SV (VALUE_Struct l)
  | SV (VALUE_Packed_struct l)
  | SV (VALUE_Array l)
  | SV (VALUE_Vector l) => List.flat_map (fun x => value_uses (snd x)) l
  | SV (OP_IBinop _ _ v1 v2) 
  | SV (OP_ICmp _ _ v1 v2)
  | SV (OP_FBinop _ _ _ v1 v2) 
  | SV (OP_FCmp _ _ v1 v2) => (value_uses v1) ++ (value_uses v2)
  | SV (OP_Conversion _ _ v _) => value_uses v
  | SV (OP_GetElementPtr _ (_,ptr) idxs) => (value_uses ptr) ++ (List.flat_map (fun x => value_uses (snd x)) idxs)
  | SV (OP_ExtractElement  (_,vec) (_,idx)) => (value_uses vec) ++ (value_uses idx)
  | SV (OP_InsertElement (_,vec) (_,elt) (_,idx)) => (value_uses vec) ++ (value_uses elt) ++ (value_uses idx)
  | SV (OP_ShuffleVector (_, vec1) (_,vec2) (_,idxmask)) => (value_uses vec1) ++ (value_uses vec2) ++ (value_uses idxmask)
  | SV (OP_ExtractValue (_,vec) _) => value_uses vec
  | SV (OP_InsertValue (_,vec) (_,elt) _) => (value_uses vec) ++ (value_uses elt)
  | SV (OP_Select (_,cnd) (_,v1) (_,v2)) => (value_uses cnd) ++ (value_uses v1) ++ (value_uses v2)
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