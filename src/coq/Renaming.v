(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

From Coq Require Import 
     ZArith Ascii Strings.String Setoid.

From ExtLib Require Import
     Programming.Eqv
     Structures.Monads.

Require Import ITree.ITree.

From Vellvm Require Import 
     Error
     Util
     LLVMAst
     AstLib
     CFG
     DynamicValues
     StepSemantics
     Memory
     LLVMIO.




Import EqvNotation.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope eq_itree_scope.

Module RENAMING
       (A:MemoryAddress.ADDRESS)
       (LLVMIO:LLVM_INTERACTIONS(A)).

  Module SS := StepSemantics A LLVMIO.
  Import SS.
  Import LLVMIO.
  
Class Swap (A:Type) := swap : raw_id -> raw_id -> A -> A.

Class SwapLaws (A:Type) `{Swap A} := {
  swap_same_id :
    forall (id:raw_id) (x:A), swap id id x = x;

  swap_comm:
    forall id1 id2 (x:A), swap id1 id2 x = swap id2 id1 x;

  swap_swap_id :
    forall id1 id2 (x:A), swap id1 id2 (swap id1 id2 x) = x
}.

Class SwapInvariant (A:Type) `{Swap A} := {
  swap_invariant :
    forall id1 id2 (x:A), swap id1 id2 x = x
}.

Definition swap_raw_id (id1 id2:raw_id) (id:raw_id) : raw_id :=
  if id ~=? id1 then id2 else
    if id ~=? id2 then id1 else
      id.
Instance swap_of_raw_id : Swap raw_id := swap_raw_id.
Hint Unfold swap_of_raw_id.

Ltac unfold_swaps :=
  repeat match goal with
         | [H : context [swap _ _ _] |- _] => unfold swap in H; autounfold in H
         | [H : _ |- context[swap _ _ _] ] => unfold swap; autounfold
         end.

Ltac simpl_ifs :=
  repeat match goal with
         | [_ : context [if ?X then _ else _] |- _] => destruct (X)
         | [_ : _ |- context [if ?X then _ else _ ]] => destruct (X)
         end.

Program Instance raw_id_swaplaws : SwapLaws raw_id.
Next Obligation.
  unfold_swaps. unfold swap_raw_id.
  destruct (x ~=? id); auto.
Qed.
Next Obligation.
  unfold_swaps. unfold swap_raw_id. simpl_ifs; subst; auto.
  unfold eqv, eqv_raw_id in *. subst. reflexivity.
Qed.
Next Obligation.
  unfold_swaps. unfold swap_raw_id. simpl_ifs; subst; unfold eqv, eqv_raw_id in *; subst; auto.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
Qed.    
  

Definition swap_ident (id1 id2:raw_id) (id:ident) : ident :=
  match id with
  | ID_Global i => ID_Global (swap id1 id2 i)
  | ID_Local i => ID_Local (swap id1 id2 i)
  end.
Instance swap_of_ident : Swap ident := swap_ident.
Program Instance ident_swaplaws : SwapLaws ident.
Next Obligation.
  unfold_swaps; unfold swap_of_ident; destruct x; simpl; rewrite swap_same_id; reflexivity.
Qed.
Next Obligation.
  unfold_swaps; unfold swap_of_ident; destruct x; simpl; rewrite swap_comm; reflexivity.
Qed.
Next Obligation.
  unfold_swaps; unfold swap_of_ident; destruct x; simpl; rewrite swap_swap_id; reflexivity.
Qed.  


Instance swap_of_pair {A B} `(SA:Swap A) `(SB:Swap B) : Swap (A * B)%type :=
  fun id1 id2 p => (swap id1 id2 (fst p), swap id1 id2 (snd p)).
Hint Unfold swap_of_pair.

Program Instance swap_laws_pair {A B} `(SA:Swap A) `(SB:Swap B) `(SLA:SwapLaws A) `(SLB:SwapLaws B) : SwapLaws (A*B)%type.
Next Obligation.
  unfold swap. unfold swap_of_pair.
  rewrite swap_same_id. rewrite swap_same_id. reflexivity.
Qed.  
Next Obligation.
  unfold swap. unfold swap_of_pair. simpl.
  rewrite swap_comm. rewrite (@swap_comm B) at 1. reflexivity. assumption.
Qed.
Next Obligation.
  unfold swap. unfold swap_of_pair. simpl.
  rewrite swap_swap_id. rewrite (@swap_swap_id B) at 1. reflexivity. assumption.
Qed.

Instance swap_of_option {A} `(SA:Swap A) : Swap (option A) :=
  fun id1 id2 opt => match opt with None => None | Some x => Some (swap id1 id2 x) end.
Hint Unfold swap_of_option.

Instance swap_of_list {A} `(SA:Swap A) : Swap (list A) :=
  fun id1 id2 l => List.map (swap id1 id2) l.
Hint Unfold swap_of_list.

Instance swap_of_err {A} `(SA:Swap A) : Swap (err A) :=
  fun id1 id2 e =>
    match e with 
    | inl s => inl s
    | inr a => inr (swap id1 id2 a)
    end.
Hint Unfold swap_of_err.

Instance swap_of_bool : Swap bool :=
  fun id1 id2 b => b.

Instance swap_of_nat : Swap nat :=
  fun id1 id2 n => n.

Instance swap_of_int : Swap int :=
  fun id1 id2 n => n.

Instance swap_of_string : Swap string :=
  fun id1 id2 s => s.

Instance swap_of_ibinop : Swap ibinop :=
  fun id1 id2 n => n.

Instance swap_of_fbinop : Swap fbinop :=
  fun id1 id2 n => n.

Instance swap_of_icmp : Swap icmp :=
  fun id1 id2 n => n.

Instance swap_of_fcmp : Swap fcmp :=
  fun id1 id2 n => n.

Hint Unfold swap_of_bool swap_of_nat swap_of_string swap_of_int swap_of_ibinop swap_of_fbinop swap_of_icmp swap_of_fcmp.

Fixpoint swap_typ (id1 id2:raw_id) (t:typ) : typ :=
  match t with
  | TYPE_Pointer t' => TYPE_Pointer (swap_typ id1 id2 t')
  | TYPE_Array sz t' => TYPE_Array sz (swap_typ id1 id2 t')
  | TYPE_Function ret args => TYPE_Function (swap_typ id1 id2 ret) (List.map (swap_typ id1 id2) args)
  | TYPE_Struct fields => TYPE_Struct (List.map (swap_typ id1 id2) fields)
  | TYPE_Packed_struct fields => TYPE_Packed_struct (List.map (swap_typ id1 id2) fields)
  | TYPE_Vector sz t' => TYPE_Vector sz (swap_typ id1 id2 t')
  | TYPE_Identified id => TYPE_Identified (swap id1 id2 id)
  | _ => t
  end.
(* Hint Unfold swap_typ.*) (* DO WE WANT THESE UNFOLD HINTS? *)

Instance swap_of_typ : Swap typ := swap_typ.
Hint Unfold swap_of_typ.

Instance swap_of_dtyp : Swap dtyp :=
  fun id1 id2 d => d.

Instance swap_of_tident : Swap tident := swap.
Hint Unfold swap_of_tident.

Fixpoint swap_exp (id1 id2:raw_id) (e:exp) : exp :=
  match e with
  | EXP_Ident id => EXP_Ident (swap id1 id2 id)
  | EXP_Integer _
  | EXP_Float   _
  | EXP_Double  _                
  | EXP_Hex     _
  | EXP_Bool    _
  | EXP_Null
  | EXP_Zero_initializer
  | EXP_Cstring _
  | EXP_Undef => e
  | EXP_Struct fields =>
    EXP_Struct (List.map (fun '(t,e) => (swap id1 id2 t, swap_exp id1 id2 e)) fields)
  | EXP_Packed_struct fields =>
    EXP_Packed_struct (List.map (fun '(t,e) => (swap id1 id2 t, swap_exp id1 id2 e)) fields)    
  | EXP_Array elts =>
    EXP_Array (List.map (fun '(t,e) => (swap id1 id2 t, swap_exp id1 id2 e)) elts)
  | EXP_Vector elts =>
    EXP_Vector (List.map (fun '(t,e) => (swap id1 id2 t, swap_exp id1 id2 e)) elts)
  | OP_IBinop iop t v1 v2 =>
    OP_IBinop (swap id1 id2 iop) (swap id1 id2 t) (swap_exp id1 id2 v1) (swap_exp id1 id2 v2)
  | OP_ICmp cmp t v1 v2 =>
    OP_ICmp (swap id1 id2 cmp) (swap id1 id2 t) (swap_exp id1 id2 v1) (swap_exp id1 id2 v2)
  | OP_FBinop fop fm t v1 v2 =>
    OP_FBinop (swap id1 id2 fop) fm (swap id1 id2 t) (swap_exp id1 id2 v1) (swap_exp id1 id2 v2)    
  | OP_FCmp cmp t v1 v2 =>
    OP_FCmp (swap id1 id2 cmp) (swap id1 id2 t) (swap_exp id1 id2 v1) (swap_exp id1 id2 v2)    
  | OP_Conversion conv t_from v t_to =>
    OP_Conversion conv (swap id1 id2 t_from) (swap_exp id1 id2 v) (swap id1 id2 t_to)
  | OP_GetElementPtr t ptrval idxs =>
    OP_GetElementPtr (swap id1 id2 t) (swap id1 id2 (fst ptrval), swap_exp id1 id2 (snd ptrval))
                     (List.map (fun '(t,e) => (swap id1 id2 t, swap_exp id1 id2 e)) idxs)
  | OP_ExtractElement vec idx =>
    OP_ExtractElement (swap id1 id2 (fst vec), swap_exp id1 id2 (snd vec))
                      (swap id1 id2 (fst idx), swap_exp id1 id2 (snd idx))
  | OP_InsertElement  vec elt idx =>
    OP_InsertElement (swap id1 id2 (fst vec), swap_exp id1 id2 (snd vec))
                     (swap id1 id2 (fst elt), swap_exp id1 id2 (snd elt))                     
                     (swap id1 id2 (fst idx), swap_exp id1 id2 (snd idx))
  | OP_ShuffleVector vec1 vec2 idxmask =>
    OP_ShuffleVector (swap id1 id2 (fst vec1), swap_exp id1 id2 (snd vec1))
                     (swap id1 id2 (fst vec2), swap_exp id1 id2 (snd vec2))                     
                     (swap id1 id2 (fst idxmask), swap_exp id1 id2 (snd idxmask))
  | OP_ExtractValue  vec idxs =>
    OP_ExtractValue  (swap id1 id2 (fst vec), swap_exp id1 id2 (snd vec))
                     idxs
  | OP_InsertValue vec elt idxs =>
    OP_InsertValue (swap id1 id2 (fst vec), swap_exp id1 id2 (snd vec))
                   (swap id1 id2 (fst elt), swap_exp id1 id2 (snd elt))
                   idxs
  | OP_Select cnd v1 v2 =>
    OP_Select (swap id1 id2 (fst cnd), swap_exp id1 id2 (snd cnd))
              (swap id1 id2 (fst v1), swap_exp id1 id2 (snd v1))
              (swap id1 id2 (fst v2), swap_exp id1 id2 (snd v2))
  end.

Instance swap_of_exp : Swap exp := swap_exp.
Hint Unfold swap_of_exp.

Definition swap_instr_id (id1 id2:raw_id) (i:instr_id) : instr_id :=
  match i with
  | IId id => IId (swap id1 id2 id)
  | IVoid n => IVoid n  (* TODO: support renaming these too? *)
  end.

Instance swap_of_instr_id : Swap instr_id := swap_instr_id.
Hint Unfold swap_of_instr_id.

Definition swap_phi (id1 id2:raw_id) (p:phi) : phi :=
  match p with
  | Phi t args => Phi (swap id1 id2 t) (swap id1 id2 args)
  end.
Instance swap_of_phi : Swap phi := swap_phi.
Hint Unfold swap_of_phi.

Definition swap_instr (id1 id2:raw_id) (ins:instr) : instr :=
  match ins with
  | INSTR_Op op => INSTR_Op (swap id1 id2 op)
  | INSTR_Call fn args => INSTR_Call (swap id1 id2 fn) (swap id1 id2 args)
  | INSTR_Alloca t nb align =>
    INSTR_Alloca (swap id1 id2 t) (swap id1 id2 nb) align
  | INSTR_Load volatile t ptr align =>
    INSTR_Load volatile (swap id1 id2 t) (swap id1 id2 ptr) align
  | INSTR_Store volatile val ptr align =>
    INSTR_Store volatile (swap id1 id2 val) (swap id1 id2 ptr) align
  | INSTR_Comment _
  | INSTR_Fence
  | INSTR_AtomicCmpXchg
  | INSTR_AtomicRMW
  | INSTR_Unreachable
  | INSTR_VAArg
  | INSTR_LandingPad => ins
  end.
Instance swap_of_instr : Swap instr := swap_instr.
Hint Unfold swap_of_instr.

Definition swap_terminator (id1 id2:raw_id) (trm:terminator) : terminator :=
  match trm with
  | TERM_Ret  v => TERM_Ret (swap id1 id2 v)
  | TERM_Ret_void => TERM_Ret_void
  | TERM_Br v br1 br2 => TERM_Br (swap id1 id2 v) (swap id1 id2 br1) (swap id1 id2 br2)
  | TERM_Br_1 br => TERM_Br_1 (swap id1 id2 br)
  | TERM_Switch  v default_dest brs =>
    TERM_Switch (swap id1 id2 v) (swap id1 id2 default_dest) (swap id1 id2 brs)
  | TERM_IndirectBr v brs =>
    TERM_IndirectBr (swap id1 id2 v) (swap id1 id2 brs)
  | TERM_Resume v => TERM_Resume (swap id1 id2 v)
  | TERM_Invoke fnptrval args to_label unwind_label =>
    TERM_Invoke (swap id1 id2 fnptrval) (swap id1 id2 args) (swap id1 id2 to_label) (swap id1 id2 unwind_label)
  end.
Instance swap_of_terminator : Swap terminator := swap_terminator.
Hint Unfold swap_of_terminator.

Instance swap_of_param_attr : Swap param_attr :=
  fun id1 id2 l => l.
Instance swap_of_fn_attr : Swap fn_attr :=
  fun id1 id2 l => l.
Instance swap_of_cconv : Swap cconv :=
  fun id1 id2 l => l.
Instance swap_of_linkage : Swap linkage :=
  fun id1 id2 l => l.
Instance swap_of_visibility : Swap visibility :=
    fun id1 id2 l => l.
Instance swap_of_dll_storage : Swap dll_storage :=
    fun id1 id2 l => l.
Instance swap_of_thread_local_storage : Swap thread_local_storage :=
  fun id1 id2 l => l.

Hint Unfold swap_of_param_attr swap_of_fn_attr swap_of_cconv swap_of_linkage swap_of_visibility swap_of_dll_storage swap_of_thread_local_storage.

Definition swap_global (id1 id2:raw_id) (g:global) : global :=
  mk_global 
      (swap id1 id2 (g_ident g))
      (swap id1 id2 (g_typ g))     
      (swap id1 id2 (g_constant g))
      (swap id1 id2 (g_exp g))
      (swap id1 id2 (g_linkage g))
      (swap id1 id2 (g_visibility g))
      (swap id1 id2 (g_dll_storage g))
      (swap id1 id2 (g_thread_local g))
      (swap id1 id2 (g_unnamed_addr g))
      (swap id1 id2 (g_addrspace g))
      (swap id1 id2 (g_externally_initialized g))
      (swap id1 id2 (g_section g))
      (swap id1 id2 (g_align g)).
Hint Unfold swap_global.
Instance swap_of_global : Swap global := swap_global.
Hint Unfold swap_of_global.

Definition swap_declaration (id1 id2:raw_id) (d:declaration) : declaration :=
  mk_declaration
    (swap id1 id2 (dc_name d))
    (swap id1 id2 (dc_type d))
    (swap id1 id2 (dc_param_attrs d))
    (swap id1 id2 (dc_linkage d))
    (swap id1 id2 (dc_visibility d))
    (swap id1 id2 (dc_dll_storage d))
    (swap id1 id2 (dc_cconv d))
    (swap id1 id2 (dc_attrs d))
    (swap id1 id2 (dc_section d))
    (swap id1 id2 (dc_align d))
    (swap id1 id2 (dc_gc d)).
Hint Unfold swap_declaration.
Instance swap_of_declaration : Swap declaration := swap_declaration.    
Hint Unfold swap_of_declaration.

Definition swap_block (id1 id2:raw_id) (b:block) : block :=
  mk_block (swap id1 id2 (blk_id b))
           (swap id1 id2 (blk_phis b))
           (swap id1 id2 (blk_code b))
           (swap id1 id2 (blk_term b))
           (blk_comments b).
Hint Unfold swap_block.  
Instance swap_of_block : Swap block := swap_block.
Hint Unfold swap_of_block.

Definition swap_definition {FnBody:Set} `{SF: Swap FnBody} (id1 id2:raw_id) (d:definition FnBody) : definition FnBody :=
  mk_definition _
    (swap id1 id2 (df_prototype d))
    (swap id1 id2 (df_args d))
    (swap id1 id2 (df_instrs d)).
Hint Unfold swap_definition.

Instance swap_of_definition {FnBody:Set} `{SF:Swap FnBody} : Swap (definition FnBody) :=
  swap_definition.
Hint Unfold swap_of_definition.


Fixpoint swap_metadata (id1 id2:raw_id) (m:metadata) : metadata :=
  match m with
  | METADATA_Const  tv => METADATA_Const (swap id1 id2 tv)
  | METADATA_Null => METADATA_Null
  | METADATA_Id id => METADATA_Id (swap id1 id2 id)
  | METADATA_String str => METADATA_String (swap id1 id2 str)
  | METADATA_Named strs => METADATA_Named (swap id1 id2 strs)
  | METADATA_Node mds => METADATA_Node (List.map (swap_metadata id1 id2) mds)
  end.
Instance swap_of_metadata : Swap metadata := swap_metadata.
Hint Unfold swap_of_metadata.

Definition swap_toplevel_entity {FnBody:Set} `{SF:Swap FnBody} (id1 id2:raw_id) (tle:toplevel_entity FnBody) :=
  match tle with
  | TLE_Comment msg => tle
  | TLE_Target tgt => TLE_Target (swap id1 id2 tgt)
  | TLE_Datalayout layout => TLE_Datalayout (swap id1 id2 layout)
  | TLE_Declaration decl => TLE_Declaration (swap id1 id2 decl)
  | TLE_Definition defn => TLE_Definition (swap id1 id2 defn)
  | TLE_Type_decl id t => TLE_Type_decl (swap id1 id2 id) (swap id1 id2 t)
  | TLE_Source_filename s => TLE_Source_filename (swap id1 id2 s)
  | TLE_Global g => TLE_Global (swap id1 id2 g)
  | TLE_Metadata id md => TLE_Metadata (swap id1 id2 id) (swap id1 id2 md)
  | TLE_Attribute_group i attrs => TLE_Attribute_group (swap id1 id2 i) (swap id1 id2 attrs)
  end.

Instance swap_of_toplevel_entity {FnBody:Set} `{SF:Swap FnBody} : Swap (toplevel_entity FnBody) :=
  swap_toplevel_entity.
Hint Unfold swap_of_toplevel_entity.

Definition swap_modul {FnBody:Set} `{SF:Swap FnBody} (id1 id2:raw_id) (m:modul FnBody) : modul FnBody :=
  mk_modul _
    (swap id1 id2 (m_name m))
    (swap id1 id2 (m_target m))
    (swap id1 id2 (m_datalayout m))
    (swap id1 id2 (m_type_defs m))
    (swap id1 id2 (m_globals m))
    (swap id1 id2 (m_declarations m))
    (swap id1 id2 (m_definitions m)).
Hint Unfold swap_modul.

Instance swap_of_modul {FnBody:Set} `{SF:Swap FnBody} : Swap (modul FnBody) :=
  swap_modul.
Hint Unfold swap_of_modul.

Definition swap_pc (id1 id2:raw_id) (p:pc) : pc :=
  mk_pc (swap id1 id2 (fn p)) (swap id1 id2 (bk p)) (swap id1 id2 (pt p)).
Hint Unfold swap_pc.

Instance swap_of_pc : Swap pc := swap_pc.
Hint Unfold swap_of_pc.

Definition swap_cmd (id1 id2:raw_id) (c:cmd) : cmd :=
  match c with
  | Inst i => Inst (swap id1 id2 i)
  | Term t => Term (swap id1 id2 t)
  end.                    
Instance swap_of_cmd : Swap cmd := swap_cmd.
Hint Unfold swap_of_cmd.

Definition swap_cfg (id1 id2:raw_id) (CFG:cfg) : cfg :=
  mkCFG (swap id1 id2 (init CFG)) (swap id1 id2 (blks CFG)) (swap id1 id2 (args CFG)).
Hint Unfold swap_cfg.

Instance swap_of_cfg : Swap cfg := swap_cfg.
Hint Unfold swap_of_cfg.

Instance swap_of_mcfg : Swap mcfg := swap.
Hint Unfold swap_of_mcfg.


Instance swap_of_inttyp : forall {x:Z}, Swap (inttyp x) := fun _ id1 id2 a => a.
Instance swap_of_int1 : Swap int1 := fun id1 id2 a => a.
Instance swap_of_int32 : Swap int32 := fun id1 id2 a => a.
Instance swap_of_int64 : Swap int64 := fun id1 id2 a => a.
Instance swap_of_ll_double : Swap ll_double := fun id1 id2 a => a.
Instance swap_of_ll_float : Swap ll_float := fun id1 id2 a => a.
Hint Unfold swap_of_inttyp swap_of_int1 swap_of_int32 swap_of_int64 swap_of_ll_double swap_of_ll_float.

Instance swap_of_dvalue : Swap dvalue := fun (id1 id2 : raw_id) dv => dv.
Hint Unfold swap_of_dvalue.

Program Instance swap_invariant_dvalue_inst : SwapInvariant dvalue := _.
Next Obligation.
  constructor. intros. unfold swap. reflexivity.
Defined.  

Instance swap_of_IO X : Swap (IO X) := fun id1 id2 x => x.
Hint Unfold swap_of_IO.

Definition swap_itree {X E} `{Swap X} (id1 id2:raw_id) (t:itree E X) : itree E X :=
  ITree.map (swap id1 id2) t.
  
Instance swap_of_itree {X E} `{SX : Swap X} : Swap (itree E X) := swap_itree.
Hint Unfold swap_of_itree.


(* Parameter fold : forall A: Type, (key -> elt -> A -> A) -> t elt -> A -> A. *)
Definition swap_ENV {X} `{SX : Swap X} (id1 id2:raw_id) (m:ENV.t X) : ENV.t X :=
  ENV.fold (fun k v n => ENV.add (swap id1 id2 k) (swap id1 id2 v) n) m (ENV.empty X).
Hint Unfold swap_ENV.

Instance swap_of_ENV {X} `{SX : Swap X} : Swap (ENV.t X) := swap_ENV.
Hint Unfold swap_of_ENV.

Definition swap_frame (id1 id2:raw_id) (f:frame) : frame :=
  match f with
  | KRet e id q => KRet (swap id1 id2 e) (swap id1 id2 id) (swap id1 id2 q)
  | KRet_void e q => KRet_void (swap id1 id2 e) (swap id1 id2 q)
  end.

Instance swap_of_frame : Swap frame := swap_frame.
Hint Unfold swap_of_frame.

Definition swap_result (id1 id2:raw_id) (r:result) : result :=
  match r with
  | Done v => Done (swap id1 id2 v)
  | Step s => Step (swap id1 id2 s)
  end.       

Instance swap_of_result : Swap result := swap_result.
Hint Unfold swap_of_result.

Section PROOFS.

  (* TODO: Add to Coq Library *)
  Lemma Empty_Equals : forall {X} (e:ENV.t X), ENV.Empty e -> ENV.Equal (ENV.empty X) e.
  Proof.
    intros.
    apply ENVFacts.Equal_mapsto_iff.
    intros k x.
    pose (H1 := H k x). clearbody H1.
    split.
    intros H2.
    apply ENVFacts.empty_mapsto_iff in H2. contradiction.
    intros. contradiction.
  Qed.

  (* TODO: Add to Coq Library *)
  Lemma find_Empty_none : forall {X} (e:ENV.t X) (id:raw_id), ENV.Empty e -> ENV.find id e = None.
  Proof.
    intros.
    apply ENVFacts.not_find_in_iff.
    unfold not. intros H1.
    apply (@ENVFacts.empty_in_iff X id).
    apply Empty_Equals in H.
    rewrite H. assumption.
  Qed.

  Variable id1 id2 : raw_id.
  
  Lemma swap_raw_id_inj : forall (k j:raw_id), swap id1 id2 k = swap id1 id2 j -> k = j.
  Proof.
    intros.
    unfold_swaps. unfold swap_raw_id in *.
    simpl_ifs; unfold eqv, eqv_raw_id in *; subst; try reflexivity; try contradiction.
  Qed.
  
  Lemma swap_ENV_find : forall {X} `{SX : Swap X} (e:ENV.t X) (id:raw_id),
      (ENV.find (swap id1 id2 id) (swap id1 id2 e)) = swap id1 id2 (ENV.find id e).
  Proof.
    intros X SX. 
    unfold_swaps.
    intros e id.
    apply ENVProps.fold_rec.
    - intros m H.
      rewrite find_Empty_none. rewrite find_Empty_none. reflexivity. assumption. 
      apply ENV.empty_1.

    - intros k e0 a m' m'' H H0 H1 H2. 
      rewrite H1.
      repeat rewrite ENVFacts.add_o.
      destruct (ENVProps.F.eq_dec k id).
      subst.
      (* Set Printing All. (* The ENV.key vs. raw_id types in swap make destruction with the displayed syntax not work. *) *)
      destruct (RawIDOrd.eq_dec (swap_raw_id id1 id2 id) (swap_raw_id id1 id2 id)).
      (* Unset Printing All. *)
      simpl. reflexivity. contradiction.

      destruct (RawIDOrd.eq_dec (swap_raw_id id1 id2 k) (swap_raw_id id1 id2 id)).
      apply swap_raw_id_inj in e1. contradiction.
      apply H2.
  Qed.

  
  Lemma swap_lookup_env : forall {X} `{SX : Swap X} (e:ENV.t X) (id:raw_id),
      (lookup_env (swap id1 id2 e) (swap id1 id2 id) = swap id1 id2 (lookup_env e id)).
  Proof.
    intros.
    unfold lookup_env.
    rewrite swap_ENV_find.
    (* FIXME: error message doesn't work *)
    (* destruct (ENV.find id e); unfold_swaps; simpl; reflexivity. *)
  Admitted.

  Lemma swap_lookup_id : forall (g:genv) (e:env) (i:ident),
      lookup_id (swap id1 id2 g) (swap id1 id2 e) (swap id1 id2 i) = swap id1 id2 (lookup_id g e i).
  Proof.
    intros g e i.
    unfold lookup_id.
    destruct i; simpl; apply swap_lookup_env.
  Qed.
  
  Lemma swap_eval_i1_op : forall (iop:ibinop) (x y:inttyp 1),
      eval_int_op (swap id1 id2 iop) (swap id1 id2 x) (swap id1 id2 y) = swap id1 id2 (eval_int_op iop x y).
  Proof.
    unfold_swaps.
    intros iop x y.
    reflexivity.
  Qed.

  Lemma swap_eval_i32_op : forall (iop:ibinop) (x y:inttyp 32),
      eval_int_op (swap id1 id2 iop) (swap id1 id2 x) (swap id1 id2 y) = swap id1 id2 (eval_int_op iop x y).
  Proof.
    unfold_swaps.
    intros iop x y.
    reflexivity.
  Qed.

  Lemma swap_eval_i64_op : forall (iop:ibinop) (x y:inttyp 64),
      eval_int_op (swap id1 id2 iop) (swap id1 id2 x) (swap id1 id2 y) = swap id1 id2 (eval_int_op iop x y).
  Proof.
    unfold_swaps.
    intros iop x y. 
    reflexivity.
  Qed.

  Lemma swap_integer_op : forall (bits:Z) (iop:ibinop) (x y:inttyp bits),
   integer_op bits (swap id1 id2 iop) (swap id1 id2 x) (swap id1 id2 y) = swap id1 id2 (integer_op bits iop x y).
  Proof.
    intros bits iop x y.
    unfold_swaps.
    destruct (integer_op bits iop x y); reflexivity.
  Qed.


  Lemma swap_eval_iop : forall iop v1 v2,
      eval_iop (swap id1 id2 iop) (swap id1 id2 v1) (swap id1 id2 v2) =
      swap id1 id2 (eval_iop iop v1 v2).
  Proof.
    intros iop v1 v2.
    unfold_swaps.
    destruct (eval_iop iop v1 v2); reflexivity.
  Qed.

  Lemma swap_eval_icmp : forall icmp v1 v2,
      eval_icmp (swap id1 id2 icmp) (swap id1 id2 v1) (swap id1 id2 v2) =
      swap id1 id2 (eval_icmp icmp v1 v2).
  Proof.
    intros icmp v1 v2.
    unfold_swaps.
    destruct (eval_icmp icmp v1 v2); reflexivity.
  Qed.

  (*
  (* Before changing ITrees to records, we could prove _equality_ here.  Now we prove 
     only bisimulation?
   *)
  Lemma swap_raise {X} `{SX: Swap X} : forall s : string, (@raise string Trace _ _ s) ≅ (swap id1 id2 (@raise string Trace _ _ s)).
  Proof.
    intros s.
    econstructor.
    econstructor.
  Qed.    


  Lemma swap_ret {X E} `{SX: Swap X} : forall x, (Ret (swap id1 id2 x) : itree E (_+X)) ≅ swap id1 id2 (Ret x).
  Proof.
    intros x.
    econstructor.
    econstructor.
  Qed.


    Ltac bisim :=
    repeat (cbn; match goal with
                 | [H : _ |- go ?X ≅ swap ?ID1 ?ID2 (go ?Y) ] => econstructor
                 | [H : _ |- ?X ≅ swap ?ID1 ?ID2 ?X ] => econstructor; cbn                                  
                 | [ _ : _ |- match swap ?ID1 ?ID2 ?X with _ => _ end ≅ swap ?ID1 ?ID2 (match ?X with _ => _  end) ] => destruct X; cbn
                 | [ _ : _ |- eq_itreeF eq_itree ?X ?X ] => econstructor; cbn
                 | [ _ : _ |- eq_itreeF eq_itree (RetF ?X) (RetF ?Y) ] => econstructor; cbn
                 | [ _ : _ |- eq_itreeF eq_itree (TauF ?X) (TauF ?Y) ] => econstructor; cbn
                 | [ _ : _ |- eq_itreeF eq_itree (VisF _ ?X ?K) (VisF _ ?Y ?K2) ] => econstructor; cbn
                 | [ _ : _ |- (lift_err (swap ?ID1 ?ID2 ?E) ?k) ≅ swap ?ID1 ?ID2 (lift_err ?E ?k) ] => destruct E; cbn
                end).


  Lemma swap_lift_err {X:Type} `{SX: Swap X} :
      forall a, (fun x : err X => Ret (swap id1 id2 x)) a ≅ (lift_err (fun x : X => swap id1 id2 (ret x))) a.
  Proof.
    intros a.
    destruct a; cbn.
    - reflexivity.
    - constructor. econstructor.
  Qed.
    
    
  Lemma swap_bind {X Y} `{SX : Swap X} `{SY : Swap Y} `{SIY : SwapInvariant Y} : 
    forall (e : Trace Y) (k : Y -> Trace X),
      swap id1 id2 (bind e k) ≅ bind (swap id1 id2 e) (fun y => swap id1 id2 (k y)).
  Proof.
    cofix ch.
    intros e k.
    econstructor. 
    cbn.
    destruct (observe e).
    - cbn. destruct r; cbn.
      + econstructor.
      + rewrite swap_invariant. 
        destruct (observe (k y)) eqn:Heq; cbn; econstructor.
        * reflexivity.
        * intros. reflexivity.
    - econstructor. 
      pose bind_associativity as HA.
      unfold bind, monad_trace, bind_trace, ITree.bind in HA.
      
      
      
      
      
      
      
        
  Admitted.   




  
  Lemma swap_eval_exp : forall CFG g e top o,
      eval_exp (swap id1 id2 CFG) (swap id1 id2 g) (swap id1 id2 e) (swap id1 id2 top) (swap id1 id2 o) ≅
      swap id1 id2 (eval_exp CFG g e top o).
  Proof.
    intros CFG g e top.
    unfold err in *.
    induction o using exp_ind'; bisim.
    - cbn. rewrite swap_lookup_id. 
      bisim.
(*      
    - destruct (coerce_integer_to_int sz x); bisim.

    - destruct b; bisim.

    - destruct top. simpl.
      induction fields; simpl.
      + bisim.
      + destruct a. cbn. bisim.

      
    - cbn. econstructor. econstructor.

    - cbn. destruct top; try destruct d; simpl; try (econstructor; econstructor).

    - cbn. econstructor. 
      
*)
(* Change to the ITree affected the way that errors need to be handled here. *)      
    
  Admitted.

  

  Lemma swap_step : forall (CFG:mcfg) (s:state),
      eq_itree (step (swap id1 id2 CFG) (swap id1 id2 s)) (swap id1 id2 (step CFG s)).
  Proof.
    intros CFG.
    destruct s as [[[g pc] e] k].
    unfold_swaps. simpl.
  Admitted.
    
  
  Lemma swap_step_sem : forall (CFG:mcfg) (r:result),
      eq_itree (step_sem (swap id1 id2 CFG) (swap id1 id2 r)) (swap id1 id2 (step_sem CFG r)).
  Proof.
    intros CFG r.
    (*
    cofix swap_step_sem.
    destruct r.
    - rewrite Trace.matchM. simpl.
      assert (swap id1 id2 (step_sem CFG (Done v)) = Trace.idM (swap id1 id2 (step_sem CFG (Done v)))).
      rewrite Trace.matchM at 1. reflexivity.
      rewrite H. simpl. constructor.

      
    - unfold swap at 2. simpl.
      rewrite Trace.matchM. simpl.
    *)
    
  Admitted.    

    *)
End PROOFS.  
End RENAMING.

