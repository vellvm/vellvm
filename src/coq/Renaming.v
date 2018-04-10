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
Require Import Vellvm.Classes Vellvm.Util.
Require Import Vellvm.LLVMAst Vellvm.AstLib Vellvm.CFG.
Require Import Vellvm.Memory.

Open Scope string_scope.

Class Swap (A:Type) := swap : raw_id -> raw_id -> A -> A.
Definition swap_raw_id (id1 id2:raw_id) (id:raw_id) : raw_id :=
  if id == id1 then id2 else
    if id == id2 then id1 else
      id.
Instance raw_id_swap : Swap raw_id := swap_raw_id.


Class SwapLaws (A:Type) `{Swap A} := {
  swap_same_id :
    forall (id:raw_id) (x:A), swap id id x = x;

  swap_comm:
    forall id1 id2 (x:A), swap id1 id2 x = swap id2 id1 x;
}.

Program Instance raw_id_swaplaws : SwapLaws raw_id.
Next Obligation.
  unfold swap. unfold raw_id_swap. unfold swap_raw_id.
  destruct (x == id); auto.
Qed.
Next Obligation.
  unfold swap. unfold raw_id_swap. unfold swap_raw_id.
  destruct (x == id1); auto.
  destruct (x == id2); auto. subst. reflexivity.
Qed.  

Definition swap_ident (id1 id2:raw_id) (id:ident) : ident :=
  match id with
  | ID_Global i => ID_Global (swap id1 id2 i)
  | ID_Local i => ID_Local (swap id1 id2 i)
  end.
Instance ident_swap : Swap ident := swap_ident.
Program Instance ident_swaplaws : SwapLaws ident.
Next Obligation.
  unfold swap. unfold ident_swap. unfold swap_ident. destruct x.
  rewrite swap_same_id. reflexivity.
  rewrite swap_same_id. reflexivity.
Qed.  

Instance swap_of_pair {A B} `(SA:Swap A) `(SB:Swap B) : Swap (A * B)%type :=
  fun id1 id2 p => (swap id1 id2 (fst p), swap id2 id2 (snd p)).

Program Instance swap_laws_pair {A B} `(SA:Swap A) `(SB:Swap B) `(SLA:SwapLaws A) `(SLB:SwapLaws B) : SwapLaws (A*B)%type.
Next Obligation.
  destruct x. unfold swap. simpl. rewrite swap_comm. reflexivity.
  unfold swap. simpl. rewrite swap_comm. reflexivity.
Qed.


Instance swap_of_option {A} `(SA:Swap A) : Swap (option A) :=
  fun id1 id2 opt => match opt with None => None | Some x => Some (swap id1 id2 x) end.

Instance swap_of_list {A} `(SA:Swap A) : Swap (list A) :=
  fun id1 id2 l => List.map (swap id1 id2) l.

Instance swap_of_bool : Swap bool :=
  fun id1 id2 b => b.

Instance swap_of_nat : Swap nat :=
  fun id1 id2 n => n.

Instance swap_of_int : Swap int :=
  fun id1 id2 n => n.


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

Instance swap_of_typ : Swap typ := swap_typ.

Instance swap_of_tident : Swap tident := swap.

Fixpoint swap_exp (id1 id2:raw_id) (e:exp) : exp :=
  match e with
  | EXP_Ident id => EXP_Ident (swap id1 id2 id)
  | EXP_Integer _
  | EXP_Float   _
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
    OP_IBinop iop (swap id1 id2 t) (swap_exp id1 id2 v1) (swap_exp id1 id2 v2)
  | OP_ICmp cmp t v1 v2 =>
    OP_ICmp cmp (swap id1 id2 t) (swap_exp id1 id2 v1) (swap_exp id1 id2 v2)
  | OP_FBinop fop fm t v1 v2 =>
    OP_FBinop fop fm (swap id1 id2 t) (swap_exp id1 id2 v1) (swap_exp id1 id2 v2)    
  | OP_FCmp cmp t v1 v2 =>
    OP_FCmp cmp (swap id1 id2 t) (swap_exp id1 id2 v1) (swap_exp id1 id2 v2)    
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

Instance swap_of_texp : Swap texp := swap.

Definition swap_instr_id (id1 id2:raw_id) (i:instr_id) : instr_id :=
  match i with
  | IId id => IId (swap id1 id2 id)
  | IVoid n => IVoid n  (* TODO: support renaming these too? *)
  end.

Instance swap_of_instr_id : Swap instr_id := swap_instr_id.

Definition swap_phi (id1 id2:raw_id) (p:phi) : phi :=
  match p with
  | Phi t args => Phi (swap id1 id2 t) (swap id1 id2 args)
  end.
Instance swap_of_phi : Swap phi := swap_phi.

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
  | INSTR_Fence
  | INSTR_AtomicCmpXchg
  | INSTR_AtomicRMW
  | INSTR_Unreachable
  | INSTR_VAArg
  | INSTR_LandingPad => ins
  end.
Instance swap_of_instr : Swap instr := swap_instr.

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
Instance swap_of_string : Swap string :=
  fun id1 id2 s => s.

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

Instance swap_of_global : Swap global := swap_global.

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
Instance swap_of_declaration : Swap declaration := swap_declaration.    

Definition swap_block (id1 id2:raw_id) (b:block) : block :=
  mk_block (swap id1 id2 (blk_id b))
           (swap id1 id2 (blk_phis b))
           (swap id1 id2 (blk_code b))
           (swap id1 id2 (blk_term b)).
  
Instance swap_of_block : Swap block := swap_block.

Definition swap_definition {FnBody:Set} `{SF: Swap FnBody} (id1 id2:raw_id) (d:definition FnBody) : definition FnBody :=
  mk_definition _
    (swap id1 id2 (df_prototype d))
    (swap id1 id2 (df_args d))
    (swap id1 id2 (df_instrs d)).

Instance swap_of_definition {FnBody:Set} `{SF:Swap FnBody} : Swap (definition FnBody) :=
  swap_definition.

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


Definition swap_toplevel_entity {FnBody:Set} `{SF:Swap FnBody} (id1 id2:raw_id) (tle:toplevel_entity FnBody) :=
  match tle with
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

Instance swap_of_tle {FnBody:Set} `{SF:Swap FnBody} : Swap (toplevel_entity FnBody) :=
  swap_toplevel_entity.

Definition swap_modul {FnBody:Set} `{SF:Swap FnBody} (id1 id2:raw_id) (m:modul FnBody) : modul FnBody :=
  mk_modul _
    (swap id1 id2 (m_name m))
    (swap id1 id2 (m_target m))
    (swap id1 id2 (m_datalayout m))
    (swap id1 id2 (m_type_defs m))
    (swap id1 id2 (m_globals m))
    (swap id1 id2 (m_declarations m))
    (swap id1 id2 (m_definitions m)).

Instance swap_of_modul {FnBody:Set} `{SF:Swap FnBody} : Swap (modul FnBody) :=
  swap_modul.

Definition swap_pc (id1 id2:raw_id) (p:pc) : pc :=
  mk_pc (swap id1 id2 (fn p)) (swap id1 id2 (bk p)) (swap id1 id2 (pt p)).

Instance swap_of_pc : Swap pc := swap_pc.

Definition swap_cmd (id1 id2:raw_id) (c:cmd) : cmd :=
  match c with
  | Inst i => Inst (swap id1 id2 i)
  | Term t => Term (swap id1 id2 t)
  end.                    

Instance swap_of_cmd : Swap cmd := swap_cmd.

Definition swap_cfg (id1 id2:raw_id) (CFG:cfg) : cfg :=
  mkCFG (swap id1 id2 (init CFG)) (swap id1 id2 (blks CFG)) (swap id1 id2 (args CFG)).

Instance swap_of_cfg : Swap cfg := swap_cfg.

Instance swap_of_mcfg : Swap mcfg := swap.


Instance swap_of_addr : Swap addr := fun id1 id2 a => a.
Instance swap_of_int1 : Swap LLVMBaseTypes.int1 := fun id1 id2 a => a.
Instance swap_of_int32 : Swap LLVMBaseTypes.int32 := fun id1 id2 a => a.
Instance swap_of_int64 : Swap LLVMBaseTypes.int64 := fun id1 id2 a => a.
Instance swap_of_ll_double : Swap LLVMBaseTypes.ll_double := fun id1 id2 a => a.
Instance swap_of_ll_float : Swap LLVMBaseTypes.ll_float := fun id1 id2 a => a.

Fixpoint swap_dvalue (id1 id2:raw_id) (dv:dvalue) : dvalue :=
  match dv with
  | DVALUE_FunPtr fid => DVALUE_FunPtr (swap id1 id2 fid)
  | DVALUE_Addr a => DVALUE_Addr (swap id1 id2 a)
  | DVALUE_I1 x => DVALUE_I1 (swap id1 id2 x)
  | DVALUE_I32 x => DVALUE_I32 (swap id1 id2 x)
  | DVALUE_I64 x => DVALUE_I64 (swap id1 id2 x)
  | DVALUE_Double x => DVALUE_Double (swap id1 id2 x)
  | DVALUE_Float x => DVALUE_Float (swap id1 id2 x)
  | DVALUE_Undef t v => DVALUE_Undef (swap id1 id2 t) (swap id1 id2 v)
  | DVALUE_Poison => DVALUE_Poison
  | DVALUE_None => DVALUE_None
  | DVALUE_Struct fields => DVALUE_Struct (List.map (fun '(t,e) => (swap id1 id2 t, swap_dvalue id1 id2 e)) fields)    
  | DVALUE_Packed_struct fields => DVALUE_Packed_struct (List.map (fun '(t,e) => (swap id1 id2 t, swap_dvalue id1 id2 e)) fields)    
  | DVALUE_Array elts => DVALUE_Array (List.map (fun '(t,e) => (swap id1 id2 t, swap_dvalue id1 id2 e)) elts)    
  | DVALUE_Vector elts => DVALUE_Vector (List.map (fun '(t,e) => (swap id1 id2 t, swap_dvalue id1 id2 e)) elts)    
  end.
  
Instance swap_of_dvalue : Swap dvalue := swap_dvalue.

Definition swap_IO {X} (id1 id2:raw_id) (x:IO X) : IO X:=
  match x with
  | Alloca t => Alloca (swap id1 id2 t)
  | Load t a => Load (swap id1 id2 t) (swap id1 id2 a)
  | Store a v => Store (swap id1 id2 a) (swap id1 id2 v)
  | GEP  t v vs => GEP (swap id1 id2 t) (swap id1 id2 v) (swap id1 id2 vs)
  | ItoP  t i => ItoP (swap id1 id2 t) (swap id1 id2 i)
  | PtoI t a => PtoI (swap id1 id2 t) (swap id1 id2 a)
  | Call t f args => Call (swap id1 id2 t) (swap id1 id2 f) (swap id1 id2 args)
  | DeclareFun f => DeclareFun (swap id1 id2 f)
  end.

Instance swap_of_IO {X} : Swap (IO X) := swap_IO.

CoFixpoint swap_Trace X `{Swap X} (id1 id2:raw_id) (t:Trace X) : Trace X :=
  match t with
  | Trace.Ret x => Trace.Ret (swap id1 id2 x)
  | Trace.Vis _ e k => Trace.Vis (swap id1 id2 e) (fun y => swap_Trace X id1 id2 (k y))
  | Trace.Tau k => Trace.Tau (swap_Trace X id1 id2 k)
  | Trace.Err s => Trace.Err s
  end.

Instance swap_of_Trace {X} `{SX : Swap X} : Swap (Trace X) := swap_Trace X.

Check ENV.fold.

(* Parameter fold : forall A: Type, (key -> elt -> A -> A) -> t elt -> A -> A. *)
Definition swap_ENV {X} `{SX : Swap X} (id1 id2:raw_id) (m:ENV.t X) : ENV.t X :=
  ENV.fold (fun k v n => ENV.add (swap id1 id2 k) (swap id1 id2 v) n) m (ENV.empty X).

Instance swap_of_ENV {X} `{SX : Swap X} : Swap (ENV.t X) := swap_ENV.


Definition swap_frame (id1 id2:raw_id) (f:frame) : frame :=
  match f with
  | KRet e id q => KRet (swap id1 id2 e) (swap id1 id2 id) (swap id1 id2 q)
  | KRet_void e q => KRet_void (swap id1 id2 e) (swap id1 id2 q)
  end.

Instance swap_of_frame : Swap frame := swap_frame.

Definition swap_result (id1 id2:raw_id) (r:result) : result :=
  match r with
  | Done v => Done (swap id1 id2 v)
  | Step s => Step (swap id1 id2 s)
  end.       

Instance stawp_of_result : Swap result := swap_result.


Section PROOFS.

  Variable id1 id2 : raw_id.

  Lemma swap_step_sem : forall (CFG:mcfg) (r:result),
      step_sem (swap id1 id2 CFG) (swap id1 id2 r) = swap id1 id2 (step_sem CFG r).
  Proof.
    intros CFG r.
    
  
