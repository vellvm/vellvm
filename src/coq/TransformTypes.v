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
     Structures.Monads
     Structures.Functor
     Data.Option.

From Vellvm Require Import 
     Error
     Util
     LLVMAst
     AstLib
     CFG.

Import EqvNotation.

Open Scope Z_scope.
Open Scope string_scope.

Section WithTU.
  Variable (T U:Set).
  Variable (f : T -> U).

Definition fmap_pair {X} : (T * X) -> (U * X) := fun '(t, x)=> (f t, x).

Fixpoint fmap_exp (e:exp T) : exp U :=
  let fmap_texp '(t, e) := (f t, fmap_exp e) in
  match e with
  | EXP_Ident id => EXP_Ident _ id
  | EXP_Integer x => EXP_Integer _ x
  | EXP_Float x => EXP_Float _ x
  | EXP_Hex x => EXP_Hex _ x
  | EXP_Bool x => EXP_Bool _ x
  | EXP_Null => EXP_Null _
  | EXP_Zero_initializer  => EXP_Zero_initializer _
  | EXP_Cstring x => EXP_Cstring _ x
  | EXP_Undef => EXP_Undef _ 
  | EXP_Struct fields =>
    EXP_Struct _ (List.map fmap_texp fields)
  | EXP_Packed_struct fields =>
    EXP_Packed_struct _ (List.map fmap_texp fields)    
  | EXP_Array elts =>
    EXP_Array _ (List.map fmap_texp elts)
  | EXP_Vector elts =>
    EXP_Vector _ (List.map fmap_texp elts)
  | OP_IBinop iop t v1 v2 =>
    OP_IBinop _ iop (f t) (fmap_exp v1) (fmap_exp v2)
  | OP_ICmp cmp t v1 v2 =>
    OP_ICmp _ cmp (f t) (fmap_exp v1) (fmap_exp v2)
  | OP_FBinop fop fm t v1 v2 =>
    OP_FBinop _ fop fm (f t) (fmap_exp v1) (fmap_exp v2)    
  | OP_FCmp cmp t v1 v2 =>
    OP_FCmp _ cmp (f t) (fmap_exp v1) (fmap_exp v2)    
  | OP_Conversion conv t_from v t_to =>
    OP_Conversion _ conv (f t_from) (fmap_exp v) (f t_to)
  | OP_GetElementPtr t ptrval idxs =>
    OP_GetElementPtr _ (f t) (fmap_texp ptrval) (List.map fmap_texp idxs)
  | OP_ExtractElement vec idx =>
    OP_ExtractElement _ (fmap_texp vec) (fmap_texp idx)
  | OP_InsertElement  vec elt idx =>
    OP_InsertElement _ (fmap_texp vec) (fmap_texp elt) (fmap_texp idx)
  | OP_ShuffleVector vec1 vec2 idxmask =>
    OP_ShuffleVector _ (fmap_texp vec1) (fmap_texp vec2) (fmap_texp idxmask)
  | OP_ExtractValue  vec idxs =>
    OP_ExtractValue  _ (fmap_texp vec) idxs
  | OP_InsertValue vec elt idxs =>
    OP_InsertValue _ (fmap_texp vec) (fmap_texp elt) idxs
  | OP_Select cnd v1 v2 =>
    OP_Select _ (fmap_texp cnd) (fmap_texp v1) (fmap_texp v2)
  end.

Definition fmap_texp '(t, e) := (f t, fmap_exp e).

Definition fmap_phi (p:phi T) : phi U :=
  match p with
  | Phi t args => Phi _ (f t) (List.map (fun '(b,e) => (b, fmap_exp e)) args)
  end.

Definition fmap_instr (ins:instr T) : instr U :=
  match ins with
  | INSTR_Op op => INSTR_Op _ (fmap_exp op)
  | INSTR_Call fn args => INSTR_Call _ (fmap_texp fn) (List.map fmap_texp args)
  | INSTR_Alloca t nb align =>
    INSTR_Alloca _ (f t) (fmap fmap_texp nb) align
  | INSTR_Load volatile t ptr align =>
    INSTR_Load _ volatile (f t) (fmap_texp ptr) align
  | INSTR_Store volatile val ptr align =>
    INSTR_Store _ volatile (fmap_texp val) (fmap_texp ptr) align
  | INSTR_Comment c => INSTR_Comment _ c
  | INSTR_Fence => INSTR_Fence _
  | INSTR_AtomicCmpXchg => INSTR_AtomicCmpXchg _
  | INSTR_AtomicRMW => INSTR_AtomicRMW _
  | INSTR_Unreachable => INSTR_Unreachable _
  | INSTR_VAArg => INSTR_VAArg _
  | INSTR_LandingPad => INSTR_LandingPad _
  end.

Definition fmap_terminator (trm:terminator T) : terminator U :=
  match trm with
  | TERM_Ret  v => TERM_Ret _ (fmap_texp v)
  | TERM_Ret_void => TERM_Ret_void _
  | TERM_Br v br1 br2 => TERM_Br _ (fmap_texp v) br1 br2
  | TERM_Br_1 br => TERM_Br_1 _ br
  | TERM_Switch  v default_dest brs =>
    TERM_Switch _ (fmap_texp v) default_dest (List.map (fun '(e,b) => (fmap_texp e, b)) brs)
  | TERM_IndirectBr v brs =>
    TERM_IndirectBr _ (fmap_texp v) brs
  | TERM_Resume v => TERM_Resume _ (fmap_texp v)
  | TERM_Invoke fnptrval args to_label unwind_label =>
    TERM_Invoke _ (fmap_pair fnptrval) (List.map fmap_texp args) to_label unwind_label
  end.


Definition fmap_global (g:global T) : (global U) :=
  mk_global _
      (g_ident _ g)
      (f (g_typ _ g))
      (g_constant _ g)
      (fmap fmap_exp (g_exp _ g))
      (g_linkage _ g)
      (g_visibility _ g)
      (g_dll_storage _ g)
      (g_thread_local _ g)
      (g_unnamed_addr _ g)
      (g_addrspace _ g)
      (g_externally_initialized _ g)
      (g_section _ g)
      (g_align _ g).

Definition fmap_declaration (d:declaration T) : declaration U :=
  mk_declaration _
     (dc_name _ d)
     (f (dc_type _ d))
     (dc_param_attrs _ d)
     (dc_linkage _ d)
     (dc_visibility _ d)
     (dc_dll_storage _ d)
     (dc_cconv _ d)
     (dc_attrs _ d)
     (dc_section _ d)
     (dc_align _ d)
     (dc_gc _ d).

Definition fmap_code (c:code T) : code U :=
  List.map (fun '(id, i) => (id, fmap_instr i)) c.

Definition fmap_phis (phis:list (local_id * phi T)) : list (local_id * phi U) :=
  List.map (fun '(id, p) => (id, fmap_phi p)) phis.

Definition fmap_block (b:block T) : block U :=
  mk_block _ (blk_id _ b)
           (fmap_phis (blk_phis _ b))
           (fmap_code (blk_code _ b))
           (fst (blk_term _ b), fmap_terminator (snd (blk_term _ b)))
           (blk_comments _ b).


Definition fmap_definition {X Y:Set} (g : X -> Y) (d:definition T X) : definition U Y :=
  mk_definition _ _
    (fmap_declaration (df_prototype _ _ d))
    (df_args _ _ d)
    (g (df_instrs _ _ d)).

Fixpoint fmap_metadata (m:metadata T) : metadata U :=
  match m with
  | METADATA_Const  tv => METADATA_Const _ (fmap_texp tv)
  | METADATA_Null => METADATA_Null _
  | METADATA_Id id => METADATA_Id _ id
  | METADATA_String str => METADATA_String _ str
  | METADATA_Named strs => METADATA_Named _ strs
  | METADATA_Node mds => METADATA_Node _ (List.map fmap_metadata mds)
  end.


Definition fmap_toplevel_entity {X Y:Set} (g : X -> Y) (tle:toplevel_entity T X) : toplevel_entity U Y :=
  match tle with
  | TLE_Comment msg => TLE_Comment _ _ msg
  | TLE_Target tgt => TLE_Target _ _ tgt
  | TLE_Datalayout layout => TLE_Datalayout _ _ layout
  | TLE_Declaration decl => TLE_Declaration _ _ (fmap_declaration decl)
  | TLE_Definition defn => TLE_Definition _ _ (fmap_definition g defn)
  | TLE_Type_decl id t => TLE_Type_decl _ _ id (f t)
  | TLE_Source_filename s => TLE_Source_filename _ _ s
  | TLE_Global g => TLE_Global _ _ (fmap_global g)
  | TLE_Metadata id md => TLE_Metadata _ _ id (fmap_metadata md)
  | TLE_Attribute_group id attrs => TLE_Attribute_group _ _ id attrs
  end.


Definition fmap_modul {X Y:Set} (g : X -> Y) (m:modul T X) : modul U Y :=
  mk_modul _ _
    (m_name _ _ m)
    (m_target _ _ m)
    (m_datalayout _ _ m)
    (List.map (fun '(i,t) => (i, f t)) (m_type_defs _ _ m))
    (List.map fmap_global (m_globals _ _ m))
    (List.map fmap_declaration (m_declarations _ _ m))
    (List.map (fmap_definition g) (m_definitions _ _ m)).

Definition fmap_cfg (CFG:cfg T) : cfg U :=
  mkCFG _
        (init _ CFG)
        (List.map fmap_block (blks _ CFG))
        (args _ CFG).

Definition fmap_mcfg := fmap_modul fmap_cfg.

End WithTU.

