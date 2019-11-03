From Coq Require Import List ZArith String.
Import ListNotations.

From ITree Require Import
     ITree.

 From Vellvm Require Import
     CFG
     LLVMAst.

Section Traverse.

  Class endo (T: Type) := f_endo: T -> T.

  Section Functors.

    Global Instance endo_list {T: Set}
           `{endo T}
    : endo (list T) | 50 :=
      List.map f_endo.

    Global Instance endo_option {T: Set}
           `{endo T}
      : endo (option T) | 50 :=
      fun ot => match ot with None => None | Some t => Some (f_endo t) end.

    Global Instance endo_prod {T1 T2: Set}
           `{endo T1}
           `{endo T2}
      : endo (T1 * T2) | 50 :=
      fun '(a,b) => (f_endo a, f_endo b).

  End Functors.

  Section Syntax.
    Context {T: Set}.

    Global Instance endo_ident
           `{endo raw_id}
      : endo ident | 50 :=
      fun id =>
        match id with
        | ID_Global rid => ID_Global (f_endo rid)
        | ID_Local lid => ID_Local (f_endo lid)
        end.

    Global Instance endo_instr_id
           `{endo raw_id}
      : endo instr_id | 50 :=
      fun id =>
        match id with
        | IId rid => IId (f_endo rid)
        | IVoid n => IVoid n
        end.

    Global Instance endo_typ
           `{endo raw_id}
      : endo typ | 50 :=
      fix endo_typ t :=
        match t with
        | TYPE_Pointer t' => TYPE_Pointer (endo_typ t')
        | TYPE_Array sz t' => TYPE_Array sz (endo_typ t')
        | TYPE_Function ret args => TYPE_Function (endo_typ ret) (List.map endo_typ args)
        | TYPE_Struct fields => TYPE_Struct (List.map endo_typ fields)
        | TYPE_Packed_struct fields => TYPE_Packed_struct (List.map endo_typ fields)
        | TYPE_Vector sz t' => TYPE_Vector sz (endo_typ t')
        | TYPE_Identified id => TYPE_Identified (f_endo id)
        | _ => t
        end.

    Global Instance endo_exp
           `{endo T}
           `{endo raw_id}
           `{endo ibinop}
           `{endo icmp}
           `{endo fbinop}
           `{endo fcmp}
      : endo (exp T) | 50 :=
      fix f_exp (e:exp T) :=
        match e with
        | EXP_Ident id => EXP_Ident (f_endo id)
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
          EXP_Struct (List.map (fun '(t,e) => (f_endo t, f_exp e)) fields)
        | EXP_Packed_struct fields =>
          EXP_Packed_struct (List.map (fun '(t,e) => (f_endo t, f_exp e)) fields)
        | EXP_Array elts =>
          EXP_Array (List.map (fun '(t,e) => (f_endo t, f_exp e)) elts)
        | EXP_Vector elts =>
          EXP_Vector (List.map (fun '(t,e) => (f_endo t, f_exp e)) elts)
        | OP_IBinop iop t v1 v2 =>
          OP_IBinop (f_endo iop) (f_endo t) (f_exp v1) (f_exp v2)
        | OP_ICmp cmp t v1 v2 =>
          OP_ICmp (f_endo cmp) (f_endo t) (f_exp v1) (f_exp v2)
        | OP_FBinop fop fm t v1 v2 =>
          OP_FBinop (f_endo fop) fm (f_endo t) (f_exp v1) (f_exp v2)
        | OP_FCmp cmp t v1 v2 =>
          OP_FCmp (f_endo cmp) (f_endo t) (f_exp v1) (f_exp v2)
        | OP_Conversion conv t_from v t_to =>
          OP_Conversion conv (f_endo t_from) (f_exp v) (f_endo t_to)
        | OP_GetElementPtr t ptrval idxs =>
          OP_GetElementPtr (f_endo t) (f_endo (fst ptrval), f_exp (snd ptrval))
                           (List.map (fun '(a,b) => (f_endo a, f_exp b)) idxs)
        | OP_ExtractElement vec idx =>
          OP_ExtractElement (f_endo (fst vec), f_exp (snd vec))
                            (f_endo (fst idx), f_exp (snd idx))
        | OP_InsertElement  vec elt idx =>
          OP_InsertElement (f_endo (fst vec), f_exp (snd vec))
                           (f_endo (fst elt), f_exp (snd elt))
                           (f_endo (fst idx), f_exp (snd idx))
        | OP_ShuffleVector vec1 vec2 idxmask =>
          OP_ShuffleVector (f_endo (fst vec1), f_exp (snd vec1))
                           (f_endo (fst vec2), f_exp (snd vec2))
                           (f_endo (fst idxmask), f_exp (snd idxmask))
        | OP_ExtractValue vec idxs =>
          OP_ExtractValue (f_endo (fst vec), f_exp (snd vec))
                          idxs
        | OP_InsertValue vec elt idxs =>
          OP_InsertValue (f_endo (fst vec), f_exp (snd vec))
                         (f_endo (fst elt), f_exp (snd elt))
                         idxs
        | OP_Select cnd v1 v2 =>
          OP_Select (f_endo (fst cnd), f_exp (snd cnd))
                    (f_endo (fst v1), f_exp (snd v1))
                    (f_endo (fst v2), f_exp (snd v2))
        end.

    Global Instance endo_texp
           `{endo T}
           `{endo (exp T)}
      : endo (texp T) | 50 :=
      fun te => let '(t,e) := te in (f_endo t, f_endo e).

    Global Instance endo_instr
           `{endo T}
           `{endo (exp T)}
      : endo (instr T) | 50 :=
      fun ins =>
        match ins with
        | INSTR_Op op => INSTR_Op (f_endo op)
        | INSTR_Call fn args => INSTR_Call (f_endo fn) (f_endo args)
        | INSTR_Alloca t nb align =>
          INSTR_Alloca (f_endo t) (f_endo nb) align
        | INSTR_Load volatile t ptr align =>
          INSTR_Load volatile (f_endo t) (f_endo ptr) align
        | INSTR_Store volatile val ptr align =>
          INSTR_Store volatile (f_endo val) (f_endo ptr) align
        | INSTR_Comment _
        | INSTR_Fence
        | INSTR_AtomicCmpXchg
        | INSTR_AtomicRMW
        | INSTR_Unreachable
        | INSTR_VAArg
        | INSTR_LandingPad => ins
        end.

    Global Instance endo_terminator
           `{endo T}
           `{endo raw_id}
           `{endo (exp T)}
      : endo (terminator T) | 50 :=
      fun trm =>
        match trm with
        | TERM_Ret  v => TERM_Ret (f_endo v)
        | TERM_Ret_void => TERM_Ret_void
        | TERM_Br v br1 br2 => TERM_Br (f_endo v) (f_endo br1) (f_endo br2)
        | TERM_Br_1 br => TERM_Br_1 (f_endo br)
        | TERM_Switch  v default_dest brs =>
          TERM_Switch (f_endo v) (f_endo default_dest) (f_endo brs)
        | TERM_IndirectBr v brs =>
          TERM_IndirectBr (f_endo v) (f_endo brs)
        | TERM_Resume v => TERM_Resume (f_endo v)
        | TERM_Invoke fnptrval args to_label unwind_label =>
          TERM_Invoke (f_endo fnptrval) (f_endo args) (f_endo to_label) (f_endo unwind_label)
        end.

    Global Instance endo_phi
           `{endo T}
           `{endo raw_id}
           `{endo (exp T)}
      : endo (phi T) | 50 :=
      fun p => match p with
            | Phi t args => Phi (f_endo t) (f_endo args)
            end.

    Global Instance endo_block
           `{endo raw_id}
           `{endo (instr T)}
           `{endo (terminator T)}
           `{endo (phi T)}
      : endo (block T) | 50 :=
      fun b =>
        mk_block (f_endo (blk_id b))
                 (f_endo (blk_phis b))
                 (f_endo (blk_code b))
                 (f_endo (blk_term b))
                 (blk_comments b).

    Global Instance endo_global
           `{endo raw_id}
           `{endo T}
           `{endo bool}
           `{endo int}
           `{endo string}
           `{endo (exp T)}
           `{endo linkage}
           `{endo visibility}
           `{endo dll_storage}
           `{endo thread_local_storage}
      : endo (global T) | 50 :=
      fun g =>
        mk_global
          (f_endo (g_ident g))
          (f_endo (g_typ g))
          (f_endo (g_constant g))
          (f_endo (g_exp g))
          (f_endo (g_linkage g))
          (f_endo (g_visibility g))
          (f_endo (g_dll_storage g))
          (f_endo (g_thread_local g))
          (f_endo (g_unnamed_addr g))
          (f_endo (g_addrspace g))
          (f_endo (g_externally_initialized g))
          (f_endo (g_section g))
          (f_endo (g_align g)).

    Global Instance endo_declaration
           `{endo function_id}
           `{endo T}
           `{endo string}
           `{endo int}
           `{endo param_attr}
           `{endo linkage}
           `{endo visibility}
           `{endo dll_storage}
           `{endo cconv}
           `{endo fn_attr}
      : endo (declaration T) | 50 :=
      fun d => mk_declaration
              (f_endo (dc_name d))
              (f_endo (dc_type d))
              (f_endo (dc_param_attrs d))
              (f_endo (dc_linkage d))
              (f_endo (dc_visibility d))
              (f_endo (dc_dll_storage d))
              (f_endo (dc_cconv d))
              (f_endo (dc_attrs d))
              (f_endo (dc_section d))
              (f_endo (dc_align d))
              (f_endo (dc_gc d)).

    Global Instance endo_metadata
           `{endo T}
           `{endo (exp T)}
           `{endo raw_id}
           `{endo string}
      : endo (metadata T) | 50 :=
      fix endo_metadata m :=
        match m with
        | METADATA_Const  tv => METADATA_Const (f_endo tv)
        | METADATA_Null => METADATA_Null
        | METADATA_Id id => METADATA_Id (f_endo id)
        | METADATA_String str => METADATA_String (f_endo str)
        | METADATA_Named strs => METADATA_Named (f_endo strs)
        | METADATA_Node mds => METADATA_Node (List.map endo_metadata mds)
        end.

    Global Instance endo_definition
           {FnBody:Set}
           `{endo (declaration T)}
           `{endo raw_id}
           `{endo FnBody}
      : endo (definition T FnBody) | 50 :=
      fun d =>
        mk_definition _
                      (f_endo (df_prototype d))
                      (f_endo (df_args d))
                      (f_endo (df_instrs d)).

    Global Instance endo_toplevel_entity
           {FnBody:Set}
           `{endo FnBody}
           `{endo T}
           `{endo (global T)}
           `{endo raw_id}
           `{endo (metadata T)}
           `{endo (declaration T)}
           `{endo (definition T FnBody)}
           `{endo fn_attr}
           `{endo int}
           `{endo string}
      : endo (toplevel_entity T FnBody) | 50 :=
      fun tle =>
        match tle with
        | TLE_Comment msg => tle
        | TLE_Target tgt => TLE_Target (f_endo tgt)
        | TLE_Datalayout layout => TLE_Datalayout (f_endo layout)
        | TLE_Declaration decl => TLE_Declaration (f_endo decl)
        | TLE_Definition defn => TLE_Definition (f_endo defn)
        | TLE_Type_decl id t => TLE_Type_decl (f_endo id) (f_endo t)
        | TLE_Source_filename s => TLE_Source_filename (f_endo s)
        | TLE_Global g => TLE_Global (f_endo g)
        | TLE_Metadata id md => TLE_Metadata (f_endo id) (f_endo md)
        | TLE_Attribute_group i attrs => TLE_Attribute_group (f_endo i) (f_endo attrs)
        end.

    Global Instance endo_modul
           {FnBody:Set}
           `{endo FnBody}
           `{endo string}
           `{endo T}
           `{endo (global T)}
           `{endo (declaration T)}
           `{endo raw_id}
      : endo (modul T FnBody) | 50 :=
      fun m =>
        mk_modul _
                 (f_endo (m_name m))
                 (f_endo (m_target m))
                 (f_endo (m_datalayout m))
                 (f_endo (m_type_defs m))
                 (f_endo (m_globals m))
                 (f_endo (m_declarations m))
                 (f_endo (m_definitions m)).

    Global Instance endo_cfg
           `{endo raw_id}
           `{endo (block T)}
      : endo (cfg T) | 50 :=
      fun p => mkCFG _
                  (f_endo (init _ p))
                  (f_endo (blks _ p))
                  (f_endo (args _ p)).

    Global Instance endo_mcfg
           {FnBody:Set}
           `{endo T}
           `{endo FnBody}
           `{endo string}
           `{endo raw_id}
           `{endo (global T)}
           `{endo (declaration T)}
           `{endo (definition T FnBody)}
      : endo (modul T FnBody) | 50 :=
      fun p => mk_modul _
                  (f_endo (m_name p))
                  (f_endo (m_target p))
                  (f_endo (m_datalayout p))
                  (f_endo (m_type_defs p))
                  (f_endo (m_globals p))
                  (f_endo (m_declarations p))
                  (f_endo (m_definitions p)).

  End Syntax.

  Section Semantics.

    Global Instance endo_of_sum1
           {A B: Type -> Type}
           {X}
           `{endo (A X)}
           `{endo (B X)}
    : endo ((A +' B) X) | 50 :=
      fun ab =>
        match ab with
        | inl1 a => inl1 (f_endo a)
        | inr1 b => inr1 (f_endo b)
        end.

    Global Instance endo_itree {X E}
           `{endo X}
           `{forall T, endo (E T)}
    : endo (itree E X) | 50 :=
      fun t =>
    ITree.map f_endo (@translate E E (fun T => f_endo) _ t).

  End Semantics.

  (* By default, the solver can always pick the identity as an instance.
     However both structural traversal from this section and local
     instances should always have priority over this, hence the 100.
   *)
  Global Instance endo_id (T: Set): endo T | 100 := fun x: T => x.

End Traverse.

