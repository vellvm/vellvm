(* begin hide *)
From Coq Require Import List ZArith String.
Import ListNotations.

From ITree Require Import
     ITree.

From Vellvm Require Import
     Syntax.CFG
     Syntax.LLVMAst.
(* end hide *)

(** ** Definition of generic transformations on Vellvm's abstract syntax.
    The general idea is to define two functions, an endofunction and an fmap
    over each syntactic construct in the ast.
    The additional trick is to parameterize all instances explicitly by
    instances of its substructures.
    By default, the endofunction would result in the identity, while the fmap one would
    be the expected [fmap] function.
    However, the point of this additional boilerplate is to be able to override the default
    behavior at any level by simply locally defining other [fmap] or [endo] instances.

    Examples of use are provided at the end of the file.

   NOTE: I wrote the code as such for historical reasons, but I believe all instances of [endo] for
   structures that are family of types could be redefined as [endo id].
 *)

Section Endo.

  Class Endo (T: Type) := endo: T -> T.

  #[global] Instance Endo_list {T: Set}
         `{Endo T}
    : Endo (list T) | 50 :=
    List.map endo.

  #[global] Instance Endo_option {T: Set}
         `{Endo T}
    : Endo (option T) | 50 :=
    fun ot => match ot with None => None | Some t => Some (endo t) end.

  #[global] Instance Endo_prod {T1 T2: Set}
         `{Endo T1}
         `{Endo T2}
    : Endo (T1 * T2) | 50 :=
    fun '(a,b) => (endo a, endo b).

  Section Syntax.

    Context {T: Set}.

    #[global] Instance Endo_ident
           `{Endo raw_id}
      : Endo ident | 50 :=
      fun id =>
        match id with
        | ID_Global rid => ID_Global (endo rid)
        | ID_Local lid => ID_Local (endo lid)
        end.

    #[global] Instance Endo_instr_id
           `{Endo raw_id}
      : Endo instr_id | 50 :=
      fun id =>
        match id with
        | IId rid => IId (endo rid)
        | IVoid n => IVoid n
        end.

    #[global] Instance Endo_typ
           `{Endo raw_id}
      : Endo typ | 50 :=
      fix endo_typ t :=
        match t with
        | TYPE_Pointer t' => TYPE_Pointer (endo_typ t')
        | TYPE_Array sz t' => TYPE_Array sz (endo_typ t')
        | TYPE_Function ret args => TYPE_Function (endo_typ ret) (List.map endo_typ args)
        | TYPE_Struct fields => TYPE_Struct (List.map endo_typ fields)
        | TYPE_Packed_struct fields => TYPE_Packed_struct (List.map endo_typ fields)
        | TYPE_Vector sz t' => TYPE_Vector sz (endo_typ t')
        | TYPE_Identified id => TYPE_Identified (endo id)
        | _ => t
        end.

    #[global] Instance Endo_exp
           `{Endo T}
           `{Endo raw_id}
           `{Endo ibinop}
           `{Endo icmp}
           `{Endo fbinop}
           `{Endo fcmp}
      : Endo (exp T) | 50 :=
      fix f_exp (e:exp T) :=
        match e with
        | EXP_Ident id => EXP_Ident (endo id)
        | EXP_Integer _
        | EXP_Float   _
        | EXP_Double  _
        | EXP_Hex     _
        | EXP_Bool    _
        | EXP_Null
        | EXP_Zero_initializer
        | EXP_Undef => e
        | EXP_Cstring elts =>
          EXP_Cstring (List.map (fun '(t,e) => (endo t, f_exp e)) elts)          
        | EXP_Struct fields =>
          EXP_Struct (List.map (fun '(t,e) => (endo t, f_exp e)) fields)
        | EXP_Packed_struct fields =>
          EXP_Packed_struct (List.map (fun '(t,e) => (endo t, f_exp e)) fields)
        | EXP_Array elts =>
          EXP_Array (List.map (fun '(t,e) => (endo t, f_exp e)) elts)
        | EXP_Vector elts =>
          EXP_Vector (List.map (fun '(t,e) => (endo t, f_exp e)) elts)
        | OP_IBinop iop t v1 v2 =>
          OP_IBinop (endo iop) (endo t) (f_exp v1) (f_exp v2)
        | OP_ICmp cmp t v1 v2 =>
          OP_ICmp (endo cmp) (endo t) (f_exp v1) (f_exp v2)
        | OP_FBinop fop fm t v1 v2 =>
          OP_FBinop (endo fop) fm (endo t) (f_exp v1) (f_exp v2)
        | OP_FCmp cmp t v1 v2 =>
          OP_FCmp (endo cmp) (endo t) (f_exp v1) (f_exp v2)
        | OP_Conversion conv t_from v t_to =>
          OP_Conversion conv (endo t_from) (f_exp v) (endo t_to)
        | OP_GetElementPtr t ptrval idxs =>
          OP_GetElementPtr (endo t) (endo (fst ptrval), f_exp (snd ptrval))
                           (List.map (fun '(a,b) => (endo a, f_exp b)) idxs)
        | OP_ExtractElement vec idx =>
          OP_ExtractElement (endo (fst vec), f_exp (snd vec))
                            (endo (fst idx), f_exp (snd idx))
        | OP_InsertElement  vec elt idx =>
          OP_InsertElement (endo (fst vec), f_exp (snd vec))
                           (endo (fst elt), f_exp (snd elt))
                           (endo (fst idx), f_exp (snd idx))
        | OP_ShuffleVector vec1 vec2 idxmask =>
          OP_ShuffleVector (endo (fst vec1), f_exp (snd vec1))
                           (endo (fst vec2), f_exp (snd vec2))
                           (endo (fst idxmask), f_exp (snd idxmask))
        | OP_ExtractValue vec idxs =>
          OP_ExtractValue (endo (fst vec), f_exp (snd vec))
                          idxs
        | OP_InsertValue vec elt idxs =>
          OP_InsertValue (endo (fst vec), f_exp (snd vec))
                         (endo (fst elt), f_exp (snd elt))
                         idxs
        | OP_Select cnd v1 v2 =>
          OP_Select (endo (fst cnd), f_exp (snd cnd))
                    (endo (fst v1), f_exp (snd v1))
                    (endo (fst v2), f_exp (snd v2))
        | OP_Freeze v =>
          OP_Freeze (endo (fst v), f_exp (snd v))
        end.

    #[global] Instance Endo_texp
           `{Endo T}
           `{Endo (exp T)}
      : Endo (texp T) | 50 :=
      fun te => let '(t,e) := te in (endo t, endo e).

    #[global] Instance Endo_tint_literal
      : Endo tint_literal | 50 := id.
    
    #[global] Instance Endo_instr
           `{Endo T}
           `{Endo (exp T)}
      : Endo (instr T) | 50 :=
      fun ins =>
        match ins with
        | INSTR_Op op => INSTR_Op (endo op)
        | INSTR_Call fn args => INSTR_Call (endo fn) (endo args)
        | INSTR_Alloca t nb align =>
          INSTR_Alloca (endo t) (endo nb) align
        | INSTR_Load volatile t ptr align =>
          INSTR_Load volatile (endo t) (endo ptr) align
        | INSTR_Store volatile val ptr align =>
          INSTR_Store volatile (endo val) (endo ptr) align
        | INSTR_Comment _
        | INSTR_Fence
        | INSTR_AtomicCmpXchg
        | INSTR_AtomicRMW
        | INSTR_VAArg
        | INSTR_LandingPad => ins
        end.

    #[global] Instance Endo_terminator
           `{Endo T}
           `{Endo raw_id}
           `{Endo (exp T)}
      : Endo (terminator T) | 50 :=
      fun trm =>
        match trm with
        | TERM_Ret  v => TERM_Ret (endo v)
        | TERM_Ret_void => TERM_Ret_void
        | TERM_Br v br1 br2 => TERM_Br (endo v) (endo br1) (endo br2)
        | TERM_Br_1 br => TERM_Br_1 (endo br)
        | TERM_Switch  v default_dest brs =>
          TERM_Switch (endo v) (endo default_dest) (endo brs)
        | TERM_IndirectBr v brs =>
          TERM_IndirectBr (endo v) (endo brs)
        | TERM_Resume v => TERM_Resume (endo v)
        | TERM_Invoke fnptrval args to_label unwind_label =>
          TERM_Invoke (endo fnptrval) (endo args) (endo to_label) (endo unwind_label)
        | TERM_Unreachable => TERM_Unreachable 
        end.

    #[global] Instance Endo_phi
           `{Endo T}
           `{Endo raw_id}
           `{Endo (exp T)}
      : Endo (phi T) | 50 :=
      fun p => match p with
            | Phi t args => Phi (endo t) (endo args)
            end.

    #[global] Instance Endo_block
           `{Endo raw_id}
           `{Endo (code T)}
           `{Endo (terminator T)}
           `{Endo (phi T)}
      : Endo (block T) | 50 :=
      fun b =>
        mk_block (endo (blk_id b))
                 (endo (blk_phis b))
                 (endo (blk_code b))
                 (endo (blk_term b))
                 (blk_comments b).

    #[global] Instance Endo_global
           `{Endo raw_id}
           `{Endo T}
           `{Endo bool}
           `{Endo int}
           `{Endo string}
           `{Endo (exp T)}
           `{Endo linkage}
           `{Endo visibility}
           `{Endo dll_storage}
           `{Endo thread_local_storage}
      : Endo (global T) | 50 :=
      fun g =>
        mk_global
          (endo (g_ident g))
          (endo (g_typ g))
          (endo (g_constant g))
          (endo (g_exp g))
          (endo (g_linkage g))
          (endo (g_visibility g))
          (endo (g_dll_storage g))
          (endo (g_thread_local g))
          (endo (g_unnamed_addr g))
          (endo (g_addrspace g))
          (endo (g_externally_initialized g))
          (endo (g_section g))
          (endo (g_align g)).

    #[global] Instance Endo_declaration
           `{Endo function_id}
           `{Endo T}
           `{Endo string}
           `{Endo int}
           `{Endo param_attr}
           `{Endo linkage}
           `{Endo visibility}
           `{Endo dll_storage}
           `{Endo cconv}
           `{Endo fn_attr}
      : Endo (declaration T) | 50 :=
      fun d => mk_declaration
              (endo (dc_name d))
              (endo (dc_type d))
              (endo (dc_param_attrs d))
              (endo (dc_linkage d))
              (endo (dc_visibility d))
              (endo (dc_dll_storage d))
              (endo (dc_cconv d))
              (endo (dc_attrs d))
              (endo (dc_section d))
              (endo (dc_align d))
              (endo (dc_gc d)).

    #[global] Instance Endo_metadata
           `{Endo T}
           `{Endo (exp T)}
           `{Endo raw_id}
           `{Endo string}
      : Endo (metadata T) | 50 :=
      fix endo_metadata m :=
        match m with
        | METADATA_Const  tv => METADATA_Const (endo tv)
        | METADATA_Null => METADATA_Null
        | METADATA_Id id => METADATA_Id (endo id)
        | METADATA_String str => METADATA_String (endo str)
        | METADATA_Named strs => METADATA_Named (endo strs)
        | METADATA_Node mds => METADATA_Node (List.map endo_metadata mds)
        end.

    #[global] Instance Endo_definition
           {FnBody:Set}
           `{Endo (declaration T)}
           `{Endo raw_id}
           `{Endo FnBody}
      : Endo (definition T FnBody) | 50 :=
      fun d =>
        mk_definition _
                      (endo (df_prototype d))
                      (endo (df_args d))
                      (endo (df_instrs d)).

    #[global] Instance Endo_toplevel_entity
           {FnBody:Set}
           `{Endo FnBody}
           `{Endo T}
           `{Endo (global T)}
           `{Endo raw_id}
           `{Endo (metadata T)}
           `{Endo (declaration T)}
           `{Endo (definition T FnBody)}
           `{Endo fn_attr}
           `{Endo int}
           `{Endo string}
      : Endo (toplevel_entity T FnBody) | 50 :=
      fun tle =>
        match tle with
        | TLE_Comment msg => tle
        | TLE_Target tgt => TLE_Target (endo tgt)
        | TLE_Datalayout layout => TLE_Datalayout (endo layout)
        | TLE_Declaration decl => TLE_Declaration (endo decl)
        | TLE_Definition defn => TLE_Definition (endo defn)
        | TLE_Type_decl id t => TLE_Type_decl (endo id) (endo t)
        | TLE_Source_filename s => TLE_Source_filename (endo s)
        | TLE_Global g => TLE_Global (endo g)
        | TLE_Metadata id md => TLE_Metadata (endo id) (endo md)
        | TLE_Attribute_group i attrs => TLE_Attribute_group (endo i) (endo attrs)
        end.

    #[global] Instance Endo_modul
           {FnBody:Set}
           `{Endo FnBody}
           `{Endo string}
           `{Endo T}
           `{Endo (global T)}
           `{Endo (declaration T)}
           `{Endo raw_id}
      : Endo (modul FnBody) | 50 :=
      fun m =>
        mk_modul (endo (m_name m))
                 (endo (m_target m))
                 (endo (m_datalayout m))
                 (endo (m_type_defs m))
                 (endo (m_globals m))
                 (endo (m_declarations m))
                 (endo (m_definitions m)).

    #[global] Instance Endo_cfg
           `{Endo raw_id}
           `{Endo (block T)}
      : Endo (cfg T) | 50 :=
      fun p => mkCFG (endo (init p))
                  (endo (blks p))
                  (endo (args p)).

    #[global] Instance Endo_mcfg
           {FnBody:Set}
           `{Endo T}
           `{Endo FnBody}
           `{Endo string}
           `{Endo raw_id}
           `{Endo (global T)}
           `{Endo (declaration T)}
           `{Endo (definition T FnBody)}
      : Endo (modul FnBody) | 50 :=
      fun p => mk_modul (endo (m_name p))
                     (endo (m_target p))
                     (endo (m_datalayout p))
                     (endo (m_type_defs p))
                     (endo (m_globals p))
                     (endo (m_declarations p))
                     (endo (m_definitions p)).

  End Syntax.

  Section Semantics.

    #[global] Instance Endo_of_sum1
           {A B: Type -> Type}
           {X}
           `{Endo (A X)}
           `{Endo (B X)}
    : Endo ((A +' B) X) | 50 :=
      fun ab =>
        match ab with
        | inl1 a => inl1 (endo a)
        | inr1 b => inr1 (endo b)
        end.

    #[global] Instance Endo_itree {X E}
           `{Endo X}
           `{forall T, Endo (E T)}
      : Endo (itree E X) | 50 :=
      fun t =>
        ITree.map endo (@translate E E (fun T => endo) _ t).

  End Semantics.

  (** **
     By default, the solver can always pick the identity as an instance.
     However both structural traversal from this section and local
     instances should always have priority over this, hence the 100.
   *)

  #[global] Instance Endo_id (T: Set): Endo T | 100 := fun x: T => x.

End Endo.

(* This is a duplicate of extlib's functor typeclass. We should cut off one or the other.
   The "T" prefix is to avoid collision of names so that we don't have to worry when importing
   in the mean time.
 *)
Section TFunctor.

  Class TFunctor (T: Set -> Set) := tfmap: forall {U V: Set} (f: U -> V), T U -> T V.

  Section Generics.

    Definition compose {A B C: Type} (f: A -> B) (g: B -> C): A -> C := fun a => g (f a).

    #[global] Instance TFunctor_list 
      : TFunctor list | 50 :=
      List.map.

    #[global] Instance TFunctor_list' {F} `{TFunctor F} 
      : TFunctor (fun T => list (F T)) | 49 :=
      fun U V f => List.map (tfmap f).

    #[global] Instance TFunctor_option {F} `{TFunctor F}
      : TFunctor (fun T => option (F T)) | 50 :=
      fun U V f ot => match ot with None => None | Some t => Some (tfmap f t) end.

  End Generics.

  Section Syntax.

    #[global] Instance TFunctor_exp
           `{Endo raw_id}
           `{Endo ibinop}
           `{Endo icmp}
           `{Endo fbinop}
           `{Endo fcmp}
    : TFunctor exp | 50 :=
      fun (U V: Set) (f: U -> V) => fix f_exp (e:exp U) :=
        let ftexp (te: U * exp U) := (f (fst te), f_exp (snd te)) in
        match e with
        | EXP_Ident id                       => EXP_Ident (endo id)
        | EXP_Integer n                      => EXP_Integer n 
        | EXP_Float   f                      => EXP_Float   f
        | EXP_Double  d                      => EXP_Double  d
        | EXP_Hex     f                      => EXP_Hex     f
        | EXP_Bool    b                      => EXP_Bool    b
        | EXP_Null                           => EXP_Null
        | EXP_Zero_initializer               => EXP_Zero_initializer
        | EXP_Cstring elts                   => EXP_Cstring (tfmap ftexp elts)
        | EXP_Undef                          => EXP_Undef
        | EXP_Struct fields                  => EXP_Struct (tfmap ftexp fields)
        | EXP_Packed_struct fields           => EXP_Packed_struct (tfmap ftexp fields)
        | EXP_Array elts                     => EXP_Array (tfmap ftexp elts)
        | EXP_Vector elts                    => EXP_Vector (tfmap ftexp elts)
        | OP_IBinop iop t v1 v2              => OP_IBinop (endo iop) (f t) (f_exp v1) (f_exp v2)
        | OP_ICmp cmp t v1 v2                => OP_ICmp (endo cmp) (f t) (f_exp v1) (f_exp v2)
        | OP_FBinop fop fm t v1 v2           => OP_FBinop (endo fop) fm (f t) (f_exp v1) (f_exp v2)
        | OP_FCmp cmp t v1 v2                => OP_FCmp (endo cmp) (f t) (f_exp v1) (f_exp v2)
        | OP_Conversion conv t_from v t_to   => OP_Conversion conv (f t_from) (f_exp v) (f t_to)
        | OP_GetElementPtr t ptr idxs        => OP_GetElementPtr (f t) (ftexp ptr) (tfmap ftexp idxs)
        | OP_ExtractElement vec idx          => OP_ExtractElement (ftexp vec) (ftexp idx)
        | OP_InsertElement vec elt idx       => OP_InsertElement (ftexp vec) (ftexp elt) (ftexp idx)
        | OP_ShuffleVector vec1 vec2 idxmask => OP_ShuffleVector (ftexp vec1) (ftexp vec2) (ftexp  idxmask)
        | OP_ExtractValue vec idxs           => OP_ExtractValue (ftexp vec) idxs
        | OP_InsertValue vec elt idxs        => OP_InsertValue (ftexp vec) (ftexp elt) idxs
        | OP_Select cnd v1 v2                => OP_Select (ftexp cnd) (ftexp v1) (ftexp v2)
        | OP_Freeze v                        => OP_Freeze (ftexp v)
        end.

    #[global] Instance TFunctor_texp 
           `{TFunctor exp}
      : TFunctor texp | 50 :=
      fun _ _ f '(t,e) => (f t, tfmap f e).

    #[global] Instance TFunctor_instr
           `{TFunctor exp}
      : TFunctor instr | 50 :=
      fun U V f ins =>
        match ins with
        | INSTR_Comment s => INSTR_Comment s
        | INSTR_Op op => INSTR_Op (tfmap f op) 
        | INSTR_Call fn args => INSTR_Call  (tfmap f fn) (tfmap f args)
        | INSTR_Alloca t nb align => INSTR_Alloca (f t) (tfmap f nb) align
        | INSTR_Load volatile t ptr align => INSTR_Load volatile (f t) (tfmap f ptr) align
        | INSTR_Store volatile val ptr align => INSTR_Store volatile (tfmap f val) (tfmap f ptr) align
        | INSTR_Fence => INSTR_Fence
        | INSTR_AtomicCmpXchg => INSTR_AtomicCmpXchg
        | INSTR_AtomicRMW => INSTR_AtomicRMW
        | INSTR_VAArg => INSTR_VAArg
        | INSTR_LandingPad => INSTR_LandingPad 
        end.

    #[global] Instance TFunctor_tident
           `{Endo ident}: TFunctor (@tident)
      := fun U V f '(t,i) => (f t, endo i).

    #[global] Instance TFunctor_terminator
           `{Endo tint_literal}
           `{Endo raw_id}
           `{TFunctor exp}
      : TFunctor terminator | 50 :=
      fun U V f trm =>
        match trm with
        | TERM_Ret  v => TERM_Ret (tfmap f v)
        | TERM_Ret_void => TERM_Ret_void
        | TERM_Br v br1 br2 => TERM_Br (tfmap f v) (endo br1) (endo br2)
        | TERM_Br_1 br => TERM_Br_1 (endo br)
        | TERM_Switch v default_dest brs => TERM_Switch (tfmap f v) (endo default_dest) (endo brs) 
        | TERM_IndirectBr v brs => TERM_IndirectBr (tfmap f v) (endo brs)
        | TERM_Resume v => TERM_Resume (tfmap f v)
        | TERM_Invoke fnptrval args to_label unwind_label => TERM_Invoke (tfmap f fnptrval) (tfmap f args) (endo to_label) (endo unwind_label)
        | TERM_Unreachable => TERM_Unreachable
        end.

    #[global] Instance TFunctor_phi
           `{Endo raw_id}
           `{TFunctor exp}
      : TFunctor phi | 50 :=
      fun U V f '(Phi t args) =>
        Phi (f t) (tfmap (fun '(id,e) => (endo id, tfmap f e)) args).

    #[global] Instance TFunctor_code
           `{Endo raw_id}
           `{TFunctor instr}
      : TFunctor code | 50 :=
      fun U V f => tfmap (fun '(id,i) => (endo id, tfmap f i)).

    #[global] Instance TFunctor_block
           `{Endo raw_id}
           `{TFunctor instr}
           `{TFunctor terminator}
           `{TFunctor phi}
      : TFunctor block | 50  :=
      fun U V f b =>
        mk_block (endo (blk_id b)) 
                 (tfmap (fun '(id,phi) => (endo id, tfmap f phi)) (blk_phis b))
                 (tfmap f (blk_code b))
                 (tfmap f (blk_term b)) 
                 (blk_comments b).
    
    #[global] Instance TFunctor_global
           `{Endo raw_id}
           `{Endo bool}
           `{Endo int}
           `{Endo string}
           `{TFunctor exp}
           `{Endo linkage}
           `{Endo visibility}
           `{Endo dll_storage}
           `{Endo thread_local_storage}
      : TFunctor global | 50 :=
      fun U V f g =>
        mk_global
          (endo (g_ident g))
          (f (g_typ g))
          (endo (g_constant g))
          (tfmap f (g_exp g))
          (endo (g_linkage g))
          (endo (g_visibility g))
          (endo (g_dll_storage g))
          (endo (g_thread_local g))
          (endo (g_unnamed_addr g))
          (endo (g_addrspace g))
          (endo (g_externally_initialized g))
          (endo (g_section g))
          (endo (g_align g)).

    #[global] Instance TFunctor_declaration
           `{Endo function_id}
           `{Endo string}
           `{Endo int}
           `{Endo param_attr}
           `{Endo linkage}
           `{Endo visibility}
           `{Endo dll_storage}
           `{Endo cconv}
           `{Endo fn_attr}
      : TFunctor declaration | 50 :=
      fun U V f d => mk_declaration
                       (endo (dc_name d))
                       (f (dc_type d))
                       (endo (dc_param_attrs d))
                       (endo (dc_linkage d))
                       (endo (dc_visibility d))
                       (endo (dc_dll_storage d))
                       (endo (dc_cconv d))
                       (endo (dc_attrs d))
                       (endo (dc_section d))
                       (endo (dc_align d))
                       (endo (dc_gc d)).

    #[global] Instance TFunctor_metadata
           `{TFunctor exp}
           `{Endo raw_id}
           `{Endo string}
      : TFunctor metadata | 50 :=
      fun U V f => fix endo_metadata m :=
        match m with
        | METADATA_Const tv => METADATA_Const (tfmap f tv)
        | METADATA_Null => METADATA_Null
        | METADATA_Id id => METADATA_Id (endo id)
        | METADATA_String str => METADATA_String (endo str)
        | METADATA_Named strs => METADATA_Named (endo strs)
        | METADATA_Node mds => METADATA_Node (tfmap endo_metadata mds)
        end.

    #[global] Instance TFunctor_definition
           {FnBody:Set -> Set}
           `{TFunctor declaration}
           `{Endo raw_id}
           `{TFunctor FnBody}
      : TFunctor (fun T => definition T (FnBody T)) | 50 :=
      fun U V f d =>
        mk_definition _
                      (tfmap f (df_prototype d))
                      (endo (df_args d))
                      (tfmap f (df_instrs d)).

    #[global] Instance TFunctor_toplevel_entity
           {FnBody : Set -> Set}
           `{TFunctor FnBody}
           `{TFunctor global}
           `{Endo raw_id}
           `{TFunctor metadata}
           `{TFunctor declaration}
           `{TFunctor (fun T => definition T (FnBody T))}
           `{Endo fn_attr}
           `{Endo int}
           `{Endo string}
      : TFunctor (fun T => toplevel_entity T (FnBody T)) | 50 :=
      fun U V f tle =>
        match tle with
        | TLE_Comment msg => TLE_Comment msg
        | TLE_Target tgt => TLE_Target (endo tgt)
        | TLE_Datalayout layout => TLE_Datalayout (endo layout)
        | TLE_Declaration decl => TLE_Declaration (tfmap f decl)
        | TLE_Definition defn => TLE_Definition (tfmap f defn)
        | TLE_Type_decl id t => TLE_Type_decl (endo id) (f t)
        | TLE_Source_filename s => TLE_Source_filename (endo s)
        | TLE_Global g => TLE_Global (tfmap f g)
        | TLE_Metadata id md => TLE_Metadata (endo id) (tfmap f md)
        | TLE_Attribute_group i attrs => TLE_Attribute_group (endo i) (endo attrs)
        end.

    #[global] Instance TFunctor_modul
           {FnBody : Set -> Set}
           `{TFunctor FnBody}
           `{Endo string}
           `{TFunctor global}
           `{TFunctor declaration}
           `{Endo raw_id}
      : TFunctor (fun T => modul (FnBody T)) | 50 :=
      fun U V f m =>
        mk_modul (endo (m_name m)) 
                 (endo (m_target m)) (endo (m_datalayout m)) 
                 (tfmap (fun '(id,t) => (id, f t)) (m_type_defs m)) 
                 (tfmap f (m_globals m))
                 (tfmap f (m_declarations m))
                 (tfmap f (m_definitions m)).

    #[global] Instance TFunctor_cfg
           `{Endo raw_id}
           `{TFunctor block}
      : TFunctor cfg | 50 :=
      fun U V f p => mkCFG (endo (init p))
                        (tfmap f (blks p))
                        (endo (args p)).

    #[global] Instance TFunctor_mcfg
           {FnBody : Set -> Set}
           `{TFunctor FnBody}
           `{Endo string}
           `{Endo raw_id}
           `{TFunctor global}
           `{TFunctor declaration}
           `{TFunctor (fun T => definition T (FnBody T))}
      : TFunctor (fun T => modul (FnBody T)) | 50 :=
      fun U V f p => mk_modul (endo (m_name p))
                           (endo (m_target p))
                           (endo (m_datalayout p))
                           (tfmap (fun '(id,t) => (id, f t)) (m_type_defs p))
                           (tfmap f (m_globals p))
                           (tfmap f (m_declarations p))
                           (tfmap f (m_definitions p)).

  End Syntax.

End TFunctor.

Lemma tfmap_list_app: forall U V H H' c1 c2 f,
    @tfmap code (@TFunctor_code H H') U V f (c1 ++ c2) =
    tfmap f c1  ++ tfmap f c2.
Proof.
  induction c1 as [| [] c1 IH]; cbn; intros; [reflexivity |].
  rewrite IH; reflexivity.
Qed.

From ExtLib Require Import
     Programming.Eqv
     Structures.Monads.

Import EqvNotation.

Section Examples.

  Section SubstId.

    (** ** 
        Example definition of a transformation swapping identifier [x] for identifier [y] and reciprocally in a [cfg]
     *)

    Variable x y: raw_id.

    (* We define the swapping over [raw_id] *)
    Definition swap_raw_id (id:raw_id) : raw_id :=
      if id ~=? x then y else
        if id ~=? y then x else
          id.

    (* The default instance of [Endo raw_id] that would get picked would be [endo_id]. We locally hijack this choice with our swapping function *)
    Instance swap_endo_raw_id : Endo raw_id := swap_raw_id.

    Definition swap_code T: Endo (code T) := endo.

    (* We can now get for free the swapping over a whole [cfg] *)
    Definition swap_cfg T: Endo (cfg T) := endo.

    (** **
      If we print the definition of [swap_cfg] with implicits, we can see that the sub-term [Endo_cfg swap_cfg (...)].
      Since we have resolved the choice of instance at definition time, we can use this definition outside
      of this section without worrying about it anymore.
  Set Printing Implicit.
  Print swap_cfg.
     *)

    (* And we can do the same for a whole [mcfg] *)
    Definition swap_mcfg T: Endo (mcfg T) := tfmap id.

  End SubstId.

  Section SubstCFG.

    (** **
        Example definition of a transformation substituting a [cfg] in a [mcfg]
     *)

    Context {T : Set}.
    Variable fid: function_id.
    Variable new_f : cfg T.

    (* We define the substitution of cfgs *)
    (* Note: this assumes the new function shares the exact same prototype. *)
    Instance subst_cfg_endo_cfg: Endo (definition T (cfg T)) :=
      fun f =>
        if (dc_name (df_prototype f)) ~=? fid
        then {| df_prototype := df_prototype f; df_args := df_args f ; df_instrs := new_f |}
        else f.

    Definition subst_cfg: Endo (mcfg T) := endo.

  End SubstCFG.

End Examples.

