(** 
    These "Repr" instances for Vellvm should serialize Vellvm ASTs
    into a Coq string which represents the AST, allowing ASTs to be
    serialized and read back into Coq later.

    One potential use for this is for test case generation with
    QuickChick. It may be worthwhile to serialize a counterexample
    into a format that it can be imported into Coq for debugging.
*)

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Eqv.

From Vellvm Require Import LLVMAst Utilities AstLib Syntax.CFG Semantics.TopLevel QC.Utils.
Require Import Integers Floats.

Require Import List.

Import ListNotations.
Import MonadNotation.

From Coq Require Import
     ZArith List String Lia Bool.Bool.

(* Class for the Coq representation of a structure. *)
Class Repr A : Type :=
  {
    repr : A -> string
  }.

Section ReprInstances.
  Global Instance reprList (A : Type) `{Repr A} : Repr (list A) :=
    {
      repr l := ("[" ++ contents repr l ++ "]")%string
    }.

  Global Instance reprInt : Repr LLVMAst.int :=
    {
      repr i := ("(" ++ show i ++ ")%Z")%string
    }.

  Global Instance reprBool : Repr bool :=
    {
      repr := show
    }.

  Global Instance reprString : Repr string
    := {| repr s := ("" ++ show s ++ "")%string |}.

  Definition repr_raw_id (rid : raw_id) : string
    := match rid with
       | Name s => "(Name " ++ repr s ++ ")"
       | Anon i => "(Anon " ++ repr i ++ ")"
       | Raw i  => "(Raw " ++ repr i ++ ")"
       end.

  Global Instance reprRawId : Repr raw_id
    := {| repr := repr_raw_id |}.

  Definition repr_ident (i : ident) : string
    := match i with
       | ID_Global r => "(ID_Global " ++ repr r ++ ")"
       | ID_Local r  => "(ID_Local " ++ repr r ++ ")"
       end.

  Global Instance reprIdent : Repr ident
    := {| repr := repr_ident |}.

  Global Instance reprN : Repr N
    := {| repr := show |}.

  Local Open Scope string.

  Lemma contents_In {A : Type} (l : list A) (f : forall (x : A), In x l -> string) : string.
  Proof.
    induction l.
    - exact "".
    - destruct l.
      + refine (f a _).
        cbn. auto.
      + refine ((f a _ ++ "; ") ++ @IHl _)%string.
        * cbn. auto.
        * intros x H.
          apply (f x). cbn.
          auto.
  Defined.

  (* I don't think I want to use sizeof_typ for measures... *)
  Fixpoint typ_measure (t : typ) : nat :=
    match t with
    | TYPE_I sz => 0
    | TYPE_Pointer t => S (typ_measure t)
    | TYPE_Void => 0
    | TYPE_Half => 0
    | TYPE_Float => 0
    | TYPE_Double => 0
    | TYPE_X86_fp80 => 0
    | TYPE_Fp128 => 0
    | TYPE_Ppc_fp128 => 0
    | TYPE_Metadata => 0
    | TYPE_X86_mmx => 0
    | TYPE_Array sz t => S (typ_measure t)
    | TYPE_Function ret args => S (typ_measure ret + list_sum (map typ_measure args))
    | TYPE_Struct fields => S (list_sum (map typ_measure fields))
    | TYPE_Packed_struct fields => S (list_sum (map typ_measure fields))
    | TYPE_Opaque => 0
    | TYPE_Vector sz t => S (typ_measure t)
    | TYPE_Identified id => 0
    end.

  Program Fixpoint repr_typ (t : typ) {measure (typ_measure t)} : string :=
    match t with
    | TYPE_I sz                 => "(TYPE_I " ++ repr sz ++ ")"
    | TYPE_Pointer t            => "(TYPE_Pointer " ++ repr_typ t ++ ")"
    | TYPE_Void                 => "TYPE_Void"
    | TYPE_Half                 => "TYPE_Half"
    | TYPE_Float                => "TYPE_Float"
    | TYPE_Double               => "TYPE_Double"
    | TYPE_X86_fp80             => "TYPE_X86_fp80"
    | TYPE_Fp128                => "TYPE_Fp128"
    | TYPE_Ppc_fp128            => "TYPE_Ppc_fp128"
    | TYPE_Metadata             => "TYPE_Metadata"
    | TYPE_X86_mmx              => "TYPE_X86_mmx"
    | TYPE_Array sz t           => "(TYPE_Array (" ++ repr sz ++ ") (" ++ repr_typ t ++ "))"
    | TYPE_Function ret args    => "(TYPE_Function (" ++ repr_typ ret ++ ") [" ++ contents_In args (fun arg HIn => repr_typ arg) ++ "])"
    | TYPE_Struct fields        => "(TYPE_Struct [" ++ contents_In fields (fun fld HIn => repr_typ fld) ++ "])"
    | TYPE_Packed_struct fields => "(TYPE_Packed_struct [" ++ contents_In fields (fun fld HIn => repr_typ fld) ++ "])"
    | TYPE_Opaque               => "TYPE_Opaque"
    | TYPE_Vector sz t          => "(TYPE_Vector (" ++ repr sz ++ ") (" ++ repr_typ t ++ ")"
    | TYPE_Identified id        => "(TYPE_Identified " ++ repr id ++ ")"
    end.
  Next Obligation.
    cbn in *.
    lia.
  Qed.
  Next Obligation.
    cbn.
    pose proof (list_sum_map typ_measure arg args HIn).
    lia.
  Qed.
  Next Obligation.
    cbn.
    pose proof (list_sum_map typ_measure fld fields HIn).
    lia.
  Qed.
  Next Obligation.
    cbn.
    pose proof (list_sum_map typ_measure fld fields HIn).
    lia.
  Qed.

  Global Instance reprTyp:  Repr typ :=
    {|
    repr := repr_typ
    |}.

  Definition repr_ibinop (iop : ibinop) : string
    := match iop with
       (* TODO print flags *)
       | LLVMAst.Add a b => "(LLVMAst.Add " ++ repr a ++ " " ++ repr b ++ ")"
       | Sub a b => "(Sub " ++ repr a ++ " " ++ repr b ++ ")"
       | Mul a b => "(Mul " ++ repr a ++ " " ++ repr b ++ ")"
       | Shl a b => "(Shl " ++ repr a ++ " " ++ repr b ++ ")"
       | UDiv f  => "(UDiv " ++ repr f ++ ")"
       | SDiv f  => "(SDiv " ++ repr f ++ ")"
       | LShr f  => "(LShr " ++ repr f ++ ")"
       | AShr f  => "(AShr " ++ repr f ++ ")"
       | URem    => "URem"
       | SRem    => "SRem"
       | And     => "And"
       | Or      => "Or"
       | Xor     => "Xor"
       end.

  Global Instance reprIBinop : Repr ibinop
    := {| repr := repr_ibinop |}.

  Definition repr_icmp (cmp : icmp) : string
    := match cmp with
       | Eq  => "Eq"
       | Ne  => "Ne"
       | Ugt => "Ugt"
       | Uge => "Uge"
       | Ult => "Ult"
       | Ule => "Ule"
       | Sgt => "Sgt"
       | Sge => "Sge"
       | Slt => "Slt"
       | Sle => "Sle"
       end.

  Global Instance reprICmp : Repr icmp
    := {| repr := repr_icmp |}.

  Global Instance reprPair (A B : Type) `{Repr A} `{Repr B} : Repr (A * B) :=
    {|
    repr p :=
      match p with
      | (a, b) => "(" ++ repr a ++ ", " ++ repr b ++ ")"
      end
    |}.

  (* Move this *)
  Fixpoint exp_measure {T : Set} (e : exp T) : nat :=
    match e with
    | EXP_Ident id => 0
    | EXP_Integer x => 0
    | EXP_Float f => 0
    | EXP_Double f => 0
    | EXP_Hex f => 0
    | EXP_Bool b => 0
    | EXP_Null => 0
    | EXP_Zero_initializer => 0
    | EXP_Cstring elts => S (list_sum (map (fun et => exp_measure (snd et)) elts))
    | EXP_Undef => 0
    | EXP_Struct fields => S (list_sum (map (fun et => exp_measure (snd et)) fields))
    | EXP_Packed_struct fields => S (list_sum (map (fun et => exp_measure (snd et)) fields))
    | EXP_Array elts => S (list_sum (map (fun et => exp_measure (snd et)) elts))
    | EXP_Vector elts => S (list_sum (map (fun et => exp_measure (snd et)) elts))
    | OP_IBinop iop t v1 v2 => S (exp_measure v1 + exp_measure v2)
    | OP_ICmp cmp t v1 v2 => S (exp_measure v1 + exp_measure v2)
    | OP_FBinop fop fm t v1 v2 => S (exp_measure v1 + exp_measure v2)
    | OP_FCmp cmp t v1 v2 => S (exp_measure v1 + exp_measure v2)
    | OP_Conversion conv t_from v t_to => S (exp_measure v)
    | OP_GetElementPtr t ptrval idxs => S (exp_measure (snd ptrval) + list_sum (map (fun et => exp_measure (snd et)) idxs))
    | OP_ExtractElement vec idx => S (exp_measure (snd vec) + exp_measure (snd idx))
    | OP_InsertElement vec elt idx => S (exp_measure (snd vec) + exp_measure (snd elt) + exp_measure (snd idx))
    | OP_ShuffleVector vec1 vec2 idxmask => S (exp_measure (snd vec1) + exp_measure (snd vec2) + exp_measure (snd idxmask))
    | OP_ExtractValue vec idxs => S (exp_measure (snd vec))
    | OP_InsertValue vec elt idxs => S (exp_measure (snd vec) + exp_measure (snd elt))
    | OP_Select cnd v1 v2 => S (exp_measure (snd cnd) + exp_measure (snd v1) + exp_measure (snd v2) )
    | OP_Freeze v => S (exp_measure (snd v))
    end.

  Definition pair_repr {A B : Type} (fa : A -> string) (fb : B -> string) (ab : A * B) : string :=
    match ab with
    | (a, b) =>
      "(" ++ fa a ++ ", " ++ fb b ++ ")"
    end.


  Ltac exp_measure_solve :=
    solve [cbn; lia
          |
          cbn;
          match goal with
          | HIn : In ?x ?xs |- context [ list_sum (map ?f _)] =>
            pose proof (list_sum_map f x xs HIn)
          end;
          cbn in *; lia
          | repeat split; discriminate
          ].

  Obligation Tactic := try Tactics.program_simpl; try solve [exp_measure_solve].
  Program Fixpoint repr_exp (v : exp typ) {measure (exp_measure v)} : string :=
    match v with
    | EXP_Ident id => "(EXP_Ident " ++ repr id ++ ")"
    | EXP_Integer x => "(EXP_Integer " ++ repr x ++ ")"
    | EXP_Bool b => "(EXP_Bool " ++ repr b ++ ")"
    | EXP_Null => "EXP_Null"
    | EXP_Zero_initializer => "EXP_Zero_initializer"
    | EXP_Cstring s =>
      "(EXP_Cstring [" ++ contents_In s (fun '(t, e) HIn => "(" ++ repr t ++ ", " ++ repr_exp e ++ ")") ++ "])"
    | EXP_Undef => "EXP_Undef"
    | OP_IBinop iop t v1 v2 =>
      "(OP_IBinop " ++ repr iop ++ " " ++ repr t ++ " " ++ repr_exp v1 ++ " " ++ repr_exp v2 ++ ")"
    | OP_ICmp cmp t v1 v2 =>
      "(OP_ICmp " ++ repr cmp ++ " " ++ repr t ++ " " ++ repr_exp v1 ++ " " ++ repr_exp v2 ++ ")"
    | OP_GetElementPtr t ptrval idxs =>
      "(OP_GetElementPtr " ++ repr t ++
                           "(" ++ repr (fst ptrval) ++ ", " ++ repr_exp (snd ptrval) ++ ") [" ++ contents_In idxs (fun '(t, e) Hin => "(" ++ repr t ++ ", " ++ repr_exp e ++ ")") ++ "])"
    | OP_Select (tc, cnd) (t1, v1) (t2, v2) =>
      "(OP_Select ( " ++ repr tc ++ ", " ++ repr_exp cnd ++ ") (" ++ repr t1 ++ ", " ++ repr_exp v1  ++ ") (" ++ repr t2 ++ ", " ++ repr_exp v2 ++ "))"
    | _ => "repr_exp todo"
    end.

  Global Instance reprExp : Repr (exp typ)
    := {| repr := repr_exp |}.

  Global Instance reprTExp : Repr (texp typ)
    := {| repr te :=
            match te with
            | (t, e) => "(" ++ repr t ++ ", " ++ repr e ++ ")"
            end
       |}.

  Definition repr_opt {A} `{Repr A} (ma : option A) : string
    := match ma with
       | None   => "None"
       | Some a => "(Some " ++ repr a ++ ")"
       end.

  Global Instance reprOption (A : Type) `{Repr A} : Repr (option A) :=
    {| repr := repr_opt |}.

  Definition repr_instr (i : instr typ) : string
    := match i with
       | INSTR_Comment s => "(INSTR_Comment " ++ s ++ ")"
       | INSTR_Op e => "(INSTR_Op " ++ repr e ++ ")"
       | INSTR_Load vol t ptr align =>
         "(INSTR_Load " ++ repr vol ++ " " ++ repr t ++ " " ++ repr ptr ++ " " ++ repr align ++ ")"
       | INSTR_Store vol tval ptr align =>
         "(INSTR_Store " ++ repr vol ++ " " ++ repr tval ++ " " ++ repr ptr ++ " " ++ repr align ++ ")"
       | INSTR_Alloca t nb align =>
         "(INSTR_Alloca " ++ repr t ++ " " ++ repr nb ++ " " ++ repr align ++ ")"
       | _ => "repr_instr todo"
       end.

  Global Instance reprInstr : Repr (instr typ)
    := {| repr := repr_instr |}.

  Global Instance reprInstrId : Repr instr_id
    := {| repr i :=
            match i with
            | IId raw => ("(IId " ++ repr raw ++ ")")%string
            | IVoid n => ("(IVoid " ++ repr n ++ ")")%string
            end
       |}.

  Definition repr_terminator (t : terminator typ) : string
    := match t with
       | TERM_Ret v => "(TERM_Ret " ++ repr v ++ ")"
       | TERM_Ret_void => "TERM_Ret_void"
       | TERM_Br te b1 b2 =>
         "(TERM_Br " ++ repr te ++ " " ++ repr b1 ++ " " ++ repr b2 ++ ")"
       | TERM_Br_1 b => "(TERM_Br_1 " ++ repr b ++ ")"
       | _ => "repr_terminator todo"
       end.

  Global Instance reprTerminator : Repr (terminator typ)
    := {| repr := repr_terminator |}.

  Definition repr_phi (p : phi typ) : string
    := match p with
       | Phi t args =>
         "(Phi " ++ repr t ++ repr args ++ ")"
       end.

  Global Instance reprPhi : Repr (phi typ)
    := {| repr := repr_phi
       |}.

  Definition repr_block (b : block typ) : string
    :=
      match b with
      | mk_block blk_id blk_phis blk_code blk_term blk_comments =>
        "(mk_block " ++ repr blk_id ++ " " ++ repr blk_phis ++ " " ++ repr blk_code ++ " " ++ repr blk_term ++ " " ++ repr blk_comments ++ ")"
      end.

  Global Instance reprBlock: Repr (block typ) :=
    {|
    repr := repr_block
    |}.

  Definition repr_param_attr (pa : param_attr) : string :=
    match pa with
    | PARAMATTR_Zeroext => "PARAMATTR_Zeroext"
    | PARAMATTR_Signext => "PARAMATTR_Signext"
    | PARAMATTR_Inreg => "PARAMATTR_Inreg"
    | PARAMATTR_Byval => "PARAMATTR_Byval"
    | PARAMATTR_Inalloca => "PARAMATTR_Inalloca"
    | PARAMATTR_Sret => "PARAMATTR_Sret"
    | PARAMATTR_Align a => "(PARAMATTR_Align " ++ repr a ++ ")"
    | PARAMATTR_Noalias => "PARAMATTR_Noalias"
    | PARAMATTR_Nocapture => "PARAMATTR_Nocapture"
    | PARAMATTR_Readonly => "PARAMATTR_Readonly"
    | PARAMATTR_Nest => "PARAMATTR_Nest"
    | PARAMATTR_Returned => "PARAMATTR_Returned"
    | PARAMATTR_Nonnull => "PARAMATTR_Nonnull"
    | PARAMATTR_Dereferenceable a => "(PARAMATTR_Dereferenceable " ++ repr a ++ ")"
    | PARAMATTR_Immarg => "PARAMATTR_Immarg"
    | PARAMATTR_Noundef => "PARAMATTR_Noundef"
    | PARAMATTR_Nofree => "PARAMATTR_Nofree"
    end.

  Global Instance reprParamAttr : Repr (param_attr) :=
    {| repr := repr_param_attr |}.

  Definition repr_linkage (l : linkage) : string :=
    match l with
    | LINKAGE_Private => "LINKAGE_Private"
    | LINKAGE_Internal => "LINKAGE_Internal"
    | LINKAGE_Available_externally => "LINKAGE_Available_externally"
    | LINKAGE_Linkonce => "LINKAGE_Linkonce"
    | LINKAGE_Weak => "LINKAGE_Weak"
    | LINKAGE_Common => "LINKAGE_Common"
    | LINKAGE_Appending => "LINKAGE_Appending"
    | LINKAGE_Extern_weak => "LINKAGE_Extern_weak"
    | LINKAGE_Linkonce_odr => "LINKAGE_Linkonce_odr"
    | LINKAGE_Weak_odr => "LINKAGE_Weak_odr"
    | LINKAGE_External => "LINKAGE_External"
    end.

  Global Instance reprLinkage : Repr linkage :=
    {| repr := repr_linkage |}.

  Definition repr_visibility (v : visibility) : string :=
    match v with
    | VISIBILITY_Default => "VISIBILITY_Default"
    | VISIBILITY_Hidden => "VISIBILITY_Hidden"
    | VISIBILITY_Protected => "VISIBILITY_Protected"
    end.

  Global Instance reprVisibility : Repr visibility :=
    {| repr := repr_visibility |}.

  Definition repr_dll_storage (d : dll_storage) : string :=
    match d with
    | DLLSTORAGE_Dllimport => "DLLSTORAGE_Dllimport"
    | DLLSTORAGE_Dllexport => "DLLSTORAGE_Dllexport"
    end.

  Global Instance reprDll_Storage : Repr dll_storage :=
    {| repr := repr_dll_storage |}.

  Definition repr_cconv (c : cconv) : string :=
    match c with
    | CC_Ccc => "CC_Ccc"
    | CC_Fastcc => "CC_Fastcc"
    | CC_Coldcc => "CC_Coldcc"
    | CC_Cc cc => "CC_Cc cc"
    end.

  Global Instance reprCconv : Repr cconv :=
    {| repr := repr_cconv |}.

  Definition repr_fn_attr (fa : fn_attr) : string :=
    match fa with
    | FNATTR_Alignstack a => "(FNATTR_Alignstack " ++ repr a ++ ")"
    | FNATTR_Allocsize l => "(FNATTR_Allocsize " ++ repr l ++ ")"
    | FNATTR_Alwaysinline => "FNATTR_Alwaysinline"
    | FNATTR_Builtin => "FNATTR_Builtin"
    | FNATTR_Cold => "FNATTR_Cold"
    | FNATTR_Convergent => "FNATTR_Convergent"
    | FNATTR_Hot => "FNATTR_Hot"
    | FNATTR_Inaccessiblememonly => "FNATTR_Inaccessiblememonly"
    | FNATTR_Inaccessiblemem_or_argmemonly => "FNATTR_Inaccessiblemem_or_argmemonly"
    | FNATTR_Inlinehint => "FNATTR_Inlinehint"
    | FNATTR_Jumptable => "FNATTR_Jumptable"
    | FNATTR_Minsize => "FNATTR_Minsize"
    | FNATTR_Naked => "FNATTR_Naked"
    | FNATTR_No_jump_tables => "FNATTR_No_jump_tables"
    | FNATTR_Nobuiltin => "FNATTR_Nobuiltin"
    | FNATTR_Noduplicate => "FNATTR_Noduplicate"
    | FNATTR_Nofree => "FNATTR_Nofree"
    | FNATTR_Noimplicitfloat => "FNATTR_Noimplicitfloat"
    | FNATTR_Noinline => "FNATTR_Noinline"
    | FNATTR_Nomerge => "FNATTR_Nomerge"
    | FNATTR_Nonlazybind => "FNATTR_Nonlazybind"
    | FNATTR_Noredzone => "FNATTR_Noredzone"
    | FNATTR_Indirect_tls_seg_refs => "FNATTR_Indirect_tls_seg_refs"
    | FNATTR_Noreturn => "FNATTR_Noreturn"
    | FNATTR_Norecurse => "FNATTR_Norecurse"
    | FNATTR_Willreturn => "FNATTR_Willreturn"
    | FNATTR_Nosync => "FNATTR_Nosync"
    | FNATTR_Nounwind => "FNATTR_Nounwind"
    | FNATTR_Null_pointer_is_valid => "FNATTR_Null_pointer_is_valid"
    | FNATTR_Optforfuzzing => "FNATTR_Optforfuzzing"
    | FNATTR_Optnone => "FNATTR_Optnone"
    | FNATTR_Optsize => "FNATTR_Optsize"
    | FNATTR_Readnone => "FNATTR_Readnone"
    | FNATTR_Readonly => "FNATTR_Readonly"
    | FNATTR_Writeonly => "FNATTR_Writeonly"
    | FNATTR_Argmemonly => "FNATTR_Argmemonly"
    | FNATTR_Returns_twice => "FNATTR_Returns_twice"
    | FNATTR_Safestack => "FNATTR_Safestack"
    | FNATTR_Sanitize_address => "FNATTR_Sanitize_address"
    | FNATTR_Sanitize_memory => "FNATTR_Sanitize_memory"
    | FNATTR_Sanitize_thread => "FNATTR_Sanitize_thread"
    | FNATTR_Sanitize_hwaddress => "FNATTR_Sanitize_hwaddress"
    | FNATTR_Sanitize_memtag => "FNATTR_Sanitize_memtag"
    | FNATTR_Speculative_load_hardening => "FNATTR_Speculative_load_hardening"
    | FNATTR_Speculatable => "FNATTR_Speculatable"
    | FNATTR_Ssp => "FNATTR_Ssp"
    | FNATTR_Sspreq => "FNATTR_Sspreq"
    | FNATTR_Sspstrong => "FNATTR_Sspstrong"
    | FNATTR_Strictfp => "FNATTR_Strictfp"
    | FNATTR_Uwtable => "FNATTR_Uwtable"
    | FNATTR_Nocf_check => "FNATTR_Nocf_check"
    | FNATTR_Shadowcallstack => "FNATTR_Shadowcallstack"
    | FNATTR_Mustprogress => "FNATTR_Mustprogress"
    | FNATTR_String s => "(FNATTR_String " ++ repr s ++ ")"
    | FNATTR_Key_value kv => "(FNATTR_Key_value " ++ repr kv ++ ")"
    | FNATTR_Attr_grp g => "(FNATTR_Attr_grp " ++ repr g ++ ")"
    end.

  Global Instance reprFn_Attr : Repr fn_attr :=
    {| repr := repr_fn_attr |}.

  Definition repr_declaration (dec : declaration typ) : string
    := match dec with
       | mk_declaration dc_name dc_type dc_param_attrs dc_linkage dc_visibility dc_dll_storage dc_cconv
                        dc_attrs dc_section dc_align dc_gc =>
         "(mk_declaration " ++ repr dc_name ++ " "
                            ++ repr dc_type ++ " "
                            ++ repr dc_param_attrs ++ " "
                            ++ repr dc_linkage ++ " "
                            ++ repr dc_visibility ++ " "
                            ++ repr dc_dll_storage ++ " "
                            ++ repr dc_cconv ++ " "
                            ++ repr dc_attrs ++ " "
                            ++ repr dc_section ++ " "
                            ++ repr dc_align ++ " "
                            ++ repr dc_gc ++ ")"
       end.
  
  Global Instance reprDeclaration : Repr (declaration typ) :=
    {| repr := repr_declaration |}.

  Definition repr_definition (defn : definition typ (block typ * list (block typ))) : string
    :=
      match defn with
      | mk_definition _ df_prototype df_args df_instrs =>
        "(mk_definition _ " ++ repr df_prototype ++ " "
                            ++ repr df_args ++ " "
                            ++ repr df_instrs ++ ")"
      end.

  Global Instance reprDefinition: Repr (definition typ (block typ * list (block typ))) :=
    {| repr := repr_definition |}.

  Definition repr_thread_local_storage (tls : thread_local_storage) : string :=
    match tls with
    | TLS_Localdynamic => "TLS_Localdynamic"
    | TLS_Initialexec => "TLS_Initialexec"
    | TLS_Localexec => "TLS_Localexec"
    end.

  Global Instance reprThread_Local_Storage : Repr thread_local_storage :=
    {| repr := repr_thread_local_storage |}.


  Definition repr_global (g : global typ) : string :=
    match g with
    | mk_global g_ident g_typ g_constant g_exp g_linkage g_visibility g_dll_storage g_thread_local
                g_unnamed_addr g_addrspace g_externally_initialized g_section g_align =>
      "(mk_global " ++ repr g_ident ++ " "
                    ++ repr g_typ ++ " "
                    ++ repr g_constant ++ " "
                    ++ repr g_exp ++ " "
                    ++ repr g_linkage ++ " "
                    ++ repr g_visibility ++ " "
                    ++ repr g_dll_storage ++ " "
                    ++ repr g_thread_local ++ " "
                    ++ repr g_unnamed_addr ++ " "
                    ++ repr g_addrspace ++ " "
                    ++ repr g_externally_initialized ++ " "
                    ++ repr g_section ++ " "
                    ++ repr g_align ++ " "
                    ++ ")"
    end.

  Global Instance reprGlobal : Repr (global typ) :=
    {| repr := repr_global |}.

  Fixpoint metadata_measure (m : metadata typ) : nat
    := match m with
       | METADATA_Const tv => 0
       | METADATA_Null => 0
       | METADATA_Id id => 0
       | METADATA_String str => 0
       | METADATA_Named strs => 0
       | METADATA_Node mds => S (list_sum (map metadata_measure mds))
       end.
        
  Program Fixpoint repr_metadata (m : metadata typ) {measure (metadata_measure m)}: string :=
    match m with
    | METADATA_Const tv => "(METADATA_Const " ++ repr tv ++ ")"
    | METADATA_Null => "METADATA_Null"
    | METADATA_Id id => "(METADATA_Id " ++ repr id ++ ")"
    | METADATA_String str => "(METADATA_String " ++ repr str ++ ")"
    | METADATA_Named strs => "(METADATA_Named " ++ repr strs ++ ")"
    | METADATA_Node mds => "(METADATA_Node [" ++ contents_In mds (fun md Hin => repr_metadata md) ++ "])"
    end.

  Global Instance reprMetadata : Repr (metadata typ) :=
    {| repr := repr_metadata |}.

  Definition repr_tle (tle : toplevel_entity typ (block typ * list (block typ))) : string
    := match tle with
       | TLE_Comment msg => "(TLE_Comment " ++ repr msg ++ ")"
       | TLE_Target tgt => "(TLE_Target " ++ repr tgt ++ ")"
       | TLE_Datalayout layout => "(TLE_Datalayout " ++ repr layout ++ ")"
       | TLE_Declaration decl => "(TLE_Declaration " ++ repr decl ++ ")"
       | TLE_Definition defn => "(TLE_Definition " ++ repr defn ++ ")"
       | TLE_Type_decl id t => "(TLE_Type_decl " ++ repr id ++ " " ++ repr t ++ ")"
       | TLE_Source_filename s => "(TLE_Source_filename " ++ repr s ++ ")"
       | TLE_Global g => "(TLE_Global " ++ repr g ++ ")"
       | TLE_Metadata id md => "(TLE_Metadata " ++ repr id ++ " " ++ repr md ++ ")"
       | TLE_Attribute_group i attrs => "(TLE_Attribute_group " ++ repr i ++ " " ++ repr attrs ++ ")"
       end.

  Global Instance reprTLE: Repr (toplevel_entity typ (block typ * list (block typ))) :=
    {| repr := repr_tle |}.

End ReprInstances.
