(**
    These "Repr" instances for Vellvm should serialize Vellvm ASTs
    into a Coq string which represents the AST, allowing ASTs to be
    serialized and read back into Coq later.

    One potential use for this is for test case generation with
    QuickChick. It may be worthwhile to serialize a counterexample
    into a format that it can be imported into Coq for debugging.
*)

From Vellvm Require Import LLVMAst ShowAST Utilities DynamicTypes.


Require Import List.


Import ListNotations.

From Coq Require Import
     ZArith String.

From QuickChick Require Import Show.
Set Warnings "-extraction-opaque-accessed,-extraction".

(* Class for the Coq representation of a structure. *)
Class Repr A : Type :=
  {
    repr : A -> string
  }.

Section ReprInstances.
  #[global]
   Instance reprList (A : Type) `{Repr A} : Repr (list A) :=
    {
      repr l := ("[" ++ contents repr l ++ "]")%string
    }.

  #[global]
   Instance reprInt : Repr LLVMAst.int_ast :=
    {
      repr i := ("(" ++ show i ++ ")%Z")%string
    }.

  #[global]
   Instance reprBool : Repr bool :=
    {
      repr := show
    }.

  #[global]
   Instance reprString : Repr string
    := {| repr s := ("" ++ show s ++ "")%string |}.

  Definition repr_raw_id (rid : raw_id) : string
    := match rid with
       | Name s => "(Name " ++ repr s ++ ")"
       | Anon i => "(Anon " ++ repr i ++ ")"
       | Raw i  => "(Raw " ++ repr i ++ ")"
       end.

  #[global]
   Instance reprRawId : Repr raw_id
    := {| repr := repr_raw_id |}.

  Definition repr_ident (i : ident) : string
    := match i with
       | ID_Global r => "(ID_Global " ++ repr r ++ ")"
       | ID_Local r  => "(ID_Local " ++ repr r ++ ")"
       end.

  #[global]
   Instance reprIdent : Repr ident
    := {| repr := repr_ident |}.

  #[global]
   Instance reprN : Repr N
    := {| repr := show |}.

  #[global]
   Instance reprPos : Repr positive
    := {| repr := show |}.

  Local Open Scope string.

  Fixpoint repr_dtyp (t : dtyp) : string :=
    match t with
    | DTYPE_I sz => "(DTYPE_I " ++ repr sz ++ ")"
    | DTYPE_IPTR => "DTYPE_IPTR"
    | DTYPE_Pointer => "DTYPE_Pointer"
    | DTYPE_Void => "DTYPE_Void"
    | DTYPE_Half => "DTYPE_Half"
    | DTYPE_Float => "DTYPE_Float"
    | DTYPE_Double => "DTYPE_Double"
    | DTYPE_X86_fp80 => "DTYPE_X86_fp80"
    | DTYPE_Fp128 => "DTYPE_Fp128"
    | DTYPE_Ppc_fp128 => "DTYPE_Ppc_fp128"
    | DTYPE_Metadata => "DTYPE_Metadata"
    | DTYPE_X86_mmx => "DTYPE_X86_mmx"
    | DTYPE_Array sz t => "(DTYPE_Array (" ++ repr sz ++ ") (" ++ repr_dtyp t ++ "))"
    | DTYPE_Struct fields => "(DTYPE_Struct [" ++ (contents id (List.map repr_dtyp fields)) ++ "])"
    | DTYPE_Packed_struct fields => "(DTYPE_Packed_struct [" ++ (contents id (List.map repr_dtyp fields)) ++ "])"
    | DTYPE_Opaque => "DTYPE_Opaque"
    | DTYPE_Vector sz t => "(DTYPE_Vector (" ++ repr sz ++ ") (" ++ repr_dtyp t ++ "))"
    end.

  Fixpoint repr_typ (t : typ) : string :=
    match t with
    | TYPE_I sz                 => "(TYPE_I " ++ repr sz ++ ")"
    | TYPE_IPTR                 => "TYPE_IPTR"
    | TYPE_Pointer (Some t)     => "(TYPE_Pointer (Some " ++ repr_typ t ++ "))"
    | TYPE_Pointer None         => "(TYPE_Pointer None)"
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
    | TYPE_Function ret args varargs
      => "(TYPE_Function (" ++ repr_typ ret ++ ")
        [" ++ (contents id (List.map repr_typ args)) ++ "]"
        ++ " " ++ (if varargs then "true" else "false") ++ ")"
    | TYPE_Struct fields        => "(TYPE_Struct [" ++ (contents id (List.map repr_typ fields)) ++ "])"
    | TYPE_Packed_struct fields => "(TYPE_Packed_struct [" ++ (contents id (List.map repr_typ fields)) ++ "])"
    | TYPE_Opaque               => "TYPE_Opaque"
    | TYPE_Vector sz t          => "(TYPE_Vector (" ++ repr sz ++ ") (" ++ repr_typ t ++ "))"
    | TYPE_Identified id        => "(TYPE_Identified " ++ repr id ++ ")"
    end.

  #[global]
   Instance reprTyp:  Repr typ :=
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

  #[global]
   Instance reprIBinop : Repr ibinop
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

  #[global]
   Instance reprICmp : Repr icmp
    := {| repr := repr_icmp |}.

  #[global]
   Instance reprPair (A B : Type) `{Repr A} `{Repr B} : Repr (A * B) :=
    {|
    repr p :=
      match p with
      | (a, b) => "(" ++ repr a ++ ", " ++ repr b ++ ")"
      end
    |}.

  Definition pair_repr {A B : Type} (fa : A -> string) (fb : B -> string) (ab : A * B) : string :=
    match ab with
    | (a, b) =>
      "(" ++ fa a ++ ", " ++ fb b ++ ")"
    end.

  Definition repr_conversion_type (c:conversion_type) : string :=
    match c with
    | Trunc => "Trunc"
    | Zext => "Zext"
    | Sext => "Sext"
    | Fptrunc => "Fptrunc"
    | Fpext => "Fpext"
    | Uitofp => "Uitofp"
    | Sitofp => "Sitofp"
    | Fptoui => "Fptoui"
    | Fptosi => "Fptosi"
    | Inttoptr  => "Inttoptr "
    | Ptrtoint => "Ptrtoint"
    | Bitcast => "Bitcast"
    | Addrspacecast => "Addrspacecast"
    end.

  #[global]
   Instance reprConversionType : Repr conversion_type :=
    {| repr := repr_conversion_type |}.

  Definition repr_fbinop (f:fbinop) : string :=
    match f with
    | FAdd => "FAdd"
    | FSub => "FSub"
    | FMul => "FMul"
    | FDiv => "FDiv"
    | FRem => "FRem"
    end.

  #[global]
   Instance reprFBinop : Repr fbinop :=
    {| repr := repr_fbinop |}.

  Definition repr_fast_math (fm:fast_math) : string :=
    match fm with
    | Nnan => "Nnan"
    | Ninf => "Ninf"
    | Nsz => "Nsz"
    | Arcp => "Arcp"
    | Contract => "Contract"
    | Afn => "Afn"
    | Reassoc => "Reassoc"
    | Fast => "Fast"
    end.

  #[global]
   Instance reprFastMath : Repr fast_math :=
    {| repr := repr_fast_math |}.

  Definition repr_fcmp (f:fcmp) : string :=
    match f with
    | FFalse => "FFalse"
    | FOeq => "FOeq"
    | FOgt => "FOgt"
    | FOge => "FOge"
    | FOlt => "FOlt"
    | FOle => "FOle"
    | FOne => "FOne"
    | FOrd => "FOrd"
    | FUno => "FUno"
    | FUeq => "FUeq"
    | FUgt => "FUgt"
    | FUge => "FUge"
    | FUlt => "FUlt"
    | FUle => "FUle"
    | FUne => "FUne"
    | FTrue => "FTrue"
    end.

  #[global]
   Instance reprFCmp : Repr fcmp :=
    {| repr := repr_fcmp |}.

  Fixpoint repr_exp (v : exp typ) : string :=
    let texp (te : (typ * exp typ)) : string :=
      let '(t, e) := te in "(" ++ repr_typ t ++ ", " ++ repr_exp e ++ ")"
    in
    match v with
    | EXP_Ident id => "(EXP_Ident " ++ repr id ++ ")"
    | EXP_Integer x => "(EXP_Integer " ++ repr x ++ ")"
    | EXP_Float f  => "(EXP_Float  (Float.of_bits (@Integers.repr 32 " ++ show f ++ ")))"
    | EXP_Double f => "(EXP_Double (Float.of_bits (@Integers.repr 64 " ++ show f ++ ")))"
    | EXP_Hex f => "(EXP_Hex (Float.of_bits (@Integers.repr 64 " ++ show f ++ ")))"
    | EXP_Bool b => "(EXP_Bool " ++ repr b ++ ")"
    | EXP_Null => "EXP_Null"
    | EXP_Zero_initializer => "EXP_Zero_initializer"
    | EXP_Cstring s => "(EXP_Cstring [" ++ (contents id (List.map texp s)) ++ "])"
    | EXP_Undef => "EXP_Undef"
    | EXP_Poison => "EXP_Poison"
    | EXP_Struct fields => "(EXP_Struct [" ++ (contents id (List.map texp fields)) ++ "])"
    | EXP_Packed_struct fields => "(EXP_Packed_struct [" ++ (contents id (List.map texp fields)) ++ "])"
    | EXP_Array t fields => "(EXP_Array (" ++ repr t ++ ")" ++ " [" ++ (contents id (List.map texp fields)) ++ "])"
    | EXP_Vector t fields => "(EXP_vector (" ++ repr t ++ ")" ++ " [" ++ (contents id (List.map texp fields)) ++ "])"
    | OP_IBinop iop t v1 v2 =>
      "(OP_IBinop " ++ repr iop ++ " " ++ repr t ++ " " ++ repr_exp v1 ++ " " ++ repr_exp v2 ++ ")"
    | OP_ICmp cmp t v1 v2 =>
        "(OP_ICmp " ++ repr cmp ++ " " ++ repr t ++ " " ++ repr_exp v1 ++ " " ++ repr_exp v2 ++ ")"
    | OP_FBinop fop fm t v1 v2 =>
        "(OP_FBinop " ++ repr fop ++ " [" ++ (contents id (List.map repr_fast_math fm)) ++
                      "] " ++ repr t ++ " " ++ repr_exp v1 ++ " " ++ repr_exp v2 ++ ")"
    | OP_FCmp cmp t v1 v2 =>
        "(OP_FCmp " ++ repr cmp ++ " " ++ repr t ++ " " ++ repr_exp v1 ++ " " ++ repr_exp v2 ++ ")"
    | OP_Conversion c from v to =>
        "(OP_Conversion " ++ repr c ++ " " ++ repr from ++ " " ++ repr_exp v ++ " " ++ repr to ++ ")"
    | OP_GetElementPtr t ptrval idxs =>
        "(OP_GetElementPtr " ++ repr t ++
                             "(" ++ texp ptrval ++  ") ["
                             ++ (contents id (List.map texp idxs)) ++ "])"
    | OP_ExtractElement v i =>
        "(OP_ExtractElement " ++ texp v ++ " " ++ texp i ++ ")"
    | OP_InsertElement v e i =>
        "(OP_ExtractElement " ++ texp v ++ " " ++ texp e ++ " " ++ texp i ++ ")"
    | OP_ShuffleVector v1 v2 mask =>
        "(OP_ShuffleVector " ++ texp v1 ++ " " ++ texp v2 ++ " " ++ texp mask ++ ")"
    | OP_ExtractValue v idxs =>
        "(OP_ExtractValue " ++ texp v ++ " [" ++ (contents id (List.map show idxs)) ++ "])"
    | OP_InsertValue v e idxs =>
        "(OP_ExtractValue " ++ texp v ++ " " ++ texp e ++ " [" ++ (contents id (List.map show idxs)) ++ "])"
    | OP_Select cnd v1 v2 =>
        "(OP_Select " ++ texp cnd ++ " " ++ texp v1 ++ " " ++ texp v2 ++ ")"
    | OP_Freeze v =>
        "(OP_Freez " ++ texp v ++")"
    end.


  #[global]
   Instance reprExp : Repr (exp typ)
    := {| repr := repr_exp |}.

  #[global]
   Instance reprTExp : Repr (texp typ)
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

  #[global]
   Instance reprOption (A : Type) `{Repr A} : Repr (option A) :=
    {| repr := repr_opt |}.


   Definition repr_param_attr (pa : param_attr) : string :=
    match pa with
    | PARAMATTR_Zeroext => "PARAMATTR_Zeroext"
    | PARAMATTR_Signext => "PARAMATTR_Signext"
    | PARAMATTR_Inreg => "PARAMATTR_Inreg"
    | PARAMATTR_Byval t => "PARAMATTR_Byval " ++ repr t
    | PARAMATTR_Byref (t) => "PARAMATTR_Byref " ++ repr t
    | PARAMATTR_Preallocated (t) => "PARAMATTR_Preallocated " ++ repr t
    | PARAMATTR_Inalloca t => "PARAMATTR_Inalloca " ++ repr t
    | PARAMATTR_Sret t => "PARAMATTR_Sret " ++ repr t
    | PARAMATTR_Elementtype (t) => "PARAMATTR_Elementtype " ++ repr t
    | PARAMATTR_Align a => "(PARAMATTR_Align " ++ repr a ++ ")"
    | PARAMATTR_Noalias => "PARAMATTR_Noalias"
    | PARAMATTR_Nocapture => "PARAMATTR_Nocapture"
    | PARAMATTR_Nofree => "PARAMATTR_Nofree"
    | PARAMATTR_Nest => "PARAMATTR_Nest"
    | PARAMATTR_Returned => "PARAMATTR_Returned"
    | PARAMATTR_Nonnull => "PARAMATTR_Nonnull"
    | PARAMATTR_Dereferenceable a => "(PARAMATTR_Dereferenceable " ++ repr a ++ ")"
    | PARAMATTR_Dereferenceable_or_null (a) =>  "(PARAMATTR_Dereferenceable_or_null " ++ repr a ++ ")"
    | PARAMATTR_Swiftself =>  "PARAMATTR_Swiftself"
    | PARAMATTR_Swiftasync => "PARAMATTR_Swiftasync"
    | PARAMATTR_Swifterror => "PARAMATTR_Swifterror"
    | PARAMATTR_Immarg => "PARAMATTR_Immarg"
    | PARAMATTR_Noundef => "PARAMATTR_Noundef"
    | PARAMATTR_Alignstack (a) => "PARAMATTR_Alignstack " ++ repr a
    | PARAMATTR_Allocalign =>  "PARAMATTR_Allocalign"
    | PARAMATTR_Allocptr => "PARAMATTR_Allocptr"
    | PARAMATTR_Readnone => "PARAMATTR_Readnone"
    | PARAMATTR_Readonly => "PARAMATTR_Readonly"
    | PARAMATTR_Writeonly => "PARAMATTR_Writeonly"
    | PARAMATTR_Writable => "PARAMATTR_Writable"
    | PARAMATTR_Dead_on_unwind => "PARAMATTR_Dead_on_unwind"
    end.

  #[global]
   Instance reprParamAttr : Repr (param_attr) :=
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

  #[global]
   Instance reprLinkage : Repr linkage :=
    {| repr := repr_linkage |}.

  Definition repr_visibility (v : visibility) : string :=
    match v with
    | VISIBILITY_Default => "VISIBILITY_Default"
    | VISIBILITY_Hidden => "VISIBILITY_Hidden"
    | VISIBILITY_Protected => "VISIBILITY_Protected"
    end.

  #[global]
   Instance reprVisibility : Repr visibility :=
    {| repr := repr_visibility |}.

  Definition repr_dll_storage (d : dll_storage) : string :=
    match d with
    | DLLSTORAGE_Dllimport => "DLLSTORAGE_Dllimport"
    | DLLSTORAGE_Dllexport => "DLLSTORAGE_Dllexport"
    end.

  #[global]
   Instance reprDll_Storage : Repr dll_storage :=
    {| repr := repr_dll_storage |}.

  Definition repr_cconv (c : cconv) : string :=
    match c with
    | CC_Ccc => "CC_Ccc"
    | CC_Fastcc => "CC_Fastcc"
    | CC_Coldcc => "CC_Coldcc"
    | CC_Cc cc => "CC_Cc cc"
    | CC_Webkit_jscc => "CC_Webkit_jscc"
    | CC_Anyregcc  => "CC_Anyregcc"
    | CC_Preserve_allcc => "CC_Preserve_allcc"
    | CC_Cxx_fast_tlscc =>  "CC_Cxx_fast_tlscc"
    | CC_Tailcc =>  "CC_Tailcc"
    | CC_Swiftcc => "CC_Swiftcc"
    | CC_Swifttailcc => "CC_Swifttailcc"
    | CC_cfguard_checkcc => "CC_cfguard_checkcc"
    | CC_Preserve_mostcc => "CC_Preserve_mostcc"
    end.

  #[global]
   Instance reprCconv : Repr cconv :=
    {| repr := repr_cconv |}.

  Definition repr_fn_attr (fa : fn_attr) : string :=
    match fa with
    | FNATTR_Alignstack a => "(FNATTR_Alignstack " ++ repr a ++ ")"
    (* | FNATTR_Alloc_family (fam) => "(FNATTR_Alloc_family " ++ repr fam ++ ")" *)
    | FNATTR_Allockind (kind) => "(FNATTR_Allockind " ++ repr kind ++ ")"
    | FNATTR_Allocsize l l2 => let printable_l2 := match l2 with
                                                 |None => ""
                                                 |Some s => repr s
                                                 end in

        "(FNATTR_Allocsize " ++ repr l ++ printable_l2 ++ ")"
    | FNATTR_Alwaysinline => "FNATTR_Alwaysinline"
    | FNATTR_Builtin => "FNATTR_Builtin"
    | FNATTR_Cold => "FNATTR_Cold"
    | FNATTR_Convergent => "FNATTR_Convergent"
    | FNATTR_Disable_sanitizer_instrumentation => "FNATTR__Disable_sanitizer_instrumentation"
    (* | FNATTR_Dontcall_error => "FNATTR_Dontcall_error"                             *)
    (* | FNATTR_Dontcall_warn => "FNATTR_Dontcall_warn"                           *)
    | FNATTR_Fn_ret_thunk_extern => "FNATTR_Fn_ret_thunk_extern"
    (* | FNATTR_Frame_pointer => "FNATTR_Frame_pointer"                             *)
    | FNATTR_Hot => "FNATTR_Hot"
    | FNATTR_Inaccessiblememonly => "FNATTR_Inaccessiblememonly"
    | FNATTR_Inaccessiblemem_or_argmemonly => "FNATTR_Inaccessiblemem_or_argmemonly"
    | FNATTR_Inlinehint => "FNATTR_Inlinehint"
    | FNATTR_Jumptable => "FNATTR_Jumptable"
    | FNATTR_Minsize => "FNATTR_Minsize"
    | FNATTR_Naked => "FNATTR_Naked"
    (* | FNATTR_No_inline_line_tables  => "FNATTR_No_inline_line_tables" *)
    | FNATTR_No_jump_tables => "FNATTR_No_jump_tables"
    | FNATTR_Nobuiltin => "FNATTR_Nobuiltin"
    | FNATTR_Noduplicate => "FNATTR_Noduplicate"
    | FNATTR_Nofree => "FNATTR_Nofree"
    | FNATTR_Noimplicitfloat => "FNATTR_Noimplicitfloat"
    | FNATTR_Noinline => "FNATTR_Noinline"
    | FNATTR_Nomerge => "FNATTR_Nomerge"
    | FNATTR_Nonlazybind => "FNATTR_Nonlazybind"
    | FNATTR_Noprofile => "FNATTR_Noprofile"
    | FNATTR_Noredzone => "FNATTR_Noredzone"
    | FNATTR_Indirect_tls_seg_refs => "FNATTR_Indirect_tls_seg_refs"
    | FNATTR_Noreturn => "FNATTR_Noreturn"
    | FNATTR_Norecurse => "FNATTR_Norecurse"
    | FNATTR_Willreturn => "FNATTR_Willreturn"
    | FNATTR_Nosync => "FNATTR_Nosync"
    | FNATTR_Nounwind => "FNATTR_Nounwind"
    | FNATTR_Nosanitize_bounds => "FNATTR_Nosanitize_bounds"
    | FNATTR_Nosanitize_coverage => "FNATTR_Nosanitize_coverage"
    | FNATTR_Null_pointer_is_valid => "FNATTR_Null_pointer_is_valid"
    | FNATTR_Optforfuzzing => "FNATTR_Optforfuzzing"
    | FNATTR_Optnone => "FNATTR_Optnone"
    | FNATTR_Optsize => "FNATTR_Optsize"
    (* | FNATTR_Patchable_function => "FNATTR_Patchable_function" *)
    (* | FNATTR_Probe_stack => "FNATTR_Probe_stack"    *)
    | FNATTR_Readnone => "FNATTR_Readnone"
    | FNATTR_Readonly => "FNATTR_Readonly"
    (* | FNATTR_Stack_probe_size => "FNATTR_Stack_probe_size"                              *)
    (* | FNATTR_No_stack_arg_probe => FNATTR_String *)
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
    (* | FNATTR_Denormal_fp_math (s1) (s2) => *)
    (*     let printable_sw := match s2 with *)
    (*                         |None => ""         *)
    (*                         |Some s => repr s             *)
    (*                         end in                       *)
    (*     "(FNATTR_Denormal_fp_math " ++ repr s1 ++ printable_sw ++ ")" *)
    (* | FNATTR_Denormal_fp_math_32 (s1) (s2) => *)
    (*      let printable_sw := match s2 with *)
    (*                         |None => ""         *)
    (*                         |Some s => repr s             *)
    (*                         end in                       *)
    (*      "(FNATTR_Denormal_fp_math32 " ++ repr s1 ++ printable_sw ++ ")" *)
    (* | FNATTR_Thunk => "FNATTR_Thunk" *)
    | FNATTR_Tls_load_hoist => "FNATTR_Tls_load_hoist"
    | FNATTR_Uwtable sync => "FNATTR_Uwtable " ++ repr sync
    | FNATTR_Nocf_check => "FNATTR_Nocf_check"
    | FNATTR_Shadowcallstack => "FNATTR_Shadowcallstack"
    | FNATTR_Mustprogress => "FNATTR_Mustprogress"
    (* | FNATTR_Warn_stack_size (th) => "FNATTR_Warn_stack_size " ++ repr th   *)
    | FNATTR_Vscale_range (min) (max) =>
         let printable_max := match max with
                            |None => ""
                            |Some s => repr s
                            end in
         "(FNATTR_Denormal_fp_math32 " ++ repr min ++ printable_max ++ ")"
    (* | FNATTR_Min_legal_vector_width  (size) => "FNATTR_Min_legal_vector_width " ++ repr size  *)
    | FNATTR_String s => "(FNATTR_String " ++ repr s ++ ")"
    | FNATTR_Key_value kv => "(FNATTR_Key_value " ++ repr kv ++ ")"
    | FNATTR_Attr_grp g => "(FNATTR_Attr_grp " ++ repr g ++ ")"
    end.

  #[global]
   Instance reprFn_Attr : Repr fn_attr :=
    {| repr := repr_fn_attr |}.


  Definition repr_thread_local_storage (tls : thread_local_storage) : string :=
    match tls with
    | TLS_Localdynamic => "TLS_Localdynamic"
    | TLS_Initialexec => "TLS_Initialexec"
    | TLS_Localexec => "TLS_Localexec"
    end.

  #[global]
   Instance reprThread_Local_Storage : Repr thread_local_storage :=
    {| repr := repr_thread_local_storage |}.

  Program Fixpoint repr_metadata (m : metadata typ) : string :=
    match m with
    | METADATA_Const tv => "(METADATA_Const " ++ repr tv ++ ")"
    | METADATA_Null => "METADATA_Null"
    | METADATA_Nontemporal => "METADATA_Nontemporal"
    | METADATA_Invariant_load => "METADATA_Invariant_load"
    | METADATA_Invariant_group => "METADATA_Invariant_group"
    | METADATA_Nonnull => "METADATA_Nonnull"
    | METADATA_Dereferenceable => "METADATA_Dereferenceable"
    | METADATA_Dereferenceable_or_null => "METADATA_Dereferenceable_or_null"
    | METADATA_Align => "METADATA_Align"
    | METADATA_Noundef => "METADATA_Noundef"
    | METADATA_Id id => "(METADATA_Id " ++ repr id ++ ")"
    | METADATA_String str => "(METADATA_String " ++ repr str ++ ")"
    | METADATA_Named strs => "(METADATA_Named " ++ repr strs ++ ")"
    | METADATA_Node mds => "(METADATA_Node [" ++ (contents id (List.map repr_metadata mds)) ++ "])"
    end.

  #[global]
   Instance reprMetadata : Repr (metadata typ) :=
    {| repr := repr_metadata |}.


  Definition repr_preemption_specifier (p:preemption_specifier) : string :=
    match p with
    | PREEMPTION_Dso_preemptable => "PREEMPTION_Dso_preemptable"
    | PREEMPTION_Dso_local => "PREEMPTION_Dso_local"
    end
  .

  #[global]
   Instance reprPremptionSpecifier : Repr (preemption_specifier) :=
    {| repr := repr_preemption_specifier |}.


  Definition repr_unnamed_addr (u:unnamed_addr) : string :=
    match u with
    | Unnamed_addr => "Unnamed_addr"
    | Local_Unnamed_addr => "Local_Unnamed_addr"
    end.

  #[global]
   Instance reprUnnamedAddr : Repr (unnamed_addr) :=
    {| repr := repr_unnamed_addr |}.

  Definition repr_tailcall (t:tailcall) : string :=
    match t with
    | Tail => "Tail"
    | Musttail => "Musttail"
    | Notail => "Notail"
    end.

  #[global]
   Instance reprTailcall : Repr tailcall :=
    {| repr := show_tailcall |}.

  Definition repr_annotation (a : annotation typ) : string :=
    match a with
    | ANN_linkage l => "ANN_linkage " ++ (repr l)
    | ANN_preemption_specifier p => "ANN_preemption_specifier " ++ (repr p)
    | ANN_visibility v => "ANN_visibility " ++ (repr v)
    | ANN_dll_storage d => "ANN_dll_storage " ++ (repr d)
    | ANN_thread_local_storage t => "ANN_thread_local_storage " ++ (repr t)
    | ANN_unnamed_addr u => "ANN_unnamed_addr " ++ (repr u)
    | ANN_addrspace n => "ANN_addrspace " ++ (repr n)
    | ANN_section s => "ANN_section " ++ (repr s)
    | ANN_partition s => "ANN_partition " ++ (repr s)
    | ANN_comdat l => "ANN_comdat " ++ (repr l)
    | ANN_align n => "ANN_align " ++ (repr n)
    | ANN_no_sanitize => "ANN_no_sanitize"
    | ANN_no_sanitize_address => "ANN_no_sanitize_address"
    | ANN_no_sanitize_hwaddress => "ANN_no_sanitize_hwaddress"
    | ANN_sanitize_address_dyninit => "ANN_sanitize_address_dyninit"
    | ANN_metadata m => "ANN_metadata " ++ (repr m)
    | ANN_cconv c => "ANN_cconv " ++ (repr c)
    | ANN_gc s => "ANN_gc " ++ (repr s)
    | ANN_prefix t => "ANN_prefix " ++ (repr t)
    | ANN_prologue t => "ANN_prologue " ++ (repr t)
    | ANN_personality t => "ANN_personality " ++ (repr t)
    | ANN_inalloca => "ANN_inalloca"
    | ANN_num_elements t => "ANN_num_elements " ++ (repr t)
    | ANN_volatile => "ANN_volatile"
    | ANN_tail t => "ANN_tail " ++ (repr t)
    | ANN_fast_math_flag f => "ANN_fast_math_flag " ++ (repr f)
    | ANN_ret_attribute r => "ANN_ret_attribute " ++ (repr r)
    | ANN_fun_attribute f => "ANN_fun_attribute " ++ (repr f)
    end.

  #[global]
   Instance reprAnnotation : Repr (annotation typ) :=
    {| repr := repr_annotation |}.

  Definition repr_ordering (ord : ordering) : string
    := match ord with
       | Unordered => "Unordered"
       | Monotonic => "Monotonic"
       | Acquire => "Acquire"
       | Release => "Release"
       | Acq_rel => "Acq_rel"
       | Seq_cst => "Seq_cst"
       end.

  #[global]
   Instance reprOrdering : Repr ordering :=
    {| repr := repr_ordering |}.

  Definition repr_atomic_rmw_operation (op : atomic_rmw_operation) :=
    match op with
    | Axchg => "Axchg"
    | Aadd => "Aadd"
    | Asub => "Asub"
    | Aand => "Aand"
    | Anand => "Anand"
    | Aor => "Aor"
    | Axor => "Axor"
    | Amax => "Amax"
    | Amin => "Amin"
    | Aumax => "Aumax"
    | Aumin => "Aumin"
    | Afadd => "Afadd"
    | Afsub => "Afsub"
    end.

  #[global]
   Instance reprAtomicRMWOperation : Repr atomic_rmw_operation :=
    {| repr := repr_atomic_rmw_operation |}.

  Definition repr_atomicrmw (rmw : atomicrmw typ) : string
    := match rmw with
       | mk_atomicrmw a_volatile a_operation a_ptr a_val a_syncscope a_ordering a_align a_type =>
           "(mk_atomicrmw " ++ repr a_volatile ++ " " ++ repr a_operation ++ " " ++
             repr a_ptr ++ " " ++ repr a_val ++ " " ++ repr a_syncscope ++ " " ++
             repr a_ordering ++ " " ++ repr a_align ++ " " ++ repr a_type ++ ")"
       end.

  #[global]
   Instance reprAtomicRMW : Repr (atomicrmw typ) :=
    {| repr := repr_atomicrmw |}.

  Definition repr_cmpxchg (cmp : cmpxchg typ) : string
    := match cmp with
       | mk_cmpxchg c_weak c_volatile c_ptr c_cmp c_cmp_type c_new c_syncscope c_success_ordering
           c_failure_ordering c_align =>
           "(mk_cmpxchg " ++ repr c_weak ++ " " ++ repr c_volatile ++ " " ++ repr c_ptr ++ " " ++ repr c_cmp ++ " " ++ repr c_cmp_type ++ " " ++ repr c_new ++ " " ++ repr c_syncscope ++ " " ++ repr c_success_ordering
           ++ " " ++ repr c_failure_ordering ++ " " ++ repr c_align ++ ")"
       end.

  #[global]
   Instance reprCmpxchg : Repr (cmpxchg typ) :=
    {| repr := repr_cmpxchg |}.

  Definition repr_instr (i : instr typ) : string
    := match i with
       | INSTR_Comment s => "(INSTR_Comment " ++ s ++ ")"
       | INSTR_Op e => "(INSTR_Op " ++ repr e ++ ")"
       | INSTR_Call e params annotations =>
           "(INSTR_Call " ++ repr e ++ " " ++ repr params ++ " " ++ repr annotations ++ ")"
       | INSTR_Alloca t anns =>
         "(INSTR_Alloca " ++ repr t ++ " " ++ repr anns ++ ")"
       | INSTR_Load t ptr anns =>
         "(INSTR_Load " ++ repr t ++ " " ++ repr ptr ++ " " ++ repr anns ++ ")"
       | INSTR_Store tval ptr anns =>
         "(INSTR_Store " ++ repr tval ++ " " ++ repr ptr ++ " " ++ repr anns ++ ")"
       | INSTR_Fence str ord =>
           "(INSTR_Fence " ++ show str ++ " " ++ repr ord ++ ")"
       | INSTR_AtomicCmpXchg cmpx =>
           "(INSTR_AtomicCmpXchg " ++ repr cmpx ++ ")"
       | INSTR_AtomicRMW rmw =>
           "(INSTR_AtomicRMW " ++ repr rmw ++ ")"
       | INSTR_VAArg e t =>
           "(INSTR_VAArg " ++ repr e ++ " " ++ repr t ++ ")"
       | INSTR_LandingPad =>
           "INSTR_LandingPad"
       end.

  #[global]
   Instance reprInstr : Repr (instr typ)
    := {| repr := repr_instr |}.

  #[global]
   Instance reprInstrId : Repr instr_id
    := {| repr i :=
            match i with
            | IId raw => ("(IId " ++ repr raw ++ ")")%string
            | IVoid n => ("(IVoid " ++ repr n ++ ")")%string
            end
       |}.

  #[global]
  Instance reprTintLiteral : Repr tint_literal 
    := {| repr tl := 
          match tl with 
            |  TInt_Literal sz x => 
                ("(TInt_Literal " ++ repr sz ++ " " ++ repr x ++ ")")%string
          end
       |}.

  Definition repr_terminator (t : terminator typ) : string
    := match t with
       | TERM_Ret v => "(TERM_Ret " ++ repr v ++ ")"
       | TERM_Ret_void => "TERM_Ret_void"
       | TERM_Br te b1 b2 =>
         "(TERM_Br " ++ repr te ++ " " ++ repr b1 ++ " " ++ repr b2 ++ ")"
       | TERM_Br_1 b => "(TERM_Br_1 " ++ repr b ++ ")"
       | TERM_Switch v dest brs  => 
          "(TERM_Switch " ++ repr v ++ " " ++ repr dest ++ repr brs ++ ")"
      | TERM_IndirectBr v brs  => 
          "(TERM_IndirectBr " ++ repr v ++ " " ++ repr brs ++ ")" 
      | TERM_Resume v  => "(TERM_Resume " ++ repr v ++ ")"
      | TERM_Invoke fnptrval args to_label unwind_label  =>
          "(TERM_Invoke " ++ repr fnptrval ++ " " ++ repr args 
          ++ " " ++ repr to_label ++ " " ++ repr unwind_label ++ ")"
      | TERM_Unreachable => "TERM_Unreachable"
       end.

  #[global]
   Instance reprTerminator : Repr (terminator typ)
    := {| repr := repr_terminator |}.

  Definition repr_phi (p : phi typ) : string
    := match p with
       | Phi t args =>
         "(Phi " ++ repr t ++ repr args ++ ")"
       end.

  #[global]
   Instance reprPhi : Repr (phi typ)
    := {| repr := repr_phi
       |}.

  Definition repr_block (b : block typ) : string
    :=
      match b with
      | mk_block blk_id blk_phis blk_code blk_term blk_comments =>
        "(mk_block " ++ repr blk_id ++ " " ++ repr blk_phis ++ " " ++ repr blk_code ++ " " ++ repr blk_term ++ " " ++ repr blk_comments ++ ")"
      end.

  #[global]
   Instance reprBlock: Repr (block typ) :=
    {|
    repr := repr_block
    |}.


  Definition repr_declaration (dec : declaration typ) : string
    := match dec with
       | mk_declaration dc_name dc_type dc_param_attrs dc_attrs dc_annotations =>
         "(mk_declaration " ++ repr dc_name ++ " "
                            ++ repr dc_type ++ " "
                            ++ repr dc_param_attrs ++ " "
                            ++ repr dc_attrs ++ " "
                            ++ repr dc_annotations ++ ")"

       end.

  #[global]
   Instance reprDeclaration : Repr (declaration typ) :=
    {| repr := repr_declaration |}.

  Definition repr_definition (defn : definition typ (block typ * list (block typ))) : string
    :=
      match defn with
      | mk_definition df_prototype df_args df_instrs =>
        "(mk_definition _ " ++ repr df_prototype ++ " "
                            ++ repr df_args ++ " "
                            ++ repr df_instrs ++ ")"
      end.

  #[global]
   Instance reprDefinition: Repr (definition typ (block typ * list (block typ))) :=
    {| repr := repr_definition |}.

  Definition repr_global (g : global typ) : string :=
    match g with
    | mk_global g_ident g_typ g_constant g_exp g_externally_initialized g_annotations =>
      "(mk_global " ++ repr g_ident ++ " "
                    ++ repr g_typ ++ " "
                    ++ repr g_constant ++ " "
                    ++ repr g_exp ++ " "
                    ++ repr g_externally_initialized ++ " "
                    ++ repr g_annotations
                    ++ ")"
    end.

  #[global]
   Instance reprGlobal : Repr (global typ) :=
    {| repr := repr_global |}.


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

  #[global]
   Instance reprTLE: Repr (toplevel_entity typ (block typ * list (block typ))) :=
    {| repr := repr_tle |}.

End ReprInstances.
