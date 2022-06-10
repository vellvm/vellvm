(** 
    Show instances for Vellvm. These serialize Vellvm ASTs into the
    standard format for .ll files. The result of show on a Vellvm
    program should give you a string that can be read by clang.
 *)

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Eqv.

From Vellvm Require Import LLVMAst Util AstLib Syntax.CFG DynamicTypes.

Require Import Integers Floats.

Require Import List.

Import ListNotations.
Import MonadNotation.

From Coq Require Import
     ZArith List String Lia Bool.Bool Hexadecimal Numbers.HexadecimalString Numbers.HexadecimalZ.

From QuickChick Require Import Show.
(* Import QcDefaultNotation. Open Scope qc_scope. *)
Set Warnings "-extraction-opaque-accessed,-extraction".

(*  ------------------------------------------------------------------------- *)
(* SAZ: this function was gotten from QuickChick Test.v, but really doesn't belong there. 
   TODO: Move somewhere saner
*)
Fixpoint concatStr (l : list string) : string :=
  match l with
    | nil => ""
    | (h :: t) => h ++ concatStr t
  end.
(*  ------------------------------------------------------------------------- *)


Section ShowInstances.
Local Open Scope string.


  Context {T : Set}.
  Context `{Show T}.
  
  Definition show_raw_id (rid : raw_id) : string
    := match rid with
       | Name s => s
       | Anon i => show i
       | Raw i  => show i
       end.
  
  Global Instance showRawId : Show raw_id
    := {| show := show_raw_id |}.

  Definition show_ident (i : ident) : string
    := match i with
       | ID_Global r => "@" ++ show_raw_id r
       | ID_Local r  => "%" ++ show_raw_id r
       end.

  Global Instance showIdent : Show ident
    := {| show := show_ident |}.

Fixpoint show_typ (t : typ) : string :=
    match t with
    | TYPE_I sz                 => "i" ++ show sz
    | TYPE_IPTR                 => "iptr"
    | TYPE_Pointer t            => show_typ t ++ "*"
    | TYPE_Void                 => "void"
    | TYPE_Half                 => "half"
    | TYPE_Float                => "float"
    | TYPE_Double               => "double"
    | TYPE_X86_fp80             => "x86_fp80"
    | TYPE_Fp128                => "fp128"
    | TYPE_Ppc_fp128            => "ppc_fp128"
    | TYPE_Metadata             => "metadata"
    | TYPE_X86_mmx              => "x86_mmx"
    | TYPE_Array sz t           => "[" ++ show sz ++ " x " ++ show_typ t ++ "]"
    | TYPE_Function ret args    => show_typ ret ++ " (" ++ concat ", " (map show_typ args) ++ ")"
    | TYPE_Struct fields        => "{" ++ concat ", " (map show_typ fields) ++ "}"
    | TYPE_Packed_struct fields => "<{" ++ concat ", " (map show_typ fields) ++ "}>"
    | TYPE_Opaque               => "opaque"
    | TYPE_Vector sz t          => "<" ++ show sz ++ " x " ++ show_typ t ++ ">"
    | TYPE_Identified id        => show id
    end.

  Global Instance showTyp:  Show typ :=
    {|
    show := show_typ
    |}.

  Definition show_dtyp (t : dtyp) : string
    := match t with
    | DTYPE_I sz                 => "Integer" ++ (show sz)
    | DTYPE_IPTR                 => "iptr"
    | DTYPE_Pointer              => "Pointer"
    | DTYPE_Void                 => "Void"
    | DTYPE_Half                 => "Half"
    | DTYPE_Float                => "Float"
    | DTYPE_Double               => "Double"
    | DTYPE_X86_fp80             => "x86 fp80"
    | DTYPE_Fp128                => "Fp128"
    | DTYPE_Ppc_fp128            => "Ppc_fp128"
    | DTYPE_Metadata             => "Metadata"
    | DTYPE_X86_mmx              => "X86_mmx"
    | DTYPE_Array sz t           => "Array"
    | DTYPE_Struct fields        => "Struct"
    | DTYPE_Packed_struct fields => "Packed struct"
    | DTYPE_Opaque               => "Opaque"
    | DTYPE_Vector sz t          => "Vector"
    end.

  Definition show_linkage (l : linkage) : string :=
    match l with 
    | LINKAGE_Private => "private"
    | LINKAGE_Internal => "internal"
    | LINKAGE_Available_externally => "available_externally"
    | LINKAGE_Linkonce => "linkonce"
    | LINKAGE_Weak => "weak"
    | LINKAGE_Common => "common"
    | LINKAGE_Appending => "appending"
    | LINKAGE_Linkonce_odr => "linkonce_odr"
    | LINKAGE_Weak_odr => "weak_odr"
    | LINKAGE_External => "external"
    | LINKAGE_Extern_weak => "extern_weak"                          
    end.

  Global Instance showLinkage (l : linkage) : Show linkage
    := {| show := show_linkage |}. 
    

  Definition show_dll_storage (d : dll_storage) : string :=
    match d with
    | DLLSTORAGE_Dllimport => "dllimport"
    | DLLSTORAGE_Dllexport => "dllexport"
    end.

  Global Instance showDllStorage (d : dll_storage) : Show dll_storage
    := {| show := show_dll_storage |}.

  Definition show_visibility (v : visibility) : string :=
    match v with
    | VISIBILITY_Default => "default"
    | VISIBILITY_Hidden => "hidden"
    | VISIBILITY_Protected => "protected"
    end.

  Global Instance showVisibility (v : visibility) : Show visibility
    := {| show := show_visibility |}.
    
  
  Definition show_cconv (c : cconv) : string :=
    match c with
    | CC_Ccc => "ccc"
    | CC_Fastcc => "fastcc"
    | CC_Coldcc => "coldcc"
    | CC_Cc cc => "cc" ++ show cc 
    | CC_Webkit_jscc => "webkit_jscc"
    | CC_Anyregcc => "anyregcc"
    | CC_Preserve_mostcc => "preserve_mostcc"
    | CC_Preserve_allcc => "preserve_allcc"
    | CC_Cxx_fast_tlscc => "cxx_fast_tlscc"
    | CC_Tailcc => "tailcc"
    | CC_Swiftcc => "swiftcc" 
    | CC_Swifttailcc => "swifttailcc"
    | CC_cfguard_checkcc => "cfguard_checkcc"
    end.

  Global Instance showCConv : Show cconv 
    := {| show := show_cconv |}.
  
                   
  Definition show_param_attr (p : param_attr) : string :=
    match p with
    | PARAMATTR_Zeroext => "zeroext"
    | PARAMATTR_Signext => "signext"
    | PARAMATTR_Inreg => "inreg"
    | PARAMATTR_Byval t => "byval(" ++ show t ++ ")"
    | PARAMATTR_Byref t => "byref(" ++ show t ++ ")"
    | PARAMATTR_Preallocated t => "preallocated(" ++ show t ++ ")"                              
    | PARAMATTR_Inalloca t => "inalloca(" ++ show t ++ ")"                               
    | PARAMATTR_Sret t => "sret(" ++ show t ++ ")"
    | PARAMATTR_Elementtype t => "elementtype(" ++ show t ++ ")"                               
    | PARAMATTR_Align a => "align(" ++ show a ++ ")"
    | PARAMATTR_Noalias => "noalias" 
    | PARAMATTR_Nocapture => "nocapture"
    | PARAMATTR_Readonly => "readonly"                          
    | PARAMATTR_Nofree => "nofree"                           
    | PARAMATTR_Nest => "nest"
    | PARAMATTR_Returned => "returned"
    | PARAMATTR_Nonnull => "nonnull"
    | PARAMATTR_Dereferenceable a => "dereferenceable(" ++ show a ++ ")"
    | PARAMATTR_Dereferenceable_or_null a => "dereferenceable_or_null(" ++ show a ++ ")"
    | PARAMATTR_Swiftself => "swiftself"
    | PARAMATTR_Swiftasync => "swiftasync"
    | PARAMATTR_Swifterror => "swifterror"
    | PARAMATTR_Immarg => "immarg"
    | PARAMATTR_Noundef => "noundef"
    | PARAMATTR_Alignstack a => "alignstack(" ++ show a ++ ")"                          
    | PARAMATTR_Allocalign => "allocalign"
    | PARAMATTR_Allocptr => "allocptr" 
    end.

    Global Instance showParamAttr : Show param_attr
    := { show := show_param_attr }.

    (* unimplemented: frame-pointer patchable-function, key_value *) 
   Definition show_fn_attr (f : fn_attr) : string :=
    match f with 
    | FNATTR_Alignstack a => "alignstack(" ++ show a ++ ")"
    | FNATTR_Alloc_family fam => """alloc-family""=" ++ """" ++ show fam ++ """"
    | FNATTR_Allockind kind => "allockind(" ++ """" ++ show kind ++ """" ++ ")"
    | FNATTR_Allocsize a1 a2 =>
       match a2 with
       | None => "allocsize(" ++ show a1 ++ ")"
       | Some a => "allocsize(" ++ show a1 ++ "," ++ show a ++ ")"
       end
    | FNATTR_Alwaysinline => "alwaysinline"
    | FNATTR_Builtin => "builtin"
    | FNATTR_Cold => "cold"
    | FNATTR_Convergent => "convergent"
    | FNATTR_Disable_sanitizer_instrumentation => "disable_sanitizer_instrumentation"
    | FNATTR_Dontcall_error => """dontcall-error"""
    | FNATTR_Dontcall_warn => """dontcall-warn"""
    | FNATTR_Frame_pointer => "unimplemented: frame-pointer"
    | FNATTR_Hot => "hot"
    | FNATTR_Inaccessiblememonly => "inaccessiblememonly"
    | FNATTR_Inaccessiblemem_or_argmemonly => "inaccessiblemem_or_argmemonly"
    | FNATTR_Inlinehint => "inlinehint"
    | FNATTR_Jumptable => "jumptable"
    | FNATTR_Minsize => "minsize"
    | FNATTR_Naked => "naked"
    | FNATTR_No_inline_line_tables => """no-inline-line-tables"""
    | FNATTR_No_jump_tables => "no-jump-tables"
    | FNATTR_Nobuiltin => "nobuiltin"
    | FNATTR_Noduplicate => "noduplicate"
    | FNATTR_Nofree => "nofree"
    | FNATTR_Noimplicitfloat => "noimplicitfloat"
    | FNATTR_Noinline => "noinline"
    | FNATTR_Nomerge => "nomerge"
    | FNATTR_Nonlazybind => "nonlazybind"
    | FNATTR_Noprofile => "noprofile"
    | FNATTR_Noredzone => "noredzone"
    | FNATTR_Indirect_tls_seg_refs => "indirect-tls-seg-refs"
    | FNATTR_Noreturn => "noreturn"
    | FNATTR_Norecurse => "norecurse"
    | FNATTR_Willreturn => "willreturn"
    | FNATTR_Nosync => "nosync"
    | FNATTR_Nounwind => "nounwind"
    | FNATTR_Nosanitize_bounds => "nosanitize_bounds"
    | FNATTR_Nosanitize_coverage => "nosanitize_coverage"
    | FNATTR_Null_pointer_is_valid => "null_pointer_is_valid"
    | FNATTR_Optforfuzzing => "optforfuzzing"
    | FNATTR_Optnone => "optnone"
    | FNATTR_Optsize => "optsize"
    | FNATTR_Patchable_function => "unimplemented: patchable-function"
    | FNATTR_Probe_stack => """probe-stack"""
    | FNATTR_Readnone => "readnone"
    | FNATTR_Readonly => "readonly"
    | FNATTR_Stack_probe_size => """stack-probe-size"""
    | FNATTR_No_stack_arg_probe => """no-stack-arg-probe"""
    | FNATTR_Writeonly => "writeonly"
    | FNATTR_Argmemonly => "argmemonly"
    | FNATTR_Returns_twice => "returns_twice"                          
    | FNATTR_Safestack => "safestack" 
    | FNATTR_Sanitize_address => "sanitize_address" 
    | FNATTR_Sanitize_memory => "sanitize_memory" 
    | FNATTR_Sanitize_thread => "sanitize_thread" 
    | FNATTR_Sanitize_hwaddress => "sanitize_hwaddress" 
    | FNATTR_Sanitize_memtag => "sanitize_memtag" 
    | FNATTR_Speculative_load_hardening => "speculative_load_hardening"    
    | FNATTR_Speculatable => "speculatable" 
    | FNATTR_Ssp => "ssp" 
    | FNATTR_Sspstrong => "sspstrong" 
    | FNATTR_Sspreq => "sspreq" 
    | FNATTR_Strictfp => "strictfp"
    | FNATTR_Denormal_fp_math s1 s2 =>
        match s2 with
        | None => """" ++ show s1 ++  """"
        | Some s => """" ++ show s1 ++ "," ++ show s2 ++ """"
        end    
    | FNATTR_Denormal_fp_math_32 s1 s2 =>
        match s2 with
        | None => """" ++ show s1 ++  """"
        | Some s => """" ++ show s1 ++ "," ++ show s2 ++ """"
        end     
    | FNATTR_Thunk => """thunk"""
    | FNATTR_Tls_load_hoist => """tls-load-hoist"""                   
    | FNATTR_Uwtable sync  => if sync then "uwtable(sync)" else "uwtable" 
    | FNATTR_Nocf_check => "nocf_check" 
    | FNATTR_Shadowcallstack => "shadowcallstack" 
    | FNATTR_Mustprogress => "mustprogeress"
    | FNATTR_Warn_stack_size th  => """warn-stack-size""=" ++ """" ++ show th ++ """"
    | FNATTR_vscale_range min max  =>
        match max with
        | None => "vscale_range(" ++ show min ++ ")"
        | Some m => "vscale_range(" ++ show min ++ "," ++ show m ++ ")"
        end                             
    | FNATTR_Min_legal_vector_width size => """min-legal-vector-width""=" ++ """"
                                                       ++ show size ++ """" 
    | FNATTR_String s => """" ++ show s ++ """"  (* "no-see" *)
    | FNATTR_Key_value kv => """" ++ fst kv ++ """=" ++ """" ++ snd kv ++ """" (* "unsafe-fp-math"="false" *)
    | FNATTR_Attr_grp g => "attr_grip" ++ show g
    end.

  Global Instance showFnAttr : Show fn_attr
    := {| show := show_fn_attr |}.

  Definition show_thread_local_storage (tls : thread_local_storage) : string :=
    match tls with
    | TLS_Localdynamic => "localdynamic"
    | TLS_Initialexec => "initialexec"
    | TLS_Localexec => "localexec" 
    end.

  Global Instance showTLS (tls : thread_local_storage) : Show thread_local_storage
    := {| show := show_thread_local_storage |}. 
    

    
   Definition show_icmp (cmp : icmp) : string
    := match cmp with
       | Eq  => "eq"
       | Ne  => "ne"
       | Ugt => "ugt"
       | Uge => "uge"
       | Ult => "ult"
       | Ule => "ule"
       | Sgt => "sgt"
       | Sge => "sge"
       | Slt => "slt"
       | Sle => "sle"
       end.

   Global Instance showICmp : Show icmp
     := {| show := show_icmp |}.

   (* Removed f's *) 
   Definition show_fcmp (cmp: fcmp) : string
    := match cmp with 
      |FFalse => "false"
      |FOeq => "oeq"
      |FOgt => "ogt"
      |FOge => "oge"
      |FOlt => "olt"
      |FOle => "ole"
      |FOne => "one"
      |FOrd => "ord"
      |FUno => "uno"
      |FUeq => "ueq"
      |FUgt => "ugt"
      |FUge => "uge"
      |FUlt => "ult"
      |FUle => "ule"
      |FUne => "une"
      |FTrue => "true"
    end.

     
  Global Instance showFCmp : Show fcmp 
  := {| show := show_fcmp|}.

  (*How to implement select, freeze, call, va_arg, landingpad, catchpad, cleanuppad*)



  (*These are under binary operations*)
  (*These are also under bitwsie binary operations*)
  (*Should we implement shl, lshr, and ashr?*)
  Definition show_ibinop (iop : ibinop) : string
    := match iop with
       (* TODO print flags *)
       | LLVMAst.Add _ _ => "add"
       | Sub _ _ => "sub"
       | Mul _ _ => "mul"
       | Shl _ _ => "shl"
       | UDiv _  => "udiv"
       | SDiv _  => "sdiv"
       | LShr _  => "lshr"
       | AShr _  => "ashr"
       | URem    => "urem"
       | SRem    => "srem"
       | And     => "and"
       | Or      => "or"
       | Xor     => "xor"
       end.

   
  Global Instance showIBinop : Show ibinop
    := {| show := show_ibinop |}.

   (*These are under binary operations*)
  Definition show_fbinop (fop : fbinop) : string
    := match fop with
       | FAdd => "fadd"
       | FSub => "fsub"
       | FMul => "fmul"
       | FDiv => "fdiv"
       | FRem => "frem"
       end.

  Global Instance showFBinop : Show fbinop
    := {| show := show_fbinop |}.



  Definition double_to_hex_string (f : float) : string
    := "0x" ++ NilEmpty.string_of_uint (N.to_hex_uint (Z.to_N (Int64.unsigned (Float.to_bits f)))).

  Definition float_to_hex_string (f : float32) : string
    := double_to_hex_string (Float32.to_double f).

  Global Instance showFloat : Show float
    := {| show := double_to_hex_string |}.

  Global Instance showFloat32 : Show float32
    := {| show := float_to_hex_string |}.

  Definition show_int (x : Integers.Int.int) : string
    := show (Int.unsigned x).
  
  Global Instance Show_Int : Show Integers.Int.int
  := {| show := show_int|}.

  Definition show_fast_math (fm : fast_math) : string
    := match fm with
       | Nnan => "nnan"
       | Ninf => "ninf"
       | Nsz => "nsz"
       | Arcp => "arcp"
       | Fast => "fast"
       end.

  Global Instance showFastMatch : Show fast_math
    := {| show := show_fast_math |}.

  (*These are Constant Expressions*)
  Definition show_conversion_type (ct : conversion_type) : string
    := match ct with
       | Trunc => "trunc"
       | Zext => "zext"
       | Sext => "sext"
       | Fptrunc => "fptrunc"
       | Fpext => "fpext"
       | Uitofp => "uitofp"
       | Sitofp => "sitofp"
       | Fptoui => "fptoui"
       | Fptosi => "fptosi"
       | Inttoptr => "inttoptr"
       | Ptrtoint => "ptrtoint"
       | Bitcast => "bitcast"
       | Addrspacecast => "addrspacecast"
                            (*Do the following ones take in arguments???*)
       end.
  
  Global Instance ShowConversionType : Show conversion_type
    := {| show := show_conversion_type |}.
  
  Fixpoint show_exp (v : exp T) :=
      match v with
      | EXP_Ident id => show id
      | EXP_Integer x => show x
      | EXP_Float f => show f
      | EXP_Double f => show f
      | EXP_Hex f => double_to_hex_string f
      | EXP_Bool b => show b
      | EXP_Null => "null"
      | EXP_Zero_initializer => "zero initializer"
      (* see notes on cstring on LLVMAst.v *)                         
      | EXP_Cstring elts => "unimplemented"      
      | EXP_Undef => "undef"
      | EXP_Struct fields => "{"  ++ concat ", " (map (fun '(ty,ex) => show ty ++ " " ++ show_exp ex) fields) ++ "}"
      | EXP_Packed_struct fields => "<{"  ++ concat ", " (map (fun '(ty,ex) => show ty ++ " " ++ show_exp ex) fields) ++ "}>"
      | EXP_Array elts => "["  ++ concat ", " (map (fun '(ty,ex) => show ty ++ " " ++ show_exp ex) elts) ++ "]"
      | EXP_Vector elts => "<"  ++ concat ", " (map (fun '(ty,ex) => show ty ++ " " ++ show_exp ex) elts) ++ ">"
      | OP_IBinop iop t v1 v2 =>
          show iop ++ " " ++ show t ++ " " ++ show_exp v1 ++ ", " ++ show_exp v2
      | OP_ICmp cmp t v1 v2 =>
          "icmp " ++ show cmp ++ " " ++ show t ++ " " ++ show_exp v1 ++ ", " ++ show_exp v2
      | OP_FBinop fop fmath t v1 v2 =>
          let fmath_string :=
            match fmath with
            | nil => " "
            | _ =>  " " ++ concat " " (map (fun x => show x) fmath) ++  " "
            end in              
         show fop ++ fmath_string ++ show t ++ " " ++ show_exp v1 ++ ", " ++ show_exp v2
      | OP_FCmp cmp t v1 v2 =>
          "fcmp " ++ show cmp ++ " " ++ show t ++ " " ++ show_exp v1 ++ ", " ++ show_exp v2
      | OP_Conversion conv t_from v t_to => show conv ++ " " ++ show t_from ++ " " ++ show_exp v ++ " to " ++ show t_to
      | OP_GetElementPtr t ptrval idxs =>
      let (tptr, exp) := ptrval in
      "getelementptr " ++ show t ++ ", " ++ show tptr ++ " " ++ show_exp exp ++ fold_left (fun str '(ty, ex) => ", " ++ show ty ++ " "++ show_exp ex ++ str) idxs ""
      | OP_ExtractElement vec idx =>
      let (tptr, exp) := vec in 
      let (tidx, iexp) := idx in
      "extractelement " ++ show tptr ++ " " ++ show_exp exp ++ ", " ++ show tidx ++ " " ++ show_exp iexp
      | OP_InsertElement vec elt idx =>
      let (tptr, exp) := vec in
      let (telt, eexp) := elt in
      let (tidx, iexp) := idx in
      "insertelement " ++ show tptr ++ " " ++ show_exp exp ++ ", " ++ show telt ++ " " ++ show_exp eexp ++ ", " ++ show tidx ++ " " ++ show_exp iexp
      | OP_ShuffleVector vec1 vec2 idxmask =>
          let (type1, expression1) := vec1 in
          let (type2, expression2) := vec2 in
          let (type3, expression3) := idxmask in
          "shufflevector " ++ show type1 ++ show_exp expression1  ++ ", " ++ show type2 ++ show_exp expression2 ++ ", " ++ show type3 ++ show_exp expression3
                           (* This one, extractValue *)
      | OP_ExtractValue vec idxs =>
      let (tptr, exp) := vec in
      "extractvalue " ++ show tptr ++ " " ++ show_exp exp ++ ", " ++ concat ", " (map (fun x => show x) idxs)
      | OP_InsertValue vec elt idxs =>
      let (tptr, exp) := vec in
      let (telt, eexp) := elt in 
      "insertvalue " ++ show tptr ++ " " ++ show_exp exp ++ ", " ++ show telt ++ " " ++ show_exp eexp ++ ", " ++ concat ", " (map (fun x => show x) idxs)
      | OP_Select (tc, cnd) (t1, v1) (t2, v2) =>
          "select " ++ show tc ++ " " ++ show_exp cnd ++ ", " ++ show t1 ++ " " ++ show_exp v1  ++ ", " ++ show t2 ++ " " ++ show_exp v2
      | OP_Freeze (ty, ex) => "freeze " ++ show ty ++ " " ++ show_exp ex
      end.

  
  Global Instance showExp : Show (exp T)
    := {| show := show_exp |}.

  Global Instance showTExp : Show (texp T)
    := {| show te :=
            match te with
            | (t, e) => show t ++ " " ++ show e
            end
       |}.

  Definition show_phi_block (p : block_id * exp T) : string :=
    let '(bid, e) := p in
    "[ " ++ show e ++ ", " ++ "%" ++ show bid ++ " ]".

  Definition intersperse (sep : string) (l : list string) : string
    := fold_left (fun acc s => if StringOrdFacts.eqb "" acc then s else s ++ sep ++ acc) l "".

  Global Instance showPhi : Show (phi T)
    := {| show p :=
            let '(Phi t phis) := p in
            "phi " ++ show t ++ " " ++ intersperse ", " (map show_phi_block phis)
       |}.


  Definition show_opt_prefix {A} `{Show A} (prefix : string) (ma : option A) : string
    := match ma with
       | None   => ""
       | Some a => prefix ++ show a
       end.

  Definition show_instr (i : instr T) : string
    := match i with
       | INSTR_Comment s => "; " ++ s
       | INSTR_Op e => show e
       | INSTR_Load vol t ptr align =>
         "load " ++ show t ++ ", " ++ show ptr ++ show_opt_prefix ", align " align
       | INSTR_Store vol tval ptr align =>
         "store " ++ (if vol then "volatile " else "") ++ show tval ++ ", " ++ show ptr ++ show_opt_prefix ", align " align
       | INSTR_Alloca t nb align =>
         "alloca " ++ show t ++ show_opt_prefix ", " nb ++ show_opt_prefix ", align " align
       | _ => "show_instr todo"
       end.

  Global Instance showInstr : Show (instr T)
    := {| show := show_instr |}.

  Global Instance showInstrId : Show instr_id
    := {| show i :=
            match i with
            | IId raw => ("%" ++ show raw)%string
            | IVoid n => ("void<" ++ show n ++ ">")%string
            end
       |}.

  Definition show_instr_id (inst : instr_id * instr T) : string
    :=
      let '(iid, i) := inst in
      match iid with
        | IId _ =>
          (show iid ++ " = " ++ show i)%string
        | IVoid n =>
          show i
      end.

  Global Instance showInstrWithId : Show (instr_id * instr T)
    := {| show := show_instr_id |}.

  
  Definition show_tint_literal (t : tint_literal) : string :=
    match t with
    (* typo? *) 
    | TInt_Literal sz x => show sz ++ show x ++ "What is a tint_literal anyway?"
    end.

  Global Instance showTintLiteral : Show tint_literal :=
    {| show := show_tint_literal |}. 

  (* To-do: add new terminators *) 
  Definition show_terminator (t : terminator T) : string
    := match t with
       | TERM_Ret v => "ret " ++ show v
       | TERM_Ret_void => "ret"
       | TERM_Br te b1 b2 =>
         "br " ++ show te ++ ", label %" ++ show b1 ++ ", label %" ++ show b2
       | TERM_Br_1 b => "br label %" ++ show b
       | TERM_Switch v def_dest brs =>
           "switch " ++ show v ++ ", label " ++ show def_dest
             ++ show (map (fun '(x, y) => show x ++ ", label " ++ show y) brs)
       | TERM_IndirectBr v brs => "indirectbr " ++ (fun '(x, y) => show x ++ "*" ++ show y) v
                                                ++ show (map (fun x => "label " ++ show x) brs) 
       | TERM_Resume v => "resume " ++ show v 
       | TERM_Invoke fnptrval args to_label unwind_label => "invoke " ++ show fnptrval
                                                              ++ "(" ++ show args ++ ")"
                                                              ++ "to label " ++ show to_label
                                                              ++ "unwind label " ++ show unwind_label
       | TERM_Unreachable => "unreachable" 
       end.

  Global Instance showTerminator : Show (terminator T)
    := {| show := show_terminator |}.

  Definition show_code (indent : string) (c : code T) : string
    := concatStr (map (fun iid => indent ++ show_instr_id iid ++ newline) c).

  Global Instance showCode : Show (code T)
     := {| show := show_code "    " |}.
  
  Definition show_block (indent : string) (b : block T) : string
    :=
      let phis   := concatStr (map (fun '(l, p) => indent ++ "%" ++ show l ++ " = " ++ show p ++ newline) (blk_phis b)) in
      let code   := show_code indent (blk_code b) in
      let term   := indent ++ show (blk_term b) ++ newline in
      show (blk_id b) ++ ":" ++ newline
           ++ phis
           ++ code
           ++ term.

  Global Instance showBlock: Show (block T) :=
    {|
    show := show_block "    "
    |}.

  Definition show_typ_instr (typ_instr: typ * instr T) : string :=
    let (t, i) := typ_instr in
    "(" ++ (show t) ++ ", " ++ (show i) ++ ")".

  Global Instance showTypInstr: Show (typ * instr T) :=
    {|
    show := show_typ_instr
    |}.
  
  Definition show_arg (arg : local_id * T * list param_attr) : string
    := let '(i, t, parameter_attributes) := arg in
       show t ++ concat " " (map (fun x => show x) (parameter_attributes)) ++ " %" ++ show i.

  Definition show_arg_list (args : list (local_id * T * list param_attr)) : string
    :=
      let arg_str := concat ", " (map show_arg args) in
      concatStr ["("; arg_str; ")"].

  (* TODO: REALLY?!? *)
  Fixpoint zip {X Y Z} (xs : list X) (ys : list Y) (zs : list Z) : list (X * Y *  Z)
    := match xs, ys, zs with
       | [], _, _ => []
       | _, [], _ => []
       | _, _, [] => []    
       | (x::xs), (y::ys), (z::zs) => (x, y, z) :: zip xs ys zs
       end.

   Fixpoint show_metadata (md : metadata T)  : string :=
    match md with
    | METADATA_Const tv => show tv
    | METADATA_Null => "null"
    | METADATA_Id i => "!" ++ show i
    | METADATA_String s => "!" ++ show s   
    | METADATA_Named strs => "!{" ++ show (intersperse " , " (List.map (fun x => "!" ++ x) strs)) ++ "}" 
    | METADATA_Node mds => "!{" ++ show (intersperse " , " (List.map show_metadata mds)) ++ "}" 
    end. 

  Global Instance showMetadata (md : metadata T) : Show (metadata T) :=
    {| show := show_metadata |}. 

  End ShowInstances. 

  Definition show_definition (defn : definition typ (block typ * list (block typ))) : string
    :=
      let name  := defn.(df_prototype).(dc_name) in
      let ftype := defn.(df_prototype).(dc_type) in
      let '(return_attributes, argument_attributes):= defn.(df_prototype).(dc_param_attrs) in
      
      match ftype with
      (*Stand for return type and arguments type*)
      | TYPE_Function ret_t args_t =>
      (* It's being zipped with name of arg and then type bc of how show_arg is defined *)
        let args := zip defn.(df_args) args_t argument_attributes in
          (* What is happening here? *)
                (* Are we matching the instructions field of definition?
                   Is that why we do "df_instrs defn"? *)
                (* Is df_instrs a list or a tuple? Or is bs a list and b some element?*)
                (* Is newline literally just writing a new line? *)
        let blocks :=
          match df_instrs defn with
            (* We are doing concat with newline as the separator bc this represent code in the body, which obviously should be separated by lines.  *)
            | (b, bs) => concat newline (map (show_block "    ") (b::bs))
            end in
       
        let ret_attributes :=  concat " " (map (fun x => show x) (return_attributes)) in
        let the_linkage := defn.(df_prototype).(dc_linkage) in 
        let printable_linkage := match the_linkage with
                                 |None => ""
                                 |Some l => show_linkage l
                                 end in
        let the_visibility := defn.(df_prototype).(dc_visibility) in 
        let printable_visibility := match the_visibility with
                                 |None => ""
                                 |Some v => show_visibility v
                                    end in
        let the_dll_storage := defn.(df_prototype).(dc_dll_storage) in 
        let printable_dll_storage := match the_dll_storage with
                                 |None => ""
                                 |Some d => show_dll_storage d
                                     end in
        let the_cconv := defn.(df_prototype).(dc_cconv) in 
        let printable_cconv := match the_cconv with
                                 |None => ""
                                 |Some c => show_cconv c
                               end in
        let the_section := defn.(df_prototype).(dc_section) in 
        let printable_section := match the_section with
                                 |None => ""
                                 |Some c => show c
                                 end in
        let the_align := defn.(df_prototype).(dc_align) in 
        let printable_align := match the_align with
                                 |None => ""
                                 |Some c => show c
                               end in
        let the_gc := defn.(df_prototype).(dc_gc) in 
        let printable_gc := match the_gc with
                                 |None => ""
                                 |Some c => show c
                                 end in
        
        concatStr ["define "; printable_linkage; printable_visibility ; printable_dll_storage ;
                   printable_cconv ; ret_attributes; show ret_t; " @"; show name; show_arg_list                   args; printable_section ; printable_align ; printable_gc ; " {"; newline ;
                   blocks;
                   "}";
                   newline]
      | _ => "Invalid type on function: " ++ show name
      end.

  Global Instance showDefinition: Show (definition typ (block typ * list (block typ))) :=
    {| show := show_definition |}.

  Definition show_global (g : global typ) : string :=
    let name  := g.(g_ident) in
    let gtype := g.(g_typ) in
    let the_linkage := g.(g_linkage) in   
    let printable_linkage := match the_linkage with                               
                             |None => ""                                       
                             |Some l => show_linkage l                                          
                             end in
    let the_visibility := g.(g_visibility) in   
    let printable_visibility := match the_visibility with                               
                             |None => ""                                       
                             |Some l => show_visibility l                                       
                                end in
    let the_dll_storage := g.(g_dll_storage) in    
    let printable_dll_storage := match the_dll_storage with                               
                             |None => ""                                       
                             |Some l => show_dll_storage l                                      
                                 end in
    let the_thread_local := g.(g_thread_local) in
    let printable_thread_local := match the_thread_local with                               
                             |None => ""                                       
                             |Some l => show_thread_local_storage l                             
                                  end in
    
    let the_unnamed_addr := g.(g_unnamed_addr) in
    let printable_unnamed_addr := if the_unnamed_addr then "unnamed_addr" else "local_unnamed_addr" in
    let the_addrspace := g.(g_addrspace) in
    let printable_addrspace := match the_addrspace with                               
                             |None => ""                                       
                             |Some x => show x                              
                                 end in
    let the_externally_initialized := g.(g_externally_initialized) in
    (* Based on example in Global Variables section *)
    let printable_externally_initialized := if the_externally_initialized then "external" else "" in
    let global_or_constant := g.(g_constant) in
    let printable_g_or_c := if global_or_constant then "constant" else "global" in
    let printable_section := match g.(g_section) with
                            | None => ""
                            | Some s =>  concatStr[", section ";  show s]
                            end in
    let printable_align :=  match g.(g_align) with
                                | None => ""
                                | Some s => show s
                                end in                                                                      
    concatStr ["@ "; show name ; "=" ; printable_linkage ; printable_visibility ; printable_dll_storage ; printable_thread_local ; printable_unnamed_addr ; printable_addrspace ; printable_externally_initialized ; printable_g_or_c ; show gtype ;  printable_section ; printable_align ].
               
      

  Global Instance showGlobal : Show (global typ) :=
      {| show := show_global |}.
  

  Definition show_declaration (decl: declaration typ) : string :=
   let name := decl.(dc_name) in
   let (ret_attrs, args_attrs) := decl.(dc_param_attrs) in
   match decl.(dc_type) with
    | TYPE_Function ret_t args_t =>
   let link := match decl.(dc_linkage) with
               | None => ""
               | Some l => show_linkage l
               end in
   let vis := match decl.(dc_visibility) with
              | None => ""
              | Some w => show_visibility w
              end in
   let dll := match decl.(dc_dll_storage) with
              | None => ""
              | Some d => show_dll_storage d
              end in
   let cc := match decl.(dc_cconv) with
             | None => ""
             | Some c => show_cconv c
             end in                  
   let sec := match decl.(dc_section) with
              | None => ""
              | Some s => concatStr["section \"; s; "\"]
              end in
   let all := match decl.(dc_align) with
              | None => ""
              | Some a => concatStr["align "; show a]
              end in
   let gc := match decl.(dc_gc) with
             | None => ""
             | Some g => concatStr["gc \"; g; "\"]
             end in                      
   concatStr ["declare "; link; " "; vis; " "; dll; " "; cc; " ";
              show (intersperse " " (List.map show ret_attrs)); 
              show ret_t; " @"; show name; 
              "("; show (intersperse ", " (List.map show (List.combine args_t args_attrs)));
              sec; all; gc] 
   | _ => "Invalid type on function: " ++ show name
   end.                                     

  Global Instance showDeclaration: Show (declaration typ) :=
    {| show := show_declaration |}.


 
    
  Definition show_tle (tle : toplevel_entity typ (block typ * list (block typ))) : string
    := match tle with
         (*Why is show_definition rather than show being used here*)
       | TLE_Definition defn => show defn
       | TLE_Comment msg => ";" ++ show msg
       | TLE_Target tgt => show tgt
       | TLE_Datalayout layout => show layout
       | TLE_Source_filename s => "source_filename = " ++ show s                                      
       | TLE_Declaration decl => show decl                                                        
       | TLE_Global g => show g
       | TLE_Metadata id md => "!" ++ show id ++ show_metadata md                        
       | TLE_Type_decl id t => concatStr ["% " ; show_ident id ;  "= type " ; show t ]
       | TLE_Attribute_group i attrs => concatStr ["attributes #" ; show i ; " = { " ; concat " " (map (fun x => show x) (attrs)) ; " }"  ]              
       end.

  Global Instance showTLE: Show (toplevel_entity typ (block typ * list (block typ))) :=
    {| show := show_tle |}.

  Global Instance showProg : Show (list (toplevel_entity typ (block typ * list (block typ)))) :=
    {| show tles := concat (newline ++ newline) (map show_tle tles) |}.

