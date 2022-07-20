(**
    Show instances for Vellvm. These serialize Vellvm ASTs into the
    standard format for .ll files. The result of show on a Vellvm
    program should give you a string that can be read by clang.
 *)


From Vellvm Require Import LLVMAst Util AstLib Syntax.CFG DynamicTypes.

Require Import Integers Floats.

Require Import List.

Import ListNotations.

From Coq Require Import
     ZArith List String Lia Bool.Bool Hexadecimal Numbers.HexadecimalString Numbers.HexadecimalZ
     Strings.Ascii.
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

  Context {T:Set}.
  Context `{Show T}.


  Definition show_raw_id (rid : raw_id) : string
    := match rid with
       | Name s => s
       | Anon i => show i
       | Raw i  => show i
       end.

  #[global] Instance showRawId : Show raw_id
    := {| show := show_raw_id |}.

  Definition show_ident (i : ident) : string
    := match i with
       | ID_Global r => "@" ++ show_raw_id r
       | ID_Local r  => "%" ++ show_raw_id r
       end.

  #[global] Instance showIdent : Show ident
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
    | TYPE_Function ret args varargs =>
        let varargs_str :=
          if Nat.eqb (List.length args) 0 then
            (if varargs then "..." else "")
          else
            (if varargs then ", ..." else "")
        in
        show_typ ret ++ " (" ++ concat ", " (map show_typ args) ++ varargs_str ++ ")"
    | TYPE_Struct fields        => "{" ++ concat ", " (map show_typ fields) ++ "}"
    | TYPE_Packed_struct fields => "<{" ++ concat ", " (map show_typ fields) ++ "}>"
    | TYPE_Opaque               => "opaque"
    | TYPE_Vector sz t          => "<" ++ show sz ++ " x " ++ show_typ t ++ ">"
    | TYPE_Identified id        => show id
    end.

  #[global] Instance showTyp:  Show typ :=
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
    | LINKAGE_Private => "private "
    | LINKAGE_Internal => "internal "
    | LINKAGE_Available_externally => "available_externally "
    | LINKAGE_Linkonce => "linkonce "
    | LINKAGE_Weak => "weak "
    | LINKAGE_Common => "common "
    | LINKAGE_Appending => "appending "
    | LINKAGE_Linkonce_odr => "linkonce_odr "
    | LINKAGE_Weak_odr => "weak_odr "
    | LINKAGE_External => "external "
    | LINKAGE_Extern_weak => "extern_weak "
    end.

  #[global] Instance showLinkage : Show linkage
    := {| show := show_linkage |}.


  Definition show_dll_storage (d : dll_storage) : string :=
    match d with
    | DLLSTORAGE_Dllimport => "dllimport"
    | DLLSTORAGE_Dllexport => "dllexport"
    end.

  #[global] Instance showDllStorage : Show dll_storage
    := {| show := show_dll_storage |}.

  Definition show_visibility (v : visibility) : string :=
    match v with
    | VISIBILITY_Default => "default"
    | VISIBILITY_Hidden => "hidden"
    | VISIBILITY_Protected => "protected"
    end.

  #[global] Instance showVisibility : Show visibility
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

  #[global] Instance showCConv : Show cconv
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
    | PARAMATTR_Align a => "align " ++ show a
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

  #[global] Instance showParamAttr : Show param_attr
    := { show := show_param_attr }.

  Definition show_fn_attr (f : fn_attr) : string :=
    match f with
    | FNATTR_Alignstack a => "alignstack(" ++ show a ++ ")"
    (* | FNATTR_Alloc_family (fam : string) - FNATTR_KeyValue *)
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
    (* | FNATTR_Dontcall_error - FNATTR_String *)
    (* | FNATTR_Dontcall_warn - FNATTR_String *)
    | FNATTR_Fn_ret_thunk_extern => "fun_ret_thunk_extern"
    (* | FNATTR_Frame_pointer - FNATTR_KeyValue *)
    | FNATTR_Hot => "hot"
    | FNATTR_Inaccessiblememonly => "inaccessiblememonly"
    | FNATTR_Inaccessiblemem_or_argmemonly => "inaccessiblemem_or_argmemonly"
    | FNATTR_Inlinehint => "inlinehint"
    | FNATTR_Jumptable => "jumptable"
    | FNATTR_Minsize => "minsize"
    | FNATTR_Naked => "naked"
    (* | FNATTR_No_inline_line_tables - FNATTR_String *)
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
    (* | FNATTR_Patchable_function - FNATTR_KeyValue *)
    (* | FNATTR_Probe_stack - FNATTR_String *)
    | FNATTR_Readnone => "readnone"
    | FNATTR_Readonly => "readonly"
    (* | FNATTR_Stack_probe_size => - FNATTR_KeyValue *)
    (* | FNATTR_No_stack_arg_probe => -  FNATTR_String *)
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
    (* | FNATTR_Denormal_fp_math s1 s2 - FNATTR_KeyValue *)
    (* | FNATTR_Denormal_fp_math_32 s1 s2 - FNATTR_KeyValue *)
    (* | FNATTR_Thunk => - FNATTR_String *)
    | FNATTR_Tls_load_hoist => """tls-load-hoist"""                   
    | FNATTR_Uwtable so  =>
        match so with
        | None => "uwtable"
        | Some sync => if sync then "uwtable(sync)" else "uwtable(async)"
        end
    | FNATTR_Nocf_check => "nocf_check" 
    | FNATTR_Shadowcallstack => "shadowcallstack" 
    | FNATTR_Mustprogress => "mustprogeress"
    (* | FNATTR_Warn_stack_size th  => - FNATTR_KeyValue *)
    | FNATTR_Vscale_range min max  =>
        match max with
        | None => "vscale_range(" ++ show min ++ ")"
        | Some m => "vscale_range(" ++ show min ++ "," ++ show m ++ ")"
        end                             
    | FNATTR_String s => """" ++ show s ++ """"  (* "no-see" *)
    | FNATTR_Key_value kv => """" ++ fst kv ++ """=" ++ """" ++ snd kv ++ """" (* "unsafe-fp-math"="false" *)
    | FNATTR_Attr_grp g => "#" ++ show g
    end.

  #[global] Instance showFnAttr : Show fn_attr
    := {| show := show_fn_attr |}.

  Definition show_thread_local_storage (tls : thread_local_storage) : string :=
    match tls with
    | TLS_Localdynamic => "localdynamic"
    | TLS_Initialexec => "initialexec"
    | TLS_Localexec => "localexec"
    end.

  #[global] Instance showTLS : Show thread_local_storage
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

  #[global] Instance showICmp : Show icmp
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


  #[global] Instance showFCmp : Show fcmp
    := {| show := show_fcmp|}.

  (*How to implement select, freeze, call, va_arg, landingpad, catchpad, cleanuppad*)

  Definition show_op_nuw_nsw (op : string) (nuw : bool) (nsw : bool) :=
    concatStr
      [ op;
        if nuw then " nuw" else "";
        if nsw then " nsw" else ""
      ].

  (*These are under binary operations*)
  (*These are also under bitwsie binary operations*)
  (*Should we implement shl, lshr, and ashr?*)
  Definition show_ibinop (iop : ibinop) : string
    := match iop with
       | LLVMAst.Add nuw nsw  =>
           show_op_nuw_nsw "add" nuw nsw

       | Sub nuw nsw =>
           show_op_nuw_nsw "sub" nuw nsw

       | Mul nuw nsw =>
           show_op_nuw_nsw "mul" nuw nsw

       | Shl nuw nsw =>
           show_op_nuw_nsw "shl" nuw nsw

       | UDiv exact  => "udiv" ++ if exact then " exact" else ""
       | SDiv exact  => "sdiv" ++ if exact then " exact" else ""
       | LShr exact  => "lshr" ++ if exact then " exact" else ""
       | AShr exact  => "ashr" ++ if exact then " exact" else ""
       | URem    => "urem"
       | SRem    => "srem"
       | And     => "and"
       | Or      => "or"
       | Xor     => "xor"
       end.


  #[global] Instance showIBinop : Show ibinop
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

  #[global] Instance showFBinop : Show fbinop
    := {| show := show_fbinop |}.


  Definition double_to_hex_string (f : float) : string
    := "0x" ++ NilEmpty.string_of_uint (N.to_hex_uint (Z.to_N (Int64.unsigned (Float.to_bits f)))).

  Definition float_to_hex_string (f : float32) : string
    := double_to_hex_string (Float32.to_double f).

  #[global] Instance showFloat : Show float
    := {| show := double_to_hex_string |}.

  #[global] Instance showFloat32 : Show float32
    := {| show := float_to_hex_string |}.

  Definition show_int (x : Integers.Int.int) : string
    := show (Int.unsigned x).

  #[global] Instance Show_Int : Show Integers.Int.int
    := {| show := show_int|}.

  Definition show_fast_math (fm : fast_math) : string
    := match fm with
       | Nnan => "nnan"
       | Ninf => "ninf"
       | Nsz => "nsz"
       | Arcp => "arcp"
       | Fast => "fast"
       end.

  #[global] Instance showFastMatch : Show fast_math
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

  #[global] Instance ShowConversionType : Show conversion_type
    := {| show := show_conversion_type |}.

  Definition ex_to_nat (ex : exp T) : nat :=
    match ex with
    |EXP_Integer x => (Z.to_nat x)
    | _ => 0 (* This is arbitrary, it's never going to hit this case anyway *)
    end.


  Definition ex_to_int (ex : exp T) : Z :=
    match ex with
    |EXP_Integer x => x
    | _ => 0%Z (* This is arbitrary, it's never going to hit this case anyway *)
    end.

  Definition show_c_string (ex : exp T) : string :=
    let n : nat := ex_to_nat ex in
    let x : Z := ex_to_int ex in
    if ((n <? 32) || (126 <? n))%nat then NilEmpty.string_of_uint (N.to_hex_uint (Z.to_N  x))
    else (string_of_list_ascii ((ascii_of_nat n) :: [])).

  Definition is_op (e : exp T) : bool :=
    match e with
    | EXP_Integer x => false
    | EXP_Float f =>  false
    | EXP_Double f =>   false
    | EXP_Hex f =>   false
    | EXP_Bool b =>     false
    | EXP_Null =>      false
    | EXP_Zero_initializer =>    false
    (* see notes on cstring on LLVMAst.v *)
    (* I'm using string_of_list_ascii bc I couldn't find any other function that converted asciis to strings  *)
    | EXP_Cstring elts =>     false
    | EXP_Undef =>         false
    | EXP_Struct fields =>    false
    | EXP_Packed_struct fields =>     false
    | EXP_Array elts =>               false
    | EXP_Vector elts =>        false
    | _ => true
    end.


  Fixpoint show_exp (b: bool) (v : exp T) :=

    match v with
    | EXP_Ident id => show id
    | EXP_Integer x => show x
    | EXP_Float f => show f
    | EXP_Double f => show f
    | EXP_Hex f => double_to_hex_string f
    | EXP_Bool b => show b
    | EXP_Null => "null"
    | EXP_Zero_initializer => "zeroinitializer"
    (* see notes on cstring on LLVMAst.v *)
    (* I'm using string_of_list_ascii bc I couldn't find any other function that converted asciis to strings  *)
    | EXP_Cstring elts => "c" ++ """" ++
                             concat "" (map (fun '(ty,ex) => show_c_string ex) elts)  ++ """"
    | EXP_Undef => "undef"
    | EXP_Struct fields => "{"  ++ concat ", " (map (fun '(ty,ex) => show ty ++ " " ++  show_exp false ex) fields) ++ "}"
    | EXP_Packed_struct fields => "<{"  ++ concat ", " (map (fun '(ty,ex) => show ty ++ " " ++  show_exp false ex) fields) ++ "}>"
    | EXP_Array elts => "["  ++ concat ", " (map (fun '(ty,ex) => show ty ++ " " ++  show_exp false ex) elts) ++ "]"
    | EXP_Vector elts => "<"  ++ concat ", " (map (fun '(ty,ex) => show ty ++ " " ++  show_exp false ex) elts) ++ ">"
    | OP_IBinop iop t v1 v2 =>
        show iop ++ " " ++ show t ++ " " ++  show_exp false v1 ++ ", " ++  show_exp false v2
    | OP_ICmp cmp t v1 v2 =>
        "icmp " ++ show cmp ++ " " ++ show t ++ " " ++  show_exp false v1 ++ ", " ++  show_exp false v2
    | OP_FBinop fop fmath t v1 v2 =>
        let fmath_string :=
          match fmath with
          | nil => " "
          | _ =>  " " ++ concat " " (map (fun x => show x) fmath) ++  " "
          end in
        show fop ++ fmath_string ++ show t ++ " " ++  show_exp false v1 ++ ", " ++  show_exp false v2
    | OP_FCmp cmp t v1 v2 =>
        "fcmp " ++ show cmp ++ " " ++ show t ++ " " ++  show_exp false v1 ++ ", " ++  show_exp false v2
    | OP_Conversion conv t_from v t_to => show conv ++ " " ++ show t_from ++ " " ++  show_exp false v ++ " to " ++ show t_to
    | OP_GetElementPtr t ptrval idxs =>
        let (tptr, exp) := ptrval in

        "getelementptr " ++ show t ++ ", " ++ show tptr ++ " " ++ show_exp false exp ++  fold_left (fun str '(ty, ex) => str ++ ", " ++ show ty ++ " " ++ show_exp false ex) idxs ""

    | OP_ExtractElement vec idx =>
        let (tptr, exp) := vec in
        let (tidx, iexp) := idx in
        "extractelement " ++ show tptr ++ " " ++  show_exp false exp ++ ", " ++ show tidx ++ " " ++  show_exp false iexp
    | OP_InsertElement vec elt idx =>
        let (tptr, exp) := vec in
        let (telt, eexp) := elt in
        let (tidx, iexp) := idx in
        "insertelement " ++ show tptr ++ " " ++  show_exp false exp ++ ", " ++ show telt ++ " " ++  show_exp false eexp ++ ", " ++ show tidx ++ " " ++ show_exp false iexp
    | OP_ShuffleVector vec1 vec2 idxmask =>
        let (type1, expression1) := vec1 in
        let (type2, expression2) := vec2 in
        let (type3, expression3) := idxmask in
        "shufflevector " ++ show type1 ++  show_exp false expression1  ++ ", " ++ show type2 ++  show_exp false expression2 ++ ", " ++ show type3 ++  show_exp false expression3
    (* This one, extractValue *)
    | OP_ExtractValue vec idxs =>
        let (tptr, exp) := vec in
        "extractvalue " ++ show tptr ++ " " ++  show_exp true exp ++ ", " ++ concat ", " (map (fun x => show x) idxs)
    | OP_InsertValue vec elt idxs =>
        let (tptr, exp) := vec in
        let (telt, eexp) := elt in
        "insertvalue " ++ show tptr ++ " " ++  show_exp false exp ++ ", " ++ show telt ++ " " ++  show_exp false eexp ++ ", " ++ concat ", " (map (fun x => show x) idxs)
    | OP_Select (tc, cnd) (t1, v1) (t2, v2) =>
        let openingParens := if b then "(" else "" in
        let closingParens := if b then ")" else "" in
        "select " ++ openingParens ++ show tc ++ " " ++  show_exp false cnd ++ ", " ++ show t1 ++ " " ++  show_exp false v1  ++ ", " ++ show t2 ++ " " ++  show_exp false v2 ++ closingParens
    | OP_Freeze (ty, ex) => "freeze " ++ show ty ++ " " ++ show_exp false ex 
    end.


  #[global] Instance showExp : Show (exp T)
    := {| show := show_exp false |}.

  #[global] Instance showTExp : Show (texp T)
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

  #[global] Instance showPhi : Show (phi T)
    := {| show p :=
         let '(Phi t phis) := p in
         "phi " ++ show t ++ " " ++ intersperse ", " (map show_phi_block phis)
       |}.


  Definition show_opt_prefix {A} `{Show A} (prefix : string) (ma : option A) : string
    := match ma with
       | None   => ""
       | Some a => prefix ++ show a
       end.

  Definition show_ordering (o : ordering) : string :=
    match o with
    |Unordered => "unordered"
    |Monotonic => "monotonic"
    |Acquire => "acquire"
    |Release => "release"
    |Acq_rel => "acq_rel"
    |Seq_cst => "seq_cst"
    end.

  #[global] Instance showOrdering : Show (ordering)
    := {| show := show_ordering |}.

  Definition show_cmpxchg (c : cmpxchg T) : string :=
    let p_weak := match c.(c_weak) with
                  |None => ""
                  |Some x => show x
                  end in
    let p_volatile := match c.(c_volatile) with
                      |None => ""
                      |Some x => show x
                      end in
    let p_syncscope := match c.(c_syncscope) with
                       |None => ""
                       |Some x => "[syncscope(""" ++ show x ++ """)]"
                       end in
    let p_align := match c.(c_align) with
                   |None => ""
                   |Some x => ", align " ++ show x
                   end in

    concatStr ["cmpxchg "; p_weak; p_volatile; show c.(c_ptr); ", ";  show c.(c_cmp_type); show c.(c_cmp); ", " ; show c.(c_new) ; p_syncscope ; show c.(c_success_ordering); show c.(c_failure_ordering) ; p_align ;  "yields  { "; show c.(c_cmp_type) ; ", i1 } "].

  #[global] Instance showCmpxchg : Show (cmpxchg T)
    := {| show := show_cmpxchg |}.

  Definition show_a_rmw_operation (a :  atomic_rmw_operation) : string :=
    match a with
    |Axchg => "xchg"
    |Aadd  => "add"
    |Asub => "sub"
    |Aand => "and"
    |Anand => "nand"
    |Aor  => "or"
    |Axor => "xor"
    |Amax => "max"
    |Amin => "min"
    |Aumax => "umax"
    |Aumin => "umin"
    |Afadd => "fadd"
    |Afsub => "fsub"
    end.

  #[global] Instance showARmwOperation : Show (atomic_rmw_operation)
    := {| show := show_a_rmw_operation |}.

  Definition show_atomic_rmw (a : atomicrmw T) : string :=
    let p_volatile := match a.(a_volatile) with
                      |None => ""
                      |Some x => show x
                      end in
    let p_syncscope := match a.(a_syncscope) with
                       |None => ""
                       |Some x => "[syncscope(""" ++ show x ++ """)]"
                       end in

    let p_align := match a.(a_align) with
                   |None => ""
                   |Some x => ", align " ++ show x
                   end in

    concatStr ["atomicrmw" ;  p_volatile ; show a.(a_operation) ; show a.(a_ptr) ; ", " ;
               show a.(a_val) ; p_syncscope ; show a.(a_ordering) ; p_align ; "yields " ;
               show a.(a_type)].

  #[global] Instance showAtomicrmw : Show (atomicrmw T)
    := {| show := show_atomic_rmw |}.

  Definition show_instr (i : instr T) : string
    := match i with
       | INSTR_Comment s => "; " ++ s
       | INSTR_Op e => show e
       (* Based on the old printer  *)
       | INSTR_Call fn args => "call " ++ show fn ++ "(" ++ (concat ", " (map (fun x => show x) (args))) ++ ")"
       | INSTR_Alloca t nb align =>
           "alloca " ++ show t ++ show_opt_prefix ", " nb ++ show_opt_prefix ", align " align
       | INSTR_Load vol t ptr align =>
           "load " ++ show t ++ ", " ++ show ptr ++ show_opt_prefix ", align " align
       | INSTR_Store vol tval ptr align =>
           "store " ++ (if vol then "volatile " else "") ++ show tval ++ ", " ++ show ptr ++ show_opt_prefix ", align " align
       | INSTR_Fence syncscope ordering => let printable_sync := match syncscope with
                                                                 | None => ""
                                                                 | Some x => "[syncscope(""" ++ show x ++ """)]"
                                                                 end in
                                           "fence " ++ printable_sync ++ show ordering  ++" ; yields void"
       | INSTR_AtomicCmpXchg c => show_cmpxchg c
       | INSTR_AtomicRMW a => show_atomic_rmw a
       | INSTR_VAArg (va_list_and_arg_list) (t)  => "va_arg " ++ show va_list_and_arg_list ++ ", " ++ show t
       | INSTR_LandingPad => "skipping implementation at the moment"
       end.

  #[global] Instance showInstr : Show (instr T)
    := {| show := show_instr |}.

  #[global] Instance showInstrId : Show instr_id
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

  #[global] Instance showInstrWithId : Show (instr_id * instr T)
    := {| show := show_instr_id |}.

  Definition show_tint_literal (t : tint_literal) : string :=
    match t with
    | TInt_Literal sz x => "i" ++ show sz ++ " " ++ show x
    end.

  #[global] Instance showTintLiteral : Show tint_literal :=
    {| show := show_tint_literal |}.

  Definition show_terminator (t : terminator T) : string
    := match t with
       | TERM_Ret v => "ret " ++ show v
       | TERM_Ret_void => "ret void"
       | TERM_Br te b1 b2 => "br " ++ show te ++ ", label %" ++ show b1 ++ ", label %" ++ show b2
       | TERM_Br_1 b => "br label %" ++ show b
       | TERM_Switch v def_dest brs => concatStr["switch "; show v; ", label %"; show def_dest;
                                                 " ["; fold_left (fun str '(x, y) =>
                                                                    str ++ show x ++ ", label %" ++ show y ++ " ") brs "";
                                                 "]"]

       | TERM_IndirectBr v brs => concatStr["indirectbr "; show v; show brs]
       | TERM_Resume v => "remove " ++ show v
       | TERM_Invoke fnptrval args to_label unwind_label => concatStr["invoke "; show fnptrval;
                                                                      "( "; show args; "to label ";
                                                                      show to_label; "unwind label ";
                                                                      show unwind_label]

       | TERM_Unreachable => "unreachable"
       end.

  #[global] Instance showTerminator : Show (terminator T)
    := {| show := show_terminator |}.

  Definition show_code (indent : string) (c : code T) : string
    := concatStr (map (fun iid => indent ++ show_instr_id iid ++ newline) c).

  #[global] Instance showCode : Show (code T)
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
  #[global] Instance showBlock: Show (block T) :=
    {|
      show := show_block "    "
    |}.

  Definition show_typ_instr (typ_instr: T * instr T) : string :=
    let (t, i) := typ_instr in
    "(" ++ (show t) ++ ", " ++ (show i) ++ ")".

  #[global] Instance showTypInstr: Show (T * instr T) :=
    {|
      show := show_typ_instr
    |}.

  Definition show_arg (arg : local_id * T * list param_attr) : string
    := let '(i, t, parameter_attributes) := arg in
       show t ++ concat " " (map (fun x => show x) (parameter_attributes)) ++ " %" ++ show i.

  Definition show_arg_list (args : list (local_id * T * list param_attr)) (varargs:bool) : string
    :=
    let vararg_str :=
      if Nat.eqb (List.length args) 0 then
        (if varargs then "..." else "")
      else
        (if varargs then ", ..." else "")
    in
    let arg_str := concat ", " (map show_arg args)
    in
      concatStr ["("; arg_str; vararg_str ; ")"].


  (* TODO: REALLY?!? *)
  Fixpoint zip {X Y} (xs : list X) (ys : list Y) : list (X * Y)
    := match xs, ys with
       | [], _ => []
       | _, [] => []
       | (x::xs), (y::ys) => (x, y) :: zip xs ys
       end.

  Fixpoint zip3 {X Y Z} (xs : list X) (ys : list Y) (zs : list Z) : list (X * Y *  Z)
    := match xs, ys, zs with
       | [], _, _ => []
       | _, [], _ => []
       | _, _, [] => []
       | (x::xs), (y::ys), (z::zs) => (x, y, z) :: zip3 xs ys zs
       end.

  Fixpoint show_metadata (md : metadata T)  : string :=
    match md with
    | METADATA_Const tv => show tv
    | METADATA_Null => "null"
    | METADATA_Id i => "!" ++ show i
    | METADATA_String s => "!" ++ show s
    | METADATA_Named strs => "!{" ++ intersperse " , " (List.map (fun x => "!" ++ x) strs) ++ "}"
    | METADATA_Node mds => "!{" ++ intersperse " , " (List.map show_metadata mds) ++ "}"
    end.

  #[global] Instance showMetadata (md : metadata T) : Show (metadata T) :=
    {| show := show_metadata |}.

End ShowInstances.

(** Return empty string when None *)
(** Adds a space -- is this the right place to do that? *)
Definition maybe_to_string {X} (to_string : X -> string) (ox : option X) :=
  match ox with
  | None => ""
  | Some x => ((to_string x) ++ " ")%string
  end.

(** Return empty stringwhen None *)
Definition maybe_show {X} `{Show X} (ox : option X) : string :=
  maybe_to_string show ox.

Definition show_definition (defn : definition typ (block typ * list (block typ))) : string
  :=
  let name  := defn.(df_prototype).(dc_name) in
  let ftype := defn.(df_prototype).(dc_type) in
  let '(return_attributes, argument_attributes):= defn.(df_prototype).(dc_param_attrs) in

  match ftype with
  | TYPE_Function ret_t args_t vararg =>
      let arg_names := defn.(df_args) in

      (* Note: if these lists are not equal in length arguments will
         be dropped...  Better to check and spew garbage, as this may
         lead to tricky to catch problems otherwise.  *)
      let arg_length := List.length arg_names in
      if negb (Nat.eqb arg_length (List.length args_t) && (Nat.eqb arg_length (List.length argument_attributes)))
      then "Function """ ++ show name ++ """ has mismatched arguments and argument attributes length"
      else
        let args := zip3 arg_names args_t argument_attributes in

        let blocks :=
          match df_instrs defn with
          | (b, bs) => concat newline (map (show_block "    ") (b::bs))
          end in

        let ret_attributes := concat " " (map (fun x => show x) (return_attributes)) in
        let printable_ret_attrs := if ret_attributes then concatStr [" "; ret_attributes] else "" in

        let linkage := maybe_show (dc_linkage defn.(df_prototype)) in
        let visibility := maybe_show (dc_visibility defn.(df_prototype)) in
        let dll_storage := maybe_show (dc_dll_storage defn.(df_prototype)) in
        let cconv := maybe_show (dc_cconv defn.(df_prototype)) in

        let section :=
          maybe_to_string
            (fun s => concatStr ["section \"; s; "\"; " "])
            (dc_section defn.(df_prototype)) in

        let align :=
          maybe_to_string
            (fun a => concatStr ["align "; show a; " "])
            (dc_align defn.(df_prototype)) in

        let gc := maybe_show (dc_gc defn.(df_prototype)) in

        concatStr ["define "; linkage; visibility ; dll_storage ;
                   cconv ; printable_ret_attrs ; show ret_t; " @"; show name; show_arg_list args vararg;
                   section ; align ; gc ; " {"; newline ;
                   blocks;
                   "}";
                   newline]

  | _ => "Invalid type on function: " ++ show name
  end.

Global Instance showDefinition: Show (definition typ (block typ * list (block typ))) :=
  {| show := show_definition |}.

(* Why can I not make show functions implicit?  *)
Definition show_declaration (decl: declaration typ) : string :=
  let name := decl.(dc_name) in
  let (ret_attrs, args_attrs) := decl.(dc_param_attrs) in
  match decl.(dc_type) with
  | TYPE_Function ret_t args_t vararg =>
      let link := maybe_show (dc_linkage decl) in
      let vis := maybe_show (dc_visibility decl) in
      let dll := maybe_show (dc_dll_storage decl) in
      let cc := maybe_show (dc_cconv decl)in

      let section :=
        maybe_to_string
          (fun s => concatStr ["section \"; s; "\"; " "])
          (dc_section decl) in

      let align :=
        maybe_to_string
          (fun a => concatStr ["align "; show a; " "])
          (dc_align decl) in

      let gc := maybe_show (dc_gc decl) in

      let vararg_str :=
        if Nat.eqb (List.length args_t) 0 then
          (if vararg then "..." else "")
        else
          (if vararg then ", ..." else "")
      in
      concatStr ["declare "; link; vis; dll; cc;
                 concatStr[intersperse " " (map show ret_attrs)]; " " ;

                 show ret_t; " @"; show name;  "(";
                 concat ", " (map (fun '(x, y) => concatStr[show x; " "; match y with
                                                                      | [] => ""
                                                                      | z :: tl => show z
                                                                      end ])
                                  (List.combine args_t args_attrs));
                 vararg_str ;
                 ")"; section; align; gc]
  | _ => "Invalid type on function: " ++ show name
  end.

Global Instance showDeclaration: Show (declaration typ) :=
  {| show := show_declaration |}.

Definition show_unnamed_addr (u:unnamed_addr) : string :=
  match u with
  | Unnamed_addr => "unnamed_addr"
  | Local_Unnamed_addr => "local_unnamed_addr"
  end.
          
#[global] Instance showUnnamedAddr : Show unnamed_addr :=
  {| show := show_unnamed_addr |}.

Definition show_global (g : global typ) : string :=
  let name  := g.(g_ident) in
  let gtype := g.(g_typ) in
  let linkage := maybe_show (g_linkage g) in
  let visibility := maybe_show (g_visibility g) in
  let dll_storage := maybe_show (g_dll_storage g) in
  let thread_local := maybe_show (g_thread_local_storage g) in
  let g_exp := maybe_show g.(g_exp) in
  let unnamed_addr := maybe_show (g_unnamed_addr g) in
  let addrspace := maybe_show (g_addrspace g) in
  let externally_initialized := if g.(g_externally_initialized) then "external " else "" in
  let g_or_c := if g.(g_constant) then "constant " else "global " in

  let section :=
    maybe_to_string
      (fun s => concatStr ["section \"; s; "\"; " "])
      (g_section g) in

  let align :=
    maybe_to_string
      (fun a => concatStr ["align "; show a; " "])
      (g_align g) in

  concatStr ["@"; show name ; " = " ; linkage ; visibility;
             dll_storage ; thread_local;
             unnamed_addr; addrspace;
             externally_initialized; g_or_c;
             show gtype; " "; g_exp;  section ; align].

Global Instance showGlobal : Show (global typ) :=
  {| show := show_global |}.

Definition show_tle (tle : toplevel_entity typ (block typ * list (block typ))) : string
  := match tle with
     (*Why is show_definition rather than show being used here*)
     | TLE_Definition defn => show defn
     | TLE_Comment msg => ";" ++ show msg (*What if the comment is multiple lines? *)
     | TLE_Target tgt => "target triple = " ++  show tgt
     | TLE_Datalayout layout => "target datalayout = " ++ show layout
     | TLE_Source_filename s => "source_filename = " ++ show s
     | TLE_Declaration decl => show decl
     | TLE_Global g => show g
     | TLE_Metadata id md => "!" ++ show id ++ show_metadata md (* Can't use implicit *)
     | TLE_Type_decl id t => concatStr [show_ident id ;  " = type " ; show t ]
     | TLE_Attribute_group i attrs => concatStr ["attributes #" ; show i ; " = { " ;
                                                concat " " (map (fun x => show x) (attrs)) ; " }"  ]
     end.

Global Instance showTLE: Show (toplevel_entity typ (block typ  * list (block typ))) :=
  {| show := show_tle |}.

Global Instance showProg : Show (list (toplevel_entity typ (block typ * list (block typ)))) :=
  {| show tles := concat (newline ++ newline) (map show_tle tles) |}.
