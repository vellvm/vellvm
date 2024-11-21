(**
    Show instances for Vellvm. These serialize Vellvm ASTs into the
    standard format for .ll files. The result of show on a Vellvm
    program should give you a string that can be read by clang.
 *)

From Vellvm Require Import LLVMAst Utilities AstLib Syntax.CFG DynamicTypes DList.

Require Import Integers Floats.

Require Import List.

Import ListNotations.

Import DList.

From Coq Require Import
     ZArith String Bool.Bool Numbers.HexadecimalString
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

#[global] Instance Show_Pos : Show positive.
split.
exact (fun p => show (Zpos p)).
Defined.

Class DShow (A : Type) := { dshow : A -> DString }.

#[global] Infix "@@" := (DList_append) (right associativity, at level 60).

#[global] Instance DShowList {A} `{DShow A} : DShow (list A) :=
  { dshow := fun x => DList_join (map dshow x) }.

#[global] Instance DShowPair {A B : Type} `{_ : DShow A} `{_ : DShow B} : DShow (A * B) :=
{|
  dshow p := match p with (a,b) => string_to_DString "(" @@ dshow a @@ string_to_DString "," @@ dshow b @@ string_to_DString ")" end
|}.

#[global] Instance DShowShow {A} `{DShow A} : Show A :=
{|
  show a := DString_to_string (dshow a);
|}.

Section ShowInstances.
  Local Open Scope string.

  Context {T : Set}.
  Context `{DShow T}.

  Definition dshow_raw_id (rid : raw_id) : DString
    := match rid with
       | Name s => string_to_DString s
       | Anon i => string_to_DString (show i)
       | Raw i  => string_to_DString (show i)
       end.

  #[global] Instance dshowRawId : DShow raw_id
    := {| dshow := dshow_raw_id |}.

  Definition dshow_ident (i : ident) : DString
    := match i with
      | ID_Global r => string_to_DString "@" @@ dshow_raw_id r
      | ID_Local r  => string_to_DString "%" @@ dshow_raw_id r
       end.

  #[global] Instance dshowIdent : DShow ident
    := {| dshow := dshow_ident |}.

  Fixpoint dshow_typ (t : typ) : DString  :=
    match t with
    | TYPE_I sz                 => string_to_DString "i" @@
                                    string_to_DString (show sz)
    | TYPE_IPTR                 => string_to_DString "iptr"
    | TYPE_Pointer (Some t)     => dshow_typ t @@ string_to_DString "*"
    | TYPE_Pointer None         => string_to_DString "ptr"
    | TYPE_Void                 => string_to_DString "void"
    | TYPE_Half                 => string_to_DString "half"
    | TYPE_Float                => string_to_DString "float"
    | TYPE_Double               => string_to_DString "double"
    | TYPE_X86_fp80             => string_to_DString "x86_fp80"
    | TYPE_Fp128                => string_to_DString "fp128"
    | TYPE_Ppc_fp128            => string_to_DString "ppc_fp128"
    | TYPE_Metadata             => string_to_DString "metadata"
    | TYPE_X86_mmx              => string_to_DString "x86_mmx"
    | TYPE_Array sz t           =>
        list_to_DString ["["; show sz; " x "] @@ dshow_typ t @@
        string_to_DString "]"
    | TYPE_Function ret args varargs =>
        let varargs_str :=
          if Nat.eqb (List.length args) 0 then
            (if varargs then string_to_DString "..." else string_to_DString  "")
          else
            (if varargs then string_to_DString ", ..." else string_to_DString "")
        in dshow_typ ret @@ string_to_DString  " (" @@
           concat_DString (string_to_DString ", ") (map dshow_typ args) @@ varargs_str @@ string_to_DString ")"

    | TYPE_Struct fields        => string_to_DString "{" @@
                                   concat_DString (string_to_DString ", ") (map dshow_typ fields) @@
                                   string_to_DString "}"
    | TYPE_Packed_struct fields =>
        string_to_DString "<{" @@ concat_DString (string_to_DString ", ") (map dshow_typ fields) @@
        string_to_DString "}>"

    | TYPE_Opaque               => string_to_DString "opaque"
    | TYPE_Vector sz t          => string_to_DString "<" @@
                                   string_to_DString (show sz) @@
                                   string_to_DString " x " @@ dshow_typ t @@
                                   string_to_DString ">"
    | TYPE_Identified id        => dshow id
    end.

  #[global] Instance dshowTyp : DShow typ :=
    {| dshow := dshow_typ |}.

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

  Definition show_sum {A B} `{Show A} `{Show B} (s : A + B) : string
    :=
    match s with
    | inl a => show a
    | inr b => show b
    end.

  #[global] Instance showSum {A B} `{Show A} `{Show B} : Show (A + B)
    := {| show := show_sum |}.

  Definition show_param_attr (p : param_attr) : DString :=
    match p with
    | PARAMATTR_Zeroext => string_to_DString "zeroext"
    | PARAMATTR_Signext => string_to_DString "signext"
    | PARAMATTR_Inreg => string_to_DString "inreg"
    | PARAMATTR_Byval t => string_to_DString "byval(" @@ dshow t @@ string_to_DString ")"
    | PARAMATTR_Byref t => string_to_DString "byref(" @@ dshow t @@ string_to_DString ")"
    | PARAMATTR_Preallocated t => string_to_DString "preallocated(" @@ dshow t @@ string_to_DString ")"
    | PARAMATTR_Inalloca t => string_to_DString "inalloca(" @@ dshow t @@ string_to_DString ")"
    | PARAMATTR_Sret t => string_to_DString "sret(" @@ dshow t @@ string_to_DString ")"
    | PARAMATTR_Elementtype t => string_to_DString "elementtype(" @@ dshow t @@ string_to_DString ")"
    | PARAMATTR_Align a => string_to_DString "align " @@ string_to_DString (show a)
    | PARAMATTR_Noalias => string_to_DString "noalias"
    | PARAMATTR_Nocapture => string_to_DString "nocapture"
    | PARAMATTR_Nofree => string_to_DString "nofree"
    | PARAMATTR_Nest => string_to_DString "nest"
    | PARAMATTR_Returned => string_to_DString "returned"
    | PARAMATTR_Nonnull => string_to_DString "nonnull"
    | PARAMATTR_Dereferenceable a => string_to_DString "dereferenceable(" @@ string_to_DString (show a) @@
                                    string_to_DString ")"
    | PARAMATTR_Dereferenceable_or_null a => string_to_DString "dereferenceable_or_null(" @@
                                            string_to_DString (show a) @@ string_to_DString ")"
    | PARAMATTR_Swiftself => string_to_DString "swiftself"
    | PARAMATTR_Swiftasync => string_to_DString "swiftasync"
    | PARAMATTR_Swifterror => string_to_DString "swifterror"
    | PARAMATTR_Immarg => string_to_DString "immarg"
    | PARAMATTR_Noundef => string_to_DString "noundef"
    | PARAMATTR_Alignstack a => string_to_DString "alignstack(" @@ string_to_DString (show a)  @@ string_to_DString ")"
    | PARAMATTR_Allocalign => string_to_DString "allocalign"
    | PARAMATTR_Allocptr => string_to_DString "allocptr"
    | PARAMATTR_Readnone => string_to_DString "readnone"
    | PARAMATTR_Readonly => string_to_DString "readonly"
    | PARAMATTR_Writeonly => string_to_DString "writeonly"
    | PARAMATTR_Writable => string_to_DString "writable"
    | PARAMATTR_Dead_on_unwind => string_to_DString "dead_on_unwind"
    end.

  #[global] Instance dshowParamAttr : DShow param_attr
    := { dshow := show_param_attr }.

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
    | FNATTR_Mustprogress => "mustprogress"
    (* | FNATTR_Warn_stack_size th  => - FNATTR_KeyValue *)
    | FNATTR_Vscale_range min max  =>
        match max with
        | None => "vscale_range(" ++ show min ++ ")"
        | Some m => "vscale_range(" ++ show min ++ "," ++ show m ++ ")"
        end
    | FNATTR_String s => """" ++ s ++ """"  (* "no-see" *)
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
    := "0x" ++ NilEmpty.string_of_uint (N.to_hex_uint (Z.to_N (@unsigned 64 (Float.to_bits f)))).

  Definition float_to_hex_string (f : float32) : string
    := double_to_hex_string (Float32.to_double f).

  #[global] Instance showFloat : Show float
    := {| show := double_to_hex_string |}.

  #[global] Instance showFloat32 : Show float32
    := {| show := float_to_hex_string |}.

  Definition show_int {sz} (x : @bit_int sz) : string
    := show (unsigned x).

  #[global] Instance Show_Int {sz} : Show (@bit_int sz)
    := {| show := show_int|}.

  Definition show_fast_math (fm : fast_math) : string
    := match fm with
       | Nnan => "nnan"
       | Ninf => "ninf"
       | Nsz => "nsz"
       | Arcp => "arcp"
       | Contract => "contract"
       | Afn => "afn"
       | Reassoc => "reassoc"
       | Fast => "fast"
       end.

  #[global] Instance showFastMath : Show fast_math
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
    if ((n <? 32) || (126 <? n))%nat then (
        let conversion :=  NilEmpty.string_of_uint (N.to_hex_uint (Z.to_N  x)) in
        if ((length (conversion)) =? (Z.to_nat 1))%nat then  "\0" ++ conversion
        else "\" ++ conversion
      )
    (*Special case for decimal 34/hex 22*)
    else if (n =? 34)%nat then "\22"
    (*Special case for decimal 92/hex 5C*)
    else if (n =? 92)%nat then "\\"
         else (string_of_list_ascii ((ascii_of_nat n) :: [])).

  Definition dshow_c_string (ex : exp T) : DString :=
    let n : nat := ex_to_nat ex in
    let x : Z := ex_to_int ex in
    if ((n <? 32) || (126 <? n))%nat then (
        let conversion_str := NilEmpty.string_of_uint (N.to_hex_uint (Z.to_N x)) in
        let conversion := NilEmpty.string_of_uint (N.to_hex_uint (Z.to_N x)) in
        if ((length conversion_str) =? (Z.to_nat 1))%nat then string_to_DString "\0" @@ string_to_DString conversion
        else string_to_DString "\" @@ string_to_DString conversion
      )
    (*Special case for decimal 34/hex 22*)
    else if (n =? 34)%nat then string_to_DString "\22"
    (*Special case for decimal 92/hex 5C*)
    else if (n =? 92)%nat then string_to_DString "\\"
         else DList_cons (ascii_of_nat n) DList_empty.

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
    | EXP_Array t elts =>               false
    | EXP_Vector t elts =>        false
    | _ => true
    end.

  Definition add_parens (b : bool) (ds : DString) : DString :=
    if b then string_to_DString "(" @@ ds @@ string_to_DString ")" else ds.

  Fixpoint dshow_exp (b: bool) (v : exp T) : DString :=
    match v with
    | EXP_Ident id => dshow id
    | EXP_Integer x => string_to_DString (show x)
    | EXP_Float f => string_to_DString (show f)
    | EXP_Double f => string_to_DString (show f)
    | EXP_Hex f => string_to_DString (double_to_hex_string f)
    | EXP_Bool b => string_to_DString (show b)
    | EXP_Null => string_to_DString "null"
    | EXP_Zero_initializer => string_to_DString "zeroinitializer"
    (* see notes on cstring on LLVMAst.v *)
    (* I'm using string_of_list_ascii bc I couldn't find any other function that converted asciis to strings  *)
    | EXP_Cstring elts => string_to_DString "c" @@ string_to_DString """" @@
                           DList_join (map (fun '(ty, ex) => (dshow_c_string ex)) elts) @@ string_to_DString  """"

    | EXP_Undef => string_to_DString "undef"
    | EXP_Poison => string_to_DString "poison"

    | EXP_Struct fields =>
        string_to_DString "{" @@
          concat_DString (string_to_DString ", ")
          (map (fun '(ty, ex) =>
                  DList_join [dshow ty ; string_to_DString " "] @@
                    dshow_exp false ex) fields) @@ string_to_DString "}"

    | EXP_Packed_struct fields =>
        string_to_DString "<{" @@
          concat_DString (string_to_DString ", ")
          (map (fun '(ty, ex) =>
                  DList_join [dshow ty ; string_to_DString " "] @@
                    dshow_exp false ex) fields) @@ string_to_DString "}>"

    | EXP_Array t elts =>
        string_to_DString "[" @@
          concat_DString (string_to_DString ", ")
          (map (fun '(ty, ex) => DList_join [dshow ty ; string_to_DString " "] @@ dshow_exp false ex) elts) @@ string_to_DString "]"
    | EXP_Vector t elts => string_to_DString "<" @@ concat_DString (string_to_DString ", ") (map (fun '(ty, ex) => DList_join [dshow ty ; string_to_DString " "] @@ dshow_exp false ex) elts) @@ string_to_DString ">"

    | OP_IBinop iop t v1 v2 =>
        let second_expression :=
          if b
          then dshow t @@ string_to_DString " " @@ dshow_exp true v2
          else dshow_exp true v2
       in string_to_DString (show iop) @@ string_to_DString " " @@ add_parens b (dshow t @@ string_to_DString " " @@ dshow_exp true v1 @@ string_to_DString ", " @@ second_expression)

    | OP_ICmp cmp t v1 v2 =>
        let second_expression :=
          if b
          then dshow t @@ string_to_DString " " @@ dshow_exp true v2
          else dshow_exp true v2
        in list_to_DString ["icmp " ; show cmp ; " "] @@ add_parens b (dshow t @@ string_to_DString " " @@ dshow_exp true v1 @@ string_to_DString ", " @@ second_expression)

    | OP_FBinop fop fmath t v1 v2 =>
        let fmath_string :=
          string_to_DString
            match fmath with
            | nil => " "
            | _ =>  " " ++ concat " " (map (fun x => show x) fmath) ++  " "
            end
        in list_to_DString [show fop ; " "] @@ add_parens b (fmath_string @@ dshow t @@ string_to_DString " " @@  dshow_exp true v1 @@ string_to_DString ", " @@ dshow_exp true v2)

    | OP_FCmp cmp t v1 v2 =>
        string_to_DString "fcmp " @@ add_parens b (list_to_DString [show cmp ; " "] @@ dshow t @@ string_to_DString " " @@ dshow_exp true v1 @@
                                                 string_to_DString ", " @@ dshow_exp true v2)

    | OP_Conversion conv t_from v t_to => list_to_DString [show conv ; " "] @@ add_parens b (dshow t_from @@ string_to_DString " " @@ dshow_exp true v @@
                                                                                             string_to_DString " to " @@ dshow t_to)

    | OP_GetElementPtr t ptrval idxs =>
        let (tptr, exp) := ptrval in
        string_to_DString "getelementptr " @@ add_parens b (dshow t @@ string_to_DString ", " @@ dshow tptr @@ string_to_DString " " @@ dshow_exp true exp @@
                                                              fold_left (fun str '(ty, ex) => str @@ string_to_DString ", " @@ dshow ty @@ string_to_DString " " @@ dshow_exp true ex) idxs DList_empty)

    | OP_ExtractElement vec idx =>
        let (tptr, exp) := vec in
        let (tidx, iexp) := idx in
        string_to_DString "extractelement " @@ add_parens b (dshow tptr @@ string_to_DString " " @@ dshow_exp true exp @@ string_to_DString ", " @@ dshow tidx @@ string_to_DString " " @@  dshow_exp true iexp)

    | OP_InsertElement vec elt idx =>
        let (tptr, exp) := vec in
        let (telt, eexp) := elt in
        let (tidx, iexp) := idx in
        string_to_DString "insertelement " @@ add_parens b (dshow tptr @@ string_to_DString " " @@ dshow_exp true exp @@ string_to_DString ", " @@ dshow telt @@ string_to_DString " " @@
                                                          dshow_exp true eexp @@ string_to_DString ", " @@ dshow tidx @@ string_to_DString " " @@ dshow_exp true iexp)

    | OP_ShuffleVector vec1 vec2 idxmask =>
        let (type1, expression1) := vec1 in
        let (type2, expression2) := vec2 in
        let (type3, expression3) := idxmask in
        string_to_DString "shufflevector " @@ add_parens b (dshow type1 @@ dshow_exp true expression1 @@ string_to_DString ", " @@ dshow type2 @@ dshow_exp true expression2 @@
                                                              string_to_DString ", " @@ dshow type3 @@ dshow_exp true expression3)
    (* This one, extractValue *)
    | OP_ExtractValue vec idxs =>
        let (tptr, exp) := vec in
        string_to_DString "extractvalue " @@ add_parens b (dshow tptr @@ string_to_DString " " @@ dshow_exp true exp @@ string_to_DString ", " @@
                                                         concat_DString (string_to_DString ", ") (map (fun x => string_to_DString (show x)) idxs))


    | OP_InsertValue vec elt idxs =>
        let (tptr, exp) := vec in
        let (telt, eexp) := elt in
        string_to_DString "insertvalue " @@ add_parens b (dshow tptr @@ string_to_DString " " @@ dshow_exp false exp @@ string_to_DString ", " @@ dshow telt @@ string_to_DString " " @@
                                                            dshow_exp false eexp @@ string_to_DString ", " @@ concat_DString (string_to_DString ", ") (map (fun x => string_to_DString (show x)) idxs))

    | OP_Select (tc, cnd) (t1, v1) (t2, v2) =>
        string_to_DString "select "  @@ add_parens b (dshow tc @@ string_to_DString " " @@ dshow_exp true cnd @@ string_to_DString ", " @@ dshow t1 @@ string_to_DString " " @@
                                                    dshow_exp true v1  @@ string_to_DString ", " @@ dshow t2 @@ string_to_DString " " @@  dshow_exp true v2)

    | OP_Freeze (ty, ex) => string_to_DString "freeze " @@ add_parens b (dshow ty @@ string_to_DString " " @@ dshow_exp true ex)
    end.

  #[global] Instance dshowExp : DShow (exp T) :=
    {| dshow := dshow_exp false |}.

  #[global] Instance dshowTExp : DShow (texp T) :=
    {| dshow te := let '(t, e) := te in dshow t @@ string_to_DString " " @@ dshow e |}.

  Definition show_phi_block (p : block_id * exp T) : DString :=
    let '(bid, e) := p in
    string_to_DString "[ " @@ dshow_exp true e @@ list_to_DString [", "; "%"] @@ dshow bid @@ string_to_DString " ]".

  Definition intersperse (sep : string) (l : list string) : string
    := fold_left (fun acc s => if String.eqb "" acc then s else acc ++ sep ++ s) l "".

  Definition dintersperse (sep : DString) (l : list DString) : DString
    := fold_left (fun acc s => if String.eqb "" (DString_to_string acc) then s else acc @@ sep @@ s) l (string_to_DString "").

  Fixpoint dconcat (sep : DString) (ls : list DString) :=
    match ls with
    | nil => string_to_DString EmptyString
    | cons x nil => x
    | cons x xs => x @@ sep @@ dconcat sep xs
    end.

  #[global] Instance dshowPhi : DShow (phi T)
    := {| dshow p :=
         let '(Phi t phis) := p in
         DList_join [string_to_DString "phi " ; dshow t ; string_to_DString " "] @@
           concat_DString (string_to_DString ", ") (map show_phi_block phis)
       |}.

  Definition show_opt_prefix {A} `{Show A} (prefix : string) (ma : option A) : string
    := match ma with
       | None   => ""
       | Some a => prefix ++ show a
       end.

  Definition dshow_opt_prefix {A} `{DShow A} (prefix : DString) (ma : option A) : DString
    := match ma with
       | None   => string_to_DString ""
       | Some a => prefix @@ dshow a
       end.

  Definition show_opt_list {A} `{Show A} (ma : option A) : list string
    := match ma with
       | None   => []
       | Some a => [show a]
       end.

  Definition dshow_opt_list {A} `{DShow A} (ma : option A) : list DString
    := match ma with
       | None   => []
       | Some a => [dshow a]
       end.

  Definition show_ordering (o : ordering) : DString :=
    string_to_DString
      match o with
      |Unordered => "unordered"
      |Monotonic => "monotonic"
      |Acquire => "acquire"
      |Release => "release"
      |Acq_rel => "acq_rel"
      |Seq_cst => "seq_cst"
      end.

  #[global] Instance dshowOrdering : DShow (ordering)
    := {| dshow := show_ordering |}.

  Definition show_cmpxchg (c : cmpxchg T) : DString :=
    let p_weak :=
      string_to_DString
        match c.(c_weak) with
        |None => ""
        |Some x => show x
        end in
    let p_volatile :=
      string_to_DString
        match c.(c_volatile) with
        |None => ""
        |Some x => show x
        end in
    let p_syncscope :=
      string_to_DString
        match c.(c_syncscope) with
        |None => ""
        |Some x => "[syncscope(""" ++ show x ++ """)]"
        end in
    let p_align :=
      string_to_DString
        match c.(c_align) with
        |None => ""
        |Some x => ", align " ++ show x
        end in

    DList_join
      [string_to_DString "cmpxchg ";
       p_weak;
       p_volatile;
       dshow c.(c_ptr);
       string_to_DString ", ";
       dshow c.(c_cmp_type);
       string_to_DString (show c.(c_cmp));
       string_to_DString ", " ;
       dshow c.(c_new);
       p_syncscope;
       dshow c.(c_success_ordering);
       dshow c.(c_failure_ordering);
       p_align;
       string_to_DString "yields  { ";
       dshow c.(c_cmp_type);
       string_to_DString ", i1 } "
      ].

  #[global] Instance dshowCmpxchg : DShow (cmpxchg T)
    := {| dshow := show_cmpxchg |}.

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

  Definition show_atomic_rmw (a : atomicrmw T) : DString :=
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

    DList_join
      [string_to_DString "atomicrmw";
       string_to_DString p_volatile;
       string_to_DString (show a.(a_operation));
       dshow a.(a_ptr);
       string_to_DString ", ";
       dshow a.(a_val);
       string_to_DString p_syncscope;
       dshow a.(a_ordering);
       string_to_DString p_align;
       string_to_DString "yields ";
       dshow a.(a_type)].

  #[global] Instance showAtomicrmw : DShow (atomicrmw T)
    := {| dshow := show_atomic_rmw |}.

  Fixpoint dshow_metadata (md : metadata T)  : DString :=
    match md with
    | METADATA_Const tv => dshow tv
    | METADATA_Null => string_to_DString "null"
    | METADATA_Nontemporal => string_to_DString "!nontemporal"
    | METADATA_Invariant_load => string_to_DString "!invariant.load"
    | METADATA_Invariant_group => string_to_DString "!invariant.group"
    | METADATA_Nonnull => string_to_DString "!nonnull"
    | METADATA_Dereferenceable => string_to_DString "!dereferenceable"
    | METADATA_Dereferenceable_or_null => string_to_DString "!dereferenceable_or_null"
    | METADATA_Align => string_to_DString "!align"
    | METADATA_Noundef => string_to_DString "!noundef"
    | METADATA_Id i => string_to_DString "!" @@ dshow i
    | METADATA_String s => string_to_DString "!" @@ string_to_DString (show s)
    | METADATA_Named strs => string_to_DString "!{" @@
                              concat_DString (string_to_DString " , ") (map (fun x => string_to_DString "!" @@
                                                                                     string_to_DString x) strs)
                              @@ string_to_DString "}"
    | METADATA_Node mds => string_to_DString "!{"
                            @@ concat_DString (string_to_DString " , ") (map dshow_metadata mds)
                            @@ string_to_DString "}"
    end.

  #[global] Instance dshowMetadata (md : metadata T) : DShow (metadata T) :=
    { dshow := dshow_metadata }.

  Definition show_unnamed_addr (u:unnamed_addr) : string :=
    match u with
    | Unnamed_addr => "unnamed_addr"
    | Local_Unnamed_addr => "local_unnamed_addr"
    end.

  #[global] Instance showUnnamedAddr : Show unnamed_addr :=
    {| show := show_unnamed_addr |}.

  Definition show_tailcall (t:tailcall) : string :=
    match t with
    | Tail => "tail"
    | Musttail => "musttail"
    | Notail => "notail"
    end.

  #[global]
    Instance showTailcall : Show tailcall :=
    {| show := show_tailcall |}.

  Definition dshow_texp (x : texp T) : DString :=
    let '(t, exp) := x in
    dshow t @@ string_to_DString " " @@ dshow_exp true exp.

  Definition show_opt_space {A} (x:option A) : string :=
    match x with
    | Some _ => " "
    | None => ""
    end.

  Definition concat_with_space (c:string) (l:list string) :=
    match l with
    | [] => ""
    | _::_ => (concat c l) ++ " "
    end.

  Definition show_call_arg (x : texp T * list param_attr) : DString :=
    let '(te, atts) := x in
    let '(t, e) := te in
    let attrs := concat_DString (string_to_DString " ") (map dshow atts) @@ string_to_DString " " in
    dshow t @@ string_to_DString  " " @@
    attrs @@ dshow_exp true e.

  #[global] Instance dshowCallArg : DShow (texp T * list param_attr) :=
    { dshow := show_call_arg }.

  Definition dshow_metadata_list (ml : list (metadata T)) := 
    concat_DString (string_to_DString " ") (map dshow_metadata ml).
    
  
  Definition dshow_instr (i : instr T) : DString
    := match i with
       | INSTR_Comment s => string_to_DString "; " @@  string_to_DString s

       | INSTR_Op e => dshow e

       | INSTR_Call fn args anns =>
           let tail := find_option ann_tail anns in
           let fast_math_flags := filter_option ann_fast_math_flag anns in
           let cconv := find_option ann_cconv anns in
           let ret_attrs := filter_option ann_ret_attribute anns in
           let addrspace := find_option ann_addrspace anns in
           let fn_attrs := filter_option ann_fun_attribute anns in
           string_to_DString (show_opt_prefix "" tail) @@ string_to_DString (show_opt_space tail)
             @@ string_to_DString "call " @@
             concat_DString (string_to_DString " ") (map (fun x => string_to_DString (show_fast_math x)) fast_math_flags)
             @@
             list_to_DString (show_opt_list cconv)
             @@
             DList_join (map show_param_attr ret_attrs)
             @@
             list_to_DString (show_opt_list addrspace) 

             @@ string_to_DString " " @@
             dshow_texp fn @@ string_to_DString "(" @@
             concat_DString (string_to_DString ", ") (map show_call_arg args) @@
             string_to_DString ") " @@
             concat_DString (string_to_DString " ") (map (fun x => string_to_DString (show_fn_attr x)) fn_attrs)

       | INSTR_Alloca t anns =>
           let inalloca := match find_option ann_inalloca anns with
                           | Some _ => "inalloca"
                           | None => ""
                           end
           in
           let nb := find_option ann_num_elements anns in
           let align := find_option ann_align anns in
           list_to_DString ["alloca " ; inalloca] @@ dshow t @@ dshow_opt_prefix (string_to_DString ", ") nb @@ string_to_DString (show_opt_prefix ", align " align)

       | INSTR_Load t ptr anns =>
           let volatile := match find_option ann_volatile anns with
                           | Some _ => "volatile"
                           | None => ""
                           end
           in
           let align := find_option ann_align anns in
           let meta := filter_option ann_metadata anns in
           let meta_str := DList_join (map (fun 'ml =>
                                                  string_to_DString ", "
                                                    @@ dshow_metadata_list ml)  meta)
           in
           list_to_DString ["load "; volatile] @@ dshow t @@ string_to_DString ", " @@ dshow_texp ptr @@
           string_to_DString (show_opt_prefix ", align " align) @@
           meta_str

       | INSTR_Store tval ptr anns =>
           let volatile := match find_option ann_volatile anns with
                           | Some _ => "volatile"
                           | None => ""
                           end
           in
           let align := find_option ann_align anns in
           let meta := filter_option ann_metadata anns in
           let meta_str := DList_join (map (fun 'ml =>
                                                  string_to_DString ", "
                                                    @@ dshow_metadata_list ml) meta)
           in
           string_to_DString "store " @@ string_to_DString volatile @@ dshow_texp tval @@
           string_to_DString ", " @@ dshow_texp ptr @@ string_to_DString (show_opt_prefix ", align " align)
                                                        @@ meta_str

       | INSTR_Fence syncscope ordering => let printable_sync := match syncscope with
                                                                 | None => ""
                                                                 | Some x => "[syncscope(""" ++ show x ++ """)]"
                                                                 end in
                                          list_to_DString ["fence " ; printable_sync ] @@
                                            dshow ordering @@
                                            string_to_DString " ; yields void"

       | INSTR_AtomicCmpXchg c => dshow c

       | INSTR_AtomicRMW a => show_atomic_rmw a

       | INSTR_VAArg va_list_and_arg_list t  =>
           string_to_DString "va_arg " @@ dshow va_list_and_arg_list @@ string_to_DString ", " @@ dshow t

       | INSTR_LandingPad => string_to_DString "skipping implementation at the moment"
       end.

  #[global] Instance dshowInstr : DShow (instr T) := { dshow := dshow_instr }.

  #[global] Instance dshowInstrId : DShow instr_id
    := {| dshow i :=
         match i with
         | IId raw => string_to_DString "%" @@ dshow raw
         | IVoid n => string_to_DString "void<" @@ string_to_DString (show n) @@ string_to_DString ">"
         end
       |}.

  Definition dshow_instr_id (inst : instr_id * instr T) : DString
    :=
    let '(iid, i) := inst in
    match iid with
    | IId _ =>
        dshow iid @@ string_to_DString " = " @@ dshow i
    | IVoid n =>
        dshow i
    end.

  #[global] Instance dshowInstrWithId : DShow (instr_id * instr T)
    := {| dshow := dshow_instr_id |}.

  Definition show_tint_literal (t : tint_literal) : string :=
    match t with
    | TInt_Literal sz x => "i" ++ show sz ++ " " ++ show x
    end.

  #[global] Instance showTintLiteral : Show tint_literal :=
    {| show := show_tint_literal |}.

  Definition dshow_terminator (t : terminator T) : DString
    := match t with
       | TERM_Ret v => string_to_DString "ret " @@ dshow_texp v
       | TERM_Ret_void => string_to_DString "ret void"
       | TERM_Br te b1 b2 =>
           string_to_DString "br " @@ dshow_texp te @@
           DList_join [string_to_DString ", label %" ; dshow b1 ; string_to_DString ", label %" ; dshow b2]
       | TERM_Br_1 b => string_to_DString "br label %" @@ dshow b

       | TERM_Switch v def_dest brs => string_to_DString "switch " @@ dshow_texp v @@
                                      string_to_DString ", label %" @@
                                      dshow def_dest @@ string_to_DString " [" @@
                                      fold_left (fun str '(x, y) => str @@ list_to_DString [show x; ", label %"] @@
                                                                   dshow y @@ string_to_DString " ") brs DList_empty @@ string_to_DString "]"

       | TERM_IndirectBr v brs => string_to_DString "indirectbr " @@ dshow_texp v @@
                                   dshow brs

       | TERM_Resume v => string_to_DString "remove " @@ dshow_texp v

       | TERM_Invoke fnptrval args to_label unwind_label =>
           string_to_DString "invoke " @@ dshow fnptrval @@
             string_to_DString "( " @@ dshow args @@ string_to_DString "to label " @@
             dshow to_label @@ string_to_DString "unwind label " @@ dshow unwind_label

       | TERM_Unreachable => string_to_DString "unreachable"
       end.

  #[global] Instance dshowTerminator : DShow (terminator T) := {dshow := dshow_terminator}.

  Definition dshow_code (indent : string) (c : code T) : DString
    := DList_join (map (fun iid => string_to_DString indent @@  dshow_instr_id iid @@ string_to_DString newline) c).

  #[global] Instance dshowCode : DShow (code T) := { dshow := dshow_code "    " }.

  Definition dnewline := string_to_DString newline.

  Definition dshow_block (indent : string) (b : block T) : DString
    :=
    let ind := string_to_DString indent in
    let phis := DList_join (map (fun '(l, p) =>
                                   ind @@
                                     DList_join
                                     [string_to_DString "%" ;
                                      dshow l ;
                                      string_to_DString " = " ;
                                      dshow p ;
                                      dnewline
                              ])
                              (blk_phis b)) in
    let code   := dshow_code indent (blk_code b) in
    let term   := DList_join [ind ; dshow (blk_term b) ; dnewline] in
    DList_join [dshow (blk_id b); string_to_DString ":"; dnewline]
         @@ phis
         @@ code
         @@ term.

  #[global] Instance dshowBlock : DShow (block T) := { dshow := dshow_block  "    " }.

  Definition dshow_typ_instr (typ_instr: T * instr T) : DString :=
    let (t, i) := typ_instr in
    string_to_DString "(" @@ dshow t @@ string_to_DString ", " @@ dshow i @@ string_to_DString ")".

  #[global] Instance dshowTypInstr: DShow (T * instr T) :=
    {|
      dshow := dshow_typ_instr
    |}.

  Definition dshow_arg (arg : local_id * T * list param_attr) : DString
    := let '(i, t, parameter_attributes) := arg in
       dshow t @@
         (match parameter_attributes with
          | [] => string_to_DString ""
          | _ => string_to_DString " " @@ concat_DString (string_to_DString " ") (map dshow (parameter_attributes))
          end) @@ string_to_DString " %" @@ dshow i.

  #[global] Instance dshowArg : DShow (local_id * T * list param_attr) :=
    { dshow := dshow_arg }.

  Definition dshow_arg_list (args : list (local_id * T * list param_attr)) (varargs:bool) : DString
    :=
    let vararg_str :=
      if Nat.eqb (List.length args) 0 then
        (if varargs then string_to_DString "..." else string_to_DString "")
      else
        (if varargs then string_to_DString ", ..." else string_to_DString "")
    in
    let arg_str := concat_DString (string_to_DString ", ") (map dshow args)
    in
    string_to_DString "(" @@ arg_str @@ vararg_str @@ string_to_DString ")".
  
End ShowInstances.

(* TODO: REALLY?!? *)
Fixpoint zip {X Y} (xs : list X) (ys : list Y) : list (X * Y)
  := match xs, ys with
     | [], _ => []
     | _, [] => []
     | (x::xs), (y::ys) => (x, y) :: zip xs ys
     end.

Fixpoint zip3 {X Y Z} (xs : list X) (ys : list Y) (zs : list Z) : list (X * Y * Z)
  := match xs, ys, zs with
     | [], _, _ => []
     | _, [], _ => []
     | _, _, [] => []
     | (x::xs), (y::ys), (z::zs) => (x, y, z) :: zip3 xs ys zs
     end.

(** Return empty string when None *)
(** Adds a space -- is this the right place to do that? *)
Definition maybe_to_string {X} (to_string : X -> string) (ox : option X) :=
  match ox with
  | None => ""
  | Some x => ((to_string x) ++ " ")%string
  end.

Definition maybe_to_dstring {X} (to_string : X -> DString) (ox : option X) :=
  match ox with
  | None => string_to_DString ""
  | Some x => (to_string x) @@ string_to_DString " "
  end.

(** Return empty string when None *)

Definition maybe_show {X} `{Show X} (ox : option X) : string :=
  maybe_to_string show ox.

Definition maybe_dshow {X} `{DShow X} (ox : option X) : DString :=
  maybe_to_dstring dshow ox.

Definition dshow_definition (defn : definition typ (block typ * list (block typ))) : DString
  :=
  let name  := defn.(df_prototype).(dc_name) in
  let ftype := defn.(df_prototype).(dc_type) in
  let '(return_attributes, argument_attributes) := defn.(df_prototype).(dc_param_attrs) in

  match ftype with
  | TYPE_Function ret_t args_t vararg =>
      let arg_names := defn.(df_args) in

      (* Note: if these lists are not equal in length arguments will
         be dropped...  Better to check and spew garbage, as this may
         lead to tricky to catch problems otherwise.  *)
      let arg_length := List.length arg_names in
      if negb (Nat.eqb arg_length (List.length args_t) && (Nat.eqb arg_length (List.length argument_attributes)))
      then string_to_DString "Function """ @@ dshow name @@ string_to_DString """ has mismatched arguments and argument attributes length"
      else
        let args := zip3 arg_names args_t argument_attributes in

        let blocks :=
          let '(b, bs) := df_instrs defn in
          concat_DString dnewline (map dshow (b::bs))
        in

        let ret_attributes := concat_DString (string_to_DString " ") (map (fun x => dshow x) (return_attributes)) @@
        string_to_DString " " in
        let printable_ret_attrs := ret_attributes in

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
            (fun a => concatStr [", align "; show a; " "])
            (dc_align defn.(df_prototype)) in

        let gc := maybe_show (dc_gc defn.(df_prototype)) in

        DList_join [ list_to_DString ["define "; linkage; visibility; dll_storage ; cconv] @@
                       printable_ret_attrs @@ dshow ret_t] @@ string_to_DString " @" @@ dshow name @@
                     dshow_arg_list args vararg @@
                     list_to_DString [section ; align ; gc ; " {"; newline] @@
                     blocks @@
                     list_to_DString ["}";  newline]

  | _ => string_to_DString "Invalid type on function: " @@ dshow name
  end.

#[global] Instance dshowDefinition: DShow (definition typ (block typ * list (block typ))) :=
  {| dshow := dshow_definition |}.

(* Why can I not make show functions implicit?  *)
Definition dshow_declaration (decl: declaration typ) : DString :=
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
          (fun a => concatStr [", align "; show a; " "])
          (dc_align decl) in

      let gc := maybe_show (dc_gc decl) in

      let vararg_str :=
        if Nat.eqb (List.length args_t) 0 then
          (if vararg then "..." else "")
        else
          (if vararg then ", ..." else "")
      in
      string_to_DString
        (concatStr ["declare "; link; vis; dll; cc]) @@
        DList_join [dintersperse (string_to_DString " ") (map dshow ret_attrs)] @@
        string_to_DString " " @@
        dshow ret_t @@ string_to_DString " @" @@ dshow name @@ string_to_DString "(" @@
        dconcat (string_to_DString ", ") (map (fun '(x, y) =>
                                                 DList_join
                                                   [dshow x; string_to_DString " ";
                                                    match y with
                                                    | [] => string_to_DString ""
                                                    | z :: tl => dshow z
                                                    end ])
                       (List.combine args_t args_attrs)) @@
        string_to_DString vararg_str @@
        string_to_DString ")" @@ string_to_DString section @@ string_to_DString align @@ string_to_DString gc
  | _ => string_to_DString "Invalid type on function: " @@ dshow name
  end.

#[global] Instance dshowDeclaration: DShow (declaration typ) :=
  {| dshow := dshow_declaration |}.

Definition dshow_global (g : global typ) : DString :=
  let name  := g.(g_ident) in
  let gtype := g.(g_typ) in
  let linkage := maybe_show (g_linkage g) in
  let visibility := maybe_show (g_visibility g) in
  let dll_storage := maybe_show (g_dll_storage g) in
  let thread_local := maybe_show (g_thread_local_storage g) in
  let g_exp := match g.(g_exp) with
               | None => string_to_DString ""
               | Some e => dshow_exp true e
               end
  in
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
      (fun a => concatStr [", align "; show a; " "])
      (g_align g) in

  DList_join
    [string_to_DString "@"; dshow name; string_to_DString " = ";
     string_to_DString linkage ; string_to_DString visibility;
     string_to_DString dll_storage ; string_to_DString thread_local;
     string_to_DString unnamed_addr; string_to_DString addrspace;
     string_to_DString externally_initialized; string_to_DString g_or_c;
     dshow gtype; string_to_DString " "; g_exp; string_to_DString section ; string_to_DString align
    ].

#[global] Instance dshowGlobal : DShow (global typ) :=
  {| dshow := dshow_global |}.

Definition quoted_dstring (str : string) : DString
  := string_to_DString (show str).

Definition dshow_tle (tle : toplevel_entity typ (block typ * list (block typ))) : DString
  := match tle with
     (*Why is show_definition rather than show being used here*)
     | TLE_Definition defn => dshow defn
     | TLE_Comment msg => string_to_DString ";" @@ quoted_dstring msg (*What if the comment is multiple lines? *)
     | TLE_Target tgt => string_to_DString "target triple = " @@ quoted_dstring tgt
     | TLE_Datalayout layout => string_to_DString "target datalayout = " @@ quoted_dstring layout
     | TLE_Source_filename s => string_to_DString "source_filename = " @@ quoted_dstring s
     | TLE_Declaration decl => dshow decl
     | TLE_Global g => dshow g
     | TLE_Metadata id md => string_to_DString "!" @@ dshow id @@ string_to_DString " = " @@ dshow_metadata md (* Can't use implicit *)
     | TLE_Type_decl id t => DList_join [dshow_ident id ; string_to_DString " = type "; dshow t ]
     | TLE_Attribute_group i attrs =>
         DList_join
           [string_to_DString "attributes #"; string_to_DString (show i); string_to_DString " = { " ;
            dconcat (string_to_DString " ") (map (fun x => string_to_DString (show x)) (attrs)); string_to_DString " }"
           ]
     end.

#[global] Instance dshowTLE: DShow (toplevel_entity typ (block typ  * list (block typ))) :=
  {| dshow := dshow_tle |}.

#[global] Instance dshowProg : DShow (list (toplevel_entity typ (block typ * list (block typ)))) :=
  {| dshow tles := dconcat (dnewline @@ dnewline) (map dshow_tle tles) |}.

Definition show_exp {T : Set} `{DShow T} (b: bool) (v : exp T) : string := show v.
Definition showProg (p: list (toplevel_entity typ (block typ * list (block typ)))) : string := show p.
Definition show_tle (tle : toplevel_entity typ (block typ * list (block typ))) : string := show tle.
Definition show_typ (t : typ) : string := show t.

#[global] Instance showTyp : Show typ :=
  {| show := show_typ |}.
