(**
    Show instances for Vellvm. These serialize Vellvm ASTs into the
    standard format for .ll files. The result of show on a Vellvm
    program should give you a string that can be read by clang.
 *)

From Vellvm Require Import
  LLVMAst
  Utils
  AstLib
  Syntax.CFG
  DynamicTypes
  DList.

From Stdlib Require Import
  List.

Import ListNotations.

Import DList.

From Stdlib Require Import
  ZArith
  String
  Bool.Bool
  Numbers.HexadecimalString
  Numbers.DecimalString
  Strings.Ascii.

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

Fixpoint concat_str_sep (sep:string) (l : list string) : string :=
  match l with
  | nil => ""
  | (h::nil) => h          
  | (h :: t) => h ++ sep ++ (concat_str_sep sep t)
  end.

(*  ------------------------------------------------------------------------- *)

Notation sd := string_to_DString.

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
  dshow p := match p with (a,b) => string_to_DString "(" @@ dshow a @@ sd "," @@ dshow b @@ sd ")" end
|}.

#[global] Instance DShowShow {A} `{DShow A} : Show A :=
{|
  show a := DString_to_string (dshow a);
|}.

Definition dintersperse (sep : DString) (l : list DString) : DString
  := fold_left (fun acc s => if String.eqb "" (DString_to_string acc) then s else acc @@ sep @@ s) l (sd "").

Fixpoint dconcat (sep : DString) (ls : list DString) :=
  match ls with
  | nil => sd EmptyString
  | cons x nil => x
  | cons x xs => x @@ sep @@ dconcat sep xs
  end.

Section StringOps.
  Local Open Scope string.

  Definition intersperse (sep : string) (l : list string) : string
    := fold_left (fun acc s => if String.eqb "" acc then s else acc ++ sep ++ s) l "".

End StringOps.
  

  (*
    - IntDecimal (Pos d)    for 1234
    - IntDecimal (Neg d)    for -1234
    - IntHexadecimal (Pos h) for u0x8000  is 32768
    - IntHexadecimal (Neg h) for s0x8000  is -32768
   *) 
  Definition show_int_syntax (d : int_syntax) : string :=
    match d with
    | Number.IntDecimal d => (NilEmpty.string_of_int d)
    | Number.IntHexadecimal (Hexadecimal.Pos h) => "u0x" ++ (HexadecimalString.NilEmpty.string_of_uint h)
    | Number.IntHexadecimal (Hexadecimal.Neg h) => "s0x" ++ (HexadecimalString.NilEmpty.string_of_uint h)
    end.

  #[global] Instance showIntSyntax : Show int_syntax
    := {| show := show_int_syntax |}.



Section ShowInstances.
  Local Open Scope string.

  Context {T : Set}.
  Context `{DShow T}.

  Definition dshow_raw_id (rid : raw_id) : DString
    := match rid with
       | Name s => sd s
       | Anon i => sd (show i)
       | Raw i  => sd (show i)
       end.

  #[global] Instance dshowRawId : DShow raw_id
    := {| dshow := dshow_raw_id |}.

  Definition dshow_ident (i : ident) : DString
    := match i with
      | ID_Global r => sd "@" @@ dshow_raw_id r
      | ID_Local r  => sd "%" @@ dshow_raw_id r
       end.

  #[global] Instance dshowIdent : DShow ident
    := {| dshow := dshow_ident |}.

  Definition show_floating_point_variant (fp:floating_point_variant) : string :=
    match fp with
    | FP_half => "half"
    | FP_bfloat => "bfloat"
    | FP_float  => "float"
    | FP_double => "double"
    | FP_fp128 => "fp128"
    | FP_x86_fp80 => "x86_fp80"
    | FP_ppc_fp128 => "ppc_fp128"
    end.

  #[global] Instance showFloatingPointVariant : Show floating_point_variant :=
    {| show := show_floating_point_variant |}.
  
  Definition dshow_floating_point_variant (fp:floating_point_variant) : DString :=
    sd (show_floating_point_variant fp).
  
  #[global] Instance dshowFLoatingPointVariant : DShow floating_point_variant 
    := {| dshow := dshow_floating_point_variant |}.
  
  Fixpoint dshow_typ (t : typ) : DString  :=
    match t with
    | TYPE_I sz                 => sd "i" @@ sd (show sz)
    | TYPE_Iptr                 => sd "iptr"
    | TYPE_Pointer (Some t)     => dshow_typ t @@ sd "*"
    | TYPE_Pointer None         => sd "ptr"
    | TYPE_Void                 => sd "void"
    | TYPE_FP fp                => dshow fp
    | TYPE_Label                => sd "label"
    | TYPE_Token                => sd "token"
    | TYPE_Metadata             => sd "metadata"
    | TYPE_X86_mmx              => sd "x86_mmx"
    | TYPE_Array sz t           =>
        list_to_DString ["["; show sz; " x "] @@ dshow_typ t @@ sd "]"
    | TYPE_Function ret args varargs =>
        let varargs_str :=
          if Nat.eqb (List.length args) 0 then
            (if varargs then sd "..." else sd  "")
          else
            (if varargs then sd ", ..." else sd "")
        in dshow_typ ret @@ sd  " (" @@
             concat_DString (sd ", ") (map dshow_typ args) @@ varargs_str @@ sd ")"

    | TYPE_Struct fields        =>
        sd "{" @@
          concat_DString (sd ", ") (map dshow_typ fields) @@
          sd "}"

    | TYPE_Packed_struct fields =>
        sd "<{" @@
          concat_DString (sd ", ") (map dshow_typ fields) @@
          sd "}>"

    | TYPE_Opaque               => sd "opaque"

    | TYPE_Vector sz t          =>
        sd "<" @@
          sd (show sz) @@
          sd " x " @@ dshow_typ t @@
          sd ">"

    | TYPE_Identified id        => dshow id
    end.

  #[global] Instance dshowTyp : DShow typ :=
    {| dshow := dshow_typ |}.

  Definition show_dtyp_base (t : dtyp_base) : string :=
    match t with
    | DTYPE_I sz                 => "i" ++ (show sz)
    | DTYPE_Iptr                 => "iptr"
    | DTYPE_Pointer              => "ptr"
    | DTYPE_Void                 => "void"
    | DTYPE_FP fp                => (show fp)
    | DTYPE_Label                => "label"
    | DTYPE_Token                => "token"
    | DTYPE_Metadata             => "metadata"
    | DTYPE_X86_mmx              => "X86_mmx"
    | DTYPE_Opaque               => "Opaque"
    | DTYPE_B sz                 => "b" ++ (show sz)
    end.
  
  Fixpoint show_dtyp (t : dtyp) : string :=
    match t with
    | DTYPE_Base t => show_dtyp_base t
    | DTYPE_Struct p fields  =>
        if p then
          "<{" ++ (String.concat ", " (map show_dtyp fields)) ++ "}>"
        else
          "{" ++ (String.concat ", " (map show_dtyp fields)) ++ "}"
    | DTYPE_Array false sz t           => "[" ++ (show sz) ++ " x " ++ show_dtyp t ++ "]"
    | DTYPE_Array true sz t          => "<" ++ (show sz) ++ " x " ++ show_dtyp t ++ ">"
    end.

  #[global] Instance dshowDTyp : Show dtyp :=
    {| show := show_dtyp |}.
  
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

  Definition dshow_pair_list {A} `{Show A} (l:list (A*A)) : DString :=
    dconcat (sd ", ") (List.map (fun x => sd (show x)) l).

  Definition show_param_attr (p : param_attr) : DString :=
    match p with
    | PARAMATTR_Zeroext => sd "zeroext"
    | PARAMATTR_Signext => sd "signext"
    | PARAMATTR_Inreg => sd "inreg"
    | PARAMATTR_Byval t => sd "byval(" @@ dshow t @@ sd ")"
    | PARAMATTR_Byref t => sd "byref(" @@ dshow t @@ sd ")"
    | PARAMATTR_Preallocated t => sd "preallocated(" @@ dshow t @@ sd ")"
    | PARAMATTR_Inalloca t => sd "inalloca(" @@ dshow t @@ sd ")"
    | PARAMATTR_Sret t => sd "sret(" @@ dshow t @@ sd ")"
    | PARAMATTR_Elementtype t => sd "elementtype(" @@ dshow t @@ sd ")"
    | PARAMATTR_Align a => sd "align " @@ sd (show a)
    | PARAMATTR_Noalias => sd "noalias"
    | PARAMATTR_Nocapture => sd "nocapture"
    | PARAMATTR_Nofree => sd "nofree"
    | PARAMATTR_Nest => sd "nest"
    | PARAMATTR_Returned => sd "returned"
    | PARAMATTR_Nonnull => sd "nonnull"
    | PARAMATTR_Dereferenceable a => sd "dereferenceable(" @@ sd (show a) @@ sd ")"
    | PARAMATTR_Dereferenceable_or_null a => sd "dereferenceable_or_null(" @@ sd (show a) @@ sd ")"
    | PARAMATTR_Swiftself => sd "swiftself"
    | PARAMATTR_Swiftasync => sd "swiftasync"
    | PARAMATTR_Swifterror => sd "swifterror"
    | PARAMATTR_Immarg => sd "immarg"
    | PARAMATTR_Noundef => sd "noundef"
    | PARAMATTR_Alignstack a => sd "alignstack(" @@ sd (show a)  @@ sd ")"
    | PARAMATTR_Allocalign => sd "allocalign"
    | PARAMATTR_Allocptr => sd "allocptr"
    | PARAMATTR_Readnone => sd "readnone"
    | PARAMATTR_Readonly => sd "readonly"
    | PARAMATTR_Writeonly => sd "writeonly"
    | PARAMATTR_Writable => sd "writable"
    | PARAMATTR_Dead_on_unwind => sd "dead_on_unwind"
    | PARAMATTR_Range t a b => sd "range(" @@ sd (show t)
                                          @@ sd " "
                                          @@ sd (show a) @@ sd ", " 
                                          @@ sd (show b) @@ sd ")"
    | PARAMATTR_Initializes l => sd "initializes(" @@ (dshow_pair_list l) @@ sd ")"
    end.

  #[global] Instance dshowParamAttr : DShow param_attr
    := { dshow := show_param_attr }.

  Definition show_eff '(loc, k) :=
    match loc with
    | LOC_Default => ""
    | LOC_Argmem => "argmem: "
    | LOC_Inaccessiblemem  => "inaccessiblemem: "
    | LOC_Errnomem => "errnomem: "
    end ++
    match k with
    | ACC_None => "none"
    | ACC_Read => "read"
    | ACC_Write => "write"
    | ACC_Readwrite => "readwrite"
    end.
  
  Definition show_fn_attr (f : fn_attr) : string :=
    match f with
    | FNATTR_Alignstack a => "alignstack(" ++ show a ++ ")"
    | FNATTR_Allockind kind => "allockind(" ++ show kind ++ ")"
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
    | FNATTR_Fn_ret_thunk_extern => "fun_ret_thunk_extern"
    | FNATTR_Hot => "hot"
    | FNATTR_Inaccessiblememonly => "inaccessiblememonly"
    | FNATTR_Inaccessiblemem_or_argmemonly => "inaccessiblemem_or_argmemonly"
    | FNATTR_Inlinehint => "inlinehint"
    | FNATTR_Jumptable => "jumptable"
    | FNATTR_Minsize => "minsize"
    | FNATTR_Naked => "naked"
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
    | FNATTR_Readnone => "readnone"
    | FNATTR_Readonly => "readonly"
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
    | FNATTR_Tls_load_hoist => """tls-load-hoist"""
    | FNATTR_Uwtable so  =>
        match so with
        | None => "uwtable"
        | Some sync => if sync then "uwtable(sync)" else "uwtable(async)"
        end
    | FNATTR_Nocf_check => "nocf_check"
    | FNATTR_Shadowcallstack => "shadowcallstack"
    | FNATTR_Mustprogress => "mustprogress"
    | FNATTR_Vscale_range min max  =>
        match max with
        | None => "vscale_range(" ++ show min ++ ")"
        | Some m => "vscale_range(" ++ show min ++ "," ++ show m ++ ")"
        end
    | FNATTR_String s => """" ++ s ++ """"  (* "no-see" *)
    | FNATTR_Key_value kv => """" ++ fst kv ++ """=" ++ """" ++ snd kv ++ """" (* "unsafe-fp-math"="false" *)
    | FNATTR_Attr_grp g => "#" ++ show g
    | FNATTR_Memory l => "memory(" ++ concat_str_sep ", " (map show_eff l ) ++ ")"
    | FNATTR_UNKNOWN s => s
    end.

  #[global] Instance showFnAttr : Show fn_attr
    := {| show := show_fn_attr |}.

  Definition show_thread_local_storage (tls : thread_local_storage) : string :=
    match tls with
    | TLS_NONE => "thread_local"  (* should never be printed *)
    | TLS_Localdynamic => "thread_local(localdynamic)"
    | TLS_Initialexec => "thread_local(initialexec)"
    | TLS_Localexec => "thread_local(localexec)"
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

  Definition show_op_nuw_nsw (op : string) (nuw : bool) (nsw : bool) :=
    concatStr
      [ op;
        if nuw then " nuw" else "";
        if nsw then " nsw" else ""
      ].

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
       | Or b    => if b then "or disjoint" else "or"
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

  (* Definition double_to_hex_string (f : float) : string *)
  (*   := "0x" ++ NilEmpty.string_of_uint (N.to_hex_uint (Z.to_N (@unsigned 64 (Float.to_bits f)))). *)

  (* Definition float_to_hex_string (f : float32) : string *)
  (*   := double_to_hex_string (Float32.to_double f). *)

  (* #[global] Instance showFloat : Show float *)
  (*   := {| show := double_to_hex_string |}. *)

  (* #[global] Instance showFloat32 : Show float32 *)
  (*   := {| show := float_to_hex_string |}. *)

  (* Definition show_int {sz} (x : @bit_int sz) : string *)
  (*   := show (unsigned x). *)

  (* #[global] Instance Show_Int {sz} : Show (@bit_int sz) *)
  (*   := {| show := show_int|}. *)

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

  Definition show_pure_conversion (ct : pure_conversion) : string :=
    match ct with
    | Trunc nuw nsw => show_op_nuw_nsw "trunc" nuw nsw
    | Zext nneg => "zext" ++ (if nneg then " nneg" else "")
    | Sext => "sext"
    | Fptrunc flags => "fptrunc" ++ concatStr (List.map (fun f => " " ++ (show_fast_math f)) flags)
    | Fpext flags => "fpext" ++ concatStr (List.map (fun f => " " ++ (show_fast_math f)) flags)
    | Uitofp nneg => "uitofp" ++ (if nneg then " nneg" else "")
    | Sitofp => "sitofp"
    | Fptoui => "fptoui"
    | Fptosi => "fptosi"
    end.      

  #[global] Instance ShowPureConversion : Show pure_conversion :=
    {| show := show_pure_conversion |}.
  
  Definition show_impure_conversion (ct : impure_conversion) : string :=
    match ct with
    | Inttoptr => "inttoptr"
    | Ptrtoint => "ptrtoint"
    | Ptrtoaddr => "ptrtoaddr"                   
    | Addrspacecast => "addrspacecast"
    end.

  #[global] Instance ShowImpureConversion : Show impure_conversion :=
    {| show := show_impure_conversion |}.

  Definition show_conversion_type (ct : conversion_type) : string
    := match ct with
       | CONV_Bitcast => "bitcast"
       | CONV_Pure ct => show ct
       | CONV_Impure ct => show ct
       end.

  #[global] Instance ShowConversionType : Show conversion_type
    := {| show := show_conversion_type |}.

  (* SAZ: TODO - revisit c_string parsing to do better than this *)
  Definition ex_to_nat (ex : exp T) : nat :=
    match ex with
    |EXP_Integer x => (Z.to_nat (Z.of_num_int x))
    | _ => 0 (* This is arbitrary, it's never going to hit this case anyway *)
    end.


  Definition ex_to_int (ex : exp T) : Z :=
    match ex with
    |EXP_Integer x => Z.of_num_int x
    | _ => 0%Z (* This is arbitrary, it's never going to hit this case anyway *)
    end.

  Definition show_c_string (ex : exp T) : string :=
    let n : nat := ex_to_nat ex in
    let x : Z := ex_to_int ex in
    if ((n <? 32) || (126 <? n))%nat then (
        let conversion :=  HexadecimalString.NilEmpty.string_of_uint (N.to_hex_uint (Z.to_N  x)) in
        if ((length (conversion)) =? (Z.to_nat 1))%nat then  "\0" ++ conversion
        else "\" ++ conversion
      )
    (*Special case for decimal 34/hex 22*)
    else if (n =? 34)%nat then "\22"
    (*Special case for decimal 92/hex 5C*)
    else if (n =? 92)%nat then "\\"
         else (string_of_list_ascii ((ascii_of_nat n) :: [])).

  Definition dshow_c_string (ex : exp T) : DString :=
    sd (show_c_string ex).
    
  (* Definition is_op (e : exp T) : bool := *)
  (*   match e with *)
  (*   | EXP_Ident _ *)
  (*   | EXP_Integer _ => false *)
  (*   | EXP_Float _ =>  false *)
  (*   | EXP_Bool _ =>     false *)
  (*   | EXP_Null =>      false *)
  (*   | EXP_Zero_initializer =>    false *)
  (*   (* see notes on cstring on LLVMAst.v *) *)
  (*   (* I'm using string_of_list_ascii bc I couldn't find any other function that converted asciis to strings  *) *)
  (*   | EXP_Cstring elts =>     false *)
  (*   | EXP_Undef =>         false *)
  (*   | EXP_Struct fields =>    false *)
  (*   | EXP_Packed_struct fields =>     false *)
  (*   | EXP_Array t elts =>               false *)
  (*   | EXP_Vector t elts =>        false *)
  (*   | EXP_Asm _ _ _ _ _ _ => false *)
  (*   | EXP_Metadata _ => false *)
  (*   | _ => true *)
  (*   end. *)

  Definition add_parens (b : bool) (ds : DString) : DString :=
    if b then sd "(" @@ ds @@ sd ")" else ds.

  Definition dshow_bool (b : bool) (s : string) : DString :=
    if b then (sd s) else DList_empty.


  Definition show_float_hex_type (ht : float_hex_type) : string :=
    match ht with
    | FH_X => "0x"
    | FH_K => "0xK"
    | FH_L => "0xL"
    | FH_M => "0xM"
    | FH_H => "0xH"
    | FH_R => "0xR"
    end.
  
  Definition show_float_syntax (f : float_syntax) : string :=
    match f with
    | FS_decimal (Decimal.Decimal i f) => (DecimalString.NilEmpty.string_of_int i) ++ "." ++ (DecimalString.NilEmpty.string_of_uint f)
    | FS_decimal (Decimal.DecimalExp i f e) => (DecimalString.NilEmpty.string_of_int i) ++ "." ++ (DecimalString.NilEmpty.string_of_uint f) ++ "e" ++
                                                (DecimalString.NilEmpty.string_of_int e)
    | FS_hex ht u => (show_float_hex_type ht) ++ (HexadecimalString.NilEmpty.string_of_uint u)
    end.

  #[global] Instance showFloatSyntax : Show float_syntax
    := {| show := show_float_syntax |}.                                            

  Definition fast_math_list_to_dstring (fmath : list fast_math) : DString :=
    sd
      match fmath with
      | nil => " "
      | _ =>  " " ++ concat " " (map (fun x => show x) fmath) ++  " "
      end.
  
  Fixpoint dshow_exp (b: bool) (v : exp T) : DString :=
    let comma_sep vals :=
      concat_DString (sd ", ")
        (map (fun '(ty, ex) =>
                DList_join [dshow ty ; sd " "] @@
                  dshow_exp false ex) vals)
    in
    match v with
    | EXP_Ident id => dshow id
    | EXP_Integer x => sd (show x)
    | EXP_Float f => sd (show f)
    | EXP_Bool b => sd (show b)
    | EXP_Null => sd "null"
    | EXP_Zero_initializer => sd "zeroinitializer"
    (* see notes on cstring on LLVMAst.v *)
    (* I'm using string_of_list_ascii bc I couldn't find any other function that converted asciis to strings  *)
    | EXP_Cstring elts => sd "c" @@ sd """" @@
                           DList_join (map (fun '(ty, ex) => (dshow_c_string ex)) elts) @@ sd  """"

    | EXP_Undef => sd "undef"

    | EXP_Poison => sd "poison"

    | EXP_Struct fields =>
        sd "{" @@ comma_sep fields @@ sd "}"

    | EXP_Packed_struct fields =>
        sd "<{" @@ comma_sep fields @@ sd "}>"

    | EXP_Array t elts =>
        sd "[" @@ comma_sep elts @@ sd "]"

    | EXP_Vector t elts =>
        sd "<" @@ comma_sep elts @@ sd ">"

    | OP_IBinop iop t v1 v2 =>
        let second_expression :=
          if b
          then dshow t @@ sd " " @@ dshow_exp true v2
          else dshow_exp true v2
       in sd (show iop) @@ sd " " @@ add_parens b (dshow t @@ sd " " @@ dshow_exp true v1 @@ sd ", " @@ second_expression)

    | OP_ICmp s cmp t v1 v2 =>
        let second_expression :=
          if b
          then dshow t @@ sd " " @@ dshow_exp true v2
          else dshow_exp true v2
        in
        let ss :=
          if s then "samesign " else ""
        in
        list_to_DString ["icmp " ; ss; show cmp ; " "] @@ add_parens b (dshow t @@ sd " " @@ dshow_exp true v1 @@ sd ", " @@ second_expression)

    | OP_FBinop fop fmath t v1 v2 =>
        let fmath_string := fast_math_list_to_dstring fmath in
        list_to_DString [show fop ; " "] @@ add_parens b (fmath_string @@ dshow t @@ sd " " @@  dshow_exp true v1 @@ sd ", " @@ dshow_exp true v2)

    | OP_Fneg fmath v =>
        let fmath_string := fast_math_list_to_dstring fmath in
        let (t, exp) := v in
        list_to_DString ["fneg" ; " "] @@ add_parens b (fmath_string @@ dshow t @@ sd " " @@  dshow_exp true exp)

                        
    | OP_FCmp cmp t v1 v2 =>
        sd "fcmp " @@ add_parens b (list_to_DString [show cmp ; " "] @@ dshow t @@ sd " " @@ dshow_exp true v1 @@
                                                 sd ", " @@ dshow_exp true v2)

    | OP_Conversion conv t_from v t_to => list_to_DString [show conv ; " "] @@ add_parens b (dshow t_from @@ sd " " @@ dshow_exp true v @@
                                                                                             sd " to " @@ dshow t_to)

    | OP_GetElementPtr t ptrval idxs =>
        let (tptr, exp) := ptrval in
        sd "getelementptr " @@ add_parens b (dshow t @@ sd ", " @@ dshow tptr @@ sd " " @@ dshow_exp true exp @@
                                                              fold_left (fun str '(ty, ex) => str @@ sd ", " @@ dshow ty @@ sd " " @@ dshow_exp true ex) idxs DList_empty)

    | OP_ExtractElement vec idx =>
        let (tptr, exp) := vec in
        let (tidx, iexp) := idx in
        sd "extractelement " @@ add_parens b (dshow tptr @@ sd " " @@ dshow_exp true exp @@ sd ", " @@ dshow tidx @@ sd " " @@  dshow_exp true iexp)

    | OP_InsertElement vec elt idx =>
        let (tptr, exp) := vec in
        let (telt, eexp) := elt in
        let (tidx, iexp) := idx in
        sd "insertelement " @@ add_parens b (dshow tptr @@ sd " " @@ dshow_exp true exp @@ sd ", " @@ dshow telt @@ sd " " @@
                                                          dshow_exp true eexp @@ sd ", " @@ dshow tidx @@ sd " " @@ dshow_exp true iexp)

    | OP_ShuffleVector vec1 vec2 idxmask =>
        let (type1, expression1) := vec1 in
        let (type2, expression2) := vec2 in
        let (type3, expression3) := idxmask in
        sd "shufflevector " @@ add_parens b (dshow type1 @@ dshow_exp true expression1 @@ sd ", " @@ dshow type2 @@ dshow_exp true expression2 @@
                                                              sd ", " @@ dshow type3 @@ dshow_exp true expression3)
    (* This one, extractValue *)
    | OP_ExtractValue vec idxs =>
        let (tptr, exp) := vec in
        sd "extractvalue " @@ add_parens b (dshow tptr @@ sd " " @@ dshow_exp true exp @@ sd ", " @@
                                                         concat_DString (sd ", ") (map (fun x => sd (show x)) idxs))


    | OP_InsertValue vec elt idxs =>
        let (tptr, exp) := vec in
        let (telt, eexp) := elt in
        sd "insertvalue " @@ add_parens b (dshow tptr @@ sd " " @@ dshow_exp false exp @@ sd ", " @@ dshow telt @@ sd " " @@
                                                            dshow_exp false eexp @@ sd ", " @@ concat_DString (sd ", ") (map (fun x => sd (show x)) idxs))

    | OP_Select (tc, cnd) (t1, v1) (t2, v2) =>
        sd "select "  @@ add_parens b (dshow tc @@ sd " " @@ dshow_exp true cnd @@ sd ", " @@ dshow t1 @@ sd " " @@
                                                    dshow_exp true v1  @@ sd ", " @@ dshow t2 @@ sd " " @@  dshow_exp true v2)

    | OP_Freeze (ty, ex) => sd "freeze " @@ add_parens b (dshow ty @@ sd " " @@ dshow_exp true ex)

    | EXP_Asm sideffect alignstack inteldialect unwind template operand_constraints =>
        sd "asm "
          @@ (dshow_bool sideffect "sideeffect ")
          @@ (dshow_bool alignstack "alignstack ")
          @@ (dshow_bool inteldialect "inteldialect ")
          @@ (dshow_bool unwind "unwind ")
          @@ sd """" @@ sd template @@ sd """, "
          @@ sd """" @@ sd operand_constraints @@ sd """"
    | EXP_Metadata m => (dshow_metadata m)
    | EXP_Splat elt =>
        let (tp, exp) := elt in
        sd "splat (" @@ dshow tp @@ sd " " @@ dshow_exp false exp @@ sd ")"
    end
  with dshow_metadata (md : metadata T)  : DString :=
         match md with
    | METADATA_Null => sd "null"
    | METADATA_Const tv => let '(t,e) := tv in (dshow t) @@ sd " " @@ dshow_exp false e
    | METADATA_Id i => sd "!" @@ dshow i
    | METADATA_Node mds => sd "!{"
                            @@ concat_DString (sd " , ") (map dshow_metadata mds)
                            @@ sd "}"
    | METADATA_Pair md1 md2 => dshow_metadata md1 @@ sd " " @@ dshow_metadata md2
    | METADATA_Debug ds s => sd ("!DI" ++ ds ++ "(" ++ s ++ ")")
    (* File info never gets printed *)                                    
    | METADATA_File_info _ => DList_empty
    end.
  
  #[global] Instance dshowExp : DShow (exp T) :=
    {| dshow := dshow_exp false |}.

  #[global] Instance dshowMetadata (md : metadata T) : DShow (metadata T) :=
    { dshow := dshow_metadata }.
  
  #[global] Instance dshowTExp : DShow (texp T) :=
    {| dshow te := let '(t, e) := te in dshow t @@ sd " " @@ dshow e |}.

  Definition show_phi_block (p : block_id * exp T) : DString :=
    let '(bid, e) := p in
    sd "[ " @@ dshow_exp true e @@ list_to_DString [", "; "%"] @@ dshow bid @@ sd " ]".

  #[global] Instance dshowPhi : DShow (phi T)
    := {| dshow p :=
         let '(Phi t phis) := p in
         DList_join [sd "phi " ; dshow t ; sd " "] @@
           concat_DString (sd ", ") (map show_phi_block phis)
       |}.

  Definition show_opt_prefix {A} `{Show A} (prefix : string) (ma : option A) : string
    := match ma with
       | None   => ""
       | Some a => prefix ++ show a
       end.

  Definition dshow_opt_prefix {A} `{DShow A} (prefix : DString) (ma : option A) : DString
    := match ma with
       | None   => sd ""
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

  Definition show_ordering (o : ordering) : string :=
      match o with
      |Unordered => "unordered"
      |Monotonic => "monotonic"
      |Acquire => "acquire"
      |Release => "release"
      |Acq_rel => "acq_rel"
      |Seq_cst => "seq_cst"
      end.

  #[global] Instance dshowOrdering : DShow (ordering)
    := {| dshow := fun o => sd (show_ordering o) |}.

  Definition show_cmpxchg (c : cmpxchg T) : DString :=
    let p_weak :=
      sd
        match c.(c_weak) with
        |None => ""
        |Some _ => "weak "
        end in
    let p_volatile :=
      sd
        match c.(c_volatile) with
        |None => ""
        |Some x => "volatile "
        end in
    let p_syncscope :=
      sd
        match c.(c_syncscope) with
        |None => ""
        |Some x => "syncscope(" ++ show x ++ ") "
        end in
    let p_align :=
      sd
        match c.(c_align) with
        |None => ""
        |Some x => ", align " ++ show x
        end in

    DList_join
      [sd "cmpxchg ";
       p_weak;
       p_volatile;
       dshow c.(c_ptr);
       sd ", ";
       dshow c.(c_cmp);
       sd ", " ;
       dshow c.(c_new);
       sd " ";
       p_syncscope;
       dshow c.(c_success_ordering);
       sd " ";
       dshow c.(c_failure_ordering);
       p_align
      ].

  #[global] Instance dshowCmpxchg : DShow (cmpxchg T)
    := {| dshow := show_cmpxchg |}.

  Definition show_a_rmw_operation (a :  atomic_rmw_operation) : string :=
    match a with
    | Axchg => "xchg"
    | Aadd  => "add"
    | Asub => "sub"
    | Aand => "and"
    | Anand => "nand"
    | Aor  => "or"
    | Axor => "xor"
    | Amax => "max"
    | Amin => "min"
    | Aumax => "umax"
    | Aumin => "umin"
    | Afadd => "fadd"
    | Afsub => "fsub"
    | Afmax => "fmax"
    | Afmin => "fmin"
    | Afmaximum => "fmaximum"
    | Afminimum => "fminimum"
    | Auinc_wrap => "uinc_wrap"
    | Audec_wrap => "udec_wrap"
    | Ausub_cond => "usub_cond"
    | Ausub_sat => "usub_sat"
    end.

  #[global] Instance showARmwOperation : Show (atomic_rmw_operation)
    := {| show := show_a_rmw_operation |}.

  Definition show_atomic_rmw (a : atomicrmw T) : DString :=
    let p_volatile := match a.(a_volatile) with
                      |None => ""
                      |Some _ => "volatile "
                      end in
    let p_syncscope := match a.(a_syncscope) with
                       |None => ""
                       |Some x => "syncscope(" ++ show x ++ ") "
                       end in

    let p_align := match a.(a_align) with
                   |None => ""
                   |Some x => ", align " ++ show x
                   end in

    DList_join
      [sd "atomicrmw ";
       sd p_volatile;
       sd (show a.(a_operation));
       sd " ";
       dshow a.(a_ptr);
       sd ", ";
       dshow a.(a_val);
       sd " ";
       sd p_syncscope;
       dshow a.(a_ordering);
       sd p_align].

  #[global] Instance showAtomicrmw : DShow (atomicrmw T)
    := {| dshow := show_atomic_rmw |}.

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
    dshow t @@ sd " " @@ dshow_exp true exp.

  Definition show_opt_space {A} (x:option A) : string :=
    match x with
    | Some _ => " "
    | None => ""
    end.

  Definition show_call_arg (x : texp T * list param_attr) : DString :=
    let '(te, atts) := x in
    let '(t, e) := te in
    let attrs := concat_DString (sd " ") (map dshow atts) @@ sd " " in
    dshow t @@ sd  " " @@
    attrs @@ dshow_exp true e.

  #[global] Instance dshowCallArg : DShow (texp T * list param_attr) :=
    { dshow := show_call_arg }.

  Definition dshow_metadata_list (ml : list (metadata T)) := 
    concat_DString (sd " ") (map dshow_metadata ml).
    
  Definition dnewline := sd newline.

  Definition dshow_clause (c : landingpad_clause) : DString :=
    match c with
    | CATCH t => (sd "catch ") @@ dshow_texp t @@ dnewline
    | FILTER t => (sd "filter ") @@ dshow_texp t @@ dnewline
    end.

(*
operand bundle set ::= '[' operand bundle (, operand bundle )* ']'
operand bundle ::= tag '(' [ bundle operand ] (, bundle operand )* ')'
bundle operand ::= SSA value | metadata string
tag ::= string constant
 *)

  Definition show_syncscope str : string := "syncscope(""" ++ str ++ """)".

  Definition ann_str {A B} (l : list A) (k:A -> option B) (to_str : B -> string) : string :=
  match find_option k l with
  | None => ""
  | Some b => to_str b
  end.
  
  Definition show_operand (o:operand) : DString :=
    match o with
    | SSA_value t => dshow_texp t
    | Metadata_string m => dshow_metadata m
    end.
  
  Definition show_operand_bundle (ob:operand_bundle) : DString :=
    (sd ("""" ++ ob_tag ob ++ """("))
      @@
      concat_DString (sd ", ") (map show_operand (ob_ops ob))
      @@
      sd (")").
  
  Definition dshow_operand_bundles (obs : list (@operand_bundle T)) : DString :=
    match obs with
    | nil =>  DList_empty
    | _::_ => sd "[" @@ concat_DString (sd ", ") (map show_operand_bundle obs) @@ sd "]"
    end.
  
  Definition dshow_instr (i : instr T) : DString
    := match i with
       | INSTR_Comment s => sd "; " @@  sd (s ++ "\n") (* include the newline *) 

       | INSTR_Op e => dshow e

       | INSTR_Call fn args anns obs =>
           let tail := find_option ann_tail anns in
           let fast_math_flags := filter_option ann_fast_math_flag anns in
           let cconv := find_option ann_cconv anns in
           let ret_attrs := filter_option ann_ret_attribute anns in
           let addrspace := find_option ann_addrspace anns in
           let fn_attrs := filter_option ann_fun_attribute anns in
           sd (show_opt_prefix "" tail) @@ sd (show_opt_space tail)
             @@ sd "call " @@
             concat_DString (sd " ") (map (fun x => sd (show_fast_math x)) fast_math_flags)
             @@
             list_to_DString (show_opt_list cconv)
             @@
             DList_join (map show_param_attr ret_attrs)
             @@
             list_to_DString (show_opt_list addrspace) 

             @@ sd " " @@
             dshow_texp fn @@ sd "(" @@
             concat_DString (sd ", ") (map show_call_arg args) @@
             sd ") " @@
             concat_DString (sd " ") (map (fun x => sd (show_fn_attr x)) fn_attrs)
             @@
             dshow_operand_bundles obs 
             
       | INSTR_Alloca t anns =>
           let inalloca := ann_str anns ann_inalloca (fun _ => "inalloca") in 
           let nb := find_option ann_num_elements anns in
           let align := find_option ann_align anns in
           list_to_DString ["alloca " ; inalloca] @@ dshow t @@ dshow_opt_prefix (sd ", ") nb @@ sd (show_opt_prefix ", align " align)

       | INSTR_Load t ptr anns =>
           let atomic := ann_str anns ann_atomic (fun _ => "atomic") in
           let volatile := ann_str anns ann_volatile (fun _ => "volatile") in
           let ss := ann_str anns ann_syncscope show_syncscope in
           let ord := ann_str anns ann_ordering show_ordering in
           let align := find_option ann_align anns in
           let meta := filter_option ann_metadata anns in
           let meta_str := DList_join (map (fun 'ml =>
                                                  sd ", "
                                                    @@ dshow_metadata_list ml)  meta)
           in
           concat_DString (sd " ") (map sd ["load"; atomic; volatile]) @@ (sd " ") @@
           dshow t @@ sd ", " @@ dshow_texp ptr @@
           concat_DString (sd " ") (map sd [ss; ord]) @@                
           sd (show_opt_prefix ", align " align) @@
           meta_str

       | INSTR_Store t ptr anns =>
           let atomic := ann_str anns ann_atomic (fun _ => "atomic") in
           let volatile := ann_str anns ann_volatile (fun _ => "volatile") in
           let ss := ann_str anns ann_syncscope show_syncscope in
           let ord := ann_str anns ann_ordering show_ordering in
           let align := find_option ann_align anns in
           let meta := filter_option ann_metadata anns in
           let meta_str := DList_join (map (fun 'ml =>
                                                  sd ", "
                                                    @@ dshow_metadata_list ml)  meta)
           in
           concat_DString (sd " ") (map sd ["store"; atomic; volatile]) @@ (sd " ") @@
           dshow_texp t @@ sd ", " @@ dshow_texp ptr @@
           concat_DString (sd " ") (map sd [ss; ord]) @@                
           sd (show_opt_prefix ", align " align) @@
           meta_str

       | INSTR_Fence syncscope ordering => let printable_sync := match syncscope with
                                                                 | None => ""
                                                                 | Some x => "[syncscope(""" ++ show x ++ """)]"
                                                                 end in
                                          list_to_DString ["fence " ; printable_sync ] @@
                                            dshow ordering @@
                                            sd " ; yields void"

       | INSTR_AtomicCmpXchg c => dshow c

       | INSTR_AtomicRMW a => show_atomic_rmw a

       | INSTR_VAArg va_list_and_arg_list t  =>
           sd "va_arg " @@ dshow va_list_and_arg_list @@ sd ", " @@ dshow t

       | INSTR_LandingPad t b cs =>
           (sd "landingpad ") @@ dshow t @@ dnewline @@
             (if b then sd "cleanup " else DList_empty)
             @@
             DList_join (map dshow_clause cs)
       end.

  #[global] Instance dshowInstr : DShow (instr T) := { dshow := dshow_instr }.

  Definition dshow_instr_id (id:instr_id) : DString :=
    match id with
    | IId rid =>
        sd "%" @@ dshow rid @@ sd " = "
    | IVoid n =>
        DList_empty
    end.

  #[global] Instance dshowInstrId : DShow instr_id
    := {| dshow := dshow_instr_id |}.

  Fixpoint remove_file_info (md : list (metadata T)) : list (metadata T) :=
    match md with
    | [] => []
    | m::rest => if is_METADATA_File_info m then remove_file_info rest else
                 m::(remove_file_info rest)
    end.
  
  Definition dshow_metadata_suffix (md : list (metadata T)) : DString :=
    let md' := remove_file_info md in
    match md' with
    | [] => DList_empty
    | _ => DList_join (map (fun m => sd ", " @@ (dshow_metadata m)) md')
    end.
  
  Definition dshow_id_instr_metadata (inst : instr_id * instr T * list (metadata T)) : DString :=
    let '(iid, i, md) := inst in
    (dshow_instr_id iid)
      @@
      dshow i
      @@
      (dshow_metadata_suffix md)
  .

  Definition dshow_id_phi_metadata (inst : local_id * phi T * list (metadata T)) : DString :=
    let '(iid, p, md) := inst in
    sd "%" @@ dshow iid @@ sd " = "
       @@
       dshow p
       @@
       (dshow_metadata_suffix md)
     .
    
  Definition show_tint_literal (t : tint_literal) : string :=
    match t with
    | TInt_Literal sz x => "i" ++ show sz ++ " " ++ show x
    end.

  #[global] Instance showTintLiteral : Show tint_literal :=
    {| show := show_tint_literal |}.

  Definition dshow_terminator (t : terminator T) : DString
    := match t with
       | TERM_Ret v => sd "ret " @@ dshow_texp v
                         
       | TERM_Ret_void => sd "ret void"
                            
       | TERM_Br te b1 b2 =>
           sd "br " @@ dshow_texp te @@
           DList_join [sd ", label %" ; dshow b1 ; sd ", label %" ; dshow b2]

       | TERM_Br_1 b => sd "br label %" @@ dshow b

       | TERM_Switch v def_dest brs => sd "switch " @@ dshow_texp v @@
                                      sd ", label %" @@
                                      dshow def_dest @@ sd " [" @@
                                      fold_left (fun str '(x, y) => str @@ list_to_DString [show x; ", label %"] @@
                                                                   dshow y @@ sd " ") brs DList_empty @@ sd "]"

       | TERM_IndirectBr v brs => sd "indirectbr " @@ dshow_texp v @@
                                   dshow brs

       | TERM_Resume v => sd "resume " @@ dshow_texp v

       | TERM_Invoke fn args to_label unwind_label anns obs =>
           let tail := find_option ann_tail anns in
           let fast_math_flags := filter_option ann_fast_math_flag anns in
           let cconv := find_option ann_cconv anns in
           let ret_attrs := filter_option ann_ret_attribute anns in
           let addrspace := find_option ann_addrspace anns in
           let fn_attrs := filter_option ann_fun_attribute anns in
             sd "invoke "
             @@
             concat_DString (sd " ") (map (fun x => sd (show_fast_math x)) fast_math_flags)
             @@
             list_to_DString (show_opt_list cconv)
             @@
             DList_join (map show_param_attr ret_attrs)
             @@
             list_to_DString (show_opt_list addrspace) 
             
             @@ sd " " @@
             dshow_texp fn @@ sd "(" @@
             concat_DString (sd ", ") (map show_call_arg args) @@
             sd ") " @@
             concat_DString (sd " ") (map (fun x => sd (show_fn_attr x)) fn_attrs)
             @@
             sd "to label %" @@ dshow to_label @@ sd " " @@
             sd "unwind label %" @@ dshow unwind_label
             @@
             dshow_operand_bundles obs 

             
       | TERM_Unreachable => sd "unreachable"
       end.

  #[global] Instance dshowTerminator : DShow (terminator T) := {dshow := dshow_terminator}.

  
  Definition dshow_id_terminator_metadata (inst : instr_id * terminator T * list (metadata T)) : DString :=
    let '(iid, t, md) := inst in
    dshow_instr_id iid
       @@
       dshow t
       @@
       (dshow_metadata_suffix md)
  .

  Definition dshow_lines {A} (indent:DString) (dshow_A : A -> DString) (lines : list A) : DString :=
    DList_join (map (fun a => indent @@ dshow_A a @@ dnewline) lines).
     
  Definition dshow_block (indent : string) (b : block T) : DString :=
    let ind := sd indent in
    let phis := dshow_lines ind dshow_id_phi_metadata (blk_phis b) in
    let code := dshow_lines ind dshow_id_instr_metadata (blk_code b) in
    let term := dshow_lines ind dshow_id_terminator_metadata [(blk_term b)] in
    DList_join [dshow (blk_id b); sd ":"; dnewline]
         @@ phis
         @@ code
         @@ term.

  #[global] Instance dshowBlock : DShow (block T) := { dshow := dshow_block  "    " }.

  Definition dshow_typ_instr (typ_instr: T * instr T) : DString :=
    let (t, i) := typ_instr in
    sd "(" @@ dshow t @@ sd ", " @@ dshow i @@ sd ")".

  #[global] Instance dshowTypInstr: DShow (T * instr T) :=
    {|
      dshow := dshow_typ_instr
    |}.

  Definition dshow_arg (arg : local_id * T * list param_attr) : DString
    := let '(i, t, parameter_attributes) := arg in
       dshow t @@
         (match parameter_attributes with
          | [] => sd ""
          | _ => sd " " @@ concat_DString (sd " ") (map dshow (parameter_attributes))
          end) @@ sd " %" @@ dshow i.

  #[global] Instance dshowArg : DShow (local_id * T * list param_attr) :=
    { dshow := dshow_arg }.

  Definition dshow_arg_list (args : list (local_id * T * list param_attr)) (varargs:bool) : DString
    :=
    let vararg_str :=
      if Nat.eqb (List.length args) 0 then
        (if varargs then sd "..." else sd "")
      else
        (if varargs then sd ", ..." else sd "")
    in
    let arg_str := concat_DString (sd ", ") (map dshow args)
    in
    sd "(" @@ arg_str @@ vararg_str @@ sd ")".
  
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
  | None => sd ""
  | Some x => (to_string x) @@ sd " "
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
      then sd "Function """ @@ dshow name @@ sd """ has mismatched arguments and argument attributes length"
      else
        let args := zip3 arg_names args_t argument_attributes in

        let blocks :=
          let '(b, bs) := df_instrs defn in
          concat_DString dnewline (map dshow (b::bs))
        in

        let ret_attributes := concat_DString (sd " ") (map (fun x => dshow x) (return_attributes)) @@
        sd " " in
        let printable_ret_attrs := ret_attributes in

        let linkage := maybe_show (dc_linkage defn.(df_prototype)) in
        let visibility := maybe_show (dc_visibility defn.(df_prototype)) in
        let dll_storage := maybe_show (dc_dll_storage defn.(df_prototype)) in
        let cconv := maybe_show (dc_cconv defn.(df_prototype)) in

        let section :=
          maybe_to_string
            (fun s => concatStr ["section """; s; """ "])
            (dc_section defn.(df_prototype))
        in
        let align :=
          maybe_to_string
            (fun a => concatStr ["align "; show a; " "])
            (dc_align defn.(df_prototype))
        in
        let gc := maybe_show (dc_gc defn.(df_prototype))
        in
        let personality :=
          maybe_to_string
            (fun t => concatStr [" personality "; show t; " "])
            (dc_personality defn.(df_prototype))
        in


        DList_join [ list_to_DString ["define "; linkage; visibility; dll_storage ; cconv] @@
                       printable_ret_attrs @@ dshow ret_t] @@ sd " @" @@ dshow name @@
                     dshow_arg_list args vararg @@
                     list_to_DString [section ; align ; gc ; personality ; " {"; newline] @@
                     blocks @@
                     list_to_DString ["}";  newline]

  | _ => sd "Invalid type on function: " @@ dshow name
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
      sd
        (concatStr ["declare "; link; vis; dll; cc]) @@
        DList_join [dintersperse (sd " ") (map dshow ret_attrs)] @@
        sd " " @@
        dshow ret_t @@ sd " @" @@ dshow name @@ sd "(" @@
        dconcat (sd ", ") (map (fun '(x, y) =>
                                                 DList_join
                                                   [dshow x; sd " ";
                                                    match y with
                                                    | [] => sd ""
                                                    | z :: tl => dshow z
                                                    end ])
                       (List.combine args_t args_attrs)) @@
        sd vararg_str @@
        sd ")" @@ sd section @@ sd align @@ sd gc
  | _ => sd "Invalid type on function: " @@ dshow name
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
               | None => sd ""
               | Some e => dshow_exp true e
               end
  in
  let unnamed_addr := maybe_show (g_unnamed_addr g) in
  let addrspace := maybe_show (g_addrspace g) in
  let externally_initialized := if g.(g_externally_initialized) then "external " else "" in
  let g_or_c := if g.(g_constant) then "constant " else "global " in

  let section :=
    maybe_to_string
      (fun s => concatStr [", section """; s; """"])
      (g_section g) in

  let align :=
    maybe_to_string
      (fun a => concatStr [", align "; show a; " "])
      (g_align g) in

  let partition :=
    maybe_to_string
      (fun a => concatStr [", partition "; show a; " "])
      (g_partition g) in
  
  (DList_join
    [sd "@"; dshow name; sd " = ";
     sd linkage ; sd visibility;
     sd dll_storage ; sd thread_local;
     sd unnamed_addr; sd addrspace;
     sd externally_initialized])
    @@
    (if (g.(g_alias)) then
       DList_join
         [ sd "alias ";
           dshow gtype;
           sd ", ";
           dshow gtype;
           sd "* ";
           g_exp;
           sd partition
         ]
     else
       DList_join
       [ sd g_or_c;
         dshow gtype;
         sd " ";
         g_exp;
         sd section ;
         sd align
       ]).

#[global] Instance dshowGlobal : DShow (global typ) :=
  {| dshow := dshow_global |}.

Definition quoted_dstring (str : string) : DString
  := sd (show str).

Definition dshow_tle (tle : toplevel_entity typ (block typ * list (block typ))) : DString
  := match tle with
     (*Why is show_definition rather than show being used here*)
     | TLE_Definition defn => dshow defn
     | TLE_Comment msg => sd ";" @@ quoted_dstring msg (*What if the comment is multiple lines? *)
     | TLE_Target tgt => sd "target triple = " @@ quoted_dstring tgt
     | TLE_Datalayout layout => sd "target datalayout = " @@ quoted_dstring layout
     | TLE_Source_filename s => sd "source_filename = " @@ quoted_dstring s
     | TLE_Declaration decl => dshow decl
     | TLE_Global g => dshow g
     | TLE_Metadata id b md => dshow_metadata id @@ sd " = " @@
                                dshow_bool b "distinct " @@
                                dshow_metadata md (* Can't use implicit *)
     | TLE_Type_decl id t => DList_join [dshow_ident id ; sd " = type "; dshow t ]
     | TLE_Attribute_group i attrs =>
         DList_join
           [sd "attributes #"; sd (show i); sd " = { " ;
            dconcat (sd " ") (map (fun x => sd (show x)) (attrs)); sd " }"
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
Definition show_raw_id (id : raw_id) : string := show id.

#[global] Instance showTyp : Show typ :=
  {| show := show_typ |}.

Instance DShow_Z : DShow Z.
split.
intros x.
apply (sd (show x)).
Defined.

Instance DShow_dtyp : DShow dtyp.
split.
intros x.
apply (sd (show_dtyp x)).
Defined.

#[global] Instance DShow_N : DShow N.
split; intros x.
apply (sd (show x)).
Defined.

