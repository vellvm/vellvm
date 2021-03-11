(*  ------------------------------------------------------------------------- *)
(* Adapted for use in Vellvm by Steve Zdancewic (c) 2017                      *)
(*  ------------------------------------------------------------------------- *)

open Format
open LLVMAst
open ParseUtil

(* TODO: Use pp_option everywhere instead of inlined matching *)
let pp_option ppf f o =
  match o with
  | None -> ()
  | Some x -> f ppf x

(* Backward compatibility with 4.01.0 *)
let rec pp_print_list ?(pp_sep = Format.pp_print_cut) pp_v ppf = function
| [] -> ()
| v :: vs ->
    pp_v ppf v; if vs <> [] then (pp_sep ppf ();
                                  pp_print_list ~pp_sep pp_v ppf vs)

let get_function_type dc_type =
  match dc_type with
  | TYPE_Function(ret,args) -> (ret,args)
  | _ -> failwith "not a function type"

let pp_sep str =
  fun ppf () -> pp_print_string ppf str

let pp_space ppf () = pp_print_char ppf ' '

let pp_comma_space ppf () = pp_print_string ppf ", "

let rec linkage : Format.formatter -> LLVMAst.linkage -> unit =
  fun ppf ->
  function
  | LINKAGE_Private              -> fprintf ppf "private"
  | LINKAGE_Internal             -> fprintf ppf "internal"
  | LINKAGE_Available_externally -> fprintf ppf "available_externally"
  | LINKAGE_Linkonce             -> fprintf ppf "linkonce"
  | LINKAGE_Weak                 -> fprintf ppf "weak"
  | LINKAGE_Common               -> fprintf ppf "common"
  | LINKAGE_Appending            -> fprintf ppf "appending"
  | LINKAGE_Extern_weak          -> fprintf ppf "extern_weak"
  | LINKAGE_Linkonce_odr         -> fprintf ppf "linkonce_ord"
  | LINKAGE_Weak_odr             -> fprintf ppf "weak_odr"
  | LINKAGE_External             -> fprintf ppf "external"

 and dll_storage : Format.formatter -> LLVMAst.dll_storage -> unit =
   fun ppf ->
   function
   | DLLSTORAGE_Dllimport -> fprintf ppf "dllimport"
   | DLLSTORAGE_Dllexport -> fprintf ppf "dllexport"

and visibility : Format.formatter -> LLVMAst.visibility -> unit =
  fun ppf ->
  function
  | VISIBILITY_Default   -> fprintf ppf "default"
  | VISIBILITY_Hidden    -> fprintf ppf "hidden"
  | VISIBILITY_Protected -> fprintf ppf "protected"

and cconv : Format.formatter -> LLVMAst.cconv -> unit =
  fun ppf -> function
          | CC_Ccc    -> fprintf ppf "ccc"
          | CC_Fastcc -> fprintf ppf "fastcc"
          | CC_Coldcc -> fprintf ppf "coldcc"
          | CC_Cc i   -> fprintf ppf "cc %d" (to_int i)

and param_attr : Format.formatter -> LLVMAst.param_attr -> unit =
  fun ppf ->
  function
  | PARAMATTR_Zeroext           -> fprintf ppf "zeroext"
  | PARAMATTR_Signext           -> fprintf ppf "signext"
  | PARAMATTR_Inreg             -> fprintf ppf "inreg"
  | PARAMATTR_Byval             -> fprintf ppf "byval"
  | PARAMATTR_Inalloca          -> fprintf ppf "inalloca"
  | PARAMATTR_Sret              -> fprintf ppf "sret"
  | PARAMATTR_Align n           -> fprintf ppf "align %d" (to_int n)
  | PARAMATTR_Noalias           -> fprintf ppf "noalias"
  | PARAMATTR_Nocapture         -> fprintf ppf "nocapture"
  | PARAMATTR_Readonly          -> fprintf ppf "readonly"
  | PARAMATTR_Nest              -> fprintf ppf "nest"
  | PARAMATTR_Returned          -> fprintf ppf "returned"
  | PARAMATTR_Nonnull           -> fprintf ppf "nonnull"
  | PARAMATTR_Dereferenceable n -> fprintf ppf "dereferenceable(%d)" (to_int n)
  | PARAMATTR_Immarg            -> fprintf ppf "immarg"
  | PARAMATTR_Noundef           -> fprintf ppf "noundef"
  | PARAMATTR_Nofree            -> fprintf ppf "nofree"

and pp_llvm_int : Format.formatter -> LLVMAst.int -> unit =
  fun ppf i -> fprintf ppf "%d" (to_int i)

and fn_attr : Format.formatter -> LLVMAst.fn_attr -> unit =
  fun ppf ->
  function
  | FNATTR_Alignstack i     -> fprintf ppf "alignstack(%a)" pp_llvm_int i
  | FNATTR_Allocsize l      ->
     fprintf ppf "allocsize(%a)" (pp_print_list ~pp_sep:pp_comma_space pp_llvm_int) l
  | FNATTR_Alwaysinline     -> fprintf ppf "alwaysinline"
  | FNATTR_Builtin          -> fprintf ppf "builtin"
  | FNATTR_Cold             -> fprintf ppf "cold"
  | FNATTR_Convergent       -> fprintf ppf "convergent"
  | FNATTR_Hot              -> fprintf ppf "hot"
  | FNATTR_Inaccessiblememonly -> fprintf ppf "inaccessiblememonly"
  | FNATTR_Inaccessiblemem_or_argmemonly-> fprintf ppf "inaccessible_or_argmemonly"
  | FNATTR_Inlinehint       -> fprintf ppf "inlinehint"
  | FNATTR_Jumptable        -> fprintf ppf "jumptable"
  | FNATTR_Minsize          -> fprintf ppf "minsize"
  | FNATTR_Naked            -> fprintf ppf "naked"
  | FNATTR_No_jump_tables   -> fprintf ppf "no_jump_tables"
  | FNATTR_Nobuiltin        -> fprintf ppf "nobuiltin"
  | FNATTR_Noduplicate      -> fprintf ppf "noduplicate"
  | FNATTR_Nofree           -> fprintf ppf "nofree"
  | FNATTR_Noimplicitfloat  -> fprintf ppf "noimplicitfloat"
  | FNATTR_Noinline         -> fprintf ppf "noinline"
  | FNATTR_Nomerge          -> fprintf ppf "nomerge"
  | FNATTR_Nonlazybind      -> fprintf ppf "nonlazybind"
  | FNATTR_Noredzone        -> fprintf ppf "noredzone"
  | FNATTR_Indirect_tls_seg_refs -> fprintf ppf "indirect-tls-seg-refs"
  | FNATTR_Noreturn         -> fprintf ppf "noreturn"
  | FNATTR_Norecurse        -> fprintf ppf "norecurse"
  | FNATTR_Willreturn       -> fprintf ppf "willreturn"
  | FNATTR_Nosync           -> fprintf ppf "nosync"
  | FNATTR_Nounwind         -> fprintf ppf "nounwind"
  | FNATTR_Null_pointer_is_valid -> fprintf ppf "null_pointer_is_valid"
  | FNATTR_Optforfuzzing    -> fprintf ppf "optforfuzzing"
  | FNATTR_Optnone          -> fprintf ppf "optnone"
  | FNATTR_Optsize          -> fprintf ppf "optsize"
  | FNATTR_Readnone         -> fprintf ppf "readnone"
  | FNATTR_Readonly         -> fprintf ppf "readonly"
  | FNATTR_Writeonly        -> fprintf ppf "writeonly"
  | FNATTR_Argmemonly       -> fprintf ppf "argmemonly"
  | FNATTR_Returns_twice    -> fprintf ppf "returns_twice"
  | FNATTR_Safestack        -> fprintf ppf "safestack"
  | FNATTR_Sanitize_address -> fprintf ppf "sanitize_address"
  | FNATTR_Sanitize_memory  -> fprintf ppf "sanitize_memory"
  | FNATTR_Sanitize_thread  -> fprintf ppf "sanitize_thread"
  | FNATTR_Sanitize_hwaddress -> fprintf ppf "sanitize_hwaddress"
  | FNATTR_Sanitize_memtag  -> fprintf ppf "santize_memtag"
  | FNATTR_Speculative_load_hardening -> fprintf ppf "speculative_load_hardening"
  | FNATTR_Speculatable     -> fprintf ppf "speculatable"
  | FNATTR_Ssp              -> fprintf ppf "ssp"
  | FNATTR_Sspreq           -> fprintf ppf "sspreq"
  | FNATTR_Sspstrong        -> fprintf ppf "sspstrong"
  | FNATTR_Strictfp         -> fprintf ppf "strictfp"
  | FNATTR_Uwtable          -> fprintf ppf "uwtable"
  | FNATTR_Nocf_check       -> fprintf ppf "nocf_check"
  | FNATTR_Shadowcallstack  -> fprintf ppf "shadowcallstack"
  | FNATTR_Mustprogress     -> fprintf ppf "mustprogress"
  | FNATTR_String s         -> fprintf ppf "\"%s\"" (of_str s)
  | FNATTR_Key_value (k, v) -> fprintf ppf "\"%s\"=\"%s\"" (of_str k) (of_str v)
  | FNATTR_Attr_grp i       -> fprintf ppf "#%d" (to_int i)

and str_of_raw_id : LLVMAst.raw_id -> string =
    function
    | Anon i -> Printf.sprintf "%d" (to_int i)
    | Name s -> Printf.sprintf "%s" (of_str s)
    | Raw i -> Printf.sprintf "_RAW_%d" (to_int i)

and lident : Format.formatter -> LLVMAst.local_id -> unit =
  fun ppf i -> pp_print_char ppf '%' ; pp_print_string ppf (str_of_raw_id i)

and arg_lident : Format.formatter -> LLVMAst.local_id -> unit =
  fun ppf i ->
  match i with
  | Anon _ -> ()
  | _ -> pp_print_char ppf '%' ; pp_print_string ppf (str_of_raw_id i)


and gident : Format.formatter -> LLVMAst.global_id -> unit =
  fun ppf i -> pp_print_char ppf '@' ; pp_print_string ppf (str_of_raw_id i)


and ident : Format.formatter -> LLVMAst.ident -> unit =

  (* let ident_format : (string -> int) -> Format.formatter -> string -> unit = *)
  (* fun finder ppf i -> *)
  (* if i.[0] >= '0' && i.[0] <= '9' then pp_print_int ppf (finder i) *)
  (* else pp_print_string ppf i in *)

  fun ppf ->
  function
  | ID_Global i -> gident ppf i
  | ID_Local i  -> lident ppf i

and typ : Format.formatter -> LLVMAst.typ -> unit =
  fun ppf ->
  function
  | TYPE_I i              -> fprintf ppf "i%d" (n_to_int i)
  | TYPE_Pointer t        -> fprintf ppf "%a*" typ t ;
  | TYPE_Void             -> fprintf ppf "void"
  | TYPE_Half             -> fprintf ppf "half"
  | TYPE_Float            -> fprintf ppf "float"
  | TYPE_Double           -> fprintf ppf "double"
  | TYPE_X86_fp80         -> fprintf ppf "x86_fp80"
  | TYPE_Fp128            -> fprintf ppf "fp128"
  | TYPE_Ppc_fp128        -> fprintf ppf "ppc_fp128"
  | TYPE_Metadata         -> fprintf ppf "metadata"
  | TYPE_X86_mmx          -> fprintf ppf "x86_mmx"
  | TYPE_Array (i, t)     -> fprintf ppf "[%d x %a]" (n_to_int i) typ t ;
  | TYPE_Function (t, tl) -> fprintf ppf "%a (%a)" typ t (pp_print_list ~pp_sep:pp_comma_space typ) tl
  | TYPE_Struct tl        -> fprintf ppf "{%a}"
                                     (pp_print_list ~pp_sep:pp_comma_space typ) tl
  | TYPE_Packed_struct tl -> fprintf ppf "<{%a}>"
                                     (pp_print_list ~pp_sep:pp_comma_space typ) tl
  | TYPE_Opaque           -> fprintf ppf "opaque"
  | TYPE_Vector (i, t)    -> fprintf ppf "<%d x %a>" (n_to_int i) typ t ;
  | TYPE_Identified i     -> ident ppf i

and icmp : Format.formatter -> LLVMAst.icmp -> unit =
  fun ppf icmp ->
  fprintf ppf ( match icmp with
                | Eq  -> "eq"
                | Ne  -> "ne"
                | Ugt -> "ugt"
                | Uge -> "uge"
                | Ult -> "ult"
                | Ule -> "ule"
                | Sgt -> "sgt"
                | Sge -> "sge"
                | Slt -> "slt"
                | Sle -> "sle")

and fcmp : Format.formatter -> LLVMAst.fcmp -> unit =
  fun ppf fcmp ->
  fprintf ppf ( match fcmp with
                | FFalse -> "false"
                | FOeq   -> "oeq"
                | FOgt   -> "ogt"
                | FOge   -> "oge"
                | FOlt   -> "olt"
                | FOle   -> "ole"
                | FOne   -> "one"
                | FOrd   -> "ord"
                | FUno   -> "uno"
                | FUeq   -> "ueq"
                | FUgt   -> "ugt"
                | FUge   -> "uge"
                | FUlt   -> "ult"
                | FUle   -> "ule"
                | FUne   -> "une"
                | FTrue  -> "true")


and ibinop : Format.formatter -> LLVMAst.ibinop -> unit =
  fun ppf ->
  let nuw ppf flag = if flag then fprintf ppf " nuw" in
  let nsw ppf flag = if flag then fprintf ppf " nsw" in
  let exact ppf flag = if flag then fprintf ppf " exact" in
  function
  | Add (nu, ns) -> fprintf ppf "add" ; nuw ppf nu ; nsw ppf ns
  | Sub (nu, ns) -> fprintf ppf "sub" ; nuw ppf nu ; nsw ppf ns
  | Mul (nu, ns) -> fprintf ppf "mul" ; nuw ppf nu ; nsw ppf ns
  | UDiv e       -> fprintf ppf "udiv" ; exact ppf e
  | SDiv e       -> fprintf ppf "sdiv" ; exact ppf e
  | URem         -> fprintf ppf "urem"
  | SRem         -> fprintf ppf "srem"
  | Shl (nu, ns) -> fprintf ppf "shl" ; nuw ppf nu ; nsw ppf ns
  | LShr e       -> fprintf ppf "lshr" ; exact ppf e
  | AShr e       -> fprintf ppf "ashr" ; exact ppf e
  | And          -> fprintf ppf "and"
  | Or           -> fprintf ppf "or"
  | Xor          -> fprintf ppf "xor"

and fbinop =
  fun ppf fbinop ->
  fprintf ppf (match fbinop with
                 | FAdd -> "fadd"
                 | FSub -> "fsub"
                 | FMul -> "fmul"
                 | FDiv -> "fdiv"
                 | FRem -> "frem")

and fast_math =
  fun ppf fast_math ->
  pp_print_string ppf (match fast_math with
                       | Nnan -> "nnan"
                       | Ninf -> "ninf"
                       | Nsz  -> "nsz"
                       | Arcp -> "arcp"
                       | Fast -> "fast")

and conversion_type : Format.formatter -> LLVMAst.conversion_type -> unit =
  fun ppf conv ->
  fprintf ppf (match conv with
               | Trunc    -> "trunc"
               | Zext     -> "zext"
               | Sext     -> "sext"
               | Fptrunc  -> "fptrunc"
               | Fpext    -> "fpext"
               | Uitofp   -> "uitofp"
               | Sitofp   -> "sitofp"
               | Fptoui   -> "fptoui"
               | Fptosi   -> "fptosi"
               | Inttoptr -> "inttoptr"
               | Ptrtoint -> "ptrtoint"
               | Bitcast  -> "bitcast")

and exp : Format.formatter -> (LLVMAst.typ LLVMAst.exp) -> unit =
  fun (ppf:Format.formatter) vv ->
    match vv with
  | EXP_Ident i           -> ident ppf i
  | EXP_Integer i         -> pp_print_int ppf (to_int i)
  | EXP_Float f           -> fprintf ppf "0x%lX" (Camlcoq.camlint_of_coqint(Floats.Float32.to_bits f))
  | EXP_Double f          -> fprintf ppf "0x%LX" (Camlcoq.camlint64_of_coqint(Floats.Float.to_bits f))
  | EXP_Hex h             -> fprintf ppf "0x%LX" (Camlcoq.camlint64_of_coqint(Floats.Float.to_bits h))
  | EXP_Bool b            -> pp_print_bool ppf b
  | EXP_Null              -> pp_print_string ppf "null"
  | EXP_Undef             -> pp_print_string ppf "undef"
  | EXP_Array tvl         -> fprintf ppf "[%a]"
                                       (pp_print_list ~pp_sep:pp_comma_space texp) tvl
  | EXP_Vector tvl        -> fprintf ppf "<%a>"
                                       (pp_print_list ~pp_sep:pp_comma_space texp) tvl
  | EXP_Struct tvl        -> fprintf ppf "{%a}"
                                       (pp_print_list ~pp_sep:pp_comma_space texp) tvl
  | EXP_Packed_struct tvl -> fprintf ppf "<{%a}>"
                                       (pp_print_list ~pp_sep:pp_comma_space texp) tvl
  | EXP_Zero_initializer  -> pp_print_string ppf "zeroinitializer"

  | EXP_Cstring s -> fprintf ppf "c\"%s\"" (of_str (escape (llvm_i8_array_to_cstring_bytes s)))

  | OP_IBinop (op, t, v1, v2) ->
     fprintf ppf "%a (%a %a, %a %a)"
             ibinop op
             typ t
             exp v1
             typ t
             exp v2

  | OP_ICmp (c, t, v1, v2) ->
     fprintf ppf "icmp %a (%a %a, %a %a)"
             icmp c
             typ t
             exp v1
             typ t
             exp v2

  | OP_FBinop (op, f, t, v1, v2) ->
     fbinop ppf op ;
     if f <> [] then (pp_space ppf () ;
                      pp_print_list ~pp_sep:pp_space fast_math ppf f) ;
     fprintf ppf " (%a %a, %a %a)"
             typ t
             exp v1
             typ t
             exp v2

  | OP_FCmp (c, t, v1, v2) ->
     fprintf ppf "fcmp %a (%a %a, %a %a)"
             fcmp c
             typ t
             exp v1
             typ t
             exp v2

  | OP_Conversion (c, t1, v, t2) ->
     fprintf ppf "%a (%a %a to %a)"
             conversion_type c
             typ t1
             exp v
             typ t2

  | OP_GetElementPtr (t, tv, tvl) ->
    fprintf ppf "getelementptr (%a, %a, %a)"
             typ t
             texp tv
             (pp_print_list ~pp_sep:pp_comma_space texp) tvl

  | OP_Select (if_, then_, else_) ->
     fprintf ppf "select (%a, %a, %a)"
             texp if_
             texp then_
             texp else_

  | OP_Freeze (tv) ->
    fprintf ppf "freeze %a"
      texp tv

  | OP_ExtractElement (vec, idx) ->
     fprintf ppf "extractelement (%a, %a)"
             texp vec
             texp idx

  | OP_InsertElement (vec, new_val, idx) ->
     fprintf ppf "insertelement (%a, %a, %a)"
             texp vec
             texp new_val
             texp idx

  | OP_ExtractValue (agg, idx) ->
     fprintf ppf "extractvalue (%a, %a)"
             texp agg
             (pp_print_list ~pp_sep:pp_comma_space pp_print_int) (List.map to_int idx)

  | OP_InsertValue (agg, new_val, idx) ->
     fprintf ppf "insertvalue (%a, %a, %a)"
             texp agg
             texp new_val
             (pp_print_list ~pp_sep:pp_comma_space pp_print_int) (List.map to_int idx)

  | OP_ShuffleVector (v1, v2, mask) ->
     fprintf ppf "shufflevector (%a, %a, %a)"
             texp v1
             texp v2
             texp mask

and inst_exp : Format.formatter -> (LLVMAst.typ LLVMAst.exp) -> unit =
  fun ppf vv ->
    match vv with
  | EXP_Ident _
  | EXP_Integer _
  | EXP_Float _
  | EXP_Double _
  | EXP_Hex _
  | EXP_Bool _
  | EXP_Null
  | EXP_Undef
  | EXP_Array _
  | EXP_Vector _
  | EXP_Struct _
  | EXP_Packed_struct _
  | EXP_Zero_initializer
  | EXP_Cstring _ -> assert false   (* there should be no "raw" exps as instructions *)

  | OP_IBinop (op, t, v1, v2) ->
     fprintf ppf "%a %a %a, %a"
             ibinop op
             typ t
             exp v1
             exp v2

  | OP_ICmp (c, t, v1, v2) ->
     fprintf ppf "icmp %a %a %a, %a"
             icmp c
             typ t
             exp v1
             exp v2

  | OP_FBinop (op, f, t, v1, v2) ->
     fbinop ppf op ;
     if f <> [] then (pp_space ppf () ;
                      pp_print_list ~pp_sep:pp_space fast_math ppf f) ;
     fprintf ppf " %a %a, %a"
             typ t
             exp v1
             exp v2

  | OP_FCmp (c, t, v1, v2) ->
     fprintf ppf "fcmp %a %a %a, %a"
             fcmp c
             typ t
             exp v1
             exp v2

  | OP_Conversion (c, t1, v, t2) ->
     fprintf ppf "%a %a %a to %a"
             conversion_type c
             typ t1
             exp v
             typ t2

  | OP_GetElementPtr (t, tv, tvl) ->
    fprintf ppf "getelementptr %a, %a, %a"
             typ t
             texp tv
             (pp_print_list ~pp_sep:pp_comma_space texp) tvl

  | OP_Select (if_, then_, else_) ->
     fprintf ppf "select %a, %a, %a"
             texp if_
             texp then_
             texp else_

  | OP_Freeze (tv) ->
    fprintf ppf "freeze %a"
      texp tv

  | OP_ExtractElement (vec, idx) ->
     fprintf ppf "extractelement %a, %a"
             texp vec
             texp idx

  | OP_InsertElement (vec, new_val, idx) ->
     fprintf ppf "insertelement %a, %a, %a"
             texp vec
             texp new_val
             texp idx

  | OP_ExtractValue (agg, idx) ->
     fprintf ppf "extractvalue %a, %a"
             texp agg
             (pp_print_list ~pp_sep:pp_comma_space pp_print_int) (List.map to_int idx)

  | OP_InsertValue (agg, new_val, idx) ->
     fprintf ppf "insertvalue %a, %a, %a"
             texp agg
             texp new_val
             (pp_print_list ~pp_sep:pp_comma_space pp_print_int) (List.map to_int idx)

  | OP_ShuffleVector (v1, v2, mask) ->
     fprintf ppf "shufflevector %a, %a, %a"
             texp v1
             texp v2
             texp mask


and phi : Format.formatter -> (LLVMAst.typ LLVMAst.phi) -> unit =
  fun ppf ->
  function
  | Phi (t, vil) ->
     fprintf ppf "phi %a [%a]"
             typ t
             (pp_print_list ~pp_sep:(pp_sep "], [")
                            (fun ppf (i, v) -> exp ppf v ;
                                               pp_print_string ppf ", " ;
                                               lident ppf i)) vil


and instr : Format.formatter -> (LLVMAst.typ LLVMAst.instr) -> unit =
  fun ppf ->
  function

  | INSTR_Comment msg ->  fprintf ppf "; %s" (of_str msg)

  | INSTR_Op v -> inst_exp ppf v

  | INSTR_Call (tv, tvl) ->
     fprintf ppf "call %a(%a)"
             texp tv
             (pp_print_list ~pp_sep:pp_comma_space texp) tvl

  | INSTR_Alloca (t, n, a) ->
     fprintf ppf "alloca %a" typ t ;
     (match n with None -> ()
                 | Some n -> fprintf ppf ", %a" texp n) ;
     (match a with None -> ()
                 | Some a -> fprintf ppf ", align %d" (to_int a))

  | INSTR_Load (vol, t, tv, a) ->
     pp_print_string ppf "load " ;
     if vol then pp_print_string ppf "volatile " ;
     (typ ppf t);
     pp_print_string ppf ", ";
     texp ppf tv ;
     (match a with None -> ()
                 | Some a -> fprintf ppf ", align %d" (to_int a))

  | INSTR_VAArg -> pp_print_string ppf "vaarg"

  | INSTR_LandingPad -> assert false

  | INSTR_Store (vol, v, ptr, a) ->
     pp_print_string ppf "store " ;
     if vol then pp_print_string ppf "volatile " ;
     fprintf ppf "%a, %a" texp v texp ptr ;
     (match a with None -> ()
                 | Some a -> fprintf ppf ", align %d" (to_int a))

  | INSTR_AtomicCmpXchg
  | INSTR_AtomicRMW
  | INSTR_Fence -> assert false

and branch_label : Format.formatter -> LLVMAst.raw_id -> unit =
  fun ppf id ->
    pp_print_string ppf "label %"; pp_print_string ppf (str_of_raw_id id)

and tint_literal : Format.formatter -> LLVMAst.tint_literal -> unit =
  fun ppf (TInt_Literal(sz, n)) ->
           fprintf ppf "i%d " (n_to_int sz);
           pp_print_int ppf (to_int n)

and terminator : Format.formatter -> (LLVMAst.typ LLVMAst.terminator) -> unit =
  fun ppf ->
  function

  | TERM_Ret (t, v)       -> fprintf ppf "ret %a" texp (t, v)

  | TERM_Ret_void         -> pp_print_string ppf "ret void"

  | TERM_Br (c, i1, i2)   ->
     fprintf ppf "br %a, %a, %a" texp c branch_label i1 branch_label i2

  | TERM_Br_1 i          -> fprintf ppf "br %a" branch_label i

  | TERM_Switch (c, def, cases) ->
     fprintf ppf "switch %a, %a [%a]"
             texp c
             branch_label def
             (pp_print_list ~pp_sep:pp_space
                (fun ppf (lit, i) ->
                  tint_literal ppf lit;
                  pp_print_string ppf ", " ;
                  branch_label ppf i)) cases

  | TERM_Resume (t, v) -> fprintf ppf "resume %a" texp (t, v)

  | TERM_IndirectBr (tv, til) ->
    fprintf ppf "indirectbr %a, [%a]"
      texp tv
      (pp_print_list ~pp_sep:pp_comma_space branch_label) til

  | TERM_Invoke (ti, tvl, i2, i3) ->
     fprintf ppf "invoke %a(%a) to %a unwind %a"
             tident ti
             (pp_print_list ~pp_sep:pp_comma_space texp) tvl
             branch_label i2
             branch_label i3

  | TERM_Unreachable -> pp_print_string ppf "unreachable"

and id_instr : Format.formatter -> (LLVMAst.instr_id * LLVMAst.typ LLVMAst.instr) -> unit =
  fun ppf ->
    function (id, inst) ->
      fprintf ppf "%a%a" instr_id id instr inst

and id_phi : Format.formatter -> (LLVMAst.local_id * LLVMAst.typ LLVMAst.phi) -> unit =
  fun ppf ->
    function (id, p) ->
      fprintf ppf "%a = %a" lident id phi p


and instr_id : Format.formatter -> LLVMAst.instr_id -> unit =
  fun ppf ->
    function
    | IId id  -> fprintf ppf "%%%s = " (str_of_raw_id id)
    | IVoid n -> fprintf ppf "; void instr %d" (to_int n); pp_force_newline ppf ()

and texp ppf (t, v) = fprintf ppf "%a %a" typ t exp v

and tident ppf (t, v) = fprintf ppf "%a %a" typ t ident v

and toplevel_entities : Format.formatter -> (LLVMAst.typ, (LLVMAst.typ block) * ((LLVMAst.typ LLVMAst.block) list)) LLVMAst.toplevel_entities -> unit =
  fun ppf entries ->
  pp_print_list ~pp_sep:pp_force_newline toplevel_entity ppf entries

and toplevel_entity : Format.formatter -> (LLVMAst.typ, (LLVMAst.typ block) * ((LLVMAst.typ LLVMAst.block) list)) LLVMAst.toplevel_entity -> unit =
  fun ppf ->
  function
  | TLE_Comment msg            -> fprintf ppf "; %s" (of_str msg)
  | TLE_Target s               -> fprintf ppf "target triple = \"%s\"" (of_str s)
  | TLE_Datalayout s           -> fprintf ppf "target datalayout = \"%s\"" (of_str s)
  | TLE_Source_filename s      -> fprintf ppf "source_filename = \"%s\"" (of_str s)
  | TLE_Declaration d          -> declaration ppf d
  | TLE_Definition d           -> definition ppf d
  | TLE_Type_decl (i, t)       -> fprintf ppf "%a = type %a" ident i typ t
  | TLE_Global g               -> global ppf g
  | TLE_Metadata (i, m)        -> fprintf ppf "!%s = %a" (str_of_raw_id i) metadata m
  | TLE_Attribute_group (i, a) -> fprintf ppf "attributes #%d = { %a }" (to_int i)
                                          (pp_print_list ~pp_sep:pp_space fn_attr) a

and metadata : Format.formatter -> (LLVMAst.typ LLVMAst.metadata) -> unit =
  fun ppf ->
  function
  | METADATA_Const v  -> texp ppf v
  | METADATA_Null     -> pp_print_string ppf "null"
  | METADATA_Id i     -> fprintf ppf "!%s" (str_of_raw_id i)
  | METADATA_String s -> fprintf ppf "!%s" (of_str s)
  | METADATA_Node m   -> fprintf ppf "!{%a}"
                                 (pp_print_list ~pp_sep:pp_comma_space metadata) m
  | METADATA_Named m  -> fprintf ppf "!{%a}"
                                 (pp_print_list ~pp_sep:pp_comma_space
                                                (fun ppf i ->
                                                 fprintf ppf "!%s" i)) (List.map of_str m)

and global : Format.formatter -> (LLVMAst.typ LLVMAst.global) -> unit =
  fun ppf ->
  fun {
    g_ident;
    g_typ;
    g_constant;
    g_exp;

    g_linkage;

    g_section = s;
    g_align = a;
    _;
  } -> fprintf ppf "@%s = "  (str_of_raw_id g_ident);
       (match g_linkage with None -> ()
                           | Some l -> linkage ppf l; pp_print_string ppf " "
       );
       (fprintf ppf "%s %a" (if g_constant then "constant" else "global") typ g_typ) ;
       (match g_exp with None -> () | Some v -> (pp_print_string ppf " "; exp ppf v)) ;
       (match s with None -> ()
                   | Some s -> fprintf ppf ", section %s" (of_str s)) ;
       (match a with None -> ()
                   | Some a -> fprintf ppf ", align %d" (to_int a))

and declaration : Format.formatter -> (LLVMAst.typ LLVMAst.declaration) -> unit =
  fun ppf ->
  fun { dc_name = i
      ; dc_type
      ; dc_param_attrs = (ret_attrs, args_attrs)
      ; dc_linkage
      ; dc_visibility
      ; dc_dll_storage
      ; dc_cconv
      ; dc_section
      ; dc_align
      ; dc_gc
      ; _
      } ->
    let (ret_t, args_t) = get_function_type dc_type in
    let typ_attr =
      fun ppf (t, attrs) ->
        typ ppf t ;
        pp_print_list ~pp_sep:pp_space param_attr ppf attrs
    in
    pp_print_string ppf "declare " ;
    (match dc_linkage with
     | Some x -> linkage ppf x ; pp_space ppf ()
     | _ -> ()) ;
    (match dc_visibility with
     | Some x -> visibility ppf x ; pp_space ppf ()
     | _ -> ()) ;
    (match dc_dll_storage with
     | Some x -> dll_storage ppf x ; pp_space ppf ()
     | _ -> ()) ;
    (match dc_cconv with
     | Some x -> cconv ppf x ; pp_space ppf ()
     | _ -> ()) ;
    if ret_attrs <> [] then (pp_print_list ~pp_sep:pp_space
                               param_attr ppf ret_attrs ;
                             pp_space ppf ()) ;
    fprintf ppf "%a @%s(%a)"
      typ ret_t
      (str_of_raw_id i)
      (pp_print_list ~pp_sep:pp_comma_space typ_attr)
      (List.combine args_t args_attrs);
    (match dc_section with
       Some x -> fprintf ppf "section \"%s\" " (of_str x) | _ -> ()) ;
    (match dc_align with
       Some x -> fprintf ppf "align %d " (to_int x) | _ -> ()) ;
    (match dc_gc with
       Some x -> fprintf ppf "gc \"%s\" " (of_str x) | _ -> ())

and definition : Format.formatter -> (LLVMAst.typ, (LLVMAst.typ LLVMAst.block) * ((LLVMAst.typ LLVMAst.block list))) LLVMAst.definition -> unit =
  fun ppf ->
  fun ({ df_prototype =
           { dc_name = i
           ; dc_type
           ; dc_param_attrs = (ret_attrs, args_attrs)
           ; dc_linkage
           ; dc_visibility
           ; dc_dll_storage
           ; dc_cconv
           ; dc_attrs
           ; dc_section
           ; dc_align
           ; dc_gc
           }
       ; _
       } as df) ->
    let (ret_t, args_t) = get_function_type dc_type in
    let typ_attr_id =
      fun ppf ((t, attrs), id) ->
        typ ppf t ;
        pp_space ppf () ;
        if attrs <> [] then (pp_print_list ~pp_sep:pp_space
                               param_attr ppf attrs ;
                             pp_space ppf ()) ;
        arg_lident ppf id
    in
    pp_print_string ppf "define " ;
    (match dc_linkage with
     | Some x -> linkage ppf x ; pp_space ppf ()
     | _ -> ()) ;
    (match dc_visibility with
     | Some x -> visibility ppf x ; pp_space ppf ()
     | _ -> ()) ;
    (match dc_dll_storage with
     | Some x -> dll_storage ppf x ; pp_space ppf ()
     | _ -> ()) ;
    (match dc_cconv with
     | Some x -> cconv ppf x ; pp_space ppf ()
     | _ -> ()) ;
    if ret_attrs <> [] then (pp_print_list ~pp_sep:pp_space
                               param_attr ppf ret_attrs ;
                             pp_space ppf ()) ;
    fprintf ppf "%a @%s(%a) "
      typ ret_t
      (str_of_raw_id i)
      (pp_print_list ~pp_sep:pp_comma_space typ_attr_id)
      (List.combine (List.combine args_t args_attrs) df.df_args) ;
    if dc_attrs <> [] then (pp_print_list ~pp_sep:pp_space
                              fn_attr ppf dc_attrs ;
                            pp_space ppf ()) ;
    (match dc_section with
       Some x -> fprintf ppf "section \"%s\" " (of_str x) | _ -> ()) ;
    (match dc_align with
       Some x -> fprintf ppf "align %d " (to_int x) | _ -> ()) ;
    (match dc_gc with
       Some x -> fprintf ppf "gc \"%s\" " (of_str x) | _ -> ()) ;
    pp_print_char ppf '{' ;
    pp_force_newline ppf () ;
    block ppf (fst df.df_instrs);
    pp_force_newline ppf () ;
    pp_print_list ~pp_sep:pp_force_newline block ppf (snd df.df_instrs) ;
    pp_force_newline ppf () ;
    pp_print_char ppf '}' ;

and block : Format.formatter -> LLVMAst.typ LLVMAst.block -> unit =
  fun ppf {blk_id=lbl; blk_phis=phis; blk_code=b; blk_term=t; blk_comments=c} ->
    begin match c with
    | None -> ()
    | Some cs ->  pp_print_list ~pp_sep:pp_force_newline comment ppf cs ;
                  pp_force_newline ppf ()
    end;
    begin match lbl with
      | Anon i -> fprintf ppf "; <label> %%%d" (to_int i)
      | Name s -> (pp_print_string ppf (of_str s); pp_print_char ppf ':')
      | Raw i -> fprintf ppf "_RAW_%d:" (to_int i)
    end;
    pp_force_newline ppf () ;
    pp_print_string ppf "  ";
    pp_open_box ppf 0 ;
    pp_print_list ~pp_sep:pp_force_newline id_phi ppf phis ;
    pp_force_newline ppf () ;
    pp_print_list ~pp_sep:pp_force_newline id_instr ppf b ;
    pp_force_newline ppf () ;
    terminator ppf t;
    pp_force_newline ppf () ;    
    pp_close_box ppf ()

and comment : Format.formatter -> char list -> unit =
  fun ppf s -> fprintf ppf "; %s" (of_str s)

and modul : Format.formatter -> (LLVMAst.typ, (LLVMAst.typ LLVMAst.block) * ((LLVMAst.typ LLVMAst.block list))) CFG.modul -> unit =
  fun ppf m ->

  pp_option ppf (fun ppf x -> fprintf ppf "; ModuleID = '%s'" (of_str x)) m.m_name ;
  pp_force_newline ppf () ;

  pp_option ppf (fun ppf x -> fprintf ppf "target triple = \"%s\"" (of_str x)) m.m_target;
  pp_force_newline ppf () ;

  pp_option ppf (fun ppf x -> fprintf ppf "target datalayout = \"%s\"" (of_str x)) m.m_datalayout ;
  pp_force_newline ppf () ;

  pp_print_list ~pp_sep:pp_force_newline global ppf m.m_globals;
  pp_force_newline ppf () ;

  (* Print function declaration only if there is no corresponding
     function definition *)
  pp_print_list ~pp_sep:pp_force_newline declaration ppf m.m_declarations;
  pp_force_newline ppf () ;

  pp_print_list ~pp_sep:pp_force_newline definition ppf m.m_definitions;
  pp_force_newline ppf ()
