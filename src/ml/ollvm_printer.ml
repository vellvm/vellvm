(*  ------------------------------------------------------------------------- *)
(* Adapted for use in Vellvm by Steve Zdancewic (c) 2017                      *)
(*  ------------------------------------------------------------------------- *)

open Format

let str = Camlcoq.coqstring_of_camlstring
let of_str = Camlcoq.camlstring_of_coqstring
let to_int = Camlcoq.Z.to_int

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

open Ollvm_ast

let get_function_type dc_type =
  match dc_type with
  | TYPE_Function(ret,args) -> (ret,args)
  | _ -> failwith "not a function type"

let pp_sep str =
  fun ppf () -> pp_print_string ppf str

let pp_space ppf () = pp_print_char ppf ' '

let pp_comma_space ppf () = pp_print_string ppf ", "

let rec linkage : Format.formatter -> Ollvm_ast.linkage -> unit =
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

 and dll_storage : Format.formatter -> Ollvm_ast.dll_storage -> unit =
   fun ppf ->
   function
   | DLLSTORAGE_Dllimport -> fprintf ppf "dllimport"
   | DLLSTORAGE_Dllexport -> fprintf ppf "dllexport"

and visibility : Format.formatter -> Ollvm_ast.visibility -> unit =
  fun ppf ->
  function
  | VISIBILITY_Default   -> fprintf ppf "default"
  | VISIBILITY_Hidden    -> fprintf ppf "hidden"
  | VISIBILITY_Protected -> fprintf ppf "protected"

and cconv : Format.formatter -> Ollvm_ast.cconv -> unit =
  fun ppf -> function
          | CC_Ccc    -> fprintf ppf "ccc"
          | CC_Fastcc -> fprintf ppf "fastcc"
          | CC_Coldcc -> fprintf ppf "coldcc"
          | CC_Cc i   -> fprintf ppf "cc %d" (to_int i)

and param_attr : Format.formatter -> Ollvm_ast.param_attr -> unit =
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
  | PARAMATTR_Nest              -> fprintf ppf "nest"
  | PARAMATTR_Returned          -> fprintf ppf "returned"
  | PARAMATTR_Nonnull           -> fprintf ppf "nonnull"
  | PARAMATTR_Dereferenceable n -> fprintf ppf "dereferenceable(%d)" (to_int n)

and fn_attr : Format.formatter -> Ollvm_ast.fn_attr -> unit =
  fun ppf ->
  function
  | FNATTR_Alignstack i     -> fprintf ppf "alignstack(%d)" (to_int i)
  | FNATTR_Alwaysinline     -> fprintf ppf "alwaysinline"
  | FNATTR_Builtin          -> fprintf ppf "builtin"
  | FNATTR_Cold             -> fprintf ppf "cold"
  | FNATTR_Inlinehint       -> fprintf ppf "inlinehint"
  | FNATTR_Jumptable        -> fprintf ppf "jumptable"
  | FNATTR_Minsize          -> fprintf ppf "minsize"
  | FNATTR_Naked            -> fprintf ppf "naked"
  | FNATTR_Nobuiltin        -> fprintf ppf "nobuiltin"
  | FNATTR_Noduplicate      -> fprintf ppf "noduplicate"
  | FNATTR_Noimplicitfloat  -> fprintf ppf "noimplicitfloat"
  | FNATTR_Noinline         -> fprintf ppf "noinline"
  | FNATTR_Nonlazybind      -> fprintf ppf "nonlazybind"
  | FNATTR_Noredzone        -> fprintf ppf "noredzone"
  | FNATTR_Noreturn         -> fprintf ppf "noreturn"
  | FNATTR_Nounwind         -> fprintf ppf "nounwind"
  | FNATTR_Optnone          -> fprintf ppf "optnone"
  | FNATTR_Optsize          -> fprintf ppf "optsize"
  | FNATTR_Readnone         -> fprintf ppf "readnone"
  | FNATTR_Readonly         -> fprintf ppf "readonly"
  | FNATTR_Returns_twice    -> fprintf ppf "returns_twice"
  | FNATTR_Sanitize_address -> fprintf ppf "sanitize_address"
  | FNATTR_Sanitize_memory  -> fprintf ppf "sanitize_memory"
  | FNATTR_Sanitize_thread  -> fprintf ppf "sanitize_thread"
  | FNATTR_Ssp              -> fprintf ppf "ssp"
  | FNATTR_Sspreq           -> fprintf ppf "sspreq"
  | FNATTR_Sspstrong        -> fprintf ppf "sspstrong"
  | FNATTR_Uwtable          -> fprintf ppf "uwtable"
  | FNATTR_String s         -> fprintf ppf "\"%s\"" (of_str s)
  | FNATTR_Key_value (k, v) -> fprintf ppf "\"%s\"=\"%s\"" (of_str k) (of_str v)
  | FNATTR_Attr_grp i       -> fprintf ppf "#%d" (to_int i)

and str_of_raw_id : Ollvm_ast.raw_id -> string =
    function
    | Anon i -> Printf.sprintf "%d" (to_int i)
    | Name s -> (of_str s)
    | Raw i -> Printf.sprintf "_RAW_%d" (to_int i)

and lident : Format.formatter -> Ollvm_ast.local_id -> unit =
  fun ppf i -> pp_print_char ppf '%' ; pp_print_string ppf (str_of_raw_id i)

and gident : Format.formatter -> Ollvm_ast.global_id -> unit =
  fun ppf i -> pp_print_char ppf '@' ; pp_print_string ppf (str_of_raw_id i)


and ident : Format.formatter -> Ollvm_ast.ident -> unit =

  (* let ident_format : (string -> int) -> Format.formatter -> string -> unit = *)
  (* fun finder ppf i -> *)
  (* if i.[0] >= '0' && i.[0] <= '9' then pp_print_int ppf (finder i) *)
  (* else pp_print_string ppf i in *)

  fun ppf ->
  function
  | ID_Global i -> gident ppf i
  | ID_Local i  -> lident ppf i

and typ : Format.formatter -> Ollvm_ast.typ -> unit =
  fun ppf ->
  function
  | TYPE_I i              -> fprintf ppf "i%d" (to_int i)
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
  | TYPE_Array (i, t)     -> fprintf ppf "[%d x %a]" (to_int i) typ t ;
  | TYPE_Function (t, tl) -> fprintf ppf "%a (%a)" typ t (pp_print_list ~pp_sep:pp_comma_space typ) tl
  | TYPE_Struct tl        -> fprintf ppf "{%a}"
                                     (pp_print_list ~pp_sep:pp_comma_space typ) tl
  | TYPE_Packed_struct tl -> fprintf ppf "<{%a}>"
                                     (pp_print_list ~pp_sep:pp_comma_space typ) tl
  | TYPE_Opaque           -> fprintf ppf "opaque"
  | TYPE_Vector (i, t)    -> fprintf ppf "<%d x %a>" (to_int i) typ t ;
  | TYPE_Identified i     -> ident ppf i

and icmp : Format.formatter -> Ollvm_ast.icmp -> unit =
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

and fcmp : Format.formatter -> Ollvm_ast.fcmp -> unit =
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


and ibinop : Format.formatter -> Ollvm_ast.ibinop -> unit =
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

and conversion_type : Format.formatter -> Ollvm_ast.conversion_type -> unit =
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

and value : Format.formatter -> Ollvm_ast.value -> unit =
  fun (ppf:Format.formatter) (SV vv) ->
    match vv with
  | VALUE_Ident i           -> ident ppf i
  | VALUE_Integer i         -> pp_print_int ppf (to_int i)
  | VALUE_Float f           -> pp_print_float ppf f
  | VALUE_Bool b            -> pp_print_bool ppf b
  | VALUE_Null              -> pp_print_string ppf "null"
  | VALUE_Undef             -> pp_print_string ppf "undef"
  | VALUE_Array tvl         -> fprintf ppf "[%a]"
                                       (pp_print_list ~pp_sep:pp_comma_space tvalue) tvl
  | VALUE_Vector tvl        -> fprintf ppf "<%a>"
                                       (pp_print_list ~pp_sep:pp_comma_space tvalue) tvl
  | VALUE_Struct tvl        -> fprintf ppf "{%a}"
                                       (pp_print_list ~pp_sep:pp_comma_space tvalue) tvl
  | VALUE_Packed_struct tvl -> fprintf ppf "<{%a}>"
                                       (pp_print_list ~pp_sep:pp_comma_space tvalue) tvl
  | VALUE_Zero_initializer  -> pp_print_string ppf "zeroinitializer"

  | VALUE_Cstring s -> fprintf ppf "c\"%s\"" (of_str s)

  | VALUE_None -> fprintf ppf "none"
  
  | OP_IBinop (op, t, v1, v2) ->
     fprintf ppf "%a (%a %a, %a %a)"
             ibinop op
             typ t
             value v1
             typ t
             value v2

  | OP_ICmp (c, t, v1, v2) ->
     fprintf ppf "icmp %a (%a %a, %a %a)"
             icmp c
             typ t
             value v1
             typ t
             value v2

  | OP_FBinop (op, f, t, v1, v2) ->
     fbinop ppf op ;
     if f <> [] then (pp_space ppf () ;
                      pp_print_list ~pp_sep:pp_space fast_math ppf f) ;
     fprintf ppf " (%a %a, %a %a)"
             typ t
             value v1
             typ t
             value v2

  | OP_FCmp (c, t, v1, v2) ->
     fprintf ppf "fcmp %a (%a %a, %a %a)"
             fcmp c
             typ t
             value v1
             typ t
             value v2

  | OP_Conversion (c, t1, v, t2) ->
     fprintf ppf "%a (%a %a to %a)"
             conversion_type c
             typ t1
             value v
             typ t2

  | OP_GetElementPtr (t, tv, tvl) ->
    fprintf ppf "getelementptr (%a, %a, %a)"
             typ t
             tvalue tv
             (pp_print_list ~pp_sep:pp_comma_space tvalue) tvl

  | OP_Select (if_, then_, else_) ->
     fprintf ppf "select (%a, %a, %a)"
             tvalue if_
             tvalue then_
             tvalue else_

  | OP_ExtractElement (vec, idx) ->
     fprintf ppf "extractelement (%a, %a)"
             tvalue vec
             tvalue idx

  | OP_InsertElement (vec, new_val, idx) ->
     fprintf ppf "insertelement (%a, %a, %a)"
             tvalue vec
             tvalue new_val
             tvalue idx

  | OP_ExtractValue (agg, idx) ->
     fprintf ppf "extractvalue (%a, %a)"
             tvalue agg
             (pp_print_list ~pp_sep:pp_comma_space pp_print_int) (List.map to_int idx)

  | OP_InsertValue (agg, new_val, idx) ->
     fprintf ppf "insertvalue (%a, %a, %a)"
             tvalue agg
             tvalue new_val
             (pp_print_list ~pp_sep:pp_comma_space pp_print_int) (List.map to_int idx)

  | OP_ShuffleVector (v1, v2, mask) ->
     fprintf ppf "shufflevector (%a, %a, %a)"
             tvalue v1
             tvalue v2
             tvalue mask

and inst_value : Format.formatter -> Ollvm_ast.value -> unit =
  fun ppf (SV vv) ->
    match vv with
  | VALUE_Ident _ 
  | VALUE_Integer _ 
  | VALUE_Float _   
  | VALUE_Bool _    
  | VALUE_Null      
  | VALUE_Undef     
  | VALUE_Array _
  | VALUE_Vector _  
  | VALUE_Struct _
  | VALUE_Packed_struct _
  | VALUE_Zero_initializer 
  | VALUE_Cstring _ 
  | VALUE_None -> assert false   (* there should be no "raw" values as instructions *)
  
  | OP_IBinop (op, t, v1, v2) ->
     fprintf ppf "%a %a %a, %a"
             ibinop op
             typ t
             value v1
             value v2

  | OP_ICmp (c, t, v1, v2) ->
     fprintf ppf "icmp %a %a %a, %a"
             icmp c
             typ t
             value v1
             value v2

  | OP_FBinop (op, f, t, v1, v2) ->
     fbinop ppf op ;
     if f <> [] then (pp_space ppf () ;
                      pp_print_list ~pp_sep:pp_space fast_math ppf f) ;
     fprintf ppf " %a %a, %a"
             typ t
             value v1
             value v2

  | OP_FCmp (c, t, v1, v2) ->
     fprintf ppf "fcmp %a %a %a, %a"
             fcmp c
             typ t
             value v1
             value v2

  | OP_Conversion (c, t1, v, t2) ->
     fprintf ppf "%a %a %a to %a"
             conversion_type c
             typ t1
             value v
             typ t2

  | OP_GetElementPtr (t, tv, tvl) ->
    fprintf ppf "getelementptr %a, %a, %a"
             typ t
             tvalue tv
             (pp_print_list ~pp_sep:pp_comma_space tvalue) tvl

  | OP_Select (if_, then_, else_) ->
     fprintf ppf "select %a, %a, %a"
             tvalue if_
             tvalue then_
             tvalue else_

  | OP_ExtractElement (vec, idx) ->
     fprintf ppf "extractelement %a, %a"
             tvalue vec
             tvalue idx

  | OP_InsertElement (vec, new_val, idx) ->
     fprintf ppf "insertelement %a, %a, %a"
             tvalue vec
             tvalue new_val
             tvalue idx

  | OP_ExtractValue (agg, idx) ->
     fprintf ppf "extractvalue %a, %a"
             tvalue agg
             (pp_print_list ~pp_sep:pp_comma_space pp_print_int) (List.map to_int idx)

  | OP_InsertValue (agg, new_val, idx) ->
     fprintf ppf "insertvalue %a, %a, %a"
             tvalue agg
             tvalue new_val
             (pp_print_list ~pp_sep:pp_comma_space pp_print_int) (List.map to_int idx)

  | OP_ShuffleVector (v1, v2, mask) ->
     fprintf ppf "shufflevector %a, %a, %a"
             tvalue v1
             tvalue v2
             tvalue mask


and phi : Format.formatter -> Ollvm_ast.phi -> unit =
  fun ppf ->
  function
  | Phi (t, vil) ->
     fprintf ppf "phi %a [%a]"
             typ t
             (pp_print_list ~pp_sep:(pp_sep "], [")
                            (fun ppf (i, v) -> value ppf v ;
                                               pp_print_string ppf ", " ;
                                               lident ppf i)) vil


and instr : Format.formatter -> Ollvm_ast.instr -> unit =
  fun ppf ->
  function

  | INSTR_Op v -> inst_value ppf v

  | INSTR_Call (ti, tvl) ->
     fprintf ppf "call %a(%a)"
             tident ti
             (pp_print_list ~pp_sep:pp_comma_space tvalue) tvl

  | INSTR_Alloca (t, n, a) ->
     fprintf ppf "alloca %a" typ t ;
     (match n with None -> ()
                 | Some n -> fprintf ppf ", %a" tvalue n) ;
     (match a with None -> ()
                 | Some a -> fprintf ppf ", align %d" (to_int a))

  | INSTR_Load (vol, t, tv, a) ->
     pp_print_string ppf "load " ;
     if vol then pp_print_string ppf "volatile " ;
     (typ ppf t);
     pp_print_string ppf ", ";
     tvalue ppf tv ;
     (match a with None -> ()
                 | Some a -> fprintf ppf ", align %d" (to_int a))

  | INSTR_VAArg -> pp_print_string ppf "vaarg"



  | INSTR_LandingPad -> assert false

  | INSTR_Store (vol, v, ptr, a) ->
     pp_print_string ppf "store " ;
     if vol then pp_print_string ppf "volatile " ;
     fprintf ppf "%a, %a" tvalue v tvalue ptr ;
     (match a with None -> ()
                 | Some a -> fprintf ppf ", align %d" (to_int a))

  | INSTR_AtomicCmpXchg
  | INSTR_AtomicRMW
  | INSTR_Fence -> assert false
  | INSTR_Unreachable -> pp_print_string ppf "unreachable"


and branch_label : Format.formatter -> Ollvm_ast.raw_id -> unit =
  fun ppf id ->
    pp_print_string ppf "label %"; pp_print_string ppf (str_of_raw_id id)
    

and terminator : Format.formatter -> Ollvm_ast.terminator -> unit =
  fun ppf ->
  function

  | TERM_Ret (t, v)       -> fprintf ppf "ret %a" tvalue (t, v)

  | TERM_Ret_void         -> pp_print_string ppf "ret void"

  | TERM_Br (c, i1, i2)   ->
     fprintf ppf "br %a, %a, %a" tvalue c branch_label i1 branch_label i2

  | TERM_Br_1 i          -> fprintf ppf "br %a" branch_label i

  | TERM_Switch (c, def, cases) ->
     fprintf ppf "switch %a, %a [%a]"
             tvalue c
             branch_label def
             (pp_print_list ~pp_sep:pp_space
                            (fun ppf (v, i) -> tvalue ppf v ;
                                               pp_print_string ppf ", " ;
                                               branch_label ppf i)) cases

  | TERM_Resume (t, v) -> fprintf ppf "resume %a" tvalue (t, v)

  | TERM_IndirectBr (tv, til) ->
    fprintf ppf "indirectbr %a, [%a]"
      tvalue tv
      (pp_print_list ~pp_sep:pp_comma_space branch_label) til

  | TERM_Invoke (ti, tvl, i2, i3) ->
     fprintf ppf "invoke %a(%a) to %a unwind %a"
             tident ti
             (pp_print_list ~pp_sep:pp_comma_space tvalue) tvl
             branch_label i2
             branch_label i3

and id_instr : Format.formatter -> (Ollvm_ast.instr_id * Ollvm_ast.instr) -> unit =
  fun ppf ->
    function (id, inst) ->
      fprintf ppf "%a%a" instr_id id instr inst

and id_phi : Format.formatter -> (Ollvm_ast.local_id * Ollvm_ast.phi) -> unit =
  fun ppf ->
    function (id, p) ->
      fprintf ppf "%a%a" lident id phi p


and instr_id : Format.formatter -> Ollvm_ast.instr_id -> unit =
  fun ppf ->
    function
    | IId id  -> fprintf ppf "%%%s = " (str_of_raw_id id)
    | IVoid n -> fprintf ppf "; void instr %d" (to_int n); pp_force_newline ppf ()
  

and tvalue ppf (t, v) = fprintf ppf "%a %a" typ t value v

and tident ppf (t, v) = fprintf ppf "%a %a" typ t ident v

and toplevel_entities : Format.formatter -> (Ollvm_ast.block list) Ollvm_ast.toplevel_entities -> unit =
  fun ppf entries ->
  pp_print_list ~pp_sep:pp_force_newline toplevel_entity ppf entries

and toplevel_entity : Format.formatter -> (Ollvm_ast.block list) Ollvm_ast.toplevel_entity -> unit =
  fun ppf ->
  function
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

and metadata : Format.formatter -> Ollvm_ast.metadata -> unit =
  fun ppf ->
  function
  | METADATA_Const v  -> tvalue ppf v
  | METADATA_Null     -> pp_print_string ppf "null"
  | METADATA_Id i     -> fprintf ppf "!%s" (str_of_raw_id i)
  | METADATA_String s -> fprintf ppf "!%s" (of_str s)
  | METADATA_Node m   -> fprintf ppf "!{%a}"
                                 (pp_print_list ~pp_sep:pp_comma_space metadata) m
  | METADATA_Named m  -> fprintf ppf "!{%a}"
                                 (pp_print_list ~pp_sep:pp_comma_space
                                                (fun ppf i ->
                                                 fprintf ppf "!%s" i)) (List.map of_str m)
and global : Format.formatter -> Ollvm_ast.global -> unit =
  fun ppf ->
  fun {
    g_ident;
    g_typ;
    g_constant;
    g_value;

    g_linkage;
    g_visibility = visibility;
    g_dll_storage = gdll;

    g_section = s;
    g_align = a;
  } -> fprintf ppf "@%s = "  (str_of_raw_id g_ident);
       (match g_linkage with None -> ()
                           | Some l -> linkage ppf l; pp_print_string ppf " "
       );
       (fprintf ppf "%s %a" (if g_constant then "constant" else "global") typ g_typ) ;
       (match g_value with None -> () | Some v -> (pp_print_string ppf " "; value ppf v)) ;
       (match s with None -> ()
                   | Some s -> fprintf ppf ", section %s" (of_str s)) ;
       (match a with None -> ()
                   | Some a -> fprintf ppf ", align %d" (to_int a))

and declaration : Format.formatter -> Ollvm_ast.declaration -> unit =
  fun ppf ->
  fun { dc_name = i
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
    
and definition : Format.formatter -> (Ollvm_ast.block list) Ollvm_ast.definition -> unit =
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
       } as df) ->
    let (ret_t, args_t) = get_function_type dc_type in
    let typ_attr_id =
      fun ppf ((t, attrs), id) ->
        typ ppf t ;
        pp_space ppf () ;
        if attrs <> [] then (pp_print_list ~pp_sep:pp_space
                               param_attr ppf attrs ;
                             pp_space ppf ()) ;
        lident ppf id
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
    pp_print_list ~pp_sep:pp_force_newline block ppf df.df_instrs ;
    pp_force_newline ppf () ;
    pp_print_char ppf '}' ;

and block : Format.formatter -> Ollvm_ast.block -> unit =
  fun ppf {blk_id=lbl; blk_phis=phis; blk_code=b; blk_term=(_,t)} ->
    begin match lbl with
      | Anon i -> fprintf ppf "; <label> %d" (to_int i)
      | Name s -> (pp_print_string ppf (of_str s); pp_print_char ppf ':')
      | Raw i -> fprintf ppf "_RAW_%d:" (to_int i)
    end;
    pp_force_newline ppf () ;
    pp_print_string ppf "  ";
    pp_open_box ppf 0 ;
    pp_print_list ~pp_sep:pp_force_newline id_phi ppf phis ;
    pp_print_list ~pp_sep:pp_force_newline id_instr ppf b ;
    pp_force_newline ppf () ;
    terminator ppf t;
    pp_close_box ppf ()

and modul : Format.formatter -> (Ollvm_ast.block list) Ollvm_ast.modul -> unit =
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
