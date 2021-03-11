(*  ------------------------------------------------------------------------- *)
(* Adapted for use in Vellvm by Steve Zdancewic (c) 2017                      *)
(*  ------------------------------------------------------------------------- *)

open Format

let str = Camlcoq.coqstring_of_camlstring
let of_str = Camlcoq.camlstring_of_coqstring
let n_to_int = Camlcoq.N.to_int
let to_int = Camlcoq.Z.to_int
let to_float = Camlcoq.camlfloat_of_coqfloat
let to_float32 = Camlcoq.camlfloat_of_coqfloat32

(* TODO: Use pp_option everywhere instead of inlined matching *)
let pp_option ppf f o =
  match o with
  | None -> ()
  | Some x -> f ppf x

let pp_print_option f ppf o =
  match o with
  | None -> pp_print_string ppf "None"
  | Some x -> pp_print_string ppf "(Some "; f ppf x; pp_print_string ppf ")"

let pp_print_int ppf n =
  fprintf ppf "%d%%Z" (to_int n)

(* Backward compatibility with 4.01.0 *)
let rec pp_print_list ?(pp_sep = Format.pp_print_cut) pp_v ppf = function
| [] -> ()
| v :: vs ->
    pp_v ppf v; if vs <> [] then (pp_sep ppf ();
                                  pp_print_list ~pp_sep pp_v ppf vs)

let pp_print_prod pp_v1 pp_v2 ppf =
  fun te ->
    pp_print_string ppf "(";
    pp_v1 ppf (fst te);
    pp_print_string ppf ",";
    pp_v2 ppf (snd te);
    pp_print_string ppf ")"

open LLVMAst

let get_function_type dc_type =
  match dc_type with
  | TYPE_Function(ret,args) -> (ret,args)
  | _ -> failwith "not a function type"

let pp_sep str =
  fun ppf () -> pp_print_string ppf str

let pp_space ppf () = pp_print_char ppf ' '

let pp_comma_space ppf () = pp_print_string ppf ", "
let pp_sc_space ppf () = pp_print_string ppf "; "

let rec str_of_raw_id : LLVMAst.raw_id -> string =
    function
    | Anon i -> Printf.sprintf "(Anon %d%%Z)" (to_int i)
    | Name s -> Printf.sprintf "(Name \"%s\")" (of_str s)
    | Raw i -> Printf.sprintf "(Raw %d%%Z)" (to_int i)

and raw_id : Format.formatter -> LLVMAst.raw_id -> unit =
  fun ppf i ->
    fprintf ppf "%s" (str_of_raw_id i);

and lident : Format.formatter -> LLVMAst.local_id -> unit =
  fun ppf i ->
    fprintf ppf "(ID_Local %s)" (str_of_raw_id i);

and gident : Format.formatter -> LLVMAst.global_id -> unit =
  fun ppf i ->
    fprintf ppf "(ID_Global %s)" (str_of_raw_id i);

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
  | TYPE_I i              -> fprintf ppf "(TYPE_I %d%%Z)" (n_to_int i)
  | TYPE_Pointer t        -> fprintf ppf "(TYPE_Pointer %a)" typ t ;
  | TYPE_Void             -> fprintf ppf "TYPE_Void"
  | TYPE_Function (t, tl) -> fprintf ppf "(TYPE_Function %a [%a])" typ t (pp_print_list ~pp_sep:pp_sc_space typ) tl

  | TYPE_Half             -> fprintf ppf "TYPE_Half"
  | TYPE_Float            -> fprintf ppf "TYPE_Float"
  | TYPE_Double           -> fprintf ppf "TYPE_Double"
  | TYPE_X86_fp80         -> fprintf ppf "TYPE_X86_fp80"
  | TYPE_Fp128            -> fprintf ppf "TYPE_Fp128"
  | TYPE_Ppc_fp128        -> fprintf ppf "TYPE_Ppc_fp128"
  | TYPE_Metadata         -> fprintf ppf "TYPE_Metadata"
  | TYPE_X86_mmx          -> fprintf ppf "TYPE_X86_mmx"
  | TYPE_Array (i, t)     -> fprintf ppf "(TYPE_Array %d%%Z %a)" (n_to_int i) typ t
  | TYPE_Struct tl        -> fprintf ppf "(TYPE_Struct [%a])" (pp_print_list ~pp_sep:pp_sc_space typ) tl
  | TYPE_Packed_struct tl -> fprintf ppf "(TYPE_Packed_struct [%a])" (pp_print_list ~pp_sep:pp_sc_space typ) tl
  | TYPE_Opaque           -> fprintf ppf "TYPE_Opaque"
  | TYPE_Vector (i, t)    -> fprintf ppf "(TYPE_Vector %d%%Z %a)" (n_to_int i) typ t
  | TYPE_Identified i     -> fprintf ppf "(TYPE_Identified %a)" ident i

and icmp : Format.formatter -> LLVMAst.icmp -> unit =
  fun ppf icmp ->
  fprintf ppf ( match icmp with
                | Eq  -> "Eq"
                | Ne  -> "Ne"
                | Ugt -> "Ugt"
                | Uge -> "Uge"
                | Ult -> "Ult"
                | Ule -> "Ule"
                | Sgt -> "Sgt"
                | Sge -> "Sge"
                | Slt -> "Slt"
                | Sle -> "Sle")

and fcmp : Format.formatter -> LLVMAst.fcmp -> unit =
  fun ppf fcmp ->
  fprintf ppf ( match fcmp with
                | FFalse -> "FFalse"
                | FOeq   -> "FOeq"
                | FOgt   -> "FOgt"
                | FOge   -> "FOge"
                | FOlt   -> "FOlt"
                | FOle   -> "FOle"
                | FOne   -> "FOne"
                | FOrd   -> "FOrd"
                | FUno   -> "FUno"
                | FUeq   -> "FUeq"
                | FUgt   -> "FUgt"
                | FUge   -> "FUge"
                | FUlt   -> "FUlt"
                | FUle   -> "FUle"
                | FUne   -> "FUne"
                | FTrue  -> "FTrue")

and ibinop : Format.formatter -> LLVMAst.ibinop -> unit =
  fun ppf ->
  let nuw ppf flag = if flag then fprintf ppf " true " else fprintf ppf " false " in
  let nsw ppf flag = if flag then fprintf ppf "true)" else fprintf ppf "false)" in
  let exact ppf flag = if flag then fprintf ppf " true)" else fprintf ppf " false)" in
   function
  | Add (nu, ns) -> fprintf ppf "(Add" ; nuw ppf nu ; nsw ppf ns
  | Sub (nu, ns) -> fprintf ppf "(Sub" ; nuw ppf nu ; nsw ppf ns
  | Mul (nu, ns) -> fprintf ppf "(Mul" ; nuw ppf nu ; nsw ppf ns
  | UDiv e       -> fprintf ppf "(UDiv" ; exact ppf e
  | SDiv e       -> fprintf ppf "(SDiv" ; exact ppf e
  | URem         -> fprintf ppf "URem"
  | SRem         -> fprintf ppf "SRem"
  | Shl (nu, ns) -> fprintf ppf "(Shl" ; nuw ppf nu ; nsw ppf ns
  | LShr e       -> fprintf ppf "(LShr" ; exact ppf e
  | AShr e       -> fprintf ppf "(AShr" ; exact ppf e
  | And          -> fprintf ppf "And"
  | Or           -> fprintf ppf "Or"
  | Xor          -> fprintf ppf "Xor"

and fbinop =
  fun ppf fbinop ->
  fprintf ppf (match fbinop with
                 | FAdd -> "FAdd"
                 | FSub -> "FSub"
                 | FMul -> "FMul"
                 | FDiv -> "FDiv"
                 | FRem -> "FRem")

and fast_math =
  fun ppf fast_math ->
  pp_print_string ppf (match fast_math with
                       | Nnan -> "Nnan"
                       | Ninf -> "Ninf"
                       | Nsz  -> "Nsz"
                       | Arcp -> "Arcp"
                       | Fast -> "Fast")

and conversion_type : Format.formatter -> LLVMAst.conversion_type -> unit =
  fun ppf conv ->
  fprintf ppf (match conv with
               | Trunc    -> "Trunc"
               | Zext     -> "Zext"
               | Sext     -> "Sext"
               | Fptrunc  -> "Fptrunc"
               | Fpext    -> "Fpext"
               | Uitofp   -> "Uitofp"
               | Sitofp   -> "Sitofp"
               | Fptoui   -> "Fptoui"
               | Fptosi   -> "Fptosi"
               | Inttoptr -> "Inttoptr"
               | Ptrtoint -> "Ptrtoint"
               | Bitcast  -> "Bitcast")

and exp : Format.formatter -> (LLVMAst.typ LLVMAst.exp) -> unit =
  fun (ppf:Format.formatter) vv ->
    match vv with
    | EXP_Ident i           ->
      pp_print_string ppf "(EXP_Ident ";
      ident ppf i;
      pp_print_string ppf ")";

    | EXP_Integer i         ->
      fprintf ppf "(EXP_Integer (%d)%%Z)" (to_int i);

    | EXP_Float f           ->
      fprintf ppf "(EXP_Float %f)" (to_float32 f)

    | EXP_Bool b            ->
      fprintf ppf "(EXP_Bool %B)" b

    | EXP_Double f          ->
      fprintf ppf "(EXP_Double %f)" (to_float f)

    | EXP_Hex h             ->
      fprintf ppf "(EXP_Hex %f)" (to_float h)

    | EXP_Null              ->
      pp_print_string ppf "EXP_Null"

    | EXP_Undef             ->
      pp_print_string ppf "EXP_Undef"

    | EXP_Array tvl         ->
      fprintf ppf "(EXP_Array [%a])"
        (pp_print_list ~pp_sep:pp_sc_space (pp_print_prod typ exp)) tvl

    | EXP_Vector tvl        ->
      fprintf ppf "(EXP_Vector [%a])"
        (pp_print_list ~pp_sep:pp_sc_space (pp_print_prod typ exp)) tvl

    | EXP_Struct tvl        ->
      fprintf ppf "(EXP_Struct [%a])"
        (pp_print_list ~pp_sep:pp_sc_space (pp_print_prod typ exp)) tvl

    | EXP_Packed_struct tvl ->
      fprintf ppf "(EXP_Packed_struct [%a])"
        (pp_print_list ~pp_sep:pp_sc_space (pp_print_prod typ exp)) tvl

    | EXP_Zero_initializer  -> pp_print_string ppf "EXP_Zero_initializer"

    | EXP_Cstring tvl         ->
      fprintf ppf "(EXP_Cstring [%a])"
        (pp_print_list ~pp_sep:pp_sc_space (pp_print_prod typ exp)) tvl

    | OP_IBinop (op, t, v1, v2) ->
      fprintf ppf "(OP_IBinop %a %a %a %a)"
        ibinop op
        typ t
        exp v1
        exp v2

    | OP_ICmp (c, t, v1, v2) ->
     fprintf ppf "(OP_ICmp %a %a %a %a)"
        icmp c
        typ t
        exp v1
        exp v2

  | OP_FBinop (op, f, t, v1, v2) ->
     fprintf ppf "(OP_FBinop %a %a %a %a %a)"
        fbinop op
        (pp_print_list ~pp_sep:pp_sc_space fast_math) f
        typ t
        exp v1
        exp v2

  | OP_FCmp (c, t, v1, v2) ->
     fprintf ppf "(OP_FCmp %a %a %a %a)"
        fcmp c
        typ t
        exp v1
        exp v2

  | OP_Conversion (c, t1, v, t2) ->
     fprintf ppf "(OP_Conversion %a %a %a %a)"
        conversion_type c
        typ t1
        exp v
        typ t2

  | OP_GetElementPtr (t, tv, tvl) ->
     fprintf ppf "(OP_GetElementPtr %a %a [%a])"
       typ t
       (pp_print_prod typ exp) tv
       (pp_print_list ~pp_sep:pp_sc_space (pp_print_prod typ exp)) tvl

  | OP_Select (if_, then_, else_) ->
     fprintf ppf "(OP_Select %a %a %a)"
       (pp_print_prod typ exp) if_
       (pp_print_prod typ exp) then_
       (pp_print_prod typ exp) else_

  | OP_Freeze (v) ->
    fprintf ppf "(OP_Freeze %a)"
      (pp_print_prod typ exp) v

  | OP_ExtractElement (vec, idx) ->
     fprintf ppf "(OP_ExtractElement %a %a)"
       (pp_print_prod typ exp) vec
       (pp_print_prod typ exp) idx

  | OP_InsertElement (vec, new_val, idx) ->
     fprintf ppf "(OP_InsertElement %a %a %a)"
       (pp_print_prod typ exp) vec
       (pp_print_prod typ exp) new_val
       (pp_print_prod typ exp) idx

  | OP_ExtractValue (agg, idx) ->
      fprintf ppf "(OP_ExtractValue %a [%a])"
       (pp_print_prod typ exp) agg
       (pp_print_list ~pp_sep:pp_sc_space (fun ppf i -> fprintf ppf "%d%%Z" (to_int i))) idx

  | OP_InsertValue (agg, new_val, idx) ->
     fprintf ppf "(OP_InsertValue %a %a [%a])"
       (pp_print_prod typ exp) agg
       (pp_print_prod typ exp) new_val
       (pp_print_list ~pp_sep:pp_sc_space (fun ppf i -> fprintf ppf "%d%%Z" (to_int i))) idx

  | OP_ShuffleVector (v1, v2, mask) ->
     fprintf ppf "(OP_ShuffleVector %a %a %a)"
       (pp_print_prod typ exp) v1
       (pp_print_prod typ exp) v2
       (pp_print_prod typ exp) mask

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
  | EXP_Cstring _ -> assert false (* there should be no "raw" exps as instructions *)

  | OP_IBinop (op, t, v1, v2) ->
    fprintf ppf "(OP_IBinop %a %a %a %a)"
      ibinop op
      typ t
      exp v1
      exp v2

  | OP_ICmp (c, t, v1, v2) ->
    fprintf ppf "(OP_ICmp %a %a %a %a)"
      icmp c
      typ t
      exp v1
      exp v2

  | OP_FBinop (op, f, t, v1, v2) ->
    fprintf ppf "(OP_FBinop %a %a %a %a %a)"
      fbinop op
      (pp_print_list ~pp_sep:pp_sc_space fast_math) f
      typ t
      exp v1
      exp v2

  | OP_FCmp (c, t, v1, v2) ->
    fprintf ppf "(OP_FCmp %a %a %a %a)"
      fcmp c
      typ t
      exp v1
      exp v2

  | OP_Conversion (c, t1, v, t2) ->
    fprintf ppf "(OP_Conversion %a %a %a %a)"
      conversion_type c
      typ t1
      exp v
      typ t2

  | OP_GetElementPtr (t, tv, tvl) ->
    fprintf ppf "(OP_GetElementPtr %a %a [%a])"
      typ t
      (pp_print_prod typ exp) tv
      (pp_print_list ~pp_sep:pp_sc_space (pp_print_prod typ exp)) tvl

  | OP_Select (if_, then_, else_) ->
    fprintf ppf "(OP_Select %a %a %a)"
      (pp_print_prod typ exp) if_
      (pp_print_prod typ exp) then_
      (pp_print_prod typ exp) else_

  | OP_Freeze (v) ->
    fprintf ppf "(OP_Freeze %a)"
      (pp_print_prod typ exp) v


  | OP_ExtractElement (vec, idx) ->
    fprintf ppf "(OP_ExtractElement %a %a)"
      (pp_print_prod typ exp) vec
      (pp_print_prod typ exp) idx

  | OP_InsertElement (vec, new_val, idx) ->
    fprintf ppf "(OP_InsertElement %a %a %a)"
      (pp_print_prod typ exp) vec
      (pp_print_prod typ exp) new_val
      (pp_print_prod typ exp) idx

  | OP_ExtractValue (agg, idx) ->
    fprintf ppf "(OP_ExtractValue %a [%a]%%Z)"
      (pp_print_prod typ exp) agg
      (pp_print_list ~pp_sep:pp_sc_space (fun ppf i -> fprintf ppf "%d%%Z" (to_int i))) idx

  | OP_InsertValue (agg, new_val, idx) ->
    fprintf ppf "(OP_InsertValue %a %a [%a]%%Z)"
      (pp_print_prod typ exp) agg
      (pp_print_prod typ exp) new_val
      (pp_print_list ~pp_sep:pp_sc_space (fun ppf i -> fprintf ppf "%d%%Z" (to_int i))) idx

  | OP_ShuffleVector (v1, v2, mask) ->
    fprintf ppf "(OP_ShuffleVector %a %a %a)"
      (pp_print_prod typ exp) v1
      (pp_print_prod typ exp) v2
      (pp_print_prod typ exp) mask

and phi : Format.formatter -> (LLVMAst.typ LLVMAst.phi) -> unit =
  fun ppf ->
    function
    | Phi (t, vil) ->
      fprintf ppf "Phi %a [%a]"
        typ t
        (pp_print_list ~pp_sep:(pp_sep "; ")
           (fun ppf (i, v) ->
              fprintf ppf "(%s, " (str_of_raw_id i);
              exp ppf v;
              pp_print_string ppf ")"
           )) vil


and instr : Format.formatter -> (LLVMAst.typ LLVMAst.instr) -> unit =
  fun ppf ->
  function

  | INSTR_Comment msg ->  fprintf ppf "(INSTR_Comment %s)" (of_str msg)

  | INSTR_Op v ->
    pp_print_string ppf "(INSTR_Op ";
    inst_exp ppf v;
    pp_print_string ppf ")";

  | INSTR_Call (tv, tvl) ->
    fprintf ppf "(INSTR_Call %a [%a])"
             texp tv
             (pp_print_list ~pp_sep:pp_sc_space texp) tvl

  | INSTR_Alloca (t, n, a) ->
    fprintf ppf "(INSTR_Alloca %a %a %a)"
    typ t
    (pp_print_option texp) n
    (pp_print_option pp_print_int) a

  | INSTR_Load (vol, t, tv, a) ->
    fprintf ppf "(INSTR_Load %B %a %a %a)" vol
      typ t
      texp tv
      (pp_print_option pp_print_int) a

  | INSTR_Store (vol, v, ptr, a) ->
    fprintf ppf "(INSTR_Store %B %a %a %a)" vol
      texp v
      texp ptr
      (pp_print_option pp_print_int) a

  | INSTR_VAArg -> pp_print_string ppf "INSTR_VAarg"
  | INSTR_LandingPad
  | INSTR_AtomicCmpXchg
  | INSTR_AtomicRMW
  | INSTR_Fence -> assert false

and branch_label : Format.formatter -> LLVMAst.raw_id -> unit =
  fun ppf id ->
    pp_print_string ppf (str_of_raw_id id)

and tint_literal : Format.formatter -> LLVMAst.tint_literal -> unit =
  fun ppf (TInt_Literal(sz, n)) ->
           fprintf ppf "TInt_Literal (%d)%%Z) (%d)%%Z)" (n_to_int sz) (to_int n)


and terminator : Format.formatter -> (LLVMAst.typ LLVMAst.terminator) -> unit =
  fun ppf ->
  function

  | TERM_Ret (t, v)       -> fprintf ppf "TERM_Ret %a" texp (t, v)

  | TERM_Ret_void         -> pp_print_string ppf "TERM_Ret_void"

  | TERM_Br (c, i1, i2)   ->
    fprintf ppf "TERM_Br %a %a %a" texp c branch_label i1 branch_label i2

  | TERM_Br_1 i          -> fprintf ppf "TERM_Br_1 %a" branch_label i

  | TERM_Switch (c, def, cases) ->
    fprintf ppf "TERM_Switch %a %a %a"
      texp c
      raw_id def
      (pp_print_list ~pp_sep:pp_sc_space (pp_print_prod tint_literal raw_id)) cases

  | TERM_Resume tv ->
    fprintf ppf "TERM_Resume %a"
     texp tv

  | TERM_IndirectBr (tv, til) ->
    fprintf ppf "TERM_IndirectBr %a %a"
      texp tv
      (pp_print_list ~pp_sep:pp_sc_space raw_id) til

  | TERM_Invoke (ti, tvl, i2, i3) ->
    fprintf ppf "TERM_Invoke %a %a %a %a"
      tident ti
      (pp_print_list ~pp_sep:pp_sc_space texp) tvl
      raw_id i2
      raw_id i3

  | TERM_Unreachable -> pp_print_string ppf "TERM_Unreachable"


and id_instr : Format.formatter -> (LLVMAst.instr_id * (LLVMAst.typ LLVMAst.instr)) -> unit =
  fun ppf ->
    function (id, inst) ->
      fprintf ppf "(%a, %a)" instr_id id instr inst

and id_phi : Format.formatter -> (LLVMAst.local_id * (LLVMAst.typ LLVMAst.phi)) -> unit =
  fun ppf ->
    function (id, p) ->
      fprintf ppf "(%s, %a)" (str_of_raw_id id) phi p


and instr_id : Format.formatter -> LLVMAst.instr_id -> unit =
  fun ppf ->
    function
    | IId id  -> fprintf ppf "IId %s" (str_of_raw_id id)
    | IVoid n -> fprintf ppf "IVoid %d%%Z" (to_int n)


and texp ppf (t, v) = fprintf ppf "(%a, %a)" typ t exp v

and tident ppf (t, v) = fprintf ppf "(%a, %a)" typ t ident v

and toplevel_entities : Format.formatter -> (LLVMAst.typ, (LLVMAst.typ LLVMAst.block) * ((LLVMAst.typ LLVMAst.block) list)) LLVMAst.toplevel_entities -> unit =
  fun ppf entries ->
    pp_print_string ppf "[";
    pp_print_list ~pp_sep:(fun ppf () -> pp_sc_space ppf (); pp_force_newline ppf ()) toplevel_entity ppf entries;
    pp_print_string ppf "].";
    pp_print_flush ppf ();

and toplevel_entity : Format.formatter -> (LLVMAst.typ, (LLVMAst.typ LLVMAst.block) * ((LLVMAst.typ LLVMAst.block) list)) LLVMAst.toplevel_entity -> unit =
  fun ppf ->
  function
  | TLE_Comment msg            -> fprintf ppf "TLE_Comment %s" (of_str msg)
  | TLE_Target s               -> fprintf ppf "TLE_Target %s" (of_str s)
  | TLE_Datalayout s           -> fprintf ppf "TLE_Datalayout %s" (of_str s)
  | TLE_Source_filename s      -> fprintf ppf "TLE_Source_filename %s" (of_str s)
  | TLE_Declaration d          -> fprintf ppf "TLE_Declaration %a" declaration d
  | TLE_Definition d           -> fprintf ppf "TLE_Definition %a" definition d
  | TLE_Type_decl (i, t)       -> fprintf ppf "TLE_Type_decl %a %a" ident i typ t
  | TLE_Global g               -> fprintf ppf "TLE_Global %a" global g
  | TLE_Metadata (i, m)        -> fprintf ppf "TLE_Metadata %a %a" raw_id i metadata m
  | TLE_Attribute_group (i, a) -> fprintf ppf "TLE_Attribute_group %d%%Z [%a]" (to_int i)
                                  (pp_print_list ~pp_sep:pp_sc_space fn_attr) a

and metadata : Format.formatter -> (LLVMAst.typ LLVMAst.metadata) -> unit =
  fun ppf ->
  function
  | METADATA_Const v  -> fprintf ppf "METADATA_Const %a" texp v
  | METADATA_Null     -> fprintf ppf "METADA_Null"
  | METADATA_Id i     -> fprintf ppf "METADATA_Id %a" raw_id i
  | METADATA_String s -> fprintf ppf "METADATA_String %s" (of_str s)
  | METADATA_Node m   -> fprintf ppf "METADATA_Node [%a]" (pp_print_list ~pp_sep:pp_sc_space metadata) m
  | METADATA_Named m  -> fprintf ppf "METADAT_Named [%a]"
                           (pp_print_list ~pp_sep:pp_sc_space (fun ppf s -> fprintf ppf "%s" (of_str s))) m

and param_attr : Format.formatter -> LLVMAst.param_attr -> unit =
  fun ppf ->
  function
  | PARAMATTR_Zeroext -> pp_print_string ppf "PARAMATTR_Zeroext"
  | PARAMATTR_Signext  -> pp_print_string ppf "PARAMATTR_Signext"
  | PARAMATTR_Inreg -> pp_print_string ppf "PARAMATTR_Inreg"
  | PARAMATTR_Byval -> pp_print_string ppf "PARAMATTR_Byval"
  | PARAMATTR_Inalloca -> pp_print_string ppf "PARAMATTR_Inalloca"
  | PARAMATTR_Sret -> pp_print_string ppf "PARAMATTR_Sret"
  | PARAMATTR_Align n -> fprintf ppf "PARAMATTR_Align %d%%Z" (to_int n)
  | PARAMATTR_Noalias -> pp_print_string ppf "PARAMATTR_Noalias"
  | PARAMATTR_Nocapture -> pp_print_string ppf "PARAMATTR_Nocapture"
  | PARAMATTR_Readonly -> pp_print_string ppf "PARAMATTR_Readonly"
  | PARAMATTR_Nest -> pp_print_string ppf "PARAMATTR_Nest"
  | PARAMATTR_Returned  -> pp_print_string ppf "PARAMATTR_Returned"
  | PARAMATTR_Nonnull -> pp_print_string ppf "PARAMATTR_Nonnull"
  | PARAMATTR_Dereferenceable n -> fprintf ppf "PARAMATTR_Dereferenceable %d%%Z" (to_int n)
  | PARAMATTR_Immarg -> fprintf ppf "PARAMATTR_Immarg"
  | PARAMATTR_Noundef -> fprintf ppf "PARAMATTR_Noundef"
  | PARAMATTR_Nofree -> fprintf ppf "PARAMATTR_Nofree"

and thread_local_storage : Format.formatter -> LLVMAst.thread_local_storage -> unit =
  fun ppf ->
  function
  | TLS_Localdynamic -> pp_print_string ppf "TLS_Localdynamic"
  | TLS_Initialexec -> pp_print_string ppf "TLS_Initialexec"
  | TLS_Localexec -> pp_print_string ppf "TLS_Localexec"

and global : Format.formatter -> (LLVMAst.typ LLVMAst.global) -> unit =
  fun ppf ->
  fun {
    g_ident = i
    ; g_typ = t
    ; g_constant = c
    ; g_exp = oe
    ; g_linkage = olink
    ; g_visibility = ovis
    ; g_dll_storage = ost
    ; g_thread_local = otls
    ; g_unnamed_addr = uad
    ; g_addrspace = adds
    ; g_externally_initialized = ei
    ; g_section = os
    ; g_align = oa
  } ->
    pp_print_string ppf "{|";
    pp_open_box ppf 0;

    fprintf ppf "g_ident := %s;" (str_of_raw_id i);
    pp_force_newline ppf ();

    fprintf ppf "g_typ := %a;" typ t;
    pp_force_newline ppf ();

    fprintf ppf "g_constant := %B;" c;
    pp_force_newline ppf ();

    fprintf ppf "g_exp := %a;" (pp_print_option exp) oe;
    pp_force_newline ppf ();

    fprintf ppf "g_linkage := %a;" (pp_print_option linkage) olink;
    pp_force_newline ppf ();

    fprintf ppf "g_visibility := %a;" (pp_print_option visibility) ovis;
    pp_force_newline ppf ();

    fprintf ppf "g_dll_storage := %a;" (pp_print_option dll_storage) ost;
    pp_force_newline ppf ();

    fprintf ppf "g_thread_local := %a;" (pp_print_option thread_local_storage) otls;
    pp_force_newline ppf ();

    fprintf ppf "g_unnamed_addr := %B;" uad;
    pp_force_newline ppf ();

    fprintf ppf "g_addrspace := %a;" (pp_print_option (fun ppf s -> fprintf ppf "%d%%Z" (to_int s))) adds;
    pp_force_newline ppf ();

    fprintf ppf "g_externally_initialized := %B;" ei;
    pp_force_newline ppf ();

    fprintf ppf "g_section := %a;" (pp_print_option (fun ppf s -> fprintf ppf "%s" (of_str s))) os;
    pp_force_newline ppf ();

    fprintf ppf "g_align := %a" (pp_print_option (fun ppf s -> fprintf ppf "%d%%Z" (to_int s))) oa;
    pp_print_string ppf "|}";

    pp_close_box ppf ();

and linkage : Format.formatter -> LLVMAst.linkage -> unit =
  fun ppf ->
  function
  | LINKAGE_Private -> pp_print_string ppf "LINKAGE_Private"
  | LINKAGE_Internal -> pp_print_string ppf "LINKAGE_Internal"
  | LINKAGE_Available_externally -> pp_print_string ppf "LINKAGE_Available_externally"
  | LINKAGE_Linkonce -> pp_print_string ppf "LINKAGE_Linkonce"
  | LINKAGE_Weak -> pp_print_string ppf "LINKAGE_Weak"
  | LINKAGE_Common -> pp_print_string ppf "LINKAGE_Common"
  | LINKAGE_Appending -> pp_print_string ppf "LINKAGE_Appending"
  | LINKAGE_Extern_weak -> pp_print_string ppf "LINKAGE_Extern_weak"
  | LINKAGE_Linkonce_odr -> pp_print_string ppf "LINKAGE_Linkonce_odr"
  | LINKAGE_Weak_odr -> pp_print_string ppf "LINKAGE_Weak_odr"
  | LINKAGE_External -> pp_print_string ppf "LINKAGE_External"

and visibility : Format.formatter -> LLVMAst.visibility -> unit =
  fun ppf ->
  function
  | VISIBILITY_Default -> pp_print_string ppf "VISIBILITY_Default"
  | VISIBILITY_Hidden  -> pp_print_string ppf "VISIBILITY_Hidden"
  | VISIBILITY_Protected -> pp_print_string ppf "VISIBILITY_Protected"

and dll_storage : Format.formatter -> LLVMAst.dll_storage -> unit =
  fun ppf ->
  function
  | DLLSTORAGE_Dllimport -> pp_print_string ppf "DLLSTORAGE_Dllimport"
  | DLLSTORAGE_Dllexport -> pp_print_string ppf "DLLSTORAGE_Dllexport"

and cconv : Format.formatter -> LLVMAst.cconv -> unit =
  fun ppf ->
  function
  | CC_Ccc -> pp_print_string ppf "CC_Ccc"
  | CC_Fastcc -> pp_print_string ppf "CC_Fastcc"
  | CC_Coldcc -> pp_print_string ppf "CC_Coldcc"
  | CC_Cc n -> fprintf ppf "CC_Cc %d%%Z" (to_int n)

and llvm_int : Format.formatter -> LLVMAst.int -> unit =
  fun ppf i -> fprintf ppf "%d%%Z" (to_int i)

and fn_attr : Format.formatter -> LLVMAst.fn_attr -> unit =
  fun ppf ->
  function
  | FNATTR_Alignstack n -> fprintf ppf "FNATTR_Alignstack %a" llvm_int n
  | FNATTR_Allocsize l ->
     fprintf ppf "FNATTR_Allocsize (%a)" (pp_print_list ~pp_sep:pp_sc_space llvm_int) l
  | FNATTR_Alwaysinline -> pp_print_string ppf "FNATTR_Alwaysinline"
  | FNATTR_Builtin -> pp_print_string ppf "FNATTR_Builtin"
  | FNATTR_Cold -> pp_print_string ppf "FNATTR_Cold"
  | FNATTR_Convergent -> pp_print_string ppf "FNATTR_Convergent"
  | FNATTR_Hot -> pp_print_string ppf "FNATTR_Hot"
  | FNATTR_Inaccessiblememonly -> pp_print_string ppf "FNATTR_Inaccessiblememonly"
  | FNATTR_Inaccessiblemem_or_argmemonly-> pp_print_string ppf "FNATTR_Inaccessible_or_argmemonly"
  | FNATTR_Inlinehint -> pp_print_string ppf "FNATTR_Inlinehint"
  | FNATTR_Jumptable -> pp_print_string ppf "FNATTR_Jumptable"
  | FNATTR_Minsize -> pp_print_string ppf "FNATTR_Minsize"
  | FNATTR_Naked -> pp_print_string ppf "FNATTR_Naked"
  | FNATTR_No_jump_tables -> pp_print_string ppf "FNATTR_No_jump_tables"
  | FNATTR_Nobuiltin -> pp_print_string ppf "FNATTR_Nobuiltin"
  | FNATTR_Noduplicate -> pp_print_string ppf "FNATTR_Noduplicate"
  | FNATTR_Nofree -> pp_print_string ppf "FNATTR_Nofree"
  | FNATTR_Noimplicitfloat -> pp_print_string ppf "FNATTR_Noimplicitfloat"
  | FNATTR_Noinline -> pp_print_string ppf "FNATTR_Noinline"
  | FNATTR_Nomerge -> pp_print_string ppf "FNATTR_Nomerge"
  | FNATTR_Nonlazybind -> pp_print_string ppf "FNATTR_Nonlazybind"
  | FNATTR_Noredzone -> pp_print_string ppf "FNATTR_Noredzone"
  | FNATTR_Indirect_tls_seg_refs -> pp_print_string ppf "FNATTR_Indirect_tls_seg_refs"
  | FNATTR_Noreturn -> pp_print_string ppf "FNATTR_Noreturn"
  | FNATTR_Norecurse -> pp_print_string ppf "FNATTR_Norecurse"
  | FNATTR_Willreturn -> pp_print_string ppf "FNATTR_Willreturn"
  | FNATTR_Nosync -> pp_print_string ppf "FNATTR_Nosync"
  | FNATTR_Nounwind -> pp_print_string ppf "FNATTR_Nounwind"
  | FNATTR_Null_pointer_is_valid -> pp_print_string ppf "FNATTR_Null_pointer_is_valid"
  | FNATTR_Optforfuzzing -> pp_print_string ppf "FNATTR_Optforfuzzing"
  | FNATTR_Optnone -> pp_print_string ppf "FNATTR_Optnone"
  | FNATTR_Optsize -> pp_print_string ppf "FNATTR_Optsize"
  | FNATTR_Readnone -> pp_print_string ppf "FNATTR_Readnone"
  | FNATTR_Readonly -> pp_print_string ppf "FNATTR_Readonly"
  | FNATTR_Writeonly -> pp_print_string ppf "FNATTR_Writeonly"
  | FNATTR_Argmemonly -> pp_print_string ppf "FNATTR_Argmemonly"
  | FNATTR_Returns_twice -> pp_print_string ppf "FNATTR_Returns_twice"
  | FNATTR_Safestack -> pp_print_string ppf "FNATTR_Safestack"
  | FNATTR_Sanitize_address -> pp_print_string ppf "FNATTR_Sanitize_address"
  | FNATTR_Sanitize_memory -> pp_print_string ppf "FNATTR_Sanitize_memory"
  | FNATTR_Sanitize_thread -> pp_print_string ppf "FNATTR_Sanitize_thread"
  | FNATTR_Sanitize_hwaddress -> pp_print_string ppf "FNATTR_Sanitize_hwaddress"
  | FNATTR_Sanitize_memtag -> pp_print_string ppf "FNATTR_Santize_memtag"
  | FNATTR_Speculative_load_hardening -> pp_print_string ppf "FNATTR_Speculative_load_hardening"
  | FNATTR_Speculatable -> pp_print_string ppf "FNATTR_Speculatable"
  | FNATTR_Ssp -> pp_print_string ppf "FNATTR_Ssp"
  | FNATTR_Sspreq -> pp_print_string ppf "FNATTR_Sspreq"
  | FNATTR_Sspstrong -> pp_print_string ppf "FNATTR_Sspstrong"
  | FNATTR_Strictfp -> pp_print_string ppf "FNATTR_Strictfp"
  | FNATTR_Uwtable -> pp_print_string ppf "FNATTR_Uwtable"
  | FNATTR_Nocf_check -> pp_print_string ppf "FNATTR_Nocf_check"
  | FNATTR_Shadowcallstack -> pp_print_string ppf "FNATTR_Shadowcallstack"
  | FNATTR_Mustprogress -> pp_print_string ppf "FNATTR_Mustprogress"
  | FNATTR_String s -> fprintf ppf "FNATTR_String %s" (of_str s)
  | FNATTR_Key_value (s,s') -> fprintf ppf "FNATTR_Key_value (%s,%s)" (of_str s) (of_str s')
  | FNATTR_Attr_grp n  -> fprintf ppf "FNATTR_Attr_grp %d%%Z" (to_int n)

and declaration : Format.formatter -> (LLVMAst.typ LLVMAst.declaration) -> unit =
  fun ppf ->
  fun { dc_name = i
      ; dc_type = t
      ; dc_param_attrs = patt
      ; dc_linkage = link
      ; dc_visibility = vis
      ; dc_dll_storage = ost
      ; dc_cconv = occ
      ; dc_attrs = att
      ; dc_section = osec
      ; dc_align = oali
      ; dc_gc = ogc
      } ->
    pp_print_string ppf "{|";
    pp_open_box ppf 0;

    fprintf ppf "dc_name := %s;" (str_of_raw_id i);
    pp_force_newline ppf ();

    fprintf ppf "dc_type := %a;" typ t;
    pp_force_newline ppf ();

    fprintf ppf "dc_param_attrs := ([%a], [%a]);"
      (pp_print_list ~pp_sep:pp_sc_space param_attr) (fst patt)
      (pp_print_list (fun ppf l -> fprintf ppf "%a" (pp_print_list ~pp_sep:pp_sc_space param_attr) l)) (snd patt);
    pp_force_newline ppf ();

    fprintf ppf "dc_linkage := %a;" (pp_print_option linkage) link;
    pp_force_newline ppf ();

    fprintf ppf "dc_visibility := %a;" (pp_print_option visibility) vis;
    pp_force_newline ppf ();

    fprintf ppf "dc_dll_storage := %a;" (pp_print_option dll_storage) ost;
    pp_force_newline ppf ();

    fprintf ppf "dc_cconv := %a;" (pp_print_option cconv) occ;
    pp_force_newline ppf ();

    fprintf ppf "dc_attrs := [%a];" (pp_print_list ~pp_sep:pp_sc_space fn_attr) att;
    pp_force_newline ppf ();

    fprintf ppf "dc_section := %a;" (pp_print_option (fun ppf s -> fprintf ppf "%s" (of_str s))) osec;
    pp_force_newline ppf ();

    fprintf ppf "dc_align := %a;" (pp_print_option (fun ppf s -> fprintf ppf "%d%%Z" (to_int s))) oali;
    pp_force_newline ppf ();

    fprintf ppf "dc_gc := %a" (pp_print_option (fun ppf s -> fprintf ppf "%s" (of_str s))) ogc;
    pp_print_string ppf "|}";

    pp_close_box ppf ();

and definition : Format.formatter -> (LLVMAst.typ, (LLVMAst.typ LLVMAst.block) * ((LLVMAst.typ LLVMAst.block list))) LLVMAst.definition -> unit =
  fun ppf ->
  fun { df_prototype = df
      ; df_args = args
      ; df_instrs = ins
      } ->
    pp_print_string ppf "{|";

    pp_force_newline ppf ();

    pp_print_string ppf "  df_prototype := ";
    fprintf ppf "%a;" declaration df;

    pp_force_newline ppf ();

    pp_print_string ppf "  df_args := [";
    pp_print_list ~pp_sep:pp_sc_space (fun ppf id -> pp_print_string ppf (str_of_raw_id id))
      ppf args;
    pp_print_string ppf "];";

    pp_force_newline ppf ();

    pp_print_string ppf "  df_instrs := [";
    pp_open_box ppf 0;
    pp_force_newline ppf ();
    block ppf (fst ins); 
    pp_force_newline ppf ();
    pp_print_list ~pp_sep:(fun ppf () -> pp_print_string ppf ";"; pp_force_newline ppf ())
      block ppf (snd ins) ;
    pp_print_string ppf "]";
    pp_force_newline ppf ();

    pp_print_string ppf "|}";
    pp_close_box ppf ();
    pp_print_flush ppf ();

and block : Format.formatter -> LLVMAst.typ LLVMAst.block -> unit =
  fun ppf {blk_id=lbl; blk_phis=phis; blk_code=b; blk_term=t; blk_comments=cmts} ->
    pp_print_string ppf "{|";
    pp_force_newline ppf ();

    pp_print_string ppf "  blk_id := ";
    pp_print_string ppf (str_of_raw_id lbl);
    pp_print_string ppf ";";
    pp_force_newline ppf () ;

    pp_print_string ppf "  blk_phis := [";
    pp_open_box ppf 0;
    pp_print_list ~pp_sep:(fun ppf () -> pp_print_string ppf ";"; pp_force_newline ppf ())
      id_phi ppf phis ;
    pp_close_box ppf ();
    pp_print_string ppf "];";
    pp_force_newline ppf () ;

    pp_print_string ppf "  blk_code := [";
    pp_open_box ppf 0 ;
    pp_print_list ~pp_sep:(fun ppf () -> pp_print_string ppf ";"; pp_force_newline ppf ();)
      id_instr ppf b ;
    pp_print_string ppf "];";
    pp_close_box ppf ();
    pp_force_newline ppf () ;

    pp_print_string ppf "  blk_term := ";
    fprintf ppf "%a;" terminator t;
    pp_force_newline ppf () ;

    pp_print_string ppf "  blk_comments := ";
    fprintf ppf "%a"
      (pp_print_option
        (fun ppf l ->
            pp_print_list ~pp_sep:pp_force_newline
             (fun ppf s -> fprintf ppf "%s" (of_str s))
            ppf l)) cmts;
    pp_force_newline ppf () ;


    pp_print_string ppf "|}";

and modul : Format.formatter -> (LLVMAst.typ, (LLVMAst.typ LLVMAst.block) * ((LLVMAst.typ LLVMAst.block list))) CFG.modul -> unit =
  fun ppf m ->

  pp_option ppf (fun ppf x -> fprintf ppf "; ModuleID = '%s'" (of_str x)) m.m_name ;
  pp_force_newline ppf () ;

  pp_print_list ~pp_sep:pp_force_newline global ppf m.m_globals;
  pp_force_newline ppf () ;

  pp_print_list ~pp_sep:pp_force_newline declaration ppf m.m_declarations;
  pp_force_newline ppf () ;

  pp_print_list ~pp_sep:pp_force_newline definition ppf m.m_definitions;
  pp_force_newline ppf ()
