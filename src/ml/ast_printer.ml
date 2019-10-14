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
    | Anon i -> Printf.sprintf "Anon %d%%Z" (to_int i)
    | Name s -> Printf.sprintf "Name \"%s\"" (of_str s)
    | Raw i -> Printf.sprintf "Raw %d%%Z" (to_int i)

and lident : Format.formatter -> LLVMAst.local_id -> unit =
  fun ppf i ->
    fprintf ppf "ID_Local (%s)" (str_of_raw_id i);

and gident : Format.formatter -> LLVMAst.global_id -> unit =
  fun ppf i ->
    fprintf ppf "ID_Global (%s)" (str_of_raw_id i);

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
  | TYPE_I i              -> fprintf ppf "TYPE_Int (%d)" (to_int i)
  | TYPE_Pointer t        -> fprintf ppf "(TYPE_Pointer (%a))" typ t ;
  | TYPE_Void             -> fprintf ppf "TYPE_Void"
  | TYPE_Function (t, tl) -> fprintf ppf "(TYPE_Function (%a) [%a])" typ t (pp_print_list ~pp_sep:pp_sc_space typ) tl

  | TYPE_Half             -> fprintf ppf "todo"
  | TYPE_Float            -> fprintf ppf "todo"
  | TYPE_Double           -> fprintf ppf "todo"
  | TYPE_X86_fp80         -> fprintf ppf "todo"
  | TYPE_Fp128            -> fprintf ppf "todo"
  | TYPE_Ppc_fp128        -> fprintf ppf "todo"
  | TYPE_Metadata         -> fprintf ppf "todo"
  | TYPE_X86_mmx          -> fprintf ppf "todo"
  | TYPE_Array (i, t)     -> fprintf ppf "todo"
  | TYPE_Struct tl        -> fprintf ppf "todo"
  | TYPE_Packed_struct tl -> fprintf ppf "todo"
  | TYPE_Opaque           -> fprintf ppf "todo"
  | TYPE_Vector (i, t)    -> fprintf ppf "todo"
  | TYPE_Identified i     -> fprintf ppf "todo"

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
  | URem         -> fprintf ppf "(URem"
  | SRem         -> fprintf ppf "(SRem"
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
               | Trunc    -> "trunc"
               | Zext     -> "zext"
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
      pp_print_string ppf "(EXP_Ident (";
      ident ppf i;
      pp_print_string ppf "))";

    | EXP_Integer i         ->
      fprintf ppf "(EXP_Integer %d%%Z)" (to_int i);

    | EXP_Float f           ->
      fprintf ppf "todo"

    | EXP_Bool b            -> 
      fprintf ppf "todo"

    | EXP_Double f          ->
      fprintf ppf "todo"

    | EXP_Hex h             ->
      fprintf ppf "todo"

    | EXP_Null              ->
      pp_print_string ppf "EXP_Null"

    | EXP_Undef             ->
      pp_print_string ppf "EXP_Undef"

    | EXP_Array tvl         -> fprintf ppf "todo"

    | EXP_Vector tvl        -> fprintf ppf "todo"
    | EXP_Struct tvl        -> fprintf ppf "todo"
    | EXP_Packed_struct tvl -> fprintf ppf "todo"

    | EXP_Zero_initializer  -> pp_print_string ppf "EXP_Zero_initializer"

    | EXP_Cstring s -> fprintf ppf "(EXP_Cstring %s)" (of_str s)

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
     fprintf ppf "(OP_FBinop %a todo %a %a %a)"
        fbinop op
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
     fprintf ppf "todo"

  | OP_GetElementPtr (t, tv, tvl) ->
     fprintf ppf "todo"

  | OP_Select (if_, then_, else_) ->
     fprintf ppf "todo"

  | OP_ExtractElement (vec, idx) ->
     fprintf ppf "todo"

  | OP_InsertElement (vec, new_val, idx) ->
     fprintf ppf "todo"

  | OP_ExtractValue (agg, idx) ->
     fprintf ppf "todo"

  | OP_InsertValue (agg, new_val, idx) ->
     fprintf ppf "todo"

  | OP_ShuffleVector (v1, v2, mask) ->
     fprintf ppf "todo"

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
     fprintf ppf "(OP_FBinop %a todo %a %a %a)"
        fbinop op
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
     fprintf ppf "todo"
  | OP_GetElementPtr (t, tv, tvl) ->
     fprintf ppf "todo"
  | OP_Select (if_, then_, else_) ->
     fprintf ppf "todo"
  | OP_ExtractElement (vec, idx) ->
     fprintf ppf "todo"
  | OP_InsertElement (vec, new_val, idx) ->
     fprintf ppf "todo"
  | OP_ExtractValue (agg, idx) ->
     fprintf ppf "todo"

  | OP_InsertValue (agg, new_val, idx) ->
     fprintf ppf "todo"

  | OP_ShuffleVector (v1, v2, mask) ->
     fprintf ppf "todo"


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
    (match n with
       None   -> fprintf ppf "(INSTR_Alloca %a None todo)" typ t ;
     | Some n -> fprintf ppf "(INSTR_Alloca %a (Some %a) todo)" typ t texp n)

  | INSTR_Load (vol, t, tv, a) ->
    fprintf ppf "(INSTR_Load todo %a %a todo)"
      typ t
      texp tv

  | INSTR_Store (vol, v, ptr, a) ->
    fprintf ppf "(INSTR_Store todo %a %a todo)"
      texp v
      texp ptr

  | INSTR_VAArg -> pp_print_string ppf "INSTR_VAarg"
  | INSTR_LandingPad
  | INSTR_AtomicCmpXchg
  | INSTR_AtomicRMW
  | INSTR_Fence -> assert false
  | INSTR_Unreachable -> pp_print_string ppf "INSTR_Unreachable"

and branch_label : Format.formatter -> LLVMAst.raw_id -> unit =
  fun ppf id ->
    pp_print_string ppf (str_of_raw_id id)

and terminator : Format.formatter -> (LLVMAst.typ LLVMAst.terminator) -> unit =
  fun ppf ->
  function

  | TERM_Ret (t, v)       -> fprintf ppf "TERM_Ret %a" texp (t, v)

  | TERM_Ret_void         -> pp_print_string ppf "TERM_Ret_void"

  | TERM_Br (c, i1, i2)   ->
     fprintf ppf "TERM_Br %a (%a) (%a)" texp c branch_label i1 branch_label i2

  | TERM_Br_1 i          -> fprintf ppf "TERM_Br_1 (%a)" branch_label i

  | TERM_Switch (c, def, cases) ->
     fprintf ppf "todo"

  | TERM_Resume (t, v) ->
     fprintf ppf "todo"

  | TERM_IndirectBr (tv, til) ->
     fprintf ppf "todo"

  | TERM_Invoke (ti, tvl, i2, i3) ->
     fprintf ppf "todo"

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
    | IId id  -> fprintf ppf "IId (%s)" (str_of_raw_id id)
    | IVoid n -> fprintf ppf "IVoid %d%%Z" (to_int n)


and texp ppf (t, v) = fprintf ppf "(%a, %a)" typ t exp v

and tident ppf (t, v) = fprintf ppf "(%a, %a)" typ t ident v

and toplevel_entities : Format.formatter -> (LLVMAst.typ, ((LLVMAst.typ LLVMAst.block) list)) LLVMAst.toplevel_entities -> unit =
  fun ppf entries ->
    pp_print_string ppf "[";
    pp_print_list ~pp_sep:(fun ppf () -> pp_sc_space ppf (); pp_force_newline ppf ()) toplevel_entity ppf entries;
    pp_print_string ppf "].";
    pp_print_flush ppf ();

and toplevel_entity : Format.formatter -> (LLVMAst.typ, ((LLVMAst.typ LLVMAst.block) list)) LLVMAst.toplevel_entity -> unit =
  fun ppf ->
  function
  | TLE_Comment msg            -> fprintf ppf "todo"
  | TLE_Target s               -> fprintf ppf "todo"
  | TLE_Datalayout s           -> fprintf ppf "todo"
  | TLE_Source_filename s      -> fprintf ppf "todo"
  | TLE_Declaration d          -> declaration ppf d
  | TLE_Definition d           -> definition ppf d
  | TLE_Type_decl (i, t)       -> fprintf ppf "todo"
  | TLE_Global g               -> global ppf g
  | TLE_Metadata (i, m)        -> fprintf ppf "todo"
  | TLE_Attribute_group (i, a) -> fprintf ppf "todo"

and metadata : Format.formatter -> (LLVMAst.typ LLVMAst.metadata) -> unit =
  fun ppf ->
  function
  | METADATA_Const v  -> fprintf ppf "todo"
  | METADATA_Null     -> fprintf ppf "todo"
  | METADATA_Id i     -> fprintf ppf "todo"
  | METADATA_String s -> fprintf ppf "todo"
  | METADATA_Node m   -> fprintf ppf "todo"
  | METADATA_Named m  -> fprintf ppf "todo"

and global : Format.formatter -> (LLVMAst.typ LLVMAst.global) -> unit =
  fun ppf ->
  fun {
    g_ident;
    g_typ;
    g_constant;
    g_exp;
  } -> fprintf ppf "todo"

and declaration : Format.formatter -> (LLVMAst.typ LLVMAst.declaration) -> unit =
  fun ppf ->
  fun { dc_name = i
      ; dc_type
      } ->
    let (ret_t, args_t) = get_function_type dc_type in
    pp_print_string ppf "declare " ;
    fprintf ppf "%a @%s(%t)"
      typ ret_t
      (str_of_raw_id i)
      (fun ppf -> pp_print_list ~pp_sep:pp_comma_space typ ppf args_t)

and definition : Format.formatter -> (LLVMAst.typ, ((LLVMAst.typ LLVMAst.block list))) LLVMAst.definition -> unit =
  fun ppf ->
  fun ({ df_prototype =
           { dc_name = i
           ; dc_type
           }
       } as df) ->
    (* let (ret_t, args_t) = get_function_type dc_type in *)
    (* let typ_arg =
     *   fun ppf (t,id) ->
     *     typ ppf t;
     *     pp_space ppf ();
     *     lident ppf id
     * in *)
    pp_print_string ppf "TLE_Definition {|";
    pp_force_newline ppf ();

    pp_print_string ppf "  df_prototype := {| ";
    pp_open_box ppf 0;
    fprintf ppf "dc_name := %s;" (str_of_raw_id i);
    pp_force_newline ppf ();
    fprintf ppf "dc_type := %a |}" typ dc_type;
    pp_close_box ppf ();
    pp_print_string ppf ";";
    pp_force_newline ppf ();

    pp_print_string ppf "  df_args := [";
    pp_print_list ~pp_sep:pp_sc_space (fun ppf id -> pp_print_string ppf (str_of_raw_id id))
      ppf df.df_args;
    pp_print_string ppf "];";

    pp_force_newline ppf ();

    pp_print_string ppf "  df_instrs := ";
    pp_force_newline ppf ();
    pp_print_string ppf "[";
    pp_open_box ppf 0;
    pp_print_list ~pp_sep:(fun ppf () -> pp_print_string ppf ";"; pp_force_newline ppf ())
      block ppf df.df_instrs ;
    pp_print_string ppf "]";
    pp_close_box ppf ();
    pp_force_newline ppf ();

    pp_print_string ppf "|}";
    pp_print_flush ppf ();

and block : Format.formatter -> LLVMAst.typ LLVMAst.block -> unit =
  fun ppf {blk_id=lbl; blk_phis=phis; blk_code=b; blk_term=(t_id,t)} ->
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
    fprintf ppf "(%a, %a)" instr_id t_id terminator t;
    pp_force_newline ppf () ;

    pp_print_string ppf "|}";

and modul : Format.formatter -> (LLVMAst.typ, ((LLVMAst.typ LLVMAst.block list))) LLVMAst.modul -> unit =
  fun ppf m ->

  pp_option ppf (fun ppf x -> fprintf ppf "; ModuleID = '%s'" (of_str x)) m.m_name ;
  pp_force_newline ppf () ;

  pp_print_list ~pp_sep:pp_force_newline global ppf m.m_globals;
  pp_force_newline ppf () ;

  (* Print function declaration only if there is no corresponding
     function definition *)
  pp_print_list ~pp_sep:pp_force_newline declaration ppf m.m_declarations;
  pp_force_newline ppf () ;

  pp_print_list ~pp_sep:pp_force_newline definition ppf m.m_definitions;
  pp_force_newline ppf ()
