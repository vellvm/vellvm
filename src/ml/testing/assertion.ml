open LLVMAst
open TopLevel
open Handlers.LLVMEvents


type raw_assertion_string =
  | Eq of { lhs : string ; rhs : string}
  | Poison' of { fcall: string}

type test =
  | EQTest of DV.uvalue * DynamicTypes.dtyp * string * DV.uvalue list
  | POISONTest of DynamicTypes.dtyp * string * DV.uvalue list
  (* Find a better name for this *)
  (* retty, args for src, (t, args) for arguments to source and test *)
  | SRCTGTTest of DynamicTypes.dtyp * (LLVMAst.typ * DV.uvalue) list


(*  Directly converts a piece of syntax to a uvalue without going through semantic interpretation.
    Only works on literals.
 *)

let rec texp_to_uvalue ((typ, exp) : LLVMAst.typ * LLVMAst.typ LLVMAst.exp) : DV.uvalue =
  match typ, exp with
  (* Allow null pointers literals *)
  | TYPE_Pointer _, EXP_Null -> UVALUE_None 
  | TYPE_I i, EXP_Integer x ->
    begin match (Camlcoq.Z.to_int (DynamicValues.Int32.unsigned i)) with
    | 1 -> UVALUE_I1 x
    | 8 -> UVALUE_I8 x
    | 32 -> UVALUE_I32 x
    | 64 -> UVALUE_I64 x
    | _ -> failwith "Assertion includes ill-typed or unsupported expression"
    end
  | TYPE_Float, EXP_Float f -> UVALUE_Float f
  | TYPE_Double, EXP_Double f -> UVALUE_Double f
  | TYPE_Array _, EXP_Array elts -> UVALUE_Array (List.map texp_to_uvalue elts)
  | TYPE_Struct _, EXP_Struct elts -> UVALUE_Struct (List.map texp_to_uvalue elts)
  | TYPE_Packed_struct _, EXP_Packed_struct elts -> UVALUE_Packed_struct (List.map texp_to_uvalue elts)
  | TYPE_Vector _, EXP_Vector elts -> UVALUE_Vector (List.map texp_to_uvalue elts)
  | _,_ -> failwith "Assertion includes unsupported expression"

let rec typ_to_dtyp (typ : LLVMAst.typ) : DynamicTypes.dtyp =
  match typ with
  | TYPE_I i -> DTYPE_I i
  | TYPE_Float -> DTYPE_Float
  | TYPE_Double -> DTYPE_Double
  | TYPE_Array (sz,dtyp) -> DTYPE_Array (sz, typ_to_dtyp dtyp)
  | TYPE_Struct dtyps -> DTYPE_Struct (List.map typ_to_dtyp dtyps)
  | TYPE_Packed_struct dtyps -> DTYPE_Packed_struct (List.map typ_to_dtyp dtyps)
  | TYPE_Vector (sz,dtyp) -> DTYPE_Vector (sz, typ_to_dtyp dtyp)
  | _ -> failwith "Assertion includes unsupported expression"


let texp_to_function_name (_, exp) : string =
  match exp with
  | EXP_Ident (ID_Global (Name x)) -> Camlcoq.camlstring_of_coqstring x
  | _ -> failwith "found non-function name"

(* | INSTR_Call of 't texp * 't texp list *)
let instr_to_call_data instr =
  match instr with
  | INSTR_Call (fn, args) ->
     (texp_to_function_name fn, List.map texp_to_uvalue args)
  | _ -> failwith "Assertion includes unsupported instruction (must be a call)"

let texp_to_name_retty (texp : LLVMAst.typ texp) : DynamicTypes.dtyp * string =
  let (t, exp) = texp in
  match exp with
  | EXP_Ident (ID_Global (Name x)) -> typ_to_dtyp t, Camlcoq.camlstring_of_coqstring x
  | _ -> failwith "found non-function name"

let instr_to_call_data' instr =
  match instr with
  | INSTR_Call (fn, args) ->
     let (t, fname) = texp_to_name_retty fn in
     (t, fname, List.map texp_to_uvalue args)
  | _ -> failwith "Assertion includes unsupported instruction (must be a call)"
  

(* Top level for parsing assertions *)  
let rec parse_assertion (filename: string)(line: string) : test list =
  let assertions = [
      parse_poison_assertion line;
      parse_eq_assertion line ;
      parse_srctgt_assertion filename line;
    ] in
  List.flatten assertions

and parse_poison_assertion (line: string) : test list =
  (* ws* "ASSERT" ws+ "POISON" ws* ':' ws* (anything+ as r) *)
  let regex = "^[ \t]*;[ \t]*ASSERT[ \t]+POISON[ \t]*:[ \t]*\\(.*\\)" in
  if not (Str.string_match (Str.regexp regex) line 0) then
    []
  else
    let assertion = Str.matched_group 1 line in
    let poisoned_fcall = Llvm_lexer.parse_test_call (Lexing.from_string assertion) in
    let (ty, fn, args) = instr_to_call_data' poisoned_fcall in
    [ POISONTest(ty, fn, args) ]

and parse_eq_assertion (line:string) : test list =
  (* ws* "ASSERT" ws+ "EQ" ws* ':' ws* (anything+ as l) ws* '=' ws* (anything+ as r)  *)
  let regex = "^[ \t]*;[ \t]*ASSERT[ \t]+EQ[ \t]*:[ \t]*\\(.*\\)=\\(.*\\)" in 
  if not (Str.string_match (Str.regexp regex) line 0) then
    begin
      (* let _ = print_endline ("NO MATCH: " ^ line) in *)
      []
    end
  else
    (* let _ = print_endline ("MATCH: " ^ line) in *)
    let lhs = Str.matched_group 1 line in
    (* let _ = print_endline ("LHS: " ^ lhs) in     *)
    let rhs = Str.matched_group 2 line in
    (* let _ = print_endline ("RHS: " ^ rhs) in         *)
    let l = Llvm_lexer.parse_texp (Lexing.from_string lhs) in
    (* let _ = print_endline "PARSED LHS" in         *)
    let r = Llvm_lexer.parse_test_call (Lexing.from_string rhs) in
    let uv = texp_to_uvalue l in
    let dt = typ_to_dtyp (fst l) in
    let (fn, args) = instr_to_call_data r in
    [ EQTest(uv, dt, fn, args) ]

and parse_srctgt_assertion (filename: string) (line: string) : test list =
  (* ws* ; ws* "ASSERT" ws+ "SRCTGT" *)
  let regex = "^[ \t]*;[ \t]*ASSERT[ \t]+SRCTGT[ \t]*" in
  (* annoying duplication of parse file :( *)
  let read_and_parse (file:string) =
    let lines = ref [] in
    let channel = open_in file in
    (try while true; do
           lines := input_line channel :: !lines
         done; ""
     with End_of_file ->
       close_in channel;
       String.concat "\n" (List.rev !lines) )
    |> Lexing.from_string |> Llvm_lexer.parse
  in

  (* Given an ast, find the source and target functions *)
  let find_fn fname toplevel_entity =
    match toplevel_entity with
    | TLE_Definition df ->
      begin match df.df_prototype.dc_name with
       | Name coqstr -> Camlcoq.camlstring_of_coqstring coqstr = fname 
       | _ -> false
      end
    | _ -> false
  in
  (* Find the function type for a given top level entity *)
  let find_ty toplevel_entity : (LLVMAst.typ list * LLVMAst.typ) =
    match toplevel_entity with
    | TLE_Definition df ->
       begin match LLVMAst.dc_type df.df_prototype with
       | LLVMAst.TYPE_Function (rt, args) -> args, rt
       | _ -> failwith "given entity not a function definition"
       end
    | _ -> failwith "not a function definition"
  in      


  if not (Str.string_match (Str.regexp regex) line 0) then
    []
  else
    let ast = read_and_parse filename in
    let (src_fxn, tgt_fxn) = (List.find_opt (find_fn "src") ast), (List.find_opt (find_fn "tgt") ast) in
    begin match src_fxn, tgt_fxn with
    | (Some src), (Some tgt) ->
       begin  try
        let  (src_t, tgt_t) = find_ty src, find_ty tgt in
        let  generated_args : (LLVMAst.typ * DV.uvalue) list list = Generate.generate_n_args 20 (fst src_t) in
        List.map (fun arg -> SRCTGTTest ((typ_to_dtyp (snd tgt_t)), arg)   ) generated_args
       with _ -> [] end
    | _ -> []
    end
