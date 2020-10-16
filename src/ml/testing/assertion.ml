open LLVMAst
open TopLevel
open Handlers.LLVMEvents


type raw_assertion_string =
  | Eq of { lhs : string ; rhs : string}
  | Poison' of { fcall: string}

type test =
  | EQTest of DV.uvalue * DynamicTypes.dtyp * string * DV.uvalue list
  | POISONTest of DynamicTypes.dtyp * string * DV.uvalue list


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
  | EXP_Ident (ID_Global (Name x)) -> t, Camlcoq.camlstring_of_coqstring x
  | _ -> failwith "found non-function name"

let instr_to_call_data' instr =
  match instr with
  | INSTR_Call (fn, args) ->
     let (t, fname) = texp_to_name_retty fn in
     (t, fname, List.map texp_to_uvalue args)
  | _ -> failwith "Assertion includes unsupported instruction (must be a call)"
  

(* Top level for parsing assertions *)  
let rec parse_assertion (line: string) : test option =
  begin match parse_eq_assertion line with
  | (Some _ as eqtest) -> print_endline "eqtest"; eqtest
  | _ -> None
  end

and parse_poison_assertion (line: string) : test option =
  (* ws* "ASSERT" ws+ "POISON" ws* ':' ws* (anything+ as r) *)
  let regex = "^[ \t]*;[ \t]*ASSERT[ \t]+POISON[ \t]*:[ \t]*\\(.*\\)" in
  if not (Str.string_match (Str.regexp regex) line 0) then
    None
  else
    let assertion = Str.matched_group 1 line in
    let poisoned_fcall = Llvm_lexer.parse_test_call (Lexing.from_string assertion) in
    let (ty, fn, args) = instr_to_call_data' poisoned_fcall in
    Some (POISONTest(ty, fn, args))

and parse_eq_assertion (line:string) =
  (* ws* "ASSERT" ws+ "EQ" ws* ':' ws* (anything+ as l) ws* '=' ws* (anything+ as r)  *)
  let regex = "^[ \t]*;[ \t]*ASSERT[ \t]+EQ[ \t]*:[ \t]*\\(.*\\)=\\(.*\\)" in 
  if not (Str.string_match (Str.regexp regex) line 0) then
    begin
      (* let _ = print_endline ("NO MATCH: " ^ line) in *)
      None
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
    Some (EQTest(uv, dt, fn, args))


