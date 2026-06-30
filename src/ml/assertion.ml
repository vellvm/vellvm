(*** This file sets up some testing infrastructure.

  See README.md for more details. *)
open LLVMAst

module DV = DynamicValues
open DV
let addr_v = Address0.coq_AddressV IPtrInfinite.coq_IPZ

let ocaml_of_EOU (c : 'x EOU.coq_EOU) : 'x =
  match c with
  | Coq_raise_error err -> failwith @@ Printf.sprintf "ERROR: %s" (Camlcoq.camlstring_of_coqstring err)
  | Coq_raise_oom err -> failwith @@ Printf.sprintf "OOM: %s" (Camlcoq.camlstring_of_coqstring err)
  | Coq_raise_ub err -> failwith @@ Printf.sprintf "UB: %s" (Camlcoq.camlstring_of_coqstring err)
  | Coq_raise_ret x -> x


open Llvm_printer
open List
open VellvmFloats

type test =
  (* expected dvalue, dynamic type, entry, arguments *)
  | EQTest of DV.dvalue * DynamicTypes.dtyp * function_id * DV.dvalue list
  | SuccessTest of function_id * DV.dvalue list


(* Directly converts a piece of syntax to a dtyp without going through
   semantic interpretation. Only works on literals. *)
let rec typ_to_dtyp (typ : LLVMAst.typ) : DynamicTypes.dtyp =
  match typ with
  | TYPE_Void -> DTYPE_Void
  | TYPE_I i -> DTYPE_I i
  | TYPE_FP FP_float -> DTYPE_FP FP_float
  | TYPE_FP FP_double -> DTYPE_FP FP_double
  | TYPE_Array (sz, dtyp) -> DTYPE_Array (sz, typ_to_dtyp dtyp)
  | TYPE_Struct dtyps -> DTYPE_Struct (List.map typ_to_dtyp dtyps)
  | TYPE_Packed_struct dtyps ->
      DTYPE_Packed_struct (List.map typ_to_dtyp dtyps)
  | TYPE_Vector (sz, dtyp) -> DTYPE_Vector (sz, typ_to_dtyp dtyp)
  | _ ->
      failwith
        (Printf.sprintf "Assertion includes unsupported type:\n\t %s"
           (string_of_typ typ) )

let rec texp_to_dvalue ((typ, exp) : LLVMAst.typ * LLVMAst.typ LLVMAst.exp) : DV.dvalue =
  match (typ, exp) with
  (* Allow null pointers literals *)
  | TYPE_Pointer _, EXP_Null ->
      DVALUE_Addr addr_v.null
  | TYPE_I bits, EXP_Integer x ->                 
     ocaml_of_EOU
       (DV.coerce_integer_to_int Interpreter.params (Some bits) (Denotation.denote_int_syntax x))

  | TYPE_FP FP_float, EXP_Float f ->
     begin match float32_of_float_syntax f with
     | Some v ->  DVALUE_Float v
     | None ->
        let s = Camlcoq.camlstring_of_coqstring (ShowAST.show_float_syntax f) in
        failwith @@ Printf.sprintf "assertion.ml: texp_to_dvalue failed float32 conversion: %s" s
     end
  | TYPE_FP FP_double, EXP_Float f ->
     begin match float_of_float_syntax f with
     | Some v ->  DVALUE_Double v
     | None ->
        let s = Camlcoq.camlstring_of_coqstring (ShowAST.show_float_syntax f) in
        failwith @@ Printf.sprintf "assertion.ml: texp_to_dvalue failed float conversion: %s" s
     end
  | TYPE_Array _, EXP_Array (t, elts) ->
      let elt_typ = match t with TYPE_Array (_, et) -> et | _ -> t in
      DVALUE_Array (typ_to_dtyp elt_typ, (List.map texp_to_dvalue elts))
  | TYPE_Struct _, EXP_Struct elts ->
      DVALUE_Struct (List.map texp_to_dvalue elts)
  | TYPE_Packed_struct _, EXP_Packed_struct elts ->
      DVALUE_Packed_struct (List.map texp_to_dvalue elts)
  | TYPE_Vector _, EXP_Vector (t, elts) ->
      let elt_typ = match t with TYPE_Vector (_, et) -> et | _ -> t in
      DVALUE_Vector (typ_to_dtyp elt_typ, (List.map texp_to_dvalue elts))
  | _, EXP_Poison -> (DVALUE_Poison (typ_to_dtyp typ))
  | _, _ ->
      failwith
        (Printf.sprintf "Assertion includes unsupported expression:\n\t%s %s"
           (string_of_typ typ) (string_of_exp exp) )

let texp_to_function_id (_, exp) : function_id =
  match exp with
  | EXP_Ident (ID_Global id) -> id
  | _ -> failwith "found non-function name"

(* | INSTR_Call of 't texp * 't texp list *)
let instr_to_call_data instr =
  match instr with
  | INSTR_Call (fn, args, _, _) ->
      ( texp_to_function_id fn
      , List.map (fun x -> texp_to_dvalue (fst x)) args )
  | _ ->
      failwith "Assertion includes unsupported instruction (must be a call)"

let texp_to_name_retty (texp : LLVMAst.typ texp) : DynamicTypes.dtyp * function_id =
  let t, _ = texp in
  (typ_to_dtyp t, texp_to_function_id texp)

(* Top level for parsing assertions *)
let rec parse_assertion (line : string) : test list =
    let assertions =
      [ parse_eq_assertion line
      ; parse_succeeds_assertion line
      ]
    in
    List.flatten assertions

and parse_eq_assertion (line : string) : test list =
  (* ws* "ASSERT" ws+ "EQ" ws* ':' ws* (anything+ as l) ws* '=' ws*
     (anything+ as r) *)
  let regex = "^[ \t]*;[ \t]*ASSERT[ \t]+EQ[ \t]*:[ \t]*\\(.*\\)=\\(.*\\)" in
  if not (Str.string_match (Str.regexp regex) line 0) then
    (* let _ = print_endline ("NO MATCH: " ^ line) in *)
    []
  else
    (* let _ = print_endline ("MATCH: " ^ line) in *)
    let lhs = Str.matched_group 1 line in
    (* let _ = print_endline ("LHS: " ^ lhs) in *)
    let rhs = Str.matched_group 2 line in
    (* let _ = print_endline ("RHS: " ^ rhs) in *)
    let l =
      try 
        Llvm_lexer.parse_texp (Lexing.from_string lhs)
      with _ -> failwith (Printf.sprintf "Ill-formed ASSERT EQ left-hand-side: %s" lhs)
    in
    (* let _ = print_endline "PARSED LHS" in *)
    let r =
      try Llvm_lexer.parse_test_call (Lexing.from_string rhs)
      with _ -> failwith (Printf.sprintf "Ill-formed ASSERT EQ right-hand-side: %s" rhs)
    in
    (* let _ = print_endline "PARSED RHS" in *)
    let uv = texp_to_dvalue l in
    let dt = typ_to_dtyp (fst l) in
    let fn, args = instr_to_call_data r in
    [EQTest (uv, dt, fn, args)]

and parse_succeeds_assertion (line : string) : test list =
  (* ws* "ASSERT" ws+ "SUCCEEDS" ws* ':' ws*  (anything+ as r) *)
  let regex = "^[ \t]*;[ \t]*ASSERT[ \t]+SUCCEEDS[ \t]*:[ \t]*\\(.*\\)" in
  if not (Str.string_match (Str.regexp regex) line 0) then
    (* let _ = print_endline ("NO MATCH: " ^ line) in *)
    []
  else
    let rhs = Str.matched_group 1 line in
    (* let _ = print_endline ("RHS: " ^ rhs) in *)
    let r =
      try Llvm_lexer.parse_test_call (Lexing.from_string rhs)
      with _ -> failwith (Printf.sprintf "Ill-formed ASSERT EQ: %s" rhs)
    in
    (* let _ = print_endline "PARSED RHS" in *)
    let fn, args = instr_to_call_data r in
    [SuccessTest (fn, args)]
