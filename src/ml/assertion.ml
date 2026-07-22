(*** This file sets up some testing infrastructure.

     ; ASSERT EQ: texp = <call>
     ; ASSERT SUCCEEDS: <call>
     ; ASSERT FAILS: call i64 @run()
     
  See README.md for more details. *)
open VellvmLib
open LLVMAst
module DV = DynamicValues
open DV
open Llvm_printer
open List
open VellvmFloats

type test =
  (* expected dvalue, dynamic type, entry, arguments *)
  | EQTest of DV.dvalue * DynamicTypes.dtyp * function_id * DV.dvalue list
  | SuccessTest of function_id * DV.dvalue list
  | FailsTest of function_id * DV.dvalue list


(* Directly converts a piece of syntax to a dtyp without going through
   semantic interpretation. Only works on literals. *)
let typ_to_dtyp_base (typ : LLVMAst.typ) : DynamicTypes.dtyp_base =
  match typ with
  | TYPE_Void -> DTYPE_Void
  | TYPE_I i -> DTYPE_I i
  | TYPE_FP FP_float -> DTYPE_FP FP_float
  | TYPE_FP FP_double -> DTYPE_FP FP_double
  | _ ->
      failwith
        (Printf.sprintf "Assertion includes unsupported type:\n\t %s"
           (string_of_typ typ) )

let rec typ_to_dtyp (typ : LLVMAst.typ) : DynamicTypes.dtyp =
  match typ with
  | TYPE_Struct dtyps -> DTYPE_Struct (false, List.map typ_to_dtyp dtyps)
  | TYPE_Packed_struct dtyps ->
      DTYPE_Struct (true, List.map typ_to_dtyp dtyps)
  | TYPE_Array (sz, dtyp) -> DTYPE_Array (false, sz, typ_to_dtyp dtyp)
  | TYPE_Vector (sz, dtyp) -> DTYPE_Array (true, sz, typ_to_dtyp dtyp)
  | _ -> DTYPE_Base (typ_to_dtyp_base typ)

let ocaml_of_EOU (c : 'x EOU.coq_EOU) : 'x =
  match c with
  | Coq_raise_error err -> failwith @@ Printf.sprintf "ERROR: %s" (Interpreter.ocaml_str err)
  | Coq_raise_oom err -> failwith @@ Printf.sprintf "OOM: %s" (Interpreter.ocaml_str err)
  | Coq_raise_ub err -> failwith @@ Printf.sprintf "UB: %s" (Interpreter.ocaml_str err)
  | Coq_raise_ret x -> x

let dvalue_to_dvalue_base_exn (dv : dvalue) : dvalue_base =
  match dv with
  | DVALUE_Base dv -> dv
  | _ -> failwith "ocaml: dvalue_to_dvalue_base cast failed"

let rec texp_to_dvalue ((typ, exp) : LLVMAst.typ * LLVMAst.typ LLVMAst.exp) : DV.dvalue =
  match (typ, exp) with
  (* Allow null pointers literals *)
  | TYPE_Pointer _, EXP_Null ->
      DVALUE_Base (DVALUE_Pointer Interpreter.pointer_v.null)
  | TYPE_I bits, EXP_Integer x ->                 
     DVALUE_Base (ocaml_of_EOU
       (DV.coerce_integer_to_int Interpreter.params (Some bits) (Denotation.denote_int_syntax x)))

  | TYPE_FP FP_float, EXP_Float f ->
     begin match float32_of_float_syntax f with
     | Some v ->  DVALUE_Base (DVALUE_Float v)
     | None ->
        let s = Camlcoq.camlstring_of_coqstring (ShowAST.show_float_syntax f) in
        failwith @@ Printf.sprintf "assertion.ml: texp_to_dvalue failed float32 conversion: %s" s
     end
  | TYPE_FP FP_double, EXP_Float f ->
     begin match float_of_float_syntax f with
     | Some v ->  DVALUE_Base (DVALUE_Double v)
     | None ->
        let s = Camlcoq.camlstring_of_coqstring (ShowAST.show_float_syntax f) in
        failwith @@ Printf.sprintf "assertion.ml: texp_to_dvalue failed float conversion: %s" s
     end
  | TYPE_Struct _, EXP_Struct elts ->
      DVALUE_Struct (false, List.map texp_to_dvalue elts)
  | TYPE_Packed_struct _, EXP_Packed_struct elts ->
      DVALUE_Struct (true, List.map texp_to_dvalue elts)
  | TYPE_Array _, EXP_Array (t, elts) ->
     let dt = typ_to_dtyp t in
     DVALUE_Array (false, dt, (List.map texp_to_dvalue elts))
  | TYPE_Vector _, EXP_Vector (t, elts) ->
     let dt = typ_to_dtyp t in
     DVALUE_Array (true, dt, (List.map texp_to_dvalue elts))
  | _, EXP_Poison -> (DVALUE_Base (DVALUE_Poison (typ_to_dtyp typ)))
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
      ; parse_fails_assertion line
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
    (* let _ = print_endline ("no match: " ^ line) in *)
    []
  else
    let rhs = Str.matched_group 1 line in
    (* let _ = print_endline ("rhs: " ^ rhs) in *)
    let r =
      try Llvm_lexer.parse_test_call (Lexing.from_string rhs)
      with _ -> failwith (Printf.sprintf "ill-formed assert succeeds: %s" rhs)
    in
    (* let _ = print_endline "parsed rhs" in *)
    let fn, args = instr_to_call_data r in
    [SuccessTest (fn, args)]

and parse_fails_assertion (line : string) : test list =
  (* ws* "ASSERT" ws+ "FAILS" ws* ':' ws*  (anything+ as r) *)
  let regex = "^[ \t]*;[ \t]*ASSERT[ \t]+FAILS[ \t]*:[ \t]*\\(.*\\)" in
  if not (Str.string_match (Str.regexp regex) line 0) then
    (* let _ = print_endline ("no match: " ^ line) in *)
    []
  else
    let rhs = Str.matched_group 1 line in
    (* let _ = print_endline ("rhs: " ^ rhs) in *)
    let r =
      try Llvm_lexer.parse_test_call (Lexing.from_string rhs)
      with _ -> failwith (Printf.sprintf "ill-formed assert fails: %s" rhs)
    in
    (* let _ = print_endline "parsed rhs" in *)
    let fn, args = instr_to_call_data r in
    [FailsTest (fn, args)]

(* Semantics of ASSERT EQ ty expected = call @f(args):

   If expected is `poison` then the call should result in poison.

   If ty is an integral type, then use LLVM's `icmp eq` as the comparison.

   If ty is a floating point type, then use LLVM's `fcmp ueq` as the comparison.
 *)

(* "Syntactic comparison" of dynamic values -- does not take
   the semantic content into account.  *)
let compare_dvalues_exn expected got msg : unit =
  if TopLevel.dvalue_eqb expected got then ()
  else
    failwith msg

let dvalue_i1_to_bool (dv : DV.dvalue) : bool =
  match dv with 
  | DVALUE_Base (DV.DVALUE_I (sz,bitint)) ->  Integers.eq sz bitint (Integers.one sz)
  | _ -> failwith "non-i1 value"


let dvalue_eq_assertion name (ty:DynamicTypes.dtyp) (expected : DV.dvalue) (got : unit -> DV.dvalue) () =
  let open DynamicTypes in
  Platform.verb (Printf.sprintf "running ASSERT in %s\n" name) ;  
  let result = got () in
  let msg =
    Printf.sprintf "ASSERT EQ failed: \ngot:\n\t%s\nasserted:\n\t%s"
      (Interpreter.string_of_dvalue result) (Interpreter.string_of_dvalue expected) 
  in
  begin match expected with
  | DVALUE_Base (DV.DVALUE_Poison _) -> compare_dvalues_exn expected result msg
  | _ ->
     (* Use the semantic "cmp eq" for these types *)
     begin match ty with
     | DTYPE_Base (DTYPE_I _)
     | DTYPE_Base DTYPE_Iptr
     | DTYPE_Base DTYPE_Pointer ->
        (* integral comparison *)
        let v = ocaml_of_EOU @@ Compare.eval_icmp Interpreter.params false Eq expected result in
        if dvalue_i1_to_bool v then () else
          failwith msg
     | _ -> (* Best effort comparison of other types *)
        compare_dvalues_exn expected result msg
     end
  end


let make_test_h run name ll_ast t : (string * Assert.assertion) option =
  let open Format in
  (* TODO: ll_ast is of type list (toplevel_entity typ (block typ * list (block typ))) *)
  (* Can just replace this with the newer ones? *)
  let run_to_value dtyp entry args ll_ast () : DV.dvalue =
    match run dtyp entry args ll_ast with
    | Ok dv -> dv
    | Error e -> failwith (Result.string_of_exit_condition e)
  in
  let args_str args =
    pp_print_list
      ~pp_sep:(fun f () -> pp_print_string f ", ")
      (fun f dv -> pp_print_string f (Interpreter.string_of_dvalue dv)) str_formatter args ;
    flush_str_formatter ()
  in
  (* let _ = Printf.printf "I can get here\n" in *)
  match t with
  | EQTest (expected, dtyp, entry, args) ->
      let str =
        let expected_str = Interpreter.string_of_dvalue expected in
        let args_str = args_str args in
        Printf.sprintf "%s = %s(%s)" expected_str (Interpreter.string_of_function_id entry) args_str
      in
      let result = run_to_value dtyp entry args ll_ast in
      Some (str, dvalue_eq_assertion name dtyp expected result)

  | SuccessTest (entry, args) ->
     let str =
       let args_str  = args_str args 
       in
       Printf.sprintf "%s(%s)" (Interpreter.string_of_function_id entry) args_str
     in
     let t_void = typ_to_dtyp (LLVMAst.TYPE_Void) in
     Some (str, (fun () -> ignore (run_to_value t_void entry args ll_ast ())))

  | FailsTest (entry, args) ->
      let str =
        let args_str  = args_str args 
        in
        Printf.sprintf "FAILS %s(%s)" (Interpreter.string_of_function_id entry) args_str
      in
      let t_void = typ_to_dtyp (LLVMAst.TYPE_Void) in
      Some (str, fun () ->
                 match run t_void entry args ll_ast with
                 | Error _ -> ()
                 | exception _ -> ()
                 | Ok dv ->
                    failwith (Printf.sprintf "expected uncaught exception, but got %s" (Interpreter.string_of_dvalue dv))
        )
