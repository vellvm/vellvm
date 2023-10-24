(* A main harness for Coq-extracted LLVM Transformations *)
open Arg
open Base
open Assert
open Driver
open ShowAST

module DV = InterpretationStack.InterpreterStackBigIntptr.LP.Events.DV

(* test harness
   ------------------------------------------------------------- *)
exception Ran_tests of bool

let suite = ref Test.suite

let exec_tests () =
  Platform.configure () ;
  let outcome = run_suite !suite in
  Printf.printf "%s\n" (outcome_to_string outcome) ;
  raise (Ran_tests (successful outcome))

(* Given two dvalues and an answer, return whether or not they equal the
   answer*)
let compare_dvalues_exn dv1 dv2 ans : bool = DV.dvalue_eqb dv1 dv2 = ans

(* given a name, a *)
let dvalue_eq_assertion name (got : unit -> DV.dvalue)
    (expected : unit -> DV.dvalue) () : bool =
  Platform.verb (Printf.sprintf "running ASSERT in %s\n" name) ;
  let dv1 = got () in
  let dv2 = expected () in
  compare_dvalues_exn dv1 dv2 true

(* This function compare and see if target is more poison If correct, will
   give the right branch. Else it will give the left branch*)
let compare_tgt_for_poison src tgt : (string, string) Either.t =
  match tgt with
  | DV.DVALUE_Poison _ -> (
    match src with
    | DV.DVALUE_Poison _ ->
        Left
          "TargetMorePoisonous: expected src to be non-poison value, but \
           got poison"
    | _ -> Right "" )
  | _ ->
      Left
        (Printf.sprintf
           "TargetMorePoisonous: expected tgt to be poison but got %s"
           (string_of_dvalue tgt) )

let run dtyp entry args ll_ast =
  Interpreter.step
    (TopLevel.TopLevelBigIntptr.interpreter_gen dtyp
       (Camlcoq.coqstring_of_camlstring entry)
       args ll_ast )

(* This function takes in a name, a got and expected function, and the left
   hand side and right hand side of the equality. It will lift the result
   into the test result class *)
let eval_EQTest (name : string) (got : unit -> DV.dvalue)
    (expected : unit -> DV.dvalue) (lhs : string) (rhs : string) () =
  match dvalue_eq_assertion name got expected () with
  | true -> EQOk (name, Eq {lhs; rhs})
  | false -> EQFal (name, Eq {lhs; rhs})

(* This function takes in a name, a got and expected function, and function
   call name. It will lift the result into the test result class *)
let eval_POISONTest (name : string) (got : unit -> DV.dvalue)
    (expected : unit -> DV.dvalue) (fcall : string) () =
  match dvalue_eq_assertion name got expected () with
  | true -> POIOk (name, Poison' {fcall})
  | false -> POIFal (name, Poison' {fcall})

(* | STOk : string * Assertion.src_tgt_mode -> test_result | STNOk : string *
   Assertion.src_tgt_mode * string -> test_result | STErr : string *
   src_tgt_error_side * string -> test_result*)
let eval_SRCTGTTest (name : string) (expected_rett : DynamicTypes.dtyp)
    (tgt_fn_str : string) (src_fn_str : string) (v_args : DV.uvalue list)
    (sum_ast :
      (LLVMAst.typ, Generate.GA.runnable_blocks) LLVMAst.toplevel_entity list
      ) () =
  let res_tgt = run expected_rett tgt_fn_str v_args sum_ast in
  let res_src = run expected_rett src_fn_str v_args sum_ast in
  match res_tgt with
  | Error (UndefinedBehavior _) -> failwith "TODO: unimplemented"
  | Error (UninterpretedCall _) -> failwith "TODO: unimplemented"
  | Ok v_tgt -> failwith "TODO: unimplemented"
  | Error e -> failwith "TODO: unimplemented"

let make_test name ll_ast t : string * (unit -> test_result) =
  let open Format in
  (* TODO: ll_ast is of type list (toplevel_entity typ (block typ * list
     (block typ))) *)
  (* Can just replace this with the newer ones? *)
  (* let run dtyp entry args ll_ast = Interpreter.step
     (TopLevel.TopLevelBigIntptr.interpreter_gen dtyp
     (Camlcoq.coqstring_of_camlstring entry) args ll_ast ) in *)
  let run_to_value dtyp entry args ll_ast () : DV.dvalue =
    match run dtyp entry args ll_ast with
    | Ok dv -> dv
    | Error e -> failwith (Interpreter.string_of_exit_condition e)
  in
  match t with
  | Assertion.EQTest (expected, dtyp, entry, args) ->
      let strs =
        let expected_str = string_of_dvalue expected in
        let args_str : doc =
          pp_print_list
            ~pp_sep:(fun f () -> pp_print_string f ", ")
            Interpreter.pp_uvalue str_formatter args ;
          flush_str_formatter ()
        in
        let lhs = expected_str in
        let rhs = Printf.sprintf "%s(%s)" entry args_str in
        (lhs, rhs)
      in
      let result = run_to_value dtyp entry args ll_ast in
      let str = Printf.sprintf "%s=%s" (fst strs) (snd strs) in
      ( str
      , eval_EQTest name result (fun () -> expected) (fst strs) (snd strs) )
  | Assertion.POISONTest (dtyp, entry, args) ->
      let expected =
        InterpretationStack.InterpreterStackBigIntptr.LP.Events.DV
        .DVALUE_Poison
          dtyp
      in
      let strs =
        let expected_str = string_of_dvalue expected in
        let args_str =
          pp_print_list
            ~pp_sep:(fun f () -> pp_print_string f ", ")
            Interpreter.pp_uvalue str_formatter args ;
          flush_str_formatter ()
        in
        let lhs = expected_str in
        let rhs = Printf.sprintf "%s(%s)" entry args_str in
        (lhs, rhs)
      in
      let result = run_to_value dtyp entry args ll_ast in
      let str = Printf.sprintf "%s=%s" (fst strs) (snd strs) in
      (str, eval_POISONTest name result (fun () -> expected) (snd strs))
  | Assertion.SRCTGTTest (mode, expected_rett, generated_args) ->
      let v_args, src_fn_str, tgt_fn_str, sum_ast =
        match generated_args with
        | Left g_args ->
            let _t_args, v_args = List.split g_args in
            (v_args, "src", "tgt", ll_ast)
        | Right g_ast ->
            ([], "runnersrc", "runnertgt", List.append ll_ast g_ast)
      in
      let str =
        let args_str : doc =
          pp_print_list
            ~pp_sep:(fun f () -> pp_print_string f ", ")
            Interpreter.pp_uvalue str_formatter v_args ;
          flush_str_formatter ()
        in
        Printf.sprintf "src = tgt on generated input (%s)" args_str
      in
      ( str
      , eval_SRCTGTTest name expected_rett tgt_fn_str src_fn_str v_args
          sum_ast )

(* let make_test' name ll_ast t : string * assertion1 = let open Format in
   let run dtyp entry args ll_ast = Interpreter.step
   (TopLevel.TopLevelBigIntptr.interpreter_gen dtyp
   (Camlcoq.coqstring_of_camlstring entry) args ll_ast ) in let run_to_value
   dtyp entry args ll_ast () : DV.dvalue = match run dtyp entry args ll_ast
   with | Ok dv -> dv | Error e -> failwith
   (Interpreter.string_of_exit_condition e) in match t with |
   Assertion.EQTest (expected, dtyp, entry, args) -> ( let str = let
   expected_str = string_of_dvalue expected in let args_str : doc =
   pp_print_list ~pp_sep:(fun f () -> pp_print_string f ", ")
   Interpreter.pp_uvalue str_formatter args ; flush_str_formatter () in
   Printf.sprintf "%s = %s(%s)" expected_str entry args_str in let result =
   run_to_value dtyp entry args ll_ast in failwith "TODO: unimplemented" | _
   -> failwith "TODO: unimplemented" ) *)
