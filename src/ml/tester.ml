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
let compare_dvalues_exn dv1 dv2 ans : (doc, unit) Either.t =
  match DV.dvalue_eqb dv1 dv2 = ans with
  | true -> Right ()
  | false ->
      Left
        (Printf.sprintf
           "dvalue comparison for %s failed: \ngot:\n\t%s\nand:\n\t%s"
           (if ans then "equality" else "inequality")
           (string_of_dvalue dv1) (string_of_dvalue dv2) )

(* given a name, a *)
let dvalue_eq_assertion name (got : unit -> DV.dvalue)
    (expected : unit -> DV.dvalue) () : (doc, unit) Either.t =
  Platform.verb (Printf.sprintf "running ASSERT in %s\n" name) ;
  let dv1 = got () in
  let dv2 = expected () in
  compare_dvalues_exn dv1 dv2 true

(* This function compare and see if target is more poison If correct, will
   give the right branch. Else it will give the left branch*)
let compare_tgt_for_poison src tgt : (string, unit) Either.t =
  match tgt with
  | DV.DVALUE_Poison _ -> (
    match src with
    | DV.DVALUE_Poison _ ->
        Left
          "TargetMorePoisonous: expected src to be non-poison value, but \
           got poison"
    | _ -> Right () )
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
  | Right _ -> EQOk (name, Eq {lhs; rhs})
  | Left _ -> EQFal (name, Eq {lhs; rhs})

(* This function takes in a name, a got and expected function, and function
   call name. It will lift the result into the test result class *)
let eval_POISONTest (name : string) (got : unit -> DV.dvalue)
    (expected : unit -> DV.dvalue) (fcall : string) () =
  match dvalue_eq_assertion name got expected () with
  | Right _ -> POIOk (name, Poison' {fcall})
  | Left _ -> POIFal (name, Poison' {fcall})

(* | STOk : string * Assertion.src_tgt_mode -> test_result | STNOk : string *
   Assertion.src_tgt_mode * string -> test_result | STErr : string *
   src_tgt_error_side * string -> test_result*)
let exit_cond2test_err (ec : Interpreter.exit_condition) : Assert.test_error
    =
  match ec with
  | UninterpretedCall e -> UninterpretedCall e
  | OutOfMemory e -> OutOfMemory e
  | UndefinedBehavior e -> UndefinedBehavior e
  | Failed e -> Failed e

let eval_SRCTGTTest (name : string) (expected_rett : DynamicTypes.dtyp)
    (tgt_fn_str : string) (src_fn_str : string) (v_args : DV.uvalue list)
    (mode : Assertion.src_tgt_mode)
    (sum_ast :
      (LLVMAst.typ, Generate.GA.runnable_blocks) LLVMAst.toplevel_entity list
      ) () : test_result =
  let res_tgt = run expected_rett tgt_fn_str v_args sum_ast in
  let res_src = run expected_rett src_fn_str v_args sum_ast in
  match res_tgt with
  (* Note that the third argument of STErr is a type from assert and not from
     interpreter *)
  | Ok v_tgt -> (
    match res_src with
    | Ok v_src -> (
      match mode with
      | NormalEquality -> (
        match compare_dvalues_exn v_src v_tgt true with
        | Left fail_msg -> STNOk (name, mode, fail_msg)
        | Right _ -> STOk (name, mode) )
      | ValueMismatch -> (
        match compare_dvalues_exn v_src v_tgt false with
        | Left fail_msg -> STNOk (name, mode, fail_msg)
        | Right _ -> STOk (name, mode) )
      | TargetMorePoisonous -> (
        match compare_tgt_for_poison v_src v_tgt with
        | Left fail_msg -> STNOk (name, mode, fail_msg)
        | Right _ -> STOk (name, mode) )
      | TargetMoreUndefined -> failwith "todo: TargetMoreUndefined"
      | SourceMoreDefined -> failwith "todo: SourceMoreDefined"
      | MismatchInMemory -> failwith "todo: MismatchInMemory" )
    | Error e -> STErr (name, Src, exit_cond2test_err e) )
  | Error e -> STErr (name, Tgt, exit_cond2test_err e)

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
      , eval_SRCTGTTest name expected_rett tgt_fn_str src_fn_str v_args mode
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
