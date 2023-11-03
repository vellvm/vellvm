(* A main harness for Coq-extracted LLVM Transformations *)
open Arg
open Base
open Result
open Assert
open Driver

module DV = InterpretationStack.InterpreterStackBigIntptr.LP.Events.DV

(* test result location
   ------------------------------------------------------------- *)

let stats_output_file_name =
  ref (Printf.sprintf "%s/%s" !Platform.result_dir_path "test_result.txt")

let result_output_file_name =
  ref (Printf.sprintf "%s/%s" !Platform.result_dir_path "result.txt")

(* test harness
   ------------------------------------------------------------- *)
exception Ran_tests of bool

let suite = ref Test.suite

(* let exec_tests () = Platform.configure () ; let outcome = run_suite'
   !suite in Printf.printf "%s\n" (outcome_to_string outcome) ; raise
   (Ran_tests (successful outcome)) *)

(* Given two dvalues and an answer, return whether or not they equal the
   answer*)
let compare_dvalues_exn dv1 dv2 ans : (doc, unit) Either.t =
  match DV.dvalue_eqb dv1 dv2 = ans with
  | true -> Right ()
  | false ->
      Left
        (Printf.sprintf
           "dvalue comparison for %s failed:\n   \ngot:\n\t%s\nand:\n\t%s"
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
          "TargetMorePoisonous: expected src to be non-poison value, but  got\n\
          \   poison"
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
    (expected : unit -> DV.dvalue) (lhs : string) (rhs : string) () :
    result_sum =
  match dvalue_eq_assertion name got expected () with
  | Right _ -> Result.make_singleton EQOk name (RAW_STR (Eq {lhs; rhs}))
  | Left _ -> Result.make_singleton EQNOk name (RAW_STR (Eq {lhs; rhs}))

(* This function takes in a name, a got and expected function, and function
   call name. It will lift the result into the test result class *)
let eval_POISONTest (name : string) (got : unit -> DV.dvalue)
    (expected : unit -> DV.dvalue) (fcall : string) () : result_sum =
  match dvalue_eq_assertion name got expected () with
  | Right _ -> Result.make_singleton POIOk name (RAW_STR (Poison' {fcall}))
  | Left _ -> Result.make_singleton POINOk name (RAW_STR (Poison' {fcall}))

(* | STOk : string * Assertion.src_tgt_mode -> test_result | STNOk : string *
   Assertion.src_tgt_mode * string -> test_result | STErr : string *
   src_tgt_error_side * string -> test_result*)

let eval_SRCTGTTest (name : string) (expected_rett : DynamicTypes.dtyp)
    (tgt_fn_str : string) (src_fn_str : string) (v_args : DV.uvalue list)
    (mode : Assertion.src_tgt_mode) (sum_ast : Result.ast) () : result_sum =
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
        | Left fail_msg ->
            Result.make_singleton (STNOk mode) name
              (AST_ERR_MSG (sum_ast, fail_msg))
        | Right _ ->
            Result.make_singleton (STOk mode) name (AST_CORRECT sum_ast) )
      | ValueMismatch -> (
        match compare_dvalues_exn v_src v_tgt false with
        | Left fail_msg ->
            Result.make_singleton (STNOk mode) name
              (AST_ERR_MSG (sum_ast, fail_msg))
        | Right _ ->
            Result.make_singleton (STOk mode) name (AST_CORRECT sum_ast) )
      | TargetMorePoisonous -> (
        match compare_tgt_for_poison v_src v_tgt with
        | Left fail_msg ->
            Result.make_singleton (STNOk mode) name
              (AST_ERR_MSG (sum_ast, fail_msg))
        | Right _ ->
            Result.make_singleton (STOk mode) name (AST_CORRECT sum_ast) )
      | TargetMoreUndefined -> failwith "todo: TargetMoreUndefined"
      | SourceMoreDefined -> failwith "todo: SourceMoreDefined"
      | MismatchInMemory -> failwith "todo:\n\n MismatchInMemory" )
    | Error e ->
        Result.make_singleton (STErr Src) name (AST_TEST_ERR (sum_ast, e)) )
  | Error e ->
      Result.make_singleton (STErr Tgt) name (AST_TEST_ERR (sum_ast, e))

let make_test name ll_ast t : string * (unit -> result_sum) =
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
    | Error e -> failwith (Result.string_of_exit_condition e)
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
            ~pp_sep:(fun f () -> pp_print_string f ",\n   ")
            Interpreter.pp_uvalue str_formatter v_args ;
          flush_str_formatter ()
        in
        Printf.sprintf "src = tgt on generated input (%s)" args_str
      in
      ( str
      , eval_SRCTGTTest name expected_rett tgt_fn_str src_fn_str v_args mode
          sum_ast )

let print_stats (rs : result_sum) () : unit =
  let stats = get_stats rs in
  let output_str =
    String.concat "\n"
      (List.map
         (fun res ->
           Printf.sprintf "%s: %s" (fst res) (string_of_int (snd res)) )
         stats )
  in
  IO.write_file !stats_output_file_name output_str

let print_result (rs : result_sum) () : unit =
  let res_bindings = Result.bindings rs in
  let output_str =
    String.concat "\n"
      (List.map (string_of_key_value_pair false) res_bindings)
  in
  IO.write_file !result_output_file_name output_str

let output_asts (_ : result_sum) () : unit = ()

let test_dir dir =
  Printf.printf "===> TESTING ASSERTIONS WITH STATISTICS: %s\n" dir ;
  Platform.configure () ;
  Platform.result_dir_configure () ;
  let pathlist = Test.ll_files_of_dir dir in
  let files =
    List.filter_map
      (fun path ->
        let _file, ext = Platform.path_to_basename_ext path in
        try
          match ext with
          | "ll" -> Some (path, IO.parse_file path, parse_tests path)
          | _ -> None
        with
        | Failure s | ParseUtil.InvalidAnonymousId s ->
            let _ = Printf.printf "FAILURE %s\n\t%s\n%!" path s in
            None
        | _ ->
            let _ = Printf.printf "FAILURE %s\n%!" path in
            None )
      pathlist
  in
  let suite =
    List.map
      (fun (file, ast, tests) ->
        Test (file, List.map (make_test file ast) tests) )
      files
  in
  let outcome = run_suite' suite in
  print_stats outcome () ;
  print_result outcome () ;
  output_asts outcome () ;
  raise (Ran_tests true)

(* failwith "unimplemented" *)
(* Printf.printf "%s\n" (outcome_to_string outcome) ; raise (Ran_tests
   (successful outcome)) *)

(* Need to add in the test directory stuff... *)
(* let test_dir2 dir = Printf.printf "===> TESTING ASSERTIONS WITH
   STATISTICS\n IN : %s\n" dir ; Platform.configure () ; let pathlist =
   Test.ll_files_of_dir dir in let files = List.filter_map (fun path -> let
   _file, ext = Platform.path_to_basename_ext path in try match ext with |
   "ll" -> Some (path, IO.parse_file path, parse_tests path) | _ -> None with
   | Failure s | ParseUtil.InvalidAnonymousId s -> let _ = Printf.printf
   "FAILURE\n %s\n\t%s\n%!" path s in None | _ -> let _ = Printf.printf
   "FAILURE %s\n%!" path in None ) pathlist in let suite = List.map (fun
   (file, ast, tests) -> Test (file, List.map (make_test file ast) tests) )
   files in let outcome = run_suite' suite in failwith "TODO:\n
   Unimplemented" *)
(* Printf.printf "%s\n" (outcome_to_string outcome) ; raise (Ran_tests
   (successful outcome)) *)
