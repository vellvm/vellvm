(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

(* A main harness for Coq-extracted LLVM Transformations *)
open Arg
open Vellvm_base
open Result
open Assert
open Driver

module DV = DynamicValues

let string_of_function_id id : string =
  LLVMAst.( match id with
  | Name n -> "@" ^ (Camlcoq.camlstring_of_coqstring n)
  | Anon z -> "@" ^ (Camlcoq.Z.to_string z)
  | Raw z ->  "_RAW_" ^  (Camlcoq.Z.to_string z)
  )


(* test harness ------------------------------------------------------------- *)
exception Ran_tests of bool

let srctgt_test_flag = ref false

let compare_dvalues_exn dv1 dv2 ans : unit =
  if TopLevel.dvalue_eqb dv1 dv2 = ans then ()
  else
    failwith
      (Printf.sprintf
         "dvalue comparison for %s failed: \ngot:\n\t%s\nasserted:\n\t%s"
         (if ans then "equality" else "inequality")
         (string_of_dvalue dv1) (string_of_dvalue dv2) )

let dvalue_eq_assertion name (got : unit -> DV.dvalue)
    (expected : unit -> DV.dvalue) () =
  Platform.verb (Printf.sprintf "running ASSERT in %s\n" name) ;
  let dv1 = got () in
  let dv2 = expected () in
  compare_dvalues_exn dv1 dv2 true

let compare_tgt_for_poison src tgt : unit =
  match tgt with
  | DV.DVALUE_Poison _ -> (
    match src with
    | DV.DVALUE_Poison _ ->
        failwith
          "TargetMorePoisonous: expected src to be non-poison value, but \
           got poison"
    | _ -> () )
  | _ ->
      failwith
        (Printf.sprintf
           "TargetMorePoisonous: expected tgt to be poison but got %s"
           (string_of_dvalue tgt) )

(* TODO: This could be reformated to make it cleaner - move some of it to
   assertion.ml?. *)
(* SAZ: why does this duplicate a lot of code in tester.ml? *)
let make_test_h run name ll_ast t : (string * assertion) option =
  let open Format in
  (* TODO: ll_ast is of type list (toplevel_entity typ (block typ * list
     (block typ))) *)
  (* Can just replace this with the newer ones? *)
  let run_to_value dtyp entry args ll_ast () : DV.dvalue =
    match run dtyp entry args ll_ast with
    | Ok dv -> dv
    | Error e -> failwith (Result.string_of_exit_condition e)
  in
  (* let _ = Printf.printf "I can get here\n" in *)
  match t with
  | Assertion.EQTest (expected, dtyp, entry, args) ->
      let str =
        let expected_str = string_of_dvalue expected in
        let args_str : doc =
          pp_print_list
            ~pp_sep:(fun f () -> pp_print_string f ", ")
            Interpreter.pp_dvalue str_formatter args ;
          flush_str_formatter ()
        in
        Printf.sprintf "%s = %s(%s)" expected_str (string_of_function_id entry) args_str
      in
      let result = run_to_value dtyp entry args ll_ast in
      Some (str, dvalue_eq_assertion name result (fun () -> expected))
  | Assertion.SuccessTest ( entry, args) ->
      let str =
        let args_str : doc =
          pp_print_list
            ~pp_sep:(fun f () -> pp_print_string f ", ")
            Interpreter.pp_dvalue str_formatter args ;
          flush_str_formatter ()
        in
        Printf.sprintf "%s(%s)" (string_of_function_id entry) args_str
      in
      let t_void = Assertion.typ_to_dtyp (LLVMAst.TYPE_Void) in
      Some (str, (fun () -> ignore (run_to_value t_void entry args ll_ast ())))
  | Assertion.POISONTest (dtyp, entry, args) ->
       let expected =
           DV.DVALUE_Poison
           dtyp
       in
       let str =
         let expected_str = string_of_dvalue expected in
         let args_str =
           pp_print_list
             ~pp_sep:(fun f () -> pp_print_string f ", ")
             Interpreter.pp_dvalue str_formatter args ;
           flush_str_formatter ()
         in
         Printf.sprintf "%s = %s(%s)" expected_str (string_of_function_id entry) args_str
       in
       let result = run_to_value dtyp entry args ll_ast in
       Some (str, dvalue_eq_assertion name result (fun () -> expected))

  | Assertion.SRCTGTTest (mode, expected_rett, generated_args) ->
      let v_args, src_fn_str, tgt_fn_str, sum_ast =
        match generated_args with
        | Left g_args ->
            let _t_args, v_args = List.split g_args in
            (v_args, "src", "tgt", ll_ast)
        | Right g_ast ->
            ([], "runnersrc", "runnertgt", List.append ll_ast g_ast)
      in
      let assertion () =
        (* let buf = Buffer.create 16 in List.iter (Buffer.add_char buf)
           (showProg sum_ast); Printf.printf "%s\n" (Buffer.contents buf); *)
        let tgt_fn_id = LLVMAst.Name (Camlcoq.coqstring_of_camlstring tgt_fn_str) in
        let src_fn_id = LLVMAst.Name (Camlcoq.coqstring_of_camlstring src_fn_str) in      
        let res_tgt = run expected_rett tgt_fn_id v_args sum_ast in
        let res_src = run expected_rett src_fn_id v_args sum_ast in
        match res_tgt with
        | Error (UndefinedBehavior _) ->
            () (* If the target is UB then the src can be anything! *)
        | Error (UninterpretedCall _) ->
            Platform.verb
              (Printf.sprintf
                 "  src-tgt test %s passed due to uninterpreted call\n" name )
        | Ok v_tgt -> (
          match res_src with
          | Ok v_src -> (
              Assertion.(
                match mode with
                | NormalEquality -> compare_dvalues_exn v_src v_tgt true
                | ValueMismatch -> compare_dvalues_exn v_src v_tgt false
                | TargetMorePoisonous -> compare_tgt_for_poison v_src v_tgt
                | TargetMoreUndefined -> failwith "todo: TargetMoreUndefined"
                | SourceMoreDefined -> failwith "todo: SourceMoreDefined"
                | MismatchInMemory -> failwith "todo: MismatchInMemory" ) )
          | Error (UninterpretedCall _) ->
              Platform.verb
                (Printf.sprintf
                   "  src-tgt test %s passed due to uninterpreted call\n"
                   name )
          | Error e ->
              failwith
                (Printf.sprintf "src - %s"
                   (Result.string_of_exit_condition e) ) )
        | Error e ->
            (* let buf = Buffer.create 16 in List.iter (Buffer.add_char buf)
               (showProg sum_ast); Printf.printf "%s\n" (Buffer.contents
               buf); *)
            failwith
              (Printf.sprintf "tgt - %s"
                 (Result.string_of_exit_condition e) )
      in
      if !srctgt_test_flag
      then
        let str =
          let args_str : doc =
            pp_print_list
              ~pp_sep:(fun f () -> pp_print_string f ", ")
              Interpreter.pp_dvalue str_formatter v_args ;
            flush_str_formatter ()
          in
          Printf.sprintf "src = tgt on generated input (%s)" args_str
        in
        Some (str, assertion)
      else None

let make_test name ll_ast t : (string * assertion) option =
  let run dtyp entry args ll_ast =
    let linked_ast = TopLevel.link_all !Driver.link_files ll_ast in
    Interpreter.step
      (TopLevel.interpreter_gen Interpreter.params dtyp
         entry
         (Monad.ret (Obj.magic ITreeDefinition.coq_Monad_itree) args) linked_ast )
  in
  make_test_h run name ll_ast t

let test_pp_file path =
  Platform.configure ();
  Test.parse_pp_test path

let test_pp_dir dir =
  let _ = Printf.printf "===> RUNNING PRETTY PRINTING TESTS IN: %s\n%!" dir in
  Platform.configure () ;
  let suite = [Test.pp_test_of_dir dir] in
  let outcome = run_suite suite in
  Printf.printf "%s\n" (outcome_to_string outcome) ;
  raise (Ran_tests (successful outcome))

(* Ugly duplication. TODO: reuse more existing facility *)
let ast_pp_file_inner path =
  let _ = Platform.verb @@ Printf.sprintf "* processing file: %s\n" path in
  let file, ext = Platform.path_to_basename_ext path in
  match ext with
  | "ll" ->
      let ll_ast = IO.parse_file path in
      let ll_ast' = transform ll_ast in
      let vast_file =
        Platform.gen_name !Platform.output_path file ".v.ast"
      in
      (* Prints the original llvm program *)
      let perm = [Open_append; Open_creat] in
      let channel = open_out_gen perm 0o640 vast_file in
      let oc = Format.formatter_of_out_channel channel in
      let _ = IO.output_ast ll_ast' oc in
      close_out channel
  | _ -> failwith @@ Printf.sprintf "found unsupported file type: %s" path

let ast_pp_file path = Platform.configure () ; ast_pp_file_inner path

let link_dir dir =
  Platform.configure () ;
  let files = Test.ll_files_of_dir dir in
  List.iter Driver.add_link_file files

let test_file_h make_test path =
  Platform.configure () ;
  let _ = Platform.verb @@ Printf.sprintf "* processing file: %s\n" path in
  let _file, ext = Platform.path_to_basename_ext path in
  match ext with
  | "ll" ->
      let tests = parse_tests path in
      let _ = Printf.printf "Parsed successfully\n" in
      let ll_ast = IO.parse_file path in
      let _ = Printf.printf "AST retrieved successfully\n" in
      let suite = Test (path, List.filter_map (make_test path ll_ast) tests) in
      let outcome = run_suite [suite] in
      Printf.printf "%s\n" (outcome_to_string outcome) ;
      raise (Ran_tests (successful outcome))
  | _ -> failwith @@ Printf.sprintf "found unsupported file type: %s" path

let test_file path = test_file_h make_test path

let test_dir dir =
  Printf.printf "===> TESTING ASSERTIONS IN: %s\n" dir ;
  Platform.configure () ;
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
        | Failure s | Parse_util.InvalidAnonymousId s ->
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
        Test (file, List.filter_map (make_test file ast) tests) )
      files
  in
  let outcome = run_suite suite in
  Printf.printf "%s\n" (outcome_to_string outcome) ;
  raise (Ran_tests (successful outcome))

let test_all () =
  let test_directory = "../tests" in
  let _ =
    Printf.printf "============== RUNNING TEST SUITE ==============\n"
  in
  let b1 = try test_pp_dir test_directory with Ran_tests b -> b in
  let b2 = try test_dir test_directory with Ran_tests b -> b in
  raise (Ran_tests (b1 && b2))

let command_line_args = ref ["todo"]

let args =
  [ ( "-test"
    , Unit test_all
    , "run comprehensive test suite\n\
       \tequivalent to running:\n\
       \t -test-pp-dir ../tests, then\n\
       \t -test-dir ../tests" )

  ; ( "-test-file", String test_file, "run the assertions in a given file")
  ; ( "-test-dir", String test_dir, "run all .ll files in the given directory")

  ; ( "-test-pp-file", String test_pp_file
    , "run the parsing/pretty-printing tests on the given .ll" )
  ; ( "-test-pp-dir", String test_pp_dir
    , "run the parsing/pretty-printing tests on all .ll files in the given \
       directory" )

  ; ( "-print-ast"
    , String ast_pp_file
    , "run the parsing on the given .ll file and write its internal ast \
       representation to a .v.ast file in the output directory." )

  ; ( "-args"
    , Rest_all (fun args -> command_line_args := args)
    , "interpret the rest of the command line arguments as 'argv' for 
       EACH .ll file that vellvm interprets. Note that all strings after 
       -args will be interpreted as members of argv, and not arguments to vellvm."
    )
  ; ( "-op"
    , Set_string Platform.output_path
    , "set the path to the output files directory  [default='output']" )

  ; ( "-L"
    , String link_dir
    , "Link all .ll files in the given directory" )

  ; ( "-interpret"
    , Set Driver.interpret
    , "interpret ll program starting from 'main'" )
  ; ( "-i"
    , Set Driver.interpret
    , "interpret ll program starting from 'main' (same as -interpret)" )

  ; ("-debug", Set Interpreter.debug_flag, "enable debugging trace output")
  ; ("-debugger", Set Driver.debugger, "debug an ll program")

  ; ("-v", Set Platform.verbose, "enables more verbose compilation output")
 ]

let main () =
  let files = ref [] in
  let _ =
    Platform.configure () ;
    Printf.printf "(* -------- Vellvm Test Harness -------- *)\n%!" ;
    try
      Arg.parse args
        (fun filename -> files := filename :: !files)
        "USAGE: ./vellvm [options] <files>\n" ;
      process_files !command_line_args !files
    with
    | Ran_tests true -> exit 0
    | Ran_tests false -> exit 1
  in
  ()


;; main ()
