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
open Base    
open Assert
open Driver
open InterpretationStack.InterpreterStackBigIntptr.LP.Events
       
(* test harness ------------------------------------------------------------- *)
exception Ran_tests of bool
let suite = ref Test.suite
let exec_tests () =
  Platform.configure();
  let outcome = run_suite !suite in
  Printf.printf "%s\n" (outcome_to_string outcome);
  raise (Ran_tests (successful outcome))

let dvalue_eq_assertion name (got : unit -> DV.dvalue) (expected : unit -> DV.dvalue) () =
  Platform.verb (Printf.sprintf "running ASSERT in %s" name);
  let dv1 = got () in
  let dv2 = expected () in
  if DV.dvalue_eqb dv1 dv2 then () else
    failwith (Printf.sprintf "dvalues different\ngot:\n\t%s\nexpected:\n\t%s"
                (string_of_dvalue dv1)
                (string_of_dvalue dv2))


let make_test name ll_ast t : string * assertion  =
  let open Format in

  let run dtyp entry args ll_ast () =
      match 
        Interpreter.step
          (TopLevel.TopLevelBigIntptr.interpreter_gen dtyp (Camlcoq.coqstring_of_camlstring entry) args ll_ast)
      with
      | Ok dv -> dv
      | Error e -> failwith e
  in
  
  match t with
  | Assertion.EQTest (expected, dtyp, entry, args) ->
    let str =
      let expected_str = string_of_dvalue expected  in
      let args_str: doc =
        pp_print_list ~pp_sep:(fun f () -> pp_print_string f ", ") Interpreter.pp_uvalue str_formatter args;
        flush_str_formatter()
      in
      Printf.sprintf "%s = %s(%s)" expected_str entry args_str
    in
    let result = run dtyp entry args ll_ast in
    str, (dvalue_eq_assertion name result (fun () -> expected))

  | Assertion.POISONTest (dtyp, entry, args) ->
     let expected = InterpretationStack.InterpreterStackBigIntptr.LP.Events.DV.DVALUE_Poison dtyp in
     let str =
       let expected_str = string_of_dvalue expected in
       let args_str =
         pp_print_list ~pp_sep:(fun f () -> pp_print_string f ", ") Interpreter.pp_uvalue str_formatter args;
         flush_str_formatter()
       in
       Printf.sprintf "%s = %s(%s)" expected_str entry args_str
     in

     let result  = run dtyp entry args ll_ast in 
     str, (dvalue_eq_assertion name result (fun () -> expected))
         
  | Assertion.SRCTGTTest (expected_rett, generated_args) ->
     let (_t_args, v_args) = List.split generated_args in
     let res_src = run expected_rett "src" v_args ll_ast in
     let res_tgt = run expected_rett "tgt" v_args ll_ast in 
     let str = 
      let args_str: doc =
        pp_print_list ~pp_sep:(fun f () -> pp_print_string f ", ") Interpreter.pp_uvalue str_formatter v_args;
        flush_str_formatter()
      in
       Printf.sprintf "src = tgt on generated input (%s)" args_str
     in
     str,  (dvalue_eq_assertion name res_src res_tgt) 

let test_pp_dir dir =
  let _ = Printf.printf "===> RUNNING PRETTY PRINTING TESTS IN: %s\n" dir in  
  Platform.configure();
  let suite = [Test.pp_test_of_dir dir] in
  let outcome = run_suite suite in
  Printf.printf "%s\n" (outcome_to_string outcome);
  raise (Ran_tests (successful outcome))

(* Ugly duplication. TODO: reuse more existing facility *)
let ast_pp_file_inner path =
  let _ = Platform.verb @@ Printf.sprintf "* processing file: %s\n" path in
  let file, ext = Platform.path_to_basename_ext path in
  begin match ext with
    | "ll" ->
      let ll_ast = IO.parse_file path in
      let ll_ast' = transform ll_ast in
      let vast_file = Platform.gen_name !Platform.output_path file ".v.ast" in

      (* Prints the original llvm program *)
      let _ = IO.output_file vast_file ll_ast' in

      let perm = [Open_append; Open_creat] in
      let channel = open_out_gen perm 0o640 vast_file in
      let oc = (Format.formatter_of_out_channel channel) in

      (* Prints the internal representation of the llvm program *)
      Format.pp_force_newline oc ();
      Format.pp_force_newline oc ();
      Format.pp_print_string oc "Internal Coq representation of the ast:";
      Format.pp_force_newline oc ();
      Format.pp_force_newline oc ();
      let _ = IO.output_ast ll_ast' oc in

      close_out channel
    | _ -> failwith @@ Printf.sprintf "found unsupported file type: %s" path
  end

let ast_pp_file path =
  Platform.configure();
  ast_pp_file_inner path

let ast_pp_dir dir =
  Platform.configure();
  let files = Test.ll_files_of_dir dir in
  List.iter ast_pp_file_inner files


let test_file path =
  Platform.configure ();
  let _ = Platform.verb @@ Printf.sprintf "* processing file: %s\n" path in
  let _file, ext = Platform.path_to_basename_ext path in
  begin match ext with
    | "ll" -> 
      let tests = parse_tests path in
      let ll_ast = IO.parse_file path in
      let suite = Test (path, List.map (make_test path ll_ast) tests) in
      let outcome = run_suite [suite] in
      Printf.printf "%s\n" (outcome_to_string outcome);
      raise (Ran_tests (successful outcome))
    | _ -> failwith @@ Printf.sprintf "found unsupported file type: %s" path
  end

let test_dir dir =
  let _ = Printf.printf "===> TESTING ASSERTIONS IN: %s\n" dir in
  Platform.configure();
  let pathlist = Test.ll_files_of_dir dir in
  let files = List.filter_map (fun path ->
      let _file, ext = Platform.path_to_basename_ext path in
      try 
      begin match ext with
        | "ll" -> Some (path, IO.parse_file path, parse_tests path)
        | _ -> None
      end
      with
        Failure s | ParseUtil.InvalidAnonymousId s ->
          let _ = Printf.printf "FAILURE %s\n\t%s\n%!" path s in
          None
      | _ ->
        let _ = Printf.printf "FAILURE %s\n%!" path in
        None
    ) pathlist
  in
  let suite = List.map (fun (file, ast, tests) ->
      Test (file, List.map (make_test file ast) tests)) files in
  let outcome = run_suite suite in
  Printf.printf "%s\n" (outcome_to_string outcome);
  raise (Ran_tests (successful outcome))

let test_directory = ref "../tests"

let test_all () =
  let _ = Printf.printf "============== RUNNING TEST SUITE ==============\n" in
  let b1 = try exec_tests () with Ran_tests b-> b in
  let b2 = try test_pp_dir (!test_directory) with Ran_tests b -> b in
  let b3 = try test_dir (!test_directory) with Ran_tests b -> b in
  raise (Ran_tests (b1 && b2 && b3))

let args =
  [
    ("-set-test-dir", Set_string test_directory, "set the path to the tests directory [default='../tests']")
  ; ("-test", Unit test_all, "run comprehensive test case:\n\tequivalent to running three times with\n\t -test-suite, then\n\t -test-pp-dir ../tests, then\n\t -test-dir ../tests")
  ; ("-test-suite", Unit exec_tests, "run the test suite, ignoring later inputs")
  ; ("-test-file", String test_file, "run the assertions in a given file")
  ; ("-test-dir", String test_dir, "run all .ll files in the given directory")
  ; ("-test-pp-dir", String test_pp_dir, "run the parsing/pretty-printing tests on all .ll files in the given directory")    
  ; ("-print-ast", String ast_pp_file, "run the parsing on the given .ll file and write its internal ast and domination tree to a .v.ast file in the output directory (see -op)")
  ; ("-print-ast-dir", String ast_pp_dir, "run the parsing on the given directory and write its internal ast and domination tree to a .v.ast file in the output directory (see -op)")
  ; ("-op", Set_string Platform.output_path, "set the path to the output files directory  [default='output']")
  ; ("-interpret", Set Driver.interpret, "interpret ll program starting from 'main'")
  ; ("-i", Set Driver.interpret, "interpret ll program starting from 'main' (same as -interpret)")      
  ; ("-debug", Set Interpreter.debug_flag, "enable debugging trace output")
  ; ("-v", Set Platform.verbose, "enables more verbose compilation output")] 

let files = ref []
let _ =
  Printf.printf "(* -------- Vellvm Test Harness -------- *)\n%!";
  try
    Arg.parse args (fun filename -> files := filename :: !files)
      "USAGE: ./vellvm [options] <files>\n";
    Platform.configure ();
    process_files !files

  with Ran_tests true -> exit 0
     | Ran_tests false -> exit 1
