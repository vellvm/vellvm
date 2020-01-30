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
open Assert
open Driver

(* test harness ------------------------------------------------------------- *)
exception Ran_tests of bool
let suite = ref Test.suite
let exec_tests () =
  Platform.configure();
  let outcome = run_suite !suite in
  Printf.printf "%s\n" (outcome_to_string outcome);
  raise (Ran_tests (successful outcome))

let test_pp_dir dir =
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
      let ll_ast = parse_file path in
      let ll_ast' = transform ll_ast in
      let vast_file = Platform.gen_name !Platform.output_path file ".v.ast" in

      (* Prints the original llvm program *)
      let _ = output_file vast_file ll_ast' in

      let perm = [Open_append; Open_creat] in
      let channel = open_out_gen perm 0o640 vast_file in
      let oc = (Format.formatter_of_out_channel channel) in

      (* Prints the internal representation of the llvm program *)
      Format.pp_force_newline oc ();
      Format.pp_force_newline oc ();
      Format.pp_print_string oc "Internal Coq representation of the ast:";
      Format.pp_force_newline oc ();
      Format.pp_force_newline oc ();
      let _ = output_ast ll_ast' oc in

      close_out channel
    | _ -> failwith @@ Printf.sprintf "found unsupported file type: %s" path
  end

let ast_pp_file path =
  Platform.configure();
  ast_pp_file_inner path

let ast_pp_dir dir =
  Platform.configure();
  let files = Test.files_of_dir dir in
  List.iter ast_pp_file_inner files

(* Use the --test option to run unit tests and the quit the program. *)
let args =
  [ ("--test", Unit exec_tests, "run the test suite, ignoring later inputs")
  ; ("--test-pp-dir", String test_pp_dir, "run the parsing/pretty-printing tests on all .ll files in the given directory")
  ; ("--print-ast", String ast_pp_file, "run the parsing on the given .ll file and print its internal ast and domination tree")
  ; ("--print-ast-dir", String ast_pp_dir, "run the parsing on the given directory and print its internal ast and domination tree")
  ; ("-op", Set_string Platform.output_path, "set the path to the output files directory  [default='output']")
  ; ("-interpret", Set Driver.interpret, "interpret ll program starting from 'main'")
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


