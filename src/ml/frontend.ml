(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

(* A harness for testing Parsing and Pretty Printing of LLVM IR code. *)
open Arg
open Base
open Assert

(* test harness ------------------------------------------------------------- *)
exception Ran_tests of bool

let test_pp = ref false

let test_pp_dir dir =
  let _ = Printf.printf "===> RUNNING PRETTY PRINTING TESTS IN: %s\n" dir in  
  Platform.configure();
  let suite = [Frontend_test.pp_test_of_dir dir] in
  let outcome = run_suite suite in
  Printf.printf "%s\n" (outcome_to_string outcome);
  raise (Ran_tests (successful outcome))

let process_test_pp file =
  Frontend_test.parse_pp_test file

let histogram_only = ref false

let output_histogram oc =
  Format.pp_print_string oc (Histogram.to_string Llvm_lexer.histogram);
  Format.pp_force_newline oc ()


(* Ugly duplication. TODO: reuse more existing facility *)
let process_histogram path =
  let _ = Platform.verb @@ Printf.sprintf "* processing file: %s\n" path in
  let file, ext = Platform.path_to_basename_ext path in
  let perm = [Open_append; Open_creat] in
  begin match ext with
    | "ll" ->
      (* Reset lexer token histogram data *)
      let _ = Hashtbl.clear (Llvm_lexer.histogram) in

      (* Parse the file - compute histogram as side effect *)
      let _ll_ast = IO.parse_file path in

      (* Output histogram data *)
      let hist_file = Platform.gen_name !Platform.output_path file ".hist" in
      let hist_channel = open_out_gen perm 0o640 hist_file in
      let hoc = (Format.formatter_of_out_channel hist_channel) in
      let _ = output_histogram hoc in
      let _ = close_out hist_channel in
      ()
    | _ -> failwith @@ Printf.sprintf "found unsupported file type: %s" path
  end

let transform
    (prog :
      ( LLVMAst.typ
      , LLVMAst.typ LLVMAst.block * LLVMAst.typ LLVMAst.block list )
      LLVMAst.toplevel_entity
      list ) :
    ( LLVMAst.typ
    , LLVMAst.typ LLVMAst.block * LLVMAst.typ LLVMAst.block list )
    LLVMAst.toplevel_entity
    list =
  Transform.transform prog

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
      let _ = IO.output_file vast_file ll_ast' in
      let perm = [Open_append; Open_creat] in
      let channel = open_out_gen perm 0o640 vast_file in
      let oc = Format.formatter_of_out_channel channel in
      (* Prints the internal representation of the llvm program *)
      Format.pp_force_newline oc () ;
      Format.pp_force_newline oc () ;
      Format.pp_print_string oc "Internal Coq representation of the ast:" ;
      Format.pp_force_newline oc () ;
      Format.pp_force_newline oc () ;
      let _ = IO.output_ast ll_ast' oc in
      close_out channel
  | _ -> failwith @@ Printf.sprintf "found unsupported file type: %s" path


let ast_pp_file path =
  Platform.configure();
  ast_pp_file_inner path

let ast_pp_dir dir =
  Platform.configure();
  let files = IO.ll_files_of_dir dir in
  List.iter ast_pp_file_inner files

let test_directory = ref "../tests"

let process_files files =
  Platform.configure ();
  if !test_pp then
    List.iter process_test_pp files
  else if !histogram_only then
    List.iter process_histogram files
  else 
    List.iter ast_pp_file_inner files

let test_all () =
  let _ = Printf.printf "============== RUNNING TEST SUITE ==============\n" in
  let b2 = try test_pp_dir (!test_directory) with Ran_tests b -> b in
  raise (Ran_tests (b2))

let args =
  [
    ("-set-test-dir", Set_string test_directory, "set the path to the tests directory [default='../tests']")
  ; ("-test", Unit test_all, "run comprehensive parsing test suite:\n\tequivalent to running with -test-pp-dir <test-dir> (default '../tests')")
  ; ("-test-pp-dir", String test_pp_dir, "run the parsing/pretty-printing tests on all .ll files in the given directory")    
  ; ("-test-pp", Set test_pp, "run the parsing/pretty-printing tests on the provided .ll files (overrides histogram)")
  ; ("-print-ast", String ast_pp_file, "run the parsing on the given .ll file and write its internal ast and domination tree to a .v.ast file in the output directory (see -op)")
  ; ("-histogram-only", Set histogram_only, "create only the .hist file for each of the .ll inputs")
  ; ("-print-ast-dir", String ast_pp_dir, "run the parsing on the given directory and write its internal ast and domination tree to a .v.ast file in the output directory (see -op)")
  ; ("-op", Set_string Platform.output_path, "set the path to the output files directory  [default='output']")
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
