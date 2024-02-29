(* A harness for testing Parsing and Pretty Printing of LLVM IR code. *)
open Arg
open Base
open Assert

(* test harness ------------------------------------------------------------- *)
exception Ran_tests of bool

let test_pp_dir dir =
  let _ = Printf.printf "===> RUNNING PRETTY PRINTING TESTS IN: %s\n" dir in  
  Platform.configure();
  let suite = [Frontend_test.pp_test_of_dir dir] in
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
      let vast_file = Platform.gen_name !Platform.output_path file ".v.ast" in

      (* Prints the original llvm program *)
      let _ = IO.output_file vast_file ll_ast in
      let _ = Printf.printf "pretty-printed version of %s:\n\n" path in
      let _ = IO.print_ast ll_ast in

      let perm = [Open_append; Open_creat] in
      let channel = open_out_gen perm 0o640 vast_file in
      let oc = (Format.formatter_of_out_channel channel) in

      (* Prints the internal representation of the llvm program *)
      Format.pp_force_newline oc ();
      Format.pp_force_newline oc ();
      Format.pp_print_string oc "Internal Coq representation of the ast:";
      Format.pp_force_newline oc ();
      Format.pp_force_newline oc ();
      let _ = IO.output_ast ll_ast oc in

      close_out channel
    | _ -> failwith @@ Printf.sprintf "found unsupported file type: %s" path
  end

let ast_pp_file path =
  Platform.configure();
  ast_pp_file_inner path

let ast_pp_dir dir =
  Platform.configure();
  let files = IO.ll_files_of_dir dir in
  List.iter ast_pp_file_inner files

let test_directory = ref "../tests"

let process_files files =
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
  ; ("-print-ast", String ast_pp_file, "run the parsing on the given .ll file and write its internal ast and domination tree to a .v.ast file in the output directory (see -op)")
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
