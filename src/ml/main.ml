(* A main harness for Coq-extracted LLVM Transformations *)
open Arg
open Driver

(* test harness ------------------------------------------------------------- *)
exception Ran_tests
let exec_tests () =
  Printf.printf "Stub for future test harness\n";
  raise Ran_tests

(* Use the --test option to run unit tests and the quit the program. *)
let args =
  [ ("--test", Unit exec_tests, "run the test suite, ignoring other inputs")
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

  with Ran_tests -> ()



