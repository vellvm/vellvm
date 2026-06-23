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
open VellvmLib
open Driver
open Test

(* Modes for the vellvm command: *)
let interpret = ref false
let debugger = ref false
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

  ; ( "-test-pp-file", String FrontendTest.test_pp_file
    , "run the parsing/pretty-printing tests on the given .ll" )
  ; ( "-test-pp-dir", String FrontendTest.test_pp_dir
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
    , Set interpret
    , "interpret ll program starting from 'main'" )
  ; ( "-i"
    , Set interpret
    , "interpret ll program starting from 'main' (same as -interpret)" )

  ; ("-debug", Set Interpreter.debug_flag, "enable debugging trace output")

  ; ("-debugger", Set debugger, "debug an ll program")

  ; ("-v", Set Platform.verbose, "enables more verbose compilation output")
 ]

let main () =
  (* Files specified directly on the command line *)
  let files = ref [] in
  let process_file path =
    let basename, _ = Platform.path_to_basename_ext path in
    let _ = Platform.verb @@ Printf.sprintf "* processing file: %s\n" path in
    (* Parse the file *)
    let ll_ast = IO.parse_file path in
    (* Transform it *)
    let ll_ast' = transform ll_ast in
    (* Add the result to the link files list *)
    let _ = add_link_ast ll_ast' in
    (* Output the resulting processed file *)
    let vll_file = Platform.gen_name !Platform.output_path basename ".v.ll" in
    let _ = IO.output_file vll_file ll_ast' in
    ()
  in
  let _ =
    Platform.configure () ;
    Printf.printf "(* -------- Vellvm Test Harness -------- *)\n%!" ;
    try
      Arg.parse args
        (fun filename -> files := filename :: !files)
        "USAGE: ./vellvm [options] <files>\n" ;
      let () = List.iter process_file !files in
      let prog = TopLevel.link_all !link_files [] in
      if !interpret then
        match Interpreter.interpret !command_line_args prog with
        | Ok dv ->
           Printf.printf "Program terminated with: %s\n" (string_of_dvalue dv)
        | Error e -> failwith (Result.string_of_exit_condition e)
      else if !debugger then
        (Interpreter.debug_flag := true;
         match Debugger.vellvm_debugger !command_line_args prog with
         | Ok dv ->
            Printf.printf "Program terminated with: %s\n" (string_of_dvalue dv)
         | Error e -> failwith (Result.string_of_exit_condition e))
    with
    | Assert.Ran_tests true -> exit 0
    | Assert.Ran_tests false -> exit 1
  in
  ()

;; main ()
