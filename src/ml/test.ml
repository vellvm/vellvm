(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

open VellvmLib
open Assert

module DV = DynamicValues

(* test harness ------------------------------------------------------------- *)
(* Todo add line count information *)
let parse_tests filename =
  let assertions = ref [] in
  let channel = open_in filename in
  try
    while true do
      let line = input_line channel in
      assertions := Assertion.parse_assertion line @ !assertions
    done ;
    []
  with End_of_file -> close_in channel ; List.rev !assertions

let make_test name link_files ll_ast t : (string * assertion) option =
  let run dtyp entry args ll_ast =
    let linked_ast = TopLevel.link_all link_files ll_ast in
    Interpreter.step
      (TopLevel.interpreter_gen Interpreter.params dtyp
         entry
         (Monad.ret (Obj.magic ITreeDefinition.coq_Monad_itree) args) linked_ast )
  in
  Assertion.make_test_h run name ll_ast t


let test_file_h make_test link_files path =
  Platform.configure () ;
  let _ = Platform.verb @@ Printf.sprintf "* processing file: %s\n" path in
  let _file, ext = Platform.path_to_basename_ext path in
  match ext with
  | "ll" ->
      let tests = parse_tests path in
      let _ = Platform.verb @@ Printf.sprintf "Parsed successfully\n" in
      let ll_ast = IO.parse_file path in
      let _ = Platform.verb @@ Printf.sprintf "AST retrieved successfully\n" in
      let suite = Test (path, List.filter_map (make_test path link_files ll_ast) tests) in
      let outcome = run_suite [suite] in
      Printf.printf "%s\n" (outcome_to_string outcome) ;
      raise (Ran_tests (successful outcome))
  | _ -> failwith @@ Printf.sprintf "found unsupported file type: %s" path

let test_file link_files path = test_file_h make_test link_files path

let test_dir link_files dir =
  Printf.printf "===> TESTING ASSERTIONS IN: %s\n" dir ;
  let pathlist = Platform.ll_files_of_dir dir in
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
        Test (file, List.filter_map (make_test file link_files ast) tests) )
      files
  in
  let outcome = run_suite suite in
  Printf.printf "%s\n" (outcome_to_string outcome) ;
  raise (Ran_tests (successful outcome))

let test_all link_files =
  let test_directory = "../tests" in
  let _ =
    Printf.printf "============== RUNNING TEST SUITE ==============\n"
  in
  let b1 = try FrontendTest.test_pp_dir test_directory with Ran_tests b -> b in
  let b2 = try test_dir link_files test_directory with Ran_tests b -> b in
  raise (Ran_tests (b1 && b2))

