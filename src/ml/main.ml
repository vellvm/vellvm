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

let make_test ll_ast t : string * assertion  =
  match t with
  | Assertion.EQTest (expected, dtyp, entry, args) ->
    let str =
      let expected_str =
        Interpreter.pp_uvalue Format.str_formatter expected;
        Format.flush_str_formatter ()
      in
      let args_str: doc =
        Format.pp_print_list ~pp_sep:(fun f () -> Format.pp_print_string f ", ") Interpreter.pp_uvalue Format.str_formatter  args;
        Format.flush_str_formatter()
      in
      Printf.sprintf "%s = %s(%s)" expected_str entry args_str
    in
    let result () = Interpreter.step (TopLevel.interpreter_gen dtyp (Camlcoq.coqstring_of_camlstring entry) args ll_ast) 
    in
    str, (Assert.assert_eqf result (Ok expected))
  | Assertion.POISONTest (dtyp, entry, args) ->
     let expected = Handlers.LLVMEvents.DV.UVALUE_Poison in
     let str =
       let expected_str =
         Interpreter.pp_uvalue Format.str_formatter expected;
         Format.flush_str_formatter ()
       in
      let args_str =
        Format.pp_print_list ~pp_sep:(fun f () -> Format.pp_print_string f ", ") Interpreter.pp_uvalue Format.str_formatter args;
        Format.flush_str_formatter()
      in
      Printf.sprintf "%s = %s(%s)" expected_str entry args_str
     in

     let result () = Interpreter.step(TopLevel.interpreter_gen dtyp (Camlcoq.coqstring_of_camlstring entry) args ll_ast)
     in 
     str, (Assert.assert_eqf result (Ok expected))
         
  | Assertion.SRCTGTTest (expected_rett, generated_args) ->
     let (_t_args, v_args) = List.split generated_args in
     let res_src () = Interpreter.step(TopLevel.interpreter_gen expected_rett (Camlcoq.coqstring_of_camlstring "src") v_args ll_ast) in
     let res_tgt () = Interpreter.step(TopLevel.interpreter_gen expected_rett (Camlcoq.coqstring_of_camlstring "tgt") v_args ll_ast) in
     let str =
       let src_str =
         match res_src () with
         | Ok v -> Interpreter.pp_uvalue Format.str_formatter v; Format.flush_str_formatter ()
         | Error e -> e
       in
       let tgt_str =
         match res_tgt () with
         | Ok v -> Interpreter.pp_uvalue Format.str_formatter v; Format.flush_str_formatter ()
         | Error e -> e
       in
      let args_str: doc =
        Format.pp_print_list ~pp_sep:(fun f () -> Format.pp_print_string f ", ") Interpreter.pp_uvalue Format.str_formatter v_args;
        Format.flush_str_formatter()
      in
       Printf.sprintf "%s = %s on generated input (%s)" src_str tgt_str args_str
     in
     str,  (Assert.assert_eqf (fun () ->
               let s,t = res_src (), res_tgt() in
               begin match s, t with | Ok sv, Ok tv -> Ok (Assertion.eq_uvalue sv tv)
                               | Error el, _ -> Error el
                               | _, Error er -> Error er
               end
             ) (Ok true))
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


let test_file path =
  Platform.configure ();
  let _ = Platform.verb @@ Printf.sprintf "* processing file: %s\n" path in
  let file, ext = Platform.path_to_basename_ext path in
  begin match ext with
    | "ll" -> 
      let tests = parse_tests path in
      let ll_ast = parse_file path in
      let suite = Test (file, List.map (make_test ll_ast) tests) in
      let outcome = run_suite [suite] in
      Printf.printf "%s\n" (outcome_to_string outcome);
      raise (Ran_tests (successful outcome))
    | _ -> failwith @@ Printf.sprintf "found unsupported file type: %s" path
  end

(* This is part of the standard library since 4.08.0 *)
let rec filter_map (filter: 'a -> 'b option) (l: 'a list) : 'b list =
match l with
| [] -> []
| hd :: tl -> (match filter hd with
              | None -> filter_map filter tl
              | Some b -> b :: filter_map filter tl)

let test_dir dir =
  Platform.configure();
  let pathlist = Test.files_of_dir dir in
  let files = filter_map (fun path ->
      let file, ext = Platform.path_to_basename_ext path in
      begin match ext with
        | "ll" -> Some (file, parse_file path, parse_tests path)
        | _ -> None
      end) pathlist
  in
  let suite = List.map (fun (file, ast, tests) -> Test (file, List.map (make_test ast) tests)) files in
  let outcome = run_suite suite in
  Printf.printf "%s\n" (outcome_to_string outcome);
  raise (Ran_tests (successful outcome))
  

(* Use the --test option to run unit tests and the quit the program. *)
let args =
  [ ("--test", Unit exec_tests, "run the test suite, ignoring later inputs")
  ; ("--test-file", String test_file, "run the assertions in a given file")
  ; ("--test-dir", String test_dir, "run all .ll files in the given directory")
  ; ("--test-pp-dir", String test_pp_dir, "run the parsing/pretty-printing tests on all .ll files in the given directory")
  ; ("--print-ast", String ast_pp_file, "run the parsing on the given .ll file and write its internal ast and domination tree to a .v.ast file in the output directory (see -op)")
  ; ("--print-ast-dir", String ast_pp_dir, "run the parsing on the given directory and write its internal ast and domination tree to a .v.ast file in the output directory (see -op)")
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


