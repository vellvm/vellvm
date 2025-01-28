(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

open Printf
open Base

open InterpretationStack.InterpreterStackBigIntptr.LP.Events

let of_str = Camlcoq.camlstring_of_coqstring

let string_of_dvalue (d : DV.dvalue) = of_str (DV.show_dvalue d)

let interpret = ref false

let trace = ref false

let trace_skip = ref ""

let link = ref false 

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

let print_banner s =
  let rec dashes n = if n = 0 then "" else "-" ^ dashes (n - 1) in
  printf "%s %s\n%!" (dashes (79 - String.length s)) s

(* Todo add line count information *)
let parse_tests filename =
  let assertions = ref [] in
  let channel = open_in filename in
  Assertion.reset_parsing_mode () ;
  (* Put the parser into "NormalMode" *)
  try
    while true do
      let line = input_line channel in
      assertions := Assertion.parse_assertion filename line @ !assertions
    done ;
    []
  with End_of_file -> close_in channel ; List.rev !assertions

let string_of_file (f : in_channel) : string =
  let rec _string_of_file (stream : string list) (f : in_channel) :
      string list =
    try
      let s = input_line f in
      _string_of_file (s :: stream) f
    with End_of_file -> stream
  in
  String.concat "\n" (List.rev (_string_of_file [] f))

(* file processing
   ---------------------------------------------------------- *)
let link_files : string list ref = ref []

let add_link_file path = link_files := path :: !link_files

let assert_max_one_main_fn ast file = 
  ignore (
    List.fold_left (fun main_found user_tle -> 
    match (user_tle, main_found) with 
      (LLVMAst.TLE_Definition { df_prototype = { dc_name = Name ['m'; 'a'; 'i'; 'n'] ; _ } ; _}, true)  -> 
        failwith ("More than one main function found in " ^ file ^ ".ll!")
    | (LLVMAst.TLE_Definition { df_prototype = { dc_name = Name ['m'; 'a'; 'i'; 'n'] ; _ } ; _}, false) -> 
        true
    | _ -> main_found
    ) false ast
  )

let process_trace command_line_arguments ll_ast file =
  let interp_res = Interpreter.interpret command_line_arguments ll_ast in
  let trace_res () = 
    begin match Trace.gen_executable_base_trace ll_ast ~skip:!trace_skip with
      | Ok ll_ast_trace ->
        let ll_ast_trace' = transform ll_ast_trace in
        let tracell_file = Platform.gen_name !Platform.output_path file ".base.trace" in
        IO.output_file tracell_file ll_ast_trace';
        Printf.printf "Trace outputed at: %s\n" tracell_file
      | Error s -> failwith s
    end in
  match interp_res with
  | Ok dv ->
    Printf.printf "Program terminated with: %s\n%!" (string_of_dvalue dv);
    trace_res ()
  | Error e ->
    trace_res ();
    failwith (Result.string_of_exit_condition e)

let process_interpret command_line_arguments ll_ast =
  let res = Interpreter.interpret command_line_arguments ll_ast in
  if !Log.store_log then Trace.print_log ~f:ShowAST.dshowDtyp else ();
  match res with
  | Ok dv ->
    Printf.printf "Program terminated with: %s\n" (string_of_dvalue dv);
  | Error e ->
    failwith (Result.string_of_exit_condition e)

let process_ll_file command_line_arguments path file =
  let _ = Platform.verb @@ Printf.sprintf "* processing file: %s\n" path in
  let ll_ast = IO.parse_file path in
  let _ =
    Log.clear_log;
    assert_max_one_main_fn ll_ast file;
    if !interpret then
      process_interpret command_line_arguments ll_ast
    else
    if !trace then
      process_trace command_line_arguments ll_ast file
    else
      failwith "Process AST: not valid parameter"
  in
  let ll_ast' = transform ll_ast in
  let vll_file = Platform.gen_name !Platform.output_path file ".v.ll" in
  let _ = IO.output_file vll_file ll_ast' in
  ()

let process_file command_line_arguments path =
  let _ = Printf.printf "Processing: %s\n" path in
  let basename, ext = Platform.path_to_basename_ext path in
  match ext with
  | "ll" -> process_ll_file command_line_arguments path basename
  | _ -> failwith @@ Printf.sprintf "found unsupported file type: %s" path

let process_files command_line_args files =
  List.iter (process_file command_line_args) files

(* file running ---------------------------------------------------------- *)
(* Parses and runs the ll file at the given path, returning the dvalue
   produced. *)
let run_ll_file command_line_arguments path : (DV.dvalue, Result.exit_condition) result =
  let _ = Platform.verb @@ Printf.sprintf "* running file: %s\n" path in
  let ll_ast = IO.parse_file path in
  Interpreter.interpret command_line_arguments ll_ast
