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

let process_ll_file path file =
  let _ = Platform.verb @@ Printf.sprintf "* processing file: %s\n" path in
  let ll_ast = IO.parse_file path in
  let _ =
    if !interpret then
      match Interpreter.interpret ll_ast with
      | Ok dv ->
        Printf.printf "Program terminated with: %s\n" (string_of_dvalue dv);
        (* let ll_ast_trace = gen_executable_trace ll_ast in *)
        (* let ll_ast_trace' = transform ll_ast_trace in *)
        (* let vll_file = Platform.gen_name !Platform.output_path file ".trace.ll" in *)
        (* IO.output_file vll_file ll_ast_trace' *)
        Trace.print_log ();
        Printf.printf "\nNormalizing\n";
        Trace.print_normalized_log ll_ast
      | Error e ->
        Trace.print_log ();
        failwith (Result.string_of_exit_condition e)
  in
  let ll_ast' = transform ll_ast in
  let vll_file = Platform.gen_name !Platform.output_path file ".v.ll" in
  let _ = IO.output_file vll_file ll_ast' in
  ()

let process_file path =
  let _ = Printf.printf "Processing: %s\n" path in
  let basename, ext = Platform.path_to_basename_ext path in
  match ext with
  | "ll" -> process_ll_file path basename
  | _ -> failwith @@ Printf.sprintf "found unsupported file type: %s" path

let process_files files = List.iter process_file files

(* file running ---------------------------------------------------------- *)
(* Parses and runs the ll file at the given path, returning the dvalue
   produced. *)
let run_ll_file path : (DV.dvalue, Result.exit_condition) result =
  let _ = Platform.verb @@ Printf.sprintf "* running file: %s\n" path in
  let ll_ast = IO.parse_file path in
  Interpreter.interpret ll_ast
