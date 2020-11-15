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

let of_str = Camlcoq.camlstring_of_coqstring

let interpret = ref false

let transform (prog : (LLVMAst.typ, (LLVMAst.typ LLVMAst.block) * ((LLVMAst.typ LLVMAst.block) list)) LLVMAst.toplevel_entity list)
  : (LLVMAst.typ, (LLVMAst.typ LLVMAst.block) * ((LLVMAst.typ LLVMAst.block list))) LLVMAst.toplevel_entity list =
  Transform.transform prog

let print_banner s =
  let rec dashes n = if n = 0 then "" else "-"^(dashes (n-1)) in
  printf "%s %s\n%!" (dashes (79 - (String.length s))) s

let read_file (file:string) : string =
  let lines = ref [] in
  let channel = open_in file in
  try while true; do
      lines := input_line channel :: !lines
  done; ""
  with End_of_file ->
    close_in channel;
    String.concat "\n" (List.rev !lines)

let write_file (file:string) (out:string) =
  let channel = open_out file in
  fprintf channel "%s" out;
  close_out channel

let parse_file filename =
  read_file filename
  |> Lexing.from_string
  |> Llvm_lexer.parse


(* Todo add line count information *)
let parse_tests filename =
  let assertions = ref [] in
  let channel = open_in filename in
  try
    while true; do
      let line = input_line channel in
      assertions := Assertion.parse_assertion filename line @ !assertions
    done; []
  with End_of_file ->
    close_in channel;
    List.rev !assertions

let output_file filename ast =
  let open Llvm_printer in
  let channel = open_out filename in
  toplevel_entities (Format.formatter_of_out_channel channel) ast;
  close_out channel

let output_ast ast channel =
  let open Ast_printer in
  toplevel_entities channel ast

let string_of_file (f:in_channel) : string =
  let rec _string_of_file (stream:string list) (f:in_channel) : string list=
    try
      let s = input_line f in
      _string_of_file (s::stream) f
    with
      | End_of_file -> stream
  in
    String.concat "\n" (List.rev (_string_of_file [] f))


(* file processing ---------------------------------------------------------- *)
let link_files : (string list) ref = ref []
let add_link_file path =
  link_files := path :: (!link_files)

let process_ll_file path file =
  let _ = Platform.verb @@ Printf.sprintf "* processing file: %s\n" path in
  let ll_ast = parse_file path in
  let _ = if !interpret then begin
      let open Format in
      match Interpreter.interpret ll_ast with
      | Ok dv ->
        Printf.printf "Program terminated with: " ;
        let ppf = std_formatter in
        Interpreter.pp_uvalue ppf dv ;
        pp_force_newline ppf ();
        pp_print_flush ppf ()

      | Error msg -> failwith msg
    end
  in
  let ll_ast' = transform ll_ast in
  let vll_file = Platform.gen_name !Platform.output_path file ".v.ll" in
  let _ = output_file vll_file ll_ast' in
  ()


let process_file path =
  let _ = Printf.printf "Processing: %s\n" path in
  let basename, ext = Platform.path_to_basename_ext path in
  begin match ext with
    | "ll" -> process_ll_file path basename
    | _ -> failwith @@ Printf.sprintf "found unsupported file type: %s" path
  end

let process_files files =
  List.iter process_file files

(* file running ---------------------------------------------------------- *)
(* Parses and runs the ll file at the given path, returning the dvalue produced. *)
let run_ll_file path =
  let _ = Platform.verb @@ Printf.sprintf "* running file: %s\n" path in
  let ll_ast = parse_file path in
  Interpreter.interpret ll_ast
