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


let process_ast ll_ast file = 
  let _ =
    Log.clear_log;
    if !interpret then
      (assert_max_one_main_fn ll_ast file;
      match Interpreter.interpret ll_ast with
      | Ok dv ->
        Printf.printf "Program terminated with: %s\n" (string_of_dvalue dv);
      | Error e ->
        Trace.print_log ();
        failwith (Result.string_of_exit_condition e))
    else if !trace then
      match Interpreter.interpret ll_ast with
      | Ok dv ->
        Printf.printf "Program terminated with: %s\n" (string_of_dvalue dv);
        (* Trace.print_log (); *)
        (* Trace.print_normalized_log ll_ast; *)
        begin match Trace.gen_executable_trace ll_ast with
        | Ok ll_ast_trace ->
          let ll_ast_trace' = transform ll_ast_trace in
          let tracell_file = Platform.gen_name !Platform.output_path file ".trace.ll" in
          IO.output_file tracell_file ll_ast_trace'
        | Error s -> failwith s
        end
      | Error e ->
        Trace.print_log ();
        failwith (Result.string_of_exit_condition e)
  in
  let ll_ast' = transform ll_ast in
  let vll_file = Platform.gen_name !Platform.output_path file ".v.ll" in
  let _ = IO.output_file vll_file ll_ast' in
  ()

let process_ll_file path file =
  let _ = Platform.verb @@ Printf.sprintf "* processing file: %s\n" path in
  let ll_ast = IO.parse_file path in
  process_ast ll_ast file 

let process_file f path =
  let _ = Printf.printf "Processing: %s\n" path in
  let basename, ext = Platform.path_to_basename_ext path in
  match ext with
  | "ll" -> f path basename
  | _ -> failwith @@ Printf.sprintf "found unsupported file type: %s" path


(* wishing for normal function composition here *)
let last xs =  List.rev xs |> List.hd

(* Here is where we can build extra checks: definition/declaration alignment, so on. *)
let link_asts = List.concat

(* let cons_uniq xs x = if List.mem x xs then xs else x :: xs

let remove_from_left xs = List.rev (List.fold_left cons_uniq [] xs)
(* RAB: credit https://stackoverflow.com/questions/30634119/ocaml-removing-duplicates-from-a-list-while-maintaining-order-from-the-right 
  for aiding my laziness*)
let validate_ssa = 
  let remove_redundant_metadata ast =  *)



(* links many files to produce a single AST. returns the AST and the name it 
  will carry at runtime. *)
let link_files files = 
  begin
    (* use existing machinery to validate files & add them to link_files *)
    List.iter (process_file (fun p _ -> add_link_file p)) files; 
    (* simple: build one ast and run it *)
    let linked_ast = link_asts (List.map IO.parse_file !link_files) in
    let last_file, _ = Platform.path_to_basename_ext (last !link_files) in
    let final_name = 
      if String.starts_with ~prefix:"linked-" last_file then last_file else 
      "linked-" ^ last_file in 
     (linked_ast, final_name)
  end

let uncurry f (x, y) = f x y

let process_files files = 
  (* length check validates use of `last` (which calls `hd`) *)
  if !link && List.length files >= 2 then
    uncurry process_ast (link_files files)
  else List.iter (process_file process_ll_file) files



(* file running ---------------------------------------------------------- *)
(* Parses and runs the ll file at the given path, returning the dvalue
   produced. *)
let run_ll_file path : (DV.dvalue, Result.exit_condition) result =
  let _ = Platform.verb @@ Printf.sprintf "* running file: %s\n" path in
  let ll_ast = IO.parse_file path in
  Interpreter.interpret ll_ast
