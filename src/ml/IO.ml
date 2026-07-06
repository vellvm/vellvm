let read_file (file : string) : string =
  let lines = ref [] in
  let channel = open_in file in
  try
    while true do
      lines := input_line channel :: !lines
    done ;
    ""
  with End_of_file ->
    close_in channel ;
    String.concat "\n" (List.rev !lines)

let write_file (file : string) (out : string) =
  let channel = open_out file in
  Printf.fprintf channel "%s" out ;
  close_out channel

let output_file filename ast =
  let open Llvm_printer in
  let channel = open_out filename in
  toplevel_entities (Format.formatter_of_out_channel channel) ast ;
  close_out channel

let print_ast ast = Llvm_printer.toplevel_entities Format.std_formatter ast

let output_ast ast channel =
  let open Ast_printer in
  toplevel_entities channel ast


let reset_lexbuf (filename:string) (lnum:int) lexbuf : unit =
  lexbuf.Lexing.lex_curr_p <- {
      pos_fname = filename;
      pos_cnum = 0;
      pos_bol = 0;
      pos_lnum = lnum;
    }

let parse_file filename =
  let lexbuf = read_file filename |> 
               Lexing.from_string
  in
  reset_lexbuf filename 1 lexbuf;  (* set the filename *)  
  try Llvm_lexer.parse lexbuf with
  | Failure err -> failwith (Printf.sprintf "Error in file %s: " filename ^ err)

let get_test_name (filename : string) =
  String.sub filename 0 (String.length filename - 3)

