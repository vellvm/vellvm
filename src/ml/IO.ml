open Platform

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

let parse_file filename =
  read_file filename |> Lexing.from_string |> Llvm_lexer.parse

let ll_files_of_dir path : string list =
  let tmp_file = gen_name "." ".ll_files" ".tmp" in
  let cmd =
    Printf.sprintf "find %s -name \"*.ll\" -print > %s" path tmp_file
  in
  let () = sh cmd raise_error in
  let fhandle = open_in tmp_file in
  let rec loop paths =
    try loop (input_line fhandle :: paths) with End_of_file -> paths
  in
  let ans = loop [] in
  close_in fhandle ;
  let rm_cmd = Printf.sprintf "rm %s" tmp_file in
  let () = sh rm_cmd raise_error in
  ans

let get_test_name (filename : string) =
  String.sub filename 0 (String.length filename - 3)

(* getting rid of the header ".." and "tests". Then split the file name into
   foldername and filename*)
let unzip_filename (filename : string) : string list * string =
  ( List.filter
      (fun x -> not (List.mem x [".."; "tests"; ""]))
      (String.split_on_char '/' (Filename.dirname filename))
  , get_test_name (Filename.basename filename) )
(* let rec concat_until_last (l : string list) (result : string * string) :
   string * string = match l with | str2 :: [] -> (fst result, str2) | str1
   :: xs -> concat_until_last xs (fst result ^ "/" ^ str1, snd result) | _ ->
   result in concat_until_last (List.filter (Fun.flip List.mem ["..";
   "tests"]) (String.split_on_char '/' filename) ) ("", "") *)
