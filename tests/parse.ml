open Ollvm.Lexer
open Ollvm.Ast

let read_file filename =
  let lines = ref "" in
  let chan = open_in filename in
  try
    while true; do
      lines := !lines ^ input_line chan ^ "\n"
    done; ""
  with End_of_file ->
    close_in chan;
    !lines

let parse_file filename =
  parse (Lexing.from_string (read_file filename))

let string_of_ident i =
  match i with
    | ID_Global s -> s
    | ID_Local s -> s

let ident_to_nat i = ???

let ident_to_pos i = Pos.of_nat (ident_to_nat i)

let rec translate_body il =
  match il with
    | [] -> ???
    | i :: rest ->
  
let rec translate ast =
  match ast with
    | [] -> []
    | TLE_Definition d :: rest ->
      let name = d.df_prototype.dc_name in
        (ident_to_nat name, replicate Zero 32, 1, ident_to_pos name, map ident_to_pos d.df_args, translate_body d.df_instrs) ::
          translate rest (S n)
    | _ :: rest -> translate rest m n
