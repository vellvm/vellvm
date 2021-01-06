module D = Denotation
module Parse = Oat_parser
module Lex = Oat_lexer
module Pprint = Print_oat

module Quaker = struct

  let fail msg = prerr_endline msg; exit 1

  let safe_open src =
    try open_in src
    with Sys_error msg -> fail msg
  
  let parse_oat filename =
    let lexbuf = safe_open filename |>
                   Lexing.from_channel in
    try
      Parse.prog Lex.token lexbuf
    with
    | Parse.Error -> failwith @@ Printf.sprintf "Parse error at: %s"
                                   (Range.string_of_range (Range.lex_range lexbuf))
    
  let print_ast p = Printf.printf "\n%s\n\n" (Pprint.ml_string_of_prog p)

  let print_and_parse filename = filename |> parse_oat |> print_ast

  let unimplemented () =
    print_endline "function unimplemented";
    exit 0

  let interpret_main_file f =
    let prog = parse_oat filename in
  
end


open Arg

let args =
  [ ("-c", Unit Quaker.unimplemented, "compile the given oat file")
  ; ("-pp", String Quaker.print_and_parse, "parse and print the given oat file")
  ; ("-i", Unit 
  ]


let () =
  Arg.parse args (fun _ -> ())
    " QUAKER OAT Compiler\n\
      USAGE: --help to see the list of options"
