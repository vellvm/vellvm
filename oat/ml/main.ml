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

  let interpret_main_file filename =
    let find_fn func (prog: Ast.prog) =
      let open Ast in
      match List.find_opt (fun dec -> match dec with
                                  | Gfdecl {elt = e; loc=_} ->
                                     (Camlcoq.camlstring_of_coqstring e.fname) = func
                                  | _ -> false
              ) prog with
      | Some (Gfdecl {elt = e; loc=_}) ->
         (e.fname, e.frtyp, e.args)
      | _ -> failwith "Could not find function to begin interpreting"
    in
                                                
      

    let prog = parse_oat filename in
    let (fname, ret_ty, _args)  = find_fn "program" prog in
    (* Arguments are empty for now :) *)
    let itree = D.interp_user ret_ty fname [] prog in
    match Interpreter.step itree with
    | Error e ->
       print_endline e
    | Ok dv ->
       print_endline @@ "Interpreting program yielded : " ^ Interpreter.pp_ovalue dv;
  
  
end


open Arg

let args =
  [ ("-c", Unit Quaker.unimplemented, "compile the given oat file")
  ; ("-pp", String Quaker.print_and_parse, "parse and print the given oat file")
  ; ("-interpret_main", String Quaker.interpret_main_file, "Interpret the given oat program from the 'program' method")
  ]


let () =
  Arg.parse args (fun _ -> ())
    " QUAKER OAT Compiler\n\
      USAGE: --help to see the list of options"
