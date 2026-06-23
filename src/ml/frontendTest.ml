open VellvmLib
open Assert

(* Testing for parsing and pretty printing ---------------------------------- *)

(* Should depend only on:
   - rocq/Syntax files
   - rocq/QC/Show
   and *not* on rocq/Semantics or rocq/Handlers (or any other theory)
 *)


let ast_pp_file path =
  let _ = Platform.verb @@ Printf.sprintf "* processing file: %s\n" path in
  let file, ext = Platform.path_to_basename_ext path in
  match ext with
  | "ll" ->
      let ll_ast = IO.parse_file path in
      let vast_file =
        Platform.gen_name !Platform.output_path file ".v.ast"
      in
      (* Prints the original llvm program *)
      let perm = [Open_append; Open_creat] in
      let channel = open_out_gen perm 0o640 vast_file in
      let oc = Format.formatter_of_out_channel channel in
      let _ = IO.output_ast ll_ast oc in
      close_out channel
  | _ -> failwith @@ Printf.sprintf "found unsupported file type: %s" path

let parse_pp_test path =
  let open Platform in
  let _ = verb @@ Printf.sprintf "* processing file: %s\n" path in
  let filename, _ = path_to_basename_ext path in
  let vll_file = gen_name !output_path filename ".v.ll" in
  let out_ll = gen_name !output_path filename ".out.ll" in
  try
    let _ = clang_parse path out_ll in
    let prog = IO.parse_file path in
    let _ = IO.output_file vll_file prog in
    try
      let _ = clang_parse vll_file out_ll in
      ()
    with PlatformError _ ->
      failwith (Printf.sprintf "vellvm output bad file: %s" vll_file)
  with PlatformError _ -> ()

let pp_test_of_dir dir =
  Test
    ( "Parsing files in: " ^ dir ^ "\n"
    , List.map
        (fun f -> (f, fun () -> parse_pp_test f))
        (Platform.ll_files_of_dir dir) )

let test_pp_file path =
  parse_pp_test path

let test_pp_dir dir =
  let _ = Printf.printf "===> RUNNING PRETTY PRINTING TESTS IN: %s\n%!" dir in
  let suite = [pp_test_of_dir dir] in
  let outcome = run_suite suite in
  Printf.printf "%s\n" (outcome_to_string outcome) ;
  raise (Ran_tests (successful outcome))

