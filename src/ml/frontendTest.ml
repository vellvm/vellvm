open VellvmLib
open Assert

(* Testing for parsing and pretty printing ---------------------------------- *)

(* Should depend only on:
   - rocq/Syntax files
   - rocq/QC/Show
   and *not* on rocq/Semantics or rocq/Handlers (or any other theory)
 *)


(* Vellvm test cases -------------------------------------------------------- *)

let parse_pp_test path =
  let open Platform in
  let _ = verb @@ Printf.sprintf "* processing file: %s\n" path in
  let filename, _ = path_to_basename_ext path in
  let vll_file = gen_name !output_path filename ".v.ll" in
  let dot_s = gen_name !output_path filename ".s" in
  try
    let _ = clang_parse path dot_s in
    let prog = IO.parse_file path in
    let _ = IO.output_file vll_file prog in
    try
      let _ = clang_parse vll_file dot_s in
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

