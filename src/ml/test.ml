;; open Platform
;; open Driver
;; open Assert

(* Vellvm test cases -------------------------------------------------------- *)


let parse_pp_test path =
  let _ = Platform.verb @@ Printf.sprintf "* processing file: %s\n" path in
  let filename, ext = Platform.path_to_basename_ext path in
  let clang_ll_file = Platform.gen_name !Platform.output_path filename ".clang.ll" in  
  let vll_file = Platform.gen_name !Platform.output_path filename ".v.ll" in
  let clang_vll_file = Platform.gen_name !Platform.output_path filename ".clang.v.ll" in  
  let _ = clang_parse path clang_ll_file in
  let prog = parse_file path in
  let _ = output_file vll_file prog in
  let _ = clang_parse vll_file clang_vll_file in
  ()

let parse_files =
  [ "/Users/stevez/vellvm/tests/add_twice.ll"
  ; 
  ]

let suite = [Test ("Parsing", List.map (fun f -> (f, fun () -> parse_pp_test f)) parse_files)]


