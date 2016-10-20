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
  let _ = Printf.fprintf stderr "Running clang on: %s\n%!" path in
  let _ = clang_parse path clang_ll_file in
  let prog = parse_file path in
  let _ = output_file vll_file prog in
  let _ = clang_parse vll_file clang_vll_file in
  ()


let files_of_dir path : string list =
  let tmp_file = gen_name "." ".ll_files" ".tmp" in
  let cmd = Printf.sprintf "find %s -name \"*.ll\" -print > %s" path tmp_file in
  let () = sh cmd raise_error in 
  let fhandle = open_in tmp_file in
  let rec loop paths =
    try
      loop ((input_line fhandle)::paths)
    with
    | End_of_file -> paths
  in
  let ans = loop [] in
  close_in fhandle;
  let rm_cmd = Printf.sprintf "rm %s" tmp_file in
  let () = sh rm_cmd raise_error in
  ans

let pp_test_of_dir dir =
  Test ("Parsing files in: " ^ dir,
        List.map (fun f -> (f, fun () -> parse_pp_test f)) (files_of_dir dir))

let parse_files =
  [  ]

let test_dirs =
  [  ]

let suite = [Test ("Parsing", List.map (fun f -> (f, fun () -> parse_pp_test f)) parse_files)] @
            (List.map pp_test_of_dir test_dirs)


