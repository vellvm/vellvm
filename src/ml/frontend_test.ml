;; open Base.Assert
;; open Base.Platform
;; open Base.IO


let parse_pp_test path =
  let _ = verb @@ Printf.sprintf "* processing file: %s\n" path in
  let filename, _ = path_to_basename_ext path in
  let vll_file = gen_name !output_path filename ".v.ll" in
  let dot_s = gen_name !output_path filename ".s" in
  try
    let _ = clang_parse path dot_s in
    let prog = parse_file path in
    let _ = output_file vll_file prog in
    try
      let _ = clang_parse vll_file dot_s in
      ()
    with
    PlatformError _ -> failwith (Printf.sprintf "vellvm output bad file: %s" vll_file)
  with
    PlatformError _ -> ()


let pp_test_of_dir dir =
  Test ("Parsing files in: " ^ dir,
        List.map (fun f -> (f, fun () -> parse_pp_test f)) (ll_files_of_dir dir))
