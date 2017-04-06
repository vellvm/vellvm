(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

;; open Platform
;; open Driver
;; open Assert

(* Vellvm test cases -------------------------------------------------------- *)


let parse_pp_test path =
  let _ = Platform.verb @@ Printf.sprintf "* processing file: %s\n" path in
  let filename, ext = Platform.path_to_basename_ext path in
  let vll_file = Platform.gen_name !Platform.output_path filename ".v.ll" in
  let dot_s = Platform.gen_name !Platform.output_path filename ".s" in
  let _ = Printf.fprintf stderr "Running llc on: %s\n%!" path in
  try 
    let _ = llc_parse path dot_s in
    let prog = parse_file path in
    let _ = output_file vll_file prog in
    try
      let _ = llc_parse vll_file dot_s in
      ()
    with
    PlatformError _ -> failwith (Printf.sprintf "vellvm output bad file: %s" vll_file)
  with
    PlatformError _ -> ()



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


