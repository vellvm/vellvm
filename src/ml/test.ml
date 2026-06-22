(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

open Vellvm_base
open Driver

open Assert

module DV = DynamicValues

let default_cl_test_args = []

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

let ll_files_of_dir path : string list =
  let open Platform in
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

let pp_test_of_dir dir =
  Test
    ( "Parsing files in: " ^ dir ^ "\n"
    , List.map
        (fun f -> (f, fun () -> parse_pp_test f))
        (ll_files_of_dir dir) )

let run_dvalue_test (test : DV.dvalue -> bool) path =
  let res, msg =
    match run_ll_file default_cl_test_args path with
    | Error e -> (false, Result.string_of_exit_condition e)
    | Ok dv -> (test dv, "OK")
  in
  if not res then failwith (path ^ " test failed: " ^ msg) ;
  ()

(* https://www.rosettacode.org/wiki/String_matching#OCaml *)
let string_begins_with s1 s2 =
  let len1 = String.length s1 and len2 = String.length s2 in
  if len1 < len2 then false
  else
    let sub = String.sub s1 0 len2 in
    sub = s2

let run_parsefail_test path prefix =
  let failed, msg =
    try
      ignore (run_ll_file default_cl_test_args path) ;
      (false, "")
    with Failure msg -> (string_begins_with msg prefix, msg)
  in
  if not failed then
    failwith
      ( path
      ^ " test failed to produce expected parsing error. Got ubstead: " ^ msg
      ) ;
  ()


