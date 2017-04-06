(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)


(* -------------------------------------------------------------------------- *)
(** Assembling and linking for X86.  Depends on the underlying OS platform    *)


open Printf
open Unix

exception PlatformError of string * string


(* -------------------------------------------------------------------------- *)
(* Platform specific configuration: Unix/Linux vs. Mac OS X                   *)

let os = Sys.os_type   (* One of "Unix" "Win32" or "Cygwin" *)

(* Default to Mac OS X configuration *)
let linux = ref false
let linux_target_triple = ref "x86_64-suse-linux"
let mangle name = if !linux then name else ("_" ^ name)

let clang_flags = ref "-fno-asynchronous-unwind-tables -mstackrealign"
let clang_ll_mode = ref "-S"
let as_mode = ref "-c" 
let link_mode = ref ""

let clang mode opt_level =
  Printf.sprintf "clang %s %s %s -o " mode opt_level !clang_flags

let llc opt_level =
  Printf.sprintf "llc %s -o " opt_level

let clang_cmd opt_level = clang !clang_ll_mode opt_level
let as_cmd    opt_level = clang !as_mode opt_level
let link_cmd  opt_level = clang !link_mode opt_level
let clang_parse_cmd = clang "-S -emit-llvm -w" "-O0"

let llc_compile_cmd = llc "-O0"

let pp_cmd = ref "cpp -E " 
let rm_cmd = ref "rm -rf " 

let verbose = ref false
let verb msg = (if !verbose then print_string msg)

      
(* paths -------------------------------------------------------------------- *)

let path_sep = "/"
let dot_path = "./"
let output_path = ref "output"
let libs = ref [] 
let lib_paths = ref []
let lib_search_paths = ref []
let include_paths = ref []
let executable_name = ref "a.out"


(* Set the link commands properly, ensure output directory exists *)
let configure () =
  if os <> "Unix" then failwith "Windows not supported"
  else begin
  let _ = if !linux then 
      (verb "platform = linux\n";
       clang_flags := "";
      )
    else 
      (verb "platform = OS X\n")
  in
  try ignore (stat !output_path)
  with Unix_error (ENOENT,_,_) ->
    (verb @@ Printf.sprintf "creating output directory: %s\n" !output_path);
    mkdir !output_path 0o755
  end


(* filename munging --------------------------------------------------------- *)
let path_to_basename_ext (path:string) : string * string =
  (* The path is of the form ... "foo/bar/baz/<file>.ext" *)
  let paths = Str.split (Str.regexp_string path_sep) path in
  let _ = if (List.length paths) = 0 then failwith @@ sprintf "bad path: %s" path in
  let filename = List.hd (List.rev paths) in
  match Str.split (Str.regexp_string ".") filename with
  | [] -> failwith @@ sprintf "no filename found: %s" filename 
  | [root] -> root, ""
  | l ->
    begin match List.rev l with
      | [] -> failwith "path_to_basename_ext got bad path"
      | ext::rst -> (String.concat "" (List.rev rst), ext)
    end

(* compilation and shell commands-------------------------------------------- *)

(* Platform independent shell command *)  
let sh (cmd:string) (ret:string -> int -> 'a) : 'a =
  verb (sprintf "* %s\n" cmd);
  match (system cmd) with
  | WEXITED   i -> ret cmd i
  | WSIGNALED i -> raise (PlatformError (cmd, sprintf "Signaled with %d." i))
  | WSTOPPED  i -> raise (PlatformError (cmd, sprintf "Stopped with %d." i))

(* Generate a name that does not already exist.
   basedir includes the path separator
*)
let gen_name (basedir:string) (basen:string) (baseext:string) : string =  
  let rec nocollide ofs =
    let nfn = sprintf "%s/%s%s%s" basedir basen
        (if ofs = 0 then "" else "_"^(string_of_int ofs)) baseext
    in
      try ignore (stat nfn); nocollide (ofs + 1)
      with Unix_error (ENOENT,_,_) -> nfn
  in nocollide 0


let raise_error cmd i =
  if i <> 0 then raise (PlatformError (cmd, sprintf "Exited with status %d." i))

let ignore_error _ _ = ()

let clang_compile (dot_ll:string) (dot_s:string) (opt_level:string) : unit =
  sh (sprintf "%s%s %s" (clang_cmd opt_level) dot_s dot_ll) raise_error

let clang_parse (in_dot_ll:string) (out_dot_ll:string) : unit =
  sh (sprintf "%s%s %s" clang_parse_cmd out_dot_ll in_dot_ll) raise_error

let llc_compile (in_dot_ll:string) (dot_s:string) : unit =
  sh (sprintf "%s%s %s" llc_compile_cmd dot_s in_dot_ll) raise_error

let llc_parse (in_dot_ll:string) (dot_s:string) : unit =
  sh (sprintf "%s%s %s" llc_compile_cmd dot_s in_dot_ll) raise_error

let assemble (dot_s:string) (dot_o:string) (opt_level:string) : unit =
  sh (sprintf "%s%s %s" (as_cmd opt_level) dot_o dot_s) raise_error

let preprocess (dot_oat:string) (dot_i:string) : unit =
  sh (sprintf "%s%s %s %s" !pp_cmd 
	(List.fold_left (fun s -> fun i -> s ^ " -I" ^ i) "" !include_paths)
        dot_oat dot_i) raise_error

let link (mods:string list) (out_fn:string) (opt_level:string) : unit =
  sh (sprintf "%s%s %s %s %s %s" (link_cmd opt_level) out_fn 
	(String.concat " " (mods @ !lib_paths))
	(List.fold_left (fun s -> fun i -> s ^ " -L" ^ i) "" !lib_search_paths)
	(List.fold_left (fun s -> fun i -> s ^ " -I" ^ i) "" !include_paths)
        (List.fold_left (fun s -> fun l -> s ^ " -l" ^ l) "" !libs))
    raise_error



