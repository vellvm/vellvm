(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

open VellvmLib

let transform
    (prog :
      ( LLVMAst.typ
      , LLVMAst.typ LLVMAst.block * LLVMAst.typ LLVMAst.block list )
      LLVMAst.toplevel_entity
      list ) :
    ( LLVMAst.typ
    , LLVMAst.typ LLVMAst.block * LLVMAst.typ LLVMAst.block list )
    LLVMAst.toplevel_entity list =
  prog

(* Files linked by reference to a directory via -L *)
let link_files : TopLevel.ll_toplevel_entities list ref = ref []

let add_link_ast ast =
  link_files := ast :: !link_files

let add_link_file path =
  add_link_ast (IO.parse_file path)

(* Include all .ll files from the given directory *)
let link_dir dir =
  let files = Platform.ll_files_of_dir dir in
  List.iter add_link_file files



