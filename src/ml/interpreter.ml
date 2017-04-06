(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

;; open Memory


let print_int_dvalue dv : unit =
  match dv with
  | SS.DV (Ollvm_ast.VALUE_Integer i) -> Printf.printf "Program terminated with: %d\n" (Camlcoq.Z.to_int i)
  | _ -> Printf.printf "Program terminated with non-Integer value.\n"

let rec step m =
  match Lazy.force m with
  | SS.E.Tau x -> step x
  | SS.E.Fin v -> print_int_dvalue v
  | SS.E.Err s -> failwith (Printf.sprintf "ERROR: %s" (Camlcoq.camlstring_of_coqstring s))
  | SS.E.Ret _ -> failwith "should be impossible"
  | SS.E.Eff (SS.E.Call(args, k)) -> ()
  | SS.E.Eff _ -> failwith "should have been handled by the memory model"  
      

let interpret (prog:Ollvm_ast.toplevel_entity list) =
  match CFG.coq_TLE_to_cfg prog with
  | None -> failwith "Vellvm interpreter got bad control-flow graph"
  | Some cfg ->
    let sem = SS.sem cfg (SS.init_state cfg) in
    let mem = memD [] sem in
    step mem
  
  
