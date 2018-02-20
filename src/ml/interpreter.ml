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
  | SS.DVALUE_I1 (x) -> Printf.printf "Program terminated with: DVALUE_I1(%d)\n" (Camlcoq.Z.to_int (StepSemantics.Int1.unsigned x))
  | SS.DVALUE_I32 (x) -> Printf.printf "Program terminated with: DVALUE_I32(%d)\n" (Camlcoq.Z.to_int (StepSemantics.Int32.unsigned x))
  | SS.DVALUE_I64 (x) -> Printf.printf "Program terminated with: DVALUE_I64(%d) [possible precision loss: converted to OCaml int]\n"
                       (Camlcoq.Z.to_int (StepSemantics.Int64.unsigned x))
  | _ -> Printf.printf "Program terminated with non-Integer value.\n"

let rec step m =
  match Lazy.force m with
  | Trace.Tau x -> step x
  | Trace.Ret v -> print_int_dvalue v
  | Trace.Err s -> failwith (Printf.sprintf "ERROR: %s" (Camlcoq.camlstring_of_coqstring s))
  | Trace.Vis (SS.INTERACTION_INTERFACE.Call(t, f, args), k) ->
    (Printf.printf "UNINTERPRETED EXTERNAL CALL: %s - returning 0l to the caller\n" (Camlcoq.camlstring_of_coqstring f));
    step (k (Obj.magic (SS.DVALUE_I64 StepSemantics.Int64.zero)))
    
  | Trace.Vis _ -> failwith "should have been handled by the memory model"  
      

let interpret (prog:(LLVMAst.block list) LLVMAst.toplevel_entity list) =
  match Memory.run_with_memory prog with
  | None -> failwith "bad module"
  | Some t -> step t
  
