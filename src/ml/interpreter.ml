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
  | SS.E.Tau (_, x) -> step x
  | SS.E.Vis (Fin v) -> print_int_dvalue v
  | SS.E.Vis (Err s) -> failwith (Printf.sprintf "ERROR: %s" (Camlcoq.camlstring_of_coqstring s))
  | SS.E.Vis (Eff (SS.E.Call(t, f, args, k))) ->
    (Printf.printf "UNINTERPRETED EXTERNAL CALL: %s - returning 0l to the caller\n" (Camlcoq.camlstring_of_coqstring f));
    step (k (SS.DVALUE_I64 StepSemantics.Int64.zero))
    
  | SS.E.Vis (Eff _) -> failwith "should have been handled by the memory model"  
      

let interpret (prog:(Ollvm_ast.block list) Ollvm_ast.toplevel_entity list) =
  let scfg = AstLib.modul_of_toplevel_entities prog in
  match CFG.mcfg_of_modul scfg with
  | None -> failwith "bad module"
  | Some mcfg ->
    begin match SS.init_state mcfg (Camlcoq.coqstring_of_camlstring "main") with
      | Datatypes.Coq_inl err -> failwith (Camlcoq.camlstring_of_coqstring err)
      | Datatypes.Coq_inr s ->
        let sem = SS.sem mcfg s in
        let mem = memD [] sem in
        step mem
    end
  
