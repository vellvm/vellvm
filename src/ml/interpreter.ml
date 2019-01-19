(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)


;; open TopLevel.IO

(* TODO: Move this into Coq *)
let rec print_dvalue dv : string =
  match dv with
  | DV.DVALUE_I1 x  -> Printf.sprintf "DVALUE_I1(%d)"  (Camlcoq.Z.to_int (DynamicValues.Int1.unsigned x))
  | DV.DVALUE_I8 x  -> Printf.sprintf "DVALUE_I8(%d)"  (Camlcoq.Z.to_int (DynamicValues.Int8.unsigned x))
  | DV.DVALUE_I32 x -> Printf.sprintf "DVALUE_I32(%d)" (Camlcoq.Z.to_int (DynamicValues.Int32.unsigned x))
  | DV.DVALUE_I64 x -> Printf.sprintf "DVALUE_I64(%d)[possible precision loss: converted to OCaml int]"
                       (Camlcoq.Z.to_int (DynamicValues.Int64.unsigned x))
  | DV.DVALUE_Float x  -> Printf.sprintf "DVALUE_Float(%f)" (Camlcoq.camlfloat_of_coqfloat x)
  | DV.DVALUE_Double x -> Printf.sprintf "DVALUE_Double(%f)" (Camlcoq.camlfloat_of_coqfloat32 x)    
  | DV.DVALUE_Array elts -> Printf.sprintf "DVALUE_Array(%s)" (String.concat "," (List.map print_dvalue elts))
  | _ -> Printf.sprintf "print_dvalue TODO: add support for more dvalues"

let debug_flag = ref false 
let debug (msg:string) =
  if !debug_flag then 
    Printf.printf "DEBUG: %s\n%!" msg

let rec step m : DV.dvalue =
  match Core.observe m with
  (* Internal steps compute as nothing *)
  | Core.TauF x -> step x

  (* We finished the computation *)
  | Core.RetF v -> v

  (* The failE effect is a failure *)
  | Core.VisF (OpenSum.Coq_inrE s, _) ->
    failwith (Printf.sprintf "ERROR: %s" (Camlcoq.camlstring_of_coqstring s))

  (* The only visible effects from LLVMIO that should propagate to the interpreter are:
     - Call to external functions
     - Debug  
  *)
  | Core.VisF (OpenSum.Coq_inlE e, k) ->
    begin match Obj.magic e with

      | Call(_, f, _) ->
        (Printf.printf "UNINTERPRETED EXTERNAL CALL: %s - returning 0l to the caller\n"
           (Camlcoq.camlstring_of_coqstring f));
        step (k (Obj.magic (DV.DVALUE_I64 DynamicValues.Int64.zero)))

      | Debug(msg) ->
        (debug (Camlcoq.camlstring_of_coqstring msg);
         step (k (Obj.magic DV.DVALUE_None)))
        
      | Alloca _   -> failwith "top-level Alloca"
      | Load (_,_) -> failwith "top-level Load"
      | Store (_,_) -> failwith "top-level Store"
      | GEP (_,_,_) -> failwith "top-level GEP"
      | ItoP _ -> failwith "top-level ItoP"
      | PtoI _ -> failwith "top-level PtoI"
    end
      

let interpret (prog:(LLVMAst.block list) LLVMAst.toplevel_entity list) : DV.dvalue = 
  match TopLevel.run_with_memory prog with
  | None -> failwith "ERROR: bad module"
  | Some t -> step t
  
