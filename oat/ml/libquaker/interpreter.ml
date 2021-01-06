module T =  Ast
module F = FMapAList
module H = Handlers
module DV = DynamicValues
open ITreeDefinition
open OatEvents

(* Serialize oat values to string *)
let pp_ovalue : DV.ovalue -> string = function
  | OVALUE_Void -> "OVALUE_Void"
  | OVALUE_Bool b -> Printf.sprintf "OVALUE_Bool(%s)" (if b then "true" else "false" )
  | OVALUE_Int i -> Printf.sprintf "OVALUE_Int(%s)" (Int64.to_string (Camlcoq.camlint64_of_coqint i ))
  | OVALUE_Str s -> Printf.sprintf "OVALUE_Str(%s)" (Camlcoq.camlstring_of_coqstring s)
  | _ -> "Unimplemented type"

(* Simplified step method - see vellvms version for a more indepth one of these *)
let rec step (t : ('a coq_Oat2, ( (var, value) F.alist * (var, value) F.alist H.stack) * DV.ovalue) itree) =
  let open  ITreeDefinition in
  match observe t with
  (* Internal step - just keep going *)
  | TauF x -> step x 
  (* Error - something weird happened :o *)
  | VisF (err, _) ->
     Error (Camlcoq.camlstring_of_coqstring err)
  (* Computation terminated in a return value! *)
  | RetF ((_stack_frame, _stack), value) ->
     Ok value

