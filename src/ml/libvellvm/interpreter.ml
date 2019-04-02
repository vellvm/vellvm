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

open Format

(* TODO: probaly should be part of ADDRESS module interface*)
let pp_addr : Format.formatter -> Memory.A.addr -> unit
  = fun ppf _ -> fprintf ppf "DVALUE_Addr(?)"

let rec pp_dvalue : Format.formatter -> DV.dvalue -> unit =
  let open Camlcoq in
  let pp_comma_space ppf () = pp_print_string ppf ", " in
  fun ppf ->
  function
  | DVALUE_Addr   x -> pp_addr ppf x
  | DVALUE_I1     x -> fprintf ppf "DVALUE_I1(%d)"  (Camlcoq.Z.to_int (DynamicValues.Int1.unsigned x))
  | DVALUE_I8     x -> fprintf ppf "DVALUE_I8(%d)"  (Camlcoq.Z.to_int (DynamicValues.Int8.unsigned x))
  | DVALUE_I32    x -> fprintf ppf "DVALUE_I32(%d)" (Camlcoq.Z.to_int (DynamicValues.Int32.unsigned x))
  | DVALUE_I64    x -> fprintf ppf "DVALUE_I64(%s)" (Int64.to_string (Z.to_int64 (DynamicValues.Int64.unsigned x)))
  | DVALUE_Double x -> fprintf ppf "DVALUE_Double(%F)" (camlfloat_of_coqfloat x)
  | DVALUE_Float  x -> fprintf ppf "DVALUE_Float(%F)"  (camlfloat_of_coqfloat32 x)
  | DVALUE_Undef    -> fprintf ppf "DVALUE_Undef"
  | DVALUE_Poison   -> fprintf ppf "DVALUE_Poison"
  | DVALUE_None     -> fprintf ppf "DVALUE_None"
  | DVALUE_Struct        l -> fprintf ppf "DVALUE_Struct(%a)"        (pp_print_list ~pp_sep:pp_comma_space pp_dvalue) l
  | DVALUE_Packed_struct l -> fprintf ppf "DVALUE_Packet_struct(%a)" (pp_print_list ~pp_sep:pp_comma_space pp_dvalue) l
  | DVALUE_Array         l -> fprintf ppf "DVALUE_Array(%a)"         (pp_print_list ~pp_sep:pp_comma_space pp_dvalue) l
  | DVALUE_Vector        l -> fprintf ppf "DVALUE_Vector(%a)"        (pp_print_list ~pp_sep:pp_comma_space pp_dvalue) l

let debug_flag = ref false 
let debug (msg:string) =
  if !debug_flag then 
    Printf.printf "DEBUG: %s\n%!" msg

let rec step m : (DV.dvalue, string) result =
  let open ITreeDefinition in
  match observe m with
  (* Internal steps compute as nothing *)
  | TauF x -> step x

  (* We finished the computation *)
  | RetF (_,v) -> Ok v

  (* The failE effect is a failure *)
  | VisF (Sum.Coq_inr1 (Sum.Coq_inl1 s), _) ->
    Error (Camlcoq.camlstring_of_coqstring s)

  (* The debugE effect *)
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 msg), k) ->
        (debug (Camlcoq.camlstring_of_coqstring msg);
         step (k (Obj.magic DV.DVALUE_None)))

  (* The only visible effects from LLVMIO that should propagate to the interpreter are:
     - Call to external functions
     - Debug  
  *)
  | VisF (Sum.Coq_inl1 e, k) ->
    begin match Obj.magic e with

      | Call(_, f, _) ->
        (Printf.printf "UNINTERPRETED EXTERNAL CALL: %s - returning 0l to the caller\n"
           (Camlcoq.camlstring_of_coqstring f));
        step (k (Obj.magic (DV.DVALUE_I64 DynamicValues.Int64.zero)))
        
      | Alloca _   -> Error "top-level Alloca"
      | Load (_,_) -> Error "top-level Load"
      | Store (_,_) -> Error "top-level Store"
      | GEP (_,_,_) -> Error "top-level GEP"
      | ItoP _ -> Error "top-level ItoP"
      | PtoI _ -> Error "top-level PtoI"
    end


let interpret (prog:(LLVMAst.block list) LLVMAst.toplevel_entity list) : (DV.dvalue, string) result =
  match TopLevel.run_with_memory prog with
  | None -> failwith "ERROR: bad module"
  | Some t -> step t
