(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

module DV = DynamicValues

let iptr   = IPtrInfinite.coq_IPZ
let params = ParamsV.coq_ParamsV iptr
let addr_v = Address0.coq_AddressV iptr

open LLVMEvents

open Format
open ITreeDefinition
open Result

(* TODO: probably should be part of ADDRESS module interface*)
let pp_addr :
    Format.formatter -> Address.addr -> unit =
 fun ppf _ -> fprintf ppf "DVALUE_Addr(?)"

(* Converts `float` to a `string` at max precision. Both OCaml `printf` and
   `string_of_float` truncate and do not print all significat digits. *)
let string_of_float_full f =
  (* Due to the limited number of bits in the representation of doubles, the
     maximal precision is 324. See Wikipedia. *)
  let s = sprintf "%.350f" f in
  Str.global_replace (Str.regexp "0+$") "" s

let rec pp_uvalue : Format.formatter -> DV.dvalue -> unit =
  let open Camlcoq in
  let open DV in
  let pp_comma_space ppf () = pp_print_string ppf ", " in
  fun ppf -> function
    | DVALUE_Addr _x -> fprintf ppf "DVALUE_Addr"
    | DVALUE_I (sz, x) ->
        fprintf ppf "DVALUE_I%d(%d)"
          (Camlcoq.P.to_int sz) (Camlcoq.Z.to_int (Integers.unsigned sz x))
    | DVALUE_IPTR x ->
        fprintf ppf "DVALUE_IPTR(%d)"
          (Camlcoq.Z.to_int (iptr.to_Z x))
    | DVALUE_Double x ->
        fprintf ppf "DVALUE_Double(%s)"
          (string_of_float_full (camlfloat_of_coqfloat x))
    | DVALUE_Float x ->
        fprintf ppf "DVALUE_Float(%s)"
          (string_of_float_full (camlfloat_of_coqfloat32 x))
    | DVALUE_Poison _ -> fprintf ppf "DVALUE_Poison"
    | DVALUE_None -> fprintf ppf "DVALUE_None"
    | DVALUE_Struct l ->
        fprintf ppf "DVALUE_Struct(%a)"
          (pp_print_list ~pp_sep:pp_comma_space pp_uvalue)
          l
    | DVALUE_Packed_struct l ->
        fprintf ppf "DVALUE_Packet_struct(%a)"
          (pp_print_list ~pp_sep:pp_comma_space pp_uvalue)
          l
    | DVALUE_Array (_, l) ->
        fprintf ppf "DVALUE_Array(%a)"
          (pp_print_list ~pp_sep:pp_comma_space pp_uvalue)
          l
    | DVALUE_Vector (_, l) ->
        fprintf ppf "DVALUE_Vector(%a)"
          (pp_print_list ~pp_sep:pp_comma_space pp_uvalue)
          l

let char_of_I8 x =
  char_of_int (Camlcoq.Z.to_int (Integers.unsigned (Camlcoq.P.of_int 8) x))

(* Converts a list of VellvmIntegers.Int8 values to OCaml string *)
let string_of_bytes (bytes : Integers.bit_int list) : bytes =
  List.map char_of_I8 bytes |> List.to_seq |> Bytes.of_seq

let debug_flag = ref false

(** Print a debug message to stdout if the `debug_flag` is enabled.

    This is used to implement `debugE` events.
*)
let debug (msg : string) =
  if !debug_flag then Printf.printf "DEBUG: %s\n%!" msg

(** The `step` function walks through an itree and handles some
    remaining events.

    In particular, `step` handles `debugE`, `failE`, and
    `ExternalCallE` events, which are not handled by the
    TopLevel.interpreter function extracted from Coq.

    Calling `step` could either loop forever, return an error,
    or return the dvalue result returned from the itree.
 *)

let current_line = ref (Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()))

type interp_state =
  Memory.state * ((Stack.stack_frame * Stack.stack) * (Global.global_env * DV.dvalue))

let single_step (m : (__ coq_L1, interp_state) itree)
    : ((__ coq_L1, interp_state) itree,
       (DV.dvalue, exit_condition) result) Either.t =
  let open ITreeDefinition in
  match observe m with
  (* Internal steps compute as nothing *)
  | TauF x ->
     if !debug_flag then begin
         let loc_str = Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()) in
         if loc_str <> !current_line then begin
             Printf.printf "%s\n%!" loc_str;
             current_line := loc_str
           end
     end;
     Either.left x
  (* SAZ: Could inspect the memory or stack here too. *)
  (* We finished the computation *)
  | RetF (_, ((_, _), (_, v))) -> Either.right (Ok v)
  (* The ExternalCallE effect *)
  | VisF (Sum.Coq_inl1 (ExternalCall (t, _, dvs)), _) ->
     let loc_str = Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()) in
     let typ_str = Camlcoq.camlstring_of_coqstring (ReprAST.repr_dtyp t) in
     let args_str = string_of_int (List.length dvs) in
     Either.right
       (Error (UninterpretedCall
                 (Printf.sprintf "%s: Call with return type %s, %s dvalues."
                    loc_str typ_str args_str)))
  (* Still TODO: Integrate 2nd argument *)
  (* The IO_stdout effect *)
  | VisF (Sum.Coq_inl1 (IO_stdout bytes), k) ->
      let str = string_of_bytes bytes in
      output_bytes stdout str ;
      Either.left (k (Obj.magic ()))
  (* The IO_stderr effect *)
  | VisF (Sum.Coq_inl1 (IO_stderr bytes), k) ->
      let str = string_of_bytes bytes in
      output_bytes stderr str ;
      Either.left (k (Obj.magic ()))
  (* The OOME effect *)
  | VisF (Sum.Coq_inr1 (Sum.Coq_inl1 _msg), _k) ->
     let loc_str = Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()) in
     Either.right (Error (OutOfMemory loc_str))

  (* LLVM Exception event *)
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 _uv)), _k) ->
     let loc_str = Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()) in
     Either.right (Error (LLVMException loc_str))

  (* UBE event *)
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 _msg))), _k) ->
     let loc_str = Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()) in
     Either.right (Error (UndefinedBehavior loc_str))

  (* The DebugE effect *)
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 _msg)))), k) ->
     let loc_str = Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()) in
     (debug loc_str;
      Either.left ((k (Obj.magic DV.DVALUE_None))))

  (* The FailureE effect is a failure *)
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 _msg)))), _) ->
     let loc_str = Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()) in
     Either.right (Error (Failed loc_str))

let rec step (m : (__ coq_L1, interp_state) itree)
    : (DV.dvalue, exit_condition) result =
  match single_step m with
  | Either.Left x -> step x
  | Either.Right res -> res

(** Interpret an LLVM program, returning a result that contains either the
    dvalue result returned by the LLVM program, or an error message.

    Note: programs consist of a non-empty list of blocks, represented by a
    tuple of a single block, and a possibly empty list of blocks.
 *)
let interpret
      (args : string list)
      (prog :
         ( LLVMAst.typ
         , LLVMAst.typ LLVMAst.block * LLVMAst.typ LLVMAst.block list )
           LLVMAst.toplevel_entity
           list )
    : (DV.dvalue, exit_condition) result =
  Out_channel.set_buffered stdout false;
  Out_channel.set_buffered stderr false;
  step (TopLevel.interpreter (List.map Camlcoq.coqstring_of_camlstring args) prog)
