(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

open Handlers.MemTheory.Mem
open Handlers.Local
open Handlers.Stack
open Handlers.Global
open Handlers.LLVMEvents

open Format
open ITreeDefinition

(* TODO: probably should be part of ADDRESS module interface*)
let pp_addr : Format.formatter -> Memory.Addr.addr -> unit
  = fun ppf _ -> fprintf ppf "UVALUE_Addr(?)"

(* Converts `float` to a `string` at max precision.
   Both OCaml `printf` and `string_of_float` truncate
   and do not print all significat digits.
*)
let string_of_float_full f =
  (* Due to the limited number of bits in the representation of doubles, the maximal precision is 324. See Wikipedia. *)
  let s = sprintf "%.350f" f in
  let open Str in
  Str.global_replace (Str.regexp "0+$") "" s

let rec pp_uvalue : Format.formatter -> DV.uvalue -> unit =
  let open Camlcoq in
  let pp_comma_space ppf () = pp_print_string ppf ", " in
  fun ppf ->
  function
  | UVALUE_Addr   x -> pp_addr ppf x
  | UVALUE_I1     x -> fprintf ppf "UVALUE_I1(%d)"  (Camlcoq.Z.to_int (DynamicValues.Int1.unsigned x))
  | UVALUE_I8     x -> fprintf ppf "UVALUE_I8(%d)"  (Camlcoq.Z.to_int (DynamicValues.Int8.unsigned x))
  | UVALUE_I32    x -> fprintf ppf "UVALUE_I32(%d)" (Camlcoq.Z.to_int (DynamicValues.Int32.unsigned x))
  | UVALUE_I64    x -> fprintf ppf "UVALUE_I64(%s)" (Int64.to_string (Z.to_int64 (DynamicValues.Int64.unsigned x)))
  | UVALUE_Double x -> fprintf ppf "UVALUE_Double(%s)" (string_of_float_full (camlfloat_of_coqfloat x))
  | UVALUE_Float  x -> fprintf ppf "UVALUE_Float(%s)"  (string_of_float_full (camlfloat_of_coqfloat32 x))
  | UVALUE_Poison   -> fprintf ppf "UVALUE_Poison"
  | UVALUE_None     -> fprintf ppf "UVALUE_None"
  | UVALUE_Undef _  -> fprintf ppf "UVALUE_Undef"
  | UVALUE_Struct        l -> fprintf ppf "UVALUE_Struct(%a)"        (pp_print_list ~pp_sep:pp_comma_space pp_uvalue) l
  | UVALUE_Packed_struct l -> fprintf ppf "UVALUE_Packet_struct(%a)" (pp_print_list ~pp_sep:pp_comma_space pp_uvalue) l
  | UVALUE_Array         l -> fprintf ppf "UVALUE_Array(%a)"         (pp_print_list ~pp_sep:pp_comma_space pp_uvalue) l
  | UVALUE_Vector        l -> fprintf ppf "UVALUE_Vector(%a)"        (pp_print_list ~pp_sep:pp_comma_space pp_uvalue) l
  | _ -> fprintf ppf "todo"

let debug_flag = ref false

(** Print a debug message to stdout if the `debug_flag` is enabled.

    This is used to implement `debugE` events.
*)
let debug (msg:string) =
  if !debug_flag then
    Printf.printf "DEBUG: %s\n%!" msg

(** The `step` function walks through an itree and handles some
    remaining events.

    In particular, `step` handles `debugE`, `failE`, and
    `ExternalCallE` events, which are not handled by the
    TopLevel.interpreter function extracted from Coq.

    Calling `step` could either loop forever, return an error,
    or return the uvalue result returned from the itree.
 *)
let rec step (m : ('a coq_L4, memory_stack * ((local_env * lstack) * (global_env * DV.uvalue))) itree) : (DV.uvalue, string) result =
  let open ITreeDefinition in
  match observe m with
  (* Internal steps compute as nothing *)
  | TauF x -> step x

  (* SAZ: Could inspect the memory or stack here too. *)
  (* We finished the computation *)
  | RetF (_,(_,(_,v))) -> Ok v

  (* The ExternalCallE effect *)
  | VisF (Sum.Coq_inl1 (ExternalCall(_, _, _)), _) ->
     Error "Uninterpreted Call"

  (* The debugE effect *)
  | VisF (Sum.Coq_inr1 (Sum.Coq_inl1 msg), k) ->
     (debug (Camlcoq.camlstring_of_coqstring msg);
      step (k (Obj.magic DV.UVALUE_None)))

  (* The failE effect is a failure *)
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 _), _) ->
     Error "Failure effect"

  (* The UndefinedBehaviourE effect is a failure *)
  (* | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 f)), _) -> *)
    (* Error (Camlcoq.camlstring_of_coqstring f) *)

  (* The only visible effects from LLVMIO that should propagate to the interpreter are:
     - Call to external functions
     - Debug
  *)

      (* | Call(_, f, _) ->
       *   (Printf.printf "UNINTERPRETED EXTERNAL CALL: %s - returning 0l to the caller\n"
       *      (Camlcoq.camlstring_of_coqstring f));
       *   step (k (Obj.magic (DV.DVALUE_I64 DynamicValues.Int64.zero))) *)


(** Interpret an LLVM program, returning a result that contains either the
    uvalue result returned by the LLVM program, or an error message.

    Note: programs consist of a non-empty list of blocks, represented by a
    tuple of a single block, and a possibly empty list of blocks.
 *)
let interpret (prog:(LLVMAst.typ, (LLVMAst.typ LLVMAst.block * (LLVMAst.typ LLVMAst.block) list)) LLVMAst.toplevel_entity list) : (DV.uvalue, string) result =
  step (TopLevel.interpreter prog)
