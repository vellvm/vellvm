open Interpreter
open Assertion
open Map
open Driver
open Base

module DV = InterpretationStack.InterpreterStackBigIntptr.LP.Events.DV

module type SRCTGTRESULT = sig
  type error_side = Src | Tgt

  (* type src_tgt_flag = | STEQ_FLAG | STOK_FLAG | STUB_FLAG | STUC_FLAG |
     STOOM_FLAG | STF_FLAG [@@deriving ord] *)

  type src_tgt_result =
    | STOk : string * src_tgt_mode -> src_tgt_result
    | STErr : string * src_tgt_mode * string -> src_tgt_result
    | STUB : string * error_side * string -> src_tgt_result
    | STUC : string * error_side * string -> src_tgt_result
    | STOOM : string * error_side * string -> src_tgt_result
    | STF : string * error_side * string -> src_tgt_result
  [@@deriving ord]
  (* | SrcTgtEq : string -> src_tgt_result | SrcTgtOK : string * src_tgt_mode
     * DV.dvalue * DV.dvalue -> src_tgt_result | SrcOrTgtError : string *
     Interpreter.exit_condition * error_side -> src_tgt_result *)

  type log = (int * src_tgt_result list) * (int * src_tgt_result list)

  val show_error_side : error_side -> string

  val sig_eq : src_tgt_result -> src_tgt_result -> bool

  val check_bool :
    string -> src_tgt_mode -> DV.dvalue -> DV.dvalue -> src_tgt_result

  val check_error :
    string -> Interpreter.exit_condition -> error_side -> src_tgt_result

  val insert : log -> src_tgt_result -> log

  val delete : log -> src_tgt_result -> string -> src_tgt_result option * log

  val empty : log

  val get_length : log -> int

  val get_type_length : log -> src_tgt_result -> int

  val show_src_tgt_result : src_tgt_result -> string

  val dump_log_to_pair : log -> string * string
end

module SRCTGTRESULT : SRCTGTRESULT = struct
  type error_side = Src | Tgt

  (* type src_tgt_flag = | STEQ_FLAG | STOK_FLAG | STUB_FLAG | STUC_FLAG |
     STOOM_FLAG | STF_FLAG [@@deriving ord] *)

  type src_tgt_result =
    | STOk : string * src_tgt_mode -> src_tgt_result
    | STErr : string * src_tgt_mode * string -> src_tgt_result
    | STUB : string * error_side * string -> src_tgt_result
    | STUC : string * error_side * string -> src_tgt_result
    | STOOM : string * error_side * string -> src_tgt_result
    | STF : string * error_side * string -> src_tgt_result
  (* | SrcTgtEq : string -> src_tgt_result | SrcTgtOK : string * src_tgt_mode
     * DV.dvalue * DV.dvalue -> src_tgt_result | SrcOrTgtError : string *
     Interpreter.exit_condition * error_side -> src_tgt_result *)

  type log = (int * src_tgt_result list) * (int * src_tgt_result list)

  let show_error_side : error_side -> string = function
    | Src -> "src"
    | Tgt -> "tgt"

  let sig_eq (res1 : src_tgt_result) (res2 : src_tgt_result) : bool =
    match (res1, res2) with
    | STOk _, STOk _
     |STErr _, STErr _
     |STUB _, STUB _
     |STUC _, STUC _
     |STOOM _, STOOM _
     |STF _, STF _ ->
        true
    | _, _ -> false

  let compare_tgt_for_poison filename dvsrc dvtgt : src_tgt_result =
    let mode = TargetMorePoisonous in
    match dvtgt with
    | DV.DVALUE_Poison _ -> (
      match dvsrc with
      | DV.DVALUE_Poison _ ->
          STErr
            ( filename
            , mode
            , "TargetMorePoisonous: expected src to be non-poison value, \
               but got poison" )
      | _ -> STOk (filename, mode) )
    | _ ->
        let error_msg =
          Printf.sprintf
            "TargetMorePoisonous: expected tgt to be poison but got %s"
            (string_of_dvalue dvtgt)
        in
        STErr (filename, mode, error_msg)

  let check_bool (filename : string) (mode : src_tgt_mode)
      (dvsrc : DV.dvalue) (dvtgt : DV.dvalue) : src_tgt_result =
    match mode with
    | NormalEquality ->
        if DV.dvalue_eqb dvsrc dvtgt = true then STOk (filename, mode)
        else
          let errorMsg =
            Printf.sprintf
              "dvalue comparison for %s failed: \ngot:\n\t%s\nand:\n\t%s"
              "equality" (string_of_dvalue dvsrc) (string_of_dvalue dvtgt)
          in
          STErr (filename, mode, errorMsg)
    | ValueMismatch ->
        if DV.dvalue_eqb dvsrc dvtgt = false then STOk (filename, mode)
        else
          let errorMsg =
            Printf.sprintf
              "dvalue comparison for %s failed: \ngot:\n\t%s\nand:\n\t%s"
              "inequality" (string_of_dvalue dvsrc) (string_of_dvalue dvtgt)
          in
          STErr (filename, mode, errorMsg)
    | TargetMorePoisonous -> compare_tgt_for_poison filename dvsrc dvtgt
    | TargetMoreUndefined -> failwith "Unimplemented"
    | SourceMoreDefined -> failwith "Unimplemented"
    | MismatchInMemory -> failwith "Unimplemented"

  let check_error (filename : string) (e : Interpreter.exit_condition)
      (err_side : error_side) : src_tgt_result =
    match e with
    | UninterpretedCall s -> STUC (filename, err_side, s)
    | OutOfMemory s -> STOOM (filename, err_side, s)
    | UndefinedBehavior s -> STUB (filename, err_side, s)
    | Failed s -> STF (filename, err_side, s)

  let ok_list (l : log) : src_tgt_result list = snd @@ fst l

  let err_list (l : log) : src_tgt_result list = snd @@ snd l

  let nok_list (l : log) : int = fst @@ fst l

  let nerr_list (l : log) : int = fst @@ snd l

  let insert (l : log) (res : src_tgt_result) : log =
    match res with
    | STOk _ ->
        ((nok_list l + 1, res :: ok_list l), (nerr_list l, err_list l))
    | _ -> ((nok_list l, ok_list l), (nerr_list l, res :: err_list l))

  let delete = failwith "not implemented"

  let empty = ((0, []), (0, []))

  let get_length (l : log) : int = nok_list l + nerr_list l

  let get_type_length (l : log) (key : src_tgt_result) : int =
    let eq_fun = sig_eq key in
    match key with
    | STOk _ -> nok_list l
    | STErr _ | STUB _ | STUC _ | STOOM _ | STF _ ->
        List.fold_right
          (fun x acc -> if eq_fun x then acc + 1 else acc)
          (err_list l) 0

  let to_string_wo_sig (res : src_tgt_result) : string =
    match res with
    | STOk (str, mode) ->
        Printf.sprintf "%s,\t%s" str (Assertion.show_src_tgt_mode mode)
    | STErr (str, mode, error_msg) ->
        Printf.sprintf "%s,\t%s,\t%s" str
          (Assertion.show_src_tgt_mode mode)
          error_msg
    | STUB (str, err_side, error_msg) ->
        Printf.sprintf "%s,\t%s,\t%s" str
          (show_error_side err_side)
          error_msg
    | STUC (str, err_side, error_msg) ->
        Printf.sprintf "%s,\t%s,\t%s" str
          (show_error_side err_side)
          error_msg
    | STOOM (str, err_side, error_msg) ->
        Printf.sprintf "%s,\t%s,\t%s" str
          (show_error_side err_side)
          error_msg
    | STF (str, err_side, error_msg) ->
        Printf.sprintf "%s,\t%s,\t%s" str
          (show_error_side err_side)
          error_msg

  let show_src_tgt_result (res : src_tgt_result) : string =
    let inner_string = to_string_wo_sig res in
    let signature =
      match res with
      | STOk _ -> "STOk"
      | STErr _ -> "STEr"
      | STUB _ -> "STUB"
      | STUC _ -> "STUC"
      | STOOM _ -> "STOM"
      | STF _ -> "STFa"
    in
    Printf.sprintf "%s,\t%s" signature inner_string

  let dump_log_to_pair (l : log) : string * string =
    let ok_string =
      List.fold_right
        (fun x acc -> show_src_tgt_result x ^ "\n" ^ acc)
        (ok_list l) ""
    in
    let err_string =
      List.fold_right
        (fun x acc -> show_src_tgt_result x ^ "\n" ^ acc)
        (err_list l) ""
    in
    (ok_string, err_string)

  let dump (l : log) (file_addr : string option) : unit =
    let ok_string, err_string = dump_log_to_pair l in
    match file_addr with
    | None -> ()
    | Some addr ->
        IO.write_file addr
          (Printf.sprintf "---ERROR---\n%s\n\n---ACCEPT---\n%s" err_string
             ok_string )
end
