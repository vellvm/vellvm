open LLVMAst
open DynamicTypes
open ShowAST
open DList
open CFG

type 'a log_entry =
  | Instr of instr_id * 'a instr
  | Phi_node of local_id * 'a phi * block_id
  | Term of 'a terminator
  | F_args of (function_id) * local_id list

type 'a log_stream = 'a log_entry list

let log_ref : dtyp log_stream ref = ref []

let ( >@ ) x y = y @ x
let ( >:: ) x y = y :: x

let dshow_log_entry (le : 'a log_entry) ~(f : 'a -> DList.coq_DString) : DList.coq_DString =
  match le with
  | Instr (uid, ins) ->
    ShowAST.dshow_instr_id f (uid, ins)
  | Phi_node (uid, phi, bid) ->
    DList.coq_DList_join
      [
      ShowAST.dshow_raw_id bid;
      ShowAST.dshow_phi_id f (uid, phi)
    ]
  | Term term ->
    ShowAST.dshowTerminator f term 
  | F_args (def, _) ->
    (* List.fold_right (fun x acc -> coq_DList_append (ShowAST.dshowRawId x) acc) args (DList.coq_EmptyDString) *)
    ShowAST.dshowRawId def

let dstring_of_log_stream (log_stream : 'a log_stream) ~(f : 'a -> DList.coq_DString) : DList.coq_DString =
  List.rev log_stream |> List.map (dshow_log_entry ~f) |> ShowAST.dintersperse (string_to_DString ('\n' :: []))

let clear_log : unit = log_ref := []

let write_log_entry (le : dtyp log_entry) : unit =
  log_ref := !log_ref >:: le

let get_log_stream () : dtyp log_stream =
  List.rev !log_ref
