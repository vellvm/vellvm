open LLVMAst
open DynamicTypes
open ShowAST
open DList

type log_entry =
  | Instr of instr_id * dtyp instr
  | Phi_node of local_id * dtyp phi
  | Ret of dtyp terminator

type log_stream = log_entry list

let log : log_stream ref = ref []

let ( >@ ) x y = y @ x
let ( >:: ) x y = y :: x

let output_channel = ref stdout

let dshow_log_entry (le : log_entry) : DList.coq_DString =
  match le with
  | Instr (uid, ins) ->
    ShowAST.dshow_instr_id ShowAST.dshow_dtyp (uid, ins)
  | Phi_node (uid, phi) ->
    ShowAST.dshowPhi ShowAST.dshow_dtyp phi
  | Ret term ->
    ShowAST.dshowTerminator ShowAST.dshow_dtyp term

let dstring_of_log_stream (log_stream : log_stream) : DList.coq_DString =
  List.rev log_stream |> List.map dshow_log_entry |> ShowAST.dintersperse (string_to_DString ('\n' :: []))

let clear_log : unit = log := []

let write_log_entry (le : log_entry) : unit =
  log := !log >:: le

let get_log_stream () : log_stream =
  List.rev !log
