open LLVMAst
open DynamicTypes
open ShowAST
open DList

type log_entry =
  | Instr of instr_id * dtyp instr
  | Phi_node of dtyp phi
  | Ret of dtyp terminator

type log_stream = log_entry list

let log : log_stream ref = ref []

let ( >@ ) x y = y @ x
let ( >:: ) x y = y :: x

let output_channel = ref stdout

let dstring_of_log_entry (le : log_entry) : DList.coq_DString =
  match le with
  | Instr (uid, ins) ->
    ShowAST.dshow_instr_id ShowAST.dshow_dtyp (uid, ins)
  | Phi_node phi ->
    ShowAST.dshowPhi ShowAST.dshow_dtyp phi
  | Ret term ->
    ShowAST.dshowTerminator ShowAST.dshow_dtyp term

let write_entry (le : log_entry) : unit =
    log := !log >:: le
