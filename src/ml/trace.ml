open Log
open Denotation
open ShowAST

let output_channel = ref stdout

let print_log () : unit =
  Printf.printf "%s" (Log.dstring_of_log_stream !Log.log |> DList.coq_DString_to_string |> Camlcoq.camlstring_of_coqstring)




  
