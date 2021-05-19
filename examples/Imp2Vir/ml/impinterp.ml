match Imp2Cvir.fact_ir with
| None -> print_string "compile error"
| Some ir -> (
  match Interpreter.interpret [ir] with
  | Ok v -> Interpreter.pp_uvalue Format.std_formatter v
  | Error e -> print_string ("interpreter error: " ^ e)
)
