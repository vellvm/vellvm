
type histogram = (string, int) Hashtbl.t

let record (tbl:histogram) (str:string) : unit =
  begin match Hashtbl.find_opt tbl str with
  | None -> Hashtbl.add tbl str 1
  | Some n -> Hashtbl.replace tbl str (n+1)
  end

let to_string (tbl:histogram) : string =
  (Hashtbl.fold
     (fun key freq acc ->
        let line = Printf.sprintf "%s, %d" key freq in
        line::acc) tbl [])
  |>
  String.concat "\n"

