open Log
open Denotation
open ShowAST
open LLVMAst
open OrderedType

(** Modules **)
module type OrdPrintT =
  sig
    type t
    val compare : t -> t -> int
    val to_string : t -> string
  end

module type PrintT =
sig
  type t
  val to_string : t -> string
end

module type SetS =
sig
  include Set.S

  val of_list : elt list -> t
  val to_string : t -> string
  val string_of_elt : elt -> string
  val printer : Format.formatter -> t -> unit
end

module type MapS =
sig
  include Map.S
  val update : ('a -> 'a) -> key -> 'a t -> 'a t
  val find_or : 'a -> 'a t -> key -> 'a
  val update_or : 'a -> ('a -> 'a) -> key -> 'a t -> 'a t
  val diff_keys : ('a -> 'a -> int) -> 'a t -> 'a t -> key list
  val to_string : (key -> 'a -> string) -> 'a t -> string
  val printer : (key -> 'a -> string) -> Format.formatter -> 'a t -> unit
end

module RawidOrdPrint : OrdPrintT = struct
  type t = AstLib.RawIDOrd.t

  let compare (t1 : t) (t2 : t) =
    match AstLib.RawIDOrd.compare t1 t2 with
    | LT -> -1
    | EQ -> 0
    | GT -> 1

  let to_string r =
    ShowAST.dshow_raw_id r |> DList.coq_DString_to_string |> Camlcoq.camlstring_of_coqstring
end

module MakeSet (Ord : OrdPrintT) : SetS with type elt = Ord.t =
struct
  include Set.Make(Ord)

  let of_list = List.fold_left (fun s e -> add e s) empty

  let to_string t =
    let s = elements t
            |> List.map Ord.to_string
            |> String.concat ", "
    in
    Printf.sprintf "{%s}" s

  let string_of_elt = Ord.to_string

  let printer f t = Format.pp_print_string f (to_string t)
end

module MakeMap (Ord : OrdPrintT) : MapS with type key = Ord.t =
struct
  include Map.Make (Ord)

  let update f k m =
    add k (f @@ find k m) m

  let find_or d m k =
    try find k m with Not_found -> d

  let diff_keys cmp_v m n =
    let module S = MakeSet(Ord) in
    let has_binding_or_add m k v l =
      try if cmp_v v @@ find k m == 0 then l else S.add k l
      with Not_found -> S.add k l
    in
    S.empty
    |> fold (has_binding_or_add n) m
    |> fold (has_binding_or_add m) n
    |> S.elements

  let update_or d f k m =
    add k (f @@ find_or d m k) m

  let to_string val_str t =
    let s = bindings t
              |> List.map (fun (k,v) -> Ord.to_string k ^ "=" ^ val_str k v)
              |> String.concat ", "
    in
    Printf.sprintf "{%s}" s

  let printer val_str f t = Format.pp_print_string f (to_string val_str t)
end

module RawidM = MakeMap(RawidOrdPrint)

(** Substitution **)


  
(** Printing trace **)
let output_channel = ref stdout

let print_log () : unit =
  Printf.printf "%s" (Log.dstring_of_log_stream !Log.log |> DList.coq_DString_to_string |> Camlcoq.camlstring_of_coqstring)




  
