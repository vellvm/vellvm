module LL = LLVMAst
open Handlers.LLVMEvents
open QCheck
module Z = Camlcoq.Z
module G = QCheck.Gen

let small_gen =
  let open G in
  G.int_range (-10000) 10000

let i8gen =
  let open G in
  G.int_range (-128) 127

let g_const : 'a. 'a -> 'a G.t = fun v _rs -> v

let g_i1 = G.map
             (fun v ->
               DV.UVALUE_I1 (if v then Z.one else Z.zero) ) G.bool
let g_si8 = G.map
                ( fun v -> DV.UVALUE_I8 (Z.of_sint v)) small_gen

let g_si32 = G.map
                 (fun v -> DV.UVALUE_I32 (Z.of_sint v)) small_gen

let g_si64 = G.map (fun v -> DV.UVALUE_I64 (Z.of_sint v)) small_gen

let rec gen_uvalue : LL.typ -> DV.uvalue G.t = function
  | LL.TYPE_I i ->
     begin match Camlcoq.N.to_int i with
     | 1 -> g_i1 | 8 -> g_si8 | 16 | 32 -> g_si32 | 64 -> g_si64
     | _ -> failwith "generating integer values of this type is not implemented"
     end
  | LL.TYPE_Void -> g_const DV.UVALUE_None
  | LL.TYPE_Vector (sz, ty) ->
     print_endline "generating vector value";
     let open G in
     let gen_t = gen_uvalue ty in
     let list_ts = G.list_size (g_const (sz |> Camlcoq.N.to_int32 |> Int32.to_int)) gen_t in
     list_ts >>= (fun l -> G.return @@ DV.UVALUE_Vector l)
  | LL.TYPE_Array (sz, ty) ->  
     let open G in
     let gen_t = gen_uvalue ty in
     let list_ts = G.list_size (g_const (sz |> Camlcoq.N.to_int32 |> Int32.to_int)) gen_t in
     list_ts >>= (fun l -> G.return @@ DV.UVALUE_Vector l)
  | _ -> failwith "generating values of this type is not implemented"


let gen_args : LL.typ list -> (DV.uvalue) list G.t = fun ts -> ts |> List.map (fun t -> gen_uvalue t) |> G.flatten_l 

let generate_args : LL.typ list -> (LL.typ * DV.uvalue) list = fun t_args ->
  let vals = G.generate1 (gen_args t_args) in
  List.combine t_args vals

let generate_n_args : int -> LL.typ list -> (LL.typ * DV.uvalue) list list = fun n t_args ->
  let vals = G.generate ~n:n (gen_args t_args) in
  List.map (List.combine t_args) vals
