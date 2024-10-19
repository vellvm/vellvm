open Base
open Log
open LLVMAst
open OrderedType
open DynamicTypes
open CFG
open TypToDtyp

(** Printing Helper Function **)
let print_tblk tblk : unit =
  Printf.printf "%s" (ShowAST.dshowBlock ShowAST.dshowTyp (tblk) |> DList.coq_DString_to_string |> Camlcoq.camlstring_of_coqstring)

let print_log_entry (le : log_entry) =
  Printf.printf "%s\n%!" (Log.dshow_log_entry le |> DList.coq_DString_to_string |> Camlcoq.camlstring_of_coqstring)

let print_log () : unit =
  Printf.printf "%s\n" (Log.dstring_of_log_stream !Log.log |> DList.coq_DString_to_string |> Camlcoq.camlstring_of_coqstring)
    
let get_mcfg ll_ast =
  (mcfg_of_tle (TopLevel.TopLevelBigIntptr.link TopLevel.TopLevelBigIntptr.coq_PREDEFINED_FUNCTIONS ll_ast))

let camlstring_of_dstring (dstr : DList.coq_DString) =
  dstr |> DList.coq_DString_to_string |> Camlcoq.camlstring_of_coqstring

(** dtyp -> typ mcfg helper function **)
type tlog_entry =
  | TInstr of instr_id * typ instr
  | TPhi of local_id * typ phi * block_id
  | TRet of typ texp

type tlog_stream = tlog_entry list

let dshow_tlog_entry (le : tlog_entry) : DList.coq_DString =
  match le with
  | TInstr (uid, ins) ->
    ShowAST.dshow_instr_id ShowAST.dshowTyp (uid, ins)
  | TPhi (uid, phi, bid) ->
    DList.coq_DList_join
      [
      ShowAST.dshow_raw_id bid;
      ShowAST.dshow_phi_id ShowAST.dshowTyp (uid, phi)
    ]
  | TRet term ->
    ShowAST.dshowTerminator ShowAST.dshowTyp (TERM_Ret term)

let dstring_of_tlog_stream (tlog_stream : tlog_stream) : DList.coq_DString =
  List.map dshow_tlog_entry tlog_stream |> ShowAST.dintersperse (DList.string_to_DString ('\n' :: []))

let print_tlog (code : tlog_stream) : unit =
  Printf.printf "%s\n" (dstring_of_tlog_stream code |> DList.coq_DString_to_string |> Camlcoq.camlstring_of_coqstring)

(* TODO: This seems to be slow, can optimize by pre-storing the data structure *)
let get_instr_from_def
    ~(f_def : (LLVMAst.typ, LLVMAst.typ cfg) definition)
    (id : instr_id) : (instr_id * typ instr) option =
  let blocks = f_def.df_instrs.blks in
  let codes = List.flatten (List.map (fun x -> x.blk_code) blocks) in
  List.find_opt (fun x -> AstLib.InstrIDDec.eq_dec (fst x) id) codes

let get_phi_from_def
    ~(f_def : (LLVMAst.typ, LLVMAst.typ cfg) definition)
    (id : local_id) : (local_id * typ phi) option =
  let blocks = f_def.df_instrs.blks in
  let phis = List.flatten (List.map (fun x -> x.blk_phis) blocks) in
  List.find_opt (fun x -> AstLib.RawIDOrd.eq_dec (fst x) id) phis

(* TODO: This is a little bit hand-waiving because I'm using OCaml equality
   Maybe need to define own equality that equates both terms / expressions
*)
let rec typ_eq (t1 : LLVMAst.typ) (t2 : LLVMAst.typ) =
  match t1, t2 with
  | TYPE_I i1, TYPE_I i2 ->
    Camlcoq.N.eq i1 i2
  | TYPE_Pointer t1, TYPE_Pointer t2 ->
    typ_eq t1 t2
  | TYPE_IPTR, TYPE_IPTR 
  | TYPE_Void, TYPE_Void
  | TYPE_Half, TYPE_Half 
  | TYPE_Float, TYPE_Float 
  | TYPE_Double, TYPE_Double 
  | TYPE_X86_fp80, TYPE_X86_fp80
  | TYPE_Fp128, TYPE_Fp128
  | TYPE_Ppc_fp128, TYPE_Ppc_fp128
  | TYPE_Metadata, TYPE_Metadata
  | TYPE_X86_mmx, TYPE_X86_mmx
  | TYPE_Opaque, TYPE_Opaque -> 
    true
  | TYPE_Array (n1, t1'), TYPE_Array (n2, t2') ->
    Camlcoq.N.eq n1 n2 && typ_eq t1' t2'
  | TYPE_Function (t1, targs1, b1), TYPE_Function (t2, targs2, b2) ->
    typ_eq t1 t2 && List.equal typ_eq targs1 targs2 && b1 == b2
  | TYPE_Struct targs1, TYPE_Struct targs2 ->
    List.equal typ_eq targs1 targs2
  | TYPE_Packed_struct targs1, TYPE_Packed_struct targs2 ->
    List.equal typ_eq targs1 targs2
  | TYPE_Vector (n1, t1), TYPE_Vector (n2, t2) ->
    Camlcoq.N.eq n1 n2 && typ_eq t1 t2
  | TYPE_Identified id1, TYPE_Identified id2 ->
    AstLib.eq_dec_ident id1 id2
  | _ ->  false

let rec exp_eq ~(f : 'a -> 'a -> bool) (e1 : 'a exp) (e2 : 'a exp) : bool =
  match e1, e2 with
  | EXP_Ident ident1, EXP_Ident ident2 ->
    AstLib.eq_dec_ident ident1 ident2
  | EXP_Integer i1, EXP_Integer i2 ->
    Camlcoq.Z.eq i1 i2
  | EXP_Float float1, EXP_Float float2 ->
    Floats.Float32.eq_dec float1 float2
  | EXP_Double float1, EXP_Double float2 ->
    Floats.Float.eq_dec float1 float2
  | EXP_Hex float1, EXP_Hex float2 ->
    Floats.Float.eq_dec float1 float2 
  | EXP_Bool b1, EXP_Bool b2 ->
    Bool.eqb b1 b2
  | EXP_Null, EXP_Null ->
    true
  | EXP_Zero_initializer, EXP_Zero_initializer ->
    true
  | EXP_Cstring tes1, EXP_Cstring tes2 ->
    List.equal (fun (t1, e1) (t2, e2) -> f t1 t2 && exp_eq ~f e1 e2) tes1 tes2
  | EXP_Undef, EXP_Undef ->
    true
  | EXP_Poison, EXP_Poison ->
    true
  | EXP_Struct tes1, EXP_Struct tes2 -> 
    List.equal (fun (t1, e1) (t2, e2) -> f t1 t2 && exp_eq ~f e1 e2) tes1 tes2
  | EXP_Packed_struct tes1, EXP_Packed_struct tes2 -> 
    List.equal (fun (t1, e1) (t2, e2) -> f t1 t2 && exp_eq ~f e1 e2) tes1 tes2
  | EXP_Array tes1, EXP_Array tes2 ->
    List.equal (fun (t1, e1) (t2, e2) -> f t1 t2 && exp_eq ~f e1 e2) tes1 tes2
  | EXP_Vector tes1, EXP_Vector tes2 ->
    List.equal (fun (t1, e1) (t2, e2) -> f t1 t2 && exp_eq ~f e1 e2) tes1 tes2
  (* OP part is never used *)
  | OP_IBinop (ibinop1, t1, e11, e12), OP_IBinop (ibinop2, t2, e21, e22) ->
    ibinop1 == ibinop2 && f t1 t2 && exp_eq ~f e11 e21 && exp_eq ~f e12 e22
  | OP_ICmp (icmp1, t1, e11, e12), OP_ICmp (icmp2, t2, e21, e22) -> 
    icmp1 == icmp2 && f t1 t2 && exp_eq ~f e11 e21 && exp_eq ~f e12 e22
  | OP_FBinop (fbinop1, _, t1, e11, e12), OP_FBinop (fbinop2, _, t2, e21, e22) ->
    fbinop1 == fbinop2 && f t1 t2 && exp_eq ~f e11 e21 && exp_eq ~f e12 e22
  | OP_FCmp (fcmp1, t1, e11, e12), OP_FCmp (fcmp2, t2, e21, e22) -> 
    fcmp1 == fcmp2 && f t1 t2 && exp_eq ~f e11 e21 && exp_eq ~f e12 e22
  | OP_Conversion (conv1, t11, e1, t12), OP_Conversion (conv2, t21, e2, t22) ->
    conv1 == conv2 && f t11 t21 && exp_eq ~f e1 e2 && f t12 t22
  | OP_GetElementPtr (t11, (t12, e12), tes1), OP_GetElementPtr (t21, (t22, e22), tes2) ->
    f t11 t21 && f t12 t22 && exp_eq ~f e12 e22 &&
    List.equal (fun (t1, e1) (t2, e2) -> f t1 t2 && exp_eq ~f e1 e2) tes1 tes2
  | OP_ExtractElement ((t11, e11), (t12, e12)), OP_ExtractElement ((t21, e21), (t22, e22)) ->
    f t11 t21 && f t12 t22 && exp_eq ~f e11 e21 && exp_eq ~f e12 e22
  | OP_InsertElement ((t11, e11), (t12, e12), (t13, e13)) , OP_InsertElement ((t21, e21), (t22, e22), (t23, e23)) ->
    f t11 t21 && f t12 t22 && f t13 t23 && exp_eq ~f e11 e21 && exp_eq ~f e12 e22 && exp_eq ~f e13 e23
  | OP_ShuffleVector ((t11, e11), (t12, e12), (t13, e13)) , OP_ShuffleVector ((t21, e21), (t22, e22), (t23, e23)) ->
    f t11 t21 && f t12 t22 && f t13 t23 && exp_eq ~f e11 e21 && exp_eq ~f e12 e22 && exp_eq ~f e13 e23
  | OP_ExtractValue _, OP_ExtractValue _ -> failwith "exp_eq: OP_ExtractValue"
  | OP_InsertValue _, OP_InsertValue _ -> failwith "exp_eq: OP_InsertValue"
  | OP_Select ((t11, e11), (t12, e12), (t13, e13)) , OP_Select ((t21, e21), (t22, e22), (t23, e23)) ->
    f t11 t21 && f t12 t22 && f t13 t23 && exp_eq ~f e11 e21 && exp_eq ~f e12 e22 && exp_eq ~f e13 e23
  | OP_Freeze (t1, e1), OP_Freeze (t2, e2) ->
    f t1 t2 && exp_eq ~f e1 e2
  | _ -> false                   

let texp_eq ~(f : 'a -> 'a -> bool) (texp1 : 'a * 'a exp) (texp2 : 'a * 'a exp) : bool =
  let (t1, exp1) = texp1 in
  let (t2, exp2) = texp2 in
  f t1 t2 && exp_eq ~f exp1 exp2

let term_eq ~(f : 'a -> 'a -> bool) (term1 : 'a terminator) (term2 : 'a terminator) : bool =
  match term1, term2 with
  | TERM_Ret (t1, exp1), TERM_Ret (t2, exp2) ->
    f t1 t2 && exp_eq ~f exp1 exp2
  | TERM_Ret_void, TERM_Ret_void ->
    true
  | TERM_Br (texp1, b11, b12), TERM_Br (texp2, b21, b22) ->
    texp_eq ~f texp1 texp2 && AstLib.RawIDOrd.eq_dec b11 b21 && AstLib.RawIDOrd.eq_dec b12 b22
  | TERM_Br_1 b1, TERM_Br_1 b2 ->
    AstLib.RawIDOrd.eq_dec b1 b2
  | TERM_Switch _, TERM_Switch _ -> failwith "term_eq: TERM_Switch"
  | TERM_IndirectBr (texp1, bs1), TERM_IndirectBr (texp2, bs2) ->
    texp_eq ~f texp1 texp2 && List.equal AstLib.RawIDOrd.eq_dec bs1 bs2
  | TERM_Resume texp1, TERM_Resume texp2 ->
    texp_eq ~f texp1 texp2
  | TERM_Invoke _, TERM_Invoke _ -> failwith "term_eq: TERM_Invoke"
  | TERM_Unreachable, TERM_Unreachable -> failwith "term_eq : TERM_Unreachable"
  | _ -> false

let get_term_from_def
    ~(f_def : (typ, typ cfg) definition)
    ~(mcfg : typ mcfg)
    (term : dtyp terminator): typ terminator option =
  let blocks = f_def.df_instrs.blks in
  let terms = List.map (fun x -> x.blk_term) blocks in
  let convert_dtyp_term : typ terminator -> dtyp terminator = fun (x : typ terminator) -> convert_typ (Obj.magic coq_ConvertTyp_term) mcfg.m_type_defs (Obj.magic x) in
  let find_aux : typ terminator -> bool = fun (x : typ terminator) -> term_eq ~f:dtyp_eqb (convert_dtyp_term x) term in
  List.find_opt find_aux terms

let get_f_def_from_mcfg
    (f_exp : LLVMAst.typ LLVMAst.exp)
    ~(mcfg : typ mcfg) : (LLVMAst.typ, LLVMAst.typ cfg) definition option =
  let defs = mcfg.m_definitions in
  let find_aux  = fun x -> exp_eq ~f:typ_eq (EXP_Ident (ID_Global x.df_prototype.dc_name)) f_exp in
  List.find_opt find_aux defs

(** Modules **)

type raw_id = LLVMAst.raw_id

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
  val of_list : (key * 'a) list -> 'a t
end

module RawidOrdPrint : OrdPrintT with type t = raw_id = struct
  type t = raw_id

  let compare (t1 : t) (t2 : t) =
    match t1, t2 with
    | Name cs1, Name cs2 ->
      let s1 = Camlcoq.camlstring_of_coqstring cs1 in
      let s2 = Camlcoq.camlstring_of_coqstring cs2 in
      String.compare s1 s2
    | _, _ -> 
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

  let of_list l = List.fold_left (fun acc (key, value) -> add key value acc) empty l
end

module RawidM = MakeMap(RawidOrdPrint)

(** Substitution **)
(* The goal of these functions is to turn the file into an execution trace.
   ml/extracted/log.ml file has already turned the interpretation trace into logs
   This file will need to normalize the trace to make it well-formed
*)

type ctx = typ exp RawidM.t
type 'a stack = 'a list

let push_stack ~(hd : 'a) (stack : 'a stack) : 'a stack = hd :: stack

let pop_stack (stack : 'a stack) : (('a * 'a stack) , string) result =
  match stack with
  | [] -> Error "Trace: fail to pop from stack"
  | hd::tl -> Ok (hd, tl)

let peek_stack (stack : 'a stack) : ('a, string) result =
  match stack with
  | [] -> Error "Trace: fail to pop from stack"
  | hd::_ -> Ok (hd)

let update_stack_hd (stack : 'a stack) ~(f : 'a -> 'a) : 'a stack =
  match stack with
  | [] -> []
  | hd::tl -> f hd::tl

let replace_stack_hd (stack : 'a stack) ~(hd : 'a) : 'a stack =
  update_stack_hd stack ~f:(fun _ -> hd)

type code = (instr_id * typ instr) list

let gensym : string -> string =
  let c = ref 0 in
  fun (s:string) -> incr c; Printf.sprintf "_temp%s%d%!" s (!c)

let gensym_int : int -> int =
  let c = ref 0 in
  fun (_:int) -> incr c; !c

(* let gensym_raw_id : raw_id -> raw_id = function *)
(*   | Name id -> *)
(*     let id' = Camlcoq.camlstring_of_coqstring id |> gensym |> Camlcoq.coqstring_of_camlstring in *)
(*     Name id' *)
(*   | Anon i -> *)
(*     let i' = Camlcoq.Z.to_int i |> gensym_int |> Camlcoq.Z.of_uint in *)
(*     Anon i' *)
(*   | Raw i -> *)
(*     let i' = Camlcoq.Z.to_int i |> gensym_int |> Camlcoq.Z.of_uint in *)
(*     Raw i' *)

let gensym_raw_id : raw_id -> raw_id =
  let c = ref 0 in
  fun (rid : raw_id) ->
    incr c;
    match rid with
    | Name _ ->
      let id = Printf.sprintf "%d%!" !c |> Camlcoq.coqstring_of_camlstring in
      Name id
    | Anon _ ->
      let i = Camlcoq.Z.of_uint !c in
      Anon i
    | Raw _ ->
      let i = Camlcoq.Z.of_uint !c in
      Raw i

(* Substitution r2 using r1 *)
let subst_raw_id_opt ~(ctx : ctx) (s : raw_id) ~(default : typ exp) =
  match RawidM.find_opt s ctx with
  | Some v -> v
  | None -> default

let subst_ident_opt ~(ctx : ctx) (s : ident) ~(default : typ exp) =
  match s with
  | ID_Global r | ID_Local r -> subst_raw_id_opt ~ctx r ~default

let subst_exp ~(ctx : ctx) (s : typ exp) : typ exp =
  match s with
  | EXP_Ident ident ->
    subst_ident_opt ~ctx ident ~default:s
  | _ -> s

let subst_texp ~(ctx : ctx) (s : typ texp) : typ texp =
  let (t, exp) = s in
  t, subst_exp ~ctx exp

let subst_texps ~(ctx : ctx) (ss : typ texp list) : typ texp list =
  List.map (subst_texp ~ctx) ss

type tblk = typ LLVMAst.block

(* Algorithm is as follows:
   If getting a ret, return by one level and get the previous context
   if getting an instruction, case analysis
      If the instruction is call. save the cfg and go for one level (a recursive call)
   if  getting phi node. need to know where did it came from (bid). Then find the right node and substitute the values into the map
*)
let add_code tblk ~(code : code) : tblk =
  let code' = tblk.blk_code >@ code in
  {blk_id = tblk.blk_id;
   blk_phis = tblk.blk_phis;
   blk_code = code';
   blk_term = tblk.blk_term;
   blk_comments = tblk.blk_comments
  }

let add_term tblk ~(term : typ terminator) : tblk =
  {blk_id = tblk.blk_id;
   blk_phis = tblk.blk_phis;
   blk_code = tblk.blk_code;
   blk_term = term;
   blk_comments = tblk.blk_comments
  }
(* TODO: How to deal with rightmost terminator when it is not well-formed *)

(* TODO: Substitution needed *)
let transform_exp ~(ctx : ctx) (op : typ exp) : typ exp =
  match op with
  | OP_IBinop (ibinop, t, exp1, exp2) ->
    let exp1' = subst_exp ~ctx exp1 in
    let exp2' = subst_exp ~ctx exp2 in
    OP_IBinop (ibinop, t, exp1', exp2')
  | OP_ICmp (icmp, t, exp1, exp2) -> 
    let exp1' = subst_exp ~ctx exp1 in
    let exp2' = subst_exp ~ctx exp2 in
    OP_ICmp (icmp, t, exp1', exp2')
  | OP_FBinop (fbinop, fm, t, exp1, exp2) ->
    let exp1' = subst_exp ~ctx exp1 in
    let exp2' = subst_exp ~ctx exp2 in
    OP_FBinop (fbinop, fm, t, exp1', exp2')
  | OP_FCmp (fcmp, t, exp1, exp2) ->
    let exp1' = subst_exp ~ctx exp1 in
    let exp2' = subst_exp ~ctx exp2 in
    OP_FCmp (fcmp, t, exp1', exp2')
  | OP_Conversion (conv, t1, exp, t2) ->
    let exp' = subst_exp ~ctx exp in
    OP_Conversion (conv, t1, exp', t2)
  | OP_GetElementPtr (t, texp, texps) ->
    let texp' = subst_texp ~ctx texp in
    let texps' = subst_texps ~ctx texps in
    OP_GetElementPtr (t, texp', texps')
  | OP_ExtractElement (texp1, texp2) ->
    let texp1' = subst_texp ~ctx texp1 in
    let texp2' = subst_texp ~ctx texp2 in
    OP_ExtractElement (texp1', texp2')
  | OP_InsertElement (texp1, texp2, texp3) -> 
    let texp1' = subst_texp ~ctx texp1 in
    let texp2' = subst_texp ~ctx texp2 in
    let texp3' = subst_texp ~ctx texp3 in
    OP_InsertElement (texp1', texp2', texp3')
  | OP_ShuffleVector (texp1, texp2, texp3) -> 
    let texp1' = subst_texp ~ctx texp1 in
    let texp2' = subst_texp ~ctx texp2 in
    let texp3' = subst_texp ~ctx texp3 in
    OP_ShuffleVector (texp1', texp2', texp3')
  | OP_ExtractValue (texp, il) -> 
    let texp' = subst_texp ~ctx texp in
    OP_ExtractValue (texp', il)
  | OP_InsertValue (texp1, texp2, il) -> 
    let texp1' = subst_texp ~ctx texp1 in
    let texp2' = subst_texp ~ctx texp2 in
    OP_InsertValue (texp1', texp2', il)
  | OP_Select (texp1, texp2, texp3) -> 
    let texp1' = subst_texp ~ctx texp1 in
    let texp2' = subst_texp ~ctx texp2 in
    let texp3' = subst_texp ~ctx texp3 in
    OP_Select (texp1', texp2', texp3')
  | OP_Freeze texp ->
    let texp' = subst_texp ~ctx texp in
    OP_Freeze texp'
  | EXP_Ident ident ->
    let op' = subst_ident_opt ~ctx ident ~default:op in
    op'
  | EXP_Integer _ | EXP_Float _ | EXP_Double _
  | EXP_Hex _ | EXP_Bool _ | EXP_Null | EXP_Zero_initializer
  | EXP_Cstring _ | EXP_Undef | EXP_Poison | EXP_Struct _
  | EXP_Packed_struct _ | EXP_Array _ | EXP_Vector _ ->
    op

let ctx_unit_to_string ~(k : raw_id) ~(v : typ exp) : string =
  Printf.sprintf "%s->%s%!" (ShowAST.dshow_raw_id k |> DList.coq_DString_to_string |> Camlcoq.camlstring_of_coqstring)
    (ShowAST.dshowExp ShowAST.dshowTyp v |> DList.coq_DString_to_string |> Camlcoq.camlstring_of_coqstring)
  (* Printf.sprintf "%s" (ShowAST.dshow_raw_id k |> DList.coq_DString_to_string |> Camlcoq.camlstring_of_coqstring) *)
  (* Printf.sprintf "%s" "bla" *)

let print_ctx ctx : unit =
  RawidM.iter (fun k v -> Printf.printf "%s; %!" (ctx_unit_to_string ~k ~v)) ctx;
  print_endline ""

let transform_phi ~(ctx : ctx) ~(id : raw_id) (phi : typ phi) ~(bid_from : raw_id) : ctx =
  match phi with
  | Phi (_, args) -> 
    match Util.assoc AstLib.eq_dec_raw_id bid_from args with
    | Some op ->
    (*
       If op is some values -> then need to case analysis on that {tempid / phi}
       If exp is some operations, then assign this id with that operations, and {id / phiid}
 *)
      let exp = transform_exp ~ctx op in
      let ctx' = RawidM.update_or exp (fun _ -> exp) id ctx in
      ctx'
    | None -> failwith (Printf.sprintf "No block match phi node")

let list_to_map l1 l2 =
  List.fold_left (fun acc (key, value) -> RawidM.add key value acc) RawidM.empty @@ List.combine l1 l2

  let is_variadic (def : (typ, typ cfg) definition) = 
    match def.df_prototype.dc_type 
      with TYPE_Function (_, _, is_variadic) -> is_variadic
         | _ -> 
          failwith ("Misuse of is_variadic: called on non-function with id \"" 
                    ^ RawidOrdPrint.to_string def.df_prototype.dc_name ^ "\"")

let transform_definition ~ctx (targs : typ texp list) ~(params : function_id list) : ctx =
  let args = List.map (fun (_, arg) -> subst_exp ~ctx arg) targs in
  (* print_endline "Here are the targs"; *)
  (* List.iter (fun s -> Printf.printf "%s\n" (ShowAST.dshowTExp ShowAST.dshowTyp s |> camlstring_of_dstring)) targs; *)
  (* print_endline "Here are the params:"; *)
  (* List.iter (fun s -> Printf.printf "%s\n" (ShowAST.dshow_raw_id s |> camlstring_of_dstring)) params; *)
  List.combine params args |> RawidM.of_list

let ( let* ) x f = Stdlib.Result.bind x f

type ctx_stack = (ctx * (typ, typ cfg) definition * instr_id) stack

(* let transform_phi_stack ~(ctxs : ctx_stack) ~(id : raw_id) (phi : typ phi) ~(bid_from : raw_id) : ctx_stack = *)
(*   stack_update_hd ~f:(fun (ctx, opt) -> transform_phi ~ctx ~id phi ~bid_from, opt) ctxs *)

let update_stack_ctx (ctxs : ctx_stack) ~(ctx : ctx) =
  update_stack_hd ctxs ~f:(fun (_, f_def, ciid) -> ctx, f_def, ciid)

let rec transform_log
    ~(ctxs : ctx_stack)
    ~(mcfg : typ CFG.mcfg)
    ~(tblk : tblk)
    (logs : log_stream) : (tblk, string) result =
  match logs with
  | [] ->
    Ok tblk
  | log::logs' ->
    let* ((ctx, f_def, ciid), ctxs_tl) = pop_stack ctxs in
    begin match log with
      | Phi_node (pid, _, bid_from) ->
        begin match get_phi_from_def ~f_def pid with
          | Some (_, phi) ->
            let ctx' = transform_phi ~ctx ~id:pid phi ~bid_from in
            let ctxs' = push_stack ctxs_tl ~hd:(ctx', f_def, ciid) in
            transform_log ~ctxs:ctxs' ~mcfg ~tblk logs'
          | None -> Error "normalize_log: cannot find phi"
        end
      | Ret dtexp ->
        begin match get_term_from_def ~f_def ~mcfg (TERM_Ret dtexp) with
          | Some (TERM_Ret texp) ->
            let (t, exp) = subst_texp ~ctx texp in
            (*
               at the highest level and hit return
Return the current transformed log with return added in it *)
            if ctxs_tl = [] then
              Ok (add_term tblk ~term:(TERM_Ret (t, exp)))
              (* Not at the highest level *)
            else
              begin match ciid with
                | IId rid -> 
                  let ctxs' = update_stack_hd ctxs_tl ~f:(fun (ctx, f_def, iid) -> RawidM.add rid exp ctx, f_def, iid) in
                  transform_log ~ctxs:ctxs' ~mcfg ~tblk logs'
                | IVoid _ ->
                  Error "transform_log: Ret match with IVoid"
              end
          | _ ->
            Error "normalize_log: cannot find terminator"
        end
      | Ret_void ->
        if ctxs = [] then
          Ok (add_term tblk ~term:(TERM_Ret_void))
        else
          transform_log ~ctxs:ctxs_tl ~mcfg ~tblk logs'
      | Instr (id, ins) ->
        begin match ins, get_instr_from_def ~f_def id with
          | INSTR_Comment _, Some (_, INSTR_Comment c) ->
            let tblk' = add_code tblk ~code:[(id, INSTR_Comment c)] in
            transform_log ~ctxs ~mcfg ~tblk:tblk' logs
          | INSTR_Op _, Some (_, INSTR_Op exp)->
            let exp' = transform_exp ~ctx exp in
            begin match id with
            | IVoid _ ->
              let tblk' = add_code tblk ~code:[(id, INSTR_Op exp')] in
              transform_log ~ctxs ~mcfg ~tblk:tblk' logs'
            | IId iid ->
              let iid' = gensym_raw_id iid in
              let e = EXP_Ident (ID_Local iid') in
              let ctx' = RawidM.update_or e (fun _ -> e) iid ctx in
              let tblk' = add_code tblk ~code:[(IId iid', INSTR_Op exp')] in
              let ctxs' = update_stack_ctx ~ctx:ctx' ctxs in
              transform_log ~ctxs:ctxs' ~mcfg ~tblk:tblk' logs'
            end
          | INSTR_Call (_, _, _), Some (_, INSTR_Call ((f_t, f_exp), taargs, anns)) ->
        
            (* 1. Need to analyze the targs. Match them with the function signatures from mcfg
               2. Recursively call normalize_log
               3. continue with the rest of the stack
            *)
            begin match id, AstLib.intrinsic_exp f_exp with
              | IVoid _, Some _ ->
                let taargs' = List.map (fun (texp, params) -> (subst_texp ~ctx texp, params)) taargs in
                let tblk' = add_code tblk ~code:[(id, INSTR_Call ((f_t, f_exp), taargs', anns))] in
                transform_log ~ctxs ~mcfg ~tblk:tblk' logs'
              | IId iid, Some _ ->
                let iid' = gensym_raw_id iid in
                let taargs' = List.map (fun (texp, params) -> (subst_texp ~ctx texp, params)) taargs in
                let tblk' = add_code tblk ~code:[(IId iid', INSTR_Call ((f_t, f_exp), taargs', anns))] in
                let exp = EXP_Ident (ID_Local iid') in
                let ctx' = RawidM.update_or exp (fun _ -> exp) iid ctx in
                let ctxs' = update_stack_ctx ~ctx:ctx' ctxs in
                transform_log ~ctxs:ctxs' ~mcfg ~tblk:tblk' logs'
              | IVoid _, None ->
                begin match logs' with
                  | F_args (f_id, params)::logs'' ->
                    let targs = List.map fst taargs in
                    let ctx' = transform_definition ~ctx targs ~params in
                    (* TODO: can simplify get_f_def_from_mcfg *)
                    begin match get_f_def_from_mcfg (EXP_Ident (ID_Global f_id)) ~mcfg with
                      | Some f_def' ->
                        let ctxs' = push_stack ~hd:(ctx', f_def', id) ctxs in
                        transform_log ~ctxs:ctxs' ~mcfg ~tblk logs''
                      | None -> Error "normalize_log: function not found"
                    end
                  | _ ->
                    let taargs' = List.map (fun (texp, params) -> (subst_texp ~ctx texp, params)) taargs in
                    let tblk' = add_code tblk ~code:[(id, INSTR_Call ((f_t, f_exp), taargs', anns))] in
                    transform_log ~ctxs ~mcfg ~tblk:tblk' logs'
                    (* Error "normalize_log: logging error on call" *)
                end
              | IId iid, None ->
                begin match logs' with
                  | F_args (f_id, params)::logs'' ->
                    let targs = List.map fst taargs in
                    let ctx' = transform_definition ~ctx targs ~params in
                    begin match get_f_def_from_mcfg (EXP_Ident (ID_Global f_id)) ~mcfg with
                      | Some f_def' ->
                        let ctxs' = push_stack ~hd:(ctx', f_def', id) ctxs in
                        transform_log ~ctxs:ctxs' ~mcfg ~tblk logs''
                        (* let* (_, stack2, tblk2, texp) = transform_log ctx' f_def' mcfg tblk stack'' in *)
                        (* begin match texp with *)
                        (*   | Some (_, exp) -> *)
                        (*     let ctx2 = RawidM.update_or exp (fun _ -> exp) iid ctx in *)
                        (*     normalize_log ctx2 f_def mcfg tblk2 stack2 *)
                        (*   | None -> *)
                        (*     Error "normalize_log: call should return some value" *)
                        (* end *)
                      | None -> Error "normalize_log: function not found"
                    end
                  | _ ->
                    let iid' = gensym_raw_id iid in
                    let taargs' = List.map (fun (texp, params) -> (subst_texp ~ctx texp, params)) taargs in
                    let tblk' = add_code tblk ~code:[(IId iid', INSTR_Call ((f_t, f_exp), taargs', anns))] in
                    let exp = EXP_Ident (ID_Local iid') in
                    let ctx' = RawidM.update_or exp (fun _ -> exp) iid ctx in
                    let ctxs' = update_stack_ctx ~ctx:ctx' ctxs in
                    transform_log ~ctxs:ctxs' ~mcfg ~tblk:tblk' logs'
                    (* Error "normalize_log: logging error on call" *)
                end
            end
          | INSTR_Alloca _, Some (_, INSTR_Alloca (dt, anns)) ->
            begin match id with
              | IVoid _ -> Error "normalize_log: Alloca must have id"
              | IId id ->
                let id' = gensym_raw_id id in
                let exp = EXP_Ident (ID_Local id') in
                let tblk' = add_code tblk ~code:[(IId id', INSTR_Alloca (dt, anns))] in
                let ctx' = RawidM.update_or exp (fun _ -> exp) id ctx in
                let ctxs' = update_stack_ctx ~ctx:ctx' ctxs in
                transform_log ~ctxs:ctxs' ~mcfg ~tblk:tblk' logs'
            end
          | INSTR_Load _, Some (_, INSTR_Load (dt, texp, anns)) ->
            begin match id with
              | IVoid _ -> Error "normalize_log: Load must have id"
              | IId id ->
                let texp' = subst_texp ~ctx texp in
                let id' = gensym_raw_id id in
                let exp = EXP_Ident (ID_Local id') in
                let tblk' = add_code tblk ~code:[(IId id', INSTR_Load (dt, texp', anns))] in
                let ctx' = RawidM.add id exp ctx in
                let ctxs' = update_stack_ctx ~ctx:ctx' ctxs in
                transform_log ~ctxs:ctxs' ~mcfg ~tblk:tblk' logs'
            end
          | INSTR_Store _, Some (_, INSTR_Store (texp1, texp2, anns)) ->
            let texp1' = subst_texp ~ctx texp1 in
            let texp2' = subst_texp ~ctx texp2 in
            let tblk' = add_code tblk ~code:[(id, INSTR_Store (texp1', texp2', anns))] in
            transform_log ~ctxs ~mcfg ~tblk:tblk' logs'
          | INSTR_Fence _, Some (_, INSTR_Fence (co, o)) ->
            let tblk' = add_code tblk ~code:[(id, INSTR_Fence (co, o))] in
            transform_log ~ctxs ~mcfg ~tblk:tblk' logs'
          | INSTR_AtomicCmpXchg _, Some (_, INSTR_AtomicCmpXchg cmpxchg) ->
            let cmpxchg' = {c_weak=cmpxchg.c_weak;
                            c_volatile=cmpxchg.c_volatile;
                            c_ptr=subst_texp ~ctx cmpxchg.c_ptr;
                            c_cmp=cmpxchg.c_cmp;
                            c_cmp_type=cmpxchg.c_cmp_type;
                            c_new=subst_texp ~ctx cmpxchg.c_new;
                            c_syncscope=cmpxchg.c_syncscope;
                            c_success_ordering=cmpxchg.c_success_ordering;
                            c_failure_ordering=cmpxchg.c_failure_ordering;
                            c_align=cmpxchg.c_align
                           } in
            begin match id with
              | IVoid _ -> Error "normalize_log: cmpxchg must have id"
              | IId id -> 
                let id' = gensym_raw_id id in
                let exp = EXP_Ident (ID_Local id') in
                let tblk' = add_code tblk ~code:[(IId id', INSTR_AtomicCmpXchg (cmpxchg'))] in
                let ctx' = RawidM.update_or exp (fun _ -> exp) id ctx in
                let ctxs' = update_stack_ctx ~ctx:ctx' ctxs in
               transform_log ~ctxs:ctxs' ~mcfg ~tblk:tblk' logs'
            end
          | INSTR_AtomicRMW _, Some (_, INSTR_AtomicRMW atomicrmw) ->
            let atomicrmw' = {a_volatile=atomicrmw.a_volatile;
                              a_operation=atomicrmw.a_operation;
                              a_ptr=subst_texp ~ctx atomicrmw.a_ptr;
                              a_val=subst_texp ~ctx atomicrmw.a_val;
                              a_syncscope=atomicrmw.a_syncscope;
                              a_ordering=atomicrmw.a_ordering;
                              a_align=atomicrmw.a_align;
                              a_type=atomicrmw.a_type
                             } in
            begin match id with
              | IVoid _ -> Error "normalize_log: atomicrmw must have id"
              | IId id -> 
                let id' = gensym_raw_id id in
                let exp = EXP_Ident (ID_Local id') in
                let tblk' = add_code tblk ~code:[(IId id', INSTR_AtomicRMW (atomicrmw'))] in
                let ctx' = RawidM.update_or exp (fun _ -> exp) id ctx in
                let ctxs' = update_stack_ctx ~ctx:ctx' ctxs in
                transform_log ~ctxs:ctxs' ~mcfg ~tblk:tblk' logs'
            end
          | INSTR_VAArg _, Some (_, INSTR_VAArg (texp, t)) ->
            let texp' = subst_texp ~ctx texp in
            begin match id with
              | IVoid _ -> Error "normalize_log: va_arg must have id"
              | IId id ->
                let id' = gensym_raw_id id in
                let exp = EXP_Ident (ID_Local id') in
                let tblk' = add_code tblk ~code:[(IId id', INSTR_VAArg (texp', t))] in
                let ctx' = RawidM.update_or exp (fun _ -> exp) id ctx in
                let ctxs' = update_stack_ctx ~ctx:ctx' ctxs in
                transform_log ~ctxs:ctxs' ~mcfg ~tblk:tblk' logs'
            end
          | INSTR_LandingPad, Some (_, INSTR_LandingPad) ->
            begin match id with
              | IVoid _ -> Error "normalize_log: va_arg must have id"
              | IId id ->
                let id' = gensym_raw_id id in
                let exp = EXP_Ident (ID_Local id') in
                let tblk' = add_code tblk ~code:[(IId id', INSTR_LandingPad)] in
                let ctx' = RawidM.update_or exp (fun _ -> exp) id ctx in
                let ctxs' = update_stack_ctx ~ctx:ctx' ctxs in
                transform_log ~ctxs:ctxs' ~mcfg ~tblk:tblk' logs'
            end
          | _ ->
            Printf.printf "The line with no match is: %s\n" (ShowAST.dshowInstrWithId ShowAST.dshowDtyp (id, ins) |> DList.coq_DString_to_string |> Camlcoq.camlstring_of_coqstring);
            Printf.printf "The function this tracer is currently in:\n%s\n" (ShowAST.dshowDeclaration (f_def.df_prototype) |> camlstring_of_dstring);
            Error "normalize_log: no match"
        end
      | _ ->  Error "normalize_log has a standalone f_args not processed"
    end

(* TODO: don't modify terminator in the function
   Use the substitution to glue afterward
   factrect.ll should be checked
*)
let transform_code
    ~(f_id : function_id)
    ~(mcfg : typ CFG.mcfg)
    (stack : log_stream) =
  match get_f_def_from_mcfg (EXP_Ident (ID_Global f_id)) ~mcfg with
  | None -> Error (Printf.sprintf "Cannot found definition %s" (ShowAST.dshow_raw_id f_id |> DList.coq_DString_to_string |> Camlcoq.camlstring_of_coqstring))
  | Some f_def -> 
    let tblk : typ block = {blk_id= f_def.df_instrs.init;
                            blk_phis=[];
                            blk_code=[];
                            blk_term=(TERM_Ret (TYPE_I (Camlcoq.N.of_int 8), EXP_Integer (Camlcoq.Z.of_sint 1)));
                            blk_comments= None
                           } in
    let ctx = RawidM.empty in
    let ctxs = [(ctx, f_def, IVoid Z0)] in
    let* tblk' = transform_log ~ctxs:ctxs ~mcfg ~tblk (List.tl stack) in
    Ok {
      blk_id = tblk'.blk_id;
      blk_phis = tblk'.blk_phis;
      blk_code = List.rev tblk'.blk_code;
      blk_term = tblk'.blk_term;
      blk_comments=tblk'.blk_comments
    }

(** Printing trace **)
let output_channel = ref stdout

let print_normalized_log ll_ast =
  let mcfg = get_mcfg ll_ast in
  let main_f_id = (Name (Camlcoq.coqstring_of_camlstring "main")) in
  let code = List.rev !Log.log in
  (* let code = transform_dtyp_to_typ_log (List.rev !Log.log) main_f_id mcfg |> List.rev in *)
  (* print_tlog code; *)
  match transform_code ~f_id:main_f_id ~mcfg code with
  | Ok tblk -> 
    print_tblk tblk
  | Error s -> failwith s

(** Generate an ll_ast for output **)
let get_f_def_from_ast
    (f_exp : typ exp)
    (ll_ast: (typ, typ block * typ block list) toplevel_entities)
  : ((typ, typ block * typ block list) toplevel_entity list) * ((typ, typ block * typ block list) toplevel_entity list) =
  let find_aux : (typ, typ block * typ block list) toplevel_entity -> bool  = function
    | TLE_Definition f_def ->
      exp_eq ~f:typ_eq (EXP_Ident (ID_Global f_def.df_prototype.dc_name)) f_exp
    | _ -> false in
  List.partition find_aux ll_ast

let gen_executable_trace ll_ast =
  let mcfg = get_mcfg ll_ast in
  let main_f_id = (Name (Camlcoq.coqstring_of_camlstring "main")) in
  let code = List.rev !Log.log in
  let* tblk = transform_code ~f_id:main_f_id ~mcfg code in
  match get_f_def_from_ast (EXP_Ident (ID_Global main_f_id)) ll_ast with
  | [f_tle], r_tles ->
    begin match f_tle with
    | TLE_Definition f_def ->
      let f_def' =
        {df_prototype=f_def.df_prototype;
         df_args=f_def.df_args;
         df_instrs=tblk,[]
        } in
       Ok (r_tles @ [TLE_Definition f_def'])
    | _ -> Error "gen_executable_trace: main function is not definition"
    end
  | _ -> Error "gen_executable_trace: failed to get main function"

