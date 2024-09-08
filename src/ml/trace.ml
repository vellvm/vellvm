open Log
open Denotation
open ShowAST
open LLVMAst
open OrderedType
open DynamicTypes
open CFG

let print_dblk dblk : unit =
  Printf.printf "%s" (ShowAST.dshowBlock ShowAST.dshowDtyp (dblk) |> DList.coq_DString_to_string |> Camlcoq.camlstring_of_coqstring)

let print_log_entry (le : log_entry) =
  Printf.printf "%s" (Log.dshow_log_entry le |> DList.coq_DString_to_string |> Camlcoq.camlstring_of_coqstring)

let print_log () : unit =
  Printf.printf "%s\n" (Log.dstring_of_log_stream !Log.log |> DList.coq_DString_to_string |> Camlcoq.camlstring_of_coqstring)
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

type ctx = dtyp exp RawidM.t

type code = (instr_id * dtyp instr) list

let gensym : string -> string =
  let c = ref 0 in
  fun (s:string) -> incr c; Printf.sprintf "_temp%s%d" s (!c)

let gensym_int : int -> int =
  let c = ref 0 in
  fun (_:int) -> incr c; !c

let gensym_raw_id : raw_id -> raw_id = function
  | Name id ->
    let id' = Camlcoq.camlstring_of_coqstring id |> gensym |> Camlcoq.coqstring_of_camlstring in
    Name id'
  | Anon i ->
    let i' = Camlcoq.Z.to_int i |> gensym_int |> Camlcoq.Z.of_uint in
    Anon i'
    (* let temp_name = Printf.sprintf "anon%d" (Camlcoq.Z.to_int i) in *)
    (* let id' = *)
    (*   temp_name |> gensym |> Camlcoq.coqstring_of_camlstring in *)
    (* Name id' *)
  | Raw i ->
    let i' = Camlcoq.Z.to_int i |> gensym_int |> Camlcoq.Z.of_uint in
    Raw i'
    (* let temp_name = Printf.sprintf "anon%d" (Camlcoq.Z.to_int i) in *)
    (* let id' = *)
    (*   temp_name |> gensym |> Camlcoq.coqstring_of_camlstring in *)
    (* Name id' *)
    (* let id' = Campcoq.camlstring_of_coqstring "raw" |> gensym |> Camlcoq.coqstring_of_camlstring in *)

(* Substitution r2 using r1 *)
let subst_raw_id_opt (ctx : ctx) (s : raw_id) (d : dtyp exp) =
  match RawidM.find_opt s ctx with
  | Some v -> v
  | None -> d

let subst_ident_opt (ctx : ctx) (s : ident) (d : dtyp exp) =
  match s with
  | ID_Global r | ID_Local r -> subst_raw_id_opt ctx r d

let subst_exp (ctx : ctx) (s : dtyp exp) : dtyp exp =
  match s with
  | EXP_Ident ident ->
    subst_ident_opt ctx ident s
  | _ -> s

let subst_texp (ctx : ctx) (s : dtyp texp) : dtyp texp =
  let (t, exp) = s in
  t, subst_exp ctx exp

let subst_texps (ctx : ctx) (ss : dtyp texp list) : dtyp texp list =
  List.map (subst_texp ctx) ss

type dblk = dtyp LLVMAst.block


(* Algorithm is as follows:
   If getting a ret, return by one level and get the previous context
   if getting an instruction, case analysis
      If the instruction is call. save the cfg and go for one level (a recursive call)
   if  getting phi node. need to know where did it came from (bid). Then find the right node and substitute the values into the map
*)
let add_code dblk (code : code) : dblk =
  let code' = dblk.blk_code >@ code in
  {blk_id = dblk.blk_id;
   blk_phis = dblk.blk_phis;
   blk_code = code';
   blk_term = dblk.blk_term;
   blk_comments = dblk.blk_comments
  }

let add_term dblk (term : dtyp terminator) : dblk =
  {blk_id = dblk.blk_id;
   blk_phis = dblk.blk_phis;
   blk_code = dblk.blk_code;
   blk_term = term;
   blk_comments = dblk.blk_comments
  }
(* TODO: How to deal with rightmost terminator when it is not well-formed *)

(* TODO: Substitution needed *)
let normalize_exp (ctx : ctx) (op : dtyp exp) : dtyp exp =
  match op with
  | OP_IBinop (ibinop, t, exp1, exp2) ->
    let exp1' = subst_exp ctx exp1 in
    let exp2' = subst_exp ctx exp2 in
    OP_IBinop (ibinop, t, exp1', exp2')
  | OP_ICmp (icmp, t, exp1, exp2) -> 
    let exp1' = subst_exp ctx exp1 in
    let exp2' = subst_exp ctx exp2 in
    OP_ICmp (icmp, t, exp1', exp2')
  | OP_FBinop (fbinop, fm, t, exp1, exp2) ->
    let exp1' = subst_exp ctx exp1 in
    let exp2' = subst_exp ctx exp2 in
    OP_FBinop (fbinop, fm, t, exp1', exp2')
  | OP_FCmp (fcmp, t, exp1, exp2) ->
    let exp1' = subst_exp ctx exp1 in
    let exp2' = subst_exp ctx exp2 in
    OP_FCmp (fcmp, t, exp1', exp2')
  | OP_Conversion (conv, t1, exp, t2) ->
    let exp' = subst_exp ctx exp in
    OP_Conversion (conv, t1, exp', t2)
  | OP_GetElementPtr (t, texp, texps) ->
    let texp' = subst_texp ctx texp in
    let texps' = subst_texps ctx texps in
    OP_GetElementPtr (t, texp', texps')
  | OP_ExtractElement (texp1, texp2) ->
    let texp1' = subst_texp ctx texp1 in
    let texp2' = subst_texp ctx texp2 in
    OP_ExtractElement (texp1', texp2')
  | OP_InsertElement (texp1, texp2, texp3) -> 
    let texp1' = subst_texp ctx texp1 in
    let texp2' = subst_texp ctx texp2 in
    let texp3' = subst_texp ctx texp3 in
    OP_InsertElement (texp1', texp2', texp3')
  | OP_ShuffleVector (texp1, texp2, texp3) -> 
    let texp1' = subst_texp ctx texp1 in
    let texp2' = subst_texp ctx texp2 in
    let texp3' = subst_texp ctx texp3 in
    OP_ShuffleVector (texp1', texp2', texp3')
  | OP_ExtractValue (texp, il) -> 
    let texp' = subst_texp ctx texp in
    OP_ExtractValue (texp', il)
  | OP_InsertValue (texp1, texp2, il) -> 
    let texp1' = subst_texp ctx texp1 in
    let texp2' = subst_texp ctx texp2 in
    OP_InsertValue (texp1', texp2', il)
  | OP_Select (texp1, texp2, texp3) -> 
    let texp1' = subst_texp ctx texp1 in
    let texp2' = subst_texp ctx texp2 in
    let texp3' = subst_texp ctx texp3 in
    OP_Select (texp1', texp2', texp3')
  | OP_Freeze texp ->
    let texp' = subst_texp ctx texp in
    OP_Freeze texp'
  | EXP_Ident ident ->
    let op' = subst_ident_opt ctx ident op in
    op'
  | EXP_Integer _ | EXP_Float _ | EXP_Double _
  | EXP_Hex _ | EXP_Bool _ | EXP_Null | EXP_Zero_initializer
  | EXP_Cstring _ | EXP_Undef | EXP_Poison | EXP_Struct _
  | EXP_Packed_struct _ | EXP_Array _ | EXP_Vector _ ->
    (* let lid' = gensym_raw_id lid in *)
    (* let code = [(IId lid', INSTR_Op op)] in *)
    (* let exp = EXP_Ident (ID_Local lid') in *)
    op

let ctx_unit_to_string (r : raw_id) (d : dtyp exp) : string =
  Printf.sprintf "%s->%s" (ShowAST.dshow_raw_id r |> DList.coq_DString_to_string |> Camlcoq.camlstring_of_coqstring)
    (ShowAST.dshowExp ShowAST.dshowDtyp d |> DList.coq_DString_to_string |> Camlcoq.camlstring_of_coqstring)

let normalize_phi (ctx : ctx) (id : raw_id) (phi : dtyp phi) (bid_from : raw_id) : ctx =
  match phi with
  | Phi (_, args) -> 
    match Util.assoc AstLib.eq_dec_raw_id bid_from args with
    | Some op ->
    (*
       If op is some values -> then need to case analysis on that {tempid / phi}
       If exp is some operations, then assign this id with that operations, and {id / phiid}
 *)
      let exp = normalize_exp ctx op in
      let ctx' = RawidM.update_or exp (fun _ -> exp) id ctx in
      ctx'
    | None -> failwith (Printf.sprintf "No block match phi node")

let list_to_map l1 l2 =
  List.fold_left (fun acc (key, value) -> RawidM.add key value acc) RawidM.empty @@ List.combine l1 l2

let normalize_definition ctx (mcfg : DynamicTypes.dtyp CFG.mcfg) (f : dtyp exp) (targs : dtyp texp list) : ctx option =
  match f with
  | EXP_Ident (ID_Global id) ->
    begin match List.find_opt (fun x -> RawidOrdPrint.compare x.df_prototype.dc_name id == 0) mcfg.m_definitions with
      | None ->
        None
      | Some def ->
        let args = List.map (fun (_, arg) -> subst_exp ctx arg) targs in
        let ctx' = List.combine def.df_args args |> RawidM.of_list in
        Printf.printf "ctx: %s\n" (RawidM.to_string ctx_unit_to_string ctx');
        Some ctx'
        (* Need to zip local_id with raw_id, If the length is the same will proceed the above, otherwise error *)
    end
  | _ -> None

let rec normalize_log
    (ctx : ctx)
    (mcfg : DynamicTypes.dtyp CFG.mcfg)
    (dblk : dblk)
    (stack : log_stream) : ctx * log_stream * dblk * dtyp texp option =
  match stack with
  | [] ->
    ctx, [], dblk, None
  | log::stack' ->
    print_log_entry log;
    begin match log with
      | Phi_node (lid, phi, bid) ->
        let ctx'= normalize_phi ctx lid phi bid in
        normalize_log ctx' mcfg dblk stack'
      | Ret texp ->
        let texp' = subst_texp ctx texp in
        let dblk' = add_term dblk (TERM_Ret texp') in
        ctx, stack', dblk', Some texp' 
      | Instr (id, ins) ->
        begin match ins with
          | INSTR_Comment _ ->
            let dblk' = add_code dblk [(id, ins)] in
            normalize_log ctx mcfg dblk' stack'
          | INSTR_Op exp ->
            let exp' = normalize_exp ctx exp in
            begin match id with
            | IVoid _ ->
              let dblk' = add_code dblk [(id, INSTR_Op exp')] in
              normalize_log ctx mcfg dblk' stack'
            | IId id ->
              let id' = gensym_raw_id id in
              let e = EXP_Ident (ID_Local id') in
              let ctx' = RawidM.update_or e (fun _ -> e) id ctx in
              let dblk' = add_code dblk [(IId id', INSTR_Op exp')] in
              normalize_log ctx' mcfg dblk' stack'
            end
          | INSTR_Call ((_, f), targs, _) ->
        
            (* 1. Need to analyze the targs. Match them with the function signatures from mcfg
               2. Recursively call normalize_log
               3. continue with the rest of the stack
            *)

            begin match id, AstLib.intrinsic_exp f with
              | IVoid _, Some s ->
                let dblk' = add_code dblk [(id, ins)] in
                normalize_log ctx mcfg dblk' stack'
              | IId id, Some s->
                let id' = gensym_raw_id id in
                let dblk' = add_code dblk [(IId id', ins)] in
                let exp = EXP_Ident (ID_Global id') in
                let ctx' = RawidM.update_or exp (fun _ -> exp) id ctx in
                normalize_log ctx' mcfg dblk' stack'
              | IVoid _, None ->
                let args = List.map (fun (arg, _) -> arg) targs in
                begin match normalize_definition ctx mcfg f args with
                  | Some ctx' ->
                    let (_, stack2, dblk2, _) = normalize_log ctx' mcfg dblk stack' in
                    normalize_log ctx mcfg dblk2 stack2
                  | None -> 
                    (* Local functions *)
                    failwith "Function mismatch"
                end
              | IId id, None ->
                let args = List.map (fun (arg, _) -> arg) targs in
                begin match normalize_definition ctx mcfg f args with
                  | Some ctx' ->
                    let (_, stack2, dblk2, texp) = normalize_log ctx' mcfg dblk stack' in
                    begin match texp with
                      | Some (_, exp) -> 
                        let ctx2 = RawidM.update_or exp (fun _ -> exp) id ctx in
                        Printf.printf "ctx: %s\n" (RawidM.to_string ctx_unit_to_string ctx);
                        Printf.printf "ctx': %s\n" (RawidM.to_string ctx_unit_to_string ctx');
                        Printf.printf "ctx2: %s\n" (RawidM.to_string ctx_unit_to_string ctx2);
                        normalize_log ctx2 mcfg dblk2 stack2
                      | None ->
                        failwith "Should return something"
                    end
                  | None ->
                    print_dblk dblk;
                    failwith "function takes in no parameter?"
                end
            end
          | INSTR_Alloca (t, tann) ->
            begin match id with
              | IVoid _ -> failwith "Alloca must have id"
              | IId id ->
                let id' = gensym_raw_id id in
                let exp = EXP_Ident (ID_Local id') in
                let ctx' = RawidM.update_or exp (fun _ -> exp) id ctx in
                let dblk' = add_code dblk [(IId id', INSTR_Alloca (t, tann))] in
                normalize_log ctx' mcfg dblk' stack'
            end
          | INSTR_Load (t, texp, tann) ->
            begin match id with
              | IVoid _ -> failwith "Load must have id"
              | IId id ->
                let texp' = subst_texp ctx texp in
                let id' = gensym_raw_id id in
                let exp = EXP_Ident (ID_Local id') in
                let ctx' = RawidM.update_or exp (fun _ -> exp) id ctx in
                let dblk' = add_code dblk [(IId id', INSTR_Load (t, texp', tann))] in
                normalize_log ctx' mcfg dblk' stack'
            end
          | INSTR_Store (texp1, texp2, tann) ->
            let texp1' = subst_texp ctx texp1 in
            let texp2' = subst_texp ctx texp2 in
            let dblk' = add_code dblk [(id, INSTR_Store (texp1', texp2', tann))] in
            normalize_log ctx mcfg dblk' stack'
          | INSTR_Fence (co, o) ->
            let dblk' = add_code dblk [(id, INSTR_Fence (co, o))] in
            normalize_log ctx mcfg dblk' stack'
          | INSTR_AtomicCmpXchg cmpxchg ->
            let cmpxchg' = {c_weak=cmpxchg.c_weak;
                            c_volatile=cmpxchg.c_volatile;
                            c_ptr=subst_texp ctx cmpxchg.c_ptr;
                            c_cmp=cmpxchg.c_cmp;
                            c_cmp_type=cmpxchg.c_cmp_type;
                            c_new=subst_texp ctx cmpxchg.c_new;
                            c_syncscope=cmpxchg.c_syncscope;
                            c_success_ordering=cmpxchg.c_success_ordering;
                            c_failure_ordering=cmpxchg.c_failure_ordering;
                            c_align=cmpxchg.c_align
                           } in
            begin match id with
              | IVoid _ -> failwith "cmpxchg must have id"
              | IId id -> 
                let id' = gensym_raw_id id in
                let exp = EXP_Ident (ID_Local id') in
                let ctx' = RawidM.update_or exp (fun _ -> exp) id ctx in
                let dblk' = add_code dblk [(IId id', INSTR_AtomicCmpXchg (cmpxchg'))] in
                normalize_log ctx' mcfg dblk' stack'
            end
          | INSTR_AtomicRMW atomicrmw ->
            let atomicrmw' = {a_volatile=atomicrmw.a_volatile;
                              a_operation=atomicrmw.a_operation;
                              a_ptr=subst_texp ctx atomicrmw.a_ptr;
                              a_val=subst_texp ctx atomicrmw.a_val;
                              a_syncscope=atomicrmw.a_syncscope;
                              a_ordering=atomicrmw.a_ordering;
                              a_align=atomicrmw.a_align;
                              a_type=atomicrmw.a_type
                             } in
            begin match id with
              | IVoid _ -> failwith "atomicrmw must have id"
              | IId id -> 
                let id' = gensym_raw_id id in
                let exp = EXP_Ident (ID_Local id') in
                let ctx' = RawidM.update_or exp (fun _ -> exp) id ctx in
                let dblk' = add_code dblk [(IId id', INSTR_AtomicRMW (atomicrmw'))] in
                normalize_log ctx' mcfg dblk' stack'
            end
          | INSTR_VAArg (texp, t) ->
            let texp' = subst_texp ctx texp in
            begin match id with
              | IVoid _ -> failwith "va_arg must have id"
              | IId id ->
                let id' = gensym_raw_id id in
                let exp = EXP_Ident (ID_Local id') in
                let ctx' = RawidM.update_or exp (fun _ -> exp) id ctx in
                let dblk' = add_code dblk [(IId id', INSTR_VAArg (texp', t))] in
                normalize_log ctx' mcfg dblk' stack'
            end
          | INSTR_LandingPad ->
            begin match id with
              | IVoid _ -> failwith "va_arg must have id"
              | IId id ->
                let id' = gensym_raw_id id in
                let exp = EXP_Ident (ID_Local id') in
                let ctx' = RawidM.update_or exp (fun _ -> exp) id ctx in
                let dblk' = add_code dblk [(IId id', INSTR_LandingPad)] in
                normalize_log ctx' mcfg dblk' stack'
            end
        end
    end

let normalize_code 
    (mcfg : DynamicTypes.dtyp CFG.mcfg)
    (stack : log_stream) : dblk =
  let ctx = RawidM.empty in
  (* Printf.printf "%s" (Log.dstring_of_log_stream stack |> DList.coq_DString_to_string |> Camlcoq.camlstring_of_coqstring); *)
  let dblk : dtyp block = {blk_id=Name (['0']);
              blk_phis=[];
              blk_code=[];
              blk_term=(TERM_Ret (DTYPE_Void, EXP_Undef));
              blk_comments= None
             } in
  let (_, _ , dblk', _) = normalize_log ctx mcfg dblk stack in
  {blk_id=dblk'.blk_id;
   blk_phis=dblk'.blk_phis;
   blk_code=List.rev dblk'.blk_code;
   blk_term=dblk'.blk_term;
   blk_comments=dblk'.blk_comments
  }

let get_mcfg ll_ast =
  (TypToDtyp.convert_types (mcfg_of_tle (TopLevel.TopLevelBigIntptr.link TopLevel.TopLevelBigIntptr.coq_PREDEFINED_FUNCTIONS ll_ast)))



(** Printing trace **)
let output_channel = ref stdout


let print_normalized_log ll_ast =
  let mcfg = get_mcfg ll_ast in
  let dblk = normalize_code mcfg (List.rev !Log.log) in
  print_dblk dblk




  
