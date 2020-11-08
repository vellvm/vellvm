(* astlib.ml *)

(* Helper functions of abstract syntax of trees. *)
(******************************************************************************)

open Format
open Ast
open Range

(* Precedence for expressions and operators *)
(* Higher precedences bind more tightly     *)

let prec_of_binop = function
| Mul -> 100
| Add | Sub -> 90
| Shl | Shr | Sar -> 80
| Lt  | Lte | Gt | Gte -> 70
| Eq  | Neq -> 60
| And  -> 50
| Or   -> 40
| IAnd -> 30
| IOr  -> 20

let prec_of_unop = function _ -> 110

let prec_of_exp = function
| Bop (o,_,_) -> prec_of_binop o
| Uop (o,_) -> prec_of_unop o
| _ -> 130


(* Pretty Printer for AST *)
let string_of_unop = function
| Neg -> "-"
| Lognot -> "!"
| Bitnot -> "~"

let string_of_binop = function
| Mul   -> "*"
| Add   -> "+"
| Sub   -> "-"
| Shl   -> "<<"
| Shr   -> ">>"
| Sar   -> ">>>"
| Lt    -> "<"
| Lte   -> "<="
| Gt    -> ">"
| Gte   -> ">="
| Eq    -> "=="
| Neq   -> "!="
| And   -> "&"
| Or    -> "|"
| IAnd  -> "[&]"
| IOr   -> "[|]"

let print_id_aux fmt (x:id) = pp_print_string fmt x

let rec print_list_aux fmt sep pp l =
  begin match l with
    | []    -> ()
    | [h]   -> pp fmt h
    | h::tl -> pp fmt h; sep ();
	           print_list_aux fmt sep pp tl
  end

let rec print_ty_aux fmt t =
  let pps = pp_print_string fmt in
  match t with
  | TBool         -> pps "bool"
  | TInt          -> pps "int"
  | TRef r        -> print_rty_aux fmt r
  | TNullRef r    -> pps "("; print_rty_aux fmt r; pps ")?"

and print_ret_ty_aux fmt t =
  let pps = pp_print_string fmt in
  begin match t with
    | RetVoid       -> pps "void"
    | RetVal t      -> print_ty_aux fmt t
  end
    
and print_rty_aux fmt r =
  let pps = pp_print_string fmt in
  begin match r with
    | RString  -> pps "string"
    | RArray t -> print_ty_aux fmt t; pps "[]"
    | RStruct id -> pps id
    | RFun (ts, t) -> pps "("; 
                      print_list_aux fmt (fun () -> pps ", ") print_ty_aux ts;
                      pps ")"; pps "->"; print_ret_ty_aux fmt t
  end

and print_exp_aux level fmt e =
  let pps = pp_print_string fmt in
  let ppsp = pp_print_space fmt in
  let this_level = prec_of_exp e.elt in

  if this_level < level then pps "(";
  begin match e.elt with
    | CNull r -> print_rty_aux fmt r; pps "null"
    | CBool v -> pps (if v then "true" else "false")
    | CInt  v -> pps (Int64.to_string v)
    | CStr  v -> pps (Printf.sprintf "%S" v)
    | CArr (ty,vs) -> begin
        pps "new "; print_ty_aux fmt ty; pps "[]";
        pps "{";
        pp_open_hbox fmt ();
        print_list_aux fmt (fun () -> pps ","; pp_print_space fmt()) (print_exp_aux 0) vs;
        pp_close_box fmt ();
        pps "}";
      end
    | Length l -> pps "length( "; print_exp_aux this_level fmt l; pps " )"
    | Id id -> print_id_aux fmt id
    | Index (e,i) -> print_exp_aux this_level fmt e; pps "["; print_exp_aux 0 fmt i; pps "]"
    | Call (e, es) -> print_exp_aux this_level fmt e; print_exps_aux "(" ")" fmt es
    | NewArr(ty, e1) ->
        pps "new"; print_ty_aux fmt ty;
        pps "["; print_exp_aux this_level fmt e1; pps "]"
    | NewArrInit (ty, e1, u, e2) ->
        pps "new"; print_ty_aux fmt ty;
        pps "["; print_exp_aux this_level fmt e1;
        pps "] {"; pps u; pps "->"; print_exp_aux this_level fmt e2; pps "}"
    | Bop (o,l,r) ->
        pp_open_box fmt 0;
        print_exp_aux this_level fmt l;
        ppsp (); pps (string_of_binop o); ppsp ();
        print_exp_aux this_level fmt r;
        pp_close_box fmt ()
    | Uop (o,v) ->
        pp_open_box fmt 0;
        pps (string_of_unop o);
        print_exp_aux this_level fmt v;
        pp_close_box fmt ()
    | Proj (e, id) ->
        pp_open_box fmt 0;
        print_exp_aux this_level fmt e;
        ppsp (); pps "."; ppsp (); pps id;
        pp_close_box fmt ()
    | CStruct (t, l) ->
        pps "new "; pps t;
        pp_open_box fmt 0;
        pps "{";
        List.iter (fun s -> print_cfield_aux this_level fmt s; pps "; ") l;
        pps "}";
        pp_close_box fmt ()
  end; if this_level < level then pps ")"

and print_cfield_aux l fmt (name, exp) =
  pp_open_box fmt 0; 
  pp_print_string fmt name; 
  pp_print_string fmt "="; print_exp_aux l fmt exp;
  pp_close_box fmt ();

and print_exps_aux l r fmt es =
  let pps = pp_print_string fmt in
  pps l;
  pp_open_hvbox fmt 0;
  print_list_aux fmt
    (fun () -> pps ","; pp_print_space fmt())
    (fun fmt -> fun e -> print_exp_aux 0 fmt e) es;
  pp_close_box fmt ();
  pps r

let print_vdecl_aux semi fmt (id, init) =
  let pps = pp_print_string fmt in
  let ppsp = pp_print_space fmt in
  pp_open_hbox fmt ();
  pps "var "; print_id_aux fmt id;
  ppsp (); pps " ="; ppsp ();
  print_exp_aux 0 fmt init; pps semi;
  pp_close_box fmt ()

let rec print_block_aux fmt stmts =
  let pps = pp_print_string fmt in
  let ppsp = pp_print_space fmt in
  let ppnl = pp_force_newline fmt in

  if (List.length stmts) > 0 then
    begin pps "{"; ppnl (); pps "  ";
          pp_open_vbox fmt 0;
          print_list_aux fmt (fun () -> ppsp ()) print_stmt_aux stmts;
          pp_close_box fmt ();
          ppnl (); pps "}"
    end
  else pps "{ }"

and print_cond_aux fmt b_then opt_b_else =
  let pps = pp_print_string fmt in
  print_block_aux fmt b_then;
  begin match opt_b_else with
    | [] -> ()
    | b_else -> pps " else "; print_block_aux fmt b_else
  end

and print_stmt_aux fmt s =
  let pps = pp_print_string fmt in
  let ppsp = pp_print_space fmt in

  begin match s.elt with
    | Decl d -> print_vdecl_aux ";" fmt d

    | Assn (p,e) ->
        pp_open_box fmt 0;
	    print_exp_aux 0 fmt p;
	    pps " ="; ppsp ();
	    print_exp_aux 0 fmt e;
	    pps ";"; pp_close_box fmt ()

    | SCall (e, es) -> 
       print_exp_aux 0 fmt e; print_exps_aux "(" ")" fmt es; pps ";"

    | Ret (eo) ->
        pps "return";
        begin match eo with
          | None -> ()
          | Some e -> pps " "; print_exp_aux 0 fmt e
        end; pps ";"

    | If (e, b_then, opt_b_else) ->
        pps "if ("; print_exp_aux 0 fmt e; pps ") ";
        print_cond_aux fmt b_then opt_b_else

    | Cast(t, id, e, b_null, b_notnull) ->
        pps "ifnull ("; print_id_aux fmt id; pps "="; print_exp_aux 0 fmt e; 
        pps ") ";
        print_cond_aux fmt b_null b_notnull

    | While(e, b) ->
	    pps "while ("; print_exp_aux 0 fmt e; pps ") ";
	    print_block_aux fmt b

    | For(decls, eo, so, body) ->
	    pps "for ("; pp_open_hvbox fmt 0;
        print_list_aux fmt (fun () -> pps ","; ppsp ()) (print_vdecl_aux "") decls;
        pps ";"; ppsp ();
	    begin match eo with
	      | None -> ();
	      | Some e -> print_exp_aux 0 fmt e;
	    end;
	    pps ";"; ppsp ();
	    begin match so with
	      | None -> ()
	      | Some s -> print_stmt_aux fmt s
	    end; pp_close_box fmt ();
	    pps ") "; print_block_aux fmt body
  end

let print_fdecl_aux fmt {elt={frtyp; fname; args; body}} =
  let pps = pp_print_string fmt in
  let ppsp = pp_print_space fmt in
  let ppnl = pp_force_newline fmt in

  print_ret_ty_aux fmt frtyp;
  pps @@ Printf.sprintf " %s(" fname;
  pp_open_hbox fmt ();
  print_list_aux fmt (fun () -> pps ","; ppsp ())
    (fun fmt -> fun (t, id) ->
      print_ty_aux fmt t;
      pps " ";
      print_id_aux fmt id;
    ) args;
  pp_close_box fmt ();
  pps ") "; print_block_aux fmt body; ppnl ()

let print_gdecl_aux fmt (gd:Ast.gdecl) =
  let pps = pp_print_string fmt in
  let ppsp = pp_print_space fmt in
  pp_open_hbox fmt ();
  pps @@ Printf.sprintf "global %s =" gd.name; ppsp ();
  print_exp_aux 0 fmt gd.init; pps ";";
  pp_close_box fmt ()

let print_field fmt f =
  let pps = pp_print_string fmt in
  pp_open_hbox fmt ();
  print_ty_aux fmt f.ftyp; pps " "; pps f.fieldName;
  pp_close_box fmt ()

let print_tdecl_aux fmt ((id, l):Ast.tdecl) =
  let pps = pp_print_string fmt in
  let ppsp = pp_print_space fmt in
  pp_open_hbox fmt ();
  pps @@ Printf.sprintf "struct %s =" id; ppsp ();
  pps "{";
  List.iter (fun s -> print_field fmt s; pps "; ") l;
  pps "}";
  pp_close_box fmt ()

let print_decl_aux fmt g =
  begin match g with
    | Gvdecl d -> print_gdecl_aux fmt d.elt
    | Gfdecl f -> print_fdecl_aux fmt f
    | Gtdecl t -> print_tdecl_aux fmt t.elt
  end

let print_prog_aux fmt p =
  let ppnl = pp_force_newline fmt in
  pp_open_vbox fmt 0;
  List.iter (fun g -> print_decl_aux fmt g; ppnl (); ppnl ()) p;
  pp_close_box fmt ()

let print ppx x : unit =
  pp_open_hvbox std_formatter 0;
  ppx std_formatter x;
  pp_close_box std_formatter ();
  pp_print_newline std_formatter ()

let string_of ppx x : string =
  pp_open_hvbox str_formatter 0;
  ppx str_formatter x;
  pp_close_box str_formatter ();
  flush_str_formatter ()

let print_prog (p:prog) : unit = print print_prog_aux p
let string_of_prog (p:prog) : string = string_of print_prog_aux p

let print_stmt (s:stmt node) : unit = print print_stmt_aux s
let string_of_stmt (s:stmt node) : string = string_of print_stmt_aux s

let print_block (b:block) : unit = print print_block_aux b
let string_of_block (b:block) : string = string_of print_block_aux b

let print_exp (e:exp node) : unit = print (print_exp_aux 0) e
let string_of_exp (e:exp node) : string = string_of (print_exp_aux 0) e

let print_ty (t:ty) : unit = print print_ty_aux t
let string_of_ty (t:ty) : string = string_of print_ty_aux t

(* AST to ML *)

let sp = Printf.sprintf

let ml_string_of_list (f: 'a -> string) (l: 'a list) : string =
  sp "[ %s ]" (String.concat " ; " (List.map f l))

let ml_string_of_option (f: 'a -> string) (o: 'a option) : string =
  begin match o with
  | None -> sp "None"
  | Some x -> sp "Some (%s)" (f x)
  end

(* TODO Change ml string printing for loc *)

let ml_string_of_node (f: 'a -> string) ({elt;loc}: 'a node) =
  sp "{ elt = %s; loc = %s }" (f elt) (Range.ml_string_of_range loc)

let rec ml_string_of_ty (t:ty) : string =
  match t with
  | TBool -> "TBool"
  | TInt -> "TInt"
  | TRef r -> sp "TRef (%s)" (ml_string_of_reft r)
  | TNullRef r -> sp "TNullRef (%s)" (ml_string_of_reft r)

and ml_string_of_ret_ty r =
  match r with
  | RetVoid -> "TVoid"
  | RetVal t -> ml_string_of_ty t


and ml_string_of_reft (r:rty) : string =
  match r with    
  | RString -> "RString"
  | RArray t -> sp "(RArray (%s))" (ml_string_of_ty t)
  | RStruct id -> sp "(RStruct (%s))" id
  | RFun (ts, t) -> sp "RFun (%s, %s)"
                    (ml_string_of_list ml_string_of_ty ts)
                    (ml_string_of_ret_ty t) 


let ml_string_of_id : id -> string = (sp "\"%s\"")

let ml_string_of_binop : binop -> string = function
  | Add  -> "Add"
  | Sub  -> "Sub" 
  | Mul  -> "Mul" 
  | Eq   -> "Eq" 
  | Neq  -> "Neq" 
  | Lt   -> "Lt" 
  | Lte  -> "Lte" 
  | Gt   -> "Gt" 
  | Gte  -> "Gte" 
  | And  -> "And" 
  | Or   -> "Or" 
  | IAnd -> "IAnd" 
  | IOr  -> "IOr" 
  | Shl  -> "Shl" 
  | Shr  -> "Shr" 
  | Sar  -> "Sar" 

let ml_string_of_unop : unop -> string = function
  | Neg    -> "Neg"
  | Lognot -> "Lognot"
  | Bitnot -> "Bitnot"

let rec ml_string_of_exp_aux (e: exp) : string =
  begin match e with 
    | CNull r -> sp "CNull %s" (ml_string_of_reft r)
    | CBool b -> sp "CBool %b" b
    | CInt i -> sp "CInt %LiL" i
    | CStr s -> sp "CStr %S" s
    | CArr (t,cs) -> sp "CArr (%s,%s)" 
                         (ml_string_of_ty t) 
                         (ml_string_of_list ml_string_of_exp cs)
    | CStruct (id, l) -> sp "CStruct (%s, %s)"
                            id
                            (ml_string_of_list ml_string_of_field l)
    | Id id -> sp "Id %s" (ml_string_of_id id)
    | Index (e, i) -> sp "Index (%s, %s)" 
                         (ml_string_of_exp e) (ml_string_of_exp i)
    | Call (e, exps) -> sp "Call (%s, %s)"
                            (ml_string_of_exp e)
                            (ml_string_of_list ml_string_of_exp exps)
    | NewArr (t,e1) -> sp "NewArr (%s,%s)"
        (ml_string_of_ty t) (ml_string_of_exp e1)
    | NewArrInit (t,e1,u,e2) -> sp "NewArrInit (%s,%s,%s,%s)"
        (ml_string_of_ty t) (ml_string_of_exp e1) (ml_string_of_id u) (ml_string_of_exp e2)
    | Proj(exp, id) -> sp "Proj (%s,%s)" (ml_string_of_exp exp) (ml_string_of_id id)
    | Bop (b, e1, e2) -> sp "Bop (%s,%s,%s)"
        (ml_string_of_binop b) (ml_string_of_exp e1) (ml_string_of_exp e2)
    | Uop (u, e) -> sp "Uop (%s, %s)"
        (ml_string_of_unop u) (ml_string_of_exp e)
    | Length (e) -> sp "Length (%s)" (ml_string_of_exp e)
  end

and ml_string_of_exp (e:exp node) : string = 
  ml_string_of_node ml_string_of_exp_aux e

and ml_string_of_field ((id, exp) : cfield) : string =
  sp "%s = %s;" (ml_string_of_id id) (ml_string_of_exp exp)

let ml_string_of_vdecl_aux (id,init:vdecl) : string =
  sp "(%s, %s)"
  (ml_string_of_id id) (ml_string_of_exp init)

let ml_string_of_vdecl (d:vdecl node) : string =
  ml_string_of_node ml_string_of_vdecl_aux d

let rec ml_string_of_stmt_aux (s:stmt) : string =
  match s with
  | Assn (p, e) -> sp "Assn (%s,%s)" (ml_string_of_exp p) (ml_string_of_exp e)
  | Decl d -> sp "Decl (%s)" (ml_string_of_vdecl_aux d)
  | Ret e -> sp "Ret (%s)" (ml_string_of_option ml_string_of_exp e)
  | SCall (exp, exps) -> 
     sp "SCall (%s, %s)" (ml_string_of_exp exp) (ml_string_of_list ml_string_of_exp exps)
  | If (e,b1,b2) -> sp "If (%s,%s,%s)"
                       (ml_string_of_exp e) (ml_string_of_block b1) (ml_string_of_block b2)
  | Cast (r, id, exp, null, notnull) ->
      sp "Cast (%s,%s,%s,%s,%s)"
        (ml_string_of_reft r) id (ml_string_of_exp exp)
        (ml_string_of_block null) (ml_string_of_block notnull)
  | For (d,e,s,b) -> sp "For (%s,%s,%s,%s)"
                        (ml_string_of_list ml_string_of_vdecl_aux d) 
                        (ml_string_of_option ml_string_of_exp e)
                        (ml_string_of_option ml_string_of_stmt s) (ml_string_of_block b)
  | While (e,b) -> sp "While (%s,%s)" (ml_string_of_exp e) (ml_string_of_block b)

and ml_string_of_stmt (s:stmt node) : string =
  ml_string_of_node ml_string_of_stmt_aux s

and ml_string_of_block (b:block) : string =
  ml_string_of_list ml_string_of_stmt b

let ml_string_of_args : (ty * id) list -> string =
  ml_string_of_list (fun (t,i) ->
    sp "(%s,%s)" (ml_string_of_ty t) (ml_string_of_id i))

let rec ml_string_of_fdecl_aux (f:fdecl) : string =
  sp "{ rtyp = %s; name = %s; args = %s; body = %s }"
  (ml_string_of_ret_ty f.frtyp) (ml_string_of_id f.fname)
  (ml_string_of_args f.args) (ml_string_of_block f.body)

and ml_string_of_fdecl (f:fdecl node) : string =
  ml_string_of_node ml_string_of_fdecl_aux f

let ml_string_of_gdecl_aux (gd:gdecl) : string =
  sp "{ name = %s; init = %s }"
     (ml_string_of_id gd.name) (ml_string_of_exp gd.init)

let ml_string_of_gdecl (d:gdecl node) : string =
  ml_string_of_node ml_string_of_gdecl_aux d

let ml_string_of_field {fieldName; ftyp} : string =
  sp "{ fname = %s; typ = %s }"
     (ml_string_of_id fieldName) (ml_string_of_ty ftyp)

let ml_string_of_tdecl_aux (id,fs) : string =
  sp "(id = %s, fs = (%s))" (ml_string_of_id id) (ml_string_of_list ml_string_of_field fs)

let ml_string_of_tdecl (t:tdecl node) : string =
  ml_string_of_node ml_string_of_tdecl_aux t

let ml_string_of_decl : decl -> string = function
  | Gvdecl d -> sp "Gvdecl (%s)" (ml_string_of_gdecl d)
  | Gfdecl f -> sp "Gfdecl (%s)" (ml_string_of_fdecl f)
  | Gtdecl t -> sp "Gtdecl (%s)" (ml_string_of_tdecl t)

let ml_string_of_prog : prog -> string =
  ml_string_of_list ml_string_of_decl
