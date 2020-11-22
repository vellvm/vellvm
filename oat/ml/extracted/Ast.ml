open BinNums
open Datatypes
open Integers

module Int64 = Int64

type int64 = Int64.int

type t = (string * (int * int) * (int * int))

type 'a node = { elt : 'a; loc : t }

(** val elt : 'a1 node -> 'a1 **)

let elt n =
  n.elt

(** val loc : 'a1 node -> t **)

let loc n =
  n.loc

(** val elt_of : 'a1 node -> 'a1 **)

let elt_of n =
  n.elt

type id = char list

type ty =
| TBool
| TInt
| TRef of rty
| TNotNullRef of rty
and rty =
| RString
| RStruct of id
| RArray of ty
| RFun of ty list * ret_ty
and ret_ty =
| RetVoid
| RetVal of ty

(** val ty_rect : 'a1 -> 'a1 -> (rty -> 'a1) -> (rty -> 'a1) -> ty -> 'a1 **)

let ty_rect f f0 f1 f2 = function
| TBool -> f
| TInt -> f0
| TRef x -> f1 x
| TNotNullRef x -> f2 x

(** val ty_rec : 'a1 -> 'a1 -> (rty -> 'a1) -> (rty -> 'a1) -> ty -> 'a1 **)

let ty_rec f f0 f1 f2 = function
| TBool -> f
| TInt -> f0
| TRef x -> f1 x
| TNotNullRef x -> f2 x

(** val rty_rect :
    'a1 -> (id -> 'a1) -> (ty -> 'a1) -> (ty list -> ret_ty -> 'a1) -> rty ->
    'a1 **)

let rty_rect f f0 f1 f2 = function
| RString -> f
| RStruct x -> f0 x
| RArray x -> f1 x
| RFun (x, x0) -> f2 x x0

(** val rty_rec :
    'a1 -> (id -> 'a1) -> (ty -> 'a1) -> (ty list -> ret_ty -> 'a1) -> rty ->
    'a1 **)

let rty_rec f f0 f1 f2 = function
| RString -> f
| RStruct x -> f0 x
| RArray x -> f1 x
| RFun (x, x0) -> f2 x x0

(** val ret_ty_rect : 'a1 -> (ty -> 'a1) -> ret_ty -> 'a1 **)

let ret_ty_rect f f0 = function
| RetVoid -> f
| RetVal x -> f0 x

(** val ret_ty_rec : 'a1 -> (ty -> 'a1) -> ret_ty -> 'a1 **)

let ret_ty_rec f f0 = function
| RetVoid -> f
| RetVal x -> f0 x

type unop =
| Neg
| Lognot
| Bitnot

(** val unop_rect : 'a1 -> 'a1 -> 'a1 -> unop -> 'a1 **)

let unop_rect f f0 f1 = function
| Neg -> f
| Lognot -> f0
| Bitnot -> f1

(** val unop_rec : 'a1 -> 'a1 -> 'a1 -> unop -> 'a1 **)

let unop_rec f f0 f1 = function
| Neg -> f
| Lognot -> f0
| Bitnot -> f1

type binop =
| Add
| Sub
| Mul
| Eq
| Neq
| Lt
| Lte
| Gt
| Gte
| And
| Or
| IAnd
| IOr
| Shl
| Shr
| Sar

(** val binop_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> binop -> 'a1 **)

let binop_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 = function
| Add -> f
| Sub -> f0
| Mul -> f1
| Eq -> f2
| Neq -> f3
| Lt -> f4
| Lte -> f5
| Gt -> f6
| Gte -> f7
| And -> f8
| Or -> f9
| IAnd -> f10
| IOr -> f11
| Shl -> f12
| Shr -> f13
| Sar -> f14

(** val binop_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> binop -> 'a1 **)

let binop_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 = function
| Add -> f
| Sub -> f0
| Mul -> f1
| Eq -> f2
| Neq -> f3
| Lt -> f4
| Lte -> f5
| Gt -> f6
| Gte -> f7
| And -> f8
| Or -> f9
| IAnd -> f10
| IOr -> f11
| Shl -> f12
| Shr -> f13
| Sar -> f14

type exp =
| CBool of bool
| CInt of int64
| CStr of char list
| Bop of binop * exp node * exp node
| Uop of unop * exp node
| Id of id
| Call of exp node * exp node list
| CNull of rty
| CArr of ty * exp node list
| CStruct of id * (id * exp node) list
| Proj of exp node * id
| NewArr of ty * exp node
| Index of exp node * exp node
| Length of exp node

(** val exp_rect :
    (bool -> 'a1) -> (int64 -> 'a1) -> (char list -> 'a1) -> (binop -> exp
    node -> exp node -> 'a1) -> (unop -> exp node -> 'a1) -> (id -> 'a1) ->
    (exp node -> exp node list -> 'a1) -> (rty -> 'a1) -> (ty -> exp node
    list -> 'a1) -> (id -> (id * exp node) list -> 'a1) -> (exp node -> id ->
    'a1) -> (ty -> exp node -> 'a1) -> (exp node -> exp node -> 'a1) -> (exp
    node -> 'a1) -> exp -> 'a1 **)

let exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 = function
| CBool x -> f x
| CInt x -> f0 x
| CStr x -> f1 x
| Bop (x, x0, x1) -> f2 x x0 x1
| Uop (x, x0) -> f3 x x0
| Id x -> f4 x
| Call (x, x0) -> f5 x x0
| CNull x -> f6 x
| CArr (x, x0) -> f7 x x0
| CStruct (x, x0) -> f8 x x0
| Proj (x, x0) -> f9 x x0
| NewArr (x, x0) -> f10 x x0
| Index (x, x0) -> f11 x x0
| Length x -> f12 x

(** val exp_rec :
    (bool -> 'a1) -> (int64 -> 'a1) -> (char list -> 'a1) -> (binop -> exp
    node -> exp node -> 'a1) -> (unop -> exp node -> 'a1) -> (id -> 'a1) ->
    (exp node -> exp node list -> 'a1) -> (rty -> 'a1) -> (ty -> exp node
    list -> 'a1) -> (id -> (id * exp node) list -> 'a1) -> (exp node -> id ->
    'a1) -> (ty -> exp node -> 'a1) -> (exp node -> exp node -> 'a1) -> (exp
    node -> 'a1) -> exp -> 'a1 **)

let exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 = function
| CBool x -> f x
| CInt x -> f0 x
| CStr x -> f1 x
| Bop (x, x0, x1) -> f2 x x0 x1
| Uop (x, x0) -> f3 x x0
| Id x -> f4 x
| Call (x, x0) -> f5 x x0
| CNull x -> f6 x
| CArr (x, x0) -> f7 x x0
| CStruct (x, x0) -> f8 x x0
| Proj (x, x0) -> f9 x x0
| NewArr (x, x0) -> f10 x x0
| Index (x, x0) -> f11 x x0
| Length x -> f12 x

type cfield = id * exp node

type vdecl = id * exp node

type stmt =
| Assn of exp node * exp node
| Decl of vdecl
| Return of exp node option
| If of exp node * stmt node list * stmt node list
| While of exp node * stmt node list
| SCall of exp node * exp node list
| For of vdecl list * exp node option * stmt node option * stmt node list
| Cast of rty * id * exp node * stmt node list * stmt node list

(** val stmt_rect :
    (exp node -> exp node -> 'a1) -> (vdecl -> 'a1) -> (exp node option ->
    'a1) -> (exp node -> stmt node list -> stmt node list -> 'a1) -> (exp
    node -> stmt node list -> 'a1) -> (exp node -> exp node list -> 'a1) ->
    (vdecl list -> exp node option -> stmt node option -> stmt node list ->
    'a1) -> (rty -> id -> exp node -> stmt node list -> stmt node list ->
    'a1) -> stmt -> 'a1 **)

let stmt_rect f f0 f1 f2 f3 f4 f5 f6 = function
| Assn (x, x0) -> f x x0
| Decl x -> f0 x
| Return x -> f1 x
| If (x, x0, x1) -> f2 x x0 x1
| While (x, x0) -> f3 x x0
| SCall (x, x0) -> f4 x x0
| For (x, x0, x1, x2) -> f5 x x0 x1 x2
| Cast (x, x0, x1, x2, x3) -> f6 x x0 x1 x2 x3

(** val stmt_rec :
    (exp node -> exp node -> 'a1) -> (vdecl -> 'a1) -> (exp node option ->
    'a1) -> (exp node -> stmt node list -> stmt node list -> 'a1) -> (exp
    node -> stmt node list -> 'a1) -> (exp node -> exp node list -> 'a1) ->
    (vdecl list -> exp node option -> stmt node option -> stmt node list ->
    'a1) -> (rty -> id -> exp node -> stmt node list -> stmt node list ->
    'a1) -> stmt -> 'a1 **)

let stmt_rec f f0 f1 f2 f3 f4 f5 f6 = function
| Assn (x, x0) -> f x x0
| Decl x -> f0 x
| Return x -> f1 x
| If (x, x0, x1) -> f2 x x0 x1
| While (x, x0) -> f3 x x0
| SCall (x, x0) -> f4 x x0
| For (x, x0, x1, x2) -> f5 x x0 x1 x2
| Cast (x, x0, x1, x2, x3) -> f6 x x0 x1 x2 x3

type block = stmt node list

type gdecl = { name : id; init : exp node }

(** val name : gdecl -> id **)

let name g =
  g.name

(** val init : gdecl -> exp node **)

let init g =
  g.init

type fdecl = { frtyp : ret_ty; fname : id; args : (ty * id) list; body : block }

(** val frtyp : fdecl -> ret_ty **)

let frtyp f =
  f.frtyp

(** val fname : fdecl -> id **)

let fname f =
  f.fname

(** val args : fdecl -> (ty * id) list **)

let args f =
  f.args

(** val body : fdecl -> block **)

let body f =
  f.body

type field = { fieldName : id; ftyp : ty }

(** val fieldName : field -> id **)

let fieldName f =
  f.fieldName

(** val ftyp : field -> ty **)

let ftyp f =
  f.ftyp

type tdecl = id * field list

type decl =
| Gfdecl of fdecl node
| Gvdecl of gdecl node
| Gtdecl of tdecl node

(** val decl_rect :
    (fdecl node -> 'a1) -> (gdecl node -> 'a1) -> (tdecl node -> 'a1) -> decl
    -> 'a1 **)

let decl_rect f f0 f1 = function
| Gfdecl x -> f x
| Gvdecl x -> f0 x
| Gtdecl x -> f1 x

(** val decl_rec :
    (fdecl node -> 'a1) -> (gdecl node -> 'a1) -> (tdecl node -> 'a1) -> decl
    -> 'a1 **)

let decl_rec f f0 f1 = function
| Gfdecl x -> f x
| Gvdecl x -> f0 x
| Gtdecl x -> f1 x

type prog = decl list
