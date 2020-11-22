open BinNums
open Datatypes
open Integers

module Int64 :
 sig
  val wordsize : nat

  val zwordsize : coq_Z

  val modulus : coq_Z

  val half_modulus : coq_Z

  val max_unsigned : coq_Z

  val max_signed : coq_Z

  val min_signed : coq_Z

  type int = coq_Z
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> coq_Z

  val coq_P_mod_two_p : positive -> nat -> coq_Z

  val coq_Z_mod_modulus : coq_Z -> coq_Z

  val unsigned : int -> coq_Z

  val signed : int -> coq_Z

  val repr : coq_Z -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val coq_Zshiftin : bool -> coq_Z -> coq_Z

  val coq_Zzero_ext : coq_Z -> coq_Z -> coq_Z

  val coq_Zsign_ext : coq_Z -> coq_Z -> coq_Z

  val zero_ext : coq_Z -> int -> int

  val sign_ext : coq_Z -> int -> int

  val coq_Z_one_bits : nat -> coq_Z -> coq_Z -> coq_Z list

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison -> int -> int -> bool

  val cmpu : comparison -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int * int) option

  val divmods2 : int -> int -> int -> (int * int) option

  val testbit : int -> coq_Z -> bool

  val powerserie : coq_Z list -> coq_Z

  val int_of_one_bits : int list -> int

  val no_overlap : int -> coq_Z -> int -> coq_Z -> bool

  val coq_Zsize : coq_Z -> coq_Z

  val size : int -> coq_Z

  val iwordsize' : Int.int

  val shl' : int -> Int.int -> int

  val shru' : int -> Int.int -> int

  val shr' : int -> Int.int -> int

  val rol' : int -> Int.int -> int

  val shrx' : int -> Int.int -> int

  val shr_carry' : int -> Int.int -> int

  val one_bits' : int -> Int.int list

  val is_power2' : int -> Int.int option

  val int_of_one_bits' : Int.int list -> int

  val loword : int -> Int.int

  val hiword : int -> Int.int

  val ofwords : Int.int -> Int.int -> int

  val mul' : Int.int -> Int.int -> int
 end

type int64 = Int64.int

type t = (string * (int * int) * (int * int))

type 'a node = { elt : 'a; loc : t }

val elt : 'a1 node -> 'a1

val loc : 'a1 node -> t

val elt_of : 'a1 node -> 'a1

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

val ty_rect : 'a1 -> 'a1 -> (rty -> 'a1) -> (rty -> 'a1) -> ty -> 'a1

val ty_rec : 'a1 -> 'a1 -> (rty -> 'a1) -> (rty -> 'a1) -> ty -> 'a1

val rty_rect :
  'a1 -> (id -> 'a1) -> (ty -> 'a1) -> (ty list -> ret_ty -> 'a1) -> rty ->
  'a1

val rty_rec :
  'a1 -> (id -> 'a1) -> (ty -> 'a1) -> (ty list -> ret_ty -> 'a1) -> rty ->
  'a1

val ret_ty_rect : 'a1 -> (ty -> 'a1) -> ret_ty -> 'a1

val ret_ty_rec : 'a1 -> (ty -> 'a1) -> ret_ty -> 'a1

type unop =
| Neg
| Lognot
| Bitnot

val unop_rect : 'a1 -> 'a1 -> 'a1 -> unop -> 'a1

val unop_rec : 'a1 -> 'a1 -> 'a1 -> unop -> 'a1

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

val binop_rect :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> binop -> 'a1

val binop_rec :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> binop -> 'a1

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

val exp_rect :
  (bool -> 'a1) -> (int64 -> 'a1) -> (char list -> 'a1) -> (binop -> exp node
  -> exp node -> 'a1) -> (unop -> exp node -> 'a1) -> (id -> 'a1) -> (exp
  node -> exp node list -> 'a1) -> (rty -> 'a1) -> (ty -> exp node list ->
  'a1) -> (id -> (id * exp node) list -> 'a1) -> (exp node -> id -> 'a1) ->
  (ty -> exp node -> 'a1) -> (exp node -> exp node -> 'a1) -> (exp node ->
  'a1) -> exp -> 'a1

val exp_rec :
  (bool -> 'a1) -> (int64 -> 'a1) -> (char list -> 'a1) -> (binop -> exp node
  -> exp node -> 'a1) -> (unop -> exp node -> 'a1) -> (id -> 'a1) -> (exp
  node -> exp node list -> 'a1) -> (rty -> 'a1) -> (ty -> exp node list ->
  'a1) -> (id -> (id * exp node) list -> 'a1) -> (exp node -> id -> 'a1) ->
  (ty -> exp node -> 'a1) -> (exp node -> exp node -> 'a1) -> (exp node ->
  'a1) -> exp -> 'a1

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

val stmt_rect :
  (exp node -> exp node -> 'a1) -> (vdecl -> 'a1) -> (exp node option -> 'a1)
  -> (exp node -> stmt node list -> stmt node list -> 'a1) -> (exp node ->
  stmt node list -> 'a1) -> (exp node -> exp node list -> 'a1) -> (vdecl list
  -> exp node option -> stmt node option -> stmt node list -> 'a1) -> (rty ->
  id -> exp node -> stmt node list -> stmt node list -> 'a1) -> stmt -> 'a1

val stmt_rec :
  (exp node -> exp node -> 'a1) -> (vdecl -> 'a1) -> (exp node option -> 'a1)
  -> (exp node -> stmt node list -> stmt node list -> 'a1) -> (exp node ->
  stmt node list -> 'a1) -> (exp node -> exp node list -> 'a1) -> (vdecl list
  -> exp node option -> stmt node option -> stmt node list -> 'a1) -> (rty ->
  id -> exp node -> stmt node list -> stmt node list -> 'a1) -> stmt -> 'a1

type block = stmt node list

type gdecl = { name : id; init : exp node }

val name : gdecl -> id

val init : gdecl -> exp node

type fdecl = { frtyp : ret_ty; fname : id; args : (ty * id) list; body : block }

val frtyp : fdecl -> ret_ty

val fname : fdecl -> id

val args : fdecl -> (ty * id) list

val body : fdecl -> block

type field = { fieldName : id; ftyp : ty }

val fieldName : field -> id

val ftyp : field -> ty

type tdecl = id * field list

type decl =
| Gfdecl of fdecl node
| Gvdecl of gdecl node
| Gtdecl of tdecl node

val decl_rect :
  (fdecl node -> 'a1) -> (gdecl node -> 'a1) -> (tdecl node -> 'a1) -> decl
  -> 'a1

val decl_rec :
  (fdecl node -> 'a1) -> (gdecl node -> 'a1) -> (tdecl node -> 'a1) -> decl
  -> 'a1

type prog = decl list
