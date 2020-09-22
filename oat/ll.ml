
type uid = string

type gid = string

type tid = string

type lbl = string

type ty =
| Void
| I1
| I8
| I64
| Ptr of ty
| Struct of ty list
| Array of int * ty
| Fun of ty list * ty
| Namedt of tid

type fty = ty list * ty

type operand =
| Null
| Const of int64
| Gid of gid
| Id of uid

type bop =
| Add
| Sub
| Mul
| Shl
| Lshr
| Ashr
| And
| Or
| Xor

type cnd =
| Eq
| Ne
| Slt
| Sle
| Sgt
| Sge

type insn =
| Binop of bop * ty * operand * operand
| Alloca of ty
| Load of ty * operand
| Store of ty * operand * operand
| Icmp of cnd * ty * operand * operand
| Call of ty * operand * (ty * operand) list
| Bitcast of ty * operand * ty
| Gep of ty * operand * operand list

type terminator =
| Ret of ty * operand option
| Br of lbl
| Cbr of operand * lbl * lbl

type block = { insns : (uid * insn) list; term : (uid * terminator) }

type cfg = block * (lbl * block) list

type fdecl = { f_ty : fty; f_param : uid list; f_cfg : cfg }

type ginit =
| GNull
| GGid of gid
| GInt of int64
| GString of string
| GArray of (ty * ginit) list
| GStruct of (ty * ginit) list

type gdecl = ty * ginit

type prog = { tdecls : (tid * ty) list; gdecls : (gid * gdecl) list;
              fdecls : (gid * fdecl) list; edecls : (gid * ty) list }
