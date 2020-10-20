Require Import String ZArith.
Open Scope string_scope.
Require Import Ascii.
Require Import Basics.
Require Import List.

Require Import Integers.

Module Int64 := Integers.Int64.
Definition int64 := Int64.int.

Export ListNotations.

Open Scope list_scope.
Open Scope nat.
Open Scope program_scope.
(* VV|TODO: This is col_start, col_end, line_start, line_end and a string???  *)
Definition t := (string * (Z * Z) * (Z * Z))%type.
(* This is no_loc right? *)
Definition norange := ("__internal", (0%Z,0%Z), (0%Z,0%Z)).

(* An AST node wraps decorates a datatype with its location in the source
   program. We attach source locations to expressions, statments, and
   top-level definitions to provide better error messages *)

(* Extract node as this: 
Definition node (A:Type) := A.
*)
(* VV| node type - *)
Record node (A:Type) := mkNode { elt : A ; loc : t }.


Definition elt_of {A} (n:node A) : A :=
  match n with
  | {| elt := a; loc := _ |} => a
  end.

Definition no_loc {A} (x:A) := mkNode A x norange.

(* OAT identifiers *)
Definition id := string.

(* OAT types *)
Inductive ty :=                                    (* types of identifiers and exprs *)
| TBool : ty 
| TInt : ty
| TRef : rty -> ty
| TNotNullRef : rty -> ty

with rty :=                                        (* reference types *)
| RString : rty
| RStruct : id -> rty
| RArray : ty -> rty 
| RFun : (list ty) -> ret_ty -> rty
                
with ret_ty :=
| RetVoid : ret_ty
| RetVal : ty -> ret_ty.

(* Expressions *)
Inductive unop :=                             (* primitive operations *)
  | Neg | Lognot | Bitnot.
(* Derive (Arbitrary, Show) for unop. *)

Inductive binop :=
  | Add | Sub | Mul
  | Eq | Neq
  | Lt | Lte | Gt | Gte
  | And | Or | IAnd | IOr
  | Shl | Shr | Sar
. 
(* Derive (Arbitrary, Show) for binop. *)

Inductive exp :=
  | CBool : bool -> exp                      (* bool literal *)
  | CInt : int64 -> exp                       (* int64 literal *)
  | CStr : string -> exp                     (* string literal *)
  | Bop : binop -> node exp -> node exp -> exp (* operations of two arguments *)
  | Uop : unop -> node exp -> exp             (* operations with one argument *)
  | Id : id -> exp                           (* identifiers *)
  | Call : node exp -> (list (node exp)) -> exp   (* function call - change to exp later *)
.
 (*
  | CNull : ty -> exp                         (* null literal for any TRef *)
  | CArr : ty -> (list (node exp)) -> exp          (* array literal *)
  | CStruct : id -> list (id * node exp) -> exp        (* struct literal *)
  | Proj : node exp -> id -> exp              (* projection from a struct *)
  | NewArr : ty -> node exp -> exp            (* zero-initialized arrays *)
  | Index : node exp -> node exp -> exp       (* index into an array *)
  | Length : node exp -> exp.
*)
Definition cfield := (id * node exp)%type.

Definition vdecl := (id * node exp)%type.              (* local variable declaration *)

(* statements *)
Inductive stmt :=
  | Assn : node exp -> node exp -> stmt         (* assignment *)
  | Decl : vdecl -> stmt                       (* local variable declaration *)
  | Return : option (node exp) -> stmt              (* return a value or void *)
  | If : node exp -> list (node stmt) -> list (node stmt) -> stmt      (* conditional *)
  | While : node exp -> list (node stmt) -> stmt           (* while loop *)
  | SCall : node exp -> list (node exp) -> stmt   (* call a void function - change to exp later*)
  .
  
(*
  | Cast : ty -> id -> (node exp) -> list (node stmt) -> list (node stmt) -> stmt
  | For : list vdecl -> option (node exp) (* for loop *)
           -> option (node stmt) -> list (node stmt) -> stmt
*)


(* blocks : statements *)
Definition block := list (node stmt).

(* global variable declarations *)
Record gdecl := mkGdecl
  { name : id
  ; init : node exp
  }.

(* global function declarations *)
Record fdecl := mkFdecl
  { frtyp : ret_ty
  ; fname : id
  ; args : list (ty * id)
  ; body : block
  }.

Record field := mkField
  {
    fieldName : id
  ; ftyp : ty
  }.

Definition tdecl := (id * (list field))%type.

(* OAT programs *)
Inductive decl :=
  | Gfdecl : node fdecl -> decl
  | Gvdecl : node gdecl -> decl
  | Gtdecl : node tdecl -> decl.

Definition fdecl' := (id * fdecl)%type.
Definition prog := list fdecl'.

