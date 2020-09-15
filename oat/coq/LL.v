Require Import Extraction.
Require Import List.
Require Import String.
Require Import ZArith.
Require Import extraction.ExtrOcamlNatInt.
Require Import extraction.ExtrOcamlString.

Import ListNotations.

Definition int64 := Z.

Open Scope type_scope.

(* LLVMlite: A simplified subset of the LLVM IR *)

Definition uid := string.       (* Local identifiers  *)
Definition gid := string.       (* Global identifiers *)
Definition tid := string.       (* Named types        *)
Definition lbl := string.       (* Labels             *)

(* Types of SSA temporaries *)
Inductive ty :=
| Void | I1 | I8 | I64
| Ptr    : ty -> ty
| Struct : list ty -> ty
| Array  : nat -> ty -> ty
| Fun    : list ty -> ty -> ty
| Namedt : tid -> ty.

(* Function type: argument types and return type *)
Definition fty := list ty * ty.

(* Syntactic Values *)
Inductive operand :=
  Null  : operand               (* null pointer        *)
| Const : int64 -> operand       (* integer constant    *)
| Gid   : gid -> operand         (* A global identifier *)
| Id    : uid -> operand.        (* A local identifier  *)

(* Type-annotated operands *)

(* Binary operations *)
Inductive bop := Add | Sub | Mul | Shl | Lshr | Ashr | And | Or | Xor.

(* Comparison Operators *)
Inductive cnd := Eq | Ne | Slt | Sle | Sgt | Sge.

Inductive insn :=
  Binop   : bop -> ty -> operand -> operand -> insn       (* bop ty %o1, %o2                    *)
| Alloca  : ty -> insn                                 (* alloca ty                          *)
| Load    : ty -> operand -> insn                       (* load ty %u                         *)
| Store   : ty -> operand -> operand -> insn             (* store ty %t, ty* %u                *)
| Icmp    : cnd -> ty -> operand -> operand -> insn       (* icmp %s ty %s, %s                  *)
| Call    : ty -> operand -> list (ty * operand) -> insn (* fn(%1, %2, ...)                    *)
| Bitcast : ty -> operand -> ty -> insn                  (* bitcast ty1 %u to ty2              *)
| Gep     : ty -> operand -> list operand -> insn.       (* getelementptr ty* %u, i64 %vi, ... *)

(* Block terminators *)
Inductive terminator :=
  Ret : ty -> option operand -> terminator  (* ret i64 %s                     *)
| Br  : lbl -> terminator                  (* br label %lbl                  *)
| Cbr : operand -> lbl -> lbl -> terminator. (* br i1 %s, label %l1, label %l2 *)

(* Basic blocks *)
Record block := mkBlock {
                    insns : list (uid * insn);
                    term  : uid * terminator }.

(* Control Flow Graph: a pair of an entry block and a set labeled blocks *)
Definition cfg := block * list (lbl * block).

(* Function declarations *)
Record fdecl := mkfdecl
  { f_ty    : fty
  ; f_param : list uid
  ; f_cfg   : cfg
  }.

(* Initializers for global data *)
Inductive ginit :=
  GNull                                (* null literal             *)
| GGid    : gid -> ginit                (* reference another global *)
| GInt    : int64 -> ginit              (* global integer value     *)
| GString : string -> ginit             (* constant global string   *)
| GArray  : list (ty * ginit) -> ginit  (* global array             *)
| GStruct : list (ty * ginit) -> ginit. (* global struct            *)

(* Global declaration *)
Definition gdecl := ty * ginit.

(* LLVMlite programs *)
Record prog := mkProg
  { tdecls : list (tid * ty)    (* named types *)
  ; gdecls : list (gid * gdecl) (* global data *)
  ; fdecls : list (gid * fdecl) (* code        *)
  ; edecls : list (gid * ty)    (* external declarations *)
  }.

Extract Inlined Constant int64 => "int64".
Extract Inductive positive => "int64" [ "(fun x -> Int64.succ (Int64.shift_left x 1))"
                                       "(fun x -> Int64.shift_left x 1)"
                                       "Int64.one" ].
Extract Inductive Z => "int64" [ "Int64.zero" "(fun x -> x)" "Int64.neg" ].

Extract Inductive string => "string" [ """""" "(fun (h,t) -> (String.make 1 h) ^ t)" ].

Extraction "ll.ml" prog.
