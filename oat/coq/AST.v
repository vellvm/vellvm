Require Import String ZArith.
Open Scope string_scope.
Require Import Ascii.
Require Import Basics.
Require Import List.
Export ListNotations.
Open Scope list_scope.
Open Scope nat.
Open Scope program_scope.

(*
SAZ: TODO - figure out how to add quickchick separately
From QuickChick Require Import QuickChick.
Export QcNotation.
Open Scope qc_scope.
*)

Definition t := (string * (Z * Z) * (Z * Z))%type.
Definition norange := ("__internal", (0%Z,0%Z), (0%Z,0%Z)).

(* An AST node wraps decorates a datatype with its location in the source
   program. We attach source locations to expressions, statments, and
   top-level definitions to provide better error messages *)

(* Extract node as this: 
Definition node (A:Type) := A.
*)
Record node (A:Type) := mkNode { elt : A ; loc : t }.


Definition elt_of {A} (n:node A) : A :=
  match n with
  | {| elt := a; loc := _ |} => a
  end.

Definition no_loc {A} (x:A) := mkNode A x norange.

(* OAT identifiers *)
Definition id := string.

(* Instance genId : Gen id := *)
(*   {| arbitrary := liftGen (String "x"%char ∘ show) (arbitrary : G nat) |}. *)

(* Parameter nat_of_string : id -> nat. *)
(* Instance shrinkId : Shrink string := *)
(*   {| shrink xn := *)
(*        match xn with *)
(*        | String x n => map (String x ∘ show) (shrink (nat_of_string n)) *)
(*        | _ => ["x"] *)
(*        end |}. *)

(* Derive (Arbitrary, Show) for node. *)

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
  | Eq | Neq | Lt | Lte | Gt | Gte
  | And | Or | IAnd | IOr
  | Shl | Shr | Sar.
(* Derive (Arbitrary, Show) for binop. *)

Inductive exp :=
  | CNull : ty -> exp                         (* null literal for any TRef *)
  | CBool : bool -> exp                      (* bool literal *)
  | CInt : Z -> exp                       (* int64 literal *)
  | CStr : string -> exp                     (* string literal *)
  | CArr : ty -> (list (node exp)) -> exp          (* array literal *)
  | CStruct : id -> list (id * node exp) -> exp        (* struct literal *)
  | Proj : node exp -> id -> exp              (* projection from a struct *)
  | NewArr : ty -> node exp -> exp            (* zero-initialized arrays *)
  | Id : id -> exp                           (* identifiers *)
  | Index : node exp -> node exp -> exp       (* index into an array *)
  | Call : node exp -> (list (node exp)) -> exp   (* function call - change to exp later *)
  | Bop : binop -> node exp -> node exp -> exp (* operations of two arguments *)
  | Uop : unop -> node exp -> exp             (* operations with one argument *)
  | Length : node exp -> exp.

Definition cfield := (id * node exp)%type.

Definition vdecl := (id * node exp)%type.              (* local variable declaration *)

(* statements *)
Inductive stmt :=
  | Assn : node exp -> node exp -> stmt         (* assignment *)
  | Decl : vdecl -> stmt                       (* local variable declaration *)
  | Return : option (node exp) -> stmt              (* return a value or void *)
  | SCall : node exp -> list (node exp) -> stmt   (* call a void function - change to exp later*)
  | If : node exp -> list (node stmt) -> list (node stmt) -> stmt      (* conditional *)
  | Cast : ty -> id -> (node exp) -> list (node stmt) -> list (node stmt) -> stmt
  | For : list vdecl -> option (node exp) (* for loop *)
           -> option (node stmt) -> list (node stmt) -> stmt
  | While : node exp -> list (node stmt) -> stmt.           (* while loop *)

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
  | Gvdecl : node gdecl -> decl
  | Gfdecl : node fdecl -> decl
  | Gtdecl : node tdecl -> decl.

Definition prog := list decl.

(* 
  QUICKCHICK STUFF -- OLD
 *)
(*
(* Instances *)
Fixpoint arbitraryTy (n : nat) : G ty :=
  match n with
  | 0 => oneOf [ret TBool; ret TInt]
  | S n =>
    oneOf
      [ ret TBool
      ; ret TInt
      ; liftGen TRef (arbitraryRty n)
      ; liftGen TNotNullRef (arbitraryRty n)
      ]
  end with
arbitraryRty (n : nat) : G rty :=
  match n with
  | 0 => oneOf [ret RString; liftGen RStruct arbitrary]
  | S n =>
    oneOf
      [ ret RString
      ; liftGen RStruct arbitrary
      ; liftGen RArray (arbitraryTy n)
      ; liftGen2 RFun (listOf (arbitraryTy n)) (arbitraryRetTy n)
      ]
  end with
arbitraryRetTy (n : nat) : G ret_ty :=
  match n with
  | 0 => ret RetVoid
  | S n => oneOf [ret RetVoid; liftGen RetVal (arbitraryTy n)]
  end.

Instance genSizedTy : GenSized ty :=
  {| arbitrarySized := arbitraryTy |}.
Instance genSizedRty : GenSized rty :=
  {| arbitrarySized := arbitraryRty |}.
Instance genSizedRetTy : GenSized ret_ty :=
  {| arbitrarySized := arbitraryRetTy |}.

Fixpoint shrink_ty (t : ty) : list ty :=
  match t with
  | TBool => []
  | TInt => [TBool]
  | TRef rt => TBool :: TInt :: map TRef (shrink_rty rt)
  | TNotNullRef rt => TBool :: TInt :: TRef rt :: map TNotNullRef (shrink_rty rt)
  end with
shrink_rty (rt : rty) : list rty :=
  match rt with
  | RString => []
  | RStruct i => RString :: map RStruct (shrink i)
  | RArray t => RString :: map RArray (shrink_ty t)
  | RFun ts rett => RString :: map (RFun ts) (shrink_ret_ty rett)
    (* LYS: Shrinking [ts] doesn't work: *)
    (* ++ map (fun ts' => RFun ts' rett) (shrinkListAux shrink_ty ts) *)
  end with
shrink_ret_ty (rett : ret_ty) : list ret_ty :=
  match rett with
  | RetVoid => []
  | RetVal t => RetVoid :: map RetVal (shrink_ty t)
  end.

Instance shrinkTy : Shrink ty :=
  {| shrink := shrink_ty |}.
Instance shrinkRty : Shrink rty :=
  {| shrink := shrink_rty |}.
Instance shrinkRetTy : Shrink ret_ty :=
  {| shrink := shrink_ret_ty |}.

Open Scope string_scope.

Fixpoint show_ty (t : ty) : string :=
  match t with
  | TBool => "bool"
  | TInt => "int"
  | TRef rt => show_rty rt ++ "?"
  | TNotNullRef rt => show_rty rt
  end with
show_rty (rt : rty) : string :=
  match rt with
  | RString => "string"
  | RStruct i => i
  | RArray t => show_ty t ++ "[]"
  | RFun ts rett => "(" (* ++ contents show_ty ts *) ++ ") -> "
                       ++ show_ret_ty rett
  end with
show_ret_ty (rett : ret_ty) : string :=
  match rett with
  | RetVoid => "void"
  | RetVal t => show_ty t
  end.

Instance showTy : Show ty :=
  {| show := show_ty |}.
Instance showRty : Show rty :=
  {| show := show_rty |}.
Instance showRetTy : Show ret_ty :=
  {| show := show_ret_ty |}.

Inductive exp' {exp : Type} :=
  CNull'    : ty     -> exp'
| CBool'    : bool      -> exp'
| CInt'     : Z      -> exp'
| CStr'     : string -> exp'
| CArr'     : ty -> list (node exp)      -> exp'
| CStruct'  : id -> list (id * node exp) -> exp'
| Proj'     : node exp -> id -> exp'
| NewArr'   : ty -> node exp -> exp'
| Id'       : id -> exp'
| Index'    : node exp -> node exp -> exp'
| Call'     : node exp -> list (node exp) -> exp'
| Bop'      : binop -> node exp -> node exp -> exp'
| Uop'      : unop  -> node exp -> exp'
| Length'   : node exp -> exp'.
Derive (Arbitrary, Show) for exp'.

Definition from_exp' (e' : @exp' exp) : exp :=
  match e' with
  | CNull'   t   => CNull   t
  | CBool'   b   => CBool   b
  | CInt'    z   => CInt    z
  | CStr'    s   => CStr    s
  | Id'      i   => Id      i
  | Length'  n   => Length  n
  | CArr'    t l => CArr    t l
  | CStruct' i l => CStruct i l
  | Proj'    n i => Proj    n i
  | NewArr'  t n => NewArr  t n
  | Index'   n m => Index   n m
  | Call'    n l => Call    n l
  | Uop'     u n => Uop     u n
  | Bop'   b n m => Bop   b n m
  end.

Definition to_exp' (e : exp) : @exp' exp :=
  match e with
  | CNull   t   => CNull'   t
  | CBool   b   => CBool'   b
  | CInt    z   => CInt'    z
  | CStr    s   => CStr'    s
  | Id      i   => Id'      i
  | Length  n   => Length'  n
  | CArr    t l => CArr'    t l
  | CStruct i l => CStruct' i l
  | Proj    n i => Proj'    n i
  | NewArr  t n => NewArr'  t n
  | Index   n m => Index'   n m
  | Call    n l => Call'    n l
  | Uop     u n => Uop'     u n
  | Bop   b n m => Bop'   b n m
  end.

Coercion from_exp' : exp' >-> exp.
Coercion to_exp'   : exp >-> exp'.

Instance genExp `{Gen exp'} : Gen exp :=
  {| arbitrary := liftGen from_exp' arbitrary |}.
Instance shrinkExp `{Shrink exp'} : Shrink exp :=
  {| shrink := map from_exp' ∘ shrink ∘ to_exp' |}.
Instance showExp `{Show exp'} : Show exp :=
  {| show := show ∘ to_exp' |}.
*)

