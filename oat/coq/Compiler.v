Require Import LL.
From Coq Require Import List String Init.Datatypes Program.Basics.
Local Open Scope string_scope.
Local Open Scope program_scope.
Local Open Scope list_scope.

(** Flattened representation of LLVM programs *)
Variant elt : Type :=
| L (lbl: LL.lbl) (* block labels *)
| I (uid: uid) (instr: LL.insn) (* instruction *)
| T (term: LL.terminator) (* block terminators *)
| G (gid: LL.gid) (gdecl: LL.gdecl) (* hoisted globals (usually strings) *)
| E (uid: LL.uid) (instr: LL.insn) (* hoisted entry block instructions *)
.

About app.
Definition stream : Type := list elt.

Notation "x >@ y" := (y ++ x)
                     (at level 50, left associativity).
Notation "x >:: y" := (cons y x)
                        ( at level 50, left associativity).

Definition lift (instrs: list ((uid * LL.insn)%type) ) : stream :=
  List.rev (List.map (fun t => I (fst t) (snd t)) instrs).

Set Implicit Arguments.
Set Contextual Implicit.
Definition bound {A} (l1 l2 l3 : list A) (e1 : A) : list A :=
  l1 >@ l2 >@ l3 >:: e1.          



(* compiling OAT types --------------------------------------------- *)
Require Import AST.

Fixpoint cmp_ty (t: AST.ty) : LL.ty :=
  match t with
  | AST.TBool => LL.I1
  | AST.TInt  => LL.I64
  | AST.TRef rty => LL.Ptr (cmp_rty rty)
  | _ => LL.I1
  end

with cmp_rty (rty : AST.rty) : LL.ty :=  
       match rty with
       | AST.RString => LL.I8
       | AST.RArray u => LL.Struct [LL.I64; LL.Array 0 (cmp_ty u)]
       | _ => LL.I1
       end.
