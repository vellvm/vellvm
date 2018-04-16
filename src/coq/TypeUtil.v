Require Import List String.
Require Import Vellvm.Util.
Require Import Vellvm.LLVMAst.
Require Import Vellvm.Classes.
Require Import Coqlib.

Import ListNotations.
Open Scope list_scope.


Definition eqb_raw_id (a : raw_id) (b : raw_id) : bool :=
  match a with
  | Name s => match b with
             | Name s2 => proj_sumbool (string_dec s s2)
             | _ => false
             end
  | Anon n => match b with
             | Anon n2 => Z.eqb n n2
             | _ => false
             end
  | Raw n => match b with
            | Raw n2 => Z.eqb n n2
            | _ => false
            end
  end.


Definition eqb_ident (a : ident) (b : ident) : bool :=
  match a with
  | ID_Global id_l => match b with
                     | ID_Global id_r => eqb_raw_id id_l id_r
                     | _ => false
                     end
  | ID_Local id_l => match b with
                    | ID_Local id_r => eqb_raw_id id_l id_r
                    | _ => false
                    end
  end.


Fixpoint normalize_type (fuel : nat) (typ_defs : list (ident * typ)) (t : typ) : option typ :=
  match fuel, t with
  | 0%nat, _ => None

  | S fuel', TYPE_Pointer t =>
      Some (TYPE_Pointer t)

  | S fuel', TYPE_Array sz t =>
      'nt <- normalize_type fuel' typ_defs t;
      Some (TYPE_Array sz nt)

  | S fuel', TYPE_Function ret args =>
      'nret <- (normalize_type fuel' typ_defs ret);
      'nargs <- (map_monad (normalize_type fuel' typ_defs) args);
      Some (TYPE_Function nret nargs)

  | S fuel', TYPE_Struct fields =>
      'nfields <- (map_monad (normalize_type fuel' typ_defs) fields);
      Some (TYPE_Struct nfields)

  | S fuel', TYPE_Packed_struct fields =>
      'nfields <- (map_monad (normalize_type fuel' typ_defs) fields);
      Some (TYPE_Packed_struct nfields)

  | S fuel', TYPE_Vector sz t =>
      'nt <- normalize_type fuel' typ_defs t;
      Some (TYPE_Vector sz nt)

  | S fuel', TYPE_Identified id =>
      '(_, t) <- find (fun a => eqb_ident id (fst a)) typ_defs;
      'nt <- normalize_type fuel' typ_defs t;
      Some nt

  | S fuel', _ => Some t
  end.


(* Inductive predicate for types in LLVM with a size *)
Inductive sized_typ : list (ident * typ) -> typ -> Prop :=
| sized_typ_I :
    forall (defs : list (ident * typ)) (sz : int),
      sized_typ defs (TYPE_I sz)

| sized_typ_Pointer :
    forall (defs : list (ident * typ)) (t : typ),
      sized_typ defs (TYPE_Pointer t)

| sized_typ_Half :
    forall (defs : list (ident * typ)),
      sized_typ defs TYPE_Half

| sized_typ_Float :
    forall (defs : list (ident * typ)),
      sized_typ defs TYPE_Float

| sized_typ_Double :
    forall (defs : list (ident * typ)),
      sized_typ defs TYPE_Double

| sized_typ_X86_fp80 :
    forall (defs : list (ident * typ)),
      sized_typ defs TYPE_X86_fp80

| sized_typ_Fp128 :
    forall (defs : list (ident * typ)),
      sized_typ defs TYPE_Fp128

| sized_typ_Ppc_fp128 :
    forall (defs : list (ident * typ)),
      sized_typ defs TYPE_Ppc_fp128

| sized_typ_Metadata :
    forall (defs : list (ident * typ)),
      sized_typ defs TYPE_Metadata

| sized_typ_X86_mmx :
    forall (defs : list (ident * typ)),
      sized_typ defs TYPE_X86_mmx

| sized_typ_Array :
    forall (defs : list (ident * typ)) (sz : int) (t : typ),
      sized_typ defs t -> sized_typ defs (TYPE_Array sz t)

| sized_typ_Struct :
    forall (defs : list (ident * typ)) (fields : list typ),
      (forall (f : typ), In f fields -> sized_typ defs f) -> sized_typ defs (TYPE_Struct fields)

| sized_typ_Packed_struct :
    forall (defs : list (ident * typ)) (fields : list typ),
      (forall (f : typ), In f fields -> sized_typ defs f) -> sized_typ defs (TYPE_Packed_struct fields)

| sized_typ_Vector :
    forall (defs : list (ident * typ)) (sz : int) (t : typ),
      sized_typ defs t -> sized_typ defs (TYPE_Vector sz t)

| sized_typ_Identified :
    forall (defs : list (ident * typ)) (id : ident),
      (exists (t : typ), In (id, t) defs -> sized_typ defs t) -> sized_typ defs (TYPE_Identified id)
.


(* Inductive predicate for types in LLVM that can be elements of vectors.

   "elementtype" may be any integer, floating-point or pointer type.

   https://llvm.org/docs/LangRef.html#vector-type *)
Inductive element_typ : typ -> Prop :=
| element_typ_Pointer : forall (t : typ), element_typ (TYPE_Pointer t)
| element_typ_I : forall (sz : int), element_typ (TYPE_I sz)
| element_typ_Half : element_typ TYPE_Half
| element_typ_Float : element_typ TYPE_Float
| element_typ_Double : element_typ TYPE_Double
| element_typ_X86_fp80 : element_typ TYPE_X86_fp80
| element_typ_Fp128 : element_typ TYPE_Fp128
| element_typ_Ppc_fp128 : element_typ TYPE_Ppc_fp128
.
  

(* Predicate to ensure that an ident is guarded by a pointer everywhere in a type in an environment *)
Inductive guarded_typ : ident -> list (ident * typ) -> typ -> Prop :=
| guarded_typ_I :
    forall (id : ident) (env : list (ident * typ)) (sz : int),
      guarded_typ id env (TYPE_I sz)

| guarded_typ_Pointer :
    forall (id : ident) (env : list (ident * typ)) (t : typ),
      guarded_typ id env (TYPE_Pointer t)

| guarded_typ_Void :
    forall (id : ident) (env : list (ident * typ)),
      guarded_typ id env TYPE_Void

| guarded_typ_Half :
    forall (id : ident) (env : list (ident * typ)),
      guarded_typ id env TYPE_Half

| guarded_typ_Float :
    forall (id : ident) (env : list (ident * typ)),
      guarded_typ id env TYPE_Float

| guarded_typ_Double :
    forall (id : ident) (env : list (ident * typ)),
      guarded_typ id env TYPE_Double

| guarded_typ_X86_fp80 :
    forall (id : ident) (env : list (ident * typ)),
      guarded_typ id env TYPE_X86_fp80

| guarded_typ_Fp128 :
    forall (id : ident) (env : list (ident * typ)),
      guarded_typ id env TYPE_Fp128

| guarded_typ_Ppc_fp128 :
    forall (id : ident) (env : list (ident * typ)),
      guarded_typ id env TYPE_Ppc_fp128

| guarded_typ_Metadata :
    forall (id : ident) (env : list (ident * typ)),
      guarded_typ id env TYPE_Metadata

| guarded_typ_X86_mmx :
    forall (id : ident) (env : list (ident * typ)),
      guarded_typ id env TYPE_X86_mmx

| guarded_typ_Array :
    forall (id : ident) (env : list (ident * typ)) (sz : int) (t : typ),
      guarded_typ id env t -> guarded_typ id env (TYPE_Array sz t)

| guarded_typ_Struct :
    forall (id : ident) (env : list (ident * typ)) (t : typ) (fields : list typ),
      (forall f, In f fields -> guarded_typ id env f) ->
      guarded_typ id env (TYPE_Struct fields)

| guarded_typ_Packed_struct :
    forall (id : ident) (env : list (ident * typ)) (t : typ) (fields : list typ),
      (forall f, In f fields -> guarded_typ id env f) ->
      guarded_typ id env (TYPE_Struct fields)

| guarded_typ_Opaque :
    forall (id : ident) (env : list (ident * typ)),
      guarded_typ id env TYPE_Opaque

| guarded_typ_Vector :
    forall (id : ident) (env : list (ident * typ)) (sz : int) (t : typ),
      guarded_typ id env (TYPE_Vector sz t)

| guarded_typ_Identified_Some :
    forall (id : ident) (env : list (ident * typ)) (id' : ident) (t : typ),
      id <> id' ->
      Some (id', t) = find (fun a => eqb_ident id' (fst a)) env ->
      guarded_typ id env t ->
      guarded_typ id' env t ->
      guarded_typ id env (TYPE_Identified id')

| guarded_typ_Identified_None :
    forall (id : ident) (env : list (ident * typ)) (id' : ident),
      id <> id' ->
      None = find (fun a => eqb_ident id' (fst a)) env ->
      guarded_typ id env (TYPE_Identified id')
.


(* Inductive predicate for well-formed LLVM types.

   wf_typ env t

   means that 't' is a well-formed type in the environment 'env'. The
   environment just associates identifiers to types, so this contains
   things like user-defined structure types.

   well-formed LLVM types should cover every valid type in LLVM.

   Examples of invalid types:

   - Vectors of size 0
   - Arrays with unsized elements
   - Recursive structures (must be guarded by a pointer) *)
Inductive wf_typ : list (ident * typ) -> typ -> Prop :=
| wf_typ_Pointer:
    forall (defs : list (ident * typ)) (t : typ),
      wf_typ defs t -> wf_typ defs (TYPE_Pointer t)

| wf_typ_I :
    forall (defs : list (ident * typ)) (sz : int),
      sz > 0 -> wf_typ defs (TYPE_I sz)

| wf_typ_Void :
    forall (defs : list (ident * typ)),
      wf_typ defs TYPE_Void

| wf_typ_Half :
    forall (defs : list (ident * typ)),
      wf_typ defs TYPE_Half

| wf_typ_Float :
    forall (defs : list (ident * typ)),
      wf_typ defs TYPE_Float

| wf_typ_Double :
    forall (defs : list (ident * typ)),
      wf_typ defs TYPE_Double

| wf_typ_X86_fp80 :
    forall (defs : list (ident * typ)),
      wf_typ defs TYPE_X86_fp80

| wf_typ_Fp128 :
    forall (defs : list (ident * typ)),
      wf_typ defs TYPE_Fp128

| wf_typ_Ppc_fp128 :
    forall (defs : list (ident * typ)),
      wf_typ defs TYPE_Ppc_fp128

| wf_typ_Metadata :
    forall (defs : list (ident * typ)),
      wf_typ defs TYPE_Metadata

| wf_typ_X86_mmx :
    forall (defs : list (ident * typ)),
      wf_typ defs TYPE_X86_mmx

(* Arrays are only well formed if the size is >= 0, and the element type is sized. *)
| wf_typ_Array :
    forall (defs : list (ident * typ)) (sz : int) (t : typ),
      sz >= 0 -> sized_typ defs t -> wf_typ defs t -> wf_typ defs (TYPE_Array sz t)

(* Vectors of size 0 are not allowed, and elemnts must be of element_typ. *)
| wf_typ_Vector :
    forall (defs : list (ident * typ)) (sz : int) (t : typ),
      sz > 0 -> element_typ t -> wf_typ defs t -> wf_typ defs (TYPE_Vector sz t)

(* Any type identifier must exist in the environment.

   Additionally the identifier must not occur anywhere in the type
   that it refers to *unless* it is guarded by a pointer. *)
| wf_typ_Identified :
    forall (defs : list (ident * typ)) (id : ident),
      (exists (t : typ), In (id, t) defs -> guarded_typ id defs t -> wf_typ defs t) ->
      wf_typ defs (TYPE_Identified id)

(* Fields of structure must be sized types *)
| wf_typ_Struct :
    forall (defs : list (ident * typ)) (fields : list typ),
      (forall (f : typ), In f fields -> sized_typ defs f -> wf_typ defs f) ->
      wf_typ defs (TYPE_Struct fields)

| wf_typ_Packed_struct :
    forall (defs : list (ident * typ)) (fields : list typ),
      (forall (f : typ), In f fields -> sized_typ defs f -> wf_typ defs f) ->
      wf_typ defs (TYPE_Packed_struct fields)

| wf_typ_Opaque :
    forall (defs : list (ident * typ)),
      wf_typ defs TYPE_Opaque
.
