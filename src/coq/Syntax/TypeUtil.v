(** ** Normalization of types
    This file contains a lot of stuff related to the historical normalization of types performed as a pre-processing phase.
    The current version uses a notion of dynamic types instead and a conversion function [TypToDtyp.typ_to_dtyp].
    The content of this file is however likely to be useful for static analyses in the future.
*)

From Coq Require Import
     List
     String
     Logic.FunctionalExtensionality.

From Vellvm Require Import
     Syntax.LLVMAst
     Syntax.AstLib.

Require Import Coqlib.

Import ListNotations.
Open Scope list_scope.


Ltac contra :=
  try match goal with
  | [Heq : ?x = ?y, Hneq : ?y <> ?x |- _] => symmetry in Heq
  end; contradiction.


(* Inductive predicate for types in LLVM with a size *)
Inductive sized_typ : list (ident * typ) -> typ -> Prop :=
| sized_typ_I :
    forall (defs : list (ident * typ)) (sz : N),
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
    forall (defs : list (ident * typ)) (sz : N) (t : typ),
      sized_typ defs t -> sized_typ defs (TYPE_Array sz t)

| sized_typ_Struct :
    forall (defs : list (ident * typ)) (fields : list typ),
      (forall (f : typ), In f fields -> sized_typ defs f) -> sized_typ defs (TYPE_Struct fields)

| sized_typ_Packed_struct :
    forall (defs : list (ident * typ)) (fields : list typ),
      (forall (f : typ), In f fields -> sized_typ defs f) -> sized_typ defs (TYPE_Packed_struct fields)

| sized_typ_Vector :
    forall (defs : list (ident * typ)) (sz : N) (t : typ),
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
| element_typ_I : forall (sz : N), element_typ (TYPE_I sz)
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
    forall (id : ident) (env : list (ident * typ)) (sz : N),
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

| guarded_typ_Function :
    forall (id : ident) (env : list (ident * typ)) (ret : typ) (args : list typ) (varargs:bool),
      guarded_typ id env ret ->
      (forall a, In a args -> guarded_typ id env a) ->
      guarded_typ id env (TYPE_Function ret args varargs)

| guarded_typ_Array :
    forall (id : ident) (env : list (ident * typ)) (sz : N) (t : typ),
      guarded_typ id env t -> guarded_typ id env (TYPE_Array sz t)

| guarded_typ_Struct :
    forall (id : ident) (env : list (ident * typ)) (t : typ) (fields : list typ),
      (forall f, In f fields -> guarded_typ id env f) ->
      guarded_typ id env (TYPE_Struct fields)

| guarded_typ_Packed_struct :
    forall (id : ident) (env : list (ident * typ)) (t : typ) (fields : list typ),
      (forall f, In f fields -> guarded_typ id env f) ->
      guarded_typ id env (TYPE_Packed_struct fields)

| guarded_typ_Opaque :
    forall (id : ident) (env : list (ident * typ)),
      guarded_typ id env TYPE_Opaque

| guarded_typ_Vector :
    forall (id : ident) (env : list (ident * typ)) (sz : N) (t : typ),
      guarded_typ id env (TYPE_Vector sz t)

| guarded_typ_Identified_Some :
    forall (id : ident) (env : list (ident * typ)) (id' : ident) (t : typ),
      id <> id' ->
      Some (id', t) = find (fun a => Ident.eq_dec id' (fst a)) env ->
      guarded_typ id env t ->
      guarded_typ id' env t ->
      guarded_typ id env (TYPE_Identified id')

| guarded_typ_Identified_None :
    forall (id : ident) (env : list (ident * typ)) (id' : ident),
      id <> id' ->
      None = find (fun a => Ident.eq_dec id' (fst a)) env ->
      guarded_typ id env (TYPE_Identified id')
.


Inductive first_class_typ : typ -> Prop :=
| first_class_I : forall sz, first_class_typ (TYPE_I sz)
| first_class_Pointer : forall t, first_class_typ (TYPE_Pointer t)
| first_class_Void : first_class_typ TYPE_Void
| first_class_Half : first_class_typ TYPE_Half
| first_class_Float : first_class_typ TYPE_Float
| first_class_Double : first_class_typ TYPE_Double
| first_class_X86_fp80 : first_class_typ TYPE_X86_fp80
| first_class_Fp128 : first_class_typ TYPE_Fp128
| first_class_Ppc_fp128 : first_class_typ TYPE_Ppc_fp128
| first_class_Metadata : first_class_typ TYPE_Metadata
| first_class_X86_mmx : first_class_typ TYPE_X86_mmx
| first_class_Array : forall sz t, first_class_typ (TYPE_Array sz t)
| first_class_Struct : forall fields, first_class_typ (TYPE_Struct fields)
| first_class_Packed_struct : forall fields, first_class_typ (TYPE_Packed_struct fields)
| first_class_Opaque : first_class_typ TYPE_Opaque
| first_class_Vector : forall sz t, first_class_typ (TYPE_Vector sz t)
| first_class_Identified : forall id, first_class_typ (TYPE_Identified id)
.


Definition function_ret_typ (t : typ) : Prop :=
  first_class_typ t /\ t <> TYPE_Metadata.


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
    forall (defs : list (ident * typ)) (sz : N),
      (sz > 0)%N -> wf_typ defs (TYPE_I sz)

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

| wf_typ_Function :
    forall (defs : list (ident * typ)) (ret : typ) (args : list typ) (varargs : bool),
      function_ret_typ ret ->
      wf_typ defs ret ->
      (forall (a : typ), In a args -> sized_typ defs a) ->
      (forall (a : typ), In a args -> wf_typ defs a) ->
      wf_typ defs (TYPE_Function ret args varargs)

(* Arrays are only well formed if the size is >= 0, and the element type is sized. *)
| wf_typ_Array :
    forall (defs : list (ident * typ)) (sz : N) (t : typ),
      (sz >= 0)%N -> sized_typ defs t -> wf_typ defs t -> wf_typ defs (TYPE_Array sz t)

(* Vectors of size 0 are not allowed, and elements must be of element_typ. *)
| wf_typ_Vector :
    forall (defs : list (ident * typ)) (sz : N) (t : typ),
      (sz > 0)%N -> element_typ t -> wf_typ defs t -> wf_typ defs (TYPE_Vector sz t)

(* Any type identifier must exist in the environment.

   Additionally the identifier must not occur anywhere in the type
   that it refers to *unless* it is guarded by a pointer. *)
| wf_typ_Identified :
    forall (defs : list (ident * typ)) (id : ident),
      (exists t, In (id, t) defs) ->
      (forall (t : typ), In (id, t) defs -> guarded_typ id defs t) ->
      (forall (t : typ), In (id, t) defs -> wf_typ defs t) ->
      wf_typ defs (TYPE_Identified id)

(* Fields of structure must be sized types *)
| wf_typ_Struct :
    forall (defs : list (ident * typ)) (fields : list typ),
      (forall (f : typ), In f fields -> sized_typ defs f) ->
      (forall (f : typ), In f fields -> wf_typ defs f) ->
      wf_typ defs (TYPE_Struct fields)

| wf_typ_Packed_struct :
    forall (defs : list (ident * typ)) (fields : list typ),
      (forall (f : typ), In f fields -> sized_typ defs f) ->
      (forall (f : typ), In f fields -> wf_typ defs f) ->
      wf_typ defs (TYPE_Packed_struct fields)

| wf_typ_Opaque :
    forall (defs : list (ident * typ)),
      wf_typ defs TYPE_Opaque
.


#[global]
Hint Constructors wf_typ : core.


Definition wf_env (env : list (ident * typ)) : Prop :=
  NoDup (map fst env) /\ Forall (wf_typ env) (map snd env).


Inductive guarded_wf_typ : list (ident * typ) -> typ -> Prop :=
| guarded_wf_typ_Pointer:
    forall (defs : list (ident * typ)) (t : typ),
      guarded_wf_typ defs (TYPE_Pointer t)

| guarded_wf_typ_I :
    forall (defs : list (ident * typ)) (sz : N),
      (sz > 0)%N -> guarded_wf_typ defs (TYPE_I sz)

| guarded_wf_typ_Void :
    forall (defs : list (ident * typ)),
      guarded_wf_typ defs TYPE_Void

| guarded_wf_typ_Half :
    forall (defs : list (ident * typ)),
      guarded_wf_typ defs TYPE_Half

| guarded_wf_typ_Float :
    forall (defs : list (ident * typ)),
      guarded_wf_typ defs TYPE_Float

| guarded_wf_typ_Double :
    forall (defs : list (ident * typ)),
      guarded_wf_typ defs TYPE_Double

| guarded_wf_typ_X86_fp80 :
    forall (defs : list (ident * typ)),
      guarded_wf_typ defs TYPE_X86_fp80

| guarded_wf_typ_Fp128 :
    forall (defs : list (ident * typ)),
      guarded_wf_typ defs TYPE_Fp128

| guarded_wf_typ_Ppc_fp128 :
    forall (defs : list (ident * typ)),
      guarded_wf_typ defs TYPE_Ppc_fp128

| guarded_wf_typ_Metadata :
    forall (defs : list (ident * typ)),
      guarded_wf_typ defs TYPE_Metadata

| guarded_wf_typ_X86_mmx :
    forall (defs : list (ident * typ)),
      guarded_wf_typ defs TYPE_X86_mmx

| guarded_wf_typ_Function :
    forall (defs : list (ident * typ)) (ret : typ) (args : list typ) (varargs:bool),
      function_ret_typ ret ->
      guarded_wf_typ defs ret ->
      (forall (a : typ), In a args -> sized_typ defs a) ->
      (forall (a : typ), In a args -> guarded_wf_typ defs a) ->
      guarded_wf_typ defs (TYPE_Function ret args varargs)

(* Arrays are only well formed if the size is >= 0, and the element type is sized. *)
| guarded_wf_typ_Array :
    forall (defs : list (ident * typ)) (sz : N) (t : typ),
      (sz >= 0)%N -> sized_typ defs t -> guarded_wf_typ defs t -> guarded_wf_typ defs (TYPE_Array sz t)

(* Vectors of size 0 are not allowed, and elemnts must be of element_typ. *)
| guarded_wf_typ_Vector :
    forall (defs : list (ident * typ)) (sz : N) (t : typ),
      (sz > 0)%N -> element_typ t -> guarded_wf_typ defs t -> guarded_wf_typ defs (TYPE_Vector sz t)

(* Identifier must be in the typing environment.

   Additionally the identifier must not occur anywhere in the type
   that it refers to *unless* it is guarded by a pointer. *)
| guarded_wf_typ_Identified :
    forall (defs : list (ident * typ)) (id : ident),
      (exists t, In (id, t) defs) ->
      (forall (t : typ), In (id, t) defs -> guarded_typ id defs t) ->
      (forall (t : typ), In (id, t) defs -> guarded_wf_typ defs t) ->
      guarded_wf_typ defs (TYPE_Identified id)

(* Fields of structure must be sized types *)
| guarded_wf_typ_Struct :
    forall (defs : list (ident * typ)) (fields : list typ),
      (forall (f : typ), In f fields -> sized_typ defs f) ->
      (forall (f : typ), In f fields -> guarded_wf_typ defs f) ->
      guarded_wf_typ defs (TYPE_Struct fields)

| guarded_wf_typ_Packed_struct :
    forall (defs : list (ident * typ)) (fields : list typ),
      (forall (f : typ), In f fields -> sized_typ defs f) ->
      (forall (f : typ), In f fields -> guarded_wf_typ defs f) ->
      guarded_wf_typ defs (TYPE_Packed_struct fields)

| guarded_wf_typ_Opaque :
    forall (defs : list (ident * typ)),
      guarded_wf_typ defs TYPE_Opaque
.

#[global]
Hint Constructors guarded_wf_typ : core.


Theorem wf_typ_is_guarded_wf_typ :
  forall env t,
    wf_typ env t ->
    guarded_wf_typ env t.
Proof.
  induction 1; auto.
Qed.


(* An unrolled type is an LLVM type that contains no identifiers,
   unless the identifier is behind a pointer.

 *)


Inductive unrolled_typ : typ -> Prop :=
| unrolled_typ_I :
    forall (sz : N),
      unrolled_typ (TYPE_I sz)

| unrolled_typ_Pointer :
    forall (t : typ),
      unrolled_typ (TYPE_Pointer t)

| unrolled_typ_Void :
    unrolled_typ TYPE_Void

| unrolled_typ_Half :
    unrolled_typ TYPE_Half

| unrolled_typ_Float :
    unrolled_typ TYPE_Float

| unrolled_typ_Double :
    unrolled_typ TYPE_Double

| unrolled_typ_X86_fp80 :
    unrolled_typ TYPE_X86_fp80

| unrolled_typ_Fp128 :
    unrolled_typ TYPE_Fp128

| unrolled_typ_Ppc_fp128 :
    unrolled_typ TYPE_Ppc_fp128

| unrolled_typ_Metadata :
    unrolled_typ TYPE_Metadata

| unrolled_typ_X86_mmx :
    unrolled_typ TYPE_X86_mmx

| unrolled_typ_Array :
    forall (sz : N) (t : typ),
      unrolled_typ t ->
      unrolled_typ (TYPE_Array sz t)

| unrolled_typ_Function :
    forall (ret : typ) (args : list typ) (varargs:bool),
      unrolled_typ ret ->
      Forall unrolled_typ args ->
      unrolled_typ (TYPE_Function ret args varargs)

| unrolled_typ_Struct :
    forall (fields : list typ),
      Forall (unrolled_typ) fields ->
      unrolled_typ (TYPE_Struct fields)

| unrolled_typ_Packed_struct :
    forall (fields : list typ),
      Forall (unrolled_typ) fields ->
      unrolled_typ (TYPE_Packed_struct fields)

| unrolled_typ_Opaque :
    unrolled_typ TYPE_Opaque

| unrolled_typ_Vector :
    forall (sz : N) (t : typ), unrolled_typ (TYPE_Vector sz t)
.


Inductive typ_order : typ -> typ -> Prop :=
| typ_order_Pointer : forall (t : typ), typ_order t (TYPE_Pointer t)
| typ_order_Array : forall (sz : N) (t : typ), typ_order t (TYPE_Array sz t)
| typ_order_Vector : forall (sz : N) (t : typ), typ_order t (TYPE_Vector sz t)
| typ_order_Struct : forall (fields : list typ),
    forall f, In f fields -> typ_order f (TYPE_Struct fields)
| typ_order_Packed_struct : forall (fields : list typ),
    forall f, In f fields -> typ_order f (TYPE_Packed_struct fields)
| typ_order_Function_args : forall (ret : typ) (args : list typ) (varargs:bool),
    forall a, In a args -> typ_order a (TYPE_Function ret args varargs)
| typ_order_Function_ret : forall (ret : typ) (args : list typ) (varargs:bool),
    typ_order ret (TYPE_Function ret args varargs)
.


#[global]
Hint Constructors typ_order : core.


Theorem wf_typ_order :
    well_founded typ_order.
Proof.
  unfold well_founded.
  induction a; constructor; intros y H'; inversion H'; subst; auto.
Qed.


Theorem wf_lt_typ_order :
  well_founded (lex_ord lt typ_order).
Proof.
  apply wf_lex_ord.
  apply lt_wf. apply wf_typ_order.
Qed.

#[global]
Hint Resolve wf_lt_typ_order : core.
#[global]
Hint Constructors lex_ord : core.


Definition length_order {A : Type} (l1 l2 : list A) :=
  (List.length l1 < List.length l2)%nat.


(* Lemma lengthOrder_wf' : forall A len, forall ls, (List.length ls <= len)%nat -> Acc (@length_order A) ls. *)
(*   unfold length_order; induction len; *)
(*     intros ls H; inversion H; subst; constructor; firstorder. *)
(* Defined. *)


(* Theorem lengthOrder_wf : forall A, well_founded (@length_order A). *)
(*   red; intros A a; eapply lengthOrder_wf'; eauto. *)
(* Defined. *)


(* Theorem wf_length_typ_order : *)
(*   forall A, *)
(*     well_founded (lex_ord (@length_order A) typ_order). *)
(* Proof. *)
(*   intros. *)
(*   apply wf_lex_ord. apply lengthOrder_wf. apply wf_typ_order. *)
(* Defined. *)

Lemma map_In {A B : Type} (l : list A) (f : forall (x : A), In x l -> B) : list B.
Proof.
  induction l.
  - exact [].
  - refine (f a _ :: IHl _).
    + simpl. auto.
    + intros x H. apply (f x). simpl. auto.
Defined.


Fixpoint remove_key {A B : Type} (eq_dec : (forall (x y : A), {x = y} + {x <> y})) (a : A) (l : list (A * B)) : list (A * B) :=
  match l with
  | nil => nil
  | cons (h, b) t =>
    match eq_dec a h with
    | left _ => t
    | right _ => (h, b) :: remove_key eq_dec a t
    end
  end.


Fixpoint remove_keys {A B : Type} (eq_dec : (forall (x y : A), {x = y} + {x <> y})) (keys : list A) (l : list (A * B)) : list (A * B) :=
  match keys with
  | nil => l
  | key :: rest_of_keys => remove_keys eq_dec rest_of_keys (remove_key eq_dec key l)
  end.


Ltac destruct_prod :=
  match goal with
  | [ |- context[let (_, _) := ?p in _]] => destruct p
  | [ p: ?A * ?B |- _ ] => destruct p
  end.


Ltac destruct_eq_dec :=
  match goal with
  | [ eq: forall x y : ?A , {x = y} + {x <> y} |- context[eq ?a ?b] ] => destruct (eq a b) eqn:?; simpl
  | [ |- context[Ident.eq_dec ?a ?b] ] => destruct (Ident.eq_dec a b) eqn:?; simpl
  end.


Lemma remove_key_in :
  forall (A B : Type) (a : A)  (b : B) eq_dec l,
    In (a, b) l ->
    (List.length (remove_key eq_dec a l) < List.length l)%nat.
Proof.
  induction l.
  - intros H. inversion H.
  - intros H.
    destruct_prod.
    simpl. destruct_eq_dec.
    + apply Nat.lt_succ_diag_r.
    + simpl. apply -> Nat.succ_lt_mono. apply IHl.
      destruct H.
      * inversion H. subst. contradiction.
      * assumption.
Qed.


Lemma remove_key_not_in :
  forall (A B : Type) (a : A) eq_dec (l : list (A * B)),
    ~ In a (map fst l) ->
    remove_key eq_dec a l = l.
Proof.
  induction l; intros H.
  - reflexivity.
  - simpl in *. destruct_prod; destruct_eq_dec.
    + intuition auto with *.
    + rewrite IHl; intuition auto with *.
Qed.


Ltac solve_eq_dec_if :=
  match goal with
  | [ eq: forall x y : ?A , {x = y} + {x <> y},
        Heq : ?eq ?a ?b = ?c |- context[if ?eq ?a ?b then _ else _] ] => rewrite Heq
  | [ Heq : Ident.eq_dec ?a ?b = ?c |- context[if Ident.eq_dec ?a ?b then _ else _] ] => rewrite Heq
  | [ eq: forall x y : ?A , {x = y} + {x <> y},
        Heq : ?eq ?a ?b = ?c |- context[if proj_sumbool (?eq ?a ?b) then _ else _] ] => rewrite Heq
  | [ Heq : Ident.eq_dec ?a ?b = ?c |- context[if proj_sumbool (Ident.eq_dec ?a ?b) then _ else _] ] => rewrite Heq

  end.


Ltac subst_eq :=
  match goal with
  | [ eq: forall x y : ?A , {x = y} + {x <> y}, Heq: eq ?a ?b = ?c |- _ ] => rewrite Heq
  | [ Heq : Ident.eq_dec ?a ?b = ?c |- _ ] => rewrite Heq
  end.


Ltac solve_eq_dec :=
  repeat destruct_prod; simpl in *;
  repeat (destruct_eq_dec; simpl in *; subst; simpl; try contra; auto; repeat (solve_eq_dec_if; simpl); auto);
  intuition auto with *; try congruence.


Lemma remove_key_commutes :
  forall (A B : Type) (k1 k2 : A) eq_dec (l : list (A * B)),
    remove_key eq_dec k1 (remove_key eq_dec k2 l) = remove_key eq_dec k2 (remove_key eq_dec k1 l).
Proof.
  induction l; solve_eq_dec.
Qed.


Lemma remove_key_keys :
  forall (A B : Type) (keys : list A) eq_dec (key : A) (l : list (A * B)),
    remove_key eq_dec key (remove_keys eq_dec keys l) = remove_keys eq_dec (key :: keys) l.
Proof.
  intros A B keys.
  induction keys as [| k keys' IHkeys]; intros eq_dec key l; auto.
  simpl in *.
  rewrite IHkeys.
  apply f_equal; apply remove_key_commutes.
Qed.


Lemma remove_keys_key :
  forall (A B : Type) (keys : list A) eq_dec (key : A) (l : list (A * B)),
    remove_keys eq_dec keys (remove_key eq_dec key l) = remove_keys eq_dec (key :: keys) l.
Proof.
  intros A B keys.
  induction keys; intros eq_dec key l; auto.
Qed.


Program Fixpoint normalize_type (env : list (ident * typ)) (t : typ) {measure (List.length env, t) (lex_ord lt typ_order)} : typ :=
  match t with
  | TYPE_Array sz t =>
    let nt := normalize_type env t in
    TYPE_Array sz nt

  | TYPE_Function ret args varargs =>
    let nret := (normalize_type env ret) in
    let nargs := map_In args (fun t _ => normalize_type env t) in
    TYPE_Function nret nargs varargs

  | TYPE_Struct fields =>
    let nfields := map_In fields (fun t _ => normalize_type env t) in
    TYPE_Struct nfields

  | TYPE_Packed_struct fields =>
    let nfields := map_In fields (fun t _ => normalize_type env t) in
    TYPE_Packed_struct nfields

  | TYPE_Vector sz t =>
    let nt := normalize_type env t in
    TYPE_Vector sz nt

  | TYPE_Identified id =>
    match find (fun a => Ident.eq_dec id (fst a)) env with
    | None => TYPE_Identified id
    | Some (_, t) => normalize_type (remove_key Ident.eq_dec id env) t
    end

  | TYPE_I sz => t
  | TYPE_IPTR => t
  | TYPE_Pointer t' => t
  | TYPE_Void => t
  | TYPE_Half => t
  | TYPE_Float => t
  | TYPE_Double => t
  | TYPE_X86_fp80 => t
  | TYPE_Fp128 => t
  | TYPE_Ppc_fp128 => t
  | TYPE_Metadata => t
  | TYPE_X86_mmx => t
  | TYPE_Opaque => t
  end.
Next Obligation.
  left.
  symmetry in Heq_anonymous. apply find_some in Heq_anonymous. destruct Heq_anonymous as [Hin Heqb_ident].
  simpl in Heqb_ident.
  destruct (Ident.eq_dec id wildcard'). subst. eapply remove_key_in. apply Hin.
  inversion Heqb_ident.
Defined.


Lemma normalize_type_equation : forall env t,
    normalize_type env t =
    match t with
  | TYPE_Array sz t =>
    let nt := normalize_type env t in
    TYPE_Array sz nt

  | TYPE_Function ret args varargs =>
    let nret := (normalize_type env ret) in
    let nargs := map_In args (fun t _ => normalize_type env t) in
    TYPE_Function nret nargs varargs

  | TYPE_Struct fields =>
    let nfields := map_In fields (fun t _ => normalize_type env t) in
    TYPE_Struct nfields

  | TYPE_Packed_struct fields =>
    let nfields := map_In fields (fun t _ => normalize_type env t) in
    TYPE_Packed_struct nfields

  | TYPE_Vector sz t =>
    let nt := normalize_type env t in
    TYPE_Vector sz nt

  | TYPE_Identified id =>
    let opt := find (fun a => Ident.eq_dec id (fst a)) env in
    match opt with
    | None => TYPE_Identified id   (* TODO: should this be None? *)
    | Some (_, t) => normalize_type (remove_key Ident.eq_dec id env) t
    end

  | TYPE_I sz => TYPE_I sz
  | TYPE_IPTR => TYPE_IPTR
  | TYPE_Pointer t' => TYPE_Pointer t'
  | TYPE_Void => TYPE_Void
  | TYPE_Half => TYPE_Half
  | TYPE_Float => TYPE_Float
  | TYPE_Double => TYPE_Double
  | TYPE_X86_fp80 => TYPE_X86_fp80
  | TYPE_Fp128 => TYPE_Fp128
  | TYPE_Ppc_fp128 => TYPE_Ppc_fp128
  | TYPE_Metadata => TYPE_Metadata
  | TYPE_X86_mmx => TYPE_X86_mmx
  | TYPE_Opaque => TYPE_Opaque
  end.
Proof.
  intros env t.
  unfold normalize_type.
  unfold normalize_type_func at 1.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext.
  destruct t; try reflexivity. simpl.
  destruct (find (fun a : ident * typ => Ident.eq_dec id (fst a)) env).
  destruct p; simpl; eauto.
  reflexivity.
Defined.

#[global]
Hint Constructors unrolled_typ : core.


Lemma find_in_wf_env :
  forall env id t,
    NoDup (map fst env) ->
    In (id, t) env ->
    find (fun a : ident * typ => Ident.eq_dec id (fst a)) env = Some (id, t).
Proof.
  intros env id t Hdup Hin.
  induction env as [| [id' t'] env IHenv].
  - contradiction.
  - destruct Hin as [Hin | Hin]; try inversion Hin; subst.
    + simpl. destruct_eq_dec; intuition auto with *.
    + simpl. destruct_eq_dec.
      * inversion Hdup. subst. apply in_map with (f:=fst) in Hin. simpl in *.
        contradiction.
      * simpl. inversion Hdup. auto.
Qed.


Lemma guarded_typ_id_same :
  forall env id,
    guarded_typ id env (TYPE_Identified id) -> False.
Proof.
  intros env id H.
  inversion H; contradiction.
Qed.



Lemma find_different_key_from_removed :
  forall env id id',
    id <> id' ->
    find (fun a : ident * typ => Ident.eq_dec id' (fst a)) env = find (fun a : ident * typ => Ident.eq_dec id' (fst a)) (remove_key Ident.eq_dec id env).
Proof.
  intros env id id' H.
  induction env; solve_eq_dec.
Qed.


Lemma remove_keys_find :
  forall env id ids,
    ~ In id ids ->
    find (fun a : ident * typ => Ident.eq_dec id (fst a)) env = find (fun a : ident * typ => Ident.eq_dec id (fst a)) (remove_keys Ident.eq_dec ids env).
Proof.
  intros env id ids H.
  induction ids.
  - reflexivity.
  - rewrite <- remove_key_keys.
    rewrite <- find_different_key_from_removed with (id:=a); intuition auto with *; subst; intuition auto with *.
Qed.


Ltac solve_some :=
  match goal with
  | [ H: (?i1, ?t1) = (?i2, ?t2) |- ?F (?i1, ?t1) = ?F (?i2, ?t2) ] => inversion H; reflexivity
  | [ Hdup : NoDup (?i :: map fst ?env),
      Hin : In (?i, ?t) ?env |- ?F (?i, ?t1) = ?F (?i, ?t2) ] =>
    let Hnin := fresh in
    let Hdup' := fresh in
    inversion Hdup as [| ? ? Hnin Hdup']; subst;
    exfalso; apply Hnin;
    replace i with (fst (i, t)) by reflexivity;
    apply in_map; auto
  | [ Hin : In (?i, ?t1) ((?i, ?t2) :: ?env) |- ?F (?i, ?t1) = ?F (?i, ?t2) ] => symmetry; solve_some
  | [ Hin : In (?i, ?t2) ((?i, ?t1) :: ?env) |- ?F (?i, ?t1) = ?F (?i, ?t2) ] => inversion Hin; solve_some
  end.


Ltac solve_in :=
  match goal with
  | [ Hin: In (?id, ?t) ((?i, ?t0) :: ?env),
      Hneq: ?id <> ?i |- In (?id, ?t) ?env ] =>
    let Htup := fresh in
    inversion Hin as [Htup | ?]; [> inversion Htup; contra | auto]

  | [ H: find (fun a => (proj_sumbool (?eq ?id (fst a)))) ?env = Some (?i, ?t)
      |- In (?id, ?t) ?env ] =>
    let Hfind := fresh in
    apply find_some in H as [? Hfind];
    simpl in Hfind;
    destruct (Ident.eq_dec id i) eqn:?; subst; intuition auto with *
  end.


Lemma find_some_id :
  forall env id p t,
    NoDup (map fst env) ->
    In (id, t) env ->
    find (fun a : ident * typ => Ident.eq_dec id (fst a)) env = Some p ->
    find (fun a : ident * typ => Ident.eq_dec id (fst a)) env = Some (id, t).
Proof.
  intros env id p t Hdup Hin H.
  induction env.
  - inversion H.
  - destruct a. simpl.
    destruct_eq_dec.
    + subst. simpl in Hdup. solve_some.
    + simpl. apply IHenv.
      * inversion Hdup; auto.
      * solve_in.
      * simpl in *. rewrite Heqs in H. simpl in *.
        assumption.
Qed.

#[global]
Hint Constructors sized_typ : core.
#[global]
Hint Constructors guarded_typ : core.


(* Types with no identifiers *)
Inductive simple_typ : typ -> Prop :=
| simple_typ_I : forall sz, simple_typ (TYPE_I sz)
| simple_typ_Pointer : forall t, simple_typ t -> simple_typ (TYPE_Pointer t)
| simple_typ_Void : simple_typ (TYPE_Void)
| simple_typ_Half : simple_typ (TYPE_Half)
| simple_typ_Float : simple_typ (TYPE_Float)
| simple_typ_Double : simple_typ (TYPE_Double)
| simple_typ_X86_fp80 : simple_typ (TYPE_X86_fp80)
| simple_typ_Fp128 : simple_typ (TYPE_Fp128)
| simple_typ_Ppc_fp128 : simple_typ (TYPE_Ppc_fp128)
| simple_typ_Metadata : simple_typ (TYPE_Metadata)
| simple_typ_X86_mmx : simple_typ (TYPE_X86_mmx)
| simple_typ_Array : forall sz t, simple_typ t -> simple_typ (TYPE_Array sz t)
| simple_typ_Function :
    forall ret args varargs,
      simple_typ ret ->
      (forall a, In a args -> simple_typ a) ->
      simple_typ (TYPE_Function ret args varargs)
| simple_typ_Struct :
    forall fields,
      (forall f, In f fields -> simple_typ f) ->
      simple_typ (TYPE_Struct fields)
| simple_typ_Packed_struct :
    forall fields,
      (forall f, In f fields -> simple_typ f) ->
      simple_typ (TYPE_Packed_struct fields)
| simple_typ_Opaque : simple_typ (TYPE_Opaque)
| simple_typ_Vector : forall sz t, simple_typ t -> simple_typ (TYPE_Vector sz t)
.


#[global]
Hint Constructors simple_typ : core.


Theorem map_in_id :
  forall {A : Type} (l : list A) (f : forall x : A, In x l -> A),
    (forall a (Hin : In a l), f a Hin = a) ->
    map_In l f = l.
Proof.
  intros A l f H.
  induction l; auto.
  simpl. rewrite H. rewrite IHl; auto.
Qed.


Theorem simple_normalizes_to_self :
  forall env t,
    simple_typ t ->
    normalize_type env t = t.
Proof.
  intros env t H.
  induction H; rewrite normalize_type_equation; simpl;
    repeat
      match goal with
      | [H : normalize_type env _ = _ |- context[normalize_type _ _]] => rewrite H
      | [|- context[(map_In _ (fun (t : typ) (_ : In t _) => normalize_type env t))]] => rewrite map_in_id; auto
      end; auto.
Qed.


Theorem simple_unrolled :
  forall t,
    simple_typ t -> unrolled_typ t.
Proof.
  intros t H.
  induction H; constructor;
    try match goal with
        | [|- Forall _ _] => apply Forall_forall
        end; auto.
Qed.


Theorem in_map_in :
  forall {A : Type} (x : A) (l : list A) f,
    In x (map_In l (fun t (_ : In t l) => f t)) ->
    exists t, In t l /\ f t = x.
Proof.
  intros A x l f H.
  induction l.
  - inversion H.
  - simpl in *. destruct H.
    + exists a. split; auto.
    + apply IHl in H as [t [Hin Hftx]].
      exists t. intuition auto with *.
Qed.


Theorem map_rewrite :
  forall {A B : Type} (x : A) (l : list A) (f g : A -> B),
    (forall x, In x l -> f x = g x) ->
    map_In l (fun t (_ : In t l) => f t) = map_In l (fun t (_ : In t l) => g t).
Proof.
  intros A B x l f g H.
  induction l as [| a l IHl]; simpl; auto.
  pose proof (H a) as Ha.
  rewrite Ha; intuition auto with *.
  rewrite IHl; intuition auto with *.
Qed.


Ltac simpl_remove_keys :=
  match goal with
  | [ |- context[remove_key ?eq ?id (remove_keys ?eq ?ids ?assoc_list)] ] =>
    replace (remove_key eq id (remove_keys eq ids assoc_list)) with
        (remove_keys eq (id :: ids) assoc_list) by auto using remove_key_keys

  | [ |- context[remove_keys ?eq ?ids (remove_key ?eq ?id ?assoc_list)] ] =>
    replace (remove_keys eq ids (remove_key eq id assoc_list)) with
        (remove_keys eq (id :: ids) assoc_list) by auto using remove_keys_key

  | [ |- context[remove_key ?eq ?id ?assoc_list] ] =>
    replace (remove_key eq id assoc_list) with
        (remove_keys eq [id] assoc_list) by auto
  end.


Ltac subst_find_some :=
  match goal with
  | [ H1: ?F ?filter ?defs = ?G (?i1, ?t1),
      H2: ?X = ?F ?filter ?defs |- _ ] => rewrite H1 in H2; inversion H2
  end.


Ltac solve_guard :=
  match goal with
  | [ H: element_typ ?x |- guarded_typ ?id ?defs ?x ] =>
        match goal with
        | [H : element_typ _ |- _] => inversion H
        end; auto

  | [ Hguard: forall i, In i ?ids -> guarded_typ i ?env ?t |- ~(In ?id ?ids) ] =>
    let Hguard' := fresh in
    let Hin := fresh in
    unfold not; intros Hin;
    pose proof Hguard id Hin as Hguard';
    inversion Hguard'; auto

  | [ Hguard: forall t, In (?i, t) ?defs -> guarded_typ ?i ?defs t,
        Hin: In ?id [?i] |- _ ] =>
    intros; inversion Hin; subst; try contradiction; auto

  | [ Hguard: forall i, In ?id [i] -> guarded_typ ?i ?env ?t |- ~(In ?id ?ids) ] =>
    let Hguard' := fresh in
    let Hin := fresh in
    unfold not; intros Hin;
    pose proof Hguard id Hin as Hguard';
    inversion Hguard'; subst; try contra; auto

  | [ Hguard: forall i, In i ?ids -> guarded_typ i ?env ?t,
        Hin: In ?id [?one] |- guarded_typ ?id ?defs ?x ] =>
    inversion Hin; subst; auto; contra

  | [ Hguard: forall i, In i ?ids -> guarded_typ i ?env ?t,
      Hin: In ?id ?ids |- guarded_typ ?id ?defs ?x ] =>
    let Hguard' := fresh in
    pose proof Hguard _ Hin as Hguard'; inversion Hguard'; auto; subst; subst_find_some; subst; auto

  | [ |- forall id, In id ?ids -> guarded_typ id ?defs ?x ] =>
    intros; solve_guard
  end.

Theorem guarded_id_normalize_same :
  forall t env,
    NoDup (map fst env) ->
    guarded_wf_typ env t ->
    (forall ids,
        (forall id, In id ids -> guarded_typ id env t) ->
        normalize_type (remove_keys Ident.eq_dec ids env) t = normalize_type env t).
Proof.
  intros t env Hdup Hwf.
  induction Hwf; intros ids Hguard;
    rewrite normalize_type_equation; symmetry; rewrite normalize_type_equation; simpl; auto;
      try rewrite IHHwf; auto;
        try match goal with
            | [H : element_typ _ |- _] => inversion H
            end;
        try (rewrite map_rewrite with (f:=normalize_type (remove_keys _ _ _)) (g:=normalize_type defs);
             try exact (TYPE_Void);
             auto; intros;
             match goal with
             | [ H: _ |- _ ] => apply H
             end;
             auto);
        try (intros id Hidin; solve_guard).

  (* Identifiers *)
  repeat simpl_remove_keys.

  (* If id is in ids, this means that guarded_typ id defs
     (TYPE_Identified id), which is a contradiction. *)
  assert (~ In id ids) as Hnotin by solve_guard.

  replace (find (fun a : ident * typ => Ident.eq_dec id (fst a)) (remove_keys Ident.eq_dec ids defs)) with
      (find (fun a : ident * typ => Ident.eq_dec id (fst a)) defs) by (auto using remove_keys_find).

  destruct (find (fun a : ident * typ => Ident.eq_dec id (fst a)) defs) eqn:Hfind; auto.
  destruct_prod. simpl.

  assert (In (id, t) defs).
  apply find_some in Hfind as [Hin Hfind].
  simpl in Hfind.

  destruct (Ident.eq_dec id i) eqn:Hidi; subst; intuition auto with *.

  repeat (simpl_remove_keys;
          repeat match goal with
                 | [ H: _ |- _ ] => rewrite H
                 end; auto); intros id0 [Hidid0 | Hin']; subst; auto.

  - inversion Hin'.
  - pose proof (Hguard id0 Hin') as Hguard'. inversion Hguard'; subst_find_some; subst; auto.
Qed.


Theorem double_map_In :
  forall A B C (l : list A) (f : A -> B) (g : B -> C),
    (map_In (map_In l (fun x (_ : In x l) => f x)) (fun x (_ : In x (map_In l (fun x (_ : In x l) => f x))) => g x)) = map_In l (fun x (_ : In x l) => g (f x)).
Proof.
  intros A B C l f g.
  induction l; simpl; auto using f_equal.
Qed.


Ltac solve_map_in :=
  repeat
    match goal with
    | [  |- context[map_In (map_In _ _)] ] => rewrite double_map_In
    | [ defs : list (ident * typ) |- _ ] =>
      try (rewrite map_rewrite with (f:=fun x => normalize_type defs (normalize_type defs x)) (g:=normalize_type defs); [> eauto | exact TYPE_Void | eauto]);
      try solve [intros;
                 match goal with
                 | [ H: _ |- _ ] => apply H
                 end; auto; solve_guard]

  end.


Ltac solve_match_find :=
  match goal with
  | [ |- context[match ?Find with _ => _ end = _] ] =>
    let i := fresh in
    let t := fresh in
    let Hfind := fresh in
    destruct Find as [[i t] |] eqn:Hfind;
    match goal with
    | [ Hf: context[find (fun a => proj_sumbool (?eq ?id (fst a))) ?defs],
            defs : list (ident * typ) |- _ ] =>
      try (assert (In (id, t) defs) by solve_in;
           symmetry; simpl_remove_keys;
           rewrite guarded_id_normalize_same; auto using wf_typ_is_guarded_wf_typ; try solve_guard;

           try (match goal with
                | [ H: _ |- _ ] => apply H
                end; auto; solve_guard));
      try (rewrite normalize_type_equation; simpl; rewrite Hfind; reflexivity)
    end
  end.


Theorem guarded_normalize_same :
  forall t env,
    NoDup (map fst env) ->
    guarded_wf_typ env t ->
    (forall ids,
        (forall id, In id ids -> guarded_typ id env t) ->
        normalize_type env (normalize_type env t) = normalize_type env t).
Proof.
  intros t env Hdup Hwf ids Hguard_all.
  induction Hwf;
    try solve [rewrite normalize_type_equation; symmetry; rewrite normalize_type_equation;
               simpl; auto;
               try rewrite IHHwf; auto; try solve_guard; solve_map_in].

  symmetry; rewrite normalize_type_equation; simpl.
  solve_match_find.
Qed.


Lemma wf_typ_guarded_normalize_twice :
  forall env t,
    NoDup (map fst env) ->
    wf_typ env t ->
    (forall ids,
        (forall id, In id ids -> guarded_typ id env t) ->
        normalize_type env (normalize_type env t) = normalize_type env t).
Proof.
  eauto using wf_typ_is_guarded_wf_typ, guarded_normalize_same.
Qed.


Theorem double_normalize_type :
  forall env t,
    wf_env env ->
    wf_typ env t ->
    normalize_type env (normalize_type env t) = normalize_type env t.
Proof.
  intros env t [Hdup Henv] Hwf.
  induction Hwf;
    try solve [rewrite normalize_type_equation; symmetry; rewrite normalize_type_equation;
               simpl; auto;
               try rewrite IHHwf; auto; try solve_guard; solve_map_in].

  symmetry; rewrite normalize_type_equation; simpl.
  solve_match_find.
Qed.


Theorem guarded_normalize_type_unrolls:
  forall env t,
    NoDup (map fst env) ->
    guarded_wf_typ env t ->
    (forall ids,
        (forall id, In id ids -> guarded_typ id env t) ->
        unrolled_typ (normalize_type env t)).
Proof.
  intros env t Hdup Hwf ids Hguard_all.
  induction Hwf; rewrite normalize_type_equation; simpl; auto;
    try constructor;
    try (apply IHHwf; auto; solve_guard);
    try (rewrite Forall_forall; intros;
         match goal with
         | [ H: In ?x (map_In _ _) |- _ ] =>  apply in_map_in in H as [t [Hin Hnorm]]
         end;

         rewrite <- Hnorm;

         match goal with
         | [ H: _ |- _ ] => apply H
         end; auto; solve_guard).
  - destruct (find (fun a : ident * typ => Ident.eq_dec id (fst a)) defs) as [[i t] |] eqn:Hfind.
    + pose proof Hfind as Hfind'.
      apply find_some in Hfind' as [Hin Heq].
      simpl in *. destruct (Ident.eq_dec id i) as [He | He]; inversion Heq.

      rewrite He.
      simpl_remove_keys.
      rewrite guarded_id_normalize_same; auto;
        try match goal with
            | [ H: _ |- _ ] => apply H
            end;
        subst; auto; solve_guard.
    + destruct H as [t Hin].
      eapply find_none in Hfind; eauto.
      simpl in Hfind. destruct (Ident.eq_dec id id).
      inversion Hfind. contradiction.
Qed.


Theorem normalize_type_unrolls:
  forall env t,
    wf_env env ->
    wf_typ env t ->
    unrolled_typ (normalize_type env t).
Proof.
  intros env t [Hdup Henv] Hwf.
  induction Hwf; rewrite normalize_type_equation; simpl; auto;
    try constructor;
    try (apply IHHwf; auto);
    try (rewrite Forall_forall; intros;
         match goal with
         | [ H: In ?x (map_In _ _) |- _ ] =>  apply in_map_in in H as [t [Hin Hnorm]]
         end;

         rewrite <- Hnorm;

         match goal with
         | [ H: _ |- _ ] => apply H
         end; auto; solve_guard).
  - destruct (find (fun a : ident * typ => Ident.eq_dec id (fst a)) defs) as [[i t] |] eqn:Hfind.
    +
      apply find_some in Hfind as [Hin Heq].
      simpl in *. destruct (Ident.eq_dec id i); inversion Heq; subst.

      simpl_remove_keys.

      rewrite guarded_id_normalize_same; auto using wf_typ_is_guarded_wf_typ; solve_guard.
    + destruct H as [t Hin].
      eapply find_none in Hfind; eauto.
      simpl in Hfind. destruct (Ident.eq_dec id id).
      inversion Hfind. contradiction.
Qed.
