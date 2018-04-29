Require Import List String.
Require Import Vellvm.Util.
Require Import Vellvm.LLVMAst.
Require Import Vellvm.AstLib.
Require Import Vellvm.Classes.
Require Import Coqlib.
Require Import Coq.Logic.FunctionalExtensionality.


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


Lemma eqb_ident_correct :
  forall (a : ident) (b : ident),
    eqb_ident a b = true ->
    a = b.
Proof.
  intros a b H.
  destruct a, b; intuition.
  - destruct id, id0; try (inversion H).
    destruct (string_dec s s0); subst; try reflexivity; try inversion H1.
    apply Z.eqb_eq in H1. subst. reflexivity.
    apply Z.eqb_eq in H1. subst. reflexivity.
  - destruct id, id0; try (inversion H).
    destruct (string_dec s s0); subst; try reflexivity; try inversion H1.
    apply Z.eqb_eq in H1. subst. reflexivity.
    apply Z.eqb_eq in H1. subst. reflexivity.
Qed.


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

| guarded_typ_Function :
    forall (id : ident) (env : list (ident * typ)) (ret : typ) (args : list typ),
      guarded_typ id env ret ->
      (forall a, In a args -> guarded_typ id env a) ->
      guarded_typ id env (TYPE_Function ret args)

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
      guarded_typ id env (TYPE_Packed_struct fields)

| guarded_typ_Opaque :
    forall (id : ident) (env : list (ident * typ)),
      guarded_typ id env TYPE_Opaque

| guarded_typ_Vector :
    forall (id : ident) (env : list (ident * typ)) (sz : int) (t : typ),
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

| wf_typ_Function :
    forall (defs : list (ident * typ)) (ret : typ) (args : list typ),
      function_ret_typ ret ->
      wf_typ defs ret ->
      (forall (a : typ), In a args -> sized_typ defs a) ->
      (forall (a : typ), In a args -> wf_typ defs a) ->
      wf_typ defs (TYPE_Function ret args)

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


Hint Constructors wf_typ.


Definition wf_env (env : list (ident * typ)) : Prop :=
  NoDup (map fst env) /\ Forall (wf_typ env) (map snd env).


Inductive guarded_wf_typ : list (ident * typ) -> typ -> Prop :=
| guarded_wf_typ_Pointer:
    forall (defs : list (ident * typ)) (t : typ),
      guarded_wf_typ defs (TYPE_Pointer t)

| guarded_wf_typ_I :
    forall (defs : list (ident * typ)) (sz : int),
      sz > 0 -> guarded_wf_typ defs (TYPE_I sz)

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
    forall (defs : list (ident * typ)) (ret : typ) (args : list typ),
      function_ret_typ ret ->
      guarded_wf_typ defs ret ->
      (forall (a : typ), In a args -> sized_typ defs a) ->
      (forall (a : typ), In a args -> guarded_wf_typ defs a) ->
      guarded_wf_typ defs (TYPE_Function ret args)

(* Arrays are only well formed if the size is >= 0, and the element type is sized. *)
| guarded_wf_typ_Array :
    forall (defs : list (ident * typ)) (sz : int) (t : typ),
      sz >= 0 -> sized_typ defs t -> guarded_wf_typ defs t -> guarded_wf_typ defs (TYPE_Array sz t)

(* Vectors of size 0 are not allowed, and elemnts must be of element_typ. *)
| guarded_wf_typ_Vector :
    forall (defs : list (ident * typ)) (sz : int) (t : typ),
      sz > 0 -> element_typ t -> guarded_wf_typ defs t -> guarded_wf_typ defs (TYPE_Vector sz t)

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

Hint Constructors guarded_wf_typ.


Theorem wf_typ_is_guarded_wf_typ :
  forall env t,
    wf_typ env t ->
    guarded_wf_typ env t.
Proof.
  intros env t H.
  induction H; auto.
Qed.


Inductive unrolled_typ : typ -> Prop :=
| unrolled_typ_I :
    forall (sz : int),
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
    forall (sz : int) (t : typ),
      unrolled_typ t ->
      unrolled_typ (TYPE_Array sz t)

| unrolled_typ_Function :
    forall (ret : typ) (args : list typ),
      unrolled_typ ret ->
      Forall unrolled_typ args ->
      unrolled_typ (TYPE_Function ret args)

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
    forall (sz : int) (t : typ), unrolled_typ (TYPE_Vector sz t)
.


Inductive typ_order : typ -> typ -> Prop :=
| typ_order_Pointer : forall (t : typ), typ_order t (TYPE_Pointer t)
| typ_order_Array : forall (sz : int) (t : typ), typ_order t (TYPE_Array sz t)
| typ_order_Vector : forall (sz : int) (t : typ), typ_order t (TYPE_Vector sz t)
| typ_order_Struct : forall (fields : list typ),
    forall f, In f fields -> typ_order f (TYPE_Struct fields)
| typ_order_Packed_struct : forall (fields : list typ),
    forall f, In f fields -> typ_order f (TYPE_Packed_struct fields)
| typ_order_Function_args : forall (ret : typ) (args : list typ),
    forall a, In a args -> typ_order a (TYPE_Function ret args)
| typ_order_Function_ret : forall (ret : typ) (args : list typ),
    typ_order ret (TYPE_Function ret args)
.


Hint Constructors typ_order.


Theorem wf_typ_order :
    well_founded typ_order.
Proof.
  unfold well_founded.
  induction a using typ_ind'; constructor; intros y H'; inversion H'; subst; auto.
Qed.


Definition sum (l : list nat) : nat := fold_left plus l 0%nat.


Theorem wf_lt_typ_order :
  well_founded (lex_ord lt typ_order).
Proof.
  apply wf_lex_ord.
  apply lt_wf. apply wf_typ_order.
Qed.

Hint Resolve wf_lt_typ_order.
Hint Constructors lex_ord.

Definition length_order {A : Type} (l1 l2 : list A) :=
  (List.length l1 < List.length l2)%nat.


Lemma lengthOrder_wf' : forall A len, forall ls, (List.length ls <= len)%nat -> Acc (@length_order A) ls.
  unfold length_order; induction len.
  - intros ls H. inversion H. rewrite length_zero_iff_nil in H1. subst.
    constructor. intros y H0. inversion H0.
  - intros ls H. inversion H.
    + constructor. intros y H0. apply IHlen. omega.
    + auto.
Defined.

Theorem lengthOrder_wf : forall A, well_founded (@length_order A).
  red; intros A a; eapply lengthOrder_wf'; eauto.
Defined.


Theorem wf_length_typ_order :
  forall A,
    well_founded (lex_ord (@length_order A) typ_order).
Proof.
  intros A. apply wf_lex_ord.
  apply lengthOrder_wf. apply wf_typ_order.
Defined.


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


Lemma remove_key_in :
  forall (A B : Type) (a : A)  (b : B) eq_dec l,
    In (a, b) l ->
    (List.length (remove_key eq_dec a l) < List.length l)%nat.
Proof.
  induction l.
  - intros H. inversion H.
  - intros H.
    destruct a0.
    simpl. destruct (eq_dec a a0).
    + apply Nat.lt_succ_diag_r.
    + simpl. apply lt_n_S. apply IHl.
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
  - simpl in *. destruct a0. destruct (eq_dec a a0).
    + intuition.
    + rewrite IHl; intuition.
Qed.


Lemma remove_key_commutes :
  forall (A B : Type) (k1 k2 : A) eq_dec (l : list (A * B)),
    remove_key eq_dec k1 (remove_key eq_dec k2 l) = remove_key eq_dec k2 (remove_key eq_dec k1 l).
Proof.
  intros A B k1 k2 eq_dec l.
  induction l; auto.
  simpl. destruct a.
  destruct (eq_dec k2 a) eqn:Hk2a.
  - destruct (eq_dec k1 a).
    + subst; auto.
    + subst. simpl. destruct (eq_dec a a); try contradiction.
      reflexivity.
  - destruct (eq_dec k1 a) eqn:Hk1a.
    + subst. simpl. destruct (eq_dec a a); try contradiction.
      reflexivity.
    + simpl. rewrite Hk2a. rewrite Hk1a. rewrite IHl.
      reflexivity.
Qed.  


Lemma remove_key_keys :
  forall (A B : Type) (keys : list A) eq_dec (key : A) (l : list (A * B)),
    remove_key eq_dec key (remove_keys eq_dec keys l) = remove_keys eq_dec (key :: keys) l.
Proof.
  intros A B keys.
  induction keys; intros eq_dec key l; auto.
  simpl in *.
  rewrite IHkeys.
  apply f_equal.
  apply remove_key_commutes.
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

  | TYPE_Function ret args =>
    let nret := (normalize_type env ret) in
    let nargs := map_In args (fun t _ => normalize_type env t) in
    TYPE_Function nret nargs

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

  | TYPE_Function ret args =>
    let nret := (normalize_type env ret) in
    let nargs := map_In args (fun t _ => normalize_type env t) in
    TYPE_Function nret nargs

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


Hint Constructors unrolled_typ.


Lemma find_in_wf_env :
  forall env id t,
    NoDup (map fst env) ->
    In (id, t) env ->
    find (fun a : ident * typ => Ident.eq_dec id (fst a)) env = Some (id, t).
Proof.
  intros env id t Hdup Hin.
  induction env as [| [id' t'] env].
  - contradiction.
  - destruct Hin as [Hin | Hin]; try inversion Hin; subst.
    + simpl. destruct (Ident.eq_dec id id); intuition.
    + simpl. destruct (Ident.eq_dec id id').
      * inversion Hdup. subst. apply in_map with (f:=fst) in Hin. simpl in *.
        contradiction.
      * simpl. inversion Hdup.
        apply IHenv; auto.
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
  induction env.
  - reflexivity.
  - destruct a as [i t]. simpl.
    destruct (Ident.eq_dec id' i) eqn:Heq.
    + simpl. destruct (Ident.eq_dec id i); subst.
      * contradiction.
      * simpl. destruct (Ident.eq_dec i i); try contradiction.
        reflexivity.
    + simpl. destruct (Ident.eq_dec id i); subst.
      * intuition.
      * simpl. rewrite Heq. simpl. auto.
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
    rewrite <- find_different_key_from_removed with (id:=a); intuition; subst; intuition.
Qed.

Lemma trans :
  forall {A} {a b c : A},
    c = a ->
    c = b ->
    a = b.
Proof.
  intros A a b c Hca Hcb.
  subst. reflexivity.
Qed.


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
    destruct (Ident.eq_dec id i).
    + simpl. subst. simpl in Hdup. inversion Hin.
      * inversion H0. reflexivity.
      * inversion Hdup. subst.
        exfalso. apply H3.
        assert (i = fst (i, t)) by reflexivity.
        rewrite H1.
        apply in_map. auto.
    + simpl. apply IHenv.
      * simpl in Hdup. inversion Hdup. auto.
      * simpl in Hin. inversion Hin.
        -- inversion H0. symmetry in H2. contradiction.
        -- assumption.
      * simpl in H. destruct (Ident.eq_dec id i); try contradiction. simpl in H.
        assumption.
Qed.

Hint Constructors sized_typ.
Hint Constructors guarded_typ.


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
    forall ret args,
      simple_typ ret ->
      (forall a, In a args -> simple_typ a) ->
      simple_typ (TYPE_Function ret args)
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


Hint Constructors simple_typ.


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
      exists t. intuition.      
Qed.


Theorem map_rewrite :
  forall {A B : Type} (x : A) (l : list A) (f g : A -> B),
    (forall x, In x l -> f x = g x) ->
    map_In l (fun t (_ : In t l) => f t) = map_In l (fun t (_ : In t l) => g t).
Proof.
  intros A B x l f g H.
  induction l as [| a l]; simpl; auto.
  pose proof (H a) as Ha.
  rewrite Ha; intuition.
  rewrite IHl; intuition.
Qed.


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
    rewrite normalize_type_equation; symmetry; rewrite normalize_type_equation; simpl; auto.
  4: { simpl. 

       replace (remove_key Ident.eq_dec id (remove_keys Ident.eq_dec ids defs)) with
           (remove_keys Ident.eq_dec (id :: ids) defs) by auto using remove_key_keys.

       (* True because id not in ids.

          because if id is in ids, this means that guarded_typ id defs
          (TYPE_Identified id), which is a contradiction.

        *)
       assert ((find (fun a : ident * typ => Ident.eq_dec id (fst a)) (remove_keys Ident.eq_dec ids defs)) = (find (fun a : ident * typ => Ident.eq_dec id (fst a)) defs)) as Hfind_removekeys.
       assert (~ In id ids). unfold not. intros Hinidids.
       pose proof Hguard id Hinidids as Hguard'.
       inversion Hguard'; contradiction.
       symmetry; auto using remove_keys_find.

       rewrite Hfind_removekeys.

       destruct (find (fun a : ident * typ => Ident.eq_dec id (fst a)) defs) eqn:Hfind.
       - destruct p. simpl.

         assert (In (id, t) defs).
         apply find_some in Hfind as [Hin Hfind].
         simpl in Hfind.
         destruct (Ident.eq_dec id i) eqn:Hidi; subst; intuition.
         
         replace (remove_keys Ident.eq_dec ids (remove_key Ident.eq_dec id defs)) with
             (remove_keys Ident.eq_dec (id :: ids) defs) by auto using remove_keys_key.

         rewrite H2; auto.

         replace (remove_key Ident.eq_dec id defs) with
             (remove_keys Ident.eq_dec [id] defs) by auto.

         rewrite H2; auto.
         + intros id0 H4. destruct H4.
           * subst; auto.
           * inversion H4.
         + intros id0 H4. destruct H4.
           * subst; auto.
           * pose proof (Hguard id0 H4) as Hguard'. inversion Hguard'; subst.
             -- rewrite Hfind in H7. inversion H7. subst. auto.
             -- rewrite Hfind in H9. inversion H9.
       - reflexivity.
     }
  - rewrite IHHwf; auto.
    rewrite map_rewrite with (f:=normalize_type (remove_keys _ _ _)) (g:=normalize_type defs); auto.
    intros x H3. apply H2; auto.
    all: intros id Hidin; pose proof Hguard id Hidin as Hguard'; inversion Hguard'; auto.
  - rewrite IHHwf; auto.
    intros id Hidin.
    pose proof Hguard id Hidin as Hguard'. inversion Hguard'; auto.
  - rewrite IHHwf; auto;
    intros id Hidin;
    match goal with
    | [H : element_typ _ |- _] => inversion H
    end; auto.
  - rewrite map_rewrite with (f:=normalize_type (remove_keys _ _ _)) (g:=normalize_type defs); auto.
    exact (TYPE_Void).
    intros x H2. apply H1; auto.
    intros id Hidin; pose proof Hguard id Hidin as Hguard'; inversion Hguard'; auto.
  - rewrite map_rewrite with (f:=normalize_type (remove_keys _ _ _)) (g:=normalize_type defs); auto.
    exact (TYPE_Void).
    intros x H2. apply H1; auto.
    intros id Hidin; pose proof Hguard id Hidin as Hguard'; inversion Hguard'; auto.
Qed.


Theorem double_map_In :
  forall A B C (l : list A) (f : A -> B) (g : B -> C),
    (map_In (map_In l (fun x (_ : In x l) => f x)) (fun x (_ : In x (map_In l (fun x (_ : In x l) => f x))) => g x)) = map_In l (fun x (_ : In x l) => g (f x)).
Proof.
  intros A B C l f g.
  induction l.
  - reflexivity.
  - simpl. auto using f_equal.
Qed.


Theorem guarded_normalize_same :
  forall t env,
    NoDup (map fst env) ->
    guarded_wf_typ env t ->
    (forall ids,
        (forall id, In id ids -> guarded_typ id env t) ->
        normalize_type env (normalize_type env t) = normalize_type env t).
Proof.
  intros t env Hdup Hwf ids Hguard_all.
  induction Hwf; try solve [rewrite normalize_type_equation; symmetry; rewrite normalize_type_equation; simpl; auto].
  - rewrite normalize_type_equation; symmetry; rewrite normalize_type_equation; simpl; auto.

    rewrite IHHwf; auto.
    rewrite double_map_In.
    rewrite map_rewrite with (f:=fun x => normalize_type defs (normalize_type defs x)) (g:=normalize_type defs); auto.
    intros x Hin. apply H2; auto.
    all: intros id Hinids; pose proof Hguard_all _ Hinids as Hguard'; inversion Hguard'; auto.

  - rewrite normalize_type_equation; symmetry; rewrite normalize_type_equation; simpl; auto.

    rewrite IHHwf; auto.
    intros id Hinids; pose proof Hguard_all _ Hinids as Hguard'; inversion Hguard'; auto.

  - rewrite normalize_type_equation; symmetry; rewrite normalize_type_equation; simpl; auto.

    rewrite IHHwf; auto.
    intros id Hinids;
      match goal with
      | [H : element_typ _ |- _] => inversion H
      end; auto.
  - symmetry. rewrite normalize_type_equation. simpl.

    destruct (find (fun a : ident * typ => Ident.eq_dec id (fst a)) defs) eqn:Hfind.
    + destruct p.

      assert (In (id, t) defs).
      apply find_some in Hfind as [Hin Hfind].
      simpl in Hfind.
      destruct (Ident.eq_dec id i) eqn:Hidi; subst; intuition.

      symmetry.
      replace (remove_key Ident.eq_dec id defs) with (remove_keys Ident.eq_dec [id] defs) by auto.
      rewrite guarded_id_normalize_same; auto.
      apply H2; auto.
      * intros id0 Hinids; pose proof Hguard_all _ Hinids as Hguard'. inversion Hguard'; auto; subst.
        -- rewrite Hfind in H6. inversion H6; subst; auto.
        -- rewrite Hfind in H8. inversion H8.
      * intros id0 H4. inversion H4. subst. auto.
        inversion H5.
    + rewrite normalize_type_equation. simpl. rewrite Hfind. reflexivity.
  - rewrite normalize_type_equation; symmetry; rewrite normalize_type_equation; simpl; auto.
    rewrite double_map_In.
    rewrite map_rewrite with (f:=fun x => normalize_type defs (normalize_type defs x)) (g:=normalize_type defs); auto.
    exact TYPE_Void.
    intros x H2. rewrite H1; auto.
    intros id0 Hinids; pose proof Hguard_all _ Hinids as Hguard'. inversion Hguard'; auto.
  - rewrite normalize_type_equation; symmetry; rewrite normalize_type_equation; simpl; auto.
    rewrite double_map_In.
    rewrite map_rewrite with (f:=fun x => normalize_type defs (normalize_type defs x)) (g:=normalize_type defs); auto.
    exact TYPE_Void.
    intros x H2. rewrite H1; auto.
    intros id0 Hinids; pose proof Hguard_all _ Hinids as Hguard'. inversion Hguard'; auto.
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
  induction Hwf; try solve [rewrite normalize_type_equation; symmetry; rewrite normalize_type_equation; simpl; auto].
  4 : {
        simpl.

        symmetry.
        rewrite normalize_type_equation. simpl.

        destruct (find (fun a : ident * typ => Ident.eq_dec id (fst a)) defs) as [[i t] |] eqn:Hfind.
        - 
          apply find_some in Hfind as [Hin Heq].
          simpl in *. destruct (Ident.eq_dec id i); inversion Heq; subst.

          replace (remove_key _ i defs) with (remove_keys Ident.eq_dec [i] defs) by auto.


          rewrite guarded_id_normalize_same; auto using wf_typ_is_guarded_wf_typ.
          + symmetry. apply H2; auto.
          + intros id H3.
            inversion H3; subst; try contradiction; auto.
        - rewrite normalize_type_equation. simpl. rewrite Hfind.
          reflexivity.
        }

        - rewrite normalize_type_equation. symmetry. rewrite normalize_type_equation.
          simpl. rewrite double_map_In.
          rewrite IHHwf; auto.
          symmetry.
          rewrite map_rewrite with (g:=normalize_type defs) at 1; auto.
        - rewrite normalize_type_equation. symmetry. rewrite normalize_type_equation.
          simpl. rewrite IHHwf; auto.
        - rewrite normalize_type_equation. symmetry. rewrite normalize_type_equation.
          simpl. rewrite IHHwf; auto.
        - rewrite normalize_type_equation. symmetry. rewrite normalize_type_equation.
          simpl. rewrite double_map_In.
          symmetry.
          rewrite map_rewrite with (g:=normalize_type defs) at 1; auto.
          exact TYPE_Void.
        - rewrite normalize_type_equation. symmetry. rewrite normalize_type_equation.
          simpl. rewrite double_map_In.
          symmetry.
          rewrite map_rewrite with (g:=normalize_type defs) at 1; auto.
          exact TYPE_Void.
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
  induction Hwf; rewrite normalize_type_equation; simpl; auto.
  - constructor.
    + apply IHHwf; auto.
      intros id H3.
      pose proof Hguard_all _ H3 as Hguard'. inversion Hguard'; auto.
    + rewrite Forall_forall. intros x H3.
      apply in_map_in in H3 as [t [Hin Hnorm]].
      rewrite <- Hnorm.
      apply H2; auto.
      intros id H3.
      pose proof Hguard_all _ H3 as Hguard'. inversion Hguard'; auto.
  - constructor. apply IHHwf; auto.
    intros id H1.
    pose proof Hguard_all _ H1 as Hguard'. inversion Hguard'; auto.
  - destruct (find (fun a : ident * typ => Ident.eq_dec id (fst a)) defs) as [[i t] |] eqn:Hfind.
    + pose proof Hfind as Hfind'.
      apply find_some in Hfind' as [Hin Heq].
      simpl in *. destruct (Ident.eq_dec id i) as [He | He]; inversion Heq.

      rewrite He.
      replace (remove_key _ i defs) with (remove_keys Ident.eq_dec [i] defs) by auto.
      rewrite guarded_id_normalize_same; auto.
      * apply H2; auto. subst; auto.
        intros id0 H3.
        pose proof Hguard_all _ H3 as Hguard'; inversion Hguard'; auto.
        -- rewrite Hfind in H6. inversion H6; subst; auto.
        -- rewrite Hfind in H8. inversion H8.
      * subst; try contradiction; auto.
      * intros id0 H3.
        inversion H3; subst.
        -- apply H0; auto.
        -- inversion H4.
    + destruct H as [t Hin].
      eapply find_none in Hfind; eauto.
      simpl in Hfind. destruct (Ident.eq_dec id id).
      inversion Hfind. contradiction.
  - constructor.
    rewrite Forall_forall.
    intros x H2.
    apply in_map_in in H2 as [t [Hin Hnorm]].
    rewrite <- Hnorm.
    apply H1; auto.
    intros id H2.
    pose proof Hguard_all _ H2 as Hguard'. inversion Hguard'; auto.
  - constructor.
    rewrite Forall_forall.
    intros x H2.
    apply in_map_in in H2 as [t [Hin Hnorm]].
    rewrite <- Hnorm.
    apply H1; auto.
    intros id H2.
    pose proof Hguard_all _ H2 as Hguard'. inversion Hguard'; auto.
Qed.



Theorem normalize_type_unrolls:
  forall env t,
    wf_env env ->
    wf_typ env t ->
    unrolled_typ (normalize_type env t).
Proof.
  intros env t [Hdup Henv] Hwf.
  induction Hwf; rewrite normalize_type_equation; simpl; auto.
  - constructor.
    + apply IHHwf; auto.
    + rewrite Forall_forall. intros x H3.
      apply in_map_in in H3 as [t [Hin Hnorm]].
      rewrite <- Hnorm.
      apply H2; auto.
  - destruct (find (fun a : ident * typ => Ident.eq_dec id (fst a)) defs) as [[i t] |] eqn:Hfind.
    +
      apply find_some in Hfind as [Hin Heq].
      simpl in *. destruct (Ident.eq_dec id i); inversion Heq; subst.

      replace (remove_key _ i defs) with (remove_keys Ident.eq_dec [i] defs) by auto.


      rewrite guarded_id_normalize_same; auto using wf_typ_is_guarded_wf_typ.
      intros id H3.
      inversion H3; subst; try contradiction; auto.
    + destruct H as [t Hin].
      eapply find_none in Hfind; eauto.
      simpl in Hfind. destruct (Ident.eq_dec id id).
      inversion Hfind. contradiction.
  - constructor.
    rewrite Forall_forall.
    intros x H2.
    apply in_map_in in H2 as [t [Hin Hnorm]].
    rewrite <- Hnorm.
    apply H1; auto.
  - constructor.
    rewrite Forall_forall.
    intros x H2.
    apply in_map_in in H2 as [t [Hin Hnorm]].
    rewrite <- Hnorm.
    apply H1; auto.
Qed.
