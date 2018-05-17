Require Import List String.
Require Import Vellvm.Util.
Require Import Vellvm.LLVMAst.
Require Import Vellvm.AstLib.
Require Import Vellvm.LLVMIO.
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


Definition wf_env (env : list (ident * typ)) : Prop :=
  NoDup (map fst env) -> Forall (wf_typ env) (map snd env).


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
Defined.


Definition sum (l : list nat) : nat := fold_left plus l 0%nat.


Theorem wf_lt_typ_order :
  well_founded (lex_ord lt typ_order).
Proof.
  apply wf_lex_ord.
  apply lt_wf. apply wf_typ_order.
Defined.

Hint Resolve wf_lt_typ_order.
Hint Constructors lex_ord.


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
Defined.


Program Fixpoint normalize_type (env : list (ident * typ)) (t : typ) {measure (List.length env, t) (lex_ord lt typ_order)} : dtyp :=
  match t with
  | TYPE_Array sz t =>
    let nt := normalize_type env t in
    DTYPE_Array sz nt

  | TYPE_Function ret args =>
    (*
    let nret := (normalize_type env ret) in
    let nargs := map_In args (fun t _ => normalize_type env t) in *)
    DTYPE_Pointer (* Function nret nargs *)

  | TYPE_Struct fields =>
    let nfields := map_In fields (fun t _ => normalize_type env t) in
    DTYPE_Struct nfields

  | TYPE_Packed_struct fields =>
    let nfields := map_In fields (fun t _ => normalize_type env t) in
    DTYPE_Packed_struct nfields

  | TYPE_Vector sz t =>
    let nt := normalize_type env t in
    DTYPE_Vector sz nt

  | TYPE_Identified id =>
    let opt := find (fun a => eqb_ident id (fst a)) env in
    match opt with
    | None => DTYPE_Void   (* TODO: should this be None? *)
    | Some (_, t) => normalize_type (remove_key Ident.eq_dec id env) t
    end

  | TYPE_I sz => DTYPE_I sz
  | TYPE_Pointer t' => DTYPE_Pointer
  | TYPE_Void => DTYPE_Void
  | TYPE_Half => DTYPE_Half
  | TYPE_Float => DTYPE_Float
  | TYPE_Double => DTYPE_Double
  | TYPE_X86_fp80 => DTYPE_X86_fp80
  | TYPE_Fp128 => DTYPE_Fp128
  | TYPE_Ppc_fp128 => DTYPE_Ppc_fp128
  | TYPE_Metadata => DTYPE_Metadata
  | TYPE_X86_mmx => DTYPE_X86_mmx
  | TYPE_Opaque => DTYPE_Opaque
  end.
Next Obligation.
  left.
  remember (find (fun a : ident * typ => eqb_ident id (fst a)) env) as o.
  destruct o.
  symmetry in Heqo.
  apply find_some in Heqo.
  destruct Heqo as [Hin Heqb_ident].
  apply eqb_ident_correct in Heqb_ident.
  inversion Heq_opt. destruct p. inversion H0. subst.
  eapply remove_key_in. simpl. apply Hin.
  inversion Heq_opt.
Defined.


Lemma normalize_type_equation : forall env t,
    normalize_type env t =
    match t with
  | TYPE_Array sz t =>
    let nt := normalize_type env t in
    DTYPE_Array sz nt

  | TYPE_Function ret args =>
    (*
    let nret := (normalize_type env ret) in
    let nargs := map_In args (fun t _ => normalize_type env t) in *)
    DTYPE_Pointer (* Function nret nargs *)

  | TYPE_Struct fields =>
    let nfields := map_In fields (fun t _ => normalize_type env t) in
    DTYPE_Struct nfields

  | TYPE_Packed_struct fields =>
    let nfields := map_In fields (fun t _ => normalize_type env t) in
    DTYPE_Packed_struct nfields

  | TYPE_Vector sz t =>
    let nt := normalize_type env t in
    DTYPE_Vector sz nt

  | TYPE_Identified id =>
    let opt := find (fun a => eqb_ident id (fst a)) env in
    match opt with
    | None => DTYPE_Void   (* TODO: should this be None? *)
    | Some (_, t) => normalize_type (remove_key Ident.eq_dec id env) t
    end

  | TYPE_I sz => DTYPE_I sz
  | TYPE_Pointer t' => DTYPE_Pointer
  | TYPE_Void => DTYPE_Void
  | TYPE_Half => DTYPE_Half
  | TYPE_Float => DTYPE_Float
  | TYPE_Double => DTYPE_Double
  | TYPE_X86_fp80 => DTYPE_X86_fp80
  | TYPE_Fp128 => DTYPE_Fp128
  | TYPE_Ppc_fp128 => DTYPE_Ppc_fp128
  | TYPE_Metadata => DTYPE_Metadata
  | TYPE_X86_mmx => DTYPE_X86_mmx
  | TYPE_Opaque => DTYPE_Opaque
  end.
Proof.
  intros env t.
  unfold normalize_type. 
  unfold normalize_type_func at 1.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext.
  destruct t; try reflexivity. simpl.
  destruct (find (fun a : ident * typ => eqb_ident id (fst a)) env).
  destruct p; simpl; reflexivity.
  reflexivity.
Defined.    

  

Lemma example: normalize_type [] TYPE_Void = DTYPE_Void.
Proof.
  rewrite normalize_type_equation. reflexivity.
Qed.  
  
  