(** * Conversion from static to dynamic types
    LLVM admits static types than can be recursive in the case of function types.
    At run-time, this information is unnecessary, we therefore pre-process them by
    converting them into a notion of dynamic types whose pointer type contains no
    further information.
    The conversion also inlines globally declared types (field [m_type_defs] of a [modul] (i.e. a [mcfg]).
*)
From Coq Require Import
     List
     String
     Logic.FunctionalExtensionality.

From Vellvm Require Import 
     Util
     LLVMAst
     AstLib
     DynamicTypes
     CFG
     Transformations.Traversal.

Require Import Coqlib.

Import ListNotations.
Open Scope list_scope.

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
Hint Constructors typ_order : core.

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

Theorem wf_typ_order :
    well_founded typ_order.
Proof.
  unfold well_founded.
  induction a using typ_ind'; constructor; intros y H'; inversion H'; subst; auto.
Qed.

Theorem wf_lt_typ_order :
  well_founded (lex_ord lt typ_order).
Proof.
  apply wf_lex_ord.
  apply lt_wf. apply wf_typ_order.
Qed.

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
    + simpl. apply lt_n_S. apply IHl.
      destruct H.
      * inversion H. subst. contradiction.
      * assumption.
Qed.

Hint Resolve wf_lt_typ_order : core.
Hint Constructors lex_ord : core.

Program Fixpoint typ_to_dtyp (env : list (ident * typ)) (t : typ) {measure (List.length env, t) (lex_ord lt typ_order)} : dtyp :=
  match t with
  | TYPE_Array sz t =>
    let nt := typ_to_dtyp env t in
    DTYPE_Array sz nt

  | TYPE_Function ret args =>
    (*
    let nret := (normalize_type env ret) in
    let nargs := map_In args (fun t _ => normalize_type env t) in *)
    DTYPE_Pointer (* Function nret nargs *)

  | TYPE_Struct fields =>
    let nfields := map_In fields (fun t _ => typ_to_dtyp env t) in
    DTYPE_Struct nfields

  | TYPE_Packed_struct fields =>
    let nfields := map_In fields (fun t _ => typ_to_dtyp env t) in
    DTYPE_Packed_struct nfields

  | TYPE_Vector sz t =>
    let nt := typ_to_dtyp env t in
    DTYPE_Vector sz nt

  | TYPE_Identified id =>
    let opt := find (fun a => Ident.eq_dec id (fst a)) env in
    match opt with
    | None => DTYPE_Void   (* TODO: should this be None? *)
    | Some (_, t) => typ_to_dtyp (remove_key Ident.eq_dec id env) t
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
  symmetry in Heq_opt. apply find_some in Heq_opt. destruct Heq_opt as [Hin Heqb_ident].
  simpl in Heqb_ident.
  destruct (Ident.eq_dec id wildcard'). subst. eapply remove_key_in. apply Hin.
  inversion Heqb_ident.
Defined.

(** ** Conversion of syntactic components

    Front-ends and optimizations generate code containing static types.
    Since the semantics always acts upon dynamic types, in order to reason
    about the sub-components of code produce, we need to be able to convert
    types of any syntactic substructure of Vellvm.

    We leverage the parameterized [Fmap] typeclass to do this in a fairly lightway.
 *)
Section ConvertTyp.

  Class ConvertTyp (F: Set -> Set) : Type :=
    convert_typ : list (ident * typ) -> F typ -> F dtyp.

  Global Instance ConvertTyp_exp : ConvertTyp exp :=
    fun env => fmap (typ_to_dtyp env).

  Global Instance ConvertTyp_instr : ConvertTyp instr :=
    fun env => fmap (typ_to_dtyp env).

  Global Instance ConvertTyp_term : ConvertTyp terminator :=
    fun env => fmap (typ_to_dtyp env).

  Global Instance ConvertTyp_code : ConvertTyp code :=
    fun env => fmap (typ_to_dtyp env).

  Global Instance ConvertTyp_phi : ConvertTyp phi :=
    fun env => fmap (typ_to_dtyp env).

  Global Instance ConvertTyp_block : ConvertTyp block :=
    fun env => fmap (typ_to_dtyp env).

  Global Instance ConvertTyp_cfg : ConvertTyp cfg :=
    fun env => fmap (typ_to_dtyp env).

  Global Instance ConvertTyp_mcfg : ConvertTyp mcfg :=
    fun env => fmap (typ_to_dtyp env).

End ConvertTyp.  
