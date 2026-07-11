(* begin hide *)
From Vellvm Require Import
     Utils
     Syntax.LLVMAst
     Syntax.AstLib
     Syntax.CFG
     Syntax.Traversal
     Syntax.DynamicTypes.

Import CFGNotations.
(* end hide *)

(** * Conversion from static to dynamic types
    LLVM admits static types than can be recursive in the case of function types.
    At run-time, this information is unnecessary, we therefore pre-process them by
    converting them into a notion of dynamic types whose pointer type contains no
    further information.
    The conversion also inlines globally declared types (field [m_type_defs] of a [modul] (i.e. a [mcfg]).
 *)


Inductive typ_order : typ -> typ -> Prop :=
| typ_order_Pointer : forall (t : typ), typ_order t (TYPE_Pointer (Some t))
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
#[export] Hint Constructors typ_order : core.

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
Proof using.
  unfold well_founded.
  induction a; constructor; intros y H'; inversion H'; subst; auto.
Qed.

Theorem wf_lt_typ_order :
  well_founded (lex_ord lt typ_order).
Proof using.
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
Proof using.
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

#[export] Hint Resolve wf_lt_typ_order : core.
#[export] Hint Constructors lex_ord : core.

Program Fixpoint typ_to_dtyp_base_option (env : list (ident * typ)) (t : typ) {measure (List.length env) lt} : option dtyp_base :=
  match t with
  | TYPE_Function ret args varargs => Some DTYPE_Pointer
  | TYPE_Identified id =>
    let opt := find (fun a => Ident.eq_dec id (fst a)) env in
    match opt with
    | None => None
    | Some (_, t) => typ_to_dtyp_base_option (remove_key Ident.eq_dec id env) t
    end
  | TYPE_I sz => Some (DTYPE_I sz)
  | TYPE_Iptr => Some (DTYPE_Iptr)
  | TYPE_Pointer t' => Some DTYPE_Pointer
  | TYPE_Label => Some DTYPE_Label
  | TYPE_Token => Some DTYPE_Token
  | TYPE_Void => Some DTYPE_Void
  | TYPE_FP fp => Some (DTYPE_FP fp)
  | TYPE_Metadata => Some DTYPE_Metadata
  | TYPE_X86_mmx => Some DTYPE_X86_mmx
  | TYPE_Opaque => Some DTYPE_Opaque
  | TYPE_Array _ _ => None
  | TYPE_Struct _ => None
  | TYPE_Vector _ _ => None
  | TYPE_Packed_struct _ => None
  end.
Next Obligation.
  symmetry in Heq_opt. apply find_some in Heq_opt. destruct Heq_opt as [Hin Heqb_ident].
  simpl in Heqb_ident.
  destruct (Ident.eq_dec id wildcard'). subst. eapply remove_key_in. apply Hin.
  inversion Heqb_ident.
Defined.

Lemma typ_to_dtyp_base_option_equation  : forall env t,
  typ_to_dtyp_base_option env t =
  match t with
  | TYPE_Function ret args varargs => Some DTYPE_Pointer
  | TYPE_Identified id =>
    let opt := find (fun a => Ident.eq_dec id (fst a)) env in
    match opt with
    | None => None
    | Some (_, t) => typ_to_dtyp_base_option (remove_key Ident.eq_dec id env) t
    end
  | TYPE_I sz => Some (DTYPE_I sz)
  | TYPE_Iptr => Some (DTYPE_Iptr)
  | TYPE_Pointer t' => Some DTYPE_Pointer
  | TYPE_Label => Some DTYPE_Label
  | TYPE_Token => Some DTYPE_Token
  | TYPE_Void => Some DTYPE_Void
  | TYPE_FP fp => Some (DTYPE_FP fp)
  | TYPE_Metadata => Some DTYPE_Metadata
  | TYPE_X86_mmx => Some DTYPE_X86_mmx
  | TYPE_Opaque => Some DTYPE_Opaque
  | TYPE_Array _ _ => None
  | TYPE_Struct _ => None
  | TYPE_Vector _ _ => None
  | TYPE_Packed_struct _ => None
  end.
Proof using.
  intros env t.
  unfold typ_to_dtyp_base_option.
  unfold typ_to_dtyp_base_option_func at 1.
  rewrite WfExtensionality.WfExtensionality.fix_sub_eq_ext. simpl.
  destruct t; try reflexivity; simpl.
  destruct (find (fun a : ident * typ => Ident.eq_dec id (fst a)) env).
  destruct p; simpl; eauto.
  reflexivity.
Defined.

Program Fixpoint typ_to_dtyp (env : list (ident * typ)) (t : typ) {measure (List.length env, t) (lex_ord lt typ_order)} : dtyp :=
  match typ_to_dtyp_base_option env t with
  | Some dt => dt
  | None =>
      match t with
      | TYPE_Array sz t =>
          let nt := typ_to_dtyp env t in
          DTYPE_Array false sz nt

      | TYPE_Struct fields =>
          let nfields := map_In fields (fun t _ => typ_to_dtyp env t) in
          DTYPE_Struct false nfields

      | TYPE_Packed_struct fields =>
          let nfields := map_In fields (fun t _ => typ_to_dtyp env t) in
          DTYPE_Struct true nfields

      | TYPE_Vector sz t =>
          match typ_to_dtyp_base_option env t with
          | Some dt =>
              if (vector_dtyp_base_dec dt)
              then DTYPE_Array true sz dt
              else  DTYPE_Void
          | None =>  DTYPE_Void
          end
      | TYPE_Identified id =>
          let opt := find (fun a => Ident.eq_dec id (fst a)) env in
          match opt with
          | None =>  DTYPE_Void   (* TODO: should this be None? *)
          | Some (_, t) => typ_to_dtyp (remove_key Ident.eq_dec id env) t
          end
      (* These cases cannot happen *)
      | TYPE_Function ret args varargs =>  DTYPE_Void
      | TYPE_I sz =>  DTYPE_Void
      | TYPE_Iptr =>  DTYPE_Void
      | TYPE_Pointer t' =>  DTYPE_Void
      | TYPE_Label =>  DTYPE_Void
      | TYPE_Token =>  DTYPE_Void
      | TYPE_Void =>  DTYPE_Void
      | TYPE_FP fp =>  DTYPE_Void
      | TYPE_Metadata =>  DTYPE_Void
      | TYPE_X86_mmx =>  DTYPE_Void
      | TYPE_Opaque =>  DTYPE_Void
      end
  end.
Next Obligation.
  left.
  symmetry in Heq_opt. apply find_some in Heq_opt. destruct Heq_opt as [Hin Heqb_ident].
  simpl in Heqb_ident.
  destruct (Ident.eq_dec id wildcard'). subst. eapply remove_key_in. apply Hin.
  inversion Heqb_ident.
Defined.

Lemma typ_to_dtyp_equation  : forall env t,
    typ_to_dtyp env t =
  match typ_to_dtyp_base_option env t with
  | Some dt =>  dt
  | None =>
      match t with
      | TYPE_Array sz t =>
          let nt := typ_to_dtyp env t in
          DTYPE_Array false sz nt

      | TYPE_Struct fields =>
          let nfields := map_In fields (fun t _ => typ_to_dtyp env t) in
          DTYPE_Struct false nfields

      | TYPE_Packed_struct fields =>
          let nfields := map_In fields (fun t _ => typ_to_dtyp env t) in
          DTYPE_Struct true nfields

      | TYPE_Vector sz t =>
          match typ_to_dtyp_base_option env t with
          | Some dt =>
              if (vector_dtyp_base_dec dt)
              then DTYPE_Array true sz dt
              else  DTYPE_Void
          | None =>  DTYPE_Void
          end
      | TYPE_Identified id =>
          let opt := find (fun a => Ident.eq_dec id (fst a)) env in
          match opt with
          | None =>  DTYPE_Void   (* TODO: should this be None? *)
          | Some (_, t) => typ_to_dtyp (remove_key Ident.eq_dec id env) t
          end
      (* These cases cannot happen *)
      | TYPE_Function ret args varargs =>  DTYPE_Void
      | TYPE_I sz =>  DTYPE_Void
      | TYPE_Iptr =>  DTYPE_Void
      | TYPE_Pointer t' =>  DTYPE_Void
      | TYPE_Label =>  DTYPE_Void
      | TYPE_Token =>  DTYPE_Void
      | TYPE_Void =>  DTYPE_Void
      | TYPE_FP fp =>  DTYPE_Void
      | TYPE_Metadata =>  DTYPE_Void
      | TYPE_X86_mmx =>  DTYPE_Void
      | TYPE_Opaque =>  DTYPE_Void
      end
  end.
Proof using.
  intros env t.
  unfold typ_to_dtyp.
  unfold typ_to_dtyp_func at 1.
  rewrite WfExtensionality.WfExtensionality.fix_sub_eq_ext. simpl.
  destruct t; try reflexivity; simpl.
  - destruct (typ_to_dtyp_base_option env t); reflexivity.
  - destruct (typ_to_dtyp_base_option env (TYPE_Identified id)); simpl.
    + reflexivity.
    + destruct (find (fun a : ident * typ => Ident.eq_dec id (fst a)) env).
      destruct p; simpl; eauto.
  reflexivity.
Defined.

(* Specialized version of the characteristic equation for contexts where we don't want to compute *)
(* SAZ: Not sure where these are needed. *)
(*
Lemma typ_to_dtyp_I : forall s i, typ_to_dtyp s (TYPE_I i) =  (DTYPE_I i).
Proof using.
  intros; rewrite typ_to_dtyp_equation; reflexivity.
Qed.

Lemma typ_to_dtyp_D : forall s fp, typ_to_dtyp s (TYPE_FP fp) = ( (DTYPE_FP fp)).
Proof using.
  intros; rewrite typ_to_dtyp_equation; reflexivity.
Qed.

Lemma typ_to_dtyp_P :
  forall t s,
    typ_to_dtyp s (TYPE_Pointer t) = ( DTYPE_Pointer).
Proof using.
  intros t s.
  apply typ_to_dtyp_equation.
Qed.

Lemma typ_to_dtyp_D_array : forall n s fp, typ_to_dtyp s (TYPE_Array n (TYPE_FP fp)) = DTYPE_Array n (DTYPE_FP fp).
Proof using.
  intros.
  rewrite typ_to_dtyp_equation.
  rewrite typ_to_dtyp_D.
  reflexivity.
Qed.
*)

(** ** Conversion of syntactic components

    Front-ends and optimizations generate code containing static types.
    Since the semantics always acts upon dynamic types, in order to reason
    about the sub-components of code produce, we need to be able to convert
    types of any syntactic substructure of Vellvm.

    We leverage the parameterized [Tfmap] typeclass to do this in a fairly lightway.
 *)
Section ConvertTyp.

  Class ConvertTyp (F: Set -> Set) : Type :=
    convert_typ : list (ident * typ) -> F typ -> F dtyp.

  #[global] Instance ConvertTyp_exp : ConvertTyp exp :=
    fun env => tfmap (typ_to_dtyp env).

  #[global] Instance ConvertTyp_instr : ConvertTyp instr :=
    fun env => tfmap (typ_to_dtyp env).

  #[global] Instance ConvertTyp_term : ConvertTyp terminator :=
    fun env => tfmap (typ_to_dtyp env).

  #[global] Instance ConvertTyp_code : ConvertTyp code :=
    fun env => tfmap (typ_to_dtyp env).

  #[global] Instance ConvertTyp_phi : ConvertTyp phi :=
    fun env => tfmap (typ_to_dtyp env).

  #[global] Instance ConvertTyp_block : ConvertTyp block :=
    fun env => tfmap (typ_to_dtyp env).

  #[global] Instance ConvertTyp_declaration : ConvertTyp declaration :=
    fun env => tfmap (typ_to_dtyp env).
  
  #[global] Instance ConvertTyp_cfg : ConvertTyp cfg :=
    fun env => tfmap (typ_to_dtyp env).

  #[global] Instance ConvertTyp_mcfg : ConvertTyp mcfg :=
    fun env => tfmap (typ_to_dtyp env).

  #[global] Instance ConvertTyp_list {A} `{TFunctor A}: ConvertTyp (fun T => list (A T)) :=
    fun env => tfmap (typ_to_dtyp env).

End ConvertTyp.

Lemma convert_typ_list_app :
  forall {F} `{TFunctor F} (a b : list (F typ)) (env : list (ident * typ)),
    convert_typ env (a ++ b)%list = (convert_typ env a ++ convert_typ env b)%list.
Proof using.
  intros F H a.
  induction a; cbn; intros; auto.
  rewrite IHa; reflexivity.
Qed.

(**
     Conversion to dynamic types
 *)

Definition convert_types (CFG:(CFG.mcfg typ)) : (CFG.mcfg dtyp) :=
  convert_typ (m_type_defs CFG) CFG.

Lemma convert_typ_ocfg_app : forall (a b : ocfg typ) env, (convert_typ env (a ++ b) = convert_typ env a ++ convert_typ env b)%list.
Proof using.
  intros; rewrite convert_typ_list_app; reflexivity.
Qed.

Lemma convert_typ_code_app : forall (a b : code typ) env, (convert_typ env (a ++ b) = convert_typ env a ++ convert_typ env b)%list.
Proof using.
  induction a as [| [] a IH]; cbn; intros; auto.
  rewrite IH; reflexivity.
Qed.

Lemma convert_typ_mcfg_app:
  forall mcfg1 mcfg2 : modul (cfg typ),
    convert_typ [] (mcfg1 @@ mcfg2) =
    convert_typ [] mcfg1 @@ convert_typ [] mcfg2.
Proof using.
  intros [] []; cbn.
  unfold convert_typ,ConvertTyp_mcfg,tfmap,TFunctor_mcfg; cbn.
  f_equal; try (unfold endo, Endo_option; cbn; repeat flatten_goal; now intuition).
  unfold tfmap, TFunctor_list; rewrite map_app; reflexivity.
  unfold tfmap, TFunctor_list'; rewrite map_app; reflexivity.
  unfold tfmap, TFunctor_list'; rewrite map_app; reflexivity.
  unfold tfmap, TFunctor_list'; rewrite map_app; reflexivity.
Qed.

Lemma convert_types_app_mcfg : forall mcfg1 mcfg2,
    m_type_defs mcfg1 = [] ->
    m_type_defs mcfg2 = [] ->
    convert_types (modul_app mcfg1 mcfg2) =
    modul_app (convert_types mcfg1) (convert_types mcfg2).
Proof using.
  unfold convert_types.
  intros * EQ1 EQ2.
  rewrite m_type_defs_app, EQ1,EQ2.
  cbn; rewrite convert_typ_mcfg_app.
  reflexivity.
Qed.

Lemma mcfg_of_tle_app : forall x y,
    m_type_defs (mcfg_of_modul (modul_of_toplevel_entities x)) = nil ->
    m_type_defs (mcfg_of_modul (modul_of_toplevel_entities y)) = nil ->
    convert_types (mcfg_of_tle (x ++ y)) =
    modul_app (convert_types (mcfg_of_tle x)) (convert_types (mcfg_of_tle y)).
Proof using.
  intros.
  unfold mcfg_of_tle.
  rewrite modul_of_toplevel_entities_app.
  rewrite mcfg_of_app_modul.
  rewrite convert_types_app_mcfg; auto.
Qed.

Lemma mcfg_of_tle_cons : forall x y,
    m_type_defs (mcfg_of_modul (modul_of_toplevel_entities [x])) = nil ->
    m_type_defs (mcfg_of_modul (modul_of_toplevel_entities y)) = nil ->
    convert_types (mcfg_of_tle (x :: y)) =
    modul_app (convert_types  (mcfg_of_tle [x])) (convert_types  (mcfg_of_tle y)).
Proof using.
  intros; rewrite list_cons_app; apply mcfg_of_tle_app; auto.
Qed.
