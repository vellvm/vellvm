
Require Import ZArith.

(* CompCert dependencies *)
Require Import compcert.lib.Integers.

(* Vellvm dependencies *)
Require Import Vellvm.Ollvm_ast Vellvm.CFG Vellvm.StepSemantics Vellvm.Memory.
Require Import Vellvm.Classes.
Require Import Vellvm.AstLib.

(** ** Decidable Equality *) 

Instance eq_dec_int : eq_dec (BinNums.Z) := Z.eq_dec.

Ltac discriminate_goal :=
  intro HFalse; inversion HFalse; tauto.

Ltac lift_decide_eq :=
  match goal with
  | |- forall x y, Decidable (x = y) =>
    induction x; destruct y; unfold Decidable;
    try (right; intro H; inversion H; tauto);
    try lift_decide_eq
  | |- { ?C ?x = ?C ?y} + { ~(?C ?x = ?C ?y) } =>
    destruct (decide (x = y));
    [subst; auto | right; discriminate_goal]
  | |- { ?C ?x1 ?x2 = ?C ?y1 ?y2} + { ~(?C ?x1 ?x2 = ?C ?y1 ?y2) } =>
    try (destruct (decide (x1 = y1));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x2 = y2));
         [subst; auto | right; discriminate_goal])
  | |- { ?C ?x1 ?x2 ?x3 = ?C ?y1 ?y2 ?y3} + { ~(?C ?x1 ?x2 ?x3 = ?C ?y1 ?y2 ?y3) } =>
    try (destruct (decide (x1 = y1));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x2 = y2));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x3 = y3));
         [subst; auto | right; discriminate_goal])
  | |- { ?C ?x1 ?x2 ?x3 ?x4 = ?C ?y1 ?y2 ?y3 ?y4}
      + { ~(?C ?x1 ?x2 ?x3 ?x4 = ?C ?y1 ?y2 ?y3 ?y4) } =>
    try (destruct (decide (x1 = y1));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x2 = y2));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x3 = y3));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x4 = y4));
         [subst; auto | right; discriminate_goal])
  | |- { ?C ?x1 ?x2 ?x3 ?x4 ?x5 = ?C ?y1 ?y2 ?y3 ?y4 ?y5} +
      { ~(?C ?x1 ?x2 ?x3 ?x4 ?x5 = ?C ?y1 ?y2 ?y3 ?y4 ?y5) } =>
    try (destruct (decide (x1 = y1));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x2 = y2));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x3 = y3));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x4 = y4));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x5 = y5));
         [subst; auto | right; discriminate_goal])
  end.

Ltac lift_decide_eq_from_inside_dv :=
  match goal with
  | |- { DV (?C ?x) = DV (?C ?y)} + { ~(DV (?C ?x) = DV (?C ?y)) } =>
    destruct (decide (x = y));
    [subst; auto | right; discriminate_goal]
  | |- { DV (?C ?x1 ?x2) = DV (?C ?y1 ?y2)} +
      { ~(DV (?C ?x1 ?x2) = DV (?C ?y1 ?y2)) } =>
    try (destruct (decide (x1 = y1));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x2 = y2));
         [subst; auto | right; discriminate_goal])
  | |- { DV (?C ?x1 ?x2 ?x3) = DV (?C ?y1 ?y2 ?y3)} +
      { ~(DV (?C ?x1 ?x2 ?x3) = DV (?C ?y1 ?y2 ?y3)) } =>
    try (destruct (decide (x1 = y1));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x2 = y2));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x3 = y3));
         [subst; auto | right; discriminate_goal])
  | |- { DV (?C ?x1 ?x2 ?x3 ?x4) = DV (?C ?y1 ?y2 ?y3 ?y4) }
      + { ~(DV (?C ?x1 ?x2 ?x3 ?x4) = DV (?C ?y1 ?y2 ?y3 ?y4)) } =>
    try (destruct (decide (x1 = y1));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x2 = y2));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x3 = y3));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x4 = y4));
         [subst; auto | right; discriminate_goal])
  | |- { DV (?C ?x1 ?x2 ?x3 ?x4 ?x5) = DV (?C ?y1 ?y2 ?y3 ?y4 ?y5) } +
      { ~(DV (?C ?x1 ?x2 ?x3 ?x4 ?x5) = DV (?C ?y1 ?y2 ?y3 ?y4 ?y5)) } =>
    try (destruct (decide (x1 = y1));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x2 = y2));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x3 = y3));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x4 = y4));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x5 = y5));
         [subst; auto | right; discriminate_goal])
  end.

Ltac lift_decide_eq_from_inside_sv :=
  match goal with
  | |- { SV (?C ?x) = SV (?C ?y)} + { ~(SV (?C ?x) = SV (?C ?y)) } =>
    destruct (decide (x = y));
    [subst; auto | right; discriminate_goal]
  | |- { SV (?C ?x1 ?x2) = SV (?C ?y1 ?y2)} +
      { ~(SV (?C ?x1 ?x2) = SV (?C ?y1 ?y2)) } =>
    try (destruct (decide (x1 = y1));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x2 = y2));
         [subst; auto | right; discriminate_goal])
  | |- { SV (?C ?x1 ?x2 ?x3) = SV (?C ?y1 ?y2 ?y3)} +
      { ~(SV (?C ?x1 ?x2 ?x3) = SV (?C ?y1 ?y2 ?y3)) } =>
    try (destruct (decide (x1 = y1));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x2 = y2));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x3 = y3));
         [subst; auto | right; discriminate_goal])
  | |- { SV (?C ?x1 ?x2 ?x3 ?x4) = SV (?C ?y1 ?y2 ?y3 ?y4) }
      + { ~(SV (?C ?x1 ?x2 ?x3 ?x4) = SV (?C ?y1 ?y2 ?y3 ?y4)) } =>
    try (destruct (decide (x1 = y1));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x2 = y2));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x3 = y3));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x4 = y4));
         [subst; auto | right; discriminate_goal])
  | |- { SV (?C ?x1 ?x2 ?x3 ?x4 ?x5) = SV (?C ?y1 ?y2 ?y3 ?y4 ?y5) } +
      { ~(SV (?C ?x1 ?x2 ?x3 ?x4 ?x5) = SV (?C ?y1 ?y2 ?y3 ?y4 ?y5)) } =>
    try (destruct (decide (x1 = y1));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x2 = y2));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x3 = y3));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x4 = y4));
         [subst; auto | right; discriminate_goal]);
    try (destruct (decide (x5 = y5));
         [subst; auto | right; discriminate_goal])
  end.


Instance eq_dec_global_id : eq_dec global_id.
Proof. lift_decide_eq. Defined.

Instance eq_dec_function_id : eq_dec function_id.
Proof. lift_decide_eq. Defined.

Instance eq_dec_block_id : eq_dec block_id.
Proof. lift_decide_eq. Defined.

Instance eq_dec_local_id : eq_dec local_id.
Proof. lift_decide_eq. Defined.

Instance eq_dec_instr_id : eq_dec instr_id.
Proof. lift_decide_eq. Defined.

Definition typ_strong_ind: forall P : Ollvm_ast.typ -> Set,
    (forall sz : int, P (TYPE_I sz)) ->
    (forall t : Ollvm_ast.typ, P t -> P (TYPE_Pointer t)) ->
    P TYPE_Void ->
    P TYPE_Half ->
    P TYPE_Float ->
    P TYPE_Double ->
    P TYPE_X86_fp80 ->
    P TYPE_Fp128 ->
    P TYPE_Ppc_fp128 ->
    P TYPE_Metadata ->
    P TYPE_X86_mmx ->
    (forall (sz : int) (t : Ollvm_ast.typ), P t -> P (TYPE_Array sz t)) ->
    (forall ret : Ollvm_ast.typ,
        P ret -> P (TYPE_Function ret [])) ->
    (forall (ret: Ollvm_ast.typ) (arg : Ollvm_ast.typ) (args : list Ollvm_ast.typ),
        P ret -> P arg -> P (TYPE_Function ret args) -> P (TYPE_Function ret (arg :: args))) ->
    P (TYPE_Struct []) ->
    (forall (new_field : Ollvm_ast.typ) (fields : list Ollvm_ast.typ),
        P new_field -> P (TYPE_Struct fields) -> P (TYPE_Struct (new_field :: fields))) ->
    P (TYPE_Packed_struct []) ->
    (forall (new_field : Ollvm_ast.typ) (fields : list Ollvm_ast.typ),
        P new_field -> P (TYPE_Packed_struct fields) ->
        P (TYPE_Packed_struct (new_field :: fields))) ->
    P TYPE_Opaque ->
    (forall (sz : int) (t : Ollvm_ast.typ), P t -> P (TYPE_Vector sz t)) ->
    (forall id : ident, P (TYPE_Identified id)) ->
    forall t : Ollvm_ast.typ, P t.
Proof.
  intros P HTYPE_I IHTYPE_Pointer HTYPE_Void HTYPE_Half HTYPE_Float
         HTYPE_Double HTYPE_X86_fp80 HTYPE_Fp128 HTYPE_Ppc_fp128
         HTYPE_Metadata HTYPE_X86_mmx.
  intros IHTYPE_Array IHTYPE_FunctionBase IHTYPE_FunctionInd
         IHTYPE_StructBase IHTYPE_StructInd
         IHTYPE_PackedStructBase IHTYPE_PackedStructInd
         HTYPE_Opaque IHTYPE_Vector HTYPE_Ident.
  refine
    (fix prove_t (t : Ollvm_ast.typ) : P t :=
       match t with
       | TYPE_I sz => _
       | TYPE_Pointer t' => IHTYPE_Pointer t' (prove_t t')
       | TYPE_Void => _
       | TYPE_Half => _
       | TYPE_Float => _
       | TYPE_Double => _
       | TYPE_X86_fp80 => _
       | TYPE_Fp128 => _
       | TYPE_Ppc_fp128 => _
       | TYPE_Metadata => _
       | TYPE_X86_mmx => _
       | TYPE_Opaque => _
       | TYPE_Identified id => _
       | TYPE_Array sz t' => IHTYPE_Array sz t' (prove_t t')
       | TYPE_Function ret args =>
         let fix prove_l (l : list Ollvm_ast.typ) :=
             match l with
             | [] => IHTYPE_FunctionBase ret (prove_t ret)
             | (t' :: ts) =>
               IHTYPE_FunctionInd ret t' ts
                   (prove_t ret)     
                   (prove_t t')
                   (prove_l ts)
             end
         in prove_l args
       | TYPE_Struct fields =>
         let fix prove_l base ind (l : list Ollvm_ast.typ) :=
             match l with
             | [] => base
             | (t' :: ts) =>
               ind t' ts
                   (prove_t t')
                   (prove_l base ind ts)
             end
         in
         prove_l IHTYPE_StructBase IHTYPE_StructInd fields
       | TYPE_Packed_struct fields => 
         let fix prove_l base ind (l : list Ollvm_ast.typ) :=
             match l with
             | [] => base
             | (t' :: ts) =>
               ind t' ts
                   (prove_t t')
                   (prove_l base ind ts)
             end
         in
         prove_l IHTYPE_PackedStructBase IHTYPE_PackedStructInd fields
       | TYPE_Vector sz t' => IHTYPE_Vector sz t' (prove_t t')
       end);
  auto.
Defined.

Instance eq_dec_ollvm_ast_typ : eq_dec Ollvm_ast.typ.
Proof.
  induction x using typ_strong_ind; destruct y;
    unfold Decidable;
    try (right; intro H; inversion H; tauto);
    try lift_decide_eq;
    try auto.
  - destruct args; auto.
  - refine
      (match args0 with
       | [] => right _
       | (y2 :: ys) =>
         match decide (x2 = y2) with
         | left x2_eq_y2 => _
         | right _ => right _
         end
       end).
    { intro H; inversion H. }
    { subst.
      refine (match decide (TYPE_Function y args = TYPE_Function y ys) with
              | left args_eq_ys => left _
              | right _ => right _
              end).
      { inversion args_eq_ys; subst; auto. }
      { intros H. inversion H. subst; auto. }
    } 
    { intros H; inversion H; subst; auto. }
  - destruct fields; auto.
  - refine (match fields0 with
            | [] => right _
            | y :: ys =>
              match decide (x = y) with
              | left x_eq_y =>
                match decide (TYPE_Struct fields = TYPE_Struct ys) with
                | left fields_eq_ys => left _
                | right _ => right _
                end
              | right _ => right _
              end
            end).
    { intros H; inversion H; subst; auto. }
    { inversion fields_eq_ys; subst; auto. }
    { intros H; inversion H; subst; auto. }
    { intros H; inversion H; subst; auto. }
  - destruct fields; auto.
  - refine (match fields0 with
            | [] => right _
            | y :: ys =>
              match decide (x = y) with
              | left x_eq_y =>
                match decide (TYPE_Packed_struct fields = TYPE_Packed_struct ys) with
                | left fields_eq_ys => left _
                | right _ => right _
                end
              | right _ => right _
              end
            end).
    { intros H; inversion H; subst; auto. }
    { inversion fields_eq_ys; subst; auto. }
    { intros H; inversion H; subst; auto. }
    { intros H; inversion H; subst; auto. }
Defined.

Instance eq_dec_int1 : eq_dec Int1.int := Int1.eq_dec.
Instance eq_dec_int32 : eq_dec Int32.int := Int32.eq_dec.
Instance eq_dec_int64 : eq_dec Int64.int := Int64.eq_dec.

Instance eq_dec_ibinop : eq_dec ibinop.
Proof.
  lift_decide_eq; left; auto.
Defined.

Instance eq_dec_icmp : eq_dec icmp.
Proof.
  lift_decide_eq; left; auto.
Defined.

Instance eq_dec_fbinop : eq_dec fbinop.
Proof.
  lift_decide_eq; left; auto.
Defined.

Instance eq_dec_fast_math : eq_dec fast_math.
Proof.
  lift_decide_eq; left; auto.
Defined.

Instance eq_dec_fcmp : eq_dec fcmp.
Proof.
  lift_decide_eq; left; auto.
Defined.

Instance eq_dec_conversion_type : eq_dec conversion_type.
Proof.
  lift_decide_eq; left; auto.
Defined.

Instance decide_expr {A : Set} `{decide_value : eq_dec A} : eq_dec (Expr A).
Proof.
  destruct x; destruct y; unfold Decidable;
    try (right; intro H; inversion H; tauto);
    try (left; reflexivity);
    try (lift_decide_eq).
Defined.

Definition expr_dvalue_ind: forall (P : dvalue -> Set),
    (forall id : ident, P (DV (VALUE_Ident id))) ->
    (forall x : int, P (DV (VALUE_Integer x))) ->
    (forall f : float, P (DV (VALUE_Float f))) ->
    (forall b : bool, P (DV (VALUE_Bool b))) ->
    (P (DV VALUE_Null)) ->
    (P (DV (VALUE_Zero_initializer))) ->
    (forall s : String.string, P (DV (VALUE_Cstring s))) ->
    (P (DV VALUE_None)) ->
    (P (DV VALUE_Undef)) ->
    (P (DV (VALUE_Struct []))) ->
    (forall t v fields,
        P v ->
        P (DV (VALUE_Struct fields)) ->
        P (DV (VALUE_Struct ((t, v) :: fields)))) ->
    (P (DV (VALUE_Packed_struct []))) ->
    (forall t v fields,
        P v ->
        P (DV (VALUE_Packed_struct fields)) ->
        P (DV (VALUE_Packed_struct ((t, v) :: fields)))) ->
    (P (DV (VALUE_Array []))) ->
    (forall t v arr,
        P v ->
        P (DV (VALUE_Array arr)) ->
        P (DV (VALUE_Array ((t, v) :: arr)))) ->
    (P (DV (VALUE_Vector []))) ->
    (forall t v vec,
        P v ->
        P (DV (VALUE_Vector vec)) ->
        P (DV (VALUE_Vector ((t, v) :: vec)))) ->
    (forall iop t v1 v2,
        P v1 -> P v2 ->
        P (DV (OP_IBinop iop t v1 v2))) ->
    (forall cmp t v1 v2,
        P v1 -> P v2 ->
        P (DV (OP_ICmp cmp t v1 v2))) ->
    (forall fop fm t v1 v2,
        P v1 -> P v2 ->
        P (DV (OP_FBinop fop fm t v1 v2))) ->
    (forall cmp t v1 v2,
        P v1 -> P v2 ->
        P (DV (OP_FCmp cmp t v1 v2))) ->
    (forall conv t_from v t_to,
        P v -> P (DV (OP_Conversion conv t_from v t_to))) ->
    (forall t ptr_t ptr_v,
        P (ptr_v) ->
        P (DV (OP_GetElementPtr t (ptr_t, ptr_v) []))) ->
    (forall t ptr_t ptr_v idx_t idx_v indices,
        P (ptr_v) ->
        P (idx_v) ->
        P (DV (OP_GetElementPtr t (ptr_t, ptr_v) indices)) ->
        P (DV (OP_GetElementPtr t (ptr_t, ptr_v) ((idx_t, idx_v) :: indices)))) ->
    (forall vec_t vec_v idx_t idx_v,
        P vec_v -> P idx_v -> P (DV (OP_ExtractElement (vec_t, vec_v) (idx_t, idx_v)))) ->
    (forall vec_t vec_v elt_t elt_v idx_t idx_v,
        P vec_v -> P elt_v -> P idx_v ->
        P (DV (OP_InsertElement (vec_t, vec_v) (elt_t, elt_v) (idx_t, idx_v)))) ->
    (forall vec1_t vec1_v vec2_t vec2_v idxmask_t idxmask_v,
        P vec1_v -> P vec2_v -> P (idxmask_v) ->
        P (DV (OP_ShuffleVector (vec1_t, vec1_v) (vec2_t, vec2_v) (idxmask_t, idxmask_v)))) ->
    (forall vec_t vec_v idxs,
        P vec_v -> P (DV (OP_ExtractValue (vec_t, vec_v) idxs))) ->
    (forall vec_t vec_v elt_t elt_v idxs,
        P vec_v -> P elt_v ->
        P (DV (OP_InsertValue (vec_t, vec_v) (elt_t, elt_v) idxs))) ->
    (forall cnd_t cnd_v v1_t v1_v v2_t v2_v,
        P cnd_v -> P v1_v -> P v2_v ->
        P (DV (OP_Select (cnd_t, cnd_v) (v1_t, v1_v) (v2_t, v2_v)))) ->

    (forall p : instr_id, P (DVALUE_CodePointer p)) ->
    (forall a : A.addr, P (DVALUE_Addr a)) ->
    (forall x : Int1.int, P (DVALUE_I1 x)) ->
    (forall x : Int32.int, P (DVALUE_I32 x)) ->
    (forall x : Int64.int, P (DVALUE_I64 x)) ->
    (P DVALUE_Poison) ->
    (forall v : dvalue, P v).
Proof.
  intros P H_Ident H_Integer H_Float H_Bool H_Null
         H_Zero_initializer H_Cstring H_None H_Undef.
  intros IH_Struct_Base IH_Struct_Ind
         IH_Packed_struct_Base IH_Packed_struct_Ind
         IH_Array_Base IH_Array_Ind
         IH_Vector_Base IH_Vector_Ind
         IH_IBinop IH_ICmp IH_FBinop IH_FCmp
         IH_Conversion
         IH_GetElementPtr_Base IH_GetElementPtr_Ind
         IH_ExtractElement IH_InsertElement
         IH_ShuffleVector IH_ExtractValue IH_InsertValue
         IH_Select
         H_CodePointer H_Addr H_I1 H_I32 H_I64 H_Poison.

  refine
    (fix prove_dv (v : dvalue) :=
       match v with
       | DV e =>
         match e with
         | VALUE_Ident id => _
         | VALUE_Integer n => _
         | VALUE_Float f => _
         | VALUE_Bool b => _
         | VALUE_Null => _
         | VALUE_Zero_initializer => _
         | VALUE_Cstring s => _
         | VALUE_None => _
         | VALUE_Undef => _
         | VALUE_Struct l =>
           let
             fix prove_l (l : list (Ollvm_ast.typ * dvalue)) :=
             match l with
             | [] => IH_Struct_Base
             | (t, v) :: rest =>
               IH_Struct_Ind t v rest (prove_dv v) (prove_l rest)
             end
           in prove_l l 
         | VALUE_Packed_struct l =>
           let
             fix prove_l (l : list (Ollvm_ast.typ * dvalue)) :=
             match l with
             | [] => IH_Packed_struct_Base
             | (t, v) :: rest =>
               IH_Packed_struct_Ind t v rest (prove_dv v) (prove_l rest)
             end
           in prove_l l 
         | VALUE_Array l =>
           let
             fix prove_l (l : list (Ollvm_ast.typ * dvalue)) :=
             match l with
             | [] => IH_Array_Base
             | (t, v) :: rest =>
               IH_Array_Ind t v rest (prove_dv v) (prove_l rest)
             end
           in prove_l l 

         | VALUE_Vector l =>
           let
             fix prove_l (l : list (Ollvm_ast.typ * dvalue)) :=
             match l with
             | [] => IH_Vector_Base
             | (t, v) :: rest =>
               IH_Vector_Ind t v rest (prove_dv v) (prove_l rest)
             end
           in prove_l l            

         | OP_IBinop op t v1 v2 =>
           IH_IBinop op t v1 v2 (prove_dv v1) (prove_dv v2) 
         | OP_ICmp op t v1 v2 => 
           IH_ICmp op t v1 v2 (prove_dv v1) (prove_dv v2) 
         | OP_FBinop op fm t v1 v2 =>
           IH_FBinop op fm t v1 v2 (prove_dv v1) (prove_dv v2) 
         | OP_FCmp op t v1 v2 =>
           IH_FCmp op t v1 v2 (prove_dv v1) (prove_dv v2) 
         | OP_Conversion conv t_from v t_to =>
           IH_Conversion conv t_from v t_to (prove_dv v)
           
         | OP_GetElementPtr t (ptr_t, ptr_v) l =>
           let fix prove_l (l : list (Ollvm_ast.typ * dvalue)) :=
               match l with
               | [] =>
                 IH_GetElementPtr_Base t ptr_t ptr_v (prove_dv ptr_v)
               | (idx_t, idx_v) :: rest =>
                 IH_GetElementPtr_Ind t ptr_t ptr_v idx_t idx_v rest
                                      (prove_dv ptr_v) (prove_dv idx_v)
                                      (prove_l rest)
               end
           in prove_l l
           
         | OP_ExtractElement (vec_t, vec_v) (idx_t, idx_v) =>
           IH_ExtractElement vec_t vec_v idx_t idx_v
                             (prove_dv vec_v) (prove_dv idx_v)
         | OP_InsertElement (vec_t, vec_v) (elt_t, elt_v) (idx_t, idx_v) =>
           IH_InsertElement vec_t vec_v elt_t elt_v idx_t idx_v
                            (prove_dv vec_v) (prove_dv elt_v) (prove_dv idx_v)
         | OP_ShuffleVector (vec1_t, vec1_v) (vec2_t, vec2_v) (idxmask_t, idxmask_v) => 
           IH_ShuffleVector vec1_t vec1_v vec2_t vec2_v idxmask_t idxmask_v
                            (prove_dv vec1_v) (prove_dv vec2_v) (prove_dv idxmask_v)
         | OP_ExtractValue (vec_t, vec_v) idxs =>
           IH_ExtractValue vec_t vec_v idxs (prove_dv vec_v) 
         | OP_InsertValue (vec_t, vec_v) (elt_t, elt_v) idxs =>
           IH_InsertValue vec_t vec_v elt_t elt_v idxs
                          (prove_dv vec_v) (prove_dv elt_v)
         | OP_Select (cnd_t, cnd_v) (v1_t, v1_v) (v2_t, v2_v) =>
           IH_Select cnd_t cnd_v v1_t v1_v v2_t v2_v
                     (prove_dv cnd_v) (prove_dv v1_v) (prove_dv v2_v)
         end
         
       | DVALUE_CodePointer p => _
       | DVALUE_Addr a => _
       | DVALUE_I1 x => _
       | DVALUE_I32 x => _
       | DVALUE_I64 x => _
       | DVALUE_Poison => _
       end
    ); auto.
Defined.  

Instance eq_dvalue : eq_dec dvalue.
Proof.
  induction x using expr_dvalue_ind; destruct y; 
    try (right; intro H; inversion H; tauto);
    try (lift_decide_eq);
    try destruct e; unfold Decidable;
      try (right; intro H; inversion H; tauto);
      try (lift_decide_eq_from_inside_dv);
      try solve [left; auto];
      try solve [lift_decide_eq].

  (* DV (VALUE_Struct ...) *)
  - destruct fields; auto.
  - refine
      (match fields0 with
       | [] => right _
       | (t', v') :: fields' =>
         match (decide (t = t')) with
         | left t_eq =>
           match decide (x = v') with
           | left value_eq =>
             match decide (DV (VALUE_Struct fields) =
                           DV (VALUE_Struct fields')) with
             | left fields_eq => left _
             | right fields_neq => right _
             end
           | right value_neq => right _
           end
         | right t_neq => right _
         end
       end).
    { intros H; inversion H. }
    { inversion fields_eq. subst. reflexivity. }
    { intros H; inversion H; apply fields_neq; subst; auto. }
    { intros H; inversion H; apply value_neq; subst; auto. }
    { intros H; inversion H; apply t_neq; subst; auto. }

    (* DV (VALUE_Packed_struct ...) *)
  - destruct fields; auto.
  - refine
      (match fields0 with
       | [] => right _
       | (t', v') :: fields' =>
         match (decide (t = t')) with
         | left t_eq =>
           match decide (x = v') with
           | left value_eq =>
             match decide (DV (VALUE_Packed_struct fields) =
                           DV (VALUE_Packed_struct fields')) with
             | left fields_eq => left _
             | right fields_neq => right _
             end
           | right value_neq => right _
           end
         | right t_neq => right _
         end
       end).
    { intros H; inversion H. }
    { inversion fields_eq. subst. reflexivity. }
    { intros H; inversion H; apply fields_neq; subst; auto. }
    { intros H; inversion H; apply value_neq; subst; auto. }
    { intros H; inversion H; apply t_neq; subst; auto. }

    (* DV (VALUE_Array ...) *)
  - destruct elts; auto.
  - destruct elts as [| (t', x') arr']; auto.
    refine
      (match (decide (t = t')) with
       | left t_eq =>
         match (decide (x = x')) with
         | left value_eq =>
           match decide (DV (VALUE_Array arr) = DV (VALUE_Array arr')) with
           | left rest_eq => left _
           | right rest_neq => right _
           end
         | right value_neq => right _
         end
       | right t_neq => right _
       end).
    { inversion rest_eq; subst; auto. }
    { intros H; inversion H; apply rest_neq; subst; auto. }
    { intros H; inversion H; apply value_neq; subst; auto. }
    { intros H; inversion H; apply t_neq; subst; auto. }

    (* DV (VALUE_Vector *)
  - destruct elts; auto.
  - destruct elts as [| (t', x') vec']; auto.
    refine
      (match (decide (t = t')) with
       | left t_eq =>
         match (decide (x = x')) with
         | left value_eq =>
           match decide (DV (VALUE_Vector vec) = DV (VALUE_Vector vec')) with
           | left rest_eq => left _
           | right rest_neq => right _
           end
         | right value_neq => right _
         end
       | right t_neq => right _
       end).
    { inversion rest_eq; subst; auto. }
    { intros H; inversion H; apply rest_neq; subst; auto. }
    { intros H; inversion H; apply value_neq; subst; auto. }
    { intros H; inversion H; apply t_neq; subst; auto. }

    (* DV (OP_GetElementPtr ...) *)
  - destruct ptrval as (ptr_t', ptr_v');
      destruct idxs; try (right; intros H; inversion H; tauto).
    refine
      (match decide (ptr_t = ptr_t') with
       | left t_eq =>
         match decide (x = ptr_v') with
         | left ptr_value_eq => left _
         | right ptr_value_neq => right _
         end
       | right t_neq => right _
       end).
    { subst; reflexivity. } 
    { intros H; inversion H; apply ptr_value_neq; subst; auto. }
    { intros H; inversion H; apply t_neq; subst; auto. }
  - destruct ptrval as (ptr_t', ptr_v');
      destruct idxs as [| (idx_t', idx_v')];
      try (right; intros H; inversion H; tauto).
    refine
      (match decide (ptr_t = ptr_t') with
       | left ptr_t_eq =>
         match decide (x1 = ptr_v') with
         | left ptr_value_eq =>
           match decide (idx_t = idx_t') with
           | left idx_t_eq =>
             match decide (x2 = idx_v') with
             | left idx_value_eq => _
             | right idx_value_neq => right _
             end
           | right idx_t_neq => right _
           end
         | right ptr_value_neq => right _
         end
       | right t_neq => right _
       end).
    { subst.
      refine
        (match decide (DV (OP_GetElementPtr t0 (ptr_t', ptr_v') indices) =
                       DV (OP_GetElementPtr t0 (ptr_t', ptr_v') idxs)) with
         | left rest_eq => left _
         | right rest_neq => right _
         end).
      { inversion rest_eq; subst; auto. }
      { intros H; inversion H; apply rest_neq; subst; auto. }
    }
    { intros H; inversion H; apply idx_value_neq; subst; auto. }
    { intros H; inversion H; apply idx_t_neq; subst; auto. }
    { intros H; inversion H; apply ptr_value_neq; subst; auto. }
    { intros H; inversion H; apply t_neq; subst; auto. }

    (* DV (OP_ExtractElement ...), arity 2 *)
  - destruct vec as (vec_t', vec_v');
      destruct idx as (idx_t', idx_v');
      try (right; intros H; inversion H; tauto).
    refine (match decide (vec_t = vec_t') with
            | left vec_t_eq =>
              match decide (x1 = vec_v') with
              | left vec_v_eq =>
                match decide (idx_t = idx_t') with
                | left idx_t_eq =>
                  match decide (x2 = idx_v') with
                  | left idx_v_eq => left _
                  | right idx_v_neq => right _
                  end
                | right idx_t_neq => right _
                end
              | right vec_v_neq => right _
              end
            | right vec_t_neq => right _
            end); subst; auto.
    { intros H; inversion H; apply idx_v_neq; subst; auto. }
    { intros H; inversion H; apply idx_t_neq; subst; auto. }
    { intros H; inversion H; apply vec_v_neq; subst; auto. }
    { intros H; inversion H; apply vec_t_neq; subst; auto. }

    (* DV (OP_InsertElement ...), arity 3 *)
  - destruct vec as (vec_t', vec_v');
      destruct elt as (elt_t', elt_v');      
      destruct idx as (idx_t', idx_v');
      try (right; intros H; inversion H; tauto).
    refine (match decide (vec_t = vec_t') with
            | left vec_t_eq =>
              match decide (x1 = vec_v') with
              | left vec_v_eq =>
                match decide (elt_t = elt_t') with
                | left elt_t_eq =>
                  match decide (x2 = elt_v') with
                  | left elt_v_eq => 
                    match decide (idx_t = idx_t') with
                    | left idx_t_eq =>
                      match decide (x3 = idx_v') with
                      | left idx_v_eq => left _
                      | right idx_v_neq => right _
                      end
                    | right idx_t_neq => right _
                    end
                  | right elt_v_neq => right _
                  end
                | right elt_t_neq => right _
                end                  
              | right vec_v_neq => right _
              end
            | right vec_t_neq => right _
            end); subst; auto.
    { intros H; inversion H; apply idx_v_neq; subst; auto. }
    { intros H; inversion H; apply idx_t_neq; subst; auto. }
    { intros H; inversion H; apply elt_v_neq; subst; auto. }
    { intros H; inversion H; apply elt_t_neq; subst; auto. }    
    { intros H; inversion H; apply vec_v_neq; subst; auto. }
    { intros H; inversion H; apply vec_t_neq; subst; auto. }

    (* DV (OP_ShuffleVector ...) ; Same as DV (OP_InsertElement ...), with arity 3 *)
  - destruct vec1 as (vec1_t', vec1_v');
      destruct vec2 as (vec2_t', vec2_v');      
      destruct idxmask as (idxmask_t', idxmask_v');
      try (right; intros H; inversion H; tauto).
    refine (match decide (vec1_t = vec1_t') with
            | left vec1_t_eq =>
              match decide (x1 = vec1_v') with
              | left vec1_v_eq =>
                match decide (vec2_t = vec2_t') with
                | left vec2_t_eq =>
                  match decide (x2 = vec2_v') with
                  | left vec2_v_eq => 
                    match decide (idxmask_t = idxmask_t') with
                    | left idxmask_t_eq =>
                      match decide (x3 = idxmask_v') with
                      | left idxmask_v_eq => left _
                      | right idxmask_v_neq => right _
                      end
                    | right idxmask_t_neq => right _
                    end
                  | right vec2_v_neq => right _
                  end
                | right vec2_t_neq => right _
                end                  
              | right vec1_v_neq => right _
              end
            | right vec1_t_neq => right _
            end); subst; auto.
    { intros H; inversion H; apply idxmask_v_neq; subst; auto. }
    { intros H; inversion H; apply idxmask_t_neq; subst; auto. }
    { intros H; inversion H; apply vec2_v_neq; subst; auto. }
    { intros H; inversion H; apply vec2_t_neq; subst; auto. }    
    { intros H; inversion H; apply vec1_v_neq; subst; auto. }
    { intros H; inversion H; apply vec1_t_neq; subst; auto. }

    (* DV (OP_ExtractValue ...) ; Same as DV (OP_ *)
  - destruct vec as (vec_t', vec_v');
      try (right; intros H; inversion H; tauto).
    refine
      (match decide (vec_t = vec_t') with
       | left t_eq =>
         match decide (x = vec_v') with
         | left v_eq => left _
         | right v_neq => right _
         end
       | right t_neq => right _
       end); subst; auto.
    { intros H; inversion H; apply v_neq; subst; auto. }
    { intros H; inversion H; apply t_neq; subst; auto. }

    (* DV (OP_InsertValue ...) *)
  - destruct vec as (vec_t', vec_v');
      destruct elt as (elt_t', elt_v');
      try (right; intros H; inversion H; tauto).
    refine (match decide (vec_t = vec_t') with
            | left vec_t_eq =>
              match decide (x1 = vec_v') with
              | left vec_v_eq =>
                match decide (elt_t = elt_t') with
                | left elt_t_eq =>
                  match decide (x2 = elt_v') with
                  | left elt_v_eq => left _
                  | right elt_v_neq => right _
                  end
                | right elt_t_neq => right _
                end
              | right vec_v_neq => right _
              end
            | right vec_t_neq => right _
            end); subst; auto.
    { intros H; inversion H; apply elt_v_neq; subst; auto. }
    { intros H; inversion H; apply elt_t_neq; subst; auto. }
    { intros H; inversion H; apply vec_v_neq; subst; auto. }
    { intros H; inversion H; apply vec_t_neq; subst; auto. }

    (* DV (OP_Select ...) *)
  - destruct cnd as (cnd_t', cnd_v');
      destruct v1 as (v1_t', v1_v');
      destruct v2 as (v2_t', v2_v');
      try (right; intros H; inversion H; tauto).
    refine (match decide (cnd_t = cnd_t') with
            | left cnd_t_eq =>
              match decide (x1 = cnd_v') with
              | left cnd_v_eq =>
                match decide (v1_t = v1_t') with
                | left v1_t_eq =>
                  match decide (x2 = v1_v') with
                  | left v1_v_eq => 
                    match decide (v2_t = v2_t') with
                    | left v2_t_eq =>
                      match decide (x3 = v2_v') with
                      | left v2_v_eq => left _
                      | right v2_v_neq => right _
                      end
                    | right v2_t_neq => right _
                    end
                  | right v1_v_neq => right _
                  end
                | right v1_t_neq => right _
                end                  
              | right cnd_v_neq => right _
              end
            | right cnd_t_neq => right _
            end); subst; auto.
    { intros H; inversion H; apply v2_v_neq; subst; auto. }
    { intros H; inversion H; apply v2_t_neq; subst; auto. }
    { intros H; inversion H; apply v1_v_neq; subst; auto. }
    { intros H; inversion H; apply v1_t_neq; subst; auto. }    
    { intros H; inversion H; apply cnd_v_neq; subst; auto. }
    { intros H; inversion H; apply cnd_t_neq; subst; auto. }
Defined.

Definition expr_svalue_ind: forall P : Ollvm_ast.value -> Set,
        (forall id : ident, P (SV (VALUE_Ident id))) ->
    (forall x : int, P (SV (VALUE_Integer x))) ->
    (forall f : float, P (SV (VALUE_Float f))) ->
    (forall b : bool, P (SV (VALUE_Bool b))) ->
    (P (SV VALUE_Null)) ->
    (P (SV (VALUE_Zero_initializer))) ->
    (forall s : String.string, P (SV (VALUE_Cstring s))) ->
    (P (SV VALUE_None)) ->
    (P (SV VALUE_Undef)) ->
    (P (SV (VALUE_Struct []))) ->
    (forall t v fields,
        P v ->
        P (SV (VALUE_Struct fields)) ->
        P (SV (VALUE_Struct ((t, v) :: fields)))) ->
    (P (SV (VALUE_Packed_struct []))) ->
    (forall t v fields,
        P v ->
        P (SV (VALUE_Packed_struct fields)) ->
        P (SV (VALUE_Packed_struct ((t, v) :: fields)))) ->
    (P (SV (VALUE_Array []))) ->
    (forall t v arr,
        P v ->
        P (SV (VALUE_Array arr)) ->
        P (SV (VALUE_Array ((t, v) :: arr)))) ->
    (P (SV (VALUE_Vector []))) ->
    (forall t v vec,
        P v ->
        P (SV (VALUE_Vector vec)) ->
        P (SV (VALUE_Vector ((t, v) :: vec)))) ->
    (forall iop t v1 v2,
        P v1 -> P v2 ->
        P (SV (OP_IBinop iop t v1 v2))) ->
    (forall cmp t v1 v2,
        P v1 -> P v2 ->
        P (SV (OP_ICmp cmp t v1 v2))) ->
    (forall fop fm t v1 v2,
        P v1 -> P v2 ->
        P (SV (OP_FBinop fop fm t v1 v2))) ->
    (forall cmp t v1 v2,
        P v1 -> P v2 ->
        P (SV (OP_FCmp cmp t v1 v2))) ->
    (forall conv t_from v t_to,
        P v -> P (SV (OP_Conversion conv t_from v t_to))) ->
    (forall t ptr_t ptr_v,
        P (ptr_v) ->
        P (SV (OP_GetElementPtr t (ptr_t, ptr_v) []))) ->
    (forall t ptr_t ptr_v idx_t idx_v indices,
        P (ptr_v) ->
        P (idx_v) ->
        P (SV (OP_GetElementPtr t (ptr_t, ptr_v) indices)) ->
        P (SV (OP_GetElementPtr t (ptr_t, ptr_v) ((idx_t, idx_v) :: indices)))) ->
    (forall vec_t vec_v idx_t idx_v,
        P vec_v -> P idx_v -> P (SV (OP_ExtractElement (vec_t, vec_v) (idx_t, idx_v)))) ->
    (forall vec_t vec_v elt_t elt_v idx_t idx_v,
        P vec_v -> P elt_v -> P idx_v ->
        P (SV (OP_InsertElement (vec_t, vec_v) (elt_t, elt_v) (idx_t, idx_v)))) ->
    (forall vec1_t vec1_v vec2_t vec2_v idxmask_t idxmask_v,
        P vec1_v -> P vec2_v -> P (idxmask_v) ->
        P (SV (OP_ShuffleVector (vec1_t, vec1_v) (vec2_t, vec2_v) (idxmask_t, idxmask_v)))) ->
    (forall vec_t vec_v idxs,
        P vec_v -> P (SV (OP_ExtractValue (vec_t, vec_v) idxs))) ->
    (forall vec_t vec_v elt_t elt_v idxs,
        P vec_v -> P elt_v ->
        P (SV (OP_InsertValue (vec_t, vec_v) (elt_t, elt_v) idxs))) ->
    (forall cnd_t cnd_v v1_t v1_v v2_t v2_v,
        P cnd_v -> P v1_v -> P v2_v ->
        P (SV (OP_Select (cnd_t, cnd_v) (v1_t, v1_v) (v2_t, v2_v)))) ->
    (forall v : Ollvm_ast.value, P v).
Proof.
  (* Just copying from above! *)
  intros P H_Ident H_Integer H_Float H_Bool H_Null
         H_Zero_initializer H_Cstring H_None H_Undef.
  intros IH_Struct_Base IH_Struct_Ind
         IH_Packed_struct_Base IH_Packed_struct_Ind
         IH_Array_Base IH_Array_Ind
         IH_Vector_Base IH_Vector_Ind
         IH_IBinop IH_ICmp IH_FBinop IH_FCmp
         IH_Conversion
         IH_GetElementPtr_Base IH_GetElementPtr_Ind
         IH_ExtractElement IH_InsertElement
         IH_ShuffleVector IH_ExtractValue IH_InsertValue
         IH_Select.
  
  refine
    (fix prove_sv (v : Ollvm_ast.value) :=
       match v with
       | SV e =>
         match e with
         | VALUE_Ident id => _
         | VALUE_Integer n => _
         | VALUE_Float f => _
         | VALUE_Bool b => _
         | VALUE_Null => _
         | VALUE_Zero_initializer => _
         | VALUE_Cstring s => _
         | VALUE_None => _
         | VALUE_Undef => _
         | VALUE_Struct l =>
           let
             fix prove_l (l : list (Ollvm_ast.typ * Ollvm_ast.value)) :=
             match l with
             | [] => IH_Struct_Base
             | (t, v) :: rest =>
               IH_Struct_Ind t v rest (prove_sv v) (prove_l rest)
             end
           in prove_l l 
         | VALUE_Packed_struct l =>
           let
             fix prove_l (l : list (Ollvm_ast.typ * Ollvm_ast.value)) :=
             match l with
             | [] => IH_Packed_struct_Base
             | (t, v) :: rest =>
               IH_Packed_struct_Ind t v rest (prove_sv v) (prove_l rest)
             end
           in prove_l l 
         | VALUE_Array l =>
           let
             fix prove_l (l : list (Ollvm_ast.typ * Ollvm_ast.value)) :=
             match l with
             | [] => IH_Array_Base
             | (t, v) :: rest =>
               IH_Array_Ind t v rest (prove_sv v) (prove_l rest)
             end
           in prove_l l 

         | VALUE_Vector l =>
           let
             fix prove_l (l : list (Ollvm_ast.typ * Ollvm_ast.value)) :=
             match l with
             | [] => IH_Vector_Base
             | (t, v) :: rest =>
               IH_Vector_Ind t v rest (prove_sv v) (prove_l rest)
             end
           in prove_l l            

         | OP_IBinop op t v1 v2 =>
           IH_IBinop op t v1 v2 (prove_sv v1) (prove_sv v2) 
         | OP_ICmp op t v1 v2 => 
           IH_ICmp op t v1 v2 (prove_sv v1) (prove_sv v2) 
         | OP_FBinop op fm t v1 v2 =>
           IH_FBinop op fm t v1 v2 (prove_sv v1) (prove_sv v2) 
         | OP_FCmp op t v1 v2 =>
           IH_FCmp op t v1 v2 (prove_sv v1) (prove_sv v2) 
         | OP_Conversion conv t_from v t_to =>
           IH_Conversion conv t_from v t_to (prove_sv v)
           
         | OP_GetElementPtr t (ptr_t, ptr_v) l =>
           let fix prove_l (l : list (Ollvm_ast.typ * Ollvm_ast.value)) :=
               match l with
               | [] =>
                 IH_GetElementPtr_Base t ptr_t ptr_v (prove_sv ptr_v)
               | (idx_t, idx_v) :: rest =>
                 IH_GetElementPtr_Ind t ptr_t ptr_v idx_t idx_v rest
                                      (prove_sv ptr_v) (prove_sv idx_v)
                                      (prove_l rest)
               end
           in prove_l l
           
         | OP_ExtractElement (vec_t, vec_v) (idx_t, idx_v) =>
           IH_ExtractElement vec_t vec_v idx_t idx_v
                             (prove_sv vec_v) (prove_sv idx_v)
         | OP_InsertElement (vec_t, vec_v) (elt_t, elt_v) (idx_t, idx_v) =>
           IH_InsertElement vec_t vec_v elt_t elt_v idx_t idx_v
                            (prove_sv vec_v) (prove_sv elt_v) (prove_sv idx_v)
         | OP_ShuffleVector (vec1_t, vec1_v) (vec2_t, vec2_v) (idxmask_t, idxmask_v) => 
           IH_ShuffleVector vec1_t vec1_v vec2_t vec2_v idxmask_t idxmask_v
                            (prove_sv vec1_v) (prove_sv vec2_v) (prove_sv idxmask_v)
         | OP_ExtractValue (vec_t, vec_v) idxs =>
           IH_ExtractValue vec_t vec_v idxs (prove_sv vec_v) 
         | OP_InsertValue (vec_t, vec_v) (elt_t, elt_v) idxs =>
           IH_InsertValue vec_t vec_v elt_t elt_v idxs
                          (prove_sv vec_v) (prove_sv elt_v)
         | OP_Select (cnd_t, cnd_v) (v1_t, v1_v) (v2_t, v2_v) =>
           IH_Select cnd_t cnd_v v1_t v1_v v2_t v2_v
                     (prove_sv cnd_v) (prove_sv v1_v) (prove_sv v2_v)
         end
       end
    ); auto.
Defined.

Instance eq_dec_static_value : eq_dec Ollvm_ast.value.
Proof.
  (* Just copying from above! *)
  induction x using expr_svalue_ind; destruct y; 
    try (right; intro H; inversion H; tauto);
    try (lift_decide_eq);
    try destruct e; unfold Decidable;
      try (right; intro H; inversion H; tauto);
      try (lift_decide_eq_from_inside_sv);
      try solve [left; auto].

  (* SV (VALUE_Struct ...) *)
  - destruct fields; auto.
  - refine
      (match fields0 with
       | [] => right _
       | (t', v') :: fields' =>
         match (decide (t = t')) with
         | left t_eq =>
           match decide (x = v') with
           | left value_eq =>
             match decide (SV (VALUE_Struct fields) =
                           SV (VALUE_Struct fields')) with
             | left fields_eq => left _
             | right fields_neq => right _
             end
           | right value_neq => right _
           end
         | right t_neq => right _
         end
       end).
    { intros H; inversion H. }
    { inversion fields_eq. subst. reflexivity. }
    { intros H; inversion H; apply fields_neq; subst; auto. }
    { intros H; inversion H; apply value_neq; subst; auto. }
    { intros H; inversion H; apply t_neq; subst; auto. }

    (* SV (VALUE_Packed_struct ...) *)
  - destruct fields; auto.
  - refine
      (match fields0 with
       | [] => right _
       | (t', v') :: fields' =>
         match (decide (t = t')) with
         | left t_eq =>
           match decide (x = v') with
           | left value_eq =>
             match decide (SV (VALUE_Packed_struct fields) =
                           SV (VALUE_Packed_struct fields')) with
             | left fields_eq => left _
             | right fields_neq => right _
             end
           | right value_neq => right _
           end
         | right t_neq => right _
         end
       end).
    { intros H; inversion H. }
    { inversion fields_eq. subst. reflexivity. }
    { intros H; inversion H; apply fields_neq; subst; auto. }
    { intros H; inversion H; apply value_neq; subst; auto. }
    { intros H; inversion H; apply t_neq; subst; auto. }

    (* SV (VALUE_Array ...) *)
  - destruct elts; auto.
  - destruct elts as [| (t', x') arr']; auto.
    refine
      (match (decide (t = t')) with
       | left t_eq =>
         match (decide (x = x')) with
         | left value_eq =>
           match decide (SV (VALUE_Array arr) = SV (VALUE_Array arr')) with
           | left rest_eq => left _
           | right rest_neq => right _
           end
         | right value_neq => right _
         end
       | right t_neq => right _
       end).
    { inversion rest_eq; subst; auto. }
    { intros H; inversion H; apply rest_neq; subst; auto. }
    { intros H; inversion H; apply value_neq; subst; auto. }
    { intros H; inversion H; apply t_neq; subst; auto. }

    (* SV (VALUE_Vector *)
  - destruct elts; auto.
  - destruct elts as [| (t', x') vec']; auto.
    refine
      (match (decide (t = t')) with
       | left t_eq =>
         match (decide (x = x')) with
         | left value_eq =>
           match decide (SV (VALUE_Vector vec) = SV (VALUE_Vector vec')) with
           | left rest_eq => left _
           | right rest_neq => right _
           end
         | right value_neq => right _
         end
       | right t_neq => right _
       end).
    { inversion rest_eq; subst; auto. }
    { intros H; inversion H; apply rest_neq; subst; auto. }
    { intros H; inversion H; apply value_neq; subst; auto. }
    { intros H; inversion H; apply t_neq; subst; auto. }

    (* SV (OP_GetElementPtr ...) *)
  - destruct ptrval as (ptr_t', ptr_v');
      destruct idxs; try (right; intros H; inversion H; tauto).
    refine
      (match decide (ptr_t = ptr_t') with
       | left t_eq =>
         match decide (x = ptr_v') with
         | left ptr_value_eq => left _
         | right ptr_value_neq => right _
         end
       | right t_neq => right _
       end).
    { subst; reflexivity. } 
    { intros H; inversion H; apply ptr_value_neq; subst; auto. }
    { intros H; inversion H; apply t_neq; subst; auto. }
  - destruct ptrval as (ptr_t', ptr_v');
      destruct idxs as [| (idx_t', idx_v')];
      try (right; intros H; inversion H; tauto).
    refine
      (match decide (ptr_t = ptr_t') with
       | left ptr_t_eq =>
         match decide (x1 = ptr_v') with
         | left ptr_value_eq =>
           match decide (idx_t = idx_t') with
           | left idx_t_eq =>
             match decide (x2 = idx_v') with
             | left idx_value_eq => _
             | right idx_value_neq => right _
             end
           | right idx_t_neq => right _
           end
         | right ptr_value_neq => right _
         end
       | right t_neq => right _
       end).
    { subst.
      refine
        (match decide (SV (OP_GetElementPtr t0 (ptr_t', ptr_v') indices) =
                       SV (OP_GetElementPtr t0 (ptr_t', ptr_v') idxs)) with
         | left rest_eq => left _
         | right rest_neq => right _
         end).
      { inversion rest_eq; subst; auto. }
      { intros H; inversion H; apply rest_neq; subst; auto. }
    }
    { intros H; inversion H; apply idx_value_neq; subst; auto. }
    { intros H; inversion H; apply idx_t_neq; subst; auto. }
    { intros H; inversion H; apply ptr_value_neq; subst; auto. }
    { intros H; inversion H; apply t_neq; subst; auto. }

    (* SV (OP_ExtractElement ...), arity 2 *)
  - destruct vec as (vec_t', vec_v');
      destruct idx as (idx_t', idx_v');
      try (right; intros H; inversion H; tauto).
    refine (match decide (vec_t = vec_t') with
            | left vec_t_eq =>
              match decide (x1 = vec_v') with
              | left vec_v_eq =>
                match decide (idx_t = idx_t') with
                | left idx_t_eq =>
                  match decide (x2 = idx_v') with
                  | left idx_v_eq => left _
                  | right idx_v_neq => right _
                  end
                | right idx_t_neq => right _
                end
              | right vec_v_neq => right _
              end
            | right vec_t_neq => right _
            end); subst; auto.
    { intros H; inversion H; apply idx_v_neq; subst; auto. }
    { intros H; inversion H; apply idx_t_neq; subst; auto. }
    { intros H; inversion H; apply vec_v_neq; subst; auto. }
    { intros H; inversion H; apply vec_t_neq; subst; auto. }

    (* SV (OP_InsertElement ...), arity 3 *)
  - destruct vec as (vec_t', vec_v');
      destruct elt as (elt_t', elt_v');      
      destruct idx as (idx_t', idx_v');
      try (right; intros H; inversion H; tauto).
    refine (match decide (vec_t = vec_t') with
            | left vec_t_eq =>
              match decide (x1 = vec_v') with
              | left vec_v_eq =>
                match decide (elt_t = elt_t') with
                | left elt_t_eq =>
                  match decide (x2 = elt_v') with
                  | left elt_v_eq => 
                    match decide (idx_t = idx_t') with
                    | left idx_t_eq =>
                      match decide (x3 = idx_v') with
                      | left idx_v_eq => left _
                      | right idx_v_neq => right _
                      end
                    | right idx_t_neq => right _
                    end
                  | right elt_v_neq => right _
                  end
                | right elt_t_neq => right _
                end                  
              | right vec_v_neq => right _
              end
            | right vec_t_neq => right _
            end); subst; auto.
    { intros H; inversion H; apply idx_v_neq; subst; auto. }
    { intros H; inversion H; apply idx_t_neq; subst; auto. }
    { intros H; inversion H; apply elt_v_neq; subst; auto. }
    { intros H; inversion H; apply elt_t_neq; subst; auto. }    
    { intros H; inversion H; apply vec_v_neq; subst; auto. }
    { intros H; inversion H; apply vec_t_neq; subst; auto. }

    (* SV (OP_ShuffleVector ...) ; Same as SV (OP_InsertElement ...), with arity 3 *)
  - destruct vec1 as (vec1_t', vec1_v');
      destruct vec2 as (vec2_t', vec2_v');      
      destruct idxmask as (idxmask_t', idxmask_v');
      try (right; intros H; inversion H; tauto).
    refine (match decide (vec1_t = vec1_t') with
            | left vec1_t_eq =>
              match decide (x1 = vec1_v') with
              | left vec1_v_eq =>
                match decide (vec2_t = vec2_t') with
                | left vec2_t_eq =>
                  match decide (x2 = vec2_v') with
                  | left vec2_v_eq => 
                    match decide (idxmask_t = idxmask_t') with
                    | left idxmask_t_eq =>
                      match decide (x3 = idxmask_v') with
                      | left idxmask_v_eq => left _
                      | right idxmask_v_neq => right _
                      end
                    | right idxmask_t_neq => right _
                    end
                  | right vec2_v_neq => right _
                  end
                | right vec2_t_neq => right _
                end                  
              | right vec1_v_neq => right _
              end
            | right vec1_t_neq => right _
            end); subst; auto.
    { intros H; inversion H; apply idxmask_v_neq; subst; auto. }
    { intros H; inversion H; apply idxmask_t_neq; subst; auto. }
    { intros H; inversion H; apply vec2_v_neq; subst; auto. }
    { intros H; inversion H; apply vec2_t_neq; subst; auto. }    
    { intros H; inversion H; apply vec1_v_neq; subst; auto. }
    { intros H; inversion H; apply vec1_t_neq; subst; auto. }

    (* SV (OP_ExtractValue ...) ; Same as SV (OP_ *)
  - destruct vec as (vec_t', vec_v');
      try (right; intros H; inversion H; tauto).
    refine
      (match decide (vec_t = vec_t') with
       | left t_eq =>
         match decide (x = vec_v') with
         | left v_eq => left _
         | right v_neq => right _
         end
       | right t_neq => right _
       end); subst; auto.
    { intros H; inversion H; apply v_neq; subst; auto. }
    { intros H; inversion H; apply t_neq; subst; auto. }

    (* SV (OP_InsertValue ...) *)
  - destruct vec as (vec_t', vec_v');
      destruct elt as (elt_t', elt_v');
      try (right; intros H; inversion H; tauto).
    refine (match decide (vec_t = vec_t') with
            | left vec_t_eq =>
              match decide (x1 = vec_v') with
              | left vec_v_eq =>
                match decide (elt_t = elt_t') with
                | left elt_t_eq =>
                  match decide (x2 = elt_v') with
                  | left elt_v_eq => left _
                  | right elt_v_neq => right _
                  end
                | right elt_t_neq => right _
                end
              | right vec_v_neq => right _
              end
            | right vec_t_neq => right _
            end); subst; auto.
    { intros H; inversion H; apply elt_v_neq; subst; auto. }
    { intros H; inversion H; apply elt_t_neq; subst; auto. }
    { intros H; inversion H; apply vec_v_neq; subst; auto. }
    { intros H; inversion H; apply vec_t_neq; subst; auto. }

    (* SV (OP_Select ...) *)
  - destruct cnd as (cnd_t', cnd_v');
      destruct v1 as (v1_t', v1_v');
      destruct v2 as (v2_t', v2_v');
      try (right; intros H; inversion H; tauto).
    refine (match decide (cnd_t = cnd_t') with
            | left cnd_t_eq =>
              match decide (x1 = cnd_v') with
              | left cnd_v_eq =>
                match decide (v1_t = v1_t') with
                | left v1_t_eq =>
                  match decide (x2 = v1_v') with
                  | left v1_v_eq => 
                    match decide (v2_t = v2_t') with
                    | left v2_t_eq =>
                      match decide (x3 = v2_v') with
                      | left v2_v_eq => left _
                      | right v2_v_neq => right _
                      end
                    | right v2_t_neq => right _
                    end
                  | right v1_v_neq => right _
                  end
                | right v1_t_neq => right _
                end                  
              | right cnd_v_neq => right _
              end
            | right cnd_t_neq => right _
            end); subst; auto.
    { intros H; inversion H; apply v2_v_neq; subst; auto. }
    { intros H; inversion H; apply v2_t_neq; subst; auto. }
    { intros H; inversion H; apply v1_v_neq; subst; auto. }
    { intros H; inversion H; apply v1_t_neq; subst; auto. }    
    { intros H; inversion H; apply cnd_v_neq; subst; auto. }
    { intros H; inversion H; apply cnd_t_neq; subst; auto. }
Qed.

Instance eq_dec_instr : eq_dec instr.
Proof.
  lift_decide_eq; left; auto.
Defined.

Instance eq_dec_terminator : eq_dec terminator.
Proof.
  lift_decide_eq; left; auto.
Defined.
  
Instance eq_dec_phi : eq_dec Ollvm_ast.phi.
Proof. lift_decide_eq. Defined.

Instance eq_dec_code : eq_dec code.
Proof.
  unfold code; lift_decide_eq;
  left; auto.
Defined.

Instance eq_dec_block : eq_dec block.
Proof. lift_decide_eq. Defined.

Instance eq_dec_pc : eq_dec pc.
Proof. lift_decide_eq. Defined.

Instance eq_dec_frame : eq_dec frame.
Proof. lift_decide_eq. Defined.

Instance eq_dec_SS_state : eq_dec SS.state.
Proof. lift_decide_eq. Defined.

(*
The following are not true. 
Instance eq_dec_effects `{eq_dec D} : eq_dec (effects D).
Instance eq_dec_transition `{eq_dec X} : eq_dec (transition X).
*)


(** ** Basic Propositions *) 

Inductive prefix_of {A : Type}: list A -> list A -> Prop :=
| prefix_nil : forall l : list A, prefix_of [] l
| prefix_cons_same : forall a l1 l2, prefix_of l1 l2 -> prefix_of (a :: l1) (a :: l2).

Inductive suffix_of {A : Type}: list A -> list A -> Prop :=
| suffix_nil : forall l : list A, suffix_of l []
| suffix_app : forall a l1 l2, suffix_of l1 l2 -> suffix_of (l1 ++ [a]) (l2 ++ [a]).

Instance dec_prefix_of : forall A `{eq_dec A} (l1 l2 : list A), Decidable (prefix_of l1 l2).
Proof.
  intros A A_decidable.
  induction l1 as [| a l1']; unfold Decidable.
  - intros [| a l2']; left; constructor.
  - intros [| b l2']; try solve [right; intros H; inversion H].
    refine
      (match a == b with
       | left _ =>
         match decide (prefix_of l1' l2') with
         | left tail_eq => _
         | right tail_neq => right _
         end
       | right head_neq => right _
       end).
    { subst; constructor. constructor. tauto. }
    { intros H. apply tail_neq. inversion H; subst; auto. }
    { intros H. apply head_neq. inversion H; subst; auto. }
Defined.

Instance dec_Z_leq : forall n m : int, Decidable (n <= m)%Z.
Proof.
  unfold Decidable. intros n m.
  destruct (n <=? m)%Z eqn:n_m.
  - left; rewrite Z.leb_le in n_m; auto.
  - right; intros H; rewrite <- Z.leb_le in H;
      rewrite n_m in H; inversion H.
Defined.
