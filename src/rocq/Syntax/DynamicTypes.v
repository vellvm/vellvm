(* begin hide *)
From Stdlib Require Import
     Setoid
     Morphisms
     DecidableClass
     Classes.RelationClasses
     Program.Wf.

From Vellvm Require Import
     Utils
     Syntax.LLVMAst.
Open Scope nat.

(* end hide *)

(** * Dynamic types
    LLVM types contain information unnecessary to the semantics of programs,
    and making them structurally annoying to reason about.
    We therefore pre-process them to convert them into so-called dynamic types,
    or [dtyp].
    These dynamic types differ from static ones in two aspects:
    - we have forget about the nature of the object pointer types point to
    - type variables have been resolved.
    The conversion from static types to dynamic types is defined in the module [TypToDtyp].
 *)


Unset Elimination Schemes.

Variant dtyp_base : Set :=
| DTYPE_I (sz:positive)
| DTYPE_Iptr
| DTYPE_Pointer
| DTYPE_Void
| DTYPE_FP (fp:floating_point_variant)
| DTYPE_Label
| DTYPE_Token
| DTYPE_Metadata
| DTYPE_X86_mmx
| DTYPE_Opaque
| DTYPE_B (sz:positive).

Inductive dtyp : Set :=
| DTYPE_Base (dt:dtyp_base)
| DTYPE_Struct (packed:bool) (fields:list dtyp)
| DTYPE_Array (sz:N) (t:dtyp)
| DTYPE_Vector (sz:N) (t:dtyp_base)
.
Set Elimination Schemes.

(*  NOTE: to cut down on clutter, we coerce dtyp_base to dtyp *)
Coercion DTYPE_Base : dtyp_base >-> dtyp.

Lemma dtyp_base_eq_dec : forall (t1 t2 : dtyp_base), {t1 = t2} + {t1 <> t2}.
Proof.
  repeat decide equality.
Qed.

Ltac dec_dtyp :=
  match goal with
  | [ |- { ?X ?a = ?X ?b} + { ?X ?a <> ?X ?b} ] => idtac
  | [ |- { ?X ?a = ?Y ?b} + { ?X ?a <> ?Y ?b} ] => right; intros H; inversion H
  | [ |- { ?X = ?X } + { ?X <> ?X } ] => left; reflexivity
  | [ |- { ?X = ?Y } + { ?X <> ?Y } ] => right; intros H; inversion H
  end.


Lemma dtyp_eq_dec : forall (t1 t2:dtyp), {t1 = t2} + {t1 <> t2}.
Proof.
  refine (fix f t1 t2 :=
            let lsteq_dec := list_eq_dec f in
            match t1, t2 with
            | DTYPE_Base t1, DTYPE_Base t2 => _
            | DTYPE_Struct p l, DTYPE_Struct p' l' => _
            | DTYPE_Array n t, DTYPE_Array n' t' => _
            | DTYPE_Vector n t, DTYPE_Vector n' t' => _                                                     
            | _, _ => _
            end); try (ltac:(dec_dtyp); fail).
  - destruct (dtyp_base_eq_dec t1 t2).
    * left; subst; reflexivity.
    * right; intros H; inversion H. contradiction.
  - destruct (lsteq_dec l l').
    * destruct (bool_dec p p').
      -- left; subst; reflexivity.
      -- right; intros H; inversion H. contradiction.
    * right; intros H; inversion H. contradiction.
  - destruct (N.eq_dec n n').
    * destruct (f t t').
      --  left; subst; reflexivity.
      -- right; intros H; inversion H. contradiction.
    * right; intros H; inversion H. contradiction.
  - destruct (N.eq_dec n n').
    * destruct (dtyp_base_eq_dec t t').
      -- left; subst; reflexivity.
      -- right; intros H; inversion H. contradiction.
    * right; intros H; inversion H. contradiction.         
Defined.
Arguments dtyp_eq_dec: clear implicits.

Section DtypInd.
  Variable P : dtyp -> Prop.
  Hypothesis IH_Base   : forall t, P (DTYPE_Base t).
  Hypothesis IH_Struct : forall (p:bool) (fields: list dtyp), (forall u, In u fields -> P u) -> P (DTYPE_Struct p fields).
  Hypothesis IH_Array  : forall sz (t: dtyp), (P t) -> P (DTYPE_Array sz t).  
  Hypothesis IH_Vector    : forall sz t, P (DTYPE_Vector sz t).

  Lemma dtyp_ind : forall (dt:dtyp), P dt.
    fix IH 1.
    remember P as P0 in IH.
    destruct dt; auto; subst.
    - apply IH_Struct.
      { revert fields.
        fix IHfields 1. intros [|u fields']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IHfields. apply Hin.
      }
    - eapply IH_Array. auto.
  Qed.
End DtypInd.

Section DtypRec.
  Variable P : dtyp -> Set.
  Hypothesis IH_Base   : forall t, P (DTYPE_Base t).
  Hypothesis IH_Struct : forall (p:bool) (fields: list dtyp), (forall u, In u fields -> P u) -> P (DTYPE_Struct p fields).
  Hypothesis IH_Array  : forall sz (t: dtyp), (P t) -> P (DTYPE_Array sz t).  
  Hypothesis IH_Vector    : forall sz t, P (DTYPE_Vector sz t).

  Lemma dtyp_rec : forall (dt:dtyp), P dt.
    fix IH 1.
    remember P as P0 in IH.
    destruct dt; auto; subst.
    - apply IH_Struct.
      { revert fields.
        fix IHfields 1. intros [|u fields']. intros. inversion H.
        intros u' Hin.
        pose proof In_cons_dec dtyp_eq_dec Hin.
        destruct H.
        subst. apply IH.
        eapply IHfields. apply i.
      }
    - apply IH_Array. auto.
  Qed.

End DtypRec.

Definition dtyp_base_eqb (dt1 dt2 : dtyp_base) : bool :=
  match @dtyp_base_eq_dec dt1 dt2 with
  | left x => true
  | right x => false
  end.

Definition dtyp_eqb (dt1 dt2 : dtyp) : bool :=
  match @dtyp_eq_dec dt1 dt2 with
  | left x => true
  | right x => false
  end.

Lemma dtyp_eqb_refl :
  forall dt, dtyp_eqb dt dt = true.
Proof using.
  intros dt.
  unfold dtyp_eqb.
  destruct (dtyp_eq_dec dt dt) eqn: H.
  - reflexivity.
  - contradiction.
Qed.

Lemma dtyp_eqb_eq :
  forall t1 t2,
    dtyp_eqb t1 t2 = true ->
    t1 = t2.
Proof using.
  intros t1 t2 TYPE.
  unfold dtyp_eqb in TYPE.
  destruct (dtyp_eq_dec t1 t2); auto; discriminate.
Qed.


Definition vector_dtyp_base (dt : dtyp_base) : Prop :=
  match dt with
  | DTYPE_I _
  | DTYPE_Iptr 
  | DTYPE_Pointer 
  | DTYPE_FP _
  | DTYPE_B _ => True 
  | _ => False
  end.

Lemma vector_dtyp_base_dec :
  forall t,
    {vector_dtyp_base t} + {~ vector_dtyp_base t}.
Proof.
  intros t.
  destruct t; simpl; auto.
Qed.


(* SAZ: TODO - is this dead code? *)
(*
Section WF_dtyp.

  Inductive well_formed_dtyp : dtyp -> Prop :=
  | Wf_I : forall sz, well_formed_dtyp (DTYPE_I sz)
  | Wf_Iptr : well_formed_dtyp DTYPE_Iptr
  | Wf_Pointer : well_formed_dtyp DTYPE_Pointer
  | Wf_Void : well_formed_dtyp DTYPE_Void
  | Wf_Float : forall f, well_formed_dtyp (DTYPE_FP f)
  | Wf_Label : well_formed_dtyp DTYPE_Label
  | Wf_Token : well_formed_dtyp DTYPE_Token                                                                     
  | Wf_Metadata : well_formed_dtyp DTYPE_Metadata
  | Wf_X86_mmx : well_formed_dtyp DTYPE_X86_mmx
  | Wf_Opaque : well_formed_dtyp DTYPE_Opaque
  | Wf_Array : forall (sz : N),
      N.le 0 sz ->
      forall t, well_formed_dtyp t ->
           well_formed_dtyp (DTYPE_Array sz t)
  | Wf_Vector : forall (sz : N),
      N.le 0 sz ->
      forall t, vector_dtyp t ->
           well_formed_dtyp t ->
           well_formed_dtyp (DTYPE_Vector sz t)
  | Wf_Struct_nil :
      well_formed_dtyp (DTYPE_Struct nil)
  | Wf_Struct_cons :
      forall t, well_formed_dtyp t ->
           forall l, well_formed_dtyp (DTYPE_Struct l) ->
                well_formed_dtyp (DTYPE_Struct (t :: l))
  | Wf_Packed_struct_nil :
      well_formed_dtyp (DTYPE_Packed_struct nil)
  | Wf_Packed_truct_cons :
      forall t, well_formed_dtyp t ->
           forall l, well_formed_dtyp (DTYPE_Packed_struct l) ->
                well_formed_dtyp (DTYPE_Packed_struct (t :: l))
  .

End WF_dtyp.
*)


Fixpoint dtyp_measure (t : dtyp) : nat :=
  match t with
  | DTYPE_Base t => 1
  | DTYPE_Struct p fields => S (S (list_sum (map dtyp_measure fields)))
  | DTYPE_Array sz t => S (S (dtyp_measure t))
  | DTYPE_Vector sz t => 1
  end.

Lemma dtyp_measure_gt_0 :
  forall (t : dtyp),
    0 < dtyp_measure t.
Proof using.
  destruct t; cbn; auto.
  all: apply Nat.lt_0_succ.
Qed.

(* TODO: This probably should live somewhere else... *)
#[refine]#[local] Instance Decidable_eq_N : forall (x y : N), Decidable (eq x y) := {
    Decidable_witness := N.eqb x y
  }.
apply N.eqb_eq.
Qed.


Definition NO_VOID_base (dt : dtyp_base) : Prop :=
  match dt with
  | DTYPE_Void => False    
  | _ => True
  end.
                   
Fixpoint NO_VOID (dt : dtyp) : Prop:=
  match dt with
  | DTYPE_Base dt => NO_VOID_base dt
  | DTYPE_Struct p dts => FORALL NO_VOID dts
  | DTYPE_Array sz t => NO_VOID t
  | DTYPE_Vector sz t => NO_VOID_base t
  end.  


Lemma NO_VOID_Struct_fields :
  forall p dts,
    NO_VOID (DTYPE_Struct p dts) ->
    (forall dt, In dt dts -> NO_VOID dt).
Proof using.
  intros p dts NV dt IN.
  cbn in NV.
  rewrite FORALL_forall in NV.
  rewrite Forall_forall in NV.
  apply NV; auto.
Qed.


Lemma NO_VOID_base_dec :
  forall dt,
    {NO_VOID_base dt} + {~NO_VOID_base dt}.
Proof using.
  destruct dt; simpl; auto.
Qed.  
  
Lemma NO_VOID_dec :
  forall dt,
    {NO_VOID dt} + {~NO_VOID dt}.
Proof using.
  intros dt.
  induction dt; simpl.
  - apply NO_VOID_base_dec.
  - apply FORALL_dec; assumption.
  - assumption.
  - apply NO_VOID_base_dec.
Qed.

(* Lemma NO_VOID_neq_dtyp : *)
(*   forall dt1 dt2, *)
(*     NO_VOID dt1 -> *)
(*     ~ NO_VOID dt2 -> *)
(*     dt1 <> dt2. *)
(* Proof using. *)
(*   intros dt1 dt2 NV NNV. *)
(*   intros EQ. *)
(*   induction dt1, dt2; inversion EQ. *)
(*   all: cbn in NNV; try contradiction. *)

(*   all: inversion EQ; subst; *)
(*     cbn in NV; *)
(*     contradiction. *)
(* Qed. *)

(* Lemma NO_VOID_Struct_cons_inv : *)
(*   forall dt dts, *)
(*     NO_VOID dt -> *)
(*     NO_VOID (DTYPE_Struct dts) -> *)
(*     NO_VOID (DTYPE_Struct (dt :: dts)). *)
(* Proof using. *)
(*   intros dt dts NVdt NVdts. *)
(*   cbn in *. *)
(*   intuition. *)
(* Qed. *)

(* Lemma NO_VOID_Packed_struct_cons_inv : *)
(*   forall dt dts, *)
(*     NO_VOID dt -> *)
(*     NO_VOID (DTYPE_Packed_struct dts) -> *)
(*     NO_VOID (DTYPE_Packed_struct (dt :: dts)). *)
(* Proof using. *)
(*   intros dt dts NVdt NVdts. *)
(*   cbn in *. *)
(*   intuition. *)
(* Qed. *)

(* Ltac solve_Forall_HIn := *)
(*   solve [ constructor; auto]. *)

(* #[global] Hint Resolve NO_VOID_Struct_cons_inv : NO_VOID. *)
(* #[global] Hint Resolve NO_VOID_Packed_struct_cons_inv : NO_VOID. *)

(* Ltac solve_no_void := *)
(*   solve *)
(*     [ auto with NO_VOID *)
(*     | match goal with *)
(*       | H: NO_VOID _ /\ _ |- _ *)
(*         => destruct H; solve_no_void *)
(*       end *)
(*     | cbn; solve_no_void *)
(*     ]. *)
