(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

From Coq Require Import
     ZArith
     List
     String
     Setoid
     Morphisms
     Omega
     Classes.RelationClasses.

From ExtLib Require Import
     Core.RelDec
     Programming.Eqv.

From Vellvm Require Import
     Utils.Util
     Utils.Error
     Syntax.LLVMAst.

Require Import Ceres.Ceres.

Set Implicit Arguments.
Set Contextual Implicit.

Unset Elimination Schemes.
Inductive dtyp : Set :=
| DTYPE_I (sz:Z)
| DTYPE_Pointer
| DTYPE_Void
| DTYPE_Half
| DTYPE_Float
| DTYPE_Double
| DTYPE_X86_fp80
| DTYPE_Fp128
| DTYPE_Ppc_fp128
| DTYPE_Metadata
| DTYPE_X86_mmx
| DTYPE_Array (sz:Z) (t:dtyp)
| DTYPE_Struct (fields:list dtyp)
| DTYPE_Packed_struct (fields:list dtyp)
| DTYPE_Opaque
                                   (* IY: Why isn't this defined structurally? *)
| DTYPE_Vector (sz:Z) (t:dtyp)     (* t must be integer, floating point, or pointer type *)
.
Set Elimination Schemes.

Definition vector_dtyp dt :=
  (exists n, dt = DTYPE_I n) \/ dt = DTYPE_Pointer \/ dt = DTYPE_Half \/ dt = DTYPE_Float \/
        dt = DTYPE_Double \/ dt = DTYPE_X86_fp80 \/ dt = DTYPE_Fp128 \/ dt = DTYPE_Ppc_fp128.

Section DtypInd.
  Variable P : dtyp -> Prop.
  Hypothesis IH_I             : forall a, P (DTYPE_I a).
  Hypothesis IH_Pointer       : P DTYPE_Pointer.
  Hypothesis IH_Void          : P DTYPE_Void.
  Hypothesis IH_Half          : P DTYPE_Half.
  Hypothesis IH_Float         : P DTYPE_Float.
  Hypothesis IH_Double        : P DTYPE_Double.
  Hypothesis IH_X86_fp80      : P DTYPE_X86_fp80.
  Hypothesis IH_Fp128         : P DTYPE_Fp128.
  Hypothesis IH_Ppc_fp128     : P DTYPE_Ppc_fp128.
  Hypothesis IH_Metadata      : P DTYPE_Metadata.
  Hypothesis IH_X86_mmx       : P DTYPE_X86_mmx.
  Hypothesis IH_Array         : forall sz t, P t -> P (DTYPE_Array sz t).
  Hypothesis IH_Struct        : forall (fields: list dtyp), (forall u, In u fields -> P u) -> P (DTYPE_Struct fields).
  Hypothesis IH_Packed_Struct : forall (fields: list dtyp), (forall u, In u fields -> P u) -> P (DTYPE_Packed_struct fields).
  Hypothesis IH_Opaque        : P DTYPE_Opaque.
  Hypothesis IH_Vector        : forall sz t, P t -> P (DTYPE_Vector sz t).

  Lemma dtyp_ind : forall (dt:dtyp), P dt.
    fix IH 1.
    remember P as P0 in IH.
    destruct dt; auto; subst.
    - apply IH_Array. auto.
    - apply IH_Struct.
      { revert fields.
        fix IHfields 1. intros [|u fields']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IHfields. apply Hin.
      }
    - apply IH_Packed_Struct.
      { revert fields.
        fix IHfields 1. intros [|u fields']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IHfields. apply Hin.
      }
    - apply IH_Vector. auto.
  Qed.
End DtypInd.

Section WF_dtyp.

  Inductive well_formed_dtyp : dtyp -> Prop :=
  | Wf_I : forall sz, well_formed_dtyp (DTYPE_I sz)
  | Wf_Pointer : well_formed_dtyp DTYPE_Pointer
  | Wf_Void : well_formed_dtyp DTYPE_Void
  | Wf_Half : well_formed_dtyp DTYPE_Half
  | Wf_Float : well_formed_dtyp DTYPE_Float
  | Wf_Double : well_formed_dtyp DTYPE_Double
  | Wf_X86_fp80 : well_formed_dtyp DTYPE_X86_fp80
  | Wf_Fp128 : well_formed_dtyp DTYPE_Fp128
  | Wf_Ppc_fp128 : well_formed_dtyp DTYPE_Ppc_fp128
  | Wf_Metadata : well_formed_dtyp DTYPE_Metadata
  | Wf_X86_mmx : well_formed_dtyp DTYPE_X86_mmx
  | Wf_Opaque : well_formed_dtyp DTYPE_Opaque
  | Wf_Array : forall (sz : Z),
      Z.le 0 sz ->
      forall t, well_formed_dtyp t ->
                well_formed_dtyp (DTYPE_Array sz t)
  | Wf_Vector : forall (sz : Z),
      Z.le 0 sz ->
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

Section hiding_notation.
  Local Open Scope sexp_scope.
  
  Fixpoint serialize_dtyp' (dt:dtyp): sexp :=
    match dt with
    | DTYPE_I sz     => Atom ("i" ++ to_string sz)%string
    | DTYPE_Pointer  => Atom "ptr"
    | DTYPE_Void     => Atom "dvoid"
    | DTYPE_Half     => Atom "half"
    | DTYPE_Float    => Atom "float"
    | DTYPE_Double   => Atom "double"
    | DTYPE_X86_fp80 => Atom "x86_fp80"
    | DTYPE_Fp128    => Atom "fp128"
    | DTYPE_Ppc_fp128 => Atom "ppc_fp128"
    | DTYPE_Metadata  => Atom "metadata"
    | DTYPE_X86_mmx   => Atom "x86_mmx"
    | DTYPE_Array sz t
      => [Atom ("[" ++ to_string sz) ; Atom "x" ; serialize_dtyp' t ; Atom "]"]%string
    | DTYPE_Struct fields
      => [Atom "{" ; to_sexp (List.map (fun x => [serialize_dtyp' x ; Atom ","]) fields) ; Atom "}"]
    | DTYPE_Packed_struct fields
      => [Atom "packed{" ; to_sexp (List.map (fun x => [serialize_dtyp' x ; Atom ","]) fields) ; Atom "}"]
    | DTYPE_Opaque => Atom "opaque"
    | DTYPE_Vector sz t
      => [Atom ("<" ++ to_string sz) ; Atom "x" ; serialize_dtyp' t ; Atom ">"]%string  (* TODO: right notation? *)
    end.

  Global Instance serialize_dtyp : Serialize dtyp := serialize_dtyp'.
End hiding_notation.

