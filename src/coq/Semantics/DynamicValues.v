(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

(* begin hide *)
From Coq Require Import
     ZArith DecidableClass List String Omega Bool.Bool.

Import BinInt.

Require Import Ceres.Ceres.

From ExtLib Require Import
     Core.RelDec
     Programming.Eqv
     Structures.Monads
     Data.Monads.EitherMonad
     Structures.Functor
     Data.Nat
     Data.List.

From Vellvm Require Import
     Utilities
     Syntax
     Syntax.DataLayout
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof.

Require Import Integers Floats.

From Flocq.IEEE754 Require Import
     Bits
     Binary.

Import EqvNotation.
Import MonadNotation.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

Open Scope N_scope.
(* end hide *)


(** * Dynamic values
    Definition of the dynamic values manipulated by VIR.
    They come in two flavors:
    - [dvalue] are the concrete notion of values computed.
    - [uvalue] (_under-defined values_) are an extension of [dvalue] as symbolic values:
      + a special [undef τ] value modeling LLVM's "undef"
      + delayed numerical operations.
 *)

#[global] Instance Eqv_nat : Eqv nat := (@eq nat).

(* Floating-point rounding mode *)
Definition FT_Rounding:mode := mode_NE.

(* Set up representations for for i1, i32, and i64 *)
Module Wordsize1.
  Definition wordsize := 1%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize1.

Module Wordsize8.
  Definition wordsize := 8%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize8.

Module Int1 := Make(Wordsize1).
Module Int8 := Make(Wordsize8).
Module Int32 := Integers.Int.
Module Int64 := Integers.Int64.

Definition int1 := Int1.int.
Definition int8 := Int8.int.
Definition int32 := Int32.int.
Definition int64 := Int64.int.

Definition inttyp (x:N) : Type :=
  match x with
  | 1 => int1
  | 8 => int8
  | 32 => int32
  | 64 => int64
  | _ => False
  end.

Inductive IX_supported : N -> Prop :=
| I1_Supported : IX_supported 1
| I8_Supported : IX_supported 8
| I32_Supported : IX_supported 32
| I64_Supported : IX_supported 64
.

(* TODO: This probably should live somewhere else... *)
#[refine] Instance Decidable_eq_N : forall (x y : N), Decidable (eq x y) := {
  Decidable_witness := N.eqb x y
}.
 apply N.eqb_eq.
Qed.

Lemma IX_supported_dec : forall (sz:N), {IX_supported sz} + {~IX_supported sz}.
Proof.
  intros sz.
  - decide (sz = 1)%N.
    + left. subst. constructor.
    + decide (sz = 8)%N.
      * left. subst. constructor.
      * decide (sz = 32).
        -- left. subst. constructor.
        -- decide (sz = 64).
           ++ left. subst. constructor.
           ++ right. intro X.
              inversion X; subst; contradiction.
Qed.

Lemma unsupported_cases : forall {X} (sz : N) (N : ~ IX_supported sz) (x64 x32 x8 x1 x : X),
    (if (sz =? 64) then x64
      else if (sz =? 32) then x32
          else if (sz =? 8) then x8
                else if (sz =? 1) then x1
                    else x) = x.
Proof.
  intros.
  destruct (sz =? 64) eqn: H.
  rewrite N.eqb_eq in H.
  destruct N. rewrite H. constructor.
  destruct (sz =? 32) eqn: H'.
  rewrite N.eqb_eq in H'.
  destruct N. rewrite H'. constructor.
  destruct (sz =? 8) eqn: H''.
  rewrite N.eqb_eq in H''.
  destruct N. rewrite H''. constructor.
  destruct (sz =? 1) eqn: H'''.
  rewrite N.eqb_eq in H'''.
  destruct N. rewrite H'''. constructor.
  reflexivity.
Qed.

Function unsupported_cases_match_ {X} (sz : N) (x64 x32 x8 x1 x : X) :=
    match sz with
    | 64 => x64
    | 32 => x32
    | 8 => x8
    | 1 => x1
    | _ => x
    end.

Lemma unsupported_cases_match : forall {X} (sz : N) (N : ~ IX_supported sz) (x64 x32 x8 x1 x : X),
    match sz with
    | 64 => x64
    | 32 => x32
    | 8 => x8
    | 1 => x1
    | _ => x
    end = x.
Proof.
  intros.
  change ((unsupported_cases_match_ sz x64 x32 x8 x1 x) = x).
  revert N.
  apply unsupported_cases_match__ind; intros.
  - assert False. apply N.  econstructor. inversion H.
  - assert False. apply N.  econstructor. inversion H.
  - assert False. apply N.  econstructor. inversion H.
  - assert False. apply N.  econstructor. inversion H.
  - reflexivity.
Qed.


Definition ll_float  := Floats.float32.
Definition ll_double := Floats.float.

(* Sizeof is needed for uvalue_has_dtyp for ConcatBytes case *)
Module DVALUE(A:Vellvm.Semantics.MemoryAddress.ADDRESS)(SIZEOF:Sizeof).

  Import SIZEOF.

  (* The set of dynamic values manipulated by an LLVM program. *)
 Unset Elimination Schemes.
Inductive dvalue : Set :=
| DVALUE_Addr (a:A.addr)
| DVALUE_I1 (x:int1)
| DVALUE_I8 (x:int8)
| DVALUE_I32 (x:int32)
| DVALUE_I64 (x:int64)
| DVALUE_IPTR (x:Z) (* TODO: should this be unsigned...? *)
| DVALUE_Double (x:ll_double)
| DVALUE_Float (x:ll_float)
| DVALUE_Poison (t:dtyp)
| DVALUE_None
| DVALUE_Struct        (fields: list dvalue)
| DVALUE_Packed_struct (fields: list dvalue)
| DVALUE_Array         (elts: list dvalue)
| DVALUE_Vector        (elts: list dvalue)
.
Set Elimination Schemes.

Fixpoint dvalue_measure (dv : dvalue) : nat :=
  match dv with
  | DVALUE_Addr a => 1
  | DVALUE_I1 x => 1
  | DVALUE_I8 x => 1
  | DVALUE_I32 x => 1
  | DVALUE_I64 x => 1
  | DVALUE_IPTR x => 1
  | DVALUE_Double x => 1
  | DVALUE_Float x => 1
  | DVALUE_Poison t => 1
  | DVALUE_None => 1
  | DVALUE_Struct fields => S (S (list_sum (map dvalue_measure fields)))
  | DVALUE_Packed_struct fields => S (S (list_sum (map dvalue_measure fields)))
  | DVALUE_Array elts => S (S (list_sum (map dvalue_measure elts)))
  | DVALUE_Vector elts => S (S (list_sum (map dvalue_measure elts)))
  end.

Lemma dvalue_measure_gt_0 :
  forall (dv : dvalue),
    (0 < dvalue_measure dv)%nat.
Proof.
  destruct dv; cbn; auto.
  all: apply Nat.lt_0_succ.
Qed.

Section DvalueInd.
  Variable P : dvalue -> Prop.
  Hypothesis IH_Addr          : forall a, P (DVALUE_Addr a).
  Hypothesis IH_I1            : forall x, P (DVALUE_I1 x).
  Hypothesis IH_I8            : forall x, P (DVALUE_I8 x).
  Hypothesis IH_I32           : forall x, P (DVALUE_I32 x).
  Hypothesis IH_I64           : forall x, P (DVALUE_I64 x).
  Hypothesis IH_IPTR           : forall x, P (DVALUE_IPTR x).
  Hypothesis IH_Double        : forall x, P (DVALUE_Double x).
  Hypothesis IH_Float         : forall x, P (DVALUE_Float x).
  Hypothesis IH_Poison        : forall t, P (DVALUE_Poison t).
  Hypothesis IH_None          : P DVALUE_None.
  Hypothesis IH_Struct        : forall (fields: list dvalue), (forall u, In u fields -> P u) -> P (DVALUE_Struct fields).
  Hypothesis IH_Packed_Struct : forall (fields: list dvalue), (forall u, In u fields -> P u) -> P (DVALUE_Packed_struct fields).
  Hypothesis IH_Array         : forall (elts: list dvalue), (forall e, In e elts -> P e) -> P (DVALUE_Array elts).
  Hypothesis IH_Vector        : forall (elts: list dvalue), (forall e, In e elts -> P e) -> P (DVALUE_Vector elts).

  Lemma dvalue_ind : forall (dv:dvalue), P dv.
    fix IH 1.
    remember P as P0 in IH.
    destruct dv; auto; subst.
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
    - apply IH_Array.
      { revert elts.
        fix IHelts 1. intros [|u elts']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IHelts. apply Hin.
      }
    - apply IH_Vector.
      { revert elts.
        fix IHelts 1. intros [|u elts']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IHelts. apply Hin.
      }
  Qed.
End DvalueInd.

Definition store_id := N.

(* The set of dynamic values manipulated by an LLVM program. *)
Unset Elimination Schemes.
Inductive uvalue : Type :=
| UVALUE_Addr (a:A.addr)
| UVALUE_I1 (x:int1)
| UVALUE_I8 (x:int8)
| UVALUE_I32 (x:int32)
| UVALUE_I64 (x:int64)
| UVALUE_IPTR (x:Z) (* TODO: Should this be unsigned? *)
| UVALUE_Double (x:ll_double)
| UVALUE_Float (x:ll_float)
| UVALUE_Undef (t:dtyp)
| UVALUE_Poison (t:dtyp)
| UVALUE_None
| UVALUE_Struct        (fields: list uvalue)
| UVALUE_Packed_struct (fields: list uvalue)
| UVALUE_Array         (elts: list uvalue)
| UVALUE_Vector        (elts: list uvalue)
| UVALUE_IBinop           (iop:ibinop) (v1:uvalue) (v2:uvalue)
| UVALUE_ICmp             (cmp:icmp)   (v1:uvalue) (v2:uvalue)
| UVALUE_FBinop           (fop:fbinop) (fm:list fast_math) (v1:uvalue) (v2:uvalue)
| UVALUE_FCmp             (cmp:fcmp)   (v1:uvalue) (v2:uvalue)
| UVALUE_Conversion       (conv:conversion_type) (t_from:dtyp) (v:uvalue) (t_to:dtyp)
| UVALUE_GetElementPtr    (t:dtyp) (ptrval:uvalue) (idxs:list (uvalue)) (* TODO: do we ever need this? GEP raises an event? *)
| UVALUE_ExtractElement   (vec: uvalue) (idx: uvalue)
| UVALUE_InsertElement    (vec: uvalue) (elt:uvalue) (idx:uvalue)
| UVALUE_ShuffleVector    (vec1:uvalue) (vec2:uvalue) (idxmask:uvalue)
| UVALUE_ExtractValue     (vec:uvalue) (idxs:list LLVMAst.int)
| UVALUE_InsertValue      (vec:uvalue) (elt:uvalue) (idxs:list LLVMAst.int)
| UVALUE_Select           (cnd:uvalue) (v1:uvalue) (v2:uvalue)
(* Extract the `idx` byte from a uvalue `uv`, which was stored with
   type `dt`. `idx` 0 is the least significant byte. `sid` is the "store
   id". *)
| UVALUE_ExtractByte      (uv : uvalue) (dt : dtyp) (idx : uvalue) (sid : store_id)
| UVALUE_ConcatBytes      (uvs : list uvalue) (dt : dtyp)
.
Set Elimination Schemes.

Fixpoint uvalue_measure (uv : uvalue) : nat :=
  match uv with
  | UVALUE_Addr a => 1
  | UVALUE_I1 x => 1
  | UVALUE_I8 x => 1
  | UVALUE_I32 x => 1
  | UVALUE_I64 x => 1
  | UVALUE_IPTR x => 1
  | UVALUE_Double x => 1
  | UVALUE_Float x => 1
  | UVALUE_Undef t => 1
  | UVALUE_Poison t => 1
  | UVALUE_None => 1
  | UVALUE_Struct fields => S (S (list_sum (map uvalue_measure fields)))
  | UVALUE_Packed_struct fields => S (S (list_sum (map uvalue_measure fields)))
  | UVALUE_Array elts => S (S (list_sum (map uvalue_measure elts)))
  | UVALUE_Vector elts => S (S (list_sum (map uvalue_measure elts)))
  | UVALUE_IBinop _ v1 v2
  | UVALUE_ICmp _ v1 v2
  | UVALUE_FBinop _ _ v1 v2
  | UVALUE_FCmp _ v1 v2 =>
    S (uvalue_measure v1 + uvalue_measure v2)
  | UVALUE_Conversion conv t_from v t_to =>
    S (uvalue_measure v)
  | UVALUE_GetElementPtr t ptrval idxs =>
    S (uvalue_measure ptrval + list_sum (map uvalue_measure idxs))
  | UVALUE_ExtractElement vec idx =>
    S (uvalue_measure vec + uvalue_measure idx)
  | UVALUE_InsertElement vec elt idx =>
    S (uvalue_measure vec + uvalue_measure elt + uvalue_measure idx)
  | UVALUE_ShuffleVector vec1 vec2 idxmask =>
    S (uvalue_measure vec1 + uvalue_measure vec2 + uvalue_measure idxmask)
  | UVALUE_ExtractValue vec idxs =>
    S (uvalue_measure vec)
  | UVALUE_InsertValue vec elt idxs =>
    S (uvalue_measure vec + uvalue_measure elt)
  | UVALUE_Select cnd v1 v2 =>
    S (uvalue_measure cnd + uvalue_measure v1 + uvalue_measure v2)
  | UVALUE_ExtractByte uv dt idx sid =>
    S (uvalue_measure uv + uvalue_measure idx)
  | UVALUE_ConcatBytes uvs dt =>
    S (list_sum (map uvalue_measure uvs))
  end.

Lemma uvalue_measure_gt_0 :
  forall (uv : uvalue),
    (0 < uvalue_measure uv)%nat.
Proof.
  destruct uv; cbn; auto.
  all: apply Nat.lt_0_succ.
Qed.

Definition dvalue_is_poison (dv : dvalue) : bool :=
  match dv with
  | DVALUE_Poison dt => true
  | _ => false
  end.

Definition uvalue_is_poison (uv : uvalue) : bool :=
  match uv with
  | UVALUE_Poison dt => true
  | _ => false
  end.

Section UvalueInd.
  Variable P : uvalue -> Prop.
  Hypothesis IH_Addr           : forall a, P (UVALUE_Addr a).
  Hypothesis IH_I1             : forall x, P (UVALUE_I1 x).
  Hypothesis IH_I8             : forall x, P (UVALUE_I8 x).
  Hypothesis IH_I32            : forall x, P (UVALUE_I32 x).
  Hypothesis IH_I64            : forall x, P (UVALUE_I64 x).
  Hypothesis IH_IPTR            : forall x, P (UVALUE_IPTR x).
  Hypothesis IH_Double         : forall x, P (UVALUE_Double x).
  Hypothesis IH_Float          : forall x, P (UVALUE_Float x).
  Hypothesis IH_Undef          : forall t, P (UVALUE_Undef t).
  Hypothesis IH_Poison         : forall t, P (UVALUE_Poison t).
  Hypothesis IH_None           : P UVALUE_None.
  Hypothesis IH_Struct         : forall (fields: list uvalue), (forall u, In u fields -> P u) -> P (UVALUE_Struct fields).
  Hypothesis IH_Packed_Struct  : forall (fields: list uvalue), (forall u, In u fields -> P u) -> P (UVALUE_Packed_struct fields).
  Hypothesis IH_Array          : forall (elts: list uvalue), (forall e, In e elts -> P e) -> P (UVALUE_Array elts).
  Hypothesis IH_Vector         : forall (elts: list uvalue), (forall e, In e elts -> P e) -> P (UVALUE_Vector elts).
  Hypothesis IH_IBinop         : forall (iop:ibinop) (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_IBinop iop v1 v2).
  Hypothesis IH_ICmp           : forall (cmp:icmp)   (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_ICmp cmp v1 v2).
  Hypothesis IH_FBinop         : forall (fop:fbinop) (fm:list fast_math) (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_FBinop fop fm v1 v2).
  Hypothesis IH_FCmp           : forall (cmp:fcmp)   (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_FCmp cmp v1 v2).
  Hypothesis IH_Conversion     : forall (conv:conversion_type) (t_from:dtyp) (v:uvalue) (t_to:dtyp), P v -> P (UVALUE_Conversion conv t_from v t_to).
  Hypothesis IH_GetElementPtr  : forall (t:dtyp) (ptrval:uvalue) (idxs:list (uvalue)), P ptrval -> (forall idx, In idx idxs -> P idx) -> P (UVALUE_GetElementPtr t ptrval idxs).
  Hypothesis IH_ExtractElement : forall (vec: uvalue) (idx: uvalue), P vec -> P idx -> P (UVALUE_ExtractElement vec idx).
  Hypothesis IH_InsertElement  : forall (vec: uvalue) (elt:uvalue) (idx:uvalue), P vec -> P elt -> P idx -> P (UVALUE_InsertElement vec elt idx).
  Hypothesis IH_ShuffleVector  : forall (vec1:uvalue) (vec2:uvalue) (idxmask:uvalue), P vec1 -> P vec2 -> P idxmask -> P (UVALUE_ShuffleVector vec1 vec2 idxmask).
  Hypothesis IH_ExtractValue   : forall (vec:uvalue) (idxs:list LLVMAst.int), P vec -> P (UVALUE_ExtractValue vec idxs).
  Hypothesis IH_InsertValue    : forall (vec:uvalue) (elt:uvalue) (idxs:list LLVMAst.int), P vec -> P elt -> P (UVALUE_InsertValue vec elt idxs).
  Hypothesis IH_Select         : forall (cnd:uvalue) (v1:uvalue) (v2:uvalue), P cnd -> P v1 -> P v2 -> P (UVALUE_Select cnd v1 v2).
  Hypothesis IH_ExtractByte : forall (uv : uvalue) (dt : dtyp) (idx : uvalue) (sid : N), P uv -> P idx -> P (UVALUE_ExtractByte uv dt idx sid).
  Hypothesis IH_ConcatBytes : forall (dt : dtyp) (uvs : list uvalue),
      (forall u, In u uvs -> P u) ->
      P (UVALUE_ConcatBytes uvs dt).

  Lemma uvalue_ind : forall (uv:uvalue), P uv.
    fix IH 1.
    remember P as P0 in IH.
    destruct uv; auto; subst.
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
    - apply IH_Array.
      { revert elts.
        fix IHelts 1. intros [|u elts']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IHelts. apply Hin.
      }
    - apply IH_Vector.
      { revert elts.
        fix IHelts 1. intros [|u elts']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IHelts. apply Hin.
      }
    - apply IH_IBinop; auto.
    - apply IH_ICmp; auto.
    - apply IH_FBinop; auto.
    - apply IH_FCmp; auto.
    - apply IH_Conversion; auto.
    - apply IH_GetElementPtr. apply IH.
      { revert idxs.
        fix IHidxs 1. intros [|u idxs']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IHidxs. apply Hin.
      }
    - apply IH_ExtractElement; auto.
    - apply IH_InsertElement; auto.
    - apply IH_ShuffleVector; auto.
    - apply IH_ExtractValue; auto.
    - apply IH_InsertValue; auto.
    - apply IH_Select; auto.
    - apply IH_ExtractByte; auto.
    - apply IH_ConcatBytes.
      { revert uvs.
        fix IHuvs 1. intros [|u uvs']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IHuvs. apply Hin.
      }
  Qed.
End UvalueInd.

(* Injection of [dvalue] into [uvalue] *)
Fixpoint dvalue_to_uvalue (dv : dvalue) : uvalue :=
  match dv with
  | DVALUE_Addr a => UVALUE_Addr a
  | DVALUE_I1 x => UVALUE_I1 x
  | DVALUE_I8 x => UVALUE_I8 x
  | DVALUE_I32 x => UVALUE_I32 x
  | DVALUE_I64 x => UVALUE_I64 x
  | DVALUE_IPTR x => UVALUE_IPTR x
  | DVALUE_Double x => UVALUE_Double x
  | DVALUE_Float x => UVALUE_Float x
  | DVALUE_Poison t => UVALUE_Poison t
  | DVALUE_None => UVALUE_None
  | DVALUE_Struct fields => UVALUE_Struct (map dvalue_to_uvalue fields)
  | DVALUE_Packed_struct fields => UVALUE_Packed_struct (map dvalue_to_uvalue fields)
  | DVALUE_Array elts => UVALUE_Array (map dvalue_to_uvalue elts)
  | DVALUE_Vector elts => UVALUE_Vector (map dvalue_to_uvalue elts)
  end.

(* Partial injection of [uvalue] into [dvalue] *)
Fixpoint uvalue_to_dvalue (uv : uvalue) : err dvalue :=
  match uv with
  | UVALUE_Addr a                          => ret (DVALUE_Addr a)
  | UVALUE_I1 x                            => ret (DVALUE_I1 x)
  | UVALUE_I8 x                            => ret (DVALUE_I8 x)
  | UVALUE_I32 x                           => ret (DVALUE_I32 x)
  | UVALUE_I64 x                           => ret (DVALUE_I64 x)
  | UVALUE_IPTR x                          => ret (DVALUE_IPTR x)
  | UVALUE_Double x                        => ret (DVALUE_Double x)
  | UVALUE_Float x                         => ret (DVALUE_Float x)
  | UVALUE_Undef t                         => failwith "Attempting to convert a non-defined uvalue to dvalue. The conversion should be guarded by is_concrete"
  | UVALUE_Poison t                        => ret (DVALUE_Poison t)
  | UVALUE_None                            => ret (DVALUE_None)

  | UVALUE_Struct fields                   =>
    fields' <- map_monad uvalue_to_dvalue fields ;;
    ret (DVALUE_Struct fields')

  | UVALUE_Packed_struct fields            =>
    fields' <- map_monad uvalue_to_dvalue fields ;;
    ret (DVALUE_Packed_struct fields')

  | UVALUE_Array elts                      =>
    elts' <- map_monad uvalue_to_dvalue elts ;;
    ret (DVALUE_Array elts')

  | UVALUE_Vector elts                     =>
    elts' <- map_monad uvalue_to_dvalue elts ;;
    ret (DVALUE_Vector elts')

  | _ => failwith "Attempting to convert a partially non-reduced uvalue to dvalue. Should not happen"
end.

Lemma uvalue_to_dvalue_of_dvalue_to_uvalue :
  forall (d : dvalue),
    uvalue_to_dvalue (dvalue_to_uvalue d : uvalue) = inr d.
Proof.
  intros.
  induction d; auto.
  - cbn. induction fields. cbn. reflexivity.
    assert (forall u : dvalue,
               In u fields ->
               uvalue_to_dvalue (dvalue_to_uvalue u : uvalue) = inr u).
    intros. apply H. apply in_cons; auto. specialize (IHfields H0).
    clear H0. rewrite map_cons. rewrite list_cons_app.
    rewrite map_monad_app. cbn.
    destruct (map_monad uvalue_to_dvalue (map dvalue_to_uvalue fields)) eqn: EQ.
    + discriminate IHfields.
    + rewrite H. cbn. inversion IHfields. reflexivity.
      constructor; auto.
  - cbn. induction fields. cbn. reflexivity.
    assert (forall u : dvalue,
               In u fields ->
               uvalue_to_dvalue (dvalue_to_uvalue u : uvalue) = inr u).
    intros. apply H. apply in_cons; auto. specialize (IHfields H0).
    clear H0. rewrite map_cons. rewrite list_cons_app.
    rewrite map_monad_app. cbn.
    destruct (map_monad uvalue_to_dvalue (map dvalue_to_uvalue fields)) eqn: EQ.
    + discriminate IHfields.
    + rewrite H. cbn. inversion IHfields. reflexivity.
      constructor; auto.
  - cbn. induction elts. cbn. reflexivity.
    assert (forall u : dvalue,
               In u elts ->
               uvalue_to_dvalue (dvalue_to_uvalue u : uvalue) = inr u).
    intros. apply H. apply in_cons; auto. specialize (IHelts H0).
    clear H0. rewrite map_cons. rewrite list_cons_app.
    rewrite map_monad_app. cbn.
    destruct (map_monad uvalue_to_dvalue (map dvalue_to_uvalue elts)) eqn: EQ.
    + discriminate IHelts.
    + rewrite H. cbn. inversion IHelts. reflexivity.
      constructor; auto.
  - cbn. induction elts. cbn. reflexivity.
    assert (forall u : dvalue,
               In u elts ->
               uvalue_to_dvalue (dvalue_to_uvalue u : uvalue) = inr u).
    intros. apply H. apply in_cons; auto. specialize (IHelts H0).
    clear H0. rewrite map_cons. rewrite list_cons_app.
    rewrite map_monad_app. cbn.
    destruct (map_monad uvalue_to_dvalue (map dvalue_to_uvalue elts)) eqn: EQ.
    + discriminate IHelts.
    + rewrite H. cbn. inversion IHelts. reflexivity.
      constructor; auto.
Qed.


(* returns true iff the uvalue contains no occurrence of UVALUE_Undef. *)
(* YZ: See my comment above. If I'm correct, then we should also fail on operators and hence have:
   is_concrete uv = true <-> uvalue_to_dvalue uv = Some v
 *)
Fixpoint is_concrete (uv : uvalue) : bool :=
  match uv with
  | UVALUE_Addr a => true
  | UVALUE_I1 x => true
  | UVALUE_I8 x => true
  | UVALUE_I32 x => true
  | UVALUE_I64 x => true
  | UVALUE_IPTR x => true
  | UVALUE_Double x => true
  | UVALUE_Float x => true
  | UVALUE_Undef t => false
  | UVALUE_Poison t => true
  | UVALUE_None => true
  | UVALUE_Struct fields => forallb is_concrete fields
  | UVALUE_Packed_struct fields => forallb is_concrete fields
  | UVALUE_Array elts => forallb is_concrete elts
  | UVALUE_Vector elts => forallb is_concrete elts
  | _ => false
  end.

(* If both operands are concrete, uvalue_to_dvalue them and run them through
   opd, else run the abstract ones through opu *)
Definition uvalue_to_dvalue_binop {A : Type}
           (opu : uvalue -> uvalue -> A) (opd : dvalue -> dvalue -> A) (uv1 uv2 : uvalue) : A :=
  let ma := dv1 <- uvalue_to_dvalue uv1 ;; dv2 <- uvalue_to_dvalue uv2 ;; ret (opd dv1 dv2)
  in match ma with
     | inl e => opu uv1 uv2
     | inr a => a
     end.

(* Like uvalue_to_dvalue_binop, but the second operand is already concrete *)
Definition uvalue_to_dvalue_binop2 {A : Type}
           (opu : uvalue -> uvalue -> A) (opd : dvalue -> dvalue -> A) (uv1 : uvalue) (dv2 : dvalue) : A :=
  let ma := dv1 <- uvalue_to_dvalue uv1 ;; ret (opd dv1 dv2)
  in match ma with
     | inl e => opu uv1 (dvalue_to_uvalue dv2 : uvalue)
     | inr a => a
     end.

Definition uvalue_to_dvalue_uop {A : Type}
           (opu : uvalue -> A) (opd : dvalue -> A) (uv : uvalue ) : A :=
  let ma := dv <- uvalue_to_dvalue uv ;; ret (opd dv)
  in match ma with
     | inl e => opu uv
     | inr a => a
     end.

Section hiding_notation.
  #[local] Open Scope sexp_scope.

  Fixpoint serialize_dvalue' (dv:dvalue): sexp :=
    match dv with
    | DVALUE_Addr a => Atom "address" (* TODO: insist that memory models can print addresses? *)
    | DVALUE_I1 x => Atom "dvalue(i1)"
    | DVALUE_I8 x => Atom "dvalue(i8)"
    | DVALUE_I32 x => Atom "dvalue(i32)"
    | DVALUE_I64 x => Atom "dvalue(i64)"
    | DVALUE_IPTR x => Atom "dvalue(iptr)"
    | DVALUE_Double x => Atom "dvalue(double)"
    | DVALUE_Float x => Atom "dvalue(float)"
    | DVALUE_Poison t => Atom "poison"
    | DVALUE_None => Atom "none"
    | DVALUE_Struct fields
      => [Atom "{" ; to_sexp (List.map (fun x => [serialize_dvalue' x ; Atom ","]) fields) ; Atom "}"]
    | DVALUE_Packed_struct fields
      => [Atom "packed{" ; to_sexp (List.map (fun x => [serialize_dvalue' x ; Atom ","]) fields) ; Atom "}"]
    | DVALUE_Array elts
      => [Atom "[" ; to_sexp (List.map (fun x => [serialize_dvalue' x ; Atom ","]) elts) ; Atom "]"]
    | DVALUE_Vector elts
      => [Atom "<" ; to_sexp (List.map (fun x => [serialize_dvalue' x ; Atom  ","]) elts) ; Atom ">"]
    end.

  #[global] Instance serialize_dvalue : Serialize dvalue := serialize_dvalue'.

  Fixpoint serialize_uvalue' (pre post: string) (uv:uvalue): sexp :=
    match uv with
    | UVALUE_Addr a => Atom (pre ++ "address" ++ post)%string (* TODO: insist that memory models can print addresses? *)
    | UVALUE_I1 x => Atom (pre ++ "uvalue(i1)" ++ post)%string
    | UVALUE_I8 x => Atom (pre ++ "uvalue(i8)" ++ post)%string
    | UVALUE_I32 x => Atom (pre ++ "uvalue(i32)" ++ post)%string
    | UVALUE_I64 x => Atom (pre ++ "uvalue(i64)" ++ post)%string
    | UVALUE_Double x => Atom (pre ++ "uvalue(double)" ++ post)%string
    | UVALUE_Float x => Atom (pre ++ "uvalue(float)" ++ post)%string
    | UVALUE_Poison t => Atom (pre ++ "poison" ++ post)%string
    | UVALUE_None => Atom (pre ++ "none" ++ post)%string
    | UVALUE_Struct fields
      => [Atom "{" ; to_sexp (List.map (serialize_uvalue' "" ",") fields) ; Atom "}"]
    | UVALUE_Packed_struct fields
      => [Atom "packed{" ; to_sexp (List.map (serialize_uvalue' "" ",") fields) ; Atom "}"]
    | UVALUE_Array elts
      => [Atom "[" ; to_sexp (List.map (serialize_uvalue' "" ",") elts) ; Atom "]"]
    | UVALUE_Vector elts
      => [Atom "<" ; to_sexp (List.map (serialize_uvalue' "" ",") elts) ; Atom ">"]
    | UVALUE_Undef t => [Atom "undef(" ; to_sexp t ; Atom ")"]
    | UVALUE_IBinop iop v1 v2 => [serialize_uvalue' "(" "" v1; to_sexp iop ; serialize_uvalue' "" ")" v2]
    | UVALUE_ICmp cmp v1 v2 => [serialize_uvalue' "(" "" v1; to_sexp cmp; serialize_uvalue' "" ")" v2]
    | UVALUE_FBinop fop _ v1 v2 => [serialize_uvalue' "(" "" v1; to_sexp fop; serialize_uvalue' "" ")" v2]
    | UVALUE_FCmp cmp v1 v2 => [serialize_uvalue' "(" "" v1; to_sexp cmp; serialize_uvalue' "" ")" v2]
    | _ => Atom "TODO: show_uvalue"
    end.

  #[global] Instance serialize_uvalue : Serialize (uvalue) := serialize_uvalue' "" "".

End hiding_notation.

Ltac dec_dvalue :=
  match goal with
  | [ |- { ?X ?a = ?X ?b} + { ?X ?a <> ?X ?b} ] => idtac
  | [ |- { ?X ?a = ?Y ?b} + { ?X ?a <> ?Y ?b} ] => right; intros H; inversion H
  | [ |- { ?X = ?X } + { ?X <> ?X } ] => left; reflexivity
  | [ |- { ?X = ?Y } + { ?X <> ?Y } ] => right; intros H; inversion H
  end.


Section DecidableEquality.

  Fixpoint dvalue_eqb (d1 d2:dvalue) : bool :=
    let lsteq := list_eqb (Build_RelDec eq dvalue_eqb) in
    match d1, d2 with
    | DVALUE_Addr a1, DVALUE_Addr a2 =>
      if A.eq_dec a1 a2 then true else false
    | DVALUE_I1 x1, DVALUE_I1 x2 =>
      if Int1.eq_dec x1 x2 then true else false
    | DVALUE_I8 x1, DVALUE_I8 x2 =>
      if Int8.eq_dec x1 x2 then true else false
    | DVALUE_I32 x1, DVALUE_I32 x2 =>
      if Int32.eq_dec x1 x2 then true else false
    | DVALUE_I64 x1, DVALUE_I64 x2 =>
      if Int64.eq_dec x1 x2 then true else false
    | DVALUE_Double x1, DVALUE_Double x2 =>
      if Float.eq_dec x1 x2 then true else false
    | DVALUE_Float x1, DVALUE_Float x2 =>
      if Float32.eq_dec x1 x2 then true else false
    | DVALUE_Poison t1, DVALUE_Poison t2 =>
      dtyp_eqb t1 t2
    | DVALUE_None, DVALUE_None => true
    | DVALUE_Struct f1, DVALUE_Struct f2 =>
      lsteq f1 f2
    | DVALUE_Packed_struct f1, DVALUE_Packed_struct f2 =>
      lsteq f1 f2
    | DVALUE_Array f1, DVALUE_Array f2 =>
      lsteq f1 f2
    | DVALUE_Vector f1, DVALUE_Vector f2 =>
      lsteq f1 f2
    | _, _ => false
    end.

  Lemma dvalue_eq_dec : forall (d1 d2:dvalue), {d1 = d2} + {d1 <> d2}.
    refine (fix f d1 d2 :=
    let lsteq_dec := list_eq_dec f in
    match d1, d2 with
    | DVALUE_Addr a1, DVALUE_Addr a2 => _
    | DVALUE_I1 x1, DVALUE_I1 x2 => _
    | DVALUE_I8 x1, DVALUE_I8 x2 => _
    | DVALUE_I32 x1, DVALUE_I32 x2 => _
    | DVALUE_I64 x1, DVALUE_I64 x2 => _
    | DVALUE_IPTR x1, DVALUE_IPTR x2 => _
    | DVALUE_Double x1, DVALUE_Double x2 => _
    | DVALUE_Float x1, DVALUE_Float x2 => _
    | DVALUE_Poison _, DVALUE_Poison _ => _
    | DVALUE_None, DVALUE_None => _
    | DVALUE_Struct f1, DVALUE_Struct f2 => _
    | DVALUE_Packed_struct f1, DVALUE_Packed_struct f2 => _
    | DVALUE_Array f1, DVALUE_Array f2 => _
    | DVALUE_Vector f1, DVALUE_Vector f2 => _
    | _, _ => _
    end);  ltac:(dec_dvalue).
    - destruct (A.eq_dec a1 a2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (Int1.eq_dec x1 x2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (Int8.eq_dec x1 x2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (Int32.eq_dec x1 x2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (Int64.eq_dec x1 x2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (Z.eq_dec x1 x2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (Float.eq_dec x1 x2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (Float32.eq_dec x1 x2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (dtyp_eq_dec d d0).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (lsteq_dec f1 f2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (lsteq_dec f1 f2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (lsteq_dec f1 f2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (lsteq_dec f1 f2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
  Qed.

  #[global] Instance eq_dec_dvalue : RelDec (@eq dvalue) := RelDec_from_dec (@eq dvalue) (@dvalue_eq_dec).
  #[global] Instance eqv_dvalue : Eqv dvalue := (@eq dvalue).
  Hint Unfold eqv_dvalue : core.

 Lemma ibinop_eq_dec : forall (op1 op2:ibinop), {op1 = op2} + {op1 <> op2}.
    intros.
    repeat decide equality.
  Qed.

  Lemma fbinop_eq_dec : forall (op1 op2:fbinop), {op1 = op2} + {op1 <> op2}.
    intros.
    repeat decide equality.
  Qed.

  Lemma icmp_eq_dec : forall (op1 op2:icmp), {op1 = op2} + {op1 <> op2}.
    intros.
    repeat decide equality.
  Qed.

  Lemma fcmp_eq_dec : forall (op1 op2:fcmp), {op1 = op2} + {op1 <> op2}.
    intros.
    repeat decide equality.
  Qed.

  Lemma fast_math_eq_dec : forall (op1 op2:fast_math), {op1 = op2} + {op1 <> op2}.
    intros.
    repeat decide equality.
  Qed.

  Lemma conversion_type_eq_dec : forall (op1 op2:conversion_type), {op1 = op2} + {op1 <> op2}.
    intros.
    repeat decide equality.
  Qed.

  Arguments ibinop_eq_dec: clear implicits.
  Arguments fbinop_eq_dec: clear implicits.
  Arguments icmp_eq_dec: clear implicits.
  Arguments fcmp_eq_dec: clear implicits.
  Arguments fast_math_eq_dec: clear implicits.
  Arguments conversion_type_eq_dec: clear implicits.

  Ltac __abs := right; intros H; inversion H; contradiction.
  Ltac __eq := left; subst; reflexivity.

  Lemma uvalue_eq_dec : forall (u1 u2:uvalue), {u1 = u2} + {u1 <> u2}.
  Proof with (try (__eq || __abs)).
    refine (fix f u1 u2 :=
              let lsteq_dec := list_eq_dec f in
              match u1, u2 with
              | UVALUE_Addr a1, UVALUE_Addr a2 => _
              | UVALUE_I1 x1, UVALUE_I1 x2 => _
              | UVALUE_I8 x1, UVALUE_I8 x2 => _
              | UVALUE_I32 x1, UVALUE_I32 x2 => _
              | UVALUE_I64 x1, UVALUE_I64 x2 => _
              | UVALUE_IPTR x1, UVALUE_IPTR x2 => _
              | UVALUE_Double x1, UVALUE_Double x2 => _
              | UVALUE_Float x1, UVALUE_Float x2 => _
              | UVALUE_Undef t1, UVALUE_Undef t2 => _
              | UVALUE_Poison t1, UVALUE_Poison t2 => _
              | UVALUE_None, UVALUE_None => _
              | UVALUE_Struct f1, UVALUE_Struct f2 => _
              | UVALUE_Packed_struct f1, UVALUE_Packed_struct f2 => _
              | UVALUE_Array f1, UVALUE_Array f2 => _
              | UVALUE_Vector f1, UVALUE_Vector f2 => _
              | UVALUE_IBinop op uv1 uv2, UVALUE_IBinop op' uv1' uv2' => _
              | UVALUE_ICmp op uv1 uv2, UVALUE_ICmp op' uv1' uv2' => _
              | UVALUE_FBinop op fm uv1 uv2, UVALUE_FBinop op' fm' uv1' uv2' => _
              | UVALUE_FCmp op uv1 uv2, UVALUE_FCmp op' uv1' uv2' => _
              | UVALUE_Conversion ct tf u t, UVALUE_Conversion ct' tf' u' t' => _
              | UVALUE_GetElementPtr t u l, UVALUE_GetElementPtr t' u' l' => _
              | UVALUE_ExtractElement u v, UVALUE_ExtractElement u' v' => _
              | UVALUE_InsertElement u v t, UVALUE_InsertElement u' v' t' => _
              | UVALUE_ShuffleVector u v t, UVALUE_ShuffleVector u' v' t' => _
              | UVALUE_ExtractValue u l, UVALUE_ExtractValue u' l' => _
              | UVALUE_InsertValue u v l, UVALUE_InsertValue u' v' l' => _
              | UVALUE_Select u v t, UVALUE_Select u' v' t' => _
              | UVALUE_ExtractByte uv dt idx sid, UVALUE_ExtractByte uv' dt' idx' sid' => _
              | UVALUE_ConcatBytes uvs dt, UVALUE_ConcatBytes uvs' dt' => _
              | _, _ => _
              end); try (ltac:(dec_dvalue); fail).
    - destruct (A.eq_dec a1 a2)...
    - destruct (Int1.eq_dec x1 x2)...
    - destruct (Int8.eq_dec x1 x2)...
    - destruct (Int32.eq_dec x1 x2)...
    - destruct (Int64.eq_dec x1 x2)...
    - destruct (Z.eq_dec x1 x2)...
    - destruct (Float.eq_dec x1 x2)...
    - destruct (Float32.eq_dec x1 x2)...
    - destruct (dtyp_eq_dec t1 t2)...
    - destruct (dtyp_eq_dec t1 t2)...
    - destruct (lsteq_dec f1 f2)...
    - destruct (lsteq_dec f1 f2)...
    - destruct (lsteq_dec f1 f2)...
    - destruct (lsteq_dec f1 f2)...
    - destruct (ibinop_eq_dec op op')...
      destruct (f uv1 uv1')...
      destruct (f uv2 uv2')...
    - destruct (icmp_eq_dec op op')...
      destruct (f uv1 uv1')...
      destruct (f uv2 uv2')...
    - destruct (fbinop_eq_dec op op')...
      destruct (list_eq_dec fast_math_eq_dec fm fm')...
      destruct (f uv1 uv1')...
      destruct (f uv2 uv2')...
    - destruct (fcmp_eq_dec op op')...
      destruct (f uv1 uv1')...
      destruct (f uv2 uv2')...
    - destruct (conversion_type_eq_dec ct ct')...
      destruct (f u u')...
      destruct (dtyp_eq_dec tf tf')...
      destruct (dtyp_eq_dec t t')...
    - destruct (dtyp_eq_dec t t')...
      destruct (f u u')...
      destruct (lsteq_dec l l')...
    - destruct (f u u')...
      destruct (f v v')...
    - destruct (f u u')...
      destruct (f v v')...
      destruct (f t t')...
    - destruct (f u u')...
      destruct (f v v')...
      destruct (f t t')...
    - destruct (f u u')...
      destruct (list_eq_dec Z.eq_dec l l')...
    - destruct (f u u')...
      destruct (f v v')...
      destruct (list_eq_dec Z.eq_dec l l')...
    - destruct (f u u')...
      destruct (f v v')...
      destruct (f t t')...
    - destruct (f uv uv')...
      destruct (f idx idx')...
      destruct (N.eq_dec sid sid')...
      destruct (dtyp_eq_dec dt dt')...
    - destruct (lsteq_dec uvs uvs')...
      destruct (dtyp_eq_dec dt dt')...
  Qed.


  #[global] Instance eq_dec_uvalue : RelDec (@eq uvalue) := RelDec_from_dec (@eq uvalue) (@uvalue_eq_dec).
  #[global] Instance eqv_uvalue : Eqv (uvalue) := (@eq uvalue).
  Hint Unfold eqv_uvalue : core.
  #[global] Instance eq_dec_uvalue_correct: @RelDec.RelDec_Correct uvalue (@Logic.eq uvalue) _ := _.

End DecidableEquality.

Definition is_DVALUE_I1 (d:dvalue) : bool :=
  match d with
  | DVALUE_I1 _ => true
  | _ => false
  end.

Definition is_DVALUE_I8 (d:dvalue) : bool :=
  match d with
  | DVALUE_I8 _ => true
  | _ => false
  end.

Definition is_DVALUE_I32 (d:dvalue) : bool :=
  match d with
  | DVALUE_I32 _ => true
  | _ => false
  end.

Definition is_DVALUE_I64 (d:dvalue) : bool :=
  match d with
  | DVALUE_I64 _ => true
  | _ => false
  end.

Definition is_DVALUE_IX (d:dvalue) : bool :=
  is_DVALUE_I1 d || is_DVALUE_I8 d || is_DVALUE_I32 d || is_DVALUE_I64 d.


Class VInt I : Type :=
  {
    (* Comparisons *)
    equ : I -> I -> bool;
    cmp : comparison -> I -> I -> bool;
    cmpu : comparison -> I -> I -> bool;

    (* Constants *)
    bitwidth : nat;
    zero : I;
    one : I;

    (* Arithmetic *)
    add : I -> I -> I;
    add_carry : I -> I -> I -> I;
    add_overflow : I -> I -> I -> I;

    sub : I -> I -> I;
    sub_borrow : I -> I -> I -> I;
    sub_overflow : I -> I -> I -> I;

    mul : I -> I -> I;

    divu : I -> I -> I;
    divs : I -> I -> I;
    modu : I -> I -> I;
    mods : I -> I -> I;

    shl : I -> I -> I;
    shr : I -> I -> I;
    shru : I -> I -> I;

    negative : I -> I;

    (* Logic *)
    and : I -> I -> I;
    or : I -> I -> I;
    xor : I -> I -> I;

    (* Bounds *)
    min_signed : Z;
    max_signed : Z;

    (* Conversion *)
    to_dvalue : I -> dvalue;
    unsigned : I -> Z;
    signed : I -> Z;

    repr : Z -> I;
  }.


  #[global] Instance VInt1 : VInt Int1.int :=
  {
    (* Comparisons *)
    equ := Int1.eq;
    cmp := Int1.cmp;
    cmpu := Int1.cmpu;

    bitwidth := 1;

    (* Constants *)
    zero := Int1.zero;
    one := Int1.one;

    (* Arithmetic *)
    add := Int1.add;
    add_carry := Int1.add_carry;
    add_overflow := Int1.add_overflow;

    sub := Int1.sub;
    sub_borrow := Int1.sub_borrow;
    sub_overflow := Int1.sub_overflow;

    mul := Int1.mul;

    divu := Int1.divu;
    divs := Int1.divs;
    modu := Int1.modu;
    mods := Int1.mods;

    shl := Int1.shl;
    shr := Int1.shr;
    shru := Int1.shru;

    negative := Int1.negative;

    (* Logic *)
    and := Int1.and;
    or := Int1.or;
    xor := Int1.xor;

    (* Bounds *)
    min_signed := Int1.min_signed;
    max_signed := Int1.max_signed;

    (* Conversion *)
    to_dvalue := DVALUE_I1;
    unsigned := Int1.unsigned;
    signed := Int1.signed;

    repr := Int1.repr;
  }.


  #[global] Instance VInt8 : VInt Int8.int :=
  {
    (* Comparisons *)
    equ := Int8.eq;
    cmp := Int8.cmp;
    cmpu := Int8.cmpu;

    bitwidth := 8;

    (* Constants *)
    zero := Int8.zero;
    one := Int8.one;

    (* Arithmetic *)
    add := Int8.add;
    add_carry := Int8.add_carry;
    add_overflow := Int8.add_overflow;

    sub := Int8.sub;
    sub_borrow := Int8.sub_borrow;
    sub_overflow := Int8.sub_overflow;

    mul := Int8.mul;

    divu := Int8.divu;
    divs := Int8.divs;
    modu := Int8.modu;
    mods := Int8.mods;

    shl := Int8.shl;
    shr := Int8.shr;
    shru := Int8.shru;

    negative := Int8.negative;

    (* Logic *)
    and := Int8.and;
    or := Int8.or;
    xor := Int8.xor;

    (* Bounds *)
    min_signed := Int8.min_signed;
    max_signed := Int8.max_signed;

    (* Conversion *)
    to_dvalue := DVALUE_I8;
    unsigned := Int8.unsigned;
    signed := Int8.signed;

    repr := Int8.repr;
  }.


  #[global] Instance VInt32 : VInt Int32.int :=
  {
    (* Comparisons *)
    equ := Int32.eq;
    cmp := Int32.cmp;
    cmpu := Int32.cmpu;

    bitwidth := 32;

    (* Constants *)
    zero := Int32.zero;
    one := Int32.one;

    (* Arithmetic *)
    add := Int32.add;
    add_carry := Int32.add_carry;
    add_overflow := Int32.add_overflow;

    sub := Int32.sub;
    sub_borrow := Int32.sub_borrow;
    sub_overflow := Int32.sub_overflow;

    mul := Int32.mul;

    divu := Int32.divu;
    divs := Int32.divs;
    modu := Int32.modu;
    mods := Int32.mods;

    shl := Int32.shl;
    shr := Int32.shr;
    shru := Int32.shru;

    negative := Int32.negative;

    (* Logic *)
    and := Int32.and;
    or := Int32.or;
    xor := Int32.xor;

    (* Bounds *)
    min_signed := Int32.min_signed;
    max_signed := Int32.max_signed;

    (* Conversion *)
    to_dvalue := DVALUE_I32;
    unsigned := Int32.unsigned;
    signed := Int32.signed;

    repr := Int32.repr;
  }.

  #[global] Instance VInt64 : VInt Int64.int :=
  {
    (* Comparisons *)
    equ := Int64.eq;
    cmp := Int64.cmp;
    cmpu := Int64.cmpu;

    bitwidth := 64;

    (* Constants *)
    zero := Int64.zero;
    one := Int64.one;

    (* Arithmetic *)
    add := Int64.add;
    add_carry := Int64.add_carry;
    add_overflow := Int64.add_overflow;

    sub := Int64.sub;
    sub_borrow := Int64.sub_borrow;
    sub_overflow := Int64.sub_overflow;

    mul := Int64.mul;

    divu := Int64.divu;
    divs := Int64.divs;
    modu := Int64.modu;
    mods := Int64.mods;

    shl := Int64.shl;
    shr := Int64.shr;
    shru := Int64.shru;

    negative := Int64.negative;

    (* Logic *)
    and := Int64.and;
    or := Int64.or;
    xor := Int64.xor;

    (* Bounds *)
    min_signed := Int64.min_signed;
    max_signed := Int64.max_signed;

    (* Conversion *)
    to_dvalue := DVALUE_I64;
    unsigned := Int64.unsigned;
    signed := Int64.signed;

    repr := Int64.repr;
  }.

  (* Is a uvalue a concrete integer equal to i? *)
  Definition uvalue_int_eq_Z (uv : uvalue) (i : Z)
    := match uv with
       | UVALUE_I1 x
       | UVALUE_I8 x
       | UVALUE_I32 x
       | UVALUE_I64 x => Z.eqb (unsigned x) i
       | UVALUE_IPTR x => Z.eqb x i
       | _ => false
       end.

  Definition dvalue_int_unsigned (dv : dvalue) : Z
    := match dv with
       | DVALUE_I1 x => unsigned x
       | DVALUE_I8 x => unsigned x
       | DVALUE_I32 x => unsigned x
       | DVALUE_I64 x => unsigned x
       | DVALUE_IPTR x => x (* TODO: unsigned???? *)
       | _ => 0
       end.

  (* Check if this is an instruction which can trigger UB with division by 0. *)
  Definition iop_is_div (iop : ibinop) : bool :=
    match iop with
    | UDiv _ => true
    | SDiv _ => true
    | URem   => true
    | SRem   => true
    | _      => false
    end.

  (* Check if this is an instruction which can trigger UB with division by 0. *)
  Definition fop_is_div (fop : fbinop) : bool :=
    match fop with
    | FDiv => true
    | FRem => true
    | _    => false
    end.

  Definition undef_i1 : uvalue  := UVALUE_Undef (DTYPE_I 1).
  Definition undef_i8 : uvalue  := UVALUE_Undef (DTYPE_I 8).
  Definition undef_i32 : uvalue := UVALUE_Undef (DTYPE_I 32).
  Definition undef_i64 : uvalue := UVALUE_Undef (DTYPE_I 64).
  Definition undef_int {Int} `{VInt Int} : uvalue  := UVALUE_Undef (DTYPE_I (N.of_nat bitwidth)).

  Definition to_uvalue {Int} `{VInt Int} (i : Int) : uvalue := dvalue_to_uvalue (to_dvalue i).

  Section CONVERSIONS.

    (** ** Typed conversion
        Performs a dynamic conversion of a [dvalue] of type [t1] to one of type [t2].
        For instance, convert an integer over 8 bits to one over 1 bit by truncation.

        The conversion function is not pure, i.e. in particular cannot live in [DynamicValues.v]
        as would be natural, due to the [Int2Ptr] and [Ptr2Int] cases. At those types, the conversion
        needs to cast between integers and pointers, which depends on the memory model.
     *)

    (* Note: Inferring the subevent instance takes a small but non-trivial amount of time,
       and has to be done here hundreds and hundreds of times due to the brutal pattern matching on
       several values. Factoring the inference upfront is therefore necessary.
     *)

    (* A trick avoiding proofs that involve thousands of cases: we split the conversion into
      the composition of a huge case analysis that builds a value of [conv_case], and a function
      with only four cases to actually build the tree.
     *)
    Variant conv_case : Set :=
    | Conv_Pure (x : dvalue)
    | Conv_ItoP (x : dvalue)
    | Conv_PtoI (x : dvalue)
    | Conv_Illegal (s: string).

    Variant ptr_conv_cases : Set :=
    | PtrConv_ItoP
    | PtrConv_PtoI
    | PtrConv_Neither.

    Definition get_conv_case_ptr conv (t1 : dtyp) (t2 : dtyp) : ptr_conv_cases
      := match conv with
         | Inttoptr =>
           match t1, t2 with
           | DTYPE_I 64, DTYPE_Pointer => PtrConv_ItoP
           | DTYPE_IPTR, DTYPE_Pointer => PtrConv_ItoP
           | _, _ => PtrConv_Neither
           end
         | Ptrtoint =>
           match t1, t2 with
           | DTYPE_Pointer, DTYPE_I _ => PtrConv_PtoI
           | DTYPE_Pointer, DTYPE_IPTR => PtrConv_PtoI
           | _, _ => PtrConv_Neither
           end
         | _ => PtrConv_Neither
         end.

    (* TODO: move / replace with show instance *)
    Definition dvalue_to_string (x : dvalue) : string
      := match x with
       | DVALUE_Addr a => "DVALUE_Addr"
       | DVALUE_I1 x => "DVALUE_I1"
       | DVALUE_I8 x => "DVALUE_I8"
       | DVALUE_I32 x => "DVALUE_I32"
       | DVALUE_I64 x => "DVALUE_I64"
       | DVALUE_IPTR x => "DVALUE_IPTR"
       | DVALUE_Double x => "DVALUE_Double"
       | DVALUE_Float x => "DVALUE_Float"
       | DVALUE_Poison t => "DVALUE_Poison"
       | DVALUE_None => "DVALUE_None"
       | DVALUE_Struct fields => "DVALUE_Struct"
       | DVALUE_Packed_struct fields => "DVALUE_Packed_struct"
       | DVALUE_Array elts => "DVALUE_Array"
       | DVALUE_Vector elts => "DVALUE_Vector"
       end.

    Definition get_conv_case conv (t1:dtyp) (x:dvalue) (t2:dtyp) : conv_case :=
      match conv with
      | Trunc =>
        match t1, x, t2 with
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 1
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 1
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 1 =>
          Conv_Pure (DVALUE_I1 (repr (unsigned i1)))

        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 8
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 8 =>
          Conv_Pure (DVALUE_I8 (repr (unsigned i1)))

        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 32 =>
          Conv_Pure (DVALUE_I32 (repr (unsigned i1)))

        | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 1
        | DTYPE_I 32, DVALUE_Poison t, DTYPE_I 1
        | DTYPE_I 32, DVALUE_Poison t, DTYPE_I 8
        | DTYPE_I 64, DVALUE_Poison t, DTYPE_I 1
        | DTYPE_I 64, DVALUE_Poison t, DTYPE_I 8
        | DTYPE_I 64, DVALUE_Poison t, DTYPE_I 32 =>
          Conv_Pure (DVALUE_Poison t)

        | _, _, _ => Conv_Illegal "ill-typed conv"
        end

      | Zext =>
        match t1, x, t2 with
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 8 =>
          Conv_Pure (DVALUE_I8 (repr (unsigned i1)))

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 32
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 32 =>
          Conv_Pure (DVALUE_I32 (repr (unsigned i1)))

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 64
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 64
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 64 =>
          Conv_Pure (DVALUE_I64 (repr (unsigned i1)))

        | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 8
        | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 32
        | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 32
        | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 64
        | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 64
        | DTYPE_I 32, DVALUE_Poison t, DTYPE_I 64 =>
          Conv_Pure (DVALUE_Poison t)

        | _, _, _ => Conv_Illegal "ill-typed conv"
        end

      | Sext =>
        match t1, x, t2 with
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 8 =>
          Conv_Pure (DVALUE_I8 (repr (signed i1)))

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 32
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 32 =>
          Conv_Pure (DVALUE_I32 (repr (signed i1)))

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 64
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 64
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 64 =>
          Conv_Pure (DVALUE_I64 (repr (signed i1)))

        | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 8
        | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 32
        | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 32
        | DTYPE_I 1, DVALUE_Poison t, DTYPE_I 64
        | DTYPE_I 8, DVALUE_Poison t, DTYPE_I 64
        | DTYPE_I 32, DVALUE_Poison t, DTYPE_I 64 =>
          Conv_Pure (DVALUE_Poison t)

        | _, _, _ => Conv_Illegal "ill-typed conv"
        end

      | Bitcast =>
        match t1, x, t2 with
        | DTYPE_I bits1, x, DTYPE_I bits2 =>
          if bits1 =? bits2 then Conv_Pure x else Conv_Illegal "unequal bitsize in cast"
        | DTYPE_Float, DVALUE_Float x, DTYPE_I bits =>
          if bits =? 32
          then Conv_Pure (DVALUE_I32 (Float32.to_bits x))
          else Conv_Illegal "Float to integer with different bitwidth."
        | DTYPE_I bits, DVALUE_I32 x, DTYPE_Float =>
          if bits =? 32
          then Conv_Pure (DVALUE_Float (Float32.of_bits x))
          else Conv_Illegal "Integer to float with different bitwidth."
        | DTYPE_Double, DVALUE_Double x, DTYPE_I bits =>
          if bits =? 64
          then Conv_Pure (DVALUE_I64 (Float.to_bits x))
          else Conv_Illegal "Double to integer with different bitwidth."
        | DTYPE_I bits, DVALUE_I64 x, DTYPE_Double =>
          if bits =? 64
          then Conv_Pure (DVALUE_Double (Float.of_bits x))
          else Conv_Illegal "Integer to double with different bitwidth."
        | DTYPE_Pointer, DVALUE_Addr a, DTYPE_Pointer =>
          Conv_Pure (DVALUE_Addr a)
        | DTYPE_Pointer, DVALUE_Poison t, DTYPE_Pointer =>
          Conv_Pure (DVALUE_Poison t)
        | _, _, _ => Conv_Illegal "ill-typed conv"
        end

      | Uitofp =>
        match t1, x, t2 with
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Float
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Float
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Float
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Float =>
          Conv_Pure (DVALUE_Float (Float32.of_intu (repr (unsigned i1))))

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Double
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Double
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Double
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Double =>
          Conv_Pure (DVALUE_Double (Float.of_longu (repr (unsigned i1))))

        | DTYPE_I 1, DVALUE_Poison t, DTYPE_Float
        | DTYPE_I 8, DVALUE_Poison t, DTYPE_Float
        | DTYPE_I 32, DVALUE_Poison t, DTYPE_Float
        | DTYPE_I 64, DVALUE_Poison t, DTYPE_Float
        | DTYPE_I 1, DVALUE_Poison t, DTYPE_Double
        | DTYPE_I 8, DVALUE_Poison t, DTYPE_Double
        | DTYPE_I 32, DVALUE_Poison t, DTYPE_Double
        | DTYPE_I 64, DVALUE_Poison t, DTYPE_Double =>
          Conv_Pure (DVALUE_Poison t)

        | _, _, _ => Conv_Illegal "ill-typed Uitofp"
        end

      | Sitofp =>
        match t1, x, t2 with
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Float
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Float
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Float
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Float =>
          Conv_Pure (DVALUE_Float (Float32.of_intu (repr (signed i1))))

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Double
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Double
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Double
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Double =>
          Conv_Pure (DVALUE_Double (Float.of_longu (repr (signed i1))))

        | DTYPE_I 1, DVALUE_Poison t, DTYPE_Float
        | DTYPE_I 8, DVALUE_Poison t, DTYPE_Float
        | DTYPE_I 32, DVALUE_Poison t, DTYPE_Float
        | DTYPE_I 64, DVALUE_Poison t, DTYPE_Float
        | DTYPE_I 1, DVALUE_Poison t, DTYPE_Double
        | DTYPE_I 8, DVALUE_Poison t, DTYPE_Double
        | DTYPE_I 32, DVALUE_Poison t, DTYPE_Double
        | DTYPE_I 64, DVALUE_Poison t, DTYPE_Double =>
          Conv_Pure (DVALUE_Poison t)

        | _, _, _ => Conv_Illegal "ill-typed Sitofp"
        end

      | Inttoptr =>
        match t1, t2 with
        | DTYPE_I 64, DTYPE_Pointer => Conv_ItoP x
        | _, _ => Conv_Illegal "ERROR: Inttoptr got illegal arguments"
        end
      | Ptrtoint =>
        match t1, t2 with
        | DTYPE_Pointer, DTYPE_I _ => Conv_PtoI x
        | _, _ => Conv_Illegal "ERROR: Ptrtoint got illegal arguments"
        end

      | Fptoui
      | Fptosi
      | Fptrunc
      | Fpext
        => Conv_Illegal "TODO: unimplemented numeric conversion"
      end.
    Arguments get_conv_case _ _ _ _ : simpl nomatch.

  End CONVERSIONS.

  (* Arithmetic Operations ---------------------------------------------------- *)
  Section ARITHMETIC.

    (* Evaluate integer opererations to get a dvalue.

     These operations are between VInts, which are "vellvm"
     integers. This is a typeclass that wraps all of the integer
     operations that we use for integer types with different bitwidths.

     *)
    Definition eval_int_op {Int} `{VInt Int} (iop:ibinop) (x y: Int) : UB dvalue :=
      match iop with
      (* Following to cases are probably right since they use CompCert *)
      | Add nuw nsw =>
        ret (if orb (andb nuw (equ (add_carry x y zero) one))
                    (andb nsw (equ (add_overflow x y zero) one))
             then (DVALUE_Poison (DTYPE_I (N.of_nat bitwidth))) else to_dvalue (add x y))

    | Sub nuw nsw =>
      ret (if orb (andb nuw (equ (sub_borrow x y zero) one))
                  (andb nsw (equ (sub_overflow x y zero) one))
           then (DVALUE_Poison (DTYPE_I (N.of_nat bitwidth))) else to_dvalue (sub x y))

    | Mul nuw nsw =>
      (* I1 mul can't overflow, just based on the 4 possible multiplications. *)
      if (bitwidth ~=? 1)%nat then ret (to_dvalue (mul x y))
      else
        let res := mul x y in
        let res_s' := ((signed x) * (signed y))%Z in
        if orb (andb nuw ((unsigned x) * (unsigned y) >?
                      unsigned res))
             (andb nsw (orb (min_signed >? res_s')
                            (res_s' >? max_signed)))
      then ret (DVALUE_Poison (DTYPE_I (N.of_nat bitwidth))) else ret (to_dvalue res)

    | Shl nuw nsw =>
      let bz := Z.of_nat bitwidth in
      let res := shl x y in
      let res_u := unsigned res in
      let res_u' := Z.shiftl (unsigned x) (unsigned y) in
      (* Unsigned shift x right by bitwidth - y. If shifted x != sign bit * (2^y - 1),
         then there is overflow. *)
      if (unsigned y) >=? bz then ret (DVALUE_Poison (DTYPE_I (N.of_nat bitwidth)))
      else if orb (andb nuw (res_u' >? res_u))
                  (andb nsw (negb (Z.shiftr (unsigned x)
                                            (bz - unsigned y)
                                   =? (unsigned (negative res))
                                      * (Z.pow 2 (unsigned y) - 1))%Z))
           then ret (DVALUE_Poison (DTYPE_I (N.of_nat bitwidth))) else ret (to_dvalue res)

    | UDiv ex =>
      if (unsigned y =? 0)%Z
      then raise_ub "Unsigned division by 0."
      else if andb ex (negb ((unsigned x) mod (unsigned y) =? 0))%Z
           then ret (DVALUE_Poison (DTYPE_I (N.of_nat bitwidth)))
           else ret (to_dvalue (divu x y))


    | SDiv ex =>
      (* What does signed i1 mean? *)
      if (signed y =? 0)%Z
      then raise_ub "Signed division by 0."
      else if andb ex (negb ((signed x) mod (signed y) =? 0))%Z
           then ret (DVALUE_Poison (DTYPE_I (N.of_nat bitwidth)))
           else ret (to_dvalue (divs x y))

    | LShr ex =>
      let bz := Z.of_nat bitwidth in
      if (unsigned y) >=? bz then ret (DVALUE_Poison (DTYPE_I (N.of_nat bitwidth)))
      else if andb ex (negb ((unsigned x)
                               mod (Z.pow 2 (unsigned y)) =? 0))%Z
           then ret (DVALUE_Poison (DTYPE_I (N.of_nat bitwidth))) else ret (to_dvalue (shru x y))

    | AShr ex =>
      let bz := Z.of_nat bitwidth in
      if (unsigned y) >=? bz then ret (DVALUE_Poison (DTYPE_I (N.of_nat bitwidth)))
      else if andb ex (negb ((unsigned x)
                               mod (Z.pow 2 (unsigned y)) =? 0))%Z
           then ret (DVALUE_Poison (DTYPE_I (N.of_nat bitwidth))) else ret (to_dvalue (shr x y))

    | URem =>
      if (unsigned y =? 0)%Z
      then raise_ub "Unsigned mod 0."
      else ret (to_dvalue (modu x y))

    | SRem =>
      if (signed y =? 0)%Z
      then raise_ub "Signed mod 0."
      else ret (to_dvalue (mods x y))

    | And =>
      ret (to_dvalue (and x y))

    | Or =>
      ret (to_dvalue (or x y))

    | Xor =>
      ret (to_dvalue (xor x y))
    end.
  Arguments eval_int_op _ _ _ : simpl nomatch.

  (* Evaluate the given iop on the given arguments according to the bitsize *)
  Definition integer_op (bits:N) (iop:ibinop) (x y:inttyp bits) : err_or_ub dvalue :=
    match bits, x, y with
    | 1, x, y  => lift (eval_int_op iop x y)
    | 8, x, y  => lift (eval_int_op iop x y)
    | 32, x, y => lift (eval_int_op iop x y)
    | 64, x, y => lift (eval_int_op iop x y)
    | _, _, _  => raise_error "unsupported bitsize"
    end.
  Arguments integer_op _ _ _ _ : simpl nomatch.

  (* Convert written integer constant to corresponding integer with bitsize bits.
     Takes the integer modulo 2^bits. *)
  Definition coerce_integer_to_int (bits:N) (i:Z) : err_or_ub dvalue :=
    match bits with
    | 1  => ret (DVALUE_I1 (repr i))
    | 8  => ret (DVALUE_I8 (repr i))
    | 32 => ret (DVALUE_I32 (repr i))
    | 64 => ret (DVALUE_I64 (repr i))
    | _  => raise_error "unsupported integer size"
    end.
  Arguments coerce_integer_to_int _ _ : simpl nomatch.

  (* Helper for looping 2 argument evaluation over vectors, producing a vector *)

  Definition vec_loop {A : Type} {M : Type -> Type} `{Monad M}
             (f : A -> A -> M A)
             (elts : list (A * A)) : M (list A) :=
    monad_fold_right (fun acc '(e1, e2) =>
                        val <- f e1 e2 ;;
                        ret (val :: acc)
                     ) elts [].


  (* Integer iop evaluation, called from eval_iop.
     Here the values must be integers. Helper defined
     in order to prevent eval_iop from being recursive. *)
  Definition eval_iop_integer_h iop v1 v2 : err_or_ub dvalue :=
    match v1, v2 with
    | DVALUE_I1 i1, DVALUE_I1 i2    => lift (eval_int_op iop i1 i2)
    | DVALUE_I8 i1, DVALUE_I8 i2    => lift (eval_int_op iop i1 i2)
    | DVALUE_I32 i1, DVALUE_I32 i2  => lift (eval_int_op iop i1 i2)
    | DVALUE_I64 i1, DVALUE_I64 i2  => lift (eval_int_op iop i1 i2)
    | DVALUE_Poison t, _              => lift (ret (DVALUE_Poison t))
    | _, DVALUE_Poison t              =>
      if iop_is_div iop
      then raise_ub "Division by poison."
      else ret (DVALUE_Poison t)
    | _, _                          => raise_error "ill_typed-iop"
    end.
  Arguments eval_iop_integer_h _ _ _ : simpl nomatch.

  (* I split the definition between the vector and other evaluations because
     otherwise eval_iop should be recursive to allow for vector calculations,
     but coq can't find a fixpoint. *)
  (* Here is where we want to add the case distinction  for uvalues

       - this should check for "determined" uvalues and then use eval_iop_integer_h
         otherwise leave the op symbolic

       - this should use the inclusion of dvalue into uvalue in the case that
         eval_iop_integer_h is calle

   *)

  Definition eval_iop iop v1 v2 : err_or_ub dvalue :=
    match v1, v2 with
    | (DVALUE_Vector elts1), (DVALUE_Vector elts2) =>
      val <- vec_loop (eval_iop_integer_h iop) (List.combine elts1 elts2) ;;
      ret (DVALUE_Vector val)
    | _, _ => eval_iop_integer_h iop v1 v2
    end.
  Arguments eval_iop _ _ _ : simpl nomatch.

  Definition eval_int_icmp {Int} `{VInt Int} icmp (x y : Int) : dvalue :=
    if match icmp with
       | Eq => cmp Ceq x y
       | Ne => cmp Cne x y
       | Ugt => cmpu Cgt x y
       | Uge => cmpu Cge x y
       | Ult => cmpu Clt x y
       | Ule => cmpu Cle x y
       | Sgt => cmp Cgt x y
       | Sge => cmp Cge x y
       | Slt => cmp Clt x y
       | Sle => cmp Cle x y
       end
    then DVALUE_I1 (Int1.one) else DVALUE_I1 (Int1.zero).
  Arguments eval_int_icmp _ _ _ : simpl nomatch.

  Definition eval_icmp icmp v1 v2 : err_or_ub dvalue :=
    match v1, v2 with
    | DVALUE_I1 i1, DVALUE_I1 i2 => ret (eval_int_icmp icmp i1 i2)
    | DVALUE_I8 i1, DVALUE_I8 i2 => ret (eval_int_icmp icmp i1 i2)
    | DVALUE_I32 i1, DVALUE_I32 i2 => ret (eval_int_icmp icmp i1 i2)
    | DVALUE_I64 i1, DVALUE_I64 i2 => ret (eval_int_icmp icmp i1 i2)
    | DVALUE_Poison t1, DVALUE_Poison t2 => ret (DVALUE_Poison t1)
    | DVALUE_Poison t, _ => if is_DVALUE_IX v2 then ret (DVALUE_Poison t) else raise_error "ill_typed-iop"
    | _, DVALUE_Poison t => if is_DVALUE_IX v1 then ret (DVALUE_Poison t) else raise_error "ill_typed-iop"
    | DVALUE_Addr a1, DVALUE_Addr a2 =>
      match icmp with
      | Eq => if A.eq_dec a1 a2 then ret (DVALUE_I1 (Int1.one)) else ret (DVALUE_I1 (Int1.zero))
      | Ne => if A.eq_dec a1 a2 then ret (DVALUE_I1 (Int1.zero)) else ret (DVALUE_I1 (Int1.one))
      | _ => raise_error "non-equality pointer comparison"
      end
    | _, _ => raise_error "ill_typed-icmp"
    end.
  Arguments eval_icmp _ _ _ : simpl nomatch.

  Definition double_op (fop:fbinop) (v1:ll_double) (v2:ll_double) : err_or_ub dvalue :=
    match fop with
    | FAdd => ret (DVALUE_Double (b64_plus FT_Rounding v1 v2))
    | FSub => ret (DVALUE_Double (b64_minus FT_Rounding v1 v2))
    | FMul => ret (DVALUE_Double (b64_mult FT_Rounding v1 v2))
    | FDiv => if (Float.eq_dec v2 Float.zero)
              then raise_ub "Signed division by 0."
              else ret (DVALUE_Double (b64_div FT_Rounding v1 v2))
    | FRem => raise_error "unimplemented double operation"
    end.

  Definition float_op (fop:fbinop) (v1:ll_float) (v2:ll_float) : err_or_ub dvalue :=
    match fop with
    | FAdd => ret (DVALUE_Float (b32_plus FT_Rounding v1 v2))
    | FSub => ret (DVALUE_Float (b32_minus FT_Rounding v1 v2))
    | FMul => ret (DVALUE_Float (b32_mult FT_Rounding v1 v2))
    | FDiv => if (Float32.eq_dec v2 Float32.zero)
              then raise_ub "Signed division by 0."
              else ret (DVALUE_Float (b32_div FT_Rounding v1 v2))
    | FRem => raise_error "unimplemented float operation"
    end.

  Definition eval_fop (fop:fbinop) (v1:dvalue) (v2:dvalue) : err_or_ub dvalue :=
    match v1, v2 with
    | DVALUE_Float f1, DVALUE_Float f2   => float_op fop f1 f2
    | DVALUE_Double d1, DVALUE_Double d2 => double_op fop d1 d2
    | DVALUE_Poison t, _                 => ret (DVALUE_Poison t)
    | _, DVALUE_Poison t                 =>
      if fop_is_div fop
      then raise_ub "Division by poison."
      else ret (DVALUE_Poison t)
    | _, _                               => raise_error ("ill_typed-fop: " ++ (to_string fop) ++ " " ++ (to_string v1) ++ " " ++ (to_string v2))
    end.

  Definition not_nan32 (f:ll_float) : bool :=
    negb (Flocq.IEEE754.Binary.is_nan _ _ f).

  Definition ordered32 (f1 f2:ll_float) : bool :=
    andb (not_nan32 f1) (not_nan32 f2).

  Definition not_nan64 (f:ll_double) : bool :=
    negb (Flocq.IEEE754.Binary.is_nan _ _ f).

  Definition ordered64 (f1 f2:ll_double) : bool :=
    andb (not_nan64 f1) (not_nan64 f2).

  Definition float_cmp (fcmp:fcmp) (x:ll_float) (y:ll_float) : dvalue :=
    if match fcmp with
       | FFalse => false
       | FOeq => andb (ordered32 x y) (Float32.cmp Ceq x y)
       | FOgt => andb (ordered32 x y) (Float32.cmp Cgt x y)
       | FOge => andb (ordered32 x y) (Float32.cmp Cge x y)
       | FOlt => andb (ordered32 x y) (Float32.cmp Clt x y)
       | FOle => andb (ordered32 x y) (Float32.cmp Cle x y)
       | FOne => andb (ordered32 x y) (Float32.cmp Cne x y)
       | FOrd => ordered32 x y
       | FUno => negb (ordered32 x y)
       | FUeq => (Float32.cmp Ceq x y)
       | FUgt => (Float32.cmp Cgt x y)
       | FUge => (Float32.cmp Cge x y)
       | FUlt => (Float32.cmp Clt x y)
       | FUle => (Float32.cmp Cle x y)
       | FUne => (Float32.cmp Cne x y)
       | FTrue => true
       end
    then DVALUE_I1 Int1.one else DVALUE_I1 Int1.zero.
  Arguments float_cmp _ _ _ : simpl nomatch.

  Definition double_cmp (fcmp:fcmp) (x:ll_double) (y:ll_double) : dvalue :=
    if match fcmp with
       | FFalse => false
       | FOeq => andb (ordered64 x y) (Float.cmp Ceq x y)
       | FOgt => andb (ordered64 x y) (Float.cmp Cgt x y)
       | FOge => andb (ordered64 x y) (Float.cmp Cge x y)
       | FOlt => andb (ordered64 x y) (Float.cmp Clt x y)
       | FOle => andb (ordered64 x y) (Float.cmp Cle x y)
       | FOne => andb (ordered64 x y) (Float.cmp Cne x y)
       | FOrd => ordered64 x y
       | FUno => negb (ordered64 x y)
       | FUeq => (Float.cmp Ceq x y)
       | FUgt => (Float.cmp Cgt x y)
       | FUge => (Float.cmp Cge x y)
       | FUlt => (Float.cmp Clt x y)
       | FUle => (Float.cmp Cle x y)
       | FUne => (Float.cmp Cne x y)
       | FTrue => true
       end
    then DVALUE_I1 Int1.one else DVALUE_I1 Int1.zero.
    Arguments double_cmp _ _ _ : simpl nomatch.

  Definition eval_fcmp (fcmp:fcmp) (v1:dvalue) (v2:dvalue) : err_or_ub dvalue :=
    match v1, v2 with
    | DVALUE_Float f1, DVALUE_Float f2 => ret (float_cmp fcmp f1 f2)
    | DVALUE_Double f1, DVALUE_Double f2 => ret (double_cmp fcmp f1 f2)
    | DVALUE_Poison t1, DVALUE_Poison t2 => ret (DVALUE_Poison t1)
    | DVALUE_Poison t, DVALUE_Double _ => ret (DVALUE_Poison t)
    | DVALUE_Poison t, DVALUE_Float _ => ret (DVALUE_Poison t)
    | DVALUE_Double _, DVALUE_Poison t => ret (DVALUE_Poison t)
    | DVALUE_Float _, DVALUE_Poison t => ret (DVALUE_Poison t)
    | _, _ => raise_error "ill_typed-fcmp"
    end.

  Set Printing Implicit.
  Print eval_fcmp.

  End ARITHMETIC.

  (* Same deal as above with the helper *)
  (* The pattern matching generates hundreds of subgoals, hence the factorization of the typeclass inference *)
  Definition eval_select_h (cnd : dvalue) (v1 v2 : uvalue) : err_or_ub (uvalue) :=
    let raise_error_local :=
        @raise_error err_or_ub
                     (@VErrorM_MonadExc err_or_ub
                                        (@Exception_eitherT ERR_MESSAGE UB (Monad_either UB_MESSAGE))) uvalue
    in
    let ret_local := @ret err_or_ub _ uvalue in
    match v1, v2 with
    | UVALUE_Poison t, _ => ret_local (UVALUE_Poison t)
    | _, UVALUE_Poison t => ret_local (UVALUE_Poison t)
    | _, _ =>
      match cnd with
      | DVALUE_I1 i =>
        ret_local (if (Int1.unsigned i =? 1)%Z then v1 else v2)
      | DVALUE_Poison t => ret_local (UVALUE_Poison t)
      | _ => raise_error_local "ill_typed select"
      end
    end.

  Definition eval_select cnd v1 v2 : err_or_ub (uvalue) :=
    match cnd, v1, v2 with
    | (DVALUE_Vector es), (UVALUE_Vector es1), (UVALUE_Vector es2) =>
      (* vec needs to loop over es, es1, and es2. Is there a way to
         generalize vec_loop to cover this? (make v1,v2 generic?) *)
      let fix loop elts :=
          match elts with
          | [] => ret []
          | (cnd,(v1,v2)) :: tl =>
              val <- eval_select_h cnd v1 v2 ;;
              vec <- loop tl ;;
              ret (val :: vec)
          end in
      val <- loop (List.combine es (List.combine es1 es2)) ;;
      ret (UVALUE_Vector val)
    | _, _, _ => eval_select_h cnd v1 v2
    end.
  Arguments eval_select _ _ _ : simpl nomatch.

  (* Helper function for indexing into a structured datatype
     for extractvalue and insertvalue *)
  Definition index_into_str (v:uvalue) (idx:LLVMAst.int) : err_or_ub (uvalue) :=
    let fix loop elts i :=
        match elts with
        | [] => raise_error "index out of bounds"
        | h :: tl =>
          if (idx =? 0)%Z then ret h else loop tl (i-1)%Z
        end in
    match v with
    | UVALUE_Struct f => loop f idx
    | UVALUE_Packed_struct f => loop f idx
    | UVALUE_Array e => loop e idx
    | _ => raise_error "invalid aggregate data"
    end.
  Arguments index_into_str _ _ : simpl nomatch.

  (* Helper function for indexing into a structured datatype
     for extractvalue and insertvalue *)
  Definition index_into_str_dv (v:dvalue) (idx:LLVMAst.int) : err_or_ub (dvalue) :=
    let fix loop elts i :=
        match elts with
        | [] => raise_error "index out of bounds"
        | h :: tl =>
          if (idx =? 0)%Z then ret h else loop tl (i-1)%Z
        end in
    match v with
    | DVALUE_Struct f => loop f idx
    | DVALUE_Packed_struct f => loop f idx
    | DVALUE_Array e => loop e idx
    | _ => raise_error "invalid aggregate data"
    end.
  Arguments index_into_str_dv _ _ : simpl nomatch.

  (* Helper function for inserting into a structured datatype for insertvalue *)
  Definition insert_into_str (str:dvalue) (v:dvalue) (idx:LLVMAst.int) : err_or_ub dvalue :=
    let fix loop (acc elts:list dvalue) (i:LLVMAst.int) :=
        match elts with
        | [] => raise_error "index out of bounds"
        | h :: tl =>
          (if idx =? 0 then ret (acc ++ (v :: tl))
          else loop (acc ++ [h]) tl (i-1))%Z
        end%list in
    match str with
    | DVALUE_Struct f =>
      v <- (loop [] f idx) ;;
      ret (DVALUE_Struct v)

    | DVALUE_Array e =>
      v <- (loop [] e idx) ;;
      ret (DVALUE_Array v)

    | _ => raise_error "invalid aggregate data"
    end.
  Arguments insert_into_str _ _ _ : simpl nomatch.

(*  ------------------------------------------------------------------------- *)

  (* Interpretation of [uvalue] in terms of sets of [dvalue].
     Essentially used to implemenmt the handler for [pick], but also requuired to
     define some predicates passed as arguments to the [pick] events, hence why
     it's defined here.
   *)

  (* TODO: Move this *)
  Require Import Lia.
  Program Fixpoint NO_VOID (dt : dtyp) {measure (dtyp_measure dt)} : Prop
    := match dt with
       | DTYPE_I _
       | DTYPE_IPTR
       | DTYPE_Pointer
       | DTYPE_Half
       | DTYPE_Float
       | DTYPE_Double
       | DTYPE_X86_fp80
       | DTYPE_Fp128
       | DTYPE_Ppc_fp128
       | DTYPE_Metadata
       | DTYPE_X86_mmx
       | DTYPE_Opaque =>
         True
       | DTYPE_Void => False
       | DTYPE_Vector sz t
       | DTYPE_Array sz t =>
         NO_VOID t
       | DTYPE_Struct dts
       | DTYPE_Packed_struct dts =>
         Forall_HIn dts (fun dt HIn => @NO_VOID dt _)
       end.
  Next Obligation.
    cbn.
    lia.
  Defined.
  Next Obligation.
    cbn.
    lia.
  Defined.
  Next Obligation.
    cbn.
    pose proof (list_sum_map dtyp_measure dt dts HIn).
    lia.
  Defined.
  Next Obligation.
    cbn.
    pose proof (list_sum_map dtyp_measure dt dts HIn).
    lia.
  Defined.

  Lemma NO_VOID_equation :
    forall (dt : dtyp),
      NO_VOID dt = match dt with
                   | DTYPE_I _
                   | DTYPE_IPTR
                   | DTYPE_Pointer
                   | DTYPE_Half
                   | DTYPE_Float
                   | DTYPE_Double
                   | DTYPE_X86_fp80
                   | DTYPE_Fp128
                   | DTYPE_Ppc_fp128
                   | DTYPE_Metadata
                   | DTYPE_X86_mmx
                   | DTYPE_Opaque =>
                     True
                   | DTYPE_Void => False
                   | DTYPE_Vector sz t
                   | DTYPE_Array sz t =>
                     NO_VOID t
                   | DTYPE_Struct dts
                   | DTYPE_Packed_struct dts =>
                     Forall_HIn dts (fun dt HIn => NO_VOID dt)
                   end.
  Proof.
  Admitted.

  Lemma NO_VOID_Struct_fields :
    forall dts,
      NO_VOID (DTYPE_Struct dts) ->
      (forall dt, In dt dts -> NO_VOID dt).
  Proof.
    intros dts NV dt IN.
    rewrite NO_VOID_equation in NV.
    induction dts.
    - contradiction.
    - inversion IN; subst.
      + apply NV.
      + apply IHdts; auto.
        eapply Forall_HIn_cons; eauto.
  Qed.

  Lemma NO_VOID_Packed_struct_fields :
    forall dts,
      NO_VOID (DTYPE_Packed_struct dts) ->
      (forall dt, In dt dts -> NO_VOID dt).
  Proof.
    intros dts NV dt IN.
    rewrite NO_VOID_equation in NV.
    induction dts.
    - contradiction.
    - inversion IN; subst.
      + apply NV.
      + apply IHdts; auto.
        eapply Forall_HIn_cons; eauto.
  Qed.

  Lemma NO_VOID_Struct_cons :
    forall dt dts,
      NO_VOID (DTYPE_Struct (dt :: dts)) ->
      NO_VOID (DTYPE_Struct dts).
  Proof.
    intros dt dts H.
    rewrite NO_VOID_equation.
    rewrite NO_VOID_equation in H.
    eapply Forall_HIn_cons; eauto.
  Qed.

  Lemma NO_VOID_Packed_struct_cons :
    forall dt dts,
      NO_VOID (DTYPE_Packed_struct (dt :: dts)) ->
      NO_VOID (DTYPE_Packed_struct dts).
  Proof.
    intros dt dts H.
    rewrite NO_VOID_equation.
    rewrite NO_VOID_equation in H.
    eapply Forall_HIn_cons; eauto.
  Qed.

  Lemma NO_VOID_dec :
    forall dt,
      {NO_VOID dt} + {~NO_VOID dt}.
  Proof.
    intros dt.
    induction dt.  
    all:
      try match goal with
          | NV : {NO_VOID _} + {~ NO_VOID _} |- _ =>
            destruct NV
          end;
      try rewrite NO_VOID_equation;
      try solve [left; cbn; auto | right; cbn; auto].

    all: apply Forall_HIn_dec; auto.
  Qed.

  Lemma NO_VOID_neq_dtyp :
    forall dt1 dt2,
      NO_VOID dt1 ->
      ~ NO_VOID dt2 ->
      dt1 <> dt2.
  Proof.
    intros dt1 dt2 NV NNV.
    intros EQ.
    induction dt1, dt2; inversion EQ.
    all: rewrite NO_VOID_equation in NNV; try contradiction.

    all: inversion EQ; subst;
      rewrite NO_VOID_equation in NV;
      contradiction.
  Qed.

  (* Poison not included because of concretize *)
  Unset Elimination Schemes.
  Inductive dvalue_has_dtyp : dvalue -> dtyp -> Prop :=
  | DVALUE_Addr_typ   : forall a, dvalue_has_dtyp (DVALUE_Addr a) DTYPE_Pointer
  | DVALUE_I1_typ     : forall x, dvalue_has_dtyp (DVALUE_I1 x) (DTYPE_I 1)
  | DVALUE_I8_typ     : forall x, dvalue_has_dtyp (DVALUE_I8 x) (DTYPE_I 8)
  | DVALUE_I32_typ    : forall x, dvalue_has_dtyp (DVALUE_I32 x) (DTYPE_I 32)
  | DVALUE_I64_typ    : forall x, dvalue_has_dtyp (DVALUE_I64 x) (DTYPE_I 64)
  | DVALUE_IPTR_typ   : forall x, dvalue_has_dtyp (DVALUE_IPTR x) DTYPE_IPTR
  | DVALUE_Double_typ : forall x, dvalue_has_dtyp (DVALUE_Double x) DTYPE_Double
  | DVALUE_Float_typ  : forall x, dvalue_has_dtyp (DVALUE_Float x) DTYPE_Float
  | DVALUE_None_typ   : dvalue_has_dtyp DVALUE_None DTYPE_Void
  | DVALUE_Poison_typ  : forall τ, dvalue_has_dtyp (DVALUE_Poison τ) τ

  | DVALUE_Struct_Nil_typ  : dvalue_has_dtyp (DVALUE_Struct []) (DTYPE_Struct [])
  | DVALUE_Struct_Cons_typ :
      forall f dt fields dts,
        dvalue_has_dtyp f dt ->
        dvalue_has_dtyp (DVALUE_Struct fields) (DTYPE_Struct dts) ->
        dvalue_has_dtyp (DVALUE_Struct (f :: fields)) (DTYPE_Struct (dt :: dts))

  | DVALUE_Packed_struct_Nil_typ  : dvalue_has_dtyp (DVALUE_Packed_struct []) (DTYPE_Packed_struct [])
  | DVALUE_Packed_struct_Cons_typ :
      forall f dt fields dts,
        dvalue_has_dtyp f dt ->
        dvalue_has_dtyp (DVALUE_Packed_struct fields) (DTYPE_Packed_struct dts) ->
        dvalue_has_dtyp (DVALUE_Packed_struct (f :: fields)) (DTYPE_Packed_struct (dt :: dts))

  (* Do we have to exclude mmx? "There are no arrays, vectors or constants of this type" *)
  | DVALUE_Array_typ :
      forall xs sz dt,
        Forall (fun x => dvalue_has_dtyp x dt) xs ->
        length xs = sz ->
        dvalue_has_dtyp (DVALUE_Array xs) (DTYPE_Array (N.of_nat sz) dt)

  | DVALUE_Vector_typ :
      forall xs sz dt,
        Forall (fun x => dvalue_has_dtyp x dt) xs ->
        length xs = sz ->
        vector_dtyp dt ->
        dvalue_has_dtyp (DVALUE_Vector xs) (DTYPE_Vector (N.of_nat sz) dt)
  .
  Set Elimination Schemes.

  Unset Elimination Schemes.
  Inductive uvalue_has_dtyp : uvalue -> dtyp -> Prop :=
  | UVALUE_Addr_typ   : forall a, uvalue_has_dtyp (UVALUE_Addr a) DTYPE_Pointer
  | UVALUE_I1_typ     : forall x, uvalue_has_dtyp (UVALUE_I1 x) (DTYPE_I 1)
  | UVALUE_I8_typ     : forall x, uvalue_has_dtyp (UVALUE_I8 x) (DTYPE_I 8)
  | UVALUE_I32_typ    : forall x, uvalue_has_dtyp (UVALUE_I32 x) (DTYPE_I 32)
  | UVALUE_I64_typ    : forall x, uvalue_has_dtyp (UVALUE_I64 x) (DTYPE_I 64)
  | UVALUE_IPTR_typ    : forall x, uvalue_has_dtyp (UVALUE_IPTR x) (DTYPE_IPTR)
  | UVALUE_Double_typ : forall x, uvalue_has_dtyp (UVALUE_Double x) DTYPE_Double
  | UVALUE_Float_typ  : forall x, uvalue_has_dtyp (UVALUE_Float x) DTYPE_Float
  | UVALUE_None_typ   : uvalue_has_dtyp UVALUE_None DTYPE_Void
  | UVALUE_Poison_typ  : forall τ, uvalue_has_dtyp (UVALUE_Poison τ) τ
  | UVALUE_Undef_typ  : forall τ, NO_VOID τ -> uvalue_has_dtyp (UVALUE_Undef τ) τ

  | UVALUE_Struct_Nil_typ  : uvalue_has_dtyp (UVALUE_Struct []) (DTYPE_Struct [])
  | UVALUE_Struct_Cons_typ :
      forall f dt fields dts,
        uvalue_has_dtyp f dt ->
        uvalue_has_dtyp (UVALUE_Struct fields) (DTYPE_Struct dts) ->
        uvalue_has_dtyp (UVALUE_Struct (f :: fields)) (DTYPE_Struct (dt :: dts))

  | UVALUE_Packed_struct_Nil_typ  : uvalue_has_dtyp (UVALUE_Packed_struct []) (DTYPE_Packed_struct [])
  | UVALUE_Packed_struct_Cons_typ :
      forall f dt fields dts,
        uvalue_has_dtyp f dt ->
        uvalue_has_dtyp (UVALUE_Packed_struct fields) (DTYPE_Packed_struct dts) ->
        uvalue_has_dtyp (UVALUE_Packed_struct (f :: fields)) (DTYPE_Packed_struct (dt :: dts))

  (* Do we have to exclude mmx? "There are no arrays, vectors or constants of this type" *)
  | UVALUE_Array_typ :
      forall xs sz dt,
        Forall (fun x => uvalue_has_dtyp x dt) xs ->
        length xs = sz ->
        uvalue_has_dtyp (UVALUE_Array xs) (DTYPE_Array (N.of_nat sz) dt)

  | UVALUE_Vector_typ :
      forall xs sz dt,
        Forall (fun x => uvalue_has_dtyp x dt) xs ->
        length xs = sz ->
        vector_dtyp dt ->
        uvalue_has_dtyp (UVALUE_Vector xs) (DTYPE_Vector (N.of_nat sz) dt)

  | UVALUE_IBinop_typ :
      forall x y sz op,
      IX_supported sz ->
      uvalue_has_dtyp x (DTYPE_I sz) ->
      uvalue_has_dtyp y (DTYPE_I sz) ->
      uvalue_has_dtyp (UVALUE_IBinop op x y) (DTYPE_I sz)
  | UVALUE_IBinop_ptr_typ :
      forall x y op,
      uvalue_has_dtyp x DTYPE_IPTR ->
      uvalue_has_dtyp y DTYPE_IPTR ->
      uvalue_has_dtyp (UVALUE_IBinop op x y) DTYPE_IPTR
  | UVALUE_ICmp_typ :
      forall x y sz op,
      IX_supported sz ->
      uvalue_has_dtyp x (DTYPE_I sz) ->
      uvalue_has_dtyp y (DTYPE_I sz) ->
      uvalue_has_dtyp (UVALUE_ICmp op x y) (DTYPE_I 1)
  | UVALUE_ICmp_pointer_typ :
      forall x y op,
      uvalue_has_dtyp x DTYPE_Pointer ->
      uvalue_has_dtyp y DTYPE_Pointer ->
      uvalue_has_dtyp (UVALUE_ICmp op x y) (DTYPE_I 1)
  | UVALUE_ICmp_vector_typ :
      forall x y vsz isz op,
      IX_supported isz ->
      uvalue_has_dtyp x (DTYPE_Vector vsz (DTYPE_I isz)) ->
      uvalue_has_dtyp y (DTYPE_Vector vsz (DTYPE_I isz)) ->
      uvalue_has_dtyp (UVALUE_ICmp op x y) (DTYPE_Vector vsz (DTYPE_I 1))
  | UVALUE_ICmp_vector_typ_ptr :
      forall x y vsz isz op,
      IX_supported isz ->
      uvalue_has_dtyp x (DTYPE_Vector vsz DTYPE_IPTR) ->
      uvalue_has_dtyp y (DTYPE_Vector vsz DTYPE_IPTR) ->
      uvalue_has_dtyp (UVALUE_ICmp op x y) (DTYPE_Vector vsz (DTYPE_I 1))
  | UVALUE_ICmp_vector_pointer_typ :
      forall x y vsz op,
      uvalue_has_dtyp x (DTYPE_Vector vsz DTYPE_Pointer) ->
      uvalue_has_dtyp y (DTYPE_Vector vsz DTYPE_Pointer) ->
      uvalue_has_dtyp (UVALUE_ICmp op x y) (DTYPE_Vector vsz (DTYPE_I 1))
  | UVALUE_FBinop_Float_typ :
      forall x y op fms,
      uvalue_has_dtyp x DTYPE_Float ->
      uvalue_has_dtyp y DTYPE_Float ->
      uvalue_has_dtyp (UVALUE_FBinop op fms x y) DTYPE_Float
  | UVALUE_FBinop_Double_typ :
      forall x y op fms,
      uvalue_has_dtyp x DTYPE_Double ->
      uvalue_has_dtyp y DTYPE_Double ->
      uvalue_has_dtyp (UVALUE_FBinop op fms x y) DTYPE_Double
  | UVALUE_FCmp_Float_typ :
      forall x y op,
        uvalue_has_dtyp x DTYPE_Float ->
        uvalue_has_dtyp y DTYPE_Float ->
        uvalue_has_dtyp (UVALUE_FCmp op x y) (DTYPE_I 1)
  | UVALUE_FCmp_Double_typ :
      forall x y op,
        uvalue_has_dtyp x DTYPE_Double ->
        uvalue_has_dtyp y DTYPE_Double ->
        uvalue_has_dtyp (UVALUE_FCmp op x y) (DTYPE_I 1)
  | UVALUE_Conversion_trunc_int_typ :
      forall from_sz to_sz value,
        from_sz > to_sz ->
        uvalue_has_dtyp value (DTYPE_I from_sz) ->
        uvalue_has_dtyp (UVALUE_Conversion Trunc (DTYPE_I from_sz) value (DTYPE_I to_sz)) (DTYPE_I to_sz)
  | UVALUE_Conversion_trunc_int_ptr_typ :
      forall to_sz value,
        uvalue_has_dtyp value (DTYPE_IPTR) ->
        uvalue_has_dtyp (UVALUE_Conversion Trunc DTYPE_IPTR value (DTYPE_I to_sz)) (DTYPE_I to_sz)
  | UVALUE_Conversion_trunc_vec_typ :
      forall from_sz to_sz n value,
        from_sz > to_sz ->
        uvalue_has_dtyp value (DTYPE_Vector n (DTYPE_I from_sz)) ->
        uvalue_has_dtyp (UVALUE_Conversion Trunc (DTYPE_Vector n (DTYPE_I from_sz)) value (DTYPE_Vector n (DTYPE_I to_sz))) (DTYPE_Vector n (DTYPE_I to_sz))
  | UVALUE_Conversion_trunc_vec_ptr_typ :
      forall to_sz n value,
        uvalue_has_dtyp value (DTYPE_Vector n DTYPE_IPTR) ->
        uvalue_has_dtyp (UVALUE_Conversion Trunc (DTYPE_Vector n DTYPE_IPTR) value (DTYPE_Vector n (DTYPE_I to_sz))) (DTYPE_Vector n (DTYPE_I to_sz))

  | UVALUE_Conversion_zext_int_typ :
      forall from_sz to_sz value,
        from_sz < to_sz ->
        uvalue_has_dtyp value (DTYPE_I from_sz) ->
        uvalue_has_dtyp (UVALUE_Conversion Zext (DTYPE_I from_sz) value (DTYPE_I to_sz)) (DTYPE_I to_sz)
  | UVALUE_Conversion_zext_int_ptr_typ :
      forall from_sz value,
        uvalue_has_dtyp value (DTYPE_I from_sz) ->
        uvalue_has_dtyp (UVALUE_Conversion Zext (DTYPE_I from_sz) value DTYPE_IPTR) DTYPE_IPTR
  | UVALUE_Conversion_zext_vec_typ :
      forall from_sz to_sz n value,
        from_sz < to_sz ->
        uvalue_has_dtyp value (DTYPE_Vector n (DTYPE_I from_sz)) ->
        uvalue_has_dtyp (UVALUE_Conversion Zext (DTYPE_Vector n (DTYPE_I from_sz)) value (DTYPE_Vector n (DTYPE_I to_sz))) (DTYPE_Vector n (DTYPE_I to_sz))
  | UVALUE_Conversion_zext_vec_ptr_typ :
      forall from_sz n value,
        uvalue_has_dtyp value (DTYPE_Vector n (DTYPE_I from_sz)) ->
        uvalue_has_dtyp (UVALUE_Conversion Zext (DTYPE_Vector n (DTYPE_I from_sz)) value (DTYPE_Vector n DTYPE_IPTR)) (DTYPE_Vector n DTYPE_IPTR)


  | UVALUE_Conversion_sext_int_typ :
      forall from_sz to_sz value,
        from_sz < to_sz ->
        uvalue_has_dtyp value (DTYPE_I from_sz) ->
        uvalue_has_dtyp (UVALUE_Conversion Sext (DTYPE_I from_sz) value (DTYPE_I to_sz)) (DTYPE_I to_sz)
  | UVALUE_Conversion_sext_int_ptr_typ :
      forall from_sz value,
        uvalue_has_dtyp value (DTYPE_I from_sz) ->
        uvalue_has_dtyp (UVALUE_Conversion Sext (DTYPE_I from_sz) value DTYPE_IPTR) DTYPE_IPTR
  | UVALUE_Conversion_sext_vec_typ :
      forall from_sz to_sz n value,
        from_sz < to_sz ->
        uvalue_has_dtyp value (DTYPE_Vector n (DTYPE_I from_sz)) ->
        uvalue_has_dtyp (UVALUE_Conversion Sext (DTYPE_Vector n (DTYPE_I from_sz)) value (DTYPE_Vector n (DTYPE_I to_sz))) (DTYPE_Vector n (DTYPE_I to_sz))
  | UVALUE_Conversion_sext_vec_ptr_typ :
      forall from_sz n value,
        uvalue_has_dtyp value (DTYPE_Vector n (DTYPE_I from_sz)) ->
        uvalue_has_dtyp (UVALUE_Conversion Sext (DTYPE_Vector n (DTYPE_I from_sz)) value (DTYPE_Vector n DTYPE_IPTR)) (DTYPE_Vector n DTYPE_IPTR)

  | UVALUE_GetElementPtr_typ :
      forall dt uv idxs,
        uvalue_has_dtyp (UVALUE_GetElementPtr dt uv idxs) DTYPE_Pointer
  | UVALUE_ExtractElement_typ :
      forall n vect idx t sz,
        IX_supported sz ->
        uvalue_has_dtyp idx (DTYPE_I sz) ->
        uvalue_has_dtyp vect (DTYPE_Vector (N.of_nat n) t) ->
        uvalue_has_dtyp (UVALUE_ExtractElement vect idx) t
  | UVALUE_ExtractElement_ptr_typ :
      forall n vect idx t,
        uvalue_has_dtyp idx DTYPE_IPTR ->
        uvalue_has_dtyp vect (DTYPE_Vector (N.of_nat n) t) ->
        uvalue_has_dtyp (UVALUE_ExtractElement vect idx) t
  | UVALUE_InsertElement_typ :
      forall n vect val idx t sz,
        IX_supported sz ->
        uvalue_has_dtyp idx (DTYPE_I sz) ->
        uvalue_has_dtyp vect (DTYPE_Vector (N.of_nat n) t) ->
        uvalue_has_dtyp val t ->
        uvalue_has_dtyp (UVALUE_InsertElement vect val idx) (DTYPE_Vector (N.of_nat n) t)
  | UVALUE_InsertElement_ptr_typ :
      forall n vect val idx t,
        uvalue_has_dtyp idx DTYPE_IPTR ->
        uvalue_has_dtyp vect (DTYPE_Vector (N.of_nat n) t) ->
        uvalue_has_dtyp val t ->
        uvalue_has_dtyp (UVALUE_InsertElement vect val idx) (DTYPE_Vector (N.of_nat n) t)
  | UVALUE_ShuffleVector_typ :
      forall n m v1 v2 idxs t,
        uvalue_has_dtyp idxs (DTYPE_Vector (N.of_nat m) (DTYPE_I 32)) ->
        uvalue_has_dtyp v1 (DTYPE_Vector (N.of_nat n) t) ->
        uvalue_has_dtyp v2 (DTYPE_Vector (N.of_nat n) t) ->
        uvalue_has_dtyp (UVALUE_ShuffleVector v1 v2 idxs) (DTYPE_Vector (N.of_nat m) t)
  | UVALUE_ExtractValue_Struct_sing_typ :
      forall fields fts dt (idx : LLVMAst.int),
        uvalue_has_dtyp (UVALUE_Struct fields) (DTYPE_Struct fts) ->
        (0 <= idx)%Z ->
        Nth fts (Z.to_nat idx) dt ->
        uvalue_has_dtyp (UVALUE_ExtractValue (UVALUE_Struct fields) [idx]) dt
  | UVALUE_ExtractValue_Struct_cons_typ :
      forall fields fts fld ft dt idx idxs,
        uvalue_has_dtyp (UVALUE_Struct fields) (DTYPE_Struct fts) ->
        (0 <= idx)%Z ->
        Nth fts (Z.to_nat idx) dt ->
        Nth fields (Z.to_nat idx) fld ->
        uvalue_has_dtyp fld ft ->
        uvalue_has_dtyp (UVALUE_ExtractValue fld idxs) dt ->
        uvalue_has_dtyp (UVALUE_ExtractValue (UVALUE_Struct fields) (idx :: idxs)) dt
  | UVALUE_ExtractValue_Packed_struct_sing_typ :
      forall fields fts dt idx,
        uvalue_has_dtyp (UVALUE_Packed_struct fields) (DTYPE_Packed_struct fts) ->
        (0 <= idx)%Z ->
        Nth fts (Z.to_nat idx) dt ->
        uvalue_has_dtyp (UVALUE_ExtractValue (UVALUE_Packed_struct fields) [idx]) dt
  | UVALUE_ExtractValue_Packed_struct_cons_typ :
      forall fields fts fld ft dt idx idxs,
        uvalue_has_dtyp (UVALUE_Packed_struct fields) (DTYPE_Packed_struct fts) ->
        (0 <= idx)%Z ->
        Nth fts (Z.to_nat idx) dt ->
        Nth fields (Z.to_nat idx) fld ->
        uvalue_has_dtyp fld ft ->
        uvalue_has_dtyp (UVALUE_ExtractValue fld idxs) dt ->
        uvalue_has_dtyp (UVALUE_ExtractValue (UVALUE_Packed_struct fields) (idx :: idxs)) dt
  | UVALUE_ExtractValue_Array_sing_typ :
      forall elements dt idx n,
        uvalue_has_dtyp (UVALUE_Array elements) (DTYPE_Array n dt) ->
        (0 <= idx <= Z.of_N n)%Z ->
        uvalue_has_dtyp (UVALUE_ExtractValue (UVALUE_Array elements) [idx]) dt
  | UVALUE_ExtractValue_Array_cons_typ :
      forall elements elem et dt n idx idxs,
        uvalue_has_dtyp (UVALUE_Array elements) (DTYPE_Array n dt) ->
        (0 <= idx <= Z.of_N n)%Z ->
        Nth elements (Z.to_nat idx) elem ->
        uvalue_has_dtyp elem et ->
        uvalue_has_dtyp (UVALUE_ExtractValue elem idxs) dt ->
        uvalue_has_dtyp (UVALUE_ExtractValue (UVALUE_Array elements) (idx :: idxs)) dt
  | UVALUE_InsertValue_typ :
      forall struc idxs uv st dt,
        uvalue_has_dtyp (UVALUE_ExtractValue struc idxs) dt ->
        uvalue_has_dtyp uv dt ->
        uvalue_has_dtyp struc st ->
        uvalue_has_dtyp (UVALUE_InsertValue struc uv idxs) st
  | UVALUE_Select_i1 :
      forall cond x y t,
        uvalue_has_dtyp cond (DTYPE_I 1) ->
        uvalue_has_dtyp x t ->
        uvalue_has_dtyp y t ->
        uvalue_has_dtyp (UVALUE_Select cond x y) t
  | UVALUE_Select_vect :
      forall cond x y t sz,
        uvalue_has_dtyp cond (DTYPE_Vector (N.of_nat sz) (DTYPE_I 1)) ->
        uvalue_has_dtyp x (DTYPE_Vector (N.of_nat sz) t) ->
        uvalue_has_dtyp y (DTYPE_Vector (N.of_nat sz) t) ->
        uvalue_has_dtyp (UVALUE_Select cond x y) (DTYPE_Vector (N.of_nat sz) t)
  (* Maybe ExtractByte just doesn't have a type because no values should be raw ExtractByte values... *)
  (* | UVALUE_ExtractByte_typ : *)
  (*     forall uv dt idx sid, *)
  (*       uvalue_has_dtyp (UVALUE_ExtractByte uv dt idx sid) (DTYPE_I 8) *)
  | UVALUE_ConcatBytes_typ :
      forall bytes dt,
        (forall byte, In byte bytes -> exists uv dt idx sid, byte = UVALUE_ExtractByte uv dt idx sid) ->
        N.of_nat (length bytes) = sizeof_dtyp dt ->
        uvalue_has_dtyp (UVALUE_ConcatBytes bytes dt) dt.
  Set Elimination Schemes.

  Section dvalue_has_dtyp_ind.
    Variable P : dvalue -> dtyp -> Prop.
    Hypothesis IH_Addr           : forall a, P (DVALUE_Addr a) DTYPE_Pointer.
    Hypothesis IH_I1             : forall x, P (DVALUE_I1 x) (DTYPE_I 1).
    Hypothesis IH_I8             : forall x, P (DVALUE_I8 x) (DTYPE_I 8).
    Hypothesis IH_I32            : forall x, P (DVALUE_I32 x) (DTYPE_I 32).
    Hypothesis IH_I64            : forall x, P (DVALUE_I64 x) (DTYPE_I 64).
    Hypothesis IH_IPTR           : forall x, P (DVALUE_IPTR x) DTYPE_IPTR.
    Hypothesis IH_Poison         : forall t, P (DVALUE_Poison t) t.
    Hypothesis IH_Double         : forall x, P (DVALUE_Double x) DTYPE_Double.
    Hypothesis IH_Float          : forall x, P (DVALUE_Float x) DTYPE_Float.
    Hypothesis IH_None           : P DVALUE_None DTYPE_Void.
    Hypothesis IH_Struct_nil     : P (DVALUE_Struct []) (DTYPE_Struct []).
    Hypothesis IH_Struct_cons    : forall (f : dvalue) (dt : dtyp) (fields : list dvalue) (dts : list dtyp),
        dvalue_has_dtyp f dt ->
        P f dt ->
        dvalue_has_dtyp (DVALUE_Struct fields) (DTYPE_Struct dts) ->
        P (DVALUE_Struct fields) (DTYPE_Struct dts) ->
        P (DVALUE_Struct (f :: fields)) (DTYPE_Struct (dt :: dts)).
    Hypothesis IH_Packed_Struct_nil     : P (DVALUE_Packed_struct []) (DTYPE_Packed_struct []).
    Hypothesis IH_Packed_Struct_cons    : forall (f : dvalue) (dt : dtyp) (fields : list dvalue) (dts : list dtyp),
        dvalue_has_dtyp f dt ->
        P f dt ->
        dvalue_has_dtyp (DVALUE_Packed_struct fields) (DTYPE_Packed_struct dts) ->
        P (DVALUE_Packed_struct fields) (DTYPE_Packed_struct dts) ->
        P (DVALUE_Packed_struct (f :: fields)) (DTYPE_Packed_struct (dt :: dts)).
    Hypothesis IH_Array : forall (xs : list dvalue) (sz : nat) (dt : dtyp)
                            (IH : forall x, In x xs -> P x dt)
                            (IHdtyp : forall x, In x xs -> dvalue_has_dtyp x dt),
        Datatypes.length xs = sz -> P (DVALUE_Array xs) (DTYPE_Array (N.of_nat sz) dt).

    Hypothesis IH_Vector : forall (xs : list dvalue) (sz : nat) (dt : dtyp)
                             (IH : forall x, In x xs -> P x dt)
                             (IHdtyp : forall x, In x xs -> dvalue_has_dtyp x dt),
        Datatypes.length xs = sz ->
        vector_dtyp dt -> P (DVALUE_Vector xs) (DTYPE_Vector (N.of_nat sz) dt).

    Lemma dvalue_has_dtyp_ind : forall (dv:dvalue) (dt:dtyp) (TYP: dvalue_has_dtyp dv dt), P dv dt.
      fix IH 3.
      intros dv dt TYP.
      destruct TYP;
        try (solve [let IH := fresh in
                    remember (forall (dv : dvalue) (dt : dtyp), dvalue_has_dtyp dv dt -> P dv dt) as IH;
                    match goal with
                    | H: _ |- _ =>
                      solve [eapply H; subst IH; eauto]
                    end]).
      - rename H into Hforall.
        rename H0 into Hlen.
        refine (IH_Array _ _ Hlen).

        { generalize dependent sz.
          generalize dependent xs.
          fix IHxs 2.
          intros xs Hforall sz Hlen x H.
          destruct xs.
          + inversion H.
          + inversion H; subst.
            * inversion Hforall; subst; auto.
            * eapply IHxs. inversion Hforall; subst.
              all: try eassumption. reflexivity.
        }

        apply Forall_forall; auto.
      - rename H into Hforall.
        rename H0 into Hlen.
        rename H1 into Hvect.
        refine (IH_Vector _ _ Hlen Hvect).

        { generalize dependent sz.
          generalize dependent xs.
          fix IHxs 2.
          intros xs Hforall sz Hlen x H.
          destruct xs.
          + inversion H.
          + inversion H; subst.
            * inversion Hforall; subst; auto.
            * eapply IHxs. inversion Hforall; subst.
              all: try eassumption. reflexivity.
        }

        apply Forall_forall; auto.
    Qed.
  End dvalue_has_dtyp_ind.

  Section uvalue_has_dtyp_ind.
    Variable P : uvalue -> dtyp -> Prop.
    Hypothesis IH_Addr           : forall a, P (UVALUE_Addr a) DTYPE_Pointer.
    Hypothesis IH_I1             : forall x, P (UVALUE_I1 x) (DTYPE_I 1).
    Hypothesis IH_I8             : forall x, P (UVALUE_I8 x) (DTYPE_I 8).
    Hypothesis IH_I32            : forall x, P (UVALUE_I32 x) (DTYPE_I 32).
    Hypothesis IH_I64            : forall x, P (UVALUE_I64 x) (DTYPE_I 64).
    Hypothesis IH_IPTR           : forall x, P (UVALUE_IPTR x) DTYPE_IPTR.
    Hypothesis IH_Poison         : forall t, P (UVALUE_Poison t) t.

    Hypothesis IH_Undef_Array    : forall sz t
                                     (NV: NO_VOID t)
                                     (IH: P (UVALUE_Undef t) t),
        P (UVALUE_Undef (DTYPE_Array sz t)) (DTYPE_Array sz t).
    Hypothesis IH_Undef_Vector    : forall sz t
                                     (NV: NO_VOID t)
                                     (IH: P (UVALUE_Undef t) t),
        P (UVALUE_Undef (DTYPE_Vector sz t)) (DTYPE_Vector sz t).

    Hypothesis IH_Undef_Struct_nil    :
        P (UVALUE_Undef (DTYPE_Struct [])) (DTYPE_Struct []).

    Hypothesis IH_Undef_Struct_cons    : forall dt dts,
        P (UVALUE_Undef dt) dt ->
        P (UVALUE_Undef (DTYPE_Struct dts)) (DTYPE_Struct dts) ->
        P (UVALUE_Undef (DTYPE_Struct (dt :: dts))) (DTYPE_Struct (dt :: dts)).

    Hypothesis IH_Undef_Packed_struct_nil    :
        P (UVALUE_Undef (DTYPE_Packed_struct [])) (DTYPE_Packed_struct []).

    Hypothesis IH_Undef_Packed_struct_cons    : forall dt dts,
        P (UVALUE_Undef dt) dt ->
        P (UVALUE_Undef (DTYPE_Packed_struct dts)) (DTYPE_Packed_struct dts) ->
        P (UVALUE_Undef (DTYPE_Packed_struct (dt :: dts))) (DTYPE_Packed_struct (dt :: dts)).

    Hypothesis IH_Undef          : forall t, (NO_VOID t /\ (forall dts, t <> DTYPE_Struct dts) /\ (forall dts, t <> DTYPE_Packed_struct dts) /\ (forall sz et, t <> DTYPE_Array sz et) /\ (forall sz et, t <> DTYPE_Vector sz et)) -> P (UVALUE_Undef t) t
.
    Hypothesis IH_Double         : forall x, P (UVALUE_Double x) DTYPE_Double.
    Hypothesis IH_Float          : forall x, P (UVALUE_Float x) DTYPE_Float.
    Hypothesis IH_None           : P UVALUE_None DTYPE_Void.
    Hypothesis IH_Struct_nil     : P (UVALUE_Struct []) (DTYPE_Struct []).
    Hypothesis IH_Struct_cons    : forall (f : uvalue) (dt : dtyp) (fields : list uvalue) (dts : list dtyp),
        uvalue_has_dtyp f dt ->
        P f dt ->
        uvalue_has_dtyp (UVALUE_Struct fields) (DTYPE_Struct dts) ->
        P (UVALUE_Struct fields) (DTYPE_Struct dts) ->
        P (UVALUE_Struct (f :: fields)) (DTYPE_Struct (dt :: dts)).
    Hypothesis IH_Packed_Struct_nil     : P (UVALUE_Packed_struct []) (DTYPE_Packed_struct []).
    Hypothesis IH_Packed_Struct_cons    : forall (f : uvalue) (dt : dtyp) (fields : list uvalue) (dts : list dtyp),
        uvalue_has_dtyp f dt ->
        P f dt ->
        uvalue_has_dtyp (UVALUE_Packed_struct fields) (DTYPE_Packed_struct dts) ->
        P (UVALUE_Packed_struct fields) (DTYPE_Packed_struct dts) ->
        P (UVALUE_Packed_struct (f :: fields)) (DTYPE_Packed_struct (dt :: dts)).
    Hypothesis IH_Array : forall (xs : list uvalue) (sz : nat) (dt : dtyp)
                            (IH : forall x, In x xs -> P x dt)
                            (IHdtyp : forall x, In x xs -> uvalue_has_dtyp x dt),
        Datatypes.length xs = sz -> P (UVALUE_Array xs) (DTYPE_Array (N.of_nat sz) dt).

    Hypothesis IH_Vector : forall (xs : list uvalue) (sz : nat) (dt : dtyp)
                             (IH : forall x, In x xs -> P x dt)
                             (IHdtyp : forall x, In x xs -> uvalue_has_dtyp x dt),
        Datatypes.length xs = sz ->
        vector_dtyp dt -> P (UVALUE_Vector xs) (DTYPE_Vector (N.of_nat sz) dt).

    Hypothesis IH_IBinop : forall (x y : uvalue) (sz : N) (op : ibinop),
        IX_supported sz ->
        uvalue_has_dtyp x (DTYPE_I sz) ->
        P x (DTYPE_I sz) ->
        uvalue_has_dtyp y (DTYPE_I sz) ->
        P y (DTYPE_I sz) ->
        P (UVALUE_IBinop op x y) (DTYPE_I sz).

    Hypothesis IH_IBinop_ptr : forall (x y : uvalue) (op : ibinop),
        uvalue_has_dtyp x DTYPE_IPTR ->
        P x DTYPE_IPTR ->
        uvalue_has_dtyp y DTYPE_IPTR ->
        P y DTYPE_IPTR ->
        P (UVALUE_IBinop op x y) DTYPE_IPTR.

    Hypothesis IH_ICmp : forall (x y : uvalue) (sz : N) (op : icmp),
        IX_supported sz ->
        uvalue_has_dtyp x (DTYPE_I sz) ->
        P x (DTYPE_I sz) ->
        uvalue_has_dtyp y (DTYPE_I sz) ->
        P y (DTYPE_I sz) ->
        P (UVALUE_ICmp op x y) (DTYPE_I 1).

    Hypothesis IH_ICmp_ptr : forall (x y : uvalue) (op : icmp),
        uvalue_has_dtyp x DTYPE_IPTR ->
        P x DTYPE_IPTR ->
        uvalue_has_dtyp y DTYPE_IPTR ->
        P y DTYPE_IPTR ->
        P (UVALUE_ICmp op x y) (DTYPE_I 1).

    Hypothesis IH_ICmp_pointer : forall (x y : uvalue) (op : icmp),
        uvalue_has_dtyp x DTYPE_Pointer ->
        P x DTYPE_Pointer ->
        uvalue_has_dtyp y DTYPE_Pointer ->
        P y DTYPE_Pointer ->
        P (UVALUE_ICmp op x y) (DTYPE_I 1).

    Hypothesis IH_ICmp_vector : forall (x y : uvalue) (vsz isz : N) (op : icmp),
        IX_supported isz ->
        uvalue_has_dtyp x (DTYPE_Vector vsz (DTYPE_I isz)) ->
        P x (DTYPE_Vector vsz (DTYPE_I isz)) ->
        uvalue_has_dtyp y (DTYPE_Vector vsz (DTYPE_I isz)) ->
        P y (DTYPE_Vector vsz (DTYPE_I isz)) ->
        P (UVALUE_ICmp op x y) (DTYPE_Vector vsz (DTYPE_I 1)).

    Hypothesis IH_ICmp_vector_ptr : forall (x y : uvalue) (vsz : N) (op : icmp),
        uvalue_has_dtyp x (DTYPE_Vector vsz DTYPE_IPTR) ->
        P x (DTYPE_Vector vsz DTYPE_IPTR) ->
        uvalue_has_dtyp y (DTYPE_Vector vsz DTYPE_IPTR) ->
        P y (DTYPE_Vector vsz DTYPE_IPTR) ->
        P (UVALUE_ICmp op x y) (DTYPE_Vector vsz (DTYPE_I 1)).

    Hypothesis IH_ICmp_vector_pointer : forall (x y : uvalue) (vsz : N) (op : icmp),
        uvalue_has_dtyp x (DTYPE_Vector vsz DTYPE_Pointer) ->
        P x (DTYPE_Vector vsz DTYPE_Pointer) ->
        uvalue_has_dtyp y (DTYPE_Vector vsz DTYPE_Pointer) ->
        P y (DTYPE_Vector vsz DTYPE_Pointer) ->
        P (UVALUE_ICmp op x y) (DTYPE_Vector vsz (DTYPE_I 1)).

    Hypothesis IH_FBinop_Float : forall (x y : uvalue) (op : fbinop) (fms : list fast_math),
        uvalue_has_dtyp x DTYPE_Float ->
        P x DTYPE_Float ->
        uvalue_has_dtyp y DTYPE_Float ->
        P y DTYPE_Float ->
        P (UVALUE_FBinop op fms x y) DTYPE_Float.

    Hypothesis IH_FBinop_Double : forall (x y : uvalue) (op : fbinop) (fms : list fast_math),
        uvalue_has_dtyp x DTYPE_Double ->
        P x DTYPE_Double ->
        uvalue_has_dtyp y DTYPE_Double ->
        P y DTYPE_Double ->
        P (UVALUE_FBinop op fms x y) DTYPE_Double.

    Hypothesis IH_FCmp_Float : forall (x y : uvalue) (op : fcmp),
        uvalue_has_dtyp x DTYPE_Float ->
        P x DTYPE_Float ->
        uvalue_has_dtyp y DTYPE_Float ->
        P y DTYPE_Float ->
        P (UVALUE_FCmp op x y) (DTYPE_I 1).

    Hypothesis IH_FCmp_Double : forall (x y : uvalue) (op : fcmp),
        uvalue_has_dtyp x DTYPE_Double ->
        P x DTYPE_Double ->
        uvalue_has_dtyp y DTYPE_Double ->
        P y DTYPE_Double ->
        P (UVALUE_FCmp op x y) (DTYPE_I 1).

    Hypothesis IH_Conversion_trunc_int : forall (from_sz to_sz : N) (value : uvalue),
        from_sz > to_sz ->
        uvalue_has_dtyp value (DTYPE_I from_sz) ->
        P value (DTYPE_I from_sz)  ->
        P (UVALUE_Conversion Trunc (DTYPE_I from_sz) value
                             (DTYPE_I to_sz)) (DTYPE_I to_sz).

    Hypothesis IH_Conversion_trunc_int_ptr : forall (to_sz : N) (value : uvalue),
        uvalue_has_dtyp value DTYPE_IPTR ->
        P value DTYPE_IPTR  ->
        P (UVALUE_Conversion Trunc DTYPE_IPTR value
                             (DTYPE_I to_sz)) (DTYPE_I to_sz).

    Hypothesis IH_Conversion_trunc_vec : forall (from_sz to_sz n : N) (value : uvalue),
        from_sz > to_sz ->
        uvalue_has_dtyp value (DTYPE_Vector n (DTYPE_I from_sz)) ->
        P value (DTYPE_Vector n (DTYPE_I from_sz)) ->
        P
          (UVALUE_Conversion Trunc (DTYPE_Vector n (DTYPE_I from_sz))
                             value (DTYPE_Vector n (DTYPE_I to_sz)))
          (DTYPE_Vector n (DTYPE_I to_sz)).

    Hypothesis IH_Conversion_trunc_vec_ptr : forall (to_sz n : N) (value : uvalue),
        uvalue_has_dtyp value (DTYPE_Vector n DTYPE_IPTR) ->
        P value (DTYPE_Vector n DTYPE_IPTR) ->
        P
          (UVALUE_Conversion Trunc (DTYPE_Vector n DTYPE_IPTR)
                             value (DTYPE_Vector n (DTYPE_I to_sz)))
          (DTYPE_Vector n (DTYPE_I to_sz)).

    Hypothesis IH_Conversion_zext_int : forall from_sz to_sz value,
          from_sz < to_sz ->
          uvalue_has_dtyp value (DTYPE_I from_sz) ->
          P value (DTYPE_I from_sz) ->
          P (UVALUE_Conversion Zext (DTYPE_I from_sz) value (DTYPE_I to_sz)) (DTYPE_I to_sz).

    Hypothesis IH_Conversion_zext_int_ptr : forall (from_sz : N) (value : uvalue),
        uvalue_has_dtyp value (DTYPE_I from_sz) ->
        P value (DTYPE_I from_sz) ->
        P
          (UVALUE_Conversion Zext (DTYPE_I from_sz) value DTYPE_IPTR)
          DTYPE_IPTR.

    Hypothesis IH_Conversion_zext_vec : forall (from_sz to_sz n : N) (value : uvalue),
        from_sz < to_sz ->
        uvalue_has_dtyp value (DTYPE_Vector n (DTYPE_I from_sz)) ->
        P value (DTYPE_Vector n (DTYPE_I from_sz)) ->
        P
          (UVALUE_Conversion Zext (DTYPE_Vector n (DTYPE_I from_sz)) value
                             (DTYPE_Vector n (DTYPE_I to_sz)))
          (DTYPE_Vector n (DTYPE_I to_sz)).

    Hypothesis IH_Conversion_zext_vec_ptr : forall (from_sz n : N) (value : uvalue),
        uvalue_has_dtyp value (DTYPE_Vector n (DTYPE_I from_sz)) ->
        P value (DTYPE_Vector n (DTYPE_I from_sz)) ->
        P
          (UVALUE_Conversion Zext (DTYPE_Vector n (DTYPE_I from_sz))
                             value (DTYPE_Vector n DTYPE_IPTR))
          (DTYPE_Vector n DTYPE_IPTR).

    Hypothesis IH_Conversion_sext_int : forall (from_sz to_sz : N) (value : uvalue),
        from_sz < to_sz ->
        uvalue_has_dtyp value (DTYPE_I from_sz) ->
        P value (DTYPE_I from_sz) ->
        P
          (UVALUE_Conversion Sext (DTYPE_I from_sz) value (DTYPE_I to_sz))
          (DTYPE_I to_sz).

    Hypothesis IH_Conversion_sext_int_ptr : forall (from_sz : N) (value : uvalue),
        uvalue_has_dtyp value (DTYPE_I from_sz) ->
        P value (DTYPE_I from_sz) ->
        P
          (UVALUE_Conversion Sext (DTYPE_I from_sz) value DTYPE_IPTR)
          DTYPE_IPTR.

    Hypothesis IH_Conversion_sext_vec : forall (from_sz to_sz n : N) (value : uvalue),
        from_sz < to_sz ->
        uvalue_has_dtyp value (DTYPE_Vector n (DTYPE_I from_sz)) ->
        P value (DTYPE_Vector n (DTYPE_I from_sz)) ->
        P
          (UVALUE_Conversion Sext (DTYPE_Vector n (DTYPE_I from_sz)) value
                             (DTYPE_Vector n (DTYPE_I to_sz)))
          (DTYPE_Vector n (DTYPE_I to_sz)).

    Hypothesis IH_Conversion_sext_vec_ptr : forall (from_sz n : N) (value : uvalue),
        uvalue_has_dtyp value (DTYPE_Vector n (DTYPE_I from_sz)) ->
        P value (DTYPE_Vector n (DTYPE_I from_sz)) ->
        P
          (UVALUE_Conversion Sext (DTYPE_Vector n (DTYPE_I from_sz))
                             value (DTYPE_Vector n DTYPE_IPTR))
          (DTYPE_Vector n DTYPE_IPTR).

    Hypothesis IH_GetElementPtr : forall (dt : dtyp) (uv : uvalue) (idxs : list uvalue),
        P (UVALUE_GetElementPtr dt uv idxs) DTYPE_Pointer.

    Hypothesis IH_ExtractElement : forall (n : nat) (vect idx : uvalue) (t : dtyp) (sz : N),
        IX_supported sz ->
        uvalue_has_dtyp idx (DTYPE_I sz) ->
        P idx (DTYPE_I sz) ->
        uvalue_has_dtyp vect (DTYPE_Vector (N.of_nat n) t) ->
        P vect (DTYPE_Vector (N.of_nat n) t) ->
        P (UVALUE_ExtractElement vect idx) t.

    Hypothesis IH_ExtractElement_ptr : forall (n : nat) (vect idx : uvalue) (t : dtyp),
        uvalue_has_dtyp idx DTYPE_IPTR ->
        P idx DTYPE_IPTR ->
        uvalue_has_dtyp vect (DTYPE_Vector (N.of_nat n) t) ->
        P vect (DTYPE_Vector (N.of_nat n) t) ->
        P (UVALUE_ExtractElement vect idx) t.

    Hypothesis IH_InsertElement : forall (n : nat) (vect val idx : uvalue) (t : dtyp) (sz : N),
        IX_supported sz ->
        uvalue_has_dtyp idx (DTYPE_I sz) ->
        P idx (DTYPE_I sz) ->
        uvalue_has_dtyp vect (DTYPE_Vector (N.of_nat n) t) ->
        P vect (DTYPE_Vector (N.of_nat n) t) ->
        uvalue_has_dtyp val t ->
        P val t ->
        P (UVALUE_InsertElement vect val idx)
          (DTYPE_Vector (N.of_nat n) t).

    Hypothesis IH_InsertElement_ptr : forall (n : nat) (vect val idx : uvalue) (t : dtyp),
        uvalue_has_dtyp idx DTYPE_IPTR ->
        P idx DTYPE_IPTR ->
        uvalue_has_dtyp vect (DTYPE_Vector (N.of_nat n) t) ->
        P vect (DTYPE_Vector (N.of_nat n) t) ->
        uvalue_has_dtyp val t ->
        P val t ->
        P (UVALUE_InsertElement vect val idx)
          (DTYPE_Vector (N.of_nat n) t).

    Hypothesis IH_ShuffleVector : forall (n m : nat) (v1 v2 idxs : uvalue) (t : dtyp),
        uvalue_has_dtyp idxs (DTYPE_Vector (N.of_nat m) (DTYPE_I 32)) ->
        P idxs (DTYPE_Vector (N.of_nat m) (DTYPE_I 32)) ->
        uvalue_has_dtyp v1 (DTYPE_Vector (N.of_nat n) t) ->
        P v1 (DTYPE_Vector (N.of_nat n) t) ->
        uvalue_has_dtyp v2 (DTYPE_Vector (N.of_nat n) t) ->
        P v2 (DTYPE_Vector (N.of_nat n) t) ->
        P (UVALUE_ShuffleVector v1 v2 idxs)
                        (DTYPE_Vector (N.of_nat m) t).

    Hypothesis IH_ExtractValue_Struct_sing : forall (fields : list uvalue) (fts : list dtyp)
                                               (dt : dtyp) (idx : LLVMAst.int),
        uvalue_has_dtyp (UVALUE_Struct fields) (DTYPE_Struct fts) ->
        P (UVALUE_Struct fields) (DTYPE_Struct fts) ->
        (0 <= idx)%Z ->
        Nth fts (Z.to_nat idx) dt ->
        P
          (UVALUE_ExtractValue (UVALUE_Struct fields) [idx]) dt.

    Hypothesis IH_ExtractValue_Struct_cons : forall (fields : list uvalue) (fts : list dtyp)
                                               (fld : uvalue) (ft dt : dtyp) (idx : Z)
                                               (idxs : list LLVMAst.int),
        uvalue_has_dtyp (UVALUE_Struct fields) (DTYPE_Struct fts) ->
        P (UVALUE_Struct fields) (DTYPE_Struct fts) ->
        (0 <= idx)%Z ->
        Nth fts (Z.to_nat idx) dt ->
        Nth fields (Z.to_nat idx) fld ->
        uvalue_has_dtyp fld ft ->
        P fld ft ->
        uvalue_has_dtyp (UVALUE_ExtractValue fld idxs) dt ->
        P (UVALUE_ExtractValue fld idxs) dt ->
        P
          (UVALUE_ExtractValue (UVALUE_Struct fields) (idx :: idxs))
          dt.

    Hypothesis IH_ExtractValue_Packed_struct_sing : forall (fields : list uvalue)
                                                      (fts : list dtyp) (dt : dtyp)
                                                      (idx : Z),
        uvalue_has_dtyp (UVALUE_Packed_struct fields)
                        (DTYPE_Packed_struct fts) ->
        P (UVALUE_Packed_struct fields)
          (DTYPE_Packed_struct fts) ->
        (0 <= idx)%Z ->
        Nth fts (Z.to_nat idx) dt ->
        P
          (UVALUE_ExtractValue (UVALUE_Packed_struct fields)
                               [idx]) dt.

    Hypothesis IH_ExtractValue_Packed_struct_cons : forall (fields : list uvalue)
                                                      (fts : list dtyp) (fld : uvalue)
                                                      (ft dt : dtyp) (idx : Z)
                                                      (idxs : list LLVMAst.int),
        uvalue_has_dtyp (UVALUE_Packed_struct fields)
                        (DTYPE_Packed_struct fts) ->
        P (UVALUE_Packed_struct fields)
                        (DTYPE_Packed_struct fts) ->
        (0 <= idx)%Z ->
        Nth fts (Z.to_nat idx) dt ->
        Nth fields (Z.to_nat idx) fld ->
        uvalue_has_dtyp fld ft ->
        P fld ft ->
        uvalue_has_dtyp (UVALUE_ExtractValue fld idxs) dt ->
        P (UVALUE_ExtractValue fld idxs) dt ->
        P
          (UVALUE_ExtractValue (UVALUE_Packed_struct fields)
                               (idx :: idxs)) dt.

    Hypothesis IH_ExtractValue_Array_sing : forall (elements : list uvalue) (dt : dtyp) (idx : Z) (n : N),
        uvalue_has_dtyp (UVALUE_Array elements) (DTYPE_Array n dt) ->
        P (UVALUE_Array elements) (DTYPE_Array n dt) ->
        (0 <= idx <= Z.of_N n)%Z ->
        P
          (UVALUE_ExtractValue (UVALUE_Array elements) [idx]) dt.

    Hypothesis IH_ExtractValue_Array_cons : forall (elements : list uvalue) (elem : uvalue)
                                              (et dt : dtyp) (n : N) (idx : Z)
                                              (idxs : list LLVMAst.int),
        uvalue_has_dtyp (UVALUE_Array elements) (DTYPE_Array n dt) ->
        P (UVALUE_Array elements) (DTYPE_Array n dt) ->
        (0 <= idx <= Z.of_N n)%Z ->
        Nth elements (Z.to_nat idx) elem ->
        uvalue_has_dtyp elem et ->
        P elem et ->
        uvalue_has_dtyp (UVALUE_ExtractValue elem idxs) dt ->
        P (UVALUE_ExtractValue elem idxs) dt ->
        P
          (UVALUE_ExtractValue (UVALUE_Array elements) (idx :: idxs))
          dt.

    Hypothesis IH_InsertValue : forall (struc : uvalue) (idxs : list LLVMAst.int)
                                  (uv : uvalue) (st dt : dtyp),
        uvalue_has_dtyp (UVALUE_ExtractValue struc idxs) dt ->
        P (UVALUE_ExtractValue struc idxs) dt ->
        uvalue_has_dtyp uv dt ->
        P uv dt ->
        uvalue_has_dtyp struc st ->
        P struc st ->
        P (UVALUE_InsertValue struc uv idxs) st.

    Hypothesis IH_Select_i1 : forall (cond x y : uvalue) (t : dtyp),
        uvalue_has_dtyp cond (DTYPE_I 1) ->
        P cond (DTYPE_I 1) ->
        uvalue_has_dtyp x t ->
        P x t ->
        uvalue_has_dtyp y t ->
        P y t ->
        P (UVALUE_Select cond x y) t.

    Hypothesis IH_Select_vect : forall (cond x y : uvalue) (t : dtyp) (sz : nat),
        uvalue_has_dtyp cond (DTYPE_Vector (N.of_nat sz) (DTYPE_I 1)) ->
        P cond (DTYPE_Vector (N.of_nat sz) (DTYPE_I 1)) ->
        uvalue_has_dtyp x (DTYPE_Vector (N.of_nat sz) t) ->
        P x (DTYPE_Vector (N.of_nat sz) t) ->
        uvalue_has_dtyp y (DTYPE_Vector (N.of_nat sz) t) ->
        P y (DTYPE_Vector (N.of_nat sz) t) ->
        P (UVALUE_Select cond x y) (DTYPE_Vector (N.of_nat sz) t).

    Hypothesis IH_UVALUE_ExtractByte :
      forall uv dt idx sid,
        P (UVALUE_ExtractByte uv dt idx sid) (DTYPE_I 8).

    Hypothesis IH_UVALUE_ConcatBytes :
      forall bytes dt,
        (forall byte, In byte bytes -> exists uv dt idx sid, byte = UVALUE_ExtractByte uv dt idx sid) ->
        N.of_nat (length bytes) = sizeof_dtyp dt ->
        P (UVALUE_ConcatBytes bytes dt) dt.

    Lemma uvalue_has_dtyp_ind : forall (uv:uvalue) (dt:dtyp) (TYP: uvalue_has_dtyp uv dt), P uv dt.
      fix IH 3.
      intros uv dt TYP.
      destruct TYP;
        try (solve [let IH := fresh in
                    remember (forall (uv : uvalue) (dt : dtyp), uvalue_has_dtyp uv dt -> P uv dt) as IH;
                    match goal with
                    | H: _ |- _ =>
                      solve [eapply H; subst IH; eauto]
                    end]).
      - generalize dependent τ.
        fix IHτ 1.
        intros τ NV.
        destruct τ eqn:Hτ; try contradiction;
          try solve [eapply IH_Undef;
                     repeat split; solve [intros * CONTRA; inversion CONTRA]].

        (* Undef Arrays *)
        { pose proof NV as NVd.
          rewrite NO_VOID_equation in NVd.
          apply IH_Undef_Array; auto.
        }

        (* Undef Structs *)
        { pose proof NV as NVfs.
          rewrite NO_VOID_equation in NVfs.
          clear Hτ.
          generalize dependent fields.
          induction fields; intros NV NVfs.
          - apply IH_Undef_Struct_nil.
          - apply IH_Undef_Struct_cons.
            apply IHτ.
            eapply NO_VOID_Struct_fields in NV.
            apply NV.
            left; auto.
            apply IHfields.

            eapply NO_VOID_Struct_cons; eauto.
            eapply Forall_HIn_cons; eauto.
        }

        (* Undef Packed structs *)
        { pose proof NV as NVfs.
          rewrite NO_VOID_equation in NVfs.
          clear Hτ.
          generalize dependent fields.
          induction fields; intros NV NVfs.
          - apply IH_Undef_Packed_struct_nil.
          - apply IH_Undef_Packed_struct_cons.
            apply IHτ.
            eapply NO_VOID_Packed_struct_fields in NV.
            apply NV.
            left; auto.
            apply IHfields.

            eapply NO_VOID_Packed_struct_cons; eauto.
            eapply Forall_HIn_cons; eauto.
        }

        (* Undef Vectors *)
        { pose proof NV as NVd.
          rewrite NO_VOID_equation in NVd.
          apply IH_Undef_Vector; auto.
        }

        Unshelve.
        all: try solve [exact 0%N | exact DTYPE_Void | exact ([] : list dtyp)].

      - (* Arrays *)
        rename H into Hforall.
        rename H0 into Hlen.
        refine (IH_Array _ _ Hlen).

        { generalize dependent sz.
          generalize dependent xs.
          fix IHxs 2.
          intros xs Hforall sz Hlen x H.
          destruct xs.
          + inversion H.
          + inversion H; subst.
            * inversion Hforall; subst; auto.
            * eapply IHxs. inversion Hforall; subst.
              all: try eassumption. reflexivity.
        }

        apply Forall_forall; auto.
      - (* Vectors *)
        rename H into Hforall.
        rename H0 into Hlen.
        rename H1 into Hvect.
        refine (IH_Vector _ _ Hlen Hvect).

        { generalize dependent sz.
          generalize dependent xs.
          fix IHxs 2.
          intros xs Hforall sz Hlen x H.
          destruct xs.
          + inversion H.
          + inversion H; subst.
            * inversion Hforall; subst; auto.
            * eapply IHxs. inversion Hforall; subst.
              all: try eassumption. reflexivity.
        }

        apply Forall_forall; auto.
    Qed.
  End uvalue_has_dtyp_ind.

  Lemma uvalue_has_dtyp_struct_length :
    forall fields dts,
      uvalue_has_dtyp (UVALUE_Struct fields) (DTYPE_Struct dts) ->
      length fields = length dts.
  Proof.
    induction fields;
      intros dts H; inversion H; cbn; auto.
  Qed.

  Lemma uvalue_has_dtyp_packed_struct_length :
    forall fields dts,
      uvalue_has_dtyp (UVALUE_Packed_struct fields) (DTYPE_Packed_struct dts) ->
      length fields = length dts.
  Proof.
    induction fields;
      intros dts H; inversion H; cbn; auto.
  Qed.

  Lemma dvalue_has_dtyp_struct_length :
    forall fields dts,
      dvalue_has_dtyp (DVALUE_Struct fields) (DTYPE_Struct dts) ->
      length fields = length dts.
  Proof.
    induction fields;
      intros dts H; inversion H; cbn; auto.
  Qed.

  Lemma dvalue_has_dtyp_packed_struct_length :
    forall fields dts,
      dvalue_has_dtyp (DVALUE_Packed_struct fields) (DTYPE_Packed_struct dts) ->
      length fields = length dts.
  Proof.
    induction fields;
      intros dts H; inversion H; cbn; auto.
  Qed.

End DVALUE.
