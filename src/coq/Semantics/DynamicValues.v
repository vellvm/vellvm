(* begin hide *)
From Coq Require Import
     Relations
     ZArith
     DecidableClass
     List
     String
     Bool.Bool
     Lia
     Program.Wf.
     
Import BinInt.

Require Import Ceres.Ceres.

Require Import Integers Floats.

From Flocq.IEEE754 Require Import
     Bits
     BinarySingleNaN
     Binary.

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
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Semantics.VellvmIntegers
     Utils.MapMonadExtra
     Utils.MonadEq1Laws
     Utils.MonadReturnsLaws
     QC.ShowAST.

(* TODO: when/if we cut ties to QC, change this import *)
From QuickChick Require Import Show.
Import Monad.
Import EqvNotation.
Import MonadNotation.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

Open Scope N_scope.
(* end hide *)


Definition store_id := N.

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
#[refine]#[local] Instance Decidable_eq_N : forall (x y : N), Decidable (eq x y) := {
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
Module DVALUE(A:Vellvm.Semantics.MemoryAddress.ADDRESS)(IP:Vellvm.Semantics.MemoryAddress.INTPTR)(SIZEOF:Sizeof).

  Import SIZEOF.
  Import IP.

  (* The set of dynamic values manipulated by an LLVM program. *)
  Unset Elimination Schemes.
  Inductive dvalue : Set :=
  | DVALUE_Addr (a:A.addr)
  | DVALUE_I1 (x:int1)
  | DVALUE_I8 (x:int8)
  | DVALUE_I32 (x:int32)
  | DVALUE_I64 (x:int64)
  | DVALUE_IPTR (x:intptr)
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

  Fixpoint show_dvalue (dv : dvalue) : string :=
    match dv with
    | DVALUE_Addr a => "<addr>"
    | DVALUE_I1 x => "i1 " ++ show (Int1.unsigned x)
    | DVALUE_I8 x => "i8 " ++ show (Int8.unsigned x)
    | DVALUE_I32 x => "i32 " ++ show (Int32.unsigned x)
    | DVALUE_I64 x => "i64 " ++ show (Int64.unsigned x)
    | DVALUE_IPTR x => "<intptr>"
    | DVALUE_Double x => "double " ++ show x
    | DVALUE_Float x => "float " ++ show x
    | DVALUE_Poison t => "poison[" ++ show_dtyp t ++ "]"
    | DVALUE_None => "none"
    | DVALUE_Struct fields => "{" ++ String.concat ", " (map show_dvalue fields) ++ "}"
    | DVALUE_Packed_struct fields => "{<" ++ String.concat ", " (map show_dvalue fields) ++ ">}"
    | DVALUE_Array elts => "["  ++ String.concat ", " (map show_dvalue elts) ++ "]"
    | DVALUE_Vector elts => "<"  ++ String.concat ", " (map show_dvalue elts) ++ ">"
    end.

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

  Ltac solve_dvalue_measure :=
    match goal with
    | Hin : In ?e ?fields |- context [dvalue_measure _]
      => pose proof list_sum_map dvalue_measure _ _ Hin;
        cbn; lia
    | H: Some ?f = List.nth_error ?fields _ |- context [dvalue_measure ?f]
      => symmetry in H; apply nth_error_In in H;
        pose proof list_sum_map dvalue_measure _ _ H;
        cbn; lia
    end.

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

  (* The set of dynamic values manipulated by an LLVM program. *)
  Unset Elimination Schemes.
  Inductive uvalue : Type :=
  | UVALUE_Addr (a:A.addr)
  | UVALUE_I1 (x:int1)
  | UVALUE_I8 (x:int8)
  | UVALUE_I32 (x:int32)
  | UVALUE_I64 (x:int64)
  | UVALUE_IPTR (x:intptr)
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
  | UVALUE_ExtractElement   (vec_typ : dtyp) (vec: uvalue) (idx: uvalue)
  | UVALUE_InsertElement    (vec_typ : dtyp) (vec: uvalue) (elt:uvalue) (idx:uvalue)
  | UVALUE_ShuffleVector    (vec1:uvalue) (vec2:uvalue) (idxmask:uvalue)
  | UVALUE_ExtractValue     (vec_typ : dtyp) (vec:uvalue) (idxs:list LLVMAst.int)
  | UVALUE_InsertValue      (vec_typ : dtyp) (vec:uvalue) (elt:uvalue) (idxs:list LLVMAst.int)
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
    | UVALUE_ExtractElement t vec idx =>
        S (uvalue_measure vec + uvalue_measure idx)
    | UVALUE_InsertElement t vec elt idx =>
        S (uvalue_measure vec + uvalue_measure elt + uvalue_measure idx)
    | UVALUE_ShuffleVector vec1 vec2 idxmask =>
        S (uvalue_measure vec1 + uvalue_measure vec2 + uvalue_measure idxmask)
    | UVALUE_ExtractValue t vec idxs =>
        S (uvalue_measure vec)
    | UVALUE_InsertValue t vec elt idxs =>
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

  Ltac solve_dtyp_measure :=
    cbn;
    first [ lia
          | match goal with
            | _ : _ |- context [(dtyp_measure ?t + fold_right _ _ _)%nat]
              => pose proof (dtyp_measure_gt_0 t); unfold list_sum; lia
            end
          | match goal with
            | HIn : In ?x ?xs |- context [ list_sum (map ?f _)] =>
                pose proof (list_sum_map f x xs HIn)
            end;
            cbn in *; lia
      ].

  Ltac solve_uvalue_measure :=
    cbn;
    first [ lia
          | match goal with
            | _ : _ |- context [(uvalue_measure ?t + fold_right _ _ _)%nat]
              => pose proof (uvalue_measure_gt_0 t); unfold list_sum; lia
            end
          | match goal with
            | HIn : In ?x ?xs |- context [ list_sum (map ?f _)] =>
                pose proof (list_sum_map f x xs HIn)
            end;
            cbn in *; lia
      ].

  Ltac solve_uvalue_dtyp_measure :=
    red; cbn;
    repeat match goal with
           | Hin : In _ (repeatN _ _) |- _ =>
               apply In_repeatN in Hin; subst
           end;
    solve [ apply right_lex; solve_dtyp_measure
          | apply left_lex; solve_uvalue_measure
      ].


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
    Hypothesis IH_ExtractElement : forall (t:dtyp) (vec: uvalue) (idx: uvalue), P vec -> P idx -> P (UVALUE_ExtractElement t vec idx).
    Hypothesis IH_InsertElement  : forall (t:dtyp) (vec: uvalue) (elt:uvalue) (idx:uvalue), P vec -> P elt -> P idx -> P (UVALUE_InsertElement t vec elt idx).
    Hypothesis IH_ShuffleVector  : forall (vec1:uvalue) (vec2:uvalue) (idxmask:uvalue), P vec1 -> P vec2 -> P idxmask -> P (UVALUE_ShuffleVector vec1 vec2 idxmask).
    Hypothesis IH_ExtractValue   : forall (t:dtyp) (vec:uvalue) (idxs:list LLVMAst.int), P vec -> P (UVALUE_ExtractValue t vec idxs).
    Hypothesis IH_InsertValue    : forall (t:dtyp) (vec:uvalue) (elt:uvalue) (idxs:list LLVMAst.int), P vec -> P elt -> P (UVALUE_InsertValue t vec elt idxs).
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

  Section UvalueInd'.
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
    Hypothesis IH_Struct_nil     : P (UVALUE_Struct []).
    Hypothesis IH_Struct_cons    : forall uv uvs, P uv -> P (UVALUE_Struct uvs) -> P (UVALUE_Struct (uv :: uvs)).
    Hypothesis IH_Packed_struct_nil     : P (UVALUE_Packed_struct []).
    Hypothesis IH_Packed_struct_cons    : forall uv uvs, P uv -> P (UVALUE_Packed_struct uvs) -> P (UVALUE_Packed_struct (uv :: uvs)).
    Hypothesis IH_Array_nil          : P (UVALUE_Array []).
    Hypothesis IH_Array_cons          : forall uv uvs, P uv -> P (UVALUE_Array uvs) -> P (UVALUE_Array (uv :: uvs)).
    Hypothesis IH_Vector_nil          : P (UVALUE_Vector []).
    Hypothesis IH_Vector_cons          : forall uv uvs, P uv -> P (UVALUE_Vector uvs) -> P (UVALUE_Vector (uv :: uvs)).
    Hypothesis IH_IBinop         : forall (iop:ibinop) (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_IBinop iop v1 v2).
    Hypothesis IH_ICmp           : forall (cmp:icmp)   (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_ICmp cmp v1 v2).
    Hypothesis IH_FBinop         : forall (fop:fbinop) (fm:list fast_math) (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_FBinop fop fm v1 v2).
    Hypothesis IH_FCmp           : forall (cmp:fcmp)   (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_FCmp cmp v1 v2).
    Hypothesis IH_Conversion     : forall (conv:conversion_type) (t_from:dtyp) (v:uvalue) (t_to:dtyp), P v -> P (UVALUE_Conversion conv t_from v t_to).
    Hypothesis IH_GetElementPtr  : forall (t:dtyp) (ptrval:uvalue) (idxs:list (uvalue)), P ptrval -> (forall idx, In idx idxs -> P idx) -> P (UVALUE_GetElementPtr t ptrval idxs).
    Hypothesis IH_ExtractElement : forall (t:dtyp) (vec: uvalue) (idx: uvalue), P vec -> P idx -> P (UVALUE_ExtractElement t vec idx).
    Hypothesis IH_InsertElement  : forall (t:dtyp) (vec: uvalue) (elt:uvalue) (idx:uvalue), P vec -> P elt -> P idx -> P (UVALUE_InsertElement t vec elt idx).
    Hypothesis IH_ShuffleVector  : forall (vec1:uvalue) (vec2:uvalue) (idxmask:uvalue), P vec1 -> P vec2 -> P idxmask -> P (UVALUE_ShuffleVector vec1 vec2 idxmask).
    Hypothesis IH_ExtractValue   : forall (t:dtyp) (vec:uvalue) (idxs:list LLVMAst.int), P vec -> P (UVALUE_ExtractValue t vec idxs).
    Hypothesis IH_InsertValue    : forall (t:dtyp) (vec:uvalue) (elt:uvalue) (idxs:list LLVMAst.int), P vec -> P elt -> P (UVALUE_InsertValue t vec elt idxs).
    Hypothesis IH_Select         : forall (cnd:uvalue) (v1:uvalue) (v2:uvalue), P cnd -> P v1 -> P v2 -> P (UVALUE_Select cnd v1 v2).
    Hypothesis IH_ExtractByte : forall (uv : uvalue) (dt : dtyp) (idx : uvalue) (sid : N), P uv -> P idx -> P (UVALUE_ExtractByte uv dt idx sid).
    Hypothesis IH_ConcatBytes : forall (dt : dtyp) (uvs : list uvalue),
        (forall u, In u uvs -> P u) ->
        P (UVALUE_ConcatBytes uvs dt).

    Lemma uvalue_ind' : forall (uv:uvalue), P uv.
      fix IH 1.
      remember P as P0 in IH.
      destruct uv; auto; subst.
      - revert fields.
        fix IHfields 1. intros [|u' fields']. intros. apply IH_Struct_nil.
        apply IH_Struct_cons.
        apply IH.
        apply IHfields.
      - revert fields.
        fix IHfields 1. intros [|u' fields']. intros. apply IH_Packed_struct_nil.
        apply IH_Packed_struct_cons.
        apply IH.
        apply IHfields.
      - revert elts.
        fix IHelts 1. intros [|u elts']. intros. apply IH_Array_nil.
        apply IH_Array_cons.
        apply IH.
        apply IHelts.
      - revert elts.
        fix IHelts 1. intros [|u elts']. intros. apply IH_Vector_nil.
        apply IH_Vector_cons.
        apply IH.
        apply IHelts.
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
  End UvalueInd'.

  Section UvalueInd''.
    Variable P : uvalue -> Prop.
    Hypothesis IH_Addr           : forall a, P (UVALUE_Addr a).
    Hypothesis IH_I1             : forall x, P (UVALUE_I1 x).
    Hypothesis IH_I8             : forall x, P (UVALUE_I8 x).
    Hypothesis IH_I32            : forall x, P (UVALUE_I32 x).
    Hypothesis IH_I64            : forall x, P (UVALUE_I64 x).
    Hypothesis IH_IPTR            : forall x, P (UVALUE_IPTR x).
    Hypothesis IH_Double         : forall x, P (UVALUE_Double x).
    Hypothesis IH_Float          : forall x, P (UVALUE_Float x).

    (* Undef *)
    Hypothesis IH_Undef_Array    :
      forall sz t
        (IH: P (UVALUE_Undef t)),
        P (UVALUE_Undef (DTYPE_Array sz t)).

    Hypothesis IH_Undef_Vector    :
      forall sz t
        (IH: P (UVALUE_Undef t)),
        P (UVALUE_Undef (DTYPE_Vector sz t)).

    Hypothesis IH_Undef_Struct_nil    :
        P (UVALUE_Undef (DTYPE_Struct [])).

    Hypothesis IH_Undef_Struct_cons    : forall dt dts,
        P (UVALUE_Undef dt) ->
        P (UVALUE_Undef (DTYPE_Struct dts)) ->
        P (UVALUE_Undef (DTYPE_Struct (dt :: dts))).

    Hypothesis IH_Undef_Packed_struct_nil    :
        P (UVALUE_Undef (DTYPE_Packed_struct [])).

    Hypothesis IH_Undef_Packed_struct_cons    : forall dt dts,
        P (UVALUE_Undef dt) ->
        P (UVALUE_Undef (DTYPE_Packed_struct dts)) ->
        P (UVALUE_Undef (DTYPE_Packed_struct (dt :: dts))).

    Hypothesis IH_Undef          : forall t,
        ((forall dts, t <> DTYPE_Struct dts) /\ (forall dts, t <> DTYPE_Packed_struct dts) /\ (forall sz et, t <> DTYPE_Array sz et) /\ (forall sz et, t <> DTYPE_Vector sz et)) ->
        P (UVALUE_Undef t).

    (* Poison *)
    Hypothesis IH_Poison_Array    :
      forall sz t
        (IH: P (UVALUE_Poison t)),
        P (UVALUE_Poison (DTYPE_Array sz t)).

    Hypothesis IH_Poison_Vector    :
      forall sz t
        (IH: P (UVALUE_Poison t)),
        P (UVALUE_Poison (DTYPE_Vector sz t)).

    Hypothesis IH_Poison_Struct_nil    :
        P (UVALUE_Poison (DTYPE_Struct [])).

    Hypothesis IH_Poison_Struct_cons    : forall dt dts,
        P (UVALUE_Poison dt) ->
        P (UVALUE_Poison (DTYPE_Struct dts)) ->
        P (UVALUE_Poison (DTYPE_Struct (dt :: dts))).

    Hypothesis IH_Poison_Packed_struct_nil    :
        P (UVALUE_Poison (DTYPE_Packed_struct [])).

    Hypothesis IH_Poison_Packed_struct_cons    : forall dt dts,
        P (UVALUE_Poison dt) ->
        P (UVALUE_Poison (DTYPE_Packed_struct dts)) ->
        P (UVALUE_Poison (DTYPE_Packed_struct (dt :: dts))).

    Hypothesis IH_Poison          : forall t,
        ((forall dts, t <> DTYPE_Struct dts) /\ (forall dts, t <> DTYPE_Packed_struct dts) /\ (forall sz et, t <> DTYPE_Array sz et) /\ (forall sz et, t <> DTYPE_Vector sz et)) ->
        P (UVALUE_Poison t).

    Hypothesis IH_None           : P UVALUE_None.
    Hypothesis IH_Struct_nil     : P (UVALUE_Struct []).
    Hypothesis IH_Struct_cons    : forall uv uvs, P uv -> P (UVALUE_Struct uvs) -> P (UVALUE_Struct (uv :: uvs)).
    Hypothesis IH_Packed_struct_nil     : P (UVALUE_Packed_struct []).
    Hypothesis IH_Packed_struct_cons    : forall uv uvs, P uv -> P (UVALUE_Packed_struct uvs) -> P (UVALUE_Packed_struct (uv :: uvs)).
    Hypothesis IH_Array          : forall (elts: list uvalue), (forall e, In e elts -> P e) -> P (UVALUE_Array elts).
    Hypothesis IH_Vector         : forall (elts: list uvalue), (forall e, In e elts -> P e) -> P (UVALUE_Vector elts).
    Hypothesis IH_IBinop         : forall (iop:ibinop) (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_IBinop iop v1 v2).
    Hypothesis IH_ICmp           : forall (cmp:icmp)   (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_ICmp cmp v1 v2).
    Hypothesis IH_FBinop         : forall (fop:fbinop) (fm:list fast_math) (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_FBinop fop fm v1 v2).
    Hypothesis IH_FCmp           : forall (cmp:fcmp)   (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_FCmp cmp v1 v2).
    Hypothesis IH_Conversion     : forall (conv:conversion_type) (t_from:dtyp) (v:uvalue) (t_to:dtyp), P v -> P (UVALUE_Conversion conv t_from v t_to).
    Hypothesis IH_GetElementPtr  : forall (t:dtyp) (ptrval:uvalue) (idxs:list (uvalue)), P ptrval -> (forall idx, In idx idxs -> P idx) -> P (UVALUE_GetElementPtr t ptrval idxs).
    Hypothesis IH_ExtractElement : forall (t:dtyp) (vec: uvalue) (idx: uvalue), P vec -> P idx -> P (UVALUE_ExtractElement t vec idx).
    Hypothesis IH_InsertElement  : forall (t:dtyp) (vec: uvalue) (elt:uvalue) (idx:uvalue), P vec -> P elt -> P idx -> P (UVALUE_InsertElement t vec elt idx).
    Hypothesis IH_ShuffleVector  : forall (vec1:uvalue) (vec2:uvalue) (idxmask:uvalue), P vec1 -> P vec2 -> P idxmask -> P (UVALUE_ShuffleVector vec1 vec2 idxmask).
    Hypothesis IH_ExtractValue   : forall (t:dtyp) (vec:uvalue) (idxs:list LLVMAst.int), P vec -> P (UVALUE_ExtractValue t vec idxs).
    Hypothesis IH_InsertValue    : forall (t:dtyp) (vec:uvalue) (elt:uvalue) (idxs:list LLVMAst.int), P vec -> P elt -> P (UVALUE_InsertValue t vec elt idxs).
    Hypothesis IH_Select         : forall (cnd:uvalue) (v1:uvalue) (v2:uvalue), P cnd -> P v1 -> P v2 -> P (UVALUE_Select cnd v1 v2).
    Hypothesis IH_ExtractByte : forall (uv : uvalue) (dt : dtyp) (idx : uvalue) (sid : N), P uv -> P idx -> P (UVALUE_ExtractByte uv dt idx sid).
    Hypothesis IH_ConcatBytes : forall (dt : dtyp) (uvs : list uvalue),
        (forall u, In u uvs -> P u) ->
        P (UVALUE_ConcatBytes uvs dt).

    Lemma uvalue_ind'' : forall (uv:uvalue), P uv.
      fix IH 1.
      remember P as P0 in IH.
      destruct uv; auto; subst.
      - generalize dependent t.
        fix IHτ 1.
        intros τ.
        destruct τ eqn:Hτ; try contradiction;
          try solve [eapply IH_Undef;
                     repeat split; solve [intros * CONTRA; inversion CONTRA]].

        (* Undef Arrays *)
        { apply IH_Undef_Array.
          apply IHτ.
        }

        (* Undef Structs *)
        { clear Hτ.
          generalize dependent fields.
          induction fields.
          - apply IH_Undef_Struct_nil.
          - apply IH_Undef_Struct_cons.
            apply IHτ.
            apply IHfields.
        }

        (* Undef Packed structs *)
        { clear Hτ.
          generalize dependent fields.
          induction fields.
          - apply IH_Undef_Packed_struct_nil.
          - apply IH_Undef_Packed_struct_cons.
            apply IHτ.
            apply IHfields.
        }

        (* Undef Vectors *)
        { apply IH_Undef_Vector.
          apply IHτ.
        }
      - generalize dependent t.
        fix IHτ 1.
        intros τ.
        destruct τ eqn:Hτ; try contradiction;
          try solve [eapply IH_Poison;
                     repeat split; solve [intros * CONTRA; inversion CONTRA]].

        (* Poison Arrays *)
        { apply IH_Poison_Array.
          apply IHτ.
        }

        (* Poison Structs *)
        { clear Hτ.
          generalize dependent fields.
          induction fields.
          - apply IH_Poison_Struct_nil.
          - apply IH_Poison_Struct_cons.
            apply IHτ.
            apply IHfields.
        }

        (* Poison Packed structs *)
        { clear Hτ.
          generalize dependent fields.
          induction fields.
          - apply IH_Poison_Packed_struct_nil.
          - apply IH_Poison_Packed_struct_cons.
            apply IHτ.
            apply IHfields.
        }

        (* Poison Vectors *)
        { apply IH_Poison_Vector.
          apply IHτ.
        }
      - revert fields.
        fix IHfields 1. intros [|u' fields']. intros. apply IH_Struct_nil.
        apply IH_Struct_cons.
        apply IH.
        apply IHfields.
      - revert fields.
        fix IHfields 1. intros [|u' fields']. intros. apply IH_Packed_struct_nil.
        apply IH_Packed_struct_cons.
        apply IH.
        apply IHfields.
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
  End UvalueInd''.


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
      - destruct (IP.eq_dec x1 x2).
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
                | UVALUE_ExtractElement t u v, UVALUE_ExtractElement t' u' v' => _
                | UVALUE_InsertElement t u v x, UVALUE_InsertElement t' u' v' x' => _
                | UVALUE_ShuffleVector u v x, UVALUE_ShuffleVector u' v' x' => _
                | UVALUE_ExtractValue t u l, UVALUE_ExtractValue t' u' l' => _
                | UVALUE_InsertValue t u v l, UVALUE_InsertValue t' u' v' l' => _
                | UVALUE_Select u v w, UVALUE_Select u' v' w' => _
                | UVALUE_ExtractByte uv dt idx sid, UVALUE_ExtractByte uv' dt' idx' sid' => _
                | UVALUE_ConcatBytes uvs dt, UVALUE_ConcatBytes uvs' dt' => _
                | _, _ => _
                end); try (ltac:(dec_dvalue); fail).
      - destruct (A.eq_dec a1 a2)...
      - destruct (Int1.eq_dec x1 x2)...
      - destruct (Int8.eq_dec x1 x2)...
      - destruct (Int32.eq_dec x1 x2)...
      - destruct (Int64.eq_dec x1 x2)...
      - destruct (IP.eq_dec x1 x2)...
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
      - destruct (dtyp_eq_dec t t')...
        destruct (f u u')...
        destruct (f v v')...
      - destruct (dtyp_eq_dec t t')...
        destruct (f u u')...
        destruct (f v v')...
        destruct (f x x')...
      - destruct (f u u')...
        destruct (f v v')...
        destruct (f x x')...
      - destruct (dtyp_eq_dec t t')...
        destruct (f u u')...
        destruct (list_eq_dec Z.eq_dec l l')...
      - destruct (dtyp_eq_dec t t')...
        destruct (f u u')...
        destruct (f v v')...
        destruct (list_eq_dec Z.eq_dec l l')...
      - destruct (f u u')...
        destruct (f v v')...
        destruct (f w w')...
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
      unsigned : I -> Z;
      signed : I -> Z;

      repr : Z -> I;
    }.

  Class ToDvalue I : Type :=
    { to_dvalue : I -> dvalue;
    }.

  #[global] Instance ToDvalue_intptr : ToDvalue intptr :=
    { to_dvalue := DVALUE_IPTR }.

  #[global] Instance VIntVMemInt {I} `{VInt I} : VMemInt I :=
    {
      (* Comparisons *)
      mequ := equ;
      mcmp := cmp;
      mcmpu := cmpu;

      (* Constants *)
      mbitwidth := ret bitwidth;
      mzero := zero;
      mone := one;

      (* Arithmetic *)
      madd := fun x y => ret (add x y);
      madd_carry := add_carry;
      madd_overflow := add_overflow;

      msub := fun x y => ret (sub x y);
      msub_borrow := sub_borrow;
      msub_overflow := sub_overflow;

      mmul := fun x y => ret (mul x y);

      mdivu := divu;
      mdivs := fun x y => ret (divs x y);

      mmodu := modu;
      mmods := fun x y => ret (mods x y);

      mshl := fun x y => ret (shl x y);
      mshr := shr;
      mshru := shru;

      mnegative := fun x => ret (negative x);

      (* Logic *)
      mand := and;
      mor := or;
      mxor := xor;

      (* Bounds, possibly unbounded *)
      mmin_signed := ret (min_signed);
      mmax_signed := ret (max_signed);

      (* Conversion *)
      munsigned := unsigned;
      msigned := signed;

      mrepr := fun x => NoOom (repr x);

      (* dtyp *)
      mdtyp_of_int := DTYPE_I (N.of_nat bitwidth)
    }.

  #[global] Instance VMemInt_intptr' : VMemInt intptr.
  apply VMemInt_intptr.
  Defined.

  #[global] Instance ToDvalue_Int1 : ToDvalue Int1.int :=
    { to_dvalue := DVALUE_I1 }.

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
      unsigned := Int1.unsigned;
      signed := Int1.signed;

      repr := Int1.repr;
    }.

  #[global] Instance ToDvalue_Int8 : ToDvalue Int8.int :=
    { to_dvalue := DVALUE_I8 }.

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
      unsigned := Int8.unsigned;
      signed := Int8.signed;

      repr := Int8.repr;
    }.

  #[global] Instance ToDvalue_Int32 : ToDvalue Int32.int :=
    { to_dvalue := DVALUE_I32 }.

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
    unsigned := Int32.unsigned;
    signed := Int32.signed;

    repr := Int32.repr;
  }.

  #[global] Instance ToDvalue_Int64 : ToDvalue Int64.int :=
    { to_dvalue := DVALUE_I64 }.

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
       | UVALUE_IPTR x => Z.eqb (IP.to_Z x) i
       | _ => false
       end.

  Definition dvalue_int_unsigned (dv : dvalue) : Z
    := match dv with
       | DVALUE_I1 x => unsigned x
       | DVALUE_I8 x => unsigned x
       | DVALUE_I32 x => unsigned x
       | DVALUE_I64 x => unsigned x
       | DVALUE_IPTR x => IP.to_unsigned x
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

  Definition iop_is_signed (iop : ibinop) : bool :=
    match iop with
    | SDiv _ => true
    | SRem   => true
    | _      => false
    end.

  Definition iop_is_shift (iop : ibinop) : bool :=
    match iop with
    | Shl _ _ => true
    | LShr _ => true
    | AShr _ => true
    | _ => false
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

  Definition to_uvalue {Int} `{ToDvalue Int} (i : Int) : uvalue := dvalue_to_uvalue (to_dvalue i).

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
  End CONVERSIONS.

  (* Arithmetic Operations ---------------------------------------------------- *)
  Section ARITHMETIC.

    (* Evaluate integer opererations to get a dvalue.

     These operations are between VInts, which are "vellvm"
     integers. This is a typeclass that wraps all of the integer
     operations that we use for integer types with different bitwidths.

     *)

    Definition to_dvalue_OOM {Int} `{ToDvalue Int} {M} `{Monad M} `{RAISE_OOM M}
               (i : OOM Int) : M dvalue
      := res <- lift_OOM i;;
         ret (to_dvalue res).

    Definition option_pred {A} (pred : A -> bool) (ma : option A) : bool
      := match ma with
         | Some x => pred x
         | None => false
         end.

    Definition eval_int_op {M} {Int} `{Monad M} `{RAISE_UB M} `{RAISE_OOM M} `{VMemInt Int} `{ToDvalue Int} (iop:ibinop) (x y: Int) : M dvalue :=
      match iop with
      (* Following to cases are probably right since they use CompCert *)
      | Add nuw nsw =>
          if orb (andb nuw (mequ (madd_carry x y mzero) mone))
                 (andb nsw (mequ (madd_overflow x y mzero) mone))
          then ret (DVALUE_Poison mdtyp_of_int)
          else to_dvalue_OOM (madd x y)

    | Sub nuw nsw =>
        if orb (andb nuw (mequ (msub_borrow x y mzero) mone))
               (andb nsw (mequ (msub_overflow x y mzero) mone))
        then ret (DVALUE_Poison mdtyp_of_int)
        else to_dvalue_OOM (msub x y)

    | Mul nuw nsw =>
      (* I1 mul can't overflow, just based on the 4 possible multiplications. *)
        if (option_pred (fun bw => Nat.eqb bw 1) mbitwidth)
        then to_dvalue_OOM (mmul x y)
        else
          res <- lift_OOM (mmul x y);;

          let res_u' := ((munsigned x) * (munsigned y))%Z in
          let res_s' := ((msigned x) * (msigned y))%Z in

          let min_s_bound := match fmap (fun m => m >? res_s') mmin_signed with
                             | None => false
                             | Some x => x
                             end in
          let max_s_bound := match fmap (fun m => res_s' >? m) mmax_signed with
                             | None => false
                             | Some x => x
                             end in

          if orb (andb nuw (res_u' >? munsigned res))
                 (andb nsw (orb min_s_bound max_s_bound))
          then ret (DVALUE_Poison mdtyp_of_int)
          else ret (to_dvalue res)

    | Shl nuw nsw =>
      res <- lift_OOM (mshl x y);;
      let res_u := munsigned res in
      let res_u' := Z.shiftl (munsigned x) (munsigned y) in

      (* Unsigned shift x right by bitwidth - y. If shifted x != sign bit * (2^y - 1),
         then there is overflow. *)
      if option_pred (fun bw => munsigned y >=? Z.of_nat bw) mbitwidth
      then ret (DVALUE_Poison mdtyp_of_int)
      else
        if andb nuw (res_u' >? res_u)
        then ret (DVALUE_Poison mdtyp_of_int)
        else
          (* Need to separate this out because mnegative can OOM *)
          if nsw
          then
            match mbitwidth with
            | None =>
                ret (to_dvalue res)
            | Some bw =>
                (* TODO: should this OOM here? *)
                nres <- lift_OOM (mnegative res);;
                if (negb (Z.shiftr (munsigned x)
                                   (Z.of_nat bw - munsigned y)
                          =? (munsigned nres)
                             * (Z.pow 2 (munsigned y) - 1))%Z)
                then ret (DVALUE_Poison mdtyp_of_int)
                else ret (to_dvalue res)
            end
          else ret (to_dvalue res)

    | UDiv ex =>
      if (munsigned y =? 0)%Z
      then raise_ub "Unsigned division by 0."
      else if andb ex (negb ((munsigned x) mod (munsigned y) =? 0))%Z
           then ret (DVALUE_Poison mdtyp_of_int)
           else ret (to_dvalue (mdivu x y))

    | SDiv ex =>
      (* What does signed i1 mean? *)
      if (msigned y =? 0)%Z
      then raise_ub "Signed division by 0."
      else if andb ex (negb ((msigned x) mod (msigned y) =? 0))%Z
           then ret (DVALUE_Poison mdtyp_of_int)
           else to_dvalue_OOM (mdivs x y)

    | LShr ex =>
      if option_pred (fun bw => (munsigned y) >=? Z.of_nat bw) mbitwidth
      then ret (DVALUE_Poison mdtyp_of_int)
      else if andb ex (negb ((munsigned x)
                               mod (Z.pow 2 (munsigned y)) =? 0))%Z
           then ret (DVALUE_Poison mdtyp_of_int) else ret (to_dvalue (mshru x y))

    | AShr ex =>
      if option_pred (fun bw => (munsigned y) >=? Z.of_nat bw) mbitwidth
      then ret (DVALUE_Poison mdtyp_of_int)
      else if andb ex (negb ((munsigned x)
                               mod (Z.pow 2 (munsigned y)) =? 0))%Z
           then ret (DVALUE_Poison mdtyp_of_int) else ret (to_dvalue (mshr x y))

    | URem =>
      if (munsigned y =? 0)%Z
      then raise_ub "Unsigned mod 0."
      else ret (to_dvalue (mmodu x y))

    | SRem =>
      if (msigned y =? 0)%Z
      then raise_ub "Signed mod 0."
      else to_dvalue_OOM (mmods x y)

    | And =>
      ret (to_dvalue (mand x y))

    | Or =>
      ret (to_dvalue (mor x y))

    | Xor =>
      ret (to_dvalue (mxor x y))
    end.
  Arguments eval_int_op _ _ _ : simpl nomatch.

  (* Evaluate the given iop on the given arguments according to the bitsize *)
  Definition integer_op {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M} `{RAISE_OOM M} (bits:N) (iop:ibinop) (x y:inttyp bits) : M dvalue :=
    match bits, x, y with
    | 1, x, y  => eval_int_op iop x y
    | 8, x, y  => eval_int_op iop x y
    | 32, x, y => eval_int_op iop x y
    | 64, x, y => eval_int_op iop x y
    | _, _, _  => raise_error "unsupported bitsize"
    end.
  Arguments integer_op _ _ _ _ : simpl nomatch.

  (* Convert written integer constant to corresponding integer with bitsize bits.
     Takes the integer modulo 2^bits. *)
  Definition coerce_integer_to_int {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M} `{RAISE_OOM M} (bits:option N) (i:Z) : M dvalue :=
    match bits with
    | Some 1  => ret (DVALUE_I1 (repr i))
    | Some 8  => ret (DVALUE_I8 (repr i))
    | Some 32 => ret (DVALUE_I32 (repr i))
    | Some 64 => ret (DVALUE_I64 (repr i))
    | None    =>
        i' <- lift_OOM (mrepr i);;
        ret (DVALUE_IPTR i')
    | _       =>
        raise_error "unsupported integer size"
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
  Definition eval_iop_integer_h {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M} `{RAISE_OOM M} iop v1 v2 : M dvalue :=
    match v1, v2 with
    | DVALUE_I1 i1, DVALUE_I1 i2
    | DVALUE_I8 i1, DVALUE_I8 i2
    | DVALUE_I32 i1, DVALUE_I32 i2
    | DVALUE_I64 i1, DVALUE_I64 i2
    | DVALUE_IPTR i1, DVALUE_IPTR i2 =>
        eval_int_op iop i1 i2
    | DVALUE_Poison t, _             =>
        ret (DVALUE_Poison t)
    | _, DVALUE_Poison t             =>
      if iop_is_div iop
      then raise_ub "Division by poison."
      else ret (DVALUE_Poison t)
    | _, _                           => raise_error "ill_typed-iop"
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

  Definition eval_iop {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M} `{RAISE_OOM M} iop v1 v2 : M dvalue :=
    match v1, v2 with
    | (DVALUE_Vector elts1), (DVALUE_Vector elts2) =>
      val <- vec_loop (eval_iop_integer_h iop) (List.combine elts1 elts2) ;;
      ret (DVALUE_Vector val)
    | _, _ => eval_iop_integer_h iop v1 v2
    end.
  Arguments eval_iop _ _ _ : simpl nomatch.

  Definition eval_int_icmp {Int} `{VMemInt Int} icmp (x y : Int) : dvalue :=
    if match icmp with
       | Eq => mcmp Ceq x y
       | Ne => mcmp Cne x y
       | Ugt => mcmpu Cgt x y
       | Uge => mcmpu Cge x y
       | Ult => mcmpu Clt x y
       | Ule => mcmpu Cle x y
       | Sgt => mcmp Cgt x y
       | Sge => mcmp Cge x y
       | Slt => mcmp Clt x y
       | Sle => mcmp Cle x y
       end
    then DVALUE_I1 (Int1.one) else DVALUE_I1 (Int1.zero).
  Arguments eval_int_icmp _ _ _ : simpl nomatch.

  Definition double_op {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M} (fop:fbinop) (v1:ll_double) (v2:ll_double) : M dvalue :=
    match fop with
    | FAdd => ret (DVALUE_Double (b64_plus FT_Rounding v1 v2))
    | FSub => ret (DVALUE_Double (b64_minus FT_Rounding v1 v2))
    | FMul => ret (DVALUE_Double (b64_mult FT_Rounding v1 v2))
    | FDiv => ret (DVALUE_Double (b64_div FT_Rounding v1 v2))
    | FRem => raise_error "unimplemented double operation"
    end.

  Definition float_op {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M} (fop:fbinop) (v1:ll_float) (v2:ll_float) : M dvalue :=
    match fop with
    | FAdd => ret (DVALUE_Float (b32_plus FT_Rounding v1 v2))
    | FSub => ret (DVALUE_Float (b32_minus FT_Rounding v1 v2))
    | FMul => ret (DVALUE_Float (b32_mult FT_Rounding v1 v2))
    | FDiv => ret (DVALUE_Float (b32_div FT_Rounding v1 v2))
    | FRem => raise_error "unimplemented float operation"
    end.

  Definition eval_fop {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M} (fop:fbinop) (v1:dvalue) (v2:dvalue) : M dvalue :=
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

  Definition eval_fcmp {M} `{Monad M} `{RAISE_ERROR M} (fcmp:fcmp) (v1:dvalue) (v2:dvalue) : M dvalue :=
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

  End ARITHMETIC.

  (* Same deal as above with the helper *)
  (* The pattern matching generates hundreds of subgoals, hence the factorization of the typeclass inference *)
  Definition eval_select_h {M} `{HM: Monad M} `{ERR: RAISE_ERROR M} `{RAISE_UB M} (cnd : dvalue) (v1 v2 : uvalue) : M uvalue :=
    let raise_error_local :=
        @raise_error M
                     ERR uvalue
    in
    let ret_local := @ret M _ uvalue in
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

  Definition eval_select {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M}
             cnd v1 v2 : M (uvalue) :=
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
  Definition index_into_str {M} `{Monad M} `{RAISE_ERROR M} (v:uvalue) (idx:LLVMAst.int) : M uvalue :=
    let fix loop elts i :=
        match elts with
        | [] => raise_error "index_into_str: index out of bounds"
        | h :: tl =>
          if (i =? 0)%Z then ret h else loop tl (i-1)%Z
        end in
    match v with
    | UVALUE_Struct f => loop f idx
    | UVALUE_Packed_struct f => loop f idx
    | UVALUE_Array e => loop e idx
    | _ => raise_error "index_into_str: invalid aggregate data"
    end.
  Arguments index_into_str _ _ : simpl nomatch.

  (* Helper function for indexing into a structured datatype
     for extractvalue and insertvalue *)
  Definition index_into_str_dv {M} `{Monad M} `{RAISE_ERROR M} (v:dvalue) (idx:LLVMAst.int) : M dvalue :=
    let fix loop elts i :=
        match elts with
        | [] => raise_error "index_into_str_dv: index out of bounds"
        | h :: tl =>
          if (i =? 0)%Z then ret h else loop tl (i-1)%Z
        end in
    match v with
    | DVALUE_Struct f => loop f idx
    | DVALUE_Packed_struct f => loop f idx
    | DVALUE_Array e => loop e idx
    | _ => raise_error "index_into_str_dv: invalid aggregate data"
    end.
  Arguments index_into_str_dv _ _ : simpl nomatch.

  (* Helper function for inserting into a structured datatype for insertvalue *)
  Definition insert_into_str {M} `{Monad M} `{RAISE_ERROR M} (str:dvalue) (v:dvalue) (idx:LLVMAst.int) : M dvalue :=
    let fix loop (acc elts:list dvalue) (i:LLVMAst.int) :=
        match elts with
        | [] => raise_error "insert_into_str: index out of bounds"
        | h :: tl =>
          (if i =? 0 then ret (acc ++ (v :: tl))
          else loop (acc ++ [h]) tl (i-1))%Z
        end%list in
    match str with
    | DVALUE_Struct f =>
      v <- (loop [] f idx) ;;
      ret (DVALUE_Struct v)

    | DVALUE_Packed_struct f =>
      v <- (loop [] f idx) ;;
      ret (DVALUE_Packed_struct v)

    | DVALUE_Array e =>
      v <- (loop [] e idx) ;;
      ret (DVALUE_Array v)

    | _ => raise_error "insert_into_str: invalid aggregate data"
    end.
  Arguments insert_into_str _ _ _ : simpl nomatch.

  Definition index_into_vec_dv {M} `{Monad M} `{RAISE_ERROR M} (elt_typ : dtyp) (v:dvalue) (idx:dvalue) : M dvalue :=
    let fix loop dt (elts : list dvalue) i :=
        match elts with
        | [] => ret (DVALUE_Poison dt) (* LangRef: if idx exceeds the length of val for a fixed-length vector, the result is a poison value *)
        | h :: tl =>
          if (i =? 0)%Z then ret h else loop dt tl (i-1)%Z
        end in
    match v with
    | DVALUE_Array e
    | DVALUE_Vector e =>
        match idx with
        | DVALUE_I32 i2
        | DVALUE_I64 i2 =>
            let iZ := signed i2 in
            match iZ with
            | Zneg _ =>
                raise_error "index_into_vec_dv: negative index."
            | _ => loop elt_typ e iZ
            end
        | _ => raise_error "index_into_vec_dv: non-integer dvalue index."
        end
    | _ => raise_error "index_into_vec_dv: not a vector or array."
    end.
  Arguments index_into_vec_dv _ _ : simpl nomatch.

  Definition insert_into_vec_dv {M} `{Monad M} `{RAISE_ERROR M} (vec_typ : dtyp) (vec:dvalue) (v:dvalue) (idx:dvalue) : M dvalue :=
    let fix loop (acc elts:list dvalue) (i:LLVMAst.int) :=
        match elts with
        | [] => None (* LangRef: if idx exceeds the length of val for a fixed-length vector, the result is a poison value *)
        | h :: tl =>
          (if i =? 0 then ret (acc ++ (v :: tl))
          else loop (acc ++ [h]) tl (i-1))%Z
        end%list in
    match vec with
    | DVALUE_Vector e =>
        match idx with
        | DVALUE_I32 i2
        | DVALUE_I64 i2 =>
            let iZ := signed i2 in
            match iZ with
            | Zneg _ =>
                raise_error "insert_into_vec_dv: negative index"
            | _ =>
                match loop [] e iZ with
                | None =>
                    ret (DVALUE_Poison vec_typ)
                | Some elts =>
                    ret (DVALUE_Vector elts)
                end
            end
        | _ =>
            raise_error "insert_into_vec_dv: non-integer dvalue index."
        end
    | DVALUE_Array e =>
        match idx with
        | DVALUE_I32 i2
        | DVALUE_I64 i2 =>
            let iZ := signed i2 in
            match iZ with
            | Zneg _ =>
                raise_error "insert_into_vec_dv: negative index"
            | _ =>
                match loop [] e iZ with
                | None =>
                    ret (DVALUE_Poison vec_typ)
                | Some elts =>
                    ret (DVALUE_Array elts)
                end
            end
        | _ =>
            raise_error "insert_into_vec_dv: non-integer dvalue index."
        end
    | _ => raise_error "insert_into_vec_dv: not a vector or array."
    end.
  Arguments insert_into_vec_dv _ _ _ : simpl nomatch.

(*  ------------------------------------------------------------------------- *)

  (* Interpretation of [uvalue] in terms of sets of [dvalue].
     Essentially used to implemenmt the handler for [pick], but also required to
     define some predicates passed as arguments to the [pick] events, hence why
     it's defined here.
   *)

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

  Lemma Forall_HIn_eq : forall A (l:list A) (f g : forall (x:A), In x l -> Prop),
        (forall x H1 H2, f x H1 = g x H2) ->
        Forall_HIn l f = Forall_HIn l g.
  Proof.
    induction l; intros; simpl; try reflexivity.
    erewrite H. erewrite IHl. reflexivity.
    intros.
    erewrite H. reflexivity.
  Qed.    
  
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
    unfold NO_VOID at 1.
    intros td.
    apply Fix_sub_rect.
    - intros. 
      destruct x0; try reflexivity.
      + erewrite H. reflexivity.
      + apply Forall_HIn_eq. intros. erewrite H. reflexivity.
      + apply Forall_HIn_eq. intros. erewrite H. reflexivity.
      + erewrite H. reflexivity.
    - intros.
      destruct x; try reflexivity.
  Qed.

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

  Lemma NO_VOID_Struct_cons_inv :
    forall dt dts,
      NO_VOID dt ->
      NO_VOID (DTYPE_Struct dts) ->
      NO_VOID (DTYPE_Struct (dt :: dts)).
  Proof.
    intros dt dts NVdt NVdts.
    rewrite NO_VOID_equation in NVdts.
    rewrite NO_VOID_equation.

    apply Forall_HIn_cons_inv; auto.
  Qed.

  Lemma NO_VOID_Packed_struct_cons_inv :
    forall dt dts,
      NO_VOID dt ->
      NO_VOID (DTYPE_Packed_struct dts) ->
      NO_VOID (DTYPE_Packed_struct (dt :: dts)).
  Proof.
    intros dt dts NVdt NVdts.
    rewrite NO_VOID_equation in NVdts.
    rewrite NO_VOID_equation.

    apply Forall_HIn_cons_inv; auto.
  Qed.

  #[global] Hint Rewrite NO_VOID_equation : NO_VOID.
  #[global] Hint Resolve NO_VOID_Struct_cons_inv : NO_VOID.
  #[global] Hint Resolve NO_VOID_Packed_struct_cons_inv : NO_VOID.
  Ltac solve_no_void :=
    solve
      [ auto with NO_VOID
      | match goal with
        | H: NO_VOID _ /\ _ |- _
          => destruct H; solve_no_void
        end
      | rewrite NO_VOID_equation; solve_no_void
      ].

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
  | DVALUE_Poison_typ  : forall τ, NO_VOID τ -> dvalue_has_dtyp (DVALUE_Poison τ) τ

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
  | UVALUE_Poison_typ  : forall τ, NO_VOID τ -> uvalue_has_dtyp (UVALUE_Poison τ) τ
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
        uvalue_has_dtyp (UVALUE_ExtractElement (DTYPE_Vector (N.of_nat n) t) vect idx) t
  | UVALUE_ExtractElement_ptr_typ :
      forall n vect idx t,
        uvalue_has_dtyp idx DTYPE_IPTR ->
        uvalue_has_dtyp vect (DTYPE_Vector (N.of_nat n) t) ->
        uvalue_has_dtyp (UVALUE_ExtractElement (DTYPE_Vector (N.of_nat n) t) vect idx) t
  | UVALUE_InsertElement_typ :
      forall n vect val idx t sz,
        IX_supported sz ->
        uvalue_has_dtyp idx (DTYPE_I sz) ->
        uvalue_has_dtyp vect (DTYPE_Vector (N.of_nat n) t) ->
        uvalue_has_dtyp val t ->
        uvalue_has_dtyp (UVALUE_InsertElement (DTYPE_Vector (N.of_nat n) t) vect val idx) (DTYPE_Vector (N.of_nat n) t)
  | UVALUE_InsertElement_ptr_typ :
      forall n vect val idx t,
        uvalue_has_dtyp idx DTYPE_IPTR ->
        uvalue_has_dtyp vect (DTYPE_Vector (N.of_nat n) t) ->
        uvalue_has_dtyp val t ->
        uvalue_has_dtyp (UVALUE_InsertElement (DTYPE_Vector (N.of_nat n) t) vect val idx) (DTYPE_Vector (N.of_nat n) t)
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
        uvalue_has_dtyp (UVALUE_ExtractValue (DTYPE_Struct fts) (UVALUE_Struct fields) [idx]) dt
  | UVALUE_ExtractValue_Struct_cons_typ :
      forall fields fts fld ft dt idx idxs,
        uvalue_has_dtyp (UVALUE_Struct fields) (DTYPE_Struct fts) ->
        (0 <= idx)%Z ->
        Nth fts (Z.to_nat idx) ft ->
        Nth fields (Z.to_nat idx) fld ->
        uvalue_has_dtyp fld ft ->
        uvalue_has_dtyp (UVALUE_ExtractValue ft fld idxs) dt ->
        uvalue_has_dtyp (UVALUE_ExtractValue (DTYPE_Struct fts) (UVALUE_Struct fields) (idx :: idxs)) dt
  | UVALUE_ExtractValue_Packed_struct_sing_typ :
      forall fields fts dt idx,
        uvalue_has_dtyp (UVALUE_Packed_struct fields) (DTYPE_Packed_struct fts) ->
        (0 <= idx)%Z ->
        Nth fts (Z.to_nat idx) dt ->
        uvalue_has_dtyp (UVALUE_ExtractValue (DTYPE_Packed_struct fts) (UVALUE_Packed_struct fields) [idx]) dt
  | UVALUE_ExtractValue_Packed_struct_cons_typ :
      forall fields fts fld ft dt idx idxs,
        uvalue_has_dtyp (UVALUE_Packed_struct fields) (DTYPE_Packed_struct fts) ->
        (0 <= idx)%Z ->
        Nth fts (Z.to_nat idx) ft ->
        Nth fields (Z.to_nat idx) fld ->
        uvalue_has_dtyp fld ft ->
        uvalue_has_dtyp (UVALUE_ExtractValue ft fld idxs) dt ->
        uvalue_has_dtyp (UVALUE_ExtractValue (DTYPE_Packed_struct fts) (UVALUE_Packed_struct fields) (idx :: idxs)) dt
  | UVALUE_ExtractValue_Array_sing_typ :
      forall elements dt idx n,
        uvalue_has_dtyp (UVALUE_Array elements) (DTYPE_Array n dt) ->
        (0 <= idx <= Z.of_N n)%Z ->
        uvalue_has_dtyp (UVALUE_ExtractValue (DTYPE_Array n dt) (UVALUE_Array elements) [idx]) dt
  | UVALUE_ExtractValue_Array_cons_typ :
      forall elements elem et dt n idx idxs,
        uvalue_has_dtyp (UVALUE_Array elements) (DTYPE_Array n et) ->
        (0 <= idx <= Z.of_N n)%Z ->
        Nth elements (Z.to_nat idx) elem ->
        uvalue_has_dtyp elem et ->
        uvalue_has_dtyp (UVALUE_ExtractValue et elem idxs) dt ->
        uvalue_has_dtyp (UVALUE_ExtractValue (DTYPE_Array n et) (UVALUE_Array elements) (idx :: idxs)) dt
  | UVALUE_InsertValue_typ :
      forall struc idxs uv st dt,
        uvalue_has_dtyp (UVALUE_ExtractValue st struc idxs) dt ->
        uvalue_has_dtyp uv dt ->
        uvalue_has_dtyp struc st ->
        uvalue_has_dtyp (UVALUE_InsertValue st struc uv idxs) st
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

    (* Poison *)
    Hypothesis IH_Poison_Array    : forall sz t
                                     (NV: NO_VOID t)
                                     (IH: P (UVALUE_Poison t) t),
        P (UVALUE_Poison (DTYPE_Array sz t)) (DTYPE_Array sz t).
    Hypothesis IH_Poison_Vector    : forall sz t
                                     (NV: NO_VOID t)
                                     (IH: P (UVALUE_Poison t) t),
        P (UVALUE_Poison (DTYPE_Vector sz t)) (DTYPE_Vector sz t).

    Hypothesis IH_Poison_Struct_nil    :
        P (UVALUE_Poison (DTYPE_Struct [])) (DTYPE_Struct []).

    Hypothesis IH_Poison_Struct_cons    : forall dt dts,
        P (UVALUE_Poison dt) dt ->
        P (UVALUE_Poison (DTYPE_Struct dts)) (DTYPE_Struct dts) ->
        P (UVALUE_Poison (DTYPE_Struct (dt :: dts))) (DTYPE_Struct (dt :: dts)).

    Hypothesis IH_Poison_Packed_struct_nil    :
        P (UVALUE_Poison (DTYPE_Packed_struct [])) (DTYPE_Packed_struct []).

    Hypothesis IH_Poison_Packed_struct_cons    : forall dt dts,
        P (UVALUE_Poison dt) dt ->
        P (UVALUE_Poison (DTYPE_Packed_struct dts)) (DTYPE_Packed_struct dts) ->
        P (UVALUE_Poison (DTYPE_Packed_struct (dt :: dts))) (DTYPE_Packed_struct (dt :: dts)).

    Hypothesis IH_Poison          : forall t, (NO_VOID t /\ (forall dts, t <> DTYPE_Struct dts) /\ (forall dts, t <> DTYPE_Packed_struct dts) /\ (forall sz et, t <> DTYPE_Array sz et) /\ (forall sz et, t <> DTYPE_Vector sz et)) -> P (UVALUE_Poison t) t
.

    (* Undef *)
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
        P (UVALUE_ExtractElement (DTYPE_Vector (N.of_nat n) t) vect idx) t.

    Hypothesis IH_ExtractElement_ptr : forall (n : nat) (vect idx : uvalue) (t : dtyp),
        uvalue_has_dtyp idx DTYPE_IPTR ->
        P idx DTYPE_IPTR ->
        uvalue_has_dtyp vect (DTYPE_Vector (N.of_nat n) t) ->
        P vect (DTYPE_Vector (N.of_nat n) t) ->
        P (UVALUE_ExtractElement (DTYPE_Vector (N.of_nat n) t) vect idx) t.

    Hypothesis IH_InsertElement : forall (n : nat) (vect val idx : uvalue) (t : dtyp) (sz : N),
        IX_supported sz ->
        uvalue_has_dtyp idx (DTYPE_I sz) ->
        P idx (DTYPE_I sz) ->
        uvalue_has_dtyp vect (DTYPE_Vector (N.of_nat n) t) ->
        P vect (DTYPE_Vector (N.of_nat n) t) ->
        uvalue_has_dtyp val t ->
        P val t ->
        P (UVALUE_InsertElement (DTYPE_Vector (N.of_nat n) t) vect val idx)
          (DTYPE_Vector (N.of_nat n) t).

    Hypothesis IH_InsertElement_ptr : forall (n : nat) (vect val idx : uvalue) (t : dtyp),
        uvalue_has_dtyp idx DTYPE_IPTR ->
        P idx DTYPE_IPTR ->
        uvalue_has_dtyp vect (DTYPE_Vector (N.of_nat n) t) ->
        P vect (DTYPE_Vector (N.of_nat n) t) ->
        uvalue_has_dtyp val t ->
        P val t ->
        P (UVALUE_InsertElement (DTYPE_Vector (N.of_nat n) t) vect val idx)
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
          (UVALUE_ExtractValue (DTYPE_Struct fts) (UVALUE_Struct fields) [idx]) dt.

    Hypothesis IH_ExtractValue_Struct_cons : forall (fields : list uvalue) (fts : list dtyp)
                                               (fld : uvalue) (ft dt : dtyp) (idx : Z)
                                               (idxs : list LLVMAst.int),
        uvalue_has_dtyp (UVALUE_Struct fields) (DTYPE_Struct fts) ->
        P (UVALUE_Struct fields) (DTYPE_Struct fts) ->
        (0 <= idx)%Z ->
        Nth fts (Z.to_nat idx) ft ->
        Nth fields (Z.to_nat idx) fld ->
        uvalue_has_dtyp fld ft ->
        P fld ft ->
        uvalue_has_dtyp (UVALUE_ExtractValue ft fld idxs) dt ->
        P (UVALUE_ExtractValue ft fld idxs) dt ->
        P
          (UVALUE_ExtractValue (DTYPE_Struct fts) (UVALUE_Struct fields) (idx :: idxs))
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
          (UVALUE_ExtractValue (DTYPE_Packed_struct fts) (UVALUE_Packed_struct fields)
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
        Nth fts (Z.to_nat idx) ft ->
        Nth fields (Z.to_nat idx) fld ->
        uvalue_has_dtyp fld ft ->
        P fld ft ->
        uvalue_has_dtyp (UVALUE_ExtractValue ft fld idxs) dt ->
        P (UVALUE_ExtractValue ft fld idxs) dt ->
        P
          (UVALUE_ExtractValue (DTYPE_Packed_struct fts) (UVALUE_Packed_struct fields)
                               (idx :: idxs)) dt.

    Hypothesis IH_ExtractValue_Array_sing : forall (elements : list uvalue) (dt : dtyp) (idx : Z) (n : N),
        uvalue_has_dtyp (UVALUE_Array elements) (DTYPE_Array n dt) ->
        P (UVALUE_Array elements) (DTYPE_Array n dt) ->
        (0 <= idx <= Z.of_N n)%Z ->
        P
          (UVALUE_ExtractValue (DTYPE_Array n dt) (UVALUE_Array elements) [idx]) dt.

    Hypothesis IH_ExtractValue_Array_cons : forall (elements : list uvalue) (elem : uvalue)
                                              (et dt : dtyp) (n : N) (idx : Z)
                                              (idxs : list LLVMAst.int),
        uvalue_has_dtyp (UVALUE_Array elements) (DTYPE_Array n et) ->
        P (UVALUE_Array elements) (DTYPE_Array n et) ->
        (0 <= idx <= Z.of_N n)%Z ->
        Nth elements (Z.to_nat idx) elem ->
        uvalue_has_dtyp elem et ->
        P elem et ->
        uvalue_has_dtyp (UVALUE_ExtractValue et elem idxs) dt ->
        P (UVALUE_ExtractValue et elem idxs) dt ->
        P
          (UVALUE_ExtractValue (DTYPE_Array n et) (UVALUE_Array elements) (idx :: idxs))
          dt.

    Hypothesis IH_InsertValue : forall (struc : uvalue) (idxs : list LLVMAst.int)
                                  (uv : uvalue) (st dt : dtyp),
        uvalue_has_dtyp (UVALUE_ExtractValue st struc idxs) dt ->
        P (UVALUE_ExtractValue st struc idxs) dt ->
        uvalue_has_dtyp uv dt ->
        P uv dt ->
        uvalue_has_dtyp struc st ->
        P struc st ->
        P (UVALUE_InsertValue st struc uv idxs) st.

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
          try solve [eapply IH_Poison;
                     repeat split; solve [intros * CONTRA; inversion CONTRA]].

        (* Poison Arrays *)
        { pose proof NV as NVd.
          rewrite NO_VOID_equation in NVd.
          apply IH_Poison_Array; auto.
        }

        (* Poison Structs *)
        { pose proof NV as NVfs.
          rewrite NO_VOID_equation in NVfs.
          clear Hτ.
          generalize dependent fields.
          induction fields; intros NV NVfs.
          - apply IH_Poison_Struct_nil.
          - apply IH_Poison_Struct_cons.
            apply IHτ.
            eapply NO_VOID_Struct_fields in NV.
            apply NV.
            left; auto.
            apply IHfields.

            eapply NO_VOID_Struct_cons; eauto.
            eapply Forall_HIn_cons; eauto.
        }

        (* Poison Packed structs *)
        { pose proof NV as NVfs.
          rewrite NO_VOID_equation in NVfs.
          clear Hτ.
          generalize dependent fields.
          induction fields; intros NV NVfs.
          - apply IH_Poison_Packed_struct_nil.
          - apply IH_Poison_Packed_struct_cons.
            apply IHτ.
            eapply NO_VOID_Packed_struct_fields in NV.
            apply NV.
            left; auto.
            apply IHfields.

            eapply NO_VOID_Packed_struct_cons; eauto.
            eapply Forall_HIn_cons; eauto.
        }

        (* Poison Vectors *)
        { pose proof NV as NVd.
          rewrite NO_VOID_equation in NVd.
          apply IH_Poison_Vector; auto.
        }

        Unshelve.
        all: try solve [exact 0%N | exact DTYPE_Void | exact ([] : list dtyp)].


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

  Section EvalIopLemmas.
    Context (M : Type -> Type).
    Context {Eq1 : @Monad.Eq1 M}.
    Context {Monad : Monad M}.
    Context {MonadLaws : Monad.MonadLawsE M}.
    Context {RET_INV : @Eq1_ret_inv M Eq1 Monad}.
    Context {Eq1EQV : @Monad.Eq1Equivalence M Monad Eq1}.
    Context {RETS : @MonadReturns M Monad Eq1}.
    Context {NFR : @NoFailsRet M Monad Eq1 RETS}.
    Context {ERR : RAISE_ERROR M}.
    Context {UB : RAISE_UB M}.
    Context {OOM : RAISE_OOM M}.
    Context {FERR : MFails_ERROR M}.
    Context {FUB : MFails_UB M}.
    Context {FOOM : MFails_OOM M}.

    Lemma eval_iop_integer_h_dtyp :
      forall dx dy dv sz op,
        dvalue_has_dtyp dx (DTYPE_I sz) ->
        dvalue_has_dtyp dy (DTYPE_I sz) ->
        Monad.eq1 (eval_iop_integer_h op dx dy) (@ret M _ _ dv) ->
        dvalue_has_dtyp dv (DTYPE_I sz).
    Proof.
      intros dx dy dv sz op TYPx TYPy EVAL.
      inversion TYPx; inversion TYPy; subst;
        destruct op;
        cbn in EVAL;
        repeat break_match_hyp;

        try solve
            [first
               [ apply eq1_ret_ret in EVAL; [| solve [eauto]]
               | apply MReturns_ret in EVAL;
                 apply MReturns_bind_inv in EVAL as [FAILS | (res & MA & RET)];
                 [ cbn in FAILS; apply MFails_ret in FAILS; contradiction
                 | break_match_hyp; apply MReturns_ret_inv in RET
                 ]
               | apply MReturns_ret in EVAL;
                 apply MReturns_bind_inv in EVAL as [FAILS | (res & MA & RET)];
                   [ cbn in FAILS; apply MFails_ret in FAILS; contradiction
                   | repeat break_match_hyp;
                     [ apply MReturns_ret_inv in RET
                     | cbn in RET;
                       apply MReturns_bind_inv in RET as [FAILS | (res' & MA' & RET)];
                       [ cbn in FAILS; apply MFails_ret in FAILS; contradiction
                       | repeat break_match_hyp;
                         apply MReturns_ret_inv in RET
                       ]
                     ]
                   ]
               ]; subst; constructor; solve_no_void].

      all:
        try solve [eapply EqRet_NoFail in EVAL; eauto;
        exfalso; apply EVAL;
        first [apply mfails_ub | apply mfails_error | apply mfails_oom]; eauto].
      all : apply MReturns_ret in EVAL;
              apply MReturns_bind_inv in EVAL as [FAILS | (res & MA & RET)];
                          [ cbn in FAILS; apply MFails_ret in FAILS; contradiction |];
                          apply MReturns_ret_inv in RET; subst; constructor.
      all : constructor.
    Qed.

    Lemma eval_iop_dtyp_i :
      forall dx dy dv sz op,
        dvalue_has_dtyp dx (DTYPE_I sz) ->
        dvalue_has_dtyp dy (DTYPE_I sz) ->
        Monad.eq1 (eval_iop op dx dy) (ret dv) ->
        dvalue_has_dtyp dv (DTYPE_I sz).
    Proof.
      intros dx dy dv sz op TYPx TYPy EVAL.
      unfold eval_iop in EVAL.
      inversion TYPx; inversion TYPy; subst; try lia.
      all: eapply eval_iop_integer_h_dtyp in EVAL; eauto.
    Qed.

    Lemma eval_iop_integer_h_dtyp_iptr :
      forall dx dy dv op,
        dvalue_has_dtyp dx DTYPE_IPTR ->
        dvalue_has_dtyp dy DTYPE_IPTR ->
        Monad.eq1 (eval_iop_integer_h op dx dy) (ret dv) ->
        dvalue_has_dtyp dv DTYPE_IPTR.
    Proof.
      intros dx dy dv op TYPx TYPy EVAL.
      inversion TYPx; inversion TYPy; subst;
        destruct op;
        cbn in EVAL;
        repeat break_match_hyp;
        pose proof EVAL as CONTRA;
        try solve
            [first [ apply eq1_ret_ret in EVAL;
                     subst;
                     [ try (unfold VMemInt_intptr';
                            rewrite VMemInt_intptr_dtyp)
                     | solve [eauto]
                     ]

                   | apply MReturns_ret in EVAL;
                     apply MReturns_bind_inv in EVAL as [FAILS | (res & MA & RET)];
                     [eapply EqRet_NoFail in CONTRA; eauto;
                      exfalso; apply CONTRA;
                      apply MFails_bind_ma; eauto
                     | apply MReturns_ret_inv in RET;
                       cbn in RET
                     ]

                   | apply MReturns_ret in EVAL;
                     apply MReturns_bind_inv in EVAL as [FAILS | (res & MA & RET)];
                     [eapply EqRet_NoFail in CONTRA; eauto;
                      exfalso; apply CONTRA;
                      apply MFails_bind_ma; eauto
                     | apply MReturns_ret_inv in RET;
                       cbn in RET
                     ]

                   | apply MReturns_ret in EVAL;
                     apply MReturns_bind_inv in EVAL as [FAILS | (res & MA & RET)];
                     [ eapply EqRet_NoFail in CONTRA; eauto;
                       exfalso; apply CONTRA;
                       apply MFails_bind_ma; eauto
                     | clear CONTRA;
                       break_match_hyp;
                       apply MReturns_ret_inv in RET;
                       cbn in RET
                     ]

                   | apply MReturns_ret in EVAL;
                     apply MReturns_bind_inv in EVAL as [FAILS | (res & MA & RET)];
                     [ eapply EqRet_NoFail in CONTRA; eauto;
                       exfalso; apply CONTRA;
                       apply MFails_bind_ma; eauto
                     | repeat match goal with
                              | H : MReturns _ (if ?c then _ else _) |- _ =>
                                  destruct c eqn:?
                              end;
                       [ apply MReturns_ret_inv in RET; cbn in RET
                       | cbn in RET;
                         apply MReturns_bind_inv in RET as [FAILS | (res' & MA' & RET)];
                         [eapply EqRet_NoFail in CONTRA; eauto;
                          exfalso; apply CONTRA;
                          eapply MFails_bind_k; eauto;
                          break_match;
                          [ match goal with
                            | H: true = false |- _ =>
                                inversion H
                            end
                          |]; eapply MFails_bind_ma; eauto
                         |]
                       ];
                       try (match goal with
                            | H : MReturns _ (if ?c then _ else _) |- _ =>
                                destruct c eqn:?
                            end;
                            apply MReturns_ret_inv in RET; cbn in RET)
                    ]
                ]; subst;
             try (unfold VMemInt_intptr';
                  rewrite VMemInt_intptr_dtyp);
             constructor; solve_no_void].

      all:
        try solve [eapply EqRet_NoFail in EVAL; eauto;
        exfalso; apply EVAL;
        first [apply mfails_ub | apply mfails_error | apply mfails_oom] ; eauto].
    Qed.

    Lemma eval_iop_dtyp_iptr :
      forall dx dy dv op,
        dvalue_has_dtyp dx DTYPE_IPTR ->
        dvalue_has_dtyp dy DTYPE_IPTR ->
        Monad.eq1 (eval_iop op dx dy) (ret dv) ->
        dvalue_has_dtyp dv DTYPE_IPTR.
    Proof.
      intros dx dy dv op TYPx TYPy EVAL.
      unfold eval_iop in EVAL.
      inversion TYPx; inversion TYPy; subst; try lia.
      all: eapply eval_iop_integer_h_dtyp_iptr in EVAL; eauto.
    Qed.
  End EvalIopLemmas.

  Definition default_dvalue_of_dtyp_i (sz : N) : err dvalue:=
    (if (sz =? 64) then ret (DVALUE_I64 (repr 0))
     else if (sz =? 32) then ret (DVALUE_I32 (repr 0))
          else if (sz =? 8) then ret (DVALUE_I8 (repr 0))
               else if (sz =? 1) then ret (DVALUE_I1 (repr 0))
                    else failwith
                           "Illegal size for generating default dvalue of DTYPE_I").


  (* Handler for PickE which concretizes everything to 0 *)
  (* If this succeeds the dvalue returned should agree with
     dvalue_has_dtyp for the sake of the dvalue_default lemma. *)
  Fixpoint default_dvalue_of_dtyp (dt : dtyp) : err dvalue :=
    match dt with
    | DTYPE_I sz => default_dvalue_of_dtyp_i sz
    | DTYPE_IPTR => ret (DVALUE_IPTR IP.zero)
    | DTYPE_Pointer => ret (DVALUE_Addr A.null)
    | DTYPE_Void => ret DVALUE_None
    | DTYPE_Half => failwith "Unimplemented default type: half"
    | DTYPE_Float => ret (DVALUE_Float Float32.zero)
    | DTYPE_Double => ret (DVALUE_Double (Float32.to_double Float32.zero))
    | DTYPE_X86_fp80 => failwith "Unimplemented default type: x86_fp80"
    | DTYPE_Fp128 => failwith "Unimplemented default type: fp128"
    | DTYPE_Ppc_fp128 => failwith "Unimplemented default type: ppc_fp128"
    | DTYPE_Metadata => failwith "Unimplemented default type: metadata"
    | DTYPE_X86_mmx => failwith "Unimplemented default type: x86_mmx"
    | DTYPE_Opaque => failwith "Unimplemented default type: opaque"
    | DTYPE_Array sz t =>
        v <- default_dvalue_of_dtyp t ;;
        (ret (DVALUE_Array (repeat v (N.to_nat sz))))

    (* Matching valid Vector types... *)
    (* Currently commented out unsupported ones *)
    (* | DTYPE_Vector sz (DTYPE_Half) => *)
    (*   if (0 <=? sz) then *)
    (*     (ret (DVALUE_Vector *)
    (*             (repeat (DVALUE_Float Float32.zero) (N.to_nat sz)))) *)
    (*   else *)
    (*     failwith ("Negative array length for generating default value" ++ *)
    (*     "of DTYPE_Array or DTYPE_Vector") *)
    | DTYPE_Vector sz (DTYPE_Float) =>
        ret (DVALUE_Vector
               (repeat (DVALUE_Float Float32.zero) (N.to_nat sz)))
    | DTYPE_Vector sz (DTYPE_Double) =>
        ret (DVALUE_Vector
               (repeat (DVALUE_Double (Float32.to_double Float32.zero))
                       (N.to_nat sz)))
    (* | DTYPE_Vector sz (DTYPE_X86_fp80) => *)
    (*   if (0 <=? sz) then *)
    (*     (ret (DVALUE_Vector *)
    (*             (repeat (DVALUE_Float Float32.zero) (N.to_nat sz)))) *)
    (*   else *)
    (*     failwith ("Negative array length for generating default value" ++ *)
    (*     "of DTYPE_Array or DTYPE_Vector") *)
    (* | DTYPE_Vector sz (DTYPE_Fp128) => *)
    (*   if (0 <=? sz) then *)
    (*     (ret (DVALUE_Vector *)
    (*             (repeat (DVALUE_Float Float32.zero) (N.to_nat sz)))) *)
    (*   else *)
    (*     failwith ("Negative array length for generating default value" ++ *)
    (*     "of DTYPE_Array or DTYPE_Vector") *)
    | DTYPE_Vector sz (DTYPE_I n) =>
        v <- default_dvalue_of_dtyp_i n ;;
        ret (DVALUE_Vector (repeat v (N.to_nat sz)))

    | DTYPE_Vector sz DTYPE_Pointer =>
        ret (DVALUE_Vector (repeat (DVALUE_Addr A.null) (N.to_nat sz)))

    | DTYPE_Vector _ _ => failwith ("Non-valid or unsupported vector type when generating default vector")
    | DTYPE_Struct fields =>
        v <- @map_monad err _ dtyp dvalue default_dvalue_of_dtyp fields;;
        ret (DVALUE_Struct v)
    | DTYPE_Packed_struct fields =>
        v <- @map_monad err _ dtyp dvalue default_dvalue_of_dtyp fields;;
        ret (DVALUE_Packed_struct v)
    end.

  Ltac do_it := constructor; cbn; auto; fail.

  Lemma dvalue_default : forall t v,
      inr v = (default_dvalue_of_dtyp t) ->
      dvalue_has_dtyp v t.
  Proof.
    intros t v. revert v.
    induction t; try do_it;
      try (intros; subst; inversion H; constructor).
    - intros. subst. cbn in H.
      unfold default_dvalue_of_dtyp_i in H.
      destruct (@IX_supported_dec a).
      * inversion i; subst; cbn in H; inversion H; constructor; auto.
      * rewrite unsupported_cases in H; auto. inversion H.
    - intros. subst. inversion H. clear H.
      induction sz.
      + cbn in H1.
        destruct (default_dvalue_of_dtyp t) eqn: HT. inv H1. inv H1.
        pose proof DVALUE_Array_typ.
        specialize (H nil (N.to_nat 0) t).
        rewrite Nnat.N2Nat.id in H.
        apply H. auto. auto.
      + cbn in H1.
        destruct (default_dvalue_of_dtyp t) eqn: HT. inv H1. inv H1.
        pose proof DVALUE_Array_typ as ARR.
        specialize (ARR (repeat d (Pos.to_nat p)) (N.to_nat (N.pos p)) t).
        rewrite Nnat.N2Nat.id in ARR.
        cbn in *.
        apply ARR.
        * apply forall_repeat_true.
          apply IHt. reflexivity.
        * apply repeat_length.
    - revert H. induction fields.
      + intros. inv H0. constructor.
      + intros.
        assert (forall u : dtyp,
                   In u fields ->
                   forall v : dvalue,
                     inr v = default_dvalue_of_dtyp u -> dvalue_has_dtyp v u).
        { intros. apply H. apply in_cons. auto. auto. }
        specialize (IHfields H1). clear H1.
        Opaque map_monad.
        (* Reduce H0 *)
        cbn in H0.
        rewrite list_cons_app in H0.
        rewrite map_monad_app in H0. cbn in H0.
        Transparent map_monad.
        unfold map_monad at 1 in H0.
        Opaque map_monad. cbn in H0.
        destruct (default_dvalue_of_dtyp a) eqn: A_DEFAULT.
        inv H0.
        destruct (map_monad default_dvalue_of_dtyp fields) eqn: FIELDS.
        inv H0.
        inv H0. constructor. apply H. apply in_eq.
        symmetry. auto.
        apply IHfields. cbn. rewrite FIELDS. reflexivity.
    - revert H. induction fields.
      + intros. inv H0. constructor.
      + intros.
        assert (forall u : dtyp,
                   In u fields ->
                   forall v : dvalue,
                     inr v = default_dvalue_of_dtyp u -> dvalue_has_dtyp v u).
        { intros. apply H. apply in_cons. auto. auto. }
        specialize (IHfields H1). clear H1.
        Opaque map_monad.
        (* Reduce H0 *)
        cbn in H0.
        rewrite list_cons_app in H0.
        rewrite map_monad_app in H0. cbn in H0.
        Transparent map_monad.
        unfold map_monad at 1 in H0.
        Opaque map_monad. cbn in H0.
        destruct (default_dvalue_of_dtyp a) eqn: A_DEFAULT.
        inv H0.
        destruct (map_monad default_dvalue_of_dtyp fields) eqn: FIELDS.
        inv H0.
        inv H0. constructor. apply H. apply in_eq.
        symmetry. auto.
        apply IHfields. cbn. rewrite FIELDS. reflexivity.
    - intros. subst. inversion H. clear H.
      revert H1. revert v. revert IHt. revert t.
      induction sz.
      + intros. cbn in H1.
        pose proof DVALUE_Vector_typ.
        specialize (H nil (N.to_nat 0)).
        rewrite Nnat.N2Nat.id in H.
        destruct t; inv H1;
          try
            (apply H;
             [constructor | constructor |
               unfold vector_dtyp; intuition]).
        destruct (default_dvalue_of_dtyp_i sz) eqn: HI; inv H2.
        apply H. constructor. auto. unfold vector_dtyp. left.
        exists sz. reflexivity.
      + intros. cbn in H1.
        destruct t; inv H1;
          try (
              rewrite <- positive_nat_N;
              constructor; [apply forall_repeat_true ; constructor |
                             apply repeat_length |
                             unfold vector_dtyp ; intuition ]).
        destruct (default_dvalue_of_dtyp_i sz) eqn: SZ; inv H0.
        pose proof DVALUE_Vector_typ.
        rewrite <- positive_nat_N. apply H.
        apply forall_repeat_true. apply IHt. symmetry. auto.
        apply repeat_length.
        left. exists sz. reflexivity.
  Qed.

  Definition uvalue_constructor_string (u : uvalue) : string
    := match u with
       | UVALUE_Addr a => "UVALUE_Addr"
       | UVALUE_I1 x => "UVALUE_I1"
       | UVALUE_I8 x => "UVALUE_I8"
       | UVALUE_I32 x => "UVALUE_I32"
       | UVALUE_I64 x => "UVALUE_I64"
       | UVALUE_IPTR x => "UVALUE_IPTR"
       | UVALUE_Double x => "UVALUE_Double"
       | UVALUE_Float x => "UVALUE_Float"
       | UVALUE_Undef t => "UVALUE_Undef"
       | UVALUE_Poison t => "UVALUE_Poison"
       | UVALUE_None => "UVALUE_None"
       | UVALUE_Struct fields => "UVALUE_Struct"
       | UVALUE_Packed_struct fields => "UVALUE_Packed_struct"
       | UVALUE_Array elts => "UVALUE_Array"
       | UVALUE_Vector elts => "UVALUE_Vector"
       | UVALUE_IBinop iop v1 v2 => "UVALUE_IBinop"
       | UVALUE_ICmp cmp v1 v2 => "UVALUE_ICmp"
       | UVALUE_FBinop fop fm v1 v2 => "UVALUE_FBinop"
       | UVALUE_FCmp cmp v1 v2 => "UVALUE_FCmp"
       | UVALUE_Conversion conv t_from v t_to => "UVALUE_Conversion"
       | UVALUE_GetElementPtr t ptrval idxs => "UVALUE_GetElementPtr"
       | UVALUE_ExtractElement t vec idx => "UVALUE_ExtractElement"
       | UVALUE_InsertElement t vec elt idx => "UVALUE_InsertElement"
       | UVALUE_ShuffleVector vec1 vec2 idxmask => "UVALUE_ShuffleVector"
       | UVALUE_ExtractValue t vec idxs => "UVALUE_ExtractValue"
       | UVALUE_InsertValue t vec elt idxs => "UVALUE_InsertValue"
       | UVALUE_Select cnd v1 v2 => "UVALUE_Select"
       | UVALUE_ExtractByte uv dt idx sid => "UVALUE_ExtractByte"
       | UVALUE_ConcatBytes uvs dt => "UVALUE_ConcatBytes"
       end.
End DVALUE.
