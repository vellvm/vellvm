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
     LLVMAst
     AstLib
     MemoryAddress
     Error
     DynamicTypes
     Util.

Require Import Integers Floats.

Import EqvNotation.
Import MonadNotation.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

Open Scope Z_scope.

Instance Eqv_nat : Eqv nat := (@eq nat).

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

Definition inttyp (x:Z) : Type :=
  match x with
  | 1 => int1
  | 8 => int8
  | 32 => int32
  | 64 => int64
  | _ => False
  end.

Inductive IX_supported : Z -> Prop :=
| I1_Supported : IX_supported 1
| I8_Supported : IX_supported 8
| I32_Supported : IX_supported 32
| I64_Supported : IX_supported 64
.

Lemma IX_supported_dec : forall (sz:Z), {IX_supported sz} + {~IX_supported sz}.
Proof.
  intros sz.
  - decide (sz = 1).
    + left. subst. constructor.
    + decide (sz = 8). 
      * left. subst. constructor.
      * decide (sz = 32).
        -- left. subst. constructor.
        -- decide (sz = 64).
           ++ left. subst. constructor.
           ++ right. intro X.
              inversion X; subst; contradiction.
Qed.

(* What's a good way to prove this ? *)
(* IY: This is not ideal, but here is an equivalent formulation with an ugly
   if-else chain.. I feel like there must be some clean way to prove the
   original lemma using boolean reflection. *)
Lemma unsupported_cases : forall {X} (sz : Z) (N : ~ IX_supported sz) (x64 x32 x8 x1 x : X),
    (if (sz =? 64) then x64
      else if (sz =? 32) then x32
          else if (sz =? 8) then x8
                else if (sz =? 1) then x1
                    else x) = x.
Proof.
  intros.
  destruct (sz =? 64) eqn: H.
  rewrite Z.eqb_eq in H.
  destruct N. rewrite H. constructor.
  destruct (sz =? 32) eqn: H'.
  rewrite Z.eqb_eq in H'.
  destruct N. rewrite H'. constructor.
  destruct (sz =? 8) eqn: H''.
  rewrite Z.eqb_eq in H''.
  destruct N. rewrite H''. constructor.
  destruct (sz =? 1) eqn: H'''.
  rewrite Z.eqb_eq in H'''.
  destruct N. rewrite H'''. constructor.
  reflexivity.
Qed.

Function unsupported_cases_match_ {X} (sz : Z) (x64 x32 x8 x1 x : X) :=
    match sz with
    | 64 => x64
    | 32 => x32
    | 8 => x8
    | 1 => x1
    | _ => x
    end.

Lemma unsupported_cases_match : forall {X} (sz : Z) (N : ~ IX_supported sz) (x64 x32 x8 x1 x : X), 
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

Module DVALUE(A:Vellvm.MemoryAddress.ADDRESS).

(* The set of dynamic values manipulated by an LLVM program. *)
Inductive dvalue : Set :=
| DVALUE_Addr (a:A.addr)
| DVALUE_I1 (x:int1)
| DVALUE_I8 (x:int8)
| DVALUE_I32 (x:int32)
| DVALUE_I64 (x:int64)
| DVALUE_Double (x:ll_double)
| DVALUE_Float (x:ll_float)
| DVALUE_Poison
| DVALUE_None
| DVALUE_Struct        (fields: list dvalue)
| DVALUE_Packed_struct (fields: list dvalue)
| DVALUE_Array         (elts: list dvalue)
| DVALUE_Vector        (elts: list dvalue)
.

Section DvalueInd.
  Variable P : dvalue -> Prop.
  Hypothesis IH_Addr          : forall a, P (DVALUE_Addr a).
  Hypothesis IH_I1            : forall x, P (DVALUE_I1 x).
  Hypothesis IH_I8            : forall x, P (DVALUE_I8 x).
  Hypothesis IH_I32           : forall x, P (DVALUE_I32 x).
  Hypothesis IH_I64           : forall x, P (DVALUE_I64 x).
  Hypothesis IH_Double        : forall x, P (DVALUE_Double x).
  Hypothesis IH_Float         : forall x, P (DVALUE_Float x).
  Hypothesis IH_Poison        : P DVALUE_Poison.
  Hypothesis IH_None          : P DVALUE_None.
  Hypothesis IH_Struct        : forall (fields: list dvalue), (forall u, In u fields -> P u) -> P (DVALUE_Struct fields).
  Hypothesis IH_Packed_Struct : forall (fields: list dvalue), (forall u, In u fields -> P u) -> P (DVALUE_Packed_struct fields).
  Hypothesis IH_Array         : forall (elts: list dvalue), (forall e, In e elts -> P e) -> P (DVALUE_Array elts).
  Hypothesis IH_Vector        : forall (elts: list dvalue), (forall e, In e elts -> P e) -> P (DVALUE_Vector elts).

  Lemma dvalue_ind' : forall (dv:dvalue), P dv.
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
Inductive uvalue : Set :=
| UVALUE_Addr (a:A.addr)
| UVALUE_I1 (x:int1)
| UVALUE_I8 (x:int8)
| UVALUE_I32 (x:int32)
| UVALUE_I64 (x:int64)
| UVALUE_Double (x:ll_double)
| UVALUE_Float (x:ll_float)
| UVALUE_Undef (t:dtyp)
| UVALUE_Poison
| UVALUE_None
| UVALUE_Struct        (fields: list uvalue)
| UVALUE_Packed_struct (fields: list uvalue)
| UVALUE_Array         (elts: list uvalue)
| UVALUE_Vector        (elts: list uvalue)
| UVALUE_IBinop           (iop:ibinop) (v1:uvalue) (v2:uvalue)
| UVALUE_ICmp             (cmp:icmp)   (v1:uvalue) (v2:uvalue)
| UVALUE_FBinop           (fop:fbinop) (fm:list fast_math) (v1:uvalue) (v2:uvalue)
| UVALUE_FCmp             (cmp:fcmp)   (v1:uvalue) (v2:uvalue)
| UVALUE_Conversion       (conv:conversion_type) (v:uvalue) (t_to:dtyp)
| UVALUE_GetElementPtr    (t:dtyp) (ptrval:uvalue) (idxs:list (uvalue)) (* TODO: do we ever need this? GEP raises an event? *)
| UVALUE_ExtractElement   (vec: uvalue) (idx: uvalue)
| UVALUE_InsertElement    (vec: uvalue) (elt:uvalue) (idx:uvalue)
| UVALUE_ShuffleVector    (vec1:uvalue) (vec2:uvalue) (idxmask:uvalue)
| UVALUE_ExtractValue     (vec:uvalue) (idxs:list int)
| UVALUE_InsertValue      (vec:uvalue) (elt:uvalue) (idxs:list int)
| UVALUE_Select           (cnd:uvalue) (v1:uvalue) (v2:uvalue)
.

Section UvalueInd.
  Variable P : uvalue -> Prop.
  Hypothesis IH_Addr           : forall a, P (UVALUE_Addr a).
  Hypothesis IH_I1             : forall x, P (UVALUE_I1 x).
  Hypothesis IH_I8             : forall x, P (UVALUE_I8 x).
  Hypothesis IH_I32            : forall x, P (UVALUE_I32 x).
  Hypothesis IH_I64            : forall x, P (UVALUE_I64 x).
  Hypothesis IH_Double         : forall x, P (UVALUE_Double x).
  Hypothesis IH_Float          : forall x, P (UVALUE_Float x).
  Hypothesis IH_Undef          : forall t, P (UVALUE_Undef t).
  Hypothesis IH_Poison         : P UVALUE_Poison.
  Hypothesis IH_None           : P UVALUE_None.
  Hypothesis IH_Struct         : forall (fields: list uvalue), (forall u, In u fields -> P u) -> P (UVALUE_Struct fields).
  Hypothesis IH_Packed_Struct  : forall (fields: list uvalue), (forall u, In u fields -> P u) -> P (UVALUE_Packed_struct fields).
  Hypothesis IH_Array          : forall (elts: list uvalue), (forall e, In e elts -> P e) -> P (UVALUE_Array elts).
  Hypothesis IH_Vector         : forall (elts: list uvalue), (forall e, In e elts -> P e) -> P (UVALUE_Vector elts).
  Hypothesis IH_IBinop         : forall (iop:ibinop) (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_IBinop iop v1 v2).
  Hypothesis IH_ICmp           : forall (cmp:icmp)   (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_ICmp cmp v1 v2).
  Hypothesis IH_FBinop         : forall (fop:fbinop) (fm:list fast_math) (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_FBinop fop fm v1 v2).
  Hypothesis IH_FCmp           : forall (cmp:fcmp)   (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_FCmp cmp v1 v2).
  Hypothesis IH_Conversion     : forall (conv:conversion_type) (v:uvalue) (t_to:dtyp), P v -> P (UVALUE_Conversion conv v t_to).
  Hypothesis IH_GetElementPtr  : forall (t:dtyp) (ptrval:uvalue) (idxs:list (uvalue)), P ptrval -> (forall idx, In idx idxs -> P idx) -> P (UVALUE_GetElementPtr t ptrval idxs).
  Hypothesis IH_ExtractElement : forall (vec: uvalue) (idx: uvalue), P vec -> P idx -> P (UVALUE_ExtractElement vec idx).
  Hypothesis IH_InsertElement  : forall (vec: uvalue) (elt:uvalue) (idx:uvalue), P vec -> P elt -> P idx -> P (UVALUE_InsertElement vec elt idx).
  Hypothesis IH_ShuffleVector  : forall (vec1:uvalue) (vec2:uvalue) (idxmask:uvalue), P vec1 -> P vec2 -> P idxmask -> P (UVALUE_ShuffleVector vec1 vec2 idxmask).
  Hypothesis IH_ExtractValue   : forall (vec:uvalue) (idxs:list int), P vec -> P (UVALUE_ExtractValue vec idxs).
  Hypothesis IH_InsertValue    : forall (vec:uvalue) (elt:uvalue) (idxs:list int), P vec -> P elt -> P (UVALUE_InsertValue vec elt idxs).
  Hypothesis IH_Select         : forall (cnd:uvalue) (v1:uvalue) (v2:uvalue), P cnd -> P v1 -> P v2 -> P (UVALUE_Select cnd v1 v2).

  Lemma uvalue_ind' : forall (uv:uvalue), P uv.
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
  | DVALUE_Double x => UVALUE_Double x
  | DVALUE_Float x => UVALUE_Float x
  | DVALUE_Poison => UVALUE_Poison
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
  | UVALUE_Double x                        => ret (DVALUE_Double x)
  | UVALUE_Float x                         => ret (DVALUE_Float x)
  | UVALUE_Undef t                         => failwith "Attempting to convert a non-defined uvalue to dvalue. The conversion should be guarded by is_concrete"
  | UVALUE_Poison                          => ret (DVALUE_Poison)
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
                 (* YZ: likely useless to recurse: I think it should be an invariant that:
                    1: We only call [uvalue_to_dvalue] on concrete [uvalue]s
                    2: That concrete [uvalue] do not contain any operators, i.e. are already fully reduced
                  *)
                 (* TODO: recursively convert dvalue to uvalue with evaluation*)
  (*
  | UVALUE_IBinop iop v1 v2                => ret (DVALUE_IBinop iop v1 v2)
  | UVALUE_ICmp cmp v1 v2                  => ret (DVALUE_ICmp cmp v1 v2)
  | UVALUE_FBinop fop fm v1 v2             => ret (DVALUE_FBinop fop fm v1 v2)
  | UVALUE_FCmp cmp v1 v2                  => ret (DVALUE_FCmp cmp v1 v2)
  | UVALUE_Conversion conv v t_to          => ret (DVALUE_Conversion conv v t_to)
  | UVALUE_GetElementPtr t ptrval idxs     => ret (DVALUE_GetElementPtr t ptrval idxs)
  | UVALUE_ExtractElement vec idx          => ret (DVALUE_ExtractElement vec idx)
  | UVALUE_InsertElement vec elt idx       => ret (DVALUE_InsertElement vec elt idx)
  | UVALUE_ShuffleVector vec1 vec2 idxmask => ret (DVALUE_ShuffleVector vec1 vec2 idxmask)
  | UVALUE_ExtractValue vec idxs           => ret (DVALUE_ExtractValue vec idxs)
  | UVALUE_InsertValue vec elt idxs        => ret (DVALUE_InsertValue vec elt idxs)
  | UVALUE_Select cnd v1 v2                => ret (DVALUE_Select cnd v1 v2)
   *)
  end.


Lemma list_cons_app :
  forall {A} (x : A) l, x :: l = [x] ++ l.
Proof.
  cbn. reflexivity.
Qed.

Lemma uvalue_to_dvalue_of_dvalue_to_uvalue :
  forall (d : dvalue),
    uvalue_to_dvalue (dvalue_to_uvalue d) = inr d.
Proof.
  intros.
  induction d using @dvalue_ind'; auto.
  - cbn. induction fields. cbn. reflexivity.
    assert (forall u : dvalue,
               In u fields ->
               uvalue_to_dvalue (dvalue_to_uvalue u) = inr u).
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
               uvalue_to_dvalue (dvalue_to_uvalue u) = inr u).
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
               uvalue_to_dvalue (dvalue_to_uvalue u) = inr u).
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
               uvalue_to_dvalue (dvalue_to_uvalue u) = inr u).
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
  | UVALUE_Double x => true
  | UVALUE_Float x => true
  | UVALUE_Undef t => false
  | UVALUE_Poison => true
  | UVALUE_None => true
  | UVALUE_Struct fields => allb is_concrete fields
  | UVALUE_Packed_struct fields => allb is_concrete fields
  | UVALUE_Array elts => allb is_concrete elts
  | UVALUE_Vector elts => allb is_concrete elts
  | _ => false
  (* | UVALUE_IBinop iop v1 v2 => allb is_concrete [v1 ; v2] *)
  (* | UVALUE_ICmp cmp v1 v2 => allb is_concrete [v1 ; v2] *)
  (* | UVALUE_FBinop fop fm v1 v2 => allb is_concrete [v1 ; v2] *)
  (* | UVALUE_FCmp cmp v1 v2 => allb is_concrete [v1 ; v2] *)
  (* | UVALUE_Conversion conv v t_to => is_concrete v *)
  (* | UVALUE_GetElementPtr t ptrval idxs => allb is_concrete (ptrval :: idxs) *)
  (* | UVALUE_ExtractElement vec idx => allb is_concrete [vec ; idx] *)
  (* | UVALUE_InsertElement vec elt idx => allb is_concrete [vec ; elt ; idx] *)
  (* | UVALUE_ShuffleVector vec1 vec2 idxmask => allb is_concrete [vec1 ; vec2 ; idxmask] *)
  (* | UVALUE_ExtractValue vec idxs => is_concrete vec *)
  (* | UVALUE_InsertValue vec elt idxs => allb is_concrete [vec ; elt] *)
  (* | UVALUE_Select cnd v1 v2 => allb is_concrete [cnd ; v1 ; v2] *)
  end.

(*
(* YZ: TODO: need a more general induction principle over uvalue to prove this due to Structs/Arrays/Vectors *)
Lemma uvalue_to_dvalue_is_concrete: forall uv,
    is_concrete uv = true <-> exists v, uvalue_to_dvalue uv = inr v.
Proof.
  induction uv using uvalue_ind'; simpl; split; intros HX;
    first [easy | eexists; reflexivity  | destruct HX; easy | idtac].
  - exists (match (map_monad uvalue_to_dvalue fields) with
       | inl _ => DVALUE_None
       | inr v0 => DVALUE_Struct v0
       end).
    admit.
  - 
Admitted.  
*)


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
     | inl e => opu uv1 (dvalue_to_uvalue dv2)
     | inr a => a
     end.

Definition uvalue_to_dvalue_uop {A : Type}
           (opu : uvalue -> A) (opd : dvalue -> A) (uv : uvalue) : A :=
  let ma := dv <- uvalue_to_dvalue uv ;; ret (opd dv)
  in match ma with
     | inl e => opu uv
     | inr a => a
     end.

(* TODO: define [refines : uvalue -> dvalue -> Prop] which characterizes the nondeterminism of undef values *)

Section hiding_notation.
  Local Open Scope sexp_scope.

  Fixpoint serialize_dvalue' (dv:dvalue): sexp :=
    match dv with
    | DVALUE_Addr a => Atom "address" (* TODO: insist that memory models can print addresses? *)
    | DVALUE_I1 x => Atom "dvalue(i1)"
    | DVALUE_I8 x => Atom "dvalue(i8)"
    | DVALUE_I32 x => Atom "dvalue(i32)"
    | DVALUE_I64 x => Atom "dvalue(i64)"
    | DVALUE_Double x => Atom "dvalue(double)"
    | DVALUE_Float x => Atom "dvalue(float)"
    | DVALUE_Poison => Atom "poison"
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

  Global Instance serialize_dvalue : Serialize dvalue := serialize_dvalue'.

  Fixpoint serialize_uvalue' (pre post: string) (uv:uvalue): sexp :=
    match uv with
    | UVALUE_Addr a => Atom (pre ++ "address" ++ post)%string (* TODO: insist that memory models can print addresses? *)
    | UVALUE_I1 x => Atom (pre ++ "uvalue(i1)" ++ post)%string
    | UVALUE_I8 x => Atom (pre ++ "uvalue(i8)" ++ post)%string
    | UVALUE_I32 x => Atom (pre ++ "uvalue(i32)" ++ post)%string
    | UVALUE_I64 x => Atom (pre ++ "uvalue(i64)" ++ post)%string
    | UVALUE_Double x => Atom (pre ++ "uvalue(double)" ++ post)%string
    | UVALUE_Float x => Atom (pre ++ "uvalue(float)" ++ post)%string
    | UVALUE_Poison => Atom (pre ++ "poison" ++ post)%string
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
    (* | UVALUE_Conversion       (conv:conversion_type) (v:uvalue) (t_to:dtyp) *)
    (* | UVALUE_GetElementPtr    (t:dtyp) (ptrval:uvalue) (idxs:list (uvalue)) (* TODO: do we ever need this? GEP raises an event? *) *)
    (* | UVALUE_ExtractElement   (vec: uvalue) (idx: uvalue) *)
    (* | UVALUE_InsertElement    (vec: uvalue) (elt:uvalue) (idx:uvalue) *)
    (* | UVALUE_ShuffleVector    (vec1:uvalue) (vec2:uvalue) (idxmask:uvalue) *)
    (* | UVALUE_ExtractValue     (vec:uvalue) (idxs:list int) *)
    (* | UVALUE_InsertValue      (vec:uvalue) (elt:uvalue) (idxs:list int) *)
    (* | UVALUE_Select           (cnd:uvalue) (v1:uvalue) (v2:uvalue) *)
    | _ => Atom "TODO: show_uvalue"
    end.

  Global Instance serialize_uvalue : Serialize uvalue := serialize_uvalue' "" "".

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
    | DVALUE_Poison, DVALUE_Poison => true
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
    | DVALUE_Double x1, DVALUE_Double x2 => _
    | DVALUE_Float x1, DVALUE_Float x2 => _
    | DVALUE_Poison, DVALUE_Poison => _
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
    - destruct (Float.eq_dec x1 x2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (Float32.eq_dec x1 x2).
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

  Global Instance eq_dec_dvalue : RelDec (@eq dvalue) := RelDec_from_dec (@eq dvalue) (@dvalue_eq_dec).
  Global Instance eqv_dvalue : Eqv dvalue := (@eq dvalue).
  Hint Unfold eqv_dvalue : core.
End DecidableEquality.

(* TODO: include Undefined values in this way? i.e. Undef is really a predicate on values
   Note: this isn't correct because it won't allow for undef fields of a struct or elts of an array
Inductive dvalue' : Set :=
| DVALUE_Undef (p:dvalue -> bool) (* TODO: used to include type information. is it necessary? (t:dtyp)  *)
| DVALUE_Val (d:dvalue).
*)

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
    eq : I -> I -> bool;
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


  Global Instance VInt1 : VInt Int1.int :=
  {
    (* Comparisons *)
    eq := Int1.eq;
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


  Global Instance VInt8 : VInt Int8.int :=
  {
    (* Comparisons *)
    eq := Int8.eq;
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


  Global Instance VInt32 : VInt Int32.int :=
  {
    (* Comparisons *)
    eq := Int32.eq;
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

  Global Instance VInt64 : VInt Int64.int :=
  {
    (* Comparisons *)
    eq := Int64.eq;
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

  Definition undef_i1  := UVALUE_Undef (DTYPE_I 1).
  Definition undef_i8  := UVALUE_Undef (DTYPE_I 8).
  Definition undef_i32 := UVALUE_Undef (DTYPE_I 32).
  Definition undef_i64 := UVALUE_Undef (DTYPE_I 64).
  Definition undef_int {Int} `{VInt Int}  := UVALUE_Undef (DTYPE_I (Z.of_nat bitwidth)).

  Definition to_uvalue {Int} `{VInt Int} (i : Int) : uvalue := dvalue_to_uvalue (to_dvalue i).

  (* Arithmetic Operations ---------------------------------------------------- *)
  Section ARITHMETIC.

    (* Evaluate integer opererations to get a dvalue.

     These operations are between VInts, which are "vellvm"
     integers. This is a typeclass that wraps all of the integer
     operations that we use for integer types with different bitwidths.

     SAZ: The "undef" here should refer to undefined behavior, not UVALUE_Undef, right?
     *)
    Definition eval_int_op {Int} `{VInt Int} (iop:ibinop) (x y: Int) : undef dvalue :=
      match iop with
      (* Following to cases are probably right since they use CompCert *)
      | Add nuw nsw =>
        ret (if orb (andb nuw (eq (add_carry x y zero) one))
                    (andb nsw (eq (add_overflow x y zero) one))
             then DVALUE_Poison else to_dvalue (add x y))

    | Sub nuw nsw =>
      ret (if orb (andb nuw (eq (sub_borrow x y zero) one))
                  (andb nsw (eq (sub_overflow x y zero) one))
           then DVALUE_Poison else to_dvalue (sub x y))

    | Mul nuw nsw =>
      (* I1 mul can't overflow, just based on the 4 possible multiplications. *)
      if (bitwidth ~=? 1)%nat then ret (to_dvalue (mul x y))
      else
        let res := mul x y in
        let res_s' := (signed x) * (signed y) in
        if orb (andb nuw ((unsigned x) * (unsigned y) >?
                      unsigned res))
             (andb nsw (orb (min_signed >? res_s')
                            (res_s' >? max_signed)))
      then ret DVALUE_Poison else ret (to_dvalue res)

    | Shl nuw nsw =>
      let bz := Z.of_nat bitwidth in
      let res := shl x y in
      let res_u := unsigned res in
      let res_u' := Z.shiftl (unsigned x) (unsigned y) in
      (* Unsigned shift x right by bitwidth - y. If shifted x != sign bit * (2^y - 1),
         then there is overflow. *)
      if (unsigned y) >=? bz then ret DVALUE_Poison
      else if orb (andb nuw (res_u' >? res_u))
                  (andb nsw (negb (Z.shiftr (unsigned x)
                                            (bz - unsigned y)
                                   =? (unsigned (negative res))
                                      * (Z.pow 2 (unsigned y) - 1))))
           then ret DVALUE_Poison else ret (to_dvalue res)

    | UDiv ex =>
      if (unsigned y =? 0)
      then failwith "Unsigned division by 0."
      else if andb ex (negb ((unsigned x) mod (unsigned y) =? 0))
           then ret DVALUE_Poison
           else ret (to_dvalue (divu x y))

    | SDiv ex =>
      (* What does signed i1 mean? *)
      if (signed y =? 0)
      then failwith "Signed division by 0."
      else if andb ex (negb ((signed x) mod (signed y) =? 0))
           then ret DVALUE_Poison
           else ret (to_dvalue (divs x y))

    | LShr ex =>
      let bz := Z.of_nat bitwidth in
      if (unsigned y) >=? bz then ret DVALUE_Poison
      else if andb ex (negb ((unsigned x)
                               mod (Z.pow 2 (unsigned y)) =? 0))
           then ret DVALUE_Poison else ret (to_dvalue (shru x y))

    | AShr ex =>
      let bz := Z.of_nat bitwidth in
      if (unsigned y) >=? bz then ret DVALUE_Poison
      else if andb ex (negb ((unsigned x)
                               mod (Z.pow 2 (unsigned y)) =? 0))
           then ret DVALUE_Poison else ret (to_dvalue (shr x y))

    | URem =>
      if unsigned y =? 0
      then failwith "Unsigned mod 0."
      else ret (to_dvalue (modu x y))

    | SRem =>
      if signed y =? 0
      then failwith "Signed mod 0."
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
  Definition integer_op (bits:Z) (iop:ibinop) (x y:inttyp bits) : undef_or_err dvalue :=
    match bits, x, y with
    | 1, x, y  => lift (eval_int_op iop x y)
    | 8, x, y  => lift (eval_int_op iop x y)
    | 32, x, y => lift (eval_int_op iop x y)
    | 64, x, y => lift (eval_int_op iop x y)
    | _, _, _  => failwith "unsupported bitsize"
    end.
  Arguments integer_op _ _ _ _ : simpl nomatch.

  (* Convert written integer constant to corresponding integer with bitsize bits.
     Takes the integer modulo 2^bits. *)
  Definition coerce_integer_to_int (bits:Z) (i:Z) : undef_or_err dvalue :=
    match bits with
    | 1  => ret (DVALUE_I1 (repr i))
    | 8  => ret (DVALUE_I8 (repr i))
    | 32 => ret (DVALUE_I32 (repr i))
    | 64 => ret (DVALUE_I64 (repr i))
    | _  => failwith "unsupported integer size"
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
  (* CB TODO: Should this do anything for undef? *)

  (*
    match iop with
    | UDiv ex =>
      if (unsigned y =? 0)
      then raiseUB "Unsigned division by 0."
      else if andb ex (negb ((unsigned x) mod (unsigned y) =? 0))
           then ret DVALUE_Poison
           else ret (to_dvalue (divu x y))

    | SDiv ex =>
      (* What does signed i1 mean? *)
      if (signed y =? 0)
      then raiseUB "Signed division by 0."
      else if andb ex (negb ((signed x) mod (signed y) =? 0))
           then ret DVALUE_Poison
           else ret (to_dvalue (divs x y))

    | URem =>
      if unsigned y =? 0
      then raiseUB "Unsigned mod 0."
      else ret (to_dvalue (modu x y))

    | SRem =>
      if signed y =? 0
      then raiseUB "Signed mod 0."
      else ret (to_dvalue (mods x y))
    | _ =>
 *)


  (* TODO: make work with undef ??? Maybe this is all dvalues? *)
  Definition eval_iop_integer_h iop v1 v2 : undef_or_err dvalue :=
    match v1, v2 with
    | DVALUE_I1 i1, DVALUE_I1 i2    => lift (eval_int_op iop i1 i2)
    | DVALUE_I8 i1, DVALUE_I8 i2    => lift (eval_int_op iop i1 i2)
    | DVALUE_I32 i1, DVALUE_I32 i2  => lift (eval_int_op iop i1 i2)
    | DVALUE_I64 i1, DVALUE_I64 i2  => lift (eval_int_op iop i1 i2)
    | DVALUE_Poison, _              => lift (ret DVALUE_Poison)
    | _, DVALUE_Poison              => lift (ret DVALUE_Poison)
    | _, _                          => failwith "ill_typed-iop"
    end.
  Arguments eval_iop_integer_h _ _ _ : simpl nomatch.

  (* I split the definition between the vector and other evaluations because
     otherwise eval_iop should be recursive to allow for vector calculations,
     but coq can't find a fixpoint. *)
  (* SAZ: Here is where we want to add the case distinction  for uvalues

       - this should check for "determined" uvalues and then use eval_iop_integer_h
         otherwise leave the op symbolic

       - this should use the inclusion of dvalue into uvalue in the case that
         eval_iop_integer_h is calle

   *)

  Definition eval_iop iop v1 v2 : undef_or_err dvalue :=
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

  Definition eval_icmp icmp v1 v2 : undef_or_err dvalue :=
    match v1, v2 with
    | DVALUE_I1 i1, DVALUE_I1 i2 => ret (eval_int_icmp icmp i1 i2)
    | DVALUE_I8 i1, DVALUE_I8 i2 => ret (eval_int_icmp icmp i1 i2)
    | DVALUE_I32 i1, DVALUE_I32 i2 => ret (eval_int_icmp icmp i1 i2)
    | DVALUE_I64 i1, DVALUE_I64 i2 => ret (eval_int_icmp icmp i1 i2)
    | DVALUE_Poison, DVALUE_Poison => ret DVALUE_Poison
    | DVALUE_Poison, _ => if is_DVALUE_IX v2 then ret DVALUE_Poison else failwith "ill_typed-iop"
    | _, DVALUE_Poison => if is_DVALUE_IX v1 then ret DVALUE_Poison else failwith "ill_typed-iop"
    | _, _ => failwith "ill_typed-icmp"
    end.
  Arguments eval_icmp _ _ _ : simpl nomatch.

  Definition double_op (fop:fbinop) (v1:ll_double) (v2:ll_double) : undef_or_err dvalue :=
    match fop with
    | FAdd => ret (DVALUE_Double (Float.add v1 v2))
    | FSub => ret (DVALUE_Double (Float.sub v1 v2))
    | FMul => ret (DVALUE_Double (Float.mul v1 v2))
    | FDiv => if (Float.eq_dec v2 Float.zero)
              then lift (raise "Signed division by 0.")
              else ret (DVALUE_Double (Float.div v1 v2))
    | FRem => failwith "unimplemented double operation"
    end.

  Definition float_op (fop:fbinop) (v1:ll_float) (v2:ll_float) : undef_or_err dvalue :=
    match fop with
    | FAdd => ret (DVALUE_Float (Float32.add v1 v2))
    | FSub => ret (DVALUE_Float (Float32.sub v1 v2))
    | FMul => ret (DVALUE_Float (Float32.mul v1 v2))
    | FDiv => if (Float32.eq_dec v2 Float32.zero)
              then lift (raise "Signed division by 0.")
              else ret (DVALUE_Float (Float32.div v1 v2))
    | FRem => failwith "unimplemented float operation"
    end.

  Definition eval_fop (fop:fbinop) (v1:dvalue) (v2:dvalue) : undef_or_err dvalue :=
    match v1, v2 with
    | DVALUE_Float f1, DVALUE_Float f2   => float_op fop f1 f2
    | DVALUE_Double d1, DVALUE_Double d2 => double_op fop d1 d2
    | DVALUE_Poison, _                   => ret DVALUE_Poison
    | _, DVALUE_Poison                   => ret DVALUE_Poison
    | _, _                               => failwith ("ill_typed-fop: " ++ (to_string fop) ++ " " ++ (to_string v1) ++ " " ++ (to_string v2))
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

  Definition eval_fcmp (fcmp:fcmp) (v1:dvalue) (v2:dvalue) : undef_or_err dvalue :=
    match v1, v2 with
    | DVALUE_Float f1, DVALUE_Float f2 => ret (float_cmp fcmp f1 f2)
    | DVALUE_Double f1, DVALUE_Double f2 => ret (double_cmp fcmp f1 f2)
    | DVALUE_Poison, DVALUE_Poison => ret DVALUE_Poison
    | DVALUE_Poison, DVALUE_Double _ => ret DVALUE_Poison
    | DVALUE_Poison, DVALUE_Float _ => ret DVALUE_Poison
    | DVALUE_Double _, DVALUE_Poison => ret DVALUE_Poison
    | DVALUE_Float _, DVALUE_Poison => ret DVALUE_Poison
    | _, _ => failwith "ill_typed-fcmp"
    end.

  End ARITHMETIC.

  (* Same deal as above with the helper *)
  (* The pattern matching generates hundreds of subgoals, hence the factorization of the typeclass inference *)
  Definition eval_select_h (cnd : dvalue) (v1 v2 : uvalue) : undef_or_err uvalue :=
    let failwith_local := (@failwith _ undef_or_err (Monad_eitherT string Monad_err) (Exception_eitherT string Monad_err))
    in
    let ret_local := (@ret undef_or_err (Monad_eitherT string Monad_err) uvalue)
    in
    match v1, v2 with
    | UVALUE_Poison, _ => ret_local UVALUE_Poison
    | _, UVALUE_Poison => ret_local UVALUE_Poison
    | _, _ =>
      match cnd with
      | DVALUE_I1 i =>
        ret_local (if Int1.unsigned i =? 1 then v1 else v2)
      | DVALUE_Poison => ret_local UVALUE_Poison
      | _ => failwith_local "ill_typed select"
      end
    end.

  Definition eval_select cnd v1 v2 : undef_or_err uvalue :=
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
  Definition index_into_str (v:uvalue) (idx:LLVMAst.int) : undef_or_err uvalue :=
    let fix loop elts i :=
        match elts with
        | [] => failwith "index out of bounds"
        | h :: tl =>
          if idx =? 0 then ret h else loop tl (i-1)
        end in
    match v with
    | UVALUE_Struct f => loop f idx
    | UVALUE_Array e => loop e idx
    | _ => failwith "invalid aggregate data"
    end.
  Arguments index_into_str _ _ : simpl nomatch.

  (* Helper function for inserting into a structured datatype for insertvalue *)
  Definition insert_into_str (str:dvalue) (v:dvalue) (idx:LLVMAst.int) : undef_or_err dvalue :=
    let fix loop (acc elts:list dvalue) (i:LLVMAst.int) :=
        match elts with
        | [] => failwith "index out of bounds"
        | h :: tl =>
          if idx =? 0 then ret (acc ++ (v :: tl))
          else loop (acc ++ [h]) tl (i-1)
        end%list in
    match str with
    | DVALUE_Struct f =>
      v <- (loop [] f idx) ;;
      ret (DVALUE_Struct v)

    | DVALUE_Array e =>
      v <- (loop [] e idx) ;;
      ret (DVALUE_Array v)

    | _ => failwith "invalid aggregate data"
    end.
  Arguments insert_into_str _ _ _ : simpl nomatch.

(*  ------------------------------------------------------------------------- *)

  (* Interpretation of [uvalue] in terms of sets of [dvalue].
     Essentially used to implemenmt the handler for [pick], but also required to
     define some predicates passed as arguments to the [pick] events, hence why
     it's defined here.
   *)

  (* Poison not included because of concretize *)
  Inductive dvalue_has_dtyp : dvalue -> dtyp -> Prop :=
  | DVALUE_Addr_typ   : forall a, dvalue_has_dtyp (DVALUE_Addr a) DTYPE_Pointer
  | DVALUE_I1_typ     : forall x, dvalue_has_dtyp (DVALUE_I1 x) (DTYPE_I 1)
  | DVALUE_I8_typ     : forall x, dvalue_has_dtyp (DVALUE_I8 x) (DTYPE_I 8)
  | DVALUE_I32_typ    : forall x, dvalue_has_dtyp (DVALUE_I32 x) (DTYPE_I 32)
  | DVALUE_I64_typ    : forall x, dvalue_has_dtyp (DVALUE_I64 x) (DTYPE_I 64)
  | DVALUE_IX_typ     : forall x, ~IX_supported x -> dvalue_has_dtyp DVALUE_None (DTYPE_I x)
  | DVALUE_Double_typ : forall x, dvalue_has_dtyp (DVALUE_Double x) DTYPE_Double
  | DVALUE_Float_typ  : forall x, dvalue_has_dtyp (DVALUE_Float x) DTYPE_Float
  | DVALUE_Half_typ   : forall x, dvalue_has_dtyp (DVALUE_Float x) DTYPE_Half (* ??? *)
  | DVALUE_X86_fp80   : forall x, dvalue_has_dtyp (DVALUE_Float x) DTYPE_X86_fp80 (* ??? *)
  | DVALUE_Fp128      : forall x, dvalue_has_dtyp (DVALUE_Float x) DTYPE_Fp128 (* ??? *)
  | DVALUE_Ppc_fp128  : forall x, dvalue_has_dtyp (DVALUE_Float x) DTYPE_Ppc_fp128 (* ??? *)
  | DVALUE_Metadata   : dvalue_has_dtyp DVALUE_None DTYPE_Metadata (* ??? *)
  | DVALUE_X86_mmx    : dvalue_has_dtyp DVALUE_None DTYPE_X86_mmx (* ??? *)
  | DVALUE_Opaque     : dvalue_has_dtyp DVALUE_None DTYPE_Opaque (* ??? *)
  | DVALUE_None_typ   : dvalue_has_dtyp DVALUE_None DTYPE_Void

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

  (* CB TODO: Do we have to exclude mmx? "There are no arrays, vectors or constants of this type" *)
  | DVALUE_Array_typ :
      forall xs sz dt,
        Forall (fun x => dvalue_has_dtyp x dt) xs ->
        length xs = sz ->
        dvalue_has_dtyp (DVALUE_Array xs) (DTYPE_Array (Z.of_nat sz) dt)

  | DVALUE_Vector_typ :
      forall xs sz dt,
        Forall (fun x => dvalue_has_dtyp x dt) xs ->
        length xs = sz ->
        vector_dtyp dt ->
        dvalue_has_dtyp (DVALUE_Vector xs) (DTYPE_Vector (Z.of_nat sz) dt)
  .

  Section dvalue_has_dtyp_ind.
    Variable P : dvalue -> dtyp -> Prop.
    Hypothesis IH_Addr           : forall a, P (DVALUE_Addr a) DTYPE_Pointer.
    Hypothesis IH_I1             : forall x, P (DVALUE_I1 x) (DTYPE_I 1).
    Hypothesis IH_I8             : forall x, P (DVALUE_I8 x) (DTYPE_I 8).
    Hypothesis IH_I32            : forall x, P (DVALUE_I32 x) (DTYPE_I 32).
    Hypothesis IH_I64            : forall x, P (DVALUE_I64 x) (DTYPE_I 64).
    Hypothesis IH_IX             : forall x, ~IX_supported x -> P DVALUE_None (DTYPE_I x).
    Hypothesis IH_Double         : forall x, P (DVALUE_Double x) DTYPE_Double.
    Hypothesis IH_Float          : forall x, P (DVALUE_Float x) DTYPE_Float.
    Hypothesis IH_Half           : forall x, P (DVALUE_Float x) DTYPE_Half. (* ??? *)
    Hypothesis IH_X86_fp80       : forall x, P (DVALUE_Float x) DTYPE_X86_fp80. (* ??? *)
    Hypothesis IH_Fp128          : forall x, P (DVALUE_Float x) DTYPE_Fp128. (* ??? *)
    Hypothesis IH_Ppc_fp128      : forall x, P (DVALUE_Float x) DTYPE_Ppc_fp128. (* ??? *)
    Hypothesis IH_Metadata       : P DVALUE_None DTYPE_Metadata. (* ??? *)
    Hypothesis IH_X86_mmx        : P DVALUE_None DTYPE_X86_mmx. (* ??? *)
    Hypothesis IH_Opaque         : P DVALUE_None DTYPE_Opaque. (* ??? *)
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
        Datatypes.length xs = sz -> P (DVALUE_Array xs) (DTYPE_Array (Z.of_nat sz) dt).

    Hypothesis IH_Vector : forall (xs : list dvalue) (sz : nat) (dt : dtyp)
                             (IH : forall x, In x xs -> P x dt)
                             (IHdtyp : forall x, In x xs -> dvalue_has_dtyp x dt),
        Datatypes.length xs = sz ->
        vector_dtyp dt -> P (DVALUE_Vector xs) (DTYPE_Vector (Z.of_nat sz) dt).

    Lemma dvalue_has_dtyp_ind' : forall (dv:dvalue) (dt:dtyp) (TYP: dvalue_has_dtyp dv dt), P dv dt.
      fix IH 3.
      intros dv dt TYP.
      destruct TYP.
      - apply IH_Addr.
      - apply IH_I1.
      - apply IH_I8.
      - apply IH_I32.
      - apply IH_I64.
      - apply IH_IX. assumption.
      - apply IH_Double.
      - apply IH_Float.
      - apply IH_Half.
      - apply IH_X86_fp80.
      - apply IH_Fp128.
      - apply IH_Ppc_fp128.
      - apply IH_Metadata.
      - apply IH_X86_mmx.
      - apply IH_Opaque.
      - apply IH_None.
      - apply IH_Struct_nil.
      - apply (IH_Struct_cons TYP1 (IH f dt TYP1) TYP2 (IH (DVALUE_Struct fields) (DTYPE_Struct dts) TYP2)).
      - apply IH_Packed_Struct_nil.
      - apply (IH_Packed_Struct_cons TYP1 (IH f dt TYP1) TYP2 (IH (DVALUE_Packed_struct fields) (DTYPE_Packed_struct dts) TYP2)).
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

  Inductive concretize_u : uvalue -> undef_or_err dvalue -> Prop := 
  (* Concrete uvalue are contretized into their singleton *)
  | Pick_concrete             : forall uv (dv : dvalue), uvalue_to_dvalue uv = inr dv -> concretize_u uv (ret dv)
  | Pick_fail                 : forall uv v s, ~ (uvalue_to_dvalue uv = inr v)  -> concretize_u uv (lift (failwith s))
  (* Undef relates to all dvalue of the type *)
  | Concretize_Undef          : forall dt dv,
      dvalue_has_dtyp dv dt ->
      concretize_u (UVALUE_Undef dt) (ret dv)

  (* The other operations proceed non-deterministically *)
  | Concretize_IBinop : forall iop uv1 e1 uv2 e2,
      concretize_u uv1 e1 ->
      concretize_u uv2 e2 ->
      concretize_u (UVALUE_IBinop iop uv1 uv2)
                   (dv1 <- e1 ;;
                    dv2 <- e2 ;;
                    (eval_iop iop dv1 dv2))
  
  | Concretize_ICmp : forall cmp uv1 e1 uv2 e2 ,
      concretize_u uv1 e1 ->
      concretize_u uv2 e2 ->
      concretize_u (UVALUE_ICmp cmp uv1 uv2)
                   (dv1 <- e1 ;;
                    dv2 <- e2 ;;
                    eval_icmp cmp dv1 dv2)

  | Concretize_FBinop : forall fop fm uv1 e1 uv2 e2,
      concretize_u uv1 e1 ->
      concretize_u uv2 e2 ->
      concretize_u (UVALUE_FBinop fop fm uv1 uv2)
                   (dv1 <- e1 ;;
                    dv2 <- e2 ;;
                    eval_fop fop dv1 dv2)

  | Concretize_FCmp : forall cmp uv1 e1 uv2 e2,
      concretize_u uv1 e1 ->
      concretize_u uv2 e2 ->
      concretize_u (UVALUE_FCmp cmp uv1 uv2)
                   (dv1 <- e1 ;;
                    dv2 <- e2 ;;
                    eval_fcmp cmp dv1 dv2)

  | Concretize_Struct_Nil     : concretize_u (UVALUE_Struct []) (ret (DVALUE_Struct []))
  | Concretize_Struct_Cons    : forall u e us es,
      concretize_u u e ->
      concretize_u (UVALUE_Struct us) es ->
      concretize_u (UVALUE_Struct (u :: us))
                   (d <- e ;;
                    vs <- es ;;
                    match vs with
                    | (DVALUE_Struct ds) => ret (DVALUE_Struct (d :: ds))
                    | _ => failwith "illegal Struct Cons"
                    end)


  | Concretize_Packed_struct_Nil     : concretize_u (UVALUE_Packed_struct []) (ret (DVALUE_Packed_struct []))
  | Concretize_Packed_struct_Cons    : forall u e us es,
      concretize_u u e ->
      concretize_u (UVALUE_Packed_struct us) es ->
      concretize_u (UVALUE_Packed_struct (u :: us))
                   (d <- e ;;
                    vs <- es ;;
                    match vs with
                    | (DVALUE_Packed_struct ds) => ret (DVALUE_Packed_struct (d :: ds))
                    | _ => failwith "illegal Packed_struct cons"
                    end)

  | Concretize_Array_Nil :
      concretize_u (UVALUE_Array []) (ret (DVALUE_Array []))

  | Concretize_Array_Cons : forall u e us es,
      concretize_u u e ->
      concretize_u (UVALUE_Array us) es ->      
      concretize_u (UVALUE_Array (u :: us))
                   (d <- e ;;
                    vs <- es ;;
                    match vs with
                    | (DVALUE_Array ds) => ret (DVALUE_Array (d :: ds))
                    | _ => failwith "illegal Array cons"
                    end)

  | Concretize_Vector_Nil :
      concretize_u (UVALUE_Vector []) (ret (DVALUE_Vector []))

  | Concretize_Vector_Cons : forall u e us es,
      concretize_u u e ->
      concretize_u (UVALUE_Vector us) es ->      
      concretize_u (UVALUE_Vector (u :: us))
                   (d <- e ;;
                    vs <- es ;;
                    match vs with
                    | (DVALUE_Vector ds) => ret (DVALUE_Vector (d :: ds))
                    | _ => failwith "illegal Vector cons"
                    end)
  .

  Definition concretize (uv: uvalue) (dv : dvalue) := concretize_u uv (ret dv).

  
  (*
    YZ TODO: Not sure whether those can be uvalues, to figure out
  | Concretize_Conversion     : pickU (UVALUE_Conversion       _) (DVALUE_Conversion       _)
  | Concretize_GetElementPtr  : pickU (UVALUE_GetElementPtr    _) (DVALUE_GetElementPtr    _)
  | Concretize_ExtractElement : pickU (UVALUE_ExtractElement   _) (DVALUE_ExtractElement   _)
  | Concretize_InsertElement  : pickU (UVALUE_InsertElement    _) (DVALUE_InsertElement    _)
  | Concretize_ShuffleVector  : pickU (UVALUE_ShuffleVector    _) (DVALUE_ShuffleVector    _)
  | Concretize_ExtractValue   : pickU (UVALUE_ExtractValue     _) (DVALUE_ExtractValue     _)
  | Concretize_InsertValue    : pickU (UVALUE_InsertValue      _) (DVALUE_InsertValue      _)
  | Concretize_Select         : pickU (UVALUE_Select           _) (DVALUE_Select           _)
  .
   *)


End DVALUE.
