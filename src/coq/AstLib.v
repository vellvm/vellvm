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
     ZArith.ZArith List
     String Omega.
Require Import Vellvm.LLVMAst Vellvm.Util.
Require Import Equalities OrderedType OrderedTypeEx Compare_dec.
Require Import ExtLib.Core.RelDec ExtLib.Data.Z.
Require Import ExtLib.Programming.Eqv.
Require Import Ascii.
Import ListNotations.

Import EqvNotation.

(* Equalities --------------------------------------------------------------- *)
Instance eq_dec_int : RelDec (@eq int) := Data.Z.RelDec_zeq.
Instance eqv_int : Eqv int := (@eq int).

(* SAZ : These should be moved to part of the standard library, or at least to
   ExtLib *)
Module AsciiOrd <: UsualOrderedType.
  Definition t := ascii.
  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition lt (a b:ascii) := N.lt (N_of_ascii a) (N_of_ascii b).
  Lemma lt_trans : forall a b c:t, lt a b -> lt b c -> lt a c.
  Proof.
    intros a b c.
    unfold lt.
    apply N.lt_trans.
  Qed.
  Lemma lt_not_eq : forall a b:t, lt a b -> ~eq a b.
  Proof.
    intros a b H.
    unfold eq. unfold not. intros He. rewrite He in H.
    eapply N.lt_neq. unfold lt in H. apply H. reflexivity.
  Qed.

  Lemma N_of_ascii_inj : forall x y, N_of_ascii x = N_of_ascii y -> x = y.
  Proof.
    intros x y H.
    rewrite <- ascii_N_embedding.
    rewrite <- (@ascii_N_embedding x).
    rewrite H. reflexivity.
  Defined.

  Program Definition compare (x y: t) : Compare lt eq x y :=
    match N_as_OT.compare (N_of_ascii x) (N_of_ascii y) with
    | LT p => _
    | EQ p => _
    | GT p => _
    end.
  Next Obligation.
    apply LT. unfold lt. auto.
  Defined.
  Next Obligation.
    apply EQ. unfold eq. apply N_of_ascii_inj. auto.
  Defined.
  Next Obligation.
    apply GT. unfold lt. auto.
  Defined.

  Definition eq_dec := ascii_dec.
End AsciiOrd.

Module AsciiOrdFacts := OrderedTypeFacts(AsciiOrd).

Module StringOrd <: UsualOrderedType.
  Definition t := string.
  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Fixpoint lt (s1 s2:string) : Prop :=
    match s1, s2 with
    | EmptyString, EmptyString => False
    | EmptyString, String _ _ => True
    | String a s1', String b s2' =>
      match AsciiOrd.compare a b with
      | LT _ => True
      | EQ _ => lt s1' s2'
      | GT _ => False
      end
    | String _ _, EmptyString => False
    end.

  Lemma lt_trans : forall a b c : t, lt a b -> lt b c -> lt a c.
  Proof.
    induction a.
    - destruct b; destruct c; simpl; intros; try tauto.
    - destruct b; destruct c; simpl; intros; try tauto.
      destruct (AsciiOrd.compare a a1); try tauto.
      + destruct (AsciiOrd.compare a1 a2); try tauto.
        * AsciiOrdFacts.elim_comp; auto.
        * AsciiOrdFacts.elim_comp; auto.
      + destruct (AsciiOrd.compare a1 a2); try tauto.
        * AsciiOrdFacts.elim_comp; auto.
        * AsciiOrdFacts.elim_comp; auto.
          eapply IHa; eauto.
  Qed.

  Lemma lt_not_eq : forall a b:t, lt a b -> ~eq a b.
  Proof.
    induction a; intros b H He; unfold eq in He; subst.
    - unfold lt in H. destruct H.
    - simpl in H.
      destruct (AsciiOrd.compare a a); auto.
      apply AsciiOrd.lt_not_eq in l. apply l. AsciiOrdFacts.order.
      apply IHa in H. apply H. unfold eq. reflexivity.
  Qed.

  Program Fixpoint compare (s1 s2 : t) : Compare lt eq s1 s2 :=
    match s1, s2 with
    | EmptyString, EmptyString => _
    | EmptyString, String b s2' => _
    | String a s1', String b s2' =>
      match AsciiOrd.compare a b with
      | LT _ => _
      | EQ _ => match compare s1' s2' with
               | LT _ => _
               | EQ _ => _
               | GT _ => _
               end
      | GT _ => _
      end
    | String a s1', EmptyString => _
    end.
  Next Obligation.
    apply EQ. unfold eq. reflexivity.
  Defined.
  Next Obligation.
    apply LT. simpl. auto.
  Defined.
  Next Obligation.
    apply LT. simpl. rewrite <- Heq_anonymous. auto.
  Defined.
  Next Obligation.
    apply LT. simpl. rewrite <- Heq_anonymous0. auto.
  Defined.
  Next Obligation.
    apply EQ. simpl. unfold AsciiOrd.eq in wildcard'0. subst. unfold eq in e. subst. reflexivity.
  Defined.
  Next Obligation.
    apply GT. simpl. unfold AsciiOrd.eq in wildcard'0. subst.
    rewrite <- Heq_anonymous0. auto.
  Defined.
  Next Obligation.
    apply GT. simpl. AsciiOrdFacts.elim_comp_lt b a. auto.
  Defined.
  Next Obligation.
    apply GT. simpl. auto.
  Defined.

  Definition eq_dec := string_dec.
End StringOrd.
Module StringOrdFacts := OrderedTypeFacts(StringOrd).


Module RawIDOrd <: UsualOrderedType.
  Definition t := raw_id.
  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  (* Anon < Name < Raw *)
  Definition lt (x:t) (y:t) : Prop :=
    match x,y with
    | Anon n1, Anon n2 => (n1 < n2)%Z
    | Name s1, Name s2 => StringOrd.lt s1 s2
    | Raw n1, Raw n2 => (n1 < n2)%Z
    | Anon _, _ => True
    | Name _, Raw _ => True
    | _, _ => False
    end.

  Lemma lt_trans : forall a b c : t, lt a b -> lt b c -> lt a c.
  Proof.
    destruct a; destruct b; destruct c; simpl; intros H1 H2; intuition.
    - eapply StringOrd.lt_trans; eauto.
  Qed.

  Lemma lt_not_eq : forall a b:t, lt a b -> ~eq a b.
  Proof.
    destruct a; destruct b; simpl; intros H He; inversion He; subst.
    - apply StringOrd.lt_not_eq in H. apply H. unfold StringOrd.eq. reflexivity.
    - apply Z_as_OT.lt_not_eq in H. tauto.
    - apply Z_as_OT.lt_not_eq in H. tauto.
  Qed.

  Program Definition compare (x:t) (y:t) : Compare lt eq x y :=
    match x,y with
    | Anon n1, Anon n2 =>
      match Z_as_OT.compare n1 n2 with
      | LT _ => LT _
      | EQ _ => EQ _
      | GT _ => GT _
      end
    | Anon _, Name _ => LT _
    | Anon _, Raw _ => LT _
    | Name _, Anon _ => GT _
    | Name s1, Name s2 =>
      match StringOrd.compare s1 s2 with
      | LT _ => LT _
      | EQ _ => EQ _
      | GT _ => GT _
      end
    | Name _, Raw _ => LT _
    | Raw _, Anon _ => GT _
    | Raw _, Name _ => GT _
    | Raw n1, Raw n2 =>
      match Z_as_OT.compare n1 n2 with
      | LT _ => LT _
      | EQ _ => EQ _
      | GT _ => GT _
      end
    end.
  Next Obligation.
    unfold Z_as_OT.eq in wildcard'. subst. unfold eq. reflexivity.
  Defined.
  Next Obligation.
    unfold StringOrd.eq in wildcard'. subst. unfold eq. reflexivity.
  Defined.
  Next Obligation.
    unfold Z_as_OT.eq in wildcard'. subst. unfold eq. reflexivity.
  Defined.

  Definition eq_dec : forall (x y : t), {x = y} + {x <> y}.
    decide equality.
    - apply string_dec.
    - apply rel_dec_p.
    - apply rel_dec_p.
  Defined.

End RawIDOrd.

(* Module RawIDDec <: MiniDecidableType. *)
(*   Definition t := raw_id. *)
(*   Lemma eq_dec : forall (x y : raw_id), {x = y} + {x <> y}. *)
(*   Proof. *)
(*     decide equality. *)
(*     - destruct (string_dec s s0); tauto. *)
(*     - destruct (n == n0); tauto. *)
(*     - destruct (n == n0); tauto. *)
(*   Defined. *)
(* End RawIDDec. *)

(* Module RawID := Make_UDT(RawIDDec).  *)
Instance eq_dec_raw_id : RelDec (@eq raw_id) := RelDec_from_dec (@eq raw_id) RawIDOrd.eq_dec.
Instance eqv_raw_id : Eqv raw_id := (@eq raw_id).
Hint Unfold eqv_raw_id.

Module InstrIDDec <: MiniDecidableType.
  Definition t := instr_id.

  Lemma eq_dec : forall (x y : instr_id), {x = y} + {x <> y}.
  Proof.
    intros x y.
    destruct x as [xn | xn]; destruct y as [yn | yn].
    - destruct (xn ~=? yn). unfold eqv in e. unfold eqv_raw_id in e. subst. left. reflexivity.
      right. unfold not. intros. apply n. inversion H. unfold eqv. unfold eqv_raw_id. reflexivity.
    - right. unfold not. intros. inversion H.
    - right. unfold not. intros. inversion H.
    - destruct (xn ~=? yn).
      left. unfold eqv in e. unfold eqv_int in e. subst. reflexivity.
      right. unfold not. intros. apply n. inversion H. unfold eqv. unfold eqv_int. auto.
  Defined.
End InstrIDDec.
Module InstrID := Make_UDT(InstrIDDec).

Instance eq_dec_instr_id : RelDec (@eq instr_id) := RelDec_from_dec (@eq instr_id) InstrID.eq_dec.
Instance eqv_instr_id : Eqv instr_id := (@eq instr_id).

Module IdentDec <: MiniDecidableType.
  Definition t := ident.

  Lemma eq_dec : forall (x y : ident), {x = y} + {x <> y}.
  Proof.
    intros x y.
    destruct x as [xn | xn]; destruct y as [yn | yn].
    - destruct (xn ~=? yn). unfold eqv in e. unfold eqv_raw_id in e. subst. left. reflexivity.
      right. unfold not. intros. apply n. inversion H. unfold eqv. unfold eqv_raw_id. reflexivity.
    - right. unfold not. intros. inversion H.
    - right. unfold not. intros. inversion H.
    - destruct (xn ~=? yn).
      left. unfold eqv in e. unfold eqv_raw_id in e. subst.  reflexivity.
      right. unfold not. intros. apply n. inversion H. unfold eqv. unfold eqv_raw_id. auto.
  Defined.
End IdentDec.
Module Ident := Make_UDT(IdentDec).

Instance eq_dec_ident : RelDec (@eq ident) := RelDec_from_dec (@eq ident) Ident.eq_dec.
Instance eqv_ident : Eqv ident := (@eq ident).

(* Induction Principles ----------------------------------------------------- *)

Section TypInd.

Variable P : typ -> Prop.
Hypothesis IH_I          : forall sz, P (TYPE_I sz).
Hypothesis IH_Pointer    : forall t, P t -> P(TYPE_Pointer t).
Hypothesis IH_Void       : P(TYPE_Void).
Hypothesis IH_Half       : P(TYPE_Half).
Hypothesis IH_Float      : P(TYPE_Float).
Hypothesis IH_Double     : P(TYPE_Double).
Hypothesis IH_X86_fp80   : P(TYPE_X86_fp80).
Hypothesis IH_Fp128      : P(TYPE_Fp128).
Hypothesis IH_Ppc_fp128  : P(TYPE_Ppc_fp128).
Hypothesis IH_Metadata   : P(TYPE_Metadata).
Hypothesis IH_X86_mmx    : P(TYPE_X86_mmx).
Hypothesis IH_Array      : forall sz t, P t -> P(TYPE_Array sz t).
Hypothesis IH_Function   : forall ret args, P ret -> (forall u, In u args -> P u) -> P(TYPE_Function ret args).
Hypothesis IH_Struct     : forall fields, (forall u, In u fields -> P u) -> P(TYPE_Struct fields).
Hypothesis IH_Packed_struct : forall fields, (forall u, In u fields -> P u) -> P(TYPE_Packed_struct fields).
Hypothesis IH_Opaque     : P(TYPE_Opaque).
Hypothesis IH_Vector     : forall sz t, P t -> P(TYPE_Vector sz t).
Hypothesis IH_Identified : forall id, P(TYPE_Identified id).

Lemma typ_ind' : forall (t:typ), P t.
  fix IH 1.
  destruct t.
  - apply IH_I.
  - apply IH_Pointer. apply IH.
  - apply IH_Void.
  - apply IH_Half.
  - apply IH_Float.
  - apply IH_Double.
  - apply IH_X86_fp80.
  - apply IH_Fp128.
  - apply IH_Ppc_fp128.
  - apply IH_Metadata.
  - apply IH_X86_mmx.
  - apply IH_Array. apply IH.
  - apply IH_Function. apply IH.
    { revert args.
      fix IHargs 1. intros [|u args']. intros. inversion H.
      intros u' [<-|Hin]. apply IH. eapply IHargs. apply Hin.
    }
  - apply IH_Struct.
    { revert fields.
      fix IHfields 1. intros [|u fields']. intros. inversion H.
      intros u' [<-|Hin]. apply IH. eapply IHfields. apply Hin.
    }
  - apply IH_Packed_struct.
    { revert fields.
      fix IHfields 1. intros [|u fields']. intros. inversion H.
      intros u' [<-|Hin]. apply IH. eapply IHfields. apply Hin.
    }
  - apply IH_Opaque.
  - apply IH_Vector. apply IH.
  - apply IH_Identified.
Qed.

End TypInd.

Section ExpInd.
(*
| EXP_Ident   (id:ident)
| EXP_Integer (x:int)
| EXP_Float   (f:float)
| EXP_Bool    (b:bool)
| EXP_Null
| EXP_Zero_initializer
| EXP_Cstring (s:string)
| EXP_Undef
| EXP_Struct        (fields: list (typ * a))
| EXP_Packed_struct (fields: list (typ * a))
| EXP_Array         (elts: list (typ * a))
| EXP_Vector        (elts: list (typ * a))
| OP_IBinop           (iop:ibinop) (t:typ) (v1:a) (v2:a)
| OP_ICmp             (cmp:icmp)   (t:typ) (v1:a) (v2:a)
| OP_FBinop           (fop:fbinop) (fm:list fast_math) (t:typ) (v1:a) (v2:a)
| OP_FCmp             (cmp:fcmp)   (t:typ) (v1:a) (v2:a)
| OP_Conversion     (conv:conversion_type) (t_from:typ) (v:a) (t_to:typ)
| OP_GetElementPtr  (t:typ) (ptrval:(typ * a)) (idxs:list (typ * a))
| OP_ExtractElement (vec:(typ * a)) (idx:(typ * a))
| OP_InsertElement  (vec:(typ * a)) (elt:(typ * a)) (idx:(typ * a))
| OP_ShuffleVector  (vec1:(typ * a)) (vec2:(typ * a)) (idxmask:(typ * a))
| OP_ExtractValue   (vec:(typ * a)) (idxs:list int)
| OP_InsertValue    (vec:(typ * a)) (elt:(typ * a)) (idxs:list int)
| OP_Select         (cnd:(typ * a)) (v1:(typ * a)) (v2:(typ * a)) (* if * then * else *)
.

(* static values *)
Inductive value : Set :=
| SV : Expr value -> value.
 *)
  Variable T : Set.
  Variable P : (exp T) -> Prop.
  Hypothesis IH_Ident   : forall (id:ident), P ((EXP_Ident id)).
  Hypothesis IH_Integer : forall (x:int), P ((EXP_Integer x)).
  Hypothesis IH_Float   : forall (f:float32), P ((EXP_Float f)).
  Hypothesis IH_Double  : forall (f:float), P ((EXP_Double f)).
  Hypothesis IH_Hex     : forall (h:float), P ((EXP_Hex h)).
  Hypothesis IH_Bool    : forall (b:bool), P ((EXP_Bool b)).
  Hypothesis IH_Null    : P ((EXP_Null)).
  Hypothesis IH_Zero_initializer : P ((EXP_Zero_initializer)).
  Hypothesis IH_Cstring : forall (s:string), P ((EXP_Cstring s)).
  Hypothesis IH_Undef   : P ((EXP_Undef)).
  Hypothesis IH_Struct  : forall (fields: list (T * (exp T))), (forall p, In p fields -> P (snd p)) -> P ((EXP_Struct fields)).
  Hypothesis IH_Packed_struct : forall (fields: list (T * (exp T))), (forall p, In p fields -> P (snd p)) -> P ((EXP_Packed_struct fields)).
  Hypothesis IH_Array   : forall (elts: list (T * (exp T))), (forall p, In p elts -> P (snd p)) -> P ((EXP_Array elts)).
  Hypothesis IH_Vector  : forall (elts: list (T * (exp T))), (forall p, In p elts -> P (snd p)) -> P ((EXP_Vector elts)).
  Hypothesis IH_IBinop  : forall (iop:ibinop) (t:T) (v1:exp T) (v2:exp T), P v1 -> P v2 -> P ((OP_IBinop iop t v1 v2)).
  Hypothesis IH_ICmp    : forall (cmp:icmp)   (t:T) (v1:exp T) (v2:exp T), P v1 -> P v2 -> P ((OP_ICmp cmp t v1 v2)).
  Hypothesis IH_FBinop  : forall (fop:fbinop) (fm:list fast_math) (t:T) (v1:exp T) (v2:exp T), P v1 -> P v2 -> P ((OP_FBinop fop fm t v1 v2)).
  Hypothesis IH_FCmp    : forall (cmp:fcmp)   (t:T) (v1:exp T) (v2:exp T), P v1 -> P v2 -> P ((OP_FCmp cmp t v1 v2)).
  Hypothesis IH_Conversion : forall (conv:conversion_type) (t_from:T) (v:exp T) (t_to:T), P v -> P ((OP_Conversion conv t_from v t_to)).
  Hypothesis IH_GetElementPtr : forall (t:T) (ptrval:(T * exp T)) (idxs:list (T * exp T)),
      P (snd ptrval) -> (forall p, In p idxs -> P (snd p)) -> P ((OP_GetElementPtr t ptrval idxs)).
  Hypothesis IH_ExtractElement: forall (vec:(T * exp T)) (idx:(T * exp T)), P (snd vec) -> P (snd idx) -> P ((OP_ExtractElement vec idx)).
  Hypothesis IH_InsertElement : forall (vec:(T * exp T)) (elt:(T * exp T)) (idx:(T * exp T)),
      P (snd vec) -> P (snd elt) -> P (snd idx) -> P ((OP_InsertElement vec elt idx)).
  Hypothesis IH_ShuffleVector : forall (vec1:(T * exp T)) (vec2:(T * exp T)) (idxmask:(T * exp T)),
      P (snd vec1) -> P (snd vec2 ) -> P (snd idxmask) -> P ((OP_ShuffleVector vec1 vec2 idxmask)).
  Hypothesis IH_ExtractValue  : forall (vec:(T * exp T)) (idxs:list int), P (snd vec) -> P ((OP_ExtractValue vec idxs)).
  Hypothesis IH_InsertValue   : forall (vec:(T * exp T)) (elt:(T * exp T)) (idxs:list int), P (snd vec) -> P (snd elt) -> P ((OP_InsertValue vec elt idxs)).
  Hypothesis IH_Select        : forall (cnd:(T * exp T)) (v1:(T * exp T)) (v2:(T * exp T)), P (snd cnd) -> P (snd v1) -> P (snd v2) -> P ((OP_Select cnd v1 v2)).

  Lemma exp_ind' : forall (v:exp T), P v.
    fix IH 1.
    destruct v.
    - apply IH_Ident.
    - apply IH_Integer.
    - apply IH_Float.
    - apply IH_Double.
    - apply IH_Hex.
    - apply IH_Bool.
    - apply IH_Null.
    - apply IH_Zero_initializer.
    - apply IH_Cstring.
    - apply IH_Undef.
    - apply IH_Struct.
      { revert fields.
        fix IHfields 1. intros [|u fields']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IHfields. apply Hin.
      }
    - apply IH_Packed_struct.
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
    - apply IH_IBinop. apply IH. apply IH.
    - apply IH_ICmp. apply IH. apply IH.
    - apply IH_FBinop. apply IH. apply IH.
    - apply IH_FCmp. apply IH. apply IH.
    - apply IH_Conversion. apply IH.
    - apply IH_GetElementPtr. apply IH.
      { revert idxs.
        fix IHidxs 1. intros [|u idxs']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IHidxs. apply Hin.
      }
    - apply IH_ExtractElement. apply IH. apply IH.
    - apply IH_InsertElement. apply IH. apply IH. apply IH.
    - apply IH_ShuffleVector. apply IH. apply IH. apply IH.
    - apply IH_ExtractValue. apply IH.
    - apply IH_InsertValue. apply IH. apply IH.
    - apply IH_Select.  apply IH. apply IH. apply IH.
  Qed.
End ExpInd.


(* Display *)
Require Import Ceres.Ceres.

Section hiding_notation.
  Local Open Scope sexp_scope.

  Definition serialize_raw_id (prefix: string): Serialize raw_id :=
    fun r =>
      match r with
      | Name s => Atom (prefix ++ s)%string
      | Anon n => to_sexp n
      | LLVMAst.Raw n => Atom ("_RAW_" ++ to_string n)%string
      end.

  Global Instance serialize_raw_id': Serialize raw_id := serialize_raw_id "".

  Global Instance serialize_ident : Serialize ident :=
    fun id =>
      match id with
      | ID_Global r => serialize_raw_id "@" r
      | ID_Local  r => serialize_raw_id "%" r
      end.

  Global Instance serialize_instr_id : Serialize instr_id :=
    fun ins =>
      match ins with
      | IId id => to_sexp id
      | IVoid n => Atom ("void<" ++ to_string n ++ ">")%string
      end.

  Global Instance serialize_ibinop : Serialize ibinop :=
    fun binop =>
      match binop with
      | Add nuw nsw => Atom "add"
      | Sub nuw nsw => Atom "sub"
      | Mul nuw nsw => Atom "mul"
      | Shl nuw nsw => Atom "shl"
      | UDiv flag => Atom "udiv"
      | SDiv flag => Atom "sdiv"
      | LShr flag => Atom "lshr"
      | AShr flag => Atom "ashr"
      | URem | SRem => Atom "rem"
      | And => Atom "and"
      | Or => Atom "or"
      | Xor => Atom "xor"
      end.

  Global Instance serialize_fbinop : Serialize fbinop :=
    fun fbinop =>
      match fbinop with
      | FAdd => Atom "fadd"
      | FSub => Atom "fsub"
      | FMul => Atom "fmul"
      | FDiv => Atom "fdiv"
      | FRem => Atom "frem"
      end.

  Global Instance serialize_icmp : Serialize icmp :=
    fun cmp =>
      Atom ("icmp "
             ++
             match cmp with
             | Eq => "eq"
             | Ne => "ne"
             | Ugt => "ugt"
             | Uge => "uge"
             | Ult => "ult"
             | Ule => "ule"
             | Sgt => "sgt"
             | Sge => "sge"
             | Slt => "slt"
             | Sle => "sle"
             end)%string.

  Global Instance serialize_fcmp : Serialize fcmp :=
    fun cmp =>
      Atom ("fcmp "
             ++
             match cmp with
               FFalse => "ffalse"
             | FOeq => "foeq"
             | FOgt => "fogt"
             | FOge => "foge"
             | FOlt => "folt"
             | FOle => "fole"
             | FOne => "fone"
             | FOrd => "ford"
             | FUno => "funo"
             | FUeq => "fueq"
             | FUgt => "fugt"
             | FUge => "fuge"
             | FUlt => "fult"
             | FUle => "fule"
             | FUne => "fune"
             | FTrue => "ftrue"
             end)%string.

  Fixpoint serialize_typ' typ: sexp :=
    match typ with
    | TYPE_I sz => Atom ("i" ++ to_string sz)%string
    | TYPE_Pointer t => [serialize_typ' t ; Atom "*"]
    | _ => Atom "(show_typ todo)"
    end.

  Global Instance serialize_typ : Serialize typ := serialize_typ'.

  Section WithSerializeT.
    Variable (T:Set).
    Context `{serializeT : Serialize T}.

    Fixpoint serialize_exp' (v : exp T) :=
      match v with
      | EXP_Ident id => to_sexp id
      | EXP_Integer x => to_sexp x
      | EXP_Bool b => to_sexp b
      | EXP_Null => Atom "null"
      | EXP_Zero_initializer => Atom "zero initializer"
      | EXP_Cstring s => Atom s
      | EXP_Undef => Atom "undef"
      | OP_IBinop iop t v1 v2 =>
        [to_sexp iop ; to_sexp t
                    ; serialize_exp' v1
                    ; serialize_exp' v2]
      | OP_ICmp cmp t v1 v2 =>
        [to_sexp cmp ; to_sexp t
                    ; serialize_exp' v1
                    ; serialize_exp' v2]
      | OP_GetElementPtr t ptrval idxs =>
        Atom "getelementptr"
      | _ => Atom "to_sexp_exp todo"
      end.

    Global Instance serialize_exp : Serialize (exp T) := serialize_exp'.
    Global Instance serialize_int : Serialize int := Serialize_Integral Integral_Z.

    Global Instance serialize_texp : Serialize (texp T) :=
      fun '(t, e) =>
          [to_sexp t ; Atom " " ; to_sexp e ].

    Definition serialize_opt {A:Type} `{AS:Serialize A} (s:string) : Serialize (option A) :=
      fun x =>
        match x with
        | None => Atom ""
        | Some a => [Atom s ; to_sexp a]
        end.

    Global Instance serialize_instr : Serialize (instr T) :=
      fun instr =>
        match instr with
        | INSTR_Op op => to_sexp op

        | INSTR_Load vol t ptr align =>
          [Atom "load" ; to_sexp t ; to_sexp ptr
           ; @serialize_opt _ serialize_int ", align" align]

        | INSTR_Store vol tval ptr align =>
          [Atom "store" ; to_sexp tval; to_sexp ptr
           ; @serialize_opt _ serialize_int ", align" align]

        | INSTR_Alloca t nb align =>
          [Atom "alloca" ; to_sexp t ; @serialize_opt _ serialize_int ", align" align]
        (*
           | INSTR_Call
           | INSTR_Phi
           | INSTR_Alloca
         *)
        | _ => Atom "string_of_instr todo"
        end.

    Global Instance serialize_terminator : Serialize (terminator T) :=
      fun t =>
        match t with
        | TERM_Ret v => [Atom "ret " ; to_sexp v]
        | TERM_Ret_void => Atom "ret"
        | _ => Atom "string_of_terminator todo"
        end.

    Global Instance serialize_instr_id_instr : Serialize (instr_id * (instr T)) :=
      fun '(iid, i) => [to_sexp iid ; Atom "=" ; to_sexp i].

    Global Instance serialize_block : Serialize (block T) :=
      fun block =>
        [Atom "Block "
         ; to_sexp (blk_id block) ; Atom ": " ;
           to_sexp (blk_code block)].

    Global Instance serialize_definition_list_block : Serialize (definition T (list (block T))) :=
      fun defn => [Atom "defn:" ; to_sexp (df_instrs defn)].

    Global Instance serialize_tle_list_block : Serialize (toplevel_entity T (list (block T))) :=
      fun tle =>
        match tle with
        | TLE_Definition defn => to_sexp defn
        | _ => Atom "string_of_tle_list_block todo"
        end.

  End WithSerializeT.

End hiding_notation.

Section WithType.
  Variable (T:Set).

  Definition target_of {X} (tle : toplevel_entity T X) : option string :=
    match tle with
    | TLE_Target tgt => Some tgt
    | _ => None
    end.

  Definition datalayout_of {X} (tle : toplevel_entity T X) : option string :=
    match tle with
    | TLE_Datalayout l => Some l
    | _ => None
    end.

  Definition filename_of {X} (tle : toplevel_entity T X) : option string :=
    match tle with
    | TLE_Source_filename l => Some l
    | _ => None
    end.

  Definition globals_of {X} (tle : toplevel_entity T X) : list (global T) :=
    match tle with
    | TLE_Global g => [g]
    | _ => []
    end.

  Definition declarations_of {X} (tle : toplevel_entity T X) : list (declaration T) :=
    match tle with
    | TLE_Declaration d => [d]
    | _ => []
    end.

  Definition definitions_of {X} (tle : toplevel_entity T X) : list (definition T X) :=
    match tle with
    | TLE_Definition d => [d]
    | _ => []
    end.

  Definition type_defs_of {X} (tle : toplevel_entity T X) : list (ident * T) :=
    match tle with
    | TLE_Type_decl id t => [(id,t)]
    | _ => []
    end.

  Definition modul_of_toplevel_entities {X} (tles : list (toplevel_entity T X)) : modul T X :=
    {|
      m_name := find_map filename_of tles;
      m_target := find_map target_of tles;
      m_datalayout := find_map datalayout_of tles;
      m_type_defs := flat_map type_defs_of tles;
      m_globals := flat_map globals_of tles;
      m_declarations := flat_map declarations_of tles;
      m_definitions := flat_map definitions_of tles;
    |}.

  (* Identifiers ----------------------------------------------------------- *)
  Class Ident (X:Set) := ident_of : X -> ident.

  Global Instance ident_of_block : Ident (block T) := fun (b:block T) => ID_Local (@blk_id T b).
  Global Instance ident_of_global : Ident (global T) := fun (g:global T) => ID_Global (@g_ident T g).
  Global Instance ident_of_declaration : Ident (declaration T) := fun (d:declaration T) => ID_Global (@dc_name T d).
  Global Instance ident_of_definition : forall X, Ident (definition T X) := fun X => fun (d:definition T X) => ident_of (@df_prototype T _ d).

  Definition globals {X} (m:modul T X) : list ident :=
    map ident_of (m_globals m)
        ++ map ident_of (m_declarations m)
        ++ map ident_of (m_definitions m).

End WithType.
