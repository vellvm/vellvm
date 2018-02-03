(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)


Require Import ZArith.ZArith List.
Require Import String Omega.
Require Import Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util.
Require Import Equalities OrderedType OrderedTypeEx Compare_dec.
Import ListNotations.

(* Equalities --------------------------------------------------------------- *)
Instance eq_dec_int : eq_dec int := Z_eq_dec.

Require Import Ascii.

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
    - apply eq_dec_int.
    - apply eq_dec_int.
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
Instance eq_dec_raw_id : eq_dec raw_id := RawIDOrd.eq_dec.



Module InstrIDDec <: MiniDecidableType.
  Definition t := instr_id.
  
  Lemma eq_dec : forall (x y : instr_id), {x = y} + {x <> y}.
  Proof.
    intros x y.
    destruct x as [xn | xn]; destruct y as [yn | yn].
    - destruct (xn == yn). subst. left. reflexivity.
      right. unfold not. intros. apply n. inversion H. auto.
    - right. unfold not. intros. inversion H.
    - right. unfold not. intros. inversion H.
    - destruct (xn == yn).
      left. subst. reflexivity.
      right. unfold not. intros. apply n. inversion H. auto.
  Defined.
End InstrIDDec.
Module InstrID := Make_UDT(InstrIDDec).

Instance eq_dec_instr_id : eq_dec instr_id := InstrID.eq_dec.

Module IdentDec <: MiniDecidableType.
  Definition t := ident.

  Lemma eq_dec : forall (x y : ident), {x = y} + {x <> y}.
  Proof.
    intros x y.
    destruct x as [xn | xn]; destruct y as [yn | yn].
    - destruct (xn == yn). subst. left. reflexivity.
      right. unfold not. intros. apply n. inversion H. auto.
    - right. unfold not. intros. inversion H.
    - right. unfold not. intros. inversion H.
    - destruct (xn == yn).
      left. subst. reflexivity.
      right. unfold not. intros. apply n. inversion H. auto.
  Defined.
End IdentDec.
Module Ident := Make_UDT(IdentDec).
Instance eq_dec_ident : eq_dec ident := Ident.eq_dec.  

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

Section ValueInd.
(*  
| VALUE_Ident   (id:ident)  
| VALUE_Integer (x:int)
| VALUE_Float   (f:float)
| VALUE_Bool    (b:bool)
| VALUE_Null
| VALUE_Zero_initializer
| VALUE_Cstring (s:string)
| VALUE_Undef
| VALUE_Struct        (fields: list (typ * a))
| VALUE_Packed_struct (fields: list (typ * a))
| VALUE_Array         (elts: list (typ * a))
| VALUE_Vector        (elts: list (typ * a))
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
  Variable P : value -> Prop.
  Hypothesis IH_Ident   : forall (id:ident), P ((VALUE_Ident id)).
  Hypothesis IH_Integer : forall (x:int), P ((VALUE_Integer x)).
  Hypothesis IH_Float   : forall (f:float), P ((VALUE_Float f)).
  Hypothesis IH_Hex     : forall (h:float), P ((VALUE_Hex h)).  
  Hypothesis IH_Bool    : forall (b:bool), P ((VALUE_Bool b)).
  Hypothesis IH_Null    : P ((VALUE_Null )).
  Hypothesis IH_Zero_initializer : P ((VALUE_Zero_initializer )).
  Hypothesis IH_Cstring : forall (s:string), P ((VALUE_Cstring s)).
  Hypothesis IH_Undef   : P ((VALUE_Undef )).
  Hypothesis IH_Struct  : forall (fields: list (typ * value)), (forall p, In p fields -> P (snd p)) -> P ((VALUE_Struct fields)).
  Hypothesis IH_Packed_struct : forall (fields: list (typ * value)), (forall p, In p fields -> P (snd p)) -> P ((VALUE_Packed_struct fields)).
  Hypothesis IH_Array   : forall (elts: list (typ * value)), (forall p, In p elts -> P (snd p)) -> P ((VALUE_Array elts)).
  Hypothesis IH_Vector  : forall (elts: list (typ * value)), (forall p, In p elts -> P (snd p)) -> P ((VALUE_Vector elts)).
  Hypothesis IH_IBinop  : forall (iop:ibinop) (t:typ) (v1:value) (v2:value), P v1 -> P v2 -> P ((OP_IBinop iop t v1 v2)).
  Hypothesis IH_ICmp    : forall (cmp:icmp)   (t:typ) (v1:value) (v2:value), P v1 -> P v2 -> P ((OP_ICmp cmp t v1 v2)).
  Hypothesis IH_FBinop  : forall (fop:fbinop) (fm:list fast_math) (t:typ) (v1:value) (v2:value), P v1 -> P v2 -> P ((OP_FBinop fop fm t v1 v2)).
  Hypothesis IH_FCmp    : forall (cmp:fcmp)   (t:typ) (v1:value) (v2:value), P v1 -> P v2 -> P ((OP_FCmp cmp t v1 v2)).
  Hypothesis IH_Conversion : forall (conv:conversion_type) (t_from:typ) (v:value) (t_to:typ), P v -> P ((OP_Conversion conv t_from v t_to)).
  Hypothesis IH_GetElementPtr : forall (t:typ) (ptrval:(typ * value)) (idxs:list (typ * value)),
      P (snd ptrval) -> (forall p, In p idxs -> P (snd p)) -> P ((OP_GetElementPtr t ptrval idxs)).
  Hypothesis IH_ExtractElement: forall (vec:(typ * value)) (idx:(typ * value)), P (snd vec) -> P (snd idx) -> P ((OP_ExtractElement vec idx)).
  Hypothesis IH_InsertElement : forall (vec:(typ * value)) (elt:(typ * value)) (idx:(typ * value)),
      P (snd vec) -> P (snd elt) -> P (snd idx) -> P ((OP_InsertElement vec elt idx)).
  Hypothesis IH_ShuffleVector : forall (vec1:(typ * value)) (vec2:(typ * value)) (idxmask:(typ * value)),
      P (snd vec1) -> P (snd vec2 ) -> P (snd idxmask) -> P ((OP_ShuffleVector vec1 vec2 idxmask)).
  Hypothesis IH_ExtractValue  : forall (vec:(typ * value)) (idxs:list int), P (snd vec) -> P ((OP_ExtractValue vec idxs)).
  Hypothesis IH_InsertValue   : forall (vec:(typ * value)) (elt:(typ * value)) (idxs:list int), P (snd vec) -> P (snd elt) -> P ((OP_InsertValue vec elt idxs)).
  Hypothesis IH_Select        : forall (cnd:(typ * value)) (v1:(typ * value)) (v2:(typ * value)), P (snd cnd) -> P (snd v1) -> P (snd v2) -> P ((OP_Select cnd v1 v2)).

  Lemma value_ind' : forall (v:value), P v.
    fix IH 1.
    destruct v. 
    - apply IH_Ident.
    - apply IH_Integer.
    - apply IH_Float.
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
End ValueInd.


(* Display *)


Instance string_of_raw_id : StringOf raw_id := fun r =>
  match r with
  | Name s => s
  | Anon n => to_string_b10 n
  | Raw  n => "_RAW_" ++ (to_string_b10 n)                           
  end.


Instance string_of_ident : StringOf ident :=  fun id =>
  match id with
  | ID_Global r => "@" ++ (string_of_raw_id r)
  | ID_Local  r => "%" ++ (string_of_raw_id r)
  end.

Instance string_of_instr_id : StringOf instr_id := fun ins =>
  match ins with
  | IId id => (string_of_raw_id id)
  | IVoid n => "void<" ++ (to_string_b10 n) ++ ">"
  end.


(* String of *)

Instance string_of_ibinop : StringOf ibinop :=
  fun binop =>
    match binop with
    | Add nuw nsw => "add"
    | Sub nuw nsw => "sub"
    | Mul nuw nsw => "mul"
    | Shl nuw nsw => "shl"
    | UDiv flag => "udiv"
    | SDiv flag => "sdiv"
    | LShr flag => "lshr"
    | AShr flag => "ashr"
    | URem | SRem => "rem"
    | And => "and"
    | Or => "or"
    | Xor => "xor"
    end.

Instance string_of_icmp : StringOf icmp :=
  fun cmp =>
    "icmp " ++ 
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
            end.
        
Fixpoint string_of_typ' typ := 
  match typ with
  | TYPE_I sz => ("i" ++ (string_of sz))%string
  | TYPE_Pointer t => ((string_of_typ' t) ++ "*")%string
  | _ => "(string_of_typ todo)"
  end.

Instance string_of_typ : StringOf typ := string_of_typ'.

Fixpoint string_of_value' (v : value) :=
  match v with
    | VALUE_Ident id => string_of id
    | VALUE_Integer x => string_of x
    | VALUE_Bool b => string_of b
    | VALUE_Null => "null"
    | VALUE_Zero_initializer => "zero initializer"
    | VALUE_Cstring s => s
    | VALUE_Undef => "undef"                                
    | OP_IBinop iop t v1 v2 =>
      ((string_of iop) ++ " " ++ (string_of t)
                       ++ " " ++ (string_of_value' v1)
                       ++ " " ++ (string_of_value' v2))%string
    | OP_ICmp cmp t v1 v2 =>
      ((string_of cmp) ++ " " ++ (string_of t)
                       ++ " " ++ (string_of_value' v1)
                       ++ " " ++ (string_of_value' v2))%string
    | OP_GetElementPtr t ptrval idxs =>
      "getelementptr"                                                       
    | _ => "string_of_value' todo"
  end.

Instance string_of_value : StringOf value := string_of_value'.

Instance string_of_instr : StringOf instr :=
  fun instr =>
    match instr with
    | INSTR_Op op => string_of op
    | INSTR_Load vol t ptr align =>
      ("load " ++ (string_of t) ++ " " ++ (string_of ptr)
               ++ ", align " ++ (string_of align))%string
    | INSTR_Store vol tval ptr align =>
      ("store " ++ (string_of tval) ++ " " ++ (string_of ptr)
                ++ ", align " ++ (string_of align))%string
    | INSTR_Alloca t nb align =>
      ("alloca " ++ (string_of t) ++ ", align " ++ (string_of align))%string
        (* 
    | INSTR_Call
    | INSTR_Phi
    | INSTR_Alloca
         *)
    | _ => "string_of_instr todo"
    end.

Instance string_of_terminator : StringOf terminator :=
  fun t =>
    match t with
    | TERM_Ret v => ("ret " ++ (string_of v))%string
    | TERM_Ret_void => "ret"
    | _ => "string_of_terminator todo"
    end.

Instance string_of_block : StringOf block :=
  fun block =>
    ("Block " ++ (string_of (blk_id block)) ++ ": "
              ++ (string_of (blk_code block)))%string.


Instance string_of_definition_list_block : StringOf (definition (list block)) :=
  fun defn => ("defn: " ++ string_of (df_instrs defn))%string.

Instance string_of_tle_list_block : StringOf (toplevel_entity (list block)) :=
  fun tle =>
    match tle with
    | TLE_Definition defn => string_of defn
    | _ => "string_of_tle_list_block todo"
    end.


Definition target_of {X} (tle : toplevel_entity X) : option string :=
  match tle with
  | TLE_Target tgt => Some tgt
  | _ => None
  end.

Definition datalayout_of {X} (tle : toplevel_entity X) : option string :=
  match tle with
  | TLE_Datalayout l => Some l
  | _ => None
  end.

Definition filename_of {X} (tle : toplevel_entity X) : option string :=
  match tle with
  | TLE_Source_filename l => Some l
  | _ => None
  end.

Definition globals_of {X} (tle : toplevel_entity X) : list global  :=
  match tle with
  | TLE_Global g => [g]
  | _ => []
  end.

Definition declarations_of {X} (tle : toplevel_entity X) : list declaration :=
  match tle with
  | TLE_Declaration d => [d]
  | _ => []
  end.

Definition definitions_of {X} (tle : toplevel_entity X) : list (definition X) :=
  match tle with
  | TLE_Definition d => [d]
  | _ => []
  end.

Definition modul_of_toplevel_entities {X} (tles : list (toplevel_entity X)) : modul X :=
  {|
    m_name := find_map filename_of tles;
    m_target := find_map target_of tles;
    m_datalayout := find_map datalayout_of tles;
    m_globals := flat_map globals_of tles;
    m_declarations := flat_map declarations_of tles;
    m_definitions := flat_map definitions_of tles;
  |}.




(* Identifiers ----------------------------------------------------------- *)
Class Ident (X:Set) := ident_of : X -> ident.

Instance ident_of_block : Ident block := fun (b:block) => ID_Local (blk_id b).
Instance ident_of_global : Ident global := fun (g:global) => ID_Global (g_ident g).
Instance ident_of_declaration : Ident declaration := fun (d:declaration) => ID_Global (dc_name d).
Instance ident_of_definition : forall X, Ident (definition X) := fun X => fun (d:definition X) => ident_of (df_prototype d).


Definition globals {X} (m:modul X) : list ident := 
           map ident_of (m_globals m)
        ++ map ident_of (m_declarations m)
        ++ map ident_of (m_definitions m).

