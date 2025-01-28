(* begin hide *)
From Coq Require Import
     ZArith.ZArith
     String.

From Vellvm Require Import
     Utilities
     Syntax.LLVMAst.

From QuickChick Require Import Show.

Require Import Equalities OrderedType OrderedTypeEx.
Require Import ExtLib.Core.RelDec ExtLib.Data.Z.
Require Import ExtLib.Programming.Eqv.
Require Import Ascii.

Import ListNotations.
Import EqvNotation.

(* end hide *)

(* Equalities --------------------------------------------------------------- *)
#[global] Instance eq_dec_int : RelDec (@eq int_ast) := Data.Z.RelDec_zeq.
#[global] Instance eqv_int : Eqv int_ast := (@eq int_ast).

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
    | Name s1, Name s2 => String_as_OT.lt s1 s2
    | Raw n1, Raw n2 => (n1 < n2)%Z
    | Anon _, _ => True
    | Name _, Raw _ => True
    | _, _ => False
    end.

  Lemma lt_trans : forall a b c : t, lt a b -> lt b c -> lt a c.
  Proof using.
    destruct a; destruct b; destruct c; simpl; intros H1 H2; intuition auto with *.
    - eapply String_as_OT.lt_trans; eauto.
  Qed.

  Lemma lt_not_eq : forall a b:t, lt a b -> ~eq a b.
  Proof using.
    destruct a; destruct b; simpl; intros H He; inversion He; subst.
    - apply String_as_OT.lt_not_eq in H. apply H. unfold String_as_OT.eq. reflexivity.
    - apply Z_as_OT.lt_not_eq in H. tauto.
    - apply Z_as_OT.lt_not_eq in H. tauto.
  Qed.

  Definition cmp (x:t) (y:t) : comparison :=
    match x,y with
    | Anon n1, Anon n2 =>
        Z.compare n1 n2
    | Anon _, Name _ => Lt
    | Anon _, Raw _ => Lt
    | Name _, Anon _ => Gt
    | Name s1, Name s2 =>
        String_as_OT.cmp s1 s2
    | Name _, Raw _ => Lt
    | Raw _, Anon _ => Gt
    | Raw _, Name _ => Gt
    | Raw n1, Raw n2 =>
        Z.compare n1 n2
    end.

  #[local]
    Hint Resolve
    Zcompare_antisym
    Z.compare_eq
    Zaux.Zcompare_Lt
    String_as_OT.cmp_antisym
    String_as_OT.cmp_eq
    String_as_OT.cmp_lt : CMP.

  Lemma cmp_lt (a b : t) :
    cmp a b = Lt  <->  lt a b.
  Proof.
    destruct a,b; cbn;
      try solve
        [ eauto with CMP
        | split; solve [discriminate | contradiction]
        | split; auto
        ].
  Qed.

  Lemma cmp_eq : forall a b : t, cmp a b = Datatypes.Eq <-> a = b.
  Proof.
    destruct a,b; cbn;
      try solve
        [ eauto with CMP
        | split; solve [discriminate | contradiction]
        | split; auto
        ].
    - split; intros.
      + assert (s = s0).
        { eapply String_as_OT.cmp_eq; eauto. }
        subst; auto.
      + inv H; eauto with CMP.
        apply String_as_OT.cmp_eq; auto.
    - split; intros.
      + assert (n = n0).
        { eapply Z.compare_eq; eauto. }
        subst; auto.
      + inv H; eauto with CMP.
        apply Z.compare_refl.
    - split; intros.
      + assert (n = n0).
        { eapply Z.compare_eq; eauto. }
        subst; auto.
      + inv H; eauto with CMP.
        apply Z.compare_refl.
  Qed.

  Lemma cmp_antisym :
    forall a b : t,
      cmp a b = CompOpp (cmp b a).
  Proof.
    destruct a,b; cbn; auto with CMP.
  Qed.

  Local Lemma compare_helper_lt {a b : t} (L : cmp a b = Lt):
    lt a b.
  Proof.
    now apply cmp_lt.
  Qed.

  Local Lemma compare_helper_gt {a b : t} (G : cmp a b = Gt):
    lt b a.
  Proof.
    rewrite cmp_antisym in G.
    rewrite CompOpp_iff in G.
    now apply cmp_lt.
  Qed.

  Local Lemma compare_helper_eq {a b : t} (E : cmp a b = Datatypes.Eq):
    a = b.
  Proof.
    now apply cmp_eq.
  Qed.

  Definition compare (a b : t) : Compare lt eq a b :=
    match cmp a b as z return _ = z -> _ with
    | Lt => fun E => LT (compare_helper_lt E)
    | Gt => fun E => GT (compare_helper_gt E)
    | Datatypes.Eq => fun E => EQ (compare_helper_eq E)
    end Logic.eq_refl.

  Definition eq_dec : forall (x y : t), {x = y} + {x <> y}.
    decide equality.
    - apply string_dec.
    - apply rel_dec_p.
    - apply rel_dec_p.
  Defined.

End RawIDOrd.

#[global] Instance eq_dec_raw_id : RelDec (@eq raw_id) := RelDec_from_dec (@eq raw_id) RawIDOrd.eq_dec.
#[global] Instance eqv_raw_id : Eqv raw_id := (@eq raw_id).
#[export] Hint Unfold eqv_raw_id: core.

Module InstrIDDec <: MiniDecidableType.
  Definition t := instr_id.

  Lemma eq_dec : forall (x y : instr_id), {x = y} + {x <> y}.
  Proof using.
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

#[global] Instance eq_dec_instr_id : RelDec (@eq instr_id) := RelDec_from_dec (@eq instr_id) InstrID.eq_dec.
#[global] Instance eqv_instr_id : Eqv instr_id := (@eq instr_id).

Module IdentDec <: MiniDecidableType.
  Definition t := ident.

  Lemma eq_dec : forall (x y : ident), {x = y} + {x <> y}.
  Proof using.
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

#[global] Instance eq_dec_ident : RelDec (@eq ident) := RelDec_from_dec (@eq ident) Ident.eq_dec.
#[global] Instance eqv_ident : Eqv ident := (@eq ident).

(* Induction Principles ----------------------------------------------------- *)

Section TypInd.

Variable P : typ -> Prop.
Hypothesis IH_I          : forall sz, P (TYPE_I sz).
Hypothesis IH_IPTR       : P TYPE_IPTR.
Hypothesis IH_Pointer    : forall t, P t -> P(TYPE_Pointer (Some t)).
Hypothesis IH_Opaque_Pointer : P (TYPE_Pointer None).
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
Hypothesis IH_Function   : forall ret args varargs, P ret -> (forall u, In u args -> P u) -> P(TYPE_Function ret args varargs).
Hypothesis IH_Struct     : forall fields, (forall u, In u fields -> P u) -> P(TYPE_Struct fields).
Hypothesis IH_Packed_struct : forall fields, (forall u, In u fields -> P u) -> P(TYPE_Packed_struct fields).
Hypothesis IH_Opaque     : P(TYPE_Opaque).
Hypothesis IH_Vector     : forall sz t, P t -> P(TYPE_Vector sz t).
Hypothesis IH_Identified : forall id, P(TYPE_Identified id).

Lemma typ_ind : forall (t:typ), P t.
  fix IH 1.
  destruct t.
  - apply IH_I.
  - apply IH_IPTR.
  - destruct t.
    + apply IH_Pointer. apply IH.
    + apply IH_Opaque_Pointer.
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

Section TypRect.

Variable P : typ -> Type.
Hypothesis IH_I          : forall sz, P (TYPE_I sz).
Hypothesis IH_IPTR       : P TYPE_IPTR.
Hypothesis IH_Pointer    : forall t, P t -> P(TYPE_Pointer (Some t)).
Hypothesis IH_Opaque_Pointer: P (TYPE_Pointer None).
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
Hypothesis IH_Function   : forall ret args varargs, P ret -> (forall u : typ, (P u -> typ -> P u) -> list typ -> P u -> P u) -> P(TYPE_Function ret args varargs).
Hypothesis IH_Struct     : forall fields, (forall u : typ, (P u -> typ -> P u) -> list typ -> P u -> P u) -> P(TYPE_Struct fields).
Hypothesis IH_Packed_struct : forall fields, (forall u : typ, (P u -> typ -> P u) -> list typ -> P u -> P u) -> P(TYPE_Packed_struct fields).
Hypothesis IH_Opaque     : P(TYPE_Opaque).
Hypothesis IH_Vector     : forall sz t, P t -> P(TYPE_Vector sz t).
Hypothesis IH_Identified : forall id, P(TYPE_Identified id).

Lemma typ_rect' : forall (t:typ), P t.
  fix IH 1.
  destruct t.
  - apply IH_I.
  - apply IH_IPTR.
  - destruct t.
    + apply IH_Pointer. apply IH.
    + apply IH_Opaque_Pointer.
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
    intros u f l def.
    refine (match args with [] => def | (x::rest) => f def x end).
  - apply IH_Struct.
    intros u f l def.
    refine (match fields with [] => def | (x::rest) => f def x end).
  - apply IH_Packed_struct.
    intros u f l def.
    refine (match fields with [] => def | (x::rest) => f def x end).
  - apply IH_Opaque.
  - apply IH_Vector. apply IH.
  - apply IH_Identified.
Qed.

End TypRect.

Section ExpInd.

  Variable T : Set.
  Variable P : (exp T) -> Prop.
  Hypothesis IH_Ident   : forall (id:ident), P ((EXP_Ident id)).
  Hypothesis IH_Integer : forall (x:int_ast), P ((EXP_Integer x)).
  Hypothesis IH_Float   : forall (f:float32), P ((EXP_Float f)).
  Hypothesis IH_Double  : forall (f:float), P ((EXP_Double f)).
  Hypothesis IH_Hex     : forall (h:float), P ((EXP_Hex h)).
  Hypothesis IH_Bool    : forall (b:bool), P ((EXP_Bool b)).
  Hypothesis IH_Null    : P ((EXP_Null)).
  Hypothesis IH_Zero_initializer : P ((EXP_Zero_initializer)).
  Hypothesis IH_Cstring : forall (elts: list (T * (exp T))), (forall p, In p elts -> P (snd p)) -> P ((EXP_Cstring elts)).
  Hypothesis IH_Undef   : P ((EXP_Undef)).
  Hypothesis IH_Poison  : P ((EXP_Poison)).
  Hypothesis IH_Struct  : forall (fields: list (T * (exp T))), (forall p, In p fields -> P (snd p)) -> P ((EXP_Struct fields)).
  Hypothesis IH_Packed_struct : forall (fields: list (T * (exp T))), (forall p, In p fields -> P (snd p)) -> P ((EXP_Packed_struct fields)).
  Hypothesis IH_Array   : forall t (elts: list (T * (exp T))), (forall p, In p elts -> P (snd p)) -> P ((EXP_Array t elts)).
  Hypothesis IH_Vector  : forall t (elts: list (T * (exp T))), (forall p, In p elts -> P (snd p)) -> P ((EXP_Vector t elts)).
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
  Hypothesis IH_ExtractValue  : forall (vec:(T * exp T)) (idxs:list int_ast), P (snd vec) -> P ((OP_ExtractValue vec idxs)).
  Hypothesis IH_InsertValue   : forall (vec:(T * exp T)) (elt:(T * exp T)) (idxs:list int_ast), P (snd vec) -> P (snd elt) -> P ((OP_InsertValue vec elt idxs)).
  Hypothesis IH_Select        : forall (cnd:(T * exp T)) (v1:(T * exp T)) (v2:(T * exp T)), P (snd cnd) -> P (snd v1) -> P (snd v2) -> P ((OP_Select cnd v1 v2)).
  Hypothesis IH_Freeze        : forall (v:(T * exp T)), P (snd v) -> P ((OP_Freeze v)).

  Lemma exp_ind : forall (v:exp T), P v.
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
      { revert elts.
        fix IHelts 1. intros [|u elts']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IHelts. apply Hin.
      }

    - apply IH_Undef.
    - apply IH_Poison.
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
    - apply IH_Freeze. apply IH.
  Qed.
End ExpInd.


(* Display *)
Require Import Ceres.Ceres.

Section hiding_notation.
  #[local] Open Scope sexp_scope.

  Definition serialize_raw_id (prefix: string): Serialize raw_id :=
    fun r =>
      match r with
      | Name s => Atom (prefix ++ s)%string
      | Anon n => Atom (show_Z n)
      | LLVMAst.Raw n => Atom ("_RAW_" ++ show_Z n)%string
      end.

  #[global] Instance serialize_raw_id': Serialize raw_id := serialize_raw_id "".

  #[global] Instance serialize_ident : Serialize ident :=
    fun id =>
      match id with
      | ID_Global r => serialize_raw_id "@" r
      | ID_Local  r => serialize_raw_id "%" r
      end.

  #[global] Instance serialize_instr_id : Serialize instr_id :=
    fun ins =>
      match ins with
      | IId id => serialize_raw_id "%" id
      | IVoid n => Atom ("void<" ++ show_Z n ++ ">")%string
      end.

  #[global] Instance serialize_ibinop : Serialize ibinop :=
    fun binop =>
      match binop with
      | LLVMAst.Add nuw nsw => Atom "add"
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

  #[global] Instance serialize_fbinop : Serialize fbinop :=
    fun fbinop =>
      match fbinop with
      | FAdd => Atom "fadd"
      | FSub => Atom "fsub"
      | FMul => Atom "fmul"
      | FDiv => Atom "fdiv"
      | FRem => Atom "frem"
      end.

  #[global] Instance serialize_icmp : Serialize icmp :=
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

  #[global] Instance serialize_fcmp : Serialize fcmp :=
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

  (* I need show_ZVellvm here because Ceres segfaults on extraction for
  showing integers for some reason *)
  Fixpoint serialize_typ' typ: sexp :=
    match typ with
    | TYPE_I sz => Atom ("i" ++ show_N (Npos sz))%string
    | TYPE_IPTR => Atom ("iptr")%string
    | TYPE_Pointer (Some t) => [serialize_typ' t ; Atom "*"]
    | TYPE_Pointer None => Atom "ptr"
    | TYPE_Void => Atom "void"
    | TYPE_Half => Atom "half"
    | TYPE_Float => Atom "float"
    | TYPE_Double => Atom "double"
    | TYPE_X86_fp80 => Atom "x86_fp80"
    | TYPE_Fp128 => Atom "fp128"
    | TYPE_Ppc_fp128 => Atom "ppc_fp128"
    | TYPE_Metadata => Atom "metadata"
    | TYPE_X86_mmx => Atom "x86_mmx"
    | TYPE_Array sz t => [Atom "["; Atom (show_N sz); Atom "x"; serialize_typ' t; Atom "]"]
    | TYPE_Function ret args varargs => [serialize_typ' ret; Atom "("; Atom (String.concat ", " (map (fun x => CeresFormat.string_of_sexp (serialize_typ' x)) args)); Atom ")"]
    | TYPE_Struct fields => [Atom "{"; Atom (String.concat ", " (map (fun x => CeresFormat.string_of_sexp (serialize_typ' x)) fields)); Atom "}"]
    | TYPE_Packed_struct fields => [Atom "<{"; Atom (String.concat ", " (map (fun x => CeresFormat.string_of_sexp (serialize_typ' x)) fields)); Atom "}>"]
    | TYPE_Opaque => Atom "opaque"
    | TYPE_Vector sz t => [Atom "<"; Atom (show_N sz); Atom "x"; serialize_typ' t; Atom ">"]
    | TYPE_Identified id => Atom (to_string id)
    end.

  #[global] Instance serialize_typ : Serialize typ := serialize_typ'.

  Section WithSerializeT.
    Variable (T:Set).
    Context `{serializeT : Serialize T}.

    Fixpoint serialize_exp' (v : exp T) :=
      match v with
      | EXP_Ident id => to_sexp id
      | EXP_Integer x => Atom (show_Z x)
      | EXP_Bool b => to_sexp b
      | EXP_Null => Atom "null"
      | EXP_Zero_initializer => Atom "zero initializer"
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

    #[global] Instance serialize_exp : Serialize (exp T) := serialize_exp'.
    #[global] Instance serialize_int : Serialize int_ast := fun i => Atom (show_Z i).

    #[global] Instance serialize_texp : Serialize (texp T) :=
      fun '(t, e) =>
          [to_sexp t ; Atom " " ; to_sexp e ].

    Definition serialize_opt {A:Type} `{AS:Serialize A} (s:string) : Serialize (option A) :=
      fun x =>
        match x with
        | None => Atom ""
        | Some a => [Atom s ; to_sexp a]
        end.

    #[global] Instance serialize_instr : Serialize (instr T) :=
      fun instr =>
        match instr with
          (* SAZ: OUT OF DATE *)
        (*
        | INSTR_Op op => to_sexp op

        | INSTR_Load t ptr anns =>
          [Atom "load" ; to_sexp t ; to_sexp ptr ]

        | INSTR_Store tval ptr anns =>
          [Atom "store" ; to_sexp tval; to_sexp ptr
           ; @serialize_opt _ serialize_int ", align" align]

        | INSTR_Alloca t anns (* TODO: add anns *)=>
          [Atom "alloca" ; to_sexp t]

           | INSTR_Call
           | INSTR_Phi
           | INSTR_Alloca
         *)
        | _ => Atom "string_of_instr todo"
        end.

    #[global] Instance serialize_terminator : Serialize (terminator T) :=
      fun t =>
        match t with
        | TERM_Ret v => [Atom "ret " ; to_sexp v]
        | TERM_Ret_void => Atom "ret"
        | TERM_Br te b1 b2 =>
          [Atom "br"; to_sexp te; Atom ", label "; to_sexp b1; Atom ", label "; to_sexp b2]
        | TERM_Br_1 b => [Atom "br label"; to_sexp b]
        | _ => Atom "string_of_terminator todo"
        end.

    #[global] Instance serialize_instr_id_instr : Serialize (instr_id * (instr T)) :=
      fun '(iid, i) =>
        match iid with
        | IId _ =>
          [to_sexp iid ; Atom "=" ; to_sexp i]
        | IVoid n =>
          [to_sexp i]
        end.

    #[global] Instance serialize_block : Serialize (block T) :=
      fun block =>
        [to_sexp (blk_id block) ; Atom ":\n" ;
        (* TODO: add indentation *)
        to_sexp (blk_code block); to_sexp (blk_term block)].
  End WithSerializeT.

  (* TODO: What is this SerializeTyp stuff about? Why use ceres? *)
  Section SerializeTyp.
    #[global] Instance serialize_definition_list_block : Serialize (definition typ (list (block typ))) :=
      fun defn =>
        match defn.(df_prototype).(dc_type) with
        | TYPE_Function ret_t args_t varargs
          => let name  := defn.(df_prototype).(dc_name) in
             [Atom "define"; to_sexp ret_t; to_sexp name;
             Atom " {\n";
             (* TODO: Add prefix for indentation? *)
             to_sexp (df_instrs defn);
             Atom "}\n"]
        | _ => Atom "Invalid type on function"
        end.

    #[global] Instance serialize_tle_list_block : Serialize (toplevel_entity typ (list (block typ))) :=
      fun tle =>
        match tle with
        | TLE_Definition defn => to_sexp defn
        | _ => Atom "string_of_tle_list_block todo"
        end.
  End SerializeTyp.
End hiding_notation.


(* Utility function to determine whether a typ is void or is a function type returning void.
   This is needed in the parser to determine whether a function call instruction should
   generate an "anonymous" id or a "void" id.

   Examples:
      call void @f()             ; generates a void ID since @f returns void
      call void(i32) @g(i32 3)   ; generates a void ID since @g returns void
      call i32 @h()              ; generates an anonymous ID since @h returns non-void type
*)
Definition is_void_typ (t:typ) : bool :=
  match t with
  | TYPE_Void => true
  | TYPE_Function TYPE_Void _ _ => true
  | _ => false
  end.

Definition is_void_instr (i:instr typ) : bool :=
  match i with
  | INSTR_Comment _ => true
  | INSTR_Call (t,_) _ _ => is_void_typ t
  | INSTR_Store _ _ _ => true
  | _ => false
  end.

Ltac unfold_eqv :=
  repeat (unfold eqv in *; unfold eqv_raw_id in *; unfold eqv_instr_id in * ).

(* This function extracts the string of the form [llvm._] from an LLVM expression.
   It returns None if the expression is not an intrinsic definition.
*)
Definition intrinsic_ident (id:ident) : option string :=
  match id with
  | ID_Global (Name s) =>
      if orb (orb (String.prefix "llvm." s)
                  (Coqlib.proj_sumbool (string_dec "malloc" s)))
             (Coqlib.proj_sumbool (string_dec "free" s))
      then Some s else None
  | _ => None
  end.

Definition intrinsic_exp {T} (e:exp T) : option string :=
  match e with
  | EXP_Ident id => intrinsic_ident id
  | _ => None
  end.

Lemma Name_inj : forall s1 s2,
    Name s1 = Name s2 ->
    s1 = s2.
Proof using.
  intros * EQ; inv EQ; auto.
Qed.
