(* begin hide *)
From Stdlib Require Import
     Number.

From Vellvm Require Import
     Utils
     Syntax.LLVMAst.

From Stdlib Require Import Equalities OrderedType OrderedTypeEx.
Require Import ExtLib.Core.RelDec ExtLib.Data.Z.
Require Import ExtLib.Programming.Eqv.
From Stdlib Require Import Ascii.

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
Hypothesis IH_Iptr       : P TYPE_Iptr.
Hypothesis IH_Pointer    : forall t, P t -> P(TYPE_Pointer (Some t)).
Hypothesis IH_Opaque_Pointer : P (TYPE_Pointer None).
Hypothesis IH_Void       : P(TYPE_Void).
Hypothesis IH_FP         : forall fp, P(TYPE_FP fp).
Hypothesis IH_Label      : P(TYPE_Label).
Hypothesis IH_Token      : P(TYPE_Token).
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
  - apply IH_Iptr.
  - destruct t.
    + apply IH_Pointer. apply IH.
    + apply IH_Opaque_Pointer.
  - apply IH_Void.
  - apply IH_FP.
  - apply IH_Label.
  - apply IH_Token.
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
Hypothesis IH_Iptr       : P TYPE_Iptr.
Hypothesis IH_Pointer    : forall t, P t -> P(TYPE_Pointer (Some t)).
Hypothesis IH_Opaque_Pointer: P (TYPE_Pointer None).
Hypothesis IH_Void       : P(TYPE_Void).
Hypothesis IH_FP         : forall fp, P (TYPE_FP fp).
Hypothesis IH_Label      : P(TYPE_Label).
Hypothesis IH_Token      : P(TYPE_Token).
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
  - apply IH_Iptr.
  - destruct t.
    + apply IH_Pointer. apply IH.
    + apply IH_Opaque_Pointer.
  - apply IH_Void.
  - apply IH_FP.
  - apply IH_Label.
  - apply IH_Token.
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
  Variable Q : (metadata T) -> Prop.
  Hypothesis IH_Ident   : forall (id:ident), P ((EXP_Ident id)).
  Hypothesis IH_Integer : forall (x:Number.signed_int), P ((EXP_Integer x)).
  Hypothesis IH_Float   : forall (f:float_syntax), P ((EXP_Float f)).
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
  Hypothesis IH_Fneg    : forall (flags:list fast_math) (v:(T*exp T)), P(snd v) -> P (OP_Fneg flags v).
  Hypothesis IH_ICmp    : forall (samesign:bool) (cmp:icmp)   (t:T) (v1:exp T) (v2:exp T), P v1 -> P v2 -> P ((OP_ICmp samesign cmp t v1 v2)).
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
  Hypothesis IH_ExtractValue  : forall (vec:(T * exp T)) (idxs:list int_syntax), P (snd vec) -> P ((OP_ExtractValue vec idxs)).
  Hypothesis IH_InsertValue   : forall (vec:(T * exp T)) (elt:(T * exp T)) (idxs:list int_syntax), P (snd vec) -> P (snd elt) -> P ((OP_InsertValue vec elt idxs)).
  Hypothesis IH_Select        : forall (cnd:(T * exp T)) (v1:(T * exp T)) (v2:(T * exp T)), P (snd cnd) -> P (snd v1) -> P (snd v2) -> P ((OP_Select cnd v1 v2)).
  Hypothesis IH_Freeze        : forall (v:(T * exp T)), P (snd v) -> P ((OP_Freeze v)).

  Hypothesis IH_Asm           : forall (sideffect:bool) (alignstack:bool) (inteldialect:bool) (unwind:bool) (template:string) (operand_constraints:string), P(EXP_Asm sideffect alignstack inteldialect unwind template operand_constraints).

  Hypothesis IH_Metadata      : forall (m:metadata T), Q m -> P (EXP_Metadata m).
  Hypothesis IH_Splat         : forall (elt:(T * exp T)), P (snd elt) -> P (EXP_Splat elt).
  
  Hypothesis IH_METADATA_Null : Q(METADATA_Null).
  Hypothesis IH_METADATA_Id   : forall (id:raw_id), Q (METADATA_Id id).
  Hypothesis IH_METADATA_Const : forall (te:T * exp T), P (snd te) -> Q (METADATA_Const te).
  Hypothesis IH_METADATA_Node : forall (ms:list (metadata T)), (forall m, In m ms -> Q m) -> Q (METADATA_Node ms).
  Hypothesis IH_METADATA_Pair : forall (m1 m2:metadata T), Q m1 -> Q m2 -> Q (METADATA_Pair m1 m2).
  Hypothesis IH_METADATA_Debug : forall (s t:string), Q (METADATA_Debug s t).
  Hypothesis IH_METADATA_File_info : forall (f:file_info), Q (METADATA_File_info f).
  
  Lemma exp_ind : forall (v:exp T), P v.
Proof.    
refine(  
  fix F (e : exp T) : P e :=
  match e as e0 return (P e0) with
  | EXP_Ident id => IH_Ident id
  | EXP_Integer x => IH_Integer x
  | EXP_Float f => IH_Float f
  | EXP_Bool b => IH_Bool b
  | EXP_Null => IH_Null
  | EXP_Zero_initializer => IH_Zero_initializer
  | EXP_Cstring elts => _
  | EXP_Undef => IH_Undef
  | EXP_Poison => IH_Poison
  | EXP_Struct fields => _
  | EXP_Packed_struct fields => _
  | EXP_Array t elts => _
  | EXP_Vector t elts => _
  | OP_IBinop iop t v1 v2 => IH_IBinop iop t (F v1) (F v2)
  | OP_ICmp cmp s t v1 v2 => IH_ICmp cmp s t (F v1) (F v2)
  | OP_FBinop fop fm t v1 v2 => IH_FBinop fop fm t (F v1) (F v2)
  | OP_Fneg flags v => IH_Fneg flags v (F (snd v))
  | OP_FCmp cmp t v1 v2 => IH_FCmp cmp t (F v1) (F v2)
  | OP_Conversion conv t_from v t_to => IH_Conversion conv t_from t_to (F v) 
  | OP_GetElementPtr t ptrval idxs => _
  | OP_ExtractElement vec idx => IH_ExtractElement vec idx (F (snd vec)) (F (snd idx))
  | OP_InsertElement vec elt idx => IH_InsertElement vec elt idx (F (snd vec)) (F (snd elt)) (F (snd idx))
  | OP_ShuffleVector vec1 vec2 idxmask => IH_ShuffleVector vec1 vec2 idxmask (F (snd vec1))  (F (snd vec2)) (F (snd idxmask))
  | OP_ExtractValue vec idxs => IH_ExtractValue vec idxs (F (snd vec))
  | OP_InsertValue vec elt idxs => IH_InsertValue vec elt idxs (F (snd vec)) (F (snd elt))
  | OP_Select cnd v1 v2 => IH_Select cnd v1 v2 (F (snd cnd)) (F (snd v1)) (F (snd v2))
  | OP_Freeze v => IH_Freeze v (F (snd v))
  | EXP_Asm sideffect alignstack inteldialect unwind template operand_constraints =>
      IH_Asm sideffect alignstack inteldialect unwind template operand_constraints
  | EXP_Metadata m => IH_Metadata (F0 m)
  | EXP_Splat elt => IH_Splat elt (F (snd elt))
  end
with F0 (m : metadata T) : Q m :=
    match m as m0 return (Q m0) with
  | METADATA_Null => IH_METADATA_Null      
  | METADATA_Id id => IH_METADATA_Id id
  | METADATA_Const tv => IH_METADATA_Const tv (F (snd tv))
  | METADATA_Node mds => _
  | METADATA_Pair md1 md2 => IH_METADATA_Pair (F0 md1) (F0 md2)
  | METADATA_Debug DIstr contents => IH_METADATA_Debug DIstr contents
  | METADATA_File_info f => IH_METADATA_File_info f
    end
for
F).
- apply IH_Cstring.
  { revert elts.
    fix IHelts 1. intros [|u elts']. intros. inversion H.
    intros u' [<-|Hin]. apply F. eapply IHelts. apply Hin.
  }
- apply IH_Struct.
  { revert fields.
    fix IHfields 1. intros [|u fields']. intros. inversion H.
    intros u' [<-|Hin]. apply F. eapply IHfields. apply Hin.
  }
- apply IH_Packed_struct.
  { revert fields.
    fix IHfields 1. intros [|u fields']. intros. inversion H.
    intros u' [<-|Hin]. apply F. eapply IHfields. apply Hin.
  }
- apply IH_Array.
  { revert elts.
    fix IHelts 1. intros [|u elts']. intros. inversion H.
    intros u' [<-|Hin]. apply F. eapply IHelts. apply Hin.
  }
- apply IH_Vector.
  { revert elts.
    fix IHelts 1. intros [|u elts']. intros. inversion H.
    intros u' [<-|Hin]. apply F. eapply IHelts. apply Hin.
  }
- apply IH_GetElementPtr. apply F.
  { revert idxs.
    fix IHidxs 1. intros [|u idxs']. intros. inversion H.
    intros u' [<-|Hin]. apply F. eapply IHidxs. apply Hin.
  }
- apply IH_METADATA_Node.
  { revert mds.
    fix IHmds 1. intros [| m' md']. intros. inversion H.
    intros n' [<-|Hin]. apply F0. eapply IHmds. apply Hin.
  }
Qed.

  Lemma metadata_ind : forall (m:metadata T), Q m.
Proof.    
refine(  
  fix F (e : exp T) : P e :=
  match e as e0 return (P e0) with
  | EXP_Ident id => IH_Ident id
  | EXP_Integer x => IH_Integer x
  | EXP_Float f => IH_Float f
  | EXP_Bool b => IH_Bool b
  | EXP_Null => IH_Null
  | EXP_Zero_initializer => IH_Zero_initializer
  | EXP_Cstring elts => _
  | EXP_Undef => IH_Undef
  | EXP_Poison => IH_Poison
  | EXP_Struct fields => _
  | EXP_Packed_struct fields => _
  | EXP_Array t elts => _
  | EXP_Vector t elts => _
  | OP_IBinop iop t v1 v2 => IH_IBinop iop t (F v1) (F v2)
  | OP_ICmp s cmp t v1 v2 => IH_ICmp s cmp t (F v1) (F v2)
  | OP_FBinop fop fm t v1 v2 => IH_FBinop fop fm t (F v1) (F v2)
  | OP_Fneg flags v => IH_Fneg flags v (F (snd v))
  | OP_FCmp cmp t v1 v2 => IH_FCmp cmp t (F v1) (F v2)
  | OP_Conversion conv t_from v t_to => IH_Conversion conv t_from t_to (F v) 
  | OP_GetElementPtr t ptrval idxs => _
  | OP_ExtractElement vec idx => IH_ExtractElement vec idx (F (snd vec)) (F (snd idx))
  | OP_InsertElement vec elt idx => IH_InsertElement vec elt idx (F (snd vec)) (F (snd elt)) (F (snd idx))
  | OP_ShuffleVector vec1 vec2 idxmask => IH_ShuffleVector vec1 vec2 idxmask (F (snd vec1))  (F (snd vec2)) (F (snd idxmask))
  | OP_ExtractValue vec idxs => IH_ExtractValue vec idxs (F (snd vec))
  | OP_InsertValue vec elt idxs => IH_InsertValue vec elt idxs (F (snd vec)) (F (snd elt))
  | OP_Select cnd v1 v2 => IH_Select cnd v1 v2 (F (snd cnd)) (F (snd v1)) (F (snd v2))
  | OP_Freeze v => IH_Freeze v (F (snd v))
  | EXP_Asm sideffect alignstack inteldialect unwind template operand_constraints =>
      IH_Asm sideffect alignstack inteldialect unwind template operand_constraints
  | EXP_Metadata m => IH_Metadata (F0 m)
  | EXP_Splat elt => IH_Splat elt (F (snd elt))
  end
with F0 (m : metadata T) : Q m :=
  match m as m0 return (Q m0) with
  | METADATA_Null => IH_METADATA_Null
  | METADATA_Id id => IH_METADATA_Id id
  | METADATA_Const tv => IH_METADATA_Const tv (F (snd tv))
  | METADATA_Node mds => _
  | METADATA_Pair md1 md2 => IH_METADATA_Pair (F0 md1) (F0 md2)                          
  | METADATA_Debug DIstr contents => IH_METADATA_Debug DIstr contents
  | METADATA_File_info f => IH_METADATA_File_info f
  end
for
F0).
- apply IH_Cstring.
  { revert elts.
    fix IHelts 1. intros [|u elts']. intros. inversion H.
    intros u' [<-|Hin]. apply F. eapply IHelts. apply Hin.
  }
- apply IH_Struct.
  { revert fields.
    fix IHfields 1. intros [|u fields']. intros. inversion H.
    intros u' [<-|Hin]. apply F. eapply IHfields. apply Hin.
  }
- apply IH_Packed_struct.
  { revert fields.
    fix IHfields 1. intros [|u fields']. intros. inversion H.
    intros u' [<-|Hin]. apply F. eapply IHfields. apply Hin.
  }
- apply IH_Array.
  { revert elts.
    fix IHelts 1. intros [|u elts']. intros. inversion H.
    intros u' [<-|Hin]. apply F. eapply IHelts. apply Hin.
  }
- apply IH_Vector.
  { revert elts.
    fix IHelts 1. intros [|u elts']. intros. inversion H.
    intros u' [<-|Hin]. apply F. eapply IHelts. apply Hin.
  }
- apply IH_GetElementPtr. apply F.
  { revert idxs.
    fix IHidxs 1. intros [|u idxs']. intros. inversion H.
    intros u' [<-|Hin]. apply F. eapply IHidxs. apply Hin.
  }
- apply IH_METADATA_Node.
  { revert mds.
    fix IHmds 1. intros [| m' md']. intros. inversion H.
    intros n' [<-|Hin]. apply F0. eapply IHmds. apply Hin.
  }
Qed.

Lemma exp_metadata_mut_ind : (forall (e:exp T), P e) /\ (forall (m:metadata T), Q m).
  split.
  - apply exp_ind; auto.
  - apply metadata_ind; auto.
Qed.  

End ExpInd.


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
  | INSTR_Call (t,_) _ _ _ => is_void_typ t
  | INSTR_Fence _ _ => true
  | INSTR_Store _ _ _ => true
  | _ => false
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


Ltac unfold_eqv :=
  repeat (unfold eqv in *; unfold eqv_raw_id in *; unfold eqv_instr_id in * ).

Lemma Name_inj : forall s1 s2,
    Name s1 = Name s2 ->
    s1 = s2.
Proof using.
  intros * EQ; inv EQ; auto.
Qed.

(* File information - line numbers and error messages.
   The parser associates a METADATA_File_info value with every instruction of the AST.
 *)

Definition is_METADATA_File_info {T} (m:metadata T) : option file_info :=
  match m with
  | METADATA_File_info f => Some f
  | _ => None
  end.

Fixpoint get_file_info {T} (l : list (metadata T)) : option file_info :=
  match l with
  | [] => None
  | m::rest => match is_METADATA_File_info m with
             | Some f => Some f
             | None => get_file_info rest
             end
  end.

Definition no_loc_string : string := "[??:??.??-??.??]".

Definition location_string (fo : option file_info) : string :=
  match fo with
  | None => no_loc_string
  | Some f => "[" ++ f.(filename) ++ ":" ++ (show f.(start_line)) ++ "." ++ (show f.(start_col))
                 ++ "-" ++ (show f.(end_line)) ++ "." ++ (show f.(end_col)) ++ "]"                 
  end.

Definition location_error_string {T} (l : list (metadata T)) : string :=
  location_string (get_file_info l).
