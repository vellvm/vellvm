(* begin hide *)
From Coq Require Import
     ZArith.ZArith
     String.

From Vellvm Require Import
     Utilities
     Syntax.LLVMAst.

From stdpp Require Import gmap strings.

Open Scope positive.
Import ListNotations.

(* end hide *)

(* Equalities --------------------------------------------------------------- *)

#[global] Instance EqDecision_raw_id : EqDecision raw_id.
solve_decision.
Defined.

Definition Countable_raw_id_obligation :
  ∀ x : raw_id,
    match
      match x with
      | Name s => (encode s)~0~0
      | Anon i => (encode i)~0~1
      | Raw i => (encode i)~1~0
      end
    with
    | p~0~1 => Anon <$> decode p
    | p~1~0 => Raw <$> decode p
    | p~0~0 => Name <$> decode p
    | _ => None
    end = Some x.
Proof. now intros []; cbn; rewrite decode_encode. Qed.

#[global] Instance Countable_raw_id : Countable raw_id :=
  {|
    encode id := match id with
                 | Name s => (encode s)~0~0%positive
                 | Anon i => (encode i)~0~1%positive
                 | Raw  i => (encode i)~1~0%positive
                 end;
    decode p := match p with
                | p~0~0 => Name <$> decode p
                | p~0~1 => Anon <$> decode p
                | p~1~0 => Raw  <$> decode p
                | _     => None
                end;
    decode_encode := Countable_raw_id_obligation
  |}.

#[global] Instance EqDecision_block_id : EqDecision block_id.
solve_decision.
Defined.

#[global] Instance EqDecision_instr_id : EqDecision instr_id.
solve_decision.
Defined.

#[global] Instance EqDecision_ident : EqDecision ident.
solve_decision.
Defined.

(* Scheme Induction seems to still be too stupid to derive this automatically, fails to handle the nested lists  *)
Section TypInd.

Variable P : typ -> Prop.
Hypothesis IH_I          : forall sz, P (TYPE_I sz).
Hypothesis IH_IPTR       : P TYPE_IPTR.
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

Section TypRect.

Variable P : typ -> Type.
Hypothesis IH_I          : forall sz, P (TYPE_I sz).
Hypothesis IH_IPTR       : P TYPE_IPTR.
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
  Hypothesis IH_Integer : forall (x:int), P ((EXP_Integer x)).
  Hypothesis IH_Float   : forall (f:float32), P ((EXP_Float f)).
  Hypothesis IH_Double  : forall (f:float), P ((EXP_Double f)).
  Hypothesis IH_Hex     : forall (h:float), P ((EXP_Hex h)).
  Hypothesis IH_Bool    : forall (b:bool), P ((EXP_Bool b)).
  Hypothesis IH_Null    : P ((EXP_Null)).
  Hypothesis IH_Zero_initializer : P ((EXP_Zero_initializer)).
  Hypothesis IH_Cstring : forall (elts: list (T * (exp T))), (forall p, In p elts -> P (snd p)) -> P ((EXP_Cstring elts)).
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
