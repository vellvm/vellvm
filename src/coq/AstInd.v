Require Import Ascii Strings.String List.
Require Import Vellvm.Ollvm_ast.
Open Scope string_scope.
Import ListNotations.

Set Implicit Arguments.
Generalizable All Variables.

Section TypInd.

(* 
Inductive typ : Set :=
| TYPE_I (sz:int)
| TYPE_Pointer (t:typ)
| TYPE_Void
| TYPE_Half
| TYPE_Float
| TYPE_Double
| TYPE_X86_fp80
| TYPE_Fp128
| TYPE_Ppc_fp128
| TYPE_Label
| TYPE_Metadata
| TYPE_X86_mmx
| TYPE_Array (sz:int) (t:typ)
| TYPE_Function (ret:typ) (args:list typ)
| TYPE_Struct (fields:list typ)
| TYPE_Packed_struct (fields:list typ)
| TYPE_Opaque
| TYPE_Vector (sz:int) (t:typ)
| TYPE_Identified (id:ident)
.
 *)
Variable P : typ -> Prop.
Hypothesis IH_I       : forall sz, P (TYPE_I sz).
Hypothesis IH_Pointer : forall t, P t -> P(TYPE_Pointer t).
Hypothesis IH_Void : P(TYPE_Void).
Hypothesis IH_Half : P(TYPE_Half).
Hypothesis IH_Float : P(TYPE_Float).
Hypothesis IH_Double : P(TYPE_Double).
Hypothesis IH_X86_fp80 : P(TYPE_X86_fp80).
Hypothesis IH_Fp128 : P(TYPE_Fp128).
Hypothesis IH_Ppc_fp128 : P(TYPE_Ppc_fp128).
Hypothesis IH_Label : P(TYPE_Label).
Hypothesis IH_Metadata : P(TYPE_Metadata).
Hypothesis IH_X86_mmx : P(TYPE_X86_mmx).
Hypothesis IH_Array : forall sz t, P t -> P(TYPE_Array sz t).
Hypothesis IH_Function : forall ret args, P ret -> (forall u, In u args -> P u) -> P(TYPE_Function ret args).
Hypothesis IH_Struct : forall fields, (forall u, In u fields -> P u) -> P(TYPE_Struct fields).
Hypothesis IH_Packed_struct : forall fields, (forall u, In u fields -> P u) -> P(TYPE_Packed_struct fields).
Hypothesis IH_Opaque : P(TYPE_Opaque).
Hypothesis IH_Vector: forall sz t, P t -> P(TYPE_Vector sz t).
Hypothesis IH_Identified: forall id, P(TYPE_Identified id).

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
  - apply IH_Label.
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
| VALUE_None                                       (* "token" constant *)
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
  Hypothesis IH_Ident   : forall (id:ident), P (SV (VALUE_Ident _ id)).
  Hypothesis IH_Integer : forall (x:int), P (SV (VALUE_Integer _ x)).
  Hypothesis IH_Float   : forall (f:float), P (SV (VALUE_Float _ f)).
  Hypothesis IH_Bool    : forall (b:bool), P (SV (VALUE_Bool _ b)).
  Hypothesis IH_Null    : P (SV (VALUE_Null _ )).
  Hypothesis IH_Zero_initializer : P (SV (VALUE_Zero_initializer _)).
  Hypothesis IH_Cstring : forall (s:string), P (SV (VALUE_Cstring _ s)).
  Hypothesis IH_None    : P (SV (VALUE_None _ )).
  Hypothesis IH_Undef   : P (SV (VALUE_Undef _ )).
  Hypothesis IH_Struct  : forall (fields: list (typ * value)), (forall p, In p fields -> P (snd p)) -> P (SV (VALUE_Struct _ fields)).
  Hypothesis IH_Packed_struct : forall (fields: list (typ * value)), (forall p, In p fields -> P (snd p)) -> P (SV (VALUE_Packed_struct _ fields)).
  Hypothesis IH_Array   : forall (elts: list (typ * value)), (forall p, In p elts -> P (snd p)) -> P (SV (VALUE_Array _ elts)).
  Hypothesis IH_Vector  : forall (elts: list (typ * value)), (forall p, In p elts -> P (snd p)) -> P (SV (VALUE_Vector _ elts)).
  Hypothesis IH_IBinop  : forall (iop:ibinop) (t:typ) (v1:value) (v2:value), P v1 -> P v2 -> P (SV (OP_IBinop _ iop t v1 v2)).
  Hypothesis IH_ICmp    : forall (cmp:icmp)   (t:typ) (v1:value) (v2:value), P v1 -> P v2 -> P (SV (OP_ICmp _ cmp t v1 v2)).
  Hypothesis IH_FBinop  : forall (fop:fbinop) (fm:list fast_math) (t:typ) (v1:value) (v2:value), P v1 -> P v2 -> P (SV (OP_FBinop _ fop fm t v1 v2)).
  Hypothesis IH_FCmp    : forall (cmp:fcmp)   (t:typ) (v1:value) (v2:value), P v1 -> P v2 -> P (SV (OP_FCmp _ cmp t v1 v2)).
  Hypothesis IH_Conversion : forall (conv:conversion_type) (t_from:typ) (v:value) (t_to:typ), P v -> P (SV (OP_Conversion _ conv t_from v t_to)).
  Hypothesis IH_GetElementPtr : forall (t:typ) (ptrval:(typ * value)) (idxs:list (typ * value)),
      P (snd ptrval) -> (forall p, In p idxs -> P (snd p)) -> P (SV (OP_GetElementPtr _ t ptrval idxs)).
  Hypothesis IH_ExtractElement: forall (vec:(typ * value)) (idx:(typ * value)), P (snd vec) -> P (snd idx) -> P (SV (OP_ExtractElement _ vec idx)).
  Hypothesis IH_InsertElement : forall (vec:(typ * value)) (elt:(typ * value)) (idx:(typ * value)),
      P (snd vec) -> P (snd elt) -> P (snd idx) -> P (SV (OP_InsertElement _ vec elt idx)).
  Hypothesis IH_ShuffleVector : forall (vec1:(typ * value)) (vec2:(typ * value)) (idxmask:(typ * value)),
      P (snd vec1) -> P (snd vec2 ) -> P (snd idxmask) -> P (SV (OP_ShuffleVector _ vec1 vec2 idxmask)).
  Hypothesis IH_ExtractValue  : forall (vec:(typ * value)) (idxs:list int), P (snd vec) -> P (SV (OP_ExtractValue _ vec idxs)).
  Hypothesis IH_InsertValue   : forall (vec:(typ * value)) (elt:(typ * value)) (idxs:list int), P (snd vec) -> P (snd elt) -> P (SV (OP_InsertValue _ vec elt idxs)).
  Hypothesis IH_Select        : forall (cnd:(typ * value)) (v1:(typ * value)) (v2:(typ * value)), P (snd cnd) -> P (snd v1) -> P (snd v2) -> P (SV (OP_Select _ cnd v1 v2)).

  Lemma value_ind' : forall (v:value), P v.
    fix IH 1.
    destruct v. destruct v.
    - apply IH_Ident.
    - apply IH_Integer.
    - apply IH_Float.
    - apply IH_Bool.
    - apply IH_Null.
    - apply IH_Zero_initializer.
    - apply IH_Cstring.
    - apply IH_None.
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



      
      
      
  
  
  
  
  