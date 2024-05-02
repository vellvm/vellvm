From Coq Require Import String List ZArith.

From ExtLib Require Import Structures.Monads.

From Vellvm Require Import
     Syntax.DynamicTypes
     Semantics.DynamicValues
     Semantics.LLVMEvents

     Utils.Monads
     Utils.OptionUtil
     Utils.ListUtil
     Utils.Error
     Utils.MonadReturnsLaws
     Utils.MapMonadExtra
     Utils.Tactics.

From Mem Require Import
  StoreId
  Addresses.MemoryAddress.

From LLVM_Memory Require Import
  Sizeof
  Intptr.

Import Basics.Basics.Monads.

Import ListNotations.
Import MonadNotation.

Module Type ByteImpl(Addr:ADDRESS)(IP:INTPTR)(SIZEOF:Sizeof)(LLVMEvents: LLVM_INTERACTIONS(Addr)(IP)(SIZEOF)).
  Import LLVMEvents.
  Import DV.

  Parameter SByte : Set.

  (* Get a specific byte of a uvalue of a given type.

     Arguments are:

     - The uvalue to get the byte of.
     - The type of the uvalue that we are getting the byte of.
     - The index of the byte (as a uvalue).
     - The store id for the byte we are creating.
   *)
  Parameter uvalue_sbyte : uvalue -> dtyp -> N -> store_id -> SByte.

  (* Turn an SByte into a UVALUE_ExtractByte value *)
  Parameter sbyte_to_extractbyte : SByte -> uvalue.

  Parameter sbyte_to_extractbyte_inv  :
    forall (b : SByte),
      {uv & {dt & {idx & {sid & sbyte_to_extractbyte b = UVALUE_ExtractByte uv dt idx sid}}}}.

  Parameter sbyte_to_extractbyte_of_uvalue_sbyte :
    forall uv dt idx sid,
      sbyte_to_extractbyte (uvalue_sbyte uv dt idx sid) =  UVALUE_ExtractByte uv dt idx sid.
End ByteImpl.

Module Type ByteModule(Addr:ADDRESS)(IP:INTPTR)(SIZEOF:Sizeof)(LLVMEvents:LLVM_INTERACTIONS(Addr)(IP)(SIZEOF))(Byte:ByteImpl(Addr)(IP)(SIZEOF)(LLVMEvents)).
  Export Byte.
  Import LLVMEvents.
  Import DV.
  Import SIZEOF.

  Fixpoint all_bytes_from_uvalue_helper (idx' : N) (sid' : store_id) (parent : uvalue) (bytes : list SByte) : option uvalue
    := match bytes with
       | [] => Some parent
       | sbyte::bytes =>
         match sbyte_to_extractbyte sbyte with
         | UVALUE_ExtractByte uv dt idx sid =>
           guard_opt (N.eqb idx idx');;
           guard_opt (RelDec.rel_dec uv parent);;
           guard_opt (N.eqb sid sid');;
           all_bytes_from_uvalue_helper (N.succ idx') sid' parent bytes
         | _ => None
         end
       end.

  Definition all_bytes_from_uvalue (t : dtyp) (bytes : list SByte) : option uvalue
    := match bytes with
       | nil => None
       | cons sbyte xs =>
         match sbyte_to_extractbyte sbyte with
         | UVALUE_ExtractByte uv dt idx sid =>
           guard_opt (dtyp_eqb t dt);;
           guard_opt (Coqlib.proj_sumbool (@uvalue_has_dtyp_dec uv dt));;
           all_bytes_from_uvalue_helper 0 sid uv bytes
         | _ => None
         end
       end.

  Definition to_ubytes (uv :  uvalue) (dt : dtyp) (sid : store_id) : list SByte
    := map
         (fun n => uvalue_sbyte uv dt n sid)
         (Nseq 0 (N.to_nat (sizeof_dtyp dt))).

  Fixpoint all_extract_bytes_from_uvalue_helper (idx' : N) (sid' : store_id) (dt' : dtyp) (parent : uvalue) (bytes : list uvalue) : option uvalue
    := match bytes with
       | [] => Some parent
       | (UVALUE_ExtractByte uv dt idx sid)::bytes =>
         guard_opt (N.eqb idx idx');;
         guard_opt (RelDec.rel_dec uv parent);;
         guard_opt (N.eqb sid sid');;
         guard_opt (dtyp_eqb dt dt');;
         all_extract_bytes_from_uvalue_helper (N.succ idx') sid' dt' parent bytes
       | _ => None
       end.

  Lemma all_extract_bytes_from_uvalue_helper_some :
    forall uv_bytes_fin idx sid dt parent u,
      all_extract_bytes_from_uvalue_helper idx sid dt parent uv_bytes_fin = Some u ->
      u = parent.
  Proof.
    induction uv_bytes_fin;
      intros idx sid dt parent u EXTRACT.
    - inv EXTRACT; auto.
    - cbn in EXTRACT.
      repeat break_match_hyp_inv.
      eapply IHuv_bytes_fin; eauto.
  Qed.

  Lemma all_extract_bytes_from_uvalue_helper_strict_subterm :
    forall uv_bytes_fin idx sid dt parent u,
      uvalue_strict_subterm parent (UVALUE_ConcatBytes uv_bytes_fin dt) ->
      all_extract_bytes_from_uvalue_helper idx sid dt parent uv_bytes_fin = Some u ->
      uvalue_strict_subterm u (UVALUE_ConcatBytes uv_bytes_fin dt).
  Proof.
    intros uv_bytes_fin idx sid dt parent u SUB EXTRACT.
    eapply all_extract_bytes_from_uvalue_helper_some in EXTRACT.
    subst; auto.
  Qed.

  (* Check that store ids, uvalues, and types match up, as well as
       that the extract byte indices are in the right order *)
  Definition all_extract_bytes_from_uvalue (t : dtyp) (bytes : list uvalue) : option uvalue
    := match bytes with
       | nil => None
       | (UVALUE_ExtractByte uv dt idx sid)::xs =>
           guard_opt (dtyp_eqb t dt);;
           all_extract_bytes_from_uvalue_helper 0 sid dt uv bytes
       | _ => None
       end.

  Lemma all_extract_bytes_from_uvalue_strict_subterm :
    forall uv_bytes_fin dt u,
      all_extract_bytes_from_uvalue dt uv_bytes_fin = Some u ->
      uvalue_strict_subterm u (UVALUE_ConcatBytes uv_bytes_fin dt).
  Proof.
    intros uv_bytes_fin dt u EXTRACT.
    unfold all_extract_bytes_from_uvalue in EXTRACT.
    break_match_hyp_inv.
    break_match_hyp_inv.
    break_match_hyp_inv.
    assert (dt = dt0).
    { unfold guard_opt in Heqo.
      destruct (dtyp_eqb dt dt0) eqn:DT; inv Heqo.
      eapply dtyp_eqb_eq; eauto.
    }
    subst.
    eapply all_extract_bytes_from_uvalue_helper_strict_subterm
      with (idx:=0)
           (sid:=sid)
           (parent:=u1); cbn; auto.

    eapply Relation_Operators.t_trans.
    2: {
      constructor; constructor; left; reflexivity.
    }
    constructor; constructor.
  Qed.

  Lemma all_extract_bytes_from_uvalue_success_inv :
    forall uvs dt u,
      all_extract_bytes_from_uvalue dt uvs = Some u ->
      exists sid uvs', uvs = (UVALUE_ExtractByte u dt 0 sid :: uvs').
  Proof.
    induction uvs; intros dt u EXTRACT.
    - cbn in EXTRACT; inv EXTRACT.
    - cbn in EXTRACT.
      destruct a; inv EXTRACT.
      unfold guard_opt in *.
      repeat break_match_hyp_inv.
      apply all_extract_bytes_from_uvalue_helper_some in H1; subst.
      eapply dtyp_eqb_eq in Heqb3; subst.
      apply N.eqb_eq in Heqb2; subst.
      exists sid, uvs.
      reflexivity.
  Qed.

  Definition from_ubytes (bytes : list SByte) (dt : dtyp) : uvalue
    :=
      match N.eqb (N.of_nat (length bytes)) (sizeof_dtyp dt), all_bytes_from_uvalue dt bytes with
      | true, Some uv => uv
      | _, _ => UVALUE_ConcatBytes (map sbyte_to_extractbyte bytes) dt
      end.

  Lemma to_ubytes_sizeof :
    forall uv dt sid,
      N.of_nat (length (to_ubytes uv dt sid)) = sizeof_dtyp dt.
  Proof.
    intros uv dt sid.
    unfold to_ubytes.
    rewrite map_length.
    rewrite Nseq_length.
    apply Nnat.N2Nat.id.
  Qed.

  Definition sbyte_sid (byte : SByte) : err store_id :=
    match sbyte_to_extractbyte byte with
    | UVALUE_ExtractByte uv dt idx sid => inr sid
    | _ => inl "Invalid sbyte, did not convert to extractbyte."%string
    end.
End ByteModule.

Module Byte (Addr:ADDRESS)(IP:INTPTR)(SIZEOF:Sizeof)(LLVMEvents:LLVM_INTERACTIONS(Addr)(IP)(SIZEOF))(Byte:ByteImpl(Addr)(IP)(SIZEOF)(LLVMEvents)) : ByteModule Addr IP SIZEOF LLVMEvents Byte.
  Include (ByteModule Addr IP SIZEOF LLVMEvents Byte).
End Byte.
