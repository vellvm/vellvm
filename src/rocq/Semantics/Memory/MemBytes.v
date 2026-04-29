From Stdlib Require Import String List ZArith.

From ExtLib Require Import Structures.Monads.

From Vellvm Require Import
     Syntax.DynamicTypes
     Semantics.DynamicValues
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Semantics.LLVMParams
     Semantics.StoreId
     Utils.Monads
     Utils.OptionUtil
     Utils.ListUtil
     Utils.Error
     Utils.MonadReturnsLaws
     Utils.MapMonadExtra
     Utils.Tactics.

Import Basics.Basics.Monads.

Import ListNotations.
Import MonadNotation.

Module Type ByteImpl (LP:LLVMParams).
  Import LP.DV.

  (* Parameter SByte : Set. *)
  Variant SByte : Type :=
    | dvalue_sbyte (dv : dvalue) (dt : dtyp) (idx : N) (sid : store_id).

  (* Get a specific byte of a uvalue of a given type.

     Arguments are:

     - The dvalue to get the byte of.
     - The type of the uvalue that we are getting the byte of.
     - The index of the byte (as a uvalue).
     - The store id for the byte we are creating.
   *)
  (* Parameter dvalue_sbyte : dvalue -> dtyp -> N -> store_id -> SByte. *)

  (* Turn an SByte into a DVALUE_ExtractByte value *)
  (* Parameter sbyte_to_extractbyte : SByte -> dvalue. *)
  (* Parameter sbyte_to_extractbyte : SByte -> (dvalue * dtyp * N * store_id). *)

End ByteImpl.

Module Type ByteModule (LP:LLVMParams)(Byte:ByteImpl(LP)).
  Export Byte.
  Import LP.DV.
  Import LP.SZ.
  Fixpoint all_bytes_from_dvalue_helper
    (idx' : N) (sid' : store_id) (parent : dvalue) (bytes : list SByte) : option dvalue :=
    match bytes with
    | [] => Some parent
    | sbyte::bytes =>
        let '(dvalue_sbyte dv dt idx sid) := sbyte in
        guard_opt (N.eqb idx idx');;
        guard_opt (RelDec.rel_dec dv parent);;
        guard_opt (N.eqb sid sid');;
        all_bytes_from_dvalue_helper (N.succ idx') sid' parent bytes
    end.

  Definition all_bytes_from_dvalue (t : dtyp) (bytes : list SByte) : option dvalue
    := match bytes with
       | nil => None
       | cons sbyte xs =>
           let '(dvalue_sbyte dv dt idx sid) := sbyte in
           guard_opt (dtyp_eqb t dt);;
           guard_opt (Rocqlib.proj_sumbool (@dvalue_has_dtyp_dec dv dt));;
           all_bytes_from_dvalue_helper 0 sid dv bytes
       end.

  Definition to_sbytes (dv :  dvalue) (dt : dtyp) (sid : store_id) : list SByte
    := map
         (fun n => dvalue_sbyte dv dt n sid)
         (Nseq 0 (N.to_nat (sizeof_dtyp dt))).

  Fixpoint all_extract_bytes_from_dvalue_helper
    (idx' : N) (sid' : store_id) (dt' : dtyp) (parent : dvalue) (bytes : list SByte) : option dvalue
    := match bytes with
       | [] => Some parent
       | (dvalue_sbyte dv dt idx sid)::bytes =>
           guard_opt (N.eqb idx idx');;
           guard_opt (RelDec.rel_dec dv parent);;
           guard_opt (N.eqb sid sid');;
           guard_opt (dtyp_eqb dt dt');;
           all_extract_bytes_from_dvalue_helper (N.succ idx') sid' dt' parent bytes
       end.

  Lemma all_extract_bytes_from_dvalue_helper_some :
    forall dv_bytes_fin idx sid dt parent u,
      all_extract_bytes_from_dvalue_helper idx sid dt parent dv_bytes_fin = Some u ->
      u = parent.
  Proof.
    induction dv_bytes_fin;
      intros idx sid dt parent u EXTRACT.
    - inv EXTRACT; auto.
    - cbn in EXTRACT.
      repeat break_match_hyp_inv.
      eapply IHdv_bytes_fin; eauto.
  Qed.

  (* Check that store ids, uvalues, and types match up, as well as
     that the extract byte indices are in the right order *)
  Definition all_extract_bytes_from_dvalue (t : dtyp) (bytes : list SByte) : option dvalue
    := match bytes with
       | nil => None
       | (dvalue_sbyte dv dt idx sid)::_ =>
           guard_opt (dtyp_eqb t dt);;
           all_extract_bytes_from_dvalue_helper 0 sid dt dv bytes
       end.

  (* TODO: this would be the anologue to uvalue_strict_subterm w.r.t. UVALUE_ConcatBytes
     Do we need it?
   *)
  Variant dvalue_strict_subterm_sbytes : dvalue -> list SByte -> Prop :=
    | dsss dv dv' dt idx sid bytes :
      dvalue_strict_subterm dv' dv ->
      In (dvalue_sbyte dv dt idx sid) bytes ->
      dvalue_strict_subterm_sbytes dv' bytes.
  
  (* Lemma all_extract_bytes_from_uvalue_helper_strict_subterm : *)
  (*   forall uv_bytes_fin idx sid dt parent u, *)
  (*     dvalue_strict_subterm_sbytes parent bytes -> *)
  (*     uvalue_strict_subterm parent (UVALUE_ConcatBytes uv_bytes_fin dt) -> *)
  (*     all_extract_bytes_from_uvalue_helper idx sid dt parent uv_bytes_fin = Some u -> *)
  (*     uvalue_strict_subterm u (UVALUE_ConcatBytes uv_bytes_fin dt). *)
  (* Proof. *)
  (*   intros uv_bytes_fin idx sid dt parent u SUB EXTRACT. *)
  (*   eapply all_extract_bytes_from_uvalue_helper_some in EXTRACT. *)
  (*   subst; auto. *)
  (* Qed. *)

  (* Lemma all_extract_bytes_from_uvalue_strict_subterm : *)
  (*   forall uv_bytes_fin dt u, *)
  (*     all_extract_bytes_from_uvalue dt uv_bytes_fin = Some u -> *)
  (*     uvalue_strict_subterm u (UVALUE_ConcatBytes uv_bytes_fin dt). *)
  (* Proof. *)
  (*   intros uv_bytes_fin dt u EXTRACT. *)
  (*   unfold all_extract_bytes_from_uvalue in EXTRACT. *)
  (*   break_match_hyp_inv. *)
  (*   break_match_hyp_inv. *)
  (*   break_match_hyp_inv. *)
  (*   assert (dt = dt0). *)
  (*   { unfold guard_opt in Heqo. *)
  (*     destruct (dtyp_eqb dt dt0) eqn:DT; inv Heqo. *)
  (*     eapply dtyp_eqb_eq; eauto. *)
  (*   } *)
  (*   subst. *)
  (*   eapply all_extract_bytes_from_uvalue_helper_strict_subterm *)
  (*     with (idx:=0) *)
  (*          (sid:=sid) *)
  (*          (parent:=u1); cbn; auto. *)

  (*   eapply Relation_Operators.t_trans. *)
  (*   2: { *)
  (*     constructor; constructor; left; reflexivity. *)
  (*   } *)
  (*   constructor; constructor. *)
  (* Qed. *)

  (* Lemma all_extract_bytes_from_uvalue_success_inv : *)
  (*   forall uvs dt u, *)
  (*     all_extract_bytes_from_uvalue dt uvs = Some u -> *)
  (*     exists sid uvs', uvs = (UVALUE_ExtractByte u dt 0 sid :: uvs'). *)
  (* Proof. *)
  (*   induction uvs; intros dt u EXTRACT. *)
  (*   - cbn in EXTRACT; inv EXTRACT. *)
  (*   - cbn in EXTRACT. *)
  (*     destruct a; inv EXTRACT. *)
  (*     unfold guard_opt in *. *)
  (*     repeat break_match_hyp_inv. *)
  (*     apply all_extract_bytes_from_uvalue_helper_some in H1; subst. *)
  (*     eapply dtyp_eqb_eq in Heqb3; subst. *)
  (*     apply N.eqb_eq in Heqb2; subst. *)
  (*     exists sid, uvs. *)
  (*     reflexivity. *)
  (* Qed. *)

  (* Definition from_ubytes (bytes : list SByte) (dt : dtyp) : uvalue *)
  (*   := *)
  (*   match N.eqb (N.of_nat (length bytes)) (sizeof_dtyp dt), *)
  (*         all_bytes_from_uvalue dt bytes with *)
  (*     | true, Some uv => uv *)
  (*     | _, _ => UVALUE_ConcatBytes (map sbyte_to_extractbyte bytes) dt *)
  (*     end. *)

  (* Lemma to_dbytes_sizeof : *)
  (*   forall uv dt sid, *)
  (*     N.of_nat (length (to_ubytes uv dt sid)) = sizeof_dtyp dt. *)
  (* Proof. *)
  (*   intros uv dt sid. *)
  (*   unfold to_ubytes. *)
  (*   rewrite length_map. *)
  (*   rewrite Nseq_length. *)
  (*   apply Nnat.N2Nat.id. *)
  (* Qed. *)

  Definition sbyte_sid (byte : SByte) : store_id :=
    let '(dvalue_sbyte _ _ _ sid) := byte in sid.
 
End ByteModule.

Module Byte (LP:LLVMParams)(Byte:ByteImpl LP). 
  Include (ByteModule LP Byte).
End Byte.
