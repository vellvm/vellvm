From Coq Require Import ZArith Lia List.

From ExtLib Require Import
     Core.RelDec.

From Vellvm Require Import
     Utils.Tactics
     Utils.ListUtil
     Handlers.FiniteMemory
     Handlers.Serialization
     Semantics.LLVMEvents
     Semantics.Denotation
     Semantics.MemoryAddress
     Semantics.GepM
     Semantics.Memory.Sizeof
     Semantics.Memory.MemBytes.

Module MemBytesTheory(Addr:MemoryAddress.ADDRESS)(LLVMIO: LLVM_INTERACTIONS(Addr))(SIZEOF: Sizeof)(PTOI:PTOI(Addr))(PROVENANCE:PROVENANCE(Addr))(ITOP:ITOP(Addr)(PROVENANCE))(GEP:GEPM(Addr)(LLVMIO))(BYTE_IMPL:ByteImpl(Addr)(LLVMIO)).

  Import LLVMIO.
  Import SIZEOF.
  Import PTOI.
  Import PROVENANCE.
  Import ITOP.
  Import DV.
  Import GEP.

  Module SER := Serialization.Make Addr LLVMIO SIZEOF PTOI PROVENANCE ITOP GEP BYTE_IMPL.
  Import SER.
  Import BYTE.
  Import Den.

  Ltac eval_nseq :=
    match goal with
    | |- context[Nseq ?start ?len] =>
      let HS := fresh "HS" in
      let HSeq := fresh "HSeq" in
      remember (Nseq start len) as HS eqn:HSeq;
      cbv in HSeq;
      subst HS
    end.

  Hint Resolve eq_dec_uvalue_correct : AllBytes.

  Hint Rewrite map_length : AllBytes.
  Hint Rewrite Nseq_length : AllBytes.
  Hint Rewrite N.eqb_refl : AllBytes.
  Hint Rewrite Z.eqb_refl : AllBytes.
  Hint Rewrite rel_dec_eq_true : AllBytes.
  Hint Rewrite sbyte_to_extractbyte_of_uvalue_sbyte : AllBytes.

  Ltac solve_guards_all_bytes :=
    repeat (cbn; autorewrite with AllBytes); eauto with AllBytes.

  Lemma all_bytes_helper_app :
    forall  sbytes sbytes2 start sid uv,
      all_bytes_from_uvalue_helper (Z.of_N start) sid uv sbytes = Some uv ->
      all_bytes_from_uvalue_helper (Z.of_N (start + N.of_nat (length sbytes))) sid uv sbytes2 = Some uv ->
      all_bytes_from_uvalue_helper (Z.of_N start) sid uv (sbytes ++ sbytes2) = Some uv.
  Proof.
    induction sbytes;
      intros sbytes2 start sid uv INIT REST.
    - now rewrite N.add_0_r in REST.
    - cbn.
      pose proof sbyte_to_extractbyte_inv a as (uvb & dtb & idxb & sidb & SBYTE).
      rewrite SBYTE.

      cbn in INIT; rewrite SBYTE in INIT.
      do 3 (break_match; [|solve [inv INIT]]).

      cbn in REST. auto.
      replace (Z.of_N (start + N.pos (Pos.of_succ_nat (Datatypes.length sbytes)))) with (Z.of_N (N.succ start + N.of_nat (Datatypes.length sbytes))) in REST by lia.

      rewrite <- N2Z.inj_succ in *.
      
      apply IHsbytes; auto.
  Qed.

  Lemma to_ubytes_all_bytes_from_uvalue_helper' :
    forall len uv dt sid sbytes start,
      is_supported dt ->
      map (fun n : N => uvalue_sbyte uv dt (UVALUE_IPTR (Z.of_N n)) sid) (Nseq start len) = sbytes ->
      all_bytes_from_uvalue_helper (Z.of_N start) sid uv sbytes = Some uv.
  Proof.
    induction len;
      intros uv dt sid sbytes start SUP TO.
    - inv TO; reflexivity.
    - inv TO.
      rewrite Nseq_S.
      rewrite map_app.
      apply all_bytes_helper_app; eauto.
      + solve_guards_all_bytes.
  Qed.
End MemBytesTheory.

Module SerializationTheory(LLVMIO: LLVM_INTERACTIONS(Addr))(SIZEOF: Sizeof)(PTOI:PTOI(Addr))(PROVENANCE:PROVENANCE(Addr))(ITOP:ITOP(Addr)(PROVENANCE))(GEP:GEPM(Addr)(LLVMIO))(BYTE_IMPL:ByteImpl(Addr)(LLVMIO)).

  Module MBT := MemBytesTheory Addr LLVMIO SIZEOF PTOI PROVENANCE ITOP GEP BYTE_IMPL.
  Import MBT.
  Import MBT.SER.
  Import BYTE.
  Import SIZEOF.

  Module Mem := FiniteMemory.Make LLVMIO PTOI PROVENANCE ITOP SIZEOF GEP BYTE_IMPL.
  Export Mem.

  Lemma to_ubytes_all_bytes_from_uvalue_helper :
    forall uv dt sid sbytes,
      is_supported dt ->
      to_ubytes uv dt sid = sbytes ->
      all_bytes_from_uvalue_helper 0 sid uv sbytes = Some uv.
  Proof.  
    intros uv dt sid sbytes SUP TO.

    change 0%Z with (Z.of_N 0).
    eapply to_ubytes_all_bytes_from_uvalue_helper'; eauto.    
  Qed.

  Lemma to_ubytes_sizeof_dtyp :
    forall uv dt sid,  
      N.of_nat (length (to_ubytes uv dt sid)) = sizeof_dtyp dt.
  Proof.
    intros uv dt sid.
    unfold to_ubytes.
    rewrite map_length, Nseq_length.
    lia.
  Qed.

  Lemma from_ubytes_to_ubytes :
    forall uv dt sid,
      is_supported dt ->
      sizeof_dtyp dt > 0 ->
      from_ubytes (to_ubytes uv dt sid) dt = uv.
  Proof.
    intros uv dt sid SUP SIZE.

    unfold from_ubytes.
    unfold BYTE.all_bytes_from_uvalue.

    rewrite to_ubytes_sizeof_dtyp.
    rewrite N.eqb_refl.

    break_inner_match.
    - (* Contradiction by size *)
      pose proof to_ubytes_sizeof_dtyp uv dt sid as ALLBYTES.
      rewrite Heql in ALLBYTES.

      cbn in *.
      lia.
    - pose proof sbyte_to_extractbyte_inv s as (uv' & dt' & idx' & sid' & SBYTE).
      cbn in *.
      rewrite SBYTE.

      unfold to_ubytes in Heql.
      remember (sizeof_dtyp dt) as sz.
      destruct sz; [inv SIZE|].
      cbn in *.
      pose proof Pos2Nat.is_succ p as [sz Hsz].
      rewrite Hsz in Heql.
      rewrite <- cons_Nseq in Heql.

      cbn in Heql.
      inv Heql.
      cbn.

      solve_guards_all_bytes.
      rewrite sbyte_to_extractbyte_of_uvalue_sbyte in SBYTE.
      inv SBYTE.

      cbn.
      change 1%Z with (Z.of_N 1).
      erewrite to_ubytes_all_bytes_from_uvalue_helper'; eauto.
  Qed.

  Lemma serialize_sbytes_deserialize_sbytes :
    forall uv dt sid sbytes ,
      uvalue_has_dtyp uv dt ->
      is_supported dt ->
      sizeof_dtyp dt > 0 ->
      evalErrSID (serialize_sbytes uv dt) sid = inr (sbytes) ->
      deserialize_sbytes sbytes dt = inr uv.
  Proof.
    intros uv dt sid sbytes TYP SUP SIZE SER.
    induction TYP;
      try solve [unfold serialize_sbytes in SER;
                 inv SER;
                 unfold deserialize_sbytes;
                 rewrite from_ubytes_to_ubytes; eauto
                | cbn in *;
                  match goal with
                  | |- deserialize_sbytes _ ?t = _ =>
                    cbn in *;
                    destruct t; cbn; inv SER;
                    rewrite from_ubytes_to_ubytes; eauto
                  end
                ].
    - inv SUP; exfalso; apply H; constructor.
    - rewrite sizeof_dtyp_void in SIZE. inv SIZE.
  Qed.
