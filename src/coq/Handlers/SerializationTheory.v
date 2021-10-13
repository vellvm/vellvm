From Coq Require Import ZArith Lia List String.

From ExtLib Require Import
     Core.RelDec
     Structures.Monads.

From Vellvm Require Import
     Utils.Tactics
     Utils.ListUtil
     Utils.Error
     Handlers.FiniteMemory
     Handlers.Serialization
     Semantics.LLVMEvents
     Semantics.Denotation
     Semantics.MemoryAddress
     Semantics.GepM
     Semantics.Memory.Sizeof
     Semantics.Memory.MemBytes
     Semantics.Memory.ErrSID.

Module MemBytesTheory(Addr:MemoryAddress.ADDRESS)(SIZEOF: Sizeof)(LLVMIO: LLVM_INTERACTIONS(Addr)(SIZEOF))(PTOI:PTOI(Addr))(PROVENANCE:PROVENANCE(Addr))(ITOP:ITOP(Addr)(PROVENANCE))(GEP:GEPM(Addr)(SIZEOF)(LLVMIO))(BYTE_IMPL:ByteImpl(Addr)(SIZEOF)(LLVMIO)).

  Import LLVMIO.
  Import SIZEOF.
  Import PTOI.
  Import PROVENANCE.
  Import ITOP.
  Import DV.
  Import GEP.

  Module SER := Serialization.Make Addr SIZEOF LLVMIO PTOI PROVENANCE ITOP GEP BYTE_IMPL.
  Import SER.

  Module BYTE := Byte Addr SIZEOF LLVMIO BYTE_IMPL.
  Export BYTE.

  Import BYTE.
  Import BYTE_IMPL.

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
      all_bytes_from_uvalue_helper (Z.of_N (start + N.of_nat (List.length sbytes))) sid uv sbytes2 = Some uv ->
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
      N.of_nat (List.length (to_ubytes uv dt sid)) = sizeof_dtyp dt.
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
    unfold all_bytes_from_uvalue.

    rewrite to_ubytes_sizeof_dtyp.
    rewrite N.eqb_refl.

    break_inner_match.
    - (* Contradiction by size *)
      pose proof to_ubytes_sizeof_dtyp uv dt sid.
      rewrite Heql in H.

      cbn in *.
      lia.
    - pose proof sbyte_to_extractbyte_inv s as (uvb & dtb & idxb & sidb & SBYTE).
      rewrite SBYTE.
      cbn in *.

      unfold to_ubytes in Heql.
      remember (sizeof_dtyp dt) as sz.
      destruct sz; [inv SIZE|].
      cbn in *.
      pose proof Pos2Nat.is_succ p as [sz Hsz].
      rewrite Hsz in Heql.
      rewrite <- cons_Nseq in Heql.

      cbn in Heql.
      inv Heql.
      rewrite sbyte_to_extractbyte_of_uvalue_sbyte in SBYTE.
      inv SBYTE.
      rewrite sbyte_to_extractbyte_of_uvalue_sbyte.
      cbn.

      solve_guards_all_bytes.

      cbn.
      change 1%Z with (Z.of_N 1).
      erewrite to_ubytes_all_bytes_from_uvalue_helper'; eauto.
  Qed.
End MemBytesTheory.

Module SerializationTheory(Addr:MemoryAddress.ADDRESS)(SIZEOF: Sizeof)(LLVMIO: LLVM_INTERACTIONS(Addr)(SIZEOF))(PTOI:PTOI(Addr))(PROVENANCE:PROVENANCE(Addr))(ITOP:ITOP(Addr)(PROVENANCE))(GEP:GEPM(Addr)(SIZEOF)(LLVMIO))(BYTE_IMPL:ByteImpl(Addr)(SIZEOF)(LLVMIO)).

  Import LLVMIO.

  Module MBT := MemBytesTheory Addr SIZEOF LLVMIO PTOI PROVENANCE ITOP GEP BYTE_IMPL.
  Import MBT.
  Import MBT.SER.
  Import BYTE.
  Import SIZEOF.

  Module Mem := FiniteMemory.Make Addr SIZEOF LLVMIO PTOI PROVENANCE ITOP GEP BYTE_IMPL.
  Import Mem.

  Module ESID := ERRSID Addr SIZEOF LLVMIO PROVENANCE.
  Import ESID.

  Import DynamicTypes.

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
      N.of_nat (List.length (to_ubytes uv dt sid)) = sizeof_dtyp dt.
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
    unfold all_bytes_from_uvalue.

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

  (* TODO: move this *)
  Ltac tactic_on_non_aggregate_uvalues x t :=
    match x with
    | (UVALUE_Struct _) =>
      idtac
    | (UVALUE_Packed_struct _) =>
      idtac
    | (UVALUE_Array _ _) =>
      idtac
    | (UVALUE_Vector _ _) =>
      idtac
    | _ =>
      t
    end.

  Ltac tactic_on_non_aggregate_dtyps x t :=
    match x with
    | (DTYPE_Struct _) =>
      idtac
    | (DTYPE_Packed_struct _) =>
      idtac
    | (DTYPE_Array _ _) =>
      idtac
    | (DTYPE_Vector _ _) =>
      idtac
    | _ =>
      t
    end.


  Ltac eval_serialize_sbytes_hyp :=
    match goal with
    (* Try easy case first for speedup *)
    | H: ErrSID_evals_to
           (serialize_sbytes ?x ?dt)
           ?sbytes ?sid ?prov |- _ =>
      tactic_on_non_aggregate_uvalues x ltac:(cbn in H; inv H)
    | H: context[serialize_sbytes ?x ?dt] |- _ =>
      tactic_on_non_aggregate_uvalues x ltac:(cbn in H; inv H)
    end.

  Lemma concretize_ibinop_inv:
    forall op x y dv,
      concretize_succeeds (UVALUE_IBinop op x y) ->
      concretize (UVALUE_IBinop op x y) dv ->
      exists dx dy,
        concretize x dx /\
          concretize y dy /\
          eval_iop op dx dy = ret dv.
  Proof.
    intros op x y dv SUCC CONC.

    rewrite concretize_equation in CONC.
    red in CONC.
    rewrite concretize_uvalueM_equation in CONC.

    cbn in CONC.
    destruct CONC as (ma & k' & pama & eqm & REST).

    destruct ma as [[[uba | [erra | a]]]] eqn:Hma; cbn; auto.

    (* First thing is ub... *)
    (* This should be ruled out by SUCC *)
    { cbn in SUCC.
      unfold concretize_succeeds, concretize_fails in SUCC.
      red in SUCC.

      exfalso.
      apply SUCC.

      red. rewrite concretize_uvalueM_equation.
      cbn.

      unfold bind_RefineProp.

      eexists.
      exists ret.

      split; [apply pama|].
      split; auto.

      intros a H.
      cbn in H.
      destruct uba; contradiction.
    }

    (* First thing is failure... *)
    (* This should be ruled out by SUCC *)
    { cbn in SUCC.
      unfold concretize_succeeds, concretize_fails in SUCC.
      red in SUCC.

      exfalso.
      apply SUCC.

      red. rewrite concretize_uvalueM_equation.
      cbn.

      unfold bind_RefineProp.

      eexists.
      exists ret.

      split; [apply pama|].
      split; auto.

      intros a H.
      cbn in H.
      destruct erra; contradiction.
    }

    specialize (REST a).
    forward REST; [reflexivity|].

    destruct REST as (mb & kb & pbmb & eqmb & REST).

    unfold concretize_succeeds, concretize_fails, concretize_u in SUCC.
    rewrite concretize_uvalueM_equation in SUCC.
    cbn in SUCC.
    unfold bind_RefineProp in SUCC.

    destruct mb as [[[ubb | [errb | b]]]] eqn:Hmb; cbn; auto.

    (* y raises UB *)
    { exfalso.
      apply SUCC.

      eexists.
      exists (fun _ => raise_ub "").

      
      split; [apply pama|].
      split; cbn; auto.

      intros a0 H; subst.

      eexists.
      exists ret.

      split; [apply pbmb|].
      split; auto.

      intros a H.
      cbn in H.
      destruct ubb; contradiction.
    }

    (* y fails *)
    { exfalso.
      apply SUCC.

      eexists.
      exists (fun _ => raise_ub "").

      
      split; [apply pama|].
      split; cbn; auto.

      intros a0 H; subst.

      eexists.
      exists ret.

      split; [apply pbmb|].
      split; auto.

      intros a H.
      cbn in H.
      destruct errb; contradiction.
    }

    (* Both x and y successfully concretized.

         Now eval_iop must succeed too.
     *)
    specialize (REST b).
    forward REST; [reflexivity|].

    destruct (eval_iop op a b) as [[[ubz | [errz | z]]]] eqn:Hmz; cbn; auto.

    (* Eval raises ub *)
    { exfalso.
      apply SUCC.

      eexists.
      exists (fun _ => raise_ub "").

      split; [apply pama|].
      split; cbn; auto.

      intros a0 H; subst.

      eexists.
      exists (fun _ => raise_ub "").

      split; [apply pbmb|].
      split; cbn; auto.

      intros a H; subst.

      rewrite Hmz.
      reflexivity.
    }

    (* Eval fails *)
    { exfalso.
      apply SUCC.

      eexists.
      exists (fun _ => raise_ub "").

      split; [apply pama|].
      split; cbn; auto.

      intros a0 H; subst.

      eexists.
      exists (fun _ => raise_ub "").

      split; [apply pbmb|].
      split; cbn; auto.

      intros a H; subst.

      rewrite Hmz.
      reflexivity.
    }

    cbn in eqmb.
    cbn in eqm.

    destruct (kb b) as [[[ubkbb | [errkbb | kbb]]]] eqn:Hkbb; try contradiction; subst.
    cbn in eqmb.
    
    destruct (k' a) as [[[ubka | [errka | ka]]]] eqn:Hka; try contradiction; subst.
    cbn in eqm; subst.

    exists a. exists b.
    auto.
  Qed.

  Lemma serialize_sbytes_deserialize_sbytes :
    forall uv dt sid prov sbytes ,
      uvalue_has_dtyp uv dt ->
      is_supported dt ->
      sizeof_dtyp dt > 0 ->
      ErrSID_evals_to (serialize_sbytes uv dt) sbytes sid prov ->
      deserialize_sbytes sbytes dt = inr uv.
  Proof.
    intros uv dt sid prov sbytes TYP SUP SIZE SER.
    induction TYP.

    rewrite serialize_sbytes_equation in SER; cbn in SER; inv SER; cbn; rewrite from_ubytes_to_ubytes; eauto.

    1-5: match goal with
          (* Try easy case first for speedup *)
          | |- _ = inr ?x =>
            tactic_on_non_aggregate_uvalues x ltac:(try (rewrite serialize_sbytes_equation in SER; cbn in SER; inv SER; cbn; rewrite from_ubytes_to_ubytes; eauto))
          end.

    (* Poison arrays *)
    { admit.
    }

    (* Poison vectors *)
    { admit.
    }

    (* Poison structs *)
    { admit.
    }

    { admit.
    }

    (* Poison packed structs *)
    { admit.
    }

    { admit.
    }

    (* Poison *)
    { destruct H as (NV & NSTRUCT & NPACKED & NARRAY & NVECTOR).
      destruct t;
      match goal with
      (* Try easy case first for speedup *)
      | |- _ = inr (UVALUE_Poison DynamicTypes.DTYPE_Void) =>
        cbn in NV; contradiction
      | |- _ = inr (UVALUE_Poison ?x) =>
        tactic_on_non_aggregate_dtyps x ltac:(try (rewrite serialize_sbytes_equation in SER; cbn in SER; inv SER; cbn; rewrite from_ubytes_to_ubytes; eauto))
      end.

      all: exfalso;
        match goal with
        | H: _ |- _ =>
          solve [eapply H; eauto]
        end.
    }

    (* Undef arrays *)
    { admit.
    }

    (* Undef vectors *)
    { admit.
    }

    (* Undef structs *)
    { admit.
    }

    { admit.
    }

    (* Undef packed structs *)
    { admit.
    }

    { admit.
    }


    (* Undef *)
    { destruct H as (NV & NSTRUCT & NPACKED & NARRAY & NVECTOR).
      destruct t;
      match goal with
      (* Try easy case first for speedup *)
      | |- _ = inr (UVALUE_Undef DynamicTypes.DTYPE_Void) =>
        cbn in NV; contradiction
      | |- _ = inr (UVALUE_Undef ?x) =>
        tactic_on_non_aggregate_dtyps x ltac:(try (rewrite serialize_sbytes_equation in SER; cbn in SER; inv SER; cbn; rewrite from_ubytes_to_ubytes; eauto))
      end.

      all: exfalso;
        match goal with
        | H: _ |- _ =>
          solve [eapply H; eauto]
        end.
    }

    match goal with
    (* Try easy case first for speedup *)
    | |- _ = inr ?x =>
      tactic_on_non_aggregate_uvalues x ltac:(try (rewrite serialize_sbytes_equation in SER; cbn in SER; inv SER; cbn; rewrite from_ubytes_to_ubytes; eauto))
    end.    

(*     { destruct t. *)
(*       1-12: match goal with *)
(*           (* Try easy case first for speedup *) *)
(*           | |- _ = inr ?x => *)
(*             tactic_on_non_aggregate_uvalues x ltac:(try (rewrite serialize_sbytes_equation in SER; cbn in SER; inv SER; cbn; rewrite from_ubytes_to_ubytes; eauto)) *)
(*           end. *)

(*       (* No void undefs *) *)
(*       contradiction. *)

(*       (* Aggregates *) *)
(*       (* Arrays *) *)
(*       - rewrite serialize_sbytes_equation in SER. *)

(*         (* Errr...  *)

(*            Right hand side is:  *)

(*            inr (UVALUE_Undef (DynamicTypes.DTYPE_Array sz t)) *)

(*            Because this lemma is saying that if I serialize *)
(*            UVALUE_Undef (DynamicTypes.DTYPE_Array sz t), then when I *)
(*            deserialize the result I should get *)
(*            UVALUE_Undef (DynamicTypes.DTYPE_Array sz t) back. *)

(*            I've added special cases for aggregate types in *)
(*            serialize_sbytes for undef so they get serialized with *)
(*            undef for each element / field... *)

(*            The problem is that when these are deserialized I should *)
(*            get, for instance... *)

(*            UVALUE_Array [UVALUE_Undef t; ... ; UVALUE_Undef t ] *)

(*            Instead of just *)

(*            UVALUE_Undef (DynamicTypes.DTYPE_Array sz t) *)

(*            These values should be equivalent, but they have different *)
(*            representations... *)
(*          *) *)
(*         (* unfold deserialize_sbytes,deserialize_sbytes_func. *) *)
(*         (* cbn. *) *)
(*         (* TODO: probably need an equation for rewriting *) *)
      
(*       match goal with *)
(*           (* Try easy case first for speedup *) *)
(*           | |- _ = inr ?x => *)
(*             tactic_on_non_aggregate_uvalues x ltac:(try (rewrite serialize_sbytes_equation in SER; cbn in SER; inv SER; cbn; rewrite from_ubytes_to_ubytes; eauto)) *)
(*           end. *)

(* (*       cbn. *) *)
(* (*       match goal with *) *)
(* (*       (* Try easy case first for speedup *) *) *)
(* (*       | |- _ = inr ?x => *) *)
(* (*         tactic_on_non_aggregate_uvalues x ltac:(try (rewrite serialize_sbytes_equation in SER; cbn in SER; inv SER; cbn; rewrite from_ubytes_to_ubytes; eauto)) *) *)
(* (*       end. *) *)


(* (*     } *) *)
    
(* (*     1-12: match goal with *) *)
(* (*           (* Try easy case first for speedup *) *) *)
(* (*           | |- _ = inr ?x => *) *)
(* (*             tactic_on_non_aggregate_uvalues x ltac:(try (rewrite serialize_sbytes_equation in SER; cbn in SER; inv SER; cbn; rewrite from_ubytes_to_ubytes; eauto)) *) *)
(* (*           end. *) *)

(* (*     { cbn in SER. *) *)
(* (*       inv SER. *) *)
(* (*       inv SUP. *) *)
(* (*       - cbn; rewrite from_ubytes_to_ubytes; [reflexivity|constructor|auto]. *) *)
(* (*       - cbn; rewrite from_ubytes_to_ubytes; [reflexivity|constructor|auto]. *) *)
(* (*       - cbn; rewrite from_ubytes_to_ubytes; [reflexivity|constructor|auto]. *) *)
(* (*       - cbn; rewrite from_ubytes_to_ubytes; [reflexivity|constructor|auto]. *) *)
(* (*       - cbn; rewrite from_ubytes_to_ubytes; [reflexivity|constructor|auto]. *) *)
(* (*       - (* Void... Shouldn't have void undef *) *) *)
(* (*         rewrite sizeof_dtyp_void in SIZE. lia. *) *)
(* (*       - cbn; rewrite from_ubytes_to_ubytes; [reflexivity|constructor|auto]. *) *)
(* (*       - cbn; rewrite from_ubytes_to_ubytes; [reflexivity|constructor|auto]. *) *)
(* (*       - (* Arrays... Aggregate types *) *) *)
(* (*         cbn. *) *)
(* (*         cbn; rewrite from_ubytes_to_ubytes; [reflexivity|constructor|auto]. *) *)

(* (*       cbn. *) *)
(* (*       rewrite from_ubytes_to_ubytes. *) *)
(* (*       reflexivity. *) *)
(* (*       unfold deserialize_sbytes, deserialize_sbytes_func. *) *)


(* (*       match goal with          (* Try easy case first for speedup *) *) *)
(* (*           | |- _ = inr ?x => *) *)
(* (*             tactic_on_non_aggregate_uvalues x ltac:(try (cbn in SER; inv SER; cbn; rewrite from_ubytes_to_ubytes; eauto)) *) *)
(* (*     end. *) *)

(* (*     cbn. *) *)
(* (*     cbn. *) *)


(* (*     cbn. *) *)
(* (*     cbn in SER. *) *)
(* (*     inv SER. *) *)
(* (*     cbn. *) *)
(* (*     rewrite from_ubytes_to_ubytes. *) *)
(* (*     eauto. *) *)
(* (* (*     match goal with *) *) *)
(* (* (*           (* Try easy case first for speedup *) *) *) *)
(* (* (*           | |- _ = inr ?x => *) *) *)
(* (* (*             tactic_on_non_aggregate_uvalues x ltac:(cbn in SER; inv SER) *) *) *)
(* (* (*           end; *) *) *)
(* (* (*       cbn; rewrite from_ubytes_to_ubytes; eauto. *) *) *)
(* (* (*     match goal with *) *) *)
(* (* (*           (* Try easy case first for speedup *) *) *) *)
(* (* (*           | |- _ = inr ?x => *) *) *)
(* (* (*             tactic_on_non_aggregate_uvalues x ltac:(cbn in SER; inv SER) *) *) *)
(* (* (*           end; *) *) *)
(* (* (*       cbn; rewrite from_ubytes_to_ubytes; eauto. *) *) *)
(* (* (*     match goal with *) *) *)
(* (* (*           (* Try easy case first for speedup *) *) *) *)
(* (* (*           | |- _ = inr ?x => *) *) *)
(* (* (*             tactic_on_non_aggregate_uvalues x ltac:(cbn in SER; inv SER) *) *) *)
(* (* (*           end; *) *) *)
(* (* (*       cbn; rewrite from_ubytes_to_ubytes; eauto. *) *) *)
(* (* (*     match goal with *) *) *)
(* (* (*           (* Try easy case first for speedup *) *) *) *)
(* (* (*           | |- _ = inr ?x => *) *) *)
(* (* (*             tactic_on_non_aggregate_uvalues x ltac:(cbn in SER; inv SER) *) *) *)
(* (* (*           end; *) *) *)
(* (* (*       cbn; rewrite from_ubytes_to_ubytes; eauto. *) *) *)
(* (* (*     match goal with *) *) *)
(* (* (*           (* Try easy case first for speedup *) *) *) *)
(* (* (*           | |- _ = inr ?x => *) *) *)
(* (* (*             tactic_on_non_aggregate_uvalues x ltac:(cbn in SER; inv SER) *) *) *)
(* (* (*           end; *) *) *)
(* (* (*       cbn; rewrite from_ubytes_to_ubytes; eauto. *) *) *)
(* (* (*     match goal with *) *) *)
(* (* (*           (* Try easy case first for speedup *) *) *) *)
(* (* (*           | |- _ = inr ?x => *) *) *)
(* (* (*             tactic_on_non_aggregate_uvalues x ltac:(cbn in SER; inv SER) *) *) *)
(* (* (*           end; *) *) *)
(* (* (*       cbn; rewrite from_ubytes_to_ubytes; eauto. *) *) *)

(* (* (*     - unfold deserialize_sbytes. *) *) *)
(* (* (*       cbn. *) *) *)
(* (* (* cbn in *; *) *) *)
(* (* (*         destruct t. *) *) *)
(* (* (*       cbn *) *) *)
(* (* (*       reflexivity. *) *) *)
(* (* (*       destruct t. *) *) *)

(* (* (*       cbn; inv SER. *) *) *)
(* (* (*           rewrite from_ubytes_to_ubytes; eauto. *) *) *)



(* (* (*     solve [match goal with *) *) *)
(* (* (*           (* Try easy case first for speedup *) *) *) *)
(* (* (*           | |- _ = inr ?x => *) *) *)
(* (* (*             tactic_on_non_aggregate_uvalues x ltac:(cbn in SER; inv SER) *) *) *)
(* (* (*           end; *) *) *)
(* (* (*       cbn; rewrite from_ubytes_to_ubytes; eauto]. *) *) *)
(* (* (*     match goal with *) *) *)
(* (* (*           (* Try easy case first for speedup *) *) *) *)
(* (* (*           | |- _ = inr ?x => *) *) *)
(* (* (*             tactic_on_non_aggregate_uvalues x ltac:(cbn in SER; inv SER) *) *) *)
(* (* (*           end; *) *) *)
(* (* (*       cbn; rewrite from_ubytes_to_ubytes; eauto. *) *) *)
(* (* (*     match goal with *) *) *)
(* (* (*           (* Try easy case first for speedup *) *) *) *)
(* (* (*           | |- _ = inr ?x => *) *) *)
(* (* (*             tactic_on_non_aggregate_uvalues x ltac:(cbn in SER; inv SER) *) *) *)
(* (* (*           end; *) *) *)
(* (* (*       cbn; rewrite from_ubytes_to_ubytes; eauto. *) *) *)
(* (* (*     match goal with *) *) *)
(* (* (*           (* Try easy case first for speedup *) *) *) *)
(* (* (*           | |- _ = inr ?x => *) *) *)
(* (* (*             tactic_on_non_aggregate_uvalues x ltac:(cbn in SER; inv SER) *) *) *)
(* (* (*           end; *) *) *)
(* (* (*       cbn; rewrite from_ubytes_to_ubytes; eauto. *) *) *)
(* (* (*     match goal with *) *) *)
(* (* (*           (* Try easy case first for speedup *) *) *) *)
(* (* (*           | |- _ = inr ?x => *) *) *)
(* (* (*             tactic_on_non_aggregate_uvalues x ltac:(cbn in SER; inv SER) *) *) *)
(* (* (*           end; *) *) *)
(* (* (*       cbn; rewrite from_ubytes_to_ubytes; eauto. *) *) *)
(* (* (*     match goal with *) *) *)
(* (* (*           (* Try easy case first for speedup *) *) *) *)
(* (* (*           | |- _ = inr ?x => *) *) *)
(* (* (*             tactic_on_non_aggregate_uvalues x ltac:(cbn in SER; inv SER) *) *) *)
(* (* (*           end; *) *) *)
(* (* (*       cbn; rewrite from_ubytes_to_ubytes; eauto. *) *) *)


(* (* (*     49: { eval_serialize_sbytes_hyp. *) *) *)
(* (* (*     56: { cbn in SER. destruct bytes. cbn in *. } *) *) *)
(* (* (*     all:eval_serialize_sbytes_hyp. *) *) *)
(* (* (*     1-30:eval_serialize_sbytes_hyp. *) *) *)
(* (* (*     12: { *) *) *)
(* (* (*       eval_serialize_sbytes_hyp. *) *) *)
      
(* (* (*       rewrite serialize_sbytes_equation in SER. *) *) *)
(* (* (*     } *) *) *)
(* (* (*     rewrite serialize_sbytes_equation in SER. *) *) *)
(* (* (*       try solve [cbn in SER; inv SER; cbn; rewrite from_ubytes_to_ubytes; eauto]. *) *) *)

    
(* (* (*     induction TYP; *) *) *)
(* (* (*       try solve [unfold serialize_sbytes in SER; *) *) *)
(* (* (*                  inv SER; *) *) *)
(* (* (*                  unfold deserialize_sbytes; *) *) *)
(* (* (*                  rewrite from_ubytes_to_ubytes; eauto *) *) *)
(* (* (*                 | cbn in *; *) *) *)
(* (* (*                   match goal with *) *) *)
(* (* (*                   | |- deserialize_sbytes _ ?t = _ => *) *) *)
(* (* (*                     cbn in *; *) *) *)
(* (* (*                     destruct t; cbn; inv SER; *) *) *)
(* (* (*                     rewrite from_ubytes_to_ubytes; eauto *) *) *)
(* (* (*                   end *) *) *)
(* (* (*                 ]. *) *) *)
(* (* (*     - inv SUP; exfalso; apply H; constructor. *) *) *)
(* (* (*     - rewrite sizeof_dtyp_void in SIZE. inv SIZE. *) *) *)
(* (* (*   Qed. *) *) *)
  Admitted.

    (** ** Deserialize - Serialize
        Starting from a dvalue [val] whose [dtyp] is [t], if:
        1. we serialize [val], getting a [list SByte]
        2. we add all these bytes to the memory block, starting from the position [off], getting back a new [mem_block] m'
        3. we lookup in this new memory [m'] the indices starting from [off] for the size of [t], getting back a [list SByte]
        4. we deserialize this final list of bytes
        then we should get back the initial value [val], albeit injected into [uvalue].

        The proof should go by induction over [TYP] I think, and rely on [lookup_all_index_add] notably.
     *)
    Lemma deserialize_serialize : forall val dt sid prov bytes,
        uvalue_has_dtyp val dt ->
        ErrSID_evals_to (serialize_sbytes val dt) bytes sid prov ->
        deserialize_sbytes bytes dt = inr val.
    Proof.
      intros val dt sid prov bytes TYP SER.
      induction TYP.
      - cbn in SER; inv SER.
        cbn.
    Admitted.

    (* Lemma deserialize_serialize : forall val t (TYP : dvalue_has_dtyp val t), *)
    (*     forall off (bytes : mem_block) (SUP : is_supported t), *)
    (*       deserialize_sbytes (lookup_all_index off (sizeof_dtyp t) (add_all_index (serialize_dvalue val) off bytes) SUndef) t = dvalue_to_uvalue val. *)
    (* Proof. *)
    (*   induction 1; try auto; intros; *)
    (*     match goal with *)
    (*     | H: is_supported ?t |- _ => *)
    (*       try solve [inversion H] *)
    (*     end. *)
    (*   - unroll_lookup_all_index; cbn; f_equal. *)
    (*   - unroll_lookup_all_index; cbn; f_equal. *)
    (*     pose proof (unsigned_I1_in_range x). *)
    (*     assert (EQ :DynamicValues.Int1.unsigned x / 256 = 0). *)
    (*     apply Z.div_small; lia. *)
    (*     rewrite EQ. *)
    (*     repeat rewrite Zdiv_0_l. *)
    (*     repeat rewrite Byte.unsigned_repr. *)
    (*     all: unfold Byte.max_unsigned, Byte.modulus; cbn; try lia. *)
    (*     rewrite Z.add_0_r. *)
    (*     apply DynamicValues.Int1.repr_unsigned. *)
    (*   - solve_integer_deserialize. *)
    (*   - solve_integer_deserialize. *)
    (*   - solve_integer_deserialize. *)
    (*   - inversion SUP; subst; *)
    (*     exfalso; apply H; constructor. *)
    (*   - unroll_lookup_all_index; cbn; f_equal. *)
    (*     clear bytes off. *)
    (*     remember (Float.to_bits x) as xb. *)
    (*     pose proof (unsigned_I64_in_range xb). *)
    (*     repeat rewrite Byte.unsigned_repr_eq. *)
    (*     unfold Byte.modulus, Byte.wordsize, Wordsize_8.wordsize; cbn. *)
    (*     replace (two_power_nat 8) with 256 by reflexivity. *)
    (*     remember (Int64.unsigned xb) as xbv. *)
    (*     match goal with *)
    (*     | [|- context[Int64.repr ?zv]] => replace zv with xbv *)
    (*     end. *)
    (*     + *)
    (*       subst. *)
    (*       rewrite Int64.repr_unsigned. *)
    (*       apply Float.of_to_bits. *)
    (*     + *)
    (*       (* this is the same goal as I64 branch! *) *)
    (*       clear -H. *)
    (*       rewrite Z.add_0_r. *)
    (*       unfold Z.modulo. *)
    (*       repeat break_let. *)
    (*       repeat match goal with *)
    (*              | [H : Z.div_eucl _ _ = _ |- _] => apply Z_div_mod' in H; [destruct H | lia] *)
    (*              end. *)
    (*       subst. *)
    (*       repeat *)
    (*         match goal with *)
    (*         | H: context [(?d * ?x + ?z) / ?d] |- _ => *)
    (*           rewrite div_add_lemma in H; [|lia]; subst *)
    (*         end. *)
    (*       lia. *)
    (*   - unroll_lookup_all_index; cbn; f_equal. *)
    (*     clear bytes off. *)
    (*     remember (Float32.to_bits x) as xb. *)
    (*     pose proof (unsigned_I32_in_range xb). *)
    (*     repeat rewrite Byte.unsigned_repr_eq. *)
    (*     unfold Byte.modulus, Byte.wordsize, Wordsize_8.wordsize; cbn. *)
    (*     replace (two_power_nat 8) with 256 by reflexivity. *)
    (*     remember (Int32.unsigned xb) as xbv. *)
    (*     match goal with *)
    (*     | [|- context[Int32.repr ?zv]] => replace zv with xbv *)
    (*     end. *)
    (*     + *)
    (*       subst. *)
    (*       rewrite Int32.repr_unsigned. *)
    (*       apply Float32.of_to_bits. *)
    (*     + *)
    (*       clear -H. *)

    (*       rewrite Z.add_0_r. *)
    (*       unfold Z.modulo. *)
    (*       repeat break_let. *)
    (*       repeat match goal with *)
    (*              | [H : Z.div_eucl _ _ = _ |- _] => apply Z_div_mod' in H; [destruct H | lia] *)
    (*              end. *)
    (*       subst. *)
    (*       rewrite Z.add_comm, Z.mul_comm, Z_div_plus in * by lia. *)
    (*       rewrite Zdiv_small with (x:=z0) in * by lia. *)
    (*       rewrite Z.add_0_l in *. *)
    (*       subst. *)
    (*       rewrite Z.add_comm, Z.mul_comm, Z_div_plus in * by lia. *)
    (*       rewrite Zdiv_small with (x:=z2) in * by lia. *)
    (*       rewrite Z.add_0_l in *. *)
    (*       subst. *)
    (*       rewrite Z.add_comm, Z.mul_comm, Z_div_plus in * by lia. *)
    (*       rewrite Zdiv_small with (x:=z4) in * by lia. *)
    (*       rewrite Z.add_0_l in *. *)
    (*       subst. *)
    (*       lia. *)
    (*   - (* Structs *) *)
    (*     rewrite sizeof_struct_cons. *)

    (*     inversion SUP. *)
    (*     subst. *)
    (*     rename H0 into FIELD_SUP. *)
    (*     apply List.Forall_cons_iff in FIELD_SUP. *)
    (*     destruct FIELD_SUP as [dt_SUP dts_SUP]. *)
    (*     assert (is_supported (DTYPE_Struct dts)) as SUP_STRUCT by (constructor; auto). *)

    (*     cbn. *)
    (*     rewrite lookup_all_index_append; [|apply sizeof_serialized; auto]. *)

    (*     erewrite deserialize_struct_element; auto. *)
    (*     +  erewrite <- sizeof_serialized; eauto. *)
    (*       rewrite lookup_all_index_add_all_index_same_length; eauto. *)

    (*       apply dvalue_serialized_not_sundef. *)
    (*     + pose proof deserialize_sbytes_dvalue_all_not_sundef (DVALUE_Struct fields) (DTYPE_Struct dts) (lookup_all_index (off + Z.of_N (sizeof_dtyp dt)) (sizeof_dtyp (DTYPE_Struct dts)) *)
    (*                                                                                                                       (add_all_index (serialize_dvalue (DVALUE_Struct fields)) (off + Z.of_N (sizeof_dtyp dt)) bytes) SUndef). *)
    (*       cbn in H. *)
    (*       forward H; auto. *)
    (*     + rewrite lookup_all_index_length. *)
    (*       reflexivity. *)
    (*   - (* Packed structs *) *)
    (*     rewrite sizeof_packed_struct_cons. *)

    (*     inversion SUP. *)
    (*     subst. *)
    (*     rename H0 into FIELD_SUP. *)
    (*     apply List.Forall_cons_iff in FIELD_SUP. *)
    (*     destruct FIELD_SUP as [dt_SUP dts_SUP]. *)
    (*     assert (is_supported (DTYPE_Packed_struct dts)) as SUP_STRUCT by (constructor; auto). *)

    (*     cbn. *)
    (*     rewrite lookup_all_index_append; [|apply sizeof_serialized; auto]. *)

    (*     erewrite deserialize_packed_struct_element; auto. *)
    (*     + erewrite <- sizeof_serialized; eauto. *)
    (*       rewrite lookup_all_index_add_all_index_same_length; eauto. *)

    (*       apply dvalue_serialized_not_sundef. *)
    (*     + pose proof deserialize_sbytes_dvalue_all_not_sundef (DVALUE_Packed_struct fields) (DTYPE_Packed_struct dts) (lookup_all_index (off + Z.of_N (sizeof_dtyp dt)) (sizeof_dtyp (DTYPE_Packed_struct dts)) *)
    (*                                                                                                                       (add_all_index (serialize_dvalue (DVALUE_Packed_struct fields)) (off + Z.of_N (sizeof_dtyp dt)) bytes) SUndef). *)
    (*       cbn in H. *)
    (*       forward H; auto. *)
    (*     + rewrite lookup_all_index_length. *)
    (*       reflexivity. *)
    (*   - (* Arrays *) *)
    (*     rename H into SZ. *)
    (*     generalize dependent sz. *)
    (*     generalize dependent xs. *)
    (*     induction xs; *)
    (*       intros IH IHdtyp sz SZ SUP. *)
    (*     + cbn in *. *)
    (*       subst. *)
    (*       reflexivity. *)
    (*     + cbn in SZ. *)
    (*       subst. *)
    (*       rewrite Nnat.Nat2N.inj_succ. *)
    (*       cbn. *)

    (*       assert (dvalue_has_dtyp a dt) as DTa. *)
    (*       { *)
    (*         apply IHdtyp. *)
    (*         cbn. auto. *)
    (*       } *)

    (*       rewrite Nmult_Sn_m. *)
    (*       rewrite lookup_all_index_append; [|apply sizeof_serialized; auto]. *)

    (*       erewrite deserialize_array_element; auto. *)
    (*       * inversion SUP; constructor; auto. *)
    (*       * erewrite <- sizeof_serialized; eauto. *)
    (*         rewrite lookup_all_index_add_all_index_same_length; eauto. *)

    (*         apply dvalue_serialized_not_sundef. *)
    (*       * (* Should be serialization of DVALUE_array xs *) *)
    (*         replace (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt)%N *)
    (*           with (N.of_nat (N.to_nat (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt))) by lia. *)
    (*         rewrite lookup_all_index_add_all_index_same_length. *)

    (*         apply all_not_sundef_fold_right_serialize. *)

    (*         apply serialize_fold_length; intuition. *)
    (*       * replace (sizeof_dtyp dt) with (N.of_nat (N.to_nat (sizeof_dtyp dt))) by lia. *)
    (*         rewrite lookup_all_index_add_all_index_same_length. *)
    (*         erewrite <- sizeof_serialized; intuition. *)
    (*         lia. *)
    (*         erewrite <- sizeof_serialized; intuition. *)
    (*         lia. *)
    (*       * rewrite IH; intuition. *)
    (*         inversion SUP; auto. *)
    (*       * cbn. *)

    (*         unfold deserialize_sbytes. *)
    (*         break_match. *)

    (*         2: { *)
    (*           assert (all_not_sundef *)
    (*                     (lookup_all_index (off + Z.of_N (sizeof_dtyp dt)) *)
    (*                                       (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt) *)
    (*                                       (add_all_index *)
    (*                                          (fold_right (fun (dv : dvalue) (acc : list SByte) => serialize_dvalue dv ++ acc) [] *)
    (*                                                      xs) (off + Z.of_N (sizeof_dtyp dt)) bytes) SUndef) = true) as CONTRA. *)
    (*           replace (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt)%N *)
    (*             with (N.of_nat (N.to_nat (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt))) by lia. *)
    (*           rewrite lookup_all_index_add_all_index_same_length. *)

    (*           apply all_not_sundef_fold_right_serialize. *)

    (*           apply serialize_fold_length; intuition. *)

    (*           rewrite Heqb in CONTRA. *)
    (*           inversion CONTRA. *)
    (*         } *)

    (*         forward IHxs; intuition. *)
    (*         forward IHxs; intuition. *)
    (*         specialize (IHxs (Datatypes.length xs) eq_refl). *)
    (*         forward IHxs. *)
    (*         { inversion SUP; constructor; eauto. } *)

    (*         cbn in IHxs. *)
    (*         rewrite <- IHxs. *)

    (*         rewrite all_not_sundef_deserialized; auto. *)
    (*         erewrite <- sizeof_serialized. *)

    (*         f_equal. *)

    (*         repeat rewrite <- Nnat.Nat2N.inj_mul. *)
    (*         rewrite lookup_all_index_add_all_index_same_length. *)
    (*         rewrite lookup_all_index_add_all_index_same_length. *)
    (*         reflexivity. *)

    (*         { erewrite <- serialize_fold_length. *)
    (*           erewrite <- sizeof_serialized. *)

    (*           repeat rewrite <- Nnat.Nat2N.inj_mul. *)
    (*           rewrite Nnat.Nat2N.id. *)
    (*           reflexivity. *)

    (*           eauto. *)
    (*           intuition. *)
    (*         } *)

    (*         { erewrite <- serialize_fold_length. *)
    (*           erewrite <- sizeof_serialized. *)

    (*           repeat rewrite <- Nnat.Nat2N.inj_mul. *)
    (*           rewrite Nnat.Nat2N.id. *)
    (*           reflexivity. *)

    (*           eauto. *)
    (*           intuition. *)
    (*         } *)

    (*         eauto. *)
    (*   - (* Vectors *) *)
    (*     rename H into SZ. *)
    (*     generalize dependent sz. *)
    (*     generalize dependent xs. *)
    (*     induction xs; *)
    (*       intros IH IHdtyp sz SZ SUP. *)
    (*     + cbn in *. *)
    (*       subst. *)
    (*       reflexivity. *)
    (*     + cbn in SZ. *)
    (*       subst. *)
    (*       rewrite Nnat.Nat2N.inj_succ. *)
    (*       cbn. *)

    (*       assert (dvalue_has_dtyp a dt) as DTa. *)
    (*       { *)
    (*         apply IHdtyp. *)
    (*         cbn. auto. *)
    (*       } *)

    (*       rewrite Nmult_Sn_m. *)
    (*       rewrite lookup_all_index_append; [|apply sizeof_serialized; auto]. *)

    (*       erewrite deserialize_vector_element; auto. *)
    (*       * inversion SUP; constructor; auto. *)
    (*       * erewrite <- sizeof_serialized; eauto. *)
    (*         rewrite lookup_all_index_add_all_index_same_length; eauto. *)

    (*         apply dvalue_serialized_not_sundef. *)
    (*       * (* Should be serialization of DVALUE_vector xs *) *)
    (*         replace (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt)%N *)
    (*           with (N.of_nat (N.to_nat (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt))) by lia. *)
    (*         rewrite lookup_all_index_add_all_index_same_length. *)

    (*         apply all_not_sundef_fold_right_serialize. *)

    (*         apply serialize_fold_length; intuition. *)
    (*       * replace (sizeof_dtyp dt) with (N.of_nat (N.to_nat (sizeof_dtyp dt))) by lia. *)
    (*         rewrite lookup_all_index_add_all_index_same_length. *)
    (*         erewrite <- sizeof_serialized; intuition. *)
    (*         lia. *)
    (*         erewrite <- sizeof_serialized; intuition. *)
    (*         lia. *)
    (*       * rewrite IH; intuition. *)
    (*         inversion SUP; subst; auto. *)
    (*       * cbn. *)

    (*         unfold deserialize_sbytes. *)
    (*         break_match. *)

    (*         2: { *)
    (*           assert (all_not_sundef *)
    (*                     (lookup_all_index (off + Z.of_N (sizeof_dtyp dt)) *)
    (*                                       (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt) *)
    (*                                       (add_all_index *)
    (*                                          (fold_right (fun (dv : dvalue) (acc : list SByte) => serialize_dvalue dv ++ acc) [] *)
    (*                                                      xs) (off + Z.of_N (sizeof_dtyp dt)) bytes) SUndef) = true) as CONTRA. *)
    (*           replace (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt)%N *)
    (*             with (N.of_nat (N.to_nat (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt))) by lia. *)
    (*           rewrite lookup_all_index_add_all_index_same_length. *)

    (*           apply all_not_sundef_fold_right_serialize. *)

    (*           apply serialize_fold_length; intuition. *)

    (*           rewrite Heqb in CONTRA. *)
    (*           inversion CONTRA. *)
    (*         } *)

    (*         forward IHxs; intuition. *)
    (*         forward IHxs; intuition. *)
    (*         specialize (IHxs (Datatypes.length xs) eq_refl). *)
    (*         forward IHxs. *)
    (*         { inversion SUP; constructor; eauto. } *)

    (*         cbn in IHxs. *)
    (*         rewrite <- IHxs. *)

    (*         rewrite all_not_sundef_deserialized; auto. *)
    (*         erewrite <- sizeof_serialized. *)

    (*         f_equal. *)

    (*         repeat rewrite <- Nnat.Nat2N.inj_mul. *)
    (*         rewrite lookup_all_index_add_all_index_same_length. *)
    (*         rewrite lookup_all_index_add_all_index_same_length. *)
    (*         reflexivity. *)

    (*         { erewrite <- serialize_fold_length. *)
    (*           erewrite <- sizeof_serialized. *)

    (*           repeat rewrite <- Nnat.Nat2N.inj_mul. *)
    (*           rewrite Nnat.Nat2N.id. *)
    (*           reflexivity. *)

    (*           eauto. *)
    (*           intuition. *)
    (*         } *)

    (*         { erewrite <- serialize_fold_length. *)
    (*           erewrite <- sizeof_serialized. *)

    (*           repeat rewrite <- Nnat.Nat2N.inj_mul. *)
    (*           rewrite Nnat.Nat2N.id. *)
    (*           reflexivity. *)

    (*           eauto. *)
    (*           intuition. *)
    (*         } *)

    (*         eauto. *)
    (* Qed. *)

End SerializationTheory.
