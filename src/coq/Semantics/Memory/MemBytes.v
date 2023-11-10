From Coq Require Import String List ZArith.

From ExtLib Require Import Structures.Monads.

From Vellvm Require Import
     Syntax.DynamicTypes
     Semantics.DynamicValues
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Semantics.LLVMParams
     Utils.Monads
     Utils.OptionUtil
     Utils.ListUtil
     Utils.Error
     Utils.MonadReturnsLaws
     Utils.MapMonadExtra.

Import Utils.Monads.
Import Basics.Basics.Monads.

Import ListNotations.
Import MonadNotation.

Module SByteM (LLVMParams: LLVM_PARAMS).
  Import LLVMParams.
  Import DV.
  Import Sizeof.

  (* Get a specific byte of a uvalue of a given type.

     Arguments are:

     - The uvalue to get the byte of.
     - The type of the uvalue that we are getting the byte of.
     - The index of the byte (as a uvalue).
     - The store id for the byte we are creating.
   *)
  Inductive SByte :=
  | uvalue_sbyte (uv : uvalue) (dt : dtyp) (idx : N) (sid : store_id).

  Definition sbyte_sid (byte : SByte) : store_id :=
    match byte with
    | uvalue_sbyte uv dt idx sid => sid
    end.
  
  (* Turn an SByte into a UVALUE_ExtractByte value *)
  Definition sbyte_to_extractbyte (s : SByte) : uvalue :=
    match s with
    | uvalue_sbyte uv dt idx sid => UVALUE_ExtractByte uv dt idx sid
    end.

  Lemma sbyte_to_extractbyte_inv  :
    forall (b : SByte),
    exists uv dt idx sid,
      sbyte_to_extractbyte b = UVALUE_ExtractByte uv dt idx sid.
  Proof.
    intros.
    destruct b.
    do 4 eexists. simpl. reflexivity.
  Qed.

  Lemma sbyte_to_extractbyte_of_uvalue_sbyte :
    forall uv dt idx sid,
      sbyte_to_extractbyte (uvalue_sbyte uv dt idx sid) =  UVALUE_ExtractByte uv dt idx sid.
  Proof.
    intros. reflexivity.
  Qed.

  Definition extractbyte_to_sbyte (u : uvalue) : option SByte :=
    match u with
    | UVALUE_ExtractByte uv dt idx sid => Some (uvalue_sbyte uv dt idx sid)
    | _ => None
    end.

  Lemma extractbyte_to_sbyte_inv :
    forall u sb,
      extractbyte_to_sbyte u = Some sb ->
      sbyte_to_extractbyte sb = u.
  Proof.
    intros.
    destruct u; inversion H.
    reflexivity.
  Qed.

  Lemma extractbyte_to_sbyte_inv' :
    forall u,
      extractbyte_to_sbyte u = None ->
      ~ exists sb, sbyte_to_extractbyte sb = u.
  Proof.
    intros.
    intro C.
    destruct C as [sb HEQ].
    subst.
    destruct sb.
    inversion H.
  Qed.
  
(* End ByteImpl. *)

(* Module Byte(Addr:ADDRESS)(IP:INTPTR)(SIZEOF:Sizeof)(LLVMEvents:LLVM_INTERACTIONS(Addr)(IP)(SIZEOF)). *)
(*   Module Byte := ByteImpl(Addr)(IP)(SIZEOF)(LLVMEvents). *)
(*   Export Byte. *)
(*   Import LLVMEvents. *)
(*   Import DV. *)


  (* SAZ: Do we also need to check all of the embedded dtyps ?*)
  Definition all_bytes_parent_sid (parent : uvalue) (dt:dtyp) (sid : store_id) (bytes : list SByte) : bool :=
    List.forallb
      (fun '(uvalue_sbyte uv dt' _ sid') =>
         N.eqb sid sid' && (dtyp_eqb dt dt') && 
           (RelDec.rel_dec parent uv))%bool bytes.

  Fixpoint all_bytes_in_order_from idx (bytes : list SByte) : bool :=
    match bytes with
    | [] => true
    | sbyte::bytes =>
        match sbyte with
        | uvalue_sbyte _ _ idx' _ =>
            (N.eqb idx idx') && all_bytes_in_order_from (N.succ idx) bytes
        end
    end.

  Fixpoint zero_size_uvalue (t : dtyp) : option uvalue :=
    match t with
    | DTYPE_Void => Some UVALUE_None
    | DTYPE_Array sz dt =>
        if N.eqb sz 0 then Some (UVALUE_Array []) else
          v <- zero_size_uvalue dt ;;
          Some (UVALUE_Array (repeat v (N.to_nat sz)))
    | DTYPE_Struct dts =>
        uvs <- map_monad zero_size_uvalue dts ;;
        Some (UVALUE_Struct uvs)
    | DTYPE_Packed_struct dts =>
        uvs <- map_monad zero_size_uvalue dts ;;
        Some (UVALUE_Packed_struct uvs)
    | DTYPE_Vector sz dt =>
        if N.eqb sz 0 then Some (UVALUE_Array []) else
        None  (* internal vector types are all non-zero size *)
    | _ => None
    end.
  
  Definition all_bytes_from_uvalue (t : dtyp) (bytes : list SByte) : option uvalue
    := match bytes with
       | nil =>  (* Only "zero size" uvalues can serialize to nil *)
           zero_size_uvalue t
       | cons sbyte xs =>
         match sbyte with
         | uvalue_sbyte uv dt idx sid =>
             if ((all_bytes_parent_sid uv dt sid bytes) && (all_bytes_in_order_from 0%N bytes))%bool then
               Some uv else None
         end
       end.

  Definition to_ubytes (uv :  uvalue) (dt : dtyp) (sid : store_id) : list SByte
    := map
         (fun n => uvalue_sbyte uv dt n sid)
         (Nseq 0 (N.to_nat (sizeof_dtyp dt))).

  (* Check that store ids, uvalues, and types match up, as well as
       that the extract byte indices are in the right order *)
  Definition all_extract_bytes_from_uvalue (t : dtyp) (bytes : list uvalue) : option uvalue
    :=
    sbs <- map_monad extractbyte_to_sbyte bytes ;;
    all_bytes_from_uvalue t sbs.

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

End SByteM.

