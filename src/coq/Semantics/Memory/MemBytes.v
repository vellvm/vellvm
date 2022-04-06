From Coq Require Import String List ZArith.

From ExtLib Require Import Structures.Monads.

From Vellvm Require Import
     Syntax.DynamicTypes
     Semantics.DynamicValues
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Semantics.LLVMEvents
     Utils.Monads
     Utils.NMaps
     Utils.OptionUtil
     Utils.ListUtil
     Utils.Error
     Utils.Util
     Utils.MonadReturnsLaws
     Utils.MapMonadExtra.

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
  Parameter uvalue_sbyte : uvalue -> dtyp -> uvalue -> store_id -> SByte.

  (* Turn an SByte into a UVALUE_ExtractByte value *)
  Parameter sbyte_to_extractbyte : SByte -> uvalue.

  Parameter sbyte_to_extractbyte_inv  :
    forall (b : SByte),
    exists uv dt idx sid,
      sbyte_to_extractbyte b = UVALUE_ExtractByte uv dt idx sid.

  Parameter sbyte_to_extractbyte_of_uvalue_sbyte :
    forall uv dt idx sid,
      sbyte_to_extractbyte (uvalue_sbyte uv dt idx sid) =  UVALUE_ExtractByte uv dt idx sid.
End ByteImpl.

Module Type ByteModule(Addr:ADDRESS)(IP:INTPTR)(SIZEOF:Sizeof)(LLVMEvents:LLVM_INTERACTIONS(Addr)(IP)(SIZEOF))(Byte:ByteImpl(Addr)(IP)(SIZEOF)(LLVMEvents)).
  Export Byte.
  Import LLVMEvents.
  Import DV.
  Import SIZEOF.

  Fixpoint all_bytes_from_uvalue_helper (idx' : Z) (sid' : store_id) (parent : uvalue) (bytes : list SByte) : option uvalue
    := match bytes with
       | [] => Some parent
       | sbyte::bytes =>
         match sbyte_to_extractbyte sbyte with
         | UVALUE_ExtractByte uv dt idx sid =>
           guard_opt (uvalue_int_eq_Z idx idx');;
           guard_opt (RelDec.rel_dec uv parent);;
           guard_opt (N.eqb sid sid');;
           all_bytes_from_uvalue_helper (Z.succ idx') sid' parent bytes
         | _ => None
         end
       end.

  Definition all_bytes_from_uvalue (bytes : list SByte) : option uvalue
    := match bytes with
       | nil => None
       | cons sbyte xs =>
         match sbyte_to_extractbyte sbyte with
         | UVALUE_ExtractByte uv dt idx sid =>
           all_bytes_from_uvalue_helper 0 sid uv bytes
         | _ => None
         end
       end.

  Definition to_ubytes (uv :  uvalue) (dt : dtyp) (sid : store_id) : OOM (list SByte)
    := map_monad
         (fun n => n' <- IP.from_Z (Z.of_N n);;
                ret (uvalue_sbyte uv dt (UVALUE_IPTR n') sid))
         (Nseq 0 (N.to_nat (sizeof_dtyp dt))).

  Fixpoint all_extract_bytes_from_uvalue_helper (idx' : Z) (sid' : store_id) (dt' : dtyp) (parent : uvalue) (bytes : list uvalue) : option uvalue
    := match bytes with
       | [] => Some parent
       | (UVALUE_ExtractByte uv dt idx sid)::bytes =>
         guard_opt (uvalue_int_eq_Z idx idx');;
         guard_opt (RelDec.rel_dec uv parent);;
         guard_opt (N.eqb sid sid');;
         guard_opt (dtyp_eqb dt dt');;
         all_extract_bytes_from_uvalue_helper (Z.succ idx') sid' dt' parent bytes
       | _ => None
       end.

  (* Check that store ids, uvalues, and types match up, as well as
       that the extract byte indices are in the right order *)
  Definition all_extract_bytes_from_uvalue (bytes : list uvalue) : option uvalue
    := match bytes with
       | nil => None
       | (UVALUE_ExtractByte uv dt idx sid)::xs =>
         all_extract_bytes_from_uvalue_helper 0 sid dt uv bytes
       | _ => None
       end.

  Definition from_ubytes (bytes : list SByte) (dt : dtyp) : uvalue
    :=
      match N.eqb (N.of_nat (length bytes)) (sizeof_dtyp dt), all_bytes_from_uvalue bytes with
      | true, Some uv => uv
      | _, _ => UVALUE_ConcatBytes (map sbyte_to_extractbyte bytes) dt
      end.

  Lemma to_ubytes_sizeof :
    forall uv dt sid bytes,
      MReturns bytes (to_ubytes uv dt sid) ->
      N.of_nat (length bytes) = sizeof_dtyp dt.
  Proof.
    intros uv dt sid bytes TO.
    unfold to_ubytes in TO.
    apply map_monad_length in TO. rewrite Nseq_length in TO.
    rewrite <- TO.
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
