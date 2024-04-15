From Coq Require Import
  ZArith
  List
  String
  Lia.

From Vellvm Require Import
  Numeric.Floats
  Utils.Monads
  LLVMParams
  Error
  DynamicTypes
  VellvmIntegers
  Utils.ErrUbOomProp
  Utils.Oomable
  Utils.Poisonable
  Utils.ErrOomPoison
  Utils.ListUtil.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.EitherMonad.

Import ListNotations.
Import MonadNotation.

Open Scope N_scope.


(* Convert a list of UVALUE_ExtractByte values into a dvalue of
         a given type.

         Assumes bytes are in little endian form...

         Note: I believe this function has to be endianess aware.

         This probably also needs to be mutually recursive with
         concretize_uvalue...

         Idea:

         For each byte in the list, find uvalues that are from the
         same store.

         - Can I have bytes that are from the same store, but
           different uvalues?  + Might not be possible, actually,
           because if I store a concatbytes I get the old sids...  +
           TODO: Getting the old sids might be a problem,
           though. Should be new, but entangled wherever they were
           entangled before. This needs to be changed in serialize...
           * I.e., If I load bytes from one store, and then store them
           beside them... It should have a different sid, allowing the
           bytes from that store to vary independently.  * ALSO bytes
           that are entangled should *stay* entangled.

         The above is largely an issue with serialize_sbytes...

         The idea here should be to take equal uvalues in our byte
         list with the same sid and concretize the uvalue exactly
         once.

         After all uvalues in our list are concretized we then need to
         convert the corresponding byte extractions into a single
         dvalue.

 *)

(* TODO: probably move this *)
(* TODO: Make these take endianess into account.

         Can probably use bitwidth from VInt to do big-endian...
 *)
Definition extract_byte_vint {I} `{VInt I} (i : I) (idx : Z) : Z
  := unsigned (modu (shru i (repr (idx * 8))) (repr 256)).

Fixpoint concat_bytes_vint {I} `{VInt I} (bytes : list I) : I
  := match bytes with
     | [] => repr 0
     | (byte::bytes) =>
         add byte (shl (concat_bytes_vint bytes) (repr 8))
     end.

(* TODO: Endianess *)
(* TODO: does this work correctly with negative x? *)
Definition extract_byte_Z (x : Z) (idx : Z) : Z
  := (Z.shiftr x (idx * 8)) mod 256.

(* TODO: Endianess *)
Definition concat_bytes_Z_vint {I} `{VInt I} (bytes : list Z) : I
  := concat_bytes_vint (map repr bytes).

(* TODO: Endianess *)
Fixpoint concat_bytes_Z (bytes : list Z) : Z
  := match bytes with
     | [] => 0
     | (byte::bytes) =>
         byte + (Z.shiftl (concat_bytes_Z bytes) 8)
     end.

Module Type DvalueByte (LP : LLVMParams).
  Import LP.
  Import PTOI.
  Import ITOP.
  Import PROV.
  Import SIZEOF.
  Import Events.DV.

  (* Walk through a list *)
  (* Returns field index + number of bytes remaining *)
  Fixpoint extract_field_byte_helper {M} `{Monad M} `{RAISE_ERROR M} (fields : list dtyp) (field_idx : N) (byte_idx : N) : M (dtyp * (N * N))%type
    := match fields with
       | [] =>
           raise_error "No fields left for byte-indexing..."
       | (x::xs) =>
           let sz := sizeof_dtyp x
           in if N.ltb byte_idx sz
              then ret (x, (field_idx, byte_idx))
              else extract_field_byte_helper xs (N.succ field_idx) (byte_idx - sz)
       end.

  Definition extract_field_byte {M} `{Monad M} `{RAISE_ERROR M} (fields : list dtyp) (byte_idx : N) : M (dtyp * (N * N))%type
    := extract_field_byte_helper fields 0 byte_idx.

  Fixpoint concat_bytes_vint {I} `{VInt I} (bytes : list I) : I
    := match bytes with
       | [] => repr 0
       | (byte::bytes) =>
           add byte (shl (concat_bytes_vint bytes) (repr 8))
       end.


  (* Need the type of the dvalue in order to know how big fields and array elements are.

         It's not possible to use the dvalue alone, as DVALUE_Poison's
         size depends on the type.
   *)
(*  Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia | solve_dvalue_measure]. *)
  
  Fixpoint dvalue_extract_byte {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_POISON M} `{RAISE_OOMABLE M} (dv : dvalue) (dt : dtyp) (idx : Z) {struct dv} : M Z
    :=
    let dvalue_extract_struct_bytes :=
      fix loop fields types (idx : Z) {struct fields}  :=
        match fields, types with
        | [], [] => raise_error "No fields left for byte-indexing..."
        | f::fs, dt::dts =>
            let sz := Z.of_N (sizeof_dtyp dt) in
            if Z.ltb idx sz
            then dvalue_extract_byte f dt idx
            else loop fs dts (idx - sz)%Z
        | _, _ => raise_error "type-mismatch: structs / fields have different lengths"
        end
    in
    let dvalue_extract_array_bytes :=
      fix loop elts dt (idx : Z) {struct elts}  :=
        match elts with
        | [] => raise_error "No fields left for byte-indexing..."
        | e::es =>
            let sz := Z.of_N (sizeof_dtyp dt) in
            if Z.ltb idx sz
            then dvalue_extract_byte e dt idx
            else loop es dt (idx - sz)%Z
        end
    in
    match dv with
       | DVALUE_I1 x
       | DVALUE_I8 x
       | DVALUE_I16 x
       | DVALUE_I32 x
       | DVALUE_I64 x =>
           ret (extract_byte_vint x idx)
       | DVALUE_IPTR x =>
           ret (extract_byte_Z (IP.to_Z x) idx)
       | DVALUE_Addr addr =>
           (* Note: this throws away provenance *)
           ret (extract_byte_Z (ptr_to_int addr) idx)
       | DVALUE_Float f =>
           ret (extract_byte_Z (unsigned (Float32.to_bits f)) idx)
       | DVALUE_Double d =>
           ret (extract_byte_Z (unsigned (Float.to_bits d)) idx)
       | DVALUE_Poison dt => raise_poison dt
       | DVALUE_Oom dt => raise_oomable dt
       | DVALUE_None =>
           (* TODO: Not sure if this should be an error, poison, or what. *)
           raise_error "dvalue_extract_byte on DVALUE_None"

       (* TODO: Take padding into account. *)
       | DVALUE_Struct fields =>
           match dt with
           | DTYPE_Struct dts =>
               dvalue_extract_struct_bytes fields dts idx 
           | _ => raise_error "dvalue_extract_byte: type mismatch on DVALUE_Struct."
           end

       | DVALUE_Packed_struct fields =>
           match dt with
           | DTYPE_Packed_struct dts =>
               dvalue_extract_struct_bytes fields dts idx
           | _ => raise_error "dvalue_extract_byte: type mismatch on DVALUE_Packed_struct."
           end

       | DVALUE_Array elts =>
           match dt with
           | DTYPE_Array sz dt =>
               dvalue_extract_array_bytes elts dt idx
           | _ =>
               raise_error "dvalue_extract_byte: type mismatch on DVALUE_Array."
           end

       | DVALUE_Vector elts =>
           match dt with
           | DTYPE_Vector sz dt =>
               dvalue_extract_array_bytes elts dt idx
           | _ =>
               raise_error "dvalue_extract_byte: type mismatch on DVALUE_Vector."
           end
       end.

  Lemma dvalue_extract_byte_equation {M} `{HM: Monad M} `{RE: RAISE_ERROR M} `{RP: RAISE_POISON M} `{RO: RAISE_OOMABLE M} (dv : dvalue) (dt : dtyp) (idx : Z) :
    @dvalue_extract_byte M HM RE RP RO dv dt idx =
    let dvalue_extract_struct_bytes :=
      fix loop fields types (idx : Z) {struct fields}  :=
        match fields, types with
        | [], [] => raise_error "No fields left for byte-indexing..."
        | f::fs, dt::dts =>
            let sz := Z.of_N (sizeof_dtyp dt) in
            if Z.ltb idx sz
            then dvalue_extract_byte f dt idx
            else loop fs dts (idx - sz)%Z
        | _, _ => raise_error "type-mismatch: structs / fields have different lengths"
        end
    in
    let dvalue_extract_array_bytes :=
      fix loop elts dt (idx : Z) {struct elts}  :=
        match elts with
        | [] => raise_error "No fields left for byte-indexing..."
        | e::es =>
            let sz := Z.of_N (sizeof_dtyp dt) in
            if Z.ltb idx sz
            then dvalue_extract_byte e dt idx
            else loop es dt (idx - sz)%Z
        end
    in
    match dv with
       | DVALUE_I1 x
       | DVALUE_I8 x
       | DVALUE_I16 x
       | DVALUE_I32 x
       | DVALUE_I64 x =>
           ret (extract_byte_vint x idx)
       | DVALUE_IPTR x =>
           ret (extract_byte_Z (IP.to_Z x) idx)
       | DVALUE_Addr addr =>
           (* Note: this throws away provenance *)
           ret (extract_byte_Z (ptr_to_int addr) idx)
       | DVALUE_Float f =>
           ret (extract_byte_Z (unsigned (Float32.to_bits f)) idx)
       | DVALUE_Double d =>
           ret (extract_byte_Z (unsigned (Float.to_bits d)) idx)
       | DVALUE_Poison dt => raise_poison dt
       | DVALUE_Oom dt => raise_oomable dt
       | DVALUE_None =>
           (* TODO: Not sure if this should be an error, poison, or what. *)
           raise_error "dvalue_extract_byte on DVALUE_None"

       (* TODO: Take padding into account. *)
       | DVALUE_Struct fields =>
           match dt with
           | DTYPE_Struct dts =>
               dvalue_extract_struct_bytes fields dts idx 
           | _ => raise_error "dvalue_extract_byte: type mismatch on DVALUE_Struct."
           end

       | DVALUE_Packed_struct fields =>
           match dt with
           | DTYPE_Packed_struct dts =>
               dvalue_extract_struct_bytes fields dts idx
           | _ => raise_error "dvalue_extract_byte: type mismatch on DVALUE_Packed_struct."
           end

       | DVALUE_Array elts =>
           match dt with
           | DTYPE_Array sz dt =>
               dvalue_extract_array_bytes elts dt idx
           | _ =>
               raise_error "dvalue_extract_byte: type mismatch on DVALUE_Array."
           end

       | DVALUE_Vector elts =>
           match dt with
           | DTYPE_Vector sz dt =>
               dvalue_extract_array_bytes elts dt idx
           | _ =>
               raise_error "dvalue_extract_byte: type mismatch on DVALUE_Vector."
           end
       end.
  Proof.
    unfold dvalue_extract_byte at 1.
    destruct dv; try reflexivity.
  Qed.

  (* Taking a byte out of a dvalue...

      Unlike UVALUE_ExtractByte, I don't think this needs an sid
      (store id). There should be no nondeterminism in this value. *)
  Inductive dvalue_byte : Type :=
  | DVALUE_ExtractByte (dv : dvalue) (dt : dtyp) (idx : N) : dvalue_byte
  .

  Definition dvalue_byte_value {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_POISON M} `{RAISE_OOMABLE M} (db : dvalue_byte) : M Z
    := match db with
       | DVALUE_ExtractByte dv dt idx =>
           dvalue_extract_byte dv dt (Z.of_N idx)
       end.

  Definition dvalue_to_dvalue_bytes (dv : dvalue) (dt : dtyp) : list dvalue_byte
    := map
         (fun idx => (DVALUE_ExtractByte dv dt idx))
         (Nseq 0 (N.to_nat (sizeof_dtyp dt))).

  #[local] Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia].
  Fixpoint dvalue_bytes_to_dvalue {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_POISON M} `{RAISE_OOMABLE M} (dbs : list dvalue_byte) (dt : dtyp) : M dvalue
    :=
    let list_dvalue_bytes_to_dvalue :=
      fix go dts dbs :=
        match dts with
        | [] => ret []
        | (dt::dts) =>
            let sz := sizeof_dtyp dt in
            let init_bytes := take sz dbs in
            let rest_bytes := drop sz dbs in
            f <- dvalue_bytes_to_dvalue init_bytes dt;;
            rest <- go dts rest_bytes;;
            ret (f :: rest)
        end
    in
    match dt with
       | DTYPE_I sz =>
           zs <- map_monad dvalue_byte_value dbs;;
           match sz with
           | 1 =>
               ret (DVALUE_I1 (concat_bytes_Z_vint zs))
           | 8 =>
               ret (DVALUE_I8 (concat_bytes_Z_vint zs))
           | 16 =>
               ret (DVALUE_I16 (concat_bytes_Z_vint zs))
           | 32 =>
               ret (DVALUE_I32 (concat_bytes_Z_vint zs))
           | 64 =>
               ret (DVALUE_I64 (concat_bytes_Z_vint zs))
           | _ => raise_error "Unsupported integer size."
           end
       | DTYPE_IPTR =>
           zs <- map_monad dvalue_byte_value dbs;;
           val <- lift_OOMABLE DTYPE_IPTR (IP.from_Z (concat_bytes_Z zs));;
           ret (DVALUE_IPTR val)
       | DTYPE_Pointer =>
           (* TODO: not sure if this should be wildcard provenance.
                TODO: not sure if this should truncate iptr value...
            *)
           (* TODO: not sure if this should be lazy OOM or not *)
           zs <- map_monad dvalue_byte_value dbs;;
           match int_to_ptr (concat_bytes_Z zs) wildcard_prov with
           | NoOom a => ret (DVALUE_Addr a)
           | Oom msg => raise_oomable DTYPE_Pointer
           end
       | DTYPE_Void =>
           raise_error "dvalue_bytes_to_dvalue on void type."
       | DTYPE_Half =>
           raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_Half."
       | DTYPE_Float =>
           zs <- map_monad dvalue_byte_value dbs;;
           ret (DVALUE_Float (Float32.of_bits (concat_bytes_Z_vint zs)))
       | DTYPE_Double =>
           zs <- map_monad dvalue_byte_value dbs;;
           ret (DVALUE_Double (Float.of_bits (concat_bytes_Z_vint zs)))
       | DTYPE_X86_fp80 =>
           raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_X86_fp80."
       | DTYPE_Fp128 =>
           raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_Fp128."
       | DTYPE_Ppc_fp128 =>
           raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_Ppc_fp128."
       | DTYPE_Metadata =>
           raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_Metadata."
       | DTYPE_X86_mmx =>
           raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_X86_mmx."
       | DTYPE_Array sz t =>
           let sz' := sizeof_dtyp t in
           let elt_bytes :=
             if N.eqb sz' 0
             then repeatN sz []
             else split_every_nil sz' dbs
           in
           elts <- map_monad (fun es => dvalue_bytes_to_dvalue es t) elt_bytes;;
           ret (DVALUE_Array elts)
       | DTYPE_Vector sz t =>
           let sz' := sizeof_dtyp t in
           let elt_bytes :=
             if N.eqb sz' 0
             then repeatN sz []
             else split_every_nil sz' dbs
           in
           elts <- map_monad (fun es => dvalue_bytes_to_dvalue es t) elt_bytes;;
           ret (DVALUE_Vector elts)
       | DTYPE_Struct fields =>
           Functor.fmap DVALUE_Struct (list_dvalue_bytes_to_dvalue fields dbs)
       | DTYPE_Packed_struct fields =>
           Functor.fmap DVALUE_Packed_struct (list_dvalue_bytes_to_dvalue fields dbs)
       | DTYPE_Opaque =>
           raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_Opaque."
       end.

  Lemma dvalue_bytes_to_dvalue_equation
    {M} `{HM : Monad M} `{RE: RAISE_ERROR M} `{RP: RAISE_POISON M} `{RO: RAISE_OOMABLE M} (dbs : list dvalue_byte) (dt : dtyp) :
    @dvalue_bytes_to_dvalue M HM RE RP RO dbs dt =
    let list_dvalue_bytes_to_dvalue :=
      fix go dts dbs :=
        match dts with
        | [] => ret []
        | (dt::dts) =>
            let sz := sizeof_dtyp dt in
            let init_bytes := take sz dbs in
            let rest_bytes := drop sz dbs in
            f <- dvalue_bytes_to_dvalue init_bytes dt;;
            rest <- go dts rest_bytes;;
            ret (f :: rest)
        end
    in
    match dt with
       | DTYPE_I sz =>
           zs <- map_monad dvalue_byte_value dbs;;
           match sz with
           | 1 =>
               ret (DVALUE_I1 (concat_bytes_Z_vint zs))
           | 8 =>
               ret (DVALUE_I8 (concat_bytes_Z_vint zs))
           | 16 =>
               ret (DVALUE_I16 (concat_bytes_Z_vint zs))
           | 32 =>
               ret (DVALUE_I32 (concat_bytes_Z_vint zs))
           | 64 =>
               ret (DVALUE_I64 (concat_bytes_Z_vint zs))
           | _ => raise_error "Unsupported integer size."
           end
       | DTYPE_IPTR =>
           zs <- map_monad dvalue_byte_value dbs;;
           val <- lift_OOMABLE DTYPE_IPTR (IP.from_Z (concat_bytes_Z zs));;
           ret (DVALUE_IPTR val)
       | DTYPE_Pointer =>
           (* TODO: not sure if this should be wildcard provenance.
                TODO: not sure if this should truncate iptr value...
            *)
           (* TODO: not sure if this should be lazy OOM or not *)
           zs <- map_monad dvalue_byte_value dbs;;
           match int_to_ptr (concat_bytes_Z zs) wildcard_prov with
           | NoOom a => ret (DVALUE_Addr a)
           | Oom msg => raise_oomable DTYPE_Pointer
           end
       | DTYPE_Void =>
           raise_error "dvalue_bytes_to_dvalue on void type."
       | DTYPE_Half =>
           raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_Half."
       | DTYPE_Float =>
           zs <- map_monad dvalue_byte_value dbs;;
           ret (DVALUE_Float (Float32.of_bits (concat_bytes_Z_vint zs)))
       | DTYPE_Double =>
           zs <- map_monad dvalue_byte_value dbs;;
           ret (DVALUE_Double (Float.of_bits (concat_bytes_Z_vint zs)))
       | DTYPE_X86_fp80 =>
           raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_X86_fp80."
       | DTYPE_Fp128 =>
           raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_Fp128."
       | DTYPE_Ppc_fp128 =>
           raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_Ppc_fp128."
       | DTYPE_Metadata =>
           raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_Metadata."
       | DTYPE_X86_mmx =>
           raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_X86_mmx."
       | DTYPE_Array sz t =>
           let sz' := sizeof_dtyp t in
           let elt_bytes :=
             if N.eqb sz' 0
             then repeatN sz []
             else split_every_nil sz' dbs
           in
           elts <- map_monad (fun es => dvalue_bytes_to_dvalue es t) elt_bytes;;
           ret (DVALUE_Array elts)
       | DTYPE_Vector sz t =>
           let sz' := sizeof_dtyp t in
           let elt_bytes :=
             if N.eqb sz' 0
             then repeatN sz []
             else split_every_nil sz' dbs
           in
           elts <- map_monad (fun es => dvalue_bytes_to_dvalue es t) elt_bytes;;
           ret (DVALUE_Vector elts)
       | DTYPE_Struct fields =>
           Functor.fmap DVALUE_Struct (list_dvalue_bytes_to_dvalue fields dbs)
       | DTYPE_Packed_struct fields =>
           Functor.fmap DVALUE_Packed_struct (list_dvalue_bytes_to_dvalue fields dbs)
       | DTYPE_Opaque =>
           raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_Opaque."
       end.
  Proof.
    destruct dt; try reflexivity.
  Qed.

End DvalueByte.

Module Make (LP : LLVMParams) <: DvalueByte LP.
  Include (DvalueByte LP).
End Make.
