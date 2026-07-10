From Vellvm Require Import
  Utils
  Numeric
  Syntax
  Params
  DynamicValues
  EOU
  VellvmIntegers.

From ExtLib Require Import
  Data.Monads.EitherMonad.
Open Scope N_scope.

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

Section MemoryByte.
  Context {Pa : Params}.
  
  (* Walk through a list *)
  (* Returns field index + number of bytes remaining *)
  Fixpoint extract_field_byte_helper (fields : list dtyp) (field_idx : N) (byte_idx : N) : EOU (dtyp * (N * N))%type
    := match fields with
       | [] =>
           raise_error "No fields left for byte-indexing..."
       | (x::xs) =>
           let sz := sizeof_dtyp x
           in if N.ltb byte_idx sz
              then ret (x, (field_idx, byte_idx))
              else extract_field_byte_helper xs (N.succ field_idx) (byte_idx - sz)
       end.

  Definition extract_field_byte (fields : list dtyp) (byte_idx : N) : EOU (dtyp * (N * N))%type
    := extract_field_byte_helper fields 0 byte_idx.

  (* Need the type of the dvalue in order to know how big fields and array elements are.

         It's not possible to use the dvalue alone, as DVALUE_Poison's
         size depends on the type.
   *)

  (* This function may essentially compute poison, but without a dvalue to embed it into yet.
     We take an adhoc lightweigh way to handle this currently with the following option return type.
     It is also tied to how we treat the behavior of running map_monad to extract a list of bytes:
     currently we want it to result into a Poison dvalue if any byte resulted in poison.
     We are likely to follow a finer grained approach soon.
   *)
  Variant MaybePoison (A : Type) : Type := | Pois | NoPois (a : A).
  Arguments Pois {A}.
  Arguments NoPois {A}.
  Definition EOUP Z := EOU (MaybePoison Z).
  #[local] Instance EOUP_Monad : Monad EOUP :=
    {| ret _ a := ret (NoPois a) ;
      bind _ _ c k := 
        bind (m := EOU) c (fun pov => match pov with
                                   | Pois => ret Pois
                                   | NoPois a => k a
                                   end)
    |}.


  Definition dvalue_base_extract_byte (dv : dvalue_base) (idx : Z) : EOUP Z :=
    match dv with
    | DVALUE_I sz x =>
        ret (extract_byte_vint x idx)
    | DVALUE_Iptr x =>
        ret (extract_byte_Z (to_Z x) idx)
    | DVALUE_Pointer ptr =>
        (* Note: this throws away provenance *)
        ret (extract_byte_Z (ptr_to_int ptr) idx)
    | DVALUE_Float f =>
        ret (extract_byte_Z (unsigned (Float32.to_bits f)) idx)
    | DVALUE_Double d =>
        ret (extract_byte_Z (unsigned (Float.to_bits d)) idx)
    | DVALUE_Poison dt => ret Pois
    | DVALUE_None =>
        (* TODO: Not sure if this should be an error, poison, or what. *)
        raise_error "dvalue_extract_byte on DVALUE_None"
    | DVALUE_B sz bits =>
        raise_error "Byte Type TODO"
    end.
               
  (* offset is the number of bytes indexed past so far *)
  Fixpoint dvalue_extract_byte (dv : dvalue) (dt : dtyp) (idx : Z) {struct dv} : EOUP Z  :=
    let dvalue_extract_struct_bytes (pad : option N) : list dvalue -> list dtyp -> N -> Z -> EOUP Z :=
      fix loop fields types (offset : N) (idx : Z) {struct fields} : EOUP Z :=
        match fields, types with
        | [], [] =>
            (* Handle padding at the end of the structure *)
            let padding :=
              match pad with
              | Some max_pad
                => Sizeof.pad_amount max_pad offset
              | None =>
                  0%N
              end
            in
            let zpadding := Z.of_N padding in
            if Z.ltb idx zpadding
            then
              (* Indexing into padding bytes *)
              (* TODO: currently we just pad with 0 bytes. This *)
      (*            prevents storing data in padding, though, which is *)
      (*            technically allowed *)
              ret 0%Z
            else
              raise_error "No fields left for byte-indexing..."
        | f::fs, dt::dts =>
            let padding :=
              if pad
              then pad_amount (preferred_alignment (dtyp_alignment dt)) offset
              else 0%N
            in
            let zpadding := Z.of_N padding in
            let sz := sizeof_dtyp dt in
            let zsz := Z.of_N sz in
            if Z.ltb idx zpadding
            then
              (* Indexing into padding bytes *)
              (* TODO: currently we just pad with 0 bytes. This *)
      (*            prevents storing data in padding, though, which is *)
      (*            technically allowed *)
              ret 0%Z
            else
              let offset' := (offset + padding)%N in
              let idx' := (idx - zpadding)%Z in
              if Z.ltb idx' zsz
              then dvalue_extract_byte f dt idx'
              else loop fs dts (offset' + sz)%N (idx' - zsz)%Z
        | _, _ => raise_error "type-mismatch: structs / fields have different lengths"
        end
    in

    let dvalue_extract_array_bytes :=
      fix loop (elts : list dvalue) dt (idx : Z) {struct elts}  :=
        match elts with
        | [] => raise_error "No fields left for byte-indexing..."
        | e::es =>
            let sz := sizeof_dtyp dt in
            let zsz := Z.of_N sz in
            if Z.ltb idx zsz
            then dvalue_extract_byte e dt idx
            else loop es dt (idx - zsz)%Z
        end
    in

    let dvalue_extract_vector_bytes :=
      fix loop (elts : list dvalue_base) dt (idx : Z) {struct elts}  :=
        match elts with
        | [] => raise_error "No fields left for byte-indexing..."
        | e::es =>
            let sz := sizeof_dtyp dt in
            let zsz := Z.of_N sz in
            if Z.ltb idx zsz
            then dvalue_base_extract_byte e idx
            else loop es dt (idx - zsz)%Z
        end
    in

    match dv with
    | DVALUE_Base dv => dvalue_base_extract_byte dv idx
    | DVALUE_Struct false fields =>
        match dt with
        | DTYPE_Struct false dts =>
            dvalue_extract_struct_bytes (Some (max_preferred_dtyp_alignment dts)) fields dts 0 idx
        | _ => raise_error "dvalue_extract_byte: type mismatch on DVALUE_Struct."
        end

    | DVALUE_Struct true fields =>
        match dt with
        | DTYPE_Struct true dts =>
            dvalue_extract_struct_bytes None fields dts 0 idx
        | _ => raise_error "dvalue_extract_byte: type mismatch on DVALUE_Packed_struct."
        end

    | DVALUE_Array _ elts =>
        match dt with
        | DTYPE_Array sz dt =>
            dvalue_extract_array_bytes elts dt idx
        | _ =>
            raise_error "dvalue_extract_byte: type mismatch on DVALUE_Array."
        end

    | DVALUE_Vector _ elts =>
        match dt with
        | DTYPE_Vector sz dt =>
            dvalue_extract_vector_bytes elts (DTYPE_Base dt) idx
        | _ =>
            raise_error "dvalue_extract_byte: type mismatch on DVALUE_Vector."
        end
    end.

  Inductive memory_byte : Type :=
  | MByte (dv : dvalue) (dt : dtyp) (idx : N) : memory_byte
  .

  Definition memory_byte_value (db : memory_byte) : EOU (MaybePoison Z) 
    := match db with
       | MByte dv dt idx =>
           dvalue_extract_byte dv dt (Z.of_N idx)
       end.

  Definition dvalue_to_memory_bytes (dv : dvalue) (dt : dtyp) : list memory_byte
    := map
         (fun idx => (MByte dv dt idx))
         (Nseq 0 (N.to_nat (sizeof_dtyp dt))).

  #[local] Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia].

  Definition absorb_pois {A} dt (c : EOUP A) (k : A -> EOU dvalue_base) : EOU dvalue_base :=
    x <- (c : EOU _) ;;
    match x with
    | Pois => ret (DVALUE_Poison dt)
    | NoPois v => k v
    end.

  Definition memory_bytes_to_dvalue_base (dbs : list memory_byte) (dt : dtyp_base) : EOU dvalue_base :=
    match dt with
    | DTYPE_I sz => 
        absorb_pois (DTYPE_Base dt)
          (map_monad (m := EOUP) (memory_byte_value) dbs)
          (fun v => ret (DVALUE_I sz (concat_bytes_Z_vint v)))

    | DTYPE_Iptr =>
        absorb_pois (DTYPE_Base dt)
          (map_monad memory_byte_value dbs)
          (fun zs => DVALUE_Iptr <$> from_Z (concat_bytes_Z zs))

    (* TODO: not sure if this should be wildcard provenance.
           TODO: not sure if this should truncate iptr value... *)
    (* TODO: not sure if this should be lazy OOM or not *)
    | DTYPE_Pointer =>
        absorb_pois (DTYPE_Base dt) (map_monad memory_byte_value dbs) 
          (fun zs => DVALUE_Pointer <$> int_to_ptr (concat_bytes_Z zs) wildcard_prov)
    | DTYPE_Void =>
        raise_error "memory_bytes_to_dvalue on void type."
    | DTYPE_FP FP_half =>
        raise_error "memory_bytes_to_dvalue: unsupported half."
    | DTYPE_FP FP_bfloat =>
        raise_error "memory_bytes_to_dvalue: unsupported bfloat"
    | DTYPE_FP FP_float =>
        absorb_pois (DTYPE_Base dt) (map_monad memory_byte_value dbs)
          (fun zs => ret (DVALUE_Float (Float32.of_bits (concat_bytes_Z_vint zs))))
    | DTYPE_FP FP_double => 
        absorb_pois (DTYPE_Base dt) (map_monad memory_byte_value dbs)
          (fun zs => ret (DVALUE_Double (Float.of_bits (concat_bytes_Z_vint zs))))
    | DTYPE_FP FP_x86_fp80 =>
        raise_error "memory_bytes_to_dvalue: unsupported X86_fp80."
    | DTYPE_FP FP_fp128 =>
        raise_error "memory_bytes_to_dvalue: unsupported fp128."
    | DTYPE_FP FP_ppc_fp128 =>
        raise_error "memory_bytes_to_dvalue: unsupported ppc_fp128."
    | DTYPE_Label =>
        raise_error "memory_bytes_to_dvalue: unsupported DTYPE_Label."
    | DTYPE_Token =>
        raise_error "memory_bytes_to_dvalue: unsupported DTYPE_Token."
    | DTYPE_Metadata =>
        raise_error "memory_bytes_to_dvalue: unsupported DTYPE_Metadata."
    | DTYPE_X86_mmx =>
        raise_error "memory_bytes_to_dvalue: unsupported DTYPE_X86_mmx."
    | DTYPE_Opaque =>
        raise_error "memory_bytes_to_dvalue: unsupported DTYPE_Opaque."

    | DTYPE_B sz =>
        raise_error "memory_bytes_to_dvalue_base: TODO: byte type"
    end.

  
  Fixpoint memory_bytes_to_dvalue (dbs : list memory_byte) (dt : dtyp) : EOU dvalue :=
    let list_memory_bytes_to_dvalue (pad : option N) :=
      fix go (offset : N) dts dbs :=
        match dts with
        | [] =>
            (* TODO: should we check that we have the appropriate number of extra padding bytes here? *)
            (* Long term we'll have to include padding bytes in the dvalue *)
            ret []
        | (dt::dts) =>
            let padding :=
              if pad
              then pad_amount (preferred_alignment (dtyp_alignment dt)) offset
              else 0%N
            in
            let zpadding := Z.of_N padding in
            let sz := sizeof_dtyp dt in
            (* Skip any padding bytes *)
            let dbs' := drop padding dbs in
            let init_bytes := take sz dbs' in
            let rest_bytes := drop sz dbs' in
            let offset' := offset + padding in
            f <- memory_bytes_to_dvalue init_bytes dt ;;
            rest <- go (offset' + sz) dts rest_bytes ;;
            ret (f :: rest)
        end
    in
    match dt with
    | DTYPE_Base dt => DVALUE_Base <$> (memory_bytes_to_dvalue_base dbs dt)

    (* NOTE: arrays and vectors are decorated with their whole type, which contains
         necessary size information.
     *)
    | DTYPE_Array sz t =>
        let sz' := sizeof_dtyp t in
        let elt_bytes :=
          if N.eqb sz' 0
          then repeatN sz []
          else split_every_nil sz' dbs
        in
        elts <- map_monad (fun es => memory_bytes_to_dvalue es t) elt_bytes;;
        ret (DVALUE_Array (DTYPE_Array sz t) elts)

    | DTYPE_Vector sz t =>
        let sz' := sizeof_dtyp (DTYPE_Base t) in
        let elt_bytes :=
          if N.eqb sz' 0
          then repeatN sz []
          else split_every_nil sz' dbs
        in
        elts <- map_monad (fun es => memory_bytes_to_dvalue_base es t) elt_bytes;;
        ret (DVALUE_Vector (DTYPE_Vector sz t) elts)
    | DTYPE_Struct false fields =>
        (DVALUE_Struct false) <$> (list_memory_bytes_to_dvalue (Some (max_preferred_dtyp_alignment fields)) 0 fields dbs)
                     
    | DTYPE_Struct true fields =>
        (DVALUE_Struct true) <$> (list_memory_bytes_to_dvalue None 0 fields dbs)
    end.
  
End MemoryByte.

