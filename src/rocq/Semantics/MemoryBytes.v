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
Definition extract_bit_vint {I} `{VInt I} (i : I) (idx : N) : Z
  := unsigned (modu (shru i (repr (Z.of_N idx))) (repr 2)).

Fixpoint concat_bits_vint {I} `{VInt I} (bits : list I) : I
  := match bits with
     | [] => repr 0
     | (bit::bits) =>
         add bit (shl (concat_bits_vint bits) (repr 1))
     end.

Definition extract_byte_vint {I} `{VInt I} (i : I) (idx : N) : Z
  := unsigned (modu (shru i (repr ((Z.of_N idx) * 8))) (repr 256)).

Fixpoint concat_bytes_vint {I} `{VInt I} (bytes : list I) : I
  := match bytes with
     | [] => repr 0
     | (byte::bytes) =>
         add byte (shl (concat_bytes_vint bytes) (repr 8))
     end.

(* TODO: Endianess *)
Definition extract_bit_Z (x:Z) (idx : N) : Z :=
  (Z.shiftr x (Z.of_N idx)) mod 2.

Definition extract_bit_N (x:N) (idx : N) : N :=
  (N.shiftr x idx) mod 2.

(* TODO: Endianess *)
Definition concat_bits_Z_vint {I} `{VInt I} (bits : list Z) : I
  := concat_bits_vint (map repr bits).

(* TODO: does this work correctly with negative x? *)
Definition extract_byte_Z (x : Z) (idx : N) : Z
  := (Z.shiftr x ((Z.of_N idx) * 8)) mod 256.

(* TODO: Endianess *)
Definition concat_bytes_Z_vint {I} `{VInt I} (bytes : list Z) : I
  := concat_bytes_vint (map repr bytes).

Fixpoint concat_bits_Z (bits : list Z) : Z
  := match bits with
     | [] => 0
     | (bit::bits) =>
         bit + (Z.shiftl (concat_bits_Z bits) 1)
     end.

(* TODO: Endianess *)
Fixpoint concat_bytes_Z (bytes : list Z) : Z
  := match bytes with
     | [] => 0
     | (byte::bytes) =>
         byte + (Z.shiftl (concat_bytes_Z bytes) 8)
     end.

Section MemoryByte.
  Context {Pa : Params}.

  (* Memory bytes are dvalue_bv values of 8 memory_bits.

     BYTE_Pointer p i -  represents i'th byte of pointer p, no poison bits
     BYTE_I x - is an 8-bit integral value, no poison bits
     BYTE_Mixed 8 bits -
        bits is a length 8 list that represents a combination of bits,
        pointers, poison
        Note that, unlike in the LLVM Side, it is valid to have all of
        the bits be poison.
   *)
  Definition memory_byte : Type := @dvalue_bv Pa 8.

  (* There is a "bijection" between lists of memory bytes (of the right length) and dynamic values. *)

  (* Returns a memory byte at index 0 <= idx < (max 1 (bit_sz / 8)).
     If bit_sz is not divisible by 8, returns a BYTE_Mixed value with poison as the pad bits.
   *) 
  Definition memory_byte_of_dvalue_bv (bit_sz : positive) (bv : dvalue_bv bit_sz) (idx : N) : memory_byte :=
    
    match bv with
    (* num_chunks := (8 * pointer_size / bit_sz)

       0 <= idx' < num_chunks and chunk_size = bit_sz
       bits in this chunk are numbered, so they are at offset (bit_sz * idx'):
         bit_sz * idx' + [0, ..., bit_sz-1]

       Need to extract the byte numbered of these bits:
       0 <= idx < (bit_sz / 8)

       8 * idx + [0, ..., 7]

       Assuming bit_sz >= 8 (so there is at least one bytes' worth of data)
       0 <= 8 * idx < bit_sz
       we want to "drop" 8 * idx bits and "take" the next 8
       This amounts to rescaling the first  bit_sz * idx' idx

       For example if [bit_sz] = 32 (so this is a 32-bit chunk of aligned pointer data)
       and this is the chunk at idx' = 1, then it can broken into 4 sub-pointer bytes)

       "raw" pointer bytes: [p0,p1,p2,p3,p4,p5,p6,p7,p8] = DVALUE_Pointer p
       At type dvalue_bv 32:   BYTE_pointer p 0 = [p0,p1,p2,p3] i.e., bits 32 * 0 + [0,1,2,...,31]
       At type dvalue_bv 32:   BYTE_pointer p 1 = [p4,p5,p6,p7] i.e., bits 32 * 1 + [0,1,2,...,31]
       To re-index to dvalue_bv 8:
           memory_byte_of_dvalue 32 (BYTE_pointer p 0) 0 = (BYTE_Pointer p 0) 
                                                       1 = (BYTE_Pointer p 1)

           memory_byte_of_dvalue 32 (BYTE_pointer p 1) 0 = (BYTE_Pointer p 4)
           memory_byte_of_dvalue 32 (BYTE_pointer p 1) 1 = (BYTE_Pointer p 5)

       bit_sz / 8 = 4        (bit_sz * idx' )/ 8 + idx
     *)
    | BYTE_Pointer p idx' =>
        (* TODO: Case when pointer bit_sz is not a mulutiple of 8 ? *)
        BYTE_Pointer 8 p (((Npos bit_sz) * idx' / 8) + idx)
    | BYTE_I x =>
        (* If bit_sz isn't divisible by 8 and this is the last index, there is padding *)
        let extra_bits := N.modulo (Npos bit_sz) 8 in
        if negb (N.eqb extra_bits 0) && (N.eqb (idx + 1) (sizeof_dtyp (DTYPE_Base (DTYPE_I bit_sz))))  then
          let pad_bits := 8 - extra_bits in
          let pad := repeat Bit_psn (N.to_nat pad_bits) in
          let mbits := map (fun i => Z_to_memory_bit (Z.of_N (extract_bit_N (Z.to_N (unsigned x)) i))) (Nseq (8 * idx) (N.to_nat extra_bits))
          in
          BYTE_Mixed 8 (mbits ++ pad)
        else
          BYTE_I (repr (extract_byte_vint x idx))
    | BYTE_Mixed bits =>
        let suffix := if N.eqb idx 0 then bits else drop (8 * (N.pred idx)) bits in
        let mbits := take 8 suffix in
        let pad := if negb (N.of_nat (List.length mbits) =? 8) then
                     repeat Bit_psn (8 - (List.length mbits)) else
                     []
        in
        BYTE_Mixed 8 (mbits ++ pad)
    end.

  (* A byte of poison in the memory model *)
  Definition poison_memory_byte : memory_byte :=
    BYTE_Mixed 8 (repeat Bit_psn 8).
  
  (* Computes the memory byte at index [idx] of the dvalue_base.
     Only valid if 0 <= [idx] < size_of_dv_base dvalue_base.

     TODO: 
     If the size of the dv in bits is not a multiple of 8, i.e. is such that
        n = [(bit_size dv) mod 8 <> 0]
     Then the last memory_byte should be of the form
        BYTE_Mixed [Bit_bit x1, .. , Bit_bit xn, Bit_psn, .. Bit_psn]
     where 
   *)
  Definition memory_byte_of_dvalue_base (dv:dvalue_base) (idx : N) : EOU memory_byte  :=
    match dv with
    | DVALUE_I sz x =>
        (* Here we can coerce the integer value to a dvalue_bv because the byte type
           and integer type values are the same when there is no poison *)
        ret (memory_byte_of_dvalue_bv (BYTE_I x) idx)
    | DVALUE_Iptr x =>
        ret (BYTE_I (repr (extract_byte_Z (to_Z x) idx)))
    | DVALUE_Pointer ptr =>
        ret (BYTE_Pointer 8 ptr idx)
    | DVALUE_Float f =>
        ret (BYTE_I (repr (extract_byte_Z (unsigned (Float32.to_bits f)) idx)))
    | DVALUE_Double d =>
        ret (BYTE_I (repr (extract_byte_Z (unsigned (Float.to_bits d)) idx)))
    | DVALUE_Poison dt =>
        (* NOTE: This is one place where the Memory Model violates the LLVM
           Invariants because the Memory Model doesn't have structured poison.
         *)
        ret poison_memory_byte
        
    | DVALUE_None =>
        (* TODO: Not sure if this should be an error, poison, or what. *)
        raise_error "dvalue_extract_byte on DVALUE_None"
    | DVALUE_B sz bits =>
        ret (memory_byte_of_dvalue_bv bits idx)
    end.
  

  (* TODO: does this work correctly with sub-byte size values? *)
  (* offset is the number of bytes indexed past so far *)
  Fixpoint memory_byte_of_dvalue (dv : dvalue) (dt : dtyp) (idx : N) {struct dv} : EOU memory_byte  :=
    let dvalue_extract_struct_bytes (pad : option N) : list dvalue -> list dtyp -> N -> N -> EOU memory_byte :=
      fix loop fields types (offset : N) (idx : N) {struct fields} : EOU memory_byte :=
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
            if N.ltb idx padding
            then
              (* Indexing into padding bytes *)
              (* TODO: currently we pad with poision bytes. *)
              ret poison_memory_byte
            else
              raise_error "No fields left for byte-indexing..."
        | f::fs, dt::dts =>
            let padding :=
              if pad
              then pad_amount (preferred_alignment (dtyp_alignment dt)) offset
              else 0%N
            in
            let sz := sizeof_dtyp dt in
            if N.ltb idx padding
            then
              (* Indexing into padding bytes *)
              ret poison_memory_byte
            else
              let offset' := (offset + padding)%N in
              let idx' := (idx - padding)%N in
              if N.ltb idx' sz
              then memory_byte_of_dvalue f dt idx'
              else loop fs dts (offset' + sz)%N (idx' - sz)%N
        | _, _ => raise_error "type-mismatch: structs / fields have different lengths"
        end
    in

    let dvalue_extract_array_bytes :=
      fix loop (elts : list dvalue) dt (idx : N) {struct elts}  :=
        match elts with
        | [] => raise_error "No fields left for byte-indexing..."
        | e::es =>
            let sz := sizeof_dtyp dt in
            if N.ltb idx sz
            then memory_byte_of_dvalue e dt idx
            else loop es dt (idx - sz)%N
        end
    in
    match dv with
    | DVALUE_Base dv => memory_byte_of_dvalue_base dv idx
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

    | DVALUE_Array v _ elts =>
        match dt with
        | DTYPE_Array _ sz dt =>
            dvalue_extract_array_bytes elts dt idx
        | _ =>
            raise_error "dvalue_extract_byte: type mismatch on DVALUE_Array."
        end
    end.

  (* Toplevel operation to convert a dvalue into a list of memory_bytes. *)
  Definition dvalue_to_memory_bytes (dv : dvalue) (dt : dtyp) : EOU (list memory_byte)
    := map_monad
         (memory_byte_of_dvalue dv dt)
         (Nseq 0 (N.to_nat (sizeof_dtyp dt))).


  
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

  Definition memory_bit_to_bit (mb : memory_bit) : EOUP Z :=
    match mb with
    | Bit_ptr p i  => ret (extract_bit_Z (ptr_to_int p) i)
    | Bit_psn => ret Pois
    | Bit_bit b => ret (unsigned b)
    end.


  (* Extract the bits from (non-poison) memory_bits or raise poison otherwise. *)
  Definition memory_bits_to_Z (bits : list memory_bit) : EOUP Z :=
    bits <- map_monad memory_bit_to_bit bits ;;
    ret (concat_bits_Z bits).

  Definition memory_byte_to_Z (mb : memory_byte) : EOUP Z :=
    match mb with
    | BYTE_Pointer p i => ret (extract_byte_Z (ptr_to_int p) i)
    | BYTE_I x => ret (unsigned x)
    | BYTE_Mixed bits =>
        memory_bits_to_Z bits
    end.
    
  
  
  (* Gets an integral byte value from a list of memory bits, stripping away provenance:
       given [b0; b1; ... ; bn]
       extracts bits numbered [idx*8 + 0; idx*8 + 1; ... idx*8 + 7]
       if none of them are poison, return the byte obtained by concatenating them
       if any are poison, raise poison
        
   *)
  Definition extract_byte_mixed_bits (bits : list memory_bit) (idx : N) : EOUP Z :=
    let suffix := if N.eqb idx 0 then bits else drop (8 * (N.pred idx)) bits in
    let mbits := take 8 suffix in
    if negb (N.of_nat (List.length mbits) =? 8) then
      raise_ub "extract_byte_mixed_bits: not enough bits"
    else
      vs <- map_monad memory_bit_to_bit mbits ;;
      ret (concat_bits_Z vs).
  

  (* Should probably not need this *)
  (*
  Definition dvalue_base_extract_byte (dv : dvalue_base) (idx : N) : EOUP Z :=
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
        dvalue_bv_extract_byte bits idx
    end.
   *)
  (*
  (* offset is the number of bytes indexed past so far *)
  Fixpoint dvalue_extract_memory_byte (dv : dvalue) (dt : dtyp) (idx : N) {struct dv} : EOUP memory_byte  :=
    let dvalue_extract_struct_bytes (pad : option N) : list dvalue -> list dtyp -> N -> N -> EOUP memory_byte :=
      fix loop fields types (offset : N) (idx : N) {struct fields} : EOUP Z :=
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
            if N.ltb idx padding
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
            let sz := sizeof_dtyp dt in
            if N.ltb idx padding
            then
              (* Indexing into padding bytes *)
              (* TODO: currently we just pad with 0 bytes. This *)
      (*            prevents storing data in padding, though, which is *)
      (*            technically allowed *)
              ret 0%Z
            else
              let offset' := (offset + padding)%N in
              let idx' := (idx - padding)%N in
              if N.ltb idx' sz
              then dvalue_extract_byte f dt idx'
              else loop fs dts (offset' + sz)%N (idx' - sz)%N
        | _, _ => raise_error "type-mismatch: structs / fields have different lengths"
        end
    in

    let dvalue_extract_array_bytes :=
      fix loop (elts : list dvalue) dt (idx : N) {struct elts}  :=
        match elts with
        | [] => raise_error "No fields left for byte-indexing..."
        | e::es =>
            let sz := sizeof_dtyp dt in
            if N.ltb idx sz
            then dvalue_extract_byte e dt idx
            else loop es dt (idx - sz)%N
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

    | DVALUE_Array v _ elts =>
        match dt with
        | DTYPE_Array _ sz dt =>
            dvalue_extract_array_bytes elts dt idx
        | _ =>
            raise_error "dvalue_extract_byte: type mismatch on DVALUE_Array."
        end
    end.
   *)


  #[local] Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia].

  Definition absorb_pois {A} dt (c : EOUP A) (k : A -> EOU dvalue_base) : EOU dvalue_base :=
    x <- (c : EOU _) ;;
    match x with
    | Pois => ret (DVALUE_Poison dt)
    | NoPois v => k v
    end.

  (*
  (* returns true if and only if the sequence of memory bytes contain identical data but
     increasing indices from idx to tgt.
   *)
  Fixpoint validate_sequence (dv : dvalue) (dt : dtyp) (dbs : list memory_byte) (idx:N) (tgt : N) : bool := 
    match dbs with
    | [] => N.eqb idx tgt  (* did we reach the target with none left *)
    | (MByte dv' dt' idx') :: dbs' =>
        (N.ltb idx tgt) &&  (* short circuit if the index is too big for tgt *)
          (N.eqb idx idx') && (dvalue_eqb dv dv') && (dtyp_eqb dt dt') &&
          validate_sequence dv dt dbs' (idx+1) tgt
    end.

  
  (* There are only two ways that a sequence of memory bytes can have valid pointer
     provenance:
     They must be correctly sequenced indices into the _same_ [DVALUE_Pointer p] or
     they must be correctly sequenced indices into the _same_ [DVALUE_B (BYTE_Pointer p] )
     then the provenance is p's provenance.  Otherwise there is no provenance
      (or the byte value containts poison bits)
   *)
  Definition get_provenance_from_memory_bytes (dbs : list memory_byte) : option prov :=
    match dbs with
    | [] => None
    | v::rst =>
        match v with
        | MByte (DVALUE_Pointer p) dt _ =>
            if validate_sequence (DVALUE_Pointer p) dt dbs 0 pointer_size then
              Some (ptr_provenance p)
            else None
        | MByte (DVALUE_B sz (BYTE_Pointer p)) dt _ =>
            if N.eqb (Npos sz) pointer_size then
              if validate_sequence (DVALUE_Pointer p) dt dbs 0 pointer_size then
                Some (ptr_provenance p)
              else None
            else
              None
        | _ => None
        end
    end.
   *)


  

  
  (* Recover a pointer from a byte representation for pointer p.
     The byte at index 0 <= i < pointer_size must be of the form:

     BYTE_Pointer 8 p i
     BYTE_Mixed 8 [Bit_ptr p (8*i)+0;
                   Bit_ptr p (8*i)+1;
                   ...
                   Bit_ptr p (8*i)+7]

   *)
  Fixpoint valid_pointer_bits p base offset bits : EOUP bool :=
    match bits with
    | [] => ret (N.eqb offset 8)
    | (Bit_ptr q j) :: rest  =>
        if eq_dec_ptr p q then
          if N.eqb j (base + offset) then
            valid_pointer_bits p base (1+offset) rest 
          else
            ret false
        else
          ret false
    | _ => ret Pois
    end.

  
  Definition valid_pointer_byte (p:ptr) (idx:N) (mb:memory_byte) : EOUP bool :=
    match mb with
    | BYTE_Pointer q i =>
        if eq_dec_ptr p q then ret (N.eqb idx i) else ret false 
    | BYTE_Mixed bits =>
        valid_pointer_bits p (idx * 8) 0 bits 
    | BYTE_I _ => ret false
    end.

  Fixpoint valid_pointer_bytes (p:ptr) (idx:N) (bytes : list memory_byte) : EOUP bool :=
    match bytes with
    | [] => ret (N.eqb idx 8)
    | b::rest =>
        v <- valid_pointer_byte p idx b ;;
        if v then valid_pointer_bytes p (1+idx) rest else ret false
    end.
  
  Definition memory_bytes_to_pointer (dbs : list memory_byte) : EOUP ptr :=
    match dbs with
    | ((BYTE_Pointer p _) :: _)
    | ((BYTE_Mixed ((Bit_ptr p _)::_)) :: _) =>
        v <- valid_pointer_bytes p 0 dbs ;;
        if v then ret p else ret Pois
    | _ => ret Pois
    end.

  (*
        let extra_bits := N.modulo (Npos bit_sz) 8 in
        if negb (N.eqb extra_bits 0) && (N.eqb (idx + 1) (sizeof_dtyp (DTYPE_Base (DTYPE_I bit_sz))))  then
          let pad_bits := 8 - extra_bits in
          let pad := repeat Bit_psn (N.to_nat pad_bits) in
          let mbits := map (fun i => Z_to_memory_bit (Z.of_N (extract_bit_N (Z.to_N (unsigned x)) i))) (Nseq (8 * idx) (N.to_nat extra_bits))
          in
          BYTE_Mixed 8 (mbits ++ pad)
        else
          BYTE_I (repr (extract_byte_vint x idx))

Fixpoint concat_bytes_Z (bytes : list Z) : Z
  := match bytes with
     | [] => 0
     | (byte::bytes) =>
         byte + (Z.shiftl (concat_bytes_Z bytes) 8)
     end.


*)

  (* A version of *)
  Fixpoint concat_bytes_Z_mixed (extra:N) (acc:Z) (dbs : list memory_byte) : EOUP Z :=
    match dbs with
    | [] => ret acc
      (* Special case: the last byte it must be mixed and we ignore the poison part. *)
    | (BYTE_Mixed bits)::[] =>
        x <- memory_bits_to_Z (take extra bits) ;;
        ret (acc + x)%Z
    | _::[] => raise_error "concat_bytes_Z_mixed - broken invariants for memory bytes"
    | b::rest =>
        z <- memory_byte_to_Z b ;;
        concat_bytes_Z_mixed extra (acc + z) rest
    end.
  
  Definition memory_bytes_to_int (bit_sz : positive) (dbs : list memory_byte) : EOUP Z :=
    let extra_bits := N.modulo (Npos bit_sz) 8 in
    if negb (N.eqb extra_bits 0) then
      (* we need to deal with padding *)
      concat_bytes_Z_mixed extra_bits 0 dbs 
    else
      v <- map_monad (m := EOUP) (memory_byte_to_Z) dbs ;;
      ret (concat_bytes_Z v).

  Definition memory_bytes_to_dvalue_base (dbs : list memory_byte) (dt : dtyp_base) : EOU dvalue_base :=
    match dt with
    | DTYPE_I sz =>
        (* TODO: fix for integer sizes not-multiples of 8. *)
        absorb_pois (DTYPE_Base dt)
          (memory_bytes_to_int sz dbs)
          (fun v => ret (DVALUE_I sz (repr v)))

    | DTYPE_Iptr =>
        absorb_pois (DTYPE_Base dt)
          (map_monad memory_byte_to_Z dbs)
          (fun zs => DVALUE_Iptr <$> from_Z (concat_bytes_Z zs))

    (* TODO: not sure if this should be wildcard provenance.
           TODO: not sure if this should truncate iptr value... *)
    (* TODO: not sure if this should be lazy OOM or not *)
    | DTYPE_Pointer =>
        absorb_pois (DTYPE_Base dt) (memory_bytes_to_pointer dbs)
                    (fun p => ret (DVALUE_Pointer p))
    | DTYPE_Void =>
        raise_error "memory_bytes_to_dvalue on void type."
    | DTYPE_FP FP_half =>
        raise_error "memory_bytes_to_dvalue: unsupported half."
    | DTYPE_FP FP_bfloat =>
        raise_error "memory_bytes_to_dvalue: unsupported bfloat"
    | DTYPE_FP FP_float =>
        absorb_pois (DTYPE_Base dt) (map_monad memory_byte_to_Z dbs)
          (fun zs => ret (DVALUE_Float (Float32.of_bits (concat_bytes_Z_vint zs))))
    | DTYPE_FP FP_double => 
        absorb_pois (DTYPE_Base dt) (map_monad memory_byte_to_Z dbs)
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
    | DTYPE_Array v sz t =>
        let sz' := sizeof_dtyp t in
        let elt_bytes :=
          if N.eqb sz' 0
          then repeatN sz []
          else split_every_nil sz' dbs
        in
        elts <- map_monad (fun es => memory_bytes_to_dvalue es t) elt_bytes;;
        ret (DVALUE_Array v (DTYPE_Array v sz t) elts)

    | DTYPE_Struct false fields =>
        (DVALUE_Struct false) <$> (list_memory_bytes_to_dvalue (Some (max_preferred_dtyp_alignment fields)) 0 fields dbs)
                     
    | DTYPE_Struct true fields =>
        (DVALUE_Struct true) <$> (list_memory_bytes_to_dvalue None 0 fields dbs)
    end.
  
End MemoryByte.

