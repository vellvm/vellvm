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

  (* A byte of poison in the memory model *)
  Definition poison_memory_byte : memory_byte :=
    BYTE_Mixed 8 (repeat Bit_psn 8).

  (* Accumulates num_bytes copies of mb.*)
  Definition accumulate_memory_bytes (mb:memory_byte) (num_bytes : N) : list memory_byte -> list memory_byte :=
    N.rev_loop_acc (fun _ => mb) num_bytes 0.

  Definition accumulate_poison_bytes (num_bytes : N) :=
    accumulate_memory_bytes poison_memory_byte num_bytes.

  Definition accumulate_padding (offset : N) (pad_to : option N) (acc : list memory_byte) : N * (list memory_byte) :=
    match pad_to with
    | None => (offset, acc)
    | Some align =>
        let extra_bytes :=  N.modulo offset align in
        let num_padding_bytes := if negb (N.eqb extra_bytes 0) then align - extra_bytes else 0%N in
        (num_padding_bytes + offset, accumulate_poison_bytes num_padding_bytes acc)
    end.

  (* Given a type, there is a "bijection" between lists of memory bytes (of the
  right length) and dynamic values. *)

  (* Returns a memory byte at index 0 <= idx < (max 1 (bit_sz / 8)).
     If bit_sz is not divisible by 8, returns a BYTE_Mixed value with poison as the pad bits.
   *) 
  Definition memory_byte_of_dvalue_bv
    (bit_sz : positive) (bv : dvalue_bv bit_sz) (idx : N)
    : memory_byte :=
    
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
        (* If bit_sz isn't divisible by 8 and this is the last index, there is bit-level padding *)
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

  
  (* Computes the memory byte at index [idx] of the dvalue_base.
     Only valid if 0 <= [idx] < size_of_dv_base dvalue_base.

     TODO: 
     If the size of the dv in bits is not a multiple of 8, i.e. is such that
        n = [(bit_size dv) mod 8 <> 0]
     Then the last memory_byte should be of the form
        BYTE_Mixed [Bit_bit x1, .. , Bit_bit xn, Bit_psn, .. Bit_psn]
     where 
   *)
  Definition acc_memory_bytes_of_dvalue_base (dt:dtyp_base)
    (dv:dvalue_base) (offset : N) (acc : list memory_byte)
    : N * (list memory_byte)  :=
    let byte_size := sizeof_dtyp dt in
    let byte_gen := 
      match dv with
      | DVALUE_I sz x => memory_byte_of_dvalue_bv (BYTE_I x)
      | DVALUE_Iptr x => fun idx => BYTE_I (repr (extract_byte_Z (to_Z x) idx))
      | DVALUE_Pointer ptr => BYTE_Pointer 8 ptr
      | DVALUE_Float f =>  fun idx => BYTE_I (repr (extract_byte_Z (unsigned (Float32.to_bits f)) idx))
      | DVALUE_Double d => fun idx => BYTE_I (repr (extract_byte_Z (unsigned (Float.to_bits d)) idx))
      | DVALUE_Poison => fun idx => poison_memory_byte
      | DVALUE_None => fun idx => poison_memory_byte
                        (* was: raise_error "dvalue_extract_byte on DVALUE_None" *)
      | DVALUE_B sz bits => memory_byte_of_dvalue_bv bits
      end in
    (byte_size + offset, N.rev_loop_acc byte_gen byte_size 0 acc).
  
    
  (* Invariants:
     [acc] the accumulated list of memory_bytes so far is in _reverse_ order.
     [offset] is the offset in bytes of the next byte to be accumulated
         it is used to decide when to accumulate padding
     [pad_to] gives an (option) target that determines the amount of padding
         added to the end of the dvalue.



            (* Handle padding at the end of the structure *)
            let padding :=
              match pad with
              | Some max_pad
                => Sizeof.pad_amount max_pad offset
              | None =>
                  0%N
              end
            in
            if N.ltb  padding
            then
              (* Indexing into padding bytes *)
              (* TODO: currently we pad with poison bytes. *)
              ret poison_memory_byte
            else
              raise_error "No fields left for byte-indexing..."

   *)
  Fixpoint acc_dvalue_to_memory_bytes_h
    (dt:dtyp)
    (dv : dvalue) (offset : N)
    (pad_to : option N) (acc : list memory_byte)
    {struct dv}
    : EOU (N * (list memory_byte)) :=
    let accumulate_struct_bytes (pad : option N) : list dvalue -> list dtyp -> N -> list memory_byte -> EOU (N * list memory_byte) :=
      fix loop fields types (offset : N) (acc : list memory_byte) {struct fields} : EOU (N * list memory_byte) :=
        match fields, types with
        | [], [] => ret (accumulate_padding offset pad_to acc)
        | f::fs, dt::dts =>
            let field_pad := 
              if pad
              then Some (pad_amount (preferred_alignment (dtyp_alignment dt)) offset)
              else None
            in
            '(offset', bs) <- acc_dvalue_to_memory_bytes_h dt f offset field_pad acc ;;
            loop fs dts offset' bs
        | _, _ => raise_error "type-mismatch: structs / fields have different lengths"
        end
    in
    let dvalue_extract_array_bytes dt :=
      fix loop (elts : list dvalue) offset (acc : list memory_byte) {struct elts}  :=
        match elts with
        | [] => ret (accumulate_padding offset pad_to acc)
        | e::es =>
            let padding := Some (pad_amount (preferred_alignment (dtyp_alignment dt)) offset) in
            '(offset', bs) <- acc_dvalue_to_memory_bytes_h dt e offset padding acc ;; 
            loop es offset' bs 
        end
    in
    match dt with
    | DTYPE_Base dtb =>
        match dv with
        | DVALUE_Base dv =>
            let '(offset', bs) := acc_memory_bytes_of_dvalue_base dtb dv offset acc in
            ret (accumulate_padding offset' pad_to bs)
        | _ => raise_error "acc_dvalue_to_memory_bytes_h: type-mismatch non-base value"
        end
    | DTYPE_Struct packed dts =>
        match dv with
          (* TODO: could check that the type and dvalue packed flag agree *)
        | DVALUE_Struct _ fields =>
            (* A *packed* struct gets no inter-field padding; an unpacked one
               lays its fields out at their preferred alignments. This matches
               [sizeof_dtyp_Packed_struct] / [sizeof_dtyp_Struct] and the
               [DTYPE_Struct true/false] cases of [handle_gep_h]. *)
            let pad := if packed then None else Some (max_preferred_dtyp_alignment dts) in
            accumulate_struct_bytes pad fields dts offset acc
        | _ => raise_error "acc_dvalue_to_memory_bytes_h: type-mismatch non-struct value"
        end
    | DTYPE_Array _vector sz elt_t =>
        match dv with
        | DVALUE_Array v elts =>
            dvalue_extract_array_bytes elt_t elts offset acc
        | _ => raise_error ("acc_dvalue_to_memory_bytes_h: type-mismatch non-array value: "  ++ (show dv))
        end
    end.
  
  
  
  (* Toplevel operation to convert a dvalue into a list of memory_bytes. *)
  Definition dvalue_to_memory_bytes (dt:dtyp) (dv : dvalue) (pad_to : option N) : EOU (list memory_byte) :=
    '(offset, bytes) <- acc_dvalue_to_memory_bytes_h dt dv 0 pad_to [] ;;
    (* reverse the list *)
    ret (rev_append bytes []).

  
  (* (* Walk through a list *) *)
  (* (* Returns field index + number of bytes remaining *) *)
  (* Fixpoint extract_field_byte_helper (fields : list dtyp) (field_idx : N) (byte_idx : N) : EOU (dtyp * (N * N))%type *)
  (*   := match fields with *)
  (*      | [] => *)
  (*          raise_error "No fields left for byte-indexing..." *)
  (*      | (x::xs) => *)
  (*          let sz := sizeof_dtyp x *)
  (*          in if N.ltb byte_idx sz *)
  (*             then ret (x, (field_idx, byte_idx)) *)
  (*             else extract_field_byte_helper xs (N.succ field_idx) (byte_idx - sz) *)
  (*      end. *)

  (* Definition extract_field_byte (fields : list dtyp) (byte_idx : N) : EOU (dtyp * (N * N))%type *)
  (*   := extract_field_byte_helper fields 0 byte_idx. *)

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
  #[global] Instance EOUP_Monad : Monad EOUP :=
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
  

  #[local] Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia].

  Definition absorb_pois {A} (c : EOUP A) (k : A -> EOU dvalue_base) : EOU dvalue_base :=
    x <- (c : EOU _) ;;
    match x with
    | Pois => ret DVALUE_Poison
    | NoPois v => k v
    end.
  
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
    | [] => ret (N.eqb idx (sizeof_dtyp (DTYPE_Base DTYPE_Pointer)))
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

  (* A version of concat_bytes that trims extra bits from the last byte. *)
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

  Definition memory_byte_to_memory_bits (mb : memory_byte) : list memory_bit :=
    match mb with
    | BYTE_Pointer p idx => rev_append (N.rev_loop_acc (fun i => Bit_ptr p i) 8 (8 * idx) []) []
    | BYTE_I x  => rev_append (N.rev_loop_acc (fun i => Bit_bit (repr (extract_bit_vint x i))) 8 0 []) []
    | BYTE_Mixed bits => bits
    end.

  Fixpoint get_bits_of_memory_byte_list (bit_sz : N) (dbs : list memory_byte) acc : list memory_bit :=
    match dbs with
    | [] => if (N.eqb bit_sz 0) then
             acc
           else
             (* still need poison bits as padding *)
             N.rev_loop_acc (fun _ => Bit_psn) bit_sz 0 acc 
    | b::bs =>
        let bits := memory_byte_to_memory_bits b in
        if (N.ltb bit_sz 8) then
          rev_append (take bit_sz bits) acc
        else
          get_bits_of_memory_byte_list (bit_sz - 8) bs (rev_append bits acc)
        
    end.
  
  Definition memory_bytes_to_byte_value (bit_sz : positive) (dbs : list memory_byte) : EOU (@dvalue_bv _ bit_sz) :=
    match memory_bytes_to_int bit_sz dbs with
    (* First try to serialize as an integer *)
    | raise_ret (NoPois x) => ret (BYTE_I (repr x))
    | _ => match memory_bytes_to_pointer dbs with
          (* Next try to serialize as a pointer *)            
          | raise_ret (NoPois p) => ret (BYTE_Pointer bit_sz p 0)
          | _ => (* otherwise retain as just a list of mixed bits *)
              ret (BYTE_Mixed bit_sz (rev_append (get_bits_of_memory_byte_list (Npos bit_sz) dbs []) []))
          end
    end.

  Definition is_poison_bit (b : memory_bit) : bool :=
    match b with
    | Bit_psn => true
    | _ => false
    end.
  
  Definition all_poison_bits (bits : list memory_bit) : bool :=
    List.forallb is_poison_bit bits.

  Definition is_all_poison_byte (mb : memory_byte) : bool :=
    match mb with
    | BYTE_Mixed bits => all_poison_bits bits
    | _ => false
    end.
  
  Definition all_poison_bytes (bytes : list memory_byte) : bool :=
    List.forallb is_all_poison_byte bytes.
  
  Definition memory_bytes_to_dvalue_base (dbs : list memory_byte) (dt : dtyp_base) : EOU dvalue_base :=
    match dt with
    | DTYPE_I sz =>
        absorb_pois 
          (memory_bytes_to_int sz dbs)
          (fun v => ret (DVALUE_I sz (repr v)))

    | DTYPE_Iptr =>
        absorb_pois 
          (map_monad memory_byte_to_Z dbs)
          (fun zs => DVALUE_Iptr <$> from_Z (concat_bytes_Z zs))

    | DTYPE_Pointer =>
        absorb_pois (memory_bytes_to_pointer dbs)
                    (fun p => ret (DVALUE_Pointer p))
    | DTYPE_Void =>
        raise_error "memory_bytes_to_dvalue on void type."
    | DTYPE_FP FP_half =>
        raise_error "memory_bytes_to_dvalue: unsupported half."
    | DTYPE_FP FP_bfloat =>
        raise_error "memory_bytes_to_dvalue: unsupported bfloat"
    | DTYPE_FP FP_float =>
        absorb_pois (map_monad memory_byte_to_Z dbs)
          (fun zs => ret (DVALUE_Float (Float32.of_bits (concat_bytes_Z_vint zs))))
    | DTYPE_FP FP_double => 
        absorb_pois  (map_monad memory_byte_to_Z dbs)
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
        (* If all the bits are poison then create the poison value *)
        (* Question: do we have to check the length too *)
        if all_poison_bytes dbs then
          ret DVALUE_Poison
        else
        (* otherwise at least one is non-poision *)
        dv <- memory_bytes_to_byte_value sz dbs ;;
        ret (@DVALUE_B _ sz dv)
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
        ret (DVALUE_Array v elts)

    | DTYPE_Struct false fields =>
        (DVALUE_Struct false) <$> (list_memory_bytes_to_dvalue (Some (max_preferred_dtyp_alignment fields)) 0 fields dbs)
                     
    | DTYPE_Struct true fields =>
        (DVALUE_Struct true) <$> (list_memory_bytes_to_dvalue None 0 fields dbs)
    end.

(*
  Lemma round_trip_memory_bytes_to_dvalue_base (dt : dtyp_base) (dv : dvalue_base) i bs :
    dv <> DVALUE_None ->
    dtyp_base_of_dvalue_base dv = Some dt ->
      (acc_memory_bytes_of_dvalue_base dv i []) = (sizeof_dtyp (DTYPE_Base dt) + i, bs) <->
        memory_bytes_to_dvalue_base bs dt = raise_ret dv.
  Proof.
    intros HN HT.
    split; intros H.
    - unfold acc_memory_bytes_of_dvalue_base in H.
      inversion H; clear H.
      destruct dv; simpl in HT; inversion HT; subst; clear HT; simpl.
      6 : { destruct t; inversion H0. subst. clear HN H0.
            
            
      7 : { contradiction. }
      7 : { 
*)      

  
End MemoryByte.

