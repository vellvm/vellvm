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

  (* Emit exactly [n] poison padding bytes.  Distinct from
     [accumulate_padding], which aligns an absolute offset: a field must be
     padded out to its *alloc size* by a fixed number of bytes, which is only
     the same thing when the field happens to start aligned (it does not, in a
     packed struct). *)
  Definition accumulate_padding_bytes (offset : N) (n : N) (acc : list memory_byte)
    : N * (list memory_byte) :=
    ((offset + n)%N, accumulate_poison_bytes n acc).

  (* Align an absolute offset: emit [pad_amount] poison bytes so that the
     offset becomes [pad_to align offset].  [None] means "no alignment
     requested" and is the identity. *)
  Definition accumulate_padding (offset : N) (opt_align : option N) (acc : list memory_byte)
    : N * (list memory_byte) :=
    match opt_align with
    | None => (offset, acc)
    | Some align =>
        let n := pad_amount align offset in
        ((offset + n)%N, accumulate_poison_bytes n acc)
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
        (* LangRef ('store'): a value whose width is not a whole number of
           bytes "will be zero extended to the next larger multiple of the
           byte size" -- so the last byte is just the top bits of [x], which
           [extract_byte_vint] already fills with zeros. *)
        BYTE_I (repr (extract_byte_vint x idx))
    | BYTE_Mixed bits =>
        (* byte [idx] is bits [8*idx .. 8*idx+7]; the old [8 * N.pred idx] made
           bytes 0 and 1 identical *)
        let mbits := take 8 (drop (8 * idx) bits) in
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
    let byte_size := store_size_dtyp dt in
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
    (tail_align : option N) (acc : list memory_byte)
    {struct dv}
    : EOU (N * (list memory_byte)) :=
    (* [pad] is [Some a] for an unpacked struct (a = its own alignment) and
       [None] for a packed one.  Each field is laid out as LLVM's
       [StructLayout] does: align the offset (unpacked only), emit the field,
       then pad it out to its *alloc* size.  The [], [] case emits the
       struct's own tail padding, which is part of its store size. *)
    let accumulate_struct_bytes (pad : option N) : list dvalue -> list dtyp -> N -> list memory_byte -> EOU (N * list memory_byte) :=
      fix loop fields types (offset : N) (acc : list memory_byte) {struct fields} : EOU (N * list memory_byte) :=
        match fields, types with
        | [], [] =>
            let '(offset, acc) := accumulate_padding offset pad acc in
            ret (accumulate_padding offset tail_align acc)
        | f::fs, dt::dts =>
            let a := preferred_alignment (dtyp_alignment dt) in
            (* [alloc_size_dtyp] recomputes [store_size_dtyp] internally, so
               bind both once per field *)
            let ssz := store_size_dtyp dt in
            let asz := alloc_size_dtyp dt in
            let '(offset, acc) :=
              accumulate_padding offset (if pad then Some a else None) acc in
            (* The field is laid out relative to *its own* start, so the
               recursive call begins at 0 and the parent adds the field's
               extent.  Passing the absolute [offset] down would make a
               nested unpacked aggregate pad itself against the enclosing
               offset, which disagrees with [store_size_dtyp] (and with LLVM,
               and with the reader) whenever that offset is not a multiple of
               the field's alignment -- as inside a packed struct. *)
            '(coff, bs) <- acc_dvalue_to_memory_bytes_h dt f 0%N None acc ;;
            let '(offset'', bs') :=
              accumulate_padding_bytes (offset + coff)%N (asz - ssz) bs in
            loop fs dts offset'' bs'
        | _, _ => raise_error "type-mismatch: structs / fields have different lengths"
        end
    in
    (* Array elements sit at their alloc size; vector elements are contiguous
       at their store size. *)
    let dvalue_extract_array_bytes (vector : bool) dt :=
      (* [dt] is fixed for the whole loop, so the per-element tail padding is
         computed once here rather than at every element (mirrors the reader's
         [array_elts_to_dvalue]) *)
      let elt_pad :=
        if vector then 0%N else (alloc_size_dtyp dt - store_size_dtyp dt)%N in
      fix loop (elts : list dvalue) offset (acc : list memory_byte) {struct elts}  :=
        match elts with
        | [] => ret (accumulate_padding offset tail_align acc)
        | e::es =>
            (* as in the struct loop: the element is laid out from 0 *)
            '(coff, bs) <- acc_dvalue_to_memory_bytes_h dt e 0%N None acc ;;
            let '(offset'', bs') :=
              accumulate_padding_bytes (offset + coff)%N elt_pad bs in
            loop es offset'' bs'
        end
    in
    match dt with
    | DTYPE_Base dtb =>
        match dv with
        | DVALUE_Base dv =>
            let '(offset', bs) := acc_memory_bytes_of_dvalue_base dtb dv offset acc in
            ret (accumulate_padding offset' tail_align bs)
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
        | DVALUE_Base DVALUE_Poison =>
            (* Poison inhabits every type ([DVALUE_Poison_typ_agg]), so a
               poison at aggregate type is well-typed: it serializes to the
               type's worth of poison bytes. *)
            let '(offset', bs) := accumulate_padding_bytes offset (store_size_dtyp dt) acc in
            ret (accumulate_padding offset' tail_align bs)
        | _ => raise_error "acc_dvalue_to_memory_bytes_h: type-mismatch non-struct value"
        end
    | DTYPE_Array _vector sz elt_t =>
        match dv with
        | DVALUE_Array v elts =>
            dvalue_extract_array_bytes _vector elt_t elts offset acc
        | DVALUE_Base DVALUE_Poison =>
            (* Poison inhabits every type ([DVALUE_Poison_typ_agg]), so a
               poison at aggregate type is well-typed: it serializes to the
               type's worth of poison bytes. *)
            let '(offset', bs) := accumulate_padding_bytes offset (store_size_dtyp dt) acc in
            ret (accumulate_padding offset' tail_align bs)
        | _ => raise_error ("acc_dvalue_to_memory_bytes_h: type-mismatch non-array value: "  ++ (show dv))
        end
    end.
  

  (** ** Serializing a [dvalue]: the layout model

      [dvalue_to_memory_bytes dt dv tail_align] lays [dv] out as the bytes of a
      value of type [dt], as they would appear in memory.

      *** Why the type is needed
      The value alone does not determine the layout: [DVALUE_Poison] inhabits
      every type ([DVALUE_Poison_typ_agg]), so its width comes from [dt], and
      so does every padding decision inside an aggregate.

      *** The layout law
      Writing [|bs|] for the number of bytes produced, the intended invariant is

        dvalue_has_dtyp dv dt ->
        dvalue_to_memory_bytes dt dv None = ret bs ->
        |bs| = store_size_dtyp dt

      (and [pad_to a (store_size_dtyp dt)] for [tail_align = Some a]).  This is
      [dvalue_to_memory_bytes_sizeof] in
      [Theory/MemoryBytesFacts.v].  Case by case, matching
      [SizeofTheory]:

      - [DTYPE_Base dtb] emits [store_size_dtyp dtb] bytes, no padding.

      - [DTYPE_Struct true dts] (*packed*) emits the fields back to back with no
        padding anywhere -- [sizeof_dtyp_Packed_struct].

      - [DTYPE_Struct false dts] (unpacked) emits, for each field of type [t],
        *leading* padding up to [preferred_alignment (dtyp_alignment t)] and
        then [store_size_dtyp t] bytes; after the last field, *trailing* padding up
        to [max_preferred_dtyp_alignment dts].  That is exactly
        [sizeof_dtyp_Struct]:
          pad_to (max_preferred_dtyp_alignment dts)
                 (fold_left (fun acc t => pad_to_align (dtyp_alignment t) acc
                                          + store_size_dtyp t) dts 0)
        The trailing padding is *intrinsic* to the struct -- it is part of its
        [store_size_dtyp] -- so it must be emitted whatever the caller asks for.
        It is NOT the same thing as [tail_align].

      - [DTYPE_Array _ sz t] emits [sz] elements of [store_size_dtyp t] bytes each
        with no padding between them -- [sizeof_dtyp_array].  An element's own
        trailing padding is already inside [store_size_dtyp t], which is what makes
        a contiguous layout correct.

      *** Preconditions
      - [dvalue_has_dtyp dv dt].  The element-count part matters: the array case
        loops over the elements it is given and ignores [sz], so a short array
        value serializes without complaint and yields too few bytes.
      - Bytes are laid out relative to offset [0] and are assumed to be written
        at an address that is a multiple of
        [preferred_alignment (dtyp_alignment dt)].  All padding is computed from
        the offset *within* the value, so this assumption is what makes the
        result correctly aligned once in memory.

      *** [tail_align]
      [Some a] asks for extra padding so the value occupies a multiple of [a]
      bytes; [None] asks for none.  It is a request from the caller, and is
      independent of whether the value is a packed struct.  Both callers in the
      development ([write_dvalue] and the bitcast case of [convert]) pass
      [None], so the [Some] case is currently unexercised.
      (Previously named [pad_to], which collides with [Sizeof.pad_to].)
   *)
  Definition dvalue_to_memory_bytes (dt:dtyp) (dv : dvalue) (tail_align : option N)
    : EOU (list memory_byte) :=
    '(offset, bytes) <- acc_dvalue_to_memory_bytes_h dt dv 0 tail_align [] ;;
    (* reverse the list *)
    ret (rev_append bytes []).

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
    

  Definition absorb_pois {A} (c : EOUP A) (k : A -> EOU dvalue_base) : EOU dvalue_base :=
    catch_pois DVALUE_Poison c k.
  
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
    | Bit_bit _ :: _ => ret false  (* an integer bit: not this pointer *)
    | Bit_psn :: _ => ret Pois
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
    | [] => ret (N.eqb idx (store_size_dtyp (DTYPE_Base DTYPE_Pointer)))
    | b::rest =>
        v <- valid_pointer_byte p idx b ;;
        if v then valid_pointer_bytes p (1+idx) rest else ret false
    end.
  
  (* LangRef ('bitcast', a byte value to a pointer type): if no bit is
     poison but the bits are not all those of one pointer, correctly
     ordered, the result is a pointer with the address given by the integer
     value of the bits, and without provenance.  (A load at pointer type
     follows the same rules.)  Any poison byte makes it poison. *)
  Definition memory_bytes_to_address_ptr (dbs : list memory_byte) : EOUP ptr :=
    zs <- map_monad memory_byte_to_Z dbs ;;
    NoPois <$> int_to_ptr (concat_bytes_Z zs) nil_prov.

  Definition memory_bytes_to_pointer (dbs : list memory_byte) : EOUP ptr :=
    match dbs with
    | ((BYTE_Pointer p _) :: _)
    | ((BYTE_Mixed ((Bit_ptr p _)::_)) :: _) =>
        v <- valid_pointer_bytes p 0 dbs ;;
        if v then ret p else memory_bytes_to_address_ptr dbs
    | _ => memory_bytes_to_address_ptr dbs
    end.

  Definition memory_byte_to_memory_bits (mb : memory_byte) : list memory_bit :=
    match mb with
    | BYTE_Pointer p idx => rev_append (N.rev_loop_acc (fun i => Bit_ptr p i) 8 (8 * idx) []) []
    | BYTE_I x  => rev_append (N.rev_loop_acc (fun i => Bit_bit (repr (extract_bit_vint x i))) 8 0 []) []
    | BYTE_Mixed bits => bits
    end.

  (* A version of concat_bytes that trims extra bits from the last byte. *)
  (* Like [concat_bytes_Z], but only the low [extra] bits of the last byte
     belong to the value; the rest is padding.  Each byte has to
     be weighted by its position, exactly as [concat_bytes_Z] does -- an
     unweighted running sum reads [i12 4000] back as 175. *)
  Fixpoint concat_bytes_Z_mixed (extra:N) (dbs : list memory_byte) : EOUP Z :=
    match dbs with
    | [] => ret 0%Z
    (* only the low [extra] bits of the last byte belong to the value,
       whatever wrote it *)
    | (BYTE_I y)::[] => ret (unsigned y mod 2 ^ Z.of_N extra)%Z
    | b::[] => memory_bits_to_Z (take extra (memory_byte_to_memory_bits b))
    | b::rest =>
        z <- memory_byte_to_Z b ;;
        r <- concat_bytes_Z_mixed extra rest ;;
        ret (z + Z.shiftl r 8)%Z
    end.

  Definition memory_bytes_to_int (bit_sz : positive) (dbs : list memory_byte) : EOUP Z :=
    let extra_bits := N.modulo (Npos bit_sz) 8 in
    if negb (N.eqb extra_bits 0) then
      (* we need to deal with padding *)
      concat_bytes_Z_mixed extra_bits dbs 
    else
      v <- map_monad (m := EOUP) (memory_byte_to_Z) dbs ;;
      ret (concat_bytes_Z v).


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
  
  (* Is [mb] byte number [idx] of pointer [p]?  This is just [valid_pointer_byte]
     read as a plain predicate: it answers [NoPois] on every byte shape, so the
     other outcomes can only be [Pois], which is "no". *)
  Definition pointer_byte_at (p : ptr) (idx : N) (mb : memory_byte) : bool :=
    match valid_pointer_byte p idx mb with
    | raise_ret (NoPois b) => b
    | _ => false
    end.

  Fixpoint pointer_slice_from (p : ptr) (idx : N) (dbs : list memory_byte) : bool :=
    match dbs with
    | [] => true
    | b :: rest => pointer_byte_at p idx b && pointer_slice_from p (1+idx) rest
    end.

  (** Recognise a contiguous run of bytes of a *single* pointer, starting at
      whatever index the run happens to begin at:

        [BYTE_Pointer 8 p k; BYTE_Pointer 8 p (k+1); ...]

      This is deliberately weaker than [memory_bytes_to_pointer], which
      reconstructs a *whole* pointer (it requires the run to start at index 0
      and to span the full pointer width) because that is what a
      [DTYPE_Pointer] read needs.  A [DTYPE_B] read has the opposite job: it
      must preserve the byte-level representation, provenance and byte index
      included, so that storing [p] and reading it back as, say,
      [<8 x DTYPE_B 8>] yields bytes [0..7] of [p] rather than eight
      provenance-free integers.  A sub-word slice is representable: bytes
      [k..k+n-1] read at [DTYPE_B (8*n)] give [BYTE_Pointer (8*n) p k]. *)
  Definition memory_bytes_to_pointer_slice (dbs : list memory_byte) : option (ptr * N) :=
    match dbs with
    | (BYTE_Pointer p k) :: _ =>
        if pointer_slice_from p k dbs then Some (p, k) else None
    | (BYTE_Mixed ((Bit_ptr p j) :: _)) :: _ =>
        let k := (j / 8)%N in
        if pointer_slice_from p k dbs then Some (p, k) else None
    | _ => None
    end.

  (* Is a pointer slice starting at byte [k] a whole [BYTE_Pointer] chunk at
     width [bit_sz]?  The chunk index counts [bit_sz]-bit chunks, so the
     width must be a whole number of bytes and the slice must start on a
     chunk boundary.  This is [is_pointer_chunk] (DynamicValues.v), stated
     on the starting byte rather than the starting bit. *)
  Definition pointer_chunk_aligned (bit_sz : positive) (k : N) : bool :=
    N.eqb (Npos bit_sz mod 8) 0 && N.eqb ((k * 8) mod Npos bit_sz) 0.

  (* The bits read as bits: [BYTE_Mixed] if any of them is poison or part of
     a pointer, otherwise [BYTE_I].  The pointer test must come first:
     [memory_byte_to_Z] answers pointer bits with their address, so reading
     a pointer bit as an integer would strip its provenance.  With neither
     pointer nor poison bits the integer read cannot fail; its fall-through
     is not reached. *)
  Definition memory_bytes_to_bits_value (bit_sz : positive) (dbs : list memory_byte)
    : @dvalue_bv _ bit_sz :=
    let bits := rev_append (get_bits_of_memory_byte_list (Npos bit_sz) dbs []) [] in
    if existsb is_ptr_bit bits || existsb is_poison_bit bits then BYTE_Mixed bit_sz bits
    else
      match memory_bytes_to_int bit_sz dbs with
      | raise_ret (NoPois x) => BYTE_I (repr x)
      | _ => BYTE_I (repr (int_bits_to_Z bits))
      end.

  (* The canonical representation of the bits (see "Canonical
     [dvalue_bv]s" in DynamicValues.v), except for the all-poison case,
     which [memory_bytes_to_dvalue_base] handles. *)
  Definition memory_bytes_to_byte_value (bit_sz : positive) (dbs : list memory_byte) : EOU (@dvalue_bv _ bit_sz) :=
    match memory_bytes_to_pointer_slice dbs with
    (* A slice of one pointer keeps its provenance and index -- as a
       [BYTE_Pointer] when it is a whole aligned chunk, otherwise as bits. *)
    | Some (p, k) =>
        if pointer_chunk_aligned bit_sz k
        then
          (* [k] is a *byte* index, but [BYTE_Pointer]'s index counts chunks
             of [bit_sz] bits -- [memory_byte_of_dvalue_bv] writes chunk [i]
             of a [BYTE_Pointer _ i] starting at byte [(bit_sz * i) / 8].
             Invert that here, so reading bytes 4..7 of [p] at [DTYPE_B 32]
             gives [BYTE_Pointer 32 p 1]. *)
          ret (BYTE_Pointer bit_sz p ((k * 8) / Npos bit_sz))
        else ret (memory_bytes_to_bits_value bit_sz dbs)
    | None => ret (memory_bytes_to_bits_value bit_sz dbs)
    end.

  (* [is_poison_bit] is defined in DynamicValues.v, next to [dvalue_bv_canonical]. *)
  
  Definition all_poison_bits (bits : list memory_bit) : bool :=
    List.forallb is_poison_bit bits.

  Definition is_all_poison_byte (mb : memory_byte) : bool :=
    match mb with
    | BYTE_Mixed bits => all_poison_bits bits
    | _ => false
    end.
  
  (** [poison_split dbs = (k, rest)] splits [dbs] at its first non-poison
      byte: [k] is the number of leading all-poison bytes and [rest] is what
      follows, so [rest = []] exactly when every byte is poison.  Like
      [forallb] it stops as soon as it sees a non-poison byte.

      This replaces a boolean [all_poison_bytes] test in the deserializer.
      The same scan then does two jobs: it selects the all-poison fast path,
      and its index [k] says which fields / array elements lie entirely
      before the first non-poison byte, so those can be answered with
      [DVALUE_Poison] by arithmetic instead of being re-scanned. *)
  Fixpoint poison_split (dbs : list memory_byte) : N * list memory_byte :=
    match dbs with
    | [] => (0%N, [])
    | b :: rest =>
        if is_all_poison_byte b
        then let '(k, tl) := poison_split rest in ((1 + k)%N, tl)
        else (0%N, b :: rest)
    end.

  Definition all_poison_bytes (bytes : list memory_byte) : bool :=
    match snd (poison_split bytes) with
    | [] => true
    | _ :: _ => false
    end.
  
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
        (* If all the bytes are poison then create the poison value *)
        if all_poison_bytes dbs then
          ret DVALUE_Poison
        else
        dv <- memory_bytes_to_byte_value sz dbs ;;
        (* The byte test above also sees bits beyond the value (the padding
           of a last, partial byte), so the value's own bits can still all be
           poison. *)
        if dvalue_bv_all_poison dv then ret DVALUE_Poison
        else ret (@DVALUE_B _ sz dv)
    end.

  
  (** ** Deserializing: [memory_bytes_to_dvalue dbs dt]

      The inverse of [dvalue_to_memory_bytes], and it has to agree with it byte
      for byte.  Where the writer *emits* padding, the reader *skips* it.

      *** Precondition
      [dbs] is expected to be exactly [store_size_dtyp dt] bytes, which is what
      [read_dvalue] supplies ([read_bytes p (store_size_dtyp dt)]).  The array case
      depends on it: [split_every_nil (store_size_dtyp t) dbs] chops *all* of [dbs],
      so a longer [dbs] yields more than [sz] elements rather than an error.

      *** Where the padding goes
      - Structs: [list_memory_bytes_to_dvalue] drops
        [pad_amount (preferred_alignment (dtyp_alignment t)) offset] bytes
        before each field and then consumes [store_size_dtyp t] -- the exact mirror
        of the writer's *leading* padding.  It is called with
        [Some (max_preferred_dtyp_alignment fields)] for an unpacked struct and
        [None] for a packed one, so the packed/unpacked decision is taken from
        the type on both sides.
      - Arrays: no padding between elements; the split is at [store_size_dtyp t].
      - Trailing padding is *ignored*: the [[]] case of the field loop returns
        without inspecting what is left, so surplus bytes at the end are
        dropped.  This is why a writer that omits a struct's trailing padding
        still round-trips at the top level, and why the bug is only visible in
        fields that follow a misaligned one.

      *** Round trip
      The intended statement is

        dvalue_has_dtyp dv dt ->
        dvalue_to_memory_bytes dt dv None = ret bs ->
        exists dv', memory_bytes_to_dvalue bs dt = ret dv' /\ <dv' agrees with dv>

      It is deliberately not the identity.  Padding bytes are written as poison
      and are not recorded in the dvalue, and deserialization is lossy in two
      further ways: a field whose bytes are all poison comes back as
      [DVALUE_Poison] rather than as the original shape
      (see [all_poison_bytes]), and [memory_bytes_to_byte_value] re-canonicalises
      a byte sequence (integer, then pointer, then mixed bits), so a value may
      come back under a different [dvalue_bv] constructor than it went in.
      Pinning down "<dv' agrees with dv>" is the open part of this model.
   *)
  (* Canonicalising constructor for aggregates: an aggregate all of whose
     immediate children are poison *is* poison, per [dvalue_has_dtyp].

     The [poison_split] fast path in [memory_bytes_to_dvalue] catches the
     common case -- every byte poison -- without rebuilding the value, but it
     is not sufficient on its own.  A single non-poison byte lying in padding,
     or in the tail of an array slot, leaves [rest] non-empty while every
     field still reads back as poison; e.g. reading [{i8, i32}] from
     [[psn; X; psn; psn; psn; psn; psn; psn]] would otherwise yield
     [DVALUE_Struct false [Poison; Poison]].  Children are canonical by
     induction, so the shallow [dvalue_is_poison] test is enough here.

     Note this also sends an empty aggregate to poison, which is what the
     [forallb ... = false] premises of [DVALUE_Struct_typ] / [DVALUE_Array_typ]
     require. *)
  Definition canonicalize_agg (mk : list dvalue -> dvalue) (vs : list dvalue) : dvalue :=
    if forallb dvalue_is_poison vs then DVALUE_Base DVALUE_Poison else mk vs.

  Fixpoint memory_bytes_to_dvalue (dbs : list memory_byte) (dt : dtyp) : EOU dvalue :=
    (* [np] is the index of the first non-poison byte of the *whole* aggregate.
       A field or element lying entirely below it is poison, so it is answered
       directly rather than reconstructed. *)
    let list_memory_bytes_to_dvalue (np : N) (pad : option N) :=
      fix go (offset : N) dts dbs :=
        match dts with
        | [] =>
            (* TODO: should we check that we have the appropriate number of extra padding bytes here? *)
            (* Long term we'll have to include padding bytes in the dvalue *)
            ret []
        | (dt::dts) =>
            (* mirror of the writer: skip the field's leading padding, read its
               store-size bytes, then advance by its alloc size *)
            let padding :=
              if pad
              then pad_amount (preferred_alignment (dtyp_alignment dt)) offset
              else 0%N
            in
            let dbs' := drop padding dbs in
            let start := (offset + padding)%N in
            let ssz := store_size_dtyp dt in
            let asz := alloc_size_dtyp dt in
            let rest_bytes := drop asz dbs' in
            f <- (if N.leb (start + ssz) np
                  then ret (DVALUE_Base DVALUE_Poison)
                  else memory_bytes_to_dvalue (take ssz dbs') dt) ;;
            rest <- go (start + asz) dts rest_bytes ;;
            ret (f :: rest)
        end
    in
    (* Array/vector elements: stride is the alloc size for arrays and the store
       size for vectors; in both cases only the first [store_size_dtyp t] bytes
       of each slot carry the value. *)
    let array_elts_to_dvalue (np : N) (stride : N) (t : dtyp) :=
      let ssz := store_size_dtyp t in
      fix go (n : nat) (offset : N) (dbs : list memory_byte) : EOU (list dvalue) :=
        match n with
        | O => ret []
        | S n' =>
            e <- (if N.leb (offset + ssz) np
                  then ret (DVALUE_Base DVALUE_Poison)
                  else memory_bytes_to_dvalue (take ssz dbs) t) ;;
            rest <- go n' (offset + stride)%N (drop stride dbs) ;;
            ret (e :: rest)
        end
    in
    match dt with
    | DTYPE_Base dt =>
        (* Trim to the type's store size, mirroring the [take ssz _] the
           aggregate loops below already hand their children.  Each arm of
           [memory_bytes_to_dvalue_base] consumes its whole input, so without
           this a base read is the only part of the reader that cannot
           tolerate a longer buffer: a value written with a [tail_align] would
           have its trailing padding folded into the value and read back as
           [DVALUE_Poison].  On an exactly-sized buffer this is the identity. *)
        DVALUE_Base <$> (memory_bytes_to_dvalue_base
                           (take (store_size_dtyp (DTYPE_Base dt)) dbs) dt)

    | DTYPE_Array vector sz t =>
        (* An all-poison aggregate canonicalises to [DVALUE_Poison] rather than
           to an aggregate of poisons -- the same treatment [DTYPE_B] already
           gets in [memory_bytes_to_dvalue_base]. *)
        let '(np, rest) := poison_split dbs in
        match rest with
        | [] => ret (DVALUE_Base DVALUE_Poison)
        | _ :: _ =>
            let stride := if vector then store_size_dtyp t else alloc_size_dtyp t in
            elts <- array_elts_to_dvalue np stride t (N.to_nat sz) 0%N dbs ;;
            ret (canonicalize_agg (DVALUE_Array vector) elts)
        end

    | DTYPE_Struct packed fields =>
        let '(np, rest) := poison_split dbs in
        match rest with
        | [] => ret (DVALUE_Base DVALUE_Poison)
        | _ :: _ =>
            let pad := if packed then None else Some (max_preferred_dtyp_alignment fields) in
            (canonicalize_agg (DVALUE_Struct packed))
              <$> (list_memory_bytes_to_dvalue np pad 0%N fields dbs)
        end
    end.


End MemoryByte.
