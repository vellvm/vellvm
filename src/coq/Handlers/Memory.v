(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2018 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

(* begin hide *)
From Coq Require Import
     Morphisms ZArith List String Lia
     FSets.FMapAVL
     FSets.FSetAVL
     FSetProperties
     FMapFacts
     Structures.OrderedTypeEx
     micromega.Lia
     Psatz.

From ITree Require Import
     ITree
     Basics.Basics
     Events.Exception
     Eq.Eqit
     Events.StateFacts
     Events.State.

Import Basics.Basics.Monads.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Programming.Eqv
     Data.String.

From Vellvm Require Import
     Numeric.Coqlib
     Numeric.Integers
     Numeric.Floats
     Utils.Tactics
     Utils.Util
     Utils.Error
     Syntax.LLVMAst
     Syntax.DynamicTypes
     Semantics.DynamicValues
     Semantics.Denotation
     Semantics.MemoryAddress
     Semantics.LLVMEvents.

Require Import Ceres.Ceres.

Import EqvNotation.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

#[local] Open Scope Z_scope.
(* end hide *)


(** * Memory Model

    This file implements VIR's memory model as an handler for the [MemoryE] family of events.
    The model is inspired by CompCert's memory model, but differs in that it maintains two
    representation of the memory, a logical one and a low-level one.
    Pointers (type signature [MemoryAddress.ADDRESS]) are implemented as a pair containing
    an address and an offset.
*)

(* Specifying the currently supported dynamic types.
       This is mostly to rule out:

       - arbitrary bitwidth integers
       - half
       - x86_fp80
       - fp128
       - ppc_fp128
       - metadata
       - x86_mmx
       - opaque
 *)
Inductive is_supported : dtyp -> Prop :=
| is_supported_DTYPE_I1 : is_supported (DTYPE_I 1)
| is_supported_DTYPE_I8 : is_supported (DTYPE_I 8)
| is_supported_DTYPE_I32 : is_supported (DTYPE_I 32)
| is_supported_DTYPE_I64 : is_supported (DTYPE_I 64)
| is_supported_DTYPE_Pointer : is_supported (DTYPE_Pointer)
| is_supported_DTYPE_Void : is_supported (DTYPE_Void)
| is_supported_DTYPE_Float : is_supported (DTYPE_Float)
| is_supported_DTYPE_Double : is_supported (DTYPE_Double)
| is_supported_DTYPE_Array : forall sz τ, is_supported τ -> is_supported (DTYPE_Array sz τ)
| is_supported_DTYPE_Struct : forall fields, Forall is_supported fields -> is_supported (DTYPE_Struct fields)
.


(** ** Type of pointers
    Implementation of the notion of pointer used: an address and an offset.
 *)
Module Addr : MemoryAddress.ADDRESS with Definition addr := (Z * Z) % type.
  Definition addr := (Z * Z) % type.
  Definition null : addr := (0, 0)%Z.
  Definition t := addr.
  Lemma eq_dec : forall (a b : addr), {a = b} + {a <> b}.
  Proof.
    intros [a1 a2] [b1 b2].
    destruct (Z.eq_dec a1 b1);
          destruct (Z.eq_dec a2 b2); subst.
    - left; reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
  Qed.
End Addr.

From stdpp Require Import gmap.

#[global] Coercion is_true : bool >-> Sortclass.
(** ** Memory model
    Implementation of the memory model, i.e. a handler for [MemoryE].
    The memory itself, [memory], is a finite map (using the standard library's AVLs)
    indexed on [Z].
 *)
Module Make(LLVMEvents: LLVM_INTERACTIONS(Addr)).
  Import LLVMEvents.
  Import DV.
  Open Scope list.

  Definition addr := Addr.addr.

  (** ** Finite maps
      We use finite maps in several place of the memory model. We rely on the AVL implementation from the standard library.
      We redefine locally the operations we use and their axiomatisation as the interface exposed by the standard library
      tends to leak out the [Raw] underlying implementation, and feels overall tedious to use.
   *)
  Section Map_Operations.

    (* Polymorphic type of maps indexed by [Z] *)
    Definition IntMap := gmap Z.

    Definition empty {a} := @gmap_empty a.

    (* Extends the map with a list of pairs key/value.
     Note: additions start from the end of the list, so in case of duplicate
     keys, the binding in the front will shadow though in the back.
     *)
    Definition add_all {a} ks (m:IntMap a) :=
      foldr (fun '(x, v) acc => <[x := v]> acc) m ks.

    (* Extends the map with the bindings {(i,v_1) .. (i+n-1, v_n)} for [vs ::= v_1..v_n] *)
    Fixpoint add_all_index {a} vs (i:Z) (m:IntMap a) :=
      match vs with
      | [] => m
      | v :: tl => <[ i := v ]> (add_all_index tl (i+1) m)
      end.

    Fixpoint Zseq (start : Z) (len : nat) : list Z :=
      match len with
      | O => []
      | S x => start :: Zseq (Z.succ start) x
      end.

    Fixpoint Nseq (start : N) (len : nat) : list N :=
      match len with
      | O => []
      | S x => start :: Nseq (N.succ start) x
      end.

    (* Give back a list of values from [|i|] to [|i| + |sz| - 1] in [m].
     Uses [def] as the default value if a lookup failed.
     *)
    Definition lookup_all_index {a} (i:Z) (sz:N) (m:IntMap a) (def:a) : list a :=
      List.map (fun x =>
                  match lookup x m with
                  | None => def
                  | Some val => val
                  end) (Zseq i (N.to_nat sz)).

    (* TODO : Move the three following functions *)
    Fixpoint max_default (l:list Z) (x:Z) :=
      match l with
      | [] => x
      | h :: tl =>
        max_default tl (if h >? x then h else x)
      end.

    Definition maximumBy {A} (leq : A -> A -> bool) (def : A) (l : list A) : A :=
      fold_left (fun a b => if leq a b then b else a) l def.

    Definition maximumBy_Z_le_def :
      forall def l e,
        (e <=? def = true ->
        e <=? maximumBy Z.leb def l = true)%Z.
    Proof.
      intros def l.
      revert def.
      induction l; intros def e LE.
      - cbn; auto.
      - cbn. destruct (def <=? a)%Z eqn:Hdef.
        + apply IHl.
          eapply Zle_bool_trans; eauto.
        + apply IHl; auto.
    Qed.

    Definition maximumBy_Z_def :
      forall def l,
        (def <=? maximumBy Z.leb def l = true)%Z.
    Proof.
      intros def l.
      apply maximumBy_Z_le_def; eauto.
      apply Z.leb_refl.
    Qed.

    Definition maximumBy_Z_correct :
      forall def (l : list Z),
        forall a, In a l -> Z.leb a (maximumBy Z.leb def l) = true.
    Proof.
      intros def l.
      revert def.
      induction l as [|x xs];
        intros def a IN;
        inversion IN.
      - subst; cbn.
        apply maximumBy_Z_le_def.
        destruct (def <=? a)%Z eqn:LE.
        + apply Z.leb_refl.
        + rewrite Z.leb_gt in LE.
          apply Z.leb_le.
          lia.
      - subst; cbn; apply IHxs; auto.
    Qed.

    Definition is_some {A} (o : option A) :=
      match o with
      | Some x => true
      | None => false
      end.

  End Map_Operations.

  Section Datatype_Definition.

    (** ** Logical view of memory
      A logical block is determined by a size and a mapping from [Z] to special bytes,
      we call such a mapping a [mem_block].
      Those bytes can either be an actually 8bits byte, an address of a pointer,
      a [PtrFrag], marking bytes that are part of an address but not its first byte,
      or a special undefined byte.
      It may also correspond to a concrete block whose id is then provided.
     *)
    Inductive SByte :=
    | Byte : byte -> SByte
    | Ptr : addr -> SByte
    | PtrFrag : SByte
    | SUndef : SByte.

    #[global] Instance byte_eq_dec : EqDecision byte := Byte.eq_dec.

    #[global] Instance sbyte_eq_dec : EqDecision SByte.
    Proof.
      repeat intro. destruct x, y.
      2-5,7-10,12-15: try solve [right; intro; inversion H].
      - destruct (Byte.eq_dec i i0) eqn: Hb.
        + subst; by left.
        + right; intro; by inversion H.
      - destruct (Addr.eq_dec a a0) eqn: Hb.
        + subst; by left.
        + right; intro; by inversion H.
      - left; auto.
      - left; auto.
    Defined.

    #[global] Instance sbyte_equiv : Equiv SByte.
    Proof.
      repeat intro. exact (@sbyte_eq_dec H H0).
    Defined.

    #[global] Instance sbyte_equiv_refl : Reflexive (@equiv SByte _).
    Proof.
      repeat intro.
      destruct x; eauto.
      - repeat red.
        match goal with
        | [ |- if ?x then _ else _] => remember x as Hguard
        end. destruct Hguard; try done.
        symmetry in HeqHguard.
        match goal with
          | [ H : (if ?x then _ else _) = false |- _] => remember x as Hguard
        end; destruct Hguard; try done.
      - repeat red.
        match goal with
        | [ |- if ?x then _ else _] => remember x as Hguard
        end. destruct Hguard; try done.
        symmetry in HeqHguard.
        match goal with
          | [ H : (if ?x then _ else _) = false |- _] => remember x as Hguard
        end; destruct Hguard; try done.
    Qed.

    #[global] Instance sbyte_leibniz : @LeibnizEquiv SByte sbyte_equiv.
      repeat intro. do 2 red in H.
      repeat red in H.
      destruct x, y; eauto; cbn in H; try solve [inversion H].
      - match goal with
        | [ H : if ?x then _ else _ |- _] => remember x as Hguard
        end. destruct Hguard; try done.
        symmetry in HeqHguard.
        match goal with
          | [ H : (if ?x then _ else _) = true |- _] => remember x as Hguard
        end; destruct Hguard; try done.
      - match goal with
        | [ H : if ?x then _ else _ |- _] => remember x as Hguard
        end. destruct Hguard; try done.
        symmetry in HeqHguard.
        match goal with
          | [ H : (if ?x then _ else _) = true |- _] => remember x as Hguard
        end; destruct Hguard; try done.
    Qed.

    Definition mem_block : Set := gmap Z SByte.

    Inductive logical_block : Set :=
    | LBlock (size : N) (bytes : gmap Z SByte) (concrete_id : option Z) : logical_block.

    (** ** Memory
      A concrete memory, resp. logical memory, maps addresses to concrete blocks, resp. logical blocks.
      A memory is a pair of both views of the memory.
     *)
    Definition logical_memory := IntMap logical_block.
    Definition used_locs := gset Z.
    Definition memory         := (logical_memory * used_locs)%type.

    (** ** Stack frames
      A frame contains the list of block ids that need to be freed when popped,
      i.e. when the function returns.
      A [frame_stack] is a list of such frames.
     *)
    Definition mem_frame := list Z.
    Inductive frame_stack : Type := | Singleton (f : mem_frame) | Snoc (s : frame_stack) (f : mem_frame).
    (* Definition frame_stack := list mem_frame. *)

    (** ** Memory stack
      The full notion of state manipulated by the monad is a pair of a [memory] and a [mem_stack].
     *)
    Definition memory_stack : Type := memory * frame_stack.

  End Datatype_Definition.

  Section Serialization.

   (** ** Serialization
       Conversion back and forth between values and their byte representation
   *)

    (* Converts an integer [x] to its byte representation over [n] bytes.
     The representation is little endian. In particular, if [n] is too small,
     only the least significant bytes are returned.
     *)
    Fixpoint bytes_of_int (n: nat) (x: Z) {struct n}: list byte :=
      match n with
      | O => nil
      | S m => Byte.repr x :: bytes_of_int m (x / 256)
      end.

    Definition sbytes_of_int (count:nat) (z:Z) : list SByte :=
      List.map Byte (bytes_of_int count z).

    (* Converts a list of bytes to an integer.
     The byte encoding is assumed to be little endian.
     *)
    Fixpoint int_of_bytes (l: list byte): Z :=
      match l with
      | nil => 0
      | b :: l' => Byte.unsigned b + int_of_bytes l' * 256
      end.

    (* Partial function casting a [Sbyte] into a simple [byte] *)
    Definition Sbyte_to_byte (sb:SByte) : option byte :=
      match sb with
      | Byte b => ret b
      | Ptr _ | PtrFrag | SUndef => None
      end.

    Definition Sbyte_to_byte_list (sb:SByte) : list byte :=
      match sb with
      | Byte b => [b]
      | Ptr _ | PtrFrag | SUndef => []
      end.

    Definition Sbyte_defined (sb:SByte) : bool :=
      match sb with
      | SUndef => false
      | _ => true
      end.

    Definition sbyte_list_to_byte_list (bytes:list SByte) : list byte :=
      List.flat_map Sbyte_to_byte_list bytes.

    Definition sbyte_list_to_Z (bytes:list SByte) : Z :=
      int_of_bytes (sbyte_list_to_byte_list bytes).

    (** ** Serialization of [dvalue]
      Serializes a dvalue into its SByte-sensitive form.
      Integer are stored over 8 bytes.
      Pointers as well: the address is stored in the first, [PtrFrag] flags mark the seven others.
     *)
    Fixpoint serialize_dvalue (dval:dvalue) : list SByte :=
      match dval with
      | DVALUE_Addr addr => (Ptr addr) :: (repeat PtrFrag 7)
      | DVALUE_I1 i => sbytes_of_int 8 (unsigned i)
      | DVALUE_I8 i => sbytes_of_int 8 (unsigned i)
      | DVALUE_I32 i => sbytes_of_int 8 (unsigned i)
      | DVALUE_I64 i => sbytes_of_int 8 (unsigned i)
      | DVALUE_Float f => sbytes_of_int 4 (unsigned (Float32.to_bits f))
      | DVALUE_Double d => sbytes_of_int 8 (unsigned (Float.to_bits d))
      | DVALUE_Struct fields
      | DVALUE_Array fields =>
        (* note the _right_ fold is necessary for byte ordering. *)
        fold_right (fun 'dv acc => ((serialize_dvalue dv) ++ acc) % list) [] fields
      | _ => [] 
      end.

    (** ** Well defined block
      A list of [sbytes] is considered undefined if any of its bytes is undefined.
      This predicate checks that they are all well-defined.
     *)
    Definition all_not_sundef (bytes : list SByte) : bool :=
      forallb Sbyte_defined bytes.

    (** ** Size of a dynamic type
      Computes the byte size of a [dtyp]. *)
    Fixpoint sizeof_dtyp (ty:dtyp) : N :=
      match ty with
      | DTYPE_I 1          => 8 (* All integers are padded to 8 bytes. *)
      | DTYPE_I 8          => 8 (* All integers are padded to 8 bytes. *)
      | DTYPE_I 32         => 8 (* All integers are padded to 8 bytes. *)
      | DTYPE_I 64         => 8 (* All integers are padded to 8 bytes. *)
      | DTYPE_I _          => 0 (* Unsupported integers *)
      | DTYPE_Pointer      => 8
      | DTYPE_Struct l     => fold_left (fun acc x => (acc + sizeof_dtyp x)%N) l 0%N
      | DTYPE_Array sz ty' => sz * sizeof_dtyp ty'
      | DTYPE_Float        => 4
      | DTYPE_Double       => 8
      | DTYPE_Half         => 4
      | DTYPE_X86_fp80     => 4 (* TODO: Unsupported, currently modeled by Float32 *)
      | DTYPE_Fp128        => 4 (* TODO: Unsupported, currently modeled by Float32 *)
      | DTYPE_Ppc_fp128    => 4 (* TODO: Unsupported, currently modeled by Float32 *)
      | DTYPE_Metadata     => 0
      | DTYPE_X86_mmx      => 0 (* TODO: Unsupported *)
      | DTYPE_Opaque       => 0 (* TODO: Unsupported *)
      | _                  => 0 (* TODO: add support for more types as necessary *)
      end.

    (** ** Deserialization of a list of sbytes
      Deserialize a list [bytes] of SBytes into a uvalue of type [t],
      assuming that none of the bytes are undef.
      Truncate integer as dictated by [t].
     *)
    Fixpoint deserialize_sbytes_defined (bytes:list SByte) (t:dtyp) {struct t} : uvalue :=
      match t with
      | DTYPE_I sz =>
        let des_int := sbyte_list_to_Z bytes in
        (match sz with
        | 1  => UVALUE_I1 (repr des_int)
        | 8  => UVALUE_I8 (repr des_int)
        | 32 => UVALUE_I32 (repr des_int)
        | 64 => UVALUE_I64 (repr des_int)
        | _  => UVALUE_None (* invalid size. *)
        end)%N
      | DTYPE_Float => UVALUE_Float (Float32.of_bits (repr (sbyte_list_to_Z bytes)))
      | DTYPE_Double => UVALUE_Double (Float.of_bits (repr (sbyte_list_to_Z bytes)))

      | DTYPE_Pointer =>
        match bytes with
        | Ptr addr :: tl => UVALUE_Addr addr
        | _ => UVALUE_None (* invalid pointer. *)
        end
      | DTYPE_Array sz t' =>
        let fix array_parse count byte_sz bytes :=
            match count with
            | O => []
            | S n => (deserialize_sbytes_defined (firstn byte_sz bytes) t')
                      :: array_parse n byte_sz (skipn byte_sz bytes)
            end in
        UVALUE_Array (array_parse (N.to_nat sz) (N.to_nat (sizeof_dtyp t')) bytes)
      | DTYPE_Struct fields =>
        let fix struct_parse typ_list bytes :=
            match typ_list with
            | [] => []
            | t :: tl =>
              let size_ty := N.to_nat (sizeof_dtyp t) in
              (deserialize_sbytes_defined (firstn size_ty bytes) t)
                :: struct_parse tl (skipn size_ty bytes)
            end in
        UVALUE_Struct (struct_parse fields bytes)
      | _ => UVALUE_None (* TODO add more as serialization support increases *)
      end.

    (* Returns undef if _any_ sbyte is undef.
     Note that this means for instance that the result of the deserialization of an I1
     depends on all the bytes provided, not just the first one!
     *)
    Definition deserialize_sbytes (bytes : list SByte) (t : dtyp) : uvalue :=
      if all_not_sundef bytes
      then deserialize_sbytes_defined bytes t
      else UVALUE_Undef t.

    (** ** Reading values in memory
      Given an offset in [mem_block], we decode a [uvalue] at [dtyp] [t] by looking up the
      appropriate number of [SByte] and deserializing them.
     *)

    Definition read_in_mem_block (bk : mem_block) (offset : Z) (t : dtyp) : uvalue :=
      deserialize_sbytes (lookup_all_index offset (sizeof_dtyp t) bk SUndef) t.

    (** ** Writing values to memory
      Serialize [v] into [SByte]s, and store them in the [mem_block] [bk] starting at [offset].
     *)
    Definition write_to_mem_block (bk : mem_block) (offset : Z) (v : dvalue) : mem_block
      := add_all_index (serialize_dvalue v) offset bk.

  End Serialization.

  Section GEP.

    (** ** Get Element Pointer
      Retrieve the address of a subelement of an indexable (i.e. aggregate) [dtyp] [t] (i.e. vector, array, struct, packed struct).
      The [off]set parameter contains the current entry address of the aggregate structure being analyzed, while the list
      of [dvalue] [vs] describes the indexes of interest used to access the subelement.
      The interpretation of these values slightly depends on the type considered.
      But essentially, for instance in a vector or an array, the head value should be an [i32] describing the index of interest.
      The offset is therefore incremented by this index times the size of the type of elements stored. Finally, a recursive call
      at this new offset allows for deeper unbundling of a nested structure.
     *)
    Fixpoint handle_gep_h (t:dtyp) (off:Z) (vs:list dvalue): err Z :=
      match vs with
      | v :: vs' =>
        match v with
        | DVALUE_I32 i =>
          let k := unsigned i in
          let n := BinIntDef.Z.to_nat k in
          match t with
          | DTYPE_Array _ ta =>
            handle_gep_h ta (off + k * (Z.of_N (sizeof_dtyp ta))) vs'
          | DTYPE_Struct ts =>
            (* Handle these differently in future *)
            let offset := fold_left (fun acc t => (acc + (Z.of_N (sizeof_dtyp t))))%Z
                                    (firstn n ts) 0%Z in
            match nth_error ts n with
            | None => failwith "overflow"
            | Some t' =>
              handle_gep_h t' (off + offset) vs'
            end
          | _ => failwith ("non-i32-indexable type")
          end
        | DVALUE_I8 i =>
          let k := unsigned i in
          let n := BinIntDef.Z.to_nat k in
          match t with
          | DTYPE_Array _ ta =>
            handle_gep_h ta (off + k * (Z.of_N (sizeof_dtyp ta))) vs'
          | _ => failwith ("non-i8-indexable type")
          end
        | DVALUE_I64 i =>
          let k := unsigned i in
          let n := BinIntDef.Z.to_nat k in
          match t with
          | DTYPE_Array _ ta =>
            handle_gep_h ta (off + k * (Z.of_N (sizeof_dtyp ta))) vs'
          | _ => failwith ("non-i64-indexable type")
          end
        | _ => failwith "non-I32 index"
        end
      | [] => ret off
      end.

    (* At the toplevel, GEP takes a [dvalue] as an argument that must contain a pointer, but no other pointer can be recursively followed.
     The pointer set the block into which we look, and the initial offset. The first index value add to the initial offset passed to [handle_gep_h] for the actual access to structured data.
     *)
    Definition handle_gep_addr (t:dtyp) (a:addr) (vs:list dvalue) : err addr :=
      let '(b, o) := a in
      match vs with
      | DVALUE_I32 i :: vs' => (* TODO: Handle non i32 / i64 indices *)
        bind (handle_gep_h t (o + Z.of_N (sizeof_dtyp t) * (unsigned i)) vs')
        (fun off => ret (b, off))
      | DVALUE_I64 i :: vs' =>
        bind (handle_gep_h t (o + Z.of_N (sizeof_dtyp t) * (unsigned i)) vs')
        (fun off => ret (b, off))
      | _ => failwith "non-I32 index"
      end.

    Definition handle_gep (t:dtyp) (dv:dvalue) (vs:list dvalue) : err dvalue :=
      match dv with
      | DVALUE_Addr a => Functor.fmap DVALUE_Addr (handle_gep_addr t a vs)
      | _ => failwith "non-address"
      end.

  End GEP.

  Section Logical_Operations.

    Definition logical_empty : logical_memory := empty.

    (* Returns a fresh key for use in memory map *)
    Definition logical_next_key (m : memory) : Z
      := let keys := elements (dom m.1 ∪ m.2) in
         1 + maximumBy Z.leb (-1)%Z keys.

    (** ** Initialization of blocks
      Constructs an initial [mem_block] of undefined [SByte]s, indexed from 0 to n.
     *)
    Fixpoint init_block_undef (n:nat) (m:mem_block) : mem_block :=
      match n with
      | O => <[ 0%Z := SUndef ]> m
      | S n' => <[ Z.of_nat n := SUndef ]> (init_block_undef n' m)
      end.

    (* Constructs an initial [mem_block] containing [n] undefined [SByte]s, indexed from [0] to [n - 1].
     If [n] is negative, it is treated as [0].
     *)
    Definition init_block (n:N) : mem_block :=
      match n with
      | 0%N => empty
      | N.pos n' => init_block_undef (BinPosDef.Pos.to_nat (n' - 1)) empty
      end.

    (* Constructs an initial [mem_block] appropriately sized for a given type [ty]. *)
    Definition make_empty_mem_block (ty:dtyp) : mem_block :=
      init_block (sizeof_dtyp ty).

    (* Constructs an initial [logical_block] appropriately sized for a given type [ty]. *)
    Definition make_empty_logical_block (ty:dtyp) : logical_block :=
      let block := make_empty_mem_block ty in
      LBlock (sizeof_dtyp ty) block None.

    (** ** Array element lookup
      A [mem_block] can be seen as storing an array of elements of [dtyp] [t], from which we retrieve
      the [i]th [uvalue].
      The [size] argument has no effect, but we need to provide one to the array type.
     *)
    Definition get_array_cell_mem_block (bk : mem_block) (bk_offset : Z) (i : nat) (size : N) (t : dtyp) : err uvalue :=
      bind (handle_gep_h (DTYPE_Array size t)
                             bk_offset
                             [DVALUE_I64 (DynamicValues.Int64.repr (Z.of_nat i))])
      (fun offset => inr (read_in_mem_block bk offset t)).

    (** ** Array element writing
      Treat a [mem_block] as though it is an array storing elements of
      type [t], and write the value [v] to index [i] in this array.

      - [t] should be the type of [v].
      - [size] does nothing, but we need to provide one for the array type.
    *)
    Definition write_array_cell_mem_block (bk : mem_block) (bk_offset : Z) (i : nat) (size : N) (t : dtyp) (v : dvalue) : err mem_block :=
      bind (handle_gep_h (DTYPE_Array size t)
                             bk_offset
                             [DVALUE_I64 (DynamicValues.Int64.repr (Z.of_nat i))])
      (fun offset => inr (write_to_mem_block bk offset v)).

    (** ** Array lookups -- mem_block
      Retrieve the values stored at position [from] to position [from + len - 1] in an array stored in a [mem_block].
     *)
    Definition get_array_mem_block (bk : mem_block) (bk_offset : Z) (from len : nat) (size : N) (t : dtyp) : err (list uvalue) :=
      map_monad (fun i => get_array_cell_mem_block bk bk_offset i size t) (seq from len).


    (* (* TODO: Move this? *) *)
    (* Fixpoint foldM {a b} {M} `{Monad M} (f : b -> a -> M b) (acc : b) (l : list a) : M b *)
    (*   := match l with *)
    (*      | [] => ret acc *)
    (*      | (x :: xs) => *)
    (*        bind (f acc x) (fun b => foldM f b xs) *)
    (*      end. *)

    (** ** Array writes -- mem_block
      Write all of the values in [vs] to an array stored in a [mem_block], starting from index [from].

      - [t] should be the type of each [v] in [vs]
     *)
    Fixpoint write_array_mem_block' (bk : mem_block) (bk_offset : Z) (i : nat) (size : N) (t : dtyp) (vs : list dvalue) : err mem_block :=
      match vs with
      | []       => ret bk
      | (v :: vs) =>
        bind (write_array_cell_mem_block bk bk_offset i size t v)
        (fun bk' => write_array_mem_block' bk' bk_offset (S i) size t vs)
      end.

    Definition write_array_mem_block (bk : mem_block) (bk_offset : Z) (from : nat) (t : dtyp) (vs : list dvalue) : err mem_block :=
      let size := (N.of_nat (length vs)) in
      write_array_mem_block' bk bk_offset from size t vs.

  End Logical_Operations.

  Section Memory_Operations.

      (** ** Smart lookups *)
      Definition get_logical_block_mem (b : Z) (m : memory) : option logical_block :=
        lookup b m.1.

      (* Get the next key in the logical map *)
      Definition next_logical_key_mem (m : memory) : Z :=
        logical_next_key m.

      Definition add_logical_block_mem (id : Z) (b : logical_block) (m : memory) : memory :=
        (<[ id := b ]> m.1, {[ id ]} ∪ m.2).

    (** Check if the block for an address is allocated.

        Note: This does not check that the address is in range of the
        block. *)
    (* TODO: should this check if everything is in range...? *)
    Definition allocated (a : addr) (m : memory_stack) : Prop :=
      (fst a) ∈ dom (fst m.1).

    (** Do two memory regions overlap each other?

        - *a1* and *a2* are addresses to the start of each region.
        - *sz1* and *sz2* are the sizes of the two regions.

        Proposition should hold whenever the two regions overlap each
        other. *)
    Definition overlaps (a1 : addr) (sz1 : Z) (a2 : addr) (sz2 : Z) : Prop :=
      (let a1_start := snd a1 in
      let a1_end   := snd a1 + sz1 in
      let a2_start := snd a2 in
      let a2_end   := snd a2 + sz2 in
      fst a1 = fst a2 /\ a1_start <= (a2_end - 1) /\ a2_start <= (a1_end - 1))%Z.

    (** Checks if two regions of memory overlap each other. The types
        *τ1* and *τ2* are used to determine the size of the two memory
        regions.
     *)
    Definition overlaps_dtyp (a1 : addr) (τ1 : dtyp) (a2 : addr) (τ2 : dtyp)
      : Prop :=
      overlaps a1 (Z.of_N (sizeof_dtyp τ1)) a2 (Z.of_N (sizeof_dtyp τ2)).

    (** Make sure that two regions of memory do not overlap *)
    Definition no_overlap (a1 : addr) (sz1 : Z) (a2 : addr) (sz2 : Z) : Prop :=
      (let a1_start := snd a1 in
      let a1_end   := snd a1 + sz1 in
      let a2_start := snd a2 in
      let a2_end   := snd a2 + sz2 in
      fst a1 <> fst a2 \/ a1_start > (a2_end - 1) \/ a2_start > (a1_end - 1))%Z.

    (** Same as *no_overlap*, but using *dtyp*s *τ1* and *τ2* to
        determine the size of the regions. *)
    Definition no_overlap_dtyp (a1 : addr) (τ1 : dtyp) (a2 : addr) (τ2 : dtyp)
      : Prop :=
      no_overlap a1 (Z.of_N (sizeof_dtyp τ1)) a2 (Z.of_N (sizeof_dtyp τ2)).

    (** Boolean version of *no_overlap* *)
    Definition no_overlap_b (a1 : addr) (sz1 : Z) (a2 : addr) (sz2 : Z) : bool :=
      (let a1_start := snd a1 in
      let a1_end   := snd a1 + sz1 in
      let a2_start := snd a2 in
      let a2_end   := snd a2 + sz2 in
      (fst a1 /~=? fst a2) || (a1_start >? (a2_end - 1)) || (a2_start >? (a1_end - 1)))%Z.

      (* LLVM 5.0 memcpy
         According to the documentation: http://releases.llvm.org/5.0.0/docs/LangRef.html#llvm-memcpy-intrinsic
         this operation can never fail?  It doesn't return any status code...
       *)

      (** ** MemCopy
          Implementation of the [memcpy] intrinsics.
       *)
      Definition handle_memcpy (args : list dvalue) (m:memory) : err memory :=
        match args with
        | DVALUE_Addr (dst_b, dst_o) ::
                      DVALUE_Addr (src_b, src_o) ::
                      DVALUE_I32 len ::
                      DVALUE_I32 align :: (* alignment ignored *)
                      DVALUE_I1 volatile :: [] (* volatile ignored *)  =>

          let mem_block_size := unsigned len in
          (* From LLVM Docs : The 'llvm.memcpy.*' intrinsics copy a block of
             memory from the source location to the destination location,
             which are not allowed to overlap. *)
          if (no_overlap_b (dst_b, dst_o) mem_block_size
                                 (src_b, src_o) mem_block_size) then
            (* No guarantee that src_block has a certain size. *)
            bind (trywith "memcpy src block not found"
                                (get_logical_block_mem src_b m))
            (fun src_block =>
               bind (trywith "memcpy dst block not found"
                                (get_logical_block_mem dst_b m))
              (fun dst_block =>
              let src_bytes
                  := match src_block with
                    | LBlock size bytes concrete_id => bytes
                    end in
              let '(dst_sz, dst_bytes, dst_cid)
                  := match dst_block with
                    | LBlock size bytes concrete_id => (size, bytes, concrete_id)
                    end in

            (* IY: What happens if [src_block_size < mem_block_size]?
               Since we have logical blocks, there isn't a way to get around
               this, and SUndef is invoked. Is this desired behavior? *)
            let sdata := lookup_all_index src_o (Z.to_N (unsigned len)) src_bytes SUndef in
            let dst_bytes' := add_all_index sdata dst_o dst_bytes in
            let dst_block' := LBlock dst_sz dst_bytes' dst_cid in
            let m' := add_logical_block_mem dst_b dst_block' m in
            (ret m' : err memory)))
          (* IY: For now, we're returning a "failwith". Maybe it's more ideal
             to return an "UNDEF" here? *)
          else failwith "memcpy has overlapping src and dst memory location"
        | _ => failwith "memcpy got incorrect arguments"
        end.

  End Memory_Operations.

  Section Frame_Stack_Operations.

    (* The initial frame stack is not an empty stack, but a singleton stack containing an empty frame *)
    Definition frame_empty : frame_stack := Singleton [].

    Definition free_frame_memory (f : mem_frame) (m : memory) : memory :=
      (fold_left (fun m key => delete key m) f m.1, m.2).

    Definition equivs : frame_stack -> frame_stack -> Prop := Logic.eq.

    #[global, refine] Instance equivs_Equiv : Equivalence equivs := _. Defined.

  End Frame_Stack_Operations.

  Section Memory_Stack_Operations.

   (** ** Top-level interface
       Ideally, outside of this module, the [memory_stack] datatype should be abstract and all interactions should go
       through this interface.
    *)

    (** ** The empty memory
        Both the concrete and logical views of the memory are empty maps, i.e. nothing is allocated.
        It is a matter of convention, by we consider the empty memory to contain a single empty frame
        in its stack, rather than an empty stack.
     *)
    Definition empty_memory_stack : memory_stack := ((logical_empty, ∅), frame_empty).

    (** ** Smart lookups *)

    Definition get_logical_block (m : memory_stack) (key : Z) : option logical_block :=
      get_logical_block_mem key (fst m).

    (** ** Fresh key getters *)

    (* Get the next key in the logical map *)
    Definition next_logical_key (m : memory_stack) : Z :=
      next_logical_key_mem (fst m).

    (** ** Extending the memory  *)
    Definition add_logical_block (id : Z) (b : logical_block) (m : memory_stack) : memory_stack :=
      let '(m,s) := m in (add_logical_block_mem id b m,s).

    (** ** Array lookups -- memory_stack
      Retrieve the values stored at position [from] to position [from + len - 1] in an array stored at address [a] in memory.
     *)
    Definition get_array (m: memory_stack) (a : addr) (from len: nat) (size : N) (t : dtyp) : err (list uvalue) :=
      let '(b, o) := a in
      match get_logical_block m b with
      | Some (LBlock _ bk _) =>
        get_array_mem_block bk o from len size t
      | None => failwith "Memory function [get_array] called at a non-allocated address"
      end.

    Definition get_array_cell (m : memory_stack) (a : addr) (i : nat) (τ : dtyp) : err uvalue :=
        let '(b, o) := a in
        match get_logical_block m b with
        | Some (LBlock _ bk _) =>
          get_array_cell_mem_block bk o i 0 τ
        | None => failwith "Memory function [get_array_cell] called at a non-allocated address"
        end.

    (** ** Array writes -- memory_stack
     *)
    Definition write_array (m : memory_stack) (a : addr) (from : nat) (τ : dtyp) (vs : list dvalue) : err memory_stack :=
      let '(b, o) := a in
      match get_logical_block m b with
      | Some (LBlock sz bk cid) =>
        bind (write_array_mem_block bk o from τ vs)
        (fun bk' => let block' := LBlock sz bk' cid in
        ret (add_logical_block b block' m))
      | None => failwith "Memory function [write_array] called at a non-allocated address"
      end.

    Definition write_array_cell (m : memory_stack) (a : addr) (i : nat) (τ : dtyp) (v : dvalue) : err memory_stack :=
      let '(b, o) := a in
      match get_logical_block m b with
      | Some (LBlock sz bk cid) =>
        bind (write_array_cell_mem_block bk o i 0 τ v)
        (fun bk' =>
          let block' := LBlock sz bk' cid in
          ret (add_logical_block b block' m))
      | None => failwith "Memory function [write_array_cell] called at a non-allocated address"
      end.

    Definition free_frame (m : memory_stack) : err memory_stack :=
      let '(m,sf) := m in
      match sf with
      | Snoc sf f => inr (free_frame_memory f m,sf)
      | _ => failwith "Ill-form frame-stack: attempting to free when only one frame is in scope"
      end.

    Definition push_fresh_frame (m : memory_stack) : memory_stack :=
      let '(m,s) := m in (m, Snoc s []).

    Definition add_to_frame (m : memory_stack) (k : Z) : memory_stack :=
      let '(m,s) := m in
      match s with
      | Singleton f => (m, Singleton (k :: f))
      | Snoc s f => (m, Snoc s (k :: f))
      end.

    Definition allocate (m : memory_stack) (t : dtyp) : err (memory_stack * addr) :=
      (match t with
      | DTYPE_Void => failwith (F := err) "Allocation of type void"
      | _ =>
        let new_block := make_empty_logical_block t in
        let key       := next_logical_key m in
        let m         := add_logical_block key new_block m in
        ret (m := err) (add_to_frame m key, (key,0))
      end)%Z.

    (* TODO: very similar to overlaps *)
    Definition dtyp_fits (m : memory_stack) (a : addr) (τ : dtyp) :=
      exists sz bytes cid,
        get_logical_block m (fst a) = Some (LBlock sz bytes cid) /\
        (snd a + (Z.of_N (sizeof_dtyp τ)) <= Z.of_N sz)%Z.

    Definition read (m : memory_stack) (ptr : addr) (t : dtyp) : err uvalue :=
      match get_logical_block m (fst ptr) with
      | Some (LBlock _ block _) =>
        ret (read_in_mem_block block (snd ptr) t)
      | None => failwith "Attempting to read a non-allocated address"
      end.

    Definition write (m : memory_stack) (ptr : addr) (v : dvalue) : err memory_stack :=
      match get_logical_block m (fst ptr) with
      | Some (LBlock sz bytes cid) =>
        let '(b,off) := ptr in
        let bytes' := add_all_index (serialize_dvalue v) off bytes in
        let block' := LBlock sz bytes' cid in
        ret (add_logical_block b block' m)
      | None => failwith "Attempting to write to a non-allocated address"
      end.

    (* Test whether a given address belong to the current main frame,
       and hence if it will be collected when the current function returns
     *)
    Definition in_frame (a : addr) (m : memory_stack) : Prop :=
      let '(_,s) := m in
      match s with
      | Singleton f | Snoc _ f => In (fst a) f
      end.

    Record ext_memory (m1 : memory_stack) (a : addr) (τ : dtyp) (v : uvalue) (m2 : memory_stack) : Prop :=
      {
      (* TODO: might want to extend this so if the size is 0 I know
               what the value of read is... *)
      new_lu  : sizeof_dtyp τ <> 0%N -> read m2 a τ = inr v;
      old_lu  : forall a' τ', allocated a' m1 ->
                         no_overlap_dtyp a τ a' τ' ->
                         read m2 a' τ' = read m1 a' τ'
      }.

    Definition same_reads (m1 m2 : memory_stack) : Prop := forall a τ, read m1 a τ = read m2 a τ.

    Record allocate_spec (m1 : memory_stack) (τ : dtyp) (m2 : memory_stack) (a : addr) : Prop :=
      {
      was_fresh : ~ allocated a m1;
      is_allocated : ext_memory m1 a τ (UVALUE_Undef τ) m2
      }.

    Record write_spec (m1 : memory_stack) (a : addr) (v : dvalue) (m2 : memory_stack) : Prop :=
      {
      was_allocated : allocated a m1;
      is_written    : forall τ, is_supported τ ->
                           dvalue_has_dtyp v τ ->
                           ext_memory m1 a τ (dvalue_to_uvalue v) m2
      }.

    Record read_spec (m : memory_stack) (a : addr) (τ : dtyp) (v : uvalue) : Prop :=
      {
      is_read : read m a τ = inr v
      }.

  End Memory_Stack_Operations.

  (** ** Memory Handler
      Implementation of the memory model per se as a memory handler to the [MemoryE] interface.
   *)
  Definition handle_memory {E} `{FailureE -< E} `{UBE -< E}: MemoryE ~> stateT memory_stack (itree E) :=
    fun _ e m =>
      match e with
      | MemPush =>
        ret (push_fresh_frame m, tt)

      | MemPop =>
        bind ( lift_pure_err (free_frame m))
        (fun m' => ret (m',tt))

      | Alloca t =>
        bind (lift_pure_err (allocate m t))
        (fun '(m',a) => ret (m', DVALUE_Addr a))

      | Load t dv =>
        match dv with
        | DVALUE_Addr ptr =>
          match read m ptr t with
          | inr v => ret (m, v)
          | inl s => raiseUB s
          end
        | _ => raise "Attempting to load from a non-address dvalue"
        end

      | Store dv v =>
        match dv with
        | DVALUE_Addr ptr =>
          bind (lift_pure_err (write m ptr v))
          (fun 'm' => ret (m', tt))
        | _ => raise ("Attempting to store to a non-address dvalue: " ++ (to_string dv))
        end

      | GEP t dv vs =>
        bind (lift_pure_err (handle_gep t dv vs))
        (fun dv' => ret (m, dv'))

      | _            => raise "Unsupported"
      end.

  Definition handle_intrinsic {E} `{FailureE -< E}: IntrinsicE ~> stateT memory_stack (itree E) :=
    fun _ e '(m, s) =>
      match e with
      | Intrinsic t name args =>
        (* Pick all arguments, they should all be unique. *)
        (* if string_dec name "llvm.memcpy.p0i8.p0i8.i32" then  (* FIXME: use reldec typeclass? *) *)
        (*   match handle_memcpy args m with *)
        (*   | inl err => raise err *)
        (*   | inr m' => ret ((m', s), DVALUE_None) *)
        (*   end *)
        (* else *)
          raise ("Unknown intrinsic: " ++ name)
      end.

  Section PARAMS.
    Variable (E F G : Type -> Type).
    Context `{FailureE -< F} `{UBE -< F}.
    Notation Effin := (E +' IntrinsicE +' MemoryE +' F).
    Notation Effout := (E +' F).

    Definition E_trigger {M} : forall R, E R -> (stateT M (itree Effout) R) :=
      fun R e m => bind (trigger e) (fun r => ret (m, r)).

    Definition F_trigger {M} : forall R, F R -> (stateT M (itree Effout) R) :=
      fun R e m => bind (trigger e) (fun r => ret (m, r)).

    Definition interp_memory_h := case_ E_trigger (case_ handle_intrinsic  (case_ handle_memory  F_trigger)).
    Definition interp_memory :
      itree Effin ~> stateT memory_stack (itree Effout) :=
      interp_state interp_memory_h.

  End PARAMS.

End Make.
