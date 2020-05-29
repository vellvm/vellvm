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
     Morphisms ZArith List String Omega
     FSets.FMapAVL
     Structures.OrderedTypeEx
     ZMicromega.

From ITree Require Import
     ITree
     Basics.Basics
     Events.Exception
     Eq.Eq
     Events.StateFacts
     Events.State.

Import Basics.Basics.Monads.

From ExtLib Require Import
     Structures.Monads
     Programming.Eqv
     Data.String.

From Vellvm Require Import
     Tactics
     LLVMAst
     Util
     DynamicTypes
     Denotation
     MemoryAddress
     LLVMEvents
     Error
     Coqlib
     Numeric.Integers
     Numeric.Floats.

Require Import Ceres.Ceres.

Import MonadNotation.
Import EqvNotation.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.
(* end hide *)

(** * Memory Model

    This file implements VIR's memory model as an handler for the [MemoryE] family of events.
    The model is inspired by CompCert's memory model, but differs in that it maintains two
    representation of the memory, a logical one and a low-level one.
    Pointers (type signature [MemoryAddress.ADDRESS]) are implemented as a pair containing
    an address and an offset.
*)

(** ** Type of pointers
    Implementation of the notion of pointer used: an address and an offset.
 *)
Module Addr : MemoryAddress.ADDRESS with Definition addr := (Z * Z) % type.
  Definition addr := (Z * Z) % type.
  Definition null := (0, 0).
  Definition t := addr.
  Lemma eq_dec : forall (a b : addr), {a = b} + {a <> b}.
  Proof.
    intros [a1 a2] [b1 b2].
    destruct (a1 ~=? b1);
      destruct (a2 ~=? b2); unfold eqv in *; unfold AstLib.eqv_int in *; subst.
    - left; reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
  Qed.
End Addr.

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

  Module IM := FMapAVL.Make(Coq.Structures.OrderedTypeEx.Z_as_OT).
  (* Polymorphic type of maps indexed by [Z] *)
  Definition IntMap := IM.t.

  Definition add {a} k (v:a) := IM.add k v.
  Definition delete {a} k (m:IntMap a) := IM.remove k m.
  Definition member {a} k (m:IntMap a) := IM.mem k m.
  Definition lookup {a} k (m:IntMap a) := IM.find k m.
  Definition empty {a} := @IM.empty a.
  Definition Equal {a} : IntMap a -> IntMap a -> Prop :=
    fun m m' => forall k, lookup k m = lookup k m'.
  Definition Equiv {a} (R : a -> a -> Prop) : IntMap a -> IntMap a -> Prop :=
    fun m m' =>
      (forall k, member k m <-> member k m') /\
      (forall k e e', lookup k m = Some e -> lookup k m' = Some e' -> R e e').
  
  Global Instance Equal_Equiv {a}: Equivalence (@Equal a).
  Proof.
    split.
    - repeat intro; reflexivity.
    - repeat intro.
      symmetry; apply H.
    - intros ? ? ? EQ1 EQ2 ?.
      etransitivity; eauto.
  Qed.

  Lemma add_add : forall {a} off b1 b2 (m : IM.t a),
      Equal (add off b2 (add off b1 m)) (add off b2 m).
  Proof.
    intros; intro key; cbn.
    rewrite IM.Raw.Proofs.add_find; [| apply IM.Raw.Proofs.add_bst, IM.is_bst].
    rewrite IM.Raw.Proofs.add_find; [| apply  IM.is_bst].
    rewrite IM.Raw.Proofs.add_find; [| apply  IM.is_bst].
    flatten_goal; auto.
  Qed.

  Lemma member_add_eq {a}: forall k v (m: IM.t a),
      member k (add k v m).
  Proof.
    intros.
    cbn.
    apply IM.Raw.Proofs.mem_1.
    apply IM.Raw.Proofs.add_bst, IM.is_bst.
    rewrite IM.Raw.Proofs.add_in; auto.
  Qed.

  Lemma member_add_ineq {a}: forall k k' v (m: IM.t a),
      k <> k' ->
      member k (add k' v m) <-> member k m.
  Proof.
    intros.
    cbn. split.
    - intros IN; apply IM.Raw.Proofs.mem_2 in IN.
      rewrite IM.Raw.Proofs.add_in in IN.
      destruct IN as [-> | IN]; [contradiction H; auto | ].
      apply IM.Raw.Proofs.mem_1; [apply IM.is_bst | auto]. 
    - intros IN.
      apply IM.Raw.Proofs.mem_1.
      apply IM.Raw.Proofs.add_bst, IM.is_bst.
      rewrite IM.Raw.Proofs.add_in; right; auto.
      apply IM.Raw.Proofs.mem_2 in IN; auto. 
  Qed.

  Lemma lookup_add_eq : forall {a} k x (m : IM.t a),
      lookup k (add k x m) = Some x.
  Proof.
    intros.
    unfold lookup, add.
    apply IM.find_1, IM.add_1; auto.
  Qed.

  Lemma MapsTo_inj : forall {a} k v v' (m : IM.t a),
      IM.MapsTo k v m ->
      IM.MapsTo k v' m ->
      v = v'.
  Proof.
    intros.
    apply IM.find_1 in H; apply IM.find_1 in H0.
    rewrite H0 in H; inv H. 
    reflexivity.
  Qed.

  Lemma lookup_add_ineq : forall {a} k k' x (m : IM.t a),
      k <> k' ->
      lookup k (add k' x m) = lookup k m.
  Proof.
    intros.
    unfold lookup, add.
    match goal with
      |- ?x = ?y => destruct x eqn:EQx,y eqn:EQy;
                    try apply IM.find_2,IM.add_3 in EQx;
                    try apply IM.find_2 in EQy
    end; auto.
    eapply MapsTo_inj in EQx; eauto; subst; eauto.
    apply IM.find_1 in EQx; rewrite EQx in EQy; inv EQy. 
    cbn in *.
    apply IM.Raw.Proofs.not_find_iff in EQx; [| apply IM.Raw.Proofs.add_bst, IM.is_bst].
    exfalso; apply EQx, IM.Raw.Proofs.add_in.
    destruct (RelDec.rel_dec_p k k'); auto.
    right.
    unfold IM.MapsTo in *.
    eapply IM.Raw.Proofs.MapsTo_In,EQy.
  Qed.

  Lemma Equiv_add_add : forall {a} {r: a -> a -> Prop} {rR: Reflexive r},
      forall k v1 v2 (m: IM.t a),
        Equiv r (add k v2 (add k v1 m)) (add k v2 m).
  Proof.
    intros; split.
    - intros key.
      destruct (RelDec.rel_dec_p key k).
      + subst; rewrite 2 member_add_eq; reflexivity.
      + subst; rewrite 3 member_add_ineq; auto; reflexivity.
    - intros key v v' LU1 LU2; cbn.
      destruct (RelDec.rel_dec_p key k).
      + subst; rewrite lookup_add_eq in LU1, LU2; inv LU1; inv LU2.
        reflexivity.
      + subst; rewrite lookup_add_ineq in LU1, LU2; auto; rewrite lookup_add_ineq in LU1; auto.
        rewrite LU1 in LU2; inv LU2.
        reflexivity.
  Qed.

  (* Extends the map with a list of pairs key/value.
     Note: additions start from the end of the list, so in case of duplicate
     keys, the binding in the front will shadow though in the back.
   *)
  Fixpoint add_all {a} ks (m:IntMap a) :=
    match ks with
    | [] => m
    | (k,v) :: tl => add k v (add_all tl m)
    end.

  (* Extends the map with the bindings {(i,v_1) .. (i+n-1, v_n)} for [vs ::= v_1..v_n] *)
  Fixpoint add_all_index {a} vs (i:Z) (m:IntMap a) :=
    match vs with
    | [] => m
    | v :: tl => add i v (add_all_index tl (i+1) m)
    end.

  (* Give back a list of values from [|i|] to [|i| + |sz| - 1] in [m].
     Uses [def] as the default value if a lookup failed.
   *)
  Definition lookup_all_index {a} (i:Z) (sz:Z) (m:IntMap a) (def:a) : list a :=
    List.map (fun x =>
                match lookup (Z.of_nat x) m with
                | None => def
                | Some val => val
                end) (seq (Z.to_nat i) (Z.to_nat sz)).

  (* Takes the join of two maps, favoring the first one over the intersection of their domains *)
  Definition union {a} (m1 : IntMap a) (m2 : IntMap a)
    := IM.map2 (fun mx my =>
                  match mx with | Some x => Some x | None => my end) m1 m2.

  (* TODO : Move the three following functions *)
    Fixpoint max_default (l:list Z) (x:Z) :=
    match l with
    | [] => x
    | h :: tl =>
      max_default tl (if h >? x then h else x)
    end.

  Definition maximumBy {A} (leq : A -> A -> bool) (def : A) (l : list A) : A :=
    fold_left (fun a b => if leq a b then b else a) l def.

  Definition is_some {A} (o : option A) :=
    match o with
    | Some x => true
    | None => false
    end.

  (* TODO SAZ: mem_block should keep track of its allocation size so
    that operations can fail if they are out of range

    CB: I think this might happen implicitly with make_empty_block --
    it initializes the IntMap with only the valid indices. As long as the
    lookup functions handle this properly, anyway.
   *)

  Section Datatype_Definition.

    (** ** Simple view of memory
      A concrete block is determined by its id and its size.
     *)
    Inductive concrete_block :=
    | CBlock (size : Z) (block_id : Z) : concrete_block.

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
    Definition mem_block    := IntMap SByte.
    Inductive logical_block :=
    | LBlock (size : Z) (bytes : mem_block) (concrete_id : option Z) : logical_block.

    (** ** Memory
      A concrete memory, resp. logical memory, maps addresses to concrete blocks, resp. logical blocks.
      A memory is a pair of both views of the memory.
     *)
    Definition concrete_memory := IntMap concrete_block.
    Definition logical_memory  := IntMap logical_block.
    Definition memory          := (concrete_memory * logical_memory)%type.

    (** ** Stack frames
      A frame contains the list of block ids that need to be freed when popped,
      i.e. when the function returns.
      A [frame_stack] is a list of such frames.
     *)
    Definition mem_frame := list Z.
    Definition frame_stack := list mem_frame.

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

    (** Length properties *)

    Lemma length_bytes_of_int:
      forall n x, List.length (bytes_of_int n x) = n.
    Proof.
      induction n; simpl; intros. auto. decEq. auto.
    Qed.

    Lemma int_of_bytes_of_int:
      forall n x,
        int_of_bytes (bytes_of_int n x) = x mod (two_p (Z.of_nat n * 8)).
    Proof.
      induction n; intros.
      simpl. rewrite Zmod_1_r. auto.
      Opaque Byte.wordsize.
      rewrite Nat2Z.inj_succ. simpl.
      replace (Z.succ (Z.of_nat n) * 8) with (Z.of_nat n * 8 + 8) by omega.
      rewrite two_p_is_exp; try omega.
      rewrite Zmod_recombine. rewrite IHn. rewrite Z.add_comm.
      change (Byte.unsigned (Byte.repr x)) with (Byte.Z_mod_modulus x).
      rewrite Byte.Z_mod_modulus_eq. reflexivity.
      apply two_p_gt_ZERO. omega. apply two_p_gt_ZERO. omega.
    Qed.

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
      | DVALUE_Packed_struct fields
      | DVALUE_Array fields
      | DVALUE_Vector fields =>
        (* note the _right_ fold is necessary for byte ordering. *)
        fold_right (fun 'dv acc => ((serialize_dvalue dv) ++ acc) % list) [] fields
      | _ => [] (* TODO add more dvalues as necessary *)
      end.

    (** ** Well defined block
      A list of [sbytes] is considered undefined if any of its bytes is undefined.
      This predicate checks that they are all well-defined.
     *)
    Definition all_not_sundef (bytes : list SByte) : bool :=
      forallb id (map Sbyte_defined bytes).

    (** ** Size of a dynamic type
      Computes the byte size of a [dtyp]. *)
    Fixpoint sizeof_dtyp (ty:dtyp) : Z :=
      match ty with
      | DTYPE_I sz         => 8 (* All integers are padded to 8 bytes. *)
      | DTYPE_Pointer      => 8
      | DTYPE_Packed_struct l
      | DTYPE_Struct l     => fold_left (fun acc x => acc + sizeof_dtyp x) l 0
      | DTYPE_Vector sz ty'
      | DTYPE_Array sz ty' => sz * sizeof_dtyp ty'
      | DTYPE_Float        => 4
      | DTYPE_Double       => 8
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
        match sz with
        | 1  => UVALUE_I1 (repr des_int)
        | 8  => UVALUE_I8 (repr des_int)
        | 32 => UVALUE_I32 (repr des_int)
        | 64 => UVALUE_I64 (repr des_int)
        | _  => UVALUE_None (* invalid size. *)
        end
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
        UVALUE_Array (array_parse (Z.to_nat sz) (Z.to_nat (sizeof_dtyp t')) bytes)
      | DTYPE_Vector sz t' =>
        let fix array_parse count byte_sz bytes :=
            match count with
            | O => []
            | S n => (deserialize_sbytes_defined (firstn byte_sz bytes) t')
                      :: array_parse n byte_sz (skipn byte_sz bytes)
            end in
        UVALUE_Vector (array_parse (Z.to_nat sz) (Z.to_nat (sizeof_dtyp t')) bytes)
      | DTYPE_Struct fields =>
        let fix struct_parse typ_list bytes :=
            match typ_list with
            | [] => []
            | t :: tl =>
              let size_ty := Z.to_nat (sizeof_dtyp t) in
              (deserialize_sbytes_defined (firstn size_ty bytes) t)
                :: struct_parse tl (skipn size_ty bytes)
            end in
        UVALUE_Struct (struct_parse fields bytes)
      | DTYPE_Packed_struct fields =>
        let fix struct_parse typ_list bytes :=
            match typ_list with
            | [] => []
            | t :: tl =>
              let size_ty := Z.to_nat (sizeof_dtyp t) in
              (deserialize_sbytes_defined (firstn size_ty bytes) t)
                :: struct_parse tl (skipn size_ty bytes)
            end in
        UVALUE_Packed_struct (struct_parse fields bytes)
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

    (* Todo - complete proofs, and think about moving to MemoryProp module. *)
    (* The relation defining serializable dvalues. *)
    Inductive serialize_defined : dvalue -> Prop :=
    | d_addr: forall addr,
        serialize_defined (DVALUE_Addr addr)
    | d_i1: forall i1,
        serialize_defined (DVALUE_I1 i1)
    | d_i8: forall i1,
        serialize_defined (DVALUE_I8 i1)
    | d_i32: forall i32,
        serialize_defined (DVALUE_I32 i32)
    | d_i64: forall i64,
        serialize_defined (DVALUE_I64 i64)
    | d_struct_empty:
        serialize_defined (DVALUE_Struct [])
    | d_struct_nonempty: forall dval fields_list,
        serialize_defined dval ->
        serialize_defined (DVALUE_Struct fields_list) ->
        serialize_defined (DVALUE_Struct (dval :: fields_list))
    | d_array_empty:
        serialize_defined (DVALUE_Array [])
    | d_array_nonempty: forall dval fields_list,
        serialize_defined dval ->
        serialize_defined (DVALUE_Array fields_list) ->
        serialize_defined (DVALUE_Array (dval :: fields_list)).

    (* Lemma assumes all integers encoded with 8 bytes. *)

    Inductive sbyte_list_wf : list SByte -> Prop :=
    | wf_nil : sbyte_list_wf []
    | wf_cons : forall b l, sbyte_list_wf l -> sbyte_list_wf (Byte b :: l)
    .

    Lemma fold_sizeof :
        forall (dts : list dtyp) n,
          fold_left (fun (acc : Z) (x : dtyp) => acc + sizeof_dtyp x) dts n =
          n + fold_left (fun (acc : Z) (x : dtyp) => acc + sizeof_dtyp x) dts 0.
    Proof.
      induction dts; intros n.
      - cbn. rewrite Z.add_0_r. reflexivity.
      - cbn. rewrite IHdts at 1. rewrite (IHdts (sizeof_dtyp a)).
        rewrite Z.add_assoc.
        reflexivity.
    Qed.

    Lemma sizeof_struct_cons :
      forall dt dts,
        sizeof_dtyp (DTYPE_Struct (dt :: dts)) = sizeof_dtyp dt + sizeof_dtyp (DTYPE_Struct dts).
    Proof.
      cbn.
      intros dt dts.
      rewrite fold_sizeof. reflexivity.
    Qed.

    Lemma sizeof_packed_struct_cons :
      forall dt dts,
        sizeof_dtyp (DTYPE_Packed_struct (dt :: dts)) = sizeof_dtyp dt + sizeof_dtyp (DTYPE_Packed_struct dts).
    Proof.
      cbn.
      intros dt dts.
      rewrite fold_sizeof. reflexivity.
    Qed.

    Lemma zero_le_sizeof_dvalue :
      forall dv dt,
        dvalue_has_dtyp dv dt ->
        0 <= sizeof_dtyp dt.
    Proof.
      intros dv dt TYP.
      induction TYP using dvalue_has_dtyp_ind';
        try solve [cbn; omega].
      - rewrite sizeof_struct_cons.
        omega.
      - rewrite sizeof_packed_struct_cons.
        omega.
      - cbn. destruct xs.
        + cbn in *; subst.
          reflexivity.
        + assert (In d (d :: xs)); intuition.
          pose proof (IH d H0) as Hsz.
          inversion H. cbn.
          destruct (sizeof_dtyp dt).
          reflexivity.
          apply Zle_0_pos.
          pose proof Pos2Z.neg_is_neg p.
          contradiction.
      - cbn. destruct xs.
        + cbn in *; subst.
          reflexivity.
        + assert (In d (d :: xs)); intuition.
          pose proof (IH d H1) as Hsz.
          inversion H. cbn.
          destruct (sizeof_dtyp dt).
          reflexivity.
          apply Zle_0_pos.
          pose proof Pos2Z.neg_is_neg p.
          contradiction.
    Qed.

    Lemma sizeof_serialized :
      forall dv dt,
        dvalue_has_dtyp dv dt ->
        Z.of_nat (List.length (serialize_dvalue dv)) = sizeof_dtyp dt.
    Proof.
      intros dv dt TYP.
      induction TYP using dvalue_has_dtyp_ind'; try solve [cbn; auto].
      - cbn.
        rewrite app_length.
        rewrite Nat2Z.inj_add.
        rewrite IHTYP1.
        cbn in IHTYP2. rewrite IHTYP2.
        symmetry.
        apply fold_sizeof.
      - cbn.
        rewrite app_length.
        rewrite Nat2Z.inj_add.
        rewrite IHTYP1.
        cbn in IHTYP2. rewrite IHTYP2.
        symmetry.
        apply fold_sizeof.
      - generalize dependent sz.
        induction xs; intros sz H; cbn.
        + subst; auto.
        + cbn in *. rewrite <- H. rewrite app_length.
          replace (Z.of_nat (S (Datatypes.length xs)) * sizeof_dtyp dt)
            with (sizeof_dtyp dt + Z.of_nat (Datatypes.length xs) * sizeof_dtyp dt).
          * rewrite Nat2Z.inj_add. rewrite IHxs with (sz:=Datatypes.length xs); auto.
            apply Z.add_cancel_r; auto.
          * rewrite Nat2Z.inj_succ. rewrite Z.mul_succ_l. omega.
      - generalize dependent sz.
        induction xs; intros sz H; cbn.
        + subst; auto.
        + cbn in *. rewrite <- H. rewrite app_length.
          replace (Z.of_nat (S (Datatypes.length xs)) * sizeof_dtyp dt)
            with (sizeof_dtyp dt + Z.of_nat (Datatypes.length xs) * sizeof_dtyp dt).
          * rewrite Nat2Z.inj_add. rewrite IHxs with (sz:=Datatypes.length xs); auto.
            apply Z.add_cancel_r; auto.
          * rewrite Nat2Z.inj_succ. rewrite Z.mul_succ_l. omega.
    Qed.

    (* TODO: does this exist somewhere else? *)
    Lemma app_prefix :
      forall {A} (a b c : list A),
        b = c -> a ++ b = a ++ c.
    Proof.
      intros A a b c H.
      induction a.
      - cbn; auto.
      - cbn. rewrite IHa.
        reflexivity.
    Qed.

    Lemma firstn_sizeof_dtyp :
      forall dv dt,
        dvalue_has_dtyp dv dt ->
        (firstn (Z.to_nat (sizeof_dtyp dt)) (serialize_dvalue dv)) = serialize_dvalue dv.
    Proof.
      intros dv dt TYP.
      induction TYP using dvalue_has_dtyp_ind'; auto.
      - (* Structs *)
        rewrite sizeof_struct_cons.
        cbn.
        rewrite <- sizeof_serialized with (dv:=f); auto.

        replace (Z.to_nat
                   (Z.of_nat (Datatypes.length (serialize_dvalue f)) +
                    fold_left (fun (x : Z) (acc : dtyp) => x + sizeof_dtyp acc) dts 0)) with
            (Datatypes.length (serialize_dvalue f) +
             Z.to_nat (fold_left (fun (x : Z) (acc : dtyp) => (x + sizeof_dtyp acc)%Z) dts 0%Z))%nat.
        + rewrite firstn_app_2.
          cbn in *.
          rewrite IHTYP2.
          reflexivity.
        + rewrite Z2Nat.inj_add; try omega.
          rewrite Nat2Z.id. reflexivity.
          inversion TYP2; cbn.
          omega.

          pose proof (zero_le_sizeof_dvalue H2) as Hsz_fields.
          pose proof (zero_le_sizeof_dvalue H1) as Hsz_f.
          cbn in Hsz_fields.
          cbn in Hsz_f.

          rewrite fold_sizeof.
          omega.
      - (* Packed Structs *)
        rewrite sizeof_packed_struct_cons.
        cbn.
        rewrite <- sizeof_serialized with (dv:=f); auto.

        replace (Z.to_nat
                   (Z.of_nat (Datatypes.length (serialize_dvalue f)) +
                    fold_left (fun (x : Z) (acc : dtyp) => x + sizeof_dtyp acc) dts 0)) with
            (Datatypes.length (serialize_dvalue f) +
             Z.to_nat (fold_left (fun (x : Z) (acc : dtyp) => (x + sizeof_dtyp acc)%Z) dts 0%Z))%nat.
        + rewrite firstn_app_2.
          cbn in *.
          rewrite IHTYP2.
          reflexivity.
        + rewrite Z2Nat.inj_add; try omega.
          rewrite Nat2Z.id. reflexivity.
          inversion TYP2; cbn.
          omega.

          pose proof (zero_le_sizeof_dvalue H2) as Hsz_fields.
          pose proof (zero_le_sizeof_dvalue H1) as Hsz_f.
          cbn in Hsz_fields.
          cbn in Hsz_f.

          rewrite fold_sizeof.
          omega.
      - (* Arrays *)
        generalize dependent sz.
        induction xs; intros sz H.
        + cbn. apply firstn_nil.
        + cbn in *. inversion H.
          replace (Z.of_nat (S (Datatypes.length xs)) * sizeof_dtyp dt) with
              (sizeof_dtyp dt + Z.of_nat (Datatypes.length xs) * sizeof_dtyp dt).
          * rewrite Z2Nat.inj_add.
            -- cbn. rewrite <- sizeof_serialized with (dv:=a).
               rewrite Nat2Z.id.
               rewrite firstn_app_2.
               rewrite sizeof_serialized with (dt:=dt).
               apply app_prefix.
               apply IHxs.
               intros x Hin.
               apply IH; intuition.
               intros x Hin; auto.
               auto.
               auto.
               auto.
            -- eapply zero_le_sizeof_dvalue; eauto.
            -- assert (dvalue_has_dtyp a dt) as TYP by auto.
               pose proof zero_le_sizeof_dvalue TYP.
               pose proof Zle_0_nat (Datatypes.length xs).
               apply Z.mul_nonneg_nonneg; auto.
          * rewrite Nat2Z.inj_succ. rewrite Z.mul_succ_l. omega.
      - (* Vectors *)
        generalize dependent sz.
        induction xs; intros sz H.
        + cbn. apply firstn_nil.
        + cbn in *. inversion H.
          replace (Z.of_nat (S (Datatypes.length xs)) * sizeof_dtyp dt) with
              (sizeof_dtyp dt + Z.of_nat (Datatypes.length xs) * sizeof_dtyp dt).
          * rewrite Z2Nat.inj_add.
            -- cbn. rewrite <- sizeof_serialized with (dv:=a).
               rewrite Nat2Z.id.
               rewrite firstn_app_2.
               rewrite sizeof_serialized with (dt:=dt).
               apply app_prefix.
               apply IHxs.
               intros x Hin.
               apply IH; intuition.
               intros x Hin; auto.
               auto.
               auto.
               auto.
            -- eapply zero_le_sizeof_dvalue; eauto.
            -- assert (dvalue_has_dtyp a dt) as TYP by auto.
               pose proof zero_le_sizeof_dvalue TYP.
               pose proof Zle_0_nat (Datatypes.length xs).
               apply Z.mul_nonneg_nonneg; auto.
          * rewrite Nat2Z.inj_succ. rewrite Z.mul_succ_l. omega.
    Qed.

    Lemma skipn_length_app :
      forall {A} (xs ys : list A),
        skipn (Datatypes.length xs) (xs ++ ys) = ys.
    Proof.
      intros A xs ys.
      induction xs; cbn; auto.
    Qed.

    Lemma all_not_sundef_cons :
      forall b bs,
        all_not_sundef (b :: bs) = true ->
        all_not_sundef bs = true.
    Proof.
      intros b bs H.
      cbn in H.
      unfold all_not_sundef.
      apply andb_prop in H as [Hid Hall].
      auto.
    Qed.

    Lemma all_not_sundef_app :
      forall xs ys,
        all_not_sundef xs ->
        all_not_sundef ys ->
        all_not_sundef (xs ++ ys).
    Proof.
      induction xs; intros ys Hxs Hys; auto.
      cbn in *.
      apply andb_prop in Hxs.
      apply andb_true_iff.
      intuition.
      apply IHxs; auto.
    Qed.

    Hint Resolve all_not_sundef_app.

    Lemma byte_defined :
      forall b bs,
        all_not_sundef bs ->
        In b bs ->
        Sbyte_defined b.
    Proof.
      intros b bs Hundef Hin.
      induction bs.
      - inversion Hin.
      - apply andb_prop in Hundef as [Hid Hall].
        inversion Hin; subst.
        + apply Hid.
        + apply IHbs; auto.
    Qed.

    Lemma dvalue_serialized_not_sundef :
      forall dv,
        all_not_sundef (serialize_dvalue dv) = true.
    Proof.
      intros dv.
      induction dv using dvalue_ind'; auto.
      - induction fields.
        + reflexivity.
        + cbn. apply forallb_forall.
          intros x Hin.
          apply list_in_map_inv in Hin as [b [Hxb Hin]]; subst.
          apply in_app_or in Hin as [Hin | Hin].
          * assert (In a (a :: fields)) as Hina by intuition.
            specialize (H a Hina).
            eapply byte_defined; eauto.
          * assert (forall u : dvalue, In u fields -> all_not_sundef (serialize_dvalue u) = true) as Hu.
            intros u Hinu.
            apply H. cbn. auto.

            specialize (IHfields Hu).
            eapply byte_defined. apply IHfields.
            apply Hin.
      - induction fields.
        + reflexivity.
        + cbn. apply forallb_forall.
          intros x Hin.
          apply list_in_map_inv in Hin as [b [Hxb Hin]]; subst.
          apply in_app_or in Hin as [Hin | Hin].
          * assert (In a (a :: fields)) as Hina by intuition.
            specialize (H a Hina).
            eapply byte_defined; eauto.
          * assert (forall u : dvalue, In u fields -> all_not_sundef (serialize_dvalue u) = true) as Hu.
            intros u Hinu.
            apply H. cbn. auto.

            specialize (IHfields Hu).
            eapply byte_defined. apply IHfields.
            apply Hin.
      - induction elts.
        + reflexivity.
        + cbn in *.
          rewrite map_app.
          rewrite forallb_app.
          apply andb_true_iff.
          split.
          * apply H; auto.
          * apply IHelts. intros e H0.
            apply H; auto.
      - induction elts.
        + reflexivity.
        + cbn in *.
          rewrite map_app.
          rewrite forallb_app.
          apply andb_true_iff.
          split.
          * apply H; auto.
          * apply IHelts. intros e H0.
            apply H; auto.
    Qed.

    Hint Resolve dvalue_serialized_not_sundef.

    Lemma all_not_sundef_fold_right_serialize :
      forall xs,
        all_not_sundef (fold_right (fun (dv : dvalue) (acc : list SByte) => serialize_dvalue dv ++ acc) [ ] xs).
    Proof.
      induction xs; auto.
      - cbn. apply all_not_sundef_app; auto.
    Qed.

    Hint Resolve all_not_sundef_fold_right_serialize.

    Lemma all_not_sundef_deserialized :
      forall bs t,
        all_not_sundef bs ->
        deserialize_sbytes_defined bs t = deserialize_sbytes bs t.
    Proof.
      intros bs t H.
      unfold deserialize_sbytes.
      rewrite H.
      auto.
    Qed.

    Lemma deserialize_sbytes_defined_dvalue :
      forall dv t,
        deserialize_sbytes_defined (serialize_dvalue dv) t = deserialize_sbytes (serialize_dvalue dv) t.
    Proof.
      intros dv t.
      apply all_not_sundef_deserialized.
      apply dvalue_serialized_not_sundef.
    Qed.

    Hint Resolve deserialize_sbytes_defined.

    Lemma serialize_firstn_app :
      forall dv dt rest,
        dvalue_has_dtyp dv dt ->
        firstn (Z.to_nat (sizeof_dtyp dt))
               (serialize_dvalue dv ++ rest) = serialize_dvalue dv.
    Proof.
      intros dv dt rest H.
      erewrite <- sizeof_serialized; eauto.
      rewrite Nat2Z.id.
      rewrite firstn_app.
      rewrite Nat.sub_diag.
      cbn.
      rewrite app_nil_r.
      rewrite <- (Nat2Z.id (Datatypes.length (serialize_dvalue dv))).
      erewrite sizeof_serialized; eauto.
      rewrite firstn_sizeof_dtyp; eauto.
    Qed.

    Lemma serialize_skipn_app :
      forall dv dt rest,
        dvalue_has_dtyp dv dt ->
        skipn (Z.to_nat (sizeof_dtyp dt))
               (serialize_dvalue dv ++ rest) = rest.
    Proof.
      intros dv dt rest H.
      erewrite <- sizeof_serialized; eauto.
      rewrite Nat2Z.id.
      apply skipn_length_app.
    Qed.

    Lemma serialize_inverses : forall dval t (TYP : dvalue_has_dtyp dval t),
        deserialize_sbytes (serialize_dvalue dval) t = dvalue_to_uvalue dval.
    Proof.
      intros dval t TYP.
      induction TYP using dvalue_has_dtyp_ind'; auto.
      - (* I1 *) admit.
      - (* I8 *) admit.
      - (* I32 *) admit.
      - (* I64 *) admit.
      - (* Double *) admit.
      - (* Float *) admit.
      - (* Structs *)
        generalize dependent f.
        generalize dependent dt.
        generalize dependent dts.
        induction fields; intros dts TYP2 IHTYP2 dt f TYP1 IHTYP1; inversion TYP2.
        + cbn. rewrite app_nil_r.
          unfold deserialize_sbytes.
          rewrite dvalue_serialized_not_sundef.
          cbn.
          rewrite firstn_sizeof_dtyp; auto.
          rewrite deserialize_sbytes_defined_dvalue.
          rewrite IHTYP1.
          auto.
        + subst; cbn.
          unfold deserialize_sbytes.

          rewrite all_not_sundef_app; auto.

          cbn.
          rewrite serialize_firstn_app; eauto.
          rewrite deserialize_sbytes_defined_dvalue.
          rewrite IHTYP1.

          cbn in *.
          rewrite serialize_skipn_app; eauto.
          rewrite serialize_firstn_app; eauto.
          rewrite deserialize_sbytes_defined_dvalue.

          unfold deserialize_sbytes in IHTYP2.
          rewrite all_not_sundef_app in IHTYP2; auto.

          cbn in IHTYP2.
          inversion IHTYP2.
          rewrite serialize_firstn_app in H0; eauto.
          rewrite deserialize_sbytes_defined_dvalue in H0.
          rewrite H0.

          rewrite serialize_firstn_app; eauto.
          rewrite deserialize_sbytes_defined_dvalue.
          rewrite H0.

          reflexivity.
      - (* Packed Structs *)
        generalize dependent f.
        generalize dependent dt.
        generalize dependent dts.
        induction fields; intros dts TYP2 IHTYP2 dt f TYP1 IHTYP1; inversion TYP2.
        + cbn. rewrite app_nil_r.
          unfold deserialize_sbytes.
          rewrite dvalue_serialized_not_sundef.
          cbn.
          rewrite firstn_sizeof_dtyp; auto.
          rewrite deserialize_sbytes_defined_dvalue.
          rewrite IHTYP1.
          auto.
        + subst; cbn.
          unfold deserialize_sbytes.

          rewrite all_not_sundef_app; auto.

          cbn.
          rewrite serialize_firstn_app; eauto.
          rewrite deserialize_sbytes_defined_dvalue.
          rewrite IHTYP1.

          cbn in *.
          rewrite serialize_skipn_app; eauto.
          rewrite serialize_firstn_app; eauto.
          rewrite deserialize_sbytes_defined_dvalue.

          unfold deserialize_sbytes in IHTYP2.
          rewrite all_not_sundef_app in IHTYP2; auto.

          cbn in IHTYP2.
          inversion IHTYP2.
          rewrite serialize_firstn_app in H0; eauto.
          rewrite deserialize_sbytes_defined_dvalue in H0.
          rewrite H0.

          rewrite serialize_firstn_app; eauto.
          rewrite deserialize_sbytes_defined_dvalue.
          rewrite H0.

          reflexivity.
      - (* Arrays *)
        generalize dependent sz.
        generalize dependent dt.
        induction xs; intros dt IH IHdtyp sz H; inversion H.
        + subst. auto.
        + cbn. unfold deserialize_sbytes.
          rewrite all_not_sundef_app; auto.
          cbn in *.
          rewrite SuccNat2Pos.id_succ.
          subst.

          rewrite serialize_firstn_app; auto.
          rewrite deserialize_sbytes_defined_dvalue.
          rewrite IH; auto.

          unfold deserialize_sbytes in IHxs.
          setoid_rewrite dvalue_serialized_not_sundef in IHxs.
          setoid_rewrite all_not_sundef_fold_right_serialize in IHxs.

          assert (forall x : dvalue, In x xs -> deserialize_sbytes_defined (serialize_dvalue x) dt = dvalue_to_uvalue x) as H1.
          intros x H.
          rewrite deserialize_sbytes_defined_dvalue. auto.

          assert (forall x : dvalue, In x xs -> dvalue_has_dtyp x dt) as H2 by auto.

          pose proof (IHxs dt H1 H2 (Datatypes.length xs) eq_refl).
          cbn in H.
          inversion H.

          rewrite serialize_skipn_app.
          rewrite Nat2Z.id.
          reflexivity.
          auto.
      - (* Vectors *)
        generalize dependent sz.
        generalize dependent dt.
        induction xs; intros dt IH IHdtyp Hvect sz H; inversion H.
        + subst. auto.
        + cbn. unfold deserialize_sbytes.
          rewrite all_not_sundef_app; auto.
          cbn in *.
          rewrite SuccNat2Pos.id_succ.
          subst.

          rewrite serialize_firstn_app; auto.
          rewrite deserialize_sbytes_defined_dvalue.
          rewrite IH; auto.

          unfold deserialize_sbytes in IHxs.
          setoid_rewrite dvalue_serialized_not_sundef in IHxs.
          setoid_rewrite all_not_sundef_fold_right_serialize in IHxs.

          assert (forall x : dvalue, In x xs -> deserialize_sbytes_defined (serialize_dvalue x) dt = dvalue_to_uvalue x) as H1.
          intros x H.
          rewrite deserialize_sbytes_defined_dvalue. auto.

          assert (forall x : dvalue, In x xs -> dvalue_has_dtyp x dt) as H2 by auto.

          pose proof (IHxs dt H1 H2 Hvect (Datatypes.length xs) eq_refl).
          cbn in H.
          inversion H.

          rewrite serialize_skipn_app.
          rewrite Nat2Z.id.
          reflexivity.
          auto.
    Admitted.

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
          | DTYPE_Vector _ ta
          | DTYPE_Array _ ta =>
            handle_gep_h ta (off + k * (sizeof_dtyp ta)) vs'
          | DTYPE_Struct ts
          | DTYPE_Packed_struct ts => (* Handle these differently in future *)
            let offset := fold_left (fun acc t => acc + sizeof_dtyp t)
                                    (firstn n ts) 0 in
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
          | DTYPE_Vector _ ta
          | DTYPE_Array _ ta =>
            handle_gep_h ta (off + k * (sizeof_dtyp ta)) vs'
          | _ => failwith ("non-i8-indexable type")
          end
        | DVALUE_I64 i =>
          let k := unsigned i in
          let n := BinIntDef.Z.to_nat k in
          match t with
          | DTYPE_Vector _ ta
          | DTYPE_Array _ ta =>
            handle_gep_h ta (off + k * (sizeof_dtyp ta)) vs'
          | _ => failwith ("non-i64-indexable type")
          end
        | _ => failwith "non-I32 index"
        end
      | [] => ret off
      end.

    (* At the toplevel, GEP takes a [dvalue] as an argument that must contain a pointer, but no other pointer can be recursively followed.
     The pointer set the block into which we look, and the initial offset. The first index value add to the initial offset passed to
     [handle_gep_h] for the actual access to structured data.
     *)
    Definition handle_gep (t:dtyp) (dv:dvalue) (vs:list dvalue) : err dvalue :=
      match vs with
      | DVALUE_I32 i :: vs' => (* TODO: Handle non i32 / i64 indices *)
        match dv with
        | DVALUE_Addr (b, o) =>
          off <- handle_gep_h t (o + (sizeof_dtyp t) * (unsigned i)) vs' ;;
          ret (DVALUE_Addr (b, off))
        | _ => failwith "non-address"
        end
      | DVALUE_I64 i :: vs' =>
        match dv with
        | DVALUE_Addr (b, o) =>
          off <- handle_gep_h t (o + (sizeof_dtyp t) * (unsigned i)) vs' ;;
          ret (DVALUE_Addr (b, off))
        | _ => failwith "non-address"
        end
      | _ => failwith "non-I32 index"
      end.

  End GEP.

  Section Logical_Operations.

    Inductive equivlb : logical_block -> logical_block -> Prop :=
    | Equivlb : forall z m m' cid, Equal m m' -> equivlb (LBlock z m cid) (LBlock z m' cid).

    Global Instance equivlb_Equiv : Equivalence equivlb.
    Proof.
      split.
      - intros []; constructor; reflexivity.
      - intros [] [] EQ; inv EQ; constructor; symmetry; auto. 
      - intros [] [] [] EQ1 EQ2; inv EQ1; inv EQ2; constructor; etransitivity; eauto. 
    Qed.

    Definition equivl : logical_memory -> logical_memory -> Prop :=
      @Equiv _ equivlb.

    Lemma member_lookup {a} : forall k (m : IM.t a),
        member k m -> exists v, lookup k m = Some v.
    Proof.
      unfold member,lookup in *.
      intros * IN.
      apply IM.Raw.Proofs.mem_2, IM.Raw.Proofs.In_MapsTo in IN.
      destruct IN as [v IN].
      exists v. 
      apply IM.Raw.Proofs.find_1; eauto.
      apply IM.is_bst.
    Qed.

    Lemma lookup_member {a} : forall k v(m : IM.t a),
        lookup k m = Some v -> member k m .
    Proof.
      unfold member,lookup in *.
      intros * IN.
      apply IM.Raw.Proofs.mem_1; [apply IM.is_bst |].
      apply IM.Raw.Proofs.find_2 in IN; eauto.
      eapply IM.Raw.Proofs.MapsTo_In; eauto. 
    Qed.
    
    Global Instance Equiv_Equiv {a} {r: a -> a -> Prop} {rE : Equivalence r} : Equivalence (Equiv r).
    Proof.
      split.
      - intros ?; split.
        intros k; reflexivity.
        intros * LU1 LU2; rewrite LU1 in LU2; inv LU2; reflexivity.
      - intros ? ? [DOM EQ]; split.
        intros ?; split; intros ?; apply DOM; auto. 
        intros; symmetry; eapply EQ; eauto.
      - intros ? ? ? [DOM1 EQ1] [DOM2 EQ2]; split.
        intros ?; split; intros ?.
        apply DOM2,DOM1; auto.
        apply DOM1,DOM2; auto.
       intros ? ? ? LU1 LU2.
       generalize LU1; intros LU3; apply lookup_member,DOM1,member_lookup in LU3. 
       destruct LU3 as [e'' LU3].
       transitivity e''.
       eapply EQ1; eauto.
       eapply EQ2; eauto.
    Qed. 

    Global Instance equivl_Equiv : Equivalence equivl.
    Proof.
      unfold equivl.
      apply Equiv_Equiv.
    Qed.

    Definition logical_empty : logical_memory := empty.

    (* Returns a fresh key for use in memory map *)
    Definition logical_next_key (m : logical_memory) : Z
      := let keys := map fst (IM.elements m) in
         1 + maximumBy Z.leb (-1) keys.

    (** ** Initialization of blocks
      Constructs an initial [mem_block] of undefined [SByte]s, indexed from 0 to n.
     *)
    Fixpoint init_block_undef (n:nat) (m:mem_block) : mem_block :=
      match n with
      | O => add 0 SUndef m
      | S n' => add (Z.of_nat n) SUndef (init_block_undef n' m)
      end.

    (* Constructs an initial [mem_block] containing [n] undefined [SByte]s, indexed from [0] to [n - 1].
     If [n] is negative, it is treated as [0].
     *)
    Definition init_block (n:Z) : mem_block :=
      match n with
      | 0 => empty
      | Z.pos n' => init_block_undef (BinPosDef.Pos.to_nat (n' - 1)) empty
      | Z.neg _ => empty (* invalid argument *)
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
    Definition get_array_mem_block_at_i (bk : mem_block) (bk_offset : Z) (i : nat) (size : Z) (t : dtyp) : err uvalue :=
      'offset <- handle_gep_h (DTYPE_Array size t)
                             bk_offset
                             [DVALUE_I64 (DynamicValues.Int64.repr (Z.of_nat i))];;
      inr (read_in_mem_block bk offset t).

    (** ** Array lookups -- mem_block
      Retrieve the values stored at position [from] to position [from + len - 1] in an array stored in a [mem_block].
     *)
    Definition get_array_mem_block (bk : mem_block) (bk_offset : Z) (from len : nat) (size : Z) (t : dtyp) : err (list uvalue) :=
      map_monad (fun i => get_array_mem_block_at_i bk bk_offset i size t) (seq from len).

  End Logical_Operations.

  Section Concrete_Operations.

    Definition concrete_empty : concrete_memory := empty.

    Definition equivc : concrete_memory -> concrete_memory -> Prop := Equal.

    Global Instance equivc_Equiv : Equivalence equivc.
    Proof.
      unfold equivc; typeclasses eauto.
    Qed.

    Infix "≡" := equivc (at level 39).

    Definition concrete_next_key (m : concrete_memory) : Z :=
      let keys         := List.map fst (IM.elements m) in
      let max          := max_default keys 0 in
      let offset       := 1 in (* TODO: This should be "random" *)
      match lookup max m with
      | None => offset
      | Some (CBlock sz _) => max + sz + offset
      end.

  End Concrete_Operations.

  Section Memory_Operations.

      (** ** Smart lookups *)
      Definition get_concrete_block_mem (b : Z) (m : memory) : option concrete_block :=
        let concrete_map := fst m in
        lookup b concrete_map.

      Definition get_logical_block_mem (b : Z) (m : memory) : option logical_block :=
        let logical_map := snd m in
        lookup b logical_map.

      (* Get the next key in the logical map *)
      Definition next_logical_key_mem (m : memory) : Z :=
        logical_next_key (snd m).

      (* Get the next key in the concrete map *)
      Definition next_concrete_key_mem (m : memory) : Z :=
        concrete_next_key (fst m).

      (** ** Extending the memory  *)
      Definition add_concrete_block_mem (id : Z) (b : concrete_block) (m : memory) : memory :=
        match m with
        | (cm, lm) =>
          (add id b cm, lm)
        end.

      Definition add_logical_block_mem (id : Z) (b : logical_block) (m : memory) : memory :=
        match m with
        | (cm, lm) =>
          (cm, add id b lm)
        end.

      (** ** Concretization of blocks
          Look-ups a concrete block in memory. The logical memory acts first as a potential layer of indirection:
          - if no logical block is found, the input is directly returned.
          - if a logical block is found, and that a concrete block is associated, the address of this concrete block
          is returned, paired with the input memory.
          - if a logical block is found, but that no concrete block is (yet) associated to it, then the associated
          concrete block is allocated, and the association is added to the logical block.
       *)
      Definition concretize_block_mem (b:Z) (m:memory) : Z * memory :=
        match get_logical_block_mem b m with
        | None => (b, m) (* TODO: Not sure this makes sense??? *)
        | Some (LBlock sz bytes (Some cid)) => (cid, m)
        | Some (LBlock sz bytes None) =>
          (* Allocates a concrete block for this one *)
          let id        := next_concrete_key_mem m in
          let new_block := CBlock sz b in
          let m'        := add_concrete_block_mem id new_block m in
          let m''       := add_logical_block_mem  b (LBlock sz bytes (Some id)) m' in
          (id, m'')
        end.

      (** ** Abstraction of blocks
          Retrieve a logical description of a block as address and offset from its concrete address.
          The non-trivial part consists in extracting from the [concrete_memory] the concrete address
          and block corresponding to a logical one.
       *)
      Definition get_real_cid (cid : Z) (m : memory) : option (Z * concrete_block)
        := IM.fold (fun k '(CBlock sz bid) a => if (k <=? cid) && (cid <? k + sz)
                                             then Some (k, CBlock sz bid)
                                             else a) (fst m) None.

      Definition concrete_address_to_logical_mem (cid : Z) (m : memory) : option (Z * Z)
        := match m with
           | (cm, lm) =>
             '(rid, CBlock sz bid) <- get_real_cid cid m ;;
             ret (bid, cid-rid)
           end.

      (* LLVM 5.0 memcpy
         According to the documentation: http://releases.llvm.org/5.0.0/docs/LangRef.html#llvm-memcpy-intrinsic
         this operation can never fail?  It doesn't return any status code...
       *)

      (* TODO probably doesn't handle sizes correctly... *)
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

          src_block <- trywith "memcpy src block not found" (get_logical_block_mem src_b m) ;;
          dst_block <- trywith "memcpy dst block not found" (get_logical_block_mem dst_b m) ;;

          let src_bytes
              := match src_block with
                 | LBlock size bytes concrete_id => bytes
                 end in
          let '(dst_sz, dst_bytes, dst_cid)
              := match dst_block with
                 | LBlock size bytes concrete_id => (size, bytes, concrete_id)
                 end in
          let sdata := lookup_all_index src_o (unsigned len) src_bytes SUndef in
          let dst_bytes' := add_all_index sdata dst_o dst_bytes in
          let dst_block' := LBlock dst_sz dst_bytes' dst_cid in
          let m' := add_logical_block_mem dst_b dst_block' m in
          (ret m' : err memory)
        | _ => failwith "memcpy got incorrect arguments"
        end.

  End Memory_Operations.

  Section Frame_Stack_Operations.

    (* The initial frame stack is not an empty stack, but a singleton stack containing an empty frame *)
    Definition frame_empty : frame_stack := [[]].

    (** ** Free
        [free_frame f m] deallocates the frame [f] from the memory [m].
        This acts on both representations of the memory:
        - on the logical memory, it simply removes all keys indicated by the frame;
        - on the concrete side, for each element of the frame, we lookup in the logical memory
        if it is bounded to a logical block, and if so if this logical block contains an associated
        concrete block. If so, we delete this association from the concrete memory.
     *)
    Definition free_concrete_of_logical
               (b : Z)
               (lm : logical_memory)
               (cm : concrete_memory) : concrete_memory
      := match lookup b lm with
         | None => cm
         | Some (LBlock _ _ None) => cm
         | Some (LBlock _ _ (Some cid)) => delete cid cm
         end.

    Definition free_frame_memory (f : mem_frame) (m : memory) : memory :=
      let '(cm, lm) := m in
      let cm' := fold_left (fun m key => free_concrete_of_logical key lm m) f cm in
      (cm', fold_left (fun m key => delete key m) f lm).

    Definition equivs : frame_stack -> frame_stack -> Prop := Logic.eq.

    Global Instance equivs_Equiv : Equivalence equivs. 
    split; unfold equivs; typeclasses eauto.
    Qed.

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
    Definition empty_memory_stack : memory_stack := ((concrete_empty, logical_empty), frame_empty).

    (** ** Smart lookups *)

    Definition get_concrete_block (m : memory_stack) (key : Z) : option concrete_block :=
      get_concrete_block_mem key (fst m).

    Definition get_logical_block (m : memory_stack) (key : Z) : option logical_block :=
      get_logical_block_mem key (fst m).

    (** ** Fresh key getters *)

    (* Get the next key in the logical map *)
    Definition next_logical_key (m : memory_stack) : Z :=
      next_logical_key_mem (fst m).

    (* Get the next key in the concrete map *)
    Definition next_concrete_key (m : memory_stack) : Z :=
      next_concrete_key_mem (fst m).

    (** ** Extending the memory  *)
    Definition add_concrete_block (id : Z) (b : concrete_block) (m : memory_stack) : memory_stack :=
      let '(m,s) := m in (add_concrete_block_mem id b m,s).

    Definition add_logical_block (id : Z) (b : logical_block) (m : memory_stack) : memory_stack :=
      let '(m,s) := m in (add_logical_block_mem id b m,s).

    (** ** Array lookups -- memory_stack
      Retrieve the values stored at position [from] to position [from + len - 1] in an array stored at address [a] in memory.
     *)
    Definition get_array (m: memory_stack) (a : addr) (from len: nat) (size : Z) (t : dtyp) : err (list uvalue) :=
      let '(b, o) := a in
      match get_logical_block m b with
      | Some (LBlock _ bk _) =>
        get_array_mem_block bk o from len size t
      | None => failwith "Memory function [get_array] called at a non-allocated address"
      end.

    Definition free_frame (m : memory_stack) : err memory_stack :=
      let '(m,sf) := m in
      match sf with
      | [] => failwith "Attempting to free a frame from a currently empty stack of frame"
      | f :: sf => inr (free_frame_memory f m,sf)
      end.

    Definition push_fresh_frame (m : memory_stack) : memory_stack :=
      let '(m,s) := m in (m, [] :: s).

    Definition add_to_frame (m : memory_stack) (k : Z) : err memory_stack :=
      let '(m,s) := m in
      match s with
      | [] => failwith "Attempting to allocate in a currently empty stack of frame"
      | f :: s => ret (m, (k :: f) :: s)
      end.

    Definition allocate (m : memory_stack) (t : dtyp) : err (memory_stack * Z) :=
      let new_block := make_empty_logical_block t in
      let key       := next_logical_key m in
      let m         := add_logical_block key new_block m in
      'm <- add_to_frame m key;;
      ret (m,key).

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

    Definition concrete_address_to_logical (cid : Z) (m : memory_stack) : option (Z * Z) :=
      concrete_address_to_logical_mem cid (fst m).

    Definition concretize_block (ptr : addr) (m : memory_stack) : Z * memory_stack :=
      let '(b', m') := concretize_block_mem (fst ptr) (fst m) in
      (b', (m', snd m)).

  End Memory_Stack_Operations.

  Section Memory_Stack_Theory.

    (** ** Block level lemmas *)

    Lemma get_logical_block_of_add_logical_block :
      forall (m : memory_stack) (key : Z) (lb : logical_block),
        get_logical_block (add_logical_block key lb m) key = Some lb.
    Proof.
      intros [[cm lm] s] b lb.
      cbn.
      rewrite IM.Raw.Proofs.add_find.
      pose proof @IM.Raw.Proofs.MX.elim_compare_eq b b eq_refl as [blah Heq].
      rewrite Heq.
      reflexivity.
      apply IM.is_bst.
    Qed.

    Require Import Psatz.

    Lemma seq_succ : forall off n,
        n >= 0 ->
        off >= 0 ->
        seq (Z.to_nat off) (Z.to_nat (Z.succ n)) = Z.to_nat off :: seq (Z.to_nat (Z.succ off)) (Z.to_nat n).
    Proof.
      intros; cbn.
      rewrite Z2Nat.inj_succ; [| lia].
      cbn; f_equal.
      rewrite (Z2Nat.inj_succ off); [| lia].
      auto.
      Qed.

    Lemma lookup_all_index_cons : forall off (n : Z) (bk : mem_block) def,
        off >= 0 ->
        n >= 0 ->
        lookup_all_index off (Z.succ n) bk def =
        match lookup off bk with
        | Some val => val
        | None => def
        end :: lookup_all_index (Z.succ off) n bk def
    .
    Proof.
      intros.
      unfold lookup_all_index.
      rewrite seq_succ; try lia.
      cbn.
      rewrite Z2Nat.id; auto.
      lia.
    Qed.

    Lemma lookup_all_index_add_out_of_range : forall off n (bk : mem_block) key x def,
        key < off ->
        lookup_all_index off n (add key x bk) def =
        lookup_all_index off n bk def.
    Proof.
    Admitted.

    Lemma lookup_all_index_add : forall off size x (bk : mem_block) def,
        off >= 0 ->
        size >= 0 ->
        lookup_all_index off (Z.succ size) (add off x bk) def =
        x :: lookup_all_index (Z.succ off) size bk def.
    Proof.
      intros * POS1 POS2.
      rewrite lookup_all_index_cons; auto; try lia.
      rewrite lookup_add_eq.
      f_equal.
      rewrite lookup_all_index_add_out_of_range; auto; try lia.
    Qed.

    Lemma unsigned_I1_in_range : forall (x : DynamicValues.int1),
        0 <= DynamicValues.Int1.unsigned x <= 1.
    Proof.
      destruct x as [x [? ?]].
      cbn in *.
      unfold DynamicValues.Int1.modulus,DynamicValues.Int1.wordsize, DynamicValues.Wordsize1.wordsize, two_power_nat in *.
      cbn in *; lia.
    Qed.

    Lemma unsigned_I8_in_range : forall (x : DynamicValues.int8),
        0 <= DynamicValues.Int8.unsigned x <= 255.
    Proof.
      destruct x as [x [? ?]].
      cbn in *.
      unfold DynamicValues.Int8.modulus,DynamicValues.Int8.wordsize, DynamicValues.Wordsize8.wordsize, two_power_nat in *.
      cbn in *; lia.
    Qed.

    (** ** Deserialize - Serialize
        Starting from a dvalue [val] whose [dtyp] is [t], if:
        1. we serialize [val], getting a [list SByte]
        2. we add all these bytes to the memory block, starting from the position [off], getting back a new [mem_block] m'
        3. we lookup in this new memory [m'] the indices starting from [off] for the size of [t], getting back a [list SByte]
        4. we deserialize this final list of bytes
        then we should get back the initial value [val], albeit injected into [uvalue].

        The proof should go by induction over [TYP] I think, and rely on [lookup_all_index_add] notably.
     *)
    Lemma deserialize_serialize : forall val t (TYP : dvalue_has_dtyp val t),
        forall off (bytes : mem_block),
          off >= 0 ->
          deserialize_sbytes (lookup_all_index off (sizeof_dtyp t) (add_all_index (serialize_dvalue val) off bytes) SUndef) t = dvalue_to_uvalue val.
    Proof.
      induction 1; try auto.
      - admit.
      - intros.
        simpl add_all_index; simpl sizeof_dtyp.
        replace 8 with (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ 0)))))))) by reflexivity.
        do 8 (rewrite lookup_all_index_add; try lia).
        cbn; f_equal.
        pose proof (unsigned_I1_in_range x).
        assert (EQ :DynamicValues.Int1.unsigned x / 256 = 0).
        apply Z.div_small; lia.
        rewrite EQ.
        repeat rewrite Zdiv_0_l.
        repeat rewrite Byte.unsigned_repr.
        all: unfold Byte.max_unsigned, Byte.modulus; cbn; try lia.
        rewrite Z.add_0_r.
        apply DynamicValues.Int1.repr_unsigned.
      - intros.
        simpl add_all_index; simpl sizeof_dtyp.
        replace 8 with (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ 0)))))))) by reflexivity.
        do 8 (rewrite lookup_all_index_add; try lia).
        cbn; f_equal.
        pose proof (unsigned_I8_in_range x).
        revert H0; generalize (DynamicValues.Int8.unsigned x) as y; intros y ?.
        repeat rewrite Byte.unsigned_repr.
        all: unfold Byte.max_unsigned, Byte.modulus; cbn.
        all: try lia.
        all: admit.
      - admit.
      - admit.
      - admit.
      - admit.
     Admitted.

    (** ** Write - Read
        The expected law: reading the key that has just been written to returns the written value.
        The only subtlety comes from the fact that it holds _if_ the read is performed at the type of
        the written value.
     *)
    Lemma write_read :
      forall (m m' : memory_stack) (t : dtyp) (val : dvalue) (a : addr),
        write m a val = inr m' ->
        dvalue_has_dtyp val t ->
        read m' a t = inr (dvalue_to_uvalue val).
    Proof.
      unfold write, read; cbn.
      intros * WR TYP.
      flatten_hyp WR; try inv_sum.
      destruct l,a as [id off]; inv_sum.
      rewrite get_logical_block_of_add_logical_block.
      cbn.
      unfold read_in_mem_block.
      rewrite deserialize_serialize; auto.
      (* The address needs to be well-formed in that the offset is positive *)
      admit.
    Admitted.

    Definition equiv : memory_stack -> memory_stack -> Prop := 
      fun '((cm,lm), s) '((cm',lm'),s') =>
        equivs s s' /\
        equivc cm cm' /\
        equivl lm lm'.

    Global Instance equiv_Equiv : Equivalence equiv.
    Proof.
      split.
      - intros ((cm,lm),s); cbn; split; [| split]; reflexivity. 
      - intros ((cm,lm),s) ((cm',lm'),s') EQ; cbn; split; [| split]; symmetry; apply EQ.
      - intros ((cm,lm),s) ((cm',lm'),s') ((cm'',lm''),s'') EQ1 EQ2; cbn; split; [| split]; (etransitivity; [apply EQ1 | apply EQ2]).
    Qed.      

    Infix "≡" := equiv (at level 25).

    Lemma add_add_logical : forall off b1 b2 m,
        equivl (add off b2 (add off b1 m)) (add off b2 m).
    Proof.
      intros; apply Equiv_add_add. 
   Qed.

    Lemma add_logical_block_add_logical_block :
      forall off b1 b2 m,
        add_logical_block off b2 (add_logical_block off b1 m) ≡ add_logical_block off b2 m.
    Proof.
      intros ? ? ? ((cm,lm),s).
      cbn; split; [reflexivity | split; [reflexivity |]]. 
      apply add_add_logical. 
    Qed.

    (* YZ : Either exists, or define more properly *)
    Definition equiv_sum {A : Type} (R : A -> A -> Prop) : err A -> err A -> Prop :=
      fun ma ma' => match ma,ma' with
                 | inr a, inr a' => R a a'
                 | inl _, inl _ => True
                 | _, _ => False
                 end.

    Global Instance Proper_lookup {a} k: Proper (@Equal a ==> Logic.eq) (lookup k).
    Proof.
      repeat intro.
      apply H.
    Qed.

    Lemma lookup_add_all_index_in : forall l k z (m : mem_block) v,
        z <= k <= z + Zlength l - 1 ->
        list_nth_z l (k - z) = Some v ->
        lookup k (add_all_index l z m) = Some v.
    Proof.
      induction l as [| x l IH]; simpl; intros * INEQ LU.
      inv LU.
      destruct (RelDec.rel_dec_p k z).
      - subst.
        rewrite Z.sub_diag in LU; cbn in LU; inv LU.
        rewrite lookup_add_eq;  reflexivity.
      - rewrite lookup_add_ineq; auto.
        apply IH.
        rewrite Zlength_cons in INEQ; lia.
        destruct (zeq (k - z)) eqn:INEQ'; [lia |].
        replace (k - (z + 1)) with (Z.pred (k-z)) by lia; auto.
    Qed.

    Lemma lookup_add_all_index_out : forall l k z (m : mem_block),
        (k < z \/ k >= z + Zlength l) ->
        lookup k (add_all_index l z m) = lookup k m.
    Proof.
      induction l as [| x l IH]; simpl; intros * INEQ; auto.
      destruct (RelDec.rel_dec_p k z).
      - subst. exfalso; destruct INEQ as [INEQ | INEQ]; try lia.
        rewrite Zlength_cons, Zlength_correct in INEQ; lia.
      - rewrite lookup_add_ineq; auto.
        apply IH.
        destruct INEQ as [INEQ | INEQ]; [left; lia | ].
        right.
        rewrite Zlength_cons, Zlength_correct in INEQ. 
        rewrite Zlength_correct.
        lia.
    Qed.

    Lemma key_in_range_or_not_aux : forall (k z : Z) (l : list SByte),
        {z <= k <= z + Zlength l - 1} + {k < z} + {k >= z + Zlength l}.
    Proof.
      induction l as [| x l IH]; intros.
      - cbn; rewrite Z.add_0_r.
        destruct (@RelDec.rel_dec_p _ Z.lt _ _ k z); [left; right; auto | right; lia].
      - rewrite Zlength_cons, <- Z.add_1_r.
        destruct IH as [[IH | IH] | IH].
        + left; left; lia.
        + left; right; lia.
        + destruct (RelDec.rel_dec_p k (z + Zlength l)).
          * subst; left; left; rewrite Zlength_correct; lia.
          * right; lia.
    Qed.

    Lemma key_in_range_or_not : forall (k z : Z) (l : list SByte),
        {z <= k <= z + Zlength l - 1} + {k < z \/ k >= z + Zlength l}.
    Proof.
      intros; destruct (@key_in_range_or_not_aux k z l) as [[? | ?] | ?]; [left; auto | right; auto | right; auto].
    Qed.

    Lemma range_list_nth_z : forall {a} (l : list a) k,
        0 <= k < Zlength l ->
        exists v, list_nth_z l k = Some v.
    Proof.
      induction l as [| x l IH]; intros k INEQ; [cbn in *; lia |].
      cbn; flatten_goal; [eexists; reflexivity |].
      destruct (IH (Z.pred k)) as [v LU]; eauto.
      rewrite Zlength_cons in INEQ; lia.
    Qed.

    Lemma in_range_is_in :  forall (k z : Z) (l : list SByte),
        z <= k <= z + Zlength l - 1 ->
        exists v, list_nth_z l (k - z) = Some v.
    Proof.
      intros.
      apply range_list_nth_z; lia.
    Qed.

    Lemma add_all_index_twice : forall (l1 l2 : list SByte) z bytes, 
        Zlength l1 = Zlength l2 ->
        Equal (add_all_index l2 z (add_all_index l1 z bytes))
              (add_all_index l2 z bytes).
    Proof.
      intros * EQ k.
      destruct (@key_in_range_or_not k z l2) as [IN | OUT].
      - destruct (in_range_is_in _ IN) as [? LU].
        erewrite 2 lookup_add_all_index_in; eauto.
      - rewrite 3 lookup_add_all_index_out; eauto.
        rewrite EQ; auto.
    Qed.

    Global Instance Proper_add {a} : Proper (Logic.eq ==> Logic.eq ==> Equal ==> Equal) (@add a).
    Proof.
      repeat intro; subst.
      destruct (RelDec.rel_dec_p k y); [subst; rewrite 2 lookup_add_eq; auto | rewrite 2 lookup_add_ineq; auto].
    Qed.

    Global Instance Proper_add_logical : Proper (Logic.eq ==> equivlb ==> equivl ==> equivl) add.
    Proof.
      repeat intro; subst.
      destruct H1 as [DOM EQUIV].
      split.
      - intros k; destruct (RelDec.rel_dec_p k y); [subst; rewrite 2 member_add_eq; auto | rewrite 2 member_add_ineq; auto]; reflexivity.
      - intros k; destruct (RelDec.rel_dec_p k y); [subst; rewrite 2 lookup_add_eq; auto | rewrite 2 lookup_add_ineq; auto].
        intros v v' EQ1 EQ2; inv EQ1; inv EQ2; auto. 
        intros v v' EQ1 EQ2.
        eapply EQUIV; eauto.
    Qed.

    Global Instance Proper_add_logical_block :
      Proper (Logic.eq ==> equivlb ==> equiv ==> equiv) add_logical_block.
    Proof.
      repeat intro; subst.
      destruct x1 as ((mc,ml),s), y1 as ((mc',ml'),s'), H1 as (? & ? & EQ); cbn in *.
      split; [| split]; auto.
      rewrite EQ, H0.
      reflexivity.
    Qed.

    Global Instance Proper_LBlock : Proper (Logic.eq ==> Equal ==> Logic.eq ==> equivlb) LBlock.
    Proof.
      repeat intro; subst.
      constructor; auto.
    Qed.

    Lemma write_write :
      forall (m : memory_stack) (v1 v2 : dvalue) (a : addr) τ,
        dvalue_has_dtyp v1 τ ->
        dvalue_has_dtyp v2 τ ->
        equiv_sum equiv ('m1 <- write m a v1;; write m1 a v2) (write m a v2).
    Proof.
      intros * T1 T2.
      unfold write; cbn.
      flatten_goal; repeat flatten_hyp Heq; try inv_sum.
      reflexivity.
      cbn in *.
      rewrite get_logical_block_of_add_logical_block.
      cbn.
      rewrite add_all_index_twice.
      apply add_logical_block_add_logical_block.
      erewrite 2 Zlength_correct, 2 sizeof_serialized; eauto.
    Qed.

  End Memory_Stack_Theory.

  (** ** Memory Handler
      Implementation of the memory model per se as a memory handler to the [MemoryE] interface.
   *)
  Definition handle_memory {E} `{FailureE -< E} `{UBE -< E}: MemoryE ~> stateT memory_stack (itree E) :=
    fun _ e m =>
      match e with
      | MemPush =>
        ret (push_fresh_frame m, tt)

      | MemPop =>
        'm' <- lift_pure_err (free_frame m);;
        ret (m',tt)

      | Alloca t =>
        '(m',key) <- lift_pure_err (allocate m t);;
        ret (m', DVALUE_Addr (key,0))

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
          'm' <- lift_pure_err (write m ptr v);;
          ret (m', tt)
        | _ => raise ("Attemptingeto store to a non-address dvalue: " ++ (to_string dv))
        end

      | GEP t dv vs =>
        'dv' <- lift_pure_err (handle_gep t dv vs);;
        ret (m, dv')

      | ItoP x =>
        match x with
        | DVALUE_I64 i =>
          match concrete_address_to_logical (unsigned i) m with
          | None => raise ("Invalid concrete address " ++ (to_string x))
          | Some (b, o) => ret (m, DVALUE_Addr (b, o))
          end
        | DVALUE_I32 i =>
          match concrete_address_to_logical (unsigned i) m with
          | None => raise "Invalid concrete address "
          | Some (b, o) => ret (m, DVALUE_Addr (b, o))
          end
        | DVALUE_I8 i  =>
          match concrete_address_to_logical (unsigned i) m with
          | None => raise "Invalid concrete address"
          | Some (b, o) => ret (m, DVALUE_Addr (b, o))
          end
        | DVALUE_I1 i  =>
          match concrete_address_to_logical (unsigned i) m with
          | None => raise "Invalid concrete address"
          | Some (b, o) => ret (m, DVALUE_Addr (b, o))
          end
        | _            => raise "Non integer passed to ItoP"
        end

      (* TODO take integer size into account *)
      | PtoI t a =>
        match a, t with
        | DVALUE_Addr ptr, DTYPE_I sz =>
          let (cid, m') := concretize_block ptr m in
          'addr <- lift_undef_or_err ret (coerce_integer_to_int sz (cid + (snd ptr))) ;;
          ret (m', addr)
        | _, _ => raise "PtoI type error."
        end

      end.

  Definition handle_intrinsic {E} `{FailureE -< E} `{PickE -< E}: IntrinsicE ~> stateT memory_stack (itree E) :=
    fun _ e '(m, s) =>
      match e with
      | Intrinsic t name args =>
        (* Pick all arguments, they should all be unique. *)
        if string_dec name "llvm.memcpy.p0i8.p0i8.i32" then  (* FIXME: use reldec typeclass? *)
          match handle_memcpy args m with
          | inl err => raise err
          | inr m' => ret ((m', s), DVALUE_None)
          end
        else
          raise ("Unknown intrinsic: " ++ name)
      end.


  (* TODO: clean this up *)
  (* {E} `{failureE -< E} : IO ~> stateT memory (itree E)  *)
  (* Won't need to be case analysis, just passes through failure + debug *)
  (* Might get rid of this one *)
  (* This can't show that IO ∉ E :( *)
  (* Alternative 2: Fix order of effects

   Layer interpretors so that they each chain into the next. Have to
   do ugly matches everywhere :(.

   Split the difference:

   `{IO -< IO +' failureE +' debugE}

   Alternative 3: follow 2, and then use notations to make things better.

   Alternative 4: Extend itrees mechanisms with some kind of set operations.

   If you want to allow sums on the left of your handlers, you want
   this notion of an atomic handler / event, which is different from a
   variable or a sum...

   `{E +' F -< G}

   This seems too experimental to try to work out now --- chat with Li-yao about it.

   Alternative 2 might be the most straightforward way to get things working in the short term.

   We just want to get everything hooked together to build and test
   it. Then think about making the interfaces nicer. The steps to alt
   2, start with LLVM1 ordering as the basic default. Then each stage
   of interpretation peels off one, or reintroduces the same kind of
   events / changes it.


   *)
  Section PARAMS.
    Variable (E F G : Type -> Type).
    Context `{FailureE -< F} `{UBE -< F} `{PickE -< F}.
    Notation Effin := (E +' IntrinsicE +' MemoryE +' F).
    Notation Effout := (E +' F).

    Definition E_trigger {M} : forall R, E R -> (stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition F_trigger {M} : forall R, F R -> (stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition interp_memory_h := case_ E_trigger (case_ handle_intrinsic  (case_ handle_memory  F_trigger)).
    Definition interp_memory :
      itree Effin ~> stateT memory_stack (itree Effout) :=
      interp_state interp_memory_h.

    Section Structural_Lemmas.

      Lemma interp_memory_bind :
        forall (R S : Type) (t : itree Effin R) (k : R -> itree Effin S) m,
          interp_memory (ITree.bind t k) m ≅
                        ITree.bind (interp_memory t m) (fun '(m',r) => interp_memory (k r) m').
      Proof.
        intros.
        unfold interp_memory.
        setoid_rewrite interp_state_bind.
        apply eq_itree_clo_bind with (UU := Logic.eq).
        reflexivity.
        intros [] [] EQ; inv EQ; reflexivity.
      Qed.

      Lemma interp_memory_ret :
        forall (R : Type) g (x: R),
          interp_memory (Ret x: itree Effin R) g ≅ Ret (g,x).
      Proof.
        intros; apply interp_state_ret.
      Qed.

      Lemma interp_memory_vis_eqit:
        forall S X (kk : X -> itree Effin S) m
          (e : Effin X),
          interp_memory (Vis e kk) m ≅ ITree.bind (interp_memory_h e m) (fun sx => Tau (interp_memory (kk (snd sx)) (fst sx))).
      Proof.
        intros.
        unfold interp_memory.
        setoid_rewrite interp_state_vis.
        reflexivity.
      Qed.

      Lemma interp_memory_vis:
        forall m S X (kk : X -> itree Effin S) (e : Effin X),
          interp_memory (Vis e kk) m ≈ ITree.bind (interp_memory_h e m) (fun sx => interp_memory (kk (snd sx)) (fst sx)).
      Proof.
        intros.
        rewrite interp_memory_vis_eqit.
        apply eutt_eq_bind.
        intros ?; tau_steps; reflexivity.
      Qed.

      Lemma interp_memory_trigger:
        forall (m : memory_stack) X (e : Effin X),
          interp_memory (ITree.trigger e) m ≈ interp_memory_h e m.
      Proof.
        intros.
        unfold interp_memory.
        rewrite interp_state_trigger.
        reflexivity.
      Qed.

      Lemma interp_memory_bind_trigger_eqit:
        forall m S X (kk : X -> itree Effin S) (e : Effin X),
          interp_memory (ITree.bind (trigger e) kk) m ≅ ITree.bind (interp_memory_h e m) (fun sx => Tau (interp_memory (kk (snd sx)) (fst sx))).
      Proof.
        intros.
        unfold interp_memory.
        rewrite bind_trigger.
        setoid_rewrite interp_state_vis.
        reflexivity.
      Qed.

      Lemma interp_memory_bind_trigger:
        forall m S X
          (kk : X -> itree Effin S)
          (e : Effin X),
          interp_memory (ITree.bind (trigger e) kk) m ≈ ITree.bind (interp_memory_h e m) (fun sx => interp_memory (kk (snd sx)) (fst sx)).
      Proof.
        intros.
        rewrite interp_memory_bind_trigger_eqit.
        apply eutt_eq_bind.
        intros ?; tau_steps; reflexivity.
      Qed.

      Global Instance eutt_interp_memory {R} :
        Proper (eutt Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_memory R).
      Proof.
        repeat intro.
        unfold interp_memory.
        subst; rewrite H2.
        reflexivity.
      Qed.

      Lemma interp_memory_load :
        forall (m : memory_stack) (t : dtyp) (val : uvalue) (a : addr),
          read m a t = inr val ->
          interp_memory (trigger (Load t (DVALUE_Addr a))) m ≈ ret (m, val).
      Proof.
        intros m t val a Hval.
        rewrite interp_memory_trigger.
        cbn. rewrite Hval.
        reflexivity.
      Qed.

      Lemma interp_memory_trigger_store :
        forall (m m' : memory_stack) (t : dtyp) (val : dvalue) (a : addr),
          write m a val = inr m' ->
          interp_memory (trigger (Store (DVALUE_Addr a) val)) m ≈ ret (m', tt).
      Proof.
        intros m m' t val a Hwrite.
        rewrite interp_memory_trigger.
        cbn. rewrite Hwrite.
        cbn. rewrite bind_ret_l.
        reflexivity.
      Qed.

      Lemma lookup_all_add_all_app :
        forall (xs ys : list SByte) o bytes def,
          lookup_all_index o (Z.of_nat (List.length xs + List.length ys)) (add_all_index (xs ++ ys) o bytes) def = xs ++ lookup_all_index (o + Z.of_nat (List.length xs)) (Z.of_nat (List.length ys)) (add_all_index (xs ++ ys) o bytes) def.
      Proof.
      Abort.

      Lemma lookup_all_add_all :
        forall o bytes (sbytes : list SByte) def,
          lookup_all_index o (Z.of_nat (List.length sbytes)) (add_all_index sbytes o bytes) def = sbytes.
      Proof.
        intros o bytes sbytes def.
        induction sbytes.
        - reflexivity.
        - cbn in *.
      Abort.

      (* Lemma write_read : *)
      (*   forall (m m' : memory_stack) (t : dtyp) (val : dvalue) (a : addr), *)
      (*     write m a val = inr m' -> *)
      (*     read m' a t = inr (dvalue_to_uvalue val). *)
      (* Proof. *)
      (*   intros m m' t val a Hwrite. *)
      (*   unfold write in Hwrite. *)
      (*   unfold read. *)
      (*   destruct (get_logical_block m a) eqn:Hbk. *)
      (*   - destruct l eqn:Hl. destruct a as [b o]. *)
      (*     cbn in Hbk. *)
      (*     cbn in Hwrite. *)
      (*     inversion Hwrite. *)
      (*     cbn. *)

      (*     (* TODO: clean this up *) *)
      (*     epose proof get_logical_block_of_add_logical_block m (b, o). *)
      (*     unfold get_logical_block in H2. *)
      (*     rewrite H2. clear H2. *)

      (*     rewrite blah. *)
      (*     reflexivity. *)
      (*   - inversion Hwrite. *)
      (* Qed. *)

    End Structural_Lemmas.

  End PARAMS.

End Make.
