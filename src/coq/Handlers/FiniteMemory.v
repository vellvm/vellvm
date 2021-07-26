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
     Eq.Eq
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
     Utils.ListUtil
     Utils.IntMaps
     Utils.NMaps
     Syntax.LLVMAst
     Syntax.DynamicTypes
     Syntax.DataLayout
     Semantics.DynamicValues
     Semantics.Denotation
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Semantics.LLVMEvents.

Require Import Ceres.Ceres.

Import MonadNotation.
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
| is_supported_DTYPE_Packed_struct : forall fields, Forall is_supported fields -> is_supported (DTYPE_Packed_struct fields)
(* TODO: unclear if is_supported τ is good enough here. Might need to make sure it's a sized type *)
| is_supported_DTYPE_Vector : forall sz τ, is_supported τ -> is_supported (DTYPE_Vector sz τ)
.


(** ** Type of pointers
    Implementation of the notion of pointer used: an address and an offset.
 *)
Definition Iptr := Z. (* Integer pointer type (physical addresses) *)

Definition Provenance := N.
Definition AllocationId := option Provenance. (* None is wildcard *)

(* TODO: Should probably make this an NSet, but it gives universe inconsistency with Module addr *)
Definition Prov := option (list Provenance). (* Provenance *)

(* Does the provenance set pr allow for access to aid? *)
Definition access_allowed (pr : Prov) (aid : AllocationId) : bool
  := match pr with
     | None => true (* Wildcard can access anything. *)
     | Some prset =>
       match aid with
       | None => true (* Wildcard, can be accessed by anything. *)
       | Some aid =>
         existsb (N.eqb aid) prset
       end
     end.

Definition all_accesses_allowed (pr : Prov) (aids : list AllocationId) : bool
  := forallb (access_allowed pr) aids.

Definition aid_access_allowed (pr : AllocationId) (aid : AllocationId) : bool
  := match pr with
     | None => true
     | Some pr =>
       match aid with
       | None => true
       | Some aid =>
         N.eqb pr aid
       end
     end.

Definition all_aid_accesses_allowed (pr : AllocationId) (aids : list AllocationId) : bool
  := forallb (aid_access_allowed pr) aids.

Definition wildcard_prov : Prov := None.
Definition nil_prov : Prov := Some [].

(* TODO: If Prov is an NSet, I get a universe inconsistency here... *)
Module Addr : MemoryAddress.ADDRESS with Definition addr := (Iptr * Prov) % type.
  Definition addr := (Iptr * Prov) % type.
  Definition null : addr := (0, nil_prov)%Z.
  Definition t := addr.

  (* TODO: is this what we should be using for equality on pointers? Probably *NOT* because of provenance. *)
  Lemma eq_dec : forall (a b : addr), {a = b} + {a <> b}.
  Proof.
    intros [a1 a2] [b1 b2].

    destruct (Z.eq_dec a1 b1);
      destruct (option_eq (fun x y => list_eq_dec N.eq_dec x y) a2 b2); subst.
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

  Variable ptr_size : nat.
  Variable datalayout : DataLayout.

  Definition addr := Addr.addr.
  
  Inductive SByte :=
  | UByte (uv : uvalue) (dt : dtyp) (idx : uvalue) (sid : store_id) : SByte.

  Definition endianess : Endianess
    := dl_endianess datalayout.

  Section Datatype_Definition.

    (* Memory consists of bytes which have a provenance associated with them. *)
    Definition mem_byte := (SByte * AllocationId)%type.

    (** ** Memory
        Memory is just a map of blocks.
     *)
    Definition memory := IntMap mem_byte.

    (** ** Stack frames
      A frame contains the list of block ids that need to be freed when popped,
      i.e. when the function returns.
      A [frame_stack] is a list of such frames.
     *)
    Definition mem_frame := list Provenance.
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

    (** ** Reading values in memory
      Given an offset in [mem_block], we decode a [uvalue] at [dtyp] [t] by looking up the
      appropriate number of [SByte] and deserializing them.
     *)

  (* Given a little endian list of bytes, match the endianess of `e` *)
  Definition correct_endianess {BYTES : Type} (e : Endianess) (bytes : list BYTES)
    := match e with
       | ENDIAN_BIG => rev bytes
       | ENDIAN_LITTLE => bytes
       end.

  (* Converts an integer [x] to its byte representation over [n] bytes.
     The representation is little endian. In particular, if [n] is too small,
     only the least significant bytes are returned.
   *)
  Fixpoint bytes_of_int_little_endian (n: nat) (x: Z) {struct n}: list byte :=
    match n with
    | O => nil
    | S m => Byte.repr x :: bytes_of_int_little_endian m (x / 256)
    end.

  Definition bytes_of_int (e : Endianess) (n : nat) (x : Z) : list byte :=
    correct_endianess e (bytes_of_int_little_endian n x).

  (*
  Definition sbytes_of_int (e : Endianess) (count:nat) (z:Z) : list SByte :=
    List.map Byte (bytes_of_int e count z). *)

    (** ** Size of a dynamic type
      Computes the byte size of a [dtyp]. *)
    Fixpoint sizeof_dtyp (ty:dtyp) : N :=
      match ty with
      | DTYPE_I 1          => 1 (* TODO: i1 sizes... *)
      | DTYPE_I 8          => 1
      | DTYPE_I 32         => 4
      | DTYPE_I 64         => 8
      | DTYPE_I _          => 0 (* Unsupported integers *)
      | DTYPE_IPTR         => N.of_nat ptr_size
      | DTYPE_Pointer      => N.of_nat ptr_size
      | DTYPE_Packed_struct l
      | DTYPE_Struct l     => fold_left (fun acc x => (acc + sizeof_dtyp x)%N) l 0%N
      | DTYPE_Vector sz ty'
      | DTYPE_Array sz ty' => sz * sizeof_dtyp ty'
      | DTYPE_Float        => 4
      | DTYPE_Double       => 8
      | DTYPE_Half         => 4
      | DTYPE_X86_fp80     => 10 (* TODO: Unsupported, currently modeled by Float32 *)
      | DTYPE_Fp128        => 16 (* TODO: Unsupported, currently modeled by Float32 *)
      | DTYPE_Ppc_fp128    => 16 (* TODO: Unsupported, currently modeled by Float32 *)
      | DTYPE_Metadata     => 0
      | DTYPE_X86_mmx      => 8 (* TODO: Unsupported *)
      | DTYPE_Opaque       => 0 (* TODO: Unsupported *)
      | _                  => 0 (* TODO: add support for more types as necessary *)
      end.

    Definition uvalue_bytes_little_endian (uv :  uvalue) (dt : dtyp) (sid : store_id) : list uvalue
      := map (fun n => UVALUE_ExtractByte uv dt (UVALUE_IPTR (Z.of_N n)) sid) (Nseq 0 ptr_size).
 
   Definition uvalue_bytes (e : Endianess) (uv :  uvalue) (dt : dtyp) (sid : store_id) : list uvalue
      := correct_endianess e (uvalue_bytes_little_endian uv dt sid).

    Definition to_ubytes (uv :  uvalue) (dt : dtyp) (sid : store_id) : list SByte
      := map (fun n => UByte uv dt (UVALUE_IPTR (Z.of_N n)) sid) (Nseq 0 (N.to_nat (sizeof_dtyp dt))).

    Definition ubyte_to_extractbyte (byte : SByte) : uvalue
      := match byte with
         | UByte uv dt idx sid => UVALUE_ExtractByte uv dt idx sid
         end.

    (* Is a uvalue a concrete integer equal to i? *)
    Definition uvalue_int_eq_Z (uv : uvalue) (i : Z)
      := match uv with
         | UVALUE_I1 x
         | UVALUE_I8 x
         | UVALUE_I32 x
         | UVALUE_I64 x => Z.eqb (unsigned x) i
         | UVALUE_IPTR x => Z.eqb x i
         | _ => false
         end.

    Definition dvalue_int_unsigned (dv : dvalue) : Z
      := match dv with
         | DVALUE_I1 x => unsigned x
         | DVALUE_I8 x => unsigned x
         | DVALUE_I32 x => unsigned x
         | DVALUE_I64 x => unsigned x
         | DVALUE_IPTR x => x (* TODO: unsigned???? *)
         | _ => 0
         end.

    Definition guard_opt (x : bool) : option unit
      := if x then Some tt else None.

    Fixpoint all_bytes_from_uvalue_helper (idx' : Z) (sid' : store_id) (parent : uvalue) (bytes : list SByte) : option uvalue
      := match bytes with
         | [] => Some parent
         | (UByte uv dt idx sid)::bytes =>
           guard_opt (uvalue_int_eq_Z idx idx');;
           guard_opt (RelDec.rel_dec uv parent);;
           guard_opt (N.eqb sid sid');;
           all_bytes_from_uvalue_helper (Z.succ idx') sid' parent bytes
         end.

    Definition all_bytes_from_uvalue (bytes : list SByte) : option uvalue
      := match bytes with
         | nil => None
         | cons (UByte uv dt idx sid) xs =>
           all_bytes_from_uvalue_helper 0 sid uv bytes
         end.

    (* TODO: move this *)
    Definition dtyp_eqb (dt1 dt2 : dtyp) : bool
      := match @dtyp_eq_dec dt1 dt2 with
         | left x => true
         | right x => false
         end.

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
        | _, _ => UVALUE_ConcatBytes (map ubyte_to_extractbyte bytes) dt
        end.

    (* TODO: move to utils? *)
    Definition from_option {A} (def : A) (opt : option A) : A
      := match opt with
         | Some x => x
         | None => def
         end.

    Definition fp_alignment (bits : N) : option Alignment :=
      let fp_map := dl_floating_point_alignments datalayout
      in NM.find bits fp_map.

    Definition option_pick_large {A} (leq : A -> A -> bool) (a b : option A) : option A
      := match a, b with
         | Some x, Some y =>
           if leq x y then b else a
         | Some a, _      => Some a
         | _, Some b      => Some b
         | None, None     => None
         end.

    Definition option_pick_small {A} (leq : A -> A -> bool) (a b : option A) : option A
      := match a, b with
         | Some x, Some y =>
           if leq x y then a else b
         | Some a, _      => Some a
         | _, Some b      => Some b
         | None, None     => None
         end.

    Definition maximumBy {A} (leq : A -> A -> bool) (def : A) (l : list A) : A :=
      fold_left (fun a b => if leq a b then b else a) l def.

    Definition maximumByOpt {A} (leq : A -> A -> bool) (l : list A) : option A :=
      fold_left (option_pick_large leq) (map Some l) None.

    Definition nextLargest {A} (leq : A -> A -> bool) (n : A) (def : A) (l : list A) : A :=
      fold_left (fun a b => if leq n a && leq a b then a else b) l def.

    Definition nextOrMaximum {A} (leq : A -> A -> bool) (n : A) (def : A) (l : list A) : A :=
      let max := maximumBy leq def l
      in fold_left (fun a b => if leq n b && leq a b then a else b) l max.

    Definition nextOrMaximumOpt {A} (leq : A -> A -> bool) (n : A) (l : list A) : option A :=
      let max := maximumByOpt leq l
      in fold_left (fun a b => if leq n b then option_pick_small leq a (Some b) else a) l max.

    Definition int_alignment (bits : N) : option Alignment :=
      let int_map := dl_integer_alignments datalayout
      in match NM.find bits int_map with
         | Some align => Some align
         | None =>
           let keys  := map fst (NM.elements int_map) in
           let bits' := nextOrMaximumOpt N.leb bits keys 
           in match bits' with
              | Some bits => NM.find bits int_map
              | None => None
              end
         end.

    (* TODO: Finish this function *)
    (* Fixpoint dtyp_alignment (dt : dtyp) : option Alignment := *)
    (*   match dt with *)
    (*   | DTYPE_I sz => *)
    (*     int_alignment sz *)
    (*   | DTYPE_IPTR => *)
    (*     (* TODO: should these have the same alignments as pointers? *) *)
    (*     int_alignment (N.of_nat ptr_size * 4)%N *)
    (*   | DTYPE_Pointer => *)
    (*     (* TODO: address spaces? *) *)
    (*     Some (ps_alignment (head (dl_pointer_alignments datalayout))) *)
    (*   | DTYPE_Void => *)
    (*     None *)
    (*   | DTYPE_Half => *)
    (*     fp_alignment 16 *)
    (*   | DTYPE_Float => *)
    (*     fp_alignment 32 *)
    (*   | DTYPE_Double => *)
    (*     fp_alignment 64 *)
    (*   | DTYPE_X86_fp80 => *)
    (*     fp_alignment 80 *)
    (*   | DTYPE_Fp128 => *)
    (*     fp_alignment 128 *)
    (*   | DTYPE_Ppc_fp128 => *)
    (*     fp_alignment 128 *)
    (*   | DTYPE_Metadata => *)
    (*     None *)
    (*   | DTYPE_X86_mmx => _ *)
    (*   | DTYPE_Array sz t => *)
    (*     dtyp_alignment t *)
    (*   | DTYPE_Struct fields => _ *)
    (*   | DTYPE_Packed_struct fields => _ *)
    (*   | DTYPE_Opaque => _ *)
    (*   | DTYPE_Vector sz t => _ *)
    (*   end. *)

    Definition dtyp_extract_fields (dt : dtyp) : err (list dtyp)
      := match dt with
         | DTYPE_Struct fields
         | DTYPE_Packed_struct fields =>
           ret fields
         | DTYPE_Array sz t
         | DTYPE_Vector sz t =>
           ret (repeat t (N.to_nat sz))
         | _ => inl "No fields."
         end.

    Definition extract_byte_to_ubyte (uv : uvalue) : err SByte
      := match uv with
         | UVALUE_ExtractByte uv dt idx sid =>
           ret (UByte uv dt idx sid)
         | _ => inl "extract_byte_to_ubyte invalid conversion."
         end.

    Import StateMonad.
    (* Need failure, UB, state for store_ids, and state for provenances *)
    Definition ErrSID := eitherT string (eitherT string (stateT store_id (state Provenance))).

    Definition lift_err {M A} `{MonadExc string M} `{Monad M} (e : err A) : (M A)
        := match e with
         | inl e => MonadExc.raise e
         | inr x => ret x
         end.

    Definition evalErrSID {A} (m : ErrSID A) (sid : store_id) (prov : Provenance) : err (err A)
      := evalState (evalStateT (unEitherT (unEitherT m)) sid) prov.

    Definition fresh_sid : ErrSID store_id
      := lift (lift (modify N.succ)).

    Definition fresh_provenance : ErrSID Provenance
      := lift (lift (lift (modify N.succ))).

    Definition fresh_allocation_id : ErrSID AllocationId
      := prov <- fresh_provenance;;
         ret (Some prov).

    Definition raise_error {A} (msg : string) : ErrSID A
      := MonadExc.raise msg.

    Definition raise_ub {A} (msg : string) : ErrSID A
      := lift (MonadExc.raise msg).


    Definition sbyte_sid_match (a b : SByte) : bool
      := match a, b with
         | UByte uv dt idx sid, UByte uv' dt' idx' sid' =>
           N.eqb sid sid'
         end.

    Definition replace_sid (sid : store_id) (ub : SByte) : SByte
      := let '(UByte uv dt idx sid_old) := ub in
         UByte uv dt idx sid.

    Definition filter_sid_matches (byte : SByte) (sbytes : list (N * SByte)) : (list (N * SByte) * list (N * SByte))
      := filter_split (fun '(n, uv) => sbyte_sid_match byte uv) sbytes.

    (* TODO: move to some utility file? *)
    Fixpoint NM_find_many {A} (xs : list N) (nm : NMap A) : option (list A)
      := match xs with
         | [] => ret []
         | (x::xs) =>
           elt  <- NM.find x nm;;
           elts <- NM_find_many xs nm;;
           ret (elt :: elts)
         end.

    (* TODO: move to some utility file? *)
    Fixpoint IM_find_many {A} (xs : list Z) (im : IntMap A) : option (list A)
      := match xs with
         | [] => ret []
         | (x::xs) =>
           elt  <- IM.find x im;;
           elts <- IM_find_many xs im;;
           ret (elt :: elts)
         end.

    (* Assign fresh sids to ubytes while preserving entanglement *)
    Unset Guard Checking.
    Fixpoint re_sid_ubytes_helper (bytes : list (N * SByte)) (acc : NMap SByte) {struct bytes} : ErrSID (NMap SByte)
      := match bytes with
         | [] => ret acc
         | ((n, x)::xs) =>
           let '(UByte uv dt idx sid) := x in
           let '(ins, outs) := filter_sid_matches x xs in
           nsid <- fresh_sid;;
           let acc := @NM.add _ n (replace_sid nsid x) acc in
           (* Assign new sid to entangled bytes *)
           let acc := fold_left (fun acc '(n, ub) => @NM.add _ n (replace_sid nsid ub) acc) ins acc in
           re_sid_ubytes_helper outs acc
         end
    with
    re_sid_ubytes (bytes : list SByte) : ErrSID (list SByte)
      := let len := length bytes in
         byte_map <- re_sid_ubytes_helper (zip (Nseq 0 len) bytes) (@NM.empty _);;
         trywith "re_sid_ubytes: missing indices." (NM_find_many (Nseq 0 len) byte_map). 
    Set Guard Checking.

    (* This is mostly to_ubytes, except it will also unwrap concatbytes *)
  Fixpoint serialize_sbytes (uv : uvalue) (dt : dtyp) {struct uv} : ErrSID (list SByte)
    := match uv with
       (* Base types *)
       | UVALUE_Addr _
       | UVALUE_I1 _
       | UVALUE_I8 _
       | UVALUE_I32 _
       | UVALUE_I64 _
       | UVALUE_IPTR _
       | UVALUE_Float _
       | UVALUE_Double _
       | UVALUE_Undef _
       | UVALUE_Poison

       (* Padded aggregate types *)
       | UVALUE_Struct _

       (* Packed aggregate types *)
       | UVALUE_Packed_struct _
       | UVALUE_Array _
       | UVALUE_Vector _

       (* Expressions *)
       | UVALUE_IBinop _ _ _
       | UVALUE_ICmp _ _ _
       | UVALUE_FBinop _ _ _ _
       | UVALUE_FCmp _ _ _
       | UVALUE_Conversion _ _ _
       | UVALUE_GetElementPtr _ _ _
       | UVALUE_ExtractElement _ _
       | UVALUE_InsertElement _ _ _
       | UVALUE_ShuffleVector _ _ _
       | UVALUE_ExtractValue _ _
       | UVALUE_InsertValue _ _ _
       | UVALUE_Select _ _ _ =>
         sid <- fresh_sid;;
         ret (to_ubytes uv dt sid)

       | UVALUE_None => ret nil

       (* Byte manipulation. *)
       | UVALUE_ExtractByte uv dt' idx sid =>
         raise_error "serialize_sbytes: UVALUE_ExtractByte not guarded by UVALUE_ConcatBytes."
       | UVALUE_ConcatBytes bytes t =>
         (* TODO: should provide *new* sids... May need to make this function in a fresh sid monad *)
         bytes' <- lift_err (map_monad extract_byte_to_ubyte bytes);;
         re_sid_ubytes bytes'
       end.

  (* deserialize_sbytes takes a list of SBytes and turns them into a uvalue.

     This relies on the similar, but different, from_ubytes function
     which given a set of bytes checks if all of the bytes are from
     the same uvalue, and if so returns the original uvalue, and
     otherwise returns a UVALUE_ConcatBytes value instead.

     The reason we also have deserialize_sbytes is in order to deal
     with aggregate data types.
   *)
  Definition deserialize_sbytes (bytes : list SByte) (dt : dtyp) : err uvalue
    :=
      match dt with
       (* Base types *)
       | DTYPE_I _
       | DTYPE_IPTR
       | DTYPE_Pointer
       | DTYPE_Half
       | DTYPE_Float
       | DTYPE_Double
       | DTYPE_X86_fp80
       | DTYPE_Fp128
       | DTYPE_Ppc_fp128
       | DTYPE_X86_mmx
       | _ =>
         ret (from_ubytes bytes dt)
      end.

       (* serialize_sbytes does not take aggregate structures into
          account. We just extract individual bytes from aggregate
          uvalues. This was necessary for dealing with endianess and
          expressions which yield aggregate structures.

          That said, it would still be nice to be able to edit elements of
          arrays / structures and be able to load them back...

        *)

       (* TODO: should we bother with this? *)
       (* Array and vector types *)
       (* | DTYPE_Array sz t => *)
       (*   let size := sizeof_dtyp t in *)
       (*   let size_nat := N.to_nat size in *)
       (*   fields <- monad_fold_right (fun acc idx => uv <- deserialize_sbytes (between (idx*size) ((idx+1) * size) bytes) t;; ret (uv::acc)) (Nseq 0 size_nat) [];; *)
       (*   ret (UVALUE_Array fields) *)
       (* | DTYPE_Vector sz t => *)
       (*   let size := sizeof_dtyp t in *)
       (*   let size_nat := N.to_nat size in *)
       (*   fields <- monad_fold_right (fun acc idx => uv <- deserialize_sbytes (between (idx*size) ((idx+1) * size) bytes) t;; ret (uv::acc)) (Nseq 0 size_nat) [];; *)
       (*   ret (UVALUE_Vector fields) *)

       (* (* Padded aggregate types *) *)
       (* | DTYPE_Struct fields => *)
       (*   (* TODO: Add padding *) *)
       (*   match fields with *)
       (*   | [] => ret (UVALUE_Struct []) (* TODO: Not 100% sure about this. *) *)
       (*   | (dt::dts) => *)
       (*     let sz := sizeof_dtyp dt in *)
       (*     let init_bytes := take sz bytes in *)
       (*     let rest_bytes := drop sz bytes in *)
       (*     f <- deserialize_sbytes init_bytes dt;; *)
       (*     rest <- deserialize_sbytes rest_bytes (DTYPE_Struct dts);; *)
       (*     match rest with *)
       (*     | UVALUE_Struct fs => *)
       (*       ret (UVALUE_Struct (f::fs)) *)
       (*     | _ => *)
       (*       raise "deserialize_sbytes: DTYPE_Struct recursive call did not return a struct." *)
       (*     end *)
       (*   end *)

       (*   (* match fields with *) *)
       (*   (* | [] => ret (DVALUE_Struct []) *) *)
       (*   (* | (x::xs) => _ *) *)
       (*   (* end *) *)
       (*   (* inl "deserialize_sbytes: padded structures unimplemented." *) *)

       (* (* Structures with no padding *) *)
       (* | DTYPE_Packed_struct fields => *)
         
       (*   inl "deserialize_sbytes: unimplemented packed structs." *)

       (* (* Unimplemented *) *)
       (* | DTYPE_Void => *)
       (*   inl "deserialize_sbytes: attempting to deserialize void." *)
       (* | DTYPE_Metadata => *)
       (*   inl "deserialize_sbytes: metadata." *)

       (* | DTYPE_Opaque => *)
       (*   inl "deserialize_sbytes: opaque." *)
       (* end. *)

(* (* TODO: *)

(*   What is the difference between a pointer and an integer...? *)

(*   Primarily, it's that pointers have provenance and integers don't? *)

(*   So, if we do PVI is there really any difference between an address *)
(*   and an integer, and should we actually distinguish between them? *)

(*   Provenance in UVALUE_IPTR probably means we need provenance in *all* *)
(*   data types... i1, i8, i32, etc, and even doubles and floats... *)
(*  *) *)
  
(* (* TODO: *)

(*    Should uvalue have something like... UVALUE_ExtractByte which *)
(*    extracts a certain byte out of a uvalue? *)

(*    Will probably need an equivalence relation on UVALUEs, likely won't *)
(*    end up with a round-trip property with regular equality... *)
(* *) *)

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
            handle_gep_h ta (off + k * (Z.of_N (sizeof_dtyp ta))) vs'
          | DTYPE_Struct ts
          | DTYPE_Packed_struct ts => (* Handle these differently in future *)
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
          | DTYPE_Vector _ ta
          | DTYPE_Array _ ta =>
            handle_gep_h ta (off + k * (Z.of_N (sizeof_dtyp ta))) vs'
          | _ => failwith ("non-i8-indexable type")
          end
        | DVALUE_I64 i =>
          let k := unsigned i in
          let n := BinIntDef.Z.to_nat k in
          match t with
          | DTYPE_Vector _ ta
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
      let '(ptr, prov) := a in
      match vs with
      | DVALUE_I32 i :: vs' => (* TODO: Handle non i32 / i64 indices *)
        ptr' <- handle_gep_h t (ptr + Z.of_N (sizeof_dtyp t) * (unsigned i)) vs' ;;
        ret (ptr', prov)
      | DVALUE_I64 i :: vs' =>
        ptr' <- handle_gep_h t (ptr + Z.of_N (sizeof_dtyp t) * (unsigned i)) vs' ;;
        ret (ptr', prov)
      | _ => failwith "non-I32 index"
      end.

    Definition handle_gep (t:dtyp) (dv:dvalue) (vs:list dvalue) : err dvalue :=
      match dv with
      | DVALUE_Addr a => fmap DVALUE_Addr (handle_gep_addr t a vs)
      | _ => failwith "non-address"
      end.

  End GEP.

  Section Logical_Operations.

    Definition memory_empty : memory := empty.

    (*  TODO: Is DTYPE_Void fine here? *)
    Definition SUndef : ErrSID SByte :=
      sid <- fresh_sid;;
      ret (UByte (UVALUE_Undef DTYPE_Void) DTYPE_Void (UVALUE_IPTR 0) sid).

    (** ** Reading values from memory *)
    Definition read_memory (mem : memory) (addr : Z) (pr : Prov) (t : dtyp) : ErrSID uvalue :=
      sid <- fresh_sid;;
      let mem_bytes := lookup_all_index addr (sizeof_dtyp t) mem ((UByte (UVALUE_Undef t) t (UVALUE_IPTR 0) sid), None) in
      let bytes     := map fst mem_bytes in
      let alloc_ids := map snd mem_bytes in
      if all_accesses_allowed pr alloc_ids
      then lift_err (deserialize_sbytes bytes t)
      else raise_ub "Read to memory with different provenance.".


    (** ** Writing values to memory
      Serialize [v] into [SByte]s, and store them in the [memory] starting at [addr].

      Also make sure that the write of provenance [pr] is allowed.
     *)
    Definition write_allowed (mem : memory) (addr : Z) (aid : AllocationId) (dt : dtyp) : ErrSID unit
      :=
        let mem_bytes := IM_find_many (Zseq 0 (N.to_nat (sizeof_dtyp dt))) mem in
        match mem_bytes with
        | None => raise_ub "Trying to write to unallocated memory."
        | Some mem_bytes =>
          let alloc_ids := map snd mem_bytes in
          if all_aid_accesses_allowed aid alloc_ids
          then ret tt
          else raise_ub "Trying to write to memory with invalid provenance."
        end.

    Definition write_memory (mem : memory) (addr : Z) (aid : AllocationId) (v : uvalue) (dt : dtyp) : ErrSID memory
      :=
        (* Check that we're allowed to write to each place in memory *)
        write_allowed mem addr aid dt;;
        bytes <- serialize_sbytes v dt;;
        let mem_bytes := map (fun b => (b, aid)) bytes in

        (* TODO: should we allow provenance to change like this when access is allowed...? *)
        ret (add_all_index mem_bytes (Z.of_N (sizeof_dtyp dt)) mem).

    (** ** Array element lookup
      A [memory] can be seen as storing an array of elements of [dtyp] [t], from which we retrieve
      the [i]th [uvalue].
      The [size] argument has no effect, but we need to provide one to the array type.
     *)
    Definition get_array_cell_memory (mem : memory) (addr : Z) (pr : Prov) (i : nat) (size : N) (t : dtyp) : ErrSID uvalue :=
      'offset <- lift_err (handle_gep_h (DTYPE_Array size t)
                                       addr
                                       [DVALUE_I64 (DynamicValues.Int64.repr (Z.of_nat i))]);;
      read_memory mem offset pr t.

    (** ** Array element writing
      Treat a [memory] as though it is an array storing elements of
      type [t], and write the value [v] to index [i] in this array.

      - [t] should be the type of [v].
      - [size] does nothing, but we need to provide one for the array type.
    *)
    Definition write_array_cell_memory (mem : memory) (addr : Z) (aid : AllocationId) (i : nat) (size : N) (t : dtyp) (v : uvalue) : ErrSID memory :=
      'offset <- lift_err (handle_gep_h (DTYPE_Array size t)
                                       addr
                                       [DVALUE_I64 (DynamicValues.Int64.repr (Z.of_nat i))]);;
      write_memory mem offset aid v t.

    (** ** Array lookups -- mem_block
      Retrieve the values stored at position [from] to position [from + len - 1] in an array stored in a [memory].
     *)
    Definition get_array_memory (mem : memory) (addr : Z) (pr : Prov) (from len : nat) (size : N) (t : dtyp) : ErrSID (list uvalue) :=
      map_monad (fun i => get_array_cell_memory mem addr pr i size t) (seq from len).

    (** ** Array writes -- mem_block
      Write all of the values in [vs] to an array stored in a [memory], starting from index [from].

      - [t] should be the type of each [v] in [vs]
     *)
    Fixpoint write_array_memory' (mem : memory) (addr : Z) (aid : AllocationId) (i : nat) (size : N) (t : dtyp) (vs : list uvalue) : ErrSID memory :=
      match vs with
      | []       => ret mem
      | (v :: vs) =>
        mem' <- write_array_cell_memory mem addr aid i size t v;;
        write_array_memory' mem' addr aid (S i) size t vs
      end.

    Definition write_array_mem_block (mem : memory) (addr : Z) (aid : AllocationId) (from : nat) (t : dtyp) (vs : list uvalue) : ErrSID memory :=
      let size := (N.of_nat (length vs)) in
      write_array_memory' mem addr aid from size t vs.

  End Logical_Operations.


  Section Memory_Operations.

    (** Check if the block for an address is allocated.

        Note: This does not check that the address is in range of the
        block. *)
    (* TODO: should this check if everything is in range...? *)
    Definition allocated (a : addr) (m : memory_stack) : Prop :=
      member (fst a) (fst m).

    (** Do two memory regions overlap each other?

        - *a1* and *a2* are addresses to the start of each region.
        - *sz1* and *sz2* are the sizes of the two regions.

        Proposition should hold whenever the two regions overlap each
        other. *)
    Definition overlaps (a1 : addr) (sz1 : Z) (a2 : addr) (sz2 : Z) : Prop :=
      let a1_start := fst a1 in
      let a1_end   := fst a1 + sz1 in
      let a2_start := fst a2 in
      let a2_end   := fst a2 + sz2 in
      a1_start <= (a2_end - 1) /\ a2_start <= (a1_end - 1).

    (** Checks if two regions of memory overlap each other. The types
        *τ1* and *τ2* are used to determine the size of the two memory
        regions.
     *)
    Definition overlaps_dtyp (a1 : addr) (τ1 : dtyp) (a2 : addr) (τ2 : dtyp)
      : Prop :=
      overlaps a1 (Z.of_N (sizeof_dtyp τ1)) a2 (Z.of_N (sizeof_dtyp τ2)).

    (** Make sure that two regions of memory do not overlap *)
    Definition no_overlap (a1 : addr) (sz1 : Z) (a2 : addr) (sz2 : Z) : Prop :=
      let a1_start := fst a1 in
      let a1_end   := fst a1 + sz1 in
      let a2_start := fst a2 in
      let a2_end   := fst a2 + sz2 in
      a1_start > (a2_end - 1) \/ a2_start > (a1_end - 1).

    (** Same as *no_overlap*, but using *dtyp*s *τ1* and *τ2* to
        determine the size of the regions. *)
    Definition no_overlap_dtyp (a1 : addr) (τ1 : dtyp) (a2 : addr) (τ2 : dtyp)
      : Prop :=
      no_overlap a1 (Z.of_N (sizeof_dtyp τ1)) a2 (Z.of_N (sizeof_dtyp τ2)).

    (** Boolean version of *no_overlap* *)
    Definition no_overlap_b (a1 : addr) (sz1 : Z) (a2 : addr) (sz2 : Z) : bool :=
      let a1_start := fst a1 in
      let a1_end   := fst a1 + sz1 in
      let a2_start := fst a2 in
      let a2_end   := fst a2 + sz2 in
      (a1_start >? (a2_end - 1)) || (a2_start >? (a1_end - 1)).

      (* LLVM 5.0 memcpy
         According to the documentation: http://releases.llvm.org/5.0.0/docs/LangRef.html#llvm-memcpy-intrinsic
         this operation can never fail?  It doesn't return any status code...
       *)

      (** ** MemCopy
          Implementation of the [memcpy] intrinsics.
       *)
      Definition handle_memcpy (args : list dvalue) (m:memory) : err memory :=
        match args with
        | DVALUE_Addr (dst_id, dst_prov) ::
                      DVALUE_Addr (src_id, src_prov) ::
                      DVALUE_I32 len ::
                      DVALUE_I32 align :: (* alignment ignored *)
                      DVALUE_I1 volatile :: [] (* volatile ignored *)  =>

          let mem_block_size := unsigned len in
          (* From LLVM Docs : The 'llvm.memcpy.*' intrinsics copy a block of
             memory from the source location to the destination location,
             which are not allowed to overlap. *)
          if (no_overlap_b (dst_id, dst_prov) mem_block_size
                                 (src_id, src_prov) mem_block_size) then
            (* No guarantee that src_block has a certain size. *)
            src_block <- trywith "memcpy src block not found"
                                (lookup src_id m) ;;
            dst_block <- trywith "memcpy dst block not found"
                                (lookup dst_id m) ;;

            let src_bytes
                := match src_block with
                  | Block size bytes => bytes
                  end in
            let '(dst_sz, dst_bytes)
                := match dst_block with
                  | Block size bytes => (size, bytes)
                  end in

            (* IY: What happens if [src_block_size < mem_block_size]?
               Since we have logical blocks, there isn't a way to get around
               this, and SUndef is invoked. Is this desired behavior? *)
            let sdata := lookup_all_index src_prov (Z.to_N (unsigned len)) src_bytes SUndef in
            let dst_bytes' := add_all_index sdata dst_prov dst_bytes in
            let dst_block' := Block dst_sz dst_bytes' in
            let m' := IM.add dst_id dst_block' m in
            (ret m' : err memory)
          (* IY: For now, we're returning a "failwith". Maybe it's more ideal
             to return an "UNDEF" here? *)
          else failwith "memcpy has overlapping src and dst memory location"
        | _ => failwith "memcpy got incorrect arguments"
        end.

  End Memory_Operations.

  Section Frame_Stack_Operations.

    (* The initial frame stack is not an empty stack, but a singleton stack containing an empty frame *)
    Definition frame_empty : frame_stack := Singleton [].

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
        bk' <- write_array_mem_block bk o from τ vs;;
        let block' := LBlock sz bk' cid in
        ret (add_logical_block b block' m)
      | None => failwith "Memory function [write_array] called at a non-allocated address"
      end.

    Definition write_array_cell (m : memory_stack) (a : addr) (i : nat) (τ : dtyp) (v : dvalue) : err memory_stack :=
      let '(b, o) := a in
      match get_logical_block m b with
      | Some (LBlock sz bk cid) =>
        bk' <- write_array_cell_mem_block bk o i 0 τ v;;
        let block' := LBlock sz bk' cid in
        ret (add_logical_block b block' m)
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
      match t with
      | DTYPE_Void => failwith "Allocation of type void"
      | _ =>
        let new_block := make_empty_logical_block t in
        let key       := next_logical_key m in
        let m         := add_logical_block key new_block m in
        ret (add_to_frame m key, (key,0))
      end.

    (* TODO: very similar to overlaps *)
    Definition dtyp_fits (m : memory_stack) (a : addr) (τ : dtyp) :=
      exists sz bytes cid,
        get_logical_block m (fst a) = Some (LBlock sz bytes cid) /\
        snd a + (Z.of_N (sizeof_dtyp τ)) <= Z.of_N sz.

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

    Definition concrete_address_to_logical (cid : Z) (m : memory_stack) : option (Z * Z) :=
      concrete_address_to_logical_mem cid (fst m).

    Definition concretize_block (ptr : addr) (m : memory_stack) : Z * memory_stack :=
      let '(b', m') := concretize_block_mem (fst ptr) (fst m) in
      (b', (m', snd m)).

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
        'm' <- lift_pure_err (free_frame m);;
        ret (m',tt)

      | Alloca t =>
        '(m',a) <- lift_pure_err (allocate m t);;
        ret (m', DVALUE_Addr a)

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
        | _ => raise ("Attempting to store to a non-address dvalue: " ++ (to_string dv))
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
        | DVALUE_IPTR i =>
          match concrete_address_to_logical i m with
          | None => raise "Invalid concrete address"
          | Some (b, o) => ret (m, DVALUE_Addr (b, o))
          end
        | _            => raise "Non integer passed to ItoP"
        end

      | PtoI t a =>
        match a, t with
        | DVALUE_Addr ptr, DTYPE_I sz =>
          let (cid, m') := concretize_block ptr m in
          'addr <- lift_undef_or_err ret (coerce_integer_to_int sz (cid + (snd ptr))) ;;
          ret (m', addr)
        | DVALUE_Addr ptr, DTYPE_IPTR =>
          let (cid, m') := concretize_block ptr m in
          ret (m', DVALUE_IPTR (cid + (snd ptr)))
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

  End PARAMS.

End Make.
