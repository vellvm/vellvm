From Vellvm Require Import
     Numeric.Coqlib
     Numeric.Integers
     Numeric.Floats
     Utils.Tactics
     Utils.Util
     Utils.Error
     Utils.ListUtil
     Utils.NonEmpty
     Syntax.LLVMAst
     Syntax.DynamicTypes
     Syntax.DataLayout
     Semantics.DynamicValues
     Semantics.Denotation
     Semantics.MemoryAddress
     Semantics.LLVMEvents.

Require Import ExtLib.Structures.Monad.

Import ListNotations.
Import MonadNotation.

Definition Iptr := Z. (* Integer pointer type (physical addresses) *)

(* TODO: this should probably be an NSet or something... *)
(* TODO: should there be a way to express nil / wildcard provenance? *)
Definition Prov := list N. (* Provenance *)

(* TODO: If Prov is an NSet, I get a universe inconsistency here... *)
Module Addr : MemoryAddress.ADDRESS with Definition addr := (Iptr * Prov) % type.
  Definition addr := (Iptr * Prov) % type.
  Definition null : addr := (0, nil)%Z.
  Definition t := addr.

  (* TODO: is this what we should be using for equality on pointers? Probably *NOT* because of provenance. *)
  Lemma eq_dec : forall (a b : addr), {a = b} + {a <> b}.
  Proof.
    intros [a1 a2] [b1 b2].

    destruct (Z.eq_dec a1 b1);
      destruct (list_eq_dec N.eq_dec a2 b2); subst.
    - left; reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
  Qed.
End Addr.

Module Make(LLVMEvents: LLVM_INTERACTIONS(Addr)).
  Import LLVMEvents.
  Import DV.
  Open Scope list.

  Definition addr := Addr.addr.

  Inductive SByte :=
  | Byte : byte -> SByte
  | IntPtr (phys_addr : addr) (byte_idx : N) : SByte (* Should store provenance as well... *)
  | SPoison : SByte
  | SUndef  : SByte.

  Variable ptr_size : nat.
  Variable datalayout : DataLayout.

  Definition endianess : Endianess
    := dl_endianess datalayout.

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

  Definition sbytes_of_int (e : Endianess) (count:nat) (z:Z) : list SByte :=
    List.map Byte (bytes_of_int e count z).

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
      | DTYPE_X86_fp80     => 4 (* TODO: Unsupported, currently modeled by Float32 *)
      | DTYPE_Fp128        => 4 (* TODO: Unsupported, currently modeled by Float32 *)
      | DTYPE_Ppc_fp128    => 4 (* TODO: Unsupported, currently modeled by Float32 *)
      | DTYPE_Metadata     => 0
      | DTYPE_X86_mmx      => 0 (* TODO: Unsupported *)
      | DTYPE_Opaque       => 0 (* TODO: Unsupported *)
      | _                  => 0 (* TODO: add support for more types as necessary *)
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

  Fixpoint serialize_sbytes (uv : uvalue) (dt : dtyp) : err (list SByte)
    := match uv with
       | UVALUE_Addr a =>
         ret (map (fun n => IntPtr a n) (Nseq 0 ptr_size))
       (* TODO: Not sure how i1s should be represented *)
       | UVALUE_I1 x =>
         ret (sbytes_of_int endianess 1 (unsigned x))
       | UVALUE_I8 x =>
         ret (sbytes_of_int endianess 1 (unsigned x))
       | UVALUE_I32 x =>
         ret (sbytes_of_int endianess 4 (unsigned x))
       | UVALUE_I64 x =>
         ret (sbytes_of_int endianess 8 (unsigned x))
       | UVALUE_IPTR x =>
         (* TODO: provenance in UVALUE_IPTR? *)
         ret (map (fun n => IntPtr (x, nil) n) (Nseq 0 ptr_size))
         (* This might be wrong... (Old implementation)

            1) Not unsigned, that might be bad...
            2) This serializes the integer value --- no provenance...
            3) Serializes to a certain size...

            I think (2) might be fine, that's part of the point of this...

            (3) is potentially a big issue, though.
          *)
       (* sbytes_of_int endianess ptr_size x *)
       | UVALUE_Float f => ret (sbytes_of_int endianess 4 (unsigned (Float32.to_bits f)))
       | UVALUE_Double d => ret (sbytes_of_int endianess 8 (unsigned (Float.to_bits d)))
       | UVALUE_Poison =>
         ret (repeat SPoison (N.to_nat (sizeof_dtyp dt)))
       | UVALUE_None => ret nil
       | UVALUE_Struct fields =>
         (* TODO: Structs WITH padding *)
         inl "Unimplemented"
       | UVALUE_Packed_struct fields
       | UVALUE_Array fields
       | UVALUE_Vector fields =>
         dts <- dtyp_extract_fields dt;;
         (* note the _right_ fold is necessary for byte ordering. *)
         fold_right (fun 'dv acc => ((serialize_sbytes dv) ++ acc) % list) [] (zip fields dts)
       | UVALUE_IBinop iop v1 v2 => _
       | UVALUE_ICmp cmp v1 v2 => _
       | UVALUE_FBinop fop fm v1 v2 => _
       | UVALUE_FCmp cmp v1 v2 => _
       | UVALUE_Conversion conv v t_to => _
       | UVALUE_GetElementPtr t ptrval idxs => _
       | UVALUE_ExtractElement vec idx => _
       | UVALUE_InsertElement vec elt idx => _
       | UVALUE_ShuffleVector vec1 vec2 idxmask => _
       | UVALUE_ExtractValue vec idxs => _
       | UVALUE_InsertValue vec elt idxs => _
       | UVALUE_Select cnd v1 v2 => _
       end.


(* TODO:

  What is the difference between a pointer and an integer...?

  Primarily, it's that pointers have provenance and integers don't?

  So, if we do PVI is there really any difference between an address
  and an integer, and should we actually distinguish between them?

  Provenance in UVALUE_IPTR probably means we need provenance in *all*
  data types... i1, i8, i32, etc, and even doubles and floats...
 *)
  
(* TODO:

   Should uvalue have something like... UVALUE_ExtractByte which
   extracts a certain byte out of a uvalue?

   Will probably need an equivalence relation on UVALUEs, likely won't
   end up with a round-trip property with regular equality...
*)
