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

From ExtLib Require Import
     Structures.Monads
     Data.Monads.EitherMonad.


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
  | UByte (uv : uvalue) (dt : dtyp) (idx : uvalue) (sid : store_id) : SByte.

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
      | DTYPE_X86_mmx      => 0 (* TODO: Unsupported *)
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

    Fixpoint all_extract_bytes_from_uvalue_helper (idx' : Z) (sid' : store_id) (parent : uvalue) (bytes : list uvalue) : option uvalue
      := match bytes with
         | [] => Some parent
         | (UVALUE_ExtractByte uv dt idx sid)::bytes =>
           guard_opt (uvalue_int_eq_Z idx idx');;
           guard_opt (RelDec.rel_dec uv parent);;
           guard_opt (N.eqb sid sid');;
           all_extract_bytes_from_uvalue_helper (Z.succ idx') sid' parent bytes
         | _ => None
         end.

    Definition all_extract_bytes_from_uvalue (bytes : list uvalue) : option uvalue
      := match bytes with
         | nil => None
         | (UVALUE_ExtractByte uv dt idx sid)::xs =>
           all_extract_bytes_from_uvalue_helper 0 sid uv bytes
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

    (* This is mostly to_ubytes, except it will also unwrap concatbytes *)
  Fixpoint serialize_sbytes (uv : uvalue) (dt : dtyp) (sid : store_id) {struct uv} : err (list SByte)
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
       | UVALUE_Struct fields
         =>
         ret (to_ubytes uv dt sid)
       | UVALUE_None => ret nil

       (* Padded aggregate types *)

         (* TODO: Structs WITH padding *)
         inl "Unimplemented"

       (* Packed aggregate types *)
       | UVALUE_Packed_struct fields
       | UVALUE_Array fields
       | UVALUE_Vector fields =>
         dts <- dtyp_extract_fields dt;;
         (* note the _right_ fold is necessary for byte ordering. *)
         monad_fold_right (fun acc '(uv, dt) => (bytes <- (serialize_sbytes uv dt);; ret (bytes ++ acc)) % list) (zip fields dts) []

       (* Byte manipulation. *)
       | UVALUE_ExtractByte uv idx sid =>
         inl "serialize_sbytes: UVALUE_ExtractByte not guarded by UVALUE_ConcatBytes."
       | UVALUE_ConcatBytes bytes t =>
         map_monad extract_byte_to_ubyte bytes

       (* Expressions *)
       (* TODO: this probably only works when the result is not an aggregate type...

          I believe select, for instance, can have an aggregate type
          as the result. Same with others...

          If it ends up being an aggregate type, then ExtractByte
          needs to understand the layout of aggregate types in order
          to understand which byte corresponds to what... Which is
          likely not ideal.

          For select result must be first class type... (This includes
          vectors, AND also arrays and structs): https://llvm.org/docs/LangRef.html#id1363

          Conversions must be ints or vectors...

          ExtractValue operates on structs... Can probably pull out struct types.

          Vectors must have elements of "primitive type"
        *)
       | _ =>
         inr (to_ubytes uv sid)
       (* | UVALUE_IBinop iop v1 v2 => _ *)
       (* | UVALUE_ICmp cmp v1 v2 => _ *)
       (* | UVALUE_FBinop fop fm v1 v2 => _ *)
       (* | UVALUE_FCmp cmp v1 v2 => _ *)
       (* | UVALUE_Conversion conv v t_to => _ *)
       (* | UVALUE_GetElementPtr t ptrval idxs => _ *)
       (* | UVALUE_ExtractElement vec idx => _ *)
       (* | UVALUE_InsertElement vec elt idx => _ *)
       (* | UVALUE_ShuffleVector vec1 vec2 idxmask => _ *)
       (* | UVALUE_ExtractValue vec idxs => _ *)
       (* | UVALUE_InsertValue vec elt idxs => _ *)
       (* | UVALUE_Select cnd v1 v2 => _ *)
       end.

  Set Guard Checking.

  (* TODO: move these ?*)
  Fixpoint drop {A} (n : N) (l : list A) : list A
    := match l with
       | [] => []
       | (x::xs) =>
         if N.eqb 0 n
         then l
         else drop (N.pred n) xs
       end.

  Fixpoint take {A} (n : N) (l : list A) : list A
    := match l with
       | [] => []
       | (x::xs) =>
         if N.eqb 0 n
         then []
         else x :: take (N.pred n) xs
       end.

  Definition between {A} (lo hi : N) (l : list A) : list A
    := take (hi - lo) (drop lo l).

  (* Fixpoint deserialize_sbytes (bytes : list SByte) (dt : dtyp) : err uvalue *)
  (*   := match dt with *)
  (*      (* Base types *) *)
  (*      | DTYPE_I _ *)
  (*      | DTYPE_IPTR *)
  (*      | DTYPE_Pointer *)
  (*      | DTYPE_Half *)
  (*      | DTYPE_Float *)
  (*      | DTYPE_Double *)
  (*      | DTYPE_X86_fp80 *)
  (*      | DTYPE_Fp128 *)
  (*      | DTYPE_Ppc_fp128 *)
  (*      | DTYPE_X86_mmx => *)
  (*        ret (from_ubytes bytes dt) *)

  (*      (* Unimplemented *) *)
  (*      | DTYPE_Void => *)
  (*        inl "deserialize_sbytes: attempting to deserialize void." *)
  (*      | DTYPE_Metadata => *)
  (*        inl "deserialize_sbytes: metadata." *)

  (*      (* Padded aggregate types *) *)
  (*      | DTYPE_Struct fields => *)
  (*        inl "deserialize_sbytes: padded structures unimplemented." *)

  (*      (* Packed aggregate types *) *)
  (*      | DTYPE_Array sz t => *)
  (*        let size := sizeof_dtyp t in *)
  (*        let size_nat := N.to_nat size in *)
  (*        fields <- monad_fold_right (fun acc idx => uv <- deserialize_sbytes (between (idx*size) ((idx+1) * size) bytes) t;; ret (uv::acc)) (Nseq 0 size_nat) [];; *)
  (*        ret (UVALUE_Array fields) *)
  (*      | DTYPE_Vector sz t => *)
  (*        let size := sizeof_dtyp t in *)
  (*        let size_nat := N.to_nat size in *)
  (*        fields <- monad_fold_right (fun acc idx => uv <- deserialize_sbytes (between (idx*size) ((idx+1) * size) bytes) t;; ret (uv::acc)) (Nseq 0 size_nat) [];; *)
  (*        ret (UVALUE_Vector fields) *)
  (*      | DTYPE_Packed_struct fields => *)
  (*        inl "deserialize_sbytes: unimplemented packed structs." *)

  (*      | DTYPE_Opaque => *)
  (*        inl "deserialize_sbytes: opaque." *)
  (*      end. *)

  (* TODO: if I have 8 bytes concatenated together... And they all
  have the same uvalue, will I evaluate the UVALUE 8 times???

       Naively, maybe, but I think I can optimize this when looking at ConcatBytes...
   *)

    (* TODO: probably move this *)
  Definition extract_byte_vint {I} `{VInt I} (i : I) (idx : Z) : I
    := modu (shru i (repr (idx * 8))) (repr 256).

  Fixpoint concat_bytes_vint {I} `{VInt I} (bytes : list I) : I
    := match bytes with
       | [] => repr 0
       | (byte::bytes) =>
         add byte (shl (concat_bytes_vint bytes) (repr 8))
       end.

(*     (* TODO: probably move this *) *)
(*   Inductive concretize_u : uvalue -> undef_or_err dvalue -> Prop :=  *)
(*   (* Concrete uvalue are contretized into their singleton *) *)
(*   | Pick_concrete             : forall uv (dv : dvalue), uvalue_to_dvalue uv = inr dv -> concretize_u uv (ret dv) *)
(*   | Pick_fail                 : forall uv v s, ~ (uvalue_to_dvalue uv = inr v)  -> concretize_u uv (lift (failwith s)) *)
(*   (* Undef relates to all dvalue of the type *) *)
(*   | Concretize_Undef          : forall dt dv, *)
(*       dvalue_has_dtyp dv dt -> *)
(*       concretize_u (UVALUE_Undef dt) (ret dv) *)

(*   (* The other operations proceed non-deterministically *) *)
(*   | Concretize_IBinop : forall iop uv1 e1 uv2 e2, *)
(*       concretize_u uv1 e1 -> *)
(*       concretize_u uv2 e2 -> *)
(*       concretize_u (UVALUE_IBinop iop uv1 uv2) *)
(*                    (dv1 <- e1 ;; *)
(*                     dv2 <- e2 ;; *)
(*                     (eval_iop iop dv1 dv2)) *)
  
(*   | Concretize_ICmp : forall cmp uv1 e1 uv2 e2 , *)
(*       concretize_u uv1 e1 -> *)
(*       concretize_u uv2 e2 -> *)
(*       concretize_u (UVALUE_ICmp cmp uv1 uv2) *)
(*                    (dv1 <- e1 ;; *)
(*                     dv2 <- e2 ;; *)
(*                     eval_icmp cmp dv1 dv2) *)

(*   | Concretize_FBinop : forall fop fm uv1 e1 uv2 e2, *)
(*       concretize_u uv1 e1 -> *)
(*       concretize_u uv2 e2 -> *)
(*       concretize_u (UVALUE_FBinop fop fm uv1 uv2) *)
(*                    (dv1 <- e1 ;; *)
(*                     dv2 <- e2 ;; *)
(*                     eval_fop fop dv1 dv2) *)

(*   | Concretize_FCmp : forall cmp uv1 e1 uv2 e2, *)
(*       concretize_u uv1 e1 -> *)
(*       concretize_u uv2 e2 -> *)
(*       concretize_u (UVALUE_FCmp cmp uv1 uv2) *)
(*                    (dv1 <- e1 ;; *)
(*                     dv2 <- e2 ;; *)
(*                     eval_fcmp cmp dv1 dv2) *)

(*   | Concretize_Struct_Nil     : concretize_u (UVALUE_Struct []) (ret (DVALUE_Struct [])) *)
(*   | Concretize_Struct_Cons    : forall u e us es, *)
(*       concretize_u u e -> *)
(*       concretize_u (UVALUE_Struct us) es -> *)
(*       concretize_u (UVALUE_Struct (u :: us)) *)
(*                    (d <- e ;; *)
(*                     vs <- es ;; *)
(*                     match vs with *)
(*                     | (DVALUE_Struct ds) => ret (DVALUE_Struct (d :: ds)) *)
(*                     | _ => failwith "illegal Struct Cons" *)
(*                     end) *)


(*   | Concretize_Packed_struct_Nil     : concretize_u (UVALUE_Packed_struct []) (ret (DVALUE_Packed_struct [])) *)
(*   | Concretize_Packed_struct_Cons    : forall u e us es, *)
(*       concretize_u u e -> *)
(*       concretize_u (UVALUE_Packed_struct us) es -> *)
(*       concretize_u (UVALUE_Packed_struct (u :: us)) *)
(*                    (d <- e ;; *)
(*                     vs <- es ;; *)
(*                     match vs with *)
(*                     | (DVALUE_Packed_struct ds) => ret (DVALUE_Packed_struct (d :: ds)) *)
(*                     | _ => failwith "illegal Packed_struct cons" *)
(*                     end) *)

(*   | Concretize_Array_Nil : *)
(*       concretize_u (UVALUE_Array []) (ret (DVALUE_Array [])) *)

(*   | Concretize_Array_Cons : forall u e us es, *)
(*       concretize_u u e -> *)
(*       concretize_u (UVALUE_Array us) es ->       *)
(*       concretize_u (UVALUE_Array (u :: us)) *)
(*                    (d <- e ;; *)
(*                     vs <- es ;; *)
(*                     match vs with *)
(*                     | (DVALUE_Array ds) => ret (DVALUE_Array (d :: ds)) *)
(*                     | _ => failwith "illegal Array cons" *)
(*                     end) *)

(*   | Concretize_Vector_Nil : *)
(*       concretize_u (UVALUE_Vector []) (ret (DVALUE_Vector [])) *)

(*   | Concretize_Vector_Cons : forall u e us es, *)
(*       concretize_u u e -> *)
(*       concretize_u (UVALUE_Vector us) es ->       *)
(*       concretize_u (UVALUE_Vector (u :: us)) *)
(*                    (d <- e ;; *)
(*                     vs <- es ;; *)
(*                     match vs with *)
(*                     | (DVALUE_Vector ds) => ret (DVALUE_Vector (d :: ds)) *)
(*                     | _ => failwith "illegal Vector cons" *)
(*                     end) *)

(*   | Concretize_ConcatBytes_Int : *)
(*       forall bytes sz, *)
(*         (forall byte, In byte bytes -> exists idx, byte = UVALUE_ExtractByte byte idx) *)
(*         concretize_u (UVALUE_ConcatBytes bytes (DTYPE_I sz)) *)
(*                      _ *)
(*   . *)

(*   (* The thing that's bothering me... *)

(*      Converting to DVALUE destroys information... *)

(*      Maybe it doesn't matter, though... *)

(*    *) *)
  
(*   (* May not concretize to anything. Should be a type error *) *)
(*   | Concretize_ExtractByte : *)
(*       forall byte idx c_byte c_idx, *)
(*         concretize_u byte c_byte -> *)
(*         concretize_u idx  c_idx -> *)
(*         concretize_u (UVALUE_ExtractByte byte idx) *)
(*                      (c_byte' <- c_byte;; *)
(*                       c_idx'  <- c_idx;; *)
(*                       match c_byte' with *)
(*                       | DVALUE_Addr a => _ *)
(*                       | DVALUE_I1 x => _ *)
(*                       | DVALUE_I8 x => _ *)
(*                       | DVALUE_I32 x => _ *)
(*                       | DVALUE_I64 x => _ *)
(*                       | DVALUE_IPTR x => _ *)
(*                       | DVALUE_Double x => _ *)
(*                       | DVALUE_Float x => _ *)
(*                       | DVALUE_Poison => _ *)
(*                       | DVALUE_None => _ *)
(*                       | DVALUE_Struct fields => _ *)
(*                       | DVALUE_Packed_struct fields => _ *)
(*                       | DVALUE_Array elts => _ *)
(*                       | DVALUE_Vector elts => _ *)
(*                       end *)
(*                      ) *)
(*   | Concretize_ConcatBytes_Int : *)
(*       forall bytes sz, *)
(*         concretize_u (UVALUE_ConcatBytes bytes (DTYPE_I sz)) *)
(*                      (ret DVALUE_None) *)
(*   . *)

(*   Definition concretize (uv: uvalue) (dv : dvalue) := concretize_u uv (ret dv). *)


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

    Definition default_dvalue_of_dtyp_i (sz : N) : err dvalue:=
      (if (sz =? 64) then ret (DVALUE_I64 (repr 0))
        else if (sz =? 32) then ret (DVALUE_I32 (repr 0))
            else if (sz =? 8) then ret (DVALUE_I8 (repr 0))
                  else if (sz =? 1) then ret (DVALUE_I1 (repr 0))
                       else failwith
              "Illegal size for generating default dvalue of DTYPE_I").


    (* Handler for PickE which concretizes everything to 0 *)
    Fixpoint default_dvalue_of_dtyp (dt : dtyp) : err dvalue :=
      match dt with
      | DTYPE_I sz => default_dvalue_of_dtyp_i sz
      | DTYPE_IPTR => ret (DVALUE_IPTR 0)
      | DTYPE_Pointer => ret (DVALUE_Addr Addr.null)
      | DTYPE_Void => ret DVALUE_None
      | DTYPE_Half => failwith "Unimplemented default type: half"
      | DTYPE_Float => ret (DVALUE_Float Float32.zero)
      | DTYPE_Double => ret (DVALUE_Double (Float32.to_double Float32.zero))
      | DTYPE_X86_fp80 => failwith "Unimplemented default type: x86_fp80"
      | DTYPE_Fp128 => failwith "Unimplemented default type: fp128"
      | DTYPE_Ppc_fp128 => failwith "Unimplemented default type: ppc_fp128"
      | DTYPE_Metadata => failwith "Unimplemented default type: metadata"
      | DTYPE_X86_mmx => failwith "Unimplemented default type: x86_mmx"
      | DTYPE_Opaque => failwith "Unimplemented default type: opaque"
      | DTYPE_Array sz t =>
        if (0 <=? sz) then
          v <- default_dvalue_of_dtyp t ;;
          (ret (DVALUE_Array (repeat v (N.to_nat sz))))
        else
          failwith ("Negative array length for generating default value" ++
          "of DTYPE_Array or DTYPE_Vector")

      (* Matching valid Vector types... *)
      (* Currently commented out unsupported ones *)
      (* | DTYPE_Vector sz (DTYPE_Half) => *)
      (*   if (0 <=? sz) then *)
      (*     (ret (DVALUE_Vector *)
      (*             (repeat (DVALUE_Float Float32.zero) (N.to_nat sz)))) *)
      (*   else *)
      (*     failwith ("Negative array length for generating default value" ++ *)
      (*     "of DTYPE_Array or DTYPE_Vector") *)
      | DTYPE_Vector sz (DTYPE_Float) =>
        if (0 <=? sz) then
          (ret (DVALUE_Vector
                  (repeat (DVALUE_Float Float32.zero) (N.to_nat sz))))
        else
          failwith ("Negative array length for generating default value" ++
          "of DTYPE_Array or DTYPE_Vector")
      | DTYPE_Vector sz (DTYPE_Double) =>
        if (0 <=? sz) then
          (ret (DVALUE_Vector
                  (repeat (DVALUE_Double (Float32.to_double Float32.zero))
                          (N.to_nat sz))))
        else
          failwith ("Negative array length for generating default value" ++
          "of DTYPE_Array or DTYPE_Vector")
      (* | DTYPE_Vector sz (DTYPE_X86_fp80) => *)
      (*   if (0 <=? sz) then *)
      (*     (ret (DVALUE_Vector *)
      (*             (repeat (DVALUE_Float Float32.zero) (N.to_nat sz)))) *)
      (*   else *)
      (*     failwith ("Negative array length for generating default value" ++ *)
      (*     "of DTYPE_Array or DTYPE_Vector") *)
      (* | DTYPE_Vector sz (DTYPE_Fp128) => *)
      (*   if (0 <=? sz) then *)
      (*     (ret (DVALUE_Vector *)
      (*             (repeat (DVALUE_Float Float32.zero) (N.to_nat sz)))) *)
      (*   else *)
      (*     failwith ("Negative array length for generating default value" ++ *)
      (*     "of DTYPE_Array or DTYPE_Vector") *)
      | DTYPE_Vector sz (DTYPE_I n) =>
        if (0 <=? sz) then
          v <- default_dvalue_of_dtyp_i n ;;
          (ret (DVALUE_Vector (repeat v (N.to_nat sz))))
        else
          failwith ("Negative array length for generating default value" ++
          "of DTYPE_Array or DTYPE_Vector")
      | DTYPE_Vector _ _ => failwith ("Non-valid vector type when" ++
          "generating default vector")
      | DTYPE_Struct fields =>
        v <- @map_monad err _ dtyp dvalue default_dvalue_of_dtyp fields;;
        ret (DVALUE_Struct v)
      | DTYPE_Packed_struct fields =>
        v <- @map_monad err _ dtyp dvalue default_dvalue_of_dtyp fields;;
        ret (DVALUE_Packed_struct v)
      end.


    Section Concretize.

      

      Variable endianess : Endianess.

      (* Convert a list of UVALUE_ExtractByte values into a dvalue of a given type

         Assumes bytes are in little endian form...

         Note: I believe this function has to be endianess aware.
       *)
      (* Fixpoint extractbytes_to_dvalue (uvs : list uvalue) (dt : dtyp) *)
      (*   := match dt with *)
      (*      | DTYPE_I sz =>   *)
      (*      | DTYPE_IPTR => _ *)
      (*      | DTYPE_Pointer => _ *)
      (*      | DTYPE_Void => _ *)
      (*      | DTYPE_Half => _ *)
      (*      | DTYPE_Float => _ *)
      (*      | DTYPE_Double => _ *)
      (*      | DTYPE_X86_fp80 => _ *)
      (*      | DTYPE_Fp128 => _ *)
      (*      | DTYPE_Ppc_fp128 => _ *)
      (*      | DTYPE_Metadata => _ *)
      (*      | DTYPE_X86_mmx => _ *)
      (*      | DTYPE_Array sz t => _ *)
      (*      | DTYPE_Struct fields => _ *)
      (*      | DTYPE_Packed_struct fields => _ *)
      (*      | DTYPE_Opaque => _ *)
      (*      | DTYPE_Vector sz t => _ *)
      (*      end. *)
      
      Fixpoint concretize_uvalue (u : uvalue) : undef_or_err dvalue :=
        match u with
        | UVALUE_Addr a                          => ret (DVALUE_Addr a)
        | UVALUE_I1 x                            => ret (DVALUE_I1 x)
        | UVALUE_I8 x                            => ret (DVALUE_I8 x)
        | UVALUE_I32 x                           => ret (DVALUE_I32 x)
        | UVALUE_I64 x                           => ret (DVALUE_I64 x)
        | UVALUE_IPTR x                          => ret (DVALUE_IPTR x)
        | UVALUE_Double x                        => ret (DVALUE_Double x)
        | UVALUE_Float x                         => ret (DVALUE_Float x)
        | UVALUE_Undef t                         => lift (default_dvalue_of_dtyp t)
        | UVALUE_Poison                          => ret (DVALUE_Poison)
        | UVALUE_None                            => ret DVALUE_None
        | UVALUE_Struct fields                   => 'dfields <- map_monad concretize_uvalue fields ;;
                                                   ret (DVALUE_Struct dfields)
        | UVALUE_Packed_struct fields            => 'dfields <- map_monad concretize_uvalue fields ;;
                                                   ret (DVALUE_Packed_struct dfields)
        | UVALUE_Array elts                      => 'delts <- map_monad concretize_uvalue elts ;;
                                                   ret (DVALUE_Array delts)
        | UVALUE_Vector elts                     => 'delts <- map_monad concretize_uvalue elts ;;
                                                   ret (DVALUE_Vector delts)
        | UVALUE_IBinop iop v1 v2                => dv1 <- concretize_uvalue v1 ;;
                                                   dv2 <- concretize_uvalue v2 ;;
                                                   eval_iop iop dv1 dv2
        | UVALUE_ICmp cmp v1 v2                  => dv1 <- concretize_uvalue v1 ;;
                                                   dv2 <- concretize_uvalue v2 ;;
                                                   eval_icmp cmp dv1 dv2
        | UVALUE_FBinop fop fm v1 v2             => dv1 <- concretize_uvalue v1 ;;
                                                   dv2 <- concretize_uvalue v2 ;;
                                                   eval_fop fop dv1 dv2
        | UVALUE_FCmp cmp v1 v2                  => dv1 <- concretize_uvalue v1 ;;
                                                   dv2 <- concretize_uvalue v2 ;;
                                                   eval_fcmp cmp dv1 dv2
        | UVALUE_ConcatBytes bytes dt sid =>
          (* TODO: BUG... don't the types have to be equal too...? *)
          match N.eqb (N.of_nat (length bytes)) (sizeof_dtyp dt), all_extract_bytes_from_uvalue bytes with
          | true, Some uv => concretize_uvalue uv
          | _, _ => extractbytes_to_dvalue bytes dt
          end

        | UVALUE_ExtractByte byte idx =>
          (* TODO: maybe this is just an error? ExtractByte should be guarded by ConcatBytes? *)
          lift (failwith "Attempting to concretize UVALUE_ExtractByte, should not happen.")
        | _ => (lift (failwith "Attempting to convert a partially non-reduced uvalue to dvalue. Should not happen"))
                
        end.

    End Concretize.
