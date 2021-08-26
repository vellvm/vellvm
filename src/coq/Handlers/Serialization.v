From Vellvm Require Import
     Numeric.Coqlib
     Numeric.Integers
     Numeric.Floats
     Utils.Tactics
     Utils.Util
     Utils.Error
     Utils.ListUtil
     Utils.NonEmpty
     Utils.NMaps
     Syntax.LLVMAst
     Syntax.DynamicTypes
     Syntax.DataLayout
     Semantics.DynamicValues
     Semantics.Denotation
     Semantics.MemoryAddress
     Semantics.GepM
     Semantics.Memory.Sizeof
     Semantics.Memory.MemBytes
     Semantics.LLVMEvents.

From ExtLib Require Import
     Core.RelDec
     Structures.Monads
     Data.Monads.EitherMonad.

Require Import Lia.


Import ListNotations.
Import MonadNotation.

Module Make(Addr:MemoryAddress.ADDRESS)(LLVMIO: LLVM_INTERACTIONS(Addr))(SIZEOF: Sizeof)(PTOI:PTOI(Addr))(PROVENANCE:PROVENANCE(Addr))(ITOP:ITOP(Addr)(PROVENANCE))(GEP:GEPM(Addr)(LLVMIO))(BYTE_IMPL:ByteImpl(Addr)(LLVMIO)).

  Import LLVMIO.
  Import SIZEOF.
  Import PTOI.
  Import PROVENANCE.
  Import ITOP.
  Import DV.
  Import GEP.
  Module Den := Denotation Addr LLVMIO.
  Import Den.
  Open Scope list.

  Module BYTE := Byte Addr LLVMIO BYTE_IMPL.
  Import BYTE.


  (* Variable ptr_size : nat. *)
  (* Variable datalayout : DataLayout. *)
  Definition ptr_size : nat := 8.

  Definition addr := Addr.addr.

  (* TODO: parameterize *)
  Definition endianess : Endianess
    := ENDIAN_LITTLE.

  (* Given a little endian list of bytes, match the endianess of `e` *)
  Definition correct_endianess {BYTES : Type} (e : Endianess) (bytes : list BYTES)
    := match e with
       | ENDIAN_BIG => rev bytes
       | ENDIAN_LITTLE => bytes
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

    (* TODO: move to utils? *)
    Definition from_option {A} (def : A) (opt : option A) : A
      := match opt with
         | Some x => x
         | None => def
         end.

    (* Definition fp_alignment (bits : N) : option Alignment := *)
    (*   let fp_map := dl_floating_point_alignments datalayout *)
    (*   in NM.find bits fp_map. *)

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

    (* Definition int_alignment (bits : N) : option Alignment := *)
    (*   let int_map := dl_integer_alignments datalayout *)
    (*   in match NM.find bits int_map with *)
    (*      | Some align => Some align *)
    (*      | None => *)
    (*        let keys  := map fst (NM.elements int_map) in *)
    (*        let bits' := nextOrMaximumOpt N.leb bits keys  *)
    (*        in match bits' with *)
    (*           | Some bits => NM.find bits int_map *)
    (*           | None => None *)
    (*           end *)
    (*      end. *)

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

    Import StateMonad.
    Definition ErrSID := eitherT string (state store_id).

    Definition lift_err {M A} `{MonadExc string M} `{Monad M} (e : err A) : (M A)
        := match e with
         | inl e => raise e
         | inr x => ret x
         end.

    Definition evalErrSID {A} (m : ErrSID A) (sid : store_id) : err A
      := evalState (unEitherT m) sid.

    Definition fresh_sid : ErrSID store_id
      := lift (modify N.succ).

    (* Assign fresh sids to ubytes while preserving entanglement *)
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

      (* TODO: Move this? *)
      Inductive Poisonable (A : Type) : Type :=
      | Unpoisoned : A -> Poisonable A
      | Poison : Poisonable A
      .

      Arguments Unpoisoned {A} a.
      Arguments Poison {A}.

      Global Instance MonadPoisonable : Monad Poisonable
        := { ret  := @Unpoisoned;
             bind := fun _ _ ma mab => match ma with
                                   | Poison => Poison
                                   | Unpoisoned v => mab v
                                    end
           }.

      Definition ErrPoison := eitherT string Poisonable.

      Definition ErrPoison_to_undef_or_err_dvalue (ep : ErrPoison dvalue) : undef_or_err dvalue
        := match unEitherT ep with
           | Unpoisoned dv => lift dv
           | Poisoin => ret DVALUE_Poison
           end.

      Definition err_to_ErrPoison {A} (e : err A) : ErrPoison A
        := match e with
           | inl x => failwith x
           | inr x => ret x
           end.

      (* Walk through a list *)
      (* Returns field index + number of bytes remaining *)
      Fixpoint extract_field_byte_helper {M} `{Monad M} (fields : list dtyp) (field_idx : N) (byte_idx : N) : eitherT string M (dtyp * (N * N))
        := match fields with
           | [] =>
             raise "No fields left for byte-indexing..."
           | (x::xs) =>
             let sz := sizeof_dtyp x
             in if N.ltb byte_idx sz
                then ret (x, (field_idx, byte_idx))
                else extract_field_byte_helper xs (N.succ field_idx) (byte_idx - sz)
           end.

      Fixpoint extract_field_byte {M} `{Monad M} (fields : list dtyp) (byte_idx : N) : eitherT string M (dtyp * (N * N))
        := extract_field_byte_helper fields 0 byte_idx.

      (* TODO: move this? *)
      Ltac solve_dvalue_measure :=
        match goal with
        | H: Some ?f = List.nth_error ?fields _ |- context [dvalue_measure ?f]
          => symmetry in H; apply nth_error_In in H;
            pose proof list_sum_map dvalue_measure _ _ H;
            cbn; lia
        end.


      (* Need the type of the dvalue in order to know how big fields and array elements are.

         It's not possible to use the dvalue alone, as DVALUE_Poison's
         size depends on the type.
       *)
      Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia | solve_dvalue_measure].
      Program Fixpoint dvalue_extract_byte (dv : dvalue) (dt : dtyp) (idx : Z) {measure (dvalue_measure dv)}: ErrPoison Z
        := match dv with
           | DVALUE_I1 x
           | DVALUE_I8 x
           | DVALUE_I32 x
           | DVALUE_I64 x =>
             ret (extract_byte_vint x idx)
           | DVALUE_IPTR x =>
             ret (extract_byte_Z x idx)
           | DVALUE_Addr addr =>
             (* Note: this throws away provenance *)
             ret (extract_byte_Z (ptr_to_int addr) idx)
           | DVALUE_Float f =>
             ret (extract_byte_Z (unsigned (Float32.to_bits f)) idx)
           | DVALUE_Double d =>
             ret (extract_byte_Z (unsigned (Float.to_bits d)) idx)
           | DVALUE_Poison => lift Poison
           | DVALUE_None =>
             (* TODO: Not sure if this should be an error, poison, or what. *)
             raise "dvalue_extract_byte on DVALUE_None"
           (* TODO: Take padding into account. *)
           | DVALUE_Struct fields =>
             match dt with
             | DTYPE_Struct dts =>
               (* Step to field which contains the byte we want *)
               @bind ErrPoison _ _ _ (extract_field_byte dts (Z.to_N idx))
                    (fun '(fdt, (field_idx, byte_idx)) =>
                       match List.nth_error fields (N.to_nat field_idx) with
                       | Some f =>
                         (* call dvalue_extract_byte recursively on the field *)
                         dvalue_extract_byte f fdt (Z.of_N byte_idx )
                       | None =>
                         raise "dvalue_extract_byte: more fields in DVALUE_Struct than in dtyp."
                       end)
             | _ => raise "dvalue_extract_byte: type mismatch on DVALUE_Struct."
             end
           | DVALUE_Packed_struct fields =>
             match dt with
             | DTYPE_Packed_struct dts =>
               (* Step to field which contains the byte we want *)
               @bind ErrPoison _ _ _ (extract_field_byte dts (Z.to_N idx))
                     (fun '(fdt, (field_idx, byte_idx)) =>
                        match List.nth_error fields (N.to_nat field_idx) with
                        | Some f =>
                          (* call dvalue_extract_byte recursively on the field *)
                          dvalue_extract_byte f fdt (Z.of_N byte_idx )
                        | None =>
                          raise "dvalue_extract_byte: more fields in DVALUE_Packed_struct than in dtyp."
                        end)
             | _ => raise "dvalue_extract_byte: type mismatch on DVALUE_Packed_struct."
             end
           | DVALUE_Array elts =>
             match dt with
             | DTYPE_Array sz dt =>
               let elmt_sz  := sizeof_dtyp dt in
               let elmt_idx := N.div (Z.to_N idx) elmt_sz in
               let byte_idx := (Z.to_N idx) mod elmt_sz in
               match List.nth_error elts (N.to_nat elmt_idx) with
               | Some elmt =>
                 (* call dvalue_extract_byte recursively on the field *)
                 dvalue_extract_byte elmt dt (Z.of_N byte_idx)
               | None =>
                 raise "dvalue_extract_byte: more fields in dvalue than in dtyp."
               end
             | _ =>
               raise "dvalue_extract_byte: type mismatch on DVALUE_Array."
             end
           | DVALUE_Vector elts =>
             match dt with
             | DTYPE_Vector sz dt =>
               let elmt_sz  := sizeof_dtyp dt in
               let elmt_idx := N.div (Z.to_N idx) elmt_sz in
               let byte_idx := (Z.to_N idx) mod elmt_sz in
               match List.nth_error elts (N.to_nat elmt_idx) with
               | Some elmt =>
                 (* call dvalue_extract_byte recursively on the field *)
                 dvalue_extract_byte elmt dt (Z.of_N byte_idx)
               | None =>
                 raise "dvalue_extract_byte: more fields in dvalue than in dtyp."
               end
             | _ =>
               raise "dvalue_extract_byte: type mismatch on DVALUE_Vector."
             end
           end.

      (* Taking a byte out of a dvalue...

      Unlike UVALUE_ExtractByte, I don't think this needs an sid
      (store id). There should be no nondeterminism in this value. *)
      Inductive dvalue_byte : Type :=
      | DVALUE_ExtractByte (dv : dvalue) (dt : dtyp) (idx : N) : dvalue_byte
      .

      Definition dvalue_byte_value (db : dvalue_byte) : ErrPoison Z
        := match db with
           | DVALUE_ExtractByte dv dt idx =>
             dvalue_extract_byte dv dt (Z.of_N idx)
           end.

      Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia].
      Program Fixpoint dvalue_bytes_to_dvalue (dbs : list dvalue_byte) (dt : dtyp) {measure (dtyp_measure dt)} : ErrPoison dvalue
        := match dt with
           | DTYPE_I sz =>
             zs <- map_monad dvalue_byte_value dbs;;
             match sz with
             | 1 =>
               ret (DVALUE_I1 (concat_bytes_Z_vint zs))
             | 8 =>
               ret (DVALUE_I8 (concat_bytes_Z_vint zs))
             | 32 =>
               ret (DVALUE_I32 (concat_bytes_Z_vint zs))
             | 64 =>
               ret (DVALUE_I64 (concat_bytes_Z_vint zs))
             | _ => raise "Unsupported integer size."
             end
           | DTYPE_IPTR =>
             zs <- map_monad dvalue_byte_value dbs;;
             ret (DVALUE_IPTR (concat_bytes_Z zs))
           | DTYPE_Pointer =>
             (* TODO: not sure if this should be wildcard provenance.
                TODO: not sure if this should truncate iptr value...
              *)
             zs <- map_monad dvalue_byte_value dbs;;
             ret (DVALUE_Addr (int_to_ptr (concat_bytes_Z zs) wildcard_prov))
           | DTYPE_Void =>
             raise "dvalue_bytes_to_dvalue on void type."
           | DTYPE_Half =>
             raise "dvalue_bytes_to_dvalue: unsupported DTYPE_Half."
           | DTYPE_Float =>
             zs <- map_monad dvalue_byte_value dbs;;
             ret (DVALUE_Float (Float32.of_bits (concat_bytes_Z_vint zs)))
           | DTYPE_Double =>
             zs <- map_monad dvalue_byte_value dbs;;
             ret (DVALUE_Double (Float.of_bits (concat_bytes_Z_vint zs)))
           | DTYPE_X86_fp80 =>
             raise "dvalue_bytes_to_dvalue: unsupported DTYPE_X86_fp80."
           | DTYPE_Fp128 =>
             raise "dvalue_bytes_to_dvalue: unsupported DTYPE_Fp128."
           | DTYPE_Ppc_fp128 =>
             raise "dvalue_bytes_to_dvalue: unsupported DTYPE_Ppc_fp128."
           | DTYPE_Metadata =>
             raise "dvalue_bytes_to_dvalue: unsupported DTYPE_Metadata."
           | DTYPE_X86_mmx =>
             raise "dvalue_bytes_to_dvalue: unsupported DTYPE_X86_mmx."
           | DTYPE_Array sz t =>
             let sz := sizeof_dtyp t in
             elt_bytes <- err_to_ErrPoison (split_every sz dbs);;
             elts <- map_monad (fun es => dvalue_bytes_to_dvalue es t) elt_bytes;;
             ret (DVALUE_Array elts)
           | DTYPE_Vector sz t =>
             let sz := sizeof_dtyp t in
             elt_bytes <- err_to_ErrPoison (split_every sz dbs);;
             elts <- map_monad (fun es => dvalue_bytes_to_dvalue es t) elt_bytes;;
             ret (DVALUE_Vector elts)
           | DTYPE_Struct fields =>
             match fields with
             | [] => ret (DVALUE_Struct []) (* TODO: Not 100% sure about this. *)
             | (dt::dts) =>
               let sz := sizeof_dtyp dt in
               let init_bytes := take sz dbs in
               let rest_bytes := drop sz dbs in
               f <- dvalue_bytes_to_dvalue init_bytes dt;;
               rest <- dvalue_bytes_to_dvalue rest_bytes (DTYPE_Struct dts);;
               match rest with
               | DVALUE_Struct fs =>
                 ret (DVALUE_Struct (f::fs))
               | _ =>
                 raise "dvalue_bytes_to_dvalue: DTYPE_Struct recursive call did not return a struct."
               end
             end
           | DTYPE_Packed_struct fields =>
             match fields with
             | [] => ret (DVALUE_Packed_struct []) (* TODO: Not 100% sure about this. *)
             | (dt::dts) =>
               let sz := sizeof_dtyp dt in
               let init_bytes := take sz dbs in
               let rest_bytes := drop sz dbs in
               f <- dvalue_bytes_to_dvalue init_bytes dt;;
               rest <- dvalue_bytes_to_dvalue rest_bytes (DTYPE_Struct dts);;
               match rest with
               | DVALUE_Packed_struct fs =>
                 ret (DVALUE_Packed_struct (f::fs))
               | _ =>
                 raise "dvalue_bytes_to_dvalue: DTYPE_Packed_struct recursive call did not return a struct."
               end
             end
           | DTYPE_Opaque =>
             raise "dvalue_bytes_to_dvalue: unsupported DTYPE_Opaque."
           end.
      Next Obligation.
        pose proof dtyp_measure_gt_0 dt.
        cbn.
        unfold list_sum.
        lia.
      Qed.
      Next Obligation.
        pose proof dtyp_measure_gt_0 dt.
        cbn.
        unfold list_sum.
        lia.
      Qed.

      Definition uvalue_sid_match (a b : uvalue) : bool
        :=
          match a, b with
          | UVALUE_ExtractByte uv dt idx sid, UVALUE_ExtractByte uv' dt' idx' sid' =>
            RelDec.rel_dec uv uv' && N.eqb sid sid'
          | _, _ => false
          end.

      Definition filter_uvalue_sid_matches (byte : uvalue) (uvs : list (N * uvalue)) : (list (N * uvalue) * list (N * uvalue))
        := filter_split (fun '(n, uv) => uvalue_sid_match byte uv) uvs.

      Definition uvalue_constructor_string (u : uvalue) : string
        := match u with
           | UVALUE_Addr a => "UVALUE_Addr"
           | UVALUE_I1 x => "UVALUE_I1"
           | UVALUE_I8 x => "UVALUE_I8"
           | UVALUE_I32 x => "UVALUE_I32"
           | UVALUE_I64 x => "UVALUE_I64"
           | UVALUE_IPTR x => "UVALUE_IPTR"
           | UVALUE_Double x => "UVALUE_Double"
           | UVALUE_Float x => "UVALUE_Float"
           | UVALUE_Undef t => "UVALUE_Undef"
           | UVALUE_Poison => "UVALUE_Poison"
           | UVALUE_None => "UVALUE_None"
           | UVALUE_Struct fields => "UVALUE_Struct"
           | UVALUE_Packed_struct fields => "UVALUE_Packed_struct"
           | UVALUE_Array elts => "UVALUE_Array"
           | UVALUE_Vector elts => "UVALUE_Vector"
           | UVALUE_IBinop iop v1 v2 => "UVALUE_IBinop"
           | UVALUE_ICmp cmp v1 v2 => "UVALUE_ICmp"
           | UVALUE_FBinop fop fm v1 v2 => "UVALUE_FBinop"
           | UVALUE_FCmp cmp v1 v2 => "UVALUE_FCmp"
           | UVALUE_Conversion conv t_from v t_to => "UVALUE_Conversion"
           | UVALUE_GetElementPtr t ptrval idxs => "UVALUE_GetElementPtr"
           | UVALUE_ExtractElement vec idx => "UVALUE_ExtractElement"
           | UVALUE_InsertElement vec elt idx => "UVALUE_InsertElement"
           | UVALUE_ShuffleVector vec1 vec2 idxmask => "UVALUE_ShuffleVector"
           | UVALUE_ExtractValue vec idxs => "UVALUE_ExtractValue"
           | UVALUE_InsertValue vec elt idxs => "UVALUE_InsertValue"
           | UVALUE_Select cnd v1 v2 => "UVALUE_Select"
           | UVALUE_ExtractByte uv dt idx sid => "UVALUE_ExtractByte"
           | UVALUE_ConcatBytes uvs dt => "UVALUE_ConcatBytes"
           end.


      (* Change this to take an undef handler... *)
      (* dtyp -> r *)
      (* lift dvalue to r too? dvalue -> r ? *)
      (*
        default_dvalue_of_dtyp : dtyp -> err dvalue

        pick_dtyp : dtyp -> (dvalue -> Prop)


        Inductive concretize_u : uvalue -> undef_or_err dvalue -> Prop :=
        Fixpoint concretize_uvalue (u : uvalue) {struct u} : undef_or_err dvalue :=

        

        Maybe it should be a monad???
       *)
      
      (* TODO: satisfy the termination checker here. *)
      Unset Guard Checking.
      Fixpoint concretize_uvalue (u : uvalue) {struct u} : undef_or_err dvalue :=
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
        | UVALUE_Conversion conv t_from v t_to    =>
          dv <- concretize_uvalue v ;;
          match get_conv_case conv t_from dv t_to with
          | Conv_PtoI x =>
            match x, t_to with
            | DVALUE_Addr addr, DTYPE_I sz =>
              coerce_integer_to_int sz (ptr_to_int addr)
            | _, _ =>
              lift (raise "Invalid PTOI conversion")
            end
          | Conv_ItoP x => ret (DVALUE_Addr (int_to_ptr (dvalue_int_unsigned x) wildcard_prov))
          | Conv_Pure x => ret x
          | Conv_Illegal s => raise s
          end

        | UVALUE_GetElementPtr t ua uvs =>
          da <- concretize_uvalue ua;;
          dvs <- map_monad concretize_uvalue uvs;;
          match handle_gep t da dvs with
          | inr dv  => ret dv
          | inl err => lift (failwith err)
          end

        | UVALUE_ExtractValue uv idxs =>
          str <- concretize_uvalue uv;;
          let fix loop str idxs : undef_or_err dvalue :=
              match idxs with
              | [] => ret str
              | i :: tl =>
                v <- index_into_str_dv str i ;;
                loop v tl
              end in
          loop str idxs

        | UVALUE_Select cond v1 v2 =>
          dcond <- concretize_uvalue cond;;
          uv <- eval_select dcond v1 v2;;
          concretize_uvalue uv

        | UVALUE_ConcatBytes bytes dt =>
          match N.eqb (N.of_nat (length bytes)) (sizeof_dtyp dt), all_extract_bytes_from_uvalue bytes with
          | true, Some uv => concretize_uvalue uv
          | _, _ => extractbytes_to_dvalue bytes dt
          end

        | UVALUE_ExtractByte byte dt idx sid =>
          (* TODO: maybe this is just an error? ExtractByte should be guarded by ConcatBytes? *)
          lift (failwith "Attempting to concretize UVALUE_ExtractByte, should not happen.")

         | _ => lift (failwith ("concretize_uvalue: Attempting to convert a partially non-reduced uvalue to dvalue. Should not happen: " ++ uvalue_constructor_string u))

                
        end

      with

      (* Take a UVALUE_ExtractByte, and replace the uvalue with a given dvalue... 

         Note: this also concretizes the index.
       *)
      uvalue_byte_replace_with_dvalue_byte (uv : uvalue) (dv : dvalue) {struct uv} : undef_or_err dvalue_byte
        := match uv with
           | UVALUE_ExtractByte uv dt idx sid =>
             cidx <- concretize_uvalue idx;;
             ret (DVALUE_ExtractByte dv dt (Z.to_N (dvalue_int_unsigned cidx)))
           | _ => lift (failwith "uvalue_byte_replace_with_dvalue_byte called with non-UVALUE_ExtractByte value.")
           end

      with
      (* Concretize the uvalues in a list of UVALUE_ExtractBytes...

       *)
        (* Pick out uvalue bytes that are the same + have same sid 

         Concretize these identical uvalues...
         *)

      concretize_uvalue_bytes_helper (uvs : list (N * uvalue)) (acc : NMap dvalue_byte) {struct uvs} : undef_or_err (NMap dvalue_byte)
        := match uvs with
           | [] => ret acc
           | ((n, uv)::uvs) =>
             match uv with
             | UVALUE_ExtractByte byte_uv dt idx sid =>
               let '(ins, outs) := filter_uvalue_sid_matches uv uvs in
               (* Concretize first uvalue *)
               dv <- concretize_uvalue byte_uv;;
               cidx <- concretize_uvalue idx;;
               let dv_byte := DVALUE_ExtractByte dv dt (Z.to_N (dvalue_int_unsigned cidx)) in
               let acc := @NM.add _ n dv_byte acc in
               (* Concretize entangled bytes *)
               acc <- monad_fold_right (fun acc '(n, uv) =>
                                         dvb <- uvalue_byte_replace_with_dvalue_byte uv dv;;
                                         ret (@NM.add _ n dvb acc)) ins acc;;
               (* Concretize the rest of the bytes *)
               concretize_uvalue_bytes_helper outs acc
             | _ => lift (failwith "concretize_uvalue_bytes_helper: non-byte in uvs.")
             end
           end

      with
      concretize_uvalue_bytes (uvs : list uvalue) {struct uvs} : undef_or_err (list dvalue_byte)
        :=
          let len := length uvs in
          byte_map <- concretize_uvalue_bytes_helper (zip (Nseq 0 len) uvs) (@NM.empty _);;
          match NM_find_many (Nseq 0 len) byte_map with
          | Some dvbs => ret dvbs
          | None => lift (failwith "concretize_uvalue_bytes: missing indices.")
          end
      
      with
      extractbytes_to_dvalue (uvs : list uvalue) (dt : dtyp) {struct uvs} : undef_or_err dvalue
        := dvbs <- concretize_uvalue_bytes uvs;;
           ErrPoison_to_undef_or_err_dvalue (dvalue_bytes_to_dvalue dvbs dt).

      Set Guard Checking.
    End Concretize.

Ltac eval_nseq :=
  match goal with
  | |- context[Nseq ?start ?len] =>
    let HS := fresh "HS" in
    let HSeq := fresh "HSeq" in
    remember (Nseq start len) as HS eqn:HSeq;
    cbv in HSeq;
    subst HS
  end.

Ltac uvalue_eq_dec_refl_true :=
  rewrite rel_dec_eq_true; [|exact eq_dec_uvalue_correct|reflexivity].

Ltac solve_guards_all_bytes :=
  try rewrite N.eqb_refl; try rewrite Z.eqb_refl; try uvalue_eq_dec_refl_true; cbn.

Section ConcretizeInductive.

  Variable endianess : Endianess.

  Inductive concretize_u : uvalue -> undef_or_err dvalue -> Prop :=
  (* TODO: should uvalue_to_dvalue be modified to handle concatbytes? *)
  (* Concrete uvalue are concretized into their singleton *)
  | Pick_concrete             : forall uv (dv : dvalue), uvalue_to_dvalue uv = inr dv -> concretize_u uv (ret dv)
  | Pick_fail                 : forall uv v s, ~ (uvalue_to_dvalue uv = inr v)  -> concretize_u uv (lift (failwith s))
  (* Undef relates to all dvalue of the type *)
  | Concretize_Undef          : forall dt dv,
      dvalue_has_dtyp dv dt ->
      concretize_u (UVALUE_Undef dt) (ret dv)

  (* The other operations proceed non-deterministically *)
  | Concretize_IBinop : forall iop uv1 e1 uv2 e2,
      concretize_u uv1 e1 ->
      concretize_u uv2 e2 ->
      concretize_u (UVALUE_IBinop iop uv1 uv2)
                   (dv1 <- e1 ;;
                    dv2 <- e2 ;;
                    (eval_iop iop dv1 dv2))
                   
  | Concretize_ICmp : forall cmp uv1 e1 uv2 e2 ,
      concretize_u uv1 e1 ->
      concretize_u uv2 e2 ->
      concretize_u (UVALUE_ICmp cmp uv1 uv2)
                   (dv1 <- e1 ;;
                    dv2 <- e2 ;;
                    eval_icmp cmp dv1 dv2)

  | Concretize_FBinop : forall fop fm uv1 e1 uv2 e2,
      concretize_u uv1 e1 ->
      concretize_u uv2 e2 ->
      concretize_u (UVALUE_FBinop fop fm uv1 uv2)
                   (dv1 <- e1 ;;
                    dv2 <- e2 ;;
                    eval_fop fop dv1 dv2)

  | Concretize_FCmp : forall cmp uv1 e1 uv2 e2,
      concretize_u uv1 e1 ->
      concretize_u uv2 e2 ->
      concretize_u (UVALUE_FCmp cmp uv1 uv2)
                   (dv1 <- e1 ;;
                    dv2 <- e2 ;;
                    eval_fcmp cmp dv1 dv2)

  | Concretize_Conversion : forall conv t_from v t_to e,
      concretize_u v e ->
      concretize_u (UVALUE_Conversion conv t_from v t_to)
                   (dv <- e;;
                    match get_conv_case conv t_from dv t_to with
                    | Conv_PtoI x =>
                      match x, t_to with
                      | DVALUE_Addr addr, DTYPE_I sz =>
                        coerce_integer_to_int sz (ptr_to_int addr)
                      | _, _ =>
                        lift (raise "Invalid PTOI conversion")
                      end
                    | Conv_ItoP x => ret (DVALUE_Addr (int_to_ptr (dvalue_int_unsigned x) wildcard_prov))
                    | Conv_Pure x => ret x
                    | Conv_Illegal s => raise s
                    end)

  | Concretize_GetElementPtr : forall t ua uvs ea es,
      concretize_u ua ea ->
      Forall2 concretize_u uvs es ->
      concretize_u (UVALUE_GetElementPtr t ua uvs)
                   (da <- ea;;
                    dvs <- sequence es;;
                    match handle_gep t da dvs with
                    | inr dv  => ret dv
                    | inl err => lift (failwith err)
                    end)

  | Concretize_ExtractValue : forall uv idxs e,
      concretize_u uv e ->
      concretize_u (UVALUE_ExtractValue uv idxs)
                   (str <- e;;
                    let fix loop str idxs : undef_or_err dvalue :=
                        match idxs with
                        | [] => ret str
                        | i :: tl =>
                          v <- index_into_str_dv str i ;;
                          loop v tl
                        end in
                    loop str idxs)

  | UVALUE_Select : forall cond v1 v2 econd (uv : uvalue) dv,
      concretize_u cond econd ->
      (dcond <- econd;; eval_select dcond v1 v2) = ret uv ->
      concretize_u uv dv ->
      concretize_u (UVALUE_Select cond v1 v2)
                   dv

  | Concretize_Struct_Nil     : concretize_u (UVALUE_Struct []) (ret (DVALUE_Struct []))
  | Concretize_Struct_Cons    : forall u e us es,
      concretize_u u e ->
      concretize_u (UVALUE_Struct us) es ->
      concretize_u (UVALUE_Struct (u :: us))
                   (d <- e ;;
                    vs <- es ;;
                    match vs with
                    | (DVALUE_Struct ds) => ret (DVALUE_Struct (d :: ds))
                    | _ => failwith "illegal Struct Cons"
                    end)


  | Concretize_Packed_struct_Nil     : concretize_u (UVALUE_Packed_struct []) (ret (DVALUE_Packed_struct []))
  | Concretize_Packed_struct_Cons    : forall u e us es,
      concretize_u u e ->
      concretize_u (UVALUE_Packed_struct us) es ->
      concretize_u (UVALUE_Packed_struct (u :: us))
                   (d <- e ;;
                    vs <- es ;;
                    match vs with
                    | (DVALUE_Packed_struct ds) => ret (DVALUE_Packed_struct (d :: ds))
                    | _ => failwith "illegal Packed_struct cons"
                    end)

  | Concretize_Array_Nil :
      concretize_u (UVALUE_Array []) (ret (DVALUE_Array []))

  | Concretize_Array_Cons : forall u e us es,
      concretize_u u e ->
      concretize_u (UVALUE_Array us) es ->
      concretize_u (UVALUE_Array (u :: us))
                   (d <- e ;;
                    vs <- es ;;
                    match vs with
                    | (DVALUE_Array ds) => ret (DVALUE_Array (d :: ds))
                    | _ => failwith "illegal Array cons"
                    end)

  | Concretize_Vector_Nil :
      concretize_u (UVALUE_Vector []) (ret (DVALUE_Vector []))

  | Concretize_Vector_Cons : forall u e us es,
      concretize_u u e ->
      concretize_u (UVALUE_Vector us) es ->
      concretize_u (UVALUE_Vector (u :: us))
                   (d <- e ;;
                    vs <- es ;;
                    match vs with
                    | (DVALUE_Vector ds) => ret (DVALUE_Vector (d :: ds))
                    | _ => failwith "illegal Vector cons"
                    end)

  (* The list of bytes contained here exactly match the serialization of a value of the data type.

     This means we can just take the corresponding uvalue, and concretize it.
   *)
  (* TODO: I'll need something separate for aggregate types to split the bytes up... *)
  | Concretize_ConcatBytes_Exact :
      forall bytes dt uv dv,
        all_bytes_from_uvalue bytes = Some uv ->
        N.of_nat (List.length bytes) = sizeof_dtyp dt ->
        concretize_u uv dv ->
        concretize_u (UVALUE_ConcatBytes (map sbyte_to_extractbyte bytes) dt) dv

  | Concretize_ConcatBytes_Array_nil :
      forall dt,
        concretize_u (UVALUE_ConcatBytes [] (DTYPE_Array 0 dt)) (ret (DVALUE_Array []))
  | Concretize_ConcatBytes_Array_cons :
      forall bytes elt_bytes rest_bytes sz dt e es,
        sizeof_dtyp dt > 0 ->
        take (sizeof_dtyp dt) bytes = elt_bytes ->
        drop (sizeof_dtyp dt) bytes = rest_bytes ->
        concretize_u (UVALUE_ConcatBytes elt_bytes dt) e ->
        concretize_u (UVALUE_ConcatBytes rest_bytes (DTYPE_Array sz dt)) es ->
        concretize_u (UVALUE_ConcatBytes bytes (DTYPE_Array (N.succ sz) dt))
                     (dv <- e;;
                      dvs <- es;;
                      match dvs with
                      | DVALUE_Array elts =>
                        ret (DVALUE_Array (dv :: elts))
                      | _ => failwith "ConcatBytes array cons failure."
                      end)

  | Concretize_ConcatBytes_Vector_nil :
      forall dt,
        concretize_u (UVALUE_ConcatBytes [] (DTYPE_Vector 0 dt)) (ret (DVALUE_Vector []))
  | Concretize_ConcatBytes_Vector_cons :
      forall bytes elt_bytes rest_bytes sz dt e es,
        sizeof_dtyp dt > 0 ->
        take (sizeof_dtyp dt) bytes = elt_bytes ->
        drop (sizeof_dtyp dt) bytes = rest_bytes ->
        concretize_u (UVALUE_ConcatBytes elt_bytes dt) e ->
        concretize_u (UVALUE_ConcatBytes rest_bytes (DTYPE_Vector sz dt)) es ->
        concretize_u (UVALUE_ConcatBytes bytes (DTYPE_Vector (N.succ sz) dt))
                     (dv <- e;;
                      dvs <- es;;
                      match dvs with
                      | DVALUE_Vector elts =>
                        ret (DVALUE_Vector (dv :: elts))
                      | _ => failwith "ConcatBytes array cons failure."
                      end)

  (* TODO: Take padding into account *)
  | Concretize_ConcatBytes_Struct_nil :
      concretize_u (UVALUE_ConcatBytes [] (DTYPE_Struct [])) (ret (DVALUE_Struct []))
  | Concretize_ConcatBytes_Struct_cons :
      forall bytes elt_bytes rest_bytes dt dts e es,
        sizeof_dtyp dt > 0 ->
        take (sizeof_dtyp dt) bytes = elt_bytes ->
        drop (sizeof_dtyp dt) bytes = rest_bytes ->
        concretize_u (UVALUE_ConcatBytes elt_bytes dt) e ->
        concretize_u (UVALUE_ConcatBytes rest_bytes (DTYPE_Struct dts)) es ->
        concretize_u (UVALUE_ConcatBytes bytes (DTYPE_Struct (dt::dts)))
                     (dv <- e;;
                      dvs <- es;;
                      match dvs with
                      | DVALUE_Struct elts =>
                        ret (DVALUE_Struct (dv :: elts))
                      | _ => failwith "ConcatBytes array cons failure."
                      end)

  | Concretize_ConcatBytes_Packed_struct_nil :
      concretize_u (UVALUE_ConcatBytes [] (DTYPE_Packed_struct [])) (ret (DVALUE_Packed_struct []))
  | Concretize_ConcatBytes_Packed_struct_cons :
      forall bytes elt_bytes rest_bytes dt dts e es,
        sizeof_dtyp dt > 0 ->
        take (sizeof_dtyp dt) bytes = elt_bytes ->
        drop (sizeof_dtyp dt) bytes = rest_bytes ->
        concretize_u (UVALUE_ConcatBytes elt_bytes dt) e ->
        concretize_u (UVALUE_ConcatBytes rest_bytes (DTYPE_Packed_struct dts)) es ->
        concretize_u (UVALUE_ConcatBytes bytes (DTYPE_Packed_struct (dt::dts)))
                     (dv <- e;;
                      dvs <- es;;
                      match dvs with
                      | DVALUE_Packed_struct elts =>
                        ret (DVALUE_Packed_struct (dv :: elts))
                      | _ => failwith "ConcatBytes array cons failure."
                      end)


  (* with *)
  (*   concretize_u_dvalue_bytes : list uvalue -> NMap dvalue_byte -> undef_or_err (NMap dvalue_byte) -> Prop := *)
  (* | concretize_u_dvalue_bytes_nil : forall acc, concretize_u_dvalue_bytes [] acc (ret acc) *)
  (* | concretize_u_dvalue_bytes_cons : *)
  (*     forall uv byte_uv dt idx sid cidx dv ins outs, *)
  (*     uv = UVALUE_ExtractByte byte_uv dt idx sid -> *)
  (*     filter_uvalue_sid_matches uv uvs = (ins, outs) -> *)
  (*     concretize_u byte_uv dv -> *)
  (*     concretize_u idx cidx -> *)
  (*     dv_byte = DVALUE_ExtractByte dv dt (Z.to_N (dvalue_int_unsigned cidx)) -> *)
  (*     acc' = monad_fold_right (fun acc '(n, uv) => *)
  (*                              dvb <- uvalue_byte_replace_with_dvalue_byte . *)

  (* The list of bytes in the UVALUE_ConcatBytes does not correspond
     directly to the serialization of the data type. I.e., it is not a
     list of ExtractBytes that directly come from a value of the given
     type.

     This means we essentially have to read the raw byte values and
     combine them together in order to construct a dvalue. 
   *)
  (* | Concretize_ConcatBytes_Raw : *)
  (*     (* extractbytes_to_dvalue is used in concretize_uvalue *) *)
  (*     (* Need to find the entangled bytes *) *)
  (*     (* Concretize the entangled bytes *) *)
  (*     (* Put them back together... *) *)
  (*     uv = UVALUE_ExtractByte byte_uv dt idx sid -> *)
  (*     filter_uvalue_sid_matches uv uvs = (ins, outs) -> *)
  (*     concretize_u byte_uv dv -> *)
  (*     concretize_u idx cidx -> *)
  (*     dv_byte = DVALUE_ExtractByte dv dt (Z.to_N (dvalue_int_unsigned cidx)) -> *)
  (*     concretize_u_bytes bytes dvbs -> *)
  (*     blah dvbs dv *)
  (* . *)

  (* (* *)
  (*     concretize_uvalue_bytes_helper (uvs : list (N * uvalue)) (acc : NMap dvalue_byte) {struct uvs} : undef_or_err (NMap dvalue_byte) *)
  (*       := match uvs with *)
  (*          | [] => ret acc *)
  (*          | ((n, uv)::uvs) => *)
  (*            match uv with *)
  (*            | UVALUE_ExtractByte byte_uv dt idx sid => *)
  (*              let '(ins, outs) := filter_uvalue_sid_matches uv uvs in *)
  (*              (* Concretize first uvalue *) *)
  (*              dv <- concretize_uvalue byte_uv;; *)
  (*              cidx <- concretize_uvalue idx;; *)
  (*              let dv_byte := DVALUE_ExtractByte dv dt (Z.to_N (dvalue_int_unsigned cidx)) in *)
  (*              let acc := @NM.add _ n dv_byte acc in *)
  (*              (* Concretize entangled bytes *) *)
  (*              acc <- monad_fold_right (fun acc '(n, uv) => *)
  (*                                        dvb <- uvalue_byte_replace_with_dvalue_byte uv dv;; *)
  (*                                        ret (@NM.add _ n dvb acc)) ins acc;; *)
  (*              (* Concretize the rest of the bytes *) *)
  (*              concretize_uvalue_bytes_helper outs acc *)
  (*            | _ => lift (failwith "concretize_uvalue_bytes_helper: non-byte in uvs.") *)
  (*            end *)
  (*          end *)

  (*  *) *)

  
(* (*****************************) *)
(*       (* Take a UVALUE_ExtractByte, and replace the uvalue with a given dvalue...  *)

(*          Note: this also concretizes the index. *)
(*        *) *)
(*       uvalue_byte_replace_with_dvalue_byte (uv : uvalue) (dv : dvalue) {struct uv} : undef_or_err dvalue_byte *)
(*         := match uv with *)
(*            | UVALUE_ExtractByte uv dt idx sid => *)
(*              cidx <- concretize_uvalue idx;; *)
(*              ret (DVALUE_ExtractByte dv dt (Z.to_N (dvalue_int_unsigned cidx))) *)
(*            | _ => lift (failwith "uvalue_byte_replace_with_dvalue_byte called with non-UVALUE_ExtractByte value.") *)
(*            end *)

(*       with *)
(*       (* Concretize the uvalues in a list of UVALUE_ExtractBytes... *)

(*        *) *)
(*         (* Pick out uvalue bytes that are the same + have same sid  *)

(*          Concretize these identical uvalues... *)
(*          *) *)

(*       concretize_uvalue_bytes_helper (uvs : list (N * uvalue)) (acc : NMap dvalue_byte) {struct uvs} : undef_or_err (NMap dvalue_byte) *)
(*         := match uvs with *)
(*            | [] => ret acc *)
(*            | ((n, uv)::uvs) => *)
(*              match uv with *)
(*              | UVALUE_ExtractByte byte_uv dt idx sid => *)
(*                let '(ins, outs) := filter_uvalue_sid_matches uv uvs in *)
(*                (* Concretize first uvalue *) *)
(*                dv <- concretize_uvalue byte_uv;; *)
(*                cidx <- concretize_uvalue idx;; *)
(*                let dv_byte := DVALUE_ExtractByte dv dt (Z.to_N (dvalue_int_unsigned cidx)) in *)
(*                let acc := @NM.add _ n dv_byte acc in *)
(*                (* Concretize entangled bytes *) *)
(*                acc <- monad_fold_right (fun acc '(n, uv) => *)
(*                                          dvb <- uvalue_byte_replace_with_dvalue_byte uv dv;; *)
(*                                          ret (@NM.add _ n dvb acc)) ins acc;; *)
(*                (* Concretize the rest of the bytes *) *)
(*                concretize_uvalue_bytes_helper outs acc *)
(*              | _ => lift (failwith "concretize_uvalue_bytes_helper: non-byte in uvs.") *)
(*              end *)
(*            end *)

(*       with *)
(*       concretize_uvalue_bytes (uvs : list uvalue) {struct uvs} : undef_or_err (list dvalue_byte) *)
(*         := *)
(*           let len := length uvs in *)
(*           byte_map <- concretize_uvalue_bytes_helper (zip (Nseq 0 len) uvs) (@NM.empty _);; *)
(*           match NM_find_many (Nseq 0 len) byte_map with *)
(*           | Some dvbs => ret dvbs *)
(*           | None => lift (failwith "concretize_uvalue_bytes: missing indices.") *)
(*           end *)
      
(*       with *)
(*       extractbytes_to_dvalue (uvs : list uvalue) (dt : dtyp) {struct uvs} : undef_or_err dvalue *)
(*         := dvbs <- concretize_uvalue_bytes uvs;; *)
(*            ErrPoison_to_undef_or_err_dvalue (dvalue_bytes_to_dvalue dvbs dt). *)
(*       Set Guard Checking. *)
(*****************************)
  (* | Concretize_ConcatBytes_Int : *)
  (*     forall bytes sz, *)
  (*       (forall byte, In byte bytes -> exists idx, byte = UVALUE_ExtractByte byte idx) *)
  (*         concretize_u (UVALUE_ConcatBytes bytes (DTYPE_I sz)) *)
  (*         _ *)
  (* . *)

  (* (* The thing that's bothering me... *) *)

  (* (*      Converting to DVALUE destroys information... *) *)

  (* (*      Maybe it doesn't matter, though... *) *)

  (* (*    *) *)

  (* (* May not concretize to anything. Should be a type error *) *)
  (* | Concretize_ExtractByte : *)
  (*     forall byte idx c_byte c_idx, *)
  (*       concretize_u byte c_byte -> *)
  (*       concretize_u idx  c_idx -> *)
  (*       concretize_u (UVALUE_ExtractByte byte idx) *)
  (*                    (c_byte' <- c_byte;; *)
  (*                     c_idx'  <- c_idx;; *)
  (*                     match c_byte' with *)
  (*                     | DVALUE_Addr a => _ *)
  (*                     | DVALUE_I1 x => _ *)
  (*                     | DVALUE_I8 x => _ *)
  (*                     | DVALUE_I32 x => _ *)
  (*                     | DVALUE_I64 x => _ *)
  (*                     | DVALUE_IPTR x => _ *)
  (*                     | DVALUE_Double x => _ *)
  (*                     | DVALUE_Float x => _ *)
  (*                     | DVALUE_Poison => _ *)
  (*                     | DVALUE_None => _ *)
  (*                     | DVALUE_Struct fields => _ *)
  (*                     | DVALUE_Packed_struct fields => _ *)
  (*                     | DVALUE_Array elts => _ *)
  (*                     | DVALUE_Vector elts => _ *)
  (*                     end *)
  (*                    ) *)
  (* | Concretize_ConcatBytes_Int : *)
  (*     forall bytes sz, *)
  (*       concretize_u (UVALUE_ConcatBytes bytes (DTYPE_I sz)) *)
  (*                    (ret DVALUE_None) *)
  .

  Definition concretize (uv: uvalue) (dv : dvalue) := concretize_u uv (ret dv).

  End ConcretizeInductive.
End Make.
