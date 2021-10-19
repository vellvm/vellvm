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
     Utils.MonadReturnsLaws
     Syntax.LLVMAst
     Syntax.DynamicTypes
     Syntax.DataLayout
     Semantics.DynamicValues
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

(*
Module Type Concretize (Addr:MemoryAddress.ADDRESS)(SIZEOF: Sizeof)(LLVMIO: LLVM_INTERACTIONS(Addr)(SIZEOF)).
  Import LLVMIO.
  Parameter concretize : uvalue -> dvalue -> Prop.
  Parameter concretize_u : uvalue -> err_or_ub dvalue -> Prop.
  Parameter concretize_uvalue : uvalue -> err_or_ub dvalue.

  Parameter Concretize_Undef : forall dt dv,
      dvalue_has_dtyp dv dt ->
      concretize_u (UVALUE_Undef dt) (ret dv).

  Parameter Concretize_IBinop : forall iop uv1 e1 uv2 e2,
      concretize_u uv1 e1 ->
      concretize_u uv2 e2 ->
      concretize_u (UVALUE_IBinop iop uv1 uv2)
                   (dv1 <- e1 ;;
                    dv2 <- e2 ;;
                    (eval_iop iop dv1 dv2)).

  Parameter concretize_equation : forall (uv: uvalue) (dv : dvalue),
      concretize uv dv = concretize_u uv (ret dv).

End Concretize.
*)

Module Make(Addr:MemoryAddress.ADDRESS)(IP:MemoryAddress.INTPTR)(SIZEOF: Sizeof)(LLVMIO: LLVM_INTERACTIONS(Addr)(IP)(SIZEOF))(PTOI:PTOI(Addr))(PROVENANCE:PROVENANCE(Addr))(ITOP:ITOP(Addr)(PROVENANCE))(GEP:GEPM(Addr)(IP)(SIZEOF)(LLVMIO))(BYTE_IMPL:ByteImpl(Addr)(IP)(SIZEOF)(LLVMIO)).

  Import LLVMIO.
  Import SIZEOF.
  Import PTOI.
  Import PROVENANCE.
  Import ITOP.
  Import DV.
  Import GEP.
  Open Scope list.

  Module BYTE := Byte Addr IP SIZEOF LLVMIO BYTE_IMPL.
  Export BYTE.

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
         | UVALUE_IPTR x => Z.eqb (IP.to_Z x) i
         | _ => false
         end.

    Definition dvalue_int_unsigned (dv : dvalue) : Z
      := match dv with
         | DVALUE_I1 x => unsigned x
         | DVALUE_I8 x => unsigned x
         | DVALUE_I32 x => unsigned x
         | DVALUE_I64 x => unsigned x
         | DVALUE_IPTR x => IP.to_Z x (* TODO: unsigned???? *)
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
      | DTYPE_IPTR => ret (DVALUE_IPTR IP.zero)
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

    Ltac do_it := constructor; cbn; auto; fail.

    Lemma dvalue_default : forall t v,
        inr v = (default_dvalue_of_dtyp t) ->
        dvalue_has_dtyp v t.
    Proof.
      intros t v. revert v.
      induction t; try do_it;
        try (intros; subst; inversion H; constructor).
      - intros. subst. cbn in H.
        unfold default_dvalue_of_dtyp_i in H.
        destruct (@IX_supported_dec a).
        * inversion i; subst; cbn in H; inversion H; constructor; auto.
        * rewrite unsupported_cases in H; auto. inversion H.
      - intros. subst. inversion H. clear H.
        induction sz.
        + cbn in H1.
          destruct (default_dvalue_of_dtyp t) eqn: HT. inv H1. inv H1.
          pose proof DVALUE_Array_typ.
          specialize (H nil (N.to_nat 0) t).
          rewrite Nnat.N2Nat.id in H.
          apply H. auto. auto.
        + cbn in H1.
          destruct (default_dvalue_of_dtyp t) eqn: HT. inv H1. inv H1.
          pose proof DVALUE_Array_typ as ARR.
          specialize (ARR (repeat d (Pos.to_nat p)) (N.to_nat (N.pos p)) t).
          rewrite Nnat.N2Nat.id in ARR.
          cbn in *.
          apply ARR.
          * apply forall_repeat_true.
            apply IHt. reflexivity.
          * apply repeat_length.
      - revert H. induction fields.
        + intros. inv H0. constructor.
        + intros.
          assert (forall u : dtyp,
              In u fields ->
              forall v : dvalue,
                inr v = default_dvalue_of_dtyp u -> dvalue_has_dtyp v u).
          { intros. apply H. apply in_cons. auto. auto. }
          specialize (IHfields H1). clear H1.
          Opaque map_monad.
          (* Reduce H0 *)
          cbn in H0.
          rewrite list_cons_app in H0.
          rewrite map_monad_app in H0. cbn in H0.
          Transparent map_monad.
          unfold map_monad at 1 in H0.
          Opaque map_monad. cbn in H0.
          destruct (default_dvalue_of_dtyp a) eqn: A_DEFAULT.
          inv H0.
          destruct (map_monad default_dvalue_of_dtyp fields) eqn: FIELDS.
          inv H0.
          inv H0. constructor. apply H. apply in_eq.
          symmetry. auto.
          apply IHfields. cbn. rewrite FIELDS. reflexivity.
      - revert H. induction fields.
        + intros. inv H0. constructor.
        + intros.
          assert (forall u : dtyp,
              In u fields ->
              forall v : dvalue,
                inr v = default_dvalue_of_dtyp u -> dvalue_has_dtyp v u).
          { intros. apply H. apply in_cons. auto. auto. }
          specialize (IHfields H1). clear H1.
          Opaque map_monad.
          (* Reduce H0 *)
          cbn in H0.
          rewrite list_cons_app in H0.
          rewrite map_monad_app in H0. cbn in H0.
          Transparent map_monad.
          unfold map_monad at 1 in H0.
          Opaque map_monad. cbn in H0.
          destruct (default_dvalue_of_dtyp a) eqn: A_DEFAULT.
          inv H0.
          destruct (map_monad default_dvalue_of_dtyp fields) eqn: FIELDS.
          inv H0.
          inv H0. constructor. apply H. apply in_eq.
          symmetry. auto.
          apply IHfields. cbn. rewrite FIELDS. reflexivity.
      - intros. subst. inversion H. clear H.
        revert H1. revert v. revert IHt. revert t.
        induction sz.
        + intros. cbn in H1.
          pose proof DVALUE_Vector_typ.
          specialize (H nil (N.to_nat 0)).
          rewrite Nnat.N2Nat.id in H.
          destruct t; inv H1;
              try
                (apply H;
                 [constructor | constructor |
                  unfold vector_dtyp; intuition]).
          destruct (default_dvalue_of_dtyp_i sz) eqn: HI; inv H2.
          apply H. constructor. auto. unfold vector_dtyp. left.
          exists sz. reflexivity.
        + intros. cbn in H1.
          destruct t; inv H1;
            try (
                rewrite <- positive_nat_N;
                   constructor; [apply forall_repeat_true ; constructor |
                          apply repeat_length |
                          unfold vector_dtyp ; intuition ]).
          destruct (default_dvalue_of_dtyp_i sz) eqn: SZ; inv H0.
            pose proof DVALUE_Vector_typ.
            rewrite <- positive_nat_N. apply H.
            apply forall_repeat_true. apply IHt. symmetry. auto.
            apply repeat_length.
            left. exists sz. reflexivity.
    Qed.

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

      (* TODO: Move this??? *)
      Inductive Poisonable (A : Type) : Type :=
      | Unpoisoned : A -> Poisonable A
      | Poison : forall (dt : dtyp), Poisonable A
      .

      Arguments Unpoisoned {A} a.
      Arguments Poison {A}.

      Global Instance MonadPoisonable : Monad Poisonable
        := { ret  := @Unpoisoned;
             bind := fun _ _ ma mab => match ma with
                                    | Poison dt => Poison dt
                                    | Unpoisoned v => mab v
                                    end
        }.

      Class RAISE_POISON (M : Type -> Type) :=
        { raise_poison : forall {A}, dtyp -> M A }.

      Global Instance RAISE_POISON_Poisonable : RAISE_POISON Poisonable :=
        { raise_poison := fun A dt => Poison dt }.

      #[global] Instance RAISE_POISON_E_MT {M : Type -> Type} {MT : (Type -> Type) -> Type -> Type} `{MonadT (MT M) M} `{RAISE_POISON M} : RAISE_POISON (MT M) :=
        { raise_poison := fun A dt => lift (raise_poison dt);
        }.

      Definition ErrOOMPoison := eitherT ERR_MESSAGE (eitherT OOM_MESSAGE Poisonable).

      Definition ErrOOMPoison_handle_poison_dv {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_OOM M} (ep : ErrOOMPoison dvalue) : M dvalue
        := match unEitherT (unEitherT ep) with
           | Unpoisoned edv =>
               match edv with
               | inl (OOM_message msg) => raise_oom msg
               | inr (inl (ERR_message msg)) => raise_error msg
               | inr (inr val) => ret val
               end
           | Poison dt => ret (DVALUE_Poison dt)
           end.

      (* Walk through a list *)
      (* Returns field index + number of bytes remaining *)
      Fixpoint extract_field_byte_helper {M} `{Monad M} `{RAISE_ERROR M} (fields : list dtyp) (field_idx : N) (byte_idx : N) : M (dtyp * (N * N))%type
        := match fields with
           | [] =>
               raise_error "No fields left for byte-indexing..."
           | (x::xs) =>
             let sz := sizeof_dtyp x
             in if N.ltb byte_idx sz
                then ret (x, (field_idx, byte_idx))
                else extract_field_byte_helper xs (N.succ field_idx) (byte_idx - sz)
           end.

      Definition extract_field_byte {M} `{Monad M} `{RAISE_ERROR M} (fields : list dtyp) (byte_idx : N) : M (dtyp * (N * N))%type
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
      Program Fixpoint dvalue_extract_byte {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_POISON M} (dv : dvalue) (dt : dtyp) (idx : Z) {measure (dvalue_measure dv)} : M Z
        := match dv with
           | DVALUE_I1 x
           | DVALUE_I8 x
           | DVALUE_I32 x
           | DVALUE_I64 x =>
               ret (extract_byte_vint x idx)
           | DVALUE_IPTR x =>
               ret (extract_byte_Z (IP.to_Z x) idx)
           | DVALUE_Addr addr =>
               (* Note: this throws away provenance *)
               ret (extract_byte_Z (ptr_to_int addr) idx)
           | DVALUE_Float f =>
               ret (extract_byte_Z (unsigned (Float32.to_bits f)) idx)
           | DVALUE_Double d =>
               ret (extract_byte_Z (unsigned (Float.to_bits d)) idx)
           | DVALUE_Poison dt => raise_poison dt
           | DVALUE_None =>
               (* TODO: Not sure if this should be an error, poison, or what. *)
               raise_error "dvalue_extract_byte on DVALUE_None"

           (* TODO: Take padding into account. *)
           | DVALUE_Struct fields =>
               match dt with
               | DTYPE_Struct dts =>
                   (* Step to field which contains the byte we want *)
                   '(fdt, (field_idx, byte_idx)) <- extract_field_byte dts (Z.to_N idx);;
                   match List.nth_error fields (N.to_nat field_idx) with
                   | Some f =>
                       (* call dvalue_extract_byte recursively on the field *)
                       dvalue_extract_byte f fdt (Z.of_N byte_idx )
                   | None =>
                       raise_error "dvalue_extract_byte: more fields in DVALUE_Struct than in dtyp."
                   end
               | _ => raise_error "dvalue_extract_byte: type mismatch on DVALUE_Struct."
               end

           | DVALUE_Packed_struct fields =>
               match dt with
               | DTYPE_Packed_struct dts =>
                   (* Step to field which contains the byte we want *)
                   '(fdt, (field_idx, byte_idx)) <- extract_field_byte dts (Z.to_N idx);;
                   match List.nth_error fields (N.to_nat field_idx) with
                   | Some f =>
                       (* call dvalue_extract_byte recursively on the field *)
                       dvalue_extract_byte f fdt (Z.of_N byte_idx )
                   | None =>
                       raise_error "dvalue_extract_byte: more fields in DVALUE_Packed_struct than in dtyp."
                   end
               | _ => raise_error "dvalue_extract_byte: type mismatch on DVALUE_Packed_struct."
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
                       raise_error "dvalue_extract_byte: more fields in dvalue than in dtyp."
                   end
               | _ =>
                   raise_error "dvalue_extract_byte: type mismatch on DVALUE_Array."
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
                       raise_error "dvalue_extract_byte: more fields in dvalue than in dtyp."
                   end
               | _ =>
                   raise_error "dvalue_extract_byte: type mismatch on DVALUE_Vector."
               end
           end.

      (* Taking a byte out of a dvalue...

      Unlike UVALUE_ExtractByte, I don't think this needs an sid
      (store id). There should be no nondeterminism in this value. *)
      Inductive dvalue_byte : Type :=
      | DVALUE_ExtractByte (dv : dvalue) (dt : dtyp) (idx : N) : dvalue_byte
      .

      Definition dvalue_byte_value {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_POISON M} (db : dvalue_byte) : M Z
        := match db with
           | DVALUE_ExtractByte dv dt idx =>
             dvalue_extract_byte dv dt (Z.of_N idx)
           end.

      Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia].
      Program Fixpoint dvalue_bytes_to_dvalue {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_POISON M} `{RAISE_OOM M} (dbs : list dvalue_byte) (dt : dtyp) {measure (dtyp_measure dt)} : M dvalue
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
             | _ => raise_error "Unsupported integer size."
             end
           | DTYPE_IPTR =>
             zs <- map_monad dvalue_byte_value dbs;;
             val <- lift_OOM (IP.from_Z (concat_bytes_Z zs));;
             ret (DVALUE_IPTR val)
           | DTYPE_Pointer =>
             (* TODO: not sure if this should be wildcard provenance.
                TODO: not sure if this should truncate iptr value...
              *)
             zs <- map_monad dvalue_byte_value dbs;;
             ret (DVALUE_Addr (int_to_ptr (concat_bytes_Z zs) wildcard_prov))
           | DTYPE_Void =>
             raise_error "dvalue_bytes_to_dvalue on void type."
           | DTYPE_Half =>
             raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_Half."
           | DTYPE_Float =>
             zs <- map_monad dvalue_byte_value dbs;;
             ret (DVALUE_Float (Float32.of_bits (concat_bytes_Z_vint zs)))
           | DTYPE_Double =>
             zs <- map_monad dvalue_byte_value dbs;;
             ret (DVALUE_Double (Float.of_bits (concat_bytes_Z_vint zs)))
           | DTYPE_X86_fp80 =>
             raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_X86_fp80."
           | DTYPE_Fp128 =>
             raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_Fp128."
           | DTYPE_Ppc_fp128 =>
             raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_Ppc_fp128."
           | DTYPE_Metadata =>
             raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_Metadata."
           | DTYPE_X86_mmx =>
             raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_X86_mmx."
           | DTYPE_Array sz t =>
             let sz := sizeof_dtyp t in
             elt_bytes <- lift_err_RAISE_ERROR (split_every sz dbs);;
             elts <- map_monad (fun es => dvalue_bytes_to_dvalue es t) elt_bytes;;
             ret (DVALUE_Array elts)
           | DTYPE_Vector sz t =>
             let sz := sizeof_dtyp t in
             elt_bytes <- lift_err_RAISE_ERROR (split_every sz dbs);;
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
                 raise_error "dvalue_bytes_to_dvalue: DTYPE_Struct recursive call did not return a struct."
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
                 raise_error "dvalue_bytes_to_dvalue: DTYPE_Packed_struct recursive call did not return a struct."
               end
             end
           | DTYPE_Opaque =>
             raise_error "dvalue_bytes_to_dvalue: unsupported DTYPE_Opaque."
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
           | UVALUE_Poison t => "UVALUE_Poison"
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


        Inductive concretize_u : uvalue -> err_or_ub dvalue -> Prop :=
        Fixpoint concretize_uvalue (u : uvalue) {struct u} : err_or_ub dvalue :=

        

        Maybe it should be a monad???


        M (err_or_ub dvalue)

        Identity for actual concretization...

        M X = X -> Prop otherwise...

        Is X -> Prop a monad?
       *)

      Definition RefineProp (X : Type) : Type := err_or_ub X -> Prop.

      Definition bind_RefineProp {A B : Type} (pa : RefineProp A) (k : A -> RefineProp B) : RefineProp B
        := (fun mb => exists (ma : err_or_ub A) (k' : A -> err_or_ub B),
                pa ma /\
                Monad.eq1 (Monad.bind ma k') mb /\
                (forall a, MReturns a ma -> k a (k' a))).
      
      #[global] Instance Monad_RefineProp : Monad RefineProp :=
        {|
        ret := fun _ x y => Monad.eq1 (ret x) y;
        bind := @bind_RefineProp
        |}.

      From ITree Require Import Basics.Monad.

      #[global] Instance EQM_RefineProp : Eq1 RefineProp.
      Proof.
        unfold Eq1.
        intros A X Y.
        refine (forall ma, Y ma -> X ma).
      Defined.

      Lemma RefineProp_bind_ret_l :
        forall (A B : Type) (f : A -> RefineProp B) (x : A),
          x <- ret x;; f x ≈ f x.
      Proof.
        intros A B f x.
        unfold eq1, EQM_RefineProp; cbn.
        intros ma H.
        unfold bind_RefineProp.

        exists ({| unERR_OR_UB := {| unEitherT := inr (inr x) |} |}).
        exists (fun _ => ma).
        split; eauto.
        cbn.
        split.
        + destruct ma as [[[uba | [erra | a]]]] eqn:Hma; cbn; auto.
        + intros; subst; auto.
      Qed.

      Lemma RefineProp_bind_ret_r :
        forall (A : Type) (x : RefineProp A), y <- x;; ret y ≈ x.
      Proof.
        intros A x.
        unfold eq1, EQM_RefineProp; cbn.
        intros ma H.
        unfold bind_RefineProp.

        exists ma.
        exists ret.

        split; eauto.
        split.
        + apply bind_ret_r.
        + reflexivity.  
      Qed.

      Lemma RefineProp_bind_bind :
        forall (A B C : Type) (ma : RefineProp A) (fab : A -> RefineProp B) (fbc : B -> RefineProp C),
          b <- (a <- ma;; fab a);; fbc b ≈ a <- ma;; b <- fab a;; fbc b.
      Proof.
        intros A B C ma fab fbc.

        unfold RefineProp in *.
        unfold eq1, EQM_RefineProp; cbn.
        unfold bind_RefineProp.

        intros ec H.
        destruct H as (ea & k' & paea & ea_eq_ec & REST).

        destruct ea as [[[uba | [erra | a]]]] eqn:Hma; cbn; auto.

        { (* The 'a' action raises ub *)
          exists (raise_ub "blah").
          exists (fun b => ec).
          split.

          { eexists.
            exists (fun a => raise_ub "bogus").

            split.
            apply paea.
            cbn.
            split; auto.
            intros.
            destruct uba; inversion H.
          }

          split.

          break_match.
          cbn.
          destruct unERR_OR_UB.
          destruct unEitherT; cbn; auto.
          destruct s; cbn; auto.

          destruct ec as [[[uba' | [erra' | a']]]] eqn:Hma'; cbn; auto.
          intros b H.
          inversion H.
        }

        { (* The 'a' action raises a failure *)
          exists (raise_error "blah").
          exists (fun b => ec).
          split.

          { eexists.
            exists (fun a => raise_error "bogus").

            split.
            apply paea.
            cbn.
            split; auto.
            intros.
            destruct erra; inversion H.
          }

          split.

          break_match.
          cbn.
          destruct unERR_OR_UB.
          destruct unEitherT; cbn; auto.
          destruct s; cbn; auto.

          destruct ec as [[[uba' | [erra' | a']]]] eqn:Hma'; cbn; auto.
          intros b H.
          inversion H.
        }

        { (* The 'a' action actually returns a value *)
          specialize (REST a).
          forward REST; [reflexivity|].
          destruct REST as (mb & kb & fmb & eqkb & RETS).

          exists mb.
          exists kb.

          split.
          { exists ea.
            exists (fun _ => mb).
            
            split; subst; auto.
            split.
            destruct mb as [[[ubb | [errb | b]]]] eqn:Hmb; cbn; split; auto.

            intros a' RETSa.
            cbn in RETSa; subst; auto.
          }

          split.
          { destruct mb as [[[ubb | [errb | b]]]] eqn:Hmb; cbn; auto.
            destruct (kb b) as [[[ubkbb | [errkbb | kbb]]]] eqn:Hkbb; cbn in eqkb; subst; cbn; auto.

            rewrite Hkbb in eqkb; cbn in eqkb.
            destruct (k' a) as [[[ubk'a | [errk'a | k'a]]]] eqn:Hk'a; cbn in ea_eq_ec; try contradiction.
            subst.

            destruct ec as [[[ubc | [errc | c]]]] eqn:Hmc; cbn; cbn in ea_eq_ec; auto;
              rewrite Hk'a in ea_eq_ec; cbn in ea_eq_ec; try contradiction.

            auto.
          }

          intros b RETSb.
          auto.
        }
      Qed.

      Require Import Morphisms.
      #[global] Instance RefineProp_Proper_bind {A B : Type} :
        @Proper (RefineProp A -> (A -> RefineProp B) -> RefineProp B)
                (@eq1 RefineProp EQM_RefineProp A ==>
                      @pointwise_relation A (RefineProp B) (@eq1 RefineProp EQM_RefineProp B) ==>
                      @eq1 RefineProp EQM_RefineProp B)
                (@bind RefineProp Monad_RefineProp A B).
      Proof.
        unfold Proper, respectful.
        intros A1 A2 H pa1 pa2 pw EB.

        unfold RefineProp in *.
        unfold eq1, EQM_RefineProp; cbn.
        unfold bind_RefineProp.

        intros Bind2.

        destruct Bind2 as (ma & k' & pa1ma & meq & REST).

        exists ma.
        exists k'.
        split; auto.
        split; auto.
        intros a Rets.
        specialize (REST a Rets).

        unfold pointwise_relation in pw.
        specialize (pw a).

        unfold eq1, EQM_RefineProp in pw.
        auto.
      Qed.

      #[global] Instance MonadLawsE_RefineProp : MonadLawsE RefineProp.
      Proof.
        split.
        - apply RefineProp_bind_ret_l.
        - apply RefineProp_bind_ret_r.
        - apply RefineProp_bind_bind.
        - apply @RefineProp_Proper_bind.
      Defined.

      Section Concretize.
        Context (M : Type -> Type).
        Context {HM : Monad M}.
        Variable undef_handler : dtyp -> M dvalue.
        Context (ERR_M : Type -> Type). (* Monad encapsulating errors, ub, oom *)
        Context {HM_ERR : Monad ERR_M}.
        Context {ERR : RAISE_ERROR ERR_M}.
        Context {UB : RAISE_UB ERR_M}.
        Context {OOM : RAISE_OOM ERR_M}.
        Variable lift_ue : forall {A}, ERR_M A -> M A.

        (* TODO: satisfy the termination checker here. *)
        (* M will be err_or_ub / MPropT err_or_ub? *)
        Unset Guard Checking.
        (* Define a sum type f a, g b.... a + b. Mutual recursive
           function as one big function with sum type to select between
           which "function" is being called *)
        Fixpoint concretize_uvalueM (u : uvalue) {struct u} : M dvalue:=
          match u with
          | UVALUE_Addr a                          => ret (DVALUE_Addr a)
          | UVALUE_I1 x                            => ret (DVALUE_I1 x)
          | UVALUE_I8 x                            => ret (DVALUE_I8 x)
          | UVALUE_I32 x                           => ret (DVALUE_I32 x)
          | UVALUE_I64 x                           => ret (DVALUE_I64 x)
          | UVALUE_IPTR x                          => ret (DVALUE_IPTR x)
          | UVALUE_Double x                        => ret (DVALUE_Double x)
          | UVALUE_Float x                         => ret (DVALUE_Float x)
          | UVALUE_Undef t                         => undef_handler t
          | UVALUE_Poison t                        => ret (DVALUE_Poison t)
          | UVALUE_None                            => ret DVALUE_None
          | UVALUE_Struct fields                   => 'dfields <- map_monad concretize_uvalueM fields ;;
                                                     ret (DVALUE_Struct dfields)
          | UVALUE_Packed_struct fields            => 'dfields <- map_monad concretize_uvalueM fields ;;
                                                     ret (DVALUE_Packed_struct dfields)
          | UVALUE_Array elts                      => 'delts <- map_monad concretize_uvalueM elts ;;
                                                     ret (DVALUE_Array delts)
          | UVALUE_Vector elts                     => 'delts <- map_monad concretize_uvalueM elts ;;
                                                     ret (DVALUE_Vector delts)
          | UVALUE_IBinop iop v1 v2                => dv1 <- concretize_uvalueM v1 ;;
                                                     dv2 <- concretize_uvalueM v2 ;;
                                                     lift_ue (eval_iop iop dv1 dv2)
          | UVALUE_ICmp cmp v1 v2                  => dv1 <- concretize_uvalueM v1 ;;
                                                     dv2 <- concretize_uvalueM v2 ;;
                                                     lift_ue (eval_icmp cmp dv1 dv2)
          | UVALUE_FBinop fop fm v1 v2             => dv1 <- concretize_uvalueM v1 ;;
                                                     dv2 <- concretize_uvalueM v2 ;;
                                                     lift_ue (eval_fop fop dv1 dv2)
          | UVALUE_FCmp cmp v1 v2                  => dv1 <- concretize_uvalueM v1 ;;
                                                     dv2 <- concretize_uvalueM v2 ;;
                                                     lift_ue (eval_fcmp cmp dv1 dv2)

          | UVALUE_Conversion conv t_from v t_to    =>
            dv <- concretize_uvalueM v ;;
            match get_conv_case conv t_from dv t_to with
            | Conv_PtoI x =>
              match x, t_to with
              | DVALUE_Addr addr, DTYPE_I sz =>
                lift_ue (coerce_integer_to_int sz (ptr_to_int addr))
              | _, _ =>
                lift_ue (raise_error "Invalid PTOI conversion")
              end
            | Conv_ItoP x => ret (DVALUE_Addr (int_to_ptr (dvalue_int_unsigned x) wildcard_prov))
            | Conv_Pure x => ret x
            | Conv_Illegal s => lift_ue (raise_error s)
            end

          | UVALUE_GetElementPtr t ua uvs =>
            da <- concretize_uvalueM ua;;
            dvs <- map_monad concretize_uvalueM uvs;;
            match handle_gep t da dvs with
            | inr dv  => ret dv
            | inl err => lift_ue (raise_error err)
            end

          | UVALUE_ExtractValue uv idxs =>
            str <- concretize_uvalueM uv;;
            let fix loop str idxs : ERR_M dvalue :=
                match idxs with
                | [] => ret str
                | i :: tl =>
                  v <- index_into_str_dv str i ;;
                  loop v tl
                end in
            lift_ue (loop str idxs)

          | UVALUE_Select cond v1 v2 =>
            dcond <- concretize_uvalueM cond;;
            uv <- lift_ue (eval_select dcond v1 v2);;
            concretize_uvalueM uv

          | UVALUE_ConcatBytes bytes dt =>
            match N.eqb (N.of_nat (length bytes)) (sizeof_dtyp dt), all_extract_bytes_from_uvalue bytes with
            | true, Some uv => concretize_uvalueM uv
            | _, _ => extractbytes_to_dvalue bytes dt
            end

          | UVALUE_ExtractByte byte dt idx sid =>
            (* TODO: maybe this is just an error? ExtractByte should be guarded by ConcatBytes? *)
            lift_ue (raise_error "Attempting to concretize UVALUE_ExtractByte, should not happen.")

          | _ => lift_ue (raise_error ("concretize_uvalueM: Attempting to convert a partially non-reduced uvalue to dvalue. Should not happen: " ++ uvalue_constructor_string u))

          end

        with

        (* Take a UVALUE_ExtractByte, and replace the uvalue with a given dvalue... 

         Note: this also concretizes the index.
         *)
        uvalue_byte_replace_with_dvalue_byte (uv : uvalue) (dv : dvalue) {struct uv} : M dvalue_byte
          := match uv with
             | UVALUE_ExtractByte uv dt idx sid =>
               cidx <- concretize_uvalueM idx;;
               ret (DVALUE_ExtractByte dv dt (Z.to_N (dvalue_int_unsigned cidx)))
             | _ => lift_ue (raise_error "uvalue_byte_replace_with_dvalue_byte called with non-UVALUE_ExtractByte value.")
             end

        with
        (* Concretize the uvalues in a list of UVALUE_ExtractBytes...

         *)
        (* Pick out uvalue bytes that are the same + have same sid 

         Concretize these identical uvalues...
         *)

        concretize_uvalue_bytes_helper (uvs : list (N * uvalue)) (acc : NMap dvalue_byte) {struct uvs} : M (NMap dvalue_byte)
          := match uvs with
             | [] => ret acc
             | ((n, uv)::uvs) =>
               match uv with
               | UVALUE_ExtractByte byte_uv dt idx sid =>
                 let '(ins, outs) := filter_uvalue_sid_matches uv uvs in
                 (* Concretize first uvalue *)
                 dv <- concretize_uvalueM byte_uv;;
                 cidx <- concretize_uvalueM idx;;
                 let dv_byte := DVALUE_ExtractByte dv dt (Z.to_N (dvalue_int_unsigned cidx)) in
                 let acc := @NM.add _ n dv_byte acc in
                 (* Concretize entangled bytes *)
                 acc <- monad_fold_right (fun acc '(n, uv) =>
                                           dvb <- uvalue_byte_replace_with_dvalue_byte uv dv;;
                                           ret (@NM.add _ n dvb acc)) ins acc;;
                 (* Concretize the rest of the bytes *)
                 concretize_uvalue_bytes_helper outs acc
               | _ => lift_ue (raise_error "concretize_uvalue_bytes_helper: non-byte in uvs.")
               end
             end

        with
        concretize_uvalue_bytes (uvs : list uvalue) {struct uvs} : M (list dvalue_byte)
          :=
            let len := length uvs in
            byte_map <- concretize_uvalue_bytes_helper (zip (Nseq 0 len) uvs) (@NM.empty _);;
            match NM_find_many (Nseq 0 len) byte_map with
            | Some dvbs => ret dvbs
            | None => lift_ue (raise_error "concretize_uvalue_bytes: missing indices.")
            end
              
        with
        extractbytes_to_dvalue (uvs : list uvalue) (dt : dtyp) {struct uvs} : M dvalue
          := dvbs <- concretize_uvalue_bytes uvs;;
             lift_ue (ErrOOMPoison_handle_poison_dv (dvalue_bytes_to_dvalue dvbs dt)).

        Lemma concretize_uvalueM_equation :
          forall u,
            concretize_uvalueM u =
          match u with
          | UVALUE_Addr a                          => ret (DVALUE_Addr a)
          | UVALUE_I1 x                            => ret (DVALUE_I1 x)
          | UVALUE_I8 x                            => ret (DVALUE_I8 x)
          | UVALUE_I32 x                           => ret (DVALUE_I32 x)
          | UVALUE_I64 x                           => ret (DVALUE_I64 x)
          | UVALUE_IPTR x                          => ret (DVALUE_IPTR x)
          | UVALUE_Double x                        => ret (DVALUE_Double x)
          | UVALUE_Float x                         => ret (DVALUE_Float x)
          | UVALUE_Undef t                         => undef_handler t
          | UVALUE_Poison t                        => ret (DVALUE_Poison t)
          | UVALUE_None                            => ret DVALUE_None
          | UVALUE_Struct fields                   => 'dfields <- map_monad concretize_uvalueM fields ;;
                                                     ret (DVALUE_Struct dfields)
          | UVALUE_Packed_struct fields            => 'dfields <- map_monad concretize_uvalueM fields ;;
                                                     ret (DVALUE_Packed_struct dfields)
          | UVALUE_Array elts                      => 'delts <- map_monad concretize_uvalueM elts ;;
                                                     ret (DVALUE_Array delts)
          | UVALUE_Vector elts                     => 'delts <- map_monad concretize_uvalueM elts ;;
                                                     ret (DVALUE_Vector delts)
          | UVALUE_IBinop iop v1 v2                => dv1 <- concretize_uvalueM v1 ;;
                                                     dv2 <- concretize_uvalueM v2 ;;
                                                     lift_ue (eval_iop iop dv1 dv2)
          | UVALUE_ICmp cmp v1 v2                  => dv1 <- concretize_uvalueM v1 ;;
                                                     dv2 <- concretize_uvalueM v2 ;;
                                                     lift_ue (eval_icmp cmp dv1 dv2)
          | UVALUE_FBinop fop fm v1 v2             => dv1 <- concretize_uvalueM v1 ;;
                                                     dv2 <- concretize_uvalueM v2 ;;
                                                     lift_ue (eval_fop fop dv1 dv2)
          | UVALUE_FCmp cmp v1 v2                  => dv1 <- concretize_uvalueM v1 ;;
                                                     dv2 <- concretize_uvalueM v2 ;;
                                                     lift_ue (eval_fcmp cmp dv1 dv2)

          | UVALUE_Conversion conv t_from v t_to    =>
            dv <- concretize_uvalueM v ;;
            match get_conv_case conv t_from dv t_to with
            | Conv_PtoI x =>
              match x, t_to with
              | DVALUE_Addr addr, DTYPE_I sz =>
                lift_ue (coerce_integer_to_int sz (ptr_to_int addr))
              | _, _ =>
                lift_ue (raise_error "Invalid PTOI conversion")
              end
            | Conv_ItoP x => ret (DVALUE_Addr (int_to_ptr (dvalue_int_unsigned x) wildcard_prov))
            | Conv_Pure x => ret x
            | Conv_Illegal s => lift_ue (raise_error s)
            end

          | UVALUE_GetElementPtr t ua uvs =>
            da <- concretize_uvalueM ua;;
            dvs <- map_monad concretize_uvalueM uvs;;
            match handle_gep t da dvs with
            | inr dv  => ret dv
            | inl err => lift_ue (raise_error err)
            end

          | UVALUE_ExtractValue uv idxs =>
            str <- concretize_uvalueM uv;;
            let fix loop str idxs : ERR_M dvalue :=
                match idxs with
                | [] => ret str
                | i :: tl =>
                  v <- index_into_str_dv str i ;;
                  loop v tl
                end in
            lift_ue (loop str idxs)

          | UVALUE_Select cond v1 v2 =>
            dcond <- concretize_uvalueM cond;;
            uv <- lift_ue (eval_select dcond v1 v2);;
            concretize_uvalueM uv

          | UVALUE_ConcatBytes bytes dt =>
            match N.eqb (N.of_nat (length bytes)) (sizeof_dtyp dt), all_extract_bytes_from_uvalue bytes with
            | true, Some uv => concretize_uvalueM uv
            | _, _ => extractbytes_to_dvalue bytes dt
            end

          | UVALUE_ExtractByte byte dt idx sid =>
            (* TODO: maybe this is just an error? ExtractByte should be guarded by ConcatBytes? *)
            lift_ue (raise_error "Attempting to concretize UVALUE_ExtractByte, should not happen.")

          | _ => lift_ue (raise_error ("concretize_uvalueM: Attempting to convert a partially non-reduced uvalue to dvalue. Should not happen: " ++ uvalue_constructor_string u))

          end.
        Proof.
          intros u.
          unfold concretize_uvalueM.
          destruct u; try reflexivity.
        Qed.

        Set Guard Checking.
      End Concretize.

      Arguments concretize_uvalueM {_ _}.

      Definition concretize_uvalue {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M} `{RAISE_OOM M}
                 (uv : uvalue) : M dvalue
        := concretize_uvalueM (fun dt => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt)) _ _ _ _ _ (fun _ x => x) uv.

      Definition concretize_u (uv : uvalue) : RefineProp dvalue.
        refine (concretize_uvalueM
                  (fun dt => _)
                  (eitherT ERR_MESSAGE (eitherT UB_MESSAGE (eitherT OOM_MESSAGE IdentityMonad.ident))) (* Err / oom / ub monad *)
                  _
                  _
                  _
                  _
                  (fun _ x => _) uv).

        (* Undef handler *)
        { unfold RefineProp.
         refine (fun edv => match unERR_OR_UB edv with
                    | mkEitherT (inr (inr dv)) =>
                      (* As long as the dvalue has the same type, it's a refinement *)
                      dvalue_has_dtyp dv dt
                    | _ => False
                    end).
        }

        (* lift_ue *)
        { unfold RefineProp.
          intros ue.

          (* Is x or ue the thing that should be the refinement? *)
          (* I think ue is the refinement *)
          destruct x as [[[ubx | [errx | x]]]].
          - (* UB *)
            exact True.
          - (* ERR *)
            exact True.
          - destruct ue as [[[ubue | [errue | ue]]]].
            + exact False.
            + exact False.
            + exact (x = ue).
        }
      Defined.

      Definition concretize_u_succeeds (uv : uvalue) : RefineProp dvalue.
        refine (concretize_uvalueM (fun dt => _) (fun _ x => _) uv).

        (* Undef handler *)
        { unfold RefineProp.
          refine (fun edv => match unERR_OR_UB edv with
                          | mkEitherT (inr (inr dv)) =>
                              (* As long as the dvalue has the same type, it's a refinement *)
                              dvalue_has_dtyp dv dt
                          | _ => False
                          end).
        }

        (* lift_ue *)
        { unfold RefineProp.
          intros ue.

          destruct x as [[[ubx | [errx | x]]]].
          - (* UB *)
            exact False.
          - (* ERR *)
            exact False.
          - destruct ue as [[[ubue | [errue | ue]]]].
            + exact False.
            + exact False.
            + (* This is the only case where concretize succeeds without failure anywhere *)
              exact (x = ue).
        }
      Defined.
  
      Definition concretize (uv: uvalue) (dv : dvalue) := concretize_u uv (ret dv).

      Definition concretize_fails (uv : uvalue) : Prop
        := concretize_u uv (raise_ub "").

      Definition concretize_succeeds (uv : uvalue) : Prop
        := ~ concretize_fails uv.                                                       

      Lemma concretize_equation : forall (uv: uvalue) (dv : dvalue),
          concretize uv dv = concretize_u uv (ret dv).
      Proof.
        reflexivity.
      Qed.

      Lemma Concretize_Undef : forall dt dv,
          dvalue_has_dtyp dv dt ->
          concretize (UVALUE_Undef dt) dv.
      Proof.
        intros dt dv H.
        rewrite concretize_equation.
        unfold concretize_u.
        red; cbn; auto.
      Qed.

      Lemma Concretize_IBinop : forall iop uv1 e1 uv2 e2,
          concretize_u uv1 e1 ->
          concretize_u uv2 e2 ->
          concretize_u (UVALUE_IBinop iop uv1 uv2)
                       (dv1 <- e1 ;;
                        dv2 <- e2 ;;
                        (eval_iop iop dv1 dv2)).
      Proof.
        intros iop uv1 e1 uv2 e2 C1 C2.
        unfold concretize_u in *.

        rewrite concretize_uvalueM_equation.
        red.

        unfold bind.
        cbn.
        unfold bind_RefineProp.

        eexists.
        exists (fun x => match unEitherT (unERR_OR_UB e2) with
           | inl (UB_message ub) => raise_ub ub (* inl v0 *)
           | inr (inl (ERR_message err)) => raise_error err (* inr (inl x0) *)
           | inr (inr x0) => eval_iop iop x x0
           end).
        split; eauto.
        split.

        { (* Monad.eq1 mb (x <- ma;; k' x) *)
          unfold bind.
          cbn.
          destruct e1 as [[[[ub_message] | [[err_message] | e1]]]]; cbn; try reflexivity.
          destruct e2 as [[[[ub_message] | [[err_message] | e2]]]]; cbn; try reflexivity.

          destruct (eval_iop iop e1 e2) as [[[[ub_message] | [[err_message] | res]]]]; reflexivity.
        }

        intros dv1 Re1.

        eexists.
        exists (fun x0 => eval_iop iop dv1 x0).
        split; eauto.
        split.

        { (* Monad.eq1 mb (x <- ma;; k' x) *)
          unfold bind.
          cbn.
          destruct e2 as [[[[ub_message] | [[err_message] | e2]]]]; cbn; try reflexivity.

          unfold Monad.eq1, EqM_err_or_ub.
          destruct (eval_iop iop dv1 e2) as [[[[ub_message] | [[err_message] | res]]]]; reflexivity.
        }

        intros dv2 Re2.
        destruct (eval_iop iop dv1 dv2) as [[[[ub_message] | [[err_message] | res]]]]; reflexivity.
      Qed.
      
    End Concretize.
End Make.
