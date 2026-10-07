(* begin hide *)
From ITree Require Import
  ITree.

From Vellvm Require Import
  Numeric
  Utils
  Syntax
  Params
  VellvmIntegers
  DynamicValues
  LLVMEvents.

Open Scope N_scope.
(* end hide *)

(** * Freeze

    Semantics of the [freeze] instruction: poison is replaced by an
    arbitrary-but-fixed value obtained from a [draw] event, and byte values
    are frozen bit by bit. *)

Section Freeze.
  Context {Pa : Params}.

  (** ** Freezing a byte value

      LangRef ('freeze'): "Values of the byte type are frozen on a per-bit
      basis."  Poison bit [i] becomes bit [i] of the arbitrary-but-fixed
      integer [z]; integer and pointer bits are left alone, provenance
      included. *)
  Fixpoint freeze_bits (z : Z) (i : N) (bits : list memory_bit) : list memory_bit :=
    match bits with
    | [] => []
    | Bit_psn :: rest =>
        Bit_bit (repr (if Z.testbit z (Z.of_N i) then 1 else 0)) :: freeze_bits z (1 + i) rest
    | b :: rest => b :: freeze_bits z (1 + i) rest
    end.

  (* The frozen bits, re-canonicalised: once the poison is gone the byte is
     a [BYTE_I] if every bit is an integer bit, and otherwise stays a
     [BYTE_Mixed].  It cannot have become a [BYTE_Pointer] chunk: it still
     has pointer bits, but at least one former poison bit is now an integer
     bit. *)
  Definition freeze_mixed_bits sz (z : Z) (bits : list memory_bit) : dvalue_bv sz :=
    let bits' := freeze_bits z 0 bits in
    if forallb is_int_bit bits' then BYTE_I (repr (int_bits_to_Z bits'))
    else BYTE_Mixed sz bits'.

  (** ** Freezing a [dvalue] *)

  Definition freeze_base {E} `{DrawE -< E} `{FailureE -< E} `{OOME -< E} `{UBE -< E} (dt:dtyp) (dv : dvalue_base) : itree E dvalue :=
    match dv with
    | DVALUE_Poison => draw dt
    (* bytes freeze per bit: draw the replacement bits as an integer of the
       byte's width (a non-integer answer leaves them all 0) *)
    | @DVALUE_B _ sz (BYTE_Mixed bits) =>
        if existsb is_poison_bit bits then
          x <- draw (DTYPE_I sz) ;;
          let z := match x with
                   | DVALUE_Base (DVALUE_I _ i) => unsigned i
                   | _ => 0%Z
                   end in
          ret (DVALUE_Base (DVALUE_B (freeze_mixed_bits sz z bits)))
        else DVALUE_Base <$> ret dv
    | _ => DVALUE_Base <$> ret dv
    end.


  Definition freeze {E} `{DrawE -< E} `{FailureE -< E} `{OOME -< E} `{UBE -< E} (dt:dtyp) (dv:dvalue) : itree E dvalue :=
    let f := fix freeze_h dv : dtyp -> itree E dvalue :=
        let freeze_fields : list dvalue -> list dtyp -> list dvalue -> itree E (list dvalue) :=
          fix loop (dvs:list dvalue) (dts:list dtyp)  (acc : list dvalue) : itree E (list dvalue) :=
            match dts, dvs with
            | [], [] => ret (rev_append acc [])
            | t::ts, v::vs =>
                v <- freeze_h v t ;;
                loop vs ts (v :: acc)
            | _, _ => raise "freeze_fields: mismatched field types and values"
            end
        in
      match dv with
      | DVALUE_Base v => fun dt => freeze_base dt v
      | DVALUE_Struct _ fields =>
          fun dt =>
          match dt with
          | DTYPE_Struct p dts =>
              val <- freeze_fields fields dts [] ;;
              ret (DVALUE_Struct p val)
          | _ => raise "freeze: type mismatch non-struct type"
          end
      | DVALUE_Array _ elts =>
          fun dt =>
            match dt with
            | DTYPE_Array v sz t =>
                let freeze_elts : list dvalue -> list dvalue -> itree E (list dvalue) :=
                  fix loop (dvs:list dvalue) (acc:list dvalue) : itree E (list dvalue) :=
                    match dvs with
                    | [] => ret (rev_append acc [])
                    | v::vs =>
                        v <- freeze_h v t ;;
                        loop vs (v::acc)
                    end
                in
                val <- freeze_elts elts [];;
                ret (DVALUE_Array v val)
            | _ => raise "freeze: type mismatch non-array type"
            end
      end
    in f dv dt.

End Freeze.
