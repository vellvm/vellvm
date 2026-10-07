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
    are frozen bit by bit, each poison bit by a [DrawBool] event. *)

Section Freeze.
  Context {Pa : Params}.

  (** ** Freezing a byte value

      LangRef ('freeze'): "Values of the byte type are frozen on a per-bit
      basis."  A poison bit becomes an arbitrary-but-fixed integer bit,
      chosen by a [DrawBool] event; integer and pointer bits are left
      alone, provenance included. *)
  Definition freeze_bit {E} `{DrawE -< E} `{FailureE -< E} `{OOME -< E} `{UBE -< E} (b:memory_bit) : itree E memory_bit :=
    match b with
    | Bit_psn =>
        x <- trigger DrawBool ;;
        ret (Bit_bit (repr (if (x:bool) then 1 else 0)))
    | b => ret b
    end.

  (* The frozen bits, re-canonicalised: once the poison is gone the byte is
     a [BYTE_I] if every bit is an integer bit, and otherwise stays a
     [BYTE_Mixed].  It cannot have become a [BYTE_Pointer] chunk: it still
     has pointer bits, but at least one former poison bit is now an integer
     bit. *)
  Definition freeze_mixed_bits {E} `{DrawE -< E} `{FailureE -< E} `{OOME -< E} `{UBE -< E} sz (bits : list memory_bit) : itree E (dvalue_bv sz) :=
    bits' <- map_monad freeze_bit bits ;;
    if forallb is_int_bit bits' then ret (BYTE_I (repr (int_bits_to_Z bits')))
    else ret (BYTE_Mixed sz bits').

  (** ** Freezing a [dvalue] *)

  Definition freeze_base {E} `{DrawE -< E} `{FailureE -< E} `{OOME -< E} `{UBE -< E} (dt:dtyp) (dv : dvalue_base) : itree E dvalue :=
    match dv with
    | DVALUE_Poison => draw dt
    (* bytes freeze per bit *)
    | @DVALUE_B _ sz (BYTE_Mixed bits) =>
        if existsb is_poison_bit bits then
          dv <- freeze_mixed_bits sz bits ;;
          ret (DVALUE_Base (DVALUE_B dv))
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
