From Coq Require Import
     ZArith
     List.

From Vellvm Require Import
     Syntax.DataLayout
     Numeric.Integers.

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
