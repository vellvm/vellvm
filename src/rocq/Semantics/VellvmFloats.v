From Stdlib Require Import
  Number
  PArith.BinPosDef.

From Vellvm Require Import
  Utilities
  Syntax
  Numeric.

Class VFloat FP : Type :=
  {
    (* representation *)
    denote_fp_syntax : float_syntax -> option FP
  }.

(*  Strategy for denoting floating point syntax:

    For Positive Decimal.Decimal:

      [+]xxx.yyyy

        if xxx is all 0's then
          if yyy are all 0's then use [zero]
          else
            base = 10
            mantissa = xxx * 10 ^ |yyyy| + yyyy
            exp = -|yyyy|
            Float32.from_parsed (10) mantissa exp 
        else
          Float32.from_parsed 10 x 0


    For Negative Decimal.Decimal:
      [-]xxx.yyyy
        first convert xxx.yyy positively then set the sign bit to negative



 LLVM rejects literals that don't have exact representations in IEEE754.
   

(** Given a base [base], a mantissa [m] and an exponent [e], the following function
  computes the FP number closest to [m * base ^ e], using round to odd, ties break to even.
  The algorithm is naive, computing [base ^ |e|] exactly before doing a multiplication or
  division with [m].  However, we treat specially very large or very small values of [e],
  when the result is known to be [+infinity] or [0.0] respectively. *)

  Float32.from_parsed:
    base  integral part  exppart 
      10

   Bparse 24 128 __ __ base intPart expPart.
 *) 

(* Converts a syntactic floating point value to a float32
   SAZ: not sure whether the "parsed" conversion is correct
    it maybe should fail if the number isn't exactly representable.
 *)
(* semantic comparison of uint and zero - inlined below to give better proofs. *)
Definition uint_is_zero (us:Decimal.uint) : bool :=
  match Pos.of_uint us with
  | N0 => true
  | Npos _ => false
  end.

Definition xx := Decimal.D1 (Decimal.D2 (Decimal.D3 Decimal.Nil)).


(*
   The following function creates a float32 from a parsed representation of a
   floating point value, which is a *positive* number of the form:
      "xs.ys e exp"
   where [xs] is the integral part [ys] is the fractional part and [exp] is the exponent.

   xs = integral part
   ys = fractional part
   
   All arithmetic is assumed to be base 10.

   The resulting float is the nearest representable value
          integral.fractional 10 ^ exp

    123.345
    12312.32423
    1.0
    0.000001

    00.000 e exp => 0

    Negative floating point values are handled later by flipping the sign bit.
 *)
Definition positive_decimal_decimal_signed_to_float32 (xs ys : Decimal.uint) (exp:Decimal.signed_int) : float32 :=
  match Pos.of_uint xs with
  | N0 =>
      (* xs is 0 *)
      match Pos.of_uint ys with
      | N0 => (* ys is 0 *)
          (* 000.000 *)
          Float32.zero
      | Npos yyy =>
          (* 000.123e^exp = yyy * 10^(exp -|yyy|) *)
          Float32.from_parsed 10 yyy (BinInt.Z.sub (BinInt.Z.of_int exp) (IntDef.Z.of_nat (Decimal.nb_digits ys)))
      end          
  | Npos xxx =>
      match Pos.of_uint ys with
      | N0 =>
          (* 12.000 * 10^exp *)
          Float32.from_parsed 10 xxx (BinInt.Z.of_int exp)
      | Npos yyy =>
          (* 12.345 = 12345 * 10^(exp -|yyy|) *)
          match BinNat.N.of_nat (Decimal.nb_digits ys) with
          | N0 => Float32.zero (* Should not happen since Pos.of_uint <> N0 *)
          | Npos ypos =>
              let xxx_shifted := Pos.mul xxx (pos_pow 10 ypos) in
              let total := Pos.add xxx_shifted yyy in 
              Float32.from_parsed 10 total (BinInt.Z.sub (BinInt.Z.of_int exp) (IntDef.Z.of_nat (Decimal.nb_digits ys)))
          end
      end
  end.

(* Same as above, but with the exponent set to 0, so that we get 123.4565 *)
Definition positive_decimal_decimal_to_float32 (xs ys : Decimal.uint) : float32 :=
  positive_decimal_decimal_signed_to_float32 xs ys (Nat.to_int 0).

(* SAZ: I'm worried that this is going to be too inefficient for the interpreter. *)

(*
Eval vm_compute in (positive_decimal_decimal_to_float32 (Decimal.D0 Decimal.Nil) xx).
Eval vm_compute in (positive_decimal_decimal_to_float32 xx (Decimal.D0 Decimal.Nil)).
Eval vm_compute in (positive_decimal_decimal_to_float32 (Decimal.D0 Decimal.Nil) (Decimal.D0 Decimal.Nil)).
*)

(* Same as above, but producing a [float] (aka [double], 64-bit float, instead of a [float32]. *)
Definition positive_decimal_decimal_signed_to_float (xs ys : Decimal.uint) (exp:Decimal.signed_int) : float :=
  match Pos.of_uint xs with
  | N0 =>
      (* xs is 0 *)
      match Pos.of_uint ys with
      | N0 => (* ys is 0 *)
          (* 000.000 *)
          Float.zero
      | Npos yyy =>
          (* 000.123e^exp = yyy * 10^(exp -|yyy|) *)
          Float.from_parsed 10 yyy (BinInt.Z.sub (BinInt.Z.of_int exp) (IntDef.Z.of_nat (Decimal.nb_digits ys)))
      end          
  | Npos xxx =>
      match Pos.of_uint ys with
      | N0 =>
          (* 12.000 * 10^exp *)
          Float.from_parsed 10 xxx (BinInt.Z.of_int exp)
      | Npos yyy =>
          (* 12.345 = 12345 * 10^(exp -|yyy|) *)
          match BinNat.N.of_nat (Decimal.nb_digits ys) with
          | N0 => Float.zero (* Should not happen since Pos.of_uint <> N0 *)
          | Npos ypos =>
              let xxx_shifted := Pos.mul xxx (pos_pow 10 ypos) in
              let total := Pos.add xxx_shifted yyy in 
              Float.from_parsed 10 total (BinInt.Z.sub (BinInt.Z.of_int exp) (IntDef.Z.of_nat (Decimal.nb_digits ys)))
          end
      end
  end.

(* Same as above, but with the exponent set to 0, so that we get 123.4565 *)
Definition positive_decimal_decimal_to_float (xs ys : Decimal.uint) : float :=
  positive_decimal_decimal_signed_to_float xs ys (Nat.to_int 0).



(* Converting hexadecimal to float is much easier. *)
Definition hexadecimal_uint_to_float32 (h:Hexadecimal.uint) : float32 :=
  Bits.b32_of_bits (BinInt.Z.of_hex_uint h).


Definition float32_of_float_syntax (fs:float_syntax) : option float32 :=
  match fs with
  | FS_decimal (Decimal.Decimal (Decimal.Pos xs) ys) => 
      Some (positive_decimal_decimal_to_float32 xs ys)
                                                        
  | FS_decimal (Decimal.Decimal (Decimal.Neg xs) ys) =>
      Some (Float32.neg (positive_decimal_decimal_to_float32 xs ys))
 
  | FS_decimal (Decimal.DecimalExp (Decimal.Pos i) ui exp) =>
      Some (positive_decimal_decimal_signed_to_float32 i ui exp)

  | FS_decimal (Decimal.DecimalExp (Decimal.Neg i) ui exp) =>
      Some (Float32.neg (positive_decimal_decimal_signed_to_float32 i ui exp))
           
  | FS_hex FH_X u => Some (hexadecimal_uint_to_float32 u)

  | FS_hex _ _ => None
  end.



Program Definition hexadecimal_uint_to_bit_int {b} (h:Hexadecimal.uint) : option (@Integers.bit_int b) :=
  let z := BinInt.Z.of_hex_uint h in
  if ZArith_dec.Z_lt_dec (BinInt.Z.of_hex_uint h)  (@Integers.modulus b) then
    Some (@Integers.mkint b z _)
  else
    None.
Next Obligation.
  split; auto.
  unfold BinInt.Z.of_hex_uint, BinInt.Z.of_N. 
  destruct (BinPos.Pos.of_hex_uint h); reflexivity.
Defined.
  
Definition hexadecimal_uint_to_float (h:Hexadecimal.uint) : option float :=
  match hexadecimal_uint_to_bit_int h with 
  | Some x => Some (Float.of_bits x)
  | None => None
  end.

Definition h := Hexadecimal.D3 (Hexadecimal.D1 (Hexadecimal.Nil)).

(* Eval vm_compute in hexadecimal_uint_to_float h. *)

Definition float_of_float_syntax (fs:float_syntax) : option float :=
  match fs with
  | FS_decimal (Decimal.Decimal (Decimal.Pos xs) ys) => 
      Some (positive_decimal_decimal_to_float xs ys)
                                                        
  | FS_decimal (Decimal.Decimal (Decimal.Neg xs) ys) =>
      Some (Float.neg (positive_decimal_decimal_to_float xs ys))
 
  | FS_decimal (Decimal.DecimalExp (Decimal.Pos i) ui exp) =>
      Some (positive_decimal_decimal_signed_to_float i ui exp)

  | FS_decimal (Decimal.DecimalExp (Decimal.Neg i) ui exp) =>
      Some (Float.neg (positive_decimal_decimal_signed_to_float i ui exp))
           
  | FS_hex FH_X u => hexadecimal_uint_to_float u

  | FS_hex _ _ => None
  end.

