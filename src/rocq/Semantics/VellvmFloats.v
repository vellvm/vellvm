From Stdlib Require Import
  Number
  PArith.BinPosDef.

From Vellvm Require Import
  Utils
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

(* Converts a syntactic floating point value to a float32. *)
(* semantic comparison of uint and zero - inlined below to give better proofs. *)
Definition uint_is_zero (us:Decimal.uint) : bool :=
  match Pos.of_uint us with
  | N0 => true
  | Npos _ => false
  end.

Definition xx := Decimal.D1 (Decimal.D2 (Decimal.D3 Decimal.Nil)).

(*
   The following function creates a [float] (a 64-bit double) from a parsed
   representation of a floating point value, which is a *positive* number of the
   form:
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
(* SAZ: I'm worried that this is going to be too inefficient for the interpreter. *)
(* There is deliberately no float32 counterpart: a decimal literal at type
   [float] is parsed as a double by this function and then narrowed by
   [float_to_float32], which is what LLVM does.  The former
   [positive_decimal_decimal_{signed_,}to_float32] pair, which rounded the
   decimal straight to binary32, was removed when that gate went in. *)
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
Definition hexadecimal_uint_to_float32 (h:Hexadecimal.uint) : option float32 :=
  float_to_float32 (Bits.b64_of_bits (BinInt.Z.of_hex_uint h)). 


(** A *decimal* literal at type [float] is read the way LLVM's parser reads it:
    parsed as a [double] first, then narrowed, and REJECTED if that narrowing
    would lose anything.  So [float 1.5] and [float 1.0e10] are fine, whereas
    [float 1.3], [float 3.0e38] and [float 16777217.0] are errors -- "floating
    point constant invalid for type", as llvm-as puts it.  ([float 1.0e400] is
    accepted: it overflows to an infinity as a double, and infinity narrows
    exactly.)

    NB this rule is NOT stated in LangRef, unlike the exactness requirement on
    the hex form.  LangRef's "Simple Constants" claims flatly that "the
    assembler ... accepts 1.25 but rejects 1.3", without distinguishing float
    from double -- but LLVM accepts [double 1.3], so the documented rule is not
    the implemented one.  What is encoded here is clang's observed behaviour
    (LLParser parses to an APFloat and errors if [convert] reports losesInfo),
    which is the reference [make test] is differential against.

    Going through the double matters twice over.  It is what makes the gate
    agree with LLVM's, and it also settles the rounding: computing the float32
    straight from the decimal would round once, whereas LLVM rounds decimal ->
    binary64 -> binary32, and double rounding is not in general single rounding.
    On the literals we now accept the question is moot -- they are exact -- but
    only because we reject the ones where it could have shown up. *)

Definition float32_of_float_syntax (fs:float_syntax) : option float32 :=
  match fs with
  | FS_decimal (Decimal.Decimal (Decimal.Pos xs) ys) =>
      float_to_float32 (positive_decimal_decimal_to_float xs ys)

  | FS_decimal (Decimal.Decimal (Decimal.Neg xs) ys) =>
      float_to_float32 (Float.neg (positive_decimal_decimal_to_float xs ys))

  | FS_decimal (Decimal.DecimalExp (Decimal.Pos i) ui exp) =>
      float_to_float32 (positive_decimal_decimal_signed_to_float i ui exp)

  | FS_decimal (Decimal.DecimalExp (Decimal.Neg i) ui exp) =>
      float_to_float32 (Float.neg (positive_decimal_decimal_signed_to_float i ui exp))

  (* NB: not routed through [float_of_float_syntax]'s hex arm, which rejects a
     literal of more than 16 digits ([hexadecimal_uint_to_bit_int]'s range
     check).  LLVM instead truncates it mod 2^64 -- clang folds
     [float 0x1FFF8000000000000] to [0xFFF8000000000000] -- which is what
     [b64_of_bits] does here. *)
  | FS_hex FH_X u => hexadecimal_uint_to_float32 u

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

