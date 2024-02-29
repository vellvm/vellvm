From Coq Require Import
  ZArith
  Zbool.

From ExtLib Require Import Monad.

From Vellvm Require Import Numeric.Integers Syntax.DynamicTypes Utils.Error.

(* Integers that can run out of memory... Necessary for handling
     finite memory compilation. *)
Class VMemInt I : Type :=
  {
    (* Comparisons *)
    mequ : I -> I -> bool;
    mcmp : Numeric.Integers.comparison -> I -> I -> bool;
    mcmpu : Numeric.Integers.comparison -> I -> I -> bool;

    (* Constants *)
    mbitwidth : option nat;
    mzero : I;
    mone : I;

    (* Arithmetic *)
    madd : I -> I -> OOM I;
    madd_carry : I -> I -> I -> I;
    madd_overflow : I -> I -> I -> I;

    msub : I -> I -> OOM I;
    msub_borrow : I -> I -> I -> I;
    msub_overflow : I -> I -> I -> I;

    mmul : I -> I -> OOM I;

    mdivu : I -> I -> I; (* Can this overflow? *)
    mdivs : I -> I -> OOM I;

    mmodu : I -> I -> I; (* Can this overflow / underflow *)
    mmods : I -> I -> OOM I; (* I suspect this can sort of overflow in the division by -1 case... Even though it really can't *)

    mshl : I -> I -> OOM I;
    mshr : I -> I -> I;  (* Can this overflow? *)
    mshru : I -> I -> I; (* Can this overflow? *)

    mnegative : I -> OOM I;

    (* Logic *)
    mand : I -> I -> I;
    mor : I -> I -> I;
    mxor : I -> I -> I;

    (* Bounds, possibly unbounded *)
    mmin_signed : option Z;
    mmax_signed : option Z;

    (* Conversion *)
    munsigned : I -> Z;
    msigned : I -> Z;

    mrepr : Z -> OOM I; (* Not sure if we should even have this *)

    (* dtyp *)
    mdtyp_of_int : dtyp
  }.

Definition mequ_Z (x y : Z) : bool :=
  Z.eqb x y.

Definition mcmp_Z (c : Numeric.Integers.comparison) (x y : Z) : bool :=
  match c with
  | Ceq => Z.eqb x y
  | Cne => Zneq_bool x y
  | Clt => Z.ltb x y
  | Cle => Z.leb x y
  | Cgt => Z.gtb x y
  | Cge => Z.geb x y
  end.

Definition mcmpu_Z (c : Numeric.Integers.comparison) (x y : Z) : bool :=
  match c with
  | Ceq => Z.eqb x y
  | Cne => Zneq_bool x y
  | Clt => Z.ltb x y
  | Cle => Z.leb x y
  | Cgt => Z.gtb x y
  | Cge => Z.geb x y
  end.

#[global] Instance VMemInt_Z : VMemInt Z :=
  { mequ  := Z.eqb;
    mcmp  := mcmp_Z;
    mcmpu := mcmpu_Z;

    mbitwidth := None;
    mzero     := 0%Z;
    mone      := 1%Z;

    madd := fun x y => ret (Z.add x y);
    (* No overflows *)
    madd_carry := fun x y c => 0%Z;
    madd_overflow := fun x y c => 0%Z;

    msub := fun x y => ret (Z.sub x y);
    (* No overflows *)
    msub_borrow := fun x y c => 0%Z;
    msub_overflow := fun x y c => 0%Z;

    mmul := fun x y => ret (Z.mul x y);

    mdivu := fun x y => Z.div x y;
    mdivs := fun x y => ret (Z.div x y);

    mmodu := fun x y => Z.modulo x y;
    mmods := fun x y => ret (Z.modulo x y);

    mshl := fun x y => ret (Z.shiftl x y);
    mshr := fun x y => Z.shiftr x y;
    mshru := fun x y => Z.shiftr x y;

    mnegative := fun x => ret (0 - x)%Z;

    mand := Z.land;
    mor := Z.lor;
    mxor := Z.lxor;

    mmin_signed := None;
    mmax_signed := None;

    munsigned := fun x => x;
    msigned := fun x => x;

    mrepr := fun x => ret x;

    mdtyp_of_int := DTYPE_IPTR
  }.

(* Set up representations for for i1, i32, and i64 *)
Module Wordsize1.
  Definition wordsize := 1%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof using. unfold wordsize; congruence. Qed.
End Wordsize1.

Module Wordsize8.
  Definition wordsize := 8%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof using. unfold wordsize; congruence. Qed.
End Wordsize8.

Module Int1 := Make(Wordsize1).
Module Int8 := Make(Wordsize8).
Module Int16 := Integers.Int16.
Module Int32 := Integers.Int.
Module Int64 := Integers.Int64.

Definition int1 := Int1.int.
Definition int8 := Int8.int.
Definition int16 := Int16.int.
Definition int32 := Int32.int.
Definition int64 := Int64.int.

Class VInt I : Type :=
  {
    (* Comparisons *)
    equ : I -> I -> bool;
    cmp : comparison -> I -> I -> bool;
    cmpu : comparison -> I -> I -> bool;

    (* Constants *)
    bitwidth : nat;
    zero : I;
    one : I;

    (* Arithmetic *)
    add : I -> I -> I;
    add_carry : I -> I -> I -> I;
    add_overflow : I -> I -> I -> I;

    sub : I -> I -> I;
    sub_borrow : I -> I -> I -> I;
    sub_overflow : I -> I -> I -> I;

    mul : I -> I -> I;

    divu : I -> I -> I;
    divs : I -> I -> I;
    modu : I -> I -> I;
    mods : I -> I -> I;

    shl : I -> I -> I;
    shr : I -> I -> I;
    shru : I -> I -> I;

    negative : I -> I;

    (* Logic *)
    and : I -> I -> I;
    or : I -> I -> I;
    xor : I -> I -> I;

    (* Bounds *)
    min_signed : Z;
    max_signed : Z;

    (* Conversion *)
    unsigned : I -> Z;
    signed : I -> Z;

    repr : Z -> I;
  }.

#[global] Instance VInt32 : VInt Int32.int :=
  {
    (* Comparisons *)
    equ := Int32.eq;
    cmp := Int32.cmp;
    cmpu := Int32.cmpu;

    bitwidth := 32;

    (* Constants *)
    zero := Int32.zero;
    one := Int32.one;

    (* Arithmetic *)
    add := Int32.add;
    add_carry := Int32.add_carry;
    add_overflow := Int32.add_overflow;

    sub := Int32.sub;
    sub_borrow := Int32.sub_borrow;
    sub_overflow := Int32.sub_overflow;

    mul := Int32.mul;

    divu := Int32.divu;
    divs := Int32.divs;
    modu := Int32.modu;
    mods := Int32.mods;

    shl := Int32.shl;
    shr := Int32.shr;
    shru := Int32.shru;

    negative := Int32.negative;

    (* Logic *)
    and := Int32.and;
    or := Int32.or;
    xor := Int32.xor;

    (* Bounds *)
    min_signed := Int32.min_signed;
    max_signed := Int32.max_signed;

    (* Conversion *)
    unsigned := Int32.unsigned;
    signed := Int32.signed;

    repr := Int32.repr;
  }.

#[global] Instance VInt1 : VInt Int1.int :=
  {
    (* Comparisons *)
    equ := Int1.eq;
    cmp := Int1.cmp;
    cmpu := Int1.cmpu;

    bitwidth := 1;

    (* Constants *)
    zero := Int1.zero;
    one := Int1.one;

    (* Arithmetic *)
    add := Int1.add;
    add_carry := Int1.add_carry;
    add_overflow := Int1.add_overflow;

    sub := Int1.sub;
    sub_borrow := Int1.sub_borrow;
    sub_overflow := Int1.sub_overflow;

    mul := Int1.mul;

    divu := Int1.divu;
    divs := Int1.divs;
    modu := Int1.modu;
    mods := Int1.mods;

    shl := Int1.shl;
    shr := Int1.shr;
    shru := Int1.shru;

    negative := Int1.negative;

    (* Logic *)
    and := Int1.and;
    or := Int1.or;
    xor := Int1.xor;

    (* Bounds *)
    min_signed := Int1.min_signed;
    max_signed := Int1.max_signed;

    (* Conversion *)
    unsigned := Int1.unsigned;
    signed := Int1.signed;

    repr := Int1.repr;
  }.

#[global] Instance VInt8 : VInt Int8.int :=
  {
    (* Comparisons *)
    equ := Int8.eq;
    cmp := Int8.cmp;
    cmpu := Int8.cmpu;

    bitwidth := 8;

    (* Constants *)
    zero := Int8.zero;
    one := Int8.one;

    (* Arithmetic *)
    add := Int8.add;
    add_carry := Int8.add_carry;
    add_overflow := Int8.add_overflow;

    sub := Int8.sub;
    sub_borrow := Int8.sub_borrow;
    sub_overflow := Int8.sub_overflow;

    mul := Int8.mul;

    divu := Int8.divu;
    divs := Int8.divs;
    modu := Int8.modu;
    mods := Int8.mods;

    shl := Int8.shl;
    shr := Int8.shr;
    shru := Int8.shru;

    negative := Int8.negative;

    (* Logic *)
    and := Int8.and;
    or := Int8.or;
    xor := Int8.xor;

    (* Bounds *)
    min_signed := Int8.min_signed;
    max_signed := Int8.max_signed;

    (* Conversion *)
    unsigned := Int8.unsigned;
    signed := Int8.signed;

    repr := Int8.repr;
  }.

#[global] Instance VInt16 : VInt Int16.int :=
  {
    (* Comparisons *)
    equ := Int16.eq;
    cmp := Int16.cmp;
    cmpu := Int16.cmpu;

    bitwidth := 16;

    (* Constants *)
    zero := Int16.zero;
    one := Int16.one;

    (* Arithmetic *)
    add := Int16.add;
    add_carry := Int16.add_carry;
    add_overflow := Int16.add_overflow;

    sub := Int16.sub;
    sub_borrow := Int16.sub_borrow;
    sub_overflow := Int16.sub_overflow;

    mul := Int16.mul;

    divu := Int16.divu;
    divs := Int16.divs;
    modu := Int16.modu;
    mods := Int16.mods;

    shl := Int16.shl;
    shr := Int16.shr;
    shru := Int16.shru;

    negative := Int16.negative;

    (* Logic *)
    and := Int16.and;
    or := Int16.or;
    xor := Int16.xor;

    (* Bounds *)
    min_signed := Int16.min_signed;
    max_signed := Int16.max_signed;

    (* Conversion *)
    unsigned := Int16.unsigned;
    signed := Int16.signed;

    repr := Int16.repr;
  }.

#[global] Instance VIntVMemInt {I} `{VInt I} : VMemInt I :=
  {
    (* Comparisons *)
    mequ := equ;
    mcmp := cmp;
    mcmpu := cmpu;

    (* Constants *)
    mbitwidth := ret bitwidth;
    mzero := zero;
    mone := one;

    (* Arithmetic *)
    madd := fun x y => ret (add x y);
    madd_carry := add_carry;
    madd_overflow := add_overflow;

    msub := fun x y => ret (sub x y);
    msub_borrow := sub_borrow;
    msub_overflow := sub_overflow;

    mmul := fun x y => ret (mul x y);

    mdivu := divu;
    mdivs := fun x y => ret (divs x y);

    mmodu := modu;
    mmods := fun x y => ret (mods x y);

    mshl := fun x y => ret (shl x y);
    mshr := shr;
    mshru := shru;

    mnegative := fun x => ret (negative x);

    (* Logic *)
    mand := and;
    mor := or;
    mxor := xor;

    (* Bounds, possibly unbounded *)
    mmin_signed := ret (min_signed);
    mmax_signed := ret (max_signed);

    (* Conversion *)
    munsigned := unsigned;
    msigned := signed;

    mrepr := fun x => NoOom (repr x);

    (* dtyp *)
    mdtyp_of_int := DTYPE_I (N.of_nat bitwidth)
  }.

#[global] Instance VInt64 : VInt Int64.int :=
  {
    (* Comparisons *)
    equ := Int64.eq;
    cmp := Int64.cmp;
    cmpu := Int64.cmpu;

    bitwidth := 64;

    (* Constants *)
    zero := Int64.zero;
    one := Int64.one;

    (* Arithmetic *)
    add := Int64.add;
    add_carry := Int64.add_carry;
    add_overflow := Int64.add_overflow;

    sub := Int64.sub;
    sub_borrow := Int64.sub_borrow;
    sub_overflow := Int64.sub_overflow;

    mul := Int64.mul;

    divu := Int64.divu;
    divs := Int64.divs;
    modu := Int64.modu;
    mods := Int64.mods;

    shl := Int64.shl;
    shr := Int64.shr;
    shru := Int64.shru;

    negative := Int64.negative;

    (* Logic *)
    and := Int64.and;
    or := Int64.or;
    xor := Int64.xor;

    (* Bounds *)
    min_signed := Int64.min_signed;
    max_signed := Int64.max_signed;

    (* Conversion *)
    unsigned := Int64.unsigned;
    signed := Int64.signed;

    repr := Int64.repr;
  }.
