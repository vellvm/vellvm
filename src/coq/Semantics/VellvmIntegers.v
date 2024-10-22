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
    mbitwidth : option positive;
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
    mmax_unsigned : option Z;

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
    mmax_unsigned := None;

    munsigned := fun x => x;
    msigned := fun x => x;

    mrepr := fun x => ret x;

    mdtyp_of_int := DTYPE_IPTR
  }.

Definition int1 := @int 1.
Definition int8 := @int 8.
Definition int16 := @int 16.
Definition int32 := @int 32.
Definition int64 := @int 64.

Class VInt I : Type :=
  {
    (* Comparisons *)
    equ : I -> I -> bool;
    cmp : comparison -> I -> I -> bool;
    cmpu : comparison -> I -> I -> bool;

    (* Constants *)
    bitwidth : positive;
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
    max_unsigned : Z;

    (* Conversion *)
    unsigned : I -> Z;
    signed : I -> Z;

    repr : Z -> I;
  }.

#[global] Instance VInt_Bounded (sz : positive) : VInt (@int sz) :=
  {
    (* Comparisons *)
    equ := @Integers.eq sz;
    cmp := @Integers.cmp sz;
    cmpu := @Integers.cmpu sz;

    bitwidth := sz;

    (* Constants *)
    zero := @Integers.zero sz;
    one := @Integers.one sz;

    (* Arithmetic *)
    add := @Integers.add sz;
    add_carry := @Integers.add_carry sz;
    add_overflow := @Integers.add_overflow sz;

    sub := @Integers.sub sz;
    sub_borrow := @Integers.sub_borrow sz;
    sub_overflow := @Integers.sub_overflow sz;

    mul := @Integers.mul sz;

    divu := @Integers.divu sz;
    divs := @Integers.divs sz;
    modu := @Integers.modu sz;
    mods := @Integers.mods sz;

    shl := @Integers.shl sz;
    shr := @Integers.shr sz;
    shru := @Integers.shru sz;

    negative := @Integers.negative sz;

    (* Logic *)
    and := @Integers.and sz;
    or := @Integers.or sz;
    xor := @Integers.xor sz;

    (* Bounds *)
    min_signed := @Integers.min_signed sz;
    max_signed := @Integers.max_signed sz;
    max_unsigned := @Integers.max_unsigned sz;

    (* Conversion *)
    unsigned := @Integers.unsigned sz;
    signed := @Integers.signed sz;

    repr := @Integers.repr sz;
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
    mmax_unsigned := ret (max_unsigned);

    (* Conversion *)
    munsigned := unsigned;
    msigned := signed;

    mrepr := fun x => NoOom (repr x);

    (* dtyp *)
    mdtyp_of_int := DTYPE_I bitwidth
  }.
