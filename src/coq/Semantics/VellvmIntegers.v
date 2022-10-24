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
