From Coq Require Import
     ZArith.

From Vellvm Require Import
     Numeric.Integers
     Syntax.DynamicTypes
     Utils.MonadRefactored
     Utils.MonadRefactoredTheory
     Utils.OOM.

(* Integers that can run out of memory... Necessary for handling
     finite memory compilation. *)
Class VMemInt I : Type :=
  {
    (* Comparisons *)
    mequ : I -> I -> bool;
    mcmp : comparison -> I -> I -> bool;
    mcmpu : comparison -> I -> I -> bool;

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
