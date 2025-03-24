From Vellvm Require Import QC.Generators.
Require Import Flocq.IEEE754.Binary Bool.Bool.
From QuickChick Require Import QuickChick.

Definition Float_maxnum {prec emax} (a b : binary_float prec emax) :=
  match Bcompare prec emax a b with
    | Some Lt => b
    | _ => a
  end.

Definition maxnum_correct {prec emax} (a b : binary_float prec emax) :=
  let m := Float_maxnum a b in
      match Bcompare prec emax m a, Bcompare prec emax m b with
        | Some Eq, Some Gt | Some Eq, Some Eq => true
        | Some Gt, Some Eq => true
        | _, _ => false
      end.

Definition pair_fin32_gen : G (binary32 * binary32) := 
  bindGen (fing32) (fun b1 =>
    bindGen (fing32) (fun b2 =>
      returnGen (b1, b2))).

QuickCheck (forAll pair_fin32_gen 
                   (fun '(b1, b2) => maxnum_correct b1 b2 &&
                                  maxnum_correct b1 b1 &&
                                  maxnum_correct b2 b2)).
