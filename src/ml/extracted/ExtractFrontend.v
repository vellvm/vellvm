From Coq Require Import
     Morphisms String.

Require Import List.
Import ListNotations.
Require Import ZArith.
Import ZArith.BinInt.

From TwoPhase Require
     Utils.ParserHelper
     QC.ShowAST
     QC.ReprAST
     QC.GenAlive2
     Semantics.

From QuickChick Require Import RandomQC.

Require ExtrOcamlBasic.
Require ExtrOcamlString.
Require ExtrOcamlIntConv.

Extraction Language OCaml.
Extraction Blacklist String List Char Core Z Format.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrnat ssrbool div eqtype.

(* OCaml pervasive types ---------------------------------------------------- *)
(* Extract Inlined Constant LLVMAst.int => "int". *)
(* Extract Inlined Constant LLVMAst.float => "float". *)

(* Cutting the dependency to R. *)
Extract Inlined Constant Flocq.Core.Defs.F2R => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.IEEE754.Binary.FF2R => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.IEEE754.Binary.B2R => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.IEEE754.BinarySingleNaN.round_mode => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.Calc.Bracket.inbetween_loc => "(fun _ -> assert false)".
Extract Inlined Constant Reals.ClassicalDedekindReals.sig_forall_dec => "(fun _ -> assert false)".
Extract Inlined Constant Reals.ClassicalDedekindReals.sig_not_dec => "false".

Extract Inlined Constant Archi.ppc64 => "false".

(* (* Extract Inlined Constant nat => "nat". *) *)
(* Export TopLevelBigIntptr. *)

(* NOTE: assumes that this file is compiled from /src *)
Cd "ml/extracted".

Extract Constant RandomSeed   => "Random.State.t".
Extract Constant randomSplit  => "(fun x -> (x,x))".
Extract Constant newRandomSeed => "(Random.State.make_self_init ())".

Extract Constant randomRBool => "(fun _ r -> Random.State.bool r, r)".
Extract Constant randomRInt  =>
  "(fun (x,y) r -> let yint = coqZ2Int y in let xint = coqZ2Int x in if (yint < xint) then failwith ""choose called with unordered arguments"" else (int2CoqZ (xint + (Random.State.int r (yint - xint + 1))), r))".
Extract Constant randomRN =>
  "(fun (x,y) r -> let yint = coqN2Int y in let xint = coqN2Int x in if yint < xint then failwith ""choose called with unordered arguments"" else  (int2CoqN (xint + (Random.State.int r (yint - xint + 1))), r))".

Separate Extraction LLVMAst AstLib TopLevel InterpretationStack ExtrOcamlIntConv ParserHelper ShowAST ReprAST GenAlive2.
