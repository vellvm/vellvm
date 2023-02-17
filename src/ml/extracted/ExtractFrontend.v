From Coq Require Import
     Morphisms String.

Require Import List.
Import ListNotations.
Require Import ZArith.
Import ZArith.BinInt.

From Vellvm Require
     Utils.ParserHelper
     QC.ShowAST
     QC.ReprAST.

Require ExtrOcamlBasic.
Require ExtrOcamlString.
Require ExtrOcamlIntConv.

Extraction Language OCaml.
Extraction Blacklist String List Char Core Z Format.


(* Cutting the dependency to R. *)
Extract Inlined Constant Flocq.Core.Defs.F2R => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.IEEE754.Binary.FF2R => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.IEEE754.Binary.B2R => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.IEEE754.BinarySingleNaN.round_mode => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.Calc.Bracket.inbetween_loc => "(fun _ -> assert false)".

Extract Inlined Constant Archi.ppc64 => "false".
Set Extraction AccessOpaque.
(* NOTE: assumes that this file is compiled from /src *)
Cd "ml/extracted".

Extraction Library ExtrOcamlIntConv.
Extraction Library ParserHelper.
Recursive Extraction Library ShowAST.
Recursive Extraction Library ReprAST. 
