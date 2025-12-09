
From Stdlib Require Import
     Morphisms String.

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import ZArith.
Import ZArith.BinInt.

From ITree Require Import
     ITree
     Basics.Monad
     Eq.Eqit.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics
     Handlers.Handlers
     Theory.Refinement.

Import ITreeNotations.

Import ListNotations.

From Vellvm Require
     Semantics.TopLevel
     Transformations.Transform
     Utils.ParserHelper
     QC.ShowAST
     QC.ReprAST
     (* QC.QCVellvm *).

Set Extraction AccessOpaque.

From QuickChick Require Import RandomQC.
                           
From Vellvm Require QC.GenAlive2.

Require ExtrOcamlBasic.
Require ExtrOcamlString.
Require ExtrOcamlIntConv.

Extraction Language OCaml.
Extraction Blacklist String List Char Core Z Format.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrnat ssrbool div eqtype.

(* strings ------------------------------------------------------------------ *)
(*
Extract Inductive ascii => char
[
"(* If this appears, you're using Ascii internals. Please don't *) (fun (b0,b1,b2,b3,b4,b5,b6,b7) -> let f b i = if b then 1 lsl i else 0 in Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))"
]
"(* If this appears, you're using Ascii internals. Please don't *) (fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))".
Extract Constant zero => "'\000'".
Extract Constant one => "'\001'".
Extract Constant shift =>
 "fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)".
Extract Inlined Constant ascii_dec => "(=)".
Extract Inductive string => "string" [ "str_nil" "str_cons" ].
*)


(* camlstring_of_coqstring is from Camlcoq *)
Extract Constant printer_object => "
  let loc_state = ref [] in
  let camlstring_of_coqstring (s: char list) =
    let r = Bytes.create (List.length s) in
    let rec fill pos = function
      | [] -> r
      | c :: s -> Bytes.set r pos c; fill (pos + 1) s
    in Bytes.to_string (fill 0 s)
  in
  let set_loc loc = (loc_state := loc; []) in
  let print_msg msg =
    print_string ((camlstring_of_coqstring !loc_state) ^ "": "" ^ (camlstring_of_coqstring msg) ^ ""\n"")
  in
  (set_loc, print_msg)
  ".

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

(* (* NOTE: assumes that this file is compiled from /src *) *)
Cd "ml/extracted".

Extract Constant RandomSeed   => "Random.State.t".
Extract Constant randomSplit  => "(fun x -> (x,x))".
Extract Constant newRandomSeed => "(Random.State.make_self_init ())".

Extract Constant randomRBool => "(fun _ r -> Random.State.bool r, r)".
Extract Constant randomRInt  =>
  "(fun (x,y) r -> let yint = coqZ2Int y in let xint = coqZ2Int x in if (yint < xint) then failwith ""choose called with unordered arguments"" else (int2CoqZ (xint + (Random.State.int r (yint - xint + 1))), r))".
Extract Constant randomRN =>
  "(fun (x,y) r -> let yint = coqN2Int y in let xint = coqN2Int x in if yint < xint then failwith ""choose called with unordered arguments"" else  (int2CoqN (xint + (Random.State.int r (yint - xint + 1))), r))".
Extract Constant randomRNat =>
  "(fun (x,y) r -> let yint = ExtrOcamlIntConv.int_of_nat y in let xint = ExtrOcamlIntConv.int_of_nat x in if yint < xint then failwith ""choose called with unordered arguments"" else  (ExtrOcamlIntConv.nat_of_int (xint + (Random.State.int r (yint - xint + 1))), r))".

Separate Extraction TopLevelBigIntptr ExtrOcamlIntConv TopLevel AstLib Transform ParserHelper ShowAST ReprAST Handlers GenAlive2 Numeric.Floats BinNums BinPos (* QCVellvm *).
