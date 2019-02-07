Require Vellvm.TopLevel.
Require Vellvm.Transform.


Require ExtrOcamlBasic.
Require ExtrOcamlString.
Require ExtrOcamlIntConv.

Extraction Language Ocaml.
Extraction Blacklist String List Char Core Z.


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

(* OCaml pervasive types ---------------------------------------------------- *)
(* Extract Inlined Constant LLVMAst.int => "int". *)
(* Extract Inlined Constant LLVMAst.float => "float". *)

(* Cutting the dependency to R. *)
Extract Inlined Constant Flocq.Core.Defs.F2R => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.IEEE754.Binary.FF2R => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.IEEE754.Binary.B2R => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.IEEE754.Binary.round_mode => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.Calc.Bracket.inbetween_loc => "(fun _ -> assert false)".

Set Extraction AccessOpaque.
(* NOTE: assumes that this file is compiled from /src *)
Cd "ml/extracted".

Extraction Library ExtrOcamlIntConv.
Recursive Extraction Library TopLevel.
Extraction Library Transform.
