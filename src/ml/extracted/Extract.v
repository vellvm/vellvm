
From Coq Require Import
     Morphisms String.

Require Import List.
Import ListNotations.
Require Import ZArith.
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
.

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
Extract Constant print_msg => "let camlstring_of_coqstring (s: char list) =
  let r = Bytes.create (List.length s) in
  let rec fill pos = function
  | [] -> r
  | c :: s -> Bytes.set r pos c; fill (pos + 1) s
  in Bytes.to_string (fill 0 s)
in fun msg -> print_string (camlstring_of_coqstring msg ^ ""\n"")".

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
(* Extract Inlined Constant nat => "nat". *)
Export TopLevelBigIntptr.

(* NOTE: assumes that this file is compiled from /src *)
Cd "ml/extracted".

Extraction Library ExtrOcamlIntConv.
Recursive Extraction Library TopLevel.
Extraction Library Transform.
Extraction Library ParserHelper.
Recursive Extraction Library ShowAST.
Recursive Extraction Library ReprAST.
Extraction Library Handlers.

(* From QuickChick Require Import ExtractionQC. *)

(* Modifying the extraction code from QuickChick Library *)
Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
From QuickChick Require Import RandomQC RoseTrees Test Show Checker.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.
(* Require Import ExtrOcamlZInt. *)

Extraction Blacklist String List Nat.

(** Temporary fix for https://github.com/coq/coq/issues/7017. *)
(** Scott encoding of [Decimal.int] as [forall r. (uint -> r) -> (uint -> r) -> r]. *)
Extract Inductive Decimal.int => "((Obj.t -> Obj.t) -> (Obj.t -> Obj.t) -> Obj.t) (* Decimal.int *)"
  [ "(fun x pos _ -> pos (Obj.magic x))"
    "(fun y _ neg -> neg (Obj.magic y))"
  ] "(fun i pos neg -> Obj.magic i pos neg)".
Extract Inductive Hexadecimal.int => "((Obj.t -> Obj.t) -> (Obj.t -> Obj.t) -> Obj.t) (* Hexadecimal.int *)"
  [ "(fun x pos _ -> pos (Obj.magic x))"
    "(fun y _ neg -> neg (Obj.magic y))"
  ] "(fun i pos neg -> Obj.magic i pos neg)".
(* Extract Inductive Numeral.int => "((Obj.t -> Obj.t) -> (Obj.t -> Obj.t) -> Obj.t) (* Numeral.int *)" *)
(*   [ "(fun x dec _ -> dec (Obj.magic x))" *)
(*     "(fun y _ hex -> hex (Obj.magic y))" *)
(*   ] "(fun i dec hex -> Obj.magic i dec hex)". *)

Extract Constant show_nat =>
  "(fun i ->
  let s = string_of_int i in
  let rec copy acc i =
    if i < 0 then acc else copy (s.[i] :: acc) (i-1)
  in copy [] (String.length s - 1))".
Extract Constant show_bool =>
  "(fun i ->
  let s = string_of_bool i in
  let rec copy acc i =
    if i < 0 then acc else copy (s.[i] :: acc) (i-1)
  in copy [] (String.length s - 1))".

(* Extract Constant show_Z => *)
(*   "(fun i -> *)
(*   let s = string_of_int i in *)
(*   let rec copy acc i = *)
(*     if i < 0 then acc else copy (s.[i] :: acc) (i-1) *)
(*   in copy [] (String.length s - 1))". *)
(* Extract Constant show_N => *)
(*   "(fun i -> *)
(*   let s = string_of_int i in *)
(*   let rec copy acc i = *)
(*     if i < 0 then acc else copy (s.[i] :: acc) (i-1) *)
(*   in copy [] (String.length s - 1))". *)

Extract Constant RandomSeed   => "Random.State.t".
Extract Constant randomNext   => "(fun r -> Random.State.bits r, r)".
(* Extract Constant rndGenRange => "SR.genRange".*)
Extract Constant randomSplit  => "(fun x -> (x,x))".
Extract Constant mkRandomSeed => "(fun x -> Random.init x; Random.get_state())".
(* Extract Constant randomRNat  => *)
(*   "(fun (x,y) r -> if y < x then failwith ""choose called with unordered arguments"" else  (x + (Random.State.int r (y - x + 1)), r))". *)
Extract Constant randomRBool => "(fun _ r -> Random.State.bool r, r)".
Extract Constant randomRInt  =>
          "(fun (x,y) r -> let yint = coqZToInt y in let xint = coqZToInt x in if (yint < xint) then failwith (Obj.magic coq_Monad_either) (Obj.magic coq_Exception_either) ""choose called with unordered arguments"" else (intToCoqZ (xint + (Random.State.int r (yint - xint + 1))), r))".
(* Extract Constant randomRN => *)
(*   "(fun (x,y) r -> if y < x then failwith ""choose called with unordered arguments"" else  (x + (Random.State.int r (y - x + 1)), r))". *)
Extract Constant newRandomSeed => "(Random.State.make_self_init ())".

Extract Inductive Lazy => "Lazy.t" [lazy].
Extract Constant force => "Lazy.force".

(* Extract Constant Test.ltAscii => "(<=)". *)
(* Extract Constant Test.strEq   => "(=)". *)
Extract Constant Nat.div => "(fun m -> function 0 -> 0 | d -> m / d)".
Extract Constant Test.gte => "(>=)".
Extract Constant le_gt_dec => "(<=)".
Extract Constant trace =>
  "(fun l -> print_string (
   let s = Bytes.create (List.length l) in
   let rec copy i = function
    | [] -> s
    | c :: l -> Bytes.set s i c; copy (i+1) l
   in Bytes.to_string (copy 0 l)); flush stdout; fun y -> y)".

Set Extraction AccessOpaque.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrnat ssrbool div eqtype.
Extract Constant divn => "(fun m -> function 0 -> 0 | d -> m / d)".
Extract Constant modn => "(fun m -> function 0 -> m | d -> m mod d)".
Extract Constant eqn => "(==)".

Axiom print_extracted_coq_string : string -> unit.
Extract Constant print_extracted_coq_string =>
 "fun l -> print_string (
   let s = Bytes.create (List.length l) in
   let rec copy i = function
    | [] -> s
    | c :: l -> s.[i] <- c; copy (i+1) l
   in Bytes.to_string (copy 0 l))".

Extract Inlined Constant add => "( + )".

(* Extract Inlined Constant sub => "sub". *)
(* Extract Inlined Constant eqb =  *)

(* Extract Constant randomRNat  => *)
(*   "(fun (x,y) r -> if y < x then failwith (Obj.magic monad_either) (Obj.magic exception_either) ""choose called with unordered arguments"" else  (x + (Random.State.int r (y - x + 1)), r))". *)
(* (* Extract Constant randomRBool => "(fun _ r -> Random.State.bool r, r)". *) *)
(* (* Extract Constant randomRInt  => *) *)
(* (*   "(fun (x,y) r -> if y < x then failwith (Obj.magic monad_either) (Obj.magic exception_either) ""choose called with unordered arguments"" else  (Big_int_Z.add_big_int x + Big_int_Z.big_int_of_int (Random.State.int r (y - x + 1)), r))". *) *)

(* Extract Constant randomRInt => *)
(*           "(fun (x,y) r -> if Big_int_Z.lt_big_int y x then failwith (Obj.magic monad_either) (Obj.magic exception_either) ""choose called with unordered arguments"" else let range_Z = Big_int_Z.succ_big_int (Big_int_Z.sub_big_int y x) in let range_int = Big_int_Z.int_of_big_int range_Z in (Big_int_Z.add_big_int x (Big_int_Z.big_int_of_int (Random.State.int r range_int)), r))". *)
(* Extract Constant randomRN => *)
(*           "(fun (x,y) r -> if y < x then failwith (Obj.magic monad_either) (Obj.magic exception_either) ""choose called with unordered arguments"" else  (x + (Random.State.int r (y - x + 1)), r))". *)


Extract Constant randomRNat  =>
  "(fun (x,y) r -> if y < x then failwith (Obj.magic coq_Monad_either) (Obj.magic coq_Exception_either) ""choose called with unordered arguments"" else  (x + (Random.State.int r (y - x + 1)), r))".
(* Extract Constant randomRBool => "(fun _ r -> Random.State.bool r, r)". *)
Extract Constant randomRInt  =>
  "(fun (x,y) r -> let yint = coqZToInt y in let xint = coqZToInt x in if (yint < xint) then failwith (Obj.magic coq_Monad_either) (Obj.magic coq_Exception_either) ""choose called with unordered arguments"" else (intToCoqZ (xint + (Random.State.int r (yint - xint + 1))), r))".

(* Extract Constant randomRInt => *)
(*           "(fun (x,y) r -> if y < x then failwith (Obj.magic coq_Monad_either) (Obj.magic coq_Exception_either) ""choose called with unordered arguments"" else let range_Z = (y - x) in let range_int = range_Z in (x + (Random.State.int r range_int), r))". *)
(* Extract Constant randomRN => *)
(*           "(fun (x,y) r -> if y < x then failwith (Obj.magic coq_Monad_either) (Obj.magic coq_Exception_either) ""choose called with unordered arguments"" else  (x + (Random.State.int r (y - x + 1)), r))". *)

(* not a constant? *)
(* Extract Constant raw_id => "LL.id". *)
(* Extract Constant typ => "LL.typ". *)

(* Extraction Blacklist typ. *)


(* Extraction Library GenAlive2. *)

Extraction "GenAlive2.ml" GenAlive2.GEN_ALIVE2.
(* Need a file to load this extraction *)

