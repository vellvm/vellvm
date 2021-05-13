From Coq Require Import
     Morphisms String.

Require Import List.
Import ListNotations.
Require Import ZArith.

From ITree Require Import
     ITree
     Basics.Monad
     Eq.Eq.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics
     Theory.Refinement.

Import ITreeNotations.
Import SemNotations.

Import ListNotations.
Definition repr_prog : list (toplevel_entity typ (block typ * list (block typ))). 
refine [TLE_Definition (mk_definition _ (mk_declaration (Name "main") (TYPE_Function ((TYPE_I 8)) []) ([], []) None None None None [] None None None) _ _)].
refine [].
      refine ((mk_block (Name "b0") [] [] (TERM_Br_1 (Name "b1")) None), [(mk_block (Name "b1") [] [((IId (Name "v0")), (INSTR_Op (OP_IBinop And (TYPE_I 64) (EXP_Integer (-3)%Z) (EXP_Integer (-3)%Z)))); ((IId (Name "v1")), (INSTR_Op (OP_ICmp Ule (TYPE_I 64) (EXP_Ident (ID_Local (Name "v0"))) (EXP_Integer (8)%Z)))); ((IId (Name "v2")), (INSTR_Op (OP_Select ( (TYPE_I 1), (EXP_Ident (ID_Local (Name "v1")))) ((TYPE_I 64), (EXP_Ident (ID_Local (Name "v0")))) ((TYPE_I 64), (EXP_Integer (8)%Z))))); ((IId (Name "v3")), (INSTR_Op (OP_ICmp Ugt (TYPE_I 64) (EXP_Ident (ID_Local (Name "v2"))) (EXP_Integer (0)%Z))))] (TERM_Br ((TYPE_I 1), (EXP_Ident (ID_Local (Name "v3")))) (Name "b4") (Name "b2")) None); (mk_block (Name "b4") [((Name "v5"), (Phi (TYPE_I 64)[((Name "b1"), (EXP_Ident (ID_Local (Name "v2")))); ((Name "b3"), (EXP_Ident (ID_Local (Name "v6"))))]))] [((IId (Name "v8")), (INSTR_Op (OP_IBinop And (TYPE_I 32) (EXP_Integer (1)%Z) (EXP_Integer (-3)%Z)))); ((IId (Name "v9")), (INSTR_Alloca (TYPE_I 8) None None)); ((IVoid (1)%Z), (INSTR_Store false ((TYPE_I 8), (EXP_Integer (0)%Z)) ((TYPE_Pointer (TYPE_I 8)), (EXP_Ident (ID_Local (Name "v9")))) None)); ((IId (Name "v10")), (INSTR_Alloca (TYPE_I 8) None None)); ((IVoid (2)%Z), (INSTR_Store false ((TYPE_I 8), (EXP_Integer (0)%Z)) ((TYPE_Pointer (TYPE_I 8)), (EXP_Ident (ID_Local (Name "v10")))) None))] (TERM_Ret ((TYPE_I 8), (EXP_Integer (0)%Z))) None); (mk_block (Name "b3") [] [((IId (Name "v6")), (INSTR_Op (OP_IBinop (Sub false false) (TYPE_I 64) (EXP_Ident (ID_Local (Name "v5"))) (EXP_Integer (1)%Z)))); ((IId (Name "v7")), (INSTR_Op (OP_ICmp Ugt (TYPE_I 64) (EXP_Ident (ID_Local (Name "v6"))) (EXP_Integer (0)%Z))))] (TERM_Br ((TYPE_I 1), (EXP_Ident (ID_Local (Name "v7")))) (Name "b4") (Name "b2")) None); (mk_block (Name "b2") [] [((IId (Name "v4")), (INSTR_Alloca (TYPE_I 1) None None)); ((IVoid (0)%Z), (INSTR_Store true ((TYPE_I 1), (EXP_Ident (ID_Local (Name "v3")))) ((TYPE_Pointer (TYPE_I 1)), (EXP_Ident (ID_Local (Name "v4")))) None))] (TERM_Ret ((TYPE_I 8), (EXP_Integer (3)%Z))) None)]).
Defined.

Definition parsed_prog : list (toplevel_entity typ (block typ * list (block typ))) :=
  [TLE_Definition {|
       df_prototype := {|dc_name := (Name "main");
                         dc_type := (TYPE_Function (TYPE_I 8%N) []);
                         dc_param_attrs := ([], []);
                         dc_linkage := None;
                         dc_visibility := None;
                         dc_dll_storage := None;
                         dc_cconv := None;
                         dc_attrs := [];
                         dc_section := None;
                         dc_align := None;
                         dc_gc := None|};
       df_args := [];
       df_instrs := (
                     {|
                       blk_id := (Name "b0");
                       blk_phis := [];
                       blk_code := [];
                       blk_term := TERM_Br_1 (Name "b1");
                       blk_comments := None
                     |},
                       [{|
                         blk_id := (Name "b1");
                         blk_phis := [];
                         blk_code := [(IId (Name "v0"), (INSTR_Op (OP_IBinop And (TYPE_I 64%N) (EXP_Integer (-3)%Z) (EXP_Integer (-3)%Z))));
                                     (IId (Name "v1"), (INSTR_Op (OP_ICmp Ule (TYPE_I 64%N) (EXP_Ident (ID_Local (Name "v0"))) (EXP_Integer (8)%Z))));
                                     (IId (Name "v2"), (INSTR_Op (OP_Select ((TYPE_I 1%N),(EXP_Ident (ID_Local (Name "v1")))) ((TYPE_I 64%N),(EXP_Ident (ID_Local (Name "v0")))) ((TYPE_I 64%N),(EXP_Integer (8)%Z)))));
                                     (IId (Name "v3"), (INSTR_Op (OP_ICmp Ugt (TYPE_I 64%N) (EXP_Ident (ID_Local (Name "v2"))) (EXP_Integer (0)%Z))))];
                         blk_term := TERM_Br ((TYPE_I 1%N), (EXP_Ident (ID_Local (Name "v3")))) (Name "b4") (Name "b2");
                         blk_comments := None
                       |};
                   {|
                     blk_id := (Name "b4");
                     blk_phis := [((Name "v5"), Phi (TYPE_I 64%N) [((Name "b3"), (EXP_Ident (ID_Local (Name "v6")))); ((Name "b1"), (EXP_Ident (ID_Local (Name "v2"))))])];
                     blk_code := [(IId (Name "v8"), (INSTR_Op (OP_IBinop And (TYPE_I 32%N) (EXP_Integer (1)%Z) (EXP_Integer (-3)%Z))));
                                 (IId (Name "v9"), (INSTR_Alloca (TYPE_I 8%N) None None));
                                 (IVoid 0%Z, (INSTR_Store false ((TYPE_I 8%N), (EXP_Integer (0)%Z)) ((TYPE_Pointer (TYPE_I 8%N)), (EXP_Ident (ID_Local (Name "v9")))) None));
                                 (IId (Name "v10"), (INSTR_Alloca (TYPE_I 8%N) None None));
                                 (IVoid 1%Z, (INSTR_Store false ((TYPE_I 8%N), (EXP_Integer (0)%Z)) ((TYPE_Pointer (TYPE_I 8%N)), (EXP_Ident (ID_Local (Name "v10")))) None))];
                     blk_term := TERM_Ret ((TYPE_I 8%N), (EXP_Integer (0)%Z));
                     blk_comments := None
                   |};
                   {|
                     blk_id := (Name "b3");
                     blk_phis := [];
                     blk_code := [(IId (Name "v6"), (INSTR_Op (OP_IBinop (Sub false false) (TYPE_I 64%N) (EXP_Ident (ID_Local (Name "v5"))) (EXP_Integer (1)%Z))));
                                 (IId (Name "v7"), (INSTR_Op (OP_ICmp Ugt (TYPE_I 64%N) (EXP_Ident (ID_Local (Name "v6"))) (EXP_Integer (0)%Z))))];
                     blk_term := TERM_Br ((TYPE_I 1%N), (EXP_Ident (ID_Local (Name "v7")))) (Name "b4") (Name "b2");
                     blk_comments := None
                   |};
                   {|
                     blk_id := (Name "b2");
                     blk_phis := [];
                     blk_code := [(IId (Name "v4"), (INSTR_Alloca (TYPE_I 1%N) None None));
                                 (IVoid 2%Z, (INSTR_Store false ((TYPE_I 1%N), (EXP_Ident (ID_Local (Name "v3")))) ((TYPE_Pointer (TYPE_I 1%N)), (EXP_Ident (ID_Local (Name "v4")))) None))];
                     blk_term := TERM_Ret ((TYPE_I 8%N), (EXP_Integer (3)%Z));
                     blk_comments := None
                   |}])
     |}].

From Vellvm Require
     Semantics.TopLevel
     Transformations.Transform
     Utils.ParserHelper.

Require ExtrOcamlBasic.
Require ExtrOcamlString.
Require ExtrOcamlIntConv.

Extraction Language OCaml.
Extraction Blacklist String List Char Core Z Format.


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

Extract Inlined Constant Archi.ppc64 => "false".

Set Extraction AccessOpaque.
(* NOTE: assumes that this file is compiled from /src *)
Cd "ml/extracted".

Extraction Library ExtrOcamlIntConv.
Recursive Extraction Library TopLevel.
Extraction Library Transform.
Extraction Library ParserHelper.

Extraction "test" repr_prog parsed_prog.