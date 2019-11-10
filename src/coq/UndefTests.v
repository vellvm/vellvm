From Vellvm Require Import LLVMAst CFG DynamicTypes.
Require Import List ZArith.
Import ListNotations.

From Coq Require Import List String Ascii ZArith.
Open Scope string_scope.



(* InstSimplify's undef.ll tests *)
Definition undef_test0_block : block dtyp :=
  {|
    blk_id := (Anon 0%Z);
    blk_phis := [];
    blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (Mul false false) (DTYPE_I 64%Z) EXP_Undef EXP_Undef)))];
    blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
    blk_comments := None
  |}.

Definition undef_test0_block_refine : block dtyp :=
  {|
    blk_id := (Anon 0%Z);
    blk_phis := [];
    blk_code := [];
    blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 64%Z), (EXP_Undef)));
    blk_comments := None
  |}.

Definition undef_test1_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (Mul false false) (DTYPE_I 64%Z) (EXP_Integer 3%Z) EXP_Undef)))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
      blk_comments := None
    |}.

Definition undef_test1_block_refine := undef_test0_block_refine.

Definition undef_test2_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (Mul false false) (DTYPE_I 64%Z) EXP_Undef (EXP_Integer 3%Z))))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
      blk_comments := None
    |}.

Definition undef_test2_block_refine := undef_test0_block_refine.

Definition undef_test3_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (Mul false false) (DTYPE_I 64%Z) EXP_Undef (EXP_Integer 6%Z))))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
      blk_comments := None
    |}.

Definition undef_test3_block_refine : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 64%Z), (EXP_Integer 0%Z)));
      blk_comments := None
    |}.


Definition undef_test4_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (Mul false false) (DTYPE_I 64%Z) (EXP_Integer 6%Z) EXP_Undef)))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
      blk_comments := None
    |}.

Definition undef_test4_block_refine := undef_test3_block_refine.

Definition undef_test5_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop And (DTYPE_I 64%Z) EXP_Undef EXP_Undef)))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
      blk_comments := None
    |}.

Definition undef_test5_block_refine := undef_test0_block_refine.

Definition undef_test6_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop Or (DTYPE_I 64%Z) EXP_Undef EXP_Undef)))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
      blk_comments := None
    |}.

Definition undef_test6_block_refine := undef_test0_block_refine.

Definition undef_test7_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (UDiv false) (DTYPE_I 64%Z) EXP_Undef (EXP_Integer 1%Z))))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
      blk_comments := None
    |}.

Definition undef_test7_block_refine := undef_test0_block_refine.

Definition undef_test8_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (SDiv false) (DTYPE_I 64%Z) EXP_Undef (EXP_Integer 1%Z))))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
      blk_comments := None
    |}.

Definition undef_test8_block_refine := undef_test0_block_refine.

Definition undef_test9_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop URem (DTYPE_I 64%Z) EXP_Undef (EXP_Integer 1%Z))))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
      blk_comments := None
    |}.

Definition undef_test9_block_refine := undef_test3_block_refine.

Definition undef_test10_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop SRem (DTYPE_I 64%Z) EXP_Undef (EXP_Integer 1%Z))))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
      blk_comments := None
    |}.

Definition undef_test10_block_refine := undef_test3_block_refine.

Definition undef_test11_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (Shl false false) (DTYPE_I 64%Z) EXP_Undef EXP_Undef)))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
      blk_comments := None
    |}.

Definition undef_test11b_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (Shl false false) (DTYPE_I 64%Z) (EXP_Ident (ID_Local (Name "a"))) EXP_Undef)))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
      blk_comments := None
    |}.

Definition undef_test12_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (AShr false) (DTYPE_I 64%Z) EXP_Undef EXP_Undef)))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
      blk_comments := None
    |}.

Definition undef_test12b_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (AShr false) (DTYPE_I 64%Z) (EXP_Ident (ID_Local (Name "a"))) EXP_Undef)))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
      blk_comments := None
    |}.

Definition undef_test13_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (LShr false) (DTYPE_I 64%Z) EXP_Undef EXP_Undef)))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
      blk_comments := None
    |}.

Definition undef_test13b_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (LShr false) (DTYPE_I 64%Z) (EXP_Ident (ID_Local (Name "a"))) EXP_Undef)))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
      blk_comments := None
    |}.

Definition undef_test14_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "r"), (INSTR_Op (OP_ICmp Slt (DTYPE_I 64%Z) EXP_Undef EXP_Undef)))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 1%Z), (EXP_Ident (ID_Local (Name "r")))));
      blk_comments := None
    |}.

Definition undef_test15_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "r"), (INSTR_Op (OP_ICmp Ult (DTYPE_I 64%Z) EXP_Undef EXP_Undef)))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 1%Z), (EXP_Ident (ID_Local (Name "r")))));
      blk_comments := None
    |}.

Definition undef_test16_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "r"), (INSTR_Op (OP_Select ((DTYPE_I 1%Z),EXP_Undef) ((DTYPE_I 64%Z),(EXP_Ident (ID_Local (Name "a")))) ((DTYPE_I 64%Z),EXP_Undef))))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
      blk_comments := None
    |}.

Definition undef_test17_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "r"), (INSTR_Op (OP_Select ((DTYPE_I 1%Z),EXP_Undef) ((DTYPE_I 64%Z),EXP_Undef) ((DTYPE_I 64%Z),(EXP_Ident (ID_Local (Name "a")))))))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
      blk_comments := None
    |}.

Definition undef_test18_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "r"), (INSTR_Call ((DTYPE_Pointer), @EXP_Undef dtyp) [((DTYPE_I 64%Z), (EXP_Ident (ID_Local (Name "a"))))]))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
      blk_comments := None
    |}.

Definition undef_test19_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (Shl false false) (DTYPE_Vector 4%Z (DTYPE_I 8%Z)) (EXP_Ident (ID_Local (Name "a"))) (EXP_Vector [((DTYPE_I 8%Z),(EXP_Integer 8%Z)); ((DTYPE_I 8%Z),(EXP_Integer 9%Z)); ((DTYPE_I 8%Z),EXP_Undef); ((DTYPE_I 8%Z), (EXP_Integer (-1)%Z))]))))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_Vector 4%Z (DTYPE_I 8%Z)), (EXP_Ident (ID_Local (Name "b")))));
      blk_comments := None
    |}.

Definition undef_test20_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (UDiv false) (DTYPE_I 32%Z) (EXP_Ident (ID_Local (Name "a"))) (EXP_Integer 0%Z))))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
      blk_comments := None
    |}.

Definition undef_test20vec_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (UDiv false) (DTYPE_Vector 2%Z (DTYPE_I 32%Z)) (EXP_Ident (ID_Local (Name "a"))) EXP_Zero_initializer)))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_Vector 2%Z (DTYPE_I 32%Z)), (EXP_Ident (ID_Local (Name "b")))));
      blk_comments := None
    |}.

Definition undef_test21_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (SDiv false) (DTYPE_I 32%Z) (EXP_Ident (ID_Local (Name "a"))) (EXP_Integer 0%Z))))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
      blk_comments := None
    |}.

Definition undef_test21vec_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (SDiv false) (DTYPE_Vector 2%Z (DTYPE_I 32%Z)) (EXP_Ident (ID_Local (Name "a"))) EXP_Zero_initializer)))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_Vector 2%Z (DTYPE_I 32%Z)), (EXP_Ident (ID_Local (Name "b")))));
      blk_comments := None
    |}.

Definition undef_test22_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (AShr true) (DTYPE_I 32%Z) EXP_Undef (EXP_Ident (ID_Local (Name "a"))))))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
      blk_comments := None
    |}.

Definition undef_test23_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (LShr true) (DTYPE_I 32%Z) EXP_Undef (EXP_Ident (ID_Local (Name "a"))))))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
      blk_comments := None
    |}.

Definition undef_test24_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (UDiv false) (DTYPE_I 32%Z) EXP_Undef (EXP_Integer 0%Z))))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
      blk_comments := None
    |}.

Definition undef_test25_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (LShr false) (DTYPE_I 32%Z) (EXP_Integer 0%Z) EXP_Undef)))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
      blk_comments := None
    |}.

Definition undef_test26_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (AShr false) (DTYPE_I 32%Z) (EXP_Integer 0%Z) EXP_Undef)))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
      blk_comments := None
    |}.

Definition undef_test27_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (Shl false false) (DTYPE_I 32%Z) (EXP_Integer 0%Z) EXP_Undef)))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
      blk_comments := None
    |}.

Definition undef_test28_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (Shl false true) (DTYPE_I 32%Z) EXP_Undef (EXP_Ident (ID_Local (Name "a"))))))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
      blk_comments := None
    |}.

Definition undef_test29_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (Shl true false) (DTYPE_I 32%Z) EXP_Undef (EXP_Ident (ID_Local (Name "a"))))))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
      blk_comments := None
    |}.

Definition undef_test30_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (Shl true true) (DTYPE_I 32%Z) EXP_Undef (EXP_Ident (ID_Local (Name "a"))))))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
      blk_comments := None
    |}.

Definition undef_test31_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (Shl false false) (DTYPE_I 32%Z) EXP_Undef (EXP_Ident (ID_Local (Name "a"))))))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
      blk_comments := None
    |}.

Definition undef_test32_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (Shl false false) (DTYPE_I 32%Z) EXP_Undef (EXP_Integer 0%Z))))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
      blk_comments := None
    |}.

Definition undef_test33_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (AShr false) (DTYPE_I 32%Z) EXP_Undef (EXP_Integer 0%Z))))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
      blk_comments := None
    |}.

Definition undef_test34_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (LShr false) (DTYPE_I 32%Z) EXP_Undef (EXP_Integer 0%Z))))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
      blk_comments := None
    |}.

Definition undef_test35_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "b"), (INSTR_Op (OP_ExtractElement ((DTYPE_Vector 4%Z (DTYPE_I 32%Z)),(EXP_Ident (ID_Local (Name "V")))) ((DTYPE_I 32%Z),(EXP_Integer 4%Z)))))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
      blk_comments := None
    |}.

Definition undef_test36_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "b"), (INSTR_Op (OP_ExtractElement ((DTYPE_Vector 4%Z (DTYPE_I 32%Z)),EXP_Undef) ((DTYPE_I 32%Z),(EXP_Ident (ID_Local (Name "V")))))))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
      blk_comments := None
    |}.

Definition undef_test37_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (UDiv false) (DTYPE_I 32%Z) EXP_Undef EXP_Undef)))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
      blk_comments := None
    |}.

Definition undef_test38_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (UDiv false) (DTYPE_I 32%Z) (EXP_Ident (ID_Local (Name "a"))) EXP_Undef)))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
      blk_comments := None
    |}.

Definition undef_test39_block : block dtyp
  := {|
      blk_id := (Anon 0%Z);
      blk_phis := [];
      blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (UDiv false) (DTYPE_I 32%Z) (EXP_Integer 0%Z) EXP_Undef)))];
      blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
      blk_comments := None
    |}.


(* InstSimplify's undef.ll tests *)
Definition undef_test0_cfg : cfg dtyp :=
  {| init := (Anon 0%Z);
     blks := [{|
                 blk_id := (Anon 0%Z);
                 blk_phis := [];
                 blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (Mul false false) (DTYPE_I 64%Z) EXP_Undef EXP_Undef)))];
                 blk_term := (IVoid 0%Z, TERM_Ret ((DTYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                 blk_comments := None
               |}];
     args := [];
  |}.

Definition undef_test0 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "main");
                            dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (Mul false false) (TYPE_I 64%Z) EXP_Undef EXP_Undef)))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test0_refine : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "main");
                            dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Undef)));
                          blk_comments := None
                        |}]
        |}].


Definition undef_test1 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test1");
                            dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (Mul false false) (TYPE_I 64%Z) (EXP_Integer 3%Z) EXP_Undef)))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test2 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test2");
                            dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (Mul false false) (TYPE_I 64%Z) EXP_Undef (EXP_Integer 3%Z))))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test3 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test3");
                            dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (Mul false false) (TYPE_I 64%Z) EXP_Undef (EXP_Integer 6%Z))))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test4 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test4");
                            dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (Mul false false) (TYPE_I 64%Z) (EXP_Integer 6%Z) EXP_Undef)))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test5 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test5");
                            dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop And (TYPE_I 64%Z) EXP_Undef EXP_Undef)))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test6 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test6");
                            dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop Or (TYPE_I 64%Z) EXP_Undef EXP_Undef)))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test7 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test7");
                            dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (UDiv false) (TYPE_I 64%Z) EXP_Undef (EXP_Integer 1%Z))))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test8 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test8");
                            dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (SDiv false) (TYPE_I 64%Z) EXP_Undef (EXP_Integer 1%Z))))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test9 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test9");
                            dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop URem (TYPE_I 64%Z) EXP_Undef (EXP_Integer 1%Z))))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test10 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test10");
                            dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop SRem (TYPE_I 64%Z) EXP_Undef (EXP_Integer 1%Z))))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test11 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test11");
                            dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (Shl false false) (TYPE_I 64%Z) EXP_Undef EXP_Undef)))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test11b : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test11b");
                            dc_type := (TYPE_Function (TYPE_I 64%Z) [(TYPE_I 64%Z)]);
                            dc_param_attrs := ([], []);
                            dc_linkage := None;
                            dc_visibility := None;
                            dc_dll_storage := None;
                            dc_cconv := None;
                            dc_attrs := [];
                            dc_section := None;
                            dc_align := None;
                            dc_gc := None|};
          df_args := [(Name "a")];
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (Shl false false) (TYPE_I 64%Z) (EXP_Ident (ID_Local (Name "a"))) EXP_Undef)))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test12 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test12");
                            dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (AShr false) (TYPE_I 64%Z) EXP_Undef EXP_Undef)))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test12b : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test12b");
                            dc_type := (TYPE_Function (TYPE_I 64%Z) [(TYPE_I 64%Z)]);
                            dc_param_attrs := ([], []);
                            dc_linkage := None;
                            dc_visibility := None;
                            dc_dll_storage := None;
                            dc_cconv := None;
                            dc_attrs := [];
                            dc_section := None;
                            dc_align := None;
                            dc_gc := None|};
          df_args := [(Name "a")];
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (AShr false) (TYPE_I 64%Z) (EXP_Ident (ID_Local (Name "a"))) EXP_Undef)))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test13 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test13");
                            dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (LShr false) (TYPE_I 64%Z) EXP_Undef EXP_Undef)))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test13b : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test13b");
                            dc_type := (TYPE_Function (TYPE_I 64%Z) [(TYPE_I 64%Z)]);
                            dc_param_attrs := ([], []);
                            dc_linkage := None;
                            dc_visibility := None;
                            dc_dll_storage := None;
                            dc_cconv := None;
                            dc_attrs := [];
                            dc_section := None;
                            dc_align := None;
                            dc_gc := None|};
          df_args := [(Name "a")];
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (LShr false) (TYPE_I 64%Z) (EXP_Ident (ID_Local (Name "a"))) EXP_Undef)))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test14 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test14");
                            dc_type := (TYPE_Function (TYPE_I 1%Z) []);
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
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "r"), (INSTR_Op (OP_ICmp Slt (TYPE_I 64%Z) EXP_Undef EXP_Undef)))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 1%Z), (EXP_Ident (ID_Local (Name "r")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test15 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test15");
                            dc_type := (TYPE_Function (TYPE_I 1%Z) []);
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
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "r"), (INSTR_Op (OP_ICmp Ult (TYPE_I 64%Z) EXP_Undef EXP_Undef)))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 1%Z), (EXP_Ident (ID_Local (Name "r")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test16 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test16");
                            dc_type := (TYPE_Function (TYPE_I 64%Z) [(TYPE_I 64%Z)]);
                            dc_param_attrs := ([], []);
                            dc_linkage := None;
                            dc_visibility := None;
                            dc_dll_storage := None;
                            dc_cconv := None;
                            dc_attrs := [];
                            dc_section := None;
                            dc_align := None;
                            dc_gc := None|};
          df_args := [(Name "a")];
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "r"), (INSTR_Op (OP_Select ((TYPE_I 1%Z),EXP_Undef) ((TYPE_I 64%Z),(EXP_Ident (ID_Local (Name "a")))) ((TYPE_I 64%Z),EXP_Undef))))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test17 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test17");
                            dc_type := (TYPE_Function (TYPE_I 64%Z) [(TYPE_I 64%Z)]);
                            dc_param_attrs := ([], []);
                            dc_linkage := None;
                            dc_visibility := None;
                            dc_dll_storage := None;
                            dc_cconv := None;
                            dc_attrs := [];
                            dc_section := None;
                            dc_align := None;
                            dc_gc := None|};
          df_args := [(Name "a")];
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "r"), (INSTR_Op (OP_Select ((TYPE_I 1%Z),EXP_Undef) ((TYPE_I 64%Z),EXP_Undef) ((TYPE_I 64%Z),(EXP_Ident (ID_Local (Name "a")))))))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test18 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test18");
                            dc_type := (TYPE_Function (TYPE_I 64%Z) [(TYPE_I 64%Z)]);
                            dc_param_attrs := ([], []);
                            dc_linkage := None;
                            dc_visibility := None;
                            dc_dll_storage := None;
                            dc_cconv := None;
                            dc_attrs := [];
                            dc_section := None;
                            dc_align := None;
                            dc_gc := None|};
          df_args := [(Name "a")];
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "r"), (INSTR_Call ((TYPE_Function (TYPE_I 64%Z) [(TYPE_I 64%Z)]), EXP_Undef) [((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "a"))))]))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test19 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test19");
                            dc_type := (TYPE_Function (TYPE_Vector 4%Z (TYPE_I 8%Z)) [(TYPE_Vector 4%Z (TYPE_I 8%Z))]);
                            dc_param_attrs := ([], []);
                            dc_linkage := None;
                            dc_visibility := None;
                            dc_dll_storage := None;
                            dc_cconv := None;
                            dc_attrs := [];
                            dc_section := None;
                            dc_align := None;
                            dc_gc := None|};
          df_args := [(Name "a")];
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (Shl false false) (TYPE_Vector 4%Z (TYPE_I 8%Z)) (EXP_Ident (ID_Local (Name "a"))) (EXP_Vector [((TYPE_I 8%Z),(EXP_Integer 8%Z)); ((TYPE_I 8%Z),(EXP_Integer 9%Z)); ((TYPE_I 8%Z),EXP_Undef); ((TYPE_I 8%Z), (EXP_Integer (-1)%Z))]))))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_Vector 4%Z (TYPE_I 8%Z)), (EXP_Ident (ID_Local (Name "b")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test20 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test20");
                            dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                            dc_param_attrs := ([], []);
                            dc_linkage := None;
                            dc_visibility := None;
                            dc_dll_storage := None;
                            dc_cconv := None;
                            dc_attrs := [];
                            dc_section := None;
                            dc_align := None;
                            dc_gc := None|};
          df_args := [(Name "a")];
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (UDiv false) (TYPE_I 32%Z) (EXP_Ident (ID_Local (Name "a"))) (EXP_Integer 0%Z))))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test20vec : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test20vec");
                            dc_type := (TYPE_Function (TYPE_Vector 2%Z (TYPE_I 32%Z)) [(TYPE_Vector 2%Z (TYPE_I 32%Z))]);
                            dc_param_attrs := ([], []);
                            dc_linkage := None;
                            dc_visibility := None;
                            dc_dll_storage := None;
                            dc_cconv := None;
                            dc_attrs := [];
                            dc_section := None;
                            dc_align := None;
                            dc_gc := None|};
          df_args := [(Name "a")];
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (UDiv false) (TYPE_Vector 2%Z (TYPE_I 32%Z)) (EXP_Ident (ID_Local (Name "a"))) EXP_Zero_initializer)))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_Vector 2%Z (TYPE_I 32%Z)), (EXP_Ident (ID_Local (Name "b")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test21 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test21");
                            dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                            dc_param_attrs := ([], []);
                            dc_linkage := None;
                            dc_visibility := None;
                            dc_dll_storage := None;
                            dc_cconv := None;
                            dc_attrs := [];
                            dc_section := None;
                            dc_align := None;
                            dc_gc := None|};
          df_args := [(Name "a")];
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (SDiv false) (TYPE_I 32%Z) (EXP_Ident (ID_Local (Name "a"))) (EXP_Integer 0%Z))))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test21vec : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test21vec");
                            dc_type := (TYPE_Function (TYPE_Vector 2%Z (TYPE_I 32%Z)) [(TYPE_Vector 2%Z (TYPE_I 32%Z))]);
                            dc_param_attrs := ([], []);
                            dc_linkage := None;
                            dc_visibility := None;
                            dc_dll_storage := None;
                            dc_cconv := None;
                            dc_attrs := [];
                            dc_section := None;
                            dc_align := None;
                            dc_gc := None|};
          df_args := [(Name "a")];
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (SDiv false) (TYPE_Vector 2%Z (TYPE_I 32%Z)) (EXP_Ident (ID_Local (Name "a"))) EXP_Zero_initializer)))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_Vector 2%Z (TYPE_I 32%Z)), (EXP_Ident (ID_Local (Name "b")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test22 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test22");
                            dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                            dc_param_attrs := ([], []);
                            dc_linkage := None;
                            dc_visibility := None;
                            dc_dll_storage := None;
                            dc_cconv := None;
                            dc_attrs := [];
                            dc_section := None;
                            dc_align := None;
                            dc_gc := None|};
          df_args := [(Name "a")];
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (AShr true) (TYPE_I 32%Z) EXP_Undef (EXP_Ident (ID_Local (Name "a"))))))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test23 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test23");
                            dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                            dc_param_attrs := ([], []);
                            dc_linkage := None;
                            dc_visibility := None;
                            dc_dll_storage := None;
                            dc_cconv := None;
                            dc_attrs := [];
                            dc_section := None;
                            dc_align := None;
                            dc_gc := None|};
          df_args := [(Name "a")];
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (LShr true) (TYPE_I 32%Z) EXP_Undef (EXP_Ident (ID_Local (Name "a"))))))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test24 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test24");
                            dc_type := (TYPE_Function (TYPE_I 32%Z) []);
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
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (UDiv false) (TYPE_I 32%Z) EXP_Undef (EXP_Integer 0%Z))))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test25 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test25");
                            dc_type := (TYPE_Function (TYPE_I 32%Z) []);
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
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (LShr false) (TYPE_I 32%Z) (EXP_Integer 0%Z) EXP_Undef)))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test26 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test26");
                            dc_type := (TYPE_Function (TYPE_I 32%Z) []);
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
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (AShr false) (TYPE_I 32%Z) (EXP_Integer 0%Z) EXP_Undef)))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test27 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test27");
                            dc_type := (TYPE_Function (TYPE_I 32%Z) []);
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
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (Shl false false) (TYPE_I 32%Z) (EXP_Integer 0%Z) EXP_Undef)))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test28 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test28");
                            dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                            dc_param_attrs := ([], []);
                            dc_linkage := None;
                            dc_visibility := None;
                            dc_dll_storage := None;
                            dc_cconv := None;
                            dc_attrs := [];
                            dc_section := None;
                            dc_align := None;
                            dc_gc := None|};
          df_args := [(Name "a")];
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (Shl false true) (TYPE_I 32%Z) EXP_Undef (EXP_Ident (ID_Local (Name "a"))))))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test29 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test29");
                            dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                            dc_param_attrs := ([], []);
                            dc_linkage := None;
                            dc_visibility := None;
                            dc_dll_storage := None;
                            dc_cconv := None;
                            dc_attrs := [];
                            dc_section := None;
                            dc_align := None;
                            dc_gc := None|};
          df_args := [(Name "a")];
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (Shl true false) (TYPE_I 32%Z) EXP_Undef (EXP_Ident (ID_Local (Name "a"))))))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test30 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test30");
                            dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                            dc_param_attrs := ([], []);
                            dc_linkage := None;
                            dc_visibility := None;
                            dc_dll_storage := None;
                            dc_cconv := None;
                            dc_attrs := [];
                            dc_section := None;
                            dc_align := None;
                            dc_gc := None|};
          df_args := [(Name "a")];
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (Shl true true) (TYPE_I 32%Z) EXP_Undef (EXP_Ident (ID_Local (Name "a"))))))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test31 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test31");
                            dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                            dc_param_attrs := ([], []);
                            dc_linkage := None;
                            dc_visibility := None;
                            dc_dll_storage := None;
                            dc_cconv := None;
                            dc_attrs := [];
                            dc_section := None;
                            dc_align := None;
                            dc_gc := None|};
          df_args := [(Name "a")];
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (Shl false false) (TYPE_I 32%Z) EXP_Undef (EXP_Ident (ID_Local (Name "a"))))))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test32 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test32");
                            dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                            dc_param_attrs := ([], []);
                            dc_linkage := None;
                            dc_visibility := None;
                            dc_dll_storage := None;
                            dc_cconv := None;
                            dc_attrs := [];
                            dc_section := None;
                            dc_align := None;
                            dc_gc := None|};
          df_args := [(Name "a")];
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (Shl false false) (TYPE_I 32%Z) EXP_Undef (EXP_Integer 0%Z))))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test33 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test33");
                            dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                            dc_param_attrs := ([], []);
                            dc_linkage := None;
                            dc_visibility := None;
                            dc_dll_storage := None;
                            dc_cconv := None;
                            dc_attrs := [];
                            dc_section := None;
                            dc_align := None;
                            dc_gc := None|};
          df_args := [(Name "a")];
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (AShr false) (TYPE_I 32%Z) EXP_Undef (EXP_Integer 0%Z))))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test34 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test34");
                            dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                            dc_param_attrs := ([], []);
                            dc_linkage := None;
                            dc_visibility := None;
                            dc_dll_storage := None;
                            dc_cconv := None;
                            dc_attrs := [];
                            dc_section := None;
                            dc_align := None;
                            dc_gc := None|};
          df_args := [(Name "a")];
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (LShr false) (TYPE_I 32%Z) EXP_Undef (EXP_Integer 0%Z))))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test35 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test35");
                            dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_Vector 4%Z (TYPE_I 32%Z))]);
                            dc_param_attrs := ([], []);
                            dc_linkage := None;
                            dc_visibility := None;
                            dc_dll_storage := None;
                            dc_cconv := None;
                            dc_attrs := [];
                            dc_section := None;
                            dc_align := None;
                            dc_gc := None|};
          df_args := [(Name "V")];
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "b"), (INSTR_Op (OP_ExtractElement ((TYPE_Vector 4%Z (TYPE_I 32%Z)),(EXP_Ident (ID_Local (Name "V")))) ((TYPE_I 32%Z),(EXP_Integer 4%Z)))))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test36 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test36");
                            dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                            dc_param_attrs := ([], []);
                            dc_linkage := None;
                            dc_visibility := None;
                            dc_dll_storage := None;
                            dc_cconv := None;
                            dc_attrs := [];
                            dc_section := None;
                            dc_align := None;
                            dc_gc := None|};
          df_args := [(Name "V")];
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "b"), (INSTR_Op (OP_ExtractElement ((TYPE_Vector 4%Z (TYPE_I 32%Z)),EXP_Undef) ((TYPE_I 32%Z),(EXP_Ident (ID_Local (Name "V")))))))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test37 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test37");
                            dc_type := (TYPE_Function (TYPE_I 32%Z) []);
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
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (UDiv false) (TYPE_I 32%Z) EXP_Undef EXP_Undef)))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test38 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test38");
                            dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                            dc_param_attrs := ([], []);
                            dc_linkage := None;
                            dc_visibility := None;
                            dc_dll_storage := None;
                            dc_cconv := None;
                            dc_attrs := [];
                            dc_section := None;
                            dc_align := None;
                            dc_gc := None|};
          df_args := [(Name "a")];
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (UDiv false) (TYPE_I 32%Z) (EXP_Ident (ID_Local (Name "a"))) EXP_Undef)))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                          blk_comments := None
                        |}]
        |}].

Definition undef_test39 : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
          df_prototype := {|dc_name := (Name "test39");
                            dc_type := (TYPE_Function (TYPE_I 32%Z) []);
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
          df_instrs := [
                        {|
                          blk_id := (Anon 0%Z);
                          blk_phis := [];
                          blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (UDiv false) (TYPE_I 32%Z) (EXP_Integer 0%Z) EXP_Undef)))];
                          blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                          blk_comments := None
                        |}]
        |}].

(* InstSimplify's undef.ll tests *)
Definition undef_tests : list (toplevel_entity typ (list (block typ)))
  := [TLE_Definition {|
  df_prototype := {|dc_name := (Name "test0");
                    dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (Mul false false) (TYPE_I 64%Z) EXP_Undef EXP_Undef)))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test1");
                    dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (Mul false false) (TYPE_I 64%Z) (EXP_Integer 3%Z) EXP_Undef)))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test2");
                    dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (Mul false false) (TYPE_I 64%Z) EXP_Undef (EXP_Integer 3%Z))))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test3");
                    dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (Mul false false) (TYPE_I 64%Z) EXP_Undef (EXP_Integer 6%Z))))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test4");
                    dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (Mul false false) (TYPE_I 64%Z) (EXP_Integer 6%Z) EXP_Undef)))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test5");
                    dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop And (TYPE_I 64%Z) EXP_Undef EXP_Undef)))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test6");
                    dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop Or (TYPE_I 64%Z) EXP_Undef EXP_Undef)))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test7");
                    dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (UDiv false) (TYPE_I 64%Z) EXP_Undef (EXP_Integer 1%Z))))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test8");
                    dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (SDiv false) (TYPE_I 64%Z) EXP_Undef (EXP_Integer 1%Z))))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test9");
                    dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop URem (TYPE_I 64%Z) EXP_Undef (EXP_Integer 1%Z))))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test10");
                    dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop SRem (TYPE_I 64%Z) EXP_Undef (EXP_Integer 1%Z))))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test11");
                    dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (Shl false false) (TYPE_I 64%Z) EXP_Undef EXP_Undef)))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test11b");
                    dc_type := (TYPE_Function (TYPE_I 64%Z) [(TYPE_I 64%Z)]);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [(Name "a")];
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (Shl false false) (TYPE_I 64%Z) (EXP_Ident (ID_Local (Name "a"))) EXP_Undef)))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test12");
                    dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (AShr false) (TYPE_I 64%Z) EXP_Undef EXP_Undef)))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test12b");
                    dc_type := (TYPE_Function (TYPE_I 64%Z) [(TYPE_I 64%Z)]);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [(Name "a")];
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (AShr false) (TYPE_I 64%Z) (EXP_Ident (ID_Local (Name "a"))) EXP_Undef)))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test13");
                    dc_type := (TYPE_Function (TYPE_I 64%Z) []);
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
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (LShr false) (TYPE_I 64%Z) EXP_Undef EXP_Undef)))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test13b");
                    dc_type := (TYPE_Function (TYPE_I 64%Z) [(TYPE_I 64%Z)]);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [(Name "a")];
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "r"), (INSTR_Op (OP_IBinop (LShr false) (TYPE_I 64%Z) (EXP_Ident (ID_Local (Name "a"))) EXP_Undef)))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test14");
                    dc_type := (TYPE_Function (TYPE_I 1%Z) []);
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
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "r"), (INSTR_Op (OP_ICmp Slt (TYPE_I 64%Z) EXP_Undef EXP_Undef)))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 1%Z), (EXP_Ident (ID_Local (Name "r")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test15");
                    dc_type := (TYPE_Function (TYPE_I 1%Z) []);
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
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "r"), (INSTR_Op (OP_ICmp Ult (TYPE_I 64%Z) EXP_Undef EXP_Undef)))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 1%Z), (EXP_Ident (ID_Local (Name "r")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test16");
                    dc_type := (TYPE_Function (TYPE_I 64%Z) [(TYPE_I 64%Z)]);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [(Name "a")];
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "r"), (INSTR_Op (OP_Select ((TYPE_I 1%Z),EXP_Undef) ((TYPE_I 64%Z),(EXP_Ident (ID_Local (Name "a")))) ((TYPE_I 64%Z),EXP_Undef))))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test17");
                    dc_type := (TYPE_Function (TYPE_I 64%Z) [(TYPE_I 64%Z)]);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [(Name "a")];
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "r"), (INSTR_Op (OP_Select ((TYPE_I 1%Z),EXP_Undef) ((TYPE_I 64%Z),EXP_Undef) ((TYPE_I 64%Z),(EXP_Ident (ID_Local (Name "a")))))))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test18");
                    dc_type := (TYPE_Function (TYPE_I 64%Z) [(TYPE_I 64%Z)]);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [(Name "a")];
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "r"), (INSTR_Call ((TYPE_Function (TYPE_I 64%Z) [(TYPE_I 64%Z)]), EXP_Undef) [((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "a"))))]))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 64%Z), (EXP_Ident (ID_Local (Name "r")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test19");
                    dc_type := (TYPE_Function (TYPE_Vector 4%Z (TYPE_I 8%Z)) [(TYPE_Vector 4%Z (TYPE_I 8%Z))]);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [(Name "a")];
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (Shl false false) (TYPE_Vector 4%Z (TYPE_I 8%Z)) (EXP_Ident (ID_Local (Name "a"))) (EXP_Vector [((TYPE_I 8%Z),(EXP_Integer 8%Z)); ((TYPE_I 8%Z),(EXP_Integer 9%Z)); ((TYPE_I 8%Z),EXP_Undef); ((TYPE_I 8%Z), (EXP_Integer (-1)%Z))]))))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_Vector 4%Z (TYPE_I 8%Z)), (EXP_Ident (ID_Local (Name "b")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test20");
                    dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [(Name "a")];
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (UDiv false) (TYPE_I 32%Z) (EXP_Ident (ID_Local (Name "a"))) (EXP_Integer 0%Z))))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test20vec");
                    dc_type := (TYPE_Function (TYPE_Vector 2%Z (TYPE_I 32%Z)) [(TYPE_Vector 2%Z (TYPE_I 32%Z))]);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [(Name "a")];
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (UDiv false) (TYPE_Vector 2%Z (TYPE_I 32%Z)) (EXP_Ident (ID_Local (Name "a"))) EXP_Zero_initializer)))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_Vector 2%Z (TYPE_I 32%Z)), (EXP_Ident (ID_Local (Name "b")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test21");
                    dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [(Name "a")];
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (SDiv false) (TYPE_I 32%Z) (EXP_Ident (ID_Local (Name "a"))) (EXP_Integer 0%Z))))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test21vec");
                    dc_type := (TYPE_Function (TYPE_Vector 2%Z (TYPE_I 32%Z)) [(TYPE_Vector 2%Z (TYPE_I 32%Z))]);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [(Name "a")];
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (SDiv false) (TYPE_Vector 2%Z (TYPE_I 32%Z)) (EXP_Ident (ID_Local (Name "a"))) EXP_Zero_initializer)))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_Vector 2%Z (TYPE_I 32%Z)), (EXP_Ident (ID_Local (Name "b")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test22");
                    dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [(Name "a")];
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (AShr true) (TYPE_I 32%Z) EXP_Undef (EXP_Ident (ID_Local (Name "a"))))))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test23");
                    dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [(Name "a")];
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (LShr true) (TYPE_I 32%Z) EXP_Undef (EXP_Ident (ID_Local (Name "a"))))))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test24");
                    dc_type := (TYPE_Function (TYPE_I 32%Z) []);
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
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (UDiv false) (TYPE_I 32%Z) EXP_Undef (EXP_Integer 0%Z))))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test25");
                    dc_type := (TYPE_Function (TYPE_I 32%Z) []);
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
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (LShr false) (TYPE_I 32%Z) (EXP_Integer 0%Z) EXP_Undef)))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test26");
                    dc_type := (TYPE_Function (TYPE_I 32%Z) []);
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
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (AShr false) (TYPE_I 32%Z) (EXP_Integer 0%Z) EXP_Undef)))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test27");
                    dc_type := (TYPE_Function (TYPE_I 32%Z) []);
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
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (Shl false false) (TYPE_I 32%Z) (EXP_Integer 0%Z) EXP_Undef)))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test28");
                    dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [(Name "a")];
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (Shl false true) (TYPE_I 32%Z) EXP_Undef (EXP_Ident (ID_Local (Name "a"))))))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test29");
                    dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [(Name "a")];
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (Shl true false) (TYPE_I 32%Z) EXP_Undef (EXP_Ident (ID_Local (Name "a"))))))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test30");
                    dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [(Name "a")];
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (Shl true true) (TYPE_I 32%Z) EXP_Undef (EXP_Ident (ID_Local (Name "a"))))))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test31");
                    dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [(Name "a")];
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (Shl false false) (TYPE_I 32%Z) EXP_Undef (EXP_Ident (ID_Local (Name "a"))))))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test32");
                    dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [(Name "a")];
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (Shl false false) (TYPE_I 32%Z) EXP_Undef (EXP_Integer 0%Z))))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test33");
                    dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [(Name "a")];
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (AShr false) (TYPE_I 32%Z) EXP_Undef (EXP_Integer 0%Z))))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test34");
                    dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [(Name "a")];
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (LShr false) (TYPE_I 32%Z) EXP_Undef (EXP_Integer 0%Z))))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test35");
                    dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_Vector 4%Z (TYPE_I 32%Z))]);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [(Name "V")];
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "b"), (INSTR_Op (OP_ExtractElement ((TYPE_Vector 4%Z (TYPE_I 32%Z)),(EXP_Ident (ID_Local (Name "V")))) ((TYPE_I 32%Z),(EXP_Integer 4%Z)))))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test36");
                    dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [(Name "V")];
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "b"), (INSTR_Op (OP_ExtractElement ((TYPE_Vector 4%Z (TYPE_I 32%Z)),EXP_Undef) ((TYPE_I 32%Z),(EXP_Ident (ID_Local (Name "V")))))))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test37");
                    dc_type := (TYPE_Function (TYPE_I 32%Z) []);
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
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (UDiv false) (TYPE_I 32%Z) EXP_Undef EXP_Undef)))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test38");
                    dc_type := (TYPE_Function (TYPE_I 32%Z) [(TYPE_I 32%Z)]);
                    dc_param_attrs := ([], []);
                    dc_linkage := None;
                    dc_visibility := None;
                    dc_dll_storage := None;
                    dc_cconv := None;
                    dc_attrs := [];
                    dc_section := None;
                    dc_align := None;
                    dc_gc := None|};
  df_args := [(Name "a")];
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (UDiv false) (TYPE_I 32%Z) (EXP_Ident (ID_Local (Name "a"))) EXP_Undef)))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                  blk_comments := None
                |}]
                |}; 
TLE_Definition {|
  df_prototype := {|dc_name := (Name "test39");
                    dc_type := (TYPE_Function (TYPE_I 32%Z) []);
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
  df_instrs := [
                {|
                  blk_id := (Anon 0%Z);
                  blk_phis := [];
                  blk_code := [(IId (Name "b"), (INSTR_Op (OP_IBinop (UDiv false) (TYPE_I 32%Z) (EXP_Integer 0%Z) EXP_Undef)))];
                  blk_term := (IVoid 0%Z, TERM_Ret ((TYPE_I 32%Z), (EXP_Ident (ID_Local (Name "b")))));
                  blk_comments := None
                |}]
                |}].
