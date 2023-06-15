From Vellvm Require Import
  DList
  Utilities
  AstLib
  Syntax
  Semantics.Memory.Sizeof
  LLVMEvents
  LLVMAst
  GenAST
  QC.Utils.

Require Import Integers.

From ExtLib.Structures Require Export
  Functor Applicative Monad Monoid.

Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Structures.Functor.

Require Import List.

Import ListNotations.
Import MonadNotation.
Import ApplicativeNotation.

From Coq Require Import
  ZArith Lia Bool.Bool.


From QuickChick Require Import QuickChick.
Import QcDefaultNotation.
Open Scope qc_scope.
Open Scope Z_scope.

Definition nat_gen_example : G nat :=
  choose (0, 10)%nat.


Print failGen.

Module Type GEN_ALIVE2 (ADDR : MemoryAddress.ADDRESS) (IP:MemoryAddress.INTPTR) (SIZEOF : Sizeof) (LLVMEvents:LLVM_INTERACTIONS(ADDR)(IP)(SIZEOF)).
  Import LLVMEvents.
  Import DV.

  Search G.
  
  Fixpoint gen_uvalue (t : typ): G uvalue :=
    match t with
    | TYPE_I i =>
        match i with
        | 1%N =>
            x <- choose (0,1);;
            returnGen (UVALUE_I1 (repr x)) 
        | 8%N =>
            x <- choose (0,2 ^ 8);;
            returnGen (UVALUE_I8 (repr x))
        | 32%N =>
            x <- choose (0, 2 ^ 32);;
            returnGen (UVALUE_I32 (repr x))
        | 64%N =>
            x <- choose (0, 2 ^ 63);;
            returnGen (UVALUE_I64 (repr x))
        | _ => returnGen UVALUE_None
        end
    | _ => returnGen UVALUE_None
    end.
  
End GEN_ALIVE2.
 
(* Extract Inlined Constant fst => "fst". *)
(* Extract Inlined Constant app => "append". *)
(* Extract Inlined Constant rev => "rev". *)
(* Extract Inlined Constant map => "map". *)
(* Extract Inlined Constant combine => "combine". *)
(* (* Extract Inlined Constant eqn => "( == )". *) *)

(* Recursive Extraction nat_gen_example. *)
