(** Testing show instances for Vellvm. Currently the show instances
    seem to be causing stack overflows for larger programs. *)
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

From QuickChick Require Import QuickChick.
From Vellvm Require Import
  ShowAST
  ReprAST
  GenAST
  TopLevel
  LLVMAst
  DynamicValues
  QCVellvm.


Definition gen_PROG : GenLLVM PROG
  := fmap Prog gen_llvm.

Extraction Blacklist String List Char Core Z Format.

Extract Constant defNumTests    => "100".
Extract Constant defSize    => "15".
QCInclude "./ml/*".
QCInclude "./ml/libvellvm/*".

Extract Inlined Constant Error.failwith => "(fun _ -> raise)".
QuickChick (forAll (run_GenLLVM gen_PROG) vellvm_agrees_with_clang).
