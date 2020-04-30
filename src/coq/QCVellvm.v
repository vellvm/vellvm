From Vellvm Require Import GenAST TopLevel LLVMAst.

Check TopLevelEnv.interpreter.

Definition gen_llvm :GenLLVM (list (toplevel_entity typ (list (block typ))))
  := fmap ret gen_main_tle.
