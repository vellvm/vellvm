(* Re-export of the main notions required to define the syntax of vir programs.
   Use `From Vellvm Require Import Syntax.` to get in scope most things necessary 
   to state facts about vir's syntax.

   Note: We avoid as much as possible to import notations. You can therefore import 
   additionally the following modules:
   - `Import CFGNotations.` for notations of operations over cfgs.
   - `Import SetNotations.` for notations of sets of lables manipulated by scoping operations.
   - `Import VIR_Notations.` for the surface syntax imitating LLVM IR. 
 *)

From Vellvm Require Export
     Syntax.LLVMAst
     Syntax.CFG
     Syntax.AstLib
     Syntax.Scope
     Syntax.Traversal
     Syntax.DynamicTypes
     Syntax.TypToDtyp.


