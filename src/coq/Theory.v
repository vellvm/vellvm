(* Re-export of most of the general meta-theory established on the syntax and semantics of vir.
   Use `From Vellvm Require Import Theory.` to get most of the theory in scope.
 *)
 
 From Vellvm Require Export
     Theory.ExpLemmas
     Theory.InstrLemmas
     Theory.DenotationTheory
     Theory.InterpreterCFG
     Theory.InterpreterMCFG
     Theory.SymbolicInterpreter
     Syntax.ScopeTheory.

