(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import ExtLib.Structures.Monads.

Require Import Vellvm.LLVMIO.
Require Import Vellvm.StepSemantics.
Require Import Vellvm.Memory.

Import MonadNotation.

Module IO := LLVMIO.Make(Memory.A).
Module M := Memory.Make(IO).
Module SS := StepSemantics(Memory.A)(IO).

Import IO.
Export IO.DV.

Definition run_with_memory prog : option (Trace DV.dvalue) :=
  let scfg := Vellvm.AstLib.modul_of_toplevel_entities prog in
  mcfg <- CFG.mcfg_of_modul scfg ;;
       ret
       (M.memD M.empty
               (s <- SS.init_state mcfg "main" ;;
                  SS.step_sem mcfg (SS.Step s))).
