(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import Vellvm.Classes Vellvm.Util.
Require Import Program Classical.
Require Import paco.
Require Import ITree.

Set Implicit Arguments.
Set Contextual Implicit.


Instance functor_M {E} : Functor (M E) := (@mapM E).
Instance monad_M {E} : (@Monad (M E)) (@mapM E) := { mret X x := Ret x; mbind := @bindM E }.



