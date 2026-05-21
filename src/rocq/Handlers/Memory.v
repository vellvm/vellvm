(* begin hide *)
From Stdlib Require Import
  String
  Morphisms.

From ExtLib Require Import
  Structures.Maps
  Data.Map.FMapAList.

From ITree Require Import
  ITree
  Eq.Eqit
  Events.State
  Events.StateFacts
  Basics.MonadState.

From Vellvm Require Import
  Utilities
  Syntax
  Params
  Semantics.LLVMEvents
  Semantics.DynamicValues
  Semantics.Memory.

From QuickChick Require Import Show.


