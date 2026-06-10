(* Re-export of the main utilities used accross the development.
   Use `From Vellvm Require Import Utils.` to get most utilities in scope.

   Note: We avoid as much as possible to import notations. You can therefore import 
   additionally the following modules:
   - `Import AlistNotations.` for notations related to `alist` used to lookup blocks.
 *)

From Stdlib Require Export
  List
  String
  Lia.

From Vellvm Require Export
  Numeric.Rocqlib
  Utils.Tactics
  Utils.Assoc
  Utils.ListUtil
  Utils.IntMaps
  Utils.NMaps
  Utils.StringUtil
  Utils.BoolUtil
  Utils.OptionUtil
  Utils.RelationsUtil.

#[export] Set Implicit Arguments.
(* #[export] Set Contextual Implicit. *)

From ITree Require Export
  Basics.Monad.
From ExtLib Require Export Structures.Functor.
Export Monads.

Export ListNotations.
Export FunctorNotation.
Export MonadNotation.
#[global] Open Scope list.
#[global] Open Scope monad_scope.

