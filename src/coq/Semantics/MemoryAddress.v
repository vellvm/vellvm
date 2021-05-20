(* begin hide *)
Require Import OrderedType OrderedTypeEx.
(* end hide *)

(** * Signature for addresses
    The semantics is functorized by the notion of addresses manipulated by the
    memory model. This allows us to easily plug different memory models.
    This module is concretely implemented currently in [Handlers/Memory.v].
 *)
Module Type ADDRESS.
  Parameter addr : Set.
  Parameter null : addr.
  Parameter eq_dec : forall (a b : addr), {a = b} + {a <> b}.
End ADDRESS.

