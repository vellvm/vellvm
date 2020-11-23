(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2018 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

(* begin hide *)
From Coq Require Import
     Morphisms ZArith List String Lia
     FSets.FMapAVL
     Structures.OrderedTypeEx
     micromega.Lia
     Psatz.

From ITree Require Import
     ITree
     Basics.Basics
     Events.Exception
     Eq.Eq
     Events.StateFacts
     Events.State.

Import Basics.Basics.Monads.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Programming.Eqv
     Data.String.

From Vellvm Require Import
     Numeric.Coqlib
     Numeric.Integers
     Numeric.Floats
     Utils.Tactics
     Utils.Util
     Utils.Error
     Syntax.LLVMAst
     Syntax.DynamicTypes
     Semantics.DynamicValues
     Semantics.Denotation
     Semantics.MemoryAddress
     Semantics.LLVMEvents.

Require Import Ceres.Ceres.

Import MonadNotation.
Import EqvNotation.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.
(* end hide *)

(** * Memory Model

    This file implements VIR's memory model as an handler for the [MemoryE] family of events.
    The model is inspired by CompCert's memory model, but differs in that it maintains two
    representation of the memory, a logical one and a low-level one.
    Pointers (type signature [MemoryAddress.ADDRESS]) are implemented as a pair containing
    an address and an offset.
*)

(** ** Type of pointers
    Implementation of the notion of pointer used: an address and an offset.
 *)
Module Addr : MemoryAddress.ADDRESS with Definition addr := (Z * Z) % type.
  Definition addr := (Z * Z) % type.
  Definition null := (0, 0).
  Definition t := addr.
  Lemma eq_dec : forall (a b : addr), {a = b} + {a <> b}.
  Proof.
    intros [a1 a2] [b1 b2].
    destruct (a1 ~=? b1);
      destruct (a2 ~=? b2); unfold eqv in *; unfold AstLib.eqv_int in *; subst.
    - left; reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
  Qed.
End Addr.

(** ** Memory model
    Implementation of the memory model, i.e. a handler for [MemoryE].
    The memory itself, [memory], is a finite map (using the standard library's AVLs)
    indexed on [Z].
 *)
Module Make(LLVMEvents: LLVM_INTERACTIONS(Addr)).
  Import LLVMEvents.
  Import DV.
  Open Scope list.

  Definition addr := Addr.addr.

  Module IM := FMapAVL.Make(Coq.Structures.OrderedTypeEx.Z_as_OT).

  (** ** Finite maps
      We use finite maps in several place of the memory model. We rely on the AVL implementation from the standard library.
      We redefine locally the operations we use and their axiomatisation as the interface exposed by the standard library
      tends to leak out the [Raw] underlying implementation, and feels overall tedious to use.
   *)
  Section Map_Operations.

    (* Polymorphic type of maps indexed by [Z] *)
    Definition IntMap := IM.t.

    Definition add {a} k (v:a) := IM.add k v.
    Definition delete {a} k (m:IntMap a) := IM.remove k m.
    Definition member {a} k (m:IntMap a) := IM.mem k m.
    Definition lookup {a} k (m:IntMap a) := IM.find k m.
    Definition empty {a} := @IM.empty a.

    (* We use two notions of equivalence of maps depending on the type of objects stored.
       When we can get away with Leibniz's equality over the return type, we simply use
       [Equal] that implements extensional equality (and equality of domains).
       When the domain of value itself has a non-trivial notion of equivalence, we use [Equiv]
       which relax functional equivalence up-to this relation.
     *)
    Definition Equal {a} : IntMap a -> IntMap a -> Prop :=
      fun m m' => forall k, lookup k m = lookup k m'.
    Definition Equiv {a} (R : a -> a -> Prop) : IntMap a -> IntMap a -> Prop :=
      fun m m' =>
        (forall k, member k m <-> member k m') /\
        (forall k e e', lookup k m = Some e -> lookup k m' = Some e' -> R e e').

    (* Extends the map with a list of pairs key/value.
     Note: additions start from the end of the list, so in case of duplicate
     keys, the binding in the front will shadow though in the back.
     *)
    Fixpoint add_all {a} ks (m:IntMap a) :=
      match ks with
      | [] => m
      | (k,v) :: tl => add k v (add_all tl m)
      end.

    (* Extends the map with the bindings {(i,v_1) .. (i+n-1, v_n)} for [vs ::= v_1..v_n] *)
    Fixpoint add_all_index {a} vs (i:Z) (m:IntMap a) :=
      match vs with
      | [] => m
      | v :: tl => add i v (add_all_index tl (i+1) m)
      end.

    Fixpoint Zseq (start : Z) (len : nat) : list Z :=
      match len with
      | O => []
      | S x => start :: Zseq (Z.succ start) x
      end.

    (* Give back a list of values from [|i|] to [|i| + |sz| - 1] in [m].
     Uses [def] as the default value if a lookup failed.
     *)
    Definition lookup_all_index {a} (i:Z) (sz:Z) (m:IntMap a) (def:a) : list a :=
      List.map (fun x =>
                  match lookup x m with
                  | None => def
                  | Some val => val
                  end) (Zseq i (Z.to_nat sz)).

    (* Takes the join of two maps, favoring the first one over the intersection of their domains *)
    Definition union {a} (m1 : IntMap a) (m2 : IntMap a)
      := IM.map2 (fun mx my =>
                    match mx with | Some x => Some x | None => my end) m1 m2.

    (* TODO : Move the three following functions *)
    Fixpoint max_default (l:list Z) (x:Z) :=
      match l with
      | [] => x
      | h :: tl =>
        max_default tl (if h >? x then h else x)
      end.

    Definition maximumBy {A} (leq : A -> A -> bool) (def : A) (l : list A) : A :=
      fold_left (fun a b => if leq a b then b else a) l def.

    Definition maximumBy_Z_le_def :
      forall def l e,
        e <=? def ->
        e <=? maximumBy Z.leb def l.
    Proof.
      intros def l.
      revert def.
      induction l; intros def e LE.
      - cbn; auto.
      - cbn. destruct (def <=? a) eqn:Hdef.
        + apply IHl.
          eapply Zle_bool_trans; eauto.
        + apply IHl; auto.
    Qed.

    Definition maximumBy_Z_def :
      forall def l,
        def <=? maximumBy Z.leb def l.
    Proof.
      intros def l.
      apply maximumBy_Z_le_def; eauto.
      apply Z.leb_refl.
    Qed.

    Definition maximumBy_Z_correct :
      forall def (l : list Z),
        forall a, In a l -> Z.leb a (maximumBy Z.leb def l).
    Proof.
      intros def l.
      revert def.
      induction l as [|x xs];
        intros def a IN;
        inversion IN.
      - subst; cbn.
        apply maximumBy_Z_le_def.
        destruct (def <=? a) eqn:LE.
        + apply Z.leb_refl.
        + rewrite Z.leb_gt in LE.
          apply Z.leb_le.
          lia.
      - subst; cbn; apply IHxs; auto.
    Qed.

    Definition is_some {A} (o : option A) :=
      match o with
      | Some x => true
      | None => false
      end.

  End Map_Operations.

End Make.
