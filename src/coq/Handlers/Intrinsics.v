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
     ZArith List String Morphisms.

From ExtLib Require Import
     Structures.Monads
     Programming.Eqv
     Data.String.

From Vellvm Require Import
     Utils.Util
     Syntax.LLVMAst
     Semantics.LLVMEvents
     Semantics.IntrinsicsDefinitions.

From Mem Require Import
  Addresses.MemoryAddress.

From LLVM_Memory Require Import
  Sizeof
  Intptr.

From ITree Require Import
     ITree
     InterpFacts
     Eq.Eqit.

Import MonadNotation.
Import EqvNotation.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.
(* end hide *)

(** * Handler for intrinsics

   LLVM _intrinsic_ functions are used like ordinary function calls, but
   they have a special interpretation.

     - any global identifier that starts with the prefix "llvm." is
       considered to be an intrinsic function

     - intrinsic functions must be delared in the global scope (to ascribe them types)

     - it is _illegal_ to take the address of an intrinsic function (they do not
       always map directly to external functions, e.g. arithmetic intrinsics may
       be lowered directly to in-lined assembly on platforms that support the
       operations natively.

   As a consequence of the above, it is possible to _statically_ determine
   that a call is an invocation of an intrinsic by looking for instructions
   of the form:
        call t @llvm._ (args...)
*)


(* (Pure) Intrinsics -------------------------------------------------------- *)

(* The intrinsics interpreter looks for Calls to intrinsics defined by its
   argument and runs their semantic function, raising an error in case of
   exception.  Unknown Calls (either to other intrinsics or external calls) are
   passed through unchanged.
*)
Module Make(A:MemoryAddress.ADDRESS)(IP:INTPTR)(SIZEOF:Sizeof)(LLVMIO: LLVM_INTERACTIONS(A)(IP)(SIZEOF)).

  Module IS := IntrinsicsDefinitions.Make(A)(IP)(SIZEOF)(LLVMIO).
  Include IS.
  Import LLVMIO.
  Import DV.


  (* Interprets Call events found in the given association list by their
     semantic functions.
   *)

  Definition defs_assoc := List.map (fun '(a,b) =>
                                  match dc_name a with
                                  | Name s => (s,b)
                                  | _ => ("",b)
                                  end
                               ) defined_intrinsics.

  Definition handle_intrinsics {E} `{FailureE -< E} `{IntrinsicE -< E} : IntrinsicE ~> itree E :=
    (* This is a bit hacky: declarations without global names are ignored by mapping them to empty string *)
    fun X (e : IntrinsicE X) =>
      match e in IntrinsicE Y return X = Y -> itree E Y with
      | (Intrinsic _ fname args) =>
          match assoc fname defs_assoc with
          | Some f => fun pf =>
                       match f args with
                       | inl msg => raise msg
                       | inr result => Ret result
                       end
          | None => fun pf => (eq_rect X (fun a => itree E a) (trigger e)) dvalue pf
          end
      end eq_refl.

  Section PARAMS.
    Variable (E F : Type -> Type).
    Context `{FailureE -< F}.
    Notation Eff := (E +' IntrinsicE +' F).

    Definition E_trigger : Handler E Eff := fun _ e => trigger e.
    Definition F_trigger : Handler F Eff := fun _ e => trigger e.

    Definition interp_intrinsics_h :=
      (case_ E_trigger (case_ handle_intrinsics F_trigger)).

    Definition interp_intrinsics :
      forall R, itree Eff R -> itree Eff R :=
      interp interp_intrinsics_h.

    Section Structural_Lemmas.

      Lemma interp_intrinsics_bind :
        forall (R S : Type) (t : itree Eff R) (k : R -> itree _ S),
          interp_intrinsics (ITree.bind t k) ≅ ITree.bind (interp_intrinsics t) (fun r : R => interp_intrinsics (k r)).
      Proof using.
        intros; apply interp_bind.
      Qed.

      Lemma interp_intrinsics_ret :
        forall (R : Type) (x: R),
          interp_intrinsics (Ret x: itree Eff _) ≅ Ret x.
      Proof using.
        intros; apply interp_ret.
      Qed.

      Lemma interp_intrinsics_Tau :
        forall {R} (t: itree Eff R),
          interp_intrinsics (Tau t) ≅ Tau (interp_intrinsics t).
      Proof using.
        intros.
        unfold interp_intrinsics; rewrite interp_tau; reflexivity.
      Qed.

      Lemma interp_intrinsics_vis_eqit:
        forall {X R} (e : Eff X)
          (kk : X -> itree Eff R),
          interp_intrinsics (Vis e kk) ≅
          ITree.bind (interp_intrinsics_h e) (fun x : X => Tau (interp_intrinsics (kk x))).
      Proof using.
        intros.
        unfold interp_intrinsics.
        rewrite interp_vis.
        reflexivity.
      Qed.

      Lemma interp_intrinsics_vis:
        forall X R (e : Eff X)
          (kk : X -> itree Eff R),
          interp_intrinsics (Vis e kk) ≈
          ITree.bind (interp_intrinsics_h e) (fun x : X => interp_intrinsics (kk x)).
      Proof using.
        intros.
        rewrite interp_intrinsics_vis_eqit.
        apply eutt_eq_bind.
        intros ?; tau_steps; reflexivity.
      Qed.

      Lemma interp_intrinsics_trigger:
        forall X (e : Eff X),
          interp_intrinsics (ITree.trigger e) ≈ interp_intrinsics_h e.
      Proof using.
        intros *.
        unfold interp_intrinsics.
        rewrite interp_trigger.
        reflexivity.
      Qed.

      Lemma interp_intrinsics_bind_trigger_eqit:
        forall X R (e : Eff X) (kk : X -> itree Eff R),
          interp_intrinsics (ITree.bind (trigger e) kk) ≅
          ITree.bind (interp_intrinsics_h e) (fun x : X => Tau (interp_intrinsics (kk x))).
      Proof using.
        intros *.
        unfold interp_intrinsics.
        rewrite bind_trigger.
        rewrite interp_vis.
        reflexivity.
      Qed.

      Lemma interp_intrinsics_bind_trigger:
        forall X R (e : Eff X) (kk : X -> itree Eff R),
          interp_intrinsics (ITree.bind (trigger e) kk) ≈
          ITree.bind (interp_intrinsics_h e) (fun x : X => interp_intrinsics (kk x)).
      Proof using.
        intros.
        rewrite interp_intrinsics_bind_trigger_eqit.
        apply eutt_eq_bind.
        intros ?; tau_steps; reflexivity.
      Qed.

      #[global] Instance eutt_interp_intrinsics {R} :
        Proper (eutt Logic.eq ==> eutt Logic.eq) (@interp_intrinsics R).
      Proof using.
        do 2 red; intros * EQ.
        unfold interp_intrinsics.
        rewrite EQ; reflexivity.
      Qed.

  End Structural_Lemmas.

  End PARAMS.

End Make.
