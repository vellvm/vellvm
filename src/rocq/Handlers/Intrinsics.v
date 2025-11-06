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
Unset Universe Checking.
From Stdlib Require Import
     ZArith List String Morphisms.

From ExtLib Require Import
     Structures.Monads
     Programming.Eqv
     Data.String.

From CTree Require Import
     CTree
     Fold
     FoldCTree
     FoldStateT
     Eq
     SBisim.

From Vellvm Require Import
     Utils.Util
     Utils.Tactics
     Syntax.LLVMAst
     Handlers.CTreeHandler
     Semantics.LLVMEvents
     Semantics.Memory.Sizeof
     Semantics.IntrinsicsDefinitions.


Import MonadNotation.
Import EqvNotation.
Import ListNotations.

Import CategoryOps.

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
Module Make(A:MemoryAddress.ADDRESS)(IP:MemoryAddress.INTPTR)(SIZEOF:Sizeof)(LLVMIO: LLVM_INTERACTIONS(A)(IP)(SIZEOF)).

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

  Definition handle_intrinsics {E} {BR} `{FailureE -< E} `{IntrinsicE -< E} :
    IntrinsicE ~> ctree E BR :=
    (* This is a bit hacky: declarations without global names are ignored by mapping them to empty string *)
    fun X (e : IntrinsicE X) =>
      match e in IntrinsicE Y return X = Y -> ctree E BR Y with
      | (Intrinsic _ fname args) =>
          match assoc fname defs_assoc with
          | Some f => fun pf =>
                       match f args with
                       | inl msg => raise msg
                       | inr result =>
                           Ret result
                       end
          | None => fun pf => (eq_rect X (fun a => ctree E BR a) (trigger e)) (uvalue + dvalue)%type pf
          end
      end eq_refl.

  Section PARAMS.
    Variable (E F : Type -> Type).
    Variable (BR : Type -> Type).

    Context `{FailureE -< F}.
    Context `{LLVMExcE uvalue -< F}.
    Notation Eff := (E +' IntrinsicE +' F).
    Definition E_trigger : Handler E Eff BR := fun _ e => trigger e.
    Definition F_trigger : Handler F Eff BR := fun _ e => trigger e.

    Definition interp_intrinsics_h: Handler Eff Eff BR :=
      (Handler.case_ E_trigger (case_ (handle_intrinsics (BR := BR)) F_trigger)).

    Definition interp_intrinsics :
      forall R, ctree Eff BR R -> ctree Eff BR R :=
      interp interp_intrinsics_h.

    Section Structural_Lemmas.

      Lemma interp_intrinsics_bind :
        forall (R S : Type) (t : ctree Eff BR R) (k : R -> ctree _ BR S),
          (equ eq (interp_intrinsics (CTree.bind t k)) (CTree.bind (interp_intrinsics t) (fun r : R => interp_intrinsics (k r)))).
      Proof using.
        intros. apply interp_bind.
      Qed.

      Lemma interp_intrinsics_ret :
        forall (R : Type) (x: R),
          interp_intrinsics (Ret x: ctree Eff BR _) ≅ Ret x.
      Proof using.
        intros; apply interp_ret.
      Qed.

      Lemma interp_intrinsics_Guard :
        forall {R} (t: ctree Eff BR R),
          interp_intrinsics (Guard t) ≅ Guard (interp_intrinsics t).
      Proof using.
        intros.
        unfold interp_intrinsics; rewrite interp_guard; reflexivity.
      Qed.

      Lemma interp_intrinsics_vis_eqit:
        forall {X R} (e : Eff X)
          (kk : X -> ctree Eff BR R),
          interp_intrinsics (Vis e kk) ≅
          CTree.bind (interp_intrinsics_h e) (fun x : X => Guard (interp_intrinsics (kk x))).
      Proof using.
        intros.
        unfold interp_intrinsics.
        rewrite interp_vis.
        reflexivity.
      Qed.

      Lemma interp_intrinsics_vis:
        forall X R (e : Eff X)
          (kk : X -> ctree Eff BR R),
          interp_intrinsics (Vis e kk) ~
          CTree.bind (interp_intrinsics_h e) (fun x : X => interp_intrinsics (kk x)).
      Proof using.
        intros.
        rewrite interp_intrinsics_vis_eqit.
        apply sbisim_bind_eq.
        intros ?.
        apply sbisim_guard_l.
        reflexivity.
      Qed.

  Lemma interp_trigger {C L D K} {h: K ~> ctree L D} {R} `{C -< D} : forall (e : K R),
    interp h (CTree.trigger e : ctree K C R) ≅ x <- h _ e ;; Guard (Ret x).
  Proof.
    intros. rewrite unfold_interp. cbn.
    upto_bind. reflexivity. intros.
    rewrite H2.
    now rewrite interp_ret.
  Qed.
      Lemma interp_intrinsics_trigger:
        forall X (e : Eff X),
          interp_intrinsics (CTree.trigger e) ~ interp_intrinsics_h e.
      Proof using.
        intros *.
        unfold interp_intrinsics.
        rewrite interp_trigger.
        setoid_rewrite sb_guard.
        setoid_rewrite bind_ret_r.
        reflexivity.
      Qed.

      Lemma interp_intrinsics_bind_trigger_eqit:
        forall X R (e : Eff X) (kk : X -> ctree Eff BR R),
          interp_intrinsics (CTree.bind (trigger e) kk) ≅
          CTree.bind (interp_intrinsics_h e) (fun x : X => Guard (interp_intrinsics (kk x))).
      Proof using.
        intros *.
        unfold interp_intrinsics.
        rewrite bind_trigger.
        rewrite interp_vis.
        reflexivity.
      Qed.

      Lemma interp_intrinsics_bind_trigger:
        forall X R (e : Eff X) (kk : X -> ctree Eff BR R),
          interp_intrinsics (CTree.bind (trigger e) kk) ~
          CTree.bind (interp_intrinsics_h e) (fun x : X => interp_intrinsics (kk x)).
      Proof using.
        intros.
        rewrite interp_intrinsics_bind_trigger_eqit.
        apply sbisim_bind_eq.
        intros ?. rewrite sb_guard. reflexivity.
      Qed.

      #[global] Instance equ_interp_intrinsics {R} :
        Proper (equ Logic.eq ==> equ Logic.eq) (@interp_intrinsics R).
      Proof using.
        do 2 red; intros * EQ.
        unfold interp_intrinsics.
        try rewrite EQ; try reflexivity.
      Qed.

      #[global] Instance is_simple_intrinsics_h {T}  e :
        Pure.is_simple (interp_intrinsics_h (T := T) e ).
        Proof.
          unfold interp_intrinsics_h.
          destruct e.
          typeclasses eauto.
          destruct s.
          destruct i.
          - unfold handle_intrinsics. cbn.
            repeat break_inner_match_goal; typeclasses eauto.
          - typeclasses eauto.
        Qed.
      #[global] Instance sbisim_interp_intrinsics {R} :
        Proper (sbisim Logic.eq ==> sbisim Logic.eq) (@interp_intrinsics R).
      Proof using.
        do 2 red; intros * EQ.
        try rewrite EQ; try reflexivity.
      Qed.

  End Structural_Lemmas.

  End PARAMS.

End Make.
