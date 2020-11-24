(* begin hide *)
From Coq Require Import
     List.
Import ListNotations.

From Vellvm Require Import
     Numeric.Coqlib
     Syntax.LLVMAst
     Syntax.CFG
     Syntax.TypToDtyp.
(* end hide *)

(** * Scoping
    We define through this file several functions and predicates having to do with the scope
    of VIR programs, w.r.t. both block identifiers and local variables.
    We unfortunately inherit from LLVM IR a fully named representation of variables, forcing
    on us fairly heavy sanity checks.
    - [inputs]: input labels of an [ocfg]
    - [outputs]: output labels of an [ocfg]
    - [wf_ocfg_bid]: no duplicate block identifiers


 *)

(** * Well-formedness w.r.t. block identifiers
    An [ocfg] should not admit any collisions w.r.t. to its labels.
 *)
Section OCFG_BID_OPERATIONS.

  Context {T : Type}.

  (** * inputs
     Collect the list of input labels in an open control flow graph.
     Denoting an [ocfg] starting from a label out of this static list
     always results in the identity.
   *)
  Definition inputs {t} (ocfg : @ocfg t) :=
    map blk_id ocfg.

  (** * outputs
     Collect the list of output labels in an open control flow graph.
     Denoting an [ocfg] starting from a label that belongs to its [inputs]
     will always result in a label in the static [output] list, or in a value.
   *)
  Definition terminator_outputs {t} (term : LLVMAst.terminator t) : list block_id
    := match term with
       | TERM_Ret v => []
       | TERM_Ret_void => []
       | TERM_Br v br1 br2 => [br1; br2]
       | TERM_Br_1 br => [br]
       | TERM_Switch v default_dest brs => default_dest :: map snd brs
       | TERM_IndirectBr v brs => brs
       | TERM_Resume v => []
       | TERM_Invoke fnptrval args to_label unwind_label => [to_label; unwind_label]
       end.

  Definition bk_outputs {t} (bk : block t) : list block_id :=
    terminator_outputs (snd (blk_term bk)).

  Definition outputs {t} (bks : @ocfg t) : List.list block_id
    := fold_left (fun acc bk => acc ++ bk_outputs bk) bks [].

  (* All labels in a list of blocks are distinct *)
  Definition wf_ocfg_bid {T} (bks : list (LLVMAst.block T)) :=
    list_norepet (map blk_id bks).

  (* The  *)
  Lemma wf_ocfg_bid_nil:
    forall T, wf_ocfg_bid (T := T) []. 
  Proof.
    intros; apply list_norepet_nil.
  Qed.

  Lemma wf_ocfg_bid_cons :
    forall T (b : LLVMAst.block T) bs,
      wf_ocfg_bid (b :: bs) ->
      wf_ocfg_bid bs.
  Proof.
    intros * NOREP; inv NOREP; eauto.
  Qed.

  Lemma wf_ocfg_bid_cons_not_in :
    forall T (b : LLVMAst.block T) bs,
      wf_ocfg_bid (b :: bs) ->
      not (In (blk_id b) (map blk_id bs)).
  Proof.
    intros * NOREP; inv NOREP; eauto.
  Qed.

  Lemma wf_ocfg_bid_app_r :
    forall T (bs1 bs2 : list (LLVMAst.block T)), 
      wf_ocfg_bid (bs1 ++ bs2) ->
      wf_ocfg_bid bs2.
  Proof.
    intros * NR.
    eapply list_norepet_append_right.
    unfold wf_ocfg_bid in NR.
    rewrite map_app in NR.
    eauto.
  Qed.

  Lemma wf_ocfg_bid_app_l :
    forall T (bs1 bs2 : list (LLVMAst.block T)), 
      wf_ocfg_bid (bs1 ++ bs2) ->
      wf_ocfg_bid bs1.
  Proof.
    intros * NR.
    eapply list_norepet_append_left.
    unfold wf_ocfg_bid in NR.
    rewrite map_app in NR.
    eauto.
  Qed.

  Lemma blk_id_convert_typ : forall env b,
      blk_id (convert_typ env b) = blk_id b.
  Proof.
    intros ? []; reflexivity.
  Qed.

  (* Lemma blk_id_map_convert_typ : forall env bs, *)
  (*     map blk_id (convert_typ env bs) = map blk_id bs. *)
  (* Proof. *)
  (*   induction bs as [| b bs IH]; cbn; auto. *)
  (*   f_equal; auto. *)
  (* Qed. *)

  (* Lemma wf_ocfg_bid_convert_typ : *)
  (*   forall env (bs : list (LLVMAst.block typ)), *)
  (*     wf_ocfg_bid bs -> *)
  (*     wf_ocfg_bid (convert_typ env bs). *)
  (* Proof. *)
  (*   induction bs as [| b bs IH]; intros NOREP. *)
  (*   - cbn; auto. *)
  (*   - cbn. *)
  (*     apply list_norepet_cons.  *)
  (*     + cbn. *)
  (*       apply wf_ocfg_bid_cons_not_in in NOREP. *)
  (*       rewrite blk_id_map_convert_typ; auto. *)
  (*     + eapply IH, wf_ocfg_bid_cons; eauto.  *)
  (* Qed. *)

End OCFG_BID_OPERATIONS.


