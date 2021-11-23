(** Semantic *)
From Coq Require Import
     String
     List.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.EitherMonad.

From ITree Require Import
     ITree
     ITreeFacts
     Eq.

From Vellvm Require Import
     Semantics
     Syntax
     ScopeTheory
     Theory
     DenotationTheory
     Tactics
     SymbolicInterpreter.

Require Import Utils.PostConditions.
Require Import Paco.paco.

From Imp2Vir Require Import CFGC_Utils CFGC_Combinators Imp.

Section CFGC_DenotationCombinators.
Import ListNotations.
Import MonadNotation.
Import ITreeNotations.
Import SemNotations.
Import DenoteTactics.

Notation code := (code typ).
Notation ocfg := (ocfg typ).
Notation conv := (convert_typ []).
Notation texp := (texp typ).
Definition denote_cfg g from to := denote_ocfg (conv g) (from,to).


(** Tactics *)
(** Hidden tactics *)
(** Hide iter body *)
Variant hidden_iter  (T: Type) : Type := boxh_iter (t: T).
Variant visible_iter (T: Type) : Type := boxv_iter (t: T).
Ltac hide_iter_body :=
  match goal with
  | |- context[ITree.iter ?g] =>
      let VG := fresh "VBODY" in
      let G := fresh "BODY" in
      remember g as G eqn:VG
      ; apply boxh_iter in VG
  | h: context[ITree.iter ?g] |- _ =>
      let VG := fresh "VBODY" in
      let G := fresh "BODY" in
      remember g as G eqn:VG
      ; apply boxh_iter in VG
  end.
Notation "'hidden_iter' G" := (hidden_iter (G = _)) (only printing, at level 10).

Ltac show_iter_body :=
  match goal with
  | h: hidden_iter _ |- _ =>
      let EQ := fresh "HBODY" in
      destruct h as [EQ];
apply boxv_iter in EQ
  end.

Ltac unhide_iter :=
  match goal with
  | h: hidden_iter (?body = _) |- _ =>
      destruct h ; subst body
  | h: visible_iter (?body = _) |- _ =>
      destruct h ; subst body
  end.

(** Hide block *)
Variant hidden_blk  (T: Type) : Type := boxh_blk (t: T).
Variant visible_blk (T: Type) : Type := boxv_blk (t: T).

Ltac hide_blk bid :=
  match goal with
  | h: context[
            {| blk_id := bid;
             blk_phis := ?phis;
             blk_code := ?code;
             blk_term := ?term;
             blk_comments := ?comm |}
         ] |- _ =>
      let Vblk := fresh "Vblk" in
      let blk := fresh "blk" in
      remember  {| blk_id := bid;
                 blk_phis := phis;
                 blk_code := code;
                 blk_term := term;
                 blk_comments := comm |} as blk eqn:Vblk
      ; apply boxh_blk in Vblk
  | |- context[
           {| blk_id := bid;
            blk_phis := ?phis;
            blk_code := ?code;
            blk_term := ?term;
            blk_comments := ?comm |}
        ] =>
      let Vblk := fresh "Vblk" in
      let blk := fresh "blk" in
      remember  {| blk_id := bid;
                 blk_phis := phis;
                 blk_code := code;
                 blk_term := term;
                 blk_comments := comm |} as blk eqn:Vblk
      ; apply boxh_blk in Vblk

  end.
Notation "'hidden_blk' blk" := (hidden_blk (blk = _)) (only printing, at level 10).

Ltac show_blk bid :=
  match goal with
  | h: hidden_blk ( _ = {| blk_id := bid;
                         blk_phis := _;
                         blk_code := _;
                         blk_term := _;
                         blk_comments := _ |}) |- _ =>
      let EQ := fresh "Hblk" in
      destruct h as [EQ];
apply boxv_blk in EQ
  end.

Ltac unhide_blk bid :=
  try (
  match goal with
  | h: hidden_blk ( ?blk = {| blk_id := bid;
                            blk_phis := _;
                            blk_code := _;
                            blk_term := _;
                            blk_comments := _ |}) |- _  =>
      destruct h ; subst blk
  | h: visible_blk ( ?blk = {| blk_id := bid;
                             blk_phis := _;
                             blk_code := _;
                             blk_term := _;
                             blk_comments := _ |}) |- _  =>
      destruct h ; subst blk
  end ).

Ltac refold_ocfg :=
        match goal with
        | |- context G[iter (fun '(bid_from, bid_src) =>
                           match find_block ?g bid_src with
                           | _ => _
                           end)] =>
            let G' := context G[(denote_ocfg g)] in
            (change G')
        | |- context G[ITree.iter (fun '(bid_from, bid_src) =>
                           match find_block ?g bid_src with
                           | _ => _
                           end)] =>
            let G' := context G[(denote_ocfg g)] in
            (change G')
        end.

(** Bind and translate rewritings *)
Hint Rewrite @bind_ret_l : rwbind.
Hint Rewrite @bind_bind : rwbind.
Hint Rewrite @translate_ret : rwtranslate.
Hint Rewrite @translate_bind : rwtranslate.
Hint Rewrite @translate_trigger : rwtranslate.

Ltac bstep := autorewrite with rwbind.
Ltac tstep := autorewrite with rwtranslate.
Ltac go := autorewrite with rwtranslate rwbind.

(* Unfold `CategoryOps.iter` from into `ITree.iter` *)
Ltac unfold_iter_cat :=
  try (unfold iter,Iter_Kleisli, Basics.iter , MonadIter_itree in * ).

(** Denotations tactics *)
Ltac conv_block :=
  try (unfold conv,ConvertTyp_block)
  ; try (unfold tfmap, TFunctor_list, TFunctor_block ; simpl )
  ; try (unfold tfmap, TFunctor_list ; simpl )
  ; try (unfold endo, Endo_id).

Lemma denote_code_nil :
  ⟦ [] ⟧c ≅ Ret tt.
Proof.
  intros.
  cbn.
  go.
  reflexivity.
Qed.

Lemma denote_void_block : forall bid target src com,
    denote_block
       {|
          blk_id := bid;
           blk_phis := [];
           blk_code := [];
           blk_term := TERM_Br_1 target;
           blk_comments := com |} src
       ≅ Ret (inl target).
Proof.
  intros.
  rewrite denote_block_unfold_eq_itree.
  rewrite denote_no_phis_eq_itree.
  setoid_rewrite denote_code_nil_eq_itree.
  simpl.
  go.
  reflexivity.
Qed.

Lemma denote_void_block_conv : forall bid target src com,
    denote_block
       (conv {| blk_id := bid;
                 blk_phis := [];
                 blk_code := [];
                 blk_term := TERM_Br_1 target;
                 blk_comments := com |}) src
       ≅ Ret (inl target).
Proof.
  intros.
  conv_block.
  now apply denote_void_block.
Qed.

Lemma denote_ocfg_singleton_not_in :
  forall bid phis code term comm from to,
    bid <> to ->
    denote_ocfg
       (conv
           [{| blk_id := bid;
                blk_phis := phis;
                blk_code := code;
                blk_term := term;
                blk_comments := comm
            |}]) (from, to) ≈ Ret (inl (from,to)).
Proof.
  intros.
  rewrite denote_ocfg_unfold_not_in.
  reflexivity.
  now apply find_block_none_singleton.
Qed.

Ltac step_singleton_not_in :=
  match goal with
  | h:context[ ?b1 <> ?b2 ] |-
      context[ denote_ocfg
                  (conv [{| blk_id := ?b1;
                          blk_phis := _;
                          blk_code := _;
                          blk_term := _;
                          blk_comments := _ |}])
                  (_, ?b2)] =>
      rewrite denote_ocfg_singleton_not_in
      ; [| assumption]
  | h:context[ ?b2 <> ?b1 ] |-
      context[ denote_ocfg
                  (conv [{| blk_id := ?b1;
                          blk_phis := _;
                          blk_code := _;
                          blk_term := _;
                          blk_comments := _ |}])
                  (_, ?b2)] =>
      rewrite denote_ocfg_singleton_not_in
      ; [| now apply not_eq_sym ]
      ; try (bstep)
      ; try (reflexivity)
  end.

Ltac step_singleton_in :=
  match goal with
  |  |- context[ denote_ocfg
                   (conv [{| blk_id := ?b;
                           blk_phis := ?p;
                           blk_code := ?c;
                           blk_term := ?t;
                           blk_comments := ?comm |}])
                   (_, ?b)
         ] => rewrite denote_ocfg_unfold_in with
       (bk:= conv {| blk_id := b;
                   blk_phis := p;
                   blk_code := c;
                   blk_term := t;
                   blk_comments := comm |})
             ; [| cbn; rewrite eqv_dec_p_refl; reflexivity ]
             ; try (rewrite denote_void_block_conv)
             ; try bstep
  end.


Ltac compute_eqv_dec :=
  unfold endo,Endo_id ;
  match goal with
  | h:(?b1 <> ?b2) |-
      context[if Eqv.eqv_dec_p ?b1 ?b2 then true else false]
    => rewrite <- eqb_bid_neq, eqv_dec_p_eq in h ; setoid_rewrite h
  |  |- context[if Eqv.eqv_dec_p ?b1 ?b1 then true else false]
    => setoid_rewrite eqv_dec_p_refl
  end.


(** Denotation Combinators *)

Definition denote_cfg' (bks : ocfg) (from to : block_id) :
  eitherT (block_id*block_id) (itree instr_E) uvalue :=
  mkEitherT (denote_ocfg (conv bks) (from,to)).

(* TODO Either Monad
Definition my_seq {E} (c : block_id -> block_id -> itree E (dvalue + block_id * block_id))
  (k : block_id -> block_id -> itree E (dvalue + block_id * block_id))
  (t ;; k) f i := vob <- t f i;; match vob with | inl v => inl v | inr (b,b') => k b b' end *)


Lemma denote_cfg_block : forall (c : code) (input output : block_id) from,
    wf_block c input output->
    eutt eq
    (denote_cfg (cfg_block c input output) from input)
    (denote_code (conv c) ;; ret (inl (input,output))).
Proof.
  intros * WF_BLOCK ; unfold wf_block in WF_BLOCK.
  unfold cfg_block, denote_cfg.
  setoid_rewrite denote_ocfg_unfold_in with
    (bk := (conv
               {| blk_id := input;
                   blk_phis := [];
                   blk_code := c;
                   blk_term := TERM_Br_1 output;
                   blk_comments := None |})).
  2: { cbn ; rewrite eqv_dec_p_refl ; reflexivity. }
  setoid_rewrite denote_block_unfold_cont.
  unfold Traversal.endo, Traversal.Endo_id ; simpl.
  rewrite denote_no_phis.
  bstep.
  rewrite eutt_eq_bind ; [reflexivity| intros; simpl].
  go.
  now step_singleton_not_in.
Qed.

Lemma denote_cfg_ret : forall (c : code) (e : texp) (input : block_id) from,
    eutt eq
         (denote_cfg (cfg_ret c e input) from input)
         (let (t,e) := e in
          denote_code (conv c) ;;
          v <- translate exp_to_instr (denote_exp (Some (typ_to_dtyp [] t)) (conv e)) ;;
          ret (inr v)).
Proof.
  intros.
  unfold cfg_ret, denote_cfg.
  flatten_goal.
  step_singleton_in.
  setoid_rewrite denote_block_unfold.
  simpl.
  bstep.
  rewrite denote_no_phis.
  bstep.
  rewrite eutt_eq_bind ; [reflexivity| intros ; cbn].
  go.
  rewrite eutt_eq_bind ; [reflexivity| intros ; cbn].
  go.
  reflexivity.
Qed.


Lemma denote_cfg_branch :
  forall (cond : texp) (gT gF : ocfg) (input inT inF from : block_id),
    wf_branch cond gT gF input inT inF ->
    eutt eq
         (denote_cfg (cfg_branch cond gT gF input inT inF) from input)
         (let (dt,e) := texp_break cond in
          dv <- translate exp_to_instr (
                            uv <-  (denote_exp (Some dt) e) ;;
                            concretize_or_pick uv True) ;;
          match dv with
          | DVALUE_I1 comparison_bit =>
              if equ comparison_bit Int1.one then
                 denote_cfg gT input inT
              else
                 denote_cfg gF input inF
          | DVALUE_Poison => raiseUB "Branching on poison."
          | _ => raise "Br got non-bool value"
          end).
Proof.
  intros * WF_BRANCH
  ; unfold wf_branch in WF_BRANCH
  ; destruct WF_BRANCH as [? [? [? [? [? [? ?]]]]]].
  unfold cfg_branch, denote_cfg.
  rewrite (convert_typ_list_app _ (gT++gF) _).
  rewrite denote_ocfg_app.
  2: {
     unfold no_reentrance ; simpl.
     rewrite convert_typ_outputs.
     unfold endo, Endo_id.
     rewrite Util.list_disjoint_singleton_right.
     unfold not in *.
     intro.
     match goal with
     | h:context[In _ (outputs (_++_))] |- _ =>
         rewrite outputs_app in h ; apply in_app_or in h
     end.
     intuition.
  }
  rewrite denote_ocfg_unfold_in with
    (bk := conv {|
                 blk_id := input;
                  blk_phis := [];
                  blk_code := [];
                  blk_term := TERM_Br cond inT inF;
                  blk_comments := None
              |}).
  2: {simpl; rewrite eqv_dec_p_refl; reflexivity. }
  setoid_rewrite denote_block_unfold.
  simpl.
  rewrite denote_no_phis.
  setoid_rewrite denote_code_nil.
  bstep.
  (* unfold texp_break in Heq ; flatten_hyp Heq ; inv Heq. *)
  flatten_all.
  flatten_all.
  unfold texp_break in Heq0.
  flatten_all.
  rewrite typ_to_dtyp_pair in Heq0
  ; rewrite Heq0 in Heq
  ; inv Heq ; clear Heq0.
  setoid_rewrite translate_bind.
  repeat (rewrite bind_bind).
  rewrite eutt_eq_bind ; [reflexivity|].
  intros ; simpl.
  setoid_rewrite translate_bind.
  repeat (rewrite bind_bind).
  rewrite eutt_eq_bind ; [reflexivity|].
  intros ; simpl.
  destruct u0 eqn:U0 ;
    try (
          try (rewrite exp_to_instr_raise; unfold raise)
          ; try (rewrite exp_to_instr_raiseUB; unfold raiseUB)
          ; rewrite bind_bind
          ; rewrite eutt_eq_bind ; [reflexivity|]
          ; intros ; simpl
          ; flatten_goal ).
  assert ( no_reentrance (conv gT) (conv gF) ) by
  (now apply no_reentrance_conv, independent_flows_no_reentrance_l).
  - destruct (Int1.eq x Int1.one)
    ; go
    ; unfold endo, Endo_id
    ; step_singleton_not_in
    ; bstep
    ; rewrite convert_typ_list_app
    ; rewrite denote_ocfg_app ; try assumption.
    + (* Side inT *)
      match goal with
      | h:context[independent_flows _ _] |- _ =>
          apply independent_flows_conv in h
      end.
      assert (HinT : In inT (inputs gT) \/ ~ In inT (inputs gT))
        by (apply Classical_Prop.classic).
      destruct HinT as [ HinT | HinT ].
      * rewrite <- denote_ocfg_app ; try assumption.
        apply denote_ocfg_flow_left ; try (assumption).
        simpl ; now rewrite convert_typ_inputs.
      * apply find_block_not_in_inputs in HinT.
        find_block_conv.
        rewrite denote_ocfg_unfold_not_in ; [|assumption].
        bstep.
        rewrite denote_ocfg_unfold_not_in ;
          [| now apply find_block_free_id, free_in_convert_typ].
        rewrite denote_ocfg_unfold_not_in ; [| assumption].
        reflexivity.
    + (* Side inF *)
      rewrite denote_ocfg_unfold_not_in;
        [| now apply find_block_free_id, free_in_convert_typ ].
      now bstep.
Qed.


Lemma denote_cfg_join : forall (g : ocfg) (output out1 out2 : block_id) from to,
    wf_join g output out1 out2 ->
    eutt eq
         (denote_cfg (cfg_join g output out1 out2) from to)
         (d <- denote_cfg g from to ;;
          match d with
          | inr dv => ret (inr dv)
          | inl (src,target) =>
              if (eqb_bid target out1)
              then ret (inl (out1, output))
              else if (eqb_bid target out2)
                   then ret (inl (out2, output))
                   else ret (inl (src,target))
          end).
Proof.
  intros * WF_JOIN ;
    unfold wf_join in WF_JOIN ;
    destruct WF_JOIN as [? [? ?]].
  unfold denote_cfg.
  unfold cfg_join.
  rewrite (convert_typ_list_app g _ []).
  rewrite denote_ocfg_app.
  2: {
     apply no_reentrance_conv.
     unfold no_reentrance.
     cbn.
     repeat (apply Coqlib.list_disjoint_cons_l ; auto).
     apply Util.list_disjoint_nil_l. }
  apply eutt_eq_bind.
  intros.
  destruct u as [ (src,target) | dv ] ; [| reflexivity].
  (* the result of the denotation of g is a jump to target, coming from src *)
  rewrite convert_typ_list_app.
  rewrite denote_ocfg_app.
  2: {apply no_reentrance_conv; unfold no_reentrance; cbn;
      now apply Util.list_disjoint_singletons. }
  (* We have 3 cases: target = out1, target = out2 and neither of them *)
  flatten_goal.
  - (* Jump to out1 *)
    rewrite eqb_bid_eq in Heq ; subst.
    step_singleton_in.
    step_singleton_not_in.
    step_singleton_not_in.
  - flatten_goal.
    + (* Jump to out2 *)
      rewrite eqb_bid_eq in Heq0 ; subst.
      rewrite eqb_bid_neq in Heq.
      step_singleton_not_in.
      step_singleton_in.
      step_singleton_not_in.
    + (* Neither out1 or out2 *)
      apply eqb_bid_neq in Heq,Heq0.
      step_singleton_not_in.
      step_singleton_not_in.
Qed.




(* NOTE
- to ∈ input
- ((out1 ) ∪ (output g1)) ∩ (output g2) = ∅ *)


(* TODO can I automatize \denote_ocfg_app\ (no_reentrance_proof) *)
Lemma denote_cfg_seq : forall g1 g2 out1 in2 from to,
    wf_seq g1 g2 out1 in2 ->
    In to (inputs g1) -> (* to <> out1 ? *)
    eutt eq
         (denote_cfg (cfg_seq g1 g2 out1 in2) from to)
         (d <- denote_cfg g1 from to ;;
          match d with
          | inr dv => ret (inr dv)
          | inl (src, target) =>
              if eqb_bid target out1
              then denote_cfg g2 out1 in2
              else denote_cfg g2 src target
          end).
Proof.
  intros * WF_SEQ ENTRY_POINT
  ; unfold wf_seq in WF_SEQ
  ; destruct WF_SEQ as [? [? [? [? [? [? [? [? ?]]]]]]]].
  unfold denote_cfg.
  unfold cfg_seq.
  assert (Hdis : In to (inputs g1) \/ ~ (In to (inputs g1))) by (apply Classical_Prop.classic).
  destruct Hdis as [ Hdis | Hdis ] ; [|contradiction].
  rewrite (convert_typ_list_app g1 _ []).
  rewrite denote_ocfg_app.
  2: {apply no_reentrance_conv ; rewrite no_reentrance_app_r.
     split; auto.
     unfold no_reentrance; cbn.
      apply Util.list_disjoint_singleton_left
      ; now fold (free_in_cfg g1 in2). }
  (* denote g1 in both case *)
  rewrite eutt_eq_bind ; [simpl; reflexivity|].
  intros ; simpl.
  destruct u as [ (src,target) | dv ] eqn:U ; try (reflexivity).

  rewrite Util.list_cons_app.
  rewrite (convert_typ_list_app _ g2 []).
  rewrite denote_ocfg_app.
  2: {
     apply no_reentrance_conv.
     unfold no_reentrance; cbn.
     now apply Util.list_disjoint_singleton_right. }

  (* jump to the next block - two cases *)
  assert (Htarget : target = out1 \/ target <> out1)
    by (apply Classical_Prop.classic) ;
    destruct Htarget as [ Htarget | Htarget ].
  - (* b = out1 ; we jump to the new block which is empty *)
    subst.
    assert (Heqb : eqb_bid out1 out1 = true) by (now apply eqb_bid_eq) ;
      rewrite Heqb.
    step_singleton_in.
    (* jump to in2 - which is not out1*)
    step_singleton_not_in.
    now rewrite bind_ret_l.
  - (* b <> out1 ; we skip the empty block *)
    step_singleton_not_in.
    rewrite <- eqb_bid_neq in Htarget;  rewrite Htarget.
    reflexivity.
Qed.

Definition evaluate_conditional (c : code) (cond : texp) : itree instr_E bool :=
  denote_code (conv c) ;;
  let (dt,e) := texp_break cond in
  dv <- translate exp_to_instr (
                    uv <-  (denote_exp (Some dt) e) ;;
                    concretize_or_pick uv True) ;;
  match dv with
  | DVALUE_I1 comparison_bit =>
      if equ comparison_bit Int1.one then
         Ret true
      else
         Ret false
  | DVALUE_Poison => raiseUB "Branching on poison."
  | _ => raise "Br got non-bool value"
  end.


(* Notation "g1 '⩭' g2" := (euttG _ _ _ _ _ g1 g2) (only printing, at level 10). *)

Lemma denote_cfg_while_loop :
  forall expr_code cond body input inB output outB from,
    wf_while expr_code cond body input inB output outB ->
    (forall bfrom, denote_cfg body bfrom inB ⤳
                         (fun vob => exists bfrom, vob = inl (bfrom, outB))) ->
    eutt eq
         (denote_cfg (cfg_while_loop expr_code cond body input inB output outB)
                     from input) 
         (iter (C := Kleisli _) 
            (fun (_ : unit) =>
              b <- evaluate_conditional expr_code cond;; 
              if b : bool 
              then vob <- denote_cfg body input inB;;
                   match vob with
                   | inr v => Ret (inr (inr v))
                   | inl _ => Ret (inl tt)
                   end
              else Ret (inr (inl (input,output)))) tt).
Proof.
  intros * WF_WHILE POSTCOND_BODY
  ; unfold wf_while in WF_WHILE.
  destruct WF_WHILE as
    [NEQ_INPUT_OUTPUT
        [NEQ_INPUT_INB
            [NEQ_INPUT_OUTB
                [NEQ_OUTPUT_INB
                    [NEQ_OUTPUT_OUTB
                        [FREE_IN_BODY_INPUT
                            [FREE_IN_BODY_OUTPUT
                                [FREE_IN_BODY_OUTB
                                    [WF_BODY INB_IN_BODY]]]]]]]]].
  revert from.
  unfold denote_cfg, cfg_while_loop.
  (* For the sake of my mental-health, I hide some part of the goal *)
  hide_blk input.
  hide_blk outB.
  unfold_iter_cat.
  hide_iter_body.

  (* We proceed by co-induction *)
  einit.
  ecofix CIH.
  intros.

  (* ecofix made too much simplifications *)
  repeat (
  match goal with
  | h:context[(⟦ tfmap (typ_to_dtyp []) blk :: conv (body ++ [blk0])⟧bs )]|- _ =>
      replace
         (⟦ tfmap (typ_to_dtyp []) blk :: conv (body ++ [blk0]) ⟧bs)
      with
      (⟦ conv ([blk] ++ body ++ [blk0]) ⟧bs) in h
        by
      ltac:
  (rewrite (convert_typ_list_app _ (body++_) [])
   ; unfold conv,ConvertTyp_list
   ; now simpl)
  end).

  (* Denotation of the 1st iteration of the loop *)
  rewrite unfold_iter.
  unhide_iter ; hide_iter_body.
  bstep.

  unfold denote_ocfg ; unfold_iter_cat.
  rewrite unfold_iter.
  hide_iter_body.

  (* 1: jump to the input block, ie. the condition block *)
  (* Bring the block on the top of the left side of the equation *)
  unhide_blk input.
  simpl ; compute_eqv_dec.
  (* On the right side, evaluate the expression *)
  unfold evaluate_conditional at 1.
  conv_block.
  unfold denote_block; simpl.
  hide_blk input.

  (* 1.0 : skip the phis *)
  rewrite denote_no_phis_eq_itree.
  bstep.
  show_iter_body.

  (* 1.1: Denote the code used in order to compute the expression *)
  unfold  ConvertTyp_code at 1, tfmap at 2.
  ebind ; econstructor ; [reflexivity | intros ; simpl ; subst].

  (* 1.2: denote the expression *)
  repeat flatten_all.
  rewrite !translate_bind ; rewrite !bind_bind.
  (* manage the conversion of the expression *)
  assert (Heq1 : (d,e)=(d0,e0)) by
  ltac:(
     unfold texp_break in * ; flatten_all ;
     unfold TFunctor_texp, conv, ConvertTyp_exp,
       tfmap, Endo_id, LLVMAst.texp in * ;
     now rewrite Heq in Heq0
     ) ; inv Heq1 ; clear Heq Heq0.
  ebind ; econstructor ; [reflexivity | intros ; simpl ; subst].
  rewrite !translate_bind; rewrite !bind_bind.

  (* 1.3: concretize_or_pick *)
  ebind ; econstructor ; [reflexivity | intros ; simpl ; subst].

  (* 1.4: destruct the value of the expression *)
  flatten_all.

  (* 1.4.a: if it is not a boolean, it raises an exception ; easy *)
  all: match goal with
       | |- context[_ <- translate _ (raise _) ;; _] =>
           unfold raise
           ; rewrite translate_bind
           ; bstep ; ebind ; econstructor
           ; [now rewrite translate_trigger| intros []]
       | |- context[_ <- translate _ (raiseUB _) ;; _] =>
           unfold raiseUB
           ; rewrite translate_bind
           ; bstep ; ebind ; econstructor
           ; [now rewrite translate_trigger| intros []]
       | |- _ => idtac
       end.

  (* 1.4.b: it is a boolean *)
  - flatten_all.
    + (* 2: the condition is true - jump in body *)
      tstep ; bstep.
      show_iter_body.

      rewrite tau_euttge.
      (* some rewriting aiming to simplify  *)
      unhide_iter.
      repeat refold_ocfg.
      replace (ConvertTyp_list [] body) with (conv body) by reflexivity.

      (* 2.1 - Use denote_ocfg_prefix and prove the hypothesis *)
      (* TODO find a more elegant way to express this hypothesis *)
      pose proof ( H_APP :=
              denote_ocfg_prefix_eq_itree
                 (conv [blk]) (conv body) (conv [blk0])
                 (bks := (conv ([blk] ++ body ++ [blk0])))
                 input inB).
      match goal with
      | h:context[?x = ?y -> _ -> _] |- _=>
          assert (HeqConv : (x = y)) by
        ltac:(
           now rewrite (convert_typ_list_app _ (body++_))
           ; rewrite (convert_typ_list_app body _)
        )
      end.
      pose proof (WF_WHILE := wf_bid_cfg_while_loop
                                 expr_code cond body input inB output outB)
      ; apply wf_ocfg_bid_convert_typ with (env := []) in WF_WHILE
      ; try assumption.
      apply H_APP in HeqConv ;
        try (unfold cfg_while_loop in WF_WHILE
             ; unhide_blk input
             ; unhide_blk outB
             ; assumption).
      clear H_APP.

      unfold denote_cfg in POSTCOND_BODY ;
      specialize (POSTCOND_BODY input)
      ; rewrite has_post_post_strong in POSTCOND_BODY.

      (* 2.2 - Since InB is in body, denote only the body *)
      rewrite HeqConv.
      ebind ; econstructor.
      (* Both body are related by POSTCOND_BODY *)
      apply POSTCOND_BODY.
      intros ; simpl.
      destruct H as [-> [bfrom ->]].
      (* 2.3 - In the lefy side, jump into the block [outB] *)
      bstep.
      rewrite Util.list_cons_app.
      unfold denote_ocfg.
      unfold_iter_cat.
      rewrite unfold_iter at 1.
      rewrite (convert_typ_list_app _ (body++_)), (convert_typ_list_app body _).

      (* Find the block [outB] *)
      assert ( HoutB :
            find_block (conv [blk] ++ conv body ++ conv [blk0]) outB
            = Some (conv blk0)
         ).
      {
         unfold cfg_while_loop in WF_WHILE.
         rewrite (find_block_app_r_wf outB (conv [blk]) (conv body ++ conv [blk0]) (b:= conv blk0)).
         reflexivity.
         rewrite <- (convert_typ_list_app body _), <- (convert_typ_list_app _ (body++_)).
         now unhide_blk input ; unhide_blk outB.
         rewrite (find_block_app_r_wf
                     outB (conv body) (conv [blk0]) (b:= conv blk0)).
         reflexivity.
         rewrite (convert_typ_list_app _ (body++_)), (convert_typ_list_app body _) in WF_WHILE.
         apply (wf_ocfg_bid_app_r (conv _) ((conv body) ++ (conv _))) in WF_WHILE.
         now unhide_blk outB.
         now unhide_blk outB ; simpl ; compute_eqv_dec.
      }
      setoid_rewrite HoutB ; clear HoutB.
      clear WF_WHILE.

      (* 2.4 - denote the block outB, which is an empty *)
      unhide_blk outB.
      rewrite denote_void_block_conv.
      refold_ocfg.
      hide_blk outB.
      simpl.
      bstep.
      (* rewriting about conv *)
      match goal with
      | |- context[(⟦ tfmap (typ_to_dtyp []) blk :: (conv body) ++ (conv [blk0])⟧bs )] =>
          replace
             (⟦ tfmap (typ_to_dtyp []) blk :: (conv body) ++ (conv [blk0])⟧bs)
          with
          (⟦ conv ([blk] ++ body ++ [blk0]) ⟧bs)
          by
        ltac:
     (rewrite (convert_typ_list_app _ (body++_) []), (convert_typ_list_app body _ [])
      ; unfold conv,ConvertTyp_list
      ; now simpl)
      end.
      (* 2.5 - In the left side, jump into the block [input] :
         use the co-inductive hypothesis *)
      etau.

    + (* 3: the condition is false - jump in output *)
      (* Ignore each sub-graphs in the left side *)
      tstep ; bstep.
      rewrite tau_euttge.
      setoid_rewrite unfold_iter at 1.
      inv HBODY ; hide_iter_body.
      unhide_blk input.

      (* 3.1: ignore the block input *)
      simpl find_block at 1 ; compute_eqv_dec.

      (*3.2: ignore *)
      assert
         (Hfind: find_block (ConvertTyp_list [] (body ++ [blk0])) output = None)
        by
      ltac:
        ( unhide_blk outB
          ; apply find_block_none_conv
          ; rewrite find_block_none_app
          ; simpl
          ; rewrite <- eqb_bid_neq,eqb_bid_comm in NEQ_OUTPUT_OUTB
          ; rewrite eqv_dec_p_eq in NEQ_OUTPUT_OUTB
          ; [setoid_rewrite NEQ_OUTPUT_OUTB; reflexivity
            | apply find_block_free_id ; assumption]).
      setoid_rewrite Hfind.
      simpl ; bstep. eret.
Qed.
End CFGC_DenotationCombinators.
