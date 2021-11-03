(** Semantic *)
From Coq Require Import
     String
     List.
Import ListNotations.

From ExtLib Require Import Structures.Monads.
(* From ExtLib Require Import Data.Monads.EitherMonad. *)
Import MonadNotation.



From ITree Require Import
     ITree
     ITreeFacts
     Eq.
Import ITreeNotations.

From Vellvm Require Import
     Semantics
     Syntax
     ScopeTheory
     Theory
     DenotationTheory
     Tactics
     SymbolicInterpreter.


From Imp2Vir Require Import CFGC_Utils CFGC_Combinators.

Notation code := (code typ).
Notation ocfg := (ocfg typ).
Notation conv := (convert_typ []).
Notation texp := (texp typ).
Definition denote_cfg g from to := denote_ocfg (conv g) (from,to).


(** Tactics *)
Lemma denote_void_block : forall bid target src com,
    denote_block
       {|
          blk_id := bid;
           blk_phis := [];
           blk_code := [];
           blk_term := TERM_Br_1 target;
           blk_comments := com |} src
       ≈ Ret (inl target).
Proof.
  intros.
  rewrite denote_block_unfold.
  rewrite denote_no_phis.
  setoid_rewrite denote_code_nil.
  setoid_rewrite translate_ret.
  repeat (rewrite bind_ret_l).
  reflexivity.
Qed.

Lemma denote_void_block_conv : forall bid target src com,
    denote_block
       (conv {| blk_id := bid;
                 blk_phis := [];
                 blk_code := [];
                 blk_term := TERM_Br_1 target;
                 blk_comments := com |}) src
       ≈ Ret (inl target).
Proof.
  intros.
  unfold conv.
  unfold ConvertTyp_block.
  unfold tfmap, TFunctor_block.
  simpl.
  unfold tfmap, TFunctor_list.
  simpl.
  unfold endo, Endo_id.
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
      ; try (rewrite bind_ret_l)
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
             ; try (rewrite bind_bind)
             ; try (rewrite bind_ret_l)
  end.

(* tactics for convert_typ *)
(* repeat ( *)
(*       match goal with *)
(*       | h:context[wf_ocfg_bid _] |- _ => apply wf_ocfg_bid_convert_typ *)
(*           with (env := []) in h *)
(*       | h:context[free_in_cfg _ _] |- _ => apply free_in_convert_typ with (env := []) *)
(*           in h *)
(*       end). *)



Lemma find_block_some_conv :
  forall g bid bk,
    find_block g bid = Some bk <->
    find_block (conv g) bid = Some (conv bk).
Proof.
  intros.
  assert ( Hconv: blk_id (conv bk) = blk_id bk ) by apply blk_id_convert_typ.
Admitted.

Lemma find_block_none_conv :
  forall g bid,
    find_block g bid = None <->
    find_block (conv g) bid = None.
Proof.
  intros.
Admitted.


Lemma no_reentrance_conv :
  forall g1 g2,
    no_reentrance g1 g2 <-> no_reentrance (conv g1) (conv g2).
Proof.
  intros.
  unfold no_reentrance.
  now rewrite convert_typ_outputs, convert_typ_inputs.
Qed.

Lemma no_duplicate_bid_conv :
  forall g1 g2,
    no_duplicate_bid g1 g2 <-> no_duplicate_bid (conv g1) (conv g2).
Proof.
  intros.
  unfold no_duplicate_bid.
  now rewrite 2 convert_typ_inputs.
Qed.

Lemma independent_flows_conv :
  forall g1 g2,
    independent_flows g1 g2 <-> independent_flows (conv g1) (conv g2).
Proof.
  intros.
  unfold independent_flows.
  rewrite <- 2 no_reentrance_conv.
  now rewrite no_duplicate_bid_conv.
Qed.



(** Denotation Combinators *)


Lemma denote_cfg_block : forall (c : code) (input output : block_id) from,
    input <> output -> (* TODO should be a WF property of block *)
    eutt eq
         (denote_cfg (cfg_block c input output) from input)
         (denote_code (conv c) ;; ret (inl (input,output))).
Proof.
  intros.
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
  rewrite bind_ret_l.
  rewrite eutt_eq_bind ; [reflexivity|].
  intros; simpl.
  rewrite translate_ret.
  rewrite bind_ret_l.
  rewrite denote_ocfg_unfold_not_in.
  2: { now apply find_block_none_singleton. }
  reflexivity.
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
  rewrite denote_ocfg_unfold_in.
  2: { simpl ; now rewrite eqv_dec_p_refl. }
  setoid_rewrite denote_block_unfold.
  simpl.
  rewrite bind_bind.
  rewrite denote_no_phis.
  rewrite bind_ret_l.
  rewrite bind_bind.
  rewrite eutt_eq_bind ; [reflexivity|].
  intros ; cbn.
  rewrite translate_bind.
  rewrite bind_bind.
  unfold tfmap,TFunctor_texp in Heq.
  inv Heq.
  rewrite eutt_eq_bind ; [reflexivity|].
  intros ; cbn.
  setoid_rewrite translate_ret.
  setoid_rewrite bind_ret_l ; reflexivity.
Qed.
Ltac find_block_conv :=
  match goal with
  | h:context[ find_block _ _ = None ] |- _ =>
      apply find_block_none_conv in h
  | h:context[ find_block _ _ = Some _ ] |- _ =>
      apply find_block_some_conv in h
  end.


Lemma denote_cfg_branch :
  forall (cond : texp) (gT gF : ocfg) (input inT inF from input : block_id),
    input <> inT ->
    input <> inF ->
    free_in_cfg gF inT ->
    free_in_cfg gT inF ->
    independent_flows gT gF ->
    ~ In input (outputs gT) ->
    ~ In input (outputs gF) ->
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
  intros.
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
                 blk_id := input0;
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
  repeat (rewrite bind_ret_l).
  (* unfold texp_break in Heq ; flatten_hyp Heq ; inv Heq. *)
  flatten_all.
  flatten_all.
  unfold texp_break in Heq0.
  flatten_all.
  unfold tfmap,TFunctor_texp in Heq.
  unfold conv in Heq0.
  unfold ConvertTyp_exp in Heq0.
  rewrite Heq in Heq0.
  inv Heq0. clear Heq.
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
    ; rewrite translate_ret
    ; rewrite bind_ret_l
    ; unfold endo, Endo_id
    ; step_singleton_not_in
    ; rewrite bind_ret_l
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
        rewrite bind_ret_l.
        rewrite denote_ocfg_unfold_not_in ;
          [| now apply find_block_free_id, free_in_convert_typ].
        rewrite denote_ocfg_unfold_not_in ; [| assumption].
        reflexivity.
    + (* Side inF *)
      rewrite denote_ocfg_unfold_not_in;
        [| now apply find_block_free_id, free_in_convert_typ ].
      now rewrite bind_ret_l.
Qed.


Lemma denote_cfg_join : forall (g : ocfg) (output out1 out2 : block_id) from to,
    free_in_cfg g output ->
    output <> out1 ->
    output <> out2 ->
    eutt eq
         (denote_cfg (cfg_join g output out1 out2) from to)
         (d <- denote_cfg g from to ;;
          match d with
          | inr dv => ret (inr dv)
          | inl (src,target) =>
              if (eq_bid target out1)
              then ret (inl (out1, output))
              else if (eq_bid target out2)
                   then ret (inl (out2, output))
                   else ret (inl (src,target))
          end).
Proof.
  intros.
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
    wf_ocfg_bid g1 ->
    wf_ocfg_bid g2 ->
    no_duplicate_bid g1 g2 ->
    no_reentrance g1 g2 ->
    free_in_cfg g1 out1 -> (* cfg_seq cannot create a new block with an existing ID *)
    free_in_cfg g2 out1 -> (* cfg_seq cannot create a new block with an existing ID *)
    free_in_cfg g1 in2 -> (* in2 should be an input of g2, not g1 *)
    ~ In out1 (outputs g2) ->
    out1 <> in2 -> (* cfg_seq cannot create a new block with an existing ID *)
    In to (inputs g1) ->
    eutt eq
         (denote_cfg (cfg_seq g1 g2 out1 in2) from to)
         (d <- denote_cfg g1 from to ;;
          match d with
          | inr dv => ret (inr dv)
          | inl (src, target) =>
              if eq_bid target out1
              then denote_cfg g2 out1 in2
              else denote_cfg g2 src target
          end).
Proof.
  intros.
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
      ; now fold (free_in_cfg g1 in2).}
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
    assert (Heqb : eq_bid out1 out1 = true) by (now apply eqb_bid_eq) ;
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



(* NOTE I'll probably need additional WF hypothesis *)
Lemma denote_cfg_while_loop :
  forall expr_code cond body input inB output outB from,
    input <> output ->
    input <> inB ->
    input <> outB ->
    output <> inB ->
    output <> outB ->
    free_in_cfg body input ->
    free_in_cfg body output ->
    free_in_cfg body outB ->
    wf_ocfg_bid body ->
    eutt eq
         (denote_cfg (cfg_while_loop expr_code cond body input inB output outB)
                     from input)
         (iter (C:= Kleisli _)
               (fun '(from,to) =>
                   if eq_bid to input
                   then
                      (* if to = input, denote the block of condition *)
                      (let (dt,e) := texp_break cond in
                       denote_code (conv expr_code) ;;
                       dv <- translate exp_to_instr
                                      (uv <-  (denote_exp (Some dt) e) ;;
                                       concretize_or_pick uv True) ;;
                       match dv with
                       | DVALUE_I1 comparison_bit =>
                           if equ comparison_bit Int1.one
                           then
                              (* enter in the body *)
                              (b <- denote_cfg body from to ;;
                               (* if the target is outB,
                                  iter again and jump into the cond_block *)
                               match b with
                               | inr dv => Ret (inr (inr dv))
                               | inl (src, target) =>
                                   if eq_bid outB target
                                   then Ret (inl (outB,input))
                                   else Ret (inr (inl (src,target)))
                               end)
                           else Ret (inr (inl (input, output)))
                       | DVALUE_Poison => raiseUB "Branching on poison."
                       | _ => raise "Br got non-bool value"
                       end)
                  (* if to <> input, identity *)
                   else Ret (inr ( inl (from,to)))
               ) (from,input)).

Proof.
  intros * NEQ_INPUT_OUTPUT
              NEQ_INPUT_INB NEQ_INPUT_OUTB NEQ_OUTPUT_INB
              NEQ_OUTPUT_OUTB FREE_IN_BODY_INPUT FREE_IN_BODY_OUTPUT
              FREE_IN_BODY_OUTB WF_BODY .
  unfold denote_cfg.
  unfold cfg_while_loop.
  unfold iter,Iter_Kleisli, Basics.iter, MonadIter_itree.
  rewrite unfold_iter.
  rewrite eq_bid_refl.
  flatten_goal.
  rewrite bind_bind.
  unfold denote_ocfg.
  setoid_rewrite unfold_iter.
  simpl.
  rewrite eqv_dec_p_refl.
  rewrite bind_bind.
  setoid_rewrite denote_block_unfold.
  simpl.
  unfold tfmap, TFunctor_list ; simpl.
  rewrite denote_no_phis, bind_ret_l.
  repeat (rewrite bind_bind).
  rewrite eutt_eq_bind ; [reflexivity|].
  intros ; simpl.
  repeat flatten_goal.
  unfold endo, Endo_id.
  repeat (rewrite translate_bind).
  repeat (rewrite bind_bind).
  unfold texp_break in Heq.
  flatten_all.
  unfold TFunctor_texp in Heq0.
  unfold conv,ConvertTyp_exp in Heq.
  rewrite Heq in Heq0 ; clear Heq ; inv Heq0.
  rewrite eutt_eq_bind ; [reflexivity|].
  intros ; simpl.
  repeat (rewrite translate_bind).
  repeat (rewrite bind_bind).
  rewrite eutt_eq_bind ; [reflexivity|].
  intros ; simpl.
  repeat (rewrite bind_bind).
  simpl.
  destruct u1 ;
    try (rewrite exp_to_instr_raise) ;
    try (rewrite exp_to_instr_raiseUB).
    all: match goal with
    | |- context[_ <- raise _ ;; _] => admit
    | |- context[_ <- raiseUB _ ;; _] => admit
    | |- _ => idtac
    end.
  (* NOTE all raise should have the same proof - same with raiseUB but using the
     lemmas for raiseUB instead of those for raise *)
  - destruct (Int1.eq x Int1.one) eqn:E.
    + (* the condition is true *)
      rewrite translate_ret.
      repeat (rewrite bind_ret_l).
      repeat (rewrite bind_bind).
      rewrite tau_eutt.
      setoid_rewrite unfold_iter.
      match goal with
      | h:context[input <> inB] |- _ =>
          rewrite <- eqb_bid_neq,eqv_dec_p_eq in h ; setoid_rewrite h
      end.
      rewrite bind_bind.
      apply free_in_convert_typ with (env:= []), find_block_free_id in
        FREE_IN_BODY_INPUT.
      setoid_rewrite FREE_IN_BODY_INPUT.
      repeat (rewrite bind_ret_l).
      rewrite <- eqb_bid_neq, eq_bid_comm in NEQ_INPUT_OUTB ;
        setoid_rewrite NEQ_INPUT_OUTB.
      repeat (rewrite bind_ret_l).

      admit.
    + (* the condition is false *)
      rewrite translate_ret.
      repeat (rewrite bind_ret_l).
      repeat (rewrite bind_bind).
      rewrite tau_eutt.
      rewrite unfold_iter.
      (* TODO i can probably have a tactics which do that automatically,
      ie find the right hypothesis and transform it automatically *)
      match goal with
      | h:context[input <> output] |- _ =>
          rewrite <- eqb_bid_neq,eqv_dec_p_eq in h ; setoid_rewrite h
      end.

      (* rewrite convert_typ_list_app. *)
      (* rewrite find_block_none_app *)
      flatten_goal.
      * (* contradiction => Heq is False *)
        assert ( contra:
                 (find_block (conv body) output = Some b )
                 \/ (find_block
                       (conv [{| blk_id := outB;
                                  blk_phis := [];
                                  blk_code := [];
                                  blk_term := TERM_Br_1 input;
                                  blk_comments := None
                              |}]) output = Some b)
               ).

        { apply find_block_app_wf ; [| now rewrite <- (convert_typ_list_app body _ [])].
          unfold wf_ocfg_bid in *.
          rewrite inputs_app.
          rewrite convert_typ_inputs ; simpl.
          unfold endo, Endo_id.
          apply Coqlib.list_norepet_append ; try assumption.
          now apply List_norepet_singleton.
          apply Coqlib.list_disjoint_cons_r ; [| assumption].
          apply Util.list_disjoint_nil_r.
        }
        rewrite bind_bind.
        destruct contra as [contra | contra].
        ** match goal with
           | h:context[free_in_cfg body output] |- _ =>
               apply find_block_free_id in h
           end.
           find_block_conv.
           now setoid_rewrite FREE_IN_BODY_OUTPUT in contra.
        ** simpl in *.
           now match goal with
               | h:context[output <> outB] |- _ =>
                   rewrite <- eqb_bid_neq , eq_bid_comm in h
                   ; rewrite eqv_dec_p_eq in h
                   ; setoid_rewrite h in contra
               end.
      * rewrite bind_ret_l. reflexivity.
Admitted.
