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


Ltac compute_eqv_dec :=
  match goal with
  | h:(?b1 <> ?b2) |-
      context[if Eqv.eqv_dec_p ?b1 ?b2 then true else false]
    => rewrite <- eqb_bid_neq, eqv_dec_p_eq in h ; setoid_rewrite h
  | h:(?b1 <> ?b2) |-
      context[if Eqv.eqv_dec_p (endo ?b1) (endo ?b2) then true else false]
    => rewrite <- eqb_bid_neq, eqv_dec_p_eq in h ; setoid_rewrite h
  end.



(* tactics for convert_typ *)
(* repeat ( *)
(*       match goal with *)
(*       | h:context[wf_ocfg_bid _] |- _ => apply wf_ocfg_bid_convert_typ *)
(*           with (env := []) in h *)
(*       | h:context[free_in_cfg _ _] |- _ => apply free_in_convert_typ with (env := []) *)
(*           in h *)
(*       end). *)


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
  rewrite eutt_eq_bind ; [reflexivity| intros; simpl].
  rewrite translate_ret.
  rewrite bind_ret_l.
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
  rewrite bind_bind.
  rewrite denote_no_phis.
  rewrite bind_ret_l.
  rewrite bind_bind.
  rewrite eutt_eq_bind ; [reflexivity| intros ; cbn].
  rewrite translate_bind.
  rewrite bind_bind.
  rewrite eutt_eq_bind ; [reflexivity| intros ; cbn].
  setoid_rewrite translate_ret.
  setoid_rewrite bind_ret_l ; reflexivity.
Qed.


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
    In inB (inputs body) -> (* can I relax this hypothesis ? *)
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
                              (b <- denote_cfg body input inB ;;
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
              FREE_IN_BODY_OUTB WF_BODY INB_IN_BODY.
  unfold denote_cfg, cfg_while_loop.
  unfold iter,Iter_Kleisli, Basics.iter, MonadIter_itree.

  (* Denotation of the 1st iteration of the loop *)
  rewrite unfold_iter.

  (* 1: jump to the input block, ie. the condition block *)
  (* 1.1: Denote the code used in order to compute the expression *)
  (* Bring the /denote code/ on the top of the right side of the equation *)
  rewrite eq_bid_refl.
  flatten_goal.
  rewrite bind_bind.

  (* Bring the /denote code/ on the top of the left side of the equation *)
  unfold denote_ocfg ; setoid_rewrite unfold_iter ; simpl.
  rewrite eqv_dec_p_refl.
  rewrite bind_bind.
  setoid_rewrite denote_block_unfold.
  unfold tfmap, TFunctor_list ; simpl ; rewrite denote_no_phis.
  rewrite bind_ret_l,bind_bind.
  rewrite eutt_eq_bind ; [reflexivity| intros ; simpl ].

  (* 1.2: Denote the terminator - branch *)
  (* 1.2.a: denote the expression *)
  (* Bring the /denote_expression/ in the top of each side of the equation *)
  repeat flatten_goal.
  rewrite 2 translate_bind ; rewrite 3 bind_bind.
  (* Some type conversion to manage *)
  unfold texp_break in Heq ; flatten_hyp Heq
  ; rewrite typ_to_dtyp_pair in Heq ; rewrite Heq in Heq0
  ; inv Heq0 ; clear Heq.
  rewrite eutt_eq_bind ; [reflexivity|intros ; simpl].

  (* 1.2.b: concretize or pick *)
  rewrite translate_bind ; rewrite 2 bind_bind.
  rewrite eutt_eq_bind ; [reflexivity| intros ; simpl].

  (* 1.3: destruct the value:
     - if it isn't a boolean value, raise an exception
     - if it is a boolean value, jump to the correct block
   *)
  destruct u1 ;
    try (rewrite exp_to_instr_raise) ;
    try (rewrite exp_to_instr_raiseUB).
  (* TODO: temporarely, admit the exception cases *)
  (* NOTE all raise should have the same proof - same with raiseUB but using the
     lemmas for raiseUB instead of those for raise *)
  all: match goal with
       | |- context[_ <- raise _ ;; _] => admit
       | |- context[_ <- raiseUB _ ;; _] => admit
       | |- _ => idtac
       end.

  (* 1.4: destruct the boolean value:
     - if the condition is true, jump into the body
     - if the condition is false, jump into the output block
   *)
  - destruct (Int1.eq x Int1.one) eqn:E.
    + (* the condition is true *)
      rewrite translate_ret ; rewrite 2 bind_ret_l
      ; rewrite bind_bind ; rewrite tau_eutt.

      (* 2: jump in body, entering by the block inB *)
      (* 2.0: on the left side, we are iterating on the whole ocfg,
              thus we have to ignore the block /input/ *)
      setoid_rewrite unfold_iter.
      compute_eqv_dec.
      (* 2.1: jump to /inB/, which is is the cfg /body/ -->
        maybe this hypothesis can be relaxed *)
      rewrite bind_bind.
      (* on both sides, the denotation of the block is the same *)
      rewrite eutt_eq_bind ; [| intro ; simpl].

      * (* There is some work in order to show that the denotation of
         the block inB is the same:
         On the left side, we have the cfg /body (+) outB/
         since in the right side, we have only /body/ *)

        (* TODO clean up this part of the proof *)
        (* 2.1.a: jump in block inB in the right side *)
        apply find_block_in_inputs in INB_IN_BODY
        ; destruct INB_IN_BODY as [inBk HinB].
        assert (HinB': find_block body inB = Some inBk) by assumption.
        apply find_block_some_conv in HinB.
        destruct (find_block (conv body) inB) eqn:HinBody
        ; unfold conv,ConvertTyp_list,block_id,tfmap,TFunctor_list',
          tfmap,TFunctor_block,tfmap,endo,Endo_id in HinB, HinBody
        ; rewrite HinBody in HinB
        ; clear HinBody
        ; inv HinB.

        (* 2.1.b: jump in block inB in the left side *)
        pose proof
             (find_block_app_l_wf
                 inB (b:= (conv inBk)) (conv body)
                 (conv [{| blk_id := outB;
                            blk_phis := [];
                            blk_code := [];
                            blk_term := TERM_Br_1 input;
                            blk_comments := None |}])).
        rewrite <- (convert_typ_list_app body _) in H.
        rewrite find_block_some_conv with (bk := inBk) in H ;
          [|assumption].
        unfold conv,ConvertTyp_list,block_id,tfmap,TFunctor_list',
          tfmap,TFunctor_block,tfmap,endo,Endo_id in H.
        unfold ConvertTyp_list, tfmap, TFunctor_list',tfmap,TFunctor_block at 1.
        unfold tfmap, endo, Endo_id.
        rewrite H ; try reflexivity.
        { (* easy because outB is free in body *)
           apply wf_ocfg_bid_convert_typ.
           unfold wf_ocfg_bid.
           rewrite inputs_app ; simpl.
           apply Coqlib.list_norepet_append
           ; [assumption | now apply List_norepet_singleton| ].
           apply Coqlib.list_disjoint_cons_r
           ; [now apply Util.list_disjoint_nil_r|assumption].
        }
      (* now, we have the same denotation of the block in both sides *)

      * (* since we have denoted inB, we have to continue the denotation of the body *)
        simpl.
        (* u1 = denotation of one iteration of the body entering by inB *)
        destruct u1.
      ** (* inl - continue to iterates in the body *) admit.
      ** (* inr - stop the iteration and leave the denotation of the body *)
        admit.

    + (* the condition is false *)
      (* 5: jump into the block output, which is fresh *)
      (* 5.1: in the right side, directly jumps out of the iteration *)
      rewrite bind_ret_l.

      (* 5.2: in the left side, iter again on the whole cfg *)
      rewrite translate_ret ; rewrite 2 bind_ret_l ; rewrite tau_eutt.
      rewrite unfold_iter.
      (* 5.2.a: ignore the block input *)
      compute_eqv_dec.
      (* 5.3: by contradiction, suppose that output is in body
                or output = outB *)
      flatten_goal.
      * (* contradiction *)
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

        { apply find_block_app_wf
          ; [| now rewrite <- (convert_typ_list_app body _ [])].
          unfold wf_ocfg_bid in *.
          rewrite inputs_app.
          rewrite convert_typ_inputs ; simpl.
          unfold endo, Endo_id.
          apply Coqlib.list_norepet_append ; try assumption.
          now apply List_norepet_singleton.
          apply Coqlib.list_disjoint_cons_r ; [| assumption].
          apply Util.list_disjoint_nil_r.
        }
        destruct contra as [contra | contra].
        ** (* 5.3.a : suppose that it exists a block named output in body *)
          match goal with
           | h:context[free_in_cfg body output] |- _ =>
               apply find_block_free_id in h
           end.
           find_block_conv.
           now setoid_rewrite FREE_IN_BODY_OUTPUT in contra.
        ** (* 5.3.b : suppose that output = outB *)
          simpl in *.
           now match goal with
               | h:context[output <> outB] |- _ =>
                   rewrite <- eqb_bid_neq , eq_bid_comm in h
                   ; rewrite eqv_dec_p_eq in h
                   ; setoid_rewrite h in contra
               end.
      * (* 5.4: ignore the body *)
        rewrite bind_ret_l. reflexivity.
Admitted.
