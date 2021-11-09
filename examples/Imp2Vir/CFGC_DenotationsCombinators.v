(** Semantic *)
From Coq Require Import
     String
     List.
Import ListNotations.

From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Data.Monads.EitherMonad.
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


From Imp2Vir Require Import CFGC_Utils CFGC_Combinators Imp.

Notation code := (code typ).
Notation ocfg := (ocfg typ).
Notation conv := (convert_typ []).
Notation texp := (texp typ).
Definition denote_cfg g from to := denote_ocfg (conv g) (from,to).


(** Tactics *)

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


Ltac hidden_iter_apply lemma :=
  match goal with
  | h: hidden_iter (?body = _) |- _ =>
      unhide_iter
      ; apply lemma
      ; hide_iter_body
  | h: visible_iter (?body = _) |- _ =>
      unhide_iter
      ; apply lemma
      ; hide_iter_body
  end.

Ltac hidden_iter_rewrite lemma :=
  match goal with
  | h: hidden_iter (?body = _) |- _ =>
      unhide_iter
      ; setoid_rewrite lemma
      ; hide_iter_body
  | h: visible_iter (?body = _) |- _ =>
      unhide_iter
      ; setoid_rewrite lemma
      ; hide_iter_body
  end.

Ltac hidden_iter_tactic tactic :=
  match goal with
  | h: hidden_iter (?body = _) |- _ =>
      unhide_iter
      ; tactic
      ; hide_iter_body
  | h: visible_iter (?body = _) |- _ =>
      unhide_iter
      ; tactic
      ; hide_iter_body
  end.


Variant hidden_cfg  (T: Type) : Type := boxh_cfg (t: T).
Variant visible_cfg (T: Type) : Type := boxv_cfg (t: T).
Ltac hide_cfg :=
  match goal with
  | h: context[denote_ocfg ?cfg _] |- _ =>
      remember cfg as G eqn:VG;
apply boxh_cfg in VG
  | h : visible_cfg _ |- _ =>
      let EQ := fresh "VG" in
      destruct h as [EQ];
apply boxh_cfg in EQ
  | |- context[denote_ocfg ?cfg _] =>
      remember cfg as G eqn:VG;
apply boxh_cfg in VG
  end.
Ltac show_cfg :=
  match goal with
  | h: hidden_cfg _ |- _ =>
      let EQ := fresh "HG" in
      destruct h as [EQ];
apply boxv_cfg in EQ
  end.
Notation "'hidden' G" := (hidden_cfg (G = _)) (only printing, at level 10).

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
  end.


Hint Rewrite @bind_ret_l : rwbind.
Hint Rewrite @bind_bind : rwbind.
Hint Rewrite @translate_ret : rwtranslate.
Hint Rewrite @translate_bind : rwtranslate.
Hint Rewrite @translate_trigger : rwtranslate.

Ltac bstep := autorewrite with rwbind.
Ltac tstep := autorewrite with rwtranslate.
Ltac go := autorewrite with rwtranslate rwbind.

Ltac unfold_iter_cat :=
  try (unfold iter,Iter_Kleisli, Basics.iter , MonadIter_itree in * ).

Ltac conv_block :=
  try (unfold conv,ConvertTyp_block)
  ; try (unfold tfmap, TFunctor_list, TFunctor_block ; simpl )
  ; try (unfold tfmap, TFunctor_list ; simpl )
  ; try (unfold endo, Endo_id).


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
       ≈ Ret (inl target).
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



(* tactics for convert_typ *)
(* repeat ( *)
(*       match goal with *)
(*       | h:context[wf_ocfg_bid _] |- _ => apply wf_ocfg_bid_convert_typ *)
(*           with (env := []) in h *)
(*       | h:context[free_in_cfg _ _] |- _ => apply free_in_convert_typ with (env := []) *)
(*           in h *)
(*       end). *)


(** Denotation Combinators *)

Definition denote_cfg' (bks : ocfg) (from to : block_id) :
  eitherT (block_id*block_id) (itree instr_E) uvalue :=
  mkEitherT (denote_ocfg (conv bks) (from,to)).

(* TODO Either Monad
Definition my_seq {E} (c : block_id -> block_id -> itree E (dvalue + block_id * block_id))
  (k : block_id -> block_id -> itree E (dvalue + block_id * block_id))
  (t ;; k) f i := vob <- t f i;; match vob with | inl v => inl v | inr (b,b') => k b b' end *)


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


Require Import Paco.paco.
Import SemNotations.
Require Import DenotationTheory.
Import DenoteTactics.


Lemma denote_no_phis : forall x,
    ⟦ [] ⟧Φs x ≅ Ret tt.
Proof.
  intros.
  cbn. go.
  cbn; go.
  reflexivity.
Qed.


Notation "g1 '⩭' g2" := (euttG _ _ _ _ _ g1 g2) (only printing, at level 10).
Require Import Utils.PostConditions.

(* Precondition probablement nécessaire :
    denote_cfg body input inB ⤳ (fun vob => exists bfrom, vob = inl (bfrom, inB)) *)
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
    denote_cfg body input inB ⤳ (fun vob => exists bfrom, vob = inl (bfrom, inB)) ->
    eutt eq
         (denote_cfg (cfg_while_loop expr_code cond body input inB output outB)
                     from input) 
         (iter (C := Kleisli _) 
            (fun '(from, to) => 
              b <- evaluate_conditional expr_code cond;; 
              if b : bool 
              then vob <- denote_cfg body input inB;; 
                   match vob with
                   | inr v => Ret (inr (inr v))
                   | inl b => Ret (inl b) 
                   end
              else Ret (inr (inl (input,output)))) (from, input)).

Proof.
  intros * NEQ_INPUT_OUTPUT
              NEQ_INPUT_INB NEQ_INPUT_OUTB NEQ_OUTPUT_INB
              NEQ_OUTPUT_OUTB FREE_IN_BODY_INPUT FREE_IN_BODY_OUTPUT
              FREE_IN_BODY_OUTB WF_BODY INB_IN_BODY POSTCOND_BODY.
  unfold denote_cfg, cfg_while_loop.
  (* For the sake of my mental-health, I hide some part of the goal *)
  hide_blk input.
  hide_blk outB.
  unfold_iter_cat.
  hide_iter_body.

  (* We proceed by co-induction *)
  einit.
  ecofix CIH.

  (* ecofix made too much simplifications *)
  replace
     (⟦ tfmap (typ_to_dtyp []) blk :: conv (body ++ [blk0]) ⟧bs (from, input))
    with
    (⟦ conv ([blk] ++ body ++ [blk0]) ⟧bs (from, input)) in CIHL,CIHH
      by
    ltac:
      (rewrite (convert_typ_list_app _ (body++_) [])
       ; unfold conv,ConvertTyp_list
       ; now simpl).

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
  rewrite denote_no_phis.
  bstep.

  (* 1.1: Denote the code used in order to compute the expression *)
  unfold  ConvertTyp_code at 1, tfmap at 2.
  ebind ; econstructor ; [reflexivity | intros ; simpl ; subst].

  (* 1.2: denote the expression *)
  repeat flatten_all.
  go.
  (* manage the conversion of the expression *)
  assert (Heq1 : (d,e)=(d0,e0)) by
  ltac:(
     unfold texp_break in * ; flatten_all ;
     unfold TFunctor_texp, conv, ConvertTyp_exp,
       tfmap, Endo_id, LLVMAst.texp in * ;
     now rewrite Heq in Heq0
     ) ; inv Heq1 ; clear Heq Heq0.
  ebind ; econstructor ; [reflexivity | intros ; simpl ; subst].
  go.

  (* 1.3: concretize_or_pick *)
  ebind ; econstructor ; [reflexivity | intros ; simpl ; subst].
  go.

  (* 1.4: destruct the value of the expression *)
  flatten_all ; go.

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
      go.
      rewrite tau_euttge.
      (* some rewriting aiming to simplify  *)
      unhide_iter.
      match goal with
      | |- euttG _ _ _ _ _ ?g _ =>
          replace g with
          (denote_ocfg (conv ([blk] ++ body ++ [blk0])) (input, inB))
          by
          ltac:(now unfold denote_ocfg; unfold_iter_cat)
      end.
       match goal with
      | |- euttG _ _ _ _ _ _ (_ <- ?g ;; _) =>
          replace g with
          (denote_ocfg (conv body) (input, inB))
          by
          ltac:(now unfold denote_ocfg; unfold_iter_cat)
       end.
      (* TODO explain the proof *)
      rewrite <- bind_ret_r.
      ebind ; econstructor ; [|admit].
      pose proof ( H_APP :=
              denote_ocfg_prefix
                 (bks := (conv ([blk] ++ body ++ [blk0])))
                 (conv [blk]) (conv body) (conv [blk0]) input inB
                 ).
      rewrite H_APP ;
        [| now rewrite (convert_typ_list_app _ (body++_))
           ; rewrite (convert_typ_list_app body _)
        | pose proof (WF_WHILE := wf_cfg_while_loop
                                     expr_code cond body input inB output outB)
          ; apply wf_ocfg_bid_convert_typ with (env := []) in WF_WHILE
          ; try assumption
          ; try (unfold cfg_while_loop in WF_WHILE
                 ; unhide_blk input; unhide_blk outB
                 ; apply WF_WHILE)
        ] ; clear H_APP.
      setoid_rewrite <- bind_ret_r at 4.
      (* TODO I'd like to use POSTCOND_BODY before the ebind ... *)
      apply has_post_post_strong in POSTCOND_BODY.
      (* apply POSTCOND_BODY. *)
      admit.


    + (* 3: the condition is false - jump in output *)
      (* Ignore each sub-graphs in the left side *)
      go.
      rewrite tau_euttge.
      setoid_rewrite unfold_iter at 1.
      unhide_iter ; hide_iter_body.
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
          ; rewrite <- eqb_bid_neq,eq_bid_comm in NEQ_OUTPUT_OUTB
          ; rewrite eqv_dec_p_eq in NEQ_OUTPUT_OUTB
          ; [setoid_rewrite NEQ_OUTPUT_OUTB; reflexivity
            | apply find_block_free_id ; assumption]).
      setoid_rewrite Hfind.
      simpl ; bstep. eret.
Admitted.
