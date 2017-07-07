(** ** Evaluator for Vminus *)

Require Import String.
Require Import Vminus.Vminus.

(* Some monadic set-up *)

Definition err (A : Type) : Type := (string + A)%type.
Definition err_bind {A B : Type}
           (MA : err A) (f: A -> B) (MB : err B) :=
  match MA with
  | inl err => inl err
  | inr x => inr (f x)
  end.
Definition err_ret {A : Type} (a : A) : err A :=
  inr a.

Notation "'do' x <- y ; z" := (err_bind y (fun x => z)) (at level 90).

Module MakeEval (Import Cfg:CFG).

Module SS := Make Cfg. 
Import SS.


Module Evaluator.
  (** *** Small-step, executable operational semantics *)

  Fixpoint eval_step (g : Cfg.t) (s : state) : err state :=
    let 'mkst mem pc loc ppc ploc := s in
    match (fetch g pc) with
    | Some (uid, cmd_bop bop v1 v2) =>    
      let result := eval_bop loc bop v1 v2 in
      match result with
      | Some n => inr (mkst mem (incr_pc pc) (update loc uid (Some n)) ppc ploc)
      | None => inl "cannot evalute binop command"%string
      end 
    | Some (uid, cmd_phi pas) =>
      let result := eval_phi ploc (lbl_of ppc) pas in
      match result with
      | Some n => inr (mkst mem (incr_pc pc) (update loc uid (Some n)) ppc ploc)
      | None => inl "cannot evaluate phi"%string
      end
    | Some (uid, cmd_tmn tmn) =>
      let result := eval_tmn loc tmn in
      match result with
      | Some l' => inr (mkst mem (block_entry l') loc pc loc)
      | None => inl "cannot evaluate terminator"%string
      end
    | Some (uid, cmd_load addr) =>
      inr (mkst mem (incr_pc pc) (update loc uid (Some (mem addr))) ppc ploc)
    | Some (uid, cmd_store addr v) => 
      let result := eval_val loc v in
      match result with
      (* | Some n => BUG HERE
           inr (mkst (Memory.update mem addr n) (incr_pc pc) loc pc ploc) *)
      | Some n => inr (mkst (Memory.update mem addr n) (incr_pc pc) loc ppc ploc)
      | None => inl "cannot evaluate address to store to"%string
      end
    | None => inl "no instruction fetched"%string
    end.

End Evaluator.

Module EvaluatorCorrect.
  Import Evaluator.

  Ltac eval_step_with_step next_state constructor_rule
       cfg_well_formed fetched :=
    match goal with
    | H: match ?X with
         | Some _ => _
         | None => _ end = inr next_state |-
      step ?cfg ?curr_state next_state =>
      
      destruct X eqn:Heval; 
      inversion H;
      eapply constructor_rule;
      try rewrite insn_at_pc_fetch;
      try apply fetched;
      try apply cfg_well_formed;
      rewrite Heval;
      reflexivity
    | H : _ = inr next_state |-
      step ?cfg ?curr_state next_state =>
      
      inversion H;
      eapply constructor_rule;
      try rewrite insn_at_pc_fetch;
      try apply fetched;
      try apply cfg_well_formed;
      reflexivity
    end.

  Ltac cases_on_eval_step_in_goal eval_insn :=
    match goal with
    | |- match ?X with
        | Some _ => _
        | None => _ end = inr _  =>
      destruct X;
      inversion eval_insn;
      reflexivity
    end.

  Lemma evaluator_sound: forall g s s',
      wf_cfg g -> eval_step g s = inr s' -> step g s s'.
  Proof.
    intros g s s' wf_g.
    destruct s as [mem curr_pc curr_loc previous_pc previous_loc];
      simpl.
    destruct (fetch g curr_pc) as 
        [[uid [bop v1 v2 | pas | term | addr | addr v]] | ] eqn:fetched;
      intros H;
      [eval_step_with_step s' step_bop wf_g fetched |
       eval_step_with_step s' step_phi wf_g fetched |
       eval_step_with_step s' step_tmn wf_g fetched |
       eval_step_with_step s' step_load wf_g fetched |
       eval_step_with_step s' step_store wf_g fetched | idtac].
    inversion H.
  Qed.
    
  Lemma evaluator_complete: forall g s s',
      wf_cfg g -> step g s s' -> eval_step g s = inr s'.
  Proof.
    intros g s s' wf_g step_rel.
    Print step.
    inversion step_rel as
        [mem pc loc bop v1 v2 uid n ppc ploc insn_at_pc_is eval_insn_ok s_eq s'_eq |
         mem pc loc pas uid n ppc ploc insn_at_pc_is eval_insn_ok s_eq s'_eq |
         mem pc label loc term uid ppc ploc insn_at_pc_is eval_insn_ok s_eq s'_eq |
         mem pc loc uid addr ppc ploc insn_at_pc_is eval_insn_ok s'_eq |
         mem pc loc uid addr v n ppc ploc insn_at_pc_is eval_insn_ok s_eq s'_eq];
      simpl;
      destruct (fetch g pc) as [[curr_uid curr_cmd] | ] eqn:fetched; 
      rewrite insn_at_pc_fetch in insn_at_pc_is; try apply wf_g;
        rewrite insn_at_pc_is in fetched;
        inversion fetched;
        try cases_on_eval_step_in_goal eval_insn_ok.
    reflexivity.
  Qed.

  Theorem evaluator_correct: forall g s s',
      wf_cfg g -> eval_step g s = inr s' <-> step g s s'.
  Proof.
    intros g s s' wf_g; split;
      revert g s s' wf_g.
    apply evaluator_sound.
    apply evaluator_complete.
  Qed.

End EvaluatorCorrect.
    
End MakeEval.