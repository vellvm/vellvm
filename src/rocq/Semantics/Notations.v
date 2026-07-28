From Vellvm Require Import
  Semantics.Denotation
  Semantics.InterpretationStack.
  
Module SemNotations.

  Notation ℑs  := interp_mcfg.

  Notation "⟦ e 'at?' t '⟧e'"  := (denote_exp t e).
  Notation "⟦ e 'at' t '⟧e'"   := (denote_exp (Some t) e).
  Notation "⟦ e '⟧e'"          := (denote_exp None e).
  Notation "⟦ e 'at?' t '⟧e''" := (denote_exp' t e).
  Notation "⟦ e 'at' t '⟧e''"  := (denote_exp' (Some t) e).
  Notation "⟦ e '⟧e''"         := (denote_exp' None e).
  Notation "⟦ i '⟧i'"          := (denote_instr i).
  Notation "⟦ c '⟧c'"          := (denote_code c).
  Notation "⟦ t '⟧t'"          := (denote_terminator t).
  Notation "⟦ phi '⟧Φ' from"   := (denote_phi from phi) (at level 0, from at next level).
  Notation "⟦ phis '⟧Φs' from" := (denote_phis from phis) (at level 0, from at next level).
  Notation "⟦ bk '⟧b'"         := (denote_block bk).
  Notation "⟦ bks '⟧bs'"       := (denote_ocfg bks).
  Notation "⟦ f '⟧cfg'"        := (denote_cfg f).
  Notation "⟦ f '⟧f'"          := (denote_function f).

End SemNotations.
