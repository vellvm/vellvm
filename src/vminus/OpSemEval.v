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

(** *** Small-step, executable operational semantics *)

Fixpoint step (g : Cfg.t) (s : state) : err state :=
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
    | Some n => inr (mkst (Memory.update mem addr n) (incr_pc pc) loc pc ploc)
    | None => inl "cannot evaluate address to store to"%string
    end
  | None => inl "no instruction fetched"%string
  end.

End MakeEval.