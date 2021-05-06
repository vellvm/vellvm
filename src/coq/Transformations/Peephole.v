From Coq Require Import
     Morphisms.

Require Import List.
Import ListNotations.
Require Import ZArith.

From ITree Require Import
     ITree
     Basics.Monad
     Eq.Eq.

From Vellvm Require Import
     Utils.Util
     Utils.PropT
     Utils.Tactics
     Utils.PostConditions
     Syntax.DynamicTypes
     Syntax.CFG
     Syntax.LLVMAst
     Syntax.AstLib
     Syntax.Traversal
     Syntax.Scope
     Semantics.LLVMEvents
     Semantics.InterpretationStack
     Semantics.TopLevel.

Remove Hints Eqv.EqvWF_Build : typeclass_instances.

Set Implicit Arguments.
Set Strict Implicit.

Import ListNotations.
Open Scope bool.

Section Peephole.

  (* A peephole optimization is a program transformation substituting straight code for straight code *)
  (* NOTE: I'm running the optimization _after_ conversion of dtypes so that I can avoid converting them at various level.
     In the spirit of being able to emit valid IR source code, we should however do it before. That should just be more
     tedious, TODO.
   *)
  Definition peephole_optimization := code dtyp -> code dtyp.

  (* We lift this code-local transformation to a whole VIR program transformation *)
  (* NOTE: we need to actually also lift the elementary peephole optimization only defined
     on snippets of codes being transformed to general straight code.
     It is not completely obvious to me what is the right general approach to that, especially
     granted that it must also support lifting of the correctness of the transformation.
     It is however orthogonal to the crafting of the correctness condition allowing it to be
     lifted in arbitrary context, I'll therefore come back to it later.
   *)
  Variable opt : peephole_optimization.
  Instance peephole_endo_code : Endo (code dtyp) := opt.

  Definition peephole_cfg  : Endo (cfg dtyp) := endo.
  Definition peephole_mcfg : Endo (mcfg dtyp) := endo.

End Peephole.

Section DeadCodeElim.

  (* Dead code elimination is a global optimization: it relies on liveness information.
     Interestingly, we still want to phrase its definition and correctness locally.
     We should be able to assume a pre-computed liveness oracle whose correctness can
     be phrased in isolation.
   *)
  (* Let's assume an oracle telling us if a local variable is used outside of the current block *)
  Variable dead : raw_id -> bool.

  (* We categorize instructions that cause no side effect *)
  Definition pure_instr (i : instr dtyp) : bool :=
    match i with
    | INSTR_Op _ => true
    | _ => false
    end.

  Definition dead_code_elim : peephole_optimization :=
    fix dead_code_elim c :=
      match c with
      | [] => []
      | (IId id,i)::c => if pure_instr i && dead id then dead_code_elim c else (IId id,i) :: dead_code_elim c
      | (IVoid id,i)::c => (IVoid id,i) :: dead_code_elim c
      end.

End DeadCodeElim.


Section PeepholeCorrect.

  Variable opt : peephole_optimization.

  (* Lemma peephole_cfg_correct : *)
  (*   (forall (c : code dtyp), eutt eq (denote_code c) (denote_code (opt c))) -> *)
  (*   forall (G : cfg dtyp), eutt eq (denote_cfg G) (denote_cfg (peephole_cfg opt G)). *)
  (* Proof. *)

End PeepholeCorrect.
