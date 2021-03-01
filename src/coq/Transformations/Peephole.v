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

(** Note : I'm toying with the concepts and trying to get familiar with everything.
    Once things are a bit settled, we need to use a more efficient implementation of
    sets ([MSetRBT.v] for instance)
 *)
Import ListSet.
Lemma raw_id_eq_dec : forall (x y : raw_id), {x = y} + {x <> y}.
Proof.
  intros. destruct (Eqv.eqv_dec_p x y); auto.
Qed.
Infix "+++" := (set_union raw_id_eq_dec) (right associativity, at level 60).
Infix ":::" := (set_add raw_id_eq_dec) (right associativity, at level 60).
Infix "∖"    := (set_diff raw_id_eq_dec) (right associativity, at level 60).
Notation "∅" := (empty_set _).

Definition set_flat_map {A} (f:A -> set raw_id) :=
  fix flat_map (l:set A) : set raw_id :=
    match l with
    | nil => nil
    | cons x t => (f x)+++(flat_map t)
    end.

Section Liveness.

  Section Defs.

    (** * Definition sites
      Simple static collection of all variables assigned to in a piece of syntax.
     *)
    Class Defs (A : Type) := { defs: A -> set raw_id }.

    Global Instance code_defs {T} : Defs (code T) :=
      {| defs := fold_right (fun '(id,_) acc =>
                               match id with
                               | IId id => id ::: acc
                               | _ => acc
                               end) ∅ |}.

    Global Instance block_defs {T} : Defs (block T) :=
      {| defs := fun bk => map fst bk.(blk_phis) +++ defs bk.(blk_code) |}.

    Global Instance ocfg_defs {T} : Defs (ocfg T) :=
      {| defs := set_flat_map defs |}.

    Global Instance cfg_defs {T} : Defs (cfg T) :=
      {| defs := fun cfg => defs cfg.(blks) |}.

  End Defs.

  Section Uses.

    (** * Use sites
      Simple static collection of all local variables read in a piece of syntax.
     *)
    
    Class Uses (A : Type) := { uses: A -> set raw_id }.

    Global Instance ident_uses : Uses ident :=
      {| uses := fun id => match id with | ID_Local id => [id] | ID_Global _ => ∅ end |}.

    Global Instance exp_uses {T} : Uses (exp T) :=
      {| uses :=
           fix f e := match e with
                      | EXP_Ident id
                        => uses id

                      | EXP_Integer _
                      | EXP_Float _ 
                      | EXP_Double _
                      | EXP_Hex _
                      | EXP_Bool _
                      | EXP_Null 
                      | EXP_Zero_initializer 
                      | EXP_Cstring _
                      | EXP_Undef
                        => []

                      | OP_Conversion _ _ e _
                      | OP_ExtractValue (_,e) _
                      | OP_Freeze (_,e)
                        => f e

                      | OP_IBinop _ _ e1 e2
                      | OP_ICmp _ _ e1 e2
                      | OP_FBinop _ _ _ e1 e2
                      | OP_FCmp _ _ e1 e2 
                      | OP_ExtractElement (_,e1) (_,e2)
                      | OP_InsertValue (_,e1) (_,e2) _
                        => f e1 +++ f e2

                      | OP_InsertElement (_,e1) (_,e2) (_,e3)
                      | OP_ShuffleVector (_,e1) (_,e2) (_,e3)
                      | OP_Select (_,e1) (_,e2) (_,e3)
                        => f e1 +++ f e2 +++ f e3
                            
                      | EXP_Struct l
                      | EXP_Packed_struct l
                      | EXP_Array l 
                      | EXP_Vector l
                        => set_flat_map (fun x => f (snd x)) l

                      | OP_GetElementPtr _ (_,e) l
                        => f e +++ set_flat_map (fun x => f (snd x)) l
                      end
      |}.

    Global Instance texp_uses {T} : Uses (texp T) := {| uses := fun x => uses (snd x) |}.
    Global Instance option_uses {T} `{Uses T} : Uses (option T) := {| uses := fun x => match x with | Some e => uses e | None => ∅ end |}.

    Global Instance instr_uses {T} : Uses (instr T) :=
      {| uses := fun i => match i with
                       | INSTR_Op e => uses e
                       | INSTR_Call e l => uses e +++ set_flat_map uses l
                       | INSTR_Alloca _ e _ 
                       | INSTR_Load _ _ e _ 
                         => uses e
                       | INSTR_Store _ e1 e2 _
                         => uses e1 +++ uses e2
                       | INSTR_Fence
                       | INSTR_AtomicCmpXchg
                       | INSTR_AtomicRMW
                       | INSTR_VAArg
                       | INSTR_LandingPad
                       | INSTR_Comment _
                         => []
                       end
      |}.

    Global Instance code_uses {T} : Uses (code T) :=
      {| uses := set_flat_map (fun x => uses (snd x)) |}.

    Global Instance term_uses {T} : Uses (terminator T) :=
      {| uses := fun t => match t with
                       | TERM_Ret e 
                       | TERM_Br e _ _ 
                       | TERM_IndirectBr e _
                       | TERM_Resume e
                         => uses e

                       | TERM_Switch e _ l =>
                         uses e +++ set_flat_map (fun x => uses (fst x)) l

                       | TERM_Ret_void
                       | TERM_Br_1 _
                       | TERM_Unreachable
                         => []

                       | TERM_Invoke _ l _ _ =>
                         set_flat_map uses l
                       end
      |}.

    Global Instance phi_uses {T} : Uses (phi T) :=
      {| uses := fun '(Phi _ l) => set_flat_map (fun x => uses (snd x)) l |}.

    Global Instance block_uses {T} : Uses (block T) :=
      {| uses := fun bk => set_flat_map (fun x => uses (snd x)) bk.(blk_phis) +++ uses bk.(blk_code) +++ uses bk.(blk_term) |}.

    Global Instance ocfg_uses {T} : Uses (ocfg T) :=
      {| uses := set_flat_map uses |}.

    Global Instance cfg_uses {T} : Uses (cfg T) :=
      {| uses := fun cfg => cfg.(args) +++ uses cfg.(blks) |}.

  End Uses.

  Section UpwardExposed.

    (** * Upward exposed
        A use site is said to be upward exposed if its def site is not in the
        same block, i.e. if the live range of the used variable escapes the block
        of the use site.
     *)
    (* Note: this definition is quite naive, it doesn't consider the relative position
       within the block of the def and use sites considered.
       I believe that it's correct in SSA form, but should be triple checked.
     *)

    Definition upward_exposed {T} (bk : block T) : set raw_id :=
      uses bk ∖ defs bk.

  End UpwardExposed.

  (** * Liveness
      Data-flow approach, we compute for each block the [LiveIn] set of live variables when entering the block,
      and [LiveOut] set of live variables when entering a successor of the block.
      These sets can be characterized by the following set of recursive equations:
      LiveIn bk  ≡ defs bk.(blk_phis) +++ upward_exposed bk +++ (LiveOut bk ∖ defs bk)
      LiveOut bk ≡ (set_flat_map (fun bk' => LiveIn bk' ∖ defs bk'.(blk_phis)) (bk_outputs bk)) +++ uses bk.(blk_phis)
      In SSA form, the fixpoint can be directly computed in two passses over the CFG.
   *)



End Liveness.


Section PeepholeCorrect.

  Variable opt : peephole_optimization.

  (* Lemma peephole_cfg_correct : *)
  (*   (forall (c : code dtyp), eutt eq (denote_code c) (denote_code (opt c))) -> *)
  (*   forall (G : cfg dtyp), eutt eq (denote_cfg G) (denote_cfg (peephole_cfg opt G)). *)
  (* Proof. *)

End PeepholeCorrect.
