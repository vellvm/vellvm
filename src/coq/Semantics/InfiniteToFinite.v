From Coq Require Import
     Relations
     String
     List
     Lia
     ZArith
     Morphisms.

Require Import Coq.Logic.ProofIrrelevance.

From Vellvm Require Import
     Semantics.InterpretationStack
     Semantics.LLVMEvents
     Semantics.Denotation
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Semantics.Lang
     Semantics.InterpretationStack
     Semantics.TopLevel
     Semantics.DynamicValues
     Semantics.LLVMParams
     Semantics.InfiniteToFinite.Conversions.BaseConversions
     Semantics.InfiniteToFinite.Conversions.DvalueConversions
     Semantics.InfiniteToFinite.Conversions.EventConversions
     Semantics.InfiniteToFinite.Conversions.TreeConversions
     Semantics.InfiniteToFinite.LangRefine
     Syntax.DynamicTypes
     Theory.TopLevelRefinements
     Theory.ContainsUB
     Utils.Error
     Utils.Monads
     Utils.MapMonadExtra
     Utils.PropT
     Utils.InterpProp
     Utils.ListUtil
     Utils.Tactics
     Utils.OOMRutt
     Utils.OOMRuttProps
     Handlers.MemoryModules.FiniteAddresses
     Handlers.MemoryModules.InfiniteAddresses
     Handlers.MemoryModelImplementation.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor.

From ITree Require Import
     ITree
     Basics
     Basics.HeterogeneousRelations
     Eq.Rutt
     Eq.RuttFacts
     Eq.Eqit
     Eq.EqAxiom.

Require Import Coq.Program.Equality.
Require Import Paco.paco.

Import InterpFacts.

Import MonadNotation.
Import ListNotations.

Notation LLVM_syntax :=
  (list (LLVMAst.toplevel_entity
              LLVMAst.typ
              (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ)))).

Infix "×" := prod_rel (at level 90, left associativity).

Module InfiniteToFinite.
  (* Import FinInfLangRefine. (* Just planning on using this for L4_convert from finite to infinite events. *) *)
  Import InfFinLangRefine.

  From Vellvm Require Import InterpreterMCFG.

  Import MCFGTheoryBigIntptr.
  Import MCFGTheory64BitIntptr.

  Module TLR_INF := TopLevelRefinementsBigIntptr.
  Module TLR_FIN := TopLevelRefinements64BitIntptr.

  Hint Resolve interp_PropT__mono : paco.

  (* TODO: Move these refine_OOM_h lemmas? *)
  Import Morphisms.

  Import TC1.

  #[local] Notation E1 := (E1.ExternalCallE +' OOME +' UBE +' DebugE +' FailureE).
  #[local] Notation E2 := (E2.ExternalCallE +' OOME +' UBE +' DebugE +' FailureE).
  #[local] Notation OOM_h := (refine_OOM_handler).

  Module InfLLVM := Vellvm.Semantics.InterpretationStack.InterpreterStackBigIntptr.LLVM.
  Module FinLLVM := Vellvm.Semantics.InterpretationStack.InterpreterStack64BitIntptr.LLVM.
  Module InfFinTC := Vellvm.Semantics.InfiniteToFinite.LangRefine.InfFinLangRefine.TC1.
  (* Module FinInfTC := Vellvm.Semantics.InfiniteToFinite.LangRefine.FinInfLangRefine.TC1. *)

  Module EC1 := InfFinTC.EC.
  (* Module EC2 := FinInfTC.EC. *)

  Module InfMem := MemoryBigIntptr.
  Module FinMem := Memory64BitIntptr.

  Module InfMemMMSP := MemoryBigIntptr.MMEP.MMSP.
  Module FinMemMMSP := Memory64BitIntptr.MMEP.MMSP.

  Module InfMemInterp := MemoryBigIntptr.MEM_SPEC_INTERP.
  Module FinMemInterp := Memory64BitIntptr.MEM_SPEC_INTERP.

  Module InfLP := InterpreterStackBigIntptr.LP.
  Module FinLP := InterpreterStack64BitIntptr.LP.

  Module EC2 := EventConvert FinLP InfLP FinToInfAddrConvert InfToFinAddrConvert FinLP.Events InfLP.Events.
  Module DVC2 := EC2.DVC.

  (* Could not put with the other conversions, need to know what memory structures like MemState are *)
  Definition convert_SByte (sb1 : MemoryBigIntptr.MP.BYTE_IMPL.SByte) : OOM (Memory64BitIntptr.MP.BYTE_IMPL.SByte).
    destruct sb1.
    refine (uv' <- EC.DVC.uvalue_convert_strict uv;;
            idx' <- EC.DVC.uvalue_convert_strict idx;;
            ret (FiniteSizeof.mkUByte LLVMParams64BitIntptr.Events.DV.uvalue uv' dt idx' sid)).
  Defined.

  Definition convert_mem_byte (mb1 : InfMemMMSP.mem_byte) : OOM (FinMemMMSP.mem_byte).
    destruct mb1.
    refine (s' <- convert_SByte s;;
            ret _).

    constructor.
    apply s'.
    apply a.
  Defined.

  (* Slightly tricky.

     Both the infinite and finite memory have the same underlying
     structure --- a map from Z to mem_bytes.

     The Z indexes in the finite memory may need to be limited to the
     range of the address type, but it may not matter because trying
     to look these up in a program should cause OOM anyway.
   *)
  Definition convert_memory (mem : InfMemMMSP.memory) : OOM (FinMemMMSP.memory).
    refine (elems <- map_monad _ (IntMaps.IM.elements mem);;
            ret (IntMaps.IP.of_list elems)).

    refine (fun '(ix, mb) =>
              mb' <- convert_mem_byte mb;;
              ret (ix, mb')).
  Defined.

  Definition convert_Frame (f : InfMemMMSP.Frame) : OOM (FinMemMMSP.Frame).
    induction f.
    - exact (ret []).
    - refine (a' <- InfToFinAddrConvert.addr_convert a;;
              f' <- IHf;;
              ret (a' :: f')).
  Defined.

  Definition convert_FrameStack (fs : InfMemMMSP.FrameStack) : OOM (FinMemMMSP.FrameStack).
    induction fs.
    - refine (f' <- convert_Frame f;;
              ret (FinMemMMSP.Singleton f')).
    - refine (f' <- convert_Frame f;;
              fs' <- IHfs;;
              ret (FinMemMMSP.Snoc fs' f')).
  Defined.

  Definition convert_Block (b : InfMemMMSP.Block) : OOM (FinMemMMSP.Block)
    := map_monad InfToFinAddrConvert.addr_convert b.

  Definition convert_Heap (h : InfMemMMSP.Heap) : OOM (FinMemMMSP.Heap).
    refine (blocks <- map_monad _ (IntMaps.IM.elements h);;
            ret (IntMaps.IP.of_list blocks)).

    refine (fun '(ix, b) =>
              b' <- convert_Block b;;
              ret (ix, b')).
  Defined.

  Definition convert_memory_stack (ms1 : InfMemMMSP.memory_stack) : OOM (FinMemMMSP.memory_stack).
    destruct ms1 as [mem fs h].
    refine (mem' <- convert_memory mem;;
            fs' <- convert_FrameStack fs;;
            h' <- convert_Heap h;;
            ret _).

    constructor; auto.
  Defined.

  Definition convert_MemState (m1 : InfMem.MMEP.MMSP.MemState) : OOM (FinMem.MMEP.MMSP.MemState).
    destruct m1 as [ms pr].
    refine (ms' <- convert_memory_stack ms;;
            ret _).

    constructor; auto.
  Defined.

  Definition MemState_refine (m1 : InfMem.MMEP.MMSP.MemState) (m2 : FinMem.MMEP.MMSP.MemState) : Prop
    := convert_MemState m1 = NoOom m2.

  Lemma MemState_refine_initial :
    MemState_refine InfMemMMSP.initial_memory_state FinMemMMSP.initial_memory_state.
  Proof.
    reflexivity.
  Qed.

  (** More refinement relations *)
  Definition L3_E1E2_orutt_strict (t1 : PropT InfLP.Events.L3 (InfMemMMSP.MemState *
                                                                 (MemPropT.store_id * (InfLLVM.Local.local_env * InfLLVM.Stack.lstack * (InfLLVM.Global.global_env * InfLP.Events.DV.dvalue))))) t2
    : Prop :=
    forall t', t2 t' ->
          exists t, t1 t /\
                 orutt
                   L3_refine_strict
                   L3_res_refine_strict
                   (MemState_refine × (eq × (local_refine_strict × stack_refine_strict × (global_refine_strict × EC.DVC.dvalue_refine_strict))))
                   t t' (OOM:=OOME).

  Definition model_E1E2_L3_orutt_strict p1 p2 :=
    L3_E1E2_orutt_strict
      (TopLevelBigIntptr.model_oom_L3 p1)
      (TopLevel64BitIntptr.model_oom_L3 p2).

  Require Import Coq.Logic.Classical_Pred_Type.

  (* Lemma blah : *)
  (*   forall {E X} (t : itree E X), *)
  (*     t ≈ ITree.spin -> *)
  (*     eq_itree eq t ITree.spin. *)
  (* Proof. *)
  (*   intros E X t H. *)
  (*   pcofix CIH. *)
  (*   pinversion H; cbn in *. *)
  (*   pstep. *)
  (* QED. *)

  Lemma test_proof1 :
    forall {E X} (t1 t2 : itree E X),
      t1 ≈ t2 ->
      ~ eq_itree eq t1 ITree.spin ->
      exists t, t1 ≈ t /\ t2 ≈ t /\ ~ eq_itree eq t1 t /\ ~ eq_itree eq t2 t.
  Proof.
    intros E X t1 t2 T1T2 NSPIN.

    (*
      - t2 is either eq_itree eq t2 (Tau t1) or not
       + If it is pick (Tau (Tau t1))
       + Else pick (Tau t1)

       These don't have to be constructed coinductively, which is
       different than below.
     *)
  Abort.

  Lemma test_proof1 :
    forall {E X} (t1 t2 : itree E X),
      t1 ≈ t2 ->
      ~ eq_itree eq t1 ITree.spin ->
      exists t, t1 ≈ t /\ t2 ≈ t /\ ~ eq_itree eq t1 t /\ ~ eq_itree eq t2 t.
  Proof.
    intros E X t1 t2 T1T2 NSPIN.
    pose proof (Classical_Prop.classic (eq_itree eq (Tau t1) t2)) as [EQTau | NEQtau].
    - exists (Tau (Tau t1)).
      split; [repeat rewrite tau_eutt; reflexivity|].
      split; [repeat rewrite tau_eutt; symmetry; auto|].
      split.
      + (* ~ t1 ≅ Tau (Tau t1) *)
        admit.
      + (* ~ t2 ≅ Tau (Tau t1) *)
        rewrite EQTau.
        (* ~ t2 ≅ Tau t2 *)
        admit.
    - exists (Tau t1).
      split.
      rewrite tau_eutt; reflexivity.
      split.
      rewrite tau_eutt. symmetry; auto.
      split.
      + (* ~ t1 ≅ Tau t1 *)
        intros CONTRA.
        pinversion CONTRA; admit.
      + intros CONTRA; apply NEQtau.
        symmetry; auto.
  Admitted.    
    (*
      - t2 is either eq_itree eq t2 (Tau t1) or not
       + If it is pick (Tau (Tau t1))
       + Else pick (Tau t1)

       These don't have to be constructed coinductively, which is
       different than below.
     *)

  CoInductive stream (T : Type) : Type :=
  | cons : T -> stream T -> stream T.

  CoInductive pstream (T : Type) : Prop :=
  | pcons : T -> pstream T -> pstream T.

  CoInductive pchoices (T : Type) : Prop :=
  | pccons : T -> pchoices T -> pchoices T
  | pctau : pchoices T -> pchoices T.

  CoInductive tchoices (T : Type) : Type :=
  | tccons : T -> tchoices T -> tchoices T
  | tctau : tchoices T -> tchoices T.

  Arguments cons {_}.
  Arguments pcons {_}.
  Arguments pccons {_}.
  Arguments pctau {_}. 
  Arguments tccons {_}.
  Arguments tctau {_}.

  Axiom pchoices_to_tchoices : forall {T}, pchoices T -> tchoices T.
  Axiom tchoices_to_pchoices : forall {T}, tchoices T -> pchoices T.

  Inductive seq_gen {T} seq : stream T -> stream T -> Prop :=
  | _seq_gen : forall (n : T) s1 s2 (R : seq s1 s2 : Prop), seq_gen seq (cons n s1) (cons n s2).
  Hint Constructors seq_gen : core.

  Definition seq' {T} (s1 s2 : stream T) := paco2 seq_gen bot2 s1 s2.
  Hint Unfold seq' : core.
  Lemma seq_gen_mon {T} : monotone2 (@seq_gen T). Proof. pmonauto. Qed.
  Hint Resolve seq_gen_mon : paco.

  CoFixpoint smap {A B} (f : A -> B) (s : stream A) : stream B :=
    match s with cons n s' => cons (f n) (smap f s') end.

  CoFixpoint szip {A B C} (f : A -> B -> C) (s1 : stream A) (s2 : stream B) : stream C :=
    match s1, s2 with
    | cons z1 s1', cons z2 s2' => cons (f z1 z2) (szip f s1' s2')
    end.

  CoFixpoint zeros : stream Z :=
    cons 0%Z zeros.

  Lemma test_proof2 :
    forall s1 s2,
      seq' s1 (smap (fun z => (0 - z)%Z) s2) ->
      seq' zeros (szip Z.add s1 s2).
  Proof.
    (* No existential... *)
  Abort.

  Lemma test_proof2 :
    forall s1 s2,
      seq' s1 s2 ->
      exists s3, seq' zeros (szip Z.add (szip Z.add s1 s2) s3).
  Proof.
    intros s1 s2 SEQ.
    (* s3 is easily constructed with s1 and s2... But closer? *)
    exists (smap (fun z => (0 - z)%Z) (szip Z.add s1 s2)).
  Abort.


  (* Maybe use something with rutt *)
  Variant IEvent : Type -> Type :=
    | iev : nat -> IEvent nat.

  Variant FEvent : Type -> Type :=
    | fev : bool -> FEvent bool.

  Definition nb (n : nat) (b : bool) : Prop :=
    (n = 1%nat /\ b = true) \/ (n = 0%nat /\ b = false).
  
  Definition event_rel (i : IEvent nat) (f : FEvent bool) : Prop
    := match i, f with
       | iev n, fev b => nb n b
       end.

  Definition event_rel_ans (i : IEvent nat) (ia : nat) (f : FEvent bool) (fa : bool) : Prop
    := match i, f with
       | iev n, fev b => nb n b /\ nb ia fa
       end.

  From ITree Require Import
    Nondeterminism.

  Definition InfE := nondetE +' IEvent +' OOME.
  Definition FinE := nondetE +' FEvent +' OOME.

  Definition nondetE_handle {E} X (e : (nondetE +' E) X) : PropT E X
    := match e with
       | inl1 e' =>
           match e' with
           | Or =>
               fun (t : itree E bool) => t = Ret true \/ t = Ret false
           end
       | inr1 e' => fun t => t ≈ @ITree.trigger E X e'
       end.

  Definition runInf {X} (t : itree InfE X) : PropT (IEvent +' OOME) X
    := interp_prop nondetE_handle eq t (OOM:=OOME).

  Definition runFin {X} (t : itree FinE X) : PropT (FEvent +' OOME) X
    := interp_prop nondetE_handle eq t (OOM:=OOME).

  Definition L1_ref {X Y} (i : InfE X) (f : FinE Y) : Prop.
    refine (match i, f with
            | inl1 i, inl1 f =>
                match i, f with
                | Or, Or =>
                    True
                end
            | inr1 (inl1 (iev n)), inr1 (inl1 (fev b)) => nb n b
            | inr1 (inr1 o1), inr1 (inr1 o2) => True
            | _, _ => False
            end).
  Defined.

  Definition L1_ref_ans {X Y} (i : InfE X) (x : X) (f : FinE Y) (y : Y) : Prop.
    refine (match i, f with
            | inl1 i, inl1 f =>
                match i, f with
                | Or, Or =>
                    _
                end
            | inr1 (inl1 (iev n)), inr1 (inl1 (fev b)) => _
            | inr1 (inr1 o1), inr1 (inr1 o2) => True
            | _, _ => False
            end).

    - inv i. inv f.
      exact (x = y).
    - inv i0. inv f0.
      exact (nb n b /\ nb H H0).
  Defined.

  Definition L2_ref {X Y} (i : (IEvent +' OOME) X) (f : (FEvent +' OOME) Y) : Prop.
    refine (match i, f with
            | inl1 (iev n), inl1 (fev b) => nb n b
            | inr1 o1, inr1 o2 => True
            | _, _ => False
            end).
  Defined.

  Definition L2_ref_ans {X Y} (i : (IEvent +' OOME) X) (x : X) (f : (FEvent +' OOME) Y) (y : Y) : Prop.
    refine (match i, f with
            | inl1 (iev n), inl1 (fev b) => _
            | inr1 o1, inr1 o2 => True
            | _, _ => False
            end).

    - inv i0. inv f0.
      exact (nb n b /\ nb H H0).
  Defined.

  Definition nondetE_handle_stream {E} X (e : (nondetE +' E) X) : Monads.stateT (stream bool) (itree E) X
    := match e with
       | inl1 e' =>
           match e' with
           | Or =>
               fun (choices : stream bool) =>
                 match choices with
                 | (cons b choices') =>
                     ret (choices', b)
                 end
           end
       | inr1 e' =>
           fun (choices : stream bool) =>
             x <- @ITree.trigger E X e';;
             ret (choices, x)
       end.

  (* Kind of sketchy because of axioms... But may work *)
  CoFixpoint apply_choices {E} : Monads.stateT (pchoices bool) (itree E) bool.
  cofix CIH.
  intros choices.
  apply pchoices_to_tchoices in choices.
  destruct choices.
  - apply ret.
    exact (tchoices_to_pchoices choices, b).
  - apply tchoices_to_pchoices in choices.
    apply go.
    apply TauF.
    apply CIH.
    apply choices.
  Defined.

    Definition nondetE_handle_pchoices {E} X (e : (nondetE +' E) X) : Monads.stateT (pchoices bool) (itree E) X
    := match e with
       | inl1 e' =>
           match e' with
           | Or => apply_choices
           end
       | inr1 e' =>
           fun (choices : pchoices bool) =>
             x <- @ITree.trigger E X e';;
             ret (choices, x)
       end.

  Definition runFinStream {X} (choices : stream bool) (t : itree FinE X) : itree (FEvent +' OOME) (stream bool * X)
    := State.interp_state nondetE_handle_stream t choices.

  Definition runFinChoiceStream {X} (choices : pchoices bool) (t : itree FinE X) : itree (FEvent +' OOME) (pchoices bool * X)
    := State.interp_state nondetE_handle_pchoices t choices.

  (* Can't refer to self in type... *)
  (* 
  CoFixpoint runFinTape {X} (t : itree FinE X) : PropT (FEvent +' OOME) (X * {tr : pchoices bool | runFinTape (runFinChoices tr t)}).
    := interp_prop nondetE_handle eq t (OOM:=OOME).

   *)
  (* Best I can do is produce the choices, and maybe I can later prove that running with those exact choices gives the right thing... *)

  (* Definition PropStateT (S : Type) (E : Type -> Type) (X : Type) : Type := *)
  (*   S -> itree E X -> S -> Prop. *)
  (*    Monads.stateT S (PropT E) X. *)

  CoInductive trace (T : Type) : Prop :=
  | trCons : T -> trace T -> trace T
  | trTau : trace T -> trace T
  | trStop : trace T.

  Arguments trCons {_}.
  Arguments trTau {_}.
  Arguments trStop {_}.

  CoFixpoint trApp {T} (t1 : trace T) (t2 : trace T) : trace T :=
    match t1 with
    | trStop => t2
    | trTau t1' => trTau (trApp t1' t2)
    | trCons a t1' => trCons a (trApp t1' t2)
    end.

  (*
  Definition nondetE_handle_tape {E} X (e : (nondetE +' E) X) : PropStateT (trace bool) E X
    := match e with
       | inl1 e' =>
           match e' with
           | Or =>
               fun prev t =>
                 (t = Ret (trApp prev (trCons true trStop), true)) \/
                 (t = Ret (trApp prev (trCons false trStop), false))
           end
       | inr1 e' =>
           fun prev t =>
             t ≈ fmap (fun x => (trTau prev, x)) (@ITree.trigger E X e')
       end.
   *)

  (* Definition runFinTape {X} (t : itree FinE X) : PropStateT (trace bool) (FEvent +' OOME) X *)
  (*   := interp_prop nondetE_handle_tape eq t (OOM:=OOME). *)

  Definition runInfStream {X} (choices : stream bool) (t : itree InfE X) : itree (IEvent +' OOME) (stream bool * X)
    := State.interp_state nondetE_handle_stream t choices.

  Definition runInfChoices {X} (choices : pchoices bool) (t : itree InfE X) : itree (IEvent +' OOME) (pchoices bool * X)
    := State.interp_state nondetE_handle_pchoices t choices.

  CoFixpoint falses : stream bool
    := cons false falses.

  CoFixpoint pfalses : pstream bool
    := pcons false pfalses.

  CoFixpoint pcfalses : pchoices bool
    := pccons false pcfalses.

  CoInductive exc {A : Type} (P : A -> Prop) : Prop :=
  | exc_intro : forall x : A, P x -> exc (A:=A) P
  | exc_tau : exc (A:=A) P -> exc (A:=A) P.

  Require Import Coq.Logic.ClassicalEpsilon.
  From Coq Require Import Description.

  (* Extract choices from runFin relation... *)
  Lemma runFin_choices :
    forall {X} (tf : itree FinE X) tf2,
      runFin tf tf2 -> pchoices bool.
  Proof.
    cofix CIH.
    intros X tf tf2 RUN.
    pinversion RUN.
    - subst.
      exact pcfalses.
    - apply pctau.
      eapply CIH; eauto.
    - apply pctau.
      eapply CIH.
      pstep.
      red.
      apply HS.
    - apply pctau.
      eapply CIH.
      pstep.
      red.
      apply HS.
    - (* Out of memory on the right... Any choices are fine *)
      exact pcfalses.
    - (* Vis events... May make a choice, or there may be no choice *)
      destruct e.
      + (* Choice! *)
        cbn in H1.
        destruct n.
        destruct H1 as [TRUE | FALSE].
        * specialize (HK true).
          forward HK.
          constructor. rewrite TRUE. reflexivity.
          pclearbot.

          apply (pccons true).
          eapply CIH. apply HK.
        * specialize (HK false).
          forward HK.
          constructor. rewrite FALSE. reflexivity.
          pclearbot.

          apply (pccons false).
          eapply CIH. apply HK.
      + (* No choice! *)
        apply pctau.
        red in H1.
        (* Not sure about the Returns part of HK...
           This is part of interp_prop and may be a little dodgy...
         *)

        destruct s.
        -- inversion f.
           subst.

           specialize (HK true).
           forward HK.
           rewrite H1.
           unfold ITree.trigger.
           eapply ReturnsVis. reflexivity.
           cbn.
           constructor.
           reflexivity.

           pclearbot.

           eapply CIH.
           eauto.
        -- (* I don't know what type A is, so it could be uninhabited,
              so I cannot call HK... BUT, fortunately, this is OOM on
              the left, which means the right must OOM as well, so
              there are no more choices to be made.
            *)
          exact pcfalses.
  Defined.

  Axiom interp_prop_inv_Type :
    forall {E F OOM : Type -> Type} {OOME : OOM -< E} (h_spec : forall T : Type, E T -> PropT F T) (R1 R2 : Type) (RR : R1 -> R2 -> Prop) (t1 : itree E R1) (t2 : itree F R2),
      @interp_prop E F OOM OOME h_spec R1 R2 RR t1 t2 ->
      ((interp_PropT_ h_spec RR true
        true (OOME:=OOME)
        (upaco2
           (interp_PropT_ h_spec RR
              true true (OOME:=OOME)) bot2) t1 t2) *

         ( (* Returns on both sides *)
           ({r1 & {r2 & RR r1 r2 * (RetF r1 = observe t1) * (RetF r2 = observe t2)}}) +
             (* Double tau *)
             ({t1' & {t2' & (paco2 (interp_PropT_ h_spec RR true true (OOME:=OOME)) bot2 t1' t2') * (TauF t1' = observe t1) * (TauF t2' = observe t2)}}) +
             (* Tau left *)
             ({t1' & {t2' &
                        (interp_PropTF (OOME:=OOME) h_spec RR true true (upaco2 (interp_PropT_ h_spec RR true true (OOME:=OOME)) bot2) (observe t1') (observe t2)) *
                          (TauF t1' = observe t1) * (t2' = observe t2)}}) +
             (* Tau right *)
             ({t1' & {t2' &
                     (interp_PropTF (OOME:=OOME) h_spec RR true true (upaco2 (interp_PropT_ h_spec RR true true (OOME:=OOME)) bot2) (observe t1) (observe t2')) *
                       (t1' = observe t1) * (TauF t2' = observe t2)}}) +
             (* OOM vis *)
             ({A & (sigT (fun (e : OOM A) => {k1 & {t1' & {t2' &
                 (t1' ≅ vis e k1) * (observe t1' = observe t1) * (t2' = observe t2)}}}))}) +
             (* Vis nodes *)
             ({A & {e & {k1 & {k2 & {ta & {t2' &
                 (forall (a : A), Returns a ta -> upaco2 (interp_PropT_ h_spec RR true true (OOME:=OOME)) bot2 (k1 a) (k2 a)) *
                   (h_spec A e ta) *
                   (t2' ≈ x <- ta;; k2 x) *
                   (VisF e k1 = observe t1) *
                   (observe t2' = observe t2)}}}}}})
         )
      )%type.

  Lemma runFin_runFinChoiceStream :
    forall {X} (tf : itree FinE X) tf2
      (RUN : runFin tf tf2),
      fmap snd (runFinChoiceStream (runFin_choices tf tf2 RUN) tf) ≈ tf2.
  Proof.
    cofix CIH.
    intros X tf tf2 RUN.
    red in RUN.
    (* apply interp_prop_inv_Type in RUN. *)
  Admitted.

  (*     stream bool. *)

  (*   runFin_choices tf *)

  (* (* Extract choices from runFin relation... *) *)
  (* Lemma runFin_choices : *)
  (*   forall {X} (tf : itree FinE X) tf2, *)
  (*     runFin tf tf2 -> stream bool. *)
  (* Proof. *)
  (*   cofix CIH. *)
  (*   intros X tf tf2 H. *)
  (*   assert (exists! s:runFin tf tf2, True) as H0 by admit. *)
  (*   Unset Printing Notations. *)
  (*   apply constructive_definite_description in H0. *)
  (*   destruct H0. *)
  (*   Unset Guard Checking. *)
  (*   assert (exists!  *)
  (*   pinversion H. *)
  (* Qed. *)

  (* Lemma fin_exists_choices : *)
  (*   forall {X} (tf : itree FinE X) tf2, *)
  (*     runFin tf tf2 -> *)
  (*     exists choices, *)
  (*       tf2 ≈ (fmap snd (runFinStream choices tf)). *)
  (* Proof. *)
  (*   intros X tf tf2 H. *)
  (*   pinversion H. *)
  (*   - exists falses. *)
  (*     rewrite itree_eta. *)
  (*     rewrite <- H2. *)
  (*     unfold runFinStream. *)
  (*     cbn. *)
  (*     rewrite StateFacts.unfold_interp_state. *)
  (*     rewrite <- H1. *)
  (*     cbn. *)
  (*     unfold ITree.map. *)
  (*     rewrite bind_ret_l. *)
  (*     cbn. *)
  (*     subst; reflexivity. *)
  (*   - red in H. *)
  (* Qed. *)

  (* Lemma fin_exists_choices : *)
  (*   forall {X} (tf : itree FinE X) tf2, *)
  (*     runFin tf tf2 -> *)
  (*     exc (fun choices => *)
  (*            tf2 ≈ (fmap snd (runFinStream choices tf))). *)
  (* Proof. *)
  (*   cofix CIH. *)
  (*   intros X tf tf2 H. *)
  (*   pinversion H. *)
  (*   - apply exc_intro with (x:=falses). *)
  (*     rewrite itree_eta. *)
  (*     rewrite <- H2. *)
  (*     unfold runFinStream. *)
  (*     cbn. *)
  (*     rewrite StateFacts.unfold_interp_state. *)
  (*     rewrite <- H1. *)
  (*     cbn. *)
  (*     unfold ITree.map. *)
  (*     rewrite bind_ret_l. *)
  (*     cbn. *)
  (*     subst; reflexivity. *)
  (*   - apply exc_tau. *)
  (*     specialize (CIH X t1 t2 HS). *)
  (*     destruct CIH. *)
  (*     apply exc_intro with (x:=x). *)

      

  (*     Guarded. *)

  (*     exists x. *)
      
  (* Qed. *)

  (* Lemma fin_exists_choices : *)
  (*   forall {X} (tf : itree FinE X) tf2, *)
  (*     runFin tf tf2 -> *)
  (*     exists choices, *)
  (*       tf2 ≈ (fmap snd (runFinStream choices tf)). *)
  (* Proof. *)
  (*   intros X tf tf2 RUN. *)
  (*   apply constructive_indefinite_description. *)
    
  (*   revert RUN. *)
  (*   cofix CIH. *)
  (*   cofix CIH. *)
  (*   pinversion RUN. *)
  (*   - exists falses. *)
  (*     pcofix CIH. *)
  (*     pstep. *)
  (*     cbn. *)
  (*     red. *)
  (*     setoid_rewrite Shallow.observe_bind. *)
  (*     rewrite <- H. *)
      
  (*     rewrite observe_bind. *)

  (*   unfold runFinStream. *)
  (*   unfold State.interp_state. *)
  (*   cbn. *)
  (*   unfold ITree.map. *)
  (*   unfold eutt. *)
  (*   unfold eqit. *)
  (*   pstep. *)
  (*   setoid_rewrite unfold_interp. *)
  (*   unfold interp. *)
  (*   cbn. *)
  (*   punfold RUN. *)
  (*   red in RUN. *)
  (*   induction RUN. *)
  (*   - subst. *)
  (*     exists falses. *)
  (*   red in RUN. *)
  (*   red in RUN. *)
  (*   red in RUN. *)
  (* Qed. *)

  Axiom orutt_inv_Type :
    forall {E1 E2 OOM : Type -> Type} {OOME : OOM -< E2}
      (R1 R2 : Type) (PRE : prerel E1 E2) (POST : postrel E1 E2) (RR : R1 -> R2 -> Prop) (t1 : itree E1 R1) (t2 : itree E2 R2),
      @orutt E1 E2 OOM OOME R1 R2 PRE POST RR t1 t2 ->
      ((orutt_ (OOME:=OOME) PRE POST RR
          (upaco2
             (orutt_ (OOME:=OOME) PRE POST RR) bot2) t1 t2) *

         ( (* Returns on both sides *)
           ({r1 & {r2 &
                    RR r1 r2 *
                      (RetF r1 = observe t1) *
                      (RetF r2 = observe t2)}}) +
             (* Double Tau *)
             ({m1 & {m2 &
                 (paco2 (orutt_ (OOME:=OOME) PRE POST RR) bot2 m1 m2) *
                   (TauF m1 = observe t1) *
                   (TauF m2 = observe t2)}}) +
             (* Vis Nodes *)
             ({A & {B & {e1 & {e2 & {k1 & {k2 &
                 (PRE A B e1 e2) *
                   (forall (a : A) (b : B),
                       POST A B e1 a e2 b ->
                       upaco2
                         (orutt_ (OOME:=OOME) PRE POST RR) bot2 (k1 a) (k2 b)) *
                   (forall (o : OOM B), e2 <> subevent B o) *
                   (VisF e1 k1 = observe t1) *
                   (VisF e2 k2 = observe t2)}}}}}}) +

             (* OOM Nodes *)
             ({A & sigT (fun (e : OOM A) =>
                           {t1' & {k2 &
                                     (t1' = observe t1) *
                                       (VisF (subevent A e) k2 = observe t2)}})}) +
             (* Tau Left *)
             ({t1' & {ot2 &
                 (oruttF (OOME:=OOME) PRE POST RR
                    (upaco2
                       (orutt_ (OOME:=OOME) PRE POST RR) bot2)
                    (observe t1') (observe t2)) *
                   (TauF t1' = observe t1) *
                   (ot2 = observe t2)}}) +

             (* Tau Right *)
             ({ot1 & {t2' &
                 (oruttF (OOME:=OOME) PRE POST RR
                    (upaco2
                       (orutt_ (OOME:=OOME) PRE POST RR) bot2)
                    (observe t1) (observe t2')) *
                   (ot1 = observe t1) *
                   (TauF t2' = observe t2)}})
               
      ))%type.

  CoInductive CoProd (X Y : Type) : Type :=
  | coprod : X -> Y -> CoProd X Y.

  CoInductive CoSig (X : Type) (P : X -> Prop) : Prop :=
  | coexist : forall (x : X), P x -> CoSig X P
  | cotau : CoSig X P -> CoSig X P.

  Axiom or_Type_inv : forall (P : Prop) (Q : Prop), (P \/ Q) -> (P + Q)%type.

  (* TODO: confirm this inversion axiom... *)
  Axiom interp_PropTF_vis_l_inv_Type :
    forall {E F OOM : Type -> Type}
      X
      (OOME : OOM -< E)
      (h : forall T : Type, E T -> PropT F T)
      (R1 R2 : Type)
      (RR : R1 -> R2 -> Prop)
      (b1 b2 : bool)
      (sim : itree E R1 -> itree F R2 -> Prop)
      (e : E X) k t',
      interp_PropTF (OOME:=OOME) h RR b1 b2 sim (VisF e k) (observe t') ->
      ({k2 & {ta &
                (forall (a : X), Returns a ta -> upaco2 (interp_PropT_ h RR b1 b2 (OOME:=OOME)) bot2 (k a) (k2 a)) *
                  (h X e ta) *
                  (t' ≈ x <- ta;; k2 x)}})%type.

  (*
    orutt spin finite ->
    finite ≈ spin \/ finite ≈ oom

    Should maybe be able to prove with classical reasoning on
    finite...

    finite ≈ spin \/ ~ finite ≈ spin
    finite ≈ oom \/ ~ finite ≈ oom

    
   *)
  Lemma get_inf_tree :
    forall ti tf,
      orutt (@L1_ref) (@L1_ref_ans) nb ti tf (OOM:=OOME) ->
      forall tf2, runFin tf tf2 ->
             itree (IEvent +' OOME) nat.
  Proof.
    intros ti tf REL tf2 RUN.
    revert RUN.
    revert REL.
    revert ti tf tf2.
    cofix CIH.
    intros ti tf tf2 REL RUN.
    apply orutt_inv_Type in REL as (REL' & REL).
    destruct REL as [[[[[RET | TAU] | VIS] | VISOOM] | TauL] | TauR].
    - (* Ret *)
      destruct RET as (r1 & r2 & (RRr1r2 & RET1) & RET2).
      apply (ret r1).
    - (* Double Tau *)
      destruct TAU as (m1 & m2 & (HS & TAU1) & TAU2).
      apply go.
      apply TauF.
      eapply CIH with (tf:=m2) (tf2:=tf2).
      apply HS.
      red; red in RUN.
      setoid_rewrite <- (tau_eutt m2).
      pstep. rewrite TAU2.
      red.
      cbn.
      punfold RUN.
    - (* Vis *)
      destruct VIS as (A & B & e1 & e2 & k1 & k2 & ((HS & NOOM) & VIS1) & VIS2).
      destruct HS as (e1e2 & ANS).
      destruct e1, e2; cbn in e1e2; try inv e1e2;
        try (repeat break_match_hyp; contradiction).
      + (* nondetE *)
        destruct n, n0.
        cbn in *.
        (* Need to know the choice made here for tf2 *)
        red in RUN.
        apply interp_prop_inv_Type in RUN as (RUN' & RUN).
        destruct RUN as [[[[[RETP | TAUP] | TAULP] | TAURP] | OOMP] | VISP].
        { destruct RETP as (r1 & r2 & (RRr1r2 & RET1) & RET2);
            setoid_rewrite <- VIS2 in RET1; inv RET1.
        }
        { destruct TAUP as (m1 & m2 & (HS & TAU1) & TAU2).
          setoid_rewrite <- VIS2 in TAU1; inv TAU1.
        }
        { destruct TAULP as (m1 & m2 & (HS & TAU1) & TAU2).
          setoid_rewrite <- VIS2 in TAU1; inv TAU1.
        }
        { (* Tau on right... *)
          destruct TAURP as (m1 & m2 & (HS & TAU1) & TAU2).
          apply go.
          apply TauF.
          eapply CIH.
          red; eauto.
          pstep; eauto.
        }
        { (* VisOOM *)
          destruct OOMP as (A & e & k1' & t1' & t2' & ((VISEQ & TF) & TF2)).
          (* Right hand side ran out of memory, so any tree will do *)
          apply (ret 0%nat).
        }
        { (* Vis events *)
          destruct VISP as (A & e & k1' & k2' & ta & t2' & ((((HS & HANDLE) & SPEC) & TF) &TF2)).
          (* tf2 was a vis node... *)
          setoid_rewrite <- VIS2 in TF.
          inv TF.
          subst_existT.
          red in HANDLE.
          apply or_Type_inv in HANDLE.
          destruct HANDLE; subst.
          - setoid_rewrite bind_ret_l in SPEC.
            apply go.
            apply TauF.

            specialize (ANS true true eq_refl).
            specialize (HS true).
            forward HS.
            constructor; reflexivity.
            pclearbot.

            eapply CIH with (tf2:=k2' true); eauto.
          - setoid_rewrite bind_ret_l in SPEC.
            apply go.
            apply TauF.

            specialize (ANS false false eq_refl).
            specialize (HS false).
            forward HS.
            constructor; reflexivity.
            pclearbot.

            eapply CIH with (tf2:=k2' false); eauto.
        }
      + (* Uninterpreted events *)
        destruct s, s0;
          repeat break_match_hyp; try contradiction.

        -- (* IEvent / FEvent *)
          cbn in *.
          specialize (ANS n b).
          forward ANS; auto.
          pclearbot.

          (*
            apply go.
            apply TauF.
            eapply CIH.
            apply ANS.
           *)

          (* Need to know stuff about continuations... *)
          red in RUN.
          apply interp_prop_inv_Type in RUN as (RUN' & RUN).
          destruct RUN as [[[[[RETP | TAUP] | TAULP] | TAURP] | OOMP] | VISP].
          { destruct RETP as (r1 & r2 & (RRr1r2 & RET1) & RET2);
              setoid_rewrite <- VIS2 in RET1; inv RET1.
          }
          { destruct TAUP as (m1 & m2 & (HS & TAU1) & TAU2).
            setoid_rewrite <- VIS2 in TAU1; inv TAU1.
          }
          { destruct TAULP as (m1 & m2 & (HS & TAU1) & TAU2).
            setoid_rewrite <- VIS2 in TAU1; inv TAU1.
          }
          { (* Tau on right... *)
            destruct TAURP as (m1 & m2 & (HS & TAU1) & TAU2).
            setoid_rewrite <- VIS2 in HS.

            apply interp_PropTF_vis_l_inv_Type in HS.
            destruct HS as (k2' & ta & (K & HANDLE) & EQ).
            red in HANDLE.
            rewrite HANDLE in EQ.
            cbn in EQ.
            rewrite bind_trigger in EQ.
            subst.
            
            (* tf2 has an extra tau *)
            apply go.
            apply TauF.
            eapply CIH with (tf2:=k2' b).
            apply ANS.
            red; eauto.
            pstep; eauto.

            specialize (K b).
            forward K.
            { setoid_rewrite HANDLE.
              unfold ITree.trigger.
              eapply ReturnsVis with (x:=b).
              reflexivity.
              cbn.
              constructor; reflexivity.
            }

            pclearbot.
            punfold K.
          }
          { (* VisOOM *)
            destruct OOMP as (A & e & k1' & t1' & t2' & ((VISEQ & TF) & TF2)).
            (* Right hand side ran out of memory, so any tree will do *)
            apply (ret 0%nat).
          }
          { (* Vis events *)
            destruct VISP as (A & e & k1' & k2' & ta & t2' & ((((HS & HANDLE) & SPEC) & TF) &TF2)).
            (* tf2 was a vis node... *)
            setoid_rewrite <- VIS2 in TF.
            inv TF.
            subst_existT.
            red in HANDLE.

            specialize (HS b).
            forward HS.
            { setoid_rewrite HANDLE.
              unfold ITree.trigger.
              eapply ReturnsVis with (x:=b).
              reflexivity.
              cbn.
              constructor; reflexivity.
            }

            pclearbot.

            apply go.
            apply TauF.
            eapply CIH with (tf2 := k2' b).
            apply ANS.
            apply HS.
          }
        -- (* OOM events *)
          exfalso.
          eapply NOOM.
          reflexivity.
    - (* Vis OOM *)
      destruct VISOOM as (A & e & t1' & k2 & T1' & TF).
      subst.
      (* OOM on right, any tree will do *)
      apply (ret 0%nat).
    - (* TauL *)
      destruct TauL as (t1' & ot2 & ((HS & TI) & TF)).
      apply go.
      apply TauF.
      eapply CIH; eauto.
      pstep. red.
      eauto.
    - (* TauR *)
      destruct TauR as (ot1 & t2' & ((HS & TI) & TF)).
      apply go.
      apply TauF.
      eapply CIH; eauto.
      pstep. red.
      eauto.
  Defined.

  Lemma get_inf_tree' :
    forall ti tf,
      orutt (@L1_ref) (@L1_ref_ans) nb ti tf (OOM:=OOME) ->
      forall tf2, runFin tf tf2 ->
             CoSig (itree (IEvent +' OOME) nat)
               (fun ti2 =>
                  runInf ti ti2 /\
                    orutt (@L2_ref) (@L2_ref_ans) nb ti2 tf2 (OOM:=OOME)).
  (* Proof. *)
  (*   intros ti tf REL tf2 RUN. *)
  (*   revert RUN. *)
  (*   revert REL. *)
  (*   revert ti tf tf2. *)
  (*   cofix CIH. *)
  (*   intros ti tf tf2 REL RUN. *)
  (*   apply orutt_inv_Type in REL as (REL' & REL). *)
  (*   destruct REL as [[[[[RET | TAU] | VIS] | VISOOM] | TauL] | TauR]. *)
  (*   - (* Ret *) *)
  (*     destruct RET as (r1 & r2 & (RRr1r2 & RET1) & RET2). *)
  (*     apply coexist with (x:=(ret r1)). *)
  (*     split. *)
  (*     { pstep. *)
  (*       red. *)
  (*       setoid_rewrite <- RET1. *)
  (*       cbn. *)
  (*       constructor. *)
  (*       reflexivity. *)
  (*     } *)
  (*     { clear - RRr1r2 RUN RET1 RET2. *)
  (*       revert tf tf2 r1 r2 RRr1r2 RUN RET1 RET2. *)
  (*       pcofix CIH. *)
  (*       intros tf tf2 r1 r2 RRr1r2 RUN RET1 RET2. *)
  (*       pinversion RUN; subst; *)
  (*         try (setoid_rewrite <- RET2 in H0; inv H0). *)
  (*       - pstep. *)
  (*         red. rewrite <- H. *)
  (*         cbn. *)
  (*         constructor; auto. *)
  (*       - (* Tau in tf2 *) *)
  (*         pstep. red. *)
  (*         cbn. setoid_rewrite <- H1. *)
  (*         setoid_rewrite <- RET2 in HS. *)
  (*         dependent induction HS; subst. *)
  (*         + apply OOMRutt.EqTauR. *)
  (*           rewrite <- x. *)
  (*           constructor; auto. *)
  (*         + eapply IHHS; eauto. *)
  (*           admit. *)
  (*         +  *)
  (*           cbn. *)
  (*           setoid_rewrite <- H1. *)
  (*           constructor. *)
  (*           eapply CIH. *)
          

  (*       punfold RUN. *)
  (*       pfold. *)
  (*       red in RUN. *)
  (*       setoid_rewrite <- RET2 in RUN. *)
        
  (*       dependent induction RUN. *)
  (*       - pstep. *)
  (*         red. *)
  (*         cbn. rewrite <- x. *)
  (*         constructor; auto. *)
  (*       - eapply IHRUN. eauto. *)
  (*         pstep. *)
  (*         red. *)
  (*         cbn. *)
  (*         rewrite <- x. *)
  (*         constructor. *)
          
        
  (*       apply orutt_ret. *)
        
  (*       pstep. *)
  (*       red. *)
        

  (*     }       *)
  (*     apply (ret r1). *)
  (*   - (* Double Tau *) *)
  (*     destruct TAU as (m1 & m2 & (HS & TAU1) & TAU2). *)
  (*     apply go. *)
  (*     apply TauF. *)
  (*     eapply CIH with (tf:=m2) (tf2:=tf2). *)
  (*     apply HS. *)
  (*     red; red in RUN. *)
  (*     setoid_rewrite <- (tau_eutt m2). *)
  (*     pstep. rewrite TAU2. *)
  (*     red. *)
  (*     cbn. *)
  (*     punfold RUN. *)
  (*   - (* Vis *) *)
  (*     destruct VIS as (A & B & e1 & e2 & k1 & k2 & ((HS & NOOM) & VIS1) & VIS2). *)
  (*     destruct HS as (e1e2 & ANS). *)
  (*     destruct e1, e2; cbn in e1e2; try inv e1e2; *)
  (*       try (repeat break_match_hyp; contradiction). *)
  (*     + (* nondetE *) *)
  (*       destruct n, n0. *)
  (*       cbn in *. *)
  (*       (* Need to know the choice made here for tf2 *) *)
  (*       red in RUN. *)
  (*       apply interp_prop_inv_Type in RUN as (RUN' & RUN). *)
  (*       destruct RUN as [[[[[RETP | TAUP] | TAULP] | TAURP] | OOMP] | VISP]. *)
  (*       { destruct RETP as (r1 & r2 & (RRr1r2 & RET1) & RET2); *)
  (*           setoid_rewrite <- VIS2 in RET1; inv RET1. *)
  (*       } *)
  (*       { destruct TAUP as (m1 & m2 & (HS & TAU1) & TAU2). *)
  (*         setoid_rewrite <- VIS2 in TAU1; inv TAU1. *)
  (*       } *)
  (*       { destruct TAULP as (m1 & m2 & (HS & TAU1) & TAU2). *)
  (*         setoid_rewrite <- VIS2 in TAU1; inv TAU1. *)
  (*       } *)
  (*       { (* Tau on right... *) *)
  (*         destruct TAURP as (m1 & m2 & (HS & TAU1) & TAU2). *)
  (*         apply go. *)
  (*         apply TauF. *)
  (*         eapply CIH. *)
  (*         red; eauto. *)
  (*         pstep; eauto. *)
  (*       } *)
  (*       { (* VisOOM *) *)
  (*         destruct OOMP as (A & e & k1' & t1' & t2' & ((VISEQ & TF) & TF2)). *)
  (*         (* Right hand side ran out of memory, so any tree will do *) *)
  (*         apply (ret 0%nat). *)
  (*       } *)
  (*       { (* Vis events *) *)
  (*         destruct VISP as (A & e & k1' & k2' & ta & t2' & ((((HS & HANDLE) & SPEC) & TF) &TF2)). *)
  (*         (* tf2 was a vis node... *) *)
  (*         setoid_rewrite <- VIS2 in TF. *)
  (*         inv TF. *)
  (*         subst_existT. *)
  (*         red in HANDLE. *)
  (*         apply or_Type_inv in HANDLE. *)
  (*         destruct HANDLE; subst. *)
  (*         - setoid_rewrite bind_ret_l in SPEC. *)
  (*           apply go. *)
  (*           apply TauF. *)

  (*           specialize (ANS true true eq_refl). *)
  (*           specialize (HS true). *)
  (*           forward HS. *)
  (*           constructor; reflexivity. *)
  (*           pclearbot. *)

  (*           eapply CIH with (tf2:=k2' true); eauto. *)
  (*         - setoid_rewrite bind_ret_l in SPEC. *)
  (*           apply go. *)
  (*           apply TauF. *)

  (*           specialize (ANS false false eq_refl). *)
  (*           specialize (HS false). *)
  (*           forward HS. *)
  (*           constructor; reflexivity. *)
  (*           pclearbot. *)

  (*           eapply CIH with (tf2:=k2' false); eauto. *)
  (*       } *)
  (*     + (* Uninterpreted events *) *)
  (*       destruct s, s0; *)
  (*         repeat break_match_hyp; try contradiction. *)

  (*       -- (* IEvent / FEvent *) *)
  (*         cbn in *. *)
  (*         specialize (ANS n b). *)
  (*         forward ANS; auto. *)
  (*         pclearbot. *)

  (*         (* *)
  (*           apply go. *)
  (*           apply TauF. *)
  (*           eapply CIH. *)
  (*           apply ANS. *)
  (*          *) *)

  (*         (* Need to know stuff about continuations... *) *)
  (*         red in RUN. *)
  (*         apply interp_prop_inv_Type in RUN as (RUN' & RUN). *)
  (*         destruct RUN as [[[[[RETP | TAUP] | TAULP] | TAURP] | OOMP] | VISP]. *)
  (*         { destruct RETP as (r1 & r2 & (RRr1r2 & RET1) & RET2); *)
  (*             setoid_rewrite <- VIS2 in RET1; inv RET1. *)
  (*         } *)
  (*         { destruct TAUP as (m1 & m2 & (HS & TAU1) & TAU2). *)
  (*           setoid_rewrite <- VIS2 in TAU1; inv TAU1. *)
  (*         } *)
  (*         { destruct TAULP as (m1 & m2 & (HS & TAU1) & TAU2). *)
  (*           setoid_rewrite <- VIS2 in TAU1; inv TAU1. *)
  (*         } *)
  (*         { (* Tau on right... *) *)
  (*           destruct TAURP as (m1 & m2 & (HS & TAU1) & TAU2). *)
  (*           setoid_rewrite <- VIS2 in HS. *)

  (*           apply interp_PropTF_vis_l_inv_Type in HS. *)
  (*           destruct HS as (k2' & ta & (K & HANDLE) & EQ). *)
  (*           red in HANDLE. *)
  (*           rewrite HANDLE in EQ. *)
  (*           cbn in EQ. *)
  (*           rewrite bind_trigger in EQ. *)
  (*           subst. *)
            
  (*           (* tf2 has an extra tau *) *)
  (*           apply go. *)
  (*           apply TauF. *)
  (*           eapply CIH with (tf2:=k2' b). *)
  (*           apply ANS. *)
  (*           red; eauto. *)
  (*           pstep; eauto. *)

  (*           specialize (K b). *)
  (*           forward K. *)
  (*           { setoid_rewrite HANDLE. *)
  (*             unfold ITree.trigger. *)
  (*             eapply ReturnsVis with (x:=b). *)
  (*             reflexivity. *)
  (*             cbn. *)
  (*             constructor; reflexivity. *)
  (*           } *)

  (*           pclearbot. *)
  (*           punfold K. *)
  (*         } *)
  (*         { (* VisOOM *) *)
  (*           destruct OOMP as (A & e & k1' & t1' & t2' & ((VISEQ & TF) & TF2)). *)
  (*           (* Right hand side ran out of memory, so any tree will do *) *)
  (*           apply (ret 0%nat). *)
  (*         } *)
  (*         { (* Vis events *) *)
  (*           destruct VISP as (A & e & k1' & k2' & ta & t2' & ((((HS & HANDLE) & SPEC) & TF) &TF2)). *)
  (*           (* tf2 was a vis node... *) *)
  (*           setoid_rewrite <- VIS2 in TF. *)
  (*           inv TF. *)
  (*           subst_existT. *)
  (*           red in HANDLE. *)

  (*           specialize (HS b). *)
  (*           forward HS. *)
  (*           { setoid_rewrite HANDLE. *)
  (*             unfold ITree.trigger. *)
  (*             eapply ReturnsVis with (x:=b). *)
  (*             reflexivity. *)
  (*             cbn. *)
  (*             constructor; reflexivity. *)
  (*           } *)

  (*           pclearbot. *)

  (*           apply go. *)
  (*           apply TauF. *)
  (*           eapply CIH with (tf2 := k2' b). *)
  (*           apply ANS. *)
  (*           apply HS. *)
  (*         } *)
  (*       -- (* OOM events *) *)
  (*         exfalso. *)
  (*         eapply NOOM. *)
  (*         reflexivity. *)
  (*   - (* Vis OOM *) *)
  (*     destruct VISOOM as (A & e & t1' & k2 & T1' & TF). *)
  (*     subst. *)
  (*     (* OOM on right, any tree will do *) *)
  (*     apply (ret 0%nat). *)
  (*   - (* TauL *) *)
  (*     destruct TauL as (t1' & ot2 & ((HS & TI) & TF)). *)
  (*     apply go. *)
  (*     apply TauF. *)
  (*     eapply CIH; eauto. *)
  (*     pstep. red. *)
  (*     eauto. *)
  (*   - (* TauR *) *)
  (*     destruct TauR as (ot1 & t2' & ((HS & TI) & TF)). *)
  (*     apply go. *)
  (*     apply TauF. *)
  (*     eapply CIH; eauto. *)
  (*     pstep. red. *)
  (*     eauto. *)
  (* Defined. *)

  Require Import ChoiceFacts.

(* Theorem constructive_definite_descr_excluded_middle : *)
(*   (forall A : Type, ConstructiveDefiniteDescription_on A) -> *)
(*   (forall P:Prop, P \/ ~ P) -> (forall P:Prop, {P} + {~ P}). *)
(* Proof. *)
(*   intros Descr EM P. *)
(*   pose (select := fun b:bool => if b then P else ~P). *)
(*   assert { b:bool | select b } as ([|],HP). *)
(*   red in Descr. *)
(*   apply Descr. *)
(*   rewrite <- unique_existence; split. *)
(*   destruct (EM P). *)
(*   exists true; trivial. *)
(*   exists false; trivial. *)
(*   intros [|] [|] H1 H2; simpl in *; reflexivity || contradiction. *)
(*   left; trivial. *)
(*   right; trivial. *)
(* Qed. *)

(* Theorem excluded_middle_informative : forall P:Prop, {P} + {~ P}. *)
(* Proof. *)
(*   apply *)
(*     (constructive_definite_descr_excluded_middle *)
(*       constructive_definite_description classic). *)
(* Qed. *)

(* Theorem classical_indefinite_description : *)
(*   forall (A : Type) (P : A->Prop), inhabited A -> *)
(*     { x : A | (exists x, P x) -> P x }. *)
(* Proof. *)
(*   intros A P i. *)
(*   destruct (excluded_middle_informative (exists x, P x)) as [Hex|HnonP]. *)
(*   apply constructive_indefinite_description *)
(*     with (P:= fun x => (exists x, P x) -> P x). *)
(*   destruct Hex as (x,Hx). *)
(*     exists x; intros _; exact Hx. *)
(*   assert {x : A | True} as (a,_). *)
(*     apply constructive_indefinite_description with (P := fun _ : A => True). *)
(*     destruct i as (a); firstorder. *)
(*   firstorder. *)
(* Defined. *)

  (*   Print classical_indefinite_description. *)
  Abort.

  Lemma foo :
    forall ti tf,
      orutt (@L1_ref) (@L1_ref_ans) nb ti tf (OOM:=OOME) ->
      forall tf2, runFin tf tf2 ->
      exists ti2,
        runInf ti ti2 /\
          orutt (@L2_ref) (@L2_ref_ans) nb ti2 tf2 (OOM:=OOME).  
  Proof.
    intros ti tf REL tf2 RUN.

    exists (get_inf_tree ti tf REL tf2 RUN).
    split.
    { (* Need to show that get_inf_tree is in the set of itrees generated by ti *)
      revert RUN.
      revert REL.
      revert ti tf tf2.
      pcofix CIH.
      intros ti tf tf2 REL RUN.
      remember (get_inf_tree ti tf REL tf2 RUN).
      repeat red in REL.
      punfold REL.
      dependent destruction REL.
      pose proof REL.
      apply orutt_inv_Type in H.
      dependent inversion REL.
      pinversion REL.
      destruct REL.
      dependent destruction REL.
    }

    setoid_rewrite (itree_eta_ ti).
    setoid_rewrite (itree_eta_ tf2).
    setoid_rewrite (itree_eta_ ti) in REL.
    setoid_rewrite (itree_eta_ tf) in REL.
    setoid_rewrite (itree_eta_ tf2) in RUN.
    setoid_rewrite (itree_eta_ tf) in RUN.
    genobs ti oti.
    genobs tf otf.
    genobs tf2 otf2.

    clear Heqoti ti.
    clear Heqotf tf.
    clear Heqotf2 tf2.

    exists (get_inf_tree {| _observe := oti |} {| _observe := otf |} REL {| _observe := otf2 |} RUN).
    split.
    { red in REL.
      revert RUN.
      revert REL.
      revert oti otf otf2.
      pcofix CIH.

      induction oti, otf.
      - intros otf2 REL RUN.
        pstep.
        red.
        cbn.

        red in RUN.
        red in RUN.
        red in RUN.
        
        cbn in RUN.
        pbase
        pstep. _reverse.
        punfold REL.

      intros oti otf otf2 REL RUN.
      pinversion RUN.

      pstep.
      red.
      cbn.
      red in REL.
      pstep.
      red.
      punfold REL.
      exfalso.
      dependent induction ti.
      unfold get_inf_tree.
    }

    
    assert (itree (IEvent +' OOME) nat) as ti2.
    { revert RUN.
      revert REL.
      revert ti tf tf2.
      cofix CIH.
      intros ti tf tf2 REL RUN.
      apply orutt_inv_Type in REL as (REL' & REL).
      destruct REL as [[[[[RET | TAU] | VIS] | VISOOM] | TauL] | TauR].
      - (* Ret *)
        destruct RET as (r1 & r2 & (RRr1r2 & RET1) & RET2).
        apply (ret r1).
      - (* Double Tau *)
        destruct TAU as (m1 & m2 & (HS & TAU1) & TAU2).
        apply go.
        apply TauF.
        eapply CIH with (tf:=m2) (tf2:=tf2).
        apply HS.
        red; red in RUN.
        setoid_rewrite <- (tau_eutt m2).
        pstep. rewrite TAU2.
        red.
        cbn.
        punfold RUN.
      - (* Vis *)
        destruct VIS as (A & B & e1 & e2 & k1 & k2 & ((HS & NOOM) & VIS1) & VIS2).
        destruct HS as (e1e2 & ANS).
        destruct e1, e2; cbn in e1e2; try inv e1e2;
          try (repeat break_match_hyp; contradiction).
        + (* nondetE *)
          destruct n, n0.
          cbn in *.
          (* Need to know the choice made here for tf2 *)
          red in RUN.
          apply interp_prop_inv_Type in RUN as (RUN' & RUN).
          destruct RUN as [[[[[RETP | TAUP] | TAULP] | TAURP] | OOMP] | VISP].
          { destruct RETP as (r1 & r2 & (RRr1r2 & RET1) & RET2);
            setoid_rewrite <- VIS2 in RET1; inv RET1.
          }
          { destruct TAUP as (m1 & m2 & (HS & TAU1) & TAU2).
            setoid_rewrite <- VIS2 in TAU1; inv TAU1.
          }
          { destruct TAULP as (m1 & m2 & (HS & TAU1) & TAU2).
            setoid_rewrite <- VIS2 in TAU1; inv TAU1.
          }
          { (* Tau on right... *)
            destruct TAURP as (m1 & m2 & (HS & TAU1) & TAU2).
            apply go.
            apply TauF.
            eapply CIH.
            red; eauto.
            pstep; eauto.
          }
          { (* VisOOM *)
            destruct OOMP as (A & e & k1' & t1' & t2' & ((VISEQ & TF) & TF2)).
            (* Right hand side ran out of memory, so any tree will do *)
            apply (ret 0%nat).
          }
          { (* Vis events *)
            destruct VISP as (A & e & k1' & k2' & ta & t2' & ((((HS & HANDLE) & SPEC) & TF) &TF2)).
            (* tf2 was a vis node... *)
            setoid_rewrite <- VIS2 in TF.
            inv TF.
            subst_existT.
            red in HANDLE.
            apply or_Type_inv in HANDLE.
            destruct HANDLE; subst.
            - setoid_rewrite bind_ret_l in SPEC.
              apply go.
              apply TauF.

              specialize (ANS true true eq_refl).
              specialize (HS true).
              forward HS.
              constructor; reflexivity.
              pclearbot.

              eapply CIH with (tf2:=k2' true); eauto.
            - setoid_rewrite bind_ret_l in SPEC.
              apply go.
              apply TauF.

              specialize (ANS false false eq_refl).
              specialize (HS false).
              forward HS.
              constructor; reflexivity.
              pclearbot.

              eapply CIH with (tf2:=k2' false); eauto.
          }
        + (* Uninterpreted events *)
          destruct s, s0;
            repeat break_match_hyp; try contradiction.

          -- (* IEvent / FEvent *)
            cbn in *.
            specialize (ANS n b).
            forward ANS; auto.
            pclearbot.

            (*
            apply go.
            apply TauF.
            eapply CIH.
            apply ANS.
            *)

            (* Need to know stuff about continuations... *)
            red in RUN.
            apply interp_prop_inv_Type in RUN as (RUN' & RUN).
            destruct RUN as [[[[[RETP | TAUP] | TAULP] | TAURP] | OOMP] | VISP].
            { destruct RETP as (r1 & r2 & (RRr1r2 & RET1) & RET2);
                setoid_rewrite <- VIS2 in RET1; inv RET1.
            }
            { destruct TAUP as (m1 & m2 & (HS & TAU1) & TAU2).
              setoid_rewrite <- VIS2 in TAU1; inv TAU1.
            }
            { destruct TAULP as (m1 & m2 & (HS & TAU1) & TAU2).
              setoid_rewrite <- VIS2 in TAU1; inv TAU1.
            }
            { (* Tau on right... *)
              destruct TAURP as (m1 & m2 & (HS & TAU1) & TAU2).
              setoid_rewrite <- VIS2 in HS.

              (* TODO: confirm this inversion axiom... *)
              Axiom interp_PropTF_vis_l_inv_Type :
                forall {E F OOM : Type -> Type}
                  X
                  (OOME : OOM -< E)
                  (h : forall T : Type, E T -> PropT F T)
                  (R1 R2 : Type)
                  (RR : R1 -> R2 -> Prop)
                  (b1 b2 : bool)
                  (sim : itree E R1 -> itree F R2 -> Prop)
                  (e : E X) k t',
                  interp_PropTF (OOME:=OOME) h RR b1 b2 sim (VisF e k) (observe t') ->
                  ({k2 & {ta &
                            (forall (a : X), Returns a ta -> upaco2 (interp_PropT_ h RR b1 b2 (OOME:=OOME)) bot2 (k a) (k2 a)) *
                              (h X e ta) *
                              (t' ≈ x <- ta;; k2 x)}})%type.

              apply interp_PropTF_vis_l_inv_Type in HS.
              destruct HS as (k2' & ta & (K & HANDLE) & EQ).
              red in HANDLE.
              rewrite HANDLE in EQ.
              cbn in EQ.
              rewrite bind_trigger in EQ.
              subst.
              
              (* tf2 has an extra tau *)
              apply go.
              apply TauF.
              eapply CIH with (tf2:=k2' b).
              apply ANS.
              red; eauto.
              pstep; eauto.

              specialize (K b).
              forward K.
              { setoid_rewrite HANDLE.
                unfold ITree.trigger.
                eapply ReturnsVis with (x:=b).
                reflexivity.
                cbn.
                constructor; reflexivity.
              }

              pclearbot.
              punfold K.
            }
            { (* VisOOM *)
              destruct OOMP as (A & e & k1' & t1' & t2' & ((VISEQ & TF) & TF2)).
              (* Right hand side ran out of memory, so any tree will do *)
              apply (ret 0%nat).
            }
            { (* Vis events *)
              destruct VISP as (A & e & k1' & k2' & ta & t2' & ((((HS & HANDLE) & SPEC) & TF) &TF2)).
              (* tf2 was a vis node... *)
              setoid_rewrite <- VIS2 in TF.
              inv TF.
              subst_existT.
              red in HANDLE.

              specialize (HS b).
              forward HS.
              { setoid_rewrite HANDLE.
                unfold ITree.trigger.
                eapply ReturnsVis with (x:=b).
                reflexivity.
                cbn.
                constructor; reflexivity.
              }

              pclearbot.

              apply go.
              apply TauF.
              eapply CIH with (tf2 := k2' b).
              apply ANS.
              apply HS.
            }
          -- (* OOM events *)
            exfalso.
            eapply NOOM.
            reflexivity.
      - (* Vis OOM *)
        destruct VISOOM as (A & e & t1' & k2 & T1' & TF).
        subst.
        (* OOM on right, any tree will do *)
        apply (ret 0%nat).
      - (* TauL *)
        destruct TauL as (t1' & ot2 & ((HS & TI) & TF)).
        apply go.
        apply TauF.
        eapply CIH; eauto.
        pstep. red.
        eauto.
      - (* TauR *)
        destruct TauR as (ot1 & t2' & ((HS & TI) & TF)).
        apply go.
        apply TauF.
        eapply CIH; eauto.
        pstep. red.
        eauto.
    }

    exists ti2.
    split.
    unfold ti2.
      - (* Ret *)
        
    }

    assert (CoSig (itree (IEvent +' OOME) nat) (fun ti2 => runInf ti ti2)).
    { revert RUN.
      revert REL.
      revert ti tf tf2.
      cofix CIH.
      intros ti tf tf2 REL RUN.
      apply orutt_inv_Type in REL as (REL' & REL).
      destruct REL as [[[[[RET | TAU] | VIS] | VISOOM] | TauL] | TauR].
      - (* Ret *)
        destruct RET as (r1 & r2 & (RRr1r2 & RET1) & RET2).
        apply coexist with (x:=ret r1).
        pstep. red.
        setoid_rewrite <- RET1.
        cbn.
        constructor; auto.
      - (* Double Tau *)
        destruct TAU as (m1 & m2 & (HS & TAU1) & TAU2).
        apply cotau.
        eapply CIH with (tf:=m2) (tf2:=tf2).
        + pstep.
          red.
          rewrite <- TAU1.
          constructor.
          punfold HS.
        + red.
          red in RUN.
          setoid_rewrite <- (tau_eutt m2).
          pstep. rewrite TAU2.
          red.
          cbn.
          punfold RUN.
      - (* Vis *)
        destruct VIS as (A & B & e1 & e2 & k1 & k2 & ((HS & NOOM) & VIS1) & VIS2).
        apply cotau.
        eapply CIH with (tf:=
        apply coexist with (x:=
        

        
          assert (tf ≈ m2) as EQ.
          { setoid_rewrite <- (tau_eutt m2).
            pstep.
            red.
            cbn.
            rewrite <- TAU2.
            constructor; auto.
            left.
            
            right. red.
            left.
            p
            pbase.
          }

        apply coexist with (x:=m1).
        assert (runFin m2 tf2).
        { red.
          red in RUN.
          pinversion RUN;
            try (setoid_rewrite <- H0 in TAU2; inv TAU2).
          - punfold HS0.
            red in HS0.
            pstep; red.
            red in RUN.
            apply HS0.
        }
        apply go.
        apply TauF.

        eapply CIH.
        apply HS.
        apply m2.
        apply HS.
        apply TauF.
        
    }
    unfold runFin in H0.
    unfold runInf.
    (* Possible strategy: *)
    assert (ti = Ret 0%nat).
    admit.
    assert (tf = Ret false).
    admit.
    subst.    

  (*      H0 is kind of a stream of booleans telling us what choices were made to get tf2... *)

  (*      Given ti and that stream we could write an interpreter that *)
  (*      just follows that stream to make "equivalent" choices. *)

  (*      Possible lemma to prove... *)

  (*      Define an interpreter that takes a stream for the *)
  (*      nondeterministic choices... *)

  (*      Prove that there exists a stream... Possibly runFin could *)
  (*      produce a stream of choices as well too... *)

  (*      runFin tf tf2 choices *)

  (*      Could be annoying for Vellvm because of pick having different *)
  (*      types... We'll see. Maybe could trigger error when type *)
  (*      unknown. *)
  (*   *)
  Abort.

  Unset Printing Implicit.
  
  Lemma model_E1E2_23_orutt_strict :
    forall t1 t2 sid ms1 ms2,
      L2_E1E2_orutt_strict t1 t2 ->
      MemState_refine ms1 ms2 ->
      L3_E1E2_orutt_strict (InfMemInterp.interp_memory_prop eq t1 sid ms1) (FinMemInterp.interp_memory_prop eq t2 sid ms2).
  Proof.
    intros t_inf t_fin sid ms1 ms2 REL MSR.
    (* red in REL. *)

    unfold L3_E1E2_orutt_strict.
    intros t_fin2 FIN_HANDLED.

    assert (itree InfLP.Events.L3 TopLevelBigIntptr.res_L6).
    { revert FIN_HANDLED.
      revert REL.      
      revert t_inf t_fin t_fin2.
      cofix CIH.

      intros t_inf t_fin t_fin2 REL FIN_HANDLED.
      apply orutt_inv_Type in REL.
      destruct REL.
      destruct s as [[[[[RET | TAU] | VIS] | VISOOM] | TauL] | TauR].
      - (* Ret *)
        destruct RET as (r1 & r2 & (RRr1r2 & RET1) & RET2).
        admit.
      - (* TauR *)
      exfalso.
      red in REL.
      pinversion REL.
      admit.
      admit.
      admit.
      admit.
      admit.

      Set Nested Proofs Allowed.

               +
                 (* Double tau *)
                 (exists t1' t2', (paco2 (interp_PropT_ h_spec RR true true (OOME:=OOME)) bot2 t1' t2') * (TauF t1' = observe t1) * (TauF t2' = observe t2)) +
                 (* Tau left *)
                 (exists t1' t2',
                     (interp_PropTF (OOME:=OOME) h_spec RR true true (upaco2 (interp_PropT_ h_spec RR true true (OOME:=OOME)) bot2) (observe t1') (observe t2)) *
                       (TauF t1' = observe t1) * (t2' = observe t2)) +
                 (* Tau right *)
                 (exists t1' t2',
                     (interp_PropTF (OOME:=OOME) h_spec RR true true (upaco2 (interp_PropT_ h_spec RR true true (OOME:=OOME)) bot2) (observe t1) (observe t2')) *
                       (t1' = observe t1) * (TauF t2' = observe t2)) +
                 (* OOM vis *)
                 (exists (A : Type) (e : OOM A) k1 t1' t2',
                     (t1' ≅ vis e k1) * (observe t1' = observe t1) * (t2' = observe t2)) +
                 (* Vis nodes *)
                 (exists (A : Type) e k1 k2 ta t2',
                     (forall (a : A), Returns a ta -> upaco2 (interp_PropT_ h_spec RR true true (OOME:=OOME)) bot2 (k1 a) (k2 a)) *
                       (h_spec A e ta) *
                       (t2' ≈ x <- ta;; k2 x) *
                       (VisF e k1 = observe t1) *
                       (observe t2' = observe t2))
             )
          )%type.
      Admitted.

      apply interp_prop_inv_Type in REL.
      pinversion REL.      

    }

    punfold RL2.
    red in RL2.
    punfold H.
    red in H.
    

    Set Nested Proofs Allowed.

    Definition convert_tree (t : itree L3 (FinMem.MMEP.MMSP.MemState * (MemPropT.store_id * (local_env * @stack local_env * res_L1)))) : itree InfLP.Events.L3 TopLevelBigIntptr.res_L6.
    Proof.
      revert t.
      cofix CIH.
      intros t.
      destruct t.
      rename _observe into t.
      constructor.
      induction t.
      - (* Ret *)
        destruct r as [ms [sid [[lenv s] [genv dv]]]].
        apply RetF.
        (* Convert the finite values to infinite ones*)
        constructor; [|constructor; [| constructor; [| constructor]]].
        + (* MemState conversion *)
          admit.          
        + exact sid.
        + (* Locals and local stack *)
          admit.
        + (* Global environment *)
          admit.
        + pose proof DVC2.dvalue_convert_strict.
          specialize (H dv).
          (* I *should* know that converting a finite dvalue to an
             infinite dvalue always succeeds *)
          destruct H.
          -- exact d.
          -- (* OOM here should be a contradiction... *)
            admit.
      - (* Tau *)
        apply TauF.
        specialize (CIH t).
        apply CIH.
      - (* Vis *)
        apply VisF with (X:=X).
        + (* Result from handler *)
          (* We actually already have event conversions... *)
          pose proof (EC2.L3_convert_strict _ e).
          (* Actually the event conversion we have gives us a new itree... *)
          destruct e.
          -- (* ExternalCallE *)
            inv e.
            constructor.

          admit.
        + intros x.
          specialize (k x).
          apply CIH. apply k.
        Guarded.
      punfold t.
    Defined.

    (* I need to find a `t` that corresponds to the `t'` that's in the
       set given by the interpretation of memory events in `t2`...

       I guess I need to know what decisions were made to get `t'` out
       of `t2`, and make similar decisions to get `t` out of `t1`.

       I guess we need to do coinduction on `t2`?

       - Whenever we have a `Ret` `t'` is should going to end up being
         basically the same `Ret`...
       - Tau nodes should basically be irrelevant...
       - Vis nodes have two cases...
         1. The vis node is an event that isn't interpreted by the
            memory handler... No non-determinism in this, so the
            corresponding `t` should just raise the same event again.
         2. The vis node is a memory event...

       In the second case where the vis is a memory event that we
       interpret we can have non-determinism. E.g., we might have an
       Alloca event, and we will have to pick the location in memory
       that the block gets allocated. `t'` can be any tree where a
       valid address for the allocated block is returned... So, we'll
       need to show that any valid address to allocate a block in the
       current state of the finite memory corresponds to a valid
       address to allocate a block in the current state of the
       corresponding infinite memory. This should hopefully not be too
       bad because the infinite and finite memories will have the same
       layout (this assumption is missing from the initial draft
       of this lemma).
     *)

  (*   unfold IS1.MEM.MEM_SPEC_INTERP.interp_memory_prop. *)
  (*   unfold IS2.MEM.MEM_SPEC_INTERP.interp_memory_prop. *)
  (*   cbn. *)
  (*   eapply orutt_interp_state; eauto. *)
  (*   { unfold local_stack_refine_strict in *. *)
  (*     destruct ls1, ls2; *)
  (*     constructor; tauto. *)
  (*   } *)

  (*   intros A B e1 e2 s1 s2 H H0. *)
  (*   eapply orutt_interp_local_stack_h; eauto. *)
  (*   inv H0. *)
  (*   destruct s1, s2; cbn in *; auto. *)

  (*   intros A o s. *)
  (*   exists o. *)
  (*   cbn. *)
  (*   setoid_rewrite bind_trigger. *)
  (*   exists (fun x : A => SemNotations.Ret1 s x). *)
  (*   reflexivity. *)
    (* Qed. *)
  Admitted.

  (* Lemma model_E1E2_L3_orutt_strict_sound *)
  (*   (p : list *)
  (*          (LLVMAst.toplevel_entity *)
  (*             LLVMAst.typ *)
  (*             (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ)))) : *)
  (*   model_E1E2_L3_orutt_strict p p. *)
  (* Proof. *)
  (*   apply model_E1E2_13_orutt_strict; *)
  (*     [ apply model_E1E2_L2_orutt_strict_sound *)
  (*     | apply local_stack_refine_strict_empty *)
  (*     ]. *)
  (* Qed. *)

  (* If

    - ti2 is a refinement of ti1 tf2 refines ti2 tf1 refines tf2 at
    - finite level

    Not sure that this is true.

    If ti1 -i> ti2

    and ti2 -if> tf2

    And tf2 -f> tf1...

    Does it really follow that ti1 -if> tf1?

    In theory I can refine ti1 to ti2, and to tf1 through
    tf2... BUT... Does this mean I can refine ti1 directly to tf1?

    In theory ti2 has fewer behaviours than ti1, and so if I can
    refine it to tf2, then I can also refine ti1 to tf2.
   *)
  Lemma refine_E1E2_L6_strict_compose_inf_to_fin :
    forall tx ty tz,
      TLR_INF.R.refine_L6 tx ty ->
      refine_E1E2_L6_strict ty tz ->
      refine_E1E2_L6_strict tx tz.
  Proof.
    intros tx ty tz XY_INF YZ_FIN.

    unfold refine_E1E2_L6_strict in *.
    unfold TLR_INF.R.refine_L6 in *.
    unfold TLR_FIN.R.refine_L6 in *.

    intros rz TZ.
    specialize (YZ_FIN rz TZ).
    destruct YZ_FIN as (ry_fin & TY_FIN & YZ).

    unfold L6_convert_PropT_strict in TY_FIN.
    destruct TY_FIN as (ry_inf & TY_INF & ry_fin_inf).

    specialize (XY_INF ry_inf TY_INF).
    destruct XY_INF as (rx_inf & TX_INF & XY_INF).

    set (rx_fin := L4_convert_tree_strict' res_L6_convert_strict_unsafe rx_inf).
    exists rx_fin.
    split.
    - unfold L6_convert_PropT_strict, L4_convert_PropT_strict.
      exists rx_inf; split; auto.
      subst rx_fin.
      reflexivity.
    - rewrite <- YZ.
      rewrite <- ry_fin_inf.
      subst rx_fin.

      (* There's probably a more general lemma hiding here *)
      unfold L4_convert_tree_strict'.

      Unset Universe Checking.
      eapply refine_OOM_h_bind with (RR1:=TopLevelRefinementsBigIntptr.R.refine_res3).
      { intros r1 r2 H.
        unfold TLR_INF.R.refine_res3, TLR_INF.R.refine_res2, TLR_INF.R.refine_res1 in H.
        destruct r1 as [r1a [r1sid [[r1b1 r1b2] [r1c dv1]]]].
        destruct r2 as [r2a [r2sid [[r2b1 r2b2] [r2c dv2]]]].
        cbn.

        inversion H; subst.
        inversion snd_rel; subst.
        inversion snd_rel0; subst.
        inversion snd_rel1; subst.
        cbn in *; subst; reflexivity.
      }
      { apply refine_OOM_h_L6_convert_tree_strict; auto.
      }
  Qed.

  Lemma refine_E1E2_L6_strict_compose_fin_to_inf :
    forall tx ty tz,
      refine_E1E2_L6_strict tx ty ->
      TLR_FIN.R.refine_L6 ty tz ->
      refine_E1E2_L6_strict tx tz.
  Proof.
    intros tx ty tz XY_INF_TO_FIN YZ_FIN.

    unfold refine_E1E2_L6_strict in *.
    unfold TLR_INF.R.refine_L6 in *.
    unfold TLR_FIN.R.refine_L6 in *.

    intros rz TZ.
    specialize (YZ_FIN rz TZ).
    destruct YZ_FIN as (ry_fin & TY_FIN & YZ).

    specialize (XY_INF_TO_FIN ry_fin TY_FIN).
    destruct XY_INF_TO_FIN as (rx_fin & TX_FIN & refine_inf_fin_x).

    exists rx_fin.
    split; auto.
    rewrite refine_inf_fin_x; auto.
  Qed.

  Theorem refine_E1E2_L6_transitive :
    forall ti1 ti2 tf1 tf2,
      TLR_INF.R.refine_L6 ti1 ti2 ->
      refine_E1E2_L6_strict ti2 tf1 ->
      TLR_FIN.R.refine_L6 tf1 tf2 ->
      refine_E1E2_L6_strict ti1 tf2.
  Proof.
    intros ti1 ti2 tf1 tf2 RINF RITOF RFIN.

    eapply refine_E1E2_L6_strict_compose_fin_to_inf; eauto.
    eapply refine_E1E2_L6_strict_compose_inf_to_fin; eauto.
  Qed.

  (** Safe conversion lemmas *)
  (* TODO: These used the Fin to Inf LangRefine that no longer exists
     because we added safe conversion modules... See if I still need
     these *)
  (* Lemma infinite_to_finite_dvalue_convert_safe : *)
  (*   forall dv_i, *)
  (*   exists dv_f, *)
  (*     EC1.DVC.dvalue_convert_strict dv_i = NoOom dv_f /\ *)
  (*       EC2.DVC.dvalue_convert_strict dv_f = NoOom dv_i. *)
  (* Proof. *)
  (*   intros dv_i. *)

  (*   rewrite EC1.DVC.dvalue_convert_equation. *)
  (*   destruct dv_i. *)
  (*   - (* Addresses *) *)

  (*   setoid_rewrite EC2.DVC.dvalue_convert_equation. *)

  (*   (* TODO: Ugh, everything is opaque. Fix and prove. *) *)
  (* Admitted. *)

  (* Lemma L0_convert_safe : *)
  (*   forall t, *)
  (*     InfFinTC.L0_convert_tree' EC1.DVC.dvalue_convert *)
  (*       (FinInfTC.L0_convert_tree' EC2.DVC.dvalue_convert t) ≈ t. *)
  (* Proof. *)
  (*   intros t. *)
  (*   unfold InfFinTC.L0_convert_tree', InfFinTC.L0_convert_tree. *)
  (*   unfold FinInfTC.L0_convert_tree', FinInfTC.L0_convert_tree. *)
  (*   cbn. *)
  (*   setoid_rewrite interp_bind. *)
  (*   rewrite bind_bind. *)
  (*   rewrite interp_interp. *)


  (*   cbn. *)
  (*   red. *)
  (* Admitted. *)

  (** Refinement lemmas *)
  Lemma refine_E1E2_L0_strict_interp_intrinsics :
    forall t1 t2,
      refine_E1E2_L0_strict t1 t2 ->
      refine_E1E2_L0_strict (InfLLVM.Intrinsics.interp_intrinsics t1) (FinLLVM.Intrinsics.interp_intrinsics t2).
  Proof.
    intros t1 t2 RL0.
    red in RL0.
    destruct RL0 as [t1' [OOM_T1 RL0]].
    red in RL0.
    red.
    (* exists (FinInfTC.L0_convert_tree_strict' EC2.DVC.dvalue_convert (FinLLVM.Intrinsics.interp_intrinsics t2)). *)
    (* split. *)
    (* - assert ((FinInfTC.L0_convert_tree' EC2.DVC.dvalue_convert (FinLLVM.Intrinsics.interp_intrinsics t2)) ≈  (FinInfTC.L0_convert_tree' EC2.DVC.dvalue_convert (LLVM.Intrinsics.interp_intrinsics (InfFinTC.L0_convert_tree' EC1.DVC.dvalue_convert t1')))) as EQT2. *)
    (*   { eapply @FinInfTC.L0_convert_tree'_eutt_proper with (RA:=eq). *)
    (*     intros u1 u2 H; subst. *)
    (*     reflexivity. *)

    (*     rewrite RL0. *)
    (*     reflexivity. *)
    (*   } *)

    (*   rewrite EQT2. *)

    (*   eapply refine_OOM_h_transitive with (y:=(InfLLVM.Intrinsics.interp_intrinsics t1')); try typeclasses eauto. *)
    (*   (* May hold... OOM_T1 *) *)
    (*   admit. *)

    (*   red. *)
    (*   red. *)
    (*   (* This might actually be provable by walking through t1'? *)

    (*      The conversions may cause early OOM, but otherwise preserves *)
    (*      the event structure. *)
    (*    *) *)
    (*   admit. *)
    (* - red. *)
    (*   (* This can't hold unless I know converting from E2 -> E1 -> E2 *)
    (*      is "safe" and doesn't cause any OOM. *)

    (*      This should be the case for the particular Inf / Fin case we *)
    (*      care about, though. *)
    (*    *) *)
    (*   rewrite L0_convert_safe. *)
    (*   reflexivity. *)
  Admitted.

  Lemma refine_E1E2_interp_global_strict :
    forall t1 t2 g1 g2,
      refine_E1E2_L0_strict t1 t2 ->
      global_refine_strict g1 g2 ->
      refine_E1E2_L1_strict (interp_global t1 g1) (interp_global t2 g2).
  Proof.
    intros t1 t2 g1 g2 RL0 GENVS.
    red in RL0.
    destruct RL0 as [t1' [OOM_T1 RL0]].
    red.

    (* Perhaps I need a lemma about L1_convert_tree and interp_global here? *)
  Admitted.

  Lemma refine_E1E2_interp_local_stack_strict :
    forall t1 t2 ls1 ls2,
      refine_E1E2_L1_strict t1 t2 ->
      local_stack_refine_strict ls1 ls2 ->
      refine_E1E2_L2_strict (interp_local_stack t1 ls1) (interp_local_stack t2 ls2).
  Proof.
  Admitted.

  (* Most of these are aliases of the above, but some levels of the interpreter interpret more than one event *)
  Lemma refine_E1E2_01_strict :
    forall t1 t2 g1 g2,
      refine_E1E2_L0_strict t1 t2 ->
      global_refine_strict g1 g2 ->
      refine_E1E2_L1_strict (interp_global (InfLLVM.Intrinsics.interp_intrinsics t1) g1) (interp_global (FinLLVM.Intrinsics.interp_intrinsics t2) g2).
  Proof.
    intros t1 t2 g1 g2 RL0 GENVS.
    red in RL0.
    apply refine_E1E2_interp_global_strict; auto.
    apply refine_E1E2_L0_strict_interp_intrinsics; auto.
  Qed.

  Lemma refine_E1E2_12_strict :
    forall t1 t2 l1 l2,
      refine_E1E2_L1_strict t1 t2 ->
      local_stack_refine_strict l1 l2 ->
      refine_E1E2_L2_strict (interp_local_stack t1 l1) (interp_local_stack t2 l2).
  Proof.
    intros t1 t2 g1 g2 RL1 GENVS.
    red in RL1.
    apply refine_E1E2_interp_local_stack_strict; auto.
  Qed.

  Import InterpMemoryProp.
  Lemma refine_E1E2_23_strict :
    forall t1 t2 sid m1 m2,
      refine_E1E2_L2_strict t1 t2 ->
      MemState_refine m1 m2 ->
      refine_E1E2_L3_strict (InfMemInterp.interp_memory_prop eq t1 sid m1) (FinMemInterp.interp_memory_prop eq t2 sid m2).
  Proof.
    intros t1 t2 sid m1 m2 RL2.

  (*
    h1 and h2 are handlers

    (* h2 refines h1 *)
    (forall e,
    refine_E1E2_L3 (h1 e) (h2 e)) ->
    forall u : itree,
    refine_E1E2_L3 (interp_prop h1 u) (interp_prop h2 u)

    Need something a bit more general like rutt.

    (forall e1 e2,
    refine_events e1 e2 ->
    refine_E1E2_L3 (h1 e1) (h2 e2)) ->
    forall u1 u2 : itree,
    rutt refine_events refine_dvalue eq u1 u2 ->
    refine_E1E2_L3 (interp_prop h1 u1) (interp_prop h2 u2)


    (forall e1 e2,
    refine_events e1 e2 ->
    refine_E1E2_L4 (h1 e1) (h2 e2)) ->
    forall u1 u2 : itree,
    refine_E1E2_L3 u1 u2 ->
    refine_E1E2_L4 (interp_prop h1 u1) (interp_prop h2 u2)

   *)

    (* I'll probably need something about MemMonad_valid_state eventually... *)
  Admitted.

  Lemma refine_E1E2_34_strict :
    forall t1 t2,
      refine_E1E2_L3_strict t1 t2 ->
      refine_E1E2_L4_strict (InfLLVM.Pick.model_undef eq t1) (FinLLVM.Pick.model_undef eq t2).
  Proof.
    intros t1 t2 RL3.
    red.
  Admitted.

  Lemma refine_E1E2_45_strict :
    forall t1 t2,
      refine_E1E2_L4_strict t1 t2 ->
      refine_E1E2_L5_strict (model_UB t1) (model_UB t2).
  Proof.
    intros t1 t2 RL4.
    red.
  Admitted.

  Lemma refine_E1E2_56_strict :
    forall t1 t2,
      refine_E1E2_L5_strict t1 t2 ->
      refine_E1E2_L6_strict (refine_OOM eq t1) (refine_OOM eq t2).
  Proof.
    intros t1 t2 RL4.
    red.
  Admitted.


  From Vellvm Require Import Tactics.

  From ITree Require Import
        ITree
        Basics.Monad
        Events.StateFacts
        Eq.Eqit.

  Import TranslateFacts.
  Import TopLevelBigIntptr.
  Import TopLevel64BitIntptr.
  Import InterpreterStackBigIntptr.
  Import TopLevelRefinements64BitIntptr.

  Ltac force_rewrite H :=
    let HB := fresh "HB" in
    pose proof @H as HB; eapply bisimulation_is_eq in HB; rewrite HB; clear HB.

  Tactic Notation "force_rewrite" constr(H) "in" hyp(H') :=
    let HB := fresh "HB" in
    pose proof @H as HB; eapply bisimulation_is_eq in HB; rewrite HB in H'; clear HB.


  (* TODO: this is going to be a big one *)
  Theorem model_E1E2_L0_sound :
    forall (p : LLVM_syntax),
      model_E1E2_L0 p p.
  Proof.
    intros p.
    unfold model_E1E2_L0.
    red.
    unfold refine_L0.
    unfold L0_convert_tree_strict'.
    unfold L0_convert_tree_strict.

    (* exists (FinInfTC.L0_convert_tree_strict' EC2.DVC.dvalue_convert *)
    (*      (denote_vellvm (DynamicTypes.DTYPE_I 32) "main" main_args *)
    (*         (TypToDtyp.convert_types (CFG.mcfg_of_tle p)))). *)

    (* split. *)
    (* - (* src' may have additional OOM *) *)
    (*   (* I think this pretty much has to be by induction over the syntax? *) *)
    (*   admit. *)
    (* - (* src' when converted agrees with target *) *)
    (*   (* Target may just be OOM for all we know *) *)
    (*   red. *)
    (*   setoid_rewrite L0_convert_safe. *)
    (*   reflexivity. *)
  Admitted.

  Theorem model_E1E2_L1_sound :
    forall (p : LLVM_syntax),
      model_E1E2_L1 p p.
  Proof.
    intros p.
    red.

  (* Maybe I need some lemmas akin to these:

    Lemma refine_34 : forall t1 t2,
        refine_L3 t1 t2 -> refine_L4 (model_undef refine_res3 t1) (model_undef refine_res3 t2).

    But for crossing the infinite / finite boundary...

   *)
    unfold model_oom_L1.
    unfold model_gen_oom_L1.
    unfold interp_mcfg1.

    apply refine_E1E2_01_strict.
    { (* Still need to deal with interp_intrinsics... *)
      apply model_E1E2_L0_sound.
    }

    apply global_refine_strict_empty.
  Qed.

  Theorem model_E1E2_L2_sound :
    forall (p : LLVM_syntax),
      model_E1E2_L2 p p.
  Proof.
    intros p.
    red.
    apply refine_E1E2_12_strict; [| apply local_stack_refine_strict_empty].
    apply model_E1E2_L1_sound.
  Qed.

  Theorem model_E1E2_L3_sound :
    forall (p : LLVM_syntax),
      model_E1E2_L3 p p.
  Proof.
    intros p.
    red.
    apply refine_E1E2_23_strict; [| apply MemState_refine_initial].
    apply model_E1E2_L2_sound.
  Qed.

  Theorem model_E1E2_L4_sound :
    forall (p : LLVM_syntax),
      model_E1E2_L4 p p.
  Proof.
    intros p.
    red.
    apply refine_E1E2_34_strict.
    apply model_E1E2_L3_sound.
  Qed.

  Theorem model_E1E2_L5_sound :
    forall (p : LLVM_syntax),
      model_E1E2_L5 p p.
  Proof.
    intros p.
    red.
    apply refine_E1E2_45_strict.
    apply model_E1E2_L4_sound.
  Qed.

  Theorem model_E1E2_L6_sound :
    forall (p : LLVM_syntax),
      model_E1E2_L6 p p.
  Proof.
    intros p.
    red.
    apply refine_E1E2_56_strict.
    apply model_E1E2_L5_sound.
  Qed.

End InfiniteToFinite.
