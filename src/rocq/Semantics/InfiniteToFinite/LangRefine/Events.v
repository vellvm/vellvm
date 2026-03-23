From Stdlib Require Import
  Lia
  ZArith
  List
  String
  Program.Equality.

From ITree Require Import
  ITree
  HeterogeneousRelations
  Rutt
  TranslateFacts
  Eqit.

From ExtLib Require Import
  Structures.Monads
  Structures.Functor.

Require Import Paco.paco.

From Vellvm.Semantics Require Import
  MemoryAddress
  VellvmIntegers
  DynamicValues
  InterpretationStack
  TopLevel
  LLVMEvents.

From Vellvm.Semantics.InfiniteToFinite.Conversions Require Import
  BaseConversions
  DvalueConversions
  EventConversions.

From Vellvm.Utils Require Import
  Error
  Tactics
  Monads
  MapMonadExtra
  OOMRutt
  OOMRuttProps
  AListFacts
  PropT
  VellvmRelations.

Import MonadNotation.
Import ListNotations.

Module Type EventRefine
  (IS1 : InterpreterStack)
  (IS2 : InterpreterStack)
  (LLVM1 : LLVMTopLevel IS1)
  (LLVM2 : LLVMTopLevel IS2)
  (AC1 : AddrConvert IS1.LP.ADDR IS1.LP.PTOI IS2.LP.ADDR IS2.LP.PTOI)
  (AC2 : AddrConvert IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI)
  (DVC : DVConvert IS1.LP IS2.LP AC1)
  (DVCrev : DVConvert IS2.LP IS1.LP AC2)
  (EC : EventConvert IS1.LP IS2.LP AC1 AC2 DVC DVCrev).
  Import DVC.
  Import IS2.LP.DV.
  Import IS2.LLVM.D.
  Import EC.

  (**  Converting state between the two languages *)

  (*
  Definition convert_global_env_lazy (g : IS1.LLVM.Global.global_env) : IS2.LLVM.Global.global_env
    := map (fun '(k, dv) => (k, dvalue_convert_lazy dv)) g.

  Definition convert_local_env_lazy (l : IS1.LLVM.Local.local_env) : IS2.LLVM.Local.local_env
    := map (fun '(k, uv) => (k, uvalue_convert_lazy uv)) l.
   *)

  Definition convert_global_env_strict (g : IS1.LLVM.Global.global_env) : OOM IS2.LLVM.Global.global_env
    := map_monad (fun '(k, dv) => dv' <- dvalue_convert_strict dv;;
                               ret (k, dv')) g.

  Definition convert_local_env_strict (l : IS1.LLVM.Local.local_env) : OOM IS2.LLVM.Local.local_env
    := map_monad (fun '(k, uv) => uv' <- uvalue_convert_strict uv;;
                               ret (k, uv')) l.

  Definition convert_stack_frame_strict (sf : IS1.LLVM.Stack.lstack_frame) : OOM IS2.LLVM.Stack.lstack_frame
    := match sf with
       | Build_stack_frame stack_vars stack_handler stack_exc stack_loc =>
           stack_vars' <- convert_local_env_strict stack_vars;;
           stack_exc' <-
             match stack_exc with
             | None => ret None
             | Some exc => fmap Some (uvalue_convert_strict exc)
             end;;
           ret (Build_stack_frame stack_vars' stack_handler stack_exc' stack_loc)
       end.

  (*
  Definition convert_stack_lazy (s : @stack IS1.LLVM.Local.local_env) : (@stack IS2.LLVM.Local.local_env)
    := map convert_local_env_lazy s.
   *)

  Definition convert_stack_strict (s : IS1.LLVM.Stack.lstack) : OOM IS2.LLVM.Stack.lstack
    := map_monad convert_stack_frame_strict s.

  (** Refinement between states *)
  (* Not sure if this is right...

     Presumably if [g1] OOMs when converted, we wouldn't have a [g2]
     anyway?
   *)
  (*
  Definition global_refine_lazy (g1 : IS1.LLVM.Global.global_env) (g2 : IS2.LLVM.Global.global_env) : Prop
    := alist_refine dvalue_refine_lazy g1 g2.

  Lemma global_refine_lazy_empty :
    global_refine_lazy [] [].
  Proof.
    apply alist_refine_empty.
  Qed.
   *)

  Definition global_refine_strict (g1 : IS1.LLVM.Global.global_env) (g2 : IS2.LLVM.Global.global_env) : Prop
    := alist_refine dvalue_refine_strict g1 g2.

  Lemma global_refine_strict_empty :
    global_refine_strict [] [].
  Proof.
    apply alist_refine_empty.
  Qed.

  Lemma global_refine_strict_add :
    forall rid genv1 genv2 dv1 dv2,
      global_refine_strict genv1 genv2 ->
      dvalue_refine_strict dv1 dv2 ->
      global_refine_strict (FMapAList.alist_add rid dv1 genv1) (FMapAList.alist_add rid dv2 genv2).
  Proof.
    intros rid genv1 genv2 dv1 dv2 H H0.
    eapply alist_refine_add with (x:=(rid, dv1)) (y:=(rid, dv2)); cbn; eauto.
  Qed.

  (*
  Definition local_refine_lazy (l1 : IS1.LLVM.Local.local_env) (l2 : IS2.LLVM.Local.local_env) : Prop
    := alist_refine uvalue_refine_lazy l1 l2.

  Lemma local_refine_lazy_empty :
    local_refine_lazy [] [].
  Proof.
    apply alist_refine_empty.
  Qed.
   *)

  Definition local_refine_strict (l1 : IS1.LLVM.Local.local_env) (l2 : IS2.LLVM.Local.local_env) : Prop
    := alist_refine uvalue_refine_strict l1 l2.

  Lemma local_refine_strict_empty :
    local_refine_strict [] [].
  Proof.
    apply alist_refine_empty.
  Qed.

  (*
  Definition stack_refine_lazy (s1 : @stack IS1.LLVM.Local.local_env) (s2 : @stack IS2.LLVM.Local.local_env) : Prop
    := Forall2 local_refine_lazy s1 s2.

  Lemma stack_refine_lazy_empty :
    stack_refine_lazy [] [].
  Proof.
    constructor.
  Qed.
   *)

  Definition stack_frame_refine_strict (l1 : IS1.LLVM.Stack.lstack_frame) (l2 : IS2.LLVM.Stack.lstack_frame) : Prop
    := match l1, l2 with
       | Build_stack_frame stack_vars1 stack_handler1 stack_exc1 stack_loc1,
         Build_stack_frame stack_vars2 stack_handler2 stack_exc2 stack_loc2 =>
           local_refine_strict stack_vars1 stack_vars2 /\
             stack_handler1 = stack_handler2 /\
             Rocqlib.option_rel uvalue_refine_strict stack_exc1 stack_exc2
       end.

  Lemma stack_frame_refine_strict_empty :
    stack_frame_refine_strict (Build_stack_frame [] None None None) (Build_stack_frame [] None None None).
  Proof.
    repeat split; auto.
    apply Rocqlib.option_rel_none.
  Qed.

  Definition stack_refine_strict (s1 : IS1.LLVM.Stack.lstack) (s2 : IS2.LLVM.Stack.lstack) : Prop
    := Forall2 stack_frame_refine_strict s1 s2.

  Lemma stack_refine_strict_empty :
    stack_refine_strict [] [].
  Proof.
    constructor.
  Qed.

  (*
  Definition local_stack_refine_lazy
    (ls1 : (IS1.LLVM.Local.local_env * @stack IS1.LLVM.Local.local_env)%type)
    (ls2 : (IS2.LLVM.Local.local_env * @stack IS2.LLVM.Local.local_env)%type)
    : Prop :=
    match ls1, ls2 with
    | (l1, s1), (l2, s2) =>
        local_refine_lazy l1 l2 /\ stack_refine_lazy s1 s2
    end.

  Lemma local_stack_refine_lazy_empty :
    local_stack_refine_lazy ([], []) ([], []).
  Proof.
    cbn.
    split.
    apply local_refine_lazy_empty.
    apply stack_refine_lazy_empty.
  Qed.
   *)

  Definition local_stack_refine_strict
    (ls1 : (IS1.LLVM.Stack.lstack_frame * IS1.LLVM.Stack.lstack)%type)
    (ls2 : (IS2.LLVM.Stack.lstack_frame * IS2.LLVM.Stack.lstack)%type)
    : Prop :=
    match ls1, ls2 with
    | (l1, s1), (l2, s2) =>
        stack_frame_refine_strict l1 l2 /\ stack_refine_strict s1 s2
    end.

  Lemma local_stack_refine_strict_empty :
    local_stack_refine_strict ((Build_stack_frame [] None None None), []) ((Build_stack_frame [] None None None), []).
  Proof.
    cbn.
    split.
    apply stack_frame_refine_strict_empty.
    apply stack_refine_strict_empty.
  Qed.

  (* TODO: move this *)
  Lemma local_stack_refine_strict_add :
    forall rid lenv1 lenv2 uv1 uv2,
      local_refine_strict lenv1 lenv2 ->
      uvalue_refine_strict uv1 uv2 ->
      local_refine_strict (FMapAList.alist_add rid uv1 lenv1) (FMapAList.alist_add rid uv2 lenv2).
  Proof.
    intros rid lenv1 lenv2 uv1 uv2 H H0.
    eapply alist_refine_add with (x:=(rid, uv1)) (y:=(rid, uv2)); cbn; eauto.
  Qed.

  (* TODO: move this *)
  Lemma stack_refine_strict_add :
    forall s1 s2 lenv1 lenv2,
      stack_refine_strict s1 s2 ->
      stack_frame_refine_strict lenv1 lenv2 ->
      stack_refine_strict (lenv1 :: s1) (lenv2 :: s2).
  Proof.
    intros s1 s2 lenv1 lenv2 H H0.
    red.
    apply Forall2_cons; auto.
  Qed.

  (** OOM Refinements *)
  Lemma Returns_ExternalCall_L0 :
    forall d f t args,
      @Returns L01 DV1.dvalue d (trigger (ExternalCall t f args)).
  Proof.
    intros d f t args.

    eapply ReturnsVis.
    unfold trigger.
    reflexivity.
    cbn.
    constructor.
    reflexivity.
  Qed.

  (* Opaque FinPROV.initial_provenance. *)
  (* Opaque InfPROV.initial_provenance. *)
  (* Opaque dvalue_convert_lazy. *)
  (* Opaque uvalue_convert_lazy. *)
  (* Opaque dvalue_refine_lazy. *)
  (* Opaque uvalue_refine_lazy. *)
  (* Opaque DVCrev.dvalue_convert_lazy. *)
  (* Opaque DVCrev.uvalue_convert_lazy. *)
  (* Opaque DVCrev.dvalue_refine_lazy. *)
  (* Opaque DVCrev.uvalue_refine_lazy. *)
  (* Opaque dvalue_convert_strict. *)
  (* Opaque uvalue_convert_strict. *)
  (* Opaque dvalue_refine_strict. *)
  (* Opaque uvalue_refine_strict. *)
  (* Opaque DVCrev.dvalue_convert_strict. *)
  (* Opaque DVCrev.uvalue_convert_strict. *)
  (* Opaque DVCrev.dvalue_refine_strict. *)
  (* Opaque DVCrev.uvalue_refine_strict. *)

  (** Model *)
  Import DynamicTypes TypToDtyp CFG.

  
  Definition external_call_refine_strict {A B} (e1 : ExternalCallE DV1.dvalue DV1.uvalue A) (e2 : ExternalCallE DV2.dvalue DV2.uvalue B) : Prop.
    (* External Calls *)
    refine (match e1, e2 with
            | ExternalCall dt1 f1 args1, ExternalCall dt2 f2 args2 =>
                (* Doesn't say anything about return value... *)
                dt1 = dt2 /\
                  uvalue_refine_strict f1 f2 /\
                  Forall2 dvalue_refine_strict args1 args2
            | IO_stdout msg1, IO_stdout msg2 =>
                msg1 = msg2
            | IO_stderr msg1, IO_stderr msg2 =>
                msg1 = msg2
            | _, _ =>
                False
            end).
  Defined.

  Definition intrinsic_refine_strict {A B} (e1 : IntrinsicE DV1.dvalue DV1.uvalue A) (e2 : IntrinsicE DV2.dvalue DV2.uvalue B) : Prop.
    refine
      (match e1, e2 with
       | Intrinsic dt1 name1 args1, Intrinsic dt2 name2 args2 =>
           dt1 = dt2 /\
             name1 = name2 /\
             Forall2 dvalue_refine_strict args1 args2
       end).
  Defined.

  Definition globalE_refine_strict {A B} (e1 : GlobalE LLVMAst.raw_id DV1.dvalue A) (e2 : GlobalE LLVMAst.raw_id DV2.dvalue B) : Prop.
    (* Globals *)
    { inversion e1.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_refine_strict dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }
  Defined.

  Definition localE_refine_strict {A B} (e1 : LocalE LLVMAst.raw_id DV1.uvalue A) (e2 : LocalE LLVMAst.raw_id DV2.uvalue B) : Prop.
    (* Locals *)
    { inversion e1.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_refine_strict dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }
  Defined.

  Definition stackE_refine_strict {A B} (e1 : StackE LLVMAst.raw_id DV1.uvalue DV1.uvalue A) (e2 : StackE LLVMAst.raw_id DV2.uvalue DV2.uvalue B) : Prop.
    (* Stack *)
    { inversion e1.
      - (* Stack Push *)
        destruct e2 eqn:HE2.
        1: apply (local_refine_strict args args0).
        all: apply False.
      - (* Stack Pop *)
        destruct e2 eqn:HE2.
        2: apply True.
        all: apply False.
      - (* StackSetHandler *)
        destruct e2 eqn:HE2.
        3: apply (Rocqlib.option_rel eq H o).
        all: apply False.
      - (* StackHandler *)
        destruct e2 eqn:HE2.
        4: apply True.
        all: apply False.
      - (* StackRaise *)
        destruct e2 eqn:HE2.
        5: apply (uvalue_refine_strict H u).
        all: apply False.
      - (* StackGetExc *)
        destruct e2 eqn:HE2.
        6: apply True.
        all: apply False.        
    }
  Defined.

  Definition memoryE_refine_strict {A B} (e1 : MemoryE DV1.dvalue DV1.uvalue A) (e2 : MemoryE DV2.dvalue DV2.uvalue B) : Prop.
    (* MemoryE *)
    { inversion e1.
      - (* MemPush *)
        destruct e2 eqn:HE2.
        2-5: apply False.

        apply True.
      - (* MemPop *)
        destruct e2 eqn:HE2.
        2: apply True.
        all: apply False.
      - (* Alloca *)
        destruct e2 eqn:HE2.
        1,2,4,5: apply False.

        apply (t = t0 /\
                 num_elements = num_elements0 /\
                 align = align0).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_refine_strict a a0).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_strict a a0 /\
                 uvalue_refine_strict v v0).
    }
  Defined.

  Definition pickE_refine_strict {A B} (e1 : PickUvalueE DV1.dvalue DV1.uvalue A) (e2 : PickUvalueE DV2.dvalue DV2.uvalue B) : Prop.
    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      - (* pickUnique *)
        subst.
        destruct e2.
        + apply (uvalue_refine_strict x x0).
        + exact False.
        + exact False.
      - (* pickNonPoison *)
        subst.
        destruct e2.
        + exact False.
        + apply (uvalue_refine_strict x x0).
        + exact False.
      - (* pick *)
        subst.
        destruct e2.
        + exact False.
        + exact False.
        + apply (uvalue_refine_strict x x0).
    }
  Defined.

  Definition oomE_refine_strict {A B} (e1 : OOME A) (e2 : OOME B) : Prop.
    (* OOME *)
    { apply True.
    }
  Defined.

  Definition llvmExcE_refine_strict {A B} (e1 : LLVMExcE DV1.uvalue A) (e2 : LLVMExcE DV2.uvalue B) : Prop.
    (* LLVMExcE *)
    { destruct e1 as [exc1].
      destruct e2 as [exc2].
      apply (uvalue_refine_strict exc1 exc2).
    }
  Defined.

  Definition ubE_refine_strict {A B} (e1 : UBE A) (e2 : UBE B) : Prop.
    (* UBE *)
    { apply True.
    }
  Defined.

  Definition debugE_refine_strict {A B} (e1 : DebugE A) (e2 : DebugE B) : Prop.
    (* DebugE *)
    { refine
        (match e1, e2 with
         | Debug e1_msg, Debug e2_msg =>
             e1_msg = e2_msg
         end).
    }
  Defined.

  Definition failureE_refine_strict {A B} (e1 : FailureE A) (e2 : FailureE B) : Prop.
    (* FailureE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }
  Defined.

  Definition event_refine_strict A B (e1 : L0 DV1.dvalue DV1.uvalue A) (e2 : L0 DV2.dvalue DV2.uvalue B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                external_call_refine_strict e1 e2
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                intrinsic_refine_strict e1 e2
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                globalE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inl1 (inl1 e1)))), inr1 (inr1 (inr1 (inl1 (inl1 e2)))) =>
                localE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inl1 (inr1 e1)))), inr1 (inr1 (inr1 (inl1 (inr1 e2)))) =>
                stackE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                memoryE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                pickE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))) =>
                oomE_refine_strict e0 e1
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                llvmExcE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))))) =>
                ubE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))))) =>
                debugE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1))))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2))))))))) =>
                failureE_refine_strict e1 e2
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).
  Defined.

  Definition L1_refine_strict A B (e1 : L1 DV1.dvalue DV1.uvalue A) (e2 : L1 DV2.dvalue DV2.uvalue B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                external_call_refine_strict e1 e2
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                intrinsic_refine_strict e1 e2
            | inr1 (inr1 (inl1 (inl1 e1))), inr1 (inr1 (inl1 (inl1 e2))) =>
                localE_refine_strict e1 e2
            | inr1 (inr1 (inl1 (inr1 e1))), inr1 (inr1 (inl1 (inr1 e2))) =>
                stackE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                memoryE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                pickE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))) =>
                oomE_refine_strict e0 e1
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                llvmExcE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                ubE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))))) =>
                debugE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))))) =>
                failureE_refine_strict e1 e2
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).
  Defined.

  Definition L2_refine_strict A B (e1 : L2 DV1.dvalue DV1.uvalue A) (e2 : L2 DV2.dvalue DV2.uvalue B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                external_call_refine_strict e1 e2
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                intrinsic_refine_strict e1 e2
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                memoryE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                pickE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inl1 e0)))), inr1 (inr1 (inr1 (inr1 (inl1 e1)))) =>
                oomE_refine_strict e0 e1
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                llvmExcE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                ubE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                debugE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2))))))) =>
                failureE_refine_strict e1 e2
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).
  Defined.

  Definition L3_refine_strict A B (e1 : L3 DV1.dvalue DV1.uvalue A) (e2 : L3 DV2.dvalue DV2.uvalue B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                external_call_refine_strict e1 e2
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                pickE_refine_strict e1 e2
            | inr1 (inr1 (inl1 e0)), inr1 (inr1 (inl1 e1)) =>
                oomE_refine_strict e0 e1
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                llvmExcE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                ubE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                debugE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2))))) =>
                failureE_refine_strict e1 e2
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).
  Defined.

  Definition L4_refine_strict A B (e1 : L4 DV1.dvalue DV1.uvalue A) (e2 : L4 DV2.dvalue DV2.uvalue B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                external_call_refine_strict e1 e2
            | inr1 (inl1 e0), inr1 (inl1 e1) =>
                oomE_refine_strict e0 e1
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                llvmExcE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                ubE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                debugE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inr1 e1)))), inr1 (inr1 (inr1 (inr1 (inr1 e2)))) =>
                failureE_refine_strict e1 e2
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).
  Defined.


  Definition external_call_res_refine_strict {A B} (e1 : ExternalCallE DV1.dvalue DV1.uvalue A) (res1 : A) (e2 : ExternalCallE DV2.dvalue DV2.uvalue B) (res2 : B) : Prop.
    (* External Calls *)
    inv e1.
    - (* ExternalCall *)
      inv e2.
      { apply (t = t0 /\
                 uvalue_refine_strict f f0 /\
                 Forall2 dvalue_refine_strict args args0 /\
                 dvalue_refine_strict res1 res2
              ).
      }
      all: exact False. (* Mismatch of event types *)
    - (* Stdout *)
      inv e2.
      2: {
        apply (str = str0).
      }
      all: exact False. (* Mismatch of event types *)
    - (* Stderr *)
      inv e2.
      3: {
        apply (str = str0).
      }
      all: exact False. (* Mismatch of event types *)
  Defined.

  Definition intrinsic_res_refine_strict {A B} (e1 : IntrinsicE DV1.dvalue DV1.uvalue A) (res1 : A) (e2 : IntrinsicE DV2.dvalue DV2.uvalue B) (res2 : B) : Prop.
    (* Intrinsics *)
    inv e1.
    inv e2.
    apply (t = t0 /\
             f = f0 /\
             Forall2 dvalue_refine_strict args args0 /\
             sum_rel uvalue_refine_strict dvalue_refine_strict res1 res2
          ).
  Defined.

  Definition globalE_res_refine_strict {A B} (e1 : GlobalE LLVMAst.raw_id DV1.dvalue A) (res1 : A) (e2 : GlobalE LLVMAst.raw_id DV2.dvalue B) (res2 : B) : Prop.
    (* Globals *)
    { inversion e1; subst.
      - (* Global write *)
        inversion e2.
        + apply (id = id0 /\
                   dvalue_refine_strict dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                   dvalue_refine_strict res1 res2
                ).
    }
  Defined.

  Definition localE_res_refine_strict {A B} (e1 : LocalE LLVMAst.raw_id DV1.uvalue A) (res1 : A) (e2 : LocalE LLVMAst.raw_id DV2.uvalue B) (res2 : B) : Prop.
    (* Locals *)
    { inversion e1; subst.
      - (* Local write *)
        inversion e2.
        + apply (id = id0 /\
                   uvalue_refine_strict dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                uvalue_refine_strict res1 res2).
    }
  Defined.

  Definition stackE_res_refine_strict {A B} (e1 : StackE LLVMAst.raw_id DV1.uvalue DV1.uvalue A) (res1 : A) (e2 : StackE LLVMAst.raw_id DV2.uvalue DV2.uvalue B) (res2 : B) : Prop.
    (* Stack *)
    { inversion e1.
      - (* Stack Push *)
        inversion e2; subst.
        1: apply (local_refine_strict args args0).
        all: apply False.
      - (* Stack Pop *)
        destruct e2 eqn:HE2.
        2: apply True.
        all: apply False.
      - (* StackSetHandler *)
        destruct e2 eqn:HE2.
        3: apply (Rocqlib.option_rel eq H o).
        all: apply False.
      - (* StackHandler *)
        inversion e2; subst.
        4: apply (res1 = res2).
        all: apply False.
      - (* StackRaise *)
        inversion e2; subst.
        5: apply (uvalue_refine_strict H H1).
        all: apply False.
      - (* StackGetExc *)
        inversion e2; subst.
        6: apply (Rocqlib.option_rel uvalue_refine_strict res1 res2).
        all: apply False.        
    }
  Defined.

  Definition memoryE_res_refine_strict {A B} (e1 : MemoryE DV1.dvalue DV1.uvalue A) (res1 : A) (e2 : MemoryE DV2.dvalue DV2.uvalue B) (res2 : B) : Prop.
    (* MemoryE *)
    { inversion e1; subst.
      - (* MemPush *)
        inversion e2; subst.
        2-5: apply False.

        apply True.
      - (* MemPop *)
        inversion e2; subst.
        2: apply True.
        all: apply False.
      - (* Alloca *)
        inversion e2; subst.
        1,2,4,5: apply False.

        apply (t = t0 /\
                 num_elements = num_elements0 /\
                 align = align0 /\
                 dvalue_refine_strict res1 res2).
      - (* Load *)
        inversion e2; subst.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_refine_strict a a0 /\
                 uvalue_refine_strict res1 res2).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_strict a a0 /\
                 uvalue_refine_strict v v0).
    }
  Defined.

  Definition pickE_res_refine_strict {A B} (e1 : PickUvalueE DV1.dvalue DV1.uvalue A) (res1 : A) (e2 : PickUvalueE DV2.dvalue DV2.uvalue B) (res2 : B) : Prop.
    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      - (* pickUnique *)
        inversion e2; subst.
        + destruct res1 as [r1 P1].
          destruct res2 as [r2 P2].
          apply (uvalue_refine_strict x x0 /\ dvalue_refine_strict r1 r2).
        + exact False.
        + exact False.
      - (* pickNonPoison *)
        inversion e2; subst.
        + exact False.
        + destruct res1 as [r1 P1].
          destruct res2 as [r2 P2].
          apply (uvalue_refine_strict x x0 /\ dvalue_refine_strict r1 r2).
        + exact False.
      - (* pick *)
        inversion e2; subst.
        + exact False.
        + exact False.
        + destruct res1 as [r1 P1].
          destruct res2 as [r2 P2].
          apply (uvalue_refine_strict x x0 /\ dvalue_refine_strict r1 r2).
    }
  Defined.

  Definition oomE_res_refine_strict {A B} (e1 : OOME A) (res1 : A) (e2 : OOME B) (res2 : B) : Prop.
    (* OOME *)
    { apply True.
    }
  Defined.

  Definition llvmExcE_res_refine_strict {A B} (e1 : LLVMExcE DV1.uvalue A) (res1 : A) (e2 : LLVMExcE DV2.uvalue B) (res2 : B) : Prop.
    (* LLVMExcE *)
    { inversion e1; inversion e2; subst.
      apply (uvalue_refine_strict H H1).
    }
  Defined.

  Definition ubE_res_refine_strict {A B} (e1 : UBE A) (res1 : A) (e2 : UBE B) (res2 : B) : Prop.
    (* UBE *)
    { apply True.
    }
  Defined.

  Definition debugE_res_refine_strict {A B} (e1 : DebugE A) (res1 : A) (e2 : DebugE B) (res2 : B) : Prop.
    (* DebugE *)
    { refine
        (match e1, e2 with
         | Debug e1_msg, Debug e2_msg =>
             e1_msg = e2_msg
         end).
    }
  Defined.

  Definition failureE_res_refine_strict {A B} (e1 : FailureE A) (res1 : A) (e2 : FailureE B) (res2 : B) : Prop.
    (* FailureE *)
    { inversion e1; inversion e2; subst.
      exact True.
    }
  Defined.

  Lemma external_call_res_refine_strict_external_call_refine_strict {A B} (e1 : ExternalCallE DV1.dvalue DV1.uvalue A) (res1 : A) (e2 : ExternalCallE DV2.dvalue DV2.uvalue B) (res2 : B) :
    external_call_res_refine_strict e1 res1 e2 res2 -> external_call_refine_strict e1 e2.
  Proof.
    intros RES; red; red in RES.
    repeat (break_match_goal; subst; cbn in *; eauto);
      tauto.
  Qed.
  
  Lemma intrinsic_res_refine_strict_intrinsic_refine_strict {A B} (e1 : IntrinsicE DV1.dvalue DV1.uvalue A) (res1 : A) (e2 : IntrinsicE DV2.dvalue DV2.uvalue B) (res2 : B) :
    intrinsic_res_refine_strict e1 res1 e2 res2 -> intrinsic_refine_strict e1 e2.
  Proof.
    intros RES; red; red in RES.
    repeat (break_match_goal; subst; cbn in *; eauto);
      tauto.
  Qed.

  Lemma globalE_res_refine_strict_globalE_refine_strict {A B} (e1 : GlobalE LLVMAst.raw_id DV1.dvalue A) (res1 : A) (e2 : GlobalE LLVMAst.raw_id DV2.dvalue B) (res2 : B) :
    globalE_res_refine_strict e1 res1 e2 res2 -> globalE_refine_strict e1 e2.
  Proof.
    intros RES; red; red in RES.
    repeat (break_match_goal; subst; cbn in *; eauto);
      tauto.
  Qed.

  Lemma localE_res_refine_strict_localE_refine_strict {A B} (e1 : LocalE LLVMAst.raw_id DV1.uvalue A) (res1 : A) (e2 : LocalE LLVMAst.raw_id DV2.uvalue B) (res2 : B) :
    localE_res_refine_strict e1 res1 e2 res2 -> localE_refine_strict e1 e2.
  Proof.
    intros RES; red; red in RES.
    repeat (break_match_goal; subst; cbn in *; eauto);
      tauto.
  Qed.

  Lemma stackE_res_refine_strict_stackE_refine_strict {A B} (e1 : StackE LLVMAst.raw_id DV1.uvalue DV1.uvalue A) (res1 : A) (e2 : StackE LLVMAst.raw_id DV2.uvalue DV2.uvalue B) (res2 : B) :
    stackE_res_refine_strict e1 res1 e2 res2 -> stackE_refine_strict e1 e2.
  Proof.
    intros RES; red; red in RES.
    repeat (break_match_goal; subst; cbn in *; eauto);
      tauto.
  Qed.

  Lemma memoryE_res_refine_strict_memoryE_refine_strict {A B} (e1 : MemoryE DV1.dvalue DV1.uvalue A) (res1 : A) (e2 : MemoryE DV2.dvalue DV2.uvalue B) (res2 : B) :
    memoryE_res_refine_strict e1 res1 e2 res2 -> memoryE_refine_strict e1 e2.
  Proof.
    intros RES; red; red in RES.
    repeat (break_match_goal; subst; cbn in *; eauto);
      tauto.
  Qed.

  Lemma pickE_res_refine_strict_pickE_refine_strict {A B} (e1 : PickUvalueE DV1.dvalue DV1.uvalue A) (res1 : A) (e2 : PickUvalueE DV2.dvalue DV2.uvalue B) (res2 : B) :
    pickE_res_refine_strict e1 res1 e2 res2 -> pickE_refine_strict e1 e2.
  Proof.
    destruct e1, e2; destruct res1, res2; cbn in *;
    intros RES; cbn in *;
    repeat (break_match_goal; subst; cbn in *; eauto);
      try tauto.
  Qed.

  Lemma oomE_res_refine_strict_oomE_refine_strict {A B} (e1 : OOME A) (res1 : A) (e2 : OOME B) (res2 : B) :
    oomE_res_refine_strict e1 res1 e2 res2 -> oomE_refine_strict e1 e2.
  Proof.
    intros RES; red; red in RES.
    repeat (break_match_goal; subst; cbn in *; eauto);
      tauto.
  Qed.

  Lemma llvmExcE_res_refine_strict_llvmExcE_refine_strict {A B} (e1 : LLVMExcE DV1.uvalue A) (res1 : A) (e2 : LLVMExcE DV2.uvalue B) (res2 : B) :
    llvmExcE_res_refine_strict e1 res1 e2 res2 -> llvmExcE_refine_strict e1 e2.
  Proof.
    intros RES; red; red in RES.
    repeat (break_match_goal; subst; cbn in *; eauto);
      tauto.
  Qed.

  Lemma ubE_res_refine_strict_ubE_refine_strict {A B} (e1 : UBE A) (res1 : A) (e2 : UBE B) (res2 : B) :
    ubE_res_refine_strict e1 res1 e2 res2 -> ubE_refine_strict e1 e2.
  Proof.
    intros RES; red; red in RES.
    repeat (break_match_goal; subst; cbn in *; eauto);
      tauto.
  Qed.
  
  Lemma debugE_res_refine_strict_debugE_refine_strict {A B} (e1 : DebugE A) (res1 : A) (e2 : DebugE B) (res2 : B) :
    debugE_res_refine_strict e1 res1 e2 res2 -> debugE_refine_strict e1 e2.
  Proof.
    intros RES; red; red in RES.
    repeat (break_match_goal; subst; cbn in *; eauto);
      tauto.
  Qed.
  
  Lemma failureE_res_refine_strict_failureE_refine_strict {A B} (e1 : FailureE A) (res1 : A) (e2 : FailureE B) (res2 : B) :
    failureE_res_refine_strict e1 res1 e2 res2 -> failureE_refine_strict e1 e2.
  Proof.
    intros RES; red; red in RES.
    repeat (break_match_goal; subst; cbn in *; eauto);
      tauto.
  Qed.

  #[global] Hint Resolve
    external_call_res_refine_strict_external_call_refine_strict
    intrinsic_res_refine_strict_intrinsic_refine_strict
    globalE_res_refine_strict_globalE_refine_strict
    localE_res_refine_strict_localE_refine_strict
    stackE_res_refine_strict_stackE_refine_strict
    memoryE_res_refine_strict_memoryE_refine_strict
    pickE_res_refine_strict_pickE_refine_strict
    oomE_res_refine_strict_oomE_refine_strict
    llvmExcE_res_refine_strict_llvmExcE_refine_strict
    ubE_res_refine_strict_ubE_refine_strict
    debugE_res_refine_strict_debugE_refine_strict
    failureE_res_refine_strict_failureE_refine_strict : REFINE_DB.   

  Definition event_res_refine_strict A B (e1 : L0 DV1.dvalue DV1.uvalue A) (res1 : A) (e2 : L0 DV2.dvalue DV2.uvalue B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                external_call_res_refine_strict e1 res1 e2 res2
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                intrinsic_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                globalE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inl1 (inl1 e1)))), inr1 (inr1 (inr1 (inl1 (inl1 e2)))) =>
                localE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inl1 (inr1 e1)))), inr1 (inr1 (inr1 (inl1 (inr1 e2)))) =>
                stackE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                memoryE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                pickE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                oomE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                llvmExcE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))))) =>
                ubE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))))) =>
                debugE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1))))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2))))))))) =>
                failureE_res_refine_strict e1 res1 e2 res2
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).
  Defined.

  Definition L1_res_refine_strict A B (e1 : L1 DV1.dvalue DV1.uvalue A) (res1 : A) (e2 :L1 DV2.dvalue DV2.uvalue B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                external_call_res_refine_strict e1 res1 e2 res2
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                intrinsic_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inl1 (inl1 e1))), inr1 (inr1 (inl1 (inl1 e2))) =>
                localE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inl1 (inr1 e1))), inr1 (inr1 (inl1 (inr1 e2))) =>
                stackE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                memoryE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                pickE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                oomE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                llvmExcE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                ubE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))))) =>
                debugE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))))) =>
                failureE_res_refine_strict e1 res1 e2 res2
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).
  Defined.

  Definition L2_res_refine_strict A B (e1 : L2 DV1.dvalue DV1.uvalue A) (res1 : A) (e2 : L2 DV2.dvalue DV2.uvalue B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                external_call_res_refine_strict e1 res1 e2 res2
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                intrinsic_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                memoryE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                pickE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                oomE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                llvmExcE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                ubE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                debugE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2))))))) =>
                failureE_res_refine_strict e1 res1 e2 res2
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).
  Defined.

  Definition L3_res_refine_strict A B (e1 : L3 DV1.dvalue DV1.uvalue A) (res1 : A) (e2 : L3 DV2.dvalue DV2.uvalue B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                external_call_res_refine_strict e1 res1 e2 res2
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                pickE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                oomE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                llvmExcE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                ubE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                debugE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2))))) =>
                failureE_res_refine_strict e1 res1 e2 res2
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).
  Defined.

  Definition L4_res_refine_strict A B (e1 : L4 DV1.dvalue DV1.uvalue A) (res1 : A) (e2 : L4 DV2.dvalue DV2.uvalue B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                external_call_res_refine_strict e1 res1 e2 res2
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                oomE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                llvmExcE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                ubE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                debugE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inr1 e1)))), inr1 (inr1 (inr1 (inr1 (inr1 e2)))) =>
                failureE_res_refine_strict e1 res1 e2 res2
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).
  Defined.

  Definition call_refine_strict (A B : Type) (c1 : CallE DV1.uvalue A) (c2 : CallE DV2.uvalue B) : Prop.
  Proof.
    (* Calls *)
    { (* Doesn't say anything about return value... *)
      inv c1.
      inv c2.
      apply (t = t0 /\
               uvalue_refine_strict f f0 /\
               Forall2 uvalue_refine_strict args args0).
    }
  Defined.

  Definition call_res_refine_strict (A B : Type) (c1 : CallE DV1.uvalue A) (res1 : A) (c2 : CallE DV2.uvalue B) (res2 : B) : Prop.
  Proof.
    (* Calls *)
    { inv c1.
      inv c2.
      apply (t = t0 /\
               uvalue_refine_strict f f0 /\
               Forall2 uvalue_refine_strict args args0 /\
               sum_rel uvalue_refine_strict uvalue_refine_strict res1 res2).
    }
  Defined.

  Lemma call_res_refine_strict_call_refine_strict {A B : Type} (c1 : CallE DV1.uvalue A) (res1 : A) (c2 : CallE DV2.uvalue B) (res2 : B) :
    call_res_refine_strict _ _ c1 res1 c2 res2 -> call_refine_strict _ _ c1 c2.
  Proof.
    intros H; red in H; red.
    repeat break_match; cbn in *; auto; tauto.
  Qed.

  #[global] Hint Resolve call_res_refine_strict_call_refine_strict : REFINE_DB.

  Definition L0'_refine_strict A B (e1 : L0' DV1.dvalue DV1.uvalue A) (e2 : L0' _ _ B) : Prop
    := (sum_prerel call_refine_strict event_refine_strict) _ _ e1 e2.

  Definition L0'_res_refine_strict A B (e1 : L0' _ _ A) (res1 : A) (e2 : L0' _ _ B) (res2 : B) : Prop
    := (sum_postrel call_res_refine_strict event_res_refine_strict) _ _ e1 res1 e2 res2.

  Definition exp_E_refine_strict A B (e1 : exp_E DV1.dvalue DV1.uvalue A) (e2 : exp_E DV2.dvalue DV2.uvalue B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                globalE_refine_strict e1 e2
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                localE_refine_strict e1 e2
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                memoryE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                pickE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                oomE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                llvmExcE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                ubE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                debugE_refine_strict e1 e2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2))))))) =>
                failureE_refine_strict e1 e2
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).
  Defined.

  Definition exp_E_res_refine_strict A B (e1 : exp_E DV1.dvalue DV1.uvalue A) (res1 : A) (e2 : exp_E DV2.dvalue DV2.uvalue B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                globalE_res_refine_strict e1 res1 e2 res2
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                localE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                memoryE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                pickE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                oomE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                llvmExcE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                ubE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                debugE_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2))))))) =>
                failureE_res_refine_strict e1 res1 e2 res2
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).
  Defined.

  #[global] Hint Extern 1 (exp_E_refine_strict _ _ _ _) => solve [repeat constructor] : ORUTT.

  Definition instr_E_refine_strict A B (e1 : instr_E DV1.dvalue DV1.uvalue A) (e2 : instr_E DV2.dvalue DV2.uvalue B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                call_refine_strict _ _ e1 e2
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                (* Intrinsics *)
                intrinsic_refine_strict e1 e2
            | inr1 (inr1 e1), inr1 (inr1 e2) =>
                exp_E_refine_strict _ _ e1 e2
            | _, _ =>
                False
            end).
  Defined.

  Definition instr_E_res_refine_strict A B (e1 : instr_E DV1.dvalue DV1.uvalue A) (res1 : A) (e2 : instr_E DV2.dvalue DV2.uvalue B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                call_res_refine_strict _ _ e1 res1 e2 res2
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                intrinsic_res_refine_strict e1 res1 e2 res2
            | inr1 (inr1 e1), inr1 (inr1 e2) =>
                exp_E_res_refine_strict _ _ e1 res1 e2 res2
            | _, _ =>
                False
            end).
  Defined.

  #[global] Hint Extern 1 (forall _ _ _, _ -> (instr_E_refine_strict _ _ _ _)) => solve [repeat constructor; auto].

  #[global] Hint Extern 1 (forall (dt : dtyp) (r4 : DV1.dvalue) (r5 : DV1.uvalue) (r6 : DV2.dvalue) (r7 : DV2.uvalue),
        dvalue_refine_strict r4 r6 ->
        uvalue_refine_strict r5 r7 ->
        exp_E_refine_strict unit unit (_ (Store dt r4 r5)) (_ (Store dt r6 r7)))
  => cbn;intros;tauto : ORUTT.

  #[global] Hint Resolve
    dvalue_refine_strict_dvalue_to_uvalue
    : REF.

  #[global] Hint Extern 1 (instr_E_refine_strict _ _ _ _) => solve [repeat constructor; auto] : ORUTT.

  #[global] Hint Extern 1 (forall _ _ _ _,
        instr_E_res_refine_strict {_ : DV1.dvalue | True} {_ : dvalue | True}
          (subevent {_ : DV1.dvalue | True} (IS1.LLVM.MEM.CP.CONC.pick_unique_uvalue _))
          (exist (fun _ : DV1.dvalue => True) _ I)
          (subevent {_ : dvalue | True} (IS2.LLVM.MEM.CP.CONC.pick_unique_uvalue _)) (exist (fun _ : dvalue => True) _ I) ->
        dvalue_refine_strict _ _) => intros *; cbn in *; tauto : ORUTT.

  #[global] Hint Extern 1 (forall (dt : dtyp) (s0 : string) (t1 : DV1.uvalue + DV1.dvalue) (t2 : DV2.uvalue + DV2.dvalue),
        instr_E_res_refine_strict (DV1.uvalue + DV1.dvalue) (DV2.uvalue + DV2.dvalue)
          (ReSum_inr IFun sum1 (IntrinsicE DV1.dvalue DV1.uvalue)  (IntrinsicE DV1.dvalue DV1.uvalue +' exp_E DV1.dvalue DV1.uvalue)
             CallE (DV1.uvalue + DV1.dvalue)%type (Intrinsic dt s0 _))
          t1
          (ReSum_inr IFun sum1 IntrinsicE (IntrinsicE +' exp_E) CallE (DV2.uvalue + DV2.dvalue)%type
             (Intrinsic dt s0 _))
          t2 ->
        sum_rel uvalue_refine_strict dvalue_refine_strict t1 t2) => cbn; intros; tauto : ORUTT.

  #[global] Hint Extern 1
    (forall (dt : dtyp) (f1 : DV1.uvalue) (f2 : uvalue) (t1 : DV1.uvalue + DV1.uvalue)
       (t2 : DV2.uvalue + DV2.uvalue),
        instr_E_res_refine_strict (DV1.uvalue + DV1.uvalue) (DV2.uvalue + DV2.uvalue)
          (ReSum_inl IFun sum1 (CallE DV1.uvalue) (CallE DV1.uvalue)
             (IntrinsicE DV1.dvalue DV1.uvalue +' exp_E DV1.dvalue DV1.uvalue) (DV1.uvalue + DV1.uvalue)%type
             (LLVMEvents.Call dt f1 _))
          t1
          (ReSum_inl IFun sum1 CallE CallE (IntrinsicE +' exp_E) (DV2.uvalue + DV2.uvalue)%type
             (Call dt f2 _))
          t2 ->
        sum_rel uvalue_refine_strict uvalue_refine_strict t1 t2) => cbn; tauto : ORUTT.

  Lemma exp_E_refine_strict_event_refine_strict :
    forall A B (e1 : exp_E DV1.dvalue DV1.uvalue A) (e2 : exp_E DV2.dvalue DV2.uvalue B),
      exp_E_refine_strict A B e1 e2 ->
      event_refine_strict A B (exp_to_L0 e1) (exp_to_L0 e2).
  Proof.
    intros A B e1 e2 H.
    destruct e1, e2.
    2,3: (cbn in H;
          (repeat break_match_hyp; try contradiction)).

    - destruct l, l0.
      2,3: (cbn in H;
            (repeat break_match_hyp; try contradiction)).

      all: cbn in *; auto.
    - destruct s, s0.
      2,3: (cbn in H;
            (repeat break_match_hyp; try contradiction)).

      + destruct l, l0.
        2,3: (cbn in H;
              (repeat break_match_hyp; try contradiction)).

        all: cbn in *; auto.

      + destruct s, s0.
        2,3: (cbn in H;
              (repeat break_match_hyp; try contradiction)).

        { destruct m, m0; cbn; auto.
        }

        { destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct p, p0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct o, o0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).


          { destruct u, u0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct d, d0; cbn; auto. }
          { destruct f, f0; cbn; auto. }

        }
  Qed.

  Lemma exp_E_refine_strict_instr_E_refine_strict :
    forall A B (e1 : exp_E DV1.dvalue DV1.uvalue A) (e2 : exp_E _ _ B),
      exp_E_refine_strict A B e1 e2 ->
      instr_E_refine_strict A B (exp_to_instr e1) (exp_to_instr e2).
  Proof.
    intros A B e1 e2 H.
    destruct e1, e2.
    2,3: (cbn in H;
          (repeat break_match_hyp; try contradiction)).

    - destruct l, l0.
      2,3: (cbn in H;
            (repeat break_match_hyp; try contradiction)).

      all: cbn in *; auto.
    - destruct s, s0.
      2,3: (cbn in H;
            (repeat break_match_hyp; try contradiction)).

      + destruct l, l0.
        2,3: (cbn in H;
              (repeat break_match_hyp; try contradiction)).

        all: cbn in *; auto.

      + destruct s, s0.
        2,3: (cbn in H;
              (repeat break_match_hyp; try contradiction)).

        { destruct m, m0; cbn; auto.
        }

        { destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct p, p0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct o, o0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct u, u0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct d, d0; cbn; auto. }
          { destruct f, f0; cbn; auto. }

        }
  Qed.

  Definition L0_E1E2_orutt_strict t1 t2
    : Prop :=
    orutt
      event_refine_strict
      event_res_refine_strict
      dvalue_refine_strict
      t1 t2 (OOM:=OOME).

  Definition L1_E1E2_orutt_strict t1 t2
    : Prop :=
    orutt
      L1_refine_strict
      L1_res_refine_strict
      (global_refine_strict × dvalue_refine_strict)
      t1 t2 (OOM:=OOME).

  Definition L2_E1E2_orutt_strict t1 t2
    : Prop :=
    orutt
      L2_refine_strict
      L2_res_refine_strict
      (stack_frame_refine_strict × stack_refine_strict × (global_refine_strict × dvalue_refine_strict))
      t1 t2 (OOM:=OOME).

  Definition model_E1E2_L0_orutt_strict args1 args2 p1 p2 :=
    L0_E1E2_orutt_strict
      (LLVM1.denote_vellvm (DTYPE_I 32%positive) (LLVMAst.Name "main") args1 (convert_types (mcfg_of_tle p1)))
      (LLVM2.denote_vellvm (DTYPE_I 32%positive) (LLVMAst.Name "main") args2 (convert_types (mcfg_of_tle p2))).

  Definition model_E1E2_L1_orutt_strict args1 args2 p1 p2 :=
    L1_E1E2_orutt_strict
      (LLVM1.model_oom_L1 args1 p1)
      (LLVM2.model_oom_L1 args2 p2).

  Definition model_E1E2_L2_orutt_strict args1 args2 p1 p2 :=
    L2_E1E2_orutt_strict
      (LLVM1.model_oom_L2 args1 p1)
      (LLVM2.model_oom_L2 args2 p2).

  Lemma instr_E_refine_strict_L0'_refine_strict :
    forall A B (e1 : instr_E DV1.dvalue DV1.uvalue A) (e2 : instr_E _ _ B),
      instr_E_refine_strict A B e1 e2 ->
      L0'_refine_strict A B (instr_to_L0' e1) (instr_to_L0' e2).
  Proof.
    intros A B e1 e2 H.
    unfold L0'_refine_strict.
    destruct e1, e2.
    2,3: (cbn in H;
          (repeat break_match_hyp; try contradiction)).

    - destruct c, c0.
      cbn in *.
      constructor; cbn.
      tauto.
    - destruct s, s0.
      2,3: (cbn in H;
            (repeat break_match_hyp; try contradiction)).

      + destruct i, i0.
        cbn in *.
        constructor; cbn.
        tauto.

      + destruct e, e0.
        2,3: (cbn in H;
              (repeat break_match_hyp; try contradiction)).

        { destruct l, l0; cbn; constructor; cbn; auto.
        }

        { destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct l, l0; cbn; constructor; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct m, m0; cbn; constructor; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct p, p0; cbn; constructor; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct o, o0; cbn; constructor; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { cbn; constructor; cbn; auto. }

          { destruct s, s0; cbn; try constructor; auto.
            destruct s; try solve [ cbn in H; contradiction ].
            destruct s; try solve [ cbn in H; contradiction ].
            destruct s, s0; cbn; try constructor; auto.
          }
        }
  Qed.

  Lemma event_refine_strict_exp_E_refine_strict_inv :
    forall A B (e1 : exp_E DV1.dvalue DV1.uvalue A) (e2 : exp_E _ _ B) a b,
      event_res_refine_strict A B (exp_to_L0 e1) a (exp_to_L0 e2) b ->
      exp_E_refine_strict A B e1 e2.
  Proof.
    intros A B e1 e2 a b H.
    red; red in H.
    repeat (break_match_goal; subst; cbn in *; eauto with REFINE_DB);
      repeat (unfold resum, ReSum_sum, ReSum_inr, cat, Cat_IFun, case_, Case_sum1, case_sum1 in *;
              break_match_hyp; subst; cbn in *; auto); discriminate.
  Qed.

  Lemma event_res_refine_strict_exp_E_res_refine_strict_inv :
    forall A B (e1 : exp_E DV1.dvalue DV1.uvalue A) (e2 : exp_E _ _ B) a b,
      event_res_refine_strict A B (exp_to_L0 e1) a (exp_to_L0 e2) b ->
      exp_E_res_refine_strict A B e1 a e2 b.
  Proof.
    intros A B e1 e2 a b H.
    red; red in H.
    repeat (break_match_goal; subst; cbn in *; eauto with REFINE_DB);
      repeat (unfold resum, ReSum_sum, ReSum_inr, cat, Cat_IFun, case_, Case_sum1, case_sum1 in *;
              break_match_hyp; subst; cbn in *; auto); discriminate.
  Qed.

  Lemma L0'_res_refine_strict_instr_E_res_refine_strict_inv :
    forall A B (e1 : instr_E DV1.dvalue DV1.uvalue A) (e2 : instr_E _ _ B) a b,
      L0'_res_refine_strict A B (instr_to_L0' e1) a (instr_to_L0' e2) b ->
      instr_E_res_refine_strict A B e1 a e2 b.
  Proof.
    intros A B e1 e2 a b H.
    red in H; red.
    repeat (break_match_goal; subst; cbn in *; eauto with REFINE_DB);
      repeat (unfold resum, ReSum_sum, ReSum_inr, cat, Cat_IFun, case_, Case_sum1, case_sum1 in *;
              break_match_hyp; subst; cbn in *; auto); inv H; subst_existT; cbn in *; eauto with REFINE_DB; try discriminate.
  Qed.

  Lemma translate_exp_to_L0_E1E2_rutt :
    forall {R1 R2} {RR : R1 -> R2 -> Prop} t1 t2,
      rutt exp_E_refine_strict exp_E_res_refine_strict RR
        t1
        t2 ->
      rutt event_refine_strict event_res_refine_strict RR
        (translate (@exp_to_L0 DV1.dvalue DV1.uvalue) t1)
        (translate (@exp_to_L0 DV2.dvalue DV2.uvalue) t2).
  Proof.
    intros *.
    revert t1 t2.
    ginit.
    gcofix CIH.
    intros * RUTT.
    rewrite !unfold_translate. punfold RUTT. red in RUTT.
    induction RUTT; intros; subst; simpl; pclearbot.
    - gstep.
      constructor.
      auto.
    - gstep.
      red.
      constructor.
      gbase.
      apply CIH.
      auto.
    - gstep; eauto.
      red.
      constructor; eauto.
      apply exp_E_refine_strict_event_refine_strict; auto.

      intros a b H1.

      gbase.
      apply CIH.

      apply event_res_refine_strict_exp_E_res_refine_strict_inv in H1.
      apply H0 in H1.
      pclearbot.
      pfold. red.
      punfold H1.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
  Qed.

  Ltac unfold_subevents :=
    repeat (unfold subevent, resum, ReSum_inr, ReSum_inl, ReSum_sum, ReSum_id, id_, Id_IFun, case_, Case_sum1, case_sum1, cat, Cat_IFun, inr_, Inr_sum1, inl_, Inl_sum1 in *; cbn in *).

  Lemma translate_exp_to_L0_E1E2_orutt :
    forall {R1 R2} {RR : R1 -> R2 -> Prop} t1 t2,
      orutt exp_E_refine_strict exp_E_res_refine_strict RR
        t1
        t2
        (OOM:=OOME) ->
      orutt event_refine_strict event_res_refine_strict RR
        (translate (@exp_to_L0 DV1.dvalue DV1.uvalue) t1)
        (translate (@exp_to_L0 _ _) t2)
        (OOM:=OOME).
  Proof.
    intros *.
    revert t1 t2.
    ginit.
    gcofix CIH.
    intros * RUTT.
    rewrite !unfold_translate. punfold RUTT. red in RUTT.
    induction RUTT; intros; subst; simpl; pclearbot.
    - gstep.
      constructor.
      auto.
    - gstep.
      red.
      constructor.
      gbase.
      apply CIH.
      auto.
    - gstep; eauto.
      red.
      constructor; eauto.
      apply exp_E_refine_strict_event_refine_strict; auto.

      intros a b H2.

      gbase.
      apply CIH.

      apply event_res_refine_strict_exp_E_res_refine_strict_inv in H2.
      apply H0 in H2.
      pclearbot.
      pfold. red.
      punfold H2.
      intros o CONTRA.
      specialize (H1 o).
      apply H1.
      unfold exp_to_L0 in CONTRA.
      unfold_subevents.
      repeat break_match_hyp_inv; auto.
    - gstep; eauto.
      red.
      cbn.
      change (inr1 (inr1 (inr1 (inr1 (resum IFun A e))))) with (@subevent _ _ (ReSum_inr IFun sum1 OOME
                                                                               (IntrinsicE +'
                                                                                              LLVMGEnvE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                                                                               ExternalCallE) A e).
      apply EqVisOOM.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
  Qed.

  Lemma instr_E_res_refine_strict_exp_E_res_refine_strict_inv :
    forall A B (e1 : exp_E DV1.dvalue DV1.uvalue A) (e2 : exp_E _ _ B) a b,
      instr_E_res_refine_strict A B (exp_to_instr e1) a (exp_to_instr e2) b ->
      exp_E_res_refine_strict A B e1 a e2 b.
  Proof.
    intros A B e1 e2 a b H.
    red in H; red.
    repeat (break_match_goal; subst; cbn in *; eauto with REFINE_DB);
      repeat (unfold resum, ReSum_sum, ReSum_inr, cat, Cat_IFun, case_, Case_sum1, case_sum1 in *;
              break_match_hyp; subst; cbn in *; auto); cbn in *; eauto with REFINE_DB; try discriminate.
  Qed.

  Lemma translate_instr_to_L0'_E1E2_rutt_strict :
    forall {R1 R2} {RR : R1 -> R2 -> Prop} t1 t2,
      rutt instr_E_refine_strict instr_E_res_refine_strict RR t1 t2 ->
      rutt L0'_refine_strict L0'_res_refine_strict RR
        (translate (@instr_to_L0' DV1.dvalue DV1.uvalue) t1)
        (translate (@instr_to_L0' _ _) t2).
  Proof.
    intros *.
    revert t1 t2.
    ginit.
    gcofix CIH.
    intros * RUTT.
    rewrite !unfold_translate. punfold RUTT. red in RUTT.
    induction RUTT; intros; subst; simpl; pclearbot.
    - gstep.
      constructor.
      auto.
    - gstep.
      red.
      constructor.
      gbase.
      apply CIH.
      auto.
    - gstep; eauto.
      red.
      constructor; eauto.
      apply instr_E_refine_strict_L0'_refine_strict; auto.

      intros a b H2.

      gbase.
      apply CIH.

      apply L0'_res_refine_strict_instr_E_res_refine_strict_inv in H2.
      apply H0 in H2.
      pclearbot.
      pfold. red.
      punfold H2.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
  Qed.

  Lemma translate_instr_to_L0'_E1E2_orutt_strict :
    forall {R1 R2} {RR : R1 -> R2 -> Prop} t1 t2,
      orutt instr_E_refine_strict instr_E_res_refine_strict RR t1 t2 (OOM:=OOME) ->
      orutt L0'_refine_strict L0'_res_refine_strict RR
        (translate (@instr_to_L0' DV1.dvalue DV1.uvalue) t1)
        (translate (@instr_to_L0' _ _) t2)
        (OOM:=OOME).
  Proof.
    intros *.
    revert t1 t2.
    ginit.
    gcofix CIH.
    intros * RUTT.
    rewrite !unfold_translate. punfold RUTT. red in RUTT.
    induction RUTT; intros; subst; simpl; pclearbot.
    - gstep.
      constructor.
      auto.
    - gstep.
      red.
      constructor.
      gbase.
      apply CIH.
      auto.
    - gstep; eauto.
      red.
      constructor; eauto.
      apply instr_E_refine_strict_L0'_refine_strict; auto.

      intros a b H2.

      gbase.
      apply CIH.

      apply L0'_res_refine_strict_instr_E_res_refine_strict_inv in H2.
      apply H0 in H2.
      pclearbot.
      pfold. red.
      punfold H2.

      intros o CONTRA.
      eapply H1.
      unfold instr_to_L0' in CONTRA.
      unfold_subevents. unfold OOME_L0' in *. 
      repeat break_match_hyp_inv; auto. reflexivity.
    - gstep; eauto.
      red.
      cbn.
      unfold exp_to_instr.
      unfold subevent.
      change (inr1 (inr1 (inr1 (inr1 (inr1 (resum IFun A e)))))) with
        (@subevent _ _ (ReSum_inr IFun sum1 OOME
                          (ExternalCallE +' IntrinsicE +' LLVMGEnvE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                          CallE) A e).
      apply EqVisOOM.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
  Qed.

  Lemma translate_exp_to_instr_E1E2_rutt_strict :
    forall {R1 R2} {RR : R1 -> R2 -> Prop} t1 t2,
      rutt exp_E_refine_strict exp_E_res_refine_strict RR t1 t2 ->
      rutt instr_E_refine_strict instr_E_res_refine_strict RR
        (translate (@exp_to_instr DV1.dvalue DV1.uvalue) t1)
        (translate (@exp_to_instr _ _)t2).
  Proof.
    intros *.
    revert t1 t2.
    ginit.
    gcofix CIH.
    intros * RUTT.
    rewrite !unfold_translate. punfold RUTT. red in RUTT.
    induction RUTT; intros; subst; simpl; pclearbot.
    - gstep.
      constructor.
      auto.
    - gstep.
      red.
      constructor.
      gbase.
      apply CIH.
      auto.
    - gstep; eauto.
      red.
      cbn.
      constructor; eauto.
      apply exp_E_refine_strict_instr_E_refine_strict; auto.
      intros a b H2.

      gbase.
      apply CIH.

      apply instr_E_res_refine_strict_exp_E_res_refine_strict_inv in H2.
      apply H0 in H2.
      pclearbot.
      pfold. red.
      punfold H2.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
  Qed.

  Lemma translate_exp_to_instr_E1E2_orutt_strict :
    forall {R1 R2} {RR : R1 -> R2 -> Prop} t1 t2,
      orutt exp_E_refine_strict exp_E_res_refine_strict RR t1 t2 (OOM:=OOME) ->
      orutt instr_E_refine_strict instr_E_res_refine_strict RR
        (translate (@exp_to_instr DV1.dvalue DV1.uvalue) t1)
        (translate (@exp_to_instr _ _) t2)
        (OOM:=OOME).
  Proof.
    intros *.
    revert t1 t2.
    ginit.
    gcofix CIH.
    intros * RUTT.
    rewrite !unfold_translate. punfold RUTT. red in RUTT.
    induction RUTT; intros; subst; simpl; pclearbot.
    - gstep.
      constructor.
      auto.
    - gstep.
      red.
      constructor.
      gbase.
      apply CIH.
      auto.
    - gstep; eauto.
      red.
      cbn.
      constructor; eauto.
      apply exp_E_refine_strict_instr_E_refine_strict; auto.
      intros a b H2.

      gbase.
      apply CIH.

      apply instr_E_res_refine_strict_exp_E_res_refine_strict_inv in H2.
      apply H0 in H2.
      pclearbot.
      pfold. red.
      punfold H2.

      intros o CONTRA.
      eapply H1.
      unfold exp_to_instr in *.
      unfold_subevents.
      repeat break_match_hyp_inv; auto. reflexivity.
    - gstep; eauto.
      red.
      cbn.
      unfold exp_to_instr.
      unfold subevent.
      change (inr1 (inr1 (resum IFun A e))) with
        (@subevent _ _ (ReSum_inr IFun sum1 OOME
                          (IntrinsicE +' exp_E)
                          CallE) A e).
      apply EqVisOOM.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
  Qed.

  Lemma translate_LU_to_exp_lookup_id_orutt :
    forall id : LLVMAst.ident,
      orutt exp_E_refine_strict exp_E_res_refine_strict uvalue_refine_strict
        (translate (@LU_to_exp _ _) (IS1.LLVM.D.lookup_id id)) (translate (@LU_to_exp _ _) (lookup_id id))
        (OOM:=OOME).
  Proof.
    intros id.
    destruct id.
    - cbn.
      repeat rewrite translate_bind.
      repeat rewrite translate_trigger.
      repeat setoid_rewrite translate_ret.

      repeat rewrite bind_trigger.
      apply orutt_Vis;
        [cbn; auto| |].

      intros * ?.
      apply orutt_Ret.
      cbn in H.
      apply dvalue_refine_strict_dvalue_to_uvalue.
      destruct H.
      auto.

      intros o CONTRA.
      dependent destruction CONTRA.
    - cbn.
      repeat rewrite translate_bind.
      repeat rewrite translate_trigger.
      repeat setoid_rewrite translate_ret.

      repeat rewrite bind_trigger.
      apply orutt_Vis;
        [cbn; auto| |].

      intros * ?.
      apply orutt_Ret.
      destruct H.
      auto.

      intros o CONTRA.
      dependent destruction CONTRA.
  Qed.

  (* TODO: move this! Probably somewhere that I get a version for each language? *)
  Ltac solve_dec_oom :=
    let s := fresh "s" in
    first [intros ? ? ? s | intros s];
    repeat destruct s;
    try solve
      [
        left;
        intros o CONTRA;
        inv CONTRA
      ];
    right;
    eexists; reflexivity.

  Lemma exp_E_dec_oom :
    forall A d u (e : @exp_E d u A), {forall o : OOME A, e <> subevent _ o} + {exists o : OOME A, e = subevent _ o}.
  Proof.
    solve_dec_oom.
  Qed.

  (* TODO: move this! *)
  Lemma L0'_dec_oom :
    forall A d u (e : @L0' d u A), {forall o : OOME A, e <> subevent _ o} + {exists o : OOME A, e = subevent _ o}.
  Proof.
    solve_dec_oom.
  Qed.

  (* TODO: move this! *)
  Lemma L0_dec_oom :
    forall A d u (e : @L0 d u A), {forall o : OOME A, e <> subevent _ o} + {exists o : OOME A, e = subevent _ o}.
  Proof.
    solve_dec_oom.
  Qed.

  Lemma orutt_translate :
    forall {E1 E1' E2 E2' OOM : Type -> Type} `{OOME : OOM -< E2} `{OOME' : OOM -< E2'} (h1 : E1 ~> E1') (h2 : E2 ~> E2')
      {PRE1 : prerel E1 E2} {POST1 : postrel E1 E2}
      {PRE2 : prerel E1' E2'} {POST2 : postrel E1' E2'}
      {R1 R2 : Type} {RR : R1 -> R2 -> Prop} t1 t2,
      (forall A B e1 e2, PRE1 A B e1 e2 -> PRE2 A B (h1 _ e1) (h2 _ e2)) ->
      (forall A B e1 a e2 b, POST2 A B (h1 A e1) a (h2 B e2) b -> POST1 A B e1 a e2 b) ->
      (forall A (e : E2 A) (o : OOM _), e <> @subevent OOM E2 OOME A o -> h2 _ e <> @subevent OOM E2' OOME' A o) ->
      (forall A (e : E2 A) (o : OOM _), e = @subevent OOM E2 OOME A o -> h2 _ e = @subevent OOM E2' OOME' A o) ->
      orutt PRE1 POST1 RR
        t1
        t2
      (OOM:=OOM) ->
      orutt PRE2 POST2 RR
        (translate h1 t1)
        (translate h2 t2)
        (OOM:=OOM).
  Proof.
    intros * PRE POST NOOM OOMOOM.
    revert t1 t2.
    ginit.
    gcofix CIH.
    intros * RUTT.
    rewrite !unfold_translate. punfold RUTT. red in RUTT.
    induction RUTT; intros; subst; simpl; pclearbot.
    - gstep.
      constructor.
      auto.
    - gstep.
      red.
      constructor.
      gbase.
      apply CIH.
      auto.
    - gstep; eauto.
      red.
      constructor; eauto.
      intros a b H2.
      apply POST in H2.
      eapply H0 in H2.
      gbase.
      apply CIH; auto.
    - gstep; eauto.
      red.
      cbn.
      erewrite OOMOOM; try reflexivity.
      apply EqVisOOM.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
  Qed.
End EventRefine.
