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
     Semantics.InfiniteToFinite.R2Injective
     Syntax.DynamicTypes
     Theory.TopLevelRefinements
     Theory.ContainsUB
     Utils.Error
     Utils.Monads
     Utils.MapMonadExtra
     Utils.PropT
     Utils.InterpProp
     Utils.InterpPropOOM
     Utils.ListUtil
     Utils.Tactics
     Utils.OOMRutt
     Utils.OOMRuttProps
     Utils.RuttPropsExtra
     Utils.AListFacts
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

(* TODO: Move these *)
Program Fixpoint Forall2_HInT {A B : Type}
  (xs : list A) (ys : list B) (R : forall a b, InT a xs -> InT b ys -> Prop) : Prop :=
  match xs, ys with
  | [], [] => True
  | (x::xs), (y::ys) =>
      R x y _ _ /\ Forall2_HInT xs ys (fun x y IN1 IN2 => R x y _ _)
  | _, _ =>
      False
  end.
Next Obligation.
  exact (inl eq_refl).
Defined.
Next Obligation.
  exact (inl eq_refl).
Defined.
Next Obligation.
  exact (inr IN1).
Defined.
Next Obligation.
  exact (inr IN2).
Defined.
Next Obligation.
  split. intros; intro C.
  intuition. inversion H1.
  intro C. intuition. inversion H2.
Defined.
Next Obligation.
  split. intros; intro C.
  intuition. inversion H2.
  intro C. intuition. inversion H1.
Defined.  

Lemma map_monad_InT_oom_forall2 :
  forall {A B} l (f : forall (a : A), InT a l -> OOM B) res,
    map_monad_InT l f = NoOom res <->
      Forall2_HInT l res (fun a b INA INB => f a INA = NoOom b).
Proof.
  intros A B.
  induction l; intros f res.
  - split; intros MAP.
    + cbn in *.
      inv MAP.
      auto.
    + cbn in *.
      break_match_hyp; tauto.
  - split; intros MAP.
    + rewrite map_monad_InT_unfold in MAP.
      cbn in *.
      break_match_hyp; inv MAP.
      break_match_hyp; inv H0.

      pose proof (IHl (fun (x : A) (HIn : InT x l) => f x (inr HIn)) l0) as FORALL.
      constructor; auto.
      eapply FORALL. eauto.
    + rewrite map_monad_InT_cons.
      cbn in *.
      break_match_hyp; try contradiction.
      cbn in *.
      destruct MAP as [FA MAP].
      rewrite FA.

      pose proof (IHl (fun (x : A) (HIn : InT x l) => f x (inr HIn)) l0) as FORALL.
      apply FORALL in MAP.
      rewrite MAP.
      auto.
Qed.

Lemma Forall2_Forall2_HInT :
  forall {A B : Type} (xs : list A) (ys : list B) f,
    Forall2 f xs ys ->
    Forall2_HInT xs ys (fun a b HIna HInb => f a b).
Proof.
  intros A B xs ys f H.
  induction H; cbn; auto.
Qed.

Module Type LangRefine (IS1 : InterpreterStack) (IS2 : InterpreterStack) (AC1 : AddrConvert IS1.LP.ADDR IS2.LP.ADDR) (AC2 : AddrConvert IS2.LP.ADDR IS1.LP.ADDR) (LLVM1 : LLVMTopLevel IS1) (LLVM2 : LLVMTopLevel IS2) (TLR : TopLevelRefinements IS2 LLVM2) (IPS : IPConvertSafe IS2.LP.IP IS1.LP.IP) (DVC : DVConvert IS1.LP IS2.LP AC1 IS1.LP.Events IS2.LP.Events) (DVCrev : DVConvert IS2.LP IS1.LP AC2 IS2.LP.Events IS1.LP.Events) (EC : EventConvert IS1.LP IS2.LP AC1 AC2 IS1.LP.Events IS2.LP.Events DVC DVCrev) (TC : TreeConvert IS1 IS2 AC1 AC2 DVC DVCrev EC).
  Import TLR.

  Import TC.
  Import EC.
  Import DVC.
  Import IPS.

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

  (*
  Definition convert_stack_lazy (s : @stack IS1.LLVM.Local.local_env) : (@stack IS2.LLVM.Local.local_env)
    := map convert_local_env_lazy s.
   *)

  Definition convert_stack_strict (s : @stack IS1.LLVM.Local.local_env) : OOM (@stack IS2.LLVM.Local.local_env)
    := map_monad convert_local_env_strict s.

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

  Definition stack_refine_strict (s1 : @stack IS1.LLVM.Local.local_env) (s2 : @stack IS2.LLVM.Local.local_env) : Prop
    := Forall2 local_refine_strict s1 s2.

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
    (ls1 : (IS1.LLVM.Local.local_env * @stack IS1.LLVM.Local.local_env)%type)
    (ls2 : (IS2.LLVM.Local.local_env * @stack IS2.LLVM.Local.local_env)%type)
    : Prop :=
    match ls1, ls2 with
    | (l1, s1), (l2, s2) =>
        local_refine_strict l1 l2 /\ stack_refine_strict s1 s2
    end.

  Lemma local_stack_refine_strict_empty :
    local_stack_refine_strict ([], []) ([], []).
  Proof.
    cbn.
    split.
    apply local_refine_strict_empty.
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
      local_refine_strict lenv1 lenv2 ->
      stack_refine_strict (lenv1 :: s1) (lenv2 :: s2).
  Proof.
    intros s1 s2 lenv1 lenv2 H H0.
    red.
    apply Forall2_cons; auto.
  Qed.

  (** OOM Refinements *)
  (* Lemma Returns_uvalue_convert_L1_L2 : *)
  (*   forall a d f u l t args, *)
  (*     EC.DVCrev.dvalue_convert a = NoOom d -> *)
  (*     EC.DVC.uvalue_convert f = NoOom u -> *)
  (*     @Returns (E2.ExternalCallE +' OOME +' UBE +' DebugE +' FailureE) E2.DV.dvalue a (trigger (E2.ExternalCall t u l)) -> *)
  (*     @Returns (E1.ExternalCallE +' OOME +' UBE +' DebugE +' FailureE) E1.DV.dvalue d (trigger (E1.ExternalCall t f args)). *)
  (* Proof. *)
  (* Admitted. *)

  Lemma Returns_ExternalCall_L0 :
    forall d f t args,
      @Returns E1.L0 E1.DV.dvalue d (trigger (E1.ExternalCall t f args)).
  Proof.
    intros d f t args.

    eapply ReturnsVis.
    unfold trigger.
    reflexivity.
    cbn.
    constructor.
    reflexivity.
  Qed.

  (* Lemma Returns_uvalue_convert_strict_L0 : *)
  (*   forall a d f u l t args, *)
  (*     (* EC.DVCrev.dvalue_convert_strict a = NoOom d -> *) *)
  (*     (* EC.DVC.uvalue_convert_strict f = NoOom u -> *) *)
  (*     @Returns E2.L0 E2.DV.dvalue a (trigger (E2.ExternalCall t u l)) -> *)
  (*     @Returns E1.L0 E1.DV.dvalue d (trigger (E1.ExternalCall t f args)). *)
  (* Proof. *)
  (*   intros a d f u l t args (* DVCONV UVCONV *) RET. *)

  (*   eapply ReturnsVis. *)
  (*   unfold trigger. *)
  (*   reflexivity. *)
  (*   cbn. *)
  (*   constructor. *)
  (*   reflexivity. *)


  (*   remember (trigger (E2.ExternalCall t u l)) as call. *)
  (*   assert (call ≈ trigger (E2.ExternalCall t u l)) as CALL. *)
  (*   { subst; reflexivity. } *)
  (*   clear Heqcall. *)
  (*   induction RET; subst; auto. *)
  (*   - unfold trigger in CALL. *)
  (*     rewrite H in CALL. *)
  (*     pinversion CALL. *)
  (*   - forward IHRET. *)
  (*     { rewrite <- tau_eutt. *)
  (*       rewrite <- H. *)
  (*       auto. *)
  (*     } *)
  (*     auto. *)
  (*   - (* Must be a contradiction...? *) *)
  (*     eapply ReturnsVis. *)
  (*     unfold trigger. *)
  (*     reflexivity. *)
  (*     cbn. *)
  (*     constructor. *)
  (*     reflexivity. *)
  (* Qed. *)

  (* Lemma Returns_uvalue_convert_L3 : *)
  (*   forall a d f u l t args, *)
  (*     EC.DVCrev.dvalue_convert a = NoOom d -> *)
  (*     EC.DVC.uvalue_convert f = NoOom u -> *)
  (*     @Returns E2.L3 E2.DV.dvalue a (trigger (E2.ExternalCall t u l)) -> *)
  (*     @Returns E1.L3 E1.DV.dvalue d (trigger (E1.ExternalCall t f args)). *)
  (* Proof. *)
  (* Admitted. *)

  Lemma refine_OOM_h_L0_convert_tree_strict :
    forall {T} x_inf y_inf (RR : relation T),
      refine_OOM_h RR x_inf y_inf ->
      refine_OOM_h RR (L0_convert_tree_strict x_inf) (L0_convert_tree_strict y_inf).
  Proof.
    intros T.

    unfold refine_OOM_h, L0_convert_tree_strict, refine_OOM_h_flip.
    intros.
    rewrite (unfold_interp y_inf).
    rewrite (unfold_interp x_inf).
    cbn.

    match goal with
    | |- interp_prop_oom_l _ _ ?l ?r => remember l as i; remember r as i0
    end.

    assert (i ≅ _interp EC.L0_convert_strict (observe y_inf)). {
      rewrite Heqi. reflexivity.
    } clear Heqi.
    remember (_interp EC.L0_convert_strict (observe x_inf)).
    assert (i0 ≅ _interp EC.L0_convert_strict (observe x_inf)). {
      subst; reflexivity.
    } clear Heqi1 Heqi0.
    revert x_inf y_inf H i i0 H0 H1.

    pcofix CIH.

    intros * H.
    punfold H; red in H.
    remember (observe y_inf) as oy; remember (observe x_inf) as ox.
    clear Heqoy Heqox.

    induction H; pclearbot; intros; subst; auto.
    - pstep. cbn in H1, H2.
      rewrite itree_eta in H1, H2.
      red.
      destruct (observe i) eqn: Heqi; destruct (observe i0) eqn: Heqi0;
        try apply eqit_inv in H1; try apply eqit_inv in H2; cbn in H1, H2; try contradiction; auto.
      subst; constructor; auto.
    - pstep. cbn in H1, H2.
      rewrite itree_eta in H1, H2.
      red.
      destruct (observe i) eqn: Heqi; destruct (observe i0) eqn: Heqi0;
        try apply eqit_inv in H1; try apply eqit_inv in H2; cbn in H1, H2; try contradiction; auto.
      subst; constructor; auto.

      right; eapply CIH; eauto;
      rewrite unfold_interp in H1, H2; auto.
    - pstep. cbn in H1, H2.
      rewrite itree_eta in H1, H2.
      red.
      destruct (observe i) eqn: Heqi;
        try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
      subst; constructor; auto.
      rewrite unfold_interp in H1.
      specialize (IHinterp_prop_oomTF _ _ H1 H2).
      punfold IHinterp_prop_oomTF.
    - pstep. cbn in H1, H2.
      rewrite itree_eta in H1, H2.
      red.
      destruct (observe i0) eqn: Heqi;
        try apply eqit_inv in H2; cbn in H2; try contradiction; auto.
      subst; constructor; auto.
      rewrite unfold_interp in H2.
      specialize (IHinterp_prop_oomTF _ _ H1 H2).
      punfold IHinterp_prop_oomTF.
    - pstep. apply bisimulation_is_eq in HT1.
      rewrite HT1 in H1. cbn in H1.
      destruct (resum IFun A e).
      cbn in H1.
      repeat setoid_rewrite bind_vis in H1.
      apply bisimulation_is_eq in H1. rewrite H1.
      econstructor; eauto.
      eapply eqit_Vis; intros; inv u.
    - discriminate.
    - pstep. cbn in H2, H3. red in H.
      rewrite H in H0.
      rename H2 into H1.
      rename H3 into H2.

      rewrite itree_eta in H1, H2.
      repeat destruct e; cbn in *.
      + rewrite bind_bind in H1.
        unfold lift_OOM in H1.
        rename H0 into KS. rewrite bind_trigger in KS.
        cbn in *.
        destruct (DVC.uvalue_convert_strict f) eqn : Hf.
        { rewrite bind_ret_l, bind_bind in H1.
          destruct
            (map_monad_In args
              (fun (elt : E1.DV.dvalue) (_ : In elt args) => DVC.dvalue_convert_strict elt)) eqn: Hm.
          { rewrite bind_ret_l, bind_bind in H1.
            rewrite bind_trigger in H1.

            destruct (observe i) eqn: Heqi;
              try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
            red.
            setoid_rewrite Heqi.
            destruct H1 as (?&?&?).
            dependent destruction x.
            red in H, H0.
            econstructor; [ constructor | ..]; eauto; cycle 1.
            - red; reflexivity.
            - cbn in *.
              rewrite <- unfold_interp in H2.
              rewrite <- itree_eta in H2.
              rewrite H2. rewrite KS. rewrite interp_vis. cbn.
              rewrite bind_bind. unfold lift_OOM.
              rewrite Hf. setoid_rewrite bind_ret_l.
              setoid_rewrite bind_bind. rewrite Hm.
              setoid_rewrite bind_ret_l.
              setoid_rewrite bind_bind.
              setoid_rewrite bind_trigger.
              unfold subevent. rewrite H0.
              eapply eqit_Vis. intros.
              Unshelve.
              3 : exact (fun u0 : E2.DV.dvalue =>
              ITree.bind match DVCrev.dvalue_convert_strict u0 with
                        | NoOom a0 => ret a0
                        | Oom s => raise_oom s
                         end (fun x1 : E1.DV.dvalue => Tau (interp EC.L0_convert_strict (k2 x1)))).
              reflexivity. intros. inv H.
            - cbn. red in H1. subst.
              eapply bisimulation_is_eq in H1. rewrite H1.

              destruct (DVCrev.dvalue_convert_strict a) eqn: Ht.
              + setoid_rewrite H in HK. subst.
                (* TODO: Originally used Returns_uvalue_convert_L0
                applied to H3... But it seems Returns is weird with
                the vis case and allows any value to be
                returned...? *)
                rename H3 into H3'.
                pose proof Returns_ExternalCall_L0 d f t args as H3.
                specialize (HK _ H3). pclearbot.
                pose proof @bind_ret_l as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ.
                pose proof @bind_ret_l as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ.
                pstep; constructor; eauto. right; eauto.
                eapply CIH; try rewrite <- unfold_interp; try reflexivity.
                eapply HK.
              + setoid_rewrite H in HK. subst.
                unfold raiseOOM.
                pose proof @bind_bind as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ.
                pose proof @bind_trigger as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ.
                pose proof @bind_bind as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ.
                pose proof @bind_trigger as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ.
                pstep; econstructor; eauto. unfold subevent.
                reflexivity. }
          { unfold raiseOOM in H1. rewrite bind_trigger in H1.
            red. destruct (observe i) eqn: Heqi;
              try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
            destruct H1 as (?&?&?).
            dependent destruction x.
            red in H, H0.
            inv H0.
            observe_vis; solve_interp_prop_oom.
        } }

          unfold raiseOOM in H1. rewrite bind_trigger in H1.
          red. destruct (observe i) eqn: Heqi;
            try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
          destruct H1 as (?&?&?).
          dependent destruction x.
          red in H, H0. cbn in *.
          inv H0.
          observe_vis; solve_interp_prop_oom.
      + destruct s.
        { (* Intrinsic *)
          admit.
        }
        destruct s.
        { (* Globals *)
          admit.
        }
        destruct s.
        { (* Locals + Stack *)
          admit.
        }
        destruct s.
        { (* Memory *)
          (* TODO: separate out? *)
          destruct m.
          { (* MemPush *)
            cbn in *.
            red.
            rewrite <- itree_eta in H1.
            admit.
          }
          admit.
          admit.
          admit.
          admit.
        }
        destruct s.
        { (* Pick *)
          admit.
        }
        destruct s.
        * unfold raiseOOM in H1.
          destruct o.
          cbn in H1.
          rewrite bind_bind, bind_trigger in H1.
          rewrite itree_eta in H1, H2.
          red.
          destruct (observe i) eqn: Heqi;
            try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
          destruct H1 as (?&?&?).
          dependent destruction x.
          red in H, H0. cbn in *.
          inv H0.
          observe_vis; solve_interp_prop_oom.
        * destruct s; try destruct u; cbn in H1.
          -- repeat red in HTA.
              unfold raiseUB in H1. rewrite bind_trigger in H1.
              red.
              destruct (observe i) eqn: Heqi;
                try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
              destruct H1 as (?&?&?).
              dependent destruction x.
              red in H, H0.
              eapply Interp_Prop_OomT_Vis; eauto.
              repeat red. intros.
              inv a.
              red; reflexivity.
              setoid_rewrite <- itree_eta in H2. rewrite H2.
              rewrite <- unfold_interp.
              rewrite H0. rewrite bind_trigger.
              rewrite interp_vis.
              cbn.
              setoid_rewrite bind_trigger. rewrite bind_vis. cbn in *; subst. eapply eqit_Vis.
              intros. inv u.
          -- destruct s; try destruct u; cbn in H1.
             ++ destruct d. cbn in H1.
                rewrite <- unfold_interp in H2.

                rename H0 into KS.
                setoid_rewrite bind_trigger in H1.
                setoid_rewrite bind_trigger in KS.

                red.
                destruct (observe i) eqn: Heqi;
                  try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
                destruct H1 as (?&?&?).
                dependent destruction x.
                red in H, H0. subst.
                assert (Returns tt ta).
                { rewrite H. unfold trigger. eapply ReturnsVis; eauto.
                  unfold subevent. reflexivity.
                  constructor; reflexivity. }
                specialize (HK _ H0). pclearbot.
                eapply Interp_Prop_OomT_Vis; eauto.
                ** intros. red in H1. specialize (H1 tt).
                   eapply bisimulation_is_eq in H1. destruct a.
                   rewrite H1.
                   right; eapply CIH.
                   2 : { rewrite <- interp_tau, <- unfold_interp. reflexivity. }
                   pstep; econstructor; eauto. punfold HK.
                   rewrite <- unfold_interp. Unshelve.
                   3: exact (fun x => interp EC.L0_convert_strict (k2 x)). reflexivity.
                   intros [].
                   all : shelve.
                ** red; reflexivity.
                ** rewrite <- itree_eta in H2.
                   rewrite H2. rewrite KS.
                   rewrite interp_vis. cbn. unfold debug.
                   do 2 rewrite bind_trigger. unfold subevent, resum, ReSum_inr.
                   eapply eqit_Vis. intros. rewrite tau_eutt. reflexivity.
             ++ repeat red in HTA.
                destruct f. cbn in H1. setoid_rewrite bind_trigger in H1.
                red.
                destruct (observe i) eqn: Heqi;
                  try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
                destruct H1 as (?&?&?).
                dependent destruction x.
                red in H, H0. cbn in *; subst.
                eapply Interp_Prop_OomT_Vis; eauto.
                intros. inv a.
                red; reflexivity.
                setoid_rewrite <- itree_eta in H2. rewrite H2.
                rewrite <- unfold_interp.
                rewrite H0. cbn. rewrite interp_bind.
                rewrite interp_trigger. cbn. unfold LLVMEvents.raise.
                do 2 rewrite bind_trigger. rewrite bind_vis.
                apply eqit_Vis.
                intros [].
                Unshelve.
                all : eauto.
  Admitted.

  Lemma refine_OOM_h_L1_convert_tree_strict :
    forall {T} x_inf y_inf (RR : relation T),
      refine_OOM_h RR x_inf y_inf ->
      refine_OOM_h RR (L1_convert_tree_strict x_inf) (L1_convert_tree_strict y_inf).
  Proof.
  Admitted.

  Lemma refine_OOM_h_L2_convert_tree_strict :
    forall {T} x_inf y_inf (RR : relation T),
      refine_OOM_h RR x_inf y_inf ->
      refine_OOM_h RR (L2_convert_tree_strict x_inf) (L2_convert_tree_strict y_inf).
  Proof.
  Admitted.

  Lemma refine_OOM_h_L3_convert_tree_strict :
    forall {T} x_inf y_inf (RR : relation T),
      refine_OOM_h RR x_inf y_inf ->
      refine_OOM_h RR (L3_convert_tree_strict x_inf) (L3_convert_tree_strict y_inf).
  Proof.
    (* intros T. *)

    (* unfold refine_OOM_h, L3_convert_tree, refine_OOM_h_flip. *)
    (* intros. *)
    (* rewrite (unfold_interp y_inf). *)
    (* rewrite (unfold_interp x_inf). *)
    (* cbn. *)

    (* match goal with *)
    (* | |- interp_prop _ _ ?l ?r => remember l as i; remember r as i0 *)
    (* end. *)

    (* assert (i ≅ _interp EC.L3_convert (observe y_inf)). { *)
    (*   rewrite Heqi. reflexivity. *)
    (* } clear Heqi. *)
    (* remember (_interp EC.L3_convert (observe x_inf)). *)
    (* assert (i0 ≅ _interp EC.L3_convert (observe x_inf)). { *)
    (*   subst; reflexivity. *)
    (* } clear Heqi1 Heqi0. *)
    (* revert x_inf y_inf H i i0 H0 H1. *)

    (* pcofix CIH. *)

    (* intros * H. *)
    (* punfold H; red in H. *)
    (* remember (observe y_inf) as oy; remember (observe x_inf) as ox. *)
    (* clear Heqoy Heqox. *)

    (* induction H; pclearbot; intros; subst; auto. *)
    (* - pstep. cbn in H1, H2. *)
    (*   rewrite itree_eta in H1, H2. *)
    (*   red. *)
    (*   destruct (observe i) eqn: Heqi; destruct (observe i0) eqn: Heqi0; *)
    (*     try apply eqit_inv in H1; try apply eqit_inv in H2; cbn in H1, H2; try contradiction; auto. *)
    (*   subst; constructor; auto. *)
    (* - pstep. cbn in H1, H2. *)
    (*   rewrite itree_eta in H1, H2. *)
    (*   red. *)
    (*   destruct (observe i) eqn: Heqi; destruct (observe i0) eqn: Heqi0; *)
    (*     try apply eqit_inv in H1; try apply eqit_inv in H2; cbn in H1, H2; try contradiction; auto. *)
    (*   subst; constructor; auto. *)

    (*   right; eapply CIH; eauto; *)
    (*   rewrite unfold_interp in H1, H2; auto. *)
    (* - pstep. cbn in H1, H2. *)
    (*   rewrite itree_eta in H1, H2. *)
    (*   red. *)
    (*   destruct (observe i) eqn: Heqi; *)
    (*     try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
    (*   subst; constructor; auto. *)
    (*   rewrite unfold_interp in H1. *)
    (*   specialize (IHinterp_PropTF _ _ H1 H2). *)

    (*   punfold IHinterp_PropTF. *)
    (* - pstep. cbn in H1, H2. *)
    (*   rewrite itree_eta in H1, H2. *)
    (*   red. *)
    (*   destruct (observe i0) eqn: Heqi; *)
    (*     try apply eqit_inv in H2; cbn in H2; try contradiction; auto. *)
    (*   subst; constructor; auto. *)
    (*   rewrite unfold_interp in H2. *)
    (*   specialize (IHinterp_PropTF _ _ H1 H2). *)

    (*   punfold IHinterp_PropTF. *)
    (* - pstep. apply bisimulation_is_eq in HT1. *)
    (*   rewrite HT1 in H1. cbn in H1. *)
    (*   destruct (resum IFun A e). *)
    (*   cbn in H1. *)
    (*   repeat setoid_rewrite bind_vis in H1. *)
    (*   apply bisimulation_is_eq in H1. rewrite H1. *)
    (*   econstructor; eauto. *)
    (*   eapply eqit_Vis; intros; inv u. *)
    (* - pstep. cbn in H2, H3. red in H. *)
    (*   rewrite H in H0. *)
    (*   rename H2 into H1. *)
    (*   rename H3 into H2. *)

    (*   rewrite itree_eta in H1, H2. *)
    (*   repeat destruct e; cbn in *. *)
    (*   + rewrite bind_bind in H1. *)
    (*     unfold lift_OOM in H1. *)
    (*     rename H0 into KS. rewrite bind_trigger in KS. *)
    (*     cbn in *. *)
    (*     destruct (EC.DVC.uvalue_convert f) eqn : Hf. *)
    (*     { rewrite bind_ret_l, bind_bind in H1. *)
    (*       destruct *)
    (*         (map_monad_In args *)
    (*           (fun (elt : InterpreterStackBigIntptr.LP.Events.DV.dvalue) (_ : In elt args) => EC.DVC.dvalue_convert elt)) eqn: Hm. *)
    (*       { rewrite bind_ret_l, bind_bind in H1. *)
    (*         rewrite bind_trigger in H1. *)

    (*         destruct (observe i) eqn: Heqi; *)
    (*           try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
    (*         red. *)
    (*         setoid_rewrite Heqi. *)
    (*         destruct H1 as (?&?&?). *)
    (*         dependent destruction x. *)
    (*         red in H, H0. *)
    (*         econstructor; [ constructor | ..]; eauto; cycle 1. *)
    (*         - red; reflexivity. *)
    (*         - cbn in *. *)
    (*           rewrite <- unfold_interp in H2. *)
    (*           rewrite <- itree_eta in H2. *)
    (*           rewrite H2. rewrite KS. rewrite interp_vis. cbn. *)
    (*           rewrite bind_bind. unfold lift_OOM. *)
    (*           rewrite Hf. setoid_rewrite bind_ret_l. *)
    (*           setoid_rewrite bind_bind. rewrite Hm. *)
    (*           setoid_rewrite bind_ret_l. *)
    (*           setoid_rewrite bind_bind. *)
    (*           setoid_rewrite bind_trigger. *)
    (*           unfold subevent. rewrite H0. *)
    (*           eapply eqit_Vis. intros. *)
    (*           Unshelve. *)
    (*           3 : exact (fun u0 : E2.DV.dvalue => *)
    (*           ITree.bind match EC.DVCrev.dvalue_convert u0 with *)
    (*                     | NoOom a0 => ret a0 *)
    (*                     | Oom s => raise_oom s *)
    (*                      end (fun x1 : E1.DV.dvalue => Tau (interp EC.L3_convert (k2 x1)))). *)
    (*           reflexivity. intros. inv H. *)
    (*         - cbn. red in H1. subst. *)
    (*           eapply bisimulation_is_eq in H1. rewrite H1. *)

    (*           destruct (EC.DVCrev.dvalue_convert a) eqn: Ht. *)
    (*           + setoid_rewrite H in HK. subst. *)
    (*             rewrite subevent_subevent in H3. *)
    (*             eapply Returns_uvalue_convert_L3 in H3; eauto. *)
    (*             specialize (HK _ H3). pclearbot. *)
    (*             pose proof @bind_ret_l as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *)
    (*             pose proof @bind_ret_l as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ. *)
    (*             pstep; constructor; eauto. right; eauto. *)
    (*             eapply CIH; try rewrite <- unfold_interp; try reflexivity. *)
    (*             eapply HK. *)
    (*           + setoid_rewrite H in HK. subst. *)
    (*             unfold raiseOOM. *)
    (*             pose proof @bind_bind as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *)
    (*             pose proof @bind_trigger as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *)
    (*             pose proof @bind_bind as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *)
    (*             pose proof @bind_trigger as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *)
    (*             pstep; econstructor; eauto. unfold subevent. *)
    (*             reflexivity. } *)
    (*       { unfold raiseOOM in H1. rewrite bind_trigger in H1. *)
    (*         red. destruct (observe i) eqn: Heqi; *)
    (*           try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
    (*         destruct H1 as (?&?&?). *)
    (*         dependent destruction x. *)
    (*         red in H, H0. *)
    (*         (* rewrite H1. *) *)
    (*         econstructor; eauto. *)
    (*         - intros. inv a. *)
    (*         - red; reflexivity. *)
    (*         - cbn in *. rewrite <- itree_eta in H2. *)
    (*           rewrite H2. rewrite <- unfold_interp. *)
    (*           rewrite KS. rewrite interp_vis. cbn. *)
    (*           rewrite bind_bind. unfold lift_OOM. *)
    (*           rewrite Hf. setoid_rewrite bind_ret_l. *)
    (*           setoid_rewrite bind_bind. rewrite Hm. *)
    (*           setoid_rewrite bind_trigger. *)
    (*           setoid_rewrite bind_vis. *)
    (*           unfold subevent. rewrite H0. *)
    (*           eapply eqit_Vis. intros. inv u0. } } *)

    (*       unfold raiseOOM in H1. rewrite bind_trigger in H1. *)
    (*       red. destruct (observe i) eqn: Heqi; *)
    (*         try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
    (*       destruct H1 as (?&?&?). *)
    (*       dependent destruction x. *)
    (*       red in H, H0. cbn in *. *)
    (*       econstructor; eauto. *)
    (*     * intros. inv a. *)
    (*     * red; reflexivity. *)
    (*     * rewrite <- itree_eta in H2. rewrite H2. *)
    (*       rewrite <- unfold_interp. rewrite KS. *)
    (*       rewrite interp_vis. *)
    (*       cbn. rewrite bind_bind. unfold lift_OOM. rewrite Hf. *)
    (*       setoid_rewrite bind_trigger. *)
    (*       setoid_rewrite bind_vis. *)
    (*       unfold subevent. rewrite H0. *)
    (*       eapply eqit_Vis. intros. inv u. *)
    (*   + destruct s. *)
    (*     { destruct p. *)
    (*       cbn in *. *)
    (*       destruct (EC.DVC.uvalue_convert x) eqn:Ht. *)
    (*       - cbn in *. *)
    (*         rewrite bind_ret_l in H1. *)
    (*         rewrite bind_trigger in H1. *)
    (*         rewrite bind_vis in H1. *)
    (*         red. *)
    (*         destruct (observe i) eqn: Heqi; *)
    (*           try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
    (*         destruct H1 as (?&?&?). *)
    (*         cbn in *. *)
    (*         dependent destruction x. *)
    (*         red in H, H0. *)
    (*         econstructor; eauto. *)
    (*         repeat red. intros. inv a. *)
    (*         red; reflexivity. *)
    (*         setoid_rewrite <- itree_eta in H2. rewrite H2. *)
    (*         rewrite <- unfold_interp. *)
    (*         rewrite H0. rewrite bind_trigger. *)
    (*         rewrite interp_vis. *)
    (*         cbn. *)
    (*         setoid_rewrite bind_trigger. rewrite bind_vis. cbn in *; subst. eapply eqit_Vis. *)
    (*         intros. inv u. *)

    (*         rewrite bind_trigger in H1. *)


    (*       destruct s; try destruct u; cbn in H1. *)
    (*       -- repeat red in HTA. *)
    (*           unfold raiseUB in H1. rewrite bind_trigger in H1. *)
    (*           red. *)
    (*           destruct (observe i) eqn: Heqi; *)
    (*             try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
    (*           destruct H1 as (?&?&?). *)
    (*           dependent destruction x. *)
    (*           red in H, H0. *)
    (*           econstructor; eauto. *)
    (*           repeat red. intros. inv a. *)
    (*           red; reflexivity. *)
    (*           setoid_rewrite <- itree_eta in H2. rewrite H2. *)
    (*           rewrite <- unfold_interp. *)
    (*           rewrite H0. rewrite bind_trigger. *)
    (*           rewrite interp_vis. *)
    (*           cbn. *)
    (*           setoid_rewrite bind_trigger. rewrite bind_vis. cbn in *; subst. eapply eqit_Vis. *)
    (*           intros. inv u. *)
    (*       -- destruct s; try destruct u; cbn in H1. *)
    (*          ++ destruct d. cbn in H1. *)
    (*             rewrite <- unfold_interp in H2. *)

    (*             rename H0 into KS. *)
    (*             setoid_rewrite bind_trigger in H1. *)
    (*             setoid_rewrite bind_trigger in KS. *)

    (*             red. *)
    (*             destruct (observe i) eqn: Heqi; *)
    (*               try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
    (*             destruct H1 as (?&?&?). *)
    (*             dependent destruction x. *)
    (*             red in H, H0. subst. *)
    (*             assert (Returns tt ta). *)
    (*             { rewrite H. unfold trigger. eapply ReturnsVis; eauto. *)
    (*               unfold subevent. reflexivity. *)
    (*               constructor; reflexivity. } *)
    (*             specialize (HK _ H0). pclearbot. *)
    (*             econstructor; eauto. *)
    (*             ** intros. red in H1. specialize (H1 tt). *)
    (*                eapply bisimulation_is_eq in H1. destruct a. *)
    (*                rewrite H1. *)
    (*                right; eapply CIH. *)
    (*                2 : { rewrite <- interp_tau, <- unfold_interp. reflexivity. } *)
    (*                pstep; econstructor; eauto. punfold HK. *)
    (*                rewrite <- unfold_interp. Unshelve. *)
    (*                16 : exact (fun x => interp EC.L3_convert (k2 x)). reflexivity. *)
    (*                all : shelve. *)
    (*             ** red; reflexivity. *)
    (*             ** rewrite <- itree_eta in H2. *)
    (*                rewrite H2. rewrite KS. *)
    (*                rewrite interp_vis. cbn. unfold debug. *)
    (*                do 2 rewrite bind_trigger. unfold subevent, resum, ReSum_inr. *)
    (*                eapply eqit_Vis. intros. rewrite tau_eutt. reflexivity. *)
    (*          ++ repeat red in HTA. *)
    (*             destruct f. cbn in H1. setoid_rewrite bind_trigger in H1. *)
    (*             red. *)
    (*             destruct (observe i) eqn: Heqi; *)
    (*               try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
    (*             destruct H1 as (?&?&?). *)
    (*             dependent destruction x. *)
    (*             red in H, H0. cbn in *; subst. *)
    (*             econstructor; eauto. *)
    (*             intros. inv a. *)
    (*             red; reflexivity. *)
    (*             setoid_rewrite <- itree_eta in H2. rewrite H2. *)
    (*             rewrite <- unfold_interp. *)
    (*             rewrite H0. cbn. rewrite interp_bind. *)
    (*             rewrite interp_trigger. cbn. unfold LLVMEvents.raise. *)
    (*             do 2 rewrite bind_trigger. rewrite bind_vis. *)
    (*             apply eqit_Vis; intros; inv u. *)


    (*     } *)
    (*     destruct s. *)
    (*     * unfold raiseOOM in H1. *)
    (*       destruct o. *)
    (*       cbn in H1. *)
    (*       rewrite bind_bind, bind_trigger in H1. *)
    (*       rewrite itree_eta in H1, H2. *)
    (*       red. *)
    (*       destruct (observe i) eqn: Heqi; *)
    (*         try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
    (*       destruct H1 as (?&?&?). *)
    (*       dependent destruction x. *)
    (*       red in H, H0. cbn in *. *)
    (*       econstructor; eauto. *)
    (*       -- intros. inv a. *)
    (*       -- red; reflexivity. *)
    (*       -- rewrite <- itree_eta in H2. rewrite H2. *)
    (*          rewrite <- unfold_interp. rewrite H0. *)
    (*          rewrite bind_trigger. *)
    (*          rewrite interp_vis. cbn. do 2 setoid_rewrite bind_trigger. *)
    (*          rewrite bind_vis. subst. *)
    (*          apply eqit_Vis; intros; inv u. *)
    (*     * destruct s; try destruct u; cbn in H1. *)
    (*       -- repeat red in HTA. *)
    (*           unfold raiseUB in H1. rewrite bind_trigger in H1. *)
    (*           red. *)
    (*           destruct (observe i) eqn: Heqi; *)
    (*             try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
    (*           destruct H1 as (?&?&?). *)
    (*           dependent destruction x. *)
    (*           red in H, H0. *)
    (*           econstructor; eauto. *)
    (*           repeat red. intros. inv a. *)
    (*           red; reflexivity. *)
    (*           setoid_rewrite <- itree_eta in H2. rewrite H2. *)
    (*           rewrite <- unfold_interp. *)
    (*           rewrite H0. rewrite bind_trigger. *)
    (*           rewrite interp_vis. *)
    (*           cbn. *)
    (*           setoid_rewrite bind_trigger. rewrite bind_vis. cbn in *; subst. eapply eqit_Vis. *)
    (*           intros. inv u. *)
    (*       -- destruct s; try destruct u; cbn in H1. *)
    (*          ++ destruct d. cbn in H1. *)
    (*             rewrite <- unfold_interp in H2. *)

    (*             rename H0 into KS. *)
    (*             setoid_rewrite bind_trigger in H1. *)
    (*             setoid_rewrite bind_trigger in KS. *)

    (*             red. *)
    (*             destruct (observe i) eqn: Heqi; *)
    (*               try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
    (*             destruct H1 as (?&?&?). *)
    (*             dependent destruction x. *)
    (*             red in H, H0. subst. *)
    (*             assert (Returns tt ta). *)
    (*             { rewrite H. unfold trigger. eapply ReturnsVis; eauto. *)
    (*               unfold subevent. reflexivity. *)
    (*               constructor; reflexivity. } *)
    (*             specialize (HK _ H0). pclearbot. *)
    (*             econstructor; eauto. *)
    (*             ** intros. red in H1. specialize (H1 tt). *)
    (*                eapply bisimulation_is_eq in H1. destruct a. *)
    (*                rewrite H1. *)
    (*                right; eapply CIH. *)
    (*                2 : { rewrite <- interp_tau, <- unfold_interp. reflexivity. } *)
    (*                pstep; econstructor; eauto. punfold HK. *)
    (*                rewrite <- unfold_interp. Unshelve. *)
    (*                16 : exact (fun x => interp EC.L3_convert (k2 x)). reflexivity. *)
    (*                all : shelve. *)
    (*             ** red; reflexivity. *)
    (*             ** rewrite <- itree_eta in H2. *)
    (*                rewrite H2. rewrite KS. *)
    (*                rewrite interp_vis. cbn. unfold debug. *)
    (*                do 2 rewrite bind_trigger. unfold subevent, resum, ReSum_inr. *)
    (*                eapply eqit_Vis. intros. rewrite tau_eutt. reflexivity. *)
    (*          ++ repeat red in HTA. *)
    (*             destruct f. cbn in H1. setoid_rewrite bind_trigger in H1. *)
    (*             red. *)
    (*             destruct (observe i) eqn: Heqi; *)
    (*               try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
    (*             destruct H1 as (?&?&?). *)
    (*             dependent destruction x. *)
    (*             red in H, H0. cbn in *; subst. *)
    (*             econstructor; eauto. *)
    (*             intros. inv a. *)
    (*             red; reflexivity. *)
    (*             setoid_rewrite <- itree_eta in H2. rewrite H2. *)
    (*             rewrite <- unfold_interp. *)
    (*             rewrite H0. cbn. rewrite interp_bind. *)
    (*             rewrite interp_trigger. cbn. unfold LLVMEvents.raise. *)
    (*             do 2 rewrite bind_trigger. rewrite bind_vis. *)
    (*             apply eqit_Vis; intros; inv u. *)

    (*             Unshelve. *)
    (*             all : eauto. *)
    (*             all : inv x.     *)
  Admitted.

  Opaque FinPROV.initial_provenance.
  Opaque InfPROV.initial_provenance.
  (* Opaque dvalue_convert_lazy. *)
  (* Opaque uvalue_convert_lazy. *)
  (* Opaque dvalue_refine_lazy. *)
  (* Opaque uvalue_refine_lazy. *)
  (* Opaque DVCrev.dvalue_convert_lazy. *)
  (* Opaque DVCrev.uvalue_convert_lazy. *)
  (* Opaque DVCrev.dvalue_refine_lazy. *)
  (* Opaque DVCrev.uvalue_refine_lazy. *)
  Opaque dvalue_convert_strict.
  Opaque uvalue_convert_strict.
  Opaque dvalue_refine_strict.
  Opaque uvalue_refine_strict.
  (* Opaque DVCrev.dvalue_convert_strict. *)
  (* Opaque DVCrev.uvalue_convert_strict. *)
  (* Opaque DVCrev.dvalue_refine_strict. *)
  (* Opaque DVCrev.uvalue_refine_strict. *)

  Lemma refine_OOM_h_L4_convert_tree_strict :
    forall {T} x_inf y_inf (RR : relation T),
      refine_OOM_h RR x_inf y_inf ->
      refine_OOM_h RR (L4_convert_tree_strict x_inf) (L4_convert_tree_strict y_inf).
  Proof.
    intros T.

    unfold refine_OOM_h, L4_convert_tree_strict, refine_OOM_h_flip.
    intros.
    rewrite (unfold_interp y_inf).
    rewrite (unfold_interp x_inf).
    cbn.

    match goal with
    | |- interp_prop_oom_l _ _ ?l ?r => remember l as i; remember r as i0
    end.

    assert (i ≅ _interp EC.L4_convert_strict (observe y_inf)). {
      rewrite Heqi. reflexivity.
    } clear Heqi.
    remember (_interp EC.L4_convert_strict (observe x_inf)).
    assert (i0 ≅ _interp EC.L4_convert_strict (observe x_inf)). {
      subst; reflexivity.
    } clear Heqi1 Heqi0.
    revert x_inf y_inf H i i0 H0 H1.

    pcofix CIH.

    intros * H.
    punfold H; red in H.
    remember (observe y_inf) as oy; remember (observe x_inf) as ox.
    clear Heqoy Heqox.

    induction H; pclearbot; intros; subst; auto.
    - pstep. cbn in H1, H2.
      rewrite itree_eta in H1, H2.
      red.
      destruct (observe i) eqn: Heqi; destruct (observe i0) eqn: Heqi0;
        try apply eqit_inv in H1; try apply eqit_inv in H2; cbn in H1, H2; try contradiction; auto.
      subst; constructor; auto.
    - pstep. cbn in H1, H2.
      rewrite itree_eta in H1, H2.
      red.
      destruct (observe i) eqn: Heqi; destruct (observe i0) eqn: Heqi0;
        try apply eqit_inv in H1; try apply eqit_inv in H2; cbn in H1, H2; try contradiction; auto.
      subst; constructor; auto.

      right; eapply CIH; eauto;
      rewrite unfold_interp in H1, H2; auto.
    - pstep. cbn in H1, H2.
      rewrite itree_eta in H1, H2.
      red.
      destruct (observe i) eqn: Heqi;
        try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
      subst; constructor; auto.
      rewrite unfold_interp in H1.
      specialize (IHinterp_prop_oomTF _ _ H1 H2).
      punfold IHinterp_prop_oomTF.
    - pstep. cbn in H1, H2.
      rewrite itree_eta in H1, H2.
      red.
      destruct (observe i0) eqn: Heqi;
        try apply eqit_inv in H2; cbn in H2; try contradiction; auto.
      subst; constructor; auto.
      rewrite unfold_interp in H2.
      specialize (IHinterp_prop_oomTF _ _ H1 H2).
      punfold IHinterp_prop_oomTF.
    - pstep. apply bisimulation_is_eq in HT1.
      rewrite HT1 in H1. cbn in H1.
      destruct (resum IFun A e).
      cbn in H1.
      repeat setoid_rewrite bind_vis in H1.
      apply bisimulation_is_eq in H1. rewrite H1.
      econstructor; eauto.
      eapply eqit_Vis; intros; inv u.
    - discriminate.
    - pstep. cbn in H2, H3. red in H.
      rewrite H in H0.
      rename H2 into H1.
      rename H3 into H2.

      rewrite itree_eta in H1, H2.
      repeat destruct e; cbn in *.
      + rewrite bind_bind in H1.
        unfold lift_OOM in H1.
        rename H0 into KS. rewrite bind_trigger in KS.
        cbn in *.
        destruct (DVC.uvalue_convert_strict f) eqn : Hf.
        { rewrite bind_ret_l, bind_bind in H1.
          destruct
            (map_monad_In args
              (fun (elt : E1.DV.dvalue) (_ : In elt args) => DVC.dvalue_convert_strict elt)) eqn: Hm.
          { rewrite bind_ret_l, bind_bind in H1.
            rewrite bind_trigger in H1.

            destruct (observe i) eqn: Heqi;
              try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
            red.
            setoid_rewrite Heqi.
            destruct H1 as (?&?&?).
            dependent destruction x.
            red in H, H0.
            econstructor; [ constructor | ..]; eauto; cycle 1.
            - red; reflexivity.
            - cbn in *.
              rewrite <- unfold_interp in H2.
              rewrite <- itree_eta in H2.
              rewrite H2. rewrite KS. rewrite interp_vis. cbn.
              rewrite bind_bind. unfold lift_OOM.
              rewrite Hf. setoid_rewrite bind_ret_l.
              setoid_rewrite bind_bind. rewrite Hm.
              setoid_rewrite bind_ret_l.
              setoid_rewrite bind_bind.
              setoid_rewrite bind_trigger.
              unfold subevent. rewrite H0.
              eapply eqit_Vis. intros.
              Unshelve.
              3 : exact (fun u0 : E2.DV.dvalue =>
              ITree.bind match DVCrev.dvalue_convert_strict u0 with
                        | NoOom a0 => ret a0
                        | Oom s => raise_oom s
                         end (fun x1 : E1.DV.dvalue => Tau (interp EC.L4_convert_strict (k2 x1)))).
              reflexivity. intros. inv H.
            - cbn. red in H1. subst.
              eapply bisimulation_is_eq in H1. rewrite H1.

              destruct (DVCrev.dvalue_convert_strict a) eqn: Ht.
              + setoid_rewrite H in HK. subst.
                (* TODO: Originally used Returns_uvalue_convert_L0
                applied to H3... But it seems Returns is weird with
                the vis case and allows any value to be
                returned...? *)
                rename H3 into H3'.
                pose proof Returns_ExternalCall_L0 d f t args as H3.
                specialize (HK d).
                forward HK.
                admit.
                pclearbot.
                pose proof @bind_ret_l as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ.
                pose proof @bind_ret_l as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ.
                pstep; constructor; eauto. right; eauto.
                eapply CIH; try rewrite <- unfold_interp; try reflexivity.
                eapply HK.
              + setoid_rewrite H in HK. subst.
                unfold raiseOOM.
                pose proof @bind_bind as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ.
                pose proof @bind_trigger as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ.
                pose proof @bind_bind as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ.
                pose proof @bind_trigger as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ.
                pstep; econstructor; eauto. unfold subevent.
                reflexivity. }
          { unfold raiseOOM in H1. rewrite bind_trigger in H1.
            red. destruct (observe i) eqn: Heqi;
              try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
            destruct H1 as (?&?&?).
            dependent destruction x.
            red in H, H0.
            (* rewrite H1. *)
            eapply Interp_Prop_OomT_Vis; eauto.
            - intros. inv a.
            - red; reflexivity.
            - cbn in *. rewrite <- itree_eta in H2.
              rewrite H2. rewrite <- unfold_interp.
              rewrite KS. rewrite interp_vis. cbn.
              rewrite bind_bind. unfold lift_OOM.
              rewrite Hf. setoid_rewrite bind_ret_l.
              setoid_rewrite bind_bind. rewrite Hm.
              setoid_rewrite bind_trigger.
              setoid_rewrite bind_vis.
              unfold subevent. rewrite H0.
              eapply eqit_Vis. intros. inv u0. } }

          unfold raiseOOM in H1. rewrite bind_trigger in H1.
          red. destruct (observe i) eqn: Heqi;
            try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
          destruct H1 as (?&?&?).
          dependent destruction x.
          red in H, H0. cbn in *.
          inv e.
          observe_vis.
          eapply Interp_Prop_OomT_Vis_OOM_L; eauto.
          reflexivity.
          observe_vis.
          eapply Interp_Prop_OomT_Vis_OOM_L; eauto.
          reflexivity.
      + destruct s.
        * unfold raiseOOM in H1.
          destruct o.
          cbn in H1.
          rewrite bind_bind, bind_trigger in H1.
          rewrite itree_eta in H1, H2.
          red.
          destruct (observe i) eqn: Heqi;
            try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
          destruct H1 as (?&?&?).
          dependent destruction x.
          red in H, H0. cbn in *.
          inv e.
          observe_vis.
          eapply Interp_Prop_OomT_Vis_OOM_L; eauto.
          reflexivity.
          observe_vis.
          eapply Interp_Prop_OomT_Vis_OOM_L; eauto.
          reflexivity.
        * destruct s; try destruct u; cbn in H1.
          -- repeat red in HTA.
              unfold raiseUB in H1. rewrite bind_trigger in H1.
              red.
              destruct (observe i) eqn: Heqi;
                try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
              destruct H1 as (?&?&?).
              dependent destruction x.
              red in H, H0.
              eapply Interp_Prop_OomT_Vis; eauto.
              repeat red. intros. inv a.
              red; reflexivity.
              setoid_rewrite <- itree_eta in H2. rewrite H2.
              rewrite <- unfold_interp.
              rewrite H0. rewrite bind_trigger.
              rewrite interp_vis.
              cbn.
              setoid_rewrite bind_trigger. rewrite bind_vis. cbn in *; subst. eapply eqit_Vis.
              intros. inv u.
          -- destruct s; try destruct u; cbn in H1.
             ++ destruct d. cbn in H1.
                rewrite <- unfold_interp in H2.

                rename H0 into KS.
                setoid_rewrite bind_trigger in H1.
                setoid_rewrite bind_trigger in KS.

                red.
                destruct (observe i) eqn: Heqi;
                  try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
                destruct H1 as (?&?&?).
                dependent destruction x.
                red in H, H0. subst.
                assert (Returns tt ta).
                { rewrite H. unfold trigger. eapply ReturnsVis; eauto.
                  unfold subevent. reflexivity.
                  constructor; reflexivity. }
                specialize (HK _ H0). pclearbot.
                eapply Interp_Prop_OomT_Vis; eauto.
                ** intros. red in H1. specialize (H1 tt).
                   eapply bisimulation_is_eq in H1. destruct a.
                   rewrite H1.
                   right; eapply CIH.
                   2 : { rewrite <- interp_tau, <- unfold_interp. reflexivity. }
                   pstep; econstructor; eauto. punfold HK.
                   rewrite <- unfold_interp. Unshelve.
                   8 : exact (fun x => interp EC.L4_convert_strict (k2 x)). reflexivity.
                   all : shelve.
                ** red; reflexivity.
                ** rewrite <- itree_eta in H2.
                   rewrite H2. rewrite KS.
                   rewrite interp_vis. cbn. unfold debug.
                   do 2 rewrite bind_trigger. unfold subevent, resum, ReSum_inr.
                   eapply eqit_Vis. intros. rewrite tau_eutt. reflexivity.
             ++ repeat red in HTA.
                destruct f. cbn in H1. setoid_rewrite bind_trigger in H1.
                red.
                destruct (observe i) eqn: Heqi;
                  try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
                destruct H1 as (?&?&?).
                dependent destruction x.
                red in H, H0. cbn in *; subst.
                eapply Interp_Prop_OomT_Vis; eauto.
                intros. inv a.
                red; reflexivity.
                setoid_rewrite <- itree_eta in H2. rewrite H2.
                rewrite <- unfold_interp.
                rewrite H0. cbn. rewrite interp_bind.
                rewrite interp_trigger. cbn. unfold LLVMEvents.raise.
                do 2 rewrite bind_trigger. rewrite bind_vis.
                apply eqit_Vis.
                intros [].

                Unshelve.
                all : eauto.
                all : inv x.
  Admitted.

  Lemma refine_OOM_h_L5_convert_tree_strict :
    forall {T} x_inf y_inf (RR : relation T),
      refine_OOM_h RR x_inf y_inf ->
      refine_OOM_h RR (L5_convert_tree_strict x_inf) (L5_convert_tree_strict y_inf).
  Proof.
    intros T.
    apply refine_OOM_h_L4_convert_tree_strict.
  Qed.

  Lemma refine_OOM_h_L6_convert_tree_strict :
    forall {T} x_inf y_inf (RR : relation T),
      refine_OOM_h RR x_inf y_inf ->
      refine_OOM_h RR (L6_convert_tree_strict x_inf) (L6_convert_tree_strict y_inf).
  Proof.
    intros T.
    apply refine_OOM_h_L5_convert_tree_strict.
  Qed.

  (** Model *)
  Import DynamicTypes TypToDtyp CFG.

  (*
  Definition event_refine_lazy A B (e1 : IS1.LP.Events.L0 A) (e2 : IS2.LP.Events.L0 B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.ExternalCall dt1 f1 args1), inl1 (E2.ExternalCall dt2 f2 args2) =>
                _
            | inr1 (inl1 (E1.Intrinsic dt1 name1 args1)), inr1 (inl1 (E2.Intrinsic dt2 name2 args2)) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* Globals *)
            | inr1 (inr1 (inr1 (inl1 (inl1 e1)))), inr1 (inr1 (inr1 (inl1 (inl1 e2)))) =>
                _ (* Locals *)
            | inr1 (inr1 (inr1 (inl1 (inr1 e1)))), inr1 (inr1 (inr1 (inl1 (inr1 e2)))) =>
                _ (* Stack *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { (* Doesn't say anything about return value... *)
      apply (dt1 = dt2 /\
               uvalue_refine_lazy f1 f2 /\
               Forall2 dvalue_refine_lazy args1 args2).
    }

    (* Intrinsics *)
    { apply (dt1 = dt2 /\
               name1 = name2 /\
               Forall2 dvalue_refine_lazy args1 args2).
    }

    (* Globals *)
    { inversion e1.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_refine_lazy dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

    (* Locals *)
    { inversion e1.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_refine_lazy dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

    (* Stack *)
    { inversion e1.
      - (* Stack Push *)
        destruct e2 eqn:HE2.
        + apply (local_refine_lazy args args0).
        + apply False.
      - (* Stack Pop *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply True.
    }

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
                 dvalue_refine_lazy a a0).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_lazy a a0 /\
                 uvalue_refine_lazy v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      destruct e2 eqn:HE2.
      apply ((Pre <-> Pre0) /\
               uvalue_refine_lazy x x0).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.
   *)

  Definition event_refine_strict A B (e1 : IS1.LP.Events.L0 A) (e2 : IS2.LP.Events.L0 B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.ExternalCall dt1 f1 args1), inl1 (E2.ExternalCall dt2 f2 args2) =>
                _
            | inr1 (inl1 (E1.Intrinsic dt1 name1 args1)), inr1 (inl1 (E2.Intrinsic dt2 name2 args2)) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* Globals *)
            | inr1 (inr1 (inr1 (inl1 (inl1 e1)))), inr1 (inr1 (inr1 (inl1 (inl1 e2)))) =>
                _ (* Locals *)
            | inr1 (inr1 (inr1 (inl1 (inr1 e1)))), inr1 (inr1 (inr1 (inl1 (inr1 e2)))) =>
                _ (* Stack *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { (* Doesn't say anything about return value... *)
      apply (dt1 = dt2 /\
               uvalue_refine_strict f1 f2 /\
               Forall2 dvalue_refine_strict args1 args2).
    }

    (* Intrinsics *)
    { apply (dt1 = dt2 /\
               name1 = name2 /\
               Forall2 dvalue_refine_strict args1 args2).
    }

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

    (* Stack *)
    { inversion e1.
      - (* Stack Push *)
        destruct e2 eqn:HE2.
        + apply (local_refine_strict args args0).
        + apply False.
      - (* Stack Pop *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply True.
    }

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

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      destruct e2 eqn:HE2.
      apply ((Pre -> Pre0) /\
               uvalue_refine_strict x x0).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { destruct e1 as [e1_msg ?].
      destruct e2 as [e2_msg ?].
      exact (e1_msg = e2_msg).
    }

    (* FailureE *)
    { destruct e1 as [e1_msg ?].
      destruct e2 as [e2_msg ?].
      exact (e1_msg = e2_msg).
    }
  Defined.

  Definition L1_refine_strict A B (e1 : IS1.LP.Events.L1 A) (e2 : IS2.LP.Events.L1 B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.ExternalCall dt1 f1 args1), inl1 (E2.ExternalCall dt2 f2 args2) =>
                _
            | inr1 (inl1 (E1.Intrinsic dt1 name1 args1)), inr1 (inl1 (E2.Intrinsic dt2 name2 args2)) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 (inl1 e1))), inr1 (inr1 (inl1 (inl1 e2))) =>
                _ (* Locals *)
            | inr1 (inr1 (inl1 (inr1 e1))), inr1 (inr1 (inl1 (inr1 e2))) =>
                _ (* Stack *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2))))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { (* Doesn't say anything about return value... *)
      apply (dt1 = dt2 /\
               uvalue_refine_strict f1 f2 /\
               Forall2 dvalue_refine_strict args1 args2).
    }

    (* Intrinsics *)
    { apply (dt1 = dt2 /\
               name1 = name2 /\
               Forall2 dvalue_refine_strict args1 args2).
    }

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

    (* Stack *)
    { inversion e1.
      - (* Stack Push *)
        destruct e2 eqn:HE2.
        + apply (local_refine_strict args args0).
        + apply False.
      - (* Stack Pop *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply True.
    }

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

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      destruct e2 eqn:HE2.
      apply ((Pre -> Pre0) /\
               uvalue_refine_strict x x0).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { destruct e1 as [e1_msg ?].
      destruct e2 as [e2_msg ?].
      exact (e1_msg = e2_msg).
    }

    (* FailureE *)
    { destruct e1 as [e1_msg ?].
      destruct e2 as [e2_msg ?].
      exact (e1_msg = e2_msg).
    }
  Defined.

  Definition L2_refine_strict A B (e1 : IS1.LP.Events.L2 A) (e2 : IS2.LP.Events.L2 B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.ExternalCall dt1 f1 args1), inl1 (E2.ExternalCall dt2 f2 args2) =>
                _
            | inr1 (inl1 (E1.Intrinsic dt1 name1 args1)), inr1 (inl1 (E2.Intrinsic dt2 name2 args2)) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e0)))), inr1 (inr1 (inr1 (inr1 (inl1 e1)))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { (* Doesn't say anything about return value... *)
      apply (dt1 = dt2 /\
               uvalue_refine_strict f1 f2 /\
               Forall2 dvalue_refine_strict args1 args2).
    }

    (* Intrinsics *)
    { apply (dt1 = dt2 /\
               name1 = name2 /\
               Forall2 dvalue_refine_strict args1 args2).
    }

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

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      destruct e2 eqn:HE2.
      apply ((Pre -> Pre0) /\
               uvalue_refine_strict x x0).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { destruct e1 as [e1_msg ?].
      destruct e2 as [e2_msg ?].
      exact (e1_msg = e2_msg).
    }

    (* FailureE *)
    { destruct e1 as [e1_msg ?].
      destruct e2 as [e2_msg ?].
      exact (e1_msg = e2_msg).
    }
  Defined.

  Definition L3_refine_strict A B (e1 : IS1.LP.Events.L3 A) (e2 : IS2.LP.Events.L3 B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.ExternalCall dt1 f1 args1), inl1 (E2.ExternalCall dt2 f2 args2) =>
                _
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* PickE *)
            | inr1 (inr1 (inl1 e0)), inr1 (inr1 (inl1 e1)) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 e1)))), inr1 (inr1 (inr1 (inr1 (inr1 e2)))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { (* Doesn't say anything about return value... *)
      apply (dt1 = dt2 /\
               uvalue_refine_strict f1 f2 /\
               Forall2 dvalue_refine_strict args1 args2).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      destruct e2 eqn:HE2.
      apply ((Pre -> Pre0) /\
               uvalue_refine_strict x x0).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { destruct e1 as [e1_msg ?].
      destruct e2 as [e2_msg ?].
      exact (e1_msg = e2_msg).
    }

    (* FailureE *)
    { destruct e1 as [e1_msg ?].
      destruct e2 as [e2_msg ?].
      exact (e1_msg = e2_msg).
    }
  Defined.

  (*
  Definition event_converted_lazy A B (e1 : IS1.LP.Events.L0 A) (e2 : IS2.LP.Events.L0 B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.ExternalCall dt1 f1 args1), inl1 (E2.ExternalCall dt2 f2 args2) =>
                _
            | inr1 (inl1 (E1.Intrinsic dt1 name1 args1)), inr1 (inl1 (E2.Intrinsic dt2 name2 args2)) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* Globals *)
            | inr1 (inr1 (inr1 (inl1 (inl1 e1)))), inr1 (inr1 (inr1 (inl1 (inl1 e2)))) =>
                _ (* Locals *)
            | inr1 (inr1 (inr1 (inl1 (inr1 e1)))), inr1 (inr1 (inr1 (inl1 (inr1 e2)))) =>
                _ (* Stack *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { (* Doesn't say anything about return value... *)
      apply (dt1 = dt2 /\
               uvalue_converted_lazy f1 f2 /\
               Forall2 dvalue_converted_lazy args1 args2).
    }

    (* Intrinsics *)
    { apply (dt1 = dt2 /\
               name1 = name2 /\
               Forall2 dvalue_converted_lazy args1 args2).
    }

    (* Globals *)
    { inversion e1.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_converted_lazy dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

    (* Locals *)
    { inversion e1.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_converted_lazy dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

    (* Stack *)
    { inversion e1.
      - (* Stack Push *)
        destruct e2 eqn:HE2.
        + apply (local_refine_lazy args args0).
        + apply False.
      - (* Stack Pop *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply True.
    }

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
                 dvalue_converted_lazy a a0).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_converted_lazy a a0 /\
                 uvalue_converted_lazy v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      destruct e2 eqn:HE2.
      apply ((Pre <-> Pre0) /\
               uvalue_converted_lazy x x0).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.
   *)
  (*
  Definition event_res_refine_lazy A B (e1 : IS1.LP.Events.L0 A) (res1 : A) (e2 : IS2.LP.Events.L0 B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* Globals *)
            | inr1 (inr1 (inr1 (inl1 (inl1 e1)))), inr1 (inr1 (inr1 (inl1 (inl1 e2)))) =>
                _ (* Locals *)
            | inr1 (inr1 (inr1 (inl1 (inr1 e1)))), inr1 (inr1 (inr1 (inl1 (inr1 e2)))) =>
                _ (* Stack *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { inv e1.
      inv e2.

      apply (t = t0 /\
               uvalue_refine_lazy f f0 /\
               Forall2 dvalue_refine_lazy args args0 /\
               dvalue_refine_lazy res1 res2
            ).
    }

    (* Intrinsics *)
    { inv e1.
      inv e2.
      apply (t = t0 /\
               f = f0 /\
               Forall2 dvalue_refine_lazy args args0 /\
               dvalue_refine_lazy res1 res2
            ).
    }

    (* Globals *)
    { inversion e1; subst.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_refine_lazy dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                   dvalue_refine_lazy res1 res2
                ).
    }

    (* Locals *)
    { inversion e1; subst.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_refine_lazy dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                uvalue_refine_lazy res1 res2).
    }

    (* Stack *)
    { inversion e1; subst.
      - (* Stack Push *)
        destruct e2 eqn:HE2.
        + apply (local_refine_lazy args args0).
        + apply False.
      - (* Stack Pop *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply True.
    }

    (* MemoryE *)
    { inversion e1; subst.
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
                 align = align0 /\
                 dvalue_refine_lazy res1 res2).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_refine_lazy a a0 /\
                 uvalue_refine_lazy res1 res2).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_lazy a a0 /\
                 uvalue_refine_lazy v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1; subst.
      destruct e2 eqn:HE2.
      destruct res1 as [r1 P1].
      destruct res2 as [r2 P2].
      apply ((Pre <-> Pre0) /\
               uvalue_refine_lazy x x0 /\
               dvalue_refine_lazy r1 r2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.
  *)

  Definition event_res_refine_strict A B (e1 : IS1.LP.Events.L0 A) (res1 : A) (e2 : IS2.LP.Events.L0 B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* Globals *)
            | inr1 (inr1 (inr1 (inl1 (inl1 e1)))), inr1 (inr1 (inr1 (inl1 (inl1 e2)))) =>
                _ (* Locals *)
            | inr1 (inr1 (inr1 (inl1 (inr1 e1)))), inr1 (inr1 (inr1 (inl1 (inr1 e2)))) =>
                _ (* Stack *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { inv e1.
      inv e2.

      apply (t = t0 /\
               uvalue_refine_strict f f0 /\
               Forall2 dvalue_refine_strict args args0 /\
               dvalue_refine_strict res1 res2
            ).
    }

    (* Intrinsics *)
    { inv e1.
      inv e2.
      apply (t = t0 /\
               f = f0 /\
               Forall2 dvalue_refine_strict args args0 /\
               dvalue_refine_strict res1 res2
            ).
    }

    (* Globals *)
    { inversion e1; subst.
      - (* Global write *)
        destruct e2 eqn:HE2.
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

    (* Locals *)
    { inversion e1; subst.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_refine_strict dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                uvalue_refine_strict res1 res2).
    }

    (* Stack *)
    { inversion e1; subst.
      - (* Stack Push *)
        destruct e2 eqn:HE2.
        + apply (local_refine_strict args args0).
        + apply False.
      - (* Stack Pop *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply True.
    }

    (* MemoryE *)
    { inversion e1; subst.
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
                 align = align0 /\
                 dvalue_refine_strict res1 res2).
      - (* Load *)
        destruct e2 eqn:HE2.
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

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1; subst.
      destruct e2 eqn:HE2.
      destruct res1 as [r1 P1].
      destruct res2 as [r2 P2].
      apply ((Pre -> Pre0) /\
               uvalue_refine_strict x x0 /\
               dvalue_refine_strict r1 r2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { destruct e1 as [e1_msg ?].
      destruct e2 as [e2_msg ?].
      exact (e1_msg = e2_msg).
    }

    (* FailureE *)
    { destruct e1 as [e1_msg ?].
      destruct e2 as [e2_msg ?].
      exact (e1_msg = e2_msg).
    }
  Defined.

  Definition L1_res_refine_strict A B (e1 : IS1.LP.Events.L1 A) (res1 : A) (e2 : IS2.LP.Events.L1 B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 (inl1 e1))), inr1 (inr1 (inl1 (inl1 e2))) =>
                _ (* Locals *)
            | inr1 (inr1 (inl1 (inr1 e1))), inr1 (inr1 (inl1 (inr1 e2))) =>
                _ (* Stack *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2))))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { inv e1.
      inv e2.

      apply (t = t0 /\
               uvalue_refine_strict f f0 /\
               Forall2 dvalue_refine_strict args args0 /\
               dvalue_refine_strict res1 res2
            ).
    }

    (* Intrinsics *)
    { inv e1.
      inv e2.
      apply (t = t0 /\
               f = f0 /\
               Forall2 dvalue_refine_strict args args0 /\
               dvalue_refine_strict res1 res2
            ).
    }

    (* Locals *)
    { inversion e1; subst.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_refine_strict dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                uvalue_refine_strict res1 res2).
    }

    (* Stack *)
    { inversion e1; subst.
      - (* Stack Push *)
        destruct e2 eqn:HE2.
        + apply (local_refine_strict args args0).
        + apply False.
      - (* Stack Pop *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply True.
    }

    (* MemoryE *)
    { inversion e1; subst.
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
                 align = align0 /\
                 dvalue_refine_strict res1 res2).
      - (* Load *)
        destruct e2 eqn:HE2.
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

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1; subst.
      destruct e2 eqn:HE2.
      destruct res1 as [r1 P1].
      destruct res2 as [r2 P2].
      apply ((Pre -> Pre0) /\
               uvalue_refine_strict x x0 /\
               dvalue_refine_strict r1 r2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { destruct e1 as [e1_msg ?].
      destruct e2 as [e2_msg ?].
      exact (e1_msg = e2_msg).
    }

    (* FailureE *)
    { destruct e1 as [e1_msg ?].
      destruct e2 as [e2_msg ?].
      exact (e1_msg = e2_msg).
    }
  Defined.

  Definition L2_res_refine_strict A B (e1 : IS1.LP.Events.L2 A) (res1 : A) (e2 : IS2.LP.Events.L2 B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e0)))), inr1 (inr1 (inr1 (inr1 (inl1 e1)))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).
    (* External Calls *)
    { inv e1.
      inv e2.

      apply (t = t0 /\
               uvalue_refine_strict f f0 /\
               Forall2 dvalue_refine_strict args args0 /\
               dvalue_refine_strict res1 res2
            ).
    }

    (* Intrinsics *)
    { inv e1.
      inv e2.
      apply (t = t0 /\
               f = f0 /\
               Forall2 dvalue_refine_strict args args0 /\
               dvalue_refine_strict res1 res2
            ).
    }

    (* MemoryE *)
    { inversion e1; subst.
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
                 align = align0 /\
                 dvalue_refine_strict res1 res2).
      - (* Load *)
        destruct e2 eqn:HE2.
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

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1; subst.
      destruct e2 eqn:HE2.
      destruct res1 as [r1 P1].
      destruct res2 as [r2 P2].
      apply ((Pre -> Pre0) /\
               uvalue_refine_strict x x0 /\
               dvalue_refine_strict r1 r2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { destruct e1 as [e1_msg ?].
      destruct e2 as [e2_msg ?].
      exact (e1_msg = e2_msg).
    }

    (* FailureE *)
    { destruct e1 as [e1_msg ?].
      destruct e2 as [e2_msg ?].
      exact (e1_msg = e2_msg).
    }
  Defined.

  Definition L3_res_refine_strict A B (e1 : IS1.LP.Events.L3 A) (res1 : A) (e2 : IS2.LP.Events.L3 B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* PickE *)
            | inr1 (inr1 (inl1 e0)), inr1 (inr1 (inl1 e1)) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 e1)))), inr1 (inr1 (inr1 (inr1 (inr1 e2)))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { inv e1.
      inv e2.

      apply (t = t0 /\
               uvalue_refine_strict f f0 /\
               Forall2 dvalue_refine_strict args args0 /\
               dvalue_refine_strict res1 res2
            ).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1; subst.
      destruct e2 eqn:HE2.
      destruct res1 as [r1 P1].
      destruct res2 as [r2 P2].
      apply ((Pre <-> Pre0) /\
               uvalue_refine_strict x x0 /\
               dvalue_refine_strict r1 r2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { destruct e1 as [e1_msg ?].
      destruct e2 as [e2_msg ?].
      exact (e1_msg = e2_msg).
    }

    (* FailureE *)
    { destruct e1 as [e1_msg ?].
      destruct e2 as [e2_msg ?].
      exact (e1_msg = e2_msg).
    }
  Defined.

  (*
  Definition L0'_refine_lazy A B (e1 : IS1.LP.Events.L0' A) (e2 : IS2.LP.Events.L0' B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.Call dt1 f1 args1), inl1 (E2.Call dt2 f2 args2) =>
                _ (* Calls *)
            | inr1 e1, inr1 e2 =>
                event_refine_lazy _ _ e1 e2
            | _, _ =>
                False
            end).

    (* Calls *)
    { (* Doesn't say anything about return value... *)
      apply (dt1 = dt2 /\
               uvalue_refine_lazy f1 f2 /\
               Forall2 uvalue_refine_lazy args1 args2).
    }
  Defined.

  Definition call_refine_lazy (A B : Type) (c1 : IS1.LP.Events.CallE A) (c2 : CallE B) : Prop.
  Proof.
    (* Calls *)
    { (* Doesn't say anything about return value... *)
      inv c1.
      inv c2.
      apply (t = t0 /\
               uvalue_refine_lazy f f0 /\
               Forall2 uvalue_refine_lazy args args0).
    }
  Defined.
   *)

  Definition call_refine_strict (A B : Type) (c1 : IS1.LP.Events.CallE A) (c2 : CallE B) : Prop.
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

  (*
  Definition call_res_refine_lazy (A B : Type) (c1 : IS1.LP.Events.CallE A) (res1 : A) (c2 : CallE B) (res2 : B) : Prop.
  Proof.
    (* Calls *)
    { inv c1.
      inv c2.
      apply (t = t0 /\
               uvalue_refine_lazy f f0 /\
               Forall2 uvalue_refine_lazy args args0 /\
               uvalue_refine_lazy res1 res2).
    }
  Defined.
   *)

  Definition call_res_refine_strict (A B : Type) (c1 : IS1.LP.Events.CallE A) (res1 : A) (c2 : CallE B) (res2 : B) : Prop.
  Proof.
    (* Calls *)
    { inv c1.
      inv c2.
      apply (t = t0 /\
               uvalue_refine_strict f f0 /\
               Forall2 uvalue_refine_strict args args0 /\
               uvalue_refine_strict res1 res2).
    }
  Defined.

  Definition L0'_refine_strict A B (e1 : IS1.LP.Events.L0' A) (e2 : IS2.LP.Events.L0' B) : Prop
    := (sum_prerel call_refine_strict event_refine_strict) _ _ e1 e2.

  (*
  Definition L0'_res_refine_lazy A B (e1 : IS1.LP.Events.L0' A) (res1 : A) (e2 : IS2.LP.Events.L0' B) (res2 : B) : Prop
    := (sum_postrel call_res_refine_lazy event_res_refine_lazy) _ _ e1 res1 e2 res2.
   *)

  Definition L0'_res_refine_strict A B (e1 : IS1.LP.Events.L0' A) (res1 : A) (e2 : IS2.LP.Events.L0' B) (res2 : B) : Prop
    := (sum_postrel call_res_refine_strict event_res_refine_strict) _ _ e1 res1 e2 res2.

  (*
  Definition exp_E_refine_lazy A B (e1 : IS1.LP.Events.exp_E A) (e2 : IS2.LP.Events.exp_E B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _ (* Globals *)
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* Locals *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* Globals *)
    { inversion e1.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_refine_lazy dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

    (* Locals *)
    { inversion e1.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_refine_lazy dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

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
                 dvalue_refine_lazy a a0).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_lazy a a0 /\
                 uvalue_refine_lazy v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      destruct e2 eqn:HE2.
      apply ((Pre <-> Pre0) /\
               uvalue_refine_lazy x x0).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.
   *)

  Definition exp_E_refine_strict A B (e1 : IS1.LP.Events.exp_E A) (e2 : IS2.LP.Events.exp_E B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _ (* Globals *)
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* Locals *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

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

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      destruct e2 eqn:HE2.
      apply ((Pre -> Pre0) /\
               uvalue_refine_strict x x0).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { destruct e1 as [e1_msg ?].
      destruct e2 as [e2_msg ?].
      exact (e1_msg = e2_msg).
    }

    (* FailureE *)
    { destruct e1 as [e1_msg ?].
      destruct e2 as [e2_msg ?].
      exact (e1_msg = e2_msg).
    }
  Defined.

  (*
  Definition exp_E_res_refine_lazy A B (e1 : IS1.LP.Events.exp_E A) (res1 : A) (e2 : IS2.LP.Events.exp_E B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _ (* Globals *)
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* Locals *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* Globals *)
    { inversion e1; subst.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_refine_lazy dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                   dvalue_refine_lazy res1 res2
                ).
    }

    (* Locals *)
    { inversion e1; subst.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_refine_lazy dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                uvalue_refine_lazy res1 res2).
    }

    (* MemoryE *)
    { inversion e1; subst.
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
                 align = align0 /\
                 dvalue_refine_lazy res1 res2).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_refine_lazy a a0 /\
                 uvalue_refine_lazy res1 res2).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_lazy a a0 /\
                 uvalue_refine_lazy v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1; subst.
      destruct e2 eqn:HE2.
      destruct res1 as [r1 P1].
      destruct res2 as [r2 P2].
      apply ((Pre <-> Pre0) /\
               uvalue_refine_lazy x x0 /\
            dvalue_refine_lazy r1 r2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.
   *)
  
  Definition exp_E_res_refine_strict A B (e1 : IS1.LP.Events.exp_E A) (res1 : A) (e2 : IS2.LP.Events.exp_E B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _ (* Globals *)
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* Locals *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* Globals *)
    { inversion e1; subst.
      - (* Global write *)
        destruct e2 eqn:HE2.
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

    (* Locals *)
    { inversion e1; subst.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_refine_strict dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                uvalue_refine_strict res1 res2).
    }

    (* MemoryE *)
    { inversion e1; subst.
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
                 align = align0 /\
                 dvalue_refine_strict res1 res2).
      - (* Load *)
        destruct e2 eqn:HE2.
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

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1; subst.
      destruct e2 eqn:HE2.
      destruct res1 as [r1 P1].
      destruct res2 as [r2 P2].
      apply ((Pre -> Pre0) /\
               uvalue_refine_strict x x0 /\
            dvalue_refine_strict r1 r2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { destruct e1 as [e1_msg ?].
      destruct e2 as [e2_msg ?].
      exact (e1_msg = e2_msg).
    }

    (* FailureE *)
    { destruct e1 as [e1_msg ?].
      destruct e2 as [e2_msg ?].
      exact (e1_msg = e2_msg).
    }
  Defined.

  Definition instr_E_refine_strict A B (e1 : IS1.LP.Events.instr_E A) (e2 : IS2.LP.Events.instr_E B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                call_refine_strict _ _ e1 e2
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                (* Intrinsics *)
                _
            | inr1 (inr1 e1), inr1 (inr1 e2) =>
                exp_E_refine_strict _ _ e1 e2
            | _, _ =>
                False
            end).

    (* Intrinsics *)
    { inv e1.
      inv e2.
      apply (t = t0 /\
               f = f0 /\
               Forall2 dvalue_refine_strict args args0
            ).
    }
  Defined.

  (*
  Definition instr_E_res_refine_lazy A B (e1 : IS1.LP.Events.instr_E A) (res1 : A) (e2 : IS2.LP.Events.instr_E B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                call_res_refine_lazy _ _ e1 res1 e2 res2
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                (* Intrinsics *)
                _
            | inr1 (inr1 e1), inr1 (inr1 e2) =>
                exp_E_res_refine_lazy _ _ e1 res1 e2 res2
            | _, _ =>
                False
            end).

    (* Intrinsics *)
    { inv e1.
      inv e2.
      apply (t = t0 /\
               f = f0 /\
               Forall2 dvalue_refine_lazy args args0
            ).
    }
  Defined.
   *)
  
  Definition instr_E_res_refine_strict A B (e1 : IS1.LP.Events.instr_E A) (res1 : A) (e2 : IS2.LP.Events.instr_E B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                call_res_refine_strict _ _ e1 res1 e2 res2
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                (* Intrinsics *)
                _
            | inr1 (inr1 e1), inr1 (inr1 e2) =>
                exp_E_res_refine_strict _ _ e1 res1 e2 res2
            | _, _ =>
                False
            end).

    (* Intrinsics *)
    { inv e1.
      inv e2.
      apply (t = t0 /\
               f = f0 /\
               Forall2 dvalue_refine_strict args args0 /\
               dvalue_refine_strict res1 res2
            ).
    }
  Defined.

  (*
  Definition L0_E1E2_rutt_lazy t1 t2
    : Prop :=
    rutt
      event_refine_lazy
      event_res_refine_lazy
      dvalue_refine_lazy
      t1 t2.
  *)

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
      (local_refine_strict × stack_refine_strict × (global_refine_strict × dvalue_refine_strict))
      t1 t2 (OOM:=OOME).

  Definition model_E1E2_L0_orutt_strict p1 p2 :=
    L0_E1E2_orutt_strict
      (LLVM1.denote_vellvm (DTYPE_I 32%N) "main" LLVM1.main_args (convert_types (mcfg_of_tle p1)))
      (LLVM2.denote_vellvm (DTYPE_I 32%N) "main" LLVM2.main_args (convert_types (mcfg_of_tle p2))).

  Definition model_E1E2_L1_orutt_strict p1 p2 :=
    L1_E1E2_orutt_strict
      (LLVM1.model_oom_L1 p1)
      (LLVM2.model_oom_L1 p2).

  Definition model_E1E2_L2_orutt_strict p1 p2 :=
    L2_E1E2_orutt_strict
      (LLVM1.model_oom_L2 p1)
      (LLVM2.model_oom_L2 p2).

  Import TranslateFacts.
  Import RecursionFacts.

  (* TODO: Could be worth considering making sure this isn't behind a module? *)
  Lemma function_name_eq_equiv :
    forall id1 id2,
      LLVM1.function_name_eq id1 id2 = LLVM2.function_name_eq id1 id2.
  Proof.
    intros id1 id2.
    unfold LLVM1.function_name_eq, LLVM2.function_name_eq.
    reflexivity.
  Qed.

  Lemma trigger_alloca_E1E2_rutt_strict_sound :
    forall dt n osz,
      rutt event_refine_strict event_res_refine_strict dvalue_refine_strict
        (trigger (IS1.LP.Events.Alloca dt n osz)) (trigger (Alloca dt n osz)).
  Proof.
    intros dt n osz.
    apply rutt_trigger.
    - cbn. auto.
    - intros t1 t2 H.
      cbn in *.
      tauto.
  Qed.

  Lemma trigger_globalwrite_E1E2_rutt_strict_sound :
    forall gid r1 r2,
      dvalue_refine_strict r1 r2 ->
      rutt event_refine_strict event_res_refine_strict eq (trigger (GlobalWrite gid r1))
        (trigger (GlobalWrite gid r2)).
  Proof.
    intros gid r1 r2 H.
    apply rutt_trigger.
    - cbn. auto.
    - intros [] [] _.
      auto.
  Qed.

  Lemma allocate_declarations_E1E2_rutt_strict_sound :
    forall a,
      rutt event_refine_strict event_res_refine_strict eq (LLVM1.allocate_declaration a) (allocate_declaration a).
  Proof.
    intros a.
    induction a.
    unfold LLVM1.allocate_declaration, allocate_declaration.
    cbn.
    repeat setoid_rewrite function_name_eq_equiv.
    break_match.
    - apply rutt_Ret; reflexivity.
    - eapply rutt_bind with (RR:=dvalue_refine_strict).
      { apply trigger_alloca_E1E2_rutt_strict_sound.
      }

      intros r1 r2 H.
      apply trigger_globalwrite_E1E2_rutt_strict_sound.
      auto.
  Qed.

  Lemma allocate_one_E1E2_rutt_strict_sound :
    forall (m_declarations : list (LLVMAst.declaration dtyp))
      (m_definitions : list (LLVMAst.definition dtyp (cfg dtyp))),
      rutt event_refine_strict event_res_refine_strict eq
        (map_monad LLVM1.allocate_declaration (m_declarations ++ map LLVMAst.df_prototype m_definitions))
        (map_monad allocate_declaration (m_declarations ++ map LLVMAst.df_prototype m_definitions)).
  Proof.
    intros m_declarations m_definitions.
    remember (m_declarations ++ map LLVMAst.df_prototype m_definitions) as declarations.
    clear m_declarations m_definitions Heqdeclarations.
    induction declarations.
    - cbn.
      apply rutt_Ret.
      reflexivity.
    - cbn.
      eapply rutt_bind with (RR:=eq).
      { apply allocate_declarations_E1E2_rutt_strict_sound.
      }

      intros [] [] _.
      eapply rutt_bind with (RR:=eq); auto.

      intros r1 r2 R1R2.
      subst.
      apply rutt_Ret.
      reflexivity.
  Qed.

  Lemma allocate_global_E1E2_rutt_strict_sound :
    forall (m_globals : list (LLVMAst.global dtyp)),
      rutt event_refine_strict event_res_refine_strict eq
        (map_monad LLVM1.allocate_global m_globals)
        (map_monad allocate_global m_globals).
  Proof.
    intros m_globals.
    induction m_globals.
    - cbn; apply rutt_Ret; reflexivity.
    - cbn.
      eapply rutt_bind with (RR:=eq).
      { eapply rutt_bind with (RR:=dvalue_refine_strict).
        { apply trigger_alloca_E1E2_rutt_strict_sound.
        }

        intros r1 r2 H.
        apply trigger_globalwrite_E1E2_rutt_strict_sound; auto.
      }

      intros [] [] _.
      eapply rutt_bind with (RR:=eq); auto.

      intros r1 r2 R1R2.
      subst.
      apply rutt_Ret.
      reflexivity.
  Qed.

  Lemma exp_E_refine_strict_event_refine_strict :
    forall A B (e1 : IS1.LP.Events.exp_E A) (e2 : exp_E B),
      exp_E_refine_strict A B e1 e2 ->
      event_refine_strict A B (IS1.LP.Events.exp_to_L0 e1) (exp_to_L0 e2).
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

          { destruct u, u0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct d, d0; cbn; auto. }
          { destruct f, f0; cbn; auto. }

        }
  Qed.

  Lemma exp_E_refine_strict_instr_E_refine_strict :
    forall A B (e1 : IS1.LP.Events.exp_E A) (e2 : exp_E B),
      exp_E_refine_strict A B e1 e2 ->
      instr_E_refine_strict A B (IS1.LP.Events.exp_to_instr e1) (exp_to_instr e2).
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

          { destruct u, u0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct d, d0; cbn; auto. }
          { destruct f, f0; cbn; auto. }

        }
  Qed.

  Lemma instr_E_refine_strict_L0'_refine_strict :
    forall A B (e1 : IS1.LP.Events.instr_E A) (e2 : instr_E B),
      instr_E_refine_strict A B e1 e2 ->
      L0'_refine_strict A B (IS1.LP.Events.instr_to_L0' e1) (instr_to_L0' e2).
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
          { destruct s, s0; cbn; constructor; auto.
            destruct s, s0; try solve [ cbn in H; contradiction ].
            - (* Debug *)
              destruct d, d0; cbn in *; auto.
            - (* Failure *)
              destruct f, f0.
              cbn in *; auto.
          }
        }
  Qed.

  Lemma event_refine_strict_exp_E_refine_strict_inv :
    forall A B (e1 : IS1.LP.Events.exp_E A) (e2 : exp_E B) a b,
      event_res_refine_strict A B (IS1.LP.Events.exp_to_L0 e1) a (exp_to_L0 e2) b ->
      exp_E_refine_strict A B e1 e2.
  Proof.
    intros A B e1 e2 a b H.
    destruct e1, e2.
    2-3: (cbn in *;
          break_match_hyp; subst; cbn in *; auto).

    2: {
      repeat (break_match_hyp; subst; cbn in *; auto).
      all: inv Heql0.
    }

    - destruct l, l0.
      2,3: (cbn in H;
            (repeat break_match_hyp; try contradiction)).

      all: cbn in *; tauto.
    - destruct s, s0.
      2,3: (cbn in H;
            (repeat break_match_hyp; try contradiction)).

      + destruct l, l0.
        2,3: (cbn in H;
              (repeat break_match_hyp; try contradiction)).

        all: cbn in *; tauto.

      + destruct s, s0.
        2,3: (cbn in H;
              (repeat break_match_hyp; try contradiction)).

        { destruct m, m0; cbn in *; tauto.
        }

        { destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct p, p0; cbn in *; auto.
            destruct a, b.
            tauto.
          }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct o, o0; cbn; auto. }

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

  Lemma event_res_refine_strict_exp_E_res_refine_strict_inv :
    forall A B (e1 : IS1.LP.Events.exp_E A) (e2 : exp_E B) a b,
      event_res_refine_strict A B (IS1.LP.Events.exp_to_L0 e1) a (exp_to_L0 e2) b ->
      exp_E_res_refine_strict A B e1 a e2 b.
  Proof.
    intros A B e1 e2 a b H.
    destruct e1, e2.
    2-3: (cbn in *;
          break_match_hyp; subst; cbn in *; auto).

    2: {
      repeat (break_match_hyp; subst; cbn in *; auto).
      all: inv Heql0.
    }

    - destruct l, l0.
      2,3: (cbn in H;
            (repeat break_match_hyp; try contradiction)).

      all: cbn in *; tauto.
    - destruct s, s0.
      2,3: (cbn in H;
            (repeat break_match_hyp; try contradiction)).

      + destruct l, l0.
        2,3: (cbn in H;
              (repeat break_match_hyp; try contradiction)).

        all: cbn in *; tauto.

      + destruct s, s0.
        2,3: (cbn in H;
              (repeat break_match_hyp; try contradiction)).

        { destruct m, m0; cbn in *; tauto.
        }

        { destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct p, p0; cbn in *; auto.
          }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct o, o0; cbn; auto. }

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

  Lemma L0'_res_refine_strict_instr_E_res_refine_strict_inv :
    forall A B (e1 : IS1.LP.Events.instr_E A) (e2 : instr_E B) a b,
      L0'_res_refine_strict A B (IS1.LP.Events.instr_to_L0' e1) a (instr_to_L0' e2) b ->
      instr_E_res_refine_strict A B e1 a e2 b.
  Proof.
    intros A B e1 e2 a b H.
    destruct e1, e2.
    1-3:
      (cbn in *;
       repeat (first [ tauto
                     | break_match_hyp; subst; cbn in *; auto
                     | repeat match goal with
                         | H: L0'_res_refine_strict _ _ _ _ _ _ |- _ =>
                             inv H; subst_existT; unfold call_res_refine_strict in *; cbn in *
                         end
                 ]
         )).

    - destruct s, s0.
      1-3:
        (cbn in *;
         repeat (first [ tauto
                       | break_match_hyp; subst; cbn in *; auto
                       | repeat match goal with
                           | H: L0'_res_refine_strict _ _ _ _ _ _ |- _ =>
                               inv H; subst_existT; unfold call_res_refine_strict in *; cbn in *
                           end
                   ]
        )).

      destruct e, e0.
      1-3:
        (cbn in *;
         repeat (first [ tauto
                       | break_match_hyp; subst; cbn in *; auto
                       | repeat match goal with
                           | H: L0'_res_refine_strict _ _ _ _ _ _ |- _ =>
                               inv H; subst_existT; unfold call_res_refine_strict in *; cbn in *
                           end
                   ]
        )).

      + destruct s;
          (cbn in *;
           repeat (first [ tauto
                         | break_match_hyp; subst; cbn in *; auto
                         | repeat match goal with
                             | H: L0'_res_refine_strict _ _ _ _ _ _ |- _ =>
                                 inv H; subst_existT; unfold call_res_refine_strict in *; cbn in *
                             end
                     ]
          )).
  Qed.

  Lemma translate_exp_to_L0_E1E2_rutt :
    forall {R1 R2} {RR : R1 -> R2 -> Prop} t1 t2,
      rutt exp_E_refine_strict exp_E_res_refine_strict RR
        t1
        t2 ->
      rutt event_refine_strict event_res_refine_strict RR
        (translate IS1.LP.Events.exp_to_L0 t1)
        (translate exp_to_L0 t2).
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

  Lemma translate_exp_to_L0_E1E2_orutt :
    forall {R1 R2} {RR : R1 -> R2 -> Prop} t1 t2,
      orutt exp_E_refine_strict exp_E_res_refine_strict RR
        t1
        t2
        (OOM:=OOME) ->
      orutt event_refine_strict event_res_refine_strict RR
        (translate IS1.LP.Events.exp_to_L0 t1)
        (translate exp_to_L0 t2)
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
      destruct e2; inv CONTRA.
      destruct s; inv H3.
      reflexivity.
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
    forall A B (e1 : IS1.LP.Events.exp_E A) (e2 : exp_E B) a b,
      instr_E_res_refine_strict A B (IS1.LP.Events.exp_to_instr e1) a (exp_to_instr e2) b ->
      exp_E_res_refine_strict A B e1 a e2 b.
  Proof.
    intros A B e1 e2 a b H.
    destruct e1, e2.
    1-3:(cbn in *;
       repeat (first [ tauto
                     | break_match_hyp; subst; cbn in *; auto
                     | repeat match goal with
                         | H: instr_E_res_refine_strict _ _ _ _ _ _ |- _ =>
                             inv H; subst_existT; unfold call_res_refine_strict in *; cbn in *
                         end
                 ]
         )).

    - destruct s, s0.
      1-3:
        (cbn in *;
         repeat (first [ tauto
                       | break_match_hyp; subst; cbn in *; auto
                       | repeat match goal with
                           | H: instr_E_res_refine_strict _ _ _ _ _ _ |- _ =>
                               inv H; subst_existT; unfold call_res_refine_strict in *; cbn in *
                           end
                   ]
        )).

      destruct s, s0.
      1-3:
        (cbn in *;
         repeat (first [ tauto
                       | break_match_hyp; subst; cbn in *; auto
                       | repeat match goal with
                           | H: L0'_res_refine_strict _ _ _ _ _ _ |- _ =>
                               inv H; subst_existT; unfold call_res_refine_strict in *; cbn in *
                           end
                   ]
        )).

      + destruct s;
          (cbn in *;
           repeat (first [ tauto
                         | break_match_hyp; subst; cbn in *; auto
                         | repeat match goal with
                             | H: L0'_res_refine_strict _ _ _ _ _ _ |- _ =>
                                 inv H; subst_existT; unfold call_res_refine_strict in *; cbn in *
                             end
                     ]
          )).
  Qed.

  Lemma translate_instr_to_L0'_E1E2_rutt_strict :
    forall {R1 R2} {RR : R1 -> R2 -> Prop} t1 t2,
      rutt instr_E_refine_strict instr_E_res_refine_strict RR t1 t2 ->
      rutt L0'_refine_strict L0'_res_refine_strict RR
        (translate IS1.LP.Events.instr_to_L0' t1)
        (translate instr_to_L0' t2).
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
        (translate IS1.LP.Events.instr_to_L0' t1)
        (translate instr_to_L0' t2)
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
      destruct e2.
      unfold instr_to_L0' in CONTRA.
      inv CONTRA.
      cbn in *; break_match_hyp; inv CONTRA.
      cbn in *; break_match_hyp; inv H3.
      cbn in *; break_match_hyp; inv H4.
      reflexivity.
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
        (translate IS1.LP.Events.exp_to_instr t1)
        (translate exp_to_instr t2).
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
        (translate IS1.LP.Events.exp_to_instr t1)
        (translate exp_to_instr t2)
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
      inv CONTRA.
      reflexivity.
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

  (*
  Definition event_res_converted_lazy A B (e1 : IS1.LP.Events.L0 A) (res1 : A) (e2 : IS2.LP.Events.L0 B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* Globals *)
            | inr1 (inr1 (inr1 (inl1 (inl1 e1)))), inr1 (inr1 (inr1 (inl1 (inl1 e2)))) =>
                _ (* Locals *)
            | inr1 (inr1 (inr1 (inl1 (inr1 e1)))), inr1 (inr1 (inr1 (inl1 (inr1 e2)))) =>
                _ (* Stack *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { inv e1.
      inv e2.

      apply (t = t0 /\
               uvalue_converted_lazy f f0 /\
               Forall2 dvalue_converted_lazy args args0 /\
               dvalue_converted_lazy res1 res2
            ).
    }

    (* Intrinsics *)
    { inv e1.
      inv e2.
      apply (t = t0 /\
               f = f0 /\
               Forall2 dvalue_converted_lazy args args0 /\
               dvalue_converted_lazy res1 res2
            ).
    }

    (* Globals *)
    { inversion e1; subst.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_converted_lazy dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                   dvalue_converted_lazy res1 res2
                ).
    }

    (* Locals *)
    { inversion e1; subst.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_converted_lazy dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                uvalue_converted_lazy res1 res2).
    }

    (* Stack *)
    { inversion e1; subst.
      - (* Stack Push *)
        destruct e2 eqn:HE2.
        + apply (local_refine_lazy args args0).
        + apply False.
      - (* Stack Pop *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply True.
    }

    (* MemoryE *)
    { inversion e1; subst.
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
                 align = align0 /\
                 dvalue_converted_lazy res1 res2).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_converted_lazy a a0 /\
                 uvalue_converted_lazy res1 res2).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_converted_lazy a a0 /\
                 uvalue_converted_lazy v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1; subst.
      destruct e2 eqn:HE2.
      destruct res1 as [r1 P1].
      destruct res2 as [r2 P2].
      apply ((Pre <-> Pre0) /\
               uvalue_converted_lazy x x0 /\
               dvalue_converted_lazy r1 r2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.
  *)
  (*
  Definition L0'_converted_lazy A B (e1 : IS1.LP.Events.L0' A) (e2 : IS2.LP.Events.L0' B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.Call dt1 f1 args1), inl1 (E2.Call dt2 f2 args2) =>
                _ (* Calls *)
            | inr1 e1, inr1 e2 =>
                event_refine_lazy _ _ e1 e2
            | _, _ =>
                False
            end).

    (* Calls *)
    { (* Doesn't say anything about return value... *)
      apply (dt1 = dt2 /\
               uvalue_refine_lazy f1 f2 /\
               Forall2 uvalue_refine_lazy args1 args2).
    }
  Defined.
  *)
  (*
  Definition L0'_res_converted_lazy A B (e1 : IS1.LP.Events.L0' A) (res1 : A) (e2 : IS2.LP.Events.L0' B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.Call dt1 f1 args1), inl1 (E2.Call dt2 f2 args2) =>
                _ (* Calls *)
            | inr1 e1, inr1 e2 =>
                event_res_converted_lazy _ _ e1 res1 e2 res2
            | _, _ =>
                False
            end).

    (* Calls *)
    { inv c.
      inv c0.

      apply (dt1 = dt2 /\
               uvalue_converted_lazy f1 f2 /\
               Forall2 uvalue_converted_lazy args1 args2 /\
               uvalue_converted_lazy res1 res2
            ).
    }
  Defined.
   *)
  (* 
  Definition call_converted_lazy (A B : Type) (c1 : IS1.LP.Events.CallE A) (c2 : CallE B) : Prop.
  Proof.
    (* Calls *)
    { (* Doesn't say anything about return value... *)
      inv c1.
      inv c2.
      apply (t = t0 /\
               uvalue_converted_lazy f f0 /\
               Forall2 uvalue_converted_lazy args args0).
    }
  Defined.
   *)
  (*
  Definition call_res_converted_lazy (A B : Type) (c1 : IS1.LP.Events.CallE A) (res1 : A) (c2 : CallE B) (res2 : B) : Prop.
  Proof.
    (* Calls *)
    { inv c1.
      inv c2.
      apply (t = t0 /\
               uvalue_converted_lazy f f0 /\
               Forall2 uvalue_converted_lazy args args0 /\
               uvalue_converted_lazy res1 res2).
    }
  Defined.

  Definition exp_E_converted_lazy A B (e1 : IS1.LP.Events.exp_E A) (e2 : IS2.LP.Events.exp_E B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _ (* Globals *)
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* Locals *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* Globals *)
    { inversion e1.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_converted_lazy dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

    (* Locals *)
    { inversion e1.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_converted_lazy dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

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
                 dvalue_converted_lazy a a0).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_converted_lazy a a0 /\
                 uvalue_converted_lazy v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      destruct e2 eqn:HE2.
      apply ((Pre <-> Pre0) /\
               uvalue_converted_lazy x x0).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.

  Definition exp_E_res_converted_lazy A B (e1 : IS1.LP.Events.exp_E A) (res1 : A) (e2 : IS2.LP.Events.exp_E B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _ (* Globals *)
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* Locals *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* Globals *)
    { inversion e1; subst.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_converted_lazy dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                   dvalue_converted_lazy res1 res2
                ).
    }

    (* Locals *)
    { inversion e1; subst.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_converted_lazy dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                uvalue_converted_lazy res1 res2).
    }

    (* MemoryE *)
    { inversion e1; subst.
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
                 align = align0 /\
                 dvalue_converted_lazy res1 res2).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_converted_lazy a a0 /\
                 uvalue_converted_lazy res1 res2).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_converted_lazy a a0 /\
                 uvalue_converted_lazy v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1; subst.
      destruct e2 eqn:HE2.
      destruct res1 as [r1 P1].
      destruct res2 as [r2 P2].
      apply ((Pre <-> Pre0) /\
               uvalue_converted_lazy x x0 /\
            dvalue_converted_lazy r1 r2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.

  Definition L0_E1E2_rutt_converted_lazy t1 t2
    : Prop :=
    rutt
      event_converted_lazy
      event_res_converted_lazy
      dvalue_converted_lazy
      t1 t2.

  Definition model_E1E2_rutt_converted_lazy p1 p2 :=
    L0_E1E2_rutt_converted_lazy
      (LLVM1.denote_vellvm (DTYPE_I 32%N) "main" LLVM1.main_args (convert_types (mcfg_of_tle p1)))
      (LLVM2.denote_vellvm (DTYPE_I 32%N) "main" LLVM2.main_args (convert_types (mcfg_of_tle p2))).

  Lemma allocate_one_E1E2_rutt_converted_lazy_sound :
    forall (m_declarations : list (LLVMAst.declaration dtyp))
      (m_definitions : list (LLVMAst.definition dtyp (cfg dtyp))),
      rutt event_converted_lazy event_res_converted_lazy eq
        (map_monad LLVM1.allocate_declaration (m_declarations ++ map LLVMAst.df_prototype m_definitions))
        (map_monad allocate_declaration (m_declarations ++ map LLVMAst.df_prototype m_definitions)).
  Proof.
  Abort.

  Lemma allocate_global_E1E2_rutt_converted_lazy_sound :
    forall (m_globals : list (LLVMAst.global dtyp)),
      rutt event_converted_lazy event_res_converted_lazy eq
        (map_monad LLVM1.allocate_global m_globals)
        (map_monad allocate_global m_globals).
  Proof.
  Abort.

  Lemma translate_exp_to_L0_E1E2_converted_lazy_rutt :
    forall {R1 R2} {RR : R1 -> R2 -> Prop} t1 t2,
      rutt exp_E_converted_lazy exp_E_res_converted_lazy RR
        t1
        t2 ->
      rutt event_converted_lazy event_res_converted_lazy RR
        (translate IS1.LP.Events.exp_to_L0 t1)
        (translate exp_to_L0 t2).
  Proof.
  Abort.

  Lemma translate_LU_to_exp_lookup_id_rutt_lazy :
    forall id : LLVMAst.ident,
      rutt exp_E_refine_lazy exp_E_res_refine_lazy uvalue_refine_lazy
        (translate IS1.LP.Events.LU_to_exp (IS1.LLVM.D.lookup_id id)) (translate LU_to_exp (lookup_id id)).
  Proof.
    intros id.
    destruct id.
    - cbn.
      repeat rewrite translate_bind.
      repeat rewrite translate_trigger.
      repeat setoid_rewrite translate_ret.

      repeat rewrite bind_trigger.
      apply rutt_Vis;
        [cbn; auto|].

      intros * ?.
      apply rutt_Ret.
      apply dvalue_refine_lazy_dvalue_to_uvalue.
      destruct H.
      auto.
    - cbn.
      repeat rewrite translate_bind.
      repeat rewrite translate_trigger.
      repeat setoid_rewrite translate_ret.

      repeat rewrite bind_trigger.
      apply rutt_Vis;
        [cbn; auto|].

      intros * ?.
      apply rutt_Ret.
      destruct H.
      auto.
  Qed.
   *)
  
  Lemma translate_LU_to_exp_lookup_id_orutt :
    forall id : LLVMAst.ident,
      orutt exp_E_refine_strict exp_E_res_refine_strict uvalue_refine_strict
        (translate IS1.LP.Events.LU_to_exp (IS1.LLVM.D.lookup_id id)) (translate LU_to_exp (lookup_id id))
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

  (* TODO: move this ltac, and probably use more *)
  Ltac rewrite_uvalue_convert_strict :=
    repeat
      match goal with
      | H: uvalue_convert_strict _ = _ |- _ =>
          rewrite H
      end.

  Ltac solve_pick_uvalue_orutt :=
    apply orutt_trigger; cbn;
    [ split;
      [ tauto
      | unfold_uvalue_refine_strict_goal;
        rewrite_uvalue_convert_strict;
        cbn;
        reflexivity
      ]
    | intros [t1] [t2] [_ [REF1 REF2]];
      cbn; auto
    | intros o CONTRA;
      inv CONTRA
    ].

  (* TODO: Should I move this out of LangRefine and into some kind of
     utility module based on DvalueConversions.v? *)
  Lemma pick_your_poison_orutt :
    forall r1 r2,
      uvalue_refine_strict r1 r2 ->
      orutt exp_E_refine_strict exp_E_res_refine_strict
        dvalue_refine_strict (IS1.LLVM.D.pick_your_poison r1)
        (pick_your_poison r2)
        (OOM:=OOME).
  Proof.
    intros r1 r2 H.

    unfold pick_your_poison, IS1.LLVM.D.pick_your_poison.
    rewrite uvalue_refine_strict_equation in H.
    destruct r1; rewrite uvalue_convert_strict_equation in H; cbn in *;
      try solve
        [
          inv H; cbn;
          apply orutt_Ret;
          rewrite dvalue_refine_strict_equation, dvalue_convert_strict_equation; auto
        | break_match_hyp; inv H;
          try (break_match_hyp; inv H1);
          unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick in *;
          cbn;

          eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2));
          [ solve_pick_uvalue_orutt
          | intros [?r1] [?r2] ?H0;
            cbn in *;
            apply orutt_Ret; auto
          ]
        ].
    - break_match_hyp; inv H; cbn.
      apply orutt_Ret.
      rewrite dvalue_refine_strict_equation, dvalue_convert_strict_equation.
      cbn.
      rewrite Heqo.
      reflexivity.
    - (* iptr *)
      break_match_hyp; inv H.
      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.
      rewrite Heqo.
      reflexivity.
    - (* undef *)
      inv H.
      cbn.
      eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)); eauto.
      { (* pick_uvalue *)
        (* TODO: make this a lemma? *)
        apply orutt_trigger; cbn.
        split; [tauto | solve_uvalue_refine_strict].
        intros [t1] [t2] [_ [REF1 REF2]].
        cbn; auto.
        intros o CONTRA.
        inv CONTRA.
      }

      intros r1 r2 H.
      destruct r1, r2.
      cbn in *.
      apply orutt_Ret; auto.
    - (* Poison *)
      inv H; cbn.
      eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)); eauto.
      { (* pick_uvalue *)
        apply orutt_trigger; cbn.
        split; [tauto | solve_uvalue_refine_strict].
        intros [t1] [t2] [_ [REF1 REF2]].
        cbn; auto.
        intros o CONTRA.
        inv CONTRA.
      }

      intros r1 r2 H.
      destruct r1, r2.
      cbn in *.
      apply orutt_Ret; auto.
    - (* Structs *)
      break_match_hyp; inv H; cbn.
      generalize dependent l.
      induction fields; intros l Heqo.
      + cbn in *. inv Heqo.
        cbn.
        apply orutt_Ret; auto.
        solve_dvalue_refine_strict.
      + rewrite map_monad_InT_cons in Heqo.
        cbn in Heqo.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        specialize (IHfields l0 eq_refl).
        unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick.
        cbn.

        pose proof uvalue_refine_strict_preserves_is_concrete a u (IS1.LP.Events.DV.is_concrete a) Heqo0 eq_refl.
        rewrite H.
        clear H.

        assert (forallb IS1.LP.Events.DV.is_concrete fields = forallb is_concrete l0).
        { (* Should follow from Heqo *)
          clear IHfields.
          generalize dependent l0.
          induction fields; intros l0 Heqo.
          - cbn in *; inv Heqo.
            cbn. auto.
          - rewrite map_monad_InT_cons in Heqo.
            cbn in *.
            break_match_hyp; inv Heqo.
            break_match_hyp; inv H0.
            cbn.
            specialize (IHfields l eq_refl).
            rewrite IHfields.
            erewrite uvalue_refine_strict_preserves_is_concrete; eauto.
            solve_uvalue_refine_strict.
        }

        cbn. rewrite H.
        break_match_goal.
        { apply andb_prop in Heqb as [CONCa CONCl0].
          apply IS1.LP.Events.DV.is_concrete_uvalue_to_dvalue in CONCa as [dva CONCa].
          rewrite CONCa.
          pose proof (uvalue_to_dvalue_dvalue_refine_strict _ _ _ Heqo0 CONCa) as [dvu [UV2DVdvu REFdvu]].
          rewrite UV2DVdvu.

          rewrite CONCl0 in H.

          (* I should know from H and CONCl0 that uvalue_to_dvalue
              succeeds for each element in the map_monads... *)
          break_inner_match_goal.
          { apply map_monad_err_fail in Heqs.
            destruct Heqs as [a' [INa' UV2DVa']].
            apply forallb_forall with (x:=a') in H; auto.

            apply IS1.LP.Events.DV.is_concrete_uvalue_to_dvalue in H as [dva' CONCa'].
            rewrite CONCa' in UV2DVa'. inv UV2DVa'.
          }

          break_inner_match_goal.
          { apply map_monad_err_fail in Heqs0.
            destruct Heqs0 as [a' [INa' UV2DVa']].
            apply forallb_forall with (x:=a') in CONCl0; auto.

            apply is_concrete_uvalue_to_dvalue in CONCl0 as [dva' CONCa'].
            rewrite CONCa' in UV2DVa'. inv UV2DVa'.
          }

          cbn.
          apply orutt_Ret.

          unfold_dvalue_refine_strict_goal.
          rewrite map_monad_InT_cons.
          cbn.
          rewrite REFdvu.

          break_inner_match_goal.
          2: {
            apply map_monad_InT_OOM_failT in Heqo1.
            destruct Heqo1 as [a' [INa' CONVa']].
            apply map_monad_err_InT with (x:=a') in Heqs; auto.
            destruct Heqs as [y [UV2DVy INy]].

            eapply map_monad_InT_OOM_succeeds' in Heqo; eauto.
            destruct Heqo as [b UVCyb].
            pose proof (uvalue_to_dvalue_dvalue_refine_strict _ _ _ UVCyb UV2DVy) as [dva' [UV2DVa' REFa']].
            rewrite REFa' in CONVa'.
            inv CONVa'.
          }

          (* l2 is (dvalue_convert_strict (IS1.uvalue_to_dvalue f))
                 l1 is (uvalue_to_dvalue (uvalue_convert_strict f))
           *)
          unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick in IHfields.
          cbn in IHfields.
          setoid_rewrite CONCl0 in IHfields.
          setoid_rewrite H in IHfields.
          rewrite Heqs in IHfields.
          rewrite Heqs0 in IHfields.
          cbn in IHfields.
          apply orutt_inv_Ret in IHfields.
          unfold_dvalue_refine_strict_in IHfields.
          rewrite Heqo1 in IHfields.
          cbn in IHfields.
          inv IHfields.
          auto.
        }
        { eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
          { (* Pick uvalue *)
            apply orutt_trigger; cbn.
            split; [tauto | ].
            { unfold_uvalue_refine_strict_goal.
              rewrite map_monad_InT_cons.
              cbn.
              rewrite Heqo0.
              rewrite Heqo.
              reflexivity.
            }
            intros [t1] [t2] [_ [REF1 REF2]].
            cbn; auto.
            intros o CONTRA.
            inv CONTRA.
          }

          intros [r1] [r2] H0.
          cbn in *.
          apply orutt_Ret; auto.
        }
    - (* Packed structs *)
      break_match_hyp; inv H; cbn.
      generalize dependent l.
      induction fields; intros l Heqo.
      + cbn in *. inv Heqo.
        cbn.
        apply orutt_Ret; auto.
        solve_dvalue_refine_strict.
      + rewrite map_monad_InT_cons in Heqo.
        cbn in Heqo.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        specialize (IHfields l0 eq_refl).
        unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick.
        cbn.

        pose proof uvalue_refine_strict_preserves_is_concrete a u (IS1.LP.Events.DV.is_concrete a) Heqo0 eq_refl.
        rewrite H.
        clear H.

        assert (forallb IS1.LP.Events.DV.is_concrete fields = forallb is_concrete l0).
        { (* Should follow from Heqo *)
          clear IHfields.
          generalize dependent l0.
          induction fields; intros l0 Heqo.
          - cbn in *; inv Heqo.
            cbn. auto.
          - rewrite map_monad_InT_cons in Heqo.
            cbn in *.
            break_match_hyp; inv Heqo.
            break_match_hyp; inv H0.
            cbn.
            specialize (IHfields l eq_refl).
            rewrite IHfields.
            erewrite uvalue_refine_strict_preserves_is_concrete; eauto.
            solve_uvalue_refine_strict.
        }

        cbn. rewrite H.
        break_match_goal.
        { apply andb_prop in Heqb as [CONCa CONCl0].
          apply IS1.LP.Events.DV.is_concrete_uvalue_to_dvalue in CONCa as [dva CONCa].
          rewrite CONCa.
          pose proof (uvalue_to_dvalue_dvalue_refine_strict _ _ _ Heqo0 CONCa) as [dvu [UV2DVdvu REFdvu]].
          rewrite UV2DVdvu.

          rewrite CONCl0 in H.

          (* I should know from H and CONCl0 that uvalue_to_dvalue
              succeeds for each element in the map_monads... *)
          break_inner_match_goal.
          { apply map_monad_err_fail in Heqs.
            destruct Heqs as [a' [INa' UV2DVa']].
            apply forallb_forall with (x:=a') in H; auto.

            apply IS1.LP.Events.DV.is_concrete_uvalue_to_dvalue in H as [dva' CONCa'].
            rewrite CONCa' in UV2DVa'. inv UV2DVa'.
          }

          break_inner_match_goal.
          { apply map_monad_err_fail in Heqs0.
            destruct Heqs0 as [a' [INa' UV2DVa']].
            apply forallb_forall with (x:=a') in CONCl0; auto.

            apply is_concrete_uvalue_to_dvalue in CONCl0 as [dva' CONCa'].
            rewrite CONCa' in UV2DVa'. inv UV2DVa'.
          }

          cbn.
          apply orutt_Ret.

          unfold_dvalue_refine_strict_goal.
          rewrite map_monad_InT_cons.
          cbn.
          rewrite REFdvu.

          break_inner_match_goal.
          2: {
            apply map_monad_InT_OOM_failT in Heqo1.
            destruct Heqo1 as [a' [INa' CONVa']].
            apply map_monad_err_InT with (x:=a') in Heqs; auto.
            destruct Heqs as [y [UV2DVy INy]].

            eapply map_monad_InT_OOM_succeeds' in Heqo; eauto.
            destruct Heqo as [b UVCyb].
            pose proof (uvalue_to_dvalue_dvalue_refine_strict _ _ _ UVCyb UV2DVy) as [dva' [UV2DVa' REFa']].
            rewrite REFa' in CONVa'.
            inv CONVa'.
          }

          (* l2 is (dvalue_convert_strict (IS1.uvalue_to_dvalue f))
                 l1 is (uvalue_to_dvalue (uvalue_convert_strict f))
           *)
          unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick in IHfields.
          cbn in IHfields.
          setoid_rewrite CONCl0 in IHfields.
          setoid_rewrite H in IHfields.
          rewrite Heqs in IHfields.
          rewrite Heqs0 in IHfields.
          cbn in IHfields.
          apply orutt_inv_Ret in IHfields.
          unfold_dvalue_refine_strict_in IHfields.
          rewrite Heqo1 in IHfields.
          cbn in IHfields.
          inv IHfields.
          auto.
        }
        { eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
          { (* Pick uvalue *)
            apply orutt_trigger; cbn.
            split; [tauto | ].
            { unfold_uvalue_refine_strict_goal.
              rewrite map_monad_InT_cons.
              cbn.
              rewrite Heqo0.
              rewrite Heqo.
              reflexivity.
            }
            intros [t1] [t2] [_ [REF1 REF2]].
            cbn; auto.
            intros o CONTRA.
            inv CONTRA.
          }

          intros [r1] [r2] H0.
          cbn in *.
          apply orutt_Ret; auto.
        }
    - (* Arrays *)
      break_match_hyp; inv H.
      generalize dependent l.
      induction elts; intros l Heqo.
      + cbn in *; inv Heqo.
        cbn.
        apply orutt_Ret.
        solve_dvalue_refine_strict.
      + rewrite map_monad_InT_cons in Heqo.
        cbn in *.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.
        unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick in *.
        cbn.

        specialize (IHelts l0 eq_refl).
        pose proof uvalue_refine_strict_preserves_is_concrete a u (IS1.LP.Events.DV.is_concrete a) Heqo0 eq_refl.
        rewrite H.
        clear H.

        assert (forallb IS1.LP.Events.DV.is_concrete elts = forallb is_concrete l0).
        { clear IHelts.
          generalize dependent l0.
          induction elts; intros l0 Heqo.
          - cbn in *; inv Heqo.
            cbn. auto.
          - rewrite map_monad_InT_cons in Heqo.
            cbn in *.
            break_match_hyp; inv Heqo.
            break_match_hyp; inv H0.
            cbn.
            specialize (IHelts l eq_refl).
            rewrite IHelts.
            erewrite uvalue_refine_strict_preserves_is_concrete; eauto.
            solve_uvalue_refine_strict.
        }

        cbn. rewrite H.
        break_match_goal.
        { apply andb_prop in Heqb as [CONCa CONCl0].
          apply IS1.LP.Events.DV.is_concrete_uvalue_to_dvalue in CONCa as [dva CONCa].
          rewrite CONCa.
          pose proof (uvalue_to_dvalue_dvalue_refine_strict _ _ _ Heqo0 CONCa) as [dvu [UV2DVdvu REFdvu]].
          rewrite UV2DVdvu.

          rewrite CONCl0 in H.

          (* I should know from H and CONCl0 that uvalue_to_dvalue
              succeeds for each element in the map_monads... *)
          break_inner_match_goal.
          { apply map_monad_err_fail in Heqs.
            destruct Heqs as [a' [INa' UV2DVa']].
            apply forallb_forall with (x:=a') in H; auto.

            apply IS1.LP.Events.DV.is_concrete_uvalue_to_dvalue in H as [dva' CONCa'].
            rewrite CONCa' in UV2DVa'. inv UV2DVa'.
          }

          break_inner_match_goal.
          { apply map_monad_err_fail in Heqs0.
            destruct Heqs0 as [a' [INa' UV2DVa']].
            apply forallb_forall with (x:=a') in CONCl0; auto.

            apply is_concrete_uvalue_to_dvalue in CONCl0 as [dva' CONCa'].
            rewrite CONCa' in UV2DVa'. inv UV2DVa'.
          }

          cbn.
          apply orutt_Ret.

          unfold_dvalue_refine_strict_goal.
          rewrite map_monad_InT_cons.
          cbn.
          rewrite REFdvu.

          break_inner_match_goal.
          2: {
            apply map_monad_InT_OOM_fail in Heqo1.
            destruct Heqo1 as [a' [INa' CONVa']].
            apply map_monad_err_InT with (x:=a') in Heqs; auto.
            destruct Heqs as [y [UV2DVy INy]].

            eapply map_monad_InT_OOM_succeeds' in Heqo; eauto.
            destruct Heqo as [b UVCyb].
            pose proof (uvalue_to_dvalue_dvalue_refine_strict _ _ _ UVCyb UV2DVy) as [dva' [UV2DVa' REFa']].
            rewrite REFa' in CONVa'.
            inv CONVa'.
          }

          (* l2 is (dvalue_convert_strict (IS1.uvalue_to_dvalue f))
                 l1 is (uvalue_to_dvalue (uvalue_convert_strict f))
           *)
          cbn in IHelts.
          setoid_rewrite CONCl0 in IHelts.
          setoid_rewrite H in IHelts.
          rewrite Heqs in IHelts.
          rewrite Heqs0 in IHelts.
          cbn in IHelts.
          apply orutt_inv_Ret in IHelts.
          unfold_dvalue_refine_strict_in IHelts.
          rewrite Heqo1 in IHelts.
          cbn in IHelts.
          inv IHelts.
          auto.
        }
        { eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
          { (* Pick uvalue *)
            apply orutt_trigger; cbn.
            split; [tauto | ].
            { unfold_uvalue_refine_strict_goal.
              rewrite map_monad_InT_cons.
              cbn.
              rewrite Heqo0.
              rewrite Heqo.
              reflexivity.
            }
            intros [t1] [t2] [_ [REF1 REF2]].
            cbn; auto.
            intros o CONTRA.
            inv CONTRA.
          }

          intros [r1] [r2] H0.
          cbn in *.
          apply orutt_Ret; auto.
        }
    - (* Vectors *)
      break_match_hyp; inv H.
      generalize dependent l.
      induction elts; intros l Heqo.
      + cbn in *; inv Heqo.
        cbn.
        apply orutt_Ret.
        solve_dvalue_refine_strict.
      + rewrite map_monad_InT_cons in Heqo.
        cbn in *.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.
        unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick in *.
        cbn.

        specialize (IHelts l0 eq_refl).
        pose proof uvalue_refine_strict_preserves_is_concrete a u (IS1.LP.Events.DV.is_concrete a) Heqo0 eq_refl.
        rewrite H.
        clear H.

        assert (forallb IS1.LP.Events.DV.is_concrete elts = forallb is_concrete l0).
        { clear IHelts.
          generalize dependent l0.
          induction elts; intros l0 Heqo.
          - cbn in *; inv Heqo.
            cbn. auto.
          - rewrite map_monad_InT_cons in Heqo.
            cbn in *.
            break_match_hyp; inv Heqo.
            break_match_hyp; inv H0.
            cbn.
            specialize (IHelts l eq_refl).
            rewrite IHelts.
            erewrite uvalue_refine_strict_preserves_is_concrete; eauto.
            solve_uvalue_refine_strict.
        }

        cbn. rewrite H.
        break_match_goal.
        { apply andb_prop in Heqb as [CONCa CONCl0].
          apply IS1.LP.Events.DV.is_concrete_uvalue_to_dvalue in CONCa as [dva CONCa].
          rewrite CONCa.
          pose proof (uvalue_to_dvalue_dvalue_refine_strict _ _ _ Heqo0 CONCa) as [dvu [UV2DVdvu REFdvu]].
          rewrite UV2DVdvu.

          rewrite CONCl0 in H.

          (* I should know from H and CONCl0 that uvalue_to_dvalue
              succeeds for each element in the map_monads... *)
          break_inner_match_goal.
          { apply map_monad_err_fail in Heqs.
            destruct Heqs as [a' [INa' UV2DVa']].
            apply forallb_forall with (x:=a') in H; auto.

            apply IS1.LP.Events.DV.is_concrete_uvalue_to_dvalue in H as [dva' CONCa'].
            rewrite CONCa' in UV2DVa'. inv UV2DVa'.
          }

          break_inner_match_goal.
          { apply map_monad_err_fail in Heqs0.
            destruct Heqs0 as [a' [INa' UV2DVa']].
            apply forallb_forall with (x:=a') in CONCl0; auto.

            apply is_concrete_uvalue_to_dvalue in CONCl0 as [dva' CONCa'].
            rewrite CONCa' in UV2DVa'. inv UV2DVa'.
          }

          cbn.
          apply orutt_Ret.

          unfold_dvalue_refine_strict_goal.
          rewrite map_monad_InT_cons.
          cbn.
          rewrite REFdvu.

          break_inner_match_goal.
          2: {
            apply map_monad_InT_OOM_fail in Heqo1.
            destruct Heqo1 as [a' [INa' CONVa']].
            apply map_monad_err_InT with (x:=a') in Heqs; auto.
            destruct Heqs as [y [UV2DVy INy]].

            eapply map_monad_InT_OOM_succeeds' in Heqo; eauto.
            destruct Heqo as [b UVCyb].
            pose proof (uvalue_to_dvalue_dvalue_refine_strict _ _ _ UVCyb UV2DVy) as [dva' [UV2DVa' REFa']].
            rewrite REFa' in CONVa'.
            inv CONVa'.
          }

          (* l2 is (dvalue_convert_strict (IS1.uvalue_to_dvalue f))
                 l1 is (uvalue_to_dvalue (uvalue_convert_strict f))
           *)
          cbn in IHelts.
          setoid_rewrite CONCl0 in IHelts.
          setoid_rewrite H in IHelts.
          rewrite Heqs in IHelts.
          rewrite Heqs0 in IHelts.
          cbn in IHelts.
          apply orutt_inv_Ret in IHelts.
          unfold_dvalue_refine_strict_in IHelts.
          rewrite Heqo1 in IHelts.
          cbn in IHelts.
          inv IHelts.
          auto.
        }
        { eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
          { (* Pick uvalue *)
            apply orutt_trigger; cbn.
            split; [tauto | ].
            { unfold_uvalue_refine_strict_goal.
              rewrite map_monad_InT_cons.
              cbn.
              rewrite Heqo0.
              rewrite Heqo.
              reflexivity.
            }
            intros [t1] [t2] [_ [REF1 REF2]].
            cbn; auto.
            intros o CONTRA.
            inv CONTRA.
          }

          intros [r1] [r2] H0.
          cbn in *.
          apply orutt_Ret; auto.
        }
    - (* GEP *)
      break_match_hyp; inv H;
        break_match_hyp; inv H1;
        unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick in *;
        cbn;

        eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
      {
        apply orutt_trigger; cbn;
          [ split;
            [ tauto
            | unfold_uvalue_refine_strict_goal;
              rewrite_uvalue_convert_strict;
              cbn; rewrite Heqo0;
              auto
            ]
          | intros [t1] [t2] [_ [REF1 REF2]];
            cbn; auto
          | intros o CONTRA;
            inv CONTRA
          ].
      }

      intros [?r1] [?r2] H0;
        cbn in *;
        apply orutt_Ret; auto.
    - (* InsertElement *)
      break_match_hyp; inv H.
      break_match_hyp; inv H1.
      break_match_hyp; inv H0.
      unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick in *.
      cbn.

      eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
      { (* Pick uvalue *)
        apply orutt_trigger; cbn.
        split; [tauto | ].
        { unfold_uvalue_refine_strict_goal.
          rewrite Heqo, Heqo0, Heqo1.
          cbn.
          reflexivity.
        }
        intros [t1] [t2] [_ [REF1 REF2]].
        cbn; auto.
        intros o CONTRA.
        inv CONTRA.
      }

      intros [r1] [r2] H0.
      cbn in *.
      apply orutt_Ret; auto.
    - (* ShuffleVector *)
      break_match_hyp; inv H.
      break_match_hyp; inv H1.
      break_match_hyp; inv H0.
      unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick in *.
      cbn.

      eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
      { (* Pick uvalue *)
        apply orutt_trigger; cbn.
        split; [tauto | ].
        { unfold_uvalue_refine_strict_goal.
          rewrite Heqo, Heqo0, Heqo1.
          cbn.
          reflexivity.
        }
        intros [t1] [t2] [_ [REF1 REF2]].
        cbn; auto.
        intros o CONTRA.
        inv CONTRA.
      }

      intros [r1] [r2] H0.
      cbn in *.
      apply orutt_Ret; auto.
    - (* Select *)
      break_match_hyp; inv H.
      break_match_hyp; inv H1.
      break_match_hyp; inv H0.
      unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick in *.
      cbn.

      eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
      { (* Pick uvalue *)
        apply orutt_trigger; cbn.
        split; [tauto | ].
        { unfold_uvalue_refine_strict_goal.
          rewrite Heqo, Heqo0, Heqo1.
          cbn.
          reflexivity.
        }
        intros [t1] [t2] [_ [REF1 REF2]].
        cbn; auto.
        intros o CONTRA.
        inv CONTRA.
      }

      intros [r1] [r2] H0.
      cbn in *.
      apply orutt_Ret; auto.
    - (* ConcatBytes *)
      break_match_hyp; inv H.
      unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick in *.
      cbn.

      eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
      { (* Pick uvalue *)
        apply orutt_trigger; cbn.
        split; [tauto | ].
        { unfold_uvalue_refine_strict_goal.
          rewrite Heqo.
          cbn.
          reflexivity.
        }
        intros [t1] [t2] [_ [REF1 REF2]].
        cbn; auto.
        intros o CONTRA.
        inv CONTRA.
      }

      intros [r1] [r2] H0.
      cbn in *.
      apply orutt_Ret; auto.
  Qed.

  Lemma denote_exp_E1E2_orutt :
    forall e odt,
      orutt exp_E_refine_strict
        exp_E_res_refine_strict uvalue_refine_strict
        (IS1.LLVM.D.denote_exp odt e)
        (IS2.LLVM.D.denote_exp odt e)
        (OOM:=OOME).
  Proof.
    intros e.
    induction e using AstLib.exp_ind; intros odt;
      try solve
        [ destruct odt as [dt | ];
          [
            cbn;
            destruct dt; cbn;
            try solve [
                apply orutt_raise;
                [intros * CONTRA; dependent destruction CONTRA | cbn; auto]
              | apply orutt_Ret; solve_uvalue_refine_strict
              ]
          | cbn;
            solve_orutt_raise
          ]
        ].

    - apply translate_LU_to_exp_lookup_id_orutt.
    - destruct odt as [dt | ].
      { destruct dt; cbn;
          try solve [
              apply orutt_raise;
              [intros * CONTRA; dependent destruction CONTRA | cbn; auto]
            ].

        { (* Normal integers *)
          pose proof (@IX_supported_dec sz)
            as [SUPPORTED | UNSUPPORTED].
          - inv SUPPORTED;
              repeat rewrite map_ret;
              apply orutt_Ret;
              rewrite uvalue_refine_strict_equation;
              rewrite uvalue_convert_strict_equation;
              cbn;
              reflexivity.
          - repeat rewrite unsupported_cases_match; auto;
              repeat rewrite Raise.raise_map_itree;
              apply orutt_raise;
              [intros * CONTRA; dependent destruction CONTRA | cbn; auto].
        }

        { (* Intptrs *)
          repeat rewrite map_bind.
          eapply orutt_bind with
            (RR:=(fun (ip1 : IS1.LP.IP.intptr) (ip2 : IS2.LP.IP.intptr) => IS1.LP.IP.to_Z ip1 = IS2.LP.IP.to_Z ip2)).
          unfold lift_OOM.
          { break_match; break_match.
            - apply orutt_Ret.
              rewrite IS1.LP.IP.VMemInt_intptr_mrepr_from_Z in Heqo.
              rewrite IS2.LP.IP.VMemInt_intptr_mrepr_from_Z in Heqo0.
              erewrite IP.from_Z_to_Z; eauto.
              erewrite IS1.LP.IP.from_Z_to_Z; eauto.
            - apply orutt_raise_oom.
            - (* TODO: Maybe this should be a lemma *)
              rewrite IS1.LP.IP.VMemInt_intptr_mrepr_from_Z in Heqo.
              rewrite IS2.LP.IP.VMemInt_intptr_mrepr_from_Z in Heqo0.

              pose proof intptr_convert_succeeds i as [i2 CONV].
              rewrite IP.from_Z_to_Z with (i:=i) (z:=x) in CONV; eauto.
              rewrite Heqo in CONV. inv CONV.
            - apply orutt_raise_oom.
          }

          intros r1 r2 H.
          do 2 rewrite map_ret.
          apply orutt_Ret.
          cbn.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
          cbn.
          rewrite H.
          rewrite IP.to_Z_from_Z; auto.
        }
      }

      cbn.
      solve_orutt_raise.
    - destruct b; cbn;
        apply orutt_Ret; solve_uvalue_refine_strict.
    - cbn; apply orutt_Ret.
      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      cbn.
      rewrite AC1.addr_convert_null.
      reflexivity.
    - destruct odt as [dt | ];
          [
          | solve_orutt_raise
          ].

      destruct dt; cbn;
        try solve [ apply orutt_Ret; solve_uvalue_refine_strict
                  | cbn; solve_orutt_raise
          ].

      + unfold denote_exp, IS1.LLVM.D.denote_exp.
        cbn.
        break_match.
        * apply default_dvalue_of_dtyp_i_dv1_dv2_same_error in Heqs.
          rewrite Heqs.
          solve_orutt_raise.
        * apply default_dvalue_of_dtyp_i_dv1_dv2_equiv in Heqs as [v2 [V2 REF]].
          rewrite V2.
          cbn; apply orutt_Ret.
          apply dvalue_refine_strict_dvalue_to_uvalue; auto.

      + apply orutt_Ret.
        unfold_uvalue_refine_strict.
        cbn.

        rewrite IS1.LP.IP.to_Z_0.
        rewrite IP.from_Z_0.
        reflexivity.
      + unfold denote_exp, IS1.LLVM.D.denote_exp.
        cbn.
        repeat break_match; cbn; inv Heqs0; inv Heqs.
        * assert (s = s0).
          {
            apply default_dvalue_of_dtyp_dv1_dv2_same_error in Heqs1.
            rewrite Heqs1 in Heqs2; inv Heqs2.
            auto.
          }
          subst.
          solve_orutt_raise.

        * apply default_dvalue_of_dtyp_dv1_dv2_same_error in Heqs2.
          rewrite Heqs2 in Heqs1; inv Heqs1.
        * apply default_dvalue_of_dtyp_dv1_dv2_same_error in Heqs1.
          rewrite Heqs2 in Heqs1; inv Heqs1.
        * apply default_dvalue_of_dtyp_dv1_dv2_equiv in Heqs2 as [dv2 [DEFdv2 REFdv2]].
          rewrite DEFdv2 in Heqs1; inv Heqs1.

          apply orutt_Ret.
          unfold_uvalue_refine_strict_goal.
          cbn in *.
          break_match.
          { destruct (N.to_nat sz).
            - cbn in *; inv Heqo.
              reflexivity.
            - rewrite map_repeat in Heqo.
              rewrite map_repeat.
              eapply map_monad_InT_OOM_repeat_success in Heqo; subst; cbn; auto.
              rewrite Heqo. reflexivity.
              rewrite <- uvalue_refine_strict_equation.
              intros INx.
              apply dvalue_refine_strict_dvalue_to_uvalue; auto.
          }

          apply map_monad_InT_OOM_failT in Heqo as [a [IN FAIL]].
          rewrite map_repeat in IN.
          apply repeat_spec_InT in IN; subst.
          apply dvalue_refine_strict_dvalue_to_uvalue in REFdv2.
          rewrite REFdv2 in FAIL.
          inv FAIL.
      + (* Struct zero initialization *)
        unfold denote_exp, IS1.LLVM.D.denote_exp.
        cbn.
        repeat break_match; cbn; inv Heqs0; inv Heqs; try solve_orutt_raise.
        * apply map_monad_err_fail in Heqs2.
          destruct Heqs2 as [a [IN Heqs2]].
          apply map_monad_err_forall2 in Heqs1.
          apply Util.Forall2_forall in Heqs1 as [LEN Heqs1].
          apply In_Nth in IN as [i NTH].
          pose proof Nth_exists l i as NTHl.
          forward NTHl.
          { apply Nth_ix_lt_length in NTH. lia. }
          destruct NTHl as [x NTHl].
          specialize (Heqs1 _ _ _ NTH NTHl).
          apply default_dvalue_of_dtyp_dv1_dv2_same_error in Heqs2.
          rewrite Heqs2 in Heqs1; inv Heqs1.
        * apply map_monad_err_fail in Heqs1.
          destruct Heqs1 as [a [IN Heqs1]].
          apply map_monad_err_forall2 in Heqs2.
          apply Util.Forall2_forall in Heqs2 as [LEN Heqs2].
          apply In_Nth in IN as [i NTH].
          pose proof Nth_exists l i as NTHl.
          forward NTHl.
          { apply Nth_ix_lt_length in NTH. lia. }
          destruct NTHl as [x NTHl].
          specialize (Heqs2 _ _ _ NTH NTHl).
          apply default_dvalue_of_dtyp_dv1_dv2_same_error in Heqs1.
          rewrite Heqs2 in Heqs1; inv Heqs1.
        * apply orutt_Ret.
          unfold_uvalue_refine_strict_goal.
          cbn in *.

          break_match.
          { generalize dependent l0.
            generalize dependent l1.
            generalize dependent l.
            induction fields; intros defs2 DEFS2 conv defs1 DEFS1 CONV.
            - cbn in *.
              inv DEFS1; inv DEFS2.
              cbn in *.
              inv CONV; auto.
            - cbn in *.
              break_match_hyp; inv DEFS1.
              break_match_hyp; inv H0.
              break_match_hyp; inv DEFS2.
              break_match_hyp; inv H0.

              apply default_dvalue_of_dtyp_dv1_dv2_equiv in Heqs as [dv2 [DEFdv2 REFdv2]].
              rewrite DEFdv2 in Heqs1. inv Heqs1.
              rewrite map_cons in CONV.
              rewrite map_monad_InT_cons in CONV.
              cbn in *.
              break_match_hyp; inv CONV.
              break_match_hyp; inv H0.
              specialize (IHfields l0 eq_refl l1 l eq_refl Heqo0).
              inv IHfields.
              pose proof dvalue_refine_strict_dvalue_to_uvalue _ _ REFdv2.
              rewrite uvalue_refine_strict_equation in H.
              rewrite Heqo in H.
              inv H.
              reflexivity.
          }

          apply map_monad_InT_OOM_failT in Heqo as [a [IN FAIL]].
          apply InT_map_impl in IN.
          destruct IN as [a' [EQ IN]].
          subst.

          pose proof Heqs2.
          eapply map_monad_err_InT in H; eauto.
          destruct H as [y [DEFy INy]].
          pose proof DEFy as A'.
          apply default_dvalue_of_dtyp_dv1_dv2_equiv in DEFy as [dv2 [DEFdv2 REFdv2]].
          pose proof dvalue_refine_strict_dvalue_to_uvalue _ _ REFdv2.
          rewrite H in FAIL.
          inv FAIL.
      + (* Packed struct zero initialization *)
        unfold denote_exp, IS1.LLVM.D.denote_exp.
        cbn.
        repeat break_match; cbn; inv Heqs0; inv Heqs; try solve_orutt_raise.
        * apply map_monad_err_fail in Heqs2.
          destruct Heqs2 as [a [IN Heqs2]].
          apply map_monad_err_forall2 in Heqs1.
          apply Util.Forall2_forall in Heqs1 as [LEN Heqs1].
          apply In_Nth in IN as [i NTH].
          pose proof Nth_exists l i as NTHl.
          forward NTHl.
          { apply Nth_ix_lt_length in NTH. lia. }
          destruct NTHl as [x NTHl].
          specialize (Heqs1 _ _ _ NTH NTHl).
          apply default_dvalue_of_dtyp_dv1_dv2_same_error in Heqs2.
          rewrite Heqs2 in Heqs1; inv Heqs1.
        * apply map_monad_err_fail in Heqs1.
          destruct Heqs1 as [a [IN Heqs1]].
          apply map_monad_err_forall2 in Heqs2.
          apply Util.Forall2_forall in Heqs2 as [LEN Heqs2].
          apply In_Nth in IN as [i NTH].
          pose proof Nth_exists l i as NTHl.
          forward NTHl.
          { apply Nth_ix_lt_length in NTH. lia. }
          destruct NTHl as [x NTHl].
          specialize (Heqs2 _ _ _ NTH NTHl).
          apply default_dvalue_of_dtyp_dv1_dv2_same_error in Heqs1.
          rewrite Heqs2 in Heqs1; inv Heqs1.
        * apply orutt_Ret.
          unfold_uvalue_refine_strict_goal.
          cbn in *.

          break_match.
          { generalize dependent l0.
            generalize dependent l1.
            generalize dependent l.
            induction fields; intros defs2 DEFS2 conv defs1 DEFS1 CONV.
            - cbn in *.
              inv DEFS1; inv DEFS2.
              cbn in *.
              inv CONV; auto.
            - cbn in *.
              break_match_hyp; inv DEFS1.
              break_match_hyp; inv H0.
              break_match_hyp; inv DEFS2.
              break_match_hyp; inv H0.

              apply default_dvalue_of_dtyp_dv1_dv2_equiv in Heqs as [dv2 [DEFdv2 REFdv2]].
              rewrite DEFdv2 in Heqs1. inv Heqs1.
              rewrite map_cons in CONV.
              rewrite map_monad_InT_cons in CONV.
              cbn in *.
              break_match_hyp; inv CONV.
              break_match_hyp; inv H0.
              specialize (IHfields l0 eq_refl l1 l eq_refl Heqo0).
              inv IHfields.
              pose proof dvalue_refine_strict_dvalue_to_uvalue _ _ REFdv2.
              rewrite uvalue_refine_strict_equation in H.
              rewrite Heqo in H.
              inv H.
              reflexivity.
          }

          apply map_monad_InT_OOM_fail in Heqo as [a [IN FAIL]].
          apply InT_map_impl in IN.
          destruct IN as [a' [EQ IN]].
          subst.

          pose proof Heqs2.
          eapply map_monad_err_InT in H; eauto.
          destruct H as [y [DEFy INy]].
          pose proof DEFy as A'.
          apply default_dvalue_of_dtyp_dv1_dv2_equiv in DEFy as [dv2 [DEFdv2 REFdv2]].
          pose proof dvalue_refine_strict_dvalue_to_uvalue _ _ REFdv2.
          rewrite H in FAIL.
          inv FAIL.
      + (* Vector zero initialization *)
        unfold denote_exp, IS1.LLVM.D.denote_exp.
        cbn.
        repeat break_match; cbn; inv Heqs0; inv Heqs; try solve_orutt_raise.
        * apply default_dvalue_of_dtyp_i_dv1_dv2_same_error in Heqs2.
          rewrite Heqs2 in Heqs1; inv Heqs1.
        * apply default_dvalue_of_dtyp_i_dv1_dv2_same_error in Heqs1.
          rewrite Heqs2 in Heqs1; inv Heqs1.
        * apply default_dvalue_of_dtyp_i_dv1_dv2_equiv in Heqs2 as [dv2 [DEFdv2 REFdv2]].
          rewrite DEFdv2 in Heqs1; inv Heqs1.

          apply orutt_Ret.
          unfold_uvalue_refine_strict_goal.
          cbn in *.
          break_match.
          { destruct (N.to_nat sz).
            - cbn in *; inv Heqo.
              reflexivity.
            - rewrite map_repeat in Heqo.
              rewrite map_repeat.
              eapply map_monad_InT_OOM_repeat_success in Heqo; subst; cbn; auto.
              rewrite Heqo. reflexivity.
              rewrite <- uvalue_refine_strict_equation.
              intros INx.
              apply dvalue_refine_strict_dvalue_to_uvalue; auto.
          }

          apply map_monad_InT_OOM_fail in Heqo as [a [IN FAIL]].
          rewrite map_repeat in IN.
          apply repeat_spec_InT in IN; subst.
          apply dvalue_refine_strict_dvalue_to_uvalue in REFdv2.
          rewrite REFdv2 in FAIL.
          inv FAIL.
        * apply orutt_Ret.
          unfold_uvalue_refine_strict_goal.
          cbn in *.
          break_match.
          { destruct (N.to_nat sz).
            - cbn in *; inv Heqo.
              reflexivity.
            - rewrite map_repeat in Heqo.
              rewrite map_repeat.
              eapply map_monad_InT_OOM_repeat_success in Heqo; subst; cbn; auto.
              rewrite Heqo. reflexivity.
              rewrite <- uvalue_refine_strict_equation.
              solve_uvalue_refine_strict.
          }

          apply map_monad_InT_OOM_fail in Heqo as [a [IN FAIL]].
          rewrite map_repeat in IN.
          apply repeat_spec_InT in IN; subst.
          cbn in FAIL.
          rewrite uvalue_convert_strict_equation in FAIL.
          cbn in *.
          rewrite AC1.addr_convert_null in FAIL.
          inv FAIL.
        * apply orutt_Ret.
          unfold_uvalue_refine_strict_goal.
          cbn in *.
          break_match.
          { destruct (N.to_nat sz).
            - cbn in *; inv Heqo.
              reflexivity.
            - rewrite map_repeat in Heqo.
              rewrite map_repeat.
              eapply map_monad_InT_OOM_repeat_success in Heqo; subst; cbn; auto.
              rewrite Heqo. reflexivity.
              rewrite <- uvalue_refine_strict_equation.
              solve_uvalue_refine_strict.
          }

          apply map_monad_InT_OOM_fail in Heqo as [a [IN FAIL]].
          rewrite map_repeat in IN.
          apply repeat_spec_InT in IN; subst.
          cbn in FAIL.
          rewrite uvalue_convert_strict_equation in FAIL.
          cbn in *.
          inv FAIL.
        * apply orutt_Ret.
          unfold_uvalue_refine_strict_goal.
          cbn in *.
          break_match.
          { destruct (N.to_nat sz).
            - cbn in *; inv Heqo.
              reflexivity.
            - rewrite map_repeat in Heqo.
              rewrite map_repeat.
              eapply map_monad_InT_OOM_repeat_success in Heqo; subst; cbn; auto.
              rewrite Heqo. reflexivity.
              rewrite <- uvalue_refine_strict_equation.
              solve_uvalue_refine_strict.
          }

          apply map_monad_InT_OOM_fail in Heqo as [a [IN FAIL]].
          rewrite map_repeat in IN.
          apply repeat_spec_InT in IN; subst.
          cbn in FAIL.
          rewrite uvalue_convert_strict_equation in FAIL.
          cbn in *.
          inv FAIL.
    - (* Cstrings *)
      cbn.
      eapply orutt_bind with (RR:=(fun uvs1 uvs2 => uvalue_refine_strict (DV1.UVALUE_Array uvs1) (UVALUE_Array uvs2))).
      { induction elts.
        - cbn.
          apply orutt_Ret; solve_uvalue_refine_strict.
        - repeat rewrite map_monad_unfold.
          cbn.
          destruct a.
          eapply orutt_bind.
          { specialize (H (d, e) (or_introl eq_refl)).
            cbn in H.
            apply H.
          }

          intros r1 r2 H0.
          forward IHelts.
          { intros p H1 odt0.
            eapply H.
            right; auto.
          }

          eapply orutt_bind; eauto.

          intros r0 r3 H1.
          cbn in H1.
          apply orutt_Ret.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation in H1.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
          rewrite map_monad_InT_cons.
          cbn.
          cbn in H1.
          break_match_hyp; inv H1.
          rewrite uvalue_refine_strict_equation in H0.
          rewrite H0.
          reflexivity.
      }

      intros r1 r2 H0.
      apply orutt_Ret; auto.
    - (* Structs *)
      cbn.
      eapply orutt_bind with (RR:=(fun uvs1 uvs2 => uvalue_refine_strict (DV1.UVALUE_Struct uvs1) (UVALUE_Struct uvs2))).
      { induction fields.
        - cbn.
          apply orutt_Ret; solve_uvalue_refine_strict.
        - repeat rewrite map_monad_unfold.
          cbn.
          destruct a.
          eapply orutt_bind.
          { specialize (H (d, e) (or_introl eq_refl)).
            cbn in H.
            apply H.
          }

          intros r1 r2 H0.
          forward IHfields.
          { intros p H1 odt0.
            eapply H.
            right; auto.
          }

          eapply orutt_bind; eauto.

          intros r0 r3 H1.
          cbn in H1.
          apply orutt_Ret.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation in H1.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
          rewrite map_monad_InT_cons.
          cbn.
          cbn in H1.
          break_match_hyp; inv H1.
          rewrite uvalue_refine_strict_equation in H0.
          rewrite H0.
          reflexivity.
      }

      intros r1 r2 H0.
      apply orutt_Ret; auto.
    - (* Packed Structs *)
      destruct odt as [dt | ];
        [
        | cbn;
          apply orutt_raise; cbn; auto;
          intros msg o CONTRA;
          inv CONTRA
        ].

      destruct dt; cbn;
        try solve [ apply orutt_Ret; solve_uvalue_refine_strict
                  | cbn;
                    apply orutt_raise; cbn; auto;
                    intros msg o CONTRA;
                    inv CONTRA
          ].

      cbn.
      eapply orutt_bind with (RR:=(fun uvs1 uvs2 => uvalue_refine_strict (DV1.UVALUE_Packed_struct uvs1) (UVALUE_Packed_struct uvs2))).
      { induction fields.
        - cbn.
          apply orutt_Ret; solve_uvalue_refine_strict.
        - repeat rewrite map_monad_unfold.
          cbn.
          destruct a.
          eapply orutt_bind.
          { specialize (H (d, e) (or_introl eq_refl)).
            cbn in H.
            apply H.
          }

          intros r1 r2 H0.
          forward IHfields.
          { intros p H1 odt0.
            eapply H.
            right; auto.
          }

          eapply orutt_bind; eauto.

          intros r0 r3 H1.
          cbn in H1.
          apply orutt_Ret.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation in H1.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
          rewrite map_monad_InT_cons.
          cbn.
          cbn in H1.
          break_match_hyp; inv H1.
          rewrite uvalue_refine_strict_equation in H0.
          rewrite H0.
          reflexivity.
      }

      intros r1 r2 H0.
      apply orutt_Ret; auto.
    - (* Arrays *)
      cbn.
      eapply orutt_bind with (RR:=(fun uvs1 uvs2 => uvalue_refine_strict (DV1.UVALUE_Array uvs1) (UVALUE_Array uvs2))).
      { induction elts.
        - cbn.
          apply orutt_Ret; solve_uvalue_refine_strict.
        - repeat rewrite map_monad_unfold.
          cbn.
          destruct a.
          eapply orutt_bind.
          { specialize (H (d, e) (or_introl eq_refl)).
            cbn in H.
            apply H.
          }

          intros r1 r2 H0.
          forward IHelts.
          { intros p H1 odt0.
            eapply H.
            right; auto.
          }

          eapply orutt_bind; eauto.

          intros r0 r3 H1.
          cbn in H1.
          apply orutt_Ret.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation in H1.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
          rewrite map_monad_InT_cons.
          cbn.
          cbn in H1.
          break_match_hyp; inv H1.
          rewrite uvalue_refine_strict_equation in H0.
          rewrite H0.
          reflexivity.
      }

      intros r1 r2 H0.
      apply orutt_Ret; auto.
    - (* Vectors *)
      cbn.
      eapply orutt_bind with (RR:=(fun uvs1 uvs2 => uvalue_refine_strict (DV1.UVALUE_Vector uvs1) (UVALUE_Vector uvs2))).
      { induction elts.
        - cbn.
          apply orutt_Ret; solve_uvalue_refine_strict.
        - repeat rewrite map_monad_unfold.
          cbn.
          destruct a.
          eapply orutt_bind.
          { specialize (H (d, e) (or_introl eq_refl)).
            cbn in H.
            apply H.
          }

          intros r1 r2 H0.
          forward IHelts.
          { intros p H1 odt0.
            eapply H.
            right; auto.
          }

          eapply orutt_bind; eauto.

          intros r0 r3 H1.
          cbn in H1.
          apply orutt_Ret.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation in H1.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
          rewrite map_monad_InT_cons.
          cbn.
          cbn in H1.
          break_match_hyp; inv H1.
          rewrite uvalue_refine_strict_equation in H0.
          rewrite H0.
          reflexivity.
      }

      intros r1 r2 H0.
      apply orutt_Ret; auto.
    - (* IBinops *)
      cbn.
      eapply orutt_bind; eauto.
      intros r1 r2 H.
      eapply orutt_bind; eauto.
      intros r0 r3 H0.
      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      rewrite uvalue_refine_strict_equation in H, H0.
      rewrite H, H0.
      cbn.
      reflexivity.
    - (* ICmps *)
      cbn.
      eapply orutt_bind; eauto.
      intros r1 r2 H.
      eapply orutt_bind; eauto.
      intros r0 r3 H0.
      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      rewrite uvalue_refine_strict_equation in H, H0.
      rewrite H, H0.
      cbn.
      reflexivity.
    - (* FBinops *)
      cbn.
      eapply orutt_bind; eauto.
      intros r1 r2 H.
      eapply orutt_bind; eauto.
      intros r0 r3 H0.
      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      rewrite uvalue_refine_strict_equation in H, H0.
      rewrite H, H0.
      cbn.
      reflexivity.
    - (* FCmp *)
      cbn.
      eapply orutt_bind; eauto.
      intros r1 r2 H.
      eapply orutt_bind; eauto.
      intros r0 r3 H0.
      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      rewrite uvalue_refine_strict_equation in H, H0.
      rewrite H, H0.
      cbn.
      reflexivity.
    - (* Conversion *)
      cbn.
      eapply orutt_bind; eauto.
      intros r1 r2 H.
      apply orutt_Ret.
      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      rewrite uvalue_refine_strict_equation in H.
      rewrite H.
      cbn.
      reflexivity.
    - (* GetElementPtr *)
      destruct ptrval as [ptr_t ptrval].
      cbn.
      eapply orutt_bind; eauto.
      intros r1 r2 H0.
      eapply orutt_bind with (RR:=(fun uvs1 uvs2 => uvalue_refine_strict (DV1.UVALUE_Array uvs1) (UVALUE_Array uvs2))).
      { induction idxs.
        - cbn.
          apply orutt_Ret; solve_uvalue_refine_strict.
        - repeat rewrite map_monad_unfold.
          cbn.
          destruct a.
          eapply orutt_bind.
          { specialize (H (d, e) (or_introl eq_refl)).
            cbn in H.
            apply H.
          }

          intros r0 r3 H1.
          forward IHidxs.
          { intros p H2 odt0.
            eapply H.
            right; auto.
          }

          eapply orutt_bind; eauto.

          intros r4 r5 H2.
          cbn in H2.
          apply orutt_Ret.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation in H2.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
          rewrite map_monad_InT_cons.
          cbn.
          cbn in H2.
          break_match_hyp; inv H2.
          rewrite uvalue_refine_strict_equation in H1.
          rewrite H1.
          reflexivity.
      }

      intros r0 r3 H1.
      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      rewrite uvalue_refine_strict_equation in H0, H1.
      cbn.
      rewrite H0.
      rewrite uvalue_convert_strict_equation in H1.
      cbn in H1.
      break_match_hyp; inv H1.
      reflexivity.
    - (* ExtractElement *)
      destruct vec as [vec_t vec].
      destruct idx as [idx_t idx].
      cbn.

      eapply orutt_bind; eauto.
      intros r1 r2 H.

      eapply orutt_bind; eauto.
      intros r0 r3 H0.

      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      rewrite uvalue_refine_strict_equation in H0, H.
      cbn.

      rewrite H, H0.
      reflexivity.
    - (* InsertElement *)
      destruct vec as [vec_t vec].
      destruct idx as [idx_t idx].
      destruct elt as [elt_t elt].
      cbn.

      eapply orutt_bind; eauto.
      intros r1 r2 H.

      eapply orutt_bind; eauto.
      intros r0 r3 H0.

      eapply orutt_bind; eauto.
      intros r4 r5 H1.

      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      rewrite uvalue_refine_strict_equation in H, H0, H1.
      cbn.

      rewrite H, H0, H1.
      reflexivity.
    - (* ShuffleVector *)
      destruct vec1 as [vec1_t vec1].
      destruct vec2 as [vec2_t vec2].
      destruct idxmask as [idxmask_t idxmask].
      cbn.

      eapply orutt_bind; eauto.
      intros r1 r2 H.

      eapply orutt_bind; eauto.
      intros r0 r3 H0.

      eapply orutt_bind; eauto.
      intros r4 r5 H1.

      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      rewrite uvalue_refine_strict_equation in H, H0, H1.
      cbn.

      rewrite H, H0, H1.
      reflexivity.
    - (* ExtractValue *)
      destruct vec as [vec_t vec].
      cbn.

      eapply orutt_bind; eauto.
      intros r1 r2 H.

      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      rewrite uvalue_refine_strict_equation in H.
      cbn.

      rewrite H.
      reflexivity.
    - (* InsertValue *)
      destruct vec as [vec_t vec].
      destruct elt as [elt_t elt].
      cbn.

      eapply orutt_bind; eauto.
      intros r1 r2 H.

      eapply orutt_bind; eauto.
      intros r0 r3 H0.

      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      rewrite uvalue_refine_strict_equation in H, H0.
      cbn.

      rewrite H, H0.
      reflexivity.
    - (* Select *)
      destruct cnd, v1, v2.
      cbn.

      eapply orutt_bind; eauto.
      intros r1 r2 H.

      eapply orutt_bind; eauto.
      intros r0 r3 H0.

      eapply orutt_bind; eauto.
      intros r4 r5 H1.

      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.
      rewrite uvalue_refine_strict_equation in H, H0, H1.
      cbn.

      rewrite H, H0, H1.
      reflexivity.
    - (* Freeze *)
      destruct v; cbn.
      eapply orutt_bind; eauto.
      intros r1 r2 H.

      eapply orutt_bind with (RR:=dvalue_refine_strict); eauto.
      apply pick_your_poison_orutt; auto.
      intros r0 r3 H0.
      apply orutt_Ret.
      apply dvalue_refine_strict_dvalue_to_uvalue; auto.
  Qed.

  Lemma GlobalRead_exp_E_E1E2_rutt :
    forall g,
      rutt exp_E_refine_strict exp_E_res_refine_strict dvalue_refine_strict (trigger (GlobalRead g)) (trigger (GlobalRead g)).
  Proof.
    intros g.
    apply rutt_trigger.
    cbn. auto.

    intros t1 t2 H.
    cbn in H.
    tauto.
  Qed.

  Lemma GlobalRead_L0_E1E2_rutt :
    forall g,
      rutt event_refine_strict event_res_refine_strict dvalue_refine_strict (trigger (GlobalRead g)) (trigger (GlobalRead g)).
  Proof.
    intros g.
    apply rutt_trigger.
    cbn. auto.

    intros t1 t2 H.
    cbn in H.
    tauto.
  Qed.

  Lemma Store_E1E2_rutt :
    forall dt r1 r2 r3 r4,
      dvalue_refine_strict r1 r2 ->
      uvalue_refine_strict r3 r4 ->
      rutt exp_E_refine_strict exp_E_res_refine_strict eq
        (trigger (IS1.LP.Events.Store dt r1 r3))
        (trigger (IS2.LP.Events.Store dt r2 r4)).
  Proof.
    intros dt r1 r2 r3 r4 R1R2 R3R4.
    apply rutt_trigger.
    cbn. tauto.

    intros [] [] _.
    reflexivity.
  Qed.

  (* TODO: move this! Probably somewhere that I get a version for each language? *)
  Ltac solve_dec_oom :=
    let s := fresh "s" in
    first [intros ? s | intros s];
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
    forall A (e : exp_E A), {forall o : OOME A, e <> subevent _ o} + {exists o : OOME A, e = subevent _ o}.
  Proof.
    solve_dec_oom.
  Qed.

  (* TODO: move this! *)
  Lemma L0'_dec_oom :
    forall A (e : L0' A), {forall o : OOME A, e <> subevent _ o} + {exists o : OOME A, e = subevent _ o}.
  Proof.
    solve_dec_oom.
  Qed.

  (* TODO: move this! *)
  Lemma L0_dec_oom :
    forall A (e : L0 A), {forall o : OOME A, e <> subevent _ o} + {exists o : OOME A, e = subevent _ o}.
  Proof.
    solve_dec_oom.
  Qed.

  Lemma initialize_global_E1E2_orutt :
    forall g,
      orutt exp_E_refine_strict exp_E_res_refine_strict eq
        (LLVM1.initialize_global g)
        (LLVM2.initialize_global g)
        (OOM:=OOME).
  Proof.
    intros g.
    cbn.
    eapply orutt_bind with (RR:=dvalue_refine_strict).
    { apply rutt_orutt.
      apply GlobalRead_exp_E_E1E2_rutt.
      intros A e2.
      apply exp_E_dec_oom.
    }

    intros r1 r2 R1R2.
    apply orutt_bind with (RR:=uvalue_refine_strict).
    { break_match.
      apply denote_exp_E1E2_orutt.
      eapply orutt_Ret.
      solve_uvalue_refine_strict.
    }

    intros r3 r4 R3R4.
    apply rutt_orutt; [| apply exp_E_dec_oom].
    apply Store_E1E2_rutt; auto.
  Qed.

  Lemma initialize_globals_E1E2_orutt :
    forall m_globals,
      orutt exp_E_refine_strict exp_E_res_refine_strict eq
        (map_monad LLVM1.initialize_global m_globals)
        (map_monad initialize_global m_globals)
        (OOM:=OOME).
  Proof.
    cbn.

    induction m_globals.
    { cbn.
      apply orutt_Ret.
      reflexivity.
    }
    { rewrite map_monad_unfold.
      rewrite map_monad_unfold.

      apply orutt_bind with (RR:=eq).
      apply initialize_global_E1E2_orutt.

      intros [] [] _.
      apply orutt_bind with (RR:=eq).
      apply IHm_globals.

      intros r1 r2 R1R2; subst.
      apply orutt_Ret.
      reflexivity.
    }
  Qed.

  Lemma build_global_environment_E1E2_orutt_strict_sound :
    forall (m : mcfg dtyp),
      orutt
        event_refine_strict
        event_res_refine_strict
        eq
        (LLVM1.build_global_environment m)
        (LLVM2.build_global_environment m)
        (OOM:=OOME).
  Proof.
    destruct m.
    cbn.
    apply orutt_bind with (RR:=eq).
    { apply orutt_bind with (RR:=eq).
      (* In the future this allocate_one_E1E2_rutt_strict_sound lemma may be orutt *)
      apply rutt_orutt; [| apply L0_dec_oom].
      apply allocate_one_E1E2_rutt_strict_sound.
      intros r1 r2 EQ; subst.
      apply orutt_Ret; auto.
    }

    intros r1 r2 EQ; subst.
    inv r2.

    apply orutt_bind with (RR:=eq).
    { apply orutt_bind with (RR:=eq).
      apply rutt_orutt; [| apply L0_dec_oom].
      apply allocate_global_E1E2_rutt_strict_sound.
      intros r1 r2 EQ; subst.
      apply orutt_Ret; auto.
    }

    intros r1 r2 EQ; subst.
    inv r2.

    eapply translate_exp_to_L0_E1E2_orutt.
    apply orutt_bind with (RR:=eq).
    apply initialize_globals_E1E2_orutt.

    intros r1 r2 R1R2; subst.
    apply orutt_Ret.
    reflexivity.
  Qed.

  Definition function_denotation_refine_strict : IS1.LLVM.D.function_denotation -> IS2.LLVM.D.function_denotation -> Prop.
  Proof.
    intros d1 d2.
    unfold function_denotation in *.
    unfold IS1.LLVM.D.function_denotation in *.

    refine (forall args1 args2,
               Forall2 uvalue_refine_strict args1 args2 ->
               orutt L0'_refine_strict L0'_res_refine_strict uvalue_refine_strict
                 (d1 args1)
                 (d2 args2)
                 (OOM:=OOME)
           ).
  Defined.

  (*
  Definition function_denotation_converted_lazy : IS1.LLVM.D.function_denotation -> IS2.LLVM.D.function_denotation -> Prop.
  Proof.
    intros d1 d2.
    unfold function_denotation in *.
    unfold IS1.LLVM.D.function_denotation in *.

    refine (forall args1 args2,
               Forall2 uvalue_converted_lazy args1 args2 ->
               rutt L0'_refine_lazy L0'_res_refine_lazy uvalue_converted_lazy
                 (d1 args1)
                 (d2 args2)
           ).
  Defined.
   *)

  (* TODO: Move this to rutt library *)
  Lemma rutt_iter' {E1 E2 I1 I2 R1 R2}
    (RI : I1 -> I2 -> Prop)
    (RR : R1 -> R2 -> Prop)
    (pre : prerel E1 E2) (post : postrel E1 E2)
    (body1 : I1 -> itree E1 (I1 + R1))
    (body2 : I2 -> itree E2 (I2 + R2))
    (rutt_body
      : forall j1 j2, RI j1 j2 -> rutt pre post (sum_rel RI RR) (body1 j1) (body2 j2))
    : forall (i1 : I1) (i2 : I2) (RI_i : RI i1 i2),
      rutt pre post RR (ITree.iter body1 i1) (ITree.iter body2 i2).
  Proof.
    ginit. gcofix CIH. intros.
    specialize (rutt_body i1 i2 RI_i).
    do 2 rewrite unfold_iter.
    eapply gpaco2_uclo; [|eapply rutt_clo_bind|]; eauto with paco.
    econstructor; eauto. intros ? ? [].
    - gstep.
      red; cbn.
      constructor.
      gbase.
      auto.
    - gstep.
      red.
      constructor.
      auto.
  Qed.

  (* TODO: Move this to rutt library *)
  Lemma rutt_iter_gen :
    forall {E1 E2 : Type -> Type} {A B1 B2 : Type} {R : relation A} {S : relationH B1 B2} (pre : prerel E1 E2) (post : postrel E1 E2),
    forall (x : A -> itree E1 (A + B1)) (y : A -> itree E2 (A + B2)),
      (forall x0 y0 : A, R x0 y0 -> rutt pre post (sum_rel R S) (x x0) (y y0)) ->
      forall x0 y0 : A, R x0 y0 -> rutt pre post S (CategoryOps.iter x x0) (CategoryOps.iter y y0).
  Proof.
    intros E1 E2 A B1 B2 R S pre post body1 body2 EQ_BODY x y Hxy.
    eapply rutt_iter'; eauto.
  Qed.


  (* TODO: Move this to rutt library *)
  Lemma orutt_iter' {OOME E1 E2 I1 I2 R1 R2} `{OOM: OOME -< E2}
    (RI : I1 -> I2 -> Prop)
    (RR : R1 -> R2 -> Prop)
    (pre : prerel E1 E2) (post : postrel E1 E2)
    (body1 : I1 -> itree E1 (I1 + R1))
    (body2 : I2 -> itree E2 (I2 + R2))
    (rutt_body
      : forall j1 j2, RI j1 j2 -> orutt pre post (sum_rel RI RR) (body1 j1) (body2 j2) (OOM:=OOME))
    : forall (i1 : I1) (i2 : I2) (RI_i : RI i1 i2),
      orutt pre post RR (ITree.iter body1 i1) (ITree.iter body2 i2) (OOM:=OOME).
  Proof.
    ginit. gcofix CIH. intros.
    specialize (rutt_body i1 i2 RI_i).
    do 2 rewrite unfold_iter.
    eapply gpaco2_uclo; [|eapply orutt_clo_bind|]; eauto with paco.
    econstructor; eauto. intros ? ? [].
    - gstep.
      red; cbn.
      constructor.
      gbase.
      auto.
    - gstep.
      red.
      constructor.
      auto.
  Qed.

  (* TODO: Move this to orutt library *)
  Lemma orutt_iter_gen :
    forall {OOME E1 E2 : Type -> Type} `{OOM: OOME -< E2} {A B1 B2 : Type} {R : relation A} {S : relationH B1 B2} (pre : prerel E1 E2) (post : postrel E1 E2),
    forall (x : A -> itree E1 (A + B1)) (y : A -> itree E2 (A + B2)),
      (forall x0 y0 : A, R x0 y0 -> orutt pre post (sum_rel R S) (x x0) (y y0) (OOM:=OOME)) ->
      forall x0 y0 : A, R x0 y0 -> orutt pre post S (CategoryOps.iter x x0) (CategoryOps.iter y y0) (OOM:=OOME).
  Proof.
    intros OOME E1 E2 OOM A B1 B2 R S pre post body1 body2 EQ_BODY x y Hxy.
    eapply orutt_iter'; eauto.
  Qed.

  Lemma denote_phi_orutt :
    forall bid_from id_p,
      orutt exp_E_refine_strict exp_E_res_refine_strict (eq × uvalue_refine_strict)
        (IS1.LLVM.D.denote_phi bid_from id_p) (denote_phi bid_from id_p)
        (OOM:=OOME).
  Proof.
    intros bid_from id_p.
    destruct id_p as [lid phi].
    destruct phi.
    cbn.
    break_match_goal.
    - cbn.
      eapply orutt_bind with (RR:=uvalue_refine_strict).
      + apply denote_exp_E1E2_orutt.
      + intros r1 r2 REF.
        apply orutt_Ret.
        constructor; cbn; auto.
    - apply orutt_raise; cbn; auto.
      intros msg o CONTRA.
      inv CONTRA.
  Qed.

  Lemma denote_phis_orutt_strict_helper :
    forall phis bid_from,
      orutt instr_E_refine_strict instr_E_res_refine_strict (Forall2 (eq × uvalue_refine_strict))
        (map_monad
           (fun x => translate IS1.LP.Events.exp_to_instr (IS1.LLVM.D.denote_phi bid_from x))
           phis)
        (map_monad
           (fun x => translate exp_to_instr (denote_phi bid_from x))
           phis)
        (OOM:=OOME).
  Proof.
    induction phis; intros bid_from.
    - cbn.
      apply orutt_Ret.
      constructor.
    - repeat rewrite map_monad_unfold.
      eapply orutt_bind with (RR:=eq × uvalue_refine_strict).
      { apply translate_exp_to_instr_E1E2_orutt_strict.
        apply denote_phi_orutt.
      }

      intros [id1 uv1] [id2 uv2] [EQid EQuv].
      cbn in EQid, EQuv; subst.

      cbn.
      eapply orutt_bind with (RR:=Forall2 (eq × uvalue_refine_strict)); eauto.

      intros r1 r2 H.
      apply orutt_Ret.
      apply Forall2_cons.
      + constructor; cbn; auto.
      + auto.
  Qed.

  Lemma denote_phis_orutt_strict :
    forall phis bid_from,
      orutt instr_E_refine_strict instr_E_res_refine_strict eq
        (IS1.LLVM.D.denote_phis bid_from phis) (denote_phis bid_from phis)
        (OOM:=OOME).
  Proof.
    intros phis bid_from.
    cbn.
    eapply orutt_bind with (RR:=Forall2 (eq × uvalue_refine_strict)).
    { apply denote_phis_orutt_strict_helper.
    }

    intros r1 r2 H.
    eapply orutt_bind with (RR:=eq).
    { induction H.
      - cbn.
        apply orutt_Ret.
        reflexivity.
      - repeat rewrite map_monad_unfold.
        destruct x, y.
        cbn.
        eapply orutt_bind with (RR:=eq).
        { eapply orutt_trigger; cbn.
          inv H; auto.

          intros [] [] H1; auto.

          intros o CONTRA.
          inv CONTRA.
        }

        intros [] [] ?; subst.
        eapply orutt_bind with (RR:=eq); eauto.

        intros r1 r2 EQ; subst.
        eapply orutt_Ret; auto.
    }

    intros r0 r3 H0; subst.
    eapply orutt_Ret; auto.
  Qed.

  (* TODO: Move this *)
  Lemma map_monad_orutt :
    forall {V} (elts : list V) {OOM E1 E2} `{OOME : OOM -< E2} {R1 R2} (pre : prerel E1 E2) (post : postrel E1 E2) (RR: R1 -> R2 -> Prop) (denote1 : V -> itree E1 R1) (denote2 : V -> itree E2 R2),
      (forall e,
          orutt pre post RR (denote1 e) (denote2 e) (OOM:=OOM)) ->
      orutt pre post (Forall2 RR) (map_monad denote1 elts) (map_monad denote2 elts) (OOM:=OOM).
  Proof.
    intros V elts.
    induction elts; intros OOM E1 E2 OOME R1 R2 pre post RR denote1 denote2 H.
    - cbn.
      apply orutt_Ret.
      constructor.
    - cbn.
      eapply orutt_bind; eauto.
      intros r1 r2 H0.
      eapply orutt_bind; eauto.
      intros r0 r3 H1.
      eapply orutt_Ret.
      constructor; auto.
  Qed.

  (* TODO: move this *)
  Lemma map_monad_orutt2 :
    forall {V1 V2} (elts1 : list V1) (elts2 : list V2) {OOM E1 E2} `{OOME : OOM -< E2} {R1 R2} (pre : prerel E1 E2) (post : postrel E1 E2) (VV : V1 -> V2 -> Prop) (RR: R1 -> R2 -> Prop) (denote1 : V1 -> itree E1 R1) (denote2 : V2 -> itree E2 R2),
      (Forall2 VV elts1 elts2) ->
      (forall e1 e2,
          VV e1 e2 ->
          orutt pre post RR (denote1 e1) (denote2 e2) (OOM:=OOM)) ->
      orutt pre post (Forall2 RR) (map_monad denote1 elts1) (map_monad denote2 elts2) (OOM:=OOM).
  Proof.
    intros V1 V2 elts1 elts2 OOM E1 E2 OOME R1 R2 pre post VV RR denote1 denote2 VVS H.
    induction VVS.
    - cbn.
      apply orutt_Ret.
      constructor.
    - repeat rewrite map_monad_unfold.
      eapply orutt_bind; eauto.

      intros r1 r2 H1.
      eapply orutt_bind; eauto.

      intros r0 r3 H2.
      eapply orutt_Ret.
      constructor; auto.
  Qed.

  (* TODO: Move this *)
  Lemma Forall2_Forall2_HIn :
    forall {A B : Type} (xs : list A) (ys : list B) f,
      Forall2 f xs ys ->
      Forall2_HIn xs ys (fun a b HIna HInb => f a b).
  Proof.
    intros A B xs ys f H.
    induction H; cbn; auto.
  Qed.

  Transparent uvalue_refine_strict.
  Lemma denote_op_orutt_strict :
    forall op,
      orutt exp_E_refine_strict exp_E_res_refine_strict uvalue_refine_strict
        (IS1.LLVM.D.denote_op op)
        (denote_op op)
        (OOM:=OOME).
  Proof.
    intros op.
    destruct op; cbn;
      try
        solve
        [ solve_orutt_raise
        | eapply orutt_bind with (RR:=Forall2 uvalue_refine_strict);
          [ eapply map_monad_orutt;
            intros [e];
            eapply denote_exp_E1E2_orutt
          |
            intros r1 r2 H;
            change uvalue_refine_strict with (fun a b => uvalue_refine_strict a b) in H;
            unfold uvalue_refine_strict in H;
            eapply orutt_Ret;
            apply Forall2_Forall2_HInT in H;
            eapply map_monad_InT_oom_forall2 in H;
            unfold_uvalue_refine_strict;
            cbn;
            rewrite H;
            reflexivity
          ]
        |
          eapply orutt_bind with (RR:=uvalue_refine_strict);
          [eapply denote_exp_E1E2_orutt|];
          intros r1 r2 H;
          eapply orutt_bind with (RR:=uvalue_refine_strict);
          [eapply denote_exp_E1E2_orutt|];
          intros r0 r3 H0;
          apply orutt_Ret;
          unfold_uvalue_refine_strict_goal;
          unfold uvalue_refine_strict in *;
          rewrite H, H0;
          cbn;
          reflexivity
        |
          eapply orutt_bind with (RR:=uvalue_refine_strict);
          [eapply denote_exp_E1E2_orutt|];
          intros r1 r2 H;
          apply orutt_Ret;
          unfold_uvalue_refine_strict_goal;
          unfold uvalue_refine_strict in *;
          rewrite H;
          cbn;
          reflexivity
        |
          apply denote_exp_E1E2_orutt
        ].
    - cbn.
      apply translate_LU_to_exp_lookup_id_orutt.
    - apply orutt_Ret; solve_uvalue_refine_strict.
  Qed.
  Opaque uvalue_refine_strict.

  (* TODO: Move this *)
  (* TODO: May not hold for addresses / iptr depending on their size *)
  (* May be weird for integer sizes as well... *)
  Lemma undef_not_unique_prop :
    forall dt,
      dt <> DTYPE_Void ->
      ~ unique_prop (UVALUE_Undef dt).
  Proof.
    induction dt;
      intros NVOID;
      try contradiction.

  (*   { intros [dv UNIQUE]. *)
  (*     setoid_rewrite concretize_equation in UNIQUE. *)
  (*     unfold concretize_u in UNIQUE. *)
  (*     cbn in UNIQUE. *)

  (*     induction (dvalue_has_dtyp dv (DTYPE_I a)). *)
  (*   } *)
  (*   red in UNIQUE. *)
  (*   assert (dt = DTYPE_Void). *)
  (*   admit. *)
  (*   subst. *)
  (*   destruct UNIQUE as [dv UNIQUE]. *)
  (*   specialize (UNIQUE DVALUE_None). *)
  (*   unfold concretize, concretize_u in UNIQUE. *)
  (*   rewrite concretize_uvalueM_equation in UNIQUE. *)
  (*   cbn in *. *)
  (*   forward UNIQUE. *)
  (*   constructor. *)
  (*   subst. *)
  (* Qed. *)
  Admitted.


  (* (* Maybe I can use something like this for uvalue_refine_unique_prop *) *)
  (* Lemma convert_concretize : *)
  (*   uvalue_convert uv1 = uv2 -> *)
  (*   concretize uv2 dv2 -> *)
  (*   (exists t, dv2 = DVALUE_Oom t) (* May need to be a contains OOM predicate *) \/ *)
  (*     (exists dv1, concretize uv1 dv1 /\ *)
  (*               dvalue_convert dv1 = dv2). *)
  (* Qed. *)

  (* Lemma blah : *)
  (*   forall uv1 dv1, *)
  (*     concretize uv1 dv1 -> *)
  (*     concretize (uvalue_convert uv1) (dvalue_convert dv1). *)
  (* Qed. *)

  (* Lemma blah2  : *)
  (*   IS1.LLVM.D.unique_prop uv1 -> unique_prop (uvalue_convert uv1) *)

  (* (* Change unique_prop to be a specific dvalue instead of existential? *) *)
  Require Import Coq.Logic.Classical_Pred_Type.
  Lemma uvalue_refine_strict_unique_prop_contra :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      ~ unique_prop uv2 -> ~ IS1.LLVM.D.unique_prop uv1.
  Proof.
    intros uv1 uv2 REF NUNIQUE.

    unfold unique_prop in NUNIQUE.
    unfold IS1.LLVM.D.unique_prop.

    apply all_not_not_ex.
    intros dv1 CONTRA.

    rewrite uvalue_refine_strict_equation in REF.
    eapply not_ex_all_not in NUNIQUE.
    apply NUNIQUE.
  Admitted.

  Lemma uvalue_refine_strict_unique_prop :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      IS1.LLVM.D.unique_prop uv1 -> unique_prop uv2.
  Proof.
    intros uv1 uv2 REF UNIQUE.

    unfold unique_prop.
    unfold IS1.LLVM.D.unique_prop in UNIQUE.
    destruct UNIQUE as [dv1 UNIQUE].

  (*   split. *)
  (*   { revert uv2 H. *)
  (*     induction uv1 using IS1.LP.Events.DV.uvalue_ind'; intros uv2 REF [dv UNIQUE]; *)
  (*       try *)
  (*         solve *)
  (*         [ *)
  (*           red in REF; *)
  (*           rewrite uvalue_convert_strict_equation in REF; *)
  (*           cbn in REF; *)
  (*           first [break_match_hyp; inv REF | inv REF]; *)
  (*           eexists; *)
  (*           intros dv0 CONC; *)
  (*           do 2 red in CONC; *)
  (*           rewrite concretize_uvalueM_equation in CONC; *)
  (*           inv CONC; *)
  (*           auto *)
  (*         ]. *)

  (*     { (* Undef will be a contradiction in most cases... *) *)
  (* (*          Though not all *) *)
  (*       admit. *)
  (*     } *)

  (*     { (* Struct nil *) *)
  (*       red in REF; *)
  (*         rewrite uvalue_convert_strict_equation in REF; *)
  (*         cbn in REF; *)
  (*         first [break_match_hyp; inv REF | inv REF]; *)
  (*         eexists; *)
  (*         intros dv0 CONC. *)
  (*       do 2 red in CONC. *)
  (*       rewrite concretize_uvalueM_equation in CONC. *)
  (*       cbn in CONC. *)
  (*       red in CONC. *)
  (*       destruct CONC as [ma [k' [ARGS [CONC1 CONC2]]]]. *)
  (*       destruct_err_ub_oom ma; inv ARGS; try contradiction. *)
  (*       cbn in CONC2. *)
  (*       cbn in CONC1. *)
  (*       destruct CONC2 as [CONTRA | CONC2]; try contradiction. *)
  (*       specialize (CONC2 [] eq_refl). *)
  (*       set (k'_nil := k' []). *)
  (*       destruct_err_ub_oom k'_nil; subst k'_nil; *)
  (*         rewrite Hx in CONC2, CONC1; *)
  (*         try contradiction. *)

  (*       cbn in CONC1. *)
  (*       inv CONC1. *)
  (*       reflexivity. *)
  (*     } *)

  (*     { (* Structs *) *)
  (*       admit. *)
  (*     } *)

  (*     { (* Packed struct nil *) *)
  (*       red in REF; *)
  (*         rewrite uvalue_convert_strict_equation in REF; *)
  (*         cbn in REF; *)
  (*         first [break_match_hyp; inv REF | inv REF]; *)
  (*         eexists; *)
  (*         intros dv0 CONC. *)
  (*       do 2 red in CONC. *)
  (*       rewrite concretize_uvalueM_equation in CONC. *)
  (*       cbn in CONC. *)
  (*       red in CONC. *)
  (*       destruct CONC as [ma [k' [ARGS [CONC1 CONC2]]]]. *)
  (*       destruct_err_ub_oom ma; inv ARGS; try contradiction. *)
  (*       cbn in CONC2. *)
  (*       cbn in CONC1. *)
  (*       destruct CONC2 as [CONTRA | CONC2]; try contradiction. *)
  (*       specialize (CONC2 [] eq_refl). *)
  (*       set (k'_nil := k' []). *)
  (*       destruct_err_ub_oom k'_nil; subst k'_nil; *)
  (*         rewrite Hx in CONC2, CONC1; *)
  (*         try contradiction. *)

  (*       cbn in CONC1. *)
  (*       inv CONC1. *)
  (*       reflexivity. *)
  (*     } *)

  (*     { (* Packed structs *) *)
  (*       admit. *)
  (*     } *)

  (*     { (* Array nil *) *)
  (*       red in REF; *)
  (*         rewrite uvalue_convert_strict_equation in REF; *)
  (*         cbn in REF; *)
  (*         first [break_match_hyp; inv REF | inv REF]; *)
  (*         eexists; *)
  (*         intros dv0 CONC. *)
  (*       do 2 red in CONC. *)
  (*       rewrite concretize_uvalueM_equation in CONC. *)
  (*       cbn in CONC. *)
  (*       red in CONC. *)
  (*       destruct CONC as [ma [k' [ARGS [CONC1 CONC2]]]]. *)
  (*       destruct_err_ub_oom ma; inv ARGS; try contradiction. *)
  (*       cbn in CONC2. *)
  (*       cbn in CONC1. *)
  (*       destruct CONC2 as [CONTRA | CONC2]; try contradiction. *)
  (*       specialize (CONC2 [] eq_refl). *)
  (*       set (k'_nil := k' []). *)
  (*       destruct_err_ub_oom k'_nil; subst k'_nil; *)
  (*         rewrite Hx in CONC2, CONC1; *)
  (*         try contradiction. *)

  (*       cbn in CONC1. *)
  (*       inv CONC1. *)
  (*       reflexivity. *)
  (*     } *)

  (*     { (* Arrays *) *)
  (*       admit. *)
  (*     } *)

  (*     { (* Vector nil *) *)
  (*       red in REF; *)
  (*         rewrite uvalue_convert_strict_equation in REF; *)
  (*         cbn in REF; *)
  (*         first [break_match_hyp; inv REF | inv REF]; *)
  (*         eexists; *)
  (*         intros dv0 CONC. *)
  (*       do 2 red in CONC. *)
  (*       rewrite concretize_uvalueM_equation in CONC. *)
  (*       cbn in CONC. *)
  (*       red in CONC. *)
  (*       destruct CONC as [ma [k' [ARGS [CONC1 CONC2]]]]. *)
  (*       destruct_err_ub_oom ma; inv ARGS; try contradiction. *)
  (*       cbn in CONC2. *)
  (*       cbn in CONC1. *)
  (*       destruct CONC2 as [CONTRA | CONC2]; try contradiction. *)
  (*       specialize (CONC2 [] eq_refl). *)
  (*       set (k'_nil := k' []). *)
  (*       destruct_err_ub_oom k'_nil; subst k'_nil; *)
  (*         rewrite Hx in CONC2, CONC1; *)
  (*         try contradiction. *)

  (*       cbn in CONC1. *)
  (*       inv CONC1. *)
  (*       reflexivity. *)
  (*     } *)

  (*     { (* Vectors *) *)
  (*       admit. *)
  (*     } *)

  (*     { (* IBinop *) *)
  (*       red in REF; *)
  (*         rewrite uvalue_convert_strict_equation in REF; *)
  (*         cbn in REF. *)
  (*       first [ *)
  (*           break_match_hyp; inv REF; *)
  (*           break_match_hyp; inv H0 *)
  (*         | *)
  (*           break_match_hyp; inv REF | inv REF]. *)

  (*       red. *)
  (*       eexists. *)
  (*       intros dv0 CONC. *)

  (*       do 2 red in CONC. *)
  (*       rewrite concretize_uvalueM_equation in CONC. *)
  (*       cbn in CONC. *)
  (*       destruct CONC as [ma [k' [MA [CONC1 CONC2]]]]. *)
  (*       destruct_err_ub_oom ma; subst; cbn in CONC1, CONC2. *)
  (*       - (* OOM *) *)
  (*         inv CONC1. *)
  (*       - (* UB *) *)
  (*         (* May be a contradiction with UNIQUE? *) *)
  (*         rename dv into BLAH. *)
  (*         admit. *)
  (*       - (* Error *) *)
  (*         admit. *)
  (*       - (* Success *) *)
  (*         destruct CONC2 as [[] | CONC2]. *)
  (*         specialize (CONC2 ma0 eq_refl). *)
  (*         red in CONC2. *)
  (*         destruct CONC2 as [ma [k'0 CONC2]]. *)
  (*         destruct CONC2 as [CONC2 [CONC2_EQV CONC2_RET]]. *)

  (*         rewrite concretize_uvalueM_equation in CONC2. *)

  (*       cbn in CONC2. *)
  (*       cbn in CONC1. *)
  (*       (* specialize (CONC2 [] eq_refl). *) *)
  (*       (* set (k'_nil := k' []). *) *)
  (*       (* destruct_err_ub_oom k'_nil; subst k'_nil; *) *)
  (*       (*   rewrite Hx in CONC2, CONC1; *) *)
  (*       (*   try contradiction. *) *)

  (*       (* cbn in CONC1. *) *)
  (*       (* inv CONC1. *) *)
  (*       (* reflexivity. *) *)
  (*       admit. *)
  (*     } *)
  Admitted.

  (* TODO: This may not actually be true...

     Suppose uv1 is in the infinite language, and uv2 is in the finite
     language...

     If uv2 causes OOM (e.g., it represents an intptr expression of
     any value greater than 2^64), then `unique_prop uv2` would
     actually hold vacuously...

        Definition unique_prop (uv : uvalue) : Prop
          := exists x, forall dv, concretize uv dv -> dv = x.

     because `forall dv, concretize uv2 dv <-> False`...

     However in the infinite language `uv1` might not be unique.
   *)
  Lemma uvalue_refine_strict_unique_prop_rev :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      unique_prop uv2 -> IS1.LLVM.D.unique_prop uv1.
  Proof.
  Abort.


  (* Lemma pickUnique_lazy_rutt : *)
  (*   forall uv1 uv2, *)
  (*     uvalue_refine_lazy uv1 uv2 -> *)
  (*     rutt (sum_prerel call_refine_lazy event_refine_lazy) *)
  (*       (sum_postrel call_res_refine_lazy event_res_refine_lazy) dvalue_refine_lazy *)
  (*       (IS1.LLVM.D.pickUnique uv1) (pickUnique uv2). *)
  (* Proof. *)
  (*   (* intros uv1 uv2 REF. *) *)
  (*   (* unfold IS1.LLVM.D.pickUnique, IS1.LLVM.D.concretize_or_pick. *) *)
  (*   (* unfold pickUnique, concretize_or_pick. *) *)
  (*   (* cbn. *) *)
  (*   (* break_match; *) *)
  (*   (*   eapply uvalue_convert_lazy_preserves_is_concrete with (uvc:=uv2) in Heqb; eauto; *) *)
  (*   (*   rewrite Heqb. *) *)

  (*   (* apply lift_err_uvalue_to_dvalue_rutt; auto. *) *)

  (*   (* repeat rewrite bind_trigger. *) *)
  (*   (* apply rutt_Vis. *) *)

  (*   (* { constructor. *) *)
  (*   (*   cbn. *) *)
  (*   (*   split; auto. *) *)
  (*   (*   apply uvalue_refine_lazy_unique_prop; *) *)
  (*   (*     eauto. *) *)
  (*   (* } *) *)

  (*   (* intros t1 t2 H. *) *)
  (*   (* apply rutt_Ret. *) *)
  (*   (* destruct t1, t2. *) *)
  (*   (* cbn in *. *) *)
  (*   (* destruct H; cbn in *. *) *)
  (*   (* { red in H. *) *)
  (*   (*   destruct e1; cbn in *. *) *)
  (*   (*   destruct d1; cbn in *. *) *)
  (*   (*   admit. (* ???? *) *) *)
  (*   (* } *) *)
  (*   (* { destruct e2; cbn in *. *) *)
  (*   (*   admit. *) *)
  (*   (*   cbn in *. *) *)
  (*   (*   destruct d2; cbn in *. *) *)
  (*   (*   repeat (destruct s; try inv H). *) *)
  (*   (*   admit. *) *)
  (*   (* } *) *)
  (* Admitted. *)

  Lemma lift_err_uvalue_to_dvalue_rutt_strict :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      rutt (sum_prerel call_refine_strict event_refine_strict) (sum_postrel call_res_refine_strict event_res_refine_strict) dvalue_refine_strict
        (LLVMEvents.lift_err (fun x : IS1.LP.Events.DV.dvalue => Ret x) (IS1.LP.Events.DV.uvalue_to_dvalue uv1))
        (LLVMEvents.lift_err (fun x : dvalue => Ret x) (uvalue_to_dvalue uv2)).
  Proof.
    intros uv1 uv2 H.
    destruct uv1; cbn in *;
      try solve
        [ unfold_uvalue_refine_strict_in H;
          cbn in *; inv H; cbn;
          apply rutt_Ret;
          unfold_dvalue_refine_strict_goal; reflexivity
        | unfold_uvalue_refine_strict_in H;
          cbn in *; inv H; cbn;
          apply rutt_raise; constructor; cbn; auto
        | unfold_uvalue_refine_strict_in H;
          cbn in *;
          break_match_hyp; inv H;
          break_match_hyp; inv H1;
          cbn;
          apply rutt_raise;
          constructor;
          constructor
        | unfold_uvalue_refine_strict;
          cbn in *;
          break_match_hyp; inv H;
          cbn;
          apply rutt_raise; constructor; constructor
        | unfold_uvalue_refine_strict;
          cbn in *;
          break_match_hyp; inv H;
          break_match_hyp; inv H1;
          break_match_hyp; inv H0;
          cbn;
          apply rutt_raise; constructor; constructor
        ].
    - unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.
      cbn.
      apply rutt_Ret.
      unfold_dvalue_refine_strict_goal.
      rewrite Heqo.
      cbn.
      reflexivity.
    - unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.
      cbn.
      apply rutt_Ret.
      unfold_dvalue_refine_strict_goal.
      cbn.
      rewrite Heqo.
      reflexivity.
    - (* Structs *)
      unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.

      assert (uvalue_refine_strict (DV1.UVALUE_Struct fields) (DV2.UVALUE_Struct l)) as REF.
      { unfold_uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply rutt_raise.
        constructor.
        constructor.
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply rutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold_dvalue_refine_strict.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        cbn in H2.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
    - (* Packed Structs *)
      unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.

      assert (uvalue_refine_strict (DV1.UVALUE_Struct fields) (DV2.UVALUE_Struct l)) as REF.
      { unfold_uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply rutt_raise.
        constructor.
        constructor.
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply rutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold_dvalue_refine_strict.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        cbn in H2.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
    - (* Arrays *)
      unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.

      assert (uvalue_refine_strict (DV1.UVALUE_Array elts) (DV2.UVALUE_Array l)) as REF.
      { unfold_uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply rutt_raise.
        constructor.
        constructor.
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply rutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold_dvalue_refine_strict.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        cbn in H2.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
    - (* Vectors *)
      unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.

      assert (uvalue_refine_strict (DV1.UVALUE_Array elts) (DV2.UVALUE_Array l)) as REF.
      { unfold_uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply rutt_raise.
        constructor.
        constructor.
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply rutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold_dvalue_refine_strict.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        cbn in H2.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
  Qed.

  Lemma lift_err_uvalue_to_dvalue_orutt_strict :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      orutt (sum_prerel call_refine_strict event_refine_strict) (sum_postrel call_res_refine_strict event_res_refine_strict) dvalue_refine_strict
        (LLVMEvents.lift_err (fun x : IS1.LP.Events.DV.dvalue => Ret x) (IS1.LP.Events.DV.uvalue_to_dvalue uv1))
        (LLVMEvents.lift_err (fun x : dvalue => Ret x) (uvalue_to_dvalue uv2))
        (OOM:=OOME).
  Proof.
    intros uv1 uv2 H.
    destruct uv1; cbn in *;
      try solve
        [ unfold_uvalue_refine_strict_in H;
          cbn in *; inv H; cbn;
          apply orutt_Ret;
          unfold_dvalue_refine_strict_goal; reflexivity
        | unfold_uvalue_refine_strict_in H;
          cbn in *; inv H; cbn;
          apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; cbn; auto
          ]
        | unfold_uvalue_refine_strict_in H;
          cbn in *;
          break_match_hyp; inv H;
          break_match_hyp; inv H1;
          cbn;
          apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ]
        | unfold_uvalue_refine_strict;
          cbn in *;
          break_match_hyp; inv H;
          cbn;
          apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ]
        | unfold_uvalue_refine_strict;
          cbn in *;
          break_match_hyp; inv H;
          break_match_hyp; inv H1;
          break_match_hyp; inv H0;
          cbn;
          apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ]
        ].
    - unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.
      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict_goal.
      rewrite Heqo.
      cbn.
      reflexivity.
    - unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.
      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict_goal.
      cbn.
      rewrite Heqo.
      reflexivity.
    - (* Structs *)
      unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.

      assert (uvalue_refine_strict (DV1.UVALUE_Struct fields) (DV2.UVALUE_Struct l)) as REF.
      { unfold_uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ].
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold_dvalue_refine_strict.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        cbn in H2.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
    - (* Packed Structs *)
      unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.

      assert (uvalue_refine_strict (DV1.UVALUE_Struct fields) (DV2.UVALUE_Struct l)) as REF.
      { unfold_uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ].
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold_dvalue_refine_strict.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        cbn in H2.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
    - (* Arrays *)
      unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.

      assert (uvalue_refine_strict (DV1.UVALUE_Array elts) (DV2.UVALUE_Array l)) as REF.
      { unfold_uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ].
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold_dvalue_refine_strict.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        cbn in H2.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
    - (* Vectors *)
      unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.

      assert (uvalue_refine_strict (DV1.UVALUE_Array elts) (DV2.UVALUE_Array l)) as REF.
      { unfold_uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ].
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold_dvalue_refine_strict.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        cbn in H2.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
  Qed.

  Lemma pickUnique_rutt_strict :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      rutt (sum_prerel call_refine_strict event_refine_strict)
        (sum_postrel call_res_refine_strict event_res_refine_strict) dvalue_refine_strict
        (IS1.LLVM.D.pickUnique uv1) (pickUnique uv2).
  Proof.
    intros uv1 uv2 REF.
    unfold IS1.LLVM.D.pickUnique, IS1.LLVM.D.concretize_or_pick.
    unfold pickUnique, concretize_or_pick.
    cbn.
    break_match;
      eapply uvalue_refine_strict_preserves_is_concrete with (uvc:=uv2) in Heqb; eauto;
      rewrite Heqb.

    apply lift_err_uvalue_to_dvalue_rutt_strict; auto.

    repeat rewrite bind_trigger.
    apply rutt_Vis.

    { constructor.
      cbn.
      split; auto.
      - apply uvalue_refine_strict_unique_prop; auto.
    }

    intros t1 t2 H.
    apply rutt_Ret.
    destruct t1 as [dv1 []].
    destruct t2 as [dv2 []].
    cbn in *.
    inv H; subst_existT; cbn in *.
    tauto.
  Qed.

  Lemma pickUnique_orutt_strict :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      orutt (sum_prerel call_refine_strict event_refine_strict)
        (sum_postrel call_res_refine_strict event_res_refine_strict) dvalue_refine_strict
        (IS1.LLVM.D.pickUnique uv1) (pickUnique uv2)
        (OOM:=OOME).
  Proof.
    intros uv1 uv2 REF.
    unfold IS1.LLVM.D.pickUnique, IS1.LLVM.D.concretize_or_pick.
    unfold pickUnique, concretize_or_pick.
    cbn.
    break_match;
      eapply uvalue_refine_strict_preserves_is_concrete with (uvc:=uv2) in Heqb; eauto;
      rewrite Heqb.

    apply lift_err_uvalue_to_dvalue_orutt_strict; auto.

    repeat rewrite bind_trigger.
    apply orutt_Vis.

    { constructor.
      cbn.
      split; auto.
      - apply uvalue_refine_strict_unique_prop; auto.
    }

    intros t1 t2 H.
    apply orutt_Ret.
    destruct t1 as [dv1 []].
    destruct t2 as [dv2 []].
    cbn in *.
    inv H; subst_existT; cbn in *.
    tauto.

    intros o CONTRA; inv CONTRA.
  Qed.

  (* TODO: can these pickUnique lemmas be generalized? Different
  prerel / postrel, but fundamentally the same lemma... *)
  Lemma pickUnique_instr_E_orutt_strict :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      orutt instr_E_refine_strict instr_E_res_refine_strict dvalue_refine_strict
        (IS1.LLVM.D.pickUnique uv1) (pickUnique uv2)
        (OOM:=OOME).
  Proof.
  Admitted.

  Lemma pickUnique_exp_E_orutt_strict :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      orutt exp_E_refine_strict exp_E_res_refine_strict dvalue_refine_strict
        (IS1.LLVM.D.pickUnique uv1) (pickUnique uv2)
        (OOM:=OOME).
  Proof.
  Admitted.

  Lemma uvalue_refine_strict_concretize_poison :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      (forall dt : dtyp, ~ IS1.LLVM.MEM.CP.CONC.concretize uv1 (IS1.LP.Events.DV.DVALUE_Poison dt)) <->
        (forall dt : dtyp, ~ concretize uv2 (DVALUE_Poison dt)).
  Proof.
    (* This may not be true if uv2 can OOM... *)
  Admitted.

  Lemma dvalue_int_unsigned_E1E2 :
    forall x y,
      dvalue_refine_strict x y ->
      IS1.LP.Events.DV.dvalue_int_unsigned x = dvalue_int_unsigned y.
  Proof.
    induction x; intros y REF;
      try
        solve
        [ unfold_dvalue_refine_strict;
          cbn in *; inv REF; cbn; auto
        | unfold_dvalue_refine_strict;
          cbn in *;
          break_match_hyp; inv REF;
          cbn; auto
        ].
    - unfold_dvalue_refine_strict.
      cbn in *.
      break_match_hyp; inv REF.
      cbn; auto.
      apply IP.from_Z_to_Z in Heqo.
      rewrite <- IP.to_Z_to_unsigned.
      rewrite <- IS1.LP.IP.to_Z_to_unsigned.
      auto.
  Qed.

  Lemma denote_instr_orutt_strict :
    forall instr,
      orutt instr_E_refine_strict instr_E_res_refine_strict eq
        (IS1.LLVM.D.denote_instr instr)
        (denote_instr instr)
        (OOM:=OOME).
  Proof.
    intros [[id | id] instr].
    { cbn.
      destruct instr; try solve_orutt_raise.
      - apply orutt_raise; cbn; auto.
        intros msg0 o CONTRA.
        inv CONTRA.
      - apply orutt_bind with (RR:=uvalue_refine_strict).
        { apply translate_exp_to_instr_E1E2_orutt_strict.
          apply denote_op_orutt_strict.
        }

        intros r1 r2 H.
        eapply orutt_trigger; cbn.
        inv H; auto.

        intros [] [] H1; auto.

        intros o CONTRA.
        inv CONTRA.

      - destruct fn.
        apply orutt_bind with (RR:=Forall2 uvalue_refine_strict).
        { apply map_monad_orutt.
          intros [? ?].
          apply translate_exp_to_instr_E1E2_orutt_strict.
          apply denote_exp_E1E2_orutt.
        }

        intros r1 r2 H.
        apply orutt_bind with (RR:=uvalue_refine_strict).
        { break_match.
          - apply orutt_bind with (RR:=Forall2 dvalue_refine_strict).
            + eapply map_monad_orutt2; eauto.
              intros e1 e2 H0.
              apply pickUnique_instr_E_orutt_strict; auto.
            + intros r0 r3 H0.
              unfold ITree.map.
              eapply orutt_bind with (RR:=dvalue_refine_strict).
              { eapply orutt_trigger; cbn; try tauto.
                intros o CONTRA.
                inv CONTRA.
              }

              intros r4 r5 H1.
              eapply orutt_Ret.
              eapply dvalue_refine_strict_dvalue_to_uvalue; eauto.
          - eapply orutt_bind with (RR:=uvalue_refine_strict).
            { apply translate_exp_to_instr_E1E2_orutt_strict.
              apply denote_op_orutt_strict.
            }

            intros r0 r3 H0.
            eapply orutt_trigger; cbn; try tauto.
            intros o CONTRA.
            inv CONTRA.
        }

        intros r0 r3 H0.
        eapply orutt_trigger; cbn; try tauto.
        intros [] [] _; auto.
        intros o CONTRA.
        inv CONTRA.
      - break_inner_match.
        { break_inner_match;
            try
              solve
              [ cbn;
                eapply orutt_bind with (RR:=dvalue_refine_strict);
                [ eapply orutt_trigger; cbn; try tauto;
                  intros o CONTRA;
                  inv CONTRA
                |
                ];

                intros r1 r2 H;
                eapply orutt_trigger; cbn; try tauto;
                [ split; auto; eapply dvalue_refine_strict_dvalue_to_uvalue; eauto
                | intros [] [] _; auto
                | intros o CONTRA; inv CONTRA
                ]
              ].

          destruct t0.
          eapply orutt_bind with (RR:=uvalue_refine_strict).
          { apply translate_exp_to_instr_E1E2_orutt_strict.
            apply denote_exp_E1E2_orutt.
          }

          intros r1 r2 H.
          eapply orutt_bind with (RR:=dvalue_refine_strict).
          apply pickUnique_instr_E_orutt_strict; auto.

          intros r0 r3 H0.
          eapply orutt_bind with (RR:=dvalue_refine_strict).
          { eapply orutt_trigger; cbn; try tauto.
            2: intros o CONTRA; inv CONTRA.

            split; auto.
            split; auto.

            erewrite dvalue_int_unsigned_E1E2; eauto.
          }

          intros r4 r5 H1.
          eapply orutt_trigger; cbn; try tauto;
            [ split; auto; eapply dvalue_refine_strict_dvalue_to_uvalue; eauto
            | intros [] [] _; auto
            | intros o CONTRA; inv CONTRA
            ].
        }

        { apply orutt_bind with (RR:=dvalue_refine_strict).
          eapply orutt_trigger; cbn; try tauto; intros o CONTRA; inv CONTRA.

          intros r1 r2 H.
          eapply orutt_trigger; cbn; try tauto;
            [ split; auto; eapply dvalue_refine_strict_dvalue_to_uvalue; eauto
            | intros [] [] _; auto
            | intros o CONTRA; inv CONTRA
            ].
        }

      - destruct ptr.
        eapply orutt_bind.
        { apply translate_exp_to_instr_E1E2_orutt_strict.
          apply denote_exp_E1E2_orutt.
        }

        intros r1 r2 H.
        eapply orutt_bind.
        { apply pickUnique_instr_E_orutt_strict; auto.
        }

        intros r0 r3 H0.
        eapply orutt_bind.
        { apply orutt_trigger; cbn; auto.
          intros t1 t2 H1.
          apply H1.

          intros o CONTRA; inv CONTRA.
        }

        intros r4 r5 H1.
        cbn in H1.
        apply orutt_trigger; cbn; auto.
        tauto.
        intros [] [] _; auto.
        intros o CONTRA; inv CONTRA.
      - apply orutt_raise; cbn; auto.
        intros msg o0 CONTRA; inv CONTRA.
    }

    { cbn.
      destruct instr; try solve_orutt_raise.
      - apply orutt_Ret; cbn; auto.
      - destruct fn.
        apply orutt_bind with (RR:=Forall2 uvalue_refine_strict).
        { apply map_monad_orutt.
          intros e0. destruct e0.
          apply translate_exp_to_instr_E1E2_orutt_strict.
          apply denote_exp_E1E2_orutt.
        }

        intros r1 r2 H.
        apply orutt_bind with (RR:=uvalue_refine_strict).
        { break_match.
          { apply orutt_bind with (RR:=Forall2 dvalue_refine_strict).
            { eapply map_monad_orutt2; eauto.
              intros e1 e2 H0.
              apply pickUnique_instr_E_orutt_strict; auto.
            }

            intros r0 r3 H0.
            apply orutt_bind with (RR:=dvalue_refine_strict).
            { apply orutt_trigger; cbn; auto.
              intros t1 t2 H1.
              apply H1.

              intros o CONTRA; inv CONTRA.
            }

            intros r4 r5 H1.
            apply orutt_Ret.
            apply dvalue_refine_strict_dvalue_to_uvalue; auto.
          }

          { apply orutt_bind with (RR:=uvalue_refine_strict).
            { apply translate_exp_to_instr_E1E2_orutt_strict.
              apply denote_exp_E1E2_orutt.
            }

            intros r0 r3 H0.
            apply orutt_trigger; cbn; auto.
            intros t1 t2 H1.
            apply H1.

            intros o CONTRA; inv CONTRA.
          }
        }

        intros r0 r3 H0.
        apply orutt_Ret; auto.
      - destruct val, ptr.
        apply orutt_bind with (RR:=uvalue_refine_strict).
        { apply translate_exp_to_instr_E1E2_orutt_strict.
          apply denote_exp_E1E2_orutt.
        }

        intros r1 r2 H.
        apply orutt_bind with (RR:=uvalue_refine_strict).
        { apply translate_exp_to_instr_E1E2_orutt_strict.
          apply denote_exp_E1E2_orutt.
        }

        intros r0 r3 H0.
        apply orutt_bind with (RR:=dvalue_refine_strict).
        { apply pickUnique_instr_E_orutt_strict; auto.
        }

        intros r4 r5 H1.
        { destruct r4; unfold_dvalue_refine_strict; cbn in *; try break_match_hyp; inv H1; cbn;
            try
              solve
              [ apply orutt_trigger; cbn; auto;
                [ split; auto;
                  split; auto; solve_dvalue_refine_strict
                | intros [] [] _; auto
                | intros o CONTRA; inv CONTRA
                ]
              | solve_orutt_raiseUB
              ].
          - apply orutt_trigger; cbn; auto.
            split; auto.
            split; auto.
            unfold_dvalue_refine_strict; cbn; rewrite Heqo; auto.

            intros [] [] _; auto.
            intros o CONTRA; inv CONTRA.
          - apply orutt_trigger; cbn; auto.
            split; auto.
            split; auto.
            unfold_dvalue_refine_strict; cbn; rewrite Heqo; auto.

            intros [] [] _; auto.
            intros o CONTRA; inv CONTRA.
          - apply orutt_trigger; cbn; auto.
            split; auto.
            split; auto.
            unfold_dvalue_refine_strict; cbn; rewrite Heqo; auto.

            intros [] [] _; auto.
            intros o CONTRA; inv CONTRA.
          - apply orutt_trigger; cbn; auto.
            + split; auto.
              split; auto.
              unfold_dvalue_refine_strict.
              rewrite Heqo.
              cbn; auto.
            + intros [] [] _; auto.
            + intros o CONTRA; inv CONTRA.
          - apply orutt_trigger; cbn; auto.
            + split; auto.
              split; auto.
              unfold_dvalue_refine_strict.
              rewrite Heqo.
              cbn; auto.
            + intros [] [] _; auto.
            + intros o CONTRA; inv CONTRA.
          - apply orutt_trigger; cbn; auto.
            + split; auto.
              split; auto.
              unfold_dvalue_refine_strict.
              rewrite Heqo.
              cbn; auto.
            + intros [] [] _; auto.
            + intros o CONTRA; inv CONTRA.
        }

      - clear o.
        solve_orutt_raise.
    }
  Qed.

  Lemma denote_terminator_orutt_strict :
    forall term,
      orutt exp_E_refine_strict exp_E_res_refine_strict (sum_rel eq uvalue_refine_strict) (IS1.LLVM.D.denote_terminator term)
        (denote_terminator term)
        (OOM:=OOME).
  Proof.
    intros term.
    destruct term; cbn.
    - destruct v.
      eapply orutt_bind with (RR:=uvalue_refine_strict).
      apply denote_exp_E1E2_orutt.

      intros r1 r2 H.
      apply orutt_Ret; auto.
    - apply orutt_Ret; auto.
      constructor; solve_uvalue_refine_strict.
    - destruct v.
      eapply orutt_bind with (RR:=uvalue_refine_strict).
      apply denote_exp_E1E2_orutt.

      intros r1 r2 H.
      eapply orutt_bind with (RR:=dvalue_refine_strict).
      (* TODO: need something about concretize_or_pick *)
      admit.

      intros r0 r3 H0.
      break_match; unfold_dvalue_refine_strict; cbn in *; try break_match_hyp; inv H0;
        try
          solve
          [ solve_orutt_raise
          ].

      break_match; apply orutt_Ret; auto.
      solve_orutt_raiseUB.
    - apply orutt_Ret; auto.
    - destruct v.
      eapply orutt_bind with (RR:=uvalue_refine_strict).
      apply denote_exp_E1E2_orutt.

      intros r1 r2 H.
      eapply orutt_bind with (RR:=dvalue_refine_strict).
      apply pickUnique_exp_E_orutt_strict; auto.

      intros r0 r3 H0.
      Set Nested Proofs Allowed.
      Lemma dvalue_refine_strict_preserves_dvalue_is_poison :
        forall x y,
          dvalue_refine_strict x y ->
          DV1.dvalue_is_poison x = DV2.dvalue_is_poison y.
      Proof.
        intros x y H.
        destruct x;
        unfold_dvalue_refine_strict; cbn in *; try break_match_hyp; inv H; cbn; auto.
      Qed.

      pose proof dvalue_refine_strict_preserves_dvalue_is_poison _ _ H0.
      rewrite H1.
      break_match;
        [solve_orutt_raiseUB|].

      eapply orutt_bind with (RR:=Forall2 (dvalue_refine_strict × eq)).
      { eapply map_monad_orutt.
        intros e0.
        destruct e0.
        destruct t.

        eapply orutt_bind with (RR:=dvalue_refine_strict).
        { repeat (break_match; try solve_orutt_raise).
          all: apply orutt_Ret; solve_dvalue_refine_strict.
        }

        intros r4 r5 H2.
        eapply orutt_Ret.
        constructor; auto.
      }

      intros r4 r5 H2.
      (* TODO: switch??? *)
      admit.
    - solve_orutt_raise.
    - solve_orutt_raise.
    - solve_orutt_raise.
    - solve_orutt_raiseUB.
  Admitted.

  Lemma denote_block_orutt_strict :
    forall block bid,
      orutt instr_E_refine_strict instr_E_res_refine_strict (sum_rel eq uvalue_refine_strict)
        (IS1.LLVM.D.denote_block block bid)
        (denote_block block bid)
        (OOM:=OOME).
  Proof.
    intros block bid.
    cbn.
    apply orutt_bind with (RR:=eq).
    { apply denote_phis_orutt_strict. }

    intros [] [] _.
    apply orutt_bind with (RR:=eq).
    { apply orutt_bind with (RR:=Forall2 eq).
      { eapply map_monad_orutt.
        eapply denote_instr_orutt_strict.
      }

      intros r1 r2 H.
      apply orutt_Ret.
      reflexivity.
    }

    intros [] [] _.
    apply translate_exp_to_instr_E1E2_orutt_strict.
    apply denote_terminator_orutt_strict.
  Qed.

  Lemma denote_ocfg_orutt_strict :
    forall cfg bids,
      orutt instr_E_refine_strict instr_E_res_refine_strict (sum_rel (eq × eq) uvalue_refine_strict)
        (IS1.LLVM.D.denote_ocfg cfg bids)
        (denote_ocfg cfg bids)
        (OOM:=OOME).
  Proof.
    intros cfg [bid_from bid_src].
    Opaque denote_phis denote_phi.
    Opaque IS1.LLVM.D.denote_phis IS1.LLVM.D.denote_phi.
    unfold denote_ocfg, IS1.LLVM.D.denote_ocfg.
    cbn.
    eapply @orutt_iter_gen with (R:=eq); auto.
    intros x0 y0 EQ.
    subst.
    destruct y0 as [from src].

    break_match_goal.
    { (* Found a block *)
      eapply orutt_bind with (RR:=sum_rel eq uvalue_refine_strict).
      { eapply orutt_bind with (RR:=eq).
        { apply denote_phis_orutt_strict. }

        intros [] [] _.
        eapply orutt_bind with (RR:=eq).
        { eapply orutt_bind with (RR:=Forall2 eq).
          { eapply map_monad_orutt.
            intros e.
            eapply denote_instr_orutt_strict.
          }

          intros r1 r2 H.
          apply orutt_Ret; auto.
        }

        intros [] [] _.
        apply translate_exp_to_instr_E1E2_orutt_strict.
        apply denote_terminator_orutt_strict.
      }

      intros r1 r2 H.
      inv H.
      apply orutt_Ret; auto.
      apply orutt_Ret; auto.
    }

    { (* No block found *)
      apply orutt_Ret.
      constructor.
      constructor.
      auto.
    }
  Qed.

  Lemma address_one_function_E1E2_orutt :
    forall dfn,
      orutt event_refine_strict event_res_refine_strict (dvalue_refine_strict × function_denotation_refine_strict)
        (LLVM1.address_one_function dfn)
        (LLVM2.address_one_function dfn)
        (OOM:=OOME).
  Proof.
    intros dfn.
    cbn.
    eapply orutt_bind with (RR:=dvalue_refine_strict).
    apply rutt_orutt. apply GlobalRead_L0_E1E2_rutt.
    solve_dec_oom.

    intros r1 r2 R1R2.
    apply orutt_Ret.

    constructor.
    - cbn; auto.
    - cbn.
      red.
      intros args1 args2 ARGS.
      cbn.
      eapply orutt_bind with (RR:=Forall2 (eq × uvalue_refine_strict)).
      { cbn.
        pose proof (Util.Forall2_length ARGS) as LEN.
        destruct (combine_lists_err (LLVMAst.df_args dfn) args1) eqn:HARGS1.
        { (* Error, means args1 differs in length *)
          (* Currently combine_lists_err does not ever error... This
             may change in the future.*)
          apply combine_lists_err_inl_contra in HARGS1.
          contradiction.
        }

        { assert (length args1 = length args2) as ARGSLEN by eauto using Util.Forall2_length.
          cbn.
          destruct (combine_lists_err (LLVMAst.df_args dfn) args2) eqn:HARGS2.
          apply combine_lists_err_inl_contra in HARGS2; contradiction.

          (* I know args2 is a uvalue refinement of args1.

             I also know that in HARGS1 and HARGS2, args1 and args2
             are being combined with the same list.

             This should mean that `l` and `l0` have the same length...

             And also something like...

             Forall2 (eq × uvalue_refine) l l0
           *)

          assert (Forall2 (eq × uvalue_refine_strict) l l0) as LL0.
          { assert (length l = length l0) as LENLL0.
            { eapply combine_lists_err_length_eq; eauto.
            }

            cbn.
            apply Util.Forall2_forall.
            split; auto.

            intros i a b NTHl NTHl0.
            destruct a as [a1 a2].
            destruct b as [b1 b2].
            epose proof (combine_lists_err_Nth_inv _ _ _ _ _ _ NTHl HARGS1) as [AARGS AARGS1].
            epose proof (combine_lists_err_Nth_inv _ _ _ _ _ _ NTHl0 HARGS2) as [BARGS BARGS1].

            constructor; cbn.
            - cbn in *.
              rewrite AARGS in BARGS.
              inv BARGS.
              reflexivity.
            - eapply Util.Forall2_Nth; eauto.
          }

          cbn.
          apply orutt_Ret; auto.
        }
      }


      intros params1 params2 PARAMS.
      eapply orutt_bind with (RR:=eq).
      { apply orutt_trigger.
        cbn; auto.

        constructor.
        constructor.
        intros [] [] _.
        reflexivity.

        intros o CONTRA.
        inv CONTRA.
      }

      intros [] [] _.

      eapply orutt_bind with (RR:=eq).
      { apply orutt_trigger.
        - cbn.
          induction PARAMS.
          + constructor; cbn.
            apply local_refine_strict_empty.
          + destruct x as [xid xuv].
            destruct y as [yid yuv].
            inv H.
            cbn in fst_rel, snd_rel. subst.
            constructor; cbn.
            inv IHPARAMS; subst_existT.
            apply alist_refine_cons; auto.
        - intros [] [] _.
          reflexivity.
        - intros o CONTRA; inv CONTRA.
      }

      intros [] [] _.
      eapply orutt_bind with (RR:=uvalue_refine_strict).
      { rewrite translate_bind.
        rewrite translate_bind.

        eapply orutt_bind with (RR:=sum_rel (eq × eq) uvalue_refine_strict).
        { (* ocfg stuff *)
          apply translate_instr_to_L0'_E1E2_orutt_strict.
          apply denote_ocfg_orutt_strict.
        }

        intros r0 r3 H.
        inv H.
        - inv H0.
          destruct a1, a2.
          cbn in *.
          subst.
          unfold LLVMEvents.raise.
          rewrite bind_trigger.
          rewrite bind_trigger.
          rewrite translate_vis.
          rewrite translate_vis.
          cbn.
          apply orutt_Vis; cbn; auto.
          constructor; cbn; auto.
          intros [] [] _.
          intros o CONTRA.
          inv CONTRA.
        - do 2 rewrite translate_ret.
          apply orutt_Ret.
          auto.
      }

      intros r0 r3 R0R3.
      eapply orutt_bind with (RR:=eq).
      { eapply orutt_trigger.
        cbn; constructor; cbn; auto.
        intros [] [] _.
        reflexivity.
        intros o CONTRA; inv CONTRA.
      }

      intros [] [] _.
      eapply orutt_bind with (RR:=eq).
      { eapply orutt_trigger.
        cbn; constructor; cbn; auto.
        intros [] [] _.
        reflexivity.
        intros o CONTRA; inv CONTRA.
      }

      intros [] [] _.
      eapply orutt_Ret.
      auto.
  Qed.

  Lemma address_one_functions_E1E2_orutt :
    forall dfns,
      orutt event_refine_strict event_res_refine_strict
        (Forall2 (dvalue_refine_strict × function_denotation_refine_strict))
        (map_monad LLVM1.address_one_function dfns)
        (map_monad address_one_function dfns)
        (OOM:=OOME).
  Proof.
    intros dfns.
    apply map_monad_orutt.
    intros e.
    apply address_one_function_E1E2_orutt.
  Qed.

  Lemma lookup_defn_some_refine_strict :
    forall dfns1 dfns2 r1 r2 f_den1,
      Forall2 (dvalue_refine_strict × function_denotation_refine_strict) dfns1 dfns2 ->
      dvalue_refine_strict r1 r2 ->
      IS1.LLVM.D.lookup_defn r1 dfns1 = Some f_den1 ->
      exists f_den2,
        IS2.LLVM.D.lookup_defn r2 dfns2 = Some f_den2 /\
          function_denotation_refine_strict f_den1 f_den2.
  Proof.
    intros dfns1 dfns2 r1 r2 f_den1 DFNS R1R2 LUP.

    pose proof DFNS as NTH.
    apply Util.Forall2_forall in NTH as [LEN NTH].

    pose proof LUP as LUP'.
    eapply assoc_similar_lookup with
      (xs:=dfns1) (ys:=dfns2) (a:=r1) (b:=f_den1) in LUP';
      eauto.
    2: {
      apply dvalue_refine_strict_R2_injective.
    }

    destruct LUP' as [c [d [i [ASSOC [NTH1 NTH2]]]]].
    exists d.

    pose proof (NTH i (r1, f_den1) (c, d) NTH1 NTH2).
    inv H; cbn in *.
    split; auto.

    assert (c = r2) as CR2.
    { eapply dvalue_refine_strict_R2_injective; eauto.
    }

    subst.
    auto.
  Qed.

  (* May not be true with new dvalue_refine *)
  Lemma lookup_defn_none_strict :
    forall dfns1 dfns2 r1 r2,
      Forall2 (dvalue_refine_strict × function_denotation_refine_strict) dfns1 dfns2 ->
      dvalue_refine_strict r1 r2 ->
      IS1.LLVM.D.lookup_defn r1 dfns1 = None ->
      IS2.LLVM.D.lookup_defn r2 dfns2 = None.
  Proof.
    intros dfns1 dfns2 r1 r2 ALL.
    revert r1. revert r2.
    induction ALL; intros r2 r1 REF LUP;
      cbn in *; auto.

    destruct x, y.
    cbn in *.

    inv H.
    cbn in *.

    break_match_hyp; inv LUP.
    eapply RelDec.neg_rel_dec_correct in Heqb.
    pose proof dvalue_refine_strict_R2_injective _ _ _ _ REF fst_rel.
    assert (d0 <> r2).
    { intros D0R2.
      apply H in D0R2; auto.
    }
    { assert (r2 <> d0) by auto.
      apply RelDec.neg_rel_dec_correct in H2.
      rewrite H2.
      eapply assoc_similar_no_lookup with (xs:=l) (RAC:=dvalue_refine_strict); eauto.
      apply dvalue_refine_strict_R2_injective.
    }
  Qed.

  Lemma denote_mcfg_E1E2_orutt' :
    forall dfns1 dfns2 dt f1 f2 args1 args2,
      (Forall2 (dvalue_refine_strict × function_denotation_refine_strict) dfns1 dfns2) ->
      (uvalue_refine_strict f1 f2) ->
      (Forall2 uvalue_refine_strict args1 args2) ->
      call_refine_strict IS1.LP.Events.DV.uvalue IS2.LP.Events.DV.uvalue (IS1.LP.Events.Call dt f1 args1) (Call dt f2 args2) ->
      orutt event_refine_strict event_res_refine_strict (fun res1 res2 => call_res_refine_strict IS1.LP.Events.DV.uvalue IS2.LP.Events.DV.uvalue (IS1.LP.Events.Call dt f1 args1) res1 (Call dt f2 args2) res2)
        (IS1.LLVM.D.denote_mcfg dfns1 dt f1 args1)
        (IS2.LLVM.D.denote_mcfg dfns2 dt f2 args2)
        (OOM:=OOME).
  Proof.
    intros dfns1 dfns2 dt f1 f2 args1 args2 DFNS F1F2 ARGS PRE12.
    unfold IS1.LLVM.D.denote_mcfg.
    unfold denote_mcfg.
    cbn in PRE12.
    destruct PRE12 as [DT [CONVf1f2 MAPM12]]; subst.

    eapply mrec_orutt with (RPreInv:=call_refine_strict).
    { intros A B d1 d2 PRE.

      cbn.
      destruct d1.
      destruct d2.

      cbn in PRE.

      eapply orutt_bind with (RR:=(fun r1 r2 => dvalue_refine_strict r1 r2)).
      { (* This may be tricky... *)
        (* Hopefully follows from uvalue_convert f = NoOom f0 in PRE *)
        unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick.
        destruct PRE as [T [UV ARGS_CONV]]; subst.

        break_match;
          eapply uvalue_refine_strict_preserves_is_concrete in Heqb;
          eauto; rewrite Heqb.
        - (* Concrete so just use uvalue_to_dvalue (simple) conversion *)
          apply rutt_orutt.
          apply lift_err_uvalue_to_dvalue_rutt_strict; auto.
          solve_dec_oom.
        - (* Not concrete, trigger pick events *)
          eapply orutt_bind with (RR:= fun (t1 : {_ : IS1.LP.Events.DV.dvalue | True}) (t2 : {_ : dvalue | True}) => dvalue_refine_strict (proj1_sig t1) (proj1_sig t2)) .
          { apply orutt_trigger.
            { constructor.
              cbn.
              tauto.
            }

            { intros t1 t2 H.
              inv H.
              cbn in *.
              apply inj_pair2 in H0, H3, H4, H5.
              subst.

              destruct t1 as [dv1 P1].
              destruct t2 as [dv2 P2].
              cbn in H6.
              cbn.
              tauto.
            }

            intros o CONTRA.
            inv CONTRA.
          }

          intros r1 r2 R1R2.
          apply orutt_Ret.
          destruct r1, r2.
          cbn in *.
          auto.
      }

      intros r1 r2 R1R2.
      (* Should be able to determine that the lookups
         are equivalent using DFNS *)
      cbn.
      break_match.
      { eapply lookup_defn_some_refine_strict in Heqo; eauto.
        destruct Heqo as (f_den2 & LUP2 & FDEN2).

        rewrite LUP2.
        red in FDEN2.
        specialize (FDEN2 args args0).
        forward FDEN2.
        { tauto.
        }

        destruct PRE as [T [CONV MAPM]]; subst.

        eapply orutt_weaken; eauto.
      }

      eapply lookup_defn_none_strict in Heqo; eauto.
      rewrite Heqo.

      eapply orutt_bind with (RR:=Forall2 dvalue_refine_strict).
      { (* Pick *)
        destruct PRE as [T [CONV MAPM]].
        induction MAPM.
        - cbn.
          apply orutt_Ret; auto.
        - do 2 rewrite map_monad_unfold.
          cbn.
          eapply orutt_bind with (RR:=dvalue_refine_strict).
          {
            apply rutt_orutt.
            apply pickUnique_rutt_strict; auto.
            solve_dec_oom.
          }

          intros r0 r3 R0R3.
          eapply orutt_bind with (RR:=Forall2 dvalue_refine_strict);
            eauto.

          intros r4 r5 R4R5.
          eapply orutt_Ret.
          constructor; eauto.
      }

      intros r3 r4 R3R4.
      cbn.

      destruct PRE as [T [UV ARGS_CONV]]; subst.

      unfold ITree.map.
      eapply orutt_bind with (RR:=dvalue_refine_strict).
      {
        apply orutt_trigger.
        { constructor.
          cbn.
          split; split; auto.
        }

        intros t1 t2 H.
        inv H.
        cbn in *.
        apply inj_pair2 in H0, H3, H4, H5.
        subst.

        cbn in H6.
        tauto.

        intros o CONTRA.
        inv CONTRA.
      }

      intros r0 r5 R0R5.
      apply orutt_Ret.

      split; split; auto.
      split; auto.

      eapply dvalue_refine_strict_dvalue_to_uvalue; auto.
    }

    cbn. auto.
  Qed.

  Lemma denote_mcfg_E1E2_orutt'_orutt :
    forall dfns1 dfns2 dt f1 f2 args1 args2,
      orutt event_refine_strict event_res_refine_strict (fun res1 res2 => call_res_refine_strict IS1.LP.Events.DV.uvalue IS2.LP.Events.DV.uvalue (IS1.LP.Events.Call dt f1 args1) res1 (Call dt f2 args2) res2)
        (IS1.LLVM.D.denote_mcfg dfns1 dt f1 args1)
        (IS2.LLVM.D.denote_mcfg dfns2 dt f2 args2)
        (OOM:=OOME) ->
      orutt event_refine_strict event_res_refine_strict uvalue_refine_strict
        (IS1.LLVM.D.denote_mcfg dfns1 dt f1 args1)
        (IS2.LLVM.D.denote_mcfg dfns2 dt f2 args2)
        (OOM:=OOME).
  Proof.
    intros dfns1 dfns2 dt f1 f2 args1 args2 H.
    eapply orutt_weaken; eauto.
    intros r1 r2 H0.
    cbn in H0.
    tauto.
  Qed.

  Lemma denote_mcfg_E1E2_orutt :
    forall dfns1 dfns2 dt f1 f2 args1 args2,
      (Forall2 (dvalue_refine_strict × function_denotation_refine_strict) dfns1 dfns2) ->
      (uvalue_refine_strict f1 f2) ->
      (Forall2 uvalue_refine_strict args1 args2) ->
      orutt event_refine_strict event_res_refine_strict uvalue_refine_strict
        (IS1.LLVM.D.denote_mcfg dfns1 dt f1 args1)
        (IS2.LLVM.D.denote_mcfg dfns2 dt f2 args2)
        (OOM:=OOME).
  Proof.
    intros dfns1 dfns2 dt f1 f2 args1 args2 H H0 H1.
    eapply denote_mcfg_E1E2_orutt'_orutt.
    eapply denote_mcfg_E1E2_orutt'; auto.
    cbn.
    split; auto.
  Qed.

  Lemma model_E1E2_L0_orutt_strict_sound
    (p : list
           (LLVMAst.toplevel_entity
              LLVMAst.typ
              (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ)))) :
    model_E1E2_L0_orutt_strict p p.
  Proof.
    red.

    unfold denote_vellvm.
    unfold LLVM1.denote_vellvm.
    eapply orutt_bind; [apply build_global_environment_E1E2_orutt_strict_sound|].

    intros [] [] _.
    eapply orutt_bind; [apply address_one_functions_E1E2_orutt|].

    intros r1 r2 R1R2.
    eapply orutt_bind;
      [apply rutt_orutt;
       [apply GlobalRead_L0_E1E2_rutt | solve_dec_oom]|].

    intros r3 r4 R3R4.
    eapply orutt_bind.

    { apply denote_mcfg_E1E2_orutt; auto.
      - apply dvalue_refine_strict_dvalue_to_uvalue; auto.
      - (* TODO: fold into main_args lemma probably *)
        unfold main_args.
        unfold LLVM1.main_args.
        constructor.
        + unfold_uvalue_refine_strict_goal.
          reflexivity.
        + constructor; [|constructor].
          unfold_uvalue_refine_strict_goal.
          cbn.
          rewrite AC1.addr_convert_null.
          reflexivity.
    }

    intros r0 r5 H.
    eapply orutt_bind with (RR:=fun x y => dvalue_refine_strict (proj1_sig x) (proj1_sig y)).
    { (* Pick *)
      apply orutt_trigger.
      { cbn.
        split; auto.
        (* TODO: this lemma may not even be true *)
        apply uvalue_refine_strict_concretize_poison; auto.
      }

      intros t1 t2 H0.
      cbn in *.
      destruct t1, t2; tauto.
      intros o CONTRA; inv CONTRA.
    }

    intros r6 r7 H0.
    cbn.
    apply orutt_Ret; auto.
  Qed.

  Lemma E1E2_interp_global_orutt_strict :
    forall t1 t2 g1 g2,
      L0_E1E2_orutt_strict t1 t2 ->
      global_refine_strict g1 g2 ->
      L1_E1E2_orutt_strict (interp_global t1 g1) (interp_global t2 g2).
  Proof.
    intros t1 t2 g1 g2 RL0 GENVS.
    unfold interp_global.
    unfold State.interp_state.
    red.
    red in RL0.

    Set Nested Proofs Allowed.
    Lemma orutt_interp :
      forall {E1 E2 F1 F2 OOM1 OOME1 OOM2 OOME2 R1 R2 pre1 post1 pre2 post2 RR}
        (h1 : forall T, E1 T -> itree F1 T)
        (h2 : forall T, E2 T -> itree F2 T)
        t1 t2,
        @orutt E1 E2 OOM1 OOME1 R1 R2 pre1 post1 RR t1 t2 ->
        (forall A B e1 e2,
            pre1 A B e1 e2 ->
            @orutt F1 F2 OOM2 OOME2 A B pre2 post2 (fun a b => post1 A B e1 a e2 b) (h1 A e1) (h2 B e2)) ->
        (* OOM Spec... Probably too strong right now, but easier to rewrite this way. *)
        (forall A (o : OOM1 A), exists (o' : OOM2 A) k, h2 A (subevent A o) = (vis o' k)) ->
        @orutt F1 F2 OOM2 OOME2 R1 R2 pre2 post2 RR (interp h1 t1) (interp h2 t2).
    Proof.
      intros E1 E2 F1 F2 OOM1 OOME1 OOM2 OOME2 R1 R2 pre1 post1 pre2 post2 RR h1 h2 t1 t2 EQ HANDLER OOMSPEC.
      revert EQ. revert t1 t2.
      ginit. gcofix CIH.
      intros t1 t2 EQ.
      punfold EQ; red in EQ.
      dependent induction EQ; subst; setoid_rewrite unfold_interp.
      - rewrite <- x, <- x0.
        cbn; gstep; red; cbn.
        constructor; auto.
      - rewrite <- x, <- x0.
        cbn; gstep; red; cbn.
        constructor; auto.
        gbase; pclearbot.
        eapply CIH; eauto.
      - rename H0 into KEQ.
        (* KEQ may be what I need to relate the continuations after the handler *)
        (* I may need to know something about how pre1 / pre2 and post1 / post2 relate to each other *)
        pose proof H as HSPEC.
        apply HANDLER in HSPEC.
        punfold HSPEC; red in HSPEC.
        revert HSPEC.
        gcofix CIH2.
        intros HSPEC.
        dependent induction HSPEC.
        + cbn in *.
          rewrite <- x0, <- x1.
          cbn. do 2 rewrite unfold_bind.
          rewrite <- x, <- x2.
          gstep; red; cbn.
          constructor.
          gbase.
          eapply CIH; eauto.
          specialize (KEQ _ _ H0).
          pclearbot.
          eauto.
        + cbn in *.
          rewrite <- x0, <- x1.
          cbn. do 2 rewrite unfold_bind.
          rewrite <- x, <- x2.
          gstep; red; cbn.
          constructor.
          pclearbot.
          eapply gpaco2_uclo; [|eapply orutt_clo_bind|]; eauto with paco.
          econstructor; eauto. intros ? ? ?.
          * gstep.
            red; cbn.
            constructor.
            gbase.
            eapply CIH; eauto.
            cbn in *.
            apply KEQ in H2.
            pclearbot.
            eauto.
        + cbn in *.
          rewrite <- x0, <- x1.
          cbn. do 2 rewrite unfold_bind.
          rewrite <- x, <- x2.
          gstep; red; cbn.
          constructor; eauto.
          intros a b H8.
          eapply gpaco2_uclo; [|eapply orutt_clo_bind|]; eauto with paco.
          econstructor; eauto.

          apply H0 in H8.
          pclearbot.
          eauto.

          intros u1 u2 H9.
          cbn in *.
          gstep; red; cbn.
          constructor; eauto.
          gbase.
          eapply CIH; eauto.
          apply KEQ in H9.
          pclearbot; eauto.
        + (* OOM *)
          cbn in *.
          rewrite <- x0, <- x1.
          cbn. do 2 rewrite unfold_bind.
          rewrite <- x.
          gstep; red; cbn.
          constructor.
        + (* TauL *)
          cbn in *.
          rewrite <- x0, <- x1.
          eapply gpaco2_uclo; [|eapply orutt_clo_bind|]; eauto with paco.
          econstructor; eauto. intros ? ? ?.
          * gstep.
            red; cbn.
            constructor.
            gbase.
            eapply CIH; eauto.
            cbn in *.
            apply KEQ in H0.
            pclearbot.
            eauto.
        + (* TauR *)
          cbn in *.
          rewrite <- x0, <- x1.
          eapply gpaco2_uclo; [|eapply orutt_clo_bind|]; eauto with paco.
          econstructor; eauto. intros ? ? ?.
          * gstep.
            red; cbn.
            constructor.
            gbase.
            eapply CIH; eauto.
            cbn in *.
            apply KEQ in H0.
            pclearbot.
            eauto.
      - (* OOM *)
        specialize (OOMSPEC _ e).
        destruct OOMSPEC as [o' [k OOMEQ]].
        rewrite <- x.
        cbn.
        rewrite OOMEQ.
        rewrite bind_vis.
        gstep; red; cbn.
        constructor.
      - (* TauL *)
        cbn in *.
        rewrite <- x.
        cbn.
        rewrite tau_euttge.
        rewrite <- unfold_interp.
        eapply IHEQ; eauto.
      - (* TauR *)
        cbn in *.
        rewrite <- x.
        cbn.
        rewrite tau_euttge.
        rewrite <- unfold_interp.
        eapply IHEQ; eauto.
    Qed.

    Set Nested Proofs Allowed.
    Lemma orutt_interp_state :
      forall {E1 E2 F1 F2 OOM1 OOME1 OOM2 OOME2 R1 R2 RR S1 S2}
        {SS : S1 -> S2 -> Prop}
        {pre1 : prerel E1 E2} {post1 : postrel E1 E2} {pre2 : prerel F1 F2} {post2 : postrel F1 F2}
        (h1 : forall T, E1 T -> Monads.stateT S1 (itree F1) T)
        (h2 : forall T, E2 T -> Monads.stateT S2 (itree F2) T)
        t1 t2 s1 s2,
        @orutt E1 E2 OOM1 OOME1 R1 R2 pre1 post1 RR t1 t2 ->
        SS s1 s2 ->
        (forall A B e1 e2 s1 s2,
            pre1 A B e1 e2 ->
            SS s1 s2 ->
            @orutt F1 F2 OOM2 OOME2 (S1 * A)%type (S2 * B)%type pre2 post2 (fun '(s1, a) '(s2, b) => post1 A B e1 a e2 b /\ SS s1 s2) (h1 A e1 s1) (h2 B e2 s2)) ->
        (* OOM Spec... *)
        (forall A (o : OOM1 A) s, exists (o' : OOM2 A) k, h2 A (subevent A o) s ≈ (vis o' k)) ->
        @orutt F1 F2 OOM2 OOME2 (S1 * R1)%type (S2 * R2)%type pre2 post2 (SS × RR) (State.interp_state h1 t1 s1) (State.interp_state h2 t2 s2).
    Proof.
      intros E1 E2 F1 F2 OOM1 OOME1 OOM2 OOME2 R1 R2 RR S1 S2 SS pre1 post1 pre2 post2 h1 h2 t1 t2 s1 s2 EQ SSINIT HANDLER OOMSPEC.
      revert EQ SSINIT. revert t1 t2 s1 s2.
      ginit. gcofix CIH.
      intros t1 t2 s1 s2 EQ SSINIT.
      punfold EQ; red in EQ.
      dependent induction EQ; subst; setoid_rewrite StateFacts.unfold_interp_state.
      - rewrite <- x, <- x0.
        cbn; gstep; red; cbn.
        constructor; constructor; cbn; auto.
      - rewrite <- x, <- x0.
        cbn; gstep; red; cbn.
        constructor; auto.
        gbase; pclearbot.
        eapply CIH; eauto.
      - rename H0 into KEQ.
        (* KEQ may be what I need to relate the continuations after the handler *)
        (* I may need to know something about how pre1 / pre2 and post1 / post2 relate to each other *)
        pose proof H as HSPEC.
        eapply HANDLER in HSPEC; eauto.
        punfold HSPEC; red in HSPEC.
        revert HSPEC.
        gcofix CIH2.
        intros HSPEC.
        dependent induction HSPEC.
        + cbn in *.
          rewrite <- x0, <- x1.
          cbn. do 2 rewrite unfold_bind.
          rewrite <- x, <- x2.
          gstep; red; cbn.
          constructor.
          gbase.
          destruct r1, r2.
          destruct H0.
          eapply CIH; eauto.
          specialize (KEQ _ _ H0).
          pclearbot.
          eauto.
        + cbn in *.
          rewrite <- x0, <- x1.
          cbn. do 2 rewrite unfold_bind.
          rewrite <- x, <- x2.
          gstep; red; cbn.
          constructor.
          pclearbot.
          eapply gpaco2_uclo; [|eapply orutt_clo_bind|]; eauto with paco.
          econstructor; eauto. intros ? ? ?.
          * gstep.
            red; cbn.
            constructor.
            gbase.
            destruct u1, u2, H2.
            eapply CIH; eauto.
            cbn in *.
            apply KEQ in H2.
            pclearbot.
            eauto.
        + cbn in *.
          rewrite <- x0, <- x1.
          cbn. do 2 rewrite unfold_bind.
          rewrite <- x, <- x2.
          gstep; red; cbn.
          constructor; eauto.
          intros a b H8.
          eapply gpaco2_uclo; [|eapply orutt_clo_bind|]; eauto with paco.
          econstructor; eauto.

          apply H0 in H8.
          pclearbot.
          eauto.

          intros u1 u2 H9.
          cbn in *.
          gstep; red; cbn.
          constructor; eauto.
          gbase.
          destruct u1, u2, H9.
          eapply CIH; eauto.
          eapply KEQ in H4; eauto.
          pclearbot; eauto.
        + (* OOM *)
          cbn in *.
          rewrite <- x0, <- x1.
          cbn. do 2 rewrite unfold_bind.
          rewrite <- x.
          gstep; red; cbn.
          constructor.
        + (* TauL *)
          cbn in *.
          rewrite <- x0, <- x1.
          eapply gpaco2_uclo; [|eapply orutt_clo_bind|]; eauto with paco.
          econstructor; eauto. intros ? ? ?.
          * gstep.
            red; cbn.
            constructor.
            gbase.
            destruct u1, u2, H0; cbn in *.
            eapply CIH; eauto.
            cbn in *.
            apply KEQ in H0.
            pclearbot.
            eauto.
        + (* TauR *)
          cbn in *.
          rewrite <- x0, <- x1.
          eapply gpaco2_uclo; [|eapply orutt_clo_bind|]; eauto with paco.
          econstructor; eauto. intros ? ? ?.
          * gstep.
            red; cbn.
            constructor.
            gbase.
            destruct u1, u2, H0.
            eapply CIH; eauto.
            cbn in *.
            apply KEQ in H0.
            pclearbot.
            eauto.
      - (* OOM *)
        specialize (OOMSPEC _ e s2).
        destruct OOMSPEC as [o' [k OOMEQ]].
        rewrite <- x.
        cbn.
        (* TODO: figure out how to do this rewrite *)
        (* setoid_rewrite OOMEQ. *)
        (* rewrite bind_vis. *)
        (* gstep; red; cbn. *)
        (* constructor. *)
        admit.
      - (* TauL *)
        cbn in *.
        rewrite <- x.
        cbn.
        rewrite tau_euttge.
        rewrite <- StateFacts.unfold_interp_state.
        eapply IHEQ; eauto.
      - (* TauR *)
        cbn in *.
        rewrite <- x.
        cbn.
        rewrite tau_euttge.
        rewrite <- StateFacts.unfold_interp_state.
        eapply IHEQ; eauto.
    Admitted.

    Lemma orutt_interp_global_h :
      forall A B e1 e2 genv1 genv2,
        event_refine_strict A B e1 e2 ->
        global_refine_strict genv1 genv2 ->
        orutt L1_refine_strict L1_res_refine_strict
          (fun '(s0, a) '(s3, b) => event_res_refine_strict A B e1 a e2 b /\ global_refine_strict s0 s3)
          (interp_global_h e1 genv1) (interp_global_h e2 genv2)
          (OOM:=OOME).
    Proof.
    intros A B e1 e2 genv1 genv2 REF GREF.
    destruct e1; repeat (destruct e); repeat (destruct s);
    try
      solve
        [
          cbn in REF;
          destruct e2; try inv REF;
          repeat (break_match_hyp; try inv REF);
          cbn in *;
          pstep; red; cbn;
          constructor; cbn; auto;
          [ intros ? ? ?;
              left;
            pstep; red; cbn;
            constructor; auto
          | intros o CONTRA; inv CONTRA
          ]
        ].

    all: try
           solve
           [ cbn in REF;
             destruct e2; try inv REF;
             repeat (break_match_hyp; try inv REF);
             cbn in *;
             (pstep; red; cbn;
              constructor; cbn; try tauto;
              [ intros ? ? ?; left; apply orutt_Ret; tauto
              | intros o CONTRA; inv CONTRA
             ])
           |
             cbn in REF;
             destruct e2; try inv REF;
             repeat (break_match_hyp; try inv REF);
             cbn in *;
             (pstep; red; cbn;
              constructor; cbn;
              [ first [red; red; auto | tauto]
              | intros ? ? ?; left; apply orutt_Ret; tauto
              | intros o CONTRA; inv CONTRA
             ])
           ].

    -
      cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF).
      + cbn in *.
        apply orutt_Ret.
        split; auto.
        apply global_refine_strict_add; auto.

      + cbn.
        pose proof GREF as GREF'.
        do 2 red in GREF.
        specialize (GREF id0).
        red in GREF.
        break_match_goal.
        { (* Found id in genv *)
          break_match_goal; try contradiction.
          apply orutt_Ret.
          split; eauto.
        }

        { (* Id not found in genv *)
          break_match_goal; try contradiction.
          solve_orutt_raise.
        }
    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF).

      { cbn.
        apply orutt_bind with (RR:=eq).
        apply orutt_trigger; cbn; eauto.
        intros [] [] _; auto.
        intros o CONTRA; inv CONTRA.
        intros [] [] _.
        apply orutt_Ret; tauto.
      }

      { cbn.
        apply orutt_bind with (RR:=uvalue_refine_strict).
        apply orutt_trigger; cbn; eauto.
        intros x y [_ REFxy]; auto.
        intros o CONTRA; inv CONTRA.
        intros r1 r2 REFr1r2.
        apply orutt_Ret; tauto.
      }
    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF).

       { cbn.
         apply orutt_bind with (RR:=eq).
         { apply orutt_trigger; cbn; eauto.
           intros [] [] _; auto.
           intros o CONTRA; inv CONTRA.
         }
         intros [] [] _.
         apply orutt_Ret; split; auto.
      }

       { cbn.
         apply orutt_bind with (RR:=eq).
         { apply orutt_trigger; cbn; eauto.
           intros [] [] _; auto.
           intros o CONTRA; inv CONTRA.
         }
         intros [] [] _.
         apply orutt_Ret; split; auto.
      }
    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF);

        try (cbn;
         try apply orutt_bind with (RR:=eq);
         [ apply orutt_trigger; cbn; eauto;
           [ intros [] [] _; auto
           | intros o CONTRA; inv CONTRA
           ]
         |
         ];
         intros [] [] _;
             apply orutt_Ret; split; auto).

      { cbn.
        apply orutt_bind with (RR:=dvalue_refine_strict).
        apply orutt_trigger; cbn; eauto.
        intros t1 t2 H; tauto.
        intros o CONTRA; inv CONTRA.
        intros r1 r2 H.
        apply orutt_Ret; tauto.
      }
      { cbn.
        apply orutt_bind with (RR:=uvalue_refine_strict).
        apply orutt_trigger; cbn; eauto.
        intros t1 t2 H; tauto.
        intros o CONTRA; inv CONTRA.
        intros r1 r2 H.
        apply orutt_Ret; tauto.
      }
    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF).

      cbn.
      do 2 rewrite bind_trigger.
      change (inr1 (inr1 (inr1 (inl1 o0)))) with
        (@subevent _ _ (ReSum_inr IFun sum1 OOME
                          (IS2.LP.Events.MemoryE +' IS2.LP.Events.PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                          (IS2.LP.Events.LLVMEnvE +' IS2.LP.Events.LLVMStackE)

           ) B o0).
      pstep; red; cbn.
      rewrite subevent_subevent.
      eapply EqVisOOM.
    Qed.

    eapply orutt_interp_state; eauto.
    { intros A B e1 e2 s1 s2 H H0.
      apply orutt_interp_global_h; auto.
    }
    { intros A o s.
      cbn.
      setoid_rewrite bind_trigger.
      exists (resum IFun A o).
      exists (fun x : A => SemNotations.Ret1 s x).
      reflexivity.
    }
  Qed.

  Lemma orutt_interp_intrinsics_h :
    forall A B e1 e2,
      event_refine_strict A B e1 e2 ->
      orutt event_refine_strict event_res_refine_strict
        (fun (a : A) (b : B) => event_res_refine_strict A B e1 a e2 b)
        (IS1.LLVM.Intrinsics.interp_intrinsics_h e1) (interp_intrinsics_h e2)
        (OOM:=OOME).
  Proof.
    intros A B e1 e2 REF.
    destruct e1; repeat (destruct e); repeat (destruct s).
    try
      solve
        [
          cbn in REF;
          destruct e2; try inv REF;
          repeat (break_match_hyp; try inv REF);
          cbn in *;
          pstep; red; cbn;
          constructor; cbn; auto;
          [ intros ? ? ?;
              left;
            pstep; red; cbn;
            constructor; auto
          | intros o CONTRA; inv CONTRA
          ]
        ].

    all: try
           solve
           [ cbn in REF;
             destruct e2; try inv REF;
             repeat (break_match_hyp; try inv REF);
             cbn in *;
             (pstep; red; cbn;
              constructor; cbn; try tauto;
              [ intros ? ? ?; left; apply orutt_Ret; tauto
              | intros o CONTRA; inv CONTRA
             ])
           |
             cbn in REF;
             destruct e2; try inv REF;
             repeat (break_match_hyp; try inv REF);
             cbn in *;
             (pstep; red; cbn;
              constructor; cbn;
              [ first [red; red; auto | tauto]
              | intros ? ? ?; left; apply orutt_Ret; tauto
              | intros o CONTRA; inv CONTRA
             ])
           ].

    -
      cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF);
        cbn in *.
      destruct H0 as [FEQ REFARGS]; subst.
      repeat break_inner_match_goal;
        try solve_orutt_raise.

      Lemma llvm_fabs_f32_agrees_fail :
        forall args1 args2 s,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_fabs_f32 args1 = inl s ->
          IS2.LLVM.Intrinsics.llvm_fabs_f32 args2 = inl s.
      Proof.
      Admitted.

      Lemma llvm_fabs_f32_agrees_success :
        forall args1 args2 d1,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_fabs_f32 args1 = inr d1 ->
          exists d2,
            IS2.LLVM.Intrinsics.llvm_fabs_f32 args2 = inr d2 /\
              dvalue_refine_strict d1 d2.
      Proof.
      Admitted.

      Lemma llvm_fabs_f64_agrees_fail :
        forall args1 args2 s,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_fabs_f64 args1 = inl s ->
          IS2.LLVM.Intrinsics.llvm_fabs_f64 args2 = inl s.
      Proof.
      Admitted.

      Lemma llvm_fabs_f64_agrees_success :
        forall args1 args2 d1,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_fabs_f64 args1 = inr d1 ->
          exists d2,
            IS2.LLVM.Intrinsics.llvm_fabs_f64 args2 = inr d2 /\
              dvalue_refine_strict d1 d2.
      Proof.
      Admitted.

      Lemma llvm_maxnum_f32_agrees_fail :
        forall args1 args2 s,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_maxnum_f32 args1 = inl s ->
          IS2.LLVM.Intrinsics.llvm_maxnum_f32 args2 = inl s.
      Proof.
      Admitted.

      Lemma llvm_maxnum_f32_agrees_success :
        forall args1 args2 d1,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_maxnum_f32 args1 = inr d1 ->
          exists d2,
            IS2.LLVM.Intrinsics.llvm_maxnum_f32 args2 = inr d2 /\
              dvalue_refine_strict d1 d2.
      Proof.
      Admitted.

      Lemma llvm_maxnum_f64_agrees_fail :
        forall args1 args2 s,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_maxnum_f64 args1 = inl s ->
          IS2.LLVM.Intrinsics.llvm_maxnum_f64 args2 = inl s.
      Proof.
      Admitted.

      Lemma llvm_maxnum_f64_agrees_success :
        forall args1 args2 d1,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_maxnum_f64 args1 = inr d1 ->
          exists d2,
            IS2.LLVM.Intrinsics.llvm_maxnum_f64 args2 = inr d2 /\
              dvalue_refine_strict d1 d2.
      Proof.
      Admitted.

      Lemma llvm_minimum_f32_agrees_fail :
        forall args1 args2 s,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_minimum_f32 args1 = inl s ->
          IS2.LLVM.Intrinsics.llvm_minimum_f32 args2 = inl s.
      Proof.
      Admitted.

      Lemma llvm_minimum_f32_agrees_success :
        forall args1 args2 d1,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_minimum_f32 args1 = inr d1 ->
          exists d2,
            IS2.LLVM.Intrinsics.llvm_minimum_f32 args2 = inr d2 /\
              dvalue_refine_strict d1 d2.
      Proof.
      Admitted.

      Lemma llvm_minimum_f64_agrees_fail :
        forall args1 args2 s,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_minimum_f64 args1 = inl s ->
          IS2.LLVM.Intrinsics.llvm_minimum_f64 args2 = inl s.
      Proof.
      Admitted.

      Lemma llvm_minimum_f64_agrees_success :
        forall args1 args2 d1,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_minimum_f64 args1 = inr d1 ->
          exists d2,
            IS2.LLVM.Intrinsics.llvm_minimum_f64 args2 = inr d2 /\
              dvalue_refine_strict d1 d2.
      Proof.
      Admitted.



      all:
        try solve
          [ pose proof (llvm_fabs_f32_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_fabs_f64_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_maxnum_f32_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_maxnum_f64_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_minimum_f32_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_minimum_f64_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          ].

      all:
        try solve
          [ pose proof (llvm_fabs_f32_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_fabs_f64_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_maxnum_f32_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_maxnum_f64_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_minimum_f32_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_minimum_f64_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          ].

      cbn.
      pstep; red; cbn.
      constructor; cbn; try tauto.

      intros a b H.
      left; apply orutt_Ret.
      tauto.

      intros o CONTRA; inv CONTRA.
    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF);
        cbn in *.
      pstep; red; cbn.
      change (inr1 (inr1 (inr1 (inr1 (inl1 o0))))) with
        (@subevent _ _ (ReSum_inr IFun sum1 OOME
                          ((LLVMEnvE +' LLVMStackE) +' MemoryE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                          LLVMGEnvE

           ) B o0).
      rewrite subevent_subevent.
      eapply EqVisOOM.
  Qed.

  Lemma E1E2_interp_intrinsics_orutt_strict :
    forall t1 t2,
      L0_E1E2_orutt_strict t1 t2 ->
      L0_E1E2_orutt_strict (IS1.LLVM.Intrinsics.interp_intrinsics t1) (IS2.LLVM.Intrinsics.interp_intrinsics t2).
  Proof.
    intros t1 t2 RL0.
    red. red in RL0.

    unfold IS1.LLVM.Intrinsics.interp_intrinsics.
    unfold interp_intrinsics.
    cbn.

    eapply orutt_interp; eauto.
    { intros A B e1 e2 H.
      apply orutt_interp_intrinsics_h; auto.
    }
    { intros A o.
      exists (resum IFun A o).
      exists ret.
      reflexivity.
    }
  Qed.

  Lemma model_E1E2_01_orutt_strict :
    forall t1 t2 g1 g2,
      L0_E1E2_orutt_strict t1 t2 ->
      global_refine_strict g1 g2 ->
      L1_E1E2_orutt_strict (interp_global (IS1.LLVM.Intrinsics.interp_intrinsics t1) g1) (interp_global (IS2.LLVM.Intrinsics.interp_intrinsics t2) g2).
  Proof.
    intros t1 t2 g1 g2 RL0 GENVS.
    red in RL0.
    apply E1E2_interp_global_orutt_strict; auto.
    apply E1E2_interp_intrinsics_orutt_strict; auto.
  Qed.

  Lemma orutt_interp_local_stack_h :
    forall A B e1 e2 ls1 ls2,
      L1_refine_strict A B e1 e2 ->
      local_stack_refine_strict ls1 ls2 ->
      orutt L2_refine_strict L2_res_refine_strict
        (fun '(s0, a) '(s3, b) =>
           L1_res_refine_strict A B e1 a e2 b /\ (local_refine_strict × stack_refine_strict) s0 s3)
        (interp_local_stack_h (handle_local (v:=IS1.LP.Events.DV.uvalue)) e1 ls1)
        (interp_local_stack_h (handle_local (v:=uvalue)) e2 ls2)
        (OOM:=OOME).
  Proof.
    intros A B e1 e2 ls1 ls2 REF LSR.
    destruct e1; repeat (destruct e); repeat (destruct s);
    try
      solve
        [ cbn in REF;
          destruct e2; try inv REF;
          repeat (break_match_hyp; try inv REF);
          cbn in *;
          repeat rewrite bind_trigger;
          pstep; red; cbn;
          constructor;
          [ cbn; tauto
          | intros a b H;
            left; apply orutt_Ret;
            split; try tauto;
            destruct ls1, ls2; constructor; cbn in *; tauto
          | intros o CONTRA; inv CONTRA
          ]
        ].

    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF).
      + cbn in *.
        destruct ls1, ls2.
        cbn.
        repeat rewrite map_ret.
        apply orutt_Ret;
          split; try tauto.
        constructor; cbn in *; try tauto.
        apply local_stack_refine_strict_add; tauto.
      + cbn in *.
        destruct ls1, ls2.
        cbn.
        repeat rewrite map_ret.
        destruct LSR.
        pose proof H as FIND.
        do 2 red in FIND.
        specialize (FIND id0).
        red in FIND.
        break_match_hyp; break_match_hyp; inv FIND.
        repeat rewrite map_ret.
        apply orutt_Ret; split; try tauto.
        constructor; cbn in *; try tauto.

        apply orutt_bind with (RR:=local_refine_strict × uvalue_refine_strict).
        solve_orutt_raise.
        intros [l1 r1] [l2 r2] [L R]; cbn in *.
        apply orutt_Ret.
        split; try tauto.
        constructor; tauto.

    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF).
      + red in REF.
        cbn in *.
        destruct ls1, ls2.
        cbn.
        apply orutt_Ret;
          split; try tauto.
        constructor; cbn in *; try tauto.
        { (* TODO: Move this *)
          (* Lemma alist_refine_strict_fold_right_add : *)
          (*   forall {K V1 V2} *)
          (*     `{RD_K : @RelDec.RelDec K (@eq K)} *)
          (*     `{RD_K_CORRECT : @RelDec.RelDec_Correct _ eq RD_K} *)
          (*     (R: V1 -> V2 -> Prop) xs ys vs1 vs2, *)
          (*     alist_refine R (vs1 ++ xs) (vs2 ++ ys) -> *)
          (*     alist_refine R (fold_right (fun '(id, v) => FMapAList.alist_add id v) xs vs1) (fold_right (fun '(id, v) => FMapAList.alist_add id v) ys vs2). *)
          (* Proof. *)
          (*   unfold FMapAList.alist_add. *)
          (*   unfold  *)
          (*   hinduction vs1 before vs2; intros vs2 REF. *)
          (*   - destruct vs2. *)
          (*     cbn; auto. *)

          (*     { destruct REF, p. *)
          (*       specialize (H k). *)
          (*       destruct H. *)
          (*       forward H1. *)
          (*       eexists; cbn. *)
          (*       rewrite RelDec.rel_dec_eq_true; auto. *)

          (*       destruct H1. *)
          (*       cbn in H1. *)
          (*       inv H1. *)
          (*     } *)
          (*   - induction vs2. *)
          (*     { destruct REF, a. *)
          (*       specialize (H k). *)
          (*       destruct H. *)
          (*       forward H. *)
          (*       eexists; cbn. *)
          (*       rewrite RelDec.rel_dec_eq_true; auto. *)

          (*       destruct H. *)
          (*       cbn in H. *)
          (*       inv H. *)
          (*     } *)

          (*     { cbn. *)
          (*       destruct REF. *)
          (*       cbn in *. *)
          (*       destruct a, a0. *)
          (*       (* TODO: Ugh, equivalent alists may not be in the same *)
          (*       order *) *)
          (*       eapply alist_refine_add with (x:=(k,v)) (y:=(k0,v0)); cbn; auto. *)
          (*       all: admit. *)
          (*     } *)
          (* Admitted. *)

          (* Lemma alist_refine_remove_cons : *)
          (*   forall {K V1 V2} *)
          (*     `{RD_K : @RelDec.RelDec K (@eq K)} *)
          (*     `{RD_K_CORRECT : @RelDec.RelDec_Correct _ eq RD_K} *)
          (*     (R: V1 -> V2 -> Prop) k1 v1 vs1 k2 v2 vs2, *)
          (*     alist_refine R ((k1,v1) :: vs1) ((k2,v2) :: vs2) -> *)
          (*     alist_refine R ((k1,v1) :: FMapAList.alist_remove k1 vs1) ((k2,v2) :: vs2) *)
          (*   alist_refine R *)
          (*     ((k, v) :: FMapAList.alist_remove k (fold_right (fun '(id, v1) (m : FMapAList.alist K V1) => (id, v1) :: FMapAList.alist_remove id m) [] vs1)) *)
          (*     ((k0, v0) :: FMapAList.alist_remove k0 (fold_right (fun '(id, v1) (m : FMapAList.alist K V2) => (id, v1) :: FMapAList.alist_remove id m) [] vs2)) *)

          (* TODO: look at frame stack equivalence *)
          Lemma alist_refine_strict_fold_right_add :
            forall {K V1 V2}
              `{RD_K : @RelDec.RelDec K (@eq K)}
              `{RD_K_CORRECT : @RelDec.RelDec_Correct _ eq RD_K}
              (R: V1 -> V2 -> Prop) vs1 vs2,
              alist_refine R vs1 vs2 ->
              alist_refine R (fold_right (fun '(id, v) => FMapAList.alist_add id v) [] vs1) (fold_right (fun '(id, v) => FMapAList.alist_add id v) [] vs2).
          Proof.
            intros K V1 V2 RD_K RD_K_CORRECT R vs1 vs2 REF.
            unfold FMapAList.alist_add.
            hinduction vs1 before vs2; intros vs2 REF.
            (* TODO: Ugh, equivalent alists may not be in the same
               order *)
          Admitted.

          apply alist_refine_strict_fold_right_add; auto.
        }

        apply stack_refine_strict_add; tauto.
      + cbn in *.
        destruct ls1, ls2.
        cbn.
        repeat rewrite map_ret.

        destruct LSR.
        destruct s; inv H0.
        -- solve_orutt_raise.
        -- apply orutt_Ret. split; auto.
    - (* Memory Events *)
      cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF);
        try solve [cbn;
         repeat rewrite bind_trigger;
         red; pstep; red; cbn;
         constructor; cbn; auto;
         [ intros ?a ?b ?H;
           left;
           pstep; red; cbn;
           constructor; cbn; auto;
           split; auto;
           destruct ls1, ls2; cbn in *;
           constructor; tauto
         | intros o CONTRA; inv CONTRA
          ]].
    - (* Pick events *)
      cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF);
        try solve [cbn;
         repeat rewrite bind_trigger;
         red; pstep; red; cbn;
         constructor; cbn; auto;
         [ intros ?a ?b ?H;
           left;
           pstep; red; cbn;
           constructor; cbn; auto;
           split; auto;
           destruct ls1, ls2; cbn in *;
           constructor; tauto
         | intros o CONTRA; inv CONTRA
          ]].
    - (* OOM Events *)
      cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF).

      cbn.
      repeat rewrite bind_trigger.
      change (inr1 (inr1 (inl1 o0))) with
        (@subevent _ _ (ReSum_inr IFun sum1 OOME
                          (PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                          MemoryE
           ) B o0).
      pstep; red; cbn.
      rewrite subevent_subevent.
      eapply EqVisOOM.
    - cbn in REF; 
       destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF).
      cbn.
      repeat rewrite bind_trigger.
      pfold. red.
      cbn.
      constructor; cbn; auto.
      intros [] [] _.
      left.
      pstep; red; cbn.
      constructor.
      split; auto.
      red in LSR.
      destruct ls1, ls2.
      constructor; tauto.
      intros o CONTRA.
      inv CONTRA.
    - cbn in REF; 
       destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF).
      cbn.
      repeat rewrite bind_trigger.
      pfold. red.
      cbn.
      constructor; cbn; auto.
      intros [].
      intros o CONTRA.
      inv CONTRA.
  Qed.

  Lemma model_E1E2_12_orutt_strict :
    forall t1 t2 ls1 ls2,
      L1_E1E2_orutt_strict t1 t2 ->
      local_stack_refine_strict ls1 ls2 ->
      L2_E1E2_orutt_strict (interp_local_stack t1 ls1) (interp_local_stack t2 ls2).
  Proof.
    intros t1 t2 ls1 ls2 RL1 LSR.
    red in RL1.

    unfold interp_local_stack.
    eapply orutt_interp_state; eauto.
    { unfold local_stack_refine_strict in *.
      destruct ls1, ls2;
      constructor; tauto.
    }

    intros A B e1 e2 s1 s2 H H0.
    eapply orutt_interp_local_stack_h; eauto.
    inv H0.
    destruct s1, s2; cbn in *; auto.

    intros A o s.
    exists o.
    cbn.
    setoid_rewrite bind_trigger.
    exists (fun x : A => SemNotations.Ret1 s x).
    reflexivity.
  Qed.

  Lemma model_E1E2_L1_orutt_strict_sound
    (p : list
           (LLVMAst.toplevel_entity
              LLVMAst.typ
              (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ)))) :
    model_E1E2_L1_orutt_strict p p.
  Proof.
    apply model_E1E2_01_orutt_strict;
      [ apply model_E1E2_L0_orutt_strict_sound
      | apply global_refine_strict_empty
      ].
  Qed.

  Lemma model_E1E2_L2_orutt_strict_sound
    (p : list
           (LLVMAst.toplevel_entity
              LLVMAst.typ
              (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ)))) :
    model_E1E2_L2_orutt_strict p p.
  Proof.
    apply model_E1E2_12_orutt_strict;
      [ apply model_E1E2_L1_orutt_strict_sound
      | apply local_stack_refine_strict_empty
      ].
  Qed.

End LangRefine.

Module MakeLangRefine
  (IS1 : InterpreterStack) (IS2 : InterpreterStack) (AC1 : AddrConvert IS1.LP.ADDR IS2.LP.ADDR) (AC2 : AddrConvert IS2.LP.ADDR IS1.LP.ADDR) (LLVM1 : LLVMTopLevel IS1) (LLVM2 : LLVMTopLevel IS2) (TLR : TopLevelRefinements IS2 LLVM2) (IPS : IPConvertSafe IS2.LP.IP IS1.LP.IP) (DVC : DVConvert IS1.LP IS2.LP AC1 IS1.LP.Events IS2.LP.Events) (DVCrev : DVConvert IS2.LP IS1.LP AC2 IS2.LP.Events IS1.LP.Events) (EC : EventConvert IS1.LP IS2.LP AC1 AC2 IS1.LP.Events IS2.LP.Events DVC DVCrev) (TC : TreeConvert IS1 IS2 AC1 AC2 DVC DVCrev EC) : LangRefine IS1 IS2 AC1 AC2 LLVM1 LLVM2 TLR IPS DVC DVCrev EC TC.
  Include LangRefine IS1 IS2 AC1 AC2 LLVM1 LLVM2 TLR IPS DVC DVCrev EC TC.
End MakeLangRefine.

Module InfFinLangRefine := MakeLangRefine InterpreterStackBigIntptr InterpreterStack64BitIntptr InfToFinAddrConvert FinToInfAddrConvert TopLevelBigIntptr TopLevel64BitIntptr TopLevelRefinements64BitIntptr FinToInfIntptrConvertSafe DVCInfFin DVCFinInf ECInfFin TCInfFin.

(* Just planning on using this for L4_convert from finite to infinite events. *)
(* Module FinInfLangRefine := MakeLangRefine InterpreterStack64BitIntptr InterpreterStackBigIntptr FinToInfAddrConvert InfToFinAddrConvert TopLevel64BitIntptr TopLevelBigIntptr TopLevelRefinementsBigIntptr FinToInfIntptrConvertSafe. DVCFinInf DVCInfFin ECFinInf . *)
