From Coq Require Import
     Relations
     String
     List
     Lia
     ZArith.

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
     Theory.TopLevelRefinements
     Theory.ContainsUB
     Utils.Error
     Utils.Monads
     Utils.MapMonadExtra
     Utils.PropT
     Utils.InterpProp
     Utils.ListUtil
     Handlers.MemoryModelImplementation.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor.

From ITree Require Import
     ITree
     Basics
     Basics.HeterogeneousRelations
     Eq.Eq Eq.EqAxiom.

Require Import Coq.Program.Equality.

Import InterpFacts.

Import MonadNotation.
Import ListNotations.

Module Type AddrConvert (ADDR1 : ADDRESS) (ADDR2 : ADDRESS).
  Parameter addr_convert : ADDR1.addr -> OOM ADDR2.addr.
End AddrConvert.

Module FinAddrConvert : AddrConvert MemoryModelImplementation.Addr MemoryModelImplementation.Addr.
  Definition addr_convert (a : MemoryModelImplementation.Addr.addr) : OOM MemoryModelImplementation.Addr.addr := ret a.
End FinAddrConvert.

Module Type DVConvert (LP1 : LLVMParams) (LP2 : LLVMParams) (AC : AddrConvert LP1.ADDR LP2.ADDR) (Events1 : LLVM_INTERACTIONS LP1.ADDR LP1.IP LP1.SIZEOF) (Events2 : LLVM_INTERACTIONS LP2.ADDR LP2.IP LP2.SIZEOF).
  Parameter dvalue_convert : Events1.DV.dvalue -> OOM Events2.DV.dvalue.
  Parameter uvalue_convert : Events1.DV.uvalue -> OOM Events2.DV.uvalue.
End DVConvert.

Module DVConvertMake (LP1 : LLVMParams) (LP2 : LLVMParams) (AC : AddrConvert LP1.ADDR LP2.ADDR) (Events1 : LLVM_INTERACTIONS LP1.ADDR LP1.IP LP1.SIZEOF) (Events2 : LLVM_INTERACTIONS LP2.ADDR LP2.IP LP2.SIZEOF) : DVConvert LP1 LP2 AC Events1 Events2.
  Import AC.

  Module DV1 := Events1.DV.
  Module DV2 := Events2.DV.

  Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia | DV1.solve_dvalue_measure | DV1.solve_uvalue_measure].

  Program Fixpoint dvalue_convert (dv1 : DV1.dvalue) {measure (DV1.dvalue_measure dv1)} : OOM DV2.dvalue
    := match dv1 with
       | DV1.DVALUE_Addr a =>
           a' <- addr_convert a;;
           ret (DV2.DVALUE_Addr a')
       | DV1.DVALUE_I1 x  => ret (DV2.DVALUE_I1 x)
       | DV1.DVALUE_I8 x  => ret (DV2.DVALUE_I8 x)
       | DV1.DVALUE_I32 x => ret (DV2.DVALUE_I32 x)
       | DV1.DVALUE_I64 x => ret (DV2.DVALUE_I64 x)
       | DV1.DVALUE_IPTR x =>
           let xz := LP1.IP.to_Z x in
           x' <- LP2.IP.from_Z xz;;
           ret (DV2.DVALUE_IPTR x')
       | DV1.DVALUE_Double x => ret (DV2.DVALUE_Double x)
       | DV1.DVALUE_Float x => ret (DV2.DVALUE_Float x)
       | DV1.DVALUE_Poison t => ret (DV2.DVALUE_Poison t)
       | DV1.DVALUE_None => ret DV2.DVALUE_None
       | DV1.DVALUE_Struct fields =>
           fields' <- map_monad_In fields (fun elt Hin => dvalue_convert elt);;
           ret (DV2.DVALUE_Struct fields')
       | DV1.DVALUE_Packed_struct fields =>
           fields' <- map_monad_In fields (fun elt Hin => dvalue_convert elt);;
           ret (DV2.DVALUE_Packed_struct fields')
       | DV1.DVALUE_Array elts =>
           elts' <- map_monad_In elts (fun elt Hin => dvalue_convert elt);;
           ret (DV2.DVALUE_Array elts')
       | DV1.DVALUE_Vector elts =>
           elts' <- map_monad_In elts (fun elt Hin => dvalue_convert elt);;
           ret (DV2.DVALUE_Vector elts')
       end.

  Program Fixpoint uvalue_convert (uv1 : DV1.uvalue) {measure (DV1.uvalue_measure uv1)} : OOM DV2.uvalue
    := match uv1 with
       | DV1.UVALUE_Addr a =>
           a' <- addr_convert a;;
           ret (DV2.UVALUE_Addr a')
       | DV1.UVALUE_I1 x  => ret (DV2.UVALUE_I1 x)
       | DV1.UVALUE_I8 x  => ret (DV2.UVALUE_I8 x)
       | DV1.UVALUE_I32 x => ret (DV2.UVALUE_I32 x)
       | DV1.UVALUE_I64 x => ret (DV2.UVALUE_I64 x)
       | DV1.UVALUE_IPTR x =>
           let xz := LP1.IP.to_Z x in
           x' <- LP2.IP.from_Z xz;;
           ret (DV2.UVALUE_IPTR x')
       | DV1.UVALUE_Double x => ret (DV2.UVALUE_Double x)
       | DV1.UVALUE_Float x => ret (DV2.UVALUE_Float x)
       | DV1.UVALUE_Poison t => ret (DV2.UVALUE_Poison t)
       | DV1.UVALUE_None => ret DV2.UVALUE_None
       | DV1.UVALUE_Struct fields =>
           fields' <- map_monad_In fields (fun elt Hin => uvalue_convert elt);;
           ret (DV2.UVALUE_Struct fields')
       | DV1.UVALUE_Packed_struct fields =>
           fields' <- map_monad_In fields (fun elt Hin => uvalue_convert elt);;
           ret (DV2.UVALUE_Packed_struct fields')
       | DV1.UVALUE_Array elts =>
           elts' <- map_monad_In elts (fun elt Hin => uvalue_convert elt);;
           ret (DV2.UVALUE_Array elts')
       | DV1.UVALUE_Vector elts =>
           elts' <- map_monad_In elts (fun elt Hin => uvalue_convert elt);;
           ret (DV2.UVALUE_Vector elts')
       | DV1.UVALUE_Undef dt =>
           (* Could be a bit odd with intptr *)
           ret (DV2.UVALUE_Undef dt)
       | DV1.UVALUE_IBinop iop v1 v2 =>
           v1' <- uvalue_convert v1;;
           v2' <- uvalue_convert v2;;
           ret (DV2.UVALUE_IBinop iop v1' v2')
       | DV1.UVALUE_ICmp cmp v1 v2 =>
           v1' <- uvalue_convert v1;;
           v2' <- uvalue_convert v2;;
           ret (DV2.UVALUE_ICmp cmp v1' v2')
       | DV1.UVALUE_FBinop fop fm v1 v2 =>
           v1' <- uvalue_convert v1;;
           v2' <- uvalue_convert v2;;
           ret (DV2.UVALUE_FBinop fop fm v1' v2')
       | DV1.UVALUE_FCmp cmp v1 v2 =>
           v1' <- uvalue_convert v1;;
           v2' <- uvalue_convert v2;;
           ret (DV2.UVALUE_FCmp cmp v1' v2')
       | DV1.UVALUE_Conversion conv t_from v t_to =>
           v' <- uvalue_convert v;;
           ret (DV2.UVALUE_Conversion conv t_from v' t_to)
       | DV1.UVALUE_GetElementPtr t ptrval idxs =>
           ptrval' <- uvalue_convert ptrval;;
           idxs' <- map_monad_In idxs (fun elt Hin => uvalue_convert elt);;
           ret (DV2.UVALUE_GetElementPtr t ptrval' idxs')
       | DV1.UVALUE_ExtractElement t vec idx =>
           vec' <- uvalue_convert vec;;
           idx' <- uvalue_convert idx;;
           ret (DV2.UVALUE_ExtractElement t vec' idx')
       | DV1.UVALUE_InsertElement t vec elt idx =>
           vec' <- uvalue_convert vec;;
           elt' <- uvalue_convert elt;;
           idx' <- uvalue_convert idx;;
           ret (DV2.UVALUE_InsertElement t vec' elt' idx')
       | DV1.UVALUE_ShuffleVector vec1 vec2 idxmask =>
           vec1' <- uvalue_convert vec1;;
           vec2' <- uvalue_convert vec2;;
           idxmask' <- uvalue_convert idxmask;;
           ret (DV2.UVALUE_ShuffleVector vec1' vec2' idxmask')
       | DV1.UVALUE_ExtractValue t vec idxs =>
           vec' <- uvalue_convert vec;;
           ret (DV2.UVALUE_ExtractValue t vec' idxs)
       | DV1.UVALUE_InsertValue t vec elt idxs =>
           vec' <- uvalue_convert vec;;
           elt' <- uvalue_convert elt;;
           ret (DV2.UVALUE_InsertValue t vec' elt' idxs)
       | DV1.UVALUE_Select cnd v1 v2 =>
           cnd' <- uvalue_convert cnd;;
           v1' <- uvalue_convert v1;;
           v2' <- uvalue_convert v2;;
           ret (DV2.UVALUE_Select cnd' v1' v2')
       | DV1.UVALUE_ExtractByte uv dt idx sid =>
           uv' <- uvalue_convert uv;;
           idx' <- uvalue_convert idx;;
           ret (DV2.UVALUE_ExtractByte uv' dt idx' sid)
       | DV1.UVALUE_ConcatBytes uvs dt =>
           uvs' <- map_monad_In uvs (fun elt Hin => uvalue_convert elt);;
           ret (DV2.UVALUE_ConcatBytes uvs' dt)
       end.

End DVConvertMake.

Module EventConvert (LP1 : LLVMParams) (LP2 : LLVMParams) (AC : AddrConvert LP1.ADDR LP2.ADDR) (AC2 : AddrConvert LP2.ADDR LP1.ADDR) (E1 : LLVM_INTERACTIONS LP1.ADDR LP1.IP LP1.SIZEOF) (E2 : LLVM_INTERACTIONS LP2.ADDR LP2.IP LP2.SIZEOF).
  (* TODO: should this be a parameter? *)
  Module DVC := DVConvertMake LP1 LP2 AC E1 E2.
  Module DVCrev := DVConvertMake LP2 LP1 AC2 E2 E1.
  Import DVC.



  Definition L4_convert : Handler E1.L4 E2.L4.
    refine (fun A e => _).

    refine (match e with
            | inl1 (E1.ExternalCall dt f args) =>
                _
            | inr1 (inl1 e0) =>
                raise_oom ""
            | inr1 (inr1 (inl1 e0)) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inl1 e0))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 e0))) =>
                _ (* FailureE *)
            end).

    (* External Calls *)
    refine (f' <- lift_OOM (uvalue_convert f);;
            args' <- lift_OOM (map_monad_In args (fun elt Hin => dvalue_convert elt));;
            dv <- trigger (E2.ExternalCall dt f' args');;
            _).

    inversion e0.
    apply (lift_OOM (DVCrev.dvalue_convert dv)).

    (* UBE *)
    inversion e0.
    apply (raise_ub "").

    (* DebugE *)
    inversion e0.
    apply (debug H).

    (* FailureE *)
    inversion e0.
    apply (raise_error "").
  Defined.

  Definition L5_convert : Handler E1.L5 E2.L5.
    refine (fun A e => _).

    refine (match e with
            | inl1 (E1.ExternalCall dt f args) =>
                _
            | inr1 (inl1 e0) =>
                raise_oom ""
            | inr1 (inr1 (inl1 e0)) =>
                _
            | inr1 (inr1 (inr1 e0)) =>
                _
            end).

    (* External Calls *)
    refine (f' <- lift_OOM (uvalue_convert f);;
            args' <- lift_OOM (map_monad_In args (fun elt Hin => dvalue_convert elt));;
            dv <- trigger (E2.ExternalCall dt f' args');;
            _).

    inversion e0.
    apply (lift_OOM (DVCrev.dvalue_convert dv)).

    (* DebugE *)
    inversion e0.
    apply (debug H).

    (* FailureE *)
    inversion e0.
    apply (raise_error "").
  Defined.

  Definition L6_convert : Handler E1.L6 E2.L6.
    refine (fun A e => _).

    refine (match e with
            | inl1 (E1.ExternalCall dt f args) =>
                _
            | inr1 (inl1 e0) =>
                raise_oom ""
            | inr1 (inr1 (inl1 e0)) =>
                _
            | inr1 (inr1 (inr1 e0)) =>
                _
            end).

    (* External Calls *)
    refine (f' <- lift_OOM (uvalue_convert f);;
            args' <- lift_OOM (map_monad_In args (fun elt Hin => dvalue_convert elt));;
            dv <- trigger (E2.ExternalCall dt f' args');;
            _).

    inversion e0.
    apply (lift_OOM (DVCrev.dvalue_convert dv)).

    (* DebugE *)
    inversion e0.
    apply (debug H).

    (* FailureE *)
    inversion e0.
    apply (raise_error "").
  Defined.
End EventConvert.

Module Type LangRefine (IS1 : InterpreterStack) (IS2 : InterpreterStack) (AC1 : AddrConvert IS1.LP.ADDR IS2.LP.ADDR) (AC2 : AddrConvert IS2.LP.ADDR IS1.LP.ADDR) (LLVM1 : LLVMTopLevel IS1) (LLVM2 : LLVMTopLevel IS2) (TLR : TopLevelRefinements IS2 LLVM2).
  Module E1 := IS1.LP.Events.
  Module E2 := IS2.LP.Events.

  Module EC := EventConvert IS1.LP IS2.LP AC1 AC2 IS1.LP.Events E2.
  Import EC.
  Import EC.DVC.

  (* TODO: move this? *)
  Definition L4_convert_tree {T} (t : itree E1.L4 T) : itree E2.L4 T := interp L4_convert t.
  Definition L5_convert_tree {T} (t : itree E1.L5 T) : itree E2.L5 T := interp L5_convert t.
  Definition L6_convert_tree {T} (t : itree E1.L6 T) : itree E2.L6 T := interp L6_convert t.

  (* Relate trees at L4 with proper refinement relation... *)
  Import LLVM2.
  Import TLR.
  Import TLR.R.

  Definition L4_convert_PropT {A B} (f : A -> OOM B) (ts : PropT IS1.LP.Events.L4 A) : PropT E2.L4 B
    := fun t_e2 => exists t_e1,
           ts t_e1 /\ t_e2 = L4_convert_tree (uv <- t_e1;; lift_OOM (f uv)).

  (* Ideally we would convert memstates / local envs / local stacks /
     global envs... But for now we can get away with placeholders for
     these because the refine_res3 relation used by refine_L6 ignores
     these.
   *)
  Definition res_L4_convert_unsafe (res : LLVM1.res_L4) : OOM LLVM2.res_L4
    := match res with
       | (ms, (sid, ((lenv, lstack), (genv, dv)))) =>
           dv' <- dvalue_convert dv;;
           ret (MMEP.MMSP.initial_memory_state, (0, (([], []), ([], dv'))))
       end.

  Definition refine_E1E2_L6 (srcs : PropT IS1.LP.Events.L4 LLVM1.res_L4) (tgts : PropT E2.L4 LLVM2.res_L4) : Prop
    :=
    (* res_L4_convert_unsafe should be fine here because refine_L6
       ignores all of the placeholder values *)
    refine_L6 (L4_convert_PropT res_L4_convert_unsafe srcs) tgts.

  (* TODO: not sure about name... *)
  Definition model_E1E2_L6
             (p1 p2 : list
                        (LLVMAst.toplevel_entity
                           LLVMAst.typ
                           (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ))))
    : Prop :=
    refine_E1E2_L6 (LLVM1.model p1) (LLVM2.model p2).

End LangRefine.

Module InfiniteToFinite : LangRefine InterpreterStackBigIntptr InterpreterStack64BitIntptr FinAddrConvert FinAddrConvert TopLevelBigIntptr TopLevel64BitIntptr TopLevelRefinements64BitIntptr.
  Include LangRefine InterpreterStackBigIntptr InterpreterStack64BitIntptr FinAddrConvert FinAddrConvert TopLevelBigIntptr TopLevel64BitIntptr TopLevelRefinements64BitIntptr.

  From Vellvm Require Import InterpreterMCFG.

  Import MCFGTheoryBigIntptr.
  Import MCFGTheory64BitIntptr.

  Module TLR_INF := TopLevelRefinementsBigIntptr.
  Module TLR_FIN := TopLevelRefinements64BitIntptr.

  Hint Resolve interp_PropT__mono : paco.

  (* TODO: Move these refine_OOM_h lemmas? *)
  Require Import Paco.paco.
  Import Morphisms.

  #[local] Notation E1 := (E1.ExternalCallE +' OOME +' UBE +' DebugE +' FailureE).
  #[local] Notation E2 := (E2.ExternalCallE +' OOME +' UBE +' DebugE +' FailureE).
  #[local] Notation OOM_h := (refine_OOM_handler (F:=_)).
  #[local] Notation OOM_spec := (@oom_k_spec _ _).

  Instance refine_OOM_h_eq_itree {E F T RR} : Proper (eq_itree eq ==> eq_itree eq ==> iff) (@refine_OOM_h E F T RR).
  repeat intro. rewrite H, H0.
  reflexivity.
  Qed.

  Lemma Returns_uvalue_convert_L1_L2 :
    forall a d f u l t args,
      EC.DVCrev.dvalue_convert a = NoOom d ->
      EC.DVC.uvalue_convert f = NoOom u ->
      @Returns E2 E2.DV.dvalue a (trigger (resum IFun E2.DV.dvalue (E2.ExternalCall t u l))) ->
      @Returns E1 E1.DV.dvalue d (trigger (E1.ExternalCall t f args)).
  Proof.
  Admitted.

  Lemma refine_OOM_h_L4_convert_tree :
    forall T x_inf y_inf RR,
      refine_OOM_h RR x_inf y_inf ->
      refine_OOM_h RR (@L4_convert_tree T x_inf) (@L4_convert_tree T y_inf).
  Proof.
    intros T.

    unfold refine_OOM_h, L4_convert_tree, refine_OOM_h_flip.
    intros.
    rewrite (unfold_interp y_inf).
    rewrite (unfold_interp x_inf).

    match goal with
    | |- interp_prop _ _ ?l ?r => remember l as i; remember r as i0
    end.

    assert (i ≅ _interp EC.L4_convert (observe y_inf)). {
      rewrite Heqi. reflexivity.
    } clear Heqi.
    remember (_interp EC.L4_convert (observe x_inf)).
    assert (i0 ≅ _interp EC.L4_convert (observe x_inf)). {
      rewrite Heqi0. reflexivity.
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
      setoid_rewrite Heqi. setoid_rewrite Heqi0.
      subst; constructor; auto.
    - pstep. cbn in H1, H2.
      rewrite itree_eta in H1, H2.
      red.
      destruct (observe i) eqn: Heqi; destruct (observe i0) eqn: Heqi0;
        try apply eqit_inv in H1; try apply eqit_inv in H2; cbn in H1, H2; try contradiction; auto.
      setoid_rewrite Heqi. setoid_rewrite Heqi0.
      subst; constructor; auto.

      right; eapply CIH; eauto;
      rewrite unfold_interp in H1, H2; auto.
    - pstep. cbn in H1, H2.
      rewrite itree_eta in H1, H2.
      red.
      destruct (observe i) eqn: Heqi;
        try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
      setoid_rewrite Heqi.
      subst; constructor; auto.
      rewrite unfold_interp in H1.
      specialize (IHinterp_PropTF _ _ H1 H2).

      punfold IHinterp_PropTF.
    - pstep. cbn in H1, H2.
      rewrite itree_eta in H1, H2.
      red.
      destruct (observe i0) eqn: Heqi;
        try apply eqit_inv in H2; cbn in H2; try contradiction; auto.
      setoid_rewrite Heqi.
      subst; constructor; auto.
      rewrite unfold_interp in H2.
      specialize (IHinterp_PropTF _ _ H1 H2).

      punfold IHinterp_PropTF.
    - pstep. apply bisimulation_is_eq in HT1.
      rewrite HT1 in H1. cbn in H1.
      setoid_rewrite bind_trigger in H1.
      setoid_rewrite bind_vis in H1.
      apply bisimulation_is_eq in H1. rewrite H1.
      econstructor; eauto.
      eapply eqit_Vis; intros; inv u.
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
        destruct (EC.DVC.uvalue_convert f) eqn : Hf.
        { rewrite bind_ret_l, bind_bind in H1.
          destruct
            (map_monad_In args
              (fun (elt : InterpreterStackBigIntptr.LP.Events.DV.dvalue) (_ : In elt args) => EC.DVC.dvalue_convert elt)) eqn: Hm.
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
              ITree.bind match EC.DVCrev.dvalue_convert u0 with
                        | NoOom a0 => ret a0
                        | Oom s => raise_oom s
                         end (fun x1 : E1.DV.dvalue => Tau (interp EC.L4_convert (k2 x1)))).
              reflexivity. intros. inv H.
            - cbn. red in H1. subst.
              eapply bisimulation_is_eq in H1. rewrite H1.

              destruct (EC.DVCrev.dvalue_convert a) eqn: Ht.
              + setoid_rewrite H in HK. subst.
                eapply Returns_uvalue_convert_L1_L2 in H3; eauto.
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
            setoid_rewrite Heqi.
            destruct H1 as (?&?&?).
            dependent destruction x.
            red in H, H0.
            (* rewrite H1. *)
            econstructor; eauto.
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
          setoid_rewrite Heqi.
          destruct H1 as (?&?&?).
          dependent destruction x.
          red in H, H0. cbn in *.
          econstructor; eauto.
        * intros. inv a.
        * red; reflexivity.
        * rewrite <- itree_eta in H2. rewrite H2.
          rewrite <- unfold_interp. rewrite KS.
          rewrite interp_vis.
          cbn. rewrite bind_bind. unfold lift_OOM. rewrite Hf.
          setoid_rewrite bind_trigger.
          setoid_rewrite bind_vis.
          unfold subevent. rewrite H0.
          eapply eqit_Vis. intros. inv u.
      + destruct s.
        * unfold raiseOOM in H1. rewrite bind_bind, bind_trigger in H1.
          rewrite itree_eta in H1, H2.
          red.
          destruct (observe i) eqn: Heqi;
            try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
          setoid_rewrite Heqi.
          destruct H1 as (?&?&?).
          dependent destruction x.
          red in H, H0. cbn in *.
          econstructor; eauto.
          -- intros. inv a.
          -- red; reflexivity.
          -- rewrite <- itree_eta in H2. rewrite H2.
             rewrite <- unfold_interp. rewrite H0.
             rewrite bind_trigger.
             rewrite interp_vis. cbn. do 2 setoid_rewrite bind_trigger.
             rewrite bind_vis. subst.
             apply eqit_Vis; intros; inv u.
        * destruct s; try destruct u; cbn in H1.
          -- repeat red in HTA.
              unfold raiseUB in H1. rewrite bind_trigger in H1.
              red.
              destruct (observe i) eqn: Heqi;
                try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
              setoid_rewrite Heqi.
              destruct H1 as (?&?&?).
              dependent destruction x.
              red in H, H0.
              econstructor; eauto.
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
                setoid_rewrite Heqi.
                destruct H1 as (?&?&?).
                dependent destruction x.
                red in H, H0. subst. 
                assert (Returns tt ta).
                { rewrite H. unfold trigger. eapply ReturnsVis; eauto.
                  unfold subevent. reflexivity.
                  constructor; reflexivity. }
                specialize (HK _ H0). pclearbot.
                econstructor; eauto.
                ** intros. red in H1. specialize (H1 tt).
                   eapply bisimulation_is_eq in H1. destruct a.
                   rewrite H1.
                   right; eapply CIH.
                   2 : { rewrite <- interp_tau, <- unfold_interp. reflexivity. }
                   pstep; econstructor; eauto. punfold HK.
                   rewrite <- unfold_interp. Unshelve.
                   16 : exact (fun x => interp EC.L4_convert (k2 x)). reflexivity.
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
                setoid_rewrite Heqi.
                destruct H1 as (?&?&?).
                dependent destruction x.
                red in H, H0. cbn in *; subst.
                econstructor; eauto.
                intros. inv a.
                red; reflexivity.
                setoid_rewrite <- itree_eta in H2. rewrite H2.
                rewrite <- unfold_interp.
                rewrite H0. cbn. rewrite interp_bind.
                rewrite interp_trigger. cbn. unfold LLVMEvents.raise.
                do 2 rewrite bind_trigger. rewrite bind_vis.
                apply eqit_Vis; intros; inv u.

                Unshelve.
                all : eauto.
                all : inv x.
  Qed.

  Lemma refine_OOM_h_bind :
    forall {T R E F} (x y : itree (E +' OOME +' F) T) (RR1 : relation T) (RR2 : relation R) k,
      (forall r1 r2, RR1 r1 r2 -> refine_OOM_h RR2 (k r1) (k r2)) ->
      refine_OOM_h RR1 x y ->
      refine_OOM_h RR2 (a <- x;; k a) (a <- y;; k a).
  Proof.
    intros T R E F.

    unfold refine_OOM_h, refine_OOM_h_flip.
    intros t1 t2 RR1 RR2.

    unfold bind, Monad_itree.
    revert t1 t2. pcofix CIH.
    intros t1 t2 k HK EQT.
    punfold EQT.
    red in EQT.

    assert (a <- t1 ;; k a =
              match observe t1 with
              | RetF r => k r
              | TauF t0 => Tau (ITree.bind t0 k)
              | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) k)
              end).
    { apply bisimulation_is_eq; setoid_rewrite unfold_bind; reflexivity. }
    setoid_rewrite H; clear H.

    assert (a <- t2 ;; k a =
              match observe t2 with
              | RetF r => k r
              | TauF t0 => Tau (ITree.bind t0 k)
              | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) k)
              end).
    { apply bisimulation_is_eq; setoid_rewrite unfold_bind; reflexivity. }
    setoid_rewrite H; clear H.

    pstep.
    induction EQT; eauto; pclearbot.
    - specialize (HK _ _ REL).
      punfold HK.
      eapply interp_PropTF_mono. eapply HK.
      intros. pclearbot. left.
      eapply paco2_mon; eauto.
      intros; contradiction.
    - constructor. right.
      eapply CIH; eauto.
    - econstructor; auto.
    - econstructor; auto.
    - eapply Interp_PropT_Vis_OOM with (e := e).
      punfold HT1; red in HT1. remember (observe (vis e k1)).
      hinduction HT1 before k; intros; inv Heqi; try inv CHECK.
      dependent destruction H1. unfold subevent.
      eapply eqit_Vis.
      Unshelve.
      intros. cbn.
      eapply eq_itree_clo_bind; pclearbot; eauto. intros; subst; reflexivity.
    - eapply Interp_PropT_Vis; eauto.
      intros; eauto. right. eapply CIH; eauto.
      specialize (HK0 _ H1). pclearbot. eapply HK0; eauto.
      rewrite <- unfold_bind.
      setoid_rewrite <- Eq.bind_bind.
      eapply eutt_clo_bind; eauto. intros; eauto. subst; reflexivity.
  Qed.

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
  Lemma refine_E1E2_L6_compose_inf_to_fin :
    forall tx ty tz,
      TLR_INF.R.refine_L6 tx ty ->
      refine_E1E2_L6 ty tz ->
      refine_E1E2_L6 tx tz.
  Proof.
    intros tx ty tz XY_INF YZ_FIN.

    unfold refine_E1E2_L6 in *.
    unfold TLR_INF.R.refine_L6 in *.
    unfold TLR_FIN.R.refine_L6 in *.

    intros rz TZ.
    specialize (YZ_FIN rz TZ).
    destruct YZ_FIN as (ry_fin & TY_FIN & YZ).

    unfold L4_convert_PropT in TY_FIN.
    destruct TY_FIN as (ry_inf & TY_INF & ry_fin_inf).

    specialize (XY_INF ry_inf TY_INF).
    destruct XY_INF as (rx_inf & TX_INF & XY_INF).

    set (rx_fin := L4_convert_tree (uv <- rx_inf;; lift_OOM (res_L4_convert_unsafe uv))).
    exists rx_fin.
    split.
    - unfold L4_convert_PropT.
      exists rx_inf; split; auto.
    - rewrite <- YZ.
      subst ry_fin.
      subst rx_fin.

      (* There's probably a more general lemma hiding here *)
      unfold L4_convert_tree.

      Unset Universe Checking.
      apply refine_OOM_h_L4_convert_tree.
      eapply refine_OOM_h_bind; eauto.

      intros r1 r2 H.
      unfold TLR_INF.R.refine_res3, TLR_INF.R.refine_res2, TLR_INF.R.refine_res1 in H.
      destruct r1 as [r1a [r1sid [[r1b1 r1b2] [r1c dv1]]]].
      destruct r2 as [r2a [r2sid [[r2b1 r2b2] [r2c dv2]]]].
      inversion H; subst.
      inversion H5; subst.
      inversion H7; subst.
      inversion H9; subst.
      inversion H9; subst.
      cbn.
      reflexivity.
  Qed.

  Lemma refine_E1E2_L6_compose_fin_to_inf :
    forall tx ty tz,
      refine_E1E2_L6 tx ty ->
      TLR_FIN.R.refine_L6 ty tz ->
      refine_E1E2_L6 tx tz.
  Proof.
    intros tx ty tz XY_INF_TO_FIN YZ_FIN.

    unfold refine_E1E2_L6 in *.
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


  Lemma refine_E1E2_L6_transitive :
    forall ti1 ti2 tf1 tf2,
      TLR_INF.R.refine_L6 ti1 ti2 ->
      refine_E1E2_L6 ti2 tf1 ->
      TLR_FIN.R.refine_L6 tf1 tf2 ->
      refine_E1E2_L6 ti1 tf2.
  Proof.
    intros ti1 ti2 tf1 tf2 RINF RITOF RFIN.

    eapply refine_E1E2_L6_compose_fin_to_inf; eauto.
    eapply refine_E1E2_L6_compose_inf_to_fin; eauto.
  Qed.

  (* TODO: move this *)
  Lemma model_E1E2_L6_sound :
    forall (p : list
             (LLVMAst.toplevel_entity
                LLVMAst.typ
                (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ)))),
      model_E1E2_L6 p p.
  Proof.
    intros p.
    unfold model_E1E2_L6.
    intros t' m_fin.
    exists (L4_convert_tree
    (uv <-
     LLVMEvents.raise
       ("Could not look up global id " ++ CeresString.DString.of_string ("" ++ "main") "");;
     lift_OOM (res_L4_convert_unsafe uv))).
    split.
    - unfold L4_convert_PropT.
      (* t_e1 is a tree in the model of the program in the infinite
         semantics, and t_e1 "agrees" with the behavior (t') in the
         finite semantics.

         "Agrees" in this context means that t' is equivalent to t_e1
         with the events converted, and the resulting uvalue converted.
       *)
      induction p.
      unfold model, model_gen in *.
      (* cbn in m_fin. *)
      (* red in m_fin. *)
      (* rewrite bind_bind in m_fin. *)
      (* setoid_rewrite bind_ret_l in m_fin. *)
      (* + unfold TopLevelBigIntptr.model, TopLevelBigIntptr.model_gen. *)
      (*   From Vellvm Require Import Tactics. *)
      (*   exists (LLVMEvents.raise *)
      (*        ("Could not look up global id " ++ CeresString.DString.of_string ("" ++ "main") "")). *)
      (*   set (raise := (LLVMEvents.raise *)
      (*             ("Could not look up global id " ++ CeresString.DString.of_string ("" ++ "main") ""))). *)

      (*   From ITree Require Import *)
      (*        ITree *)
      (*        Basics.Monad *)
      (*        Events.StateFacts *)
      (*        Eq.Eq. *)

      (*   unfold model in m_fin. *)
      (*   unfold model_gen in m_fin. *)
      (*   cbn in m_fin. *)
      (*   unfold interp_mcfg5 in m_fin. *)
    (*     repeat rewrite bind_ret_l in m_fin. *)
    (*     Import TranslateFacts. *)
    (*     rewrite translate_ret in m_fin. *)
    (*     repeat rewrite bind_ret_l in m_fin. *)


    (*     split. *)
    (*     left. *)
    (*     cbn. *)
    (*     unfold InterpreterStackBigIntptr.interp_mcfg5. *)
    (*     MCFGTheoryBigIntptr.MCFGTactics.go. *)
    (*     unfold LLVMEvents.raise. *)
    (*     MCFGTheoryBigIntptr.MCFGTactics.go. *)
    (*     rewrite InterpreterStackBigIntptr.LLVM.MEMORY_ITREE_THEORY.interp_memory_trigger. *)
    (*     cbn. *)
    (*     MCFGTheoryBigIntptr.MCFGTactics.go. *)
    (*     rewrite bind_trigger. *)
    (*     MCFGTheoryBigIntptr.MCFGTactics.go. *)

    (*     match goal with *)
    (*     | H: _ |-  InterpreterStackBigIntptr.LLVM.Pick.model_undef eq ?t _ => *)
    (*         assert (t ≈ LLVMEvents.raise ("Could not look up global id " ++ CeresString.DString.of_string ("" ++ "main") "")) as Ht *)
    (*     end. *)
    (*     admit. *)

    (*     rewrite Ht. *)
    (*     unfold InterpreterStackBigIntptr.LLVM.Pick.model_undef. *)
    (*     subst raise. *)
    (*     admit. *)
    (*     reflexivity. *)
    (*   + admit. *)
    (* - apply eutt_refine_oom_h; try typeclasses eauto. *)
    (*   admit. *)
  Abort.

End InfiniteToFinite.
