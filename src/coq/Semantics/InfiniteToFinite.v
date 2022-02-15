From Coq Require Import
     Relations
     String
     List
     Lia.

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
     Utils.PropT
     Utils.ListUtil.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor.

From ITree Require Import
     ITree
     Basics
     Basics.HeterogeneousRelations
     Eq.Eq.

Import InterpFacts.

Import MonadNotation.
Import ListNotations.

Module Type AddrConvert (ADDR1 : ADDRESS) (ADDR2 : ADDRESS).
  Parameter addr_convert : ADDR1.addr -> OOM ADDR2.addr.
End AddrConvert.

Module FinAddrConvert : AddrConvert FiniteMemory.Addr FiniteMemory.Addr.
  Definition addr_convert (a : FiniteMemory.Addr.addr) : OOM FiniteMemory.Addr.addr := ret a.
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
       | DV1.UVALUE_ExtractElement vec idx =>
           vec' <- uvalue_convert vec;;
           idx' <- uvalue_convert idx;;
           ret (DV2.UVALUE_ExtractElement vec' idx')
       | DV1.UVALUE_InsertElement vec elt idx =>
           vec' <- uvalue_convert vec;;
           elt' <- uvalue_convert elt;;
           idx' <- uvalue_convert idx;;
           ret (DV2.UVALUE_InsertElement vec' elt' idx')
       | DV1.UVALUE_ShuffleVector vec1 vec2 idxmask =>
           vec1' <- uvalue_convert vec1;;
           vec2' <- uvalue_convert vec2;;
           idxmask' <- uvalue_convert idxmask;;
           ret (DV2.UVALUE_ShuffleVector vec1' vec2' idxmask')
       | DV1.UVALUE_ExtractValue vec idxs =>
           vec' <- uvalue_convert vec;;
           ret (DV2.UVALUE_ExtractValue vec' idxs)
       | DV1.UVALUE_InsertValue vec elt idxs =>
           vec' <- uvalue_convert vec;;
           elt' <- uvalue_convert elt;;
           ret (DV2.UVALUE_InsertValue vec' elt' idxs)
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

  Require Import String.

  Definition L4_convert : Handler E1.L4 E2.L4.
  Proof.
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
    unfold FailureE in e0.
    apply (raise_error "").
  Defined.

  Definition L5_convert : Handler E1.L5 E2.L5.
  Proof.
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
    unfold FailureE in e0.
    apply (raise_error "").
  Defined.

  Definition L6_convert : Handler E1.L6 E2.L6.
  Proof.
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
    unfold FailureE in e0.
    apply (raise_error "").
  Defined.
End EventConvert.

Module Type LangRefine (IS1 : InterpreterStack) (IS2 : InterpreterStack) (AC1 : AddrConvert IS1.LP.ADDR IS2.LP.ADDR) (AC2 : AddrConvert IS2.LP.ADDR IS1.LP.ADDR) (LLVM1 : LLVMTopLevel IS1) (LLVM2 : LLVMTopLevel IS2) (TLR : TopLevelRefinements IS2 LLVM2).
  Module E1 := IS1.LLVM.Events.
  Module E2 := IS2.LLVM.Events.

  Module EC := EventConvert IS1.LP IS2.LP AC1 AC2 IS1.LLVM.Events E2.
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

  Definition L4_convert_PropT {A B} (f : A -> OOM B) (ts : PropT IS1.LLVM.Events.L4 A) : PropT E2.L4 B
    := fun t_e2 => exists t_e1,
           ts t_e1 /\ t_e2 = L4_convert_tree (uv <- t_e1;; lift_OOM (f uv)).

  (* Ideally we would convert memstates / local envs / local stacks /
     global envs... But for now we can get away with placeholders for
     these because the refine_res3 relation used by refine_L6 ignores
     these.
   *)
  Definition res_L4_convert_unsafe (res : LLVM1.res_L4) : OOM LLVM2.res_L4
    := match res with
       | (ms, ((lenv, lstack), (genv, uv))) =>
           uv' <- uvalue_convert uv;;
           ret (IS2.LLVM.MEM.emptyMemState, (([], []), ([], uv')))
       end.
 
  Definition refine_E1E2_L6 (srcs : PropT IS1.LLVM.Events.L4 LLVM1.res_L4) (tgts : PropT E2.L4 LLVM2.res_L4) : Prop
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

  (*
    If

    - ti2 is a refinement of ti1
    - tf2 refines ti2
    - tf1 refines tf2 at finite level

    Not sure that this is true.

    If ti1 -i> ti2

    and ti2 -if> tf2

    And tf2 -f> tf1...

    Does it really follow that ti1 -if> tf1?

    In theory I can refine ti1 to ti2, and to tf1 through
    tf2... BUT... Does this mean I can refine ti1 directly to tf1?

    In theory ti2 has fewer behaviours than ti1, and so if I can refine it to tf2, then I can also refine ti1 to tf2.
   *)
  Lemma refine_E1E2_L6_compose :
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
      Require Import Paco.paco.

      Set Nested Proofs Allowed.

      Lemma refine_OOM_h_L4_convert_tree :
        forall T x_inf y_inf RR,
          refine_OOM_h RR x_inf y_inf ->
          refine_OOM_h RR (@L4_convert_tree T x_inf) (@L4_convert_tree T y_inf).
      Proof.
        intros T x_inf y_inf RR H.
      Admitted.

      Import Morphisms.

      Lemma refine_OOM_h_bind :
        forall {T R E F} (x y : itree (E +' OOME +' F) T) (RR1 : relation T) (RR2 : relation R) k,
          (forall r1 r2, RR1 r1 r2 -> refine_OOM_h RR2 (k r1) (k r2)) ->
          refine_OOM_h RR1 x y ->
          refine_OOM_h RR2 (a <- x;; k a) (a <- y;; k a).
      Proof.
        intros T R E F x y RR1 RR2 k RK H.
        pinversion H; subst.
        - cbn.
          unfold refine_OOM_h.
          eapply interp_prop_Proper3.
          + unfold Proper, respectful, flip, impl.
            intros T0 R0 RR b a x0 y0 H0 x1 y1 H2 x2 y2 H3 x3 y3 H4 x4 y4 H5; subst.
            split; intros KSEPC;
            destruct y0 as [e | [e | e]]; cbn in *; auto.
          + rewrite unfold_bind.
            rewrite <- H1.
            reflexivity.
          + reflexivity.
          + eapply interp_prop_Proper2.
            * unfold Proper, respectful, flip, impl.
              intros A R0 e ta k1 k2 x0 y0 EQ KSPEC; subst.
              destruct e as [e | [e | e]]; cbn in *; try rewrite EQ; auto.
            * setoid_rewrite eq2.
              rewrite bind_ret_l.
              reflexivity.
            * apply RK.
              auto.
      Admitted.

      apply refine_OOM_h_L4_convert_tree.
      eapply refine_OOM_h_bind; eauto.

      intros r1 r2 H.
      unfold TLR_INF.R.refine_res3, TLR_INF.R.refine_res2, TLR_INF.R.refine_res1 in H.


      apply refine_blah.
      setoid_rewrite XY_INF.
      
      setoid_rewrite unfold_bind.
      pinversion XY_INF.
      + subst t2.
        pfold; red.
        rewrite eq2.
      unfold refine_OOM_h in XY_INF.
      setoid_rewrite interp_bind.
etransitivity; eauto.
    
    destruct XY as (rx & TX & XY).

    exists rx; split; auto.
    rewrite XY. eauto.

    - (* UB in ty *)
      unfold L4_convert_PropT in TY_FIN.
      destruct TY_FIN as (ry_inf & TY_INF & ry_fin_inf).

      specialize (XY_INF ry_inf TY_INF).
      destruct XY_INF as (rx_inf & TX_INF & [UB_rx_inf | XY_INF]);
        set (rx_fin := L4_convert_tree (uv <- rx_inf;; lift_OOM (res_L4_convert_unsafe uv))).
      + (* UB in tx *)
        exists rx_fin.
        split.
        * exists rx_inf; split; eauto.
        *
          (* rx_fin may or may not have UB.

             rx_fin may run out of memory before encountering UB.

             If rx_inf is like:

               externalcall f args;;
               UB

             Then if, say, args contains `DVALUE_IPTR 2^1000` the
             L4_convert handler will raise OOM when converting this to
             a finite IPTR value.

             Because of this `rx_fin` will always raise OOM prior to
             encountering UB.

             `rx_fin` is still a refinement of `rx_inf`...
           *)
          { clear TX_INF.
            subst rx_fin. induction UB_rx_inf.
            - destruct IHUB_rx_inf as [IHUB_UB | IHUB_REF].
              + left. setoid_rewrite interp_bind.
                rewrite H.
                rewrite tau_eutt.
                rewrite <- interp_bind.
                eauto.
              + right.
                unfold refine_OOM_h in *.
                eapply interp_prop_Proper2; eauto.
                Import Morphisms.
                * unfold Proper, respectful, Basics.flip, Basics.impl.
                  intros A R e ta k1 k2 x y EQ KSPEC.
                  destruct e as [e | [e | [e | [e | e]]]]; cbn in *;
                  auto; rewrite EQ; auto.
                * setoid_rewrite interp_bind.
                  rewrite H.
                  rewrite tau_eutt.
                  reflexivity.
            - destruct e as [call_e | oom_e].
              + (* CallE *)
                right.
                destruct call_e.
                admit.
              + (* OOME *)
                admit.
            - admit.
            - admit.
          }
          right.
          subst rx_fin.

          apply bind_contains_UB.

          (* Interp lemma *)
          { clear tx ty TX_INF TY_INF.
            clear tz TZ.
            clear ry_inf ry_fin_inf rz ry_fin UB_ry_fin.

            induction UB_rx_inf.
            - rewrite H.
              rewrite tau_eutt.
              eauto.
            - rewrite H.
              rewrite interp_vis.
              destruct e as [call_e | oom_e].
              
              + destruct call_e.cbn; destruct call_e; cbn.
                destruct (EC.DVC.uvalue_convert f).
                * (* NoOom *)
                  admit.
                * (* OOM *)
                  rewrite bind_bind.
                  cbn.
                  unfold raiseOOM.
                  rewrite bind_bind.
                  rewrite bind_trigger.
                rewrite bind_bind.
                eapply bind_contains_UB_k.
                { constructor. cbn.
              eapply IHUB_rx_inf.

            rewrite unfold_interp.
            genobs rx_inf rx_inf_obs.
            destruct rx_inf_obs.
            


          }

          
          
          apply interp_contains_UB.

          (* TODO: factor this out *)
          2: {
            clear.
            red.
            intros R [s].
            Require Import Paco.paco.
            pfold.
            cbn.
            constructor.
          }

          apply bind_contains_UB; eauto.
      + (* UB not necessarily in tx *)
        exists rx_fin.
        split.
        * exists rx_inf; split; eauto.
         * left.
          subst rx_fin.
          subst ry_fin.

          (* TODO: Move TT *)
          eapply contains_UB_refine_OOM_h with (RR:=TLR_INF.R.TT); eauto.
          Set Printing Implicit.
          unfold E1.L4.
          set (x:=(L4_convert_tree (uv <- rx_inf;; lift_OOM (res_L4_convert_unsafe uv)))).
          set (y:=(L4_convert_tree (uv <- rx_inf;; lift_OOM (res_L4_convert_unsafe uv)))).

          pose proof refine_OOM_h_reflexive.
          unfold RelationClasses.Reflexive in H.


          refine_oom_h_reflexivity.
         setoid_reflexivity.
          
    - specialize (XY ry TY).
      destruct XY as (rx & TX & [UB_rx | XY]).

      + (* UB in tx *)
        exists rx; split; auto.
      + exists rx; split; auto.
        right. 
        eapply refine_OOM_h_transitive; eauto.
        typeclasses eauto.
  Qed


    intros ubz TZ.

    specialize (YZ_FIN ubz TZ).
    destruct YZ_FIN as (uby_fin & blah & [UB | RFIN]).
    unfold L4_convert_PropT in blah.
    - (* t'' contains UB *)
      (* This means that ti2 contains UB, and can be refined to anything.

         Because ti2 is a refinement of ti1, this means that ti1 must
         also contain UB, and be able to be refined to anything.
       *)

      specialize (RINF t_e1 Hti2t_e1).
      destruct RINF as (t''' & Hti1t''' & [UB' | INF]).

      + eexists.
        split.
        2: { left. eauto. }

        unfold L4_convert_PropT in *.

        exists t'''.
        split.
        * auto.
        * subst. 
          auto.

      
      destruct ti2t'' as 
    - (* t'' doesn't contain UB *)
    exists t'.
  Qed.



  Instance Transitive_refine_L6 : Transitive refine_L6.
  Proof.
    unfold Transitive.
    intros tx ty tz XY YZ.

    intros rz TZ.
    specialize (YZ rz TZ).
    destruct YZ as (ry & TY & [UB_ry | YZ]).

    - (* UB in ty *)
      specialize (XY ry TY).
      destruct XY as (rx & TX & [UB_rx | XY]).

      + (* UB in tx *)
        exists rx; split; auto.
      + exists rx; split; auto.
        left. unfold refine_OOM_h in XY.
        eapply contains_UB_refine_OOM_h; eauto.
    - specialize (XY ry TY).
      destruct XY as (rx & TX & [UB_rx | XY]).

      + (* UB in tx *)
        exists rx; split; auto.
      + exists rx; split; auto.
        right. 
        eapply refine_OOM_h_transitive; eauto.
        typeclasses eauto.
  Abort.


  Lemma refine_E1E2_L6_transitive :
    forall ti1 ti2 tf2 tf1,
      TLR_INF.R.refine_L6 ti1 ti2 ->
      refine_E1E2_L6 ti2 tf2 ->
      TLR_FIN.R.refine_L6 tf2 tf1 ->
      refine_E1E2_L6 ti1 tf1.
  Proof.
    intros ti1 ti2 tf2 tf1 RINF RITOF RFIN.

    unfold refine_E1E2_L6 in *.
    Require Import Coq.Classes.RelationClasses.
    unfold TLR_FIN.R.refine_L6 in *.
    unfold TLR_INF.R.refine_L6 in *.

    intros t' H.
    eexists.
    split.

  Qed.

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
    exists t'.
    split.
    - unfold L4_convert_PropT.
      (* t_e1 is a tree in the model of the program in the infinite
         semantics, and t_e1 "agrees" with the behavior (t') in the
         finite semantics.

         "Agrees" in this context means that t' is equivalent to t_e1
         with the events converted, and the resulting uvalue converted.
       *)
      induction p.
      + unfold TopLevelBigIntptr.model, TopLevelBigIntptr.model_gen.
        cbn.
        From Vellvm Require Import Tactics.
        eexists.

        From ITree Require Import
             ITree
             Basics.Monad
             Events.StateFacts
             Eq.Eq.

        (* This rewrite is taking forever... wtf. *)
        rewrite bind_ret_l.
        repeat rewrite bind_ret_l.
        
        MCFGTheoryBigIntptr.MCFGTactics.go.
    - right.
      apply eutt_refine_oom_h; try typeclasses eauto.
      reflexivity.
  Qed.
End InfiniteToFinite.
