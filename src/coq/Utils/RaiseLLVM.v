Section Failure.
  Variable E : Type -> Type.
  Context {FAIL : FailureE -< E}.

  Lemma raise_bind_itree :
    forall A B (f : A -> itree E B) x,
      bind (raise x) f ≈ raise x.
  Proof using.
    intros A B f x.
    unfold raise.
    cbn.
    rewrite bind_bind.
    eapply eutt_clo_bind.
    reflexivity.
    intros u1 u2 H.
    destruct u1.
  Qed.

  Lemma raise_map_itree :
    forall A B (f : A -> B) x,
      ITree.map f (@raise _ _ FAIL x) ≈ raise x.
  Proof using.
    intros A B f x.
    unfold raise.
    rewrite map_bind.
    eapply eutt_clo_bind.
    reflexivity.
    intros [].
  Qed.

  Lemma raise_map_itree_inv :
    forall A B (f : A -> B) t x,
      ITree.map f t ≈ @raise _ _ FAIL x ->
      t ≈ raise x.
  Proof using.
    unfold ITree.map. intros A B.
    ginit. gcofix CIH.
    intros. rewrite unfold_bind in H0.
    punfold H0. red in H0.
    remember
         (observe
            match observe t with
            | RetF r => Ret (f r)
            | TauF t => Tau (ITree.bind t (fun x : A => Ret (f x)))
            | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) (fun x0 : A => Ret (f x0)))
            end); remember (observe (raise x)).

    assert (go i ≅
           match observe t with
           | RetF r => Ret (f r)
           | TauF t => Tau (ITree.bind t (fun x : A => Ret (f x)))
           | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) (fun x0 : A => Ret (f x0)))
           end). rewrite Heqi; rewrite <- itree_eta; reflexivity.
    clear Heqi.
    rewrite itree_eta; unfold raise; rewrite bind_trigger.
    gstep.

    revert t H.
    induction H0; inv Heqi0.
    - dependent destruction H1.
      dependent destruction H2.
      cbn in *. inv H0. intros.
      destruct (observe t); eapply eqit_inv in H; inv H.
      destruct H0 as (?&?). destruct H.
      constructor. intros. inv v.
    - intros t TAU.
      destruct (observe t); eapply eqit_inv in TAU; try solve [inv TAU].
      cbn in *. assert (t1 ≈ raise x). { pstep; eauto. }
      clear H0.
      assert (t1 ≅ ITree.map f t0). { punfold TAU; pstep; unfold ITree.map; eauto. }
      clear TAU.
      rewrite H0 in H1.
      specialize (IHeqitF eq_refl).
      setoid_rewrite <- unfold_bind in IHeqitF.
      constructor; eauto. eapply IHeqitF; rewrite <- itree_eta; eauto.
  Qed.

  Lemma raise_ret_inv_itree :
      forall A x (y : A),
        ~ (@raise _ _ FAIL x) ≈ (ret y).
  Proof using.
    intros A x y.
    intros CONTRA.
    cbn in CONTRA.
    pinversion CONTRA.
  Qed.

  #[global] Instance RaiseBindM_Fail : RaiseBindM (itree E) string (fun T => raise) :=
    { rbm_raise_bind := raise_bind_itree;
      rbm_raise_ret_inv := raise_ret_inv_itree;
    }.
End Failure.

Section OOM.
  Variable E : Type -> Type.
  Context {OOM : OOME -< E}.

  Lemma raiseOOM_bind_itree :
    forall A B (f : A -> itree E B) x,
      bind (raiseOOM x) f ≈ raiseOOM x.
  Proof using.
    intros A B f x.
    unfold raiseOOM.
    cbn.
    rewrite bind_bind.
    eapply eutt_clo_bind.
    reflexivity.
    intros u1 u2 H.
    destruct u1.
  Qed.

  Lemma raiseOOM_map_itree :
    forall A B (f : A -> B) x,
      ITree.map f (raiseOOM (E:=E) x) ≈ raiseOOM x.
  Proof using.
    intros A B f x.
    unfold raiseOOM, raise.
    rewrite map_bind.
    eapply eutt_clo_bind.
    reflexivity.
    intros [].
  Qed.

  Lemma raiseOOM_map_itree_inv :
    forall A B (f : A -> B) t x,
      ITree.map f t ≈ raiseOOM (E:=E) x ->
      t ≈ raiseOOM x.
  Proof using.
    unfold ITree.map. intros A B.
    ginit. gcofix CIH.
    intros. rewrite unfold_bind in H0.
    punfold H0. red in H0.
    remember
         (observe
            match observe t with
            | RetF r => Ret (f r)
            | TauF t => Tau (ITree.bind t (fun x : A => Ret (f x)))
            | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) (fun x0 : A => Ret (f x0)))
            end); remember (observe (raiseOOM x)).

    assert (go i ≅
           match observe t with
           | RetF r => Ret (f r)
           | TauF t => Tau (ITree.bind t (fun x : A => Ret (f x)))
           | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) (fun x0 : A => Ret (f x0)))
           end). rewrite Heqi; rewrite <- itree_eta; reflexivity.
    clear Heqi.
    rewrite itree_eta; unfold raiseOOM; rewrite bind_trigger.
    gstep.

    revert t H.
    induction H0; inv Heqi0.
    - dependent destruction H1.
      dependent destruction H2.
      cbn in *. inv H0. intros.
      destruct (observe t); eapply eqit_inv in H; inv H.
      destruct H0 as (?&?). destruct H.
      constructor. intros. inv v.
    - intros t TAU.
      destruct (observe t); eapply eqit_inv in TAU; try solve [inv TAU].
      cbn in *. assert (t1 ≈ raiseOOM x). { pstep; eauto. }
      clear H0.
      assert (t1 ≅ ITree.map f t0). { punfold TAU; pstep; unfold ITree.map; eauto. }
      clear TAU.
      rewrite H0 in H1.
      specialize (IHeqitF eq_refl).
      setoid_rewrite <- unfold_bind in IHeqitF.
      constructor; eauto. eapply IHeqitF; rewrite <- itree_eta; eauto.
  Qed.

  Lemma raiseOOM_ret_inv_itree :
      forall A x (y : A),
        ~ (raiseOOM (E:=E) x) ≈ (ret y).
  Proof using.
    intros A x y.
    intros CONTRA.
    cbn in CONTRA.
    pinversion CONTRA.
  Qed.

  #[global] Instance RaiseBindM_OOM : RaiseBindM (itree E) string (fun T => raiseOOM) :=
    { rbm_raise_bind := raiseOOM_bind_itree;
      rbm_raise_ret_inv := raiseOOM_ret_inv_itree;
    }.
End OOM.

Section UB.
  Variable E : Type -> Type.
  Context {UB : UBE -< E}.

  Lemma raiseUB_bind_itree :
    forall A B (f : A -> itree E B) x,
      bind (raiseUB x) f ≈ raiseUB x.
  Proof using.
    intros A B f x.
    unfold raiseUB.
    cbn.
    rewrite bind_bind.
    eapply eutt_clo_bind.
    reflexivity.
    intros u1 u2 H.
    destruct u1.
  Qed.

  Lemma raiseUB_map_itree :
    forall A B (f : A -> B) x,
      ITree.map f (raiseUB (E:=E) x) ≈ raiseUB x.
  Proof using.
    intros A B f x.
    unfold raiseUB, raise.
    rewrite map_bind.
    eapply eutt_clo_bind.
    reflexivity.
    intros [].
  Qed.

  Lemma raiseUB_map_itree_inv :
    forall A B (f : A -> B) t x,
      ITree.map f t ≈ raiseUB (E:=E) x ->
      t ≈ raiseUB x.
  Proof using.
    unfold ITree.map. intros A B.
    ginit. gcofix CIH.
    intros. rewrite unfold_bind in H0.
    punfold H0. red in H0.
    remember
         (observe
            match observe t with
            | RetF r => Ret (f r)
            | TauF t => Tau (ITree.bind t (fun x : A => Ret (f x)))
            | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) (fun x0 : A => Ret (f x0)))
            end); remember (observe (raiseUB x)).

    assert (go i ≅
           match observe t with
           | RetF r => Ret (f r)
           | TauF t => Tau (ITree.bind t (fun x : A => Ret (f x)))
           | @VisF _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) (fun x0 : A => Ret (f x0)))
           end). rewrite Heqi; rewrite <- itree_eta; reflexivity.
    clear Heqi.
    rewrite itree_eta; unfold raiseUB; rewrite bind_trigger.
    gstep.

    revert t H.
    induction H0; inv Heqi0.
    - dependent destruction H1.
      dependent destruction H2.
      cbn in *. inv H0. intros.
      destruct (observe t); eapply eqit_inv in H; inv H.
      destruct H0 as (?&?). destruct H.
      constructor. intros. inv v.
    - intros t TAU.
      destruct (observe t); eapply eqit_inv in TAU; try solve [inv TAU].
      cbn in *. assert (t1 ≈ raiseUB x). { pstep; eauto. }
      clear H0.
      assert (t1 ≅ ITree.map f t0). { punfold TAU; pstep; unfold ITree.map; eauto. }
      clear TAU.
      rewrite H0 in H1.
      specialize (IHeqitF eq_refl).
      setoid_rewrite <- unfold_bind in IHeqitF.
      constructor; eauto. eapply IHeqitF; rewrite <- itree_eta; eauto.
  Qed.


  Lemma raiseUB_ret_inv_itree :
      forall A x (y : A),
        ~ (raiseUB (E:=E) x) ≈ (ret y).
  Proof using.
    intros A x y.
    intros CONTRA.
    cbn in CONTRA.
    pinversion CONTRA.
  Qed.

  #[global] Instance RaiseBindM_UB : RaiseBindM (itree E) string (fun T => raiseUB) :=
    { rbm_raise_bind := raiseUB_bind_itree;
      rbm_raise_ret_inv := raiseUB_ret_inv_itree;
    }.
End UB.
