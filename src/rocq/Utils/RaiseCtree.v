From Stdlib Require Import
     String
     Morphisms.

From ExtLib Require Import
  Structures.Monads
  Data.Monads.EitherMonad
  Data.Monads.IdentityMonad.

Unset Universe Checking.
From Vellvm Require Import 
  Semantics.LLVMEvents
  Utils.Tactics
  Utils.Raise
  Utils.Error
  Utils.CTreeUtils.

Unset Universe Checking.
From CTree Require Import
  CTree CTreeDefinitions Eq.

Require Import Stdlib.Program.Equality.

Require Import Paco.paco.

Import MonadNotation.
Open Scope monad.


(* TODO: Move this *)
Definition raise {E B} {A} `{FailureE -< E} (msg : String.string) : ctree E B A :=
  (v <- trigger (Throw (print_msg msg));; match v: void with end)%monad.

(* TODO: Move this *)
#[global] Instance RAISE_ERR_CTREE_FAILUREE {E B : Type -> Type} `{FailureE -< E} : RAISE_ERROR (ctree E B) :=
  { raise_error := fun A e => raise e
  }.

(* TODO: Move this *)
Definition raiseUB {E B} {A} `{UBE -< E} (msg : String.string) : ctree E B A :=
  v <- trigger (ThrowUB (print_msg msg));; match v: void with end.

(* TODO: Move this *)
#[global] Instance RAISE_UB_CTREE_FAILUREE {E B : Type -> Type} `{UBE -< E} : RAISE_UB (ctree E B) :=
  { raise_ub := fun A e => raiseUB e
  }.

(* TODO: Move this *)
Definition raiseOOM {E B} {A} `{OOME -< E} (msg : String.string) : ctree E B A :=
  v <- trigger (ThrowOOM (print_msg msg));; match v: void with end.

(* TODO: Move this *)
#[global] Instance RAISE_OOM_CTREE_FAILUREE {E B : Type -> Type} `{OOME -< E} : RAISE_OOM (ctree E B) :=
  { raise_oom := fun A e => raiseOOM e
  }.

(* #[global] Instance Reflexive {F X} : Reflexive (@update_val_rel F F X X eq eq). *)
(* red. *)
(* intros x. *)
(* Set Printing Implicit. *)
(* apply update_val_rel_eq; eauto. *)
(* - destruct x; cbn. *)
(*   + apply wf_val_nonval. *)
(*     apply is_val_τ. *)
(*   + apply wf_val_nonval. *)
(*     apply is_val_obs. *)
(*   + eapply wf_val_val. *)
(*     apply is_val_obs. *)
(* -destruct x; try constructor; eauto. *)
(* constructor. *)
(* apply update_val_rel_eq; eauto. *)
(* Qed. *)

Section Failure.
  Variable E : Type -> Type.
  Variable B : Type -> Type.
  Context {FAIL : FailureE -< E}.

  Lemma raise_bind_ctree :
    forall X Y (f : X -> ctree E B Y) x,
      bind (raise x) f ~ (raise x : ctree E B Y).
  Proof using.
    intros X Y f x.
    cbn.
    rewrite bind_bind.
    eapply sbisim_clo_bind_eq; [|intros []].
    reflexivity.
  Qed.

  Lemma raise_map_ctree :
    forall X Y (f : X -> Y) x,
      CTree.map f (@raise _ _ _ FAIL x : ctree E B X) ~ (raise x : ctree E B Y).
  Proof using.
    intros X Y f x.
    unfold raise.
    setoid_rewrite map_bind.
    eapply sbisim_clo_bind_eq.
    reflexivity.
    intros [].
  Qed.

  Lemma raise_map_ctree_inv :
    forall X Y (f : X -> Y) (t : ctree E B X) x,
      CTree.map f t ~ (@raise _ _ _ FAIL x : ctree E B Y) ->
      t ~ (raise x : ctree E B X).
  Proof using.
    intros X Y f t x H.
    unfold CTree.map in *.
  Admitted.

  Lemma raise_ret_inv_ctree :
      forall A x (y : A),
        ~ (@raise _ _ _ FAIL x : ctree E B A) ~ (ret y : ctree E B A).
  Proof using.
    intros A x y.
    intros CONTRA.
    symmetry in CONTRA.
    unfold raise in CONTRA.
    setoid_rewrite bind_trigger in CONTRA.
    apply sbisim_ret_vis_inv in CONTRA.
    auto.
  Qed.

  #[global] Instance RaiseBindM_Fail : RaiseBindM (ctree E B) string (fun T => raise) :=
    { rbm_raise_bind := raise_bind_ctree;
      rbm_raise_ret_inv := raise_ret_inv_ctree;
    }.
End Failure.

Section OOM.
  Variable E : Type -> Type.
  Variable B : Type -> Type.
  Context {OOM : OOME -< E}.

  Lemma raiseOOM_bind_ctree :
    forall X Y (f : X -> ctree E B Y) x,
      bind (raiseOOM x) f ~ (raiseOOM x : ctree E B Y).
  Proof using.
    intros X Y f x.
    cbn.
    rewrite bind_bind.
    eapply sbisim_clo_bind_eq; [|intros []].
    reflexivity.
  Qed.

  Lemma raiseOOM_map_ctree :
    forall X Y (f : X -> Y) x,
      CTree.map f (@raiseOOM _ _ _ OOM x : ctree E B X) ~ (raiseOOM x : ctree E B Y).
  Proof using.
    intros X Y f x.
    unfold raise.
    setoid_rewrite map_bind.
    eapply sbisim_clo_bind_eq.
    reflexivity.
    intros [].
  Qed.

  Lemma raiseOOM_map_ctree_inv :
    forall X Y (f : X -> Y) (t : ctree E B X) x,
      CTree.map f t ~ (@raiseOOM _ _ _ OOM x : ctree E B Y) ->
      t ~ (raiseOOM x : ctree E B X).
  Proof using.
    intros X Y f t x H.
    unfold CTree.map in *.
  Admitted.

  Lemma raiseOOM_ret_inv_ctree :
      forall A x (y : A),
        ~ (@raiseOOM _ _ _ OOM x : ctree E B A) ~ (ret y : ctree E B A).
  Proof using.
    intros A x y.
    intros CONTRA.
    symmetry in CONTRA.
    unfold raise in CONTRA.
    setoid_rewrite bind_trigger in CONTRA.
    apply sbisim_ret_vis_inv in CONTRA.
    auto.
  Qed.

  #[global] Instance RaiseBindM_OOM : RaiseBindM (ctree E B) string (fun T => raiseOOM) :=
    { rbm_raise_bind := raiseOOM_bind_ctree;
      rbm_raise_ret_inv := raiseOOM_ret_inv_ctree;
    }.
End OOM.

Section UB.
  Variable E : Type -> Type.
  Variable B : Type -> Type.
  Context {UB : UBE -< E}.

  Lemma raiseUB_bind_ctree :
    forall X Y (f : X -> ctree E B Y) x,
      bind (raiseUB x) f ~ (raiseUB x : ctree E B Y).
  Proof using.
    intros X Y f x.
    cbn.
    rewrite bind_bind.
    eapply sbisim_clo_bind_eq; [|intros []].
    reflexivity.
  Qed.

  Lemma raiseUB_map_ctree :
    forall X Y (f : X -> Y) x,
      CTree.map f (@raiseUB _ _ _ UB x : ctree E B X) ~ (raiseUB x : ctree E B Y).
  Proof using.
    intros X Y f x.
    unfold raise.
    setoid_rewrite map_bind.
    eapply sbisim_clo_bind_eq.
    reflexivity.
    intros [].
  Qed.

  Lemma raiseUB_map_ctree_inv :
    forall X Y (f : X -> Y) (t : ctree E B X) x,
      CTree.map f t ~ (@raiseUB _ _ _ UB x : ctree E B Y) ->
      t ~ (raiseUB x : ctree E B X).
  Proof using.
    intros X Y f t x H.
    unfold CTree.map in *.
  Admitted.

  Lemma raiseUB_ret_inv_ctree :
      forall A x (y : A),
        ~ (@raiseUB _ _ _ UB x : ctree E B A) ~ (ret y : ctree E B A).
  Proof using.
    intros A x y.
    intros CONTRA.
    symmetry in CONTRA.
    unfold raise in CONTRA.
    setoid_rewrite bind_trigger in CONTRA.
    apply sbisim_ret_vis_inv in CONTRA.
    auto.
  Qed.

  #[global] Instance RaiseBindM_UB : RaiseBindM (ctree E B) string (fun T => raiseUB) :=
    { rbm_raise_bind := raiseUB_bind_ctree;
      rbm_raise_ret_inv := raiseUB_ret_inv_ctree;
    }.
End UB.

  Definition lift_err_ub_oom_ctree {X Y} {E B} `{FailureE -< E} `{UBE -< E} `{OOME -< E} (f : X -> ctree E B Y) (m:err_ub_oom X) : ctree E B Y :=
    match m with
    | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
        match m with
        | inl (OOM_message x) => raiseOOM x
        | inr (inl (UB_message x)) => raiseUB x
        | inr (inr (inl (ERR_message x))) => raise x
        | inr (inr (inr x)) => f x
      end
    end.
