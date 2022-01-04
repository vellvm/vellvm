(* begin hide *)
Require Import String.

From ITree Require Import
     ITree
     Basics
     Basics.HeterogeneousRelations
     Eq.Eq.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics
     Semantics.MemoryAddress
     Semantics.GepM
     Semantics.Memory.Sizeof
     Semantics.Memory.MemBytes
     Semantics.LLVMParams
     Semantics.Lang
     Handlers.OOM.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.EitherMonad
     Structures.Functor.


From Coq Require Import Relations RelationClasses.
(* end hide *)

Module Make (LP : LLVMParams) (LLVM : Lang LP).
  Import LP.
  Import LLVM.
  Import LLVM.MEM.

  Import DV.
  Import LLVM.SP.SER.

  (* Refinement relation for uvalues *)
  (* Definition 5.6 UValue refinement *)
  Variant refine_uvalue: uvalue -> uvalue -> Prop :=
    | UndefPoison: forall dt uv uv1, concretize uv1 (DVALUE_Poison dt) -> uvalue_has_dtyp uv dt -> refine_uvalue uv1 uv
    | RefineConcrete: forall uv1 uv2, (forall (dv:dvalue), concretize uv2 dv -> concretize uv1 dv) -> refine_uvalue uv1 uv2
  .
  #[export] Hint Constructors refine_uvalue : core.

  Definition uvalue_eq (uv1 uv2 : uvalue) : Prop
    := refine_uvalue uv1 uv2 /\ refine_uvalue uv2 uv1.

  Global Instance refine_uvalue_Reflexive : Reflexive refine_uvalue.
  Proof.
    repeat intro.
    destruct x; (apply RefineConcrete; solve [auto]).
  Qed.

  Global Instance uvalue_eq_Reflexive : Reflexive uvalue_eq.
  Proof.
    repeat intro.
    split; reflexivity.
  Qed.

  Lemma refine_uvalue_dtyp :
    forall uv1 uv2 dt,
      uvalue_has_dtyp uv1 dt ->
      refine_uvalue uv1 uv2 ->
      uvalue_has_dtyp uv2 dt.
  Proof.
    intros uv1 uv2 dt DTYP REF.
    induction DTYP.
    - inversion REF; subst.
  Admitted.

  Global Instance refine_uvalue_Transitive : Transitive refine_uvalue.
  Proof.
    repeat intro.
    inversion H; subst.
    - (* x concretizes to poison *)
      eapply UndefPoison; eauto.
      eapply refine_uvalue_dtyp; eauto.
    - (* x may not be poison  *)
      inversion H0; subst.
      + (* y is poison *)
        pose proof (H1 (DVALUE_Poison dt)) as POISON.
        forward POISON.
        auto.

        (* x refines to poison... *)
        eapply UndefPoison; eauto.
      + constructor.
        auto.
  Qed.

  Global Instance uvalue_eq_Transitive : Transitive uvalue_eq.
  Proof.
    intros x y z [Rxy Ryx] [Ryz Rzy].
    split; etransitivity; eauto.
  Qed.

  Global Instance uvalue_eq_Symmetric : Symmetric uvalue_eq.
  Proof.
    intros x y [Rxy Ryx].
    split; auto.
  Qed.

  Global Instance uvalue_eq_Equivalence : Equivalence uvalue_eq.
  Proof.
    split.
    - apply uvalue_eq_Reflexive.
    - apply uvalue_eq_Symmetric.
    - apply uvalue_eq_Transitive.
  Qed.

  (* TODO: move this? *)
  Ltac red_concretize :=
    unfold concretize, concretize_u; rewrite concretize_uvalueM_equation.
  Ltac red_concretize_in H :=
    unfold concretize, concretize_u in H; rewrite concretize_uvalueM_equation in H.

  Ltac normalize_array_vector_dtyp :=
    match goal with
    | H : _ |- dvalue_has_dtyp _ (DTYPE_Array (BinNat.N.of_nat) _) =>
        idtac
    | H : _ |- dvalue_has_dtyp _ (DTYPE_Array ?sz _) =>
        rewrite <- (Nnat.N2Nat.id sz)
    | H : _ |- dvalue_has_dtyp _ (DTYPE_Vector (BinNat.N.of_nat) _) =>
        idtac
    | H : _ |- dvalue_has_dtyp _ (DTYPE_Vector ?sz _) =>
        rewrite <- (Nnat.N2Nat.id sz)
    end.

  Hint Resolve forall_repeat_true : DVALUE_HAS_DTYP.
  Hint Constructors dvalue_has_dtyp : DVALUE_HAS_DTYP.
  Hint Rewrite Nnat.Nat2N.id : DVALUE_HAS_DTYP.
  Hint Resolve List.repeat_length : DVALUE_HAS_DTYP.

  Ltac solve_dvalue_has_dtyp :=
    try normalize_array_vector_dtyp;
    solve [autorewrite with DVALUE_HAS_DTYP; auto with DVALUE_HAS_DTYP].

  Ltac solve_concretize :=
    red_concretize; cbn; subst; solve_dvalue_has_dtyp.

  Ltac invert_concretize H :=
    red_concretize_in H; cbn in H; subst; inversion H; subst; auto.


  Lemma refine_uvalue_concrete :
    forall dt uv uvr,
      is_concrete uv = true ->
      (* Need this to rule out bogus integer sizes *)
      uvalue_has_dtyp uv dt ->
      is_supported dt ->
      refine_uvalue uv uvr ->
      uv = uvr.
  Proof.
    intros dt uv uvr CONC DTYP SUP_DTYP REF.
    induction uv;
      cbn in CONC;
      try solve [inversion CONC].
    - inversion REF; subst.
      + red_concretize_in H; inversion H.
      + remember (uvalue_to_dvalue uvr) as edvr;
          destruct uvr; cbn in Heqedvr;
          try match goal with
              | DV : _ = inr ?dv |- _ =>
                  specialize (H dv)
              end;
          try solve [forward H; [solve_concretize| invert_concretize H]
            ].

        -- pose proof REF as DTYP';
           eapply refine_uvalue_dtyp in DTYP'; eauto;
           inversion DTYP'; subst;

           inversion SUP_DTYP;
           match goal with
           | Ht : ?dt = dt |- _ =>
               remember (default_dvalue_of_dtyp dt) as DEF eqn:HDEF;
               cbn in HDEF
           end;
             try solve [
                 match goal with
                 | HDEF : _ = inr ?def |- _ =>
                     specialize (H def)
                 end;
                 forward H; [solve_concretize | invert_concretize H]
               | subst;
                 pose proof (ADDR.different_addrs a) as (b & DIFF_ADDR);
                 specialize (H (DVALUE_Addr b));
                 forward H;
                 [red_concretize; cbn; constructor|];

                 red_concretize_in H; inversion H;
                 subst; contradiction
               ].

           ++ break_match_hyp.

              Set Nested Proofs Allowed.
              Lemma is_supported_has_default_dvalue :
                forall dt,
                  is_supported dt ->
                  exists dv, default_dvalue_of_dtyp dt = inr dv.
              Proof.
                induction dt; intros SUPPORTED;
                  try
                    solve
                    [ inversion SUPPORTED; eexists; cbn; subst; reflexivity
                    | inversion SUPPORTED; subst;
                      destruct IHdt; eauto;
                      eexists; cbn; rewrite H; auto
                    ].

                - inversion SUPPORTED; subst.
                  induction fields.
                  + cbn; eexists; auto.
                  + match goal with
                    | H: List.Forall is_supported _ |- _ =>
                        let SUP_a := fresh SUP_a in
                        let SUP_fields := fresh SUP_fields in
                        apply List.Forall_cons_iff in H; destruct H as [SUP_a SUP_fields]
                    end.

                    pose proof H a as A; destruct A; cbn; auto.
                    rewrite H0.

                    cbn in IHfields.
                    destruct IHfields; eauto.
                    intros.
                    apply H; cbn; auto.
                    constructor; auto.
                    break_inner_match; inversion H1.
                    eexists. reflexivity.
                - inversion SUPPORTED; subst.
                  induction fields.
                  + cbn; eexists; auto.
                  + match goal with
                    | H: List.Forall is_supported _ |- _ =>
                        let SUP_a := fresh SUP_a in
                        let SUP_fields := fresh SUP_fields in
                        apply List.Forall_cons_iff in H; destruct H as [SUP_a SUP_fields]
                    end.

                    pose proof H a as A; destruct A; cbn; auto.
                    rewrite H0.

                    cbn in IHfields.
                    destruct IHfields; eauto.
                    intros.
                    apply H; cbn; auto.
                    constructor; auto.
                    break_inner_match; inversion H1.
                    eexists. reflexivity.
                - inversion SUPPORTED; subst.
                  destruct IHdt; eauto.
                  cbn.
                  destruct dt; inversion H1; inversion H2; subst; cbn;
                  eexists; try reflexivity.
                  cbn in H.
              Qed.
              --- 
              
           
           ++ inversion H0; try rewrite <- H3 in HDEF; cbn in HDEF.
              all:
                try
                  (match goal with
                   | HDEF : _ = inr ?def |- _ =>
                       specialize (H def)
                   end;
                   forward H; [solve_concretize | invert_concretize H]).

              rewrite <- H4 in HDEF; cbn in HDEF.
              --- 
                 match goal with
                 | HDEF : _ = inr ?def |- _ =>
                     specialize (H def)
                 end;
                 forward H; [solve_concretize | invert_concretize H].

               | subst;
                 pose proof (ADDR.different_addrs a) as (b & DIFF_ADDR);
                 specialize (H (DVALUE_Addr b));
                 forward H;
                 [red_concretize; cbn; constructor|];

                 red_concretize_in H; inversion H;
                 subst; contradiction
                                 ].
                             cbn.


              cbn in HDEF.
              subst.
              subst.
              subst.
              ---  
             break_match_hyp.
             --- admit.
             --- admit.
  Admitted.

  Infix"×" := prod_rel (at level 90, left associativity).

  Definition TT {A} : relation A := fun _ _ => True.

  Global Instance TT_Reflexive {A} : Reflexive (@TT A).
  Proof.
    intro.
    reflexivity.
  Qed.

  Global Instance TT_Transitive {A} : Transitive (@TT A).
  Proof.
    intro.
    auto.
  Qed.

  Global Instance TT_Symmetric {A} : Symmetric (@TT A).
  Proof.
    intro.
    auto.
  Qed.

  Global Instance TT_Equivalence {A} : Equivalence (@TT A).
  Proof.
    split; typeclasses eauto.
  Qed.

  (* Lemma 5.7 - uses this definition of refinement 
   note that refine_uvalue is the basic Uvalue refinement given by Definition 5.6 *)
  (* Refinement of uninterpreted mcfg *)
  Definition refine_L0: relation (itree L0 uvalue) := eutt refine_uvalue.

  (* Refinement of mcfg after globals *)
  Definition refine_res1 : relation (global_env * uvalue)
    := TT × refine_uvalue.

  Definition refine_L1 : relation (itree L1 (global_env * uvalue))
    := eutt refine_res1.

  (* Refinement of mcfg after locals *)
  Definition refine_res2 : relation (local_env * lstack * (global_env * uvalue))
    := TT × refine_res1.

  Definition refine_L2 : relation (itree L2 (local_env * stack * (global_env * uvalue)))
    := eutt refine_res2.

  (* For multiple CFG, after interpreting [LocalE] and [MemoryE] and [IntrinsicE] that are memory intrinsics *)
  Definition refine_res3 : relation (MemState * (local_env * stack * (global_env * uvalue)))
    := TT × refine_res2.

  Definition refine_L3 : relation (itree L3 (MemState * (local_env * stack * (global_env * uvalue))))
    := eutt refine_res3.

  (* Refinement for after interpreting pick. *)
  Definition refine_L4 : relation ((itree L4 (MemState * (local_env * stack * (global_env * uvalue)))) -> Prop)
    := fun ts ts' => forall t', ts' t' -> exists t, ts t /\ eutt refine_res3 t t'.

  Inductive contains_UB {R} : itree L4 R -> Prop :=
  | CrawlTau  : forall t, contains_UB t -> contains_UB (Tau t)
  | CrawlVis1 : forall Y (e : ExternalCallE Y) x k, contains_UB (k x) -> contains_UB (vis e k)
  | CrawlVis2 : forall Y (e : (DebugE +' FailureE) Y) x k, contains_UB (k x) -> contains_UB (vis e k)
  | FindUB    : forall s, contains_UB (raiseUB s).

  Definition refine_L5 : relation ((itree L4 (MemState * (local_env * stack * (global_env * uvalue)))) -> Prop)
    := fun ts ts' =>
         (* For any tree in the target set *)
         forall t', ts' t' ->
               (* There is a tree in the source set that either
                  exhibits UB, or is eutt our target tree *)
               exists t, ts t /\ (contains_UB t \/ eutt refine_res3 t t').

  Definition refine_L6 : relation ((itree L4 (MemState * (local_env * stack * (global_env * uvalue)))) -> Prop)
    := fun ts ts' =>
         forall t', ts' t' ->
               exists t, ts t /\ (contains_UB t \/ refine_OOM_h refine_res3 t t').

  (* Instance Transitive_refine_L6 : Transitive refine_L6. *)
  (* Proof. *)
  (*   unfold Transitive. *)
  (*   intros x y z XY YZ. *)

  (*   unfold refine_L6 in *. *)
  (*   intros t' zt'. *)

  (*   specialize (YZ  t' zt') as (t'' & yt'' & yref). *)
  (*   specialize (XY t'' yt'') as (t''' & xt''' & xref). *)
  (*   exists t'''; split; auto. *)

  (*   destruct xref as [UBX | REF_OOMX]; auto. *)
  (*   right. *)

  (*   destruct yref as [UBY | REF_OOMY]. *)

  (*   apply eutt_refine_oom_h; try typeclasses eauto. *)
  (* Qed. *)

End Make.
