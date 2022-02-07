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
        eexists; try reflexivity;
        repeat
          match goal with
          | H : exists n, _ |- _ =>
              destruct H as (n & Ht)
          | H : _ \/ _ |- _
            => destruct H as [Ht | Ht]
          end; try inversion Ht.

      Unshelve.
      all: eapply DVALUE_None.
  Qed.

  (*
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
      + (* Concretizes to poison... UVALUE_Addr can never concretize
           to poison, so this case can be dismissed. *)
        red_concretize_in H; inversion H.
      + (* If uvr can be concretized to a dvalue dv, then UVALUE_Addr
           a can also be concretized to dv *)

        (* The only dvalue that we should be able to concretize to is
           the one given by uvalue_to_dvalue... *)
        remember (uvalue_to_dvalue uvr) as edvr;
          destruct uvr; cbn in Heqedvr;
          try match goal with
              | DV : _ = inr ?dv |- _ =>
                  specialize (H dv)
              end;
          try solve [forward H; [solve_concretize| invert_concretize H]
            ];

          pose proof REF as DTYP';
          eapply refine_uvalue_dtyp in DTYP'; eauto;
          inversion DTYP; subst;
          inversion DTYP'; subst;

          try solve [
              pose proof (ADDR.different_addrs a) as (b & DIFF_ADDR);
              specialize (H (DVALUE_Addr b));
              forward H;
              [red_concretize; cbn; constructor|];
              red_concretize_in H; inversion H;
              subst; contradiction
            ].

        -- (*
             In our hypothesis we have that a GEP expression is a
             refinement of an Addr.

             In this branch of the proof GEP is a refinement because
             for every dvalue that the GEP concretizes to, the Addr
             also concretizes to that dvalue...

             UVALUE_Addr a can only concretize to DVALUE_Addr a.

             Can UVALUE_GetElementPtr t uvr idxs always concretize to
             DVALUE_Addr a?

             
            *)
          induction idxs.
          
          pose proof (ADDR.different_addrs a) as (b & DIFF_ADDR).
          specialize (H (DVALUE_Addr b)).
          forward H.

          unfold concretize, concretize_u; rewrite concretize_uvalueM_equation.
          cbn.

          Set Nested Proofs Allowed.
          Lemma concretize_ibinop_inv:
            forall op x y dv,
              concretize
              concretize_succeeds (UVALUE_IBinop op x y) ->
              concretize (UVALUE_IBinop op x y) dv ->
              exists dx dy,
                concretize_succeeds x /\
                  concretize x dx /\
                  concretize_succeeds y /\
                  concretize y dy /\
                  @eval_iop err_ub_oom _ _ _ _ op dx dy = ret dv.
          Proof.
            

            da <- concretize_uvalueM ua;;
            dvs <- map_monad concretize_uvalueM uvs;;
            match handle_gep t da dvs with
            | inr dv  => ret dv
            | inl err => lift_ue (raise_error err)
            end

          Qed.

          
          (* uvr is the thing being indexed... *)

          red_concretize.
          cbn.
            [red_concretize; cbn; constructor|];
            red_concretize_in H; inversion H;
            subst; contradiction


          
           subst.
        -- (* Case where uvr = undef *)
          pose proof REF as DTYP';
            eapply refine_uvalue_dtyp in DTYP'; eauto;
            inversion DTYP; subst;
            inversion DTYP'; subst;

            try solve [
                remember (default_dvalue_of_dtyp DTYPE_Pointer) as DEF eqn:HDEF;          
                subst;
                pose proof (ADDR.different_addrs a) as (b & DIFF_ADDR);
                specialize (H (DVALUE_Addr b));
                forward H;
                [red_concretize; cbn; constructor|];
                red_concretize_in H; inversion H;
                subst; contradiction
              ].
        --  pose proof REF as DTYP';
            eapply refine_uvalue_dtyp in DTYP'; eauto.
            inversion DTYP; subst.
            inversion DTYP'; subst.


          remember (default_dvalue_of_dtyp DTYPE_Pointer) as DEF eqn:HDEF;          
            subst;
            pose proof (ADDR.different_addrs a) as (b & DIFF_ADDR);
            specialize (H (DVALUE_Addr b));
            forward H;
            [red_concretize; cbn; constructor|];
            
            red_concretize_in H; inversion H;
            subst; contradiction.

  Admitted. *)

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

  Inductive contains_UB' {R} (CUB : itree L4 R -> Prop) : itree' L4 R -> Prop :=
  | CrawlTau  : forall t, CUB t -> contains_UB' CUB (TauF t)
  | CrawlVis1 : forall Y (e : ExternalCallE Y) x (k : Y -> itree L4 R), CUB (k x) -> contains_UB' CUB (VisF (subevent _ e) k)
  | CrawlVis2 : forall Y (e : (DebugE +' FailureE) Y) x (k : Y -> itree L4 R), CUB (k x) -> contains_UB' CUB (VisF (subevent _ e) k)
  | FindUB    : forall s k, contains_UB' CUB (VisF (subevent _ (ThrowUB s)) k).

  Require Import Morphisms.
  Require Import Paco.paco.

  Definition contains_UB {R} : itree L4 R -> Prop
    := paco1 (fun CUB t => contains_UB' CUB (observe t)) bot1.
  Hint Unfold contains_UB : Core.

  Lemma contains_UB_mon {R} : monotone1 (fun (CUB : rel1 (itree L4 R)) (t : itree L4 R) => contains_UB' CUB (observe t)).
  Proof.
    unfold monotone1.
    intros x0 r r' IN LE.
    induction (observe x0).
    - inversion IN.
    - inversion IN; subst; constructor; eauto.
    - inversion IN;
        try apply inj_pair2 in H1;
        try apply inj_pair2 in H2;
        subst;
        try econstructor; eauto.

      apply inj_pair2 in H1.
      apply inj_pair2 in H2.
      subst.

      econstructor.
  Qed.
  Hint Resolve contains_UB_mon : paco.

  (* TODO: move this *)
  Lemma eqitree_inv_Tau_l {E R} (t t' : itree E R) :
    Tau t ≅ t' -> exists t0, observe t' = TauF t0 /\ t ≅ t0.
  Proof.
    intros; punfold H; inv H; try inv CHECK; pclearbot; eauto.
  Qed.

  Lemma contains_UB_tau {R} (t : itree L4 R):
    contains_UB t <-> contains_UB (Tau t).
  Proof.
    split; intros UB.
    { pfold.
      punfold UB.
      constructor.
      left.
      pfold.
      apply UB.
    }

    { pfold.
      pinversion UB; subst.
      punfold H0.
    }
  Qed.

  Ltac inv_existT :=
    repeat match goal with
           | H: existT _ _ _ = existT _ _ _ |- _ =>
               apply inj_pair2 in H; inversion H; subst
           end.

  Ltac inv_contains_UB :=
    match goal with
    | UB : contains_UB ?x,
        H : _ = observe ?x |- _ =>
        punfold UB; rewrite <- H in UB;
        inversion UB; subst
    | UB : contains_UB ?x
      |- _ =>
        punfold UB;
        inversion UB; subst
    end.

  Ltac pfold_contains_UB :=
    match goal with
    | H : _ = observe ?y |- paco1 _ _ ?y =>
        pfold; rewrite <- H
    end.

  Instance proper_eq_itree_contains_UB {R : Type} {RR : relation R} :
    Proper (@eq_itree _ R R RR ==> iff) contains_UB.
  Proof.
    unfold Proper, respectful.
    intros x y EQ.
    split.
    { generalize dependent RR.
      generalize dependent y.
      generalize dependent x.
      pcofix CIH.
      intros x y RR EQ UB.

      (*
      pinversion EQ.
      admit.
      - inv_contains_UB.
        pclearbot.
        pfold.
        punfold H2.
        rewrite <- H.
        constructor. right.
        eapply CIH.
        apply REL.
        red.
        pfold.
        apply H2.
       *)
      
      pinversion EQ; subst;
        inv_contains_UB;
        inv_existT;
        try solve [
            pclearbot;
            pfold_contains_UB;
            econstructor; right; eauto
          ];
        inversion CHECK.
    }

    { generalize dependent RR.
      generalize dependent x.
      generalize dependent y.
      pcofix CIH.
      intros x y RR EQ UB.
      pinversion EQ; subst;
        inv_contains_UB;
        inv_existT;
        try solve [
            pclearbot;
            pfold_contains_UB;
            econstructor; right; eauto
          ];
        inversion CHECK.
    }
  Qed.

  Lemma ret_not_contains_UB {R} {RR : relation R} :
    forall t rv a b, eqit RR a b t (ret rv) -> ~ contains_UB t.
  Proof.
    intros t rv a b EQ CUB.
    punfold EQ.
    unfold eqit_ in EQ.
    punfold CUB.
    remember (observe t) as to.
    remember (observe (ret rv)) as ro.
    revert t Heqto Heqro.
    induction EQ; intros t TO RO; inversion TO; inversion RO; subst.
    - inversion CUB.
    - eapply IHEQ.
      + inversion CUB; subst; pclearbot.
        punfold H2.
      + reflexivity.
      + reflexivity.
  Qed.

  Instance proper_contains_UB {R} {RR : relation R} : Proper (eutt RR ==> iff) contains_UB.
  Proof.
    unfold Proper, respectful.
    intros x y EQ.
    split.
    { generalize dependent RR.
      generalize dependent y.
      generalize dependent x.
      pcofix CIH.
      intros x y RR EQ UB.

      pinversion EQ; subst;
        inv_contains_UB;
        inv_existT;
        pclearbot;
        try solve [
            pfold_contains_UB;
            econstructor; right; eauto
          ].

      - (* Left tau, nothing about y *)
        clear UB.
        punfold H1.

        genobs y yo.
        genobs t1 t1o.

        (* revert H0. *)
        clear H0.
        revert t1 Heqt1o Heqyo.
        pfold.

        induction REL; intros t1' Heqt1o Heqyo; pose proof True as H0; inversion Heqt1o; inversion Heqyo; subst.
        + inversion H1.
        + inversion H1; subst; pclearbot.
          constructor.
          right.
          rewrite H2 in H1.
          eapply CIH.
          2: pfold; apply H1.

          do 2 red.

          punfold REL.
          red in REL.
          pfold.
          red.
          rewrite <- H2.
          constructor.
          constructor.
          eauto.
        + inversion H1; subst; inv_existT; subst; pclearbot;
            econstructor; right; eauto.
        + inversion H1; subst; pclearbot.
          punfold H4.
        + constructor.
          right.
          eapply CIH; eauto.
          pfold.
          auto.
      - (* Left and right tau *)
        pfold_contains_UB.
        constructor; right; eapply CIH;
          pfold; eauto.
      - (* Right tau, external call on the left *)
        pfold_contains_UB.
        constructor; right; eapply CIH;
          pfold; eauto.
      - (* Right tau, debug or failure event on the left *)
        pfold_contains_UB.
        constructor; right; eapply CIH;
          pfold; eauto.
      - (* UB *)
        pfold.
        rewrite <- H1.
        constructor.
        right.
        eapply CIH.
        do 2 red.
        pfold.
        red.
        apply REL.
        pfold.
        auto.
    }

    { generalize dependent RR.
      generalize dependent x.
      generalize dependent y.
      pcofix CIH.
      intros y x RR EQ UB.

      pinversion EQ; subst;
        inv_contains_UB;
        inv_existT;
        pclearbot;
        try solve [
            pfold_contains_UB;
            econstructor; right; eauto
          ].

      - (* Left and right tau *)
        pfold_contains_UB.
        constructor; right; eapply CIH;
          pfold; eauto.
      - (* Left tau, external call on the right *)
        pfold_contains_UB.
        constructor; right; eapply CIH;
          pfold; eauto.
      - (* Left tau, debug or failure on the right *)
        pfold_contains_UB.
        constructor; right; eapply CIH;
          pfold; eauto.
      - (* UB *)
        pfold_contains_UB.
        constructor; right; eapply CIH;
          pfold; eauto.
      - (* Left tau, nothing about x on the right. *)
        clear UB.
        punfold H0.

        genobs x xo.
        genobs t2 t2o.

        (* revert H0. *)
        clear H1.
        revert t2 Heqt2o Heqxo.
        pfold.

        induction REL; intros t2' Heqt2o Heqxo; pose proof True as H1; inversion Heqt2o; inversion Heqxo; subst.
        + inversion H0.
        + inversion H0; subst; pclearbot.
          constructor.
          right.
          rewrite H2 in H0.
          eapply CIH.
          2: pfold; apply H0.

          do 2 red.

          punfold REL.
          red in REL.
          pfold.
          red.
          rewrite <- H2.
          constructor.
          constructor.
          eauto.
        + inversion H0; subst; inv_existT; subst; pclearbot;
            econstructor; right; eauto.
        + constructor.
          right.
          eapply CIH; eauto.
          pfold.
          auto.
        + inversion H0; subst; pclearbot.
          punfold H4.
    }
  Qed.

  Instance proper_refine_OOM_h {R} {RR : relation R} : Proper (refine_OOM_h RR ==> flip impl) contains_UB.
  Proof.
    unfold Proper, respectful.
    intros x y REF.
    unfold refine_OOM_h in REF.
  Admitted.

  Lemma contains_UB_eutt :
    forall R (RR : relation R) t1 t2,
      contains_UB t1 ->
      eutt RR t2 t1 ->
      contains_UB t2.
  Proof.
    intros R RR t1 t2 UB EQ.
    rewrite EQ.
    eauto.
  Qed.

  Lemma contains_UB_refine_OOM_h :
    forall R (RR : relation R) x y,
      contains_UB y ->
      refine_OOM_h RR x y ->
      contains_UB x.
  Proof.
    intros R RR x y UB REF.
    rewrite REF.
    eauto.
  Qed.

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

  Instance Transitive_refine_L5 : Transitive refine_L5.
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
        left. eapply contains_UB_eutt; eauto.
    - specialize (XY ry TY).
      destruct XY as (rx & TX & [UB_rx | XY]).

      + (* UB in tx *)
        exists rx; split; auto.
      + exists rx; split; auto.
        right. rewrite XY. eauto.
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
  Qed.

End Make.
