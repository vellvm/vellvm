From Equations Require Import Equations.

From Stdlib Require Import Lia Logic.ProofIrrelevance.

From ExtLib Require Import Structures.Monads.

From ITree Require Import
  ITree Eq HeterogeneousRelations.
From Vellvm Require Import
  Utils
  Syntax
  Semantics
  VellvmIntegers
  Integers
  Interfaces.IPtr
  Interfaces.Params
  Implementations.Pointer
  Implementations.Provenance
  Implementations.IPtrInfinite
  Implementations.IPtrFinite
  Implementations.Memory
  Implementations.ParamsV.

From Vellvm Require Import
  Utils.rutt_cutoff
  Theory.I2F.Refinement.

From Paco Require Import paco.

Ltac rstep :=
  first [apply ruttc_trigger; eauto 10; try easy |
          apply ruttc_trigger_cast |
          apply ruttc_ret; eauto 10 
    ].
Tactic Notation "rbind" uconstr(x) := eapply ruttc_bind with (RR := x).
Tactic Notation "erbind" := eapply ruttc_bind.
Hint Resolve ruttc_ret ruttc_trigger : core.
Hint Unfold I2F_refine_MCFG : core.
Hint Unfold I2F_refine : core.
Hint Unfold I2F_Addr: core.
Hint Unfold I2F_Iptr : core.
Hint Transparent dvp : core.
Ltac cbnn := cbn; unfold resum, ReSum_id, id_, Id_IFun.
Tactic Notation "cbnn" "in" ident(h) :=
  cbn in h; unfold resum, ReSum_id, id_, Id_IFun in h.

(** [refine_dvalue_base_map] is [refine_dvalue_base_map_gen]
      (Refinement.v) at the MCFG signature. *)
Lemma refine_dvalue_base_map t1 t2 :
  I2F_refine_MCFG I2F_dvalue_base t1 t2 ->
  I2F_refine_MCFG I2F_dvalue (ITree.map DVALUE_Base t1) (ITree.map DVALUE_Base t2).
Proof. apply refine_dvalue_base_map_gen. Qed.

Hint Resolve refine_dvalue_base_map : core.

(** * Unfolding [freeze]

    [freeze] is a [Definition] whose body is one outer [fix] over the
    [dvalue] with two inner loops over the fields / elements. Reasoning
    about it by [cbn] would splice the whole outer [fix] into every goal
    (and leave the recursive calls unfolded, so no induction hypothesis
    applies). Instead we name the two inner loops here --- [freeze_fields]
    and [freeze_elts], phrased in terms of [freeze] itself --- and give
    the unfolding equations, each of which holds by conversion. All of
    [freeze]/[freeze_base]'s arguments are supplied explicitly: with a
    [Params] that is a section *variable*, resolution of the [-<]
    instances in this file's import environment diverges.

    [reflexivity] diverges on these goals for the same reason, so each
    proof hands the conversion check the right-hand side directly. *)
Section FreezeUnfold.
  Variable Pa : Params.
  Variable E : Type -> Type.
  Variables (HD : @DrawE Pa -< E) (HF : FailureE -< E) (HO : OOME -< E) (HU : UBE -< E).

  Local Notation FRZ := (@freeze Pa E HD HF HO HU).
  Local Notation FRZB := (@freeze_base Pa E HD HF HO HU).
  Local Notation RAISE := (@raise E _ HF).
  Local Notation MISMATCH := "freeze_fields: mismatched field types and values".

  (** The [DVALUE_Struct] loop: walks the values and the field types in
      lockstep, accumulating in reverse. *)
  Definition freeze_fields : list dvalue -> list dtyp -> list dvalue -> itree E (list dvalue) :=
    fix loop (dvs : list dvalue) (dts : list dtyp) (acc : list dvalue) : itree E (list dvalue) :=
      match dts, dvs with
      | [], [] => ret (rev_append acc [])
      | t::ts, v::vs => v <- FRZ t v ;; loop vs ts (v :: acc)
      | _, _ => RAISE MISMATCH
      end.

  (** The [DVALUE_Array] loop: same, at a single element type. *)
  Definition freeze_elts (t : dtyp) : list dvalue -> list dvalue -> itree E (list dvalue) :=
    fix loop (dvs : list dvalue) (acc : list dvalue) : itree E (list dvalue) :=
      match dvs with
      | [] => ret (rev_append acc [])
      | v::vs => v <- FRZ t v ;; loop vs (v :: acc)
      end.

  Lemma freeze_Base_eq : forall (dt:dtyp) (v : @dvalue_base Pa),
      FRZ dt (DVALUE_Base v) = FRZB dt v.
  Proof. intros dt v; exact (@eq_refl _ (FRZB dt v)). Qed.

  Lemma freeze_Struct_eq : forall (b:bool) (fields : list (@dvalue Pa)) (dt:dtyp),
      FRZ dt (DVALUE_Struct b fields) =
        match dt with
        | DTYPE_Struct p dts => val <- freeze_fields fields dts [] ;; ret (DVALUE_Struct p val)
        | _ => RAISE "freeze: type mismatch non-struct type"
        end.
  Proof.
    intros b fields dt.
    exact (@eq_refl _ (match dt with
        | DTYPE_Struct p dts => val <- freeze_fields fields dts [] ;; ret (DVALUE_Struct p val)
        | _ => RAISE "freeze: type mismatch non-struct type" end)).
  Qed.

  Lemma freeze_Array_eq : forall (b:bool) (elts : list (@dvalue Pa)) (dt:dtyp),
      FRZ dt (DVALUE_Array b elts) =
        match dt with
        | DTYPE_Array v sz t => val <- freeze_elts t elts [] ;; ret (DVALUE_Array v val)
        | _ => RAISE "freeze: type mismatch non-array type"
        end.
  Proof.
    intros b elts dt.
    exact (@eq_refl _ (match dt with
        | DTYPE_Array v sz t => val <- freeze_elts t elts [] ;; ret (DVALUE_Array v val)
        | _ => RAISE "freeze: type mismatch non-array type" end)).
  Qed.

  Lemma freeze_fields_nil : forall acc, freeze_fields [] [] acc = ret (rev_append acc []).
  Proof. intros acc; exact (@eq_refl _ (ret (rev_append acc []))). Qed.

  Lemma freeze_fields_nil_cons : forall t ts acc, freeze_fields [] (t::ts) acc = RAISE MISMATCH.
  Proof. intros; exact (@eq_refl _ (RAISE MISMATCH)). Qed.

  Lemma freeze_fields_cons_nil : forall v vs acc, freeze_fields (v::vs) [] acc = RAISE MISMATCH.
  Proof. intros; exact (@eq_refl _ (RAISE MISMATCH)). Qed.

  Lemma freeze_fields_cons : forall v vs t ts acc,
      freeze_fields (v::vs) (t::ts) acc = x <- FRZ t v ;; freeze_fields vs ts (x :: acc).
  Proof. intros; exact (@eq_refl _ (x <- FRZ t v ;; freeze_fields vs ts (x :: acc))). Qed.

  Lemma freeze_elts_nil : forall t acc, freeze_elts t [] acc = ret (rev_append acc []).
  Proof. intros t acc; exact (@eq_refl _ (ret (rev_append acc []))). Qed.

  Lemma freeze_elts_cons : forall t v vs acc,
      freeze_elts t (v::vs) acc = x <- FRZ t v ;; freeze_elts t vs (x :: acc).
  Proof. intros; exact (@eq_refl _ (x <- FRZ t v ;; freeze_elts t vs (x :: acc))). Qed.

End FreezeUnfold.

Arguments freeze_fields {Pa E HD HF HO HU}.
Arguments freeze_elts {Pa E HD HF HO HU}.


(** Generic [freeze]/[freeze_base], parameterized over the single event
      they trigger: [draw]. The MCFG and CFG instances then differ only in
      the [draw]-refinement fed in ([I2F_draw_MCFG] / [I2F_draw_CFG]). *)
Lemma I2F_freeze_base_gen {E1 E2}
  `{@DrawE PInf -< E1} `{FailureE -< E1} `{OOME -< E1} `{UBE -< E1}
  `{@DrawE PFin -< E2} `{FailureE -< E2} `{OOME -< E2} `{UBE -< E2}
  {Rcutl : pred1 E1} {Rcutr : pred1 E2}
  {REv : prerel E1 E2} {RAns : postrel E1 E2}
  (Hdraw : forall dt, ruttc Rcutl Rcutr REv RAns I2F_dvalue (draw dt) (draw dt))
  (dt:dtyp) (a : @dvalue_base PInf) (b : @dvalue_base PFin) :
  I2F_dvalue_base a b ->
  ruttc Rcutl Rcutr REv RAns I2F_dvalue (freeze_base dt a) (freeze_base dt b).
Proof.
  intros HDV; destruct HDV; cbn;
    try solve [ apply ruttc_ret; auto
              | apply refine_dvalue_base_map_gen; apply ruttc_ret; auto ].
  apply Hdraw.
Qed.

(* SAZ: I got claude Opus 5.0 to fix the proof of freeze. *)

(** The [FailureE] branches of [freeze]: a value/type shape mismatch
    raises on *both* sides at once (the two [dvalue]s are [I2F_dvalue]-
    related, hence of the same shape and length, and the [dtyp] is
    shared), so all we need of [REv] is that it relates [Throw] to
    [Throw] --- the same side condition [I2F_refine_lift_gen] asks for,
    discharged by [I2FE_MCFG_Throw] / [I2FE_CFG_Throw]. This is the extra
    constraint [freeze] now imposes that [freeze_base] does not: the old
    [map_monad]-based [freeze] could not fail. *)
Lemma I2F_raise_gen {E1 E2}
  `{FailureE -< E1} `{FailureE -< E2}
  {Rcutl : pred1 E1} {Rcutr : pred1 E2}
  {REv : prerel E1 E2} {RAns : postrel E1 E2}
  (HThrow : forall u1 u2 : unit,
      REv void void (subevent _ (Throw u1)) (subevent _ (Throw u2)))
  {A1 A2} (RR : A1 -> A2 -> Prop) (s1 s2 : string) :
  ruttc Rcutl Rcutr REv RAns RR (raise s1) (raise s2).
Proof. apply ruttc_trigger_cast, HThrow. Qed.

(** The two inner loops, each by induction on the [Forall2] carrying the
    induction hypothesis of [I2F_freeze_gen], generalized over the
    accumulators. In [freeze_fields] the field types are consumed in
    lockstep with the values, so the three mismatch branches
    ([] / t::ts, v::vs / [], and the [dtyp] guard) fire simultaneously on
    both sides. *)
Lemma I2F_freeze_fields_gen {E1 E2}
  `{@DrawE PInf -< E1} `{FailureE -< E1} `{OOME -< E1} `{UBE -< E1}
  `{@DrawE PFin -< E2} `{FailureE -< E2} `{OOME -< E2} `{UBE -< E2}
  {Rcutl : pred1 E1} {Rcutr : pred1 E2}
  {REv : prerel E1 E2} {RAns : postrel E1 E2}
  (HThrow : forall u1 u2 : unit,
      REv void void (subevent _ (Throw u1)) (subevent _ (Throw u2))) :
  forall s1 s2,
    Forall2 (fun (a : @dvalue PInf) (b : @dvalue PFin) =>
               forall dt, ruttc Rcutl Rcutr REv RAns I2F_dvalue (freeze dt a) (freeze dt b))
      s1 s2 ->
    forall dts acc1 acc2,
      Forall2 I2F_dvalue acc1 acc2 ->
      ruttc Rcutl Rcutr REv RAns (Forall2 I2F_dvalue)
        (freeze_fields s1 dts acc1) (freeze_fields s2 dts acc2).
Proof.
  intros s1 s2 HF; induction HF as [| v1 v2 vs1 vs2 Hv HF IH];
    intros [| t ts] acc1 acc2 HACC.
  - rewrite 2 freeze_fields_nil; apply ruttc_ret; now apply Forall2_rev_append.
  - rewrite 2 freeze_fields_nil_cons; now apply I2F_raise_gen.
  - rewrite 2 freeze_fields_cons_nil; now apply I2F_raise_gen.
  - rewrite 2 freeze_fields_cons.
    rbind I2F_dvalue; [apply Hv |].
    intros r1 r2 HR; apply IH; now constructor.
Qed.

Lemma I2F_freeze_elts_gen {E1 E2}
  `{@DrawE PInf -< E1} `{FailureE -< E1} `{OOME -< E1} `{UBE -< E1}
  `{@DrawE PFin -< E2} `{FailureE -< E2} `{OOME -< E2} `{UBE -< E2}
  {Rcutl : pred1 E1} {Rcutr : pred1 E2}
  {REv : prerel E1 E2} {RAns : postrel E1 E2} :
  forall t s1 s2,
    Forall2 (fun (a : @dvalue PInf) (b : @dvalue PFin) =>
               forall dt, ruttc Rcutl Rcutr REv RAns I2F_dvalue (freeze dt a) (freeze dt b))
      s1 s2 ->
    forall acc1 acc2,
      Forall2 I2F_dvalue acc1 acc2 ->
      ruttc Rcutl Rcutr REv RAns (Forall2 I2F_dvalue)
        (freeze_elts t s1 acc1) (freeze_elts t s2 acc2).
Proof.
  intros t s1 s2 HF; induction HF as [| v1 v2 vs1 vs2 Hv HF IH];
    intros acc1 acc2 HACC.
  - rewrite 2 freeze_elts_nil; apply ruttc_ret; now apply Forall2_rev_append.
  - rewrite 2 freeze_elts_cons.
    rbind I2F_dvalue; [apply Hv |].
    intros r1 r2 HR; apply IH; now constructor.
Qed.

(** The aggregate flag of the result ([DVALUE_Struct p] / [DVALUE_Array v])
    is read off the *type*, which is shared, so the two sides agree on it
    without any appeal to the relation between the input values. *)
Lemma I2F_freeze_gen {E1 E2}
  `{@DrawE PInf -< E1} `{FailureE -< E1} `{OOME -< E1} `{UBE -< E1}
  `{@DrawE PFin -< E2} `{FailureE -< E2} `{OOME -< E2} `{UBE -< E2}
  {Rcutl : pred1 E1} {Rcutr : pred1 E2}
  {REv : prerel E1 E2} {RAns : postrel E1 E2}
  (Hdraw : forall dt, ruttc Rcutl Rcutr REv RAns I2F_dvalue (draw dt) (draw dt))
  (HThrow : forall u1 u2 : unit,
      REv void void (subevent _ (Throw u1)) (subevent _ (Throw u2)))
  (dt:dtyp) (a : @dvalue PInf) (b : @dvalue PFin) :
  I2F_dvalue a b ->
  ruttc Rcutl Rcutr REv RAns I2F_dvalue (freeze dt a) (freeze dt b).
Proof.
  intros HDV; revert dt.
  induction HDV as [b1 b2 HB | p s1 s2 HF IH | v s1 s2 HF IH]; intros dt.
  - rewrite 2 freeze_Base_eq; now apply (I2F_freeze_base_gen Hdraw).
  - rewrite 2 freeze_Struct_eq.
    destruct dt; try now apply I2F_raise_gen.
    rbind (Forall2 I2F_dvalue).
    + now apply I2F_freeze_fields_gen.
    + intros ?? HR; apply ruttc_ret; now constructor.
  - rewrite 2 freeze_Array_eq.
    destruct dt; try now apply I2F_raise_gen.
    rbind (Forall2 I2F_dvalue).
    + now apply I2F_freeze_elts_gen.
    + intros ?? HR; apply ruttc_ret; now constructor.
Qed.

(** [draw] refined by itself at the MCFG signature --- the sole
      event-triggering step of [freeze]/[freeze_base]. *)
Lemma I2F_draw_MCFG : forall dt,
    I2F_refine_MCFG I2F_dvalue (draw dt) (draw dt).
Proof. intros; unfold I2F_refine_MCFG, draw; rstep. Qed.

Lemma I2F_freeze_base dt a b :
  I2F_dvalue_base a b ->
  I2F_refine (freeze_base dt a) (freeze_base dt b).
Proof. intros H; unfold I2F_refine, I2F_refine_MCFG; now apply (I2F_freeze_base_gen I2F_draw_MCFG). Qed.

Lemma I2F_freeze dt a b :
  I2F_dvalue a b ->
  I2F_refine (freeze dt a) (freeze dt b).
Proof.
  intros H; unfold I2F_refine, I2F_refine_MCFG;
    now apply (I2F_freeze_gen I2F_draw_MCFG I2FE_MCFG_Throw).
Qed.

(** The pure content of the [EXP_Integer] case, and the one place where
      the 14-way case analysis on [dtyp] happens. *)
Lemma I2F_denote_int_syntax_as_int : forall τ x,
    I2F_EOU I2F_dvalue
      (@denote_int_syntax_as_int PInf τ x)
      (@denote_int_syntax_as_int PFin τ x).
Proof with (cbn; repeat constructor).
  intros; destruct τ as [dt| |]...
  destruct dt...
  (* [DTYPE_Iptr]: the finite side either OOMs ([I2F_EOU_oom]) or
       returns [repr x] with [x] in range, so that [unsigned (repr x) = x]. *)
  unfold from_Z_bits.
  destruct ((denote_int_syntax x <=? @Integers.max_unsigned 64)%Z
            && (denote_int_syntax x >=? 0)%Z) eqn:EQ...
  apply andb_prop in EQ as [LE GE].
  apply Z.leb_le in LE; apply Z.geb_le in GE...
  red; rewrite Integers.unsigned_repr; [reflexivity | lia].
Qed.

(** The pure content of the [EXP_Float] case. The float parsing is
      parameter-independent: both sides run the very same computation. *)
Lemma I2F_denote_float_syntax_as_float : forall τ x,
    I2F_EOU I2F_dvalue
      (@denote_float_syntax_as_float PInf τ x)
      (@denote_float_syntax_as_float PFin τ x).
Proof.
  intros; destruct τ; cbn; try (repeat constructor).
  repeat (break_match_goal; cbn); repeat constructor.
Qed.

#[local] Hint Resolve Forall2_repeat : core.
(** The pure content of the [EXP_Zero_initializer] case, by induction on
      [dtyp]. The only value-dependent leaves are [DTYPE_Iptr] (the zero
      intptr on both sides) and [DTYPE_Pointer] ([null] on both sides),
      including under vectors; the aggregate cases go through the
      compatibility of [I2F_EOU] with [bind] and [map_monad]. *)
Lemma I2F_default_dvalue_of_dtyp : forall τ,
    I2F_EOU I2F_dvalue
      (@default_dvalue_of_dtyp PInf τ)
      (@default_dvalue_of_dtyp PFin τ).
Proof.
  induction τ; cbn.
  - (* DTYPE_Base: scalar leaves, all diagonal up to [zero_iptr]/[null];
         [DTYPE_B] relates the repeated zero bits pointwise *)
    destruct t; cbn;
      try (unfold default_dvalue_of_dtyp_i);
      try (destruct fp; cbn); auto 8.
    do 4 constructor.
  - (* DTYPE_Struct *)
    eapply I2F_EOU_bind; [apply I2F_EOU_map_monad; auto|].
    intros; do 2 constructor; auto.
  - (* DTYPE_Array *)
    eapply I2F_EOU_bind; [eassumption|].
    intros; do 2 constructor.
    apply Forall2_repeatN; auto.
Qed.

  (** * Arithmetic bridge: [IPZ] vs [IP64Bit] under [I2F_Iptr]

      [I2F_Iptr x x'] pins [x = unsigned x'], so after substitution both
      sides of the integer operations compute on [unsigned x'],
      [unsigned y']. The lemmas below characterize the [unsigned] value of
      the finite operations on their success paths; the failure paths are
      absorbed by the [I2F_EOU] cuts (OOM on the right, UB on the left) or
      synchronize as equal booleans. *)

Section ArithBridge.
  Context {sz : positive}.

  Lemma unsigned_add_bounded : forall (x y : @bit_int sz),
      (unsigned x + unsigned y < @Integers.modulus sz)%Z ->
      unsigned (Integers.add x y) = (unsigned x + unsigned y)%Z.
  Proof.
    intros x y B.
    pose proof (Integers.unsigned_range x); pose proof (Integers.unsigned_range y).
    unfold Integers.add.
    rewrite Integers.unsigned_repr_eq.
    apply Zmod_small; lia.
  Qed.

  Lemma unsigned_sub_bounded : forall (x y : @bit_int sz),
      (unsigned y <= unsigned x)%Z ->
      unsigned (Integers.sub x y) = (unsigned x - unsigned y)%Z.
  Proof.
    intros x y B.
    pose proof (Integers.unsigned_range x); pose proof (Integers.unsigned_range y).
    unfold Integers.sub.
    rewrite Integers.unsigned_repr_eq.
    apply Zmod_small; lia.
  Qed.

  Lemma unsigned_divu : forall (x y : @bit_int sz),
      unsigned y <> 0%Z ->
      unsigned (Integers.divu x y) = (unsigned x / unsigned y)%Z.
  Proof.
    intros x y NZ.
    pose proof (Integers.unsigned_range x); pose proof (Integers.unsigned_range y).
    unfold Integers.divu.
    rewrite Integers.unsigned_repr; auto.
    unfold Integers.max_unsigned.
    assert (0 <= unsigned x / unsigned y <= unsigned x)%Z; [| lia].
    split.
    - apply Z.div_pos; lia.
    - apply Z.div_le_upper_bound; nia.
  Qed.

  Lemma unsigned_modu : forall (x y : @bit_int sz),
      unsigned y <> 0%Z ->
      unsigned (Integers.modu x y) = (unsigned x mod unsigned y)%Z.
  Proof.
    intros x y NZ.
    pose proof (Integers.unsigned_range x); pose proof (Integers.unsigned_range y).
    unfold Integers.modu.
    rewrite Integers.unsigned_repr; auto.
    pose proof (Z.mod_pos_bound (unsigned x) (unsigned y) ltac:(lia)).
    unfold Integers.max_unsigned; lia.
  Qed.

  Lemma unsigned_shru : forall (x y : @bit_int sz),
      unsigned (Integers.shru x y) = Z.shiftr (unsigned x) (unsigned y).
  Proof.
    intros x y.
    pose proof (Integers.unsigned_range x); pose proof (Integers.unsigned_range y).
    unfold Integers.shru.
    rewrite Integers.unsigned_repr; auto.
    rewrite Z.shiftr_div_pow2 by lia.
    assert (0 < 2 ^ unsigned y)%Z by (apply Z.pow_pos_nonneg; lia).
    unfold Integers.max_unsigned.
    assert (0 <= unsigned x / 2 ^ unsigned y <= unsigned x)%Z; [| lia].
    split.
    - apply Z.div_pos; lia.
    - apply Z.div_le_upper_bound; nia.
  Qed.

  (* Bitwise operations: the exact result already fits in [sz] bits. *)

  Lemma unsigned_testbit_above : forall (x : @bit_int sz) i,
      (Z.pos sz <= i)%Z -> Z.testbit (unsigned x) i = false.
  Proof.
    intros x i LE.
    apply Ztestbit_above with (n := Pos.to_nat sz).
    - pose proof (Integers.unsigned_range x) as R.
      unfold Integers.modulus in R.
      now rewrite <- two_power_pos_nat, <- two_power_pos_memo_eq.
    - rewrite positive_nat_Z; lia.
  Qed.

  Lemma max_unsigned_ones : @Integers.max_unsigned sz = Z.ones (Z.pos sz).
  Proof.
    unfold Integers.max_unsigned.
    rewrite Integers.modulus_power, Z.ones_equiv, two_p_equiv.
    unfold Integers.zwordsize; lia.
  Qed.

  Lemma Z_bits_range : forall z,
      (0 <= z)%Z ->
      (forall i, (Z.pos sz <= i)%Z -> Z.testbit z i = false) ->
      (0 <= z <= @Integers.max_unsigned sz)%Z.
  Proof.
    intros z NN ABOVE; split; auto.
    apply Ztestbit_le.
    - pose proof (@Integers.modulus_pos sz).
      unfold Integers.max_unsigned; lia.
    - intros i POS TB.
      rewrite max_unsigned_ones.
      destruct (Z.ltb_spec i (Z.pos sz)) as [LT | GE].
      + apply Z.ones_spec_low; lia.
      + rewrite ABOVE in TB; [discriminate | lia].
  Qed.

  Lemma unsigned_and_land : forall (x y : @bit_int sz),
      unsigned (Integers.and x y) = Z.land (unsigned x) (unsigned y).
  Proof.
    intros x y.
    pose proof (Integers.unsigned_range x); pose proof (Integers.unsigned_range y).
    unfold Integers.and.
    rewrite Integers.unsigned_repr; auto.
    apply Z_bits_range.
    - apply Z.land_nonneg; lia.
    - intros i LE.
      rewrite Z.land_spec, !unsigned_testbit_above; auto.
  Qed.

  Lemma unsigned_or_lor : forall (x y : @bit_int sz),
      unsigned (Integers.or x y) = Z.lor (unsigned x) (unsigned y).
  Proof.
    intros x y.
    pose proof (Integers.unsigned_range x); pose proof (Integers.unsigned_range y).
    unfold Integers.or.
    rewrite Integers.unsigned_repr; auto.
    apply Z_bits_range.
    - apply Z.lor_nonneg; lia.
    - intros i LE.
      rewrite Z.lor_spec, !unsigned_testbit_above; auto.
  Qed.

  Lemma unsigned_xor_lxor : forall (x y : @bit_int sz),
      unsigned (Integers.xor x y) = Z.lxor (unsigned x) (unsigned y).
  Proof.
    intros x y.
    pose proof (Integers.unsigned_range x); pose proof (Integers.unsigned_range y).
    unfold Integers.xor.
    rewrite Integers.unsigned_repr; auto.
    apply Z_bits_range.
    - apply Z.lxor_nonneg; lia.
    - intros i LE.
      rewrite Z.lxor_spec, !unsigned_testbit_above; auto.
  Qed.

  Lemma eq_unsigned_eqb : forall (x y : @bit_int sz),
      Integers.eq x y = (unsigned x =? unsigned y)%Z.
  Proof.
    intros; unfold Integers.eq.
    destruct (zeq _ _) as [e | n]; symmetry.
    - now apply Z.eqb_eq.
    - now apply Z.eqb_neq.
  Qed.

  (* The always-[zero] overflow-flag functions of the intptr instances
       make the poison guards vacuous. *)
  Lemma eq_zero_one_false : @Integers.eq sz Integers.zero Integers.one = false.
  Proof.
    rewrite eq_unsigned_eqb, Integers.unsigned_zero, Integers.unsigned_one.
    reflexivity.
  Qed.

  (* The success path of the finite [madd]. *)
  Lemma unsigned_add_no_carry : forall (x y : @bit_int sz),
      Integers.eq (Integers.add_carry x y Integers.zero) Integers.one = false ->
      unsigned (Integers.add x y) = (unsigned x + unsigned y)%Z.
  Proof.
    intros x y NC.
    unfold Integers.add_carry in NC.
    rewrite Integers.unsigned_zero, Z.add_0_r in NC.
    revert NC; destruct (zlt _ _) as [LT | GE]; intros NC.
    - apply unsigned_add_bounded; auto.
    - now rewrite Integers.eq_true in NC.
  Qed.

  (* Comparison bridges: the finite unsigned comparisons coincide with
       [mcmpu_Z] on the [unsigned] values. *)
  Lemma ltu_unsigned_ltb : forall (x y : @bit_int sz),
      Integers.ltu x y = (unsigned x <? unsigned y)%Z.
  Proof.
    intros; unfold Integers.ltu.
    destruct (zlt _ _) as [l | g]; symmetry.
    - now apply Z.ltb_lt.
    - apply Z.ltb_ge; lia.
  Qed.

  Lemma cmpu_unsigned : forall c (x y : @bit_int sz),
      Integers.cmpu c x y = mcmpu_Z c (unsigned x) (unsigned y).
  Proof.
    intros []; intros; cbv [Integers.cmpu mcmpu_Z];
      rewrite ?eq_unsigned_eqb, ?ltu_unsigned_ltb; auto.
    - now rewrite Z.leb_antisym.
    - now rewrite Z.gtb_ltb.
    - now rewrite Z.geb_leb, Z.leb_antisym.
  Qed.

  Lemma Z_gtb_irrefl : forall z : Z, (z >? z)%Z = false.
  Proof.
    intros; rewrite Z.gtb_ltb; apply Z.ltb_irrefl.
  Qed.

End ArithBridge.

(* Keep the overflow bounds abstract in goals rather than computed to
     20-digit literals, and keep [unsigned (repr z)] from reducing to
     [Z_mod_modulus z], so that explicit [destruct ... eqn:] and the
     [ArithBridge] lemmas apply syntactically. *)
#[local] Arguments Integers.max_unsigned : simpl never.
#[local] Arguments Integers.repr : simpl never.
#[local] Arguments msamesign_Z : simpl never.

(** Layer 1: [eval_int_op] at the intptr instantiations, where the two
      sides genuinely differ. The instances are pinned explicitly: at the
      concrete parameters, [iptr IP64Bit] is definitionally [bit_int 64]
      and inference would otherwise pick [ToDvalue_Int] rather than the
      [ToDvalue_iptr] used (at abstract [Params]) by [eval_iop_integer_h]. *)
Lemma I2F_eval_int_op_iptr : forall iop (x y : @iptr IPZ) (x' y' : @iptr IP64Bit),
    I2F_Iptr x x' -> I2F_Iptr y y' ->
    I2F_EOU I2F_dvalue_base
      (@eval_int_op PInf (@iptr IPZ) (@VMemInt_iptr IPZ) (@ToDvalue_iptr PInf) iop x y)
      (@eval_int_op PFin (@iptr IP64Bit) (@VMemInt_iptr IP64Bit) (@ToDvalue_iptr PFin) iop x' y').
Proof.
  intros * EQ1 EQ2; red in EQ1, EQ2; subst.
  destruct iop; cbn.
  - (* Add: the finite side OOMs on carry, else values agree *)
    destruct nuw, nsw; cbn; rewrite ?eq_zero_one_false; cbn;
      (destruct (Integers.eq (Integers.add_carry x' y' Integers.zero) Integers.one) eqn:NC;
       cbn; auto;
       do 2 constructor; red; rewrite unsigned_add_no_carry; auto).
  - (* Sub: the finite side OOMs on underflow *)
    destruct nuw, nsw; cbn; rewrite ?eq_zero_one_false; cbn;
      (destruct ((unsigned y' >? unsigned x')%Z) eqn:B; cbn; auto;
       rewrite Z.gtb_ltb, Z.ltb_ge in B;
       do 2 constructor; red; rewrite unsigned_sub_bounded; auto).
  - (* Mul: the finite side OOMs on overflow; the left side carries a
         vacuous [z >? z] guard. *)
    rewrite Z_gtb_irrefl; cbn.
    destruct ((unsigned x' * unsigned y' >? @Integers.max_unsigned 64)%Z) eqn:B; cbn; auto.
    rewrite Z.gtb_ltb, Z.ltb_ge in B.
    assert (RANGE : (0 <= unsigned x' * unsigned y' <= @Integers.max_unsigned 64)%Z).
    { pose proof (Integers.unsigned_range x'); pose proof (Integers.unsigned_range y'); nia. }
    rewrite Integers.unsigned_repr; auto.
    rewrite Z_gtb_irrefl; cbn.
    do 2 constructor; red; rewrite Integers.unsigned_repr; auto.
  - (* Shl: same shape as Mul *)
    rewrite Z_gtb_irrefl; cbn.
    destruct ((Z.shiftl (unsigned x') (unsigned y') >? @Integers.max_unsigned 64)%Z) eqn:B;
      cbn; auto.
    rewrite Z.gtb_ltb, Z.ltb_ge in B.
    assert (RANGE : (0 <= Z.shiftl (unsigned x') (unsigned y') <= @Integers.max_unsigned 64)%Z).
    { pose proof (Integers.unsigned_range x'); split; auto.
      apply Z.shiftl_nonneg; lia. }
    rewrite Integers.unsigned_repr; auto.
    rewrite Z_gtb_irrefl; cbn.
    do 2 constructor; red; rewrite Integers.unsigned_repr; auto.
  - (* UDiv: division by zero raises UB on both sides (left cut) *)
    destruct ((unsigned y' =? 0)%Z) eqn:Z0; cbn; auto.
    apply Z.eqb_neq in Z0.
    destruct exact; cbn.
    + destruct ((unsigned x' mod unsigned y' =? 0)%Z) eqn:EX; cbn; eauto.
      do 2 constructor; red; rewrite unsigned_divu; auto.
    + do 2 constructor; red; rewrite unsigned_divu; auto.
  - (* SDiv: unsupported at iptr type on both sides *)
    repeat constructor.
  - (* LShr *)
    rewrite Bool.andb_false_r; cbn.
    destruct exact; cbn.
    + destruct ((unsigned x' mod 2 ^ unsigned y' =? 0)%Z) eqn:EX; cbn; eauto.
      do 2 constructor; red; now rewrite unsigned_shru.
    + do 2 constructor; red; now rewrite unsigned_shru.
  - (* AShr: unsupported at iptr type on both sides *)
    repeat constructor.
  - (* URem *)
    destruct ((unsigned y' =? 0)%Z) eqn:Z0; cbn; auto.
    apply Z.eqb_neq in Z0.
    do 2 constructor; red; rewrite unsigned_modu; auto.
  - (* SRem: unsupported at iptr type on both sides *)
    repeat constructor.
  - (* And *)
    do 2 constructor; red; now rewrite unsigned_and_land.
  - (* Or *)
    destruct disjoint; cbn.
    + rewrite eq_unsigned_eqb, unsigned_or_lor, unsigned_xor_lxor.
      destruct ((Z.lor (unsigned x') (unsigned y') =? Z.lxor (unsigned x') (unsigned y'))%Z) eqn:D;
        cbn.
      * do 2 constructor; red; now rewrite unsigned_or_lor.
      * repeat constructor.
    + do 2 constructor; red; now rewrite unsigned_or_lor.
  - (* Xor *)
    do 2 constructor; red; now rewrite unsigned_xor_lxor.
Qed.

(** Layer 2: on [bit_int sz] arguments both sides run the very same
      computation; only the [dvalue] wrapper differs. *)
Lemma I2F_eval_int_op_bit_int : forall (sz : positive) iop (x y : @bit_int sz),
    I2F_EOU I2F_dvalue_base
      (@eval_int_op PInf _ _ _ iop x y)
      (@eval_int_op PFin _ _ _ iop x y).
Proof.
  intros; destruct iop; cbn.
  all:repeat break_goal_fast; eauto; fail.
Qed.

(** Layer 3: the scalar dispatcher. Inverting the two value relations
      keeps the case analysis synchronized; the remaining cases dispatch
      to layers 1 and 2, or share their guards (including the SDiv-on-
      poison check, whose scrutinee agrees on related values). *)
Lemma I2F_eval_iop_integer_base : forall iop v1 v2 v1' v2',
    I2F_dvalue_base v1 v1' ->
    I2F_dvalue_base v2 v2' ->
    I2F_EOU I2F_dvalue_base
      (@eval_iop_integer_base PInf iop v1 v2)
      (@eval_iop_integer_base PFin iop v1' v2').
Proof.
  intros * H1 H2.
  induction H1; induction H2; cbn; eauto.
  all: try (repeat break_goal_fast; eauto; fail).
  - repeat break_goal_fast; eauto.
    subst; cbn; apply I2F_eval_int_op_bit_int.
  - apply I2F_eval_int_op_iptr; eauto.
  - (* Poison rows: the guards are shared, up to [I2F_Iptr] on the payload *)
    destruct iop; cbn; eauto.
    try (match goal with H : I2F_Iptr _ _ |- _ => red in H; subst end).
    repeat break_goal_fast; eauto.
Qed.

(* Destruct the (variable) vector flags blocking the [eval_*] wrapper
     dispatches; the mismatched flavours are diagonal errors. *)
Ltac i2f_vec_flags :=
  repeat match goal with
    | |- context [if ?v then _ else _] => is_var v; destruct v; cbn
    end.

(** The partial coercion to base values relates related values. *)
Lemma I2F_dvalue_to_dvalue_base : forall v v',
    I2F_dvalue v v' ->
    I2F_EOU I2F_dvalue_base
      (@dvalue_to_dvalue_base PInf v) (@dvalue_to_dvalue_base PFin v').
Proof.
  intros * H; inversion H; subst; cbn; repeat constructor; eauto.
Qed.

Lemma Forall2_map_Base : forall l1 l2,
    Forall2 I2F_dvalue_base l1 l2 ->
    Forall2 I2F_dvalue (map (@DVALUE_Base PInf) l1) (map (@DVALUE_Base PFin) l2).
Proof.
  intros l1 l2 F; induction F; cbn; constructor; auto.
Qed.

(* The [eval_*] wrappers share their vector plumbing: coerce both
     element lists to base values, run the base dispatcher pointwise,
     and rewrap. *)
Ltac i2f_vec_wrap base_lemma :=
  i2f_vec_flags;
  try (repeat constructor);
  repeat match goal with
    | F : Forall2 I2F_dvalue _ _ |- _ =>
        rewrite (Forall2_length_N F); revert F
    end;
  intros F1 F2;
  break_match_goal; cbn; auto;
  (eapply I2F_EOU_bind;
   [eapply I2F_EOU_map_monad2;
    [eauto | intros; apply I2F_dvalue_to_dvalue_base; auto]|]);
  intros ? ? ?;
    (eapply I2F_EOU_bind;
     [eapply I2F_EOU_map_monad2;
      [eauto | intros; apply I2F_dvalue_to_dvalue_base; auto]|]);
  intros ? ? ?;
    (eapply I2F_EOU_bind;
     [ eapply I2F_EOU_vec_loop; [eapply Forall2_combine; eauto|];
       intros; apply base_lemma; auto
     | intros; do 2 constructor; apply Forall2_map_Base; auto ]).

(** Layer 4: [eval_iop] adds the pointwise vector case on top of the
      scalar dispatcher. *)
Lemma I2F_eval_iop a1 a2 b1 b2 iop :
  I2F_dvalue a1 b1 ->
  I2F_dvalue a2 b2 ->
  I2F_EOU I2F_dvalue (eval_iop iop a1 a2) (eval_iop iop b1 b2).
Proof.
  intros H1 H2.
  induction H1; subst; induction H2; subst; cbn; repeat constructor.
  2,3: break_goal_fast; eauto.
  - (* Base × Base *)
    eapply I2F_EOU_bind; [apply I2F_eval_iop_integer_base; auto|].
    intros; eauto.
  - (* Array × Array *)
    i2f_vec_wrap I2F_eval_iop_integer_base.
Qed.

(* The float operations are parameter-independent: related inputs have
     synchronized shapes and identical payloads, so every leaf is
     diagonal. *)
Lemma I2F_eval_fneg_base : forall v v',
    I2F_dvalue_base v v' ->
    I2F_EOU I2F_dvalue_base (@eval_fneg_base PInf v) (@eval_fneg_base PFin v').
Proof.
  intros * H; inversion H; subst; cbn; repeat constructor.
Qed.

Lemma I2F_eval_fneg a b :
  I2F_dvalue a b ->
  I2F_EOU I2F_dvalue (eval_fneg a) (eval_fneg b).
Proof.
  intros H.
  inversion H; subst; cbn; eauto.
  - (* Base *)
    eapply I2F_EOU_bind; [apply I2F_eval_fneg_base; auto| eauto].
  - (* Array: only the vector flavour computes *)
    match goal with v : bool |- _ => destruct v end; cbn; eauto.
    eapply I2F_EOU_bind;
      [eapply I2F_EOU_map_monad2;
       [eauto | intros; apply I2F_dvalue_to_dvalue_base; auto]|].
    intros;
    eapply I2F_EOU_bind;
      [eapply I2F_EOU_map_monad2;
       [eauto | intros; apply I2F_eval_fneg_base; auto]|].
    intros; do 2 constructor; apply Forall2_map_Base; auto.
Qed.

(* The infinite side's same-sign test is always true on unsigned values;
     the finite side's is constantly true. *)
Lemma msamesign_Z_nonneg : forall x y : Z,
    (0 <= x)%Z -> (0 <= y)%Z -> msamesign_Z x y = true.
Proof.
  intros x y HX HY; unfold msamesign_Z.
  apply Z.geb_le in HX; apply Z.geb_le in HY.
  now rewrite HX, HY.
Qed.

(** [eval_int_icmp] at the intptr instantiations. The signed comparisons
      are unsupported at iptr type on both sides; the unsigned ones agree
      through the comparison bridges; the same-sign poison guard is vacuous
      on both sides (unsigned values are nonnegative on the left, and the
      finite [msamesign] is constantly [true]). *)
Lemma I2F_eval_int_icmp_iptr : forall samesign icmp (x y : @iptr IPZ) (x' y' : @iptr IP64Bit),
    I2F_Iptr x x' -> I2F_Iptr y y' ->
    I2F_EOU I2F_dvalue_base
      (@eval_int_icmp PInf _ (@VMemInt_iptr IPZ) samesign icmp x y)
      (@eval_int_icmp PFin _ (@VMemInt_iptr IP64Bit) samesign icmp x' y').
Proof.
  intros * EQ1 EQ2; red in EQ1, EQ2; subst.
  pose proof (Integers.unsigned_range x'); pose proof (Integers.unsigned_range y').
  destruct icmp; cbn; repeat constructor;
    rewrite ?eq_unsigned_eqb, ?ltu_unsigned_ltb, ?Z.gtb_ltb, ?Z.geb_leb, ?Z.leb_antisym;
    rewrite msamesign_Z_nonneg by lia;
    cbn; rewrite ?Bool.andb_false_r; cbn;
    break_match_goal; repeat constructor.
Qed.

(** The scalar comparison dispatcher. *)
Lemma I2F_eval_icmp_base : forall samesign icmp v1 v2 v1' v2',
    I2F_dvalue_base v1 v1' ->
    I2F_dvalue_base v2 v2' ->
    I2F_EOU I2F_dvalue_base
      (@eval_icmp_base PInf samesign icmp v1 v2)
      (@eval_icmp_base PFin samesign icmp v1' v2').
Proof.
  intros * H1 H2.
  induction H1; induction H2; cbn; eauto.
  (* Iptr × Iptr *)
  3:apply I2F_eval_int_icmp_iptr; eauto.
  (* Remaining synchronized rows: [I × I] (after eliminating the
       bitwidth transport) and [Pointer × Pointer] (where [ptr_to_int]
       yields equal integers) run the same computation on both sides;
       close by symbolic execution of the shared tests. *)
  all: repeat match goal with
         | HA : I2F_Addr ?a ?b |- _ =>
             destruct a, b; destruct HA as [HI ->]; red in HI; subst
         end;
    try (match goal with
         | |- context [Pos.eq_dec ?a ?b] =>
             destruct (Pos.eq_dec a b) as [e | n]; [destruct e|]
         end);
    cbv [eq_rec_r eq_rec eq_rect Logic.eq_sym];
    destruct icmp; cbn; eauto;
    repeat (break_goal_fast; cbn); repeat constructor.
Qed.

Lemma I2F_eval_icmp a1 a2 b1 b2 samesign cmp :
  I2F_dvalue a1 b1 ->
  I2F_dvalue a2 b2 ->
  I2F_EOU I2F_dvalue (eval_icmp samesign cmp a1 a2)
    (eval_icmp samesign cmp b1 b2).
Proof.
  intros H1 H2.
  induction H1; induction H2; cbn; eauto.
  all: try (i2f_vec_flags; eauto).
  - (* Base × Base *)
    eapply I2F_EOU_bind; [apply I2F_eval_icmp_base; auto|].
    intros; eauto.
  - (* Array × Array *)
    i2f_vec_wrap I2F_eval_icmp_base.
Qed.

Lemma I2F_eval_fop_base : forall c v1 v2 v1' v2',
    I2F_dvalue_base v1 v1' ->
    I2F_dvalue_base v2 v2' ->
    I2F_EOU I2F_dvalue_base
      (@eval_fop_base PInf c v1 v2)
      (@eval_fop_base PFin c v1' v2').
Proof.
  intros * H1 H2.
  induction H1; induction H2; cbn; eauto;
    destruct c; cbn; try (break_goal_fast; cbn); eauto.
Qed.

Lemma I2F_eval_fop a1 a2 b1 b2 fop :
  I2F_dvalue a1 b1 ->
  I2F_dvalue a2 b2 ->
  I2F_EOU I2F_dvalue (eval_fop fop a1 a2) (eval_fop fop b1 b2).
Proof.
  intros H1 H2.
  induction H1; induction H2; cbn; eauto.
  all: try (i2f_vec_flags; repeat constructor).
  - (* Base × Base *)
    eapply I2F_EOU_bind; [apply I2F_eval_fop_base; auto|].
    intros; eauto.
  - (* Array × Array *)
    i2f_vec_wrap I2F_eval_fop_base.
Qed.

Lemma I2F_eval_fcmp_base : forall c v1 v2 v1' v2',
    I2F_dvalue_base v1 v1' ->
    I2F_dvalue_base v2 v2' ->
    I2F_EOU I2F_dvalue_base
      (@eval_fcmp_base PInf c v1 v2)
      (@eval_fcmp_base PFin c v1' v2').
Proof.
  intros * H1 H2.
  induction H1; induction H2; cbn; eauto;
    unfold float_cmp, double_cmp; destruct c; cbn;
    repeat (break_goal_fast; cbn); eauto.
Qed.

Lemma I2F_eval_fcmp a1 a2 b1 b2 cmp :
  I2F_dvalue a1 b1 ->
  I2F_dvalue a2 b2 ->
  I2F_EOU I2F_dvalue (eval_fcmp cmp a1 a2)
    (eval_fcmp cmp b1 b2).
Proof.
  intros H1 H2.
  inversion H1; subst; inversion H2; subst; cbn;
    try (repeat constructor).
  all: try (i2f_vec_flags; repeat constructor).
  - (* Base × Base *)
    eapply I2F_EOU_bind; [apply I2F_eval_fcmp_base; auto|].
    intros; do 2 constructor; auto.
  - (* Array × Array *)
    i2f_vec_wrap I2F_eval_fcmp_base.
Qed.

(** * Bitcast: relating the byte-serialization round-trip.

*)

(** The semantic relation on lazy memory bytes: equal byte values. *)
Definition I2F_memory_byte (b : @memory_byte PInf) (b' : @memory_byte PFin) : Prop :=
  I2F_dvalue_bv b b'.

(* [EOUP]'s monad instance is local to [MemoryBytes.v]; re-register it
     so that [map_monad] at [EOUP] can be spoken about here. *)
#[local] Existing Instance EOUP_Monad.


#[local] Arguments absorb_pois : simpl never.

Lemma I2F_absorb_pois {A1 A2} (RR : A1 -> A2 -> Prop) (c1 : EOUP A1) (c2 : EOUP A2)
  (k1 : A1 -> EOU (@dvalue_base PInf)) (k2 : A2 -> EOU (@dvalue_base PFin)) :
  I2F_EOUP RR c1 c2 ->
  (forall a1 a2, RR a1 a2 -> I2F_EOU I2F_dvalue_base (k1 a1) (k2 a2)) ->
  I2F_EOU I2F_dvalue_base (@absorb_pois PInf A1 c1 k1) (@absorb_pois PFin A2 c2 k2).
Proof.
  intros HC K; unfold absorb_pois.
  eapply I2F_EOUP_EOU in HC.
  eapply I2F_EOU_bind with (RA := (MaybePoisonRel RR)); auto.
  intros a1 a2 H. inversion H; subst; [apply K;auto | repeat constructor].
Qed.


(* [break_match_goal], but refusing to destruct [EOU]-typed scrutinees
     opaquely: on those the two sides must be reduced in lockstep, either
     because the scrutinees are the same term or through a dedicated
     lemma. Failing the outer candidate lets the goal-matching backtrack
     to the inner (boolean, type) tests. *)
Ltac break_match_goal_safe :=
  match goal with
  | |- context [match ?X with _ => _ end] =>
      lazymatch type of X with
      | EOU _ => fail
      | _ => destruct X eqn:?
      end
  end.

(* Close an in-range [from_Z_bits] success branch: extract the bounds
     from the guard, then relate [z] with [repr z] through
     [unsigned_repr], wrapped either as an intptr value or as an
     address. *)
Ltac i2f_in_range_case :=
  match goal with
  | B : ((_ <=? _)%Z && (_ >=? _)%Z)%bool = true |- _ =>
      apply andb_prop in B as [LE GE];
      apply Z.leb_le in LE; apply Z.geb_le in GE
  end.

Lemma I2F_memory_bit_to_bit mb1 mb2 :
    I2F_memory_bit mb1 mb2 ->
    I2F_EOUP Logic.eq (memory_bit_to_bit mb1) (memory_bit_to_bit mb2).
Proof.
  intros H.
  inversion H; subst.
  - destruct p. destruct p'. simpl in H0. destruct H0; subst.
    inversion H0. subst.
    cbn. constructor. reflexivity.
  - cbn. constructor.
  - cbn.  constructor. reflexivity.
Qed.


Lemma I2F_memory_bits_to_Z bits1 bits2 :
    Forall2 I2F_memory_bit bits1 bits2 ->
    I2F_EOUP Logic.eq (memory_bits_to_Z bits1) (memory_bits_to_Z bits2).
Proof.
  intros H.
  unfold memory_bits_to_Z.
  eapply I2F_EOUP_bind with (RA:=Forall2 Logic.eq).
  eapply I2F_EOUP_map_monad2 with (RA:=I2F_memory_bit); auto.
  intros. apply I2F_memory_bit_to_bit; auto.
  intros.
  constructor. 
  apply Forall2_eq in H0. subst.
  reflexivity.
Qed.  
  
Lemma I2F_memory_byte_to_Z mb1 mb2 :
    I2F_memory_byte mb1 mb2 ->
    I2F_EOUP Logic.eq (memory_byte_to_Z mb1) (memory_byte_to_Z mb2).
Proof.
  intros H.
  inversion H; subst.
  - constructor. reflexivity.
  - cbn in *.
    destruct p. destruct p'.  simpl in H0. intuition. subst.
    inversion H1. subst.
    constructor. cbn. reflexivity.
  - cbn.
    eapply I2F_EOUP_bind with (RA:=Forall2 Logic.eq).
    eapply I2F_EOUP_map_monad2 with (RA:=I2F_memory_bit); auto.
    intros. eapply I2F_memory_bit_to_bit. assumption.
    intros. 
    apply Forall2_eq in H1. subst.
    constructor.
    reflexivity.
Qed.  

Lemma Forall2_take {A B: Type} (RR : A -> B -> Prop) : forall n l l',
  Forall2 RR l l' ->
  Forall2 RR (take n l) (take n l').
Proof.
  intros n l l' H. revert n.
  induction H.
  - constructor.
  - cbn.
    destruct n; constructor; auto.
Qed.    

Lemma I2F_concat_bytes_Z_mixed extra_bits acc dbs dbs' 
    (H : Forall2 I2F_memory_byte dbs dbs') : 
    I2F_EOUP Logic.eq (concat_bytes_Z_mixed extra_bits acc dbs) (concat_bytes_Z_mixed extra_bits acc dbs').
Proof.
  revert acc.
  induction H; intros.
  - cbn. constructor; auto.
  - inversion H; subst.
    + cbn. inversion H0; subst; auto. 
    + cbn. inversion H0; subst; auto. 
      unfold I2F_Addr in H1.
      destruct p. destruct p'.
      destruct H1. subst. unfold I2F_Iptr in H1.
      subst.
      apply IHForall2.
    + cbn. inversion H0; subst; auto.
      * apply (Forall2_take extra_bits) in H1.
        eapply I2F_EOUP_bind with (RA:=Logic.eq).
        eapply I2F_EOUP_bind with (RA:=Forall2 Logic.eq).
        eapply I2F_EOUP_map_monad2 with (RA:=I2F_memory_bit); auto.
        apply I2F_memory_bit_to_bit.
        intros. constructor.
        apply Forall2_eq in H2. subst.
        reflexivity.
        intros. subst.
        constructor. reflexivity.
      * eapply I2F_EOUP_bind with (RA:=Logic.eq).
        eapply I2F_EOUP_bind with (RA:=Forall2 Logic.eq).
        eapply I2F_EOUP_map_monad2 with (RA:=I2F_memory_bit); auto.
        apply I2F_memory_bit_to_bit.
        intros. constructor.
        apply Forall2_eq in H4. subst.
        reflexivity.
        intros. subst.
        eapply IHForall2.
Qed.        

Lemma I2F_memory_bytes_to_int (bit_sz : positive) dbs dbs' :
    Forall2 I2F_memory_byte dbs dbs' ->
    I2F_EOUP Logic.eq (memory_bytes_to_int bit_sz dbs) (memory_bytes_to_int bit_sz dbs'). 
Proof.
  intros H.
  unfold memory_bytes_to_int.
  destruct (negb (N.pos bit_sz mod 8 =? 0)%N).
  - eapply I2F_concat_bytes_Z_mixed. assumption.
  - eapply I2F_EOUP_bind with (RA:=Forall2 Logic.eq).
    eapply I2F_EOUP_map_monad2 with (RA:=I2F_memory_byte); auto.
    apply I2F_memory_byte_to_Z.
    intros.
    apply Forall2_eq in H0. subst.
    constructor. reflexivity.
Qed.    

Lemma in_bounds_case k (x : Z)
  (LE: x <= @max_unsigned k)
  (GE : 0 <= x) :
  x = @unsigned k (repr x).
Proof.
  rewrite unsigned_repr; auto.
Qed.


(*
Lemma I2F_EOUP_valid_pointer_bits p p' base offset bits bits' 
  (H : I2F_Addr p p')
  (HM : 


  Fixpoint valid_pointer_bits p base offset bits : EOUP bool :=
    match bits with
    | [] => ret (N.eqb offset 8)
    | (Bit_ptr q j) :: rest  =>
        if eq_dec_ptr p q then
          if N.eqb j (base + offset) then
            valid_pointer_bits p base (1+offset) rest 
          else
            ret false
        else
          ret false
    | _ => ret Pois
    end.
  
  Definition valid_pointer_byte (p:ptr) (idx:N) (mb:memory_byte) : EOUP bool :=
    match mb with
    | BYTE_Pointer q i =>
        if eq_dec_ptr p q then ret (N.eqb idx i) else ret false 
    | BYTE_Mixed bits =>
        valid_pointer_bits p (idx * 8) 0 bits 
    | BYTE_I _ => ret false
    end.
 *)

(* NOTE: we use proof irrelevance here *)
Lemma unsigned_inj : forall sz x y, (@unsigned sz) x = unsigned y -> x = y.
Proof.
  intros.
  unfold unsigned in H.
  unfold intval in H.
  destruct x. destruct y.
  subst.
  specialize (proof_irrelevance _ intrange intrange0) as H.
  rewrite H.
  reflexivity.
Qed.  
  
(* TODO: this is a pretty ugly proof. *)
Lemma I2F_EOUP_valid_pointer_bits p p' base offset bits bits'  
  (HP: I2F_Addr p p')
  (HB: Forall2 I2F_memory_bit bits bits') :
  I2F_EOUP Logic.eq (@valid_pointer_bits PInf p base offset bits) (@valid_pointer_bits PFin p' base offset bits').
Proof.
  revert base offset.
  induction HB.
  - constructor. reflexivity.
  - intros. inversion H; subst. 
    + unfold valid_pointer_bits.
      repeat break_match_goal_safe; subst; try constructor; auto.
      * unfold I2F_Addr in H0.
        destruct p0. destruct p'0.
        intuition. subst.
        
        inversion H. subst.
        destruct p'.
        inversion HP. subst.
        inversion H0. subst.
        unfold I2F_Iptr in *.
        apply unsigned_inj in H1.
        subst.
        contradiction.
      * unfold I2F_Addr in H0.
        destruct p0. destruct p'0.
        intuition. subst.
        inversion H. subst.
        destruct p.
        inversion HP. subst.
        inversion H0. subst.
        unfold I2F_Iptr in *.
        subst.
        contradiction.
    + repeat constructor.
    + repeat constructor.
Qed.      
        
      
Lemma I2F_EOUP_valid_pointer_byte p p' idx byte byte'  
  (HP: I2F_Addr p p')
  (HB: I2F_memory_byte byte byte') :
  I2F_EOUP Logic.eq (@valid_pointer_byte PInf p idx byte) (@valid_pointer_byte PFin p' idx byte').
Proof.
  inversion HB.
  - repeat constructor.
  - subst.
    unfold valid_pointer_byte.
    repeat break_match_goal_safe; subst; try constructor; auto.
    + unfold I2F_Addr in HP.
      destruct p0.
      destruct p'.
      destruct p'0.
      unfold I2F_Addr in H.
      intuition. subst.
      
      unfold I2F_Iptr in *.
      subst.
      apply unsigned_inj in H2. subst.
      contradiction.
    + unfold I2F_Addr in HP.
      destruct p0.
      destruct p'0.
      destruct p.
      unfold I2F_Addr in H.
      intuition. subst.
      unfold I2F_Iptr in *.
      subst.
      contradiction.
  - cbn.
    eapply I2F_EOUP_valid_pointer_bits; auto.
Qed.    
  
                                  
Lemma I2F_EOUP_valid_pointer_bytes p p' idx bytes bytes' 
  (HP: I2F_Addr p p')
  (HB: Forall2 I2F_memory_byte bytes bytes') :
  I2F_EOUP Logic.eq (@valid_pointer_bytes PInf p idx bytes) (@valid_pointer_bytes PFin p' idx bytes').
Proof.
  revert idx.
  induction HB; intros.
  - repeat constructor.
  - eapply I2F_EOUP_bind with (RA:=Logic.eq).
    apply I2F_EOUP_valid_pointer_byte; auto.
    intros. subst.
    destruct a2; auto.
    repeat constructor.
Qed.    

Lemma I2F_EOUP_memory_bytes_to_pointer dbs dbs'
  (F : Forall2 I2F_memory_byte dbs dbs') :
  I2F_EOUP I2F_Addr (memory_bytes_to_pointer dbs) (memory_bytes_to_pointer dbs').
Proof.
  unfold memory_bytes_to_pointer.
  inversion F.
  - constructor.
  - inversion H.
    + constructor.
    + subst.
      eapply I2F_EOUP_bind with (RA:=Logic.eq).
      apply I2F_EOUP_valid_pointer_bytes; auto.
      intros; subst.
      destruct a2; auto.
      constructor; auto.
    + subst.
      inversion H3; auto; subst.
      inversion H1; subst; auto.
      eapply I2F_EOUP_bind with (RA:=Logic.eq).
      apply I2F_EOUP_valid_pointer_bytes; auto.
      intros; subst.
      destruct a2; auto.
      constructor; auto.
Qed.      
      

(** * Deserialization at the byte type [DTYPE_B]

    [memory_bytes_to_dvalue_base] at [DTYPE_B] goes through
    [all_poison_bytes] and [memory_bytes_to_byte_value]; the latter is
    the one place in deserialization that *inspects* the result of
    [memory_bytes_to_int] / [memory_bytes_to_pointer] and falls through
    to the next representation rather than propagating it. The three
    groups of lemmas below supply, in order: the bit-level [Forall2]
    plumbing, the agreement of the poison test, and the branch alignment
    that the fall-through needs. *)

(** [rev_loop_acc] is built from [N.recursion], which does not reduce on
    [N.succ]; one unfolding equation makes it usable by induction. *)
Lemma rev_loop_acc_succ {A} (f : N -> A) n :
  N.rev_loop_acc f (N.succ n) = (fun i acc => N.rev_loop_acc f n (1+i)%N (f i :: acc)).
Proof.
  unfold N.rev_loop_acc.
  apply (@N.recursion_succ (N -> list A -> list A) Logic.eq); auto.
  repeat intro; subst; auto.
Qed.

Lemma Forall2_rev_loop_acc {A B} (R : A -> B -> Prop) (f : N -> A) (g : N -> B)
  (HR : forall i, R (f i) (g i)) :
  forall n i acc acc', Forall2 R acc acc' ->
    Forall2 R (N.rev_loop_acc f n i acc) (N.rev_loop_acc g n i acc').
Proof.
  intros n; induction n using N.peano_ind; intros i acc acc' HA.
  - cbn; auto.
  - rewrite !rev_loop_acc_succ; cbn.
    apply IHn; constructor; auto.
Qed.

(** ** Bit-level plumbing *)
Lemma I2F_memory_byte_to_memory_bits mb mb' :
  I2F_memory_byte mb mb' ->
  Forall2 I2F_memory_bit (memory_byte_to_memory_bits mb) (memory_byte_to_memory_bits mb').
Proof.
  intros H; red in H; inversion H; subst.
  - (* BYTE__I *)
    apply Forall2_rev_append; [| constructor].
    apply Forall2_rev_loop_acc; [intros; constructor; auto | constructor].
  - (* BYTE_Pointer *)
    apply Forall2_rev_append; [| constructor].
    apply Forall2_rev_loop_acc; [intros; constructor; auto | constructor].
  - (* BYTE_Mixed *)
    assumption.
Qed.

Lemma I2F_get_bits_of_memory_byte_list dbs dbs' :
  Forall2 I2F_memory_byte dbs dbs' ->
  forall bit_sz acc acc',
    Forall2 I2F_memory_bit acc acc' ->
    Forall2 I2F_memory_bit
      (get_bits_of_memory_byte_list bit_sz dbs acc)
      (get_bits_of_memory_byte_list bit_sz dbs' acc').
Proof.
  intros F; induction F as [| b b' bs bs' HB F IH]; intros bit_sz acc acc' HA; cbn.
  - break_match_goal.
    + auto. 
    + apply Forall2_rev_loop_acc; intros; auto.
  - assert (HBITS : Forall2 I2F_memory_bit
                      (memory_byte_to_memory_bits b) (memory_byte_to_memory_bits b'))
      by (apply I2F_memory_byte_to_memory_bits; auto).
    break_match_goal.
    + apply Forall2_rev_append; auto; now apply Forall2_take.
    + apply IH; now apply Forall2_rev_append.
Qed.

(** ** The poison test agrees on related byte lists

    [all_poison_bytes] guards the [DVALUE_Poison] short-circuit, so the
    two sides must take the same branch of the [if]. *)
Lemma I2F_is_poison_bit b b' :
  I2F_memory_bit b b' -> is_poison_bit b = is_poison_bit b'.
Proof. intros H; inversion H; subst; reflexivity. Qed.

Lemma I2F_all_poison_bits bits bits' :
  Forall2 I2F_memory_bit bits bits' -> all_poison_bits bits = all_poison_bits bits'.
Proof.
  intros F; unfold all_poison_bits; induction F; cbn; auto.
  erewrite I2F_is_poison_bit by eauto; now rewrite IHF.
Qed.

Lemma I2F_is_all_poison_byte mb mb' :
  I2F_memory_byte mb mb' -> is_all_poison_byte mb = is_all_poison_byte mb'.
Proof.
  intros H; red in H; inversion H; subst; cbn [is_all_poison_byte]; auto.
  now apply I2F_all_poison_bits.
Qed.

Lemma I2F_all_poison_bytes dbs dbs' :
  Forall2 I2F_memory_byte dbs dbs' -> all_poison_bytes dbs = all_poison_bytes dbs'.
Proof.
  intros F; unfold all_poison_bytes; induction F; cbn; auto.
  erewrite I2F_is_all_poison_byte by eauto; now rewrite IHF.
Qed.

(** ** Branch alignment

    [I2F_EOUP]'s cuts (UB on the left, OOM on the right) let the two
    sides diverge, which is fine wherever the computation is used
    monadically --- but [memory_bytes_to_byte_value] pattern-matches on
    [memory_bytes_to_int] / [memory_bytes_to_pointer] and silently falls
    through on anything that is not a [NoPois] return, so a cut on one
    side would send the two sides down different branches. Neither
    computation can actually be UB or OOM ([no_cut] below), which
    collapses [I2F_EOUP] to the three lockstep shapes. *)

Definition no_cut {A} (c : @EOU A) : Prop :=
  match c with
  | raise_ub _ => False
  | raise_oom _ => False
  | _ => True
  end.

Lemma no_cut_ret {A} (a : A) : no_cut (raise_ret a).
Proof. exact I. Qed.

Lemma no_cut_bind_EOUP {A B} (c : EOUP A) (k : A -> EOUP B) :
  no_cut c -> (forall a, no_cut (k a)) -> no_cut (bind (m := EOUP) c k).
Proof. destruct c as [s|s|s|[|a]]; cbn; auto; contradiction. Qed.

Lemma no_cut_map_monad_EOUP {A B} (f : A -> EOUP B) :
  (forall a, no_cut (f a)) -> forall l, no_cut (map_monad (m := EOUP) f l).
Proof.
  intros Hf l; induction l as [| a l IH]; [exact I |].
  cbn [map_monad].
  apply no_cut_bind_EOUP; auto; intros b.
  apply no_cut_bind_EOUP; auto; intros bs; exact I.
Qed.

Section NoCut.
  Context {Pa : Params}.

  Lemma no_cut_memory_bit_to_bit mb : no_cut (memory_bit_to_bit mb).
  Proof. destruct mb; exact I. Qed.

  Lemma no_cut_memory_bits_to_Z bits : no_cut (memory_bits_to_Z bits).
  Proof.
    unfold memory_bits_to_Z.
    apply no_cut_bind_EOUP; [| intros; exact I].
    apply no_cut_map_monad_EOUP, no_cut_memory_bit_to_bit.
  Qed.

  Lemma no_cut_memory_byte_to_Z mb : no_cut (memory_byte_to_Z mb).
  Proof. destruct mb; try exact I; apply no_cut_memory_bits_to_Z. Qed.

  (* One unfolding step; [cbn] would reduce two levels deep. *)
  Lemma concat_bytes_Z_mixed_cons2 extra acc b d rest :
    concat_bytes_Z_mixed extra acc (b :: d :: rest) =
      z <- memory_byte_to_Z b ;; concat_bytes_Z_mixed extra (acc + z)%Z (d :: rest).
  Proof. destruct b; reflexivity. Qed.

  Lemma no_cut_concat_bytes_Z_mixed extra : forall dbs acc,
      no_cut (concat_bytes_Z_mixed extra acc dbs).
  Proof.
    induction dbs as [| b rest IH]; intros acc; [exact I |].
    destruct rest as [| d rest'].
    - destruct b; try exact I.
      cbn; apply no_cut_bind_EOUP; [apply no_cut_memory_bits_to_Z | intros; exact I].
    - rewrite concat_bytes_Z_mixed_cons2.
      apply no_cut_bind_EOUP; [apply no_cut_memory_byte_to_Z | intros; apply IH].
  Qed.

  Lemma no_cut_memory_bytes_to_int sz dbs : no_cut (memory_bytes_to_int sz dbs).
  Proof.
    unfold memory_bytes_to_int; break_match_goal.
    - apply no_cut_concat_bytes_Z_mixed.
    - apply no_cut_bind_EOUP; [| intros; exact I].
      apply no_cut_map_monad_EOUP, no_cut_memory_byte_to_Z.
  Qed.

  Lemma no_cut_valid_pointer_bits p base : forall bits offset,
      no_cut (valid_pointer_bits p base offset bits).
  Proof.
    induction bits as [| b bits IH]; intros offset; [exact I |].
    destruct b; try exact I.
    cbn; repeat break_match_goal; try exact I; apply IH.
  Qed.

  Lemma no_cut_valid_pointer_byte p idx mb : no_cut (valid_pointer_byte p idx mb).
  Proof.
    destruct mb as [q i | x | bits]; cbn.
    - break_match_goal; exact I.
    - exact I.
    - apply no_cut_valid_pointer_bits.
  Qed.

  Lemma no_cut_valid_pointer_bytes p : forall bytes idx,
      no_cut (valid_pointer_bytes p idx bytes).
  Proof.
    induction bytes as [| b bs IH]; intros idx; [exact I |].
    cbn [valid_pointer_bytes].
    apply no_cut_bind_EOUP; [apply no_cut_valid_pointer_byte |].
    intros []; [apply IH | exact I].
  Qed.

  Lemma no_cut_memory_bytes_to_pointer dbs : no_cut (memory_bytes_to_pointer dbs).
  Proof.
    unfold memory_bytes_to_pointer; repeat break_match_goal; try exact I.
    all: apply no_cut_bind_EOUP; [apply no_cut_valid_pointer_bytes |];
         intros []; exact I.
  Qed.
End NoCut.

(** ** Putting it together *)

Lemma I2F_EOUP_no_cut_inv {A1 A2} (RR : A1 -> A2 -> Prop) c1 c2 :
  I2F_EOUP RR c1 c2 -> no_cut c1 -> no_cut c2 ->
  (exists a1 a2, c1 = raise_ret (NoPois a1) /\ c2 = raise_ret (NoPois a2) /\ RR a1 a2)
  \/ (c1 = raise_ret (@Pois A1) /\ c2 = raise_ret (@Pois A2))
  \/ (exists s1 s2, c1 = raise_error s1 /\ c2 = raise_error s2).
Proof. intros [] N1 N2; eauto 10; contradiction. Qed.

Lemma I2F_mixed_fallback sz dbs dbs' :
  Forall2 I2F_memory_byte dbs dbs' ->
  I2F_dvalue_bv
    (@BYTE_Mixed PInf sz (rev_append (get_bits_of_memory_byte_list (N.pos sz) dbs []) []))
    (@BYTE_Mixed PFin sz (rev_append (get_bits_of_memory_byte_list (N.pos sz) dbs' []) [])).
Proof.
  intros F; constructor.
  apply Forall2_rev_append; [| constructor].
  apply I2F_get_bits_of_memory_byte_list; auto.
Qed.

Lemma I2F_memory_bytes_to_byte_value sz dbs dbs' :
  Forall2 I2F_memory_byte dbs dbs' ->
  I2F_EOU I2F_dvalue_bv
    (@memory_bytes_to_byte_value PInf sz dbs)
    (@memory_bytes_to_byte_value PFin sz dbs').
Proof.
  intros F.
  assert (PTR : I2F_EOU I2F_dvalue_bv
     (match @memory_bytes_to_pointer PInf dbs with
      | raise_ret (NoPois p) => ret (@BYTE_Pointer PInf sz p 0)
      | _ => ret (@BYTE_Mixed PInf sz
                    (rev_append (get_bits_of_memory_byte_list (N.pos sz) dbs []) []))
      end)
     (match @memory_bytes_to_pointer PFin dbs' with
      | raise_ret (NoPois p) => ret (@BYTE_Pointer PFin sz p 0)
      | _ => ret (@BYTE_Mixed PFin sz
                    (rev_append (get_bits_of_memory_byte_list (N.pos sz) dbs' []) []))
      end)).
  { pose proof (I2F_EOUP_memory_bytes_to_pointer F) as HP.
    apply I2F_EOUP_no_cut_inv in HP;
      [| apply (@no_cut_memory_bytes_to_pointer PInf)
       | apply (@no_cut_memory_bytes_to_pointer PFin) ].
    destruct HP as [(p1 & p2 & -> & -> & HA) | [(-> & ->) | (s1 & s2 & -> & ->)]]; cbn.
    - constructor; now constructor.
    - constructor; now apply I2F_mixed_fallback.
    - constructor; now apply I2F_mixed_fallback. }
  unfold memory_bytes_to_byte_value.
  pose proof (I2F_memory_bytes_to_int sz F) as HI.
  apply I2F_EOUP_no_cut_inv in HI;
    [| apply (@no_cut_memory_bytes_to_int PInf)
     | apply (@no_cut_memory_bytes_to_int PFin) ].
  destruct HI as [(x1 & x2 & -> & -> & <-) | [(-> & ->) | (s1 & s2 & -> & ->)]]; cbn; auto.
  constructor; constructor.
Qed.

(** Deserialization at base types: every arm funnels through the shared
      [EOUP] stream of [memory_byte_value]s (equal by [I2F_mbyte]);
      [DTYPE_Iptr] and [DTYPE_Pointer] then run the finite in-range
      analysis. *)
Lemma I2F_memory_bytes_to_dvalue_base : forall t dbs dbs',
    Forall2 I2F_memory_byte dbs dbs' ->
    I2F_EOU I2F_dvalue_base
      (@memory_bytes_to_dvalue_base PInf dbs t)
      (@memory_bytes_to_dvalue_base PFin dbs' t).
Proof.
  intros t dbs dbs' F; destruct t; cbn; auto.
  - (* DTYPE_I *)
    eapply I2F_absorb_pois; eauto.
    apply I2F_memory_bytes_to_int; auto.
    intros; subst; repeat constructor.
  - (* DTYPE_Iptr *)
    eapply I2F_absorb_pois; eauto.
    apply I2F_EOUP_map_monad2 with (RA:=I2F_memory_byte); auto.
    apply I2F_memory_byte_to_Z; auto.
    intros.
    unfold from_Z_bits.
      repeat (break_match_goal_safe; cbn); auto.
      apply Forall2_eq in H. subst.
      repeat constructor.
      unfold I2F_Iptr.
      i2f_in_range_case.
      erewrite <- in_bounds_case; auto.
  - (* DTYPE_Pointer *)
    eapply I2F_absorb_pois; eauto.
    apply I2F_EOUP_memory_bytes_to_pointer; auto.
  - (* DTYPE_FP *)
    destruct fp; cbn; auto.
    eapply I2F_absorb_pois; eauto.
    apply I2F_EOUP_map_monad2 with (RA:=I2F_memory_byte); auto.
    apply I2F_memory_byte_to_Z.
    intros.
    apply Forall2_eq in H. subst.
    repeat constructor.
    eapply I2F_absorb_pois; eauto.
    apply I2F_EOUP_map_monad2 with (RA:=I2F_memory_byte); auto.
    apply I2F_memory_byte_to_Z.
    intros.
    apply Forall2_eq in H. subst.
    repeat constructor.
  - (* DTYPE_B *)
    erewrite I2F_all_poison_bytes by eauto.
    break_match_goal; [repeat constructor |].
    pose proof (I2F_memory_bytes_to_byte_value sz F) as HB.
    destruct HB as [a1 a2 HA | s1 s2 | s m | m s]; cbn; constructor.
    now constructor.
Qed.

(** Deserialization: related byte lists deserialize to related values;
      aggregates recurse through the [Forall2] list combinators. *)
Lemma I2F_memory_bytes_to_dvalue : forall t dbs dbs',
    Forall2 I2F_memory_byte dbs dbs' ->
    I2F_EOU I2F_dvalue
      (@memory_bytes_to_dvalue PInf dbs t)
      (@memory_bytes_to_dvalue PFin dbs' t).
Proof.
  intros t; induction t using dtyp_ind; intros dbs dbs' F.
  - (* DTYPE_Base *)
    cbn.
    eapply I2F_EOU_bind;
      [apply I2F_memory_bytes_to_dvalue_base; auto|].
    intros; do 2 constructor; auto.
  - (* DTYPE_Struct: [cbn] normalizes both sides' paddings to the same
         terms (the alignment payload is only tested for [Some]-ness, so
         it reduces away entirely); both flavours then run the same
         lockstep loop induction *)
    destruct p; cbn.
    + match goal with
      | |- context [?L 0%N fields dbs] => set (goL := L)
      end.
      match goal with
      | |- context [?R 0%N fields dbs'] => set (goR := R)
      end.
      assert (GO : forall offset xs ys,
                 Forall2 I2F_memory_byte xs ys ->
                 I2F_EOU (Forall2 I2F_dvalue)
                   (goL offset fields xs) (goR offset fields ys)).
      { clear F.
        match goal with
        | IHu : forall u, In u fields -> _ |- _ => revert IHu
        end.
        induction fields as [| u fs IHf]; intros IH offset xs ys F.
        - unfold goL, goR; cbn; repeat constructor.
        - unfold goL, goR; cbn; fold goL; fold goR.
          eapply I2F_EOU_bind;
            [ apply IH; [now left | apply Forall2_take, Forall2_drop; auto] |].
          intros f1 f2 Hf.
          eapply I2F_EOU_bind;
            [ apply IHf;
              [ intros u0 IN; apply IH; now right
              | apply Forall2_drop, Forall2_drop; auto ]
            |].
          intros r1 r2 Hr.
          do 2 constructor; auto.
      }
      specialize (GO 0%N dbs dbs' F).
      revert GO; generalize (goL 0%N fields dbs) (goR 0%N fields dbs');
        intros m1 m2 GO; destruct GO; cbn; auto.
    + match goal with
      | |- context [?L 0%N fields dbs] => set (goL := L)
      end.
      match goal with
      | |- context [?R 0%N fields dbs'] => set (goR := R)
      end.
      assert (GO : forall offset xs ys,
                 Forall2 I2F_memory_byte xs ys ->
                 I2F_EOU (Forall2 I2F_dvalue)
                   (goL offset fields xs) (goR offset fields ys)).
      { clear F.
        match goal with
        | IHu : forall u, In u fields -> _ |- _ => revert IHu
        end.
        induction fields as [| u fs IHf]; intros IH offset xs ys F.
        - unfold goL, goR; cbn; repeat constructor.
        - unfold goL, goR; cbn; fold goL; fold goR.
          eapply I2F_EOU_bind;
            [ apply IH; [now left | apply Forall2_take, Forall2_drop; auto] |].
          intros f1 f2 Hf.
          eapply I2F_EOU_bind;
            [ apply IHf;
              [ intros u0 IN; apply IH; now right
              | apply Forall2_drop, Forall2_drop; auto ]
            |].
          intros r1 r2 Hr.
          do 2 constructor; auto.
      }
      specialize (GO 0%N dbs dbs' F).
      revert GO; generalize (goL 0%N fields dbs) (goR 0%N fields dbs');
        intros m1 m2 GO; destruct GO; cbn; auto.
  - (* DTYPE_Array *)
    cbn.
    break_match_goal_safe.
    + eapply I2F_EOU_bind;
        [ eapply I2F_EOU_map_monad2 with (RA := Forall2 I2F_memory_byte);
          [ apply Forall2_repeatN; constructor
          | intros ? ? ?; auto ]
        | intros ? ? ?; do 2 constructor; auto ].
    + eapply I2F_EOU_bind;
        [ eapply I2F_EOU_map_monad2 with (RA := Forall2 I2F_memory_byte);
          [ apply Forall2_split_every_nil; auto
          | intros ? ? ?; auto ]
        | intros ? ? ?; do 2 constructor; auto ].
Qed.

(* The two models share their [Sizeof] instance, but its uses appear
     behind distinct [Params] projections; align them syntactically. *)
Lemma I2F_sizeof_dtyp : forall t,
    @sizeof_dtyp (@SIZE PInf) t = @sizeof_dtyp (@SIZE PFin) t.
Proof. reflexivity. Qed.

Lemma I2F_max_alignment : forall ts,
    @max_preferred_dtyp_alignment (@SIZE PInf) ts
    = @max_preferred_dtyp_alignment (@SIZE PFin) ts.
Proof. reflexivity. Qed.

Lemma length_take {A B} (l : list A) (l' : list B) n :
  length l = length l' -> length (take n l) = length (take n l').
Proof.
  revert l' n.
  induction l; intros.
  - destruct l'.  reflexivity.
    inversion H.
  - destruct l'.  inversion H.
    cbn. destruct n; auto.
    cbn. erewrite IHl; eauto.
Qed.    

Lemma length_drop {A B} (l : list A) (l' : list B) n :
  length l = length l' -> length (drop n l) = length (drop n l').
Proof.
  revert l' n.
  induction l; intros.
  - destruct l'.  reflexivity.
    inversion H.
  - destruct l'.  inversion H.
    cbn. destruct n; auto.
Qed.


Lemma I2F_memory_byte_of_dvalue_bv (bit_sz : positive) bv bv' (idx : N) :
  I2F_dvalue_bv bv bv' ->
  I2F_memory_byte (@memory_byte_of_dvalue_bv PInf bit_sz bv idx) (@memory_byte_of_dvalue_bv PFin bit_sz bv' idx).
Proof.
  intros H.
  inversion H; subst.
  - unfold memory_byte_of_dvalue_bv.
    destruct (negb (N.pos bit_sz mod 8 =? 0)%N && (idx + 1 =? sizeof_dtyp (DTYPE_I bit_sz))%N).
    repeat constructor.
    apply Forall2_app.
    apply Forall2_map2.
    intros.
    constructor.
    apply Forall2_repeat.
    constructor.
    constructor.
  - unfold memory_byte_of_dvalue_bv.
    constructor. assumption.
  - unfold memory_byte_of_dvalue_bv.
    constructor.
    apply Forall2_app.
    apply Forall2_take.
    destruct ((idx =? 0)%N); auto.
    apply Forall2_drop; auto.
    apply Forall2_length in H0.    
    destruct ((idx =? 0)%N).
    + rewrite (length_take bits bits'); auto.
      destruct (negb (N.of_nat (Datatypes.length (take 8 bits')) =? 8)%N); auto.
    + rewrite (length_take (drop _ bits) (drop (8 * N.pred idx) bits')); auto.
      destruct (negb (N.of_nat (Datatypes.length (take 8 (drop (8 * N.pred idx) bits'))) =? 8)%N).
      apply Forall2_repeat; auto. constructor.
      apply length_drop. auto.
Qed.


Lemma I2F_poison_memory_byte : I2F_memory_byte (@poison_memory_byte PInf) (@poison_memory_byte PFin).
Proof.
  constructor.
  apply Forall2_repeat.
  constructor.
Qed.  


(** * Serialization: [dvalue_to_memory_bytes]

    [acc_dvalue_to_memory_bytes_h] has the same shape as [freeze]: an
    outer [Fixpoint] over the [dvalue] with two anonymous inner loops
    (over a struct's fields and over an array's elements). As there, we
    name the loops and give their unfolding equations, all of which hold
    by conversion --- [cbn] would splice the outer fix into every goal
    and leave the recursive calls unfolded.

    Note that both loops close over [pad_to] (used in their base case)
    but not over the struct's own [pad], which the current definition
    computes and then never uses. *)
Section SerUnfold.
  Context {Pa : Params}.

  Definition accumulate_struct_bytes (pad_to : option N) (pad : option N)
    : list dvalue -> list dtyp -> N -> list memory_byte -> EOU (N * list memory_byte) :=
    fix loop fields types (offset : N) (acc : list memory_byte) : EOU (N * list memory_byte) :=
      match fields, types with
      | [], [] => ret (accumulate_padding offset pad_to acc)
      | f::fs, dt::dts =>
          let field_pad :=
            if pad
            then Some (pad_amount (preferred_alignment (dtyp_alignment dt)) offset)
            else None
          in
          '(offset', bs) <- acc_dvalue_to_memory_bytes_h dt f offset field_pad acc ;;
          loop fs dts offset' bs
      | _, _ => raise_error "type-mismatch: structs / fields have different lengths"
      end.

  Definition accumulate_array_bytes (pad_to : option N) (elt_t : dtyp)
    : list dvalue -> N -> list memory_byte -> EOU (N * list memory_byte) :=
    fix loop elts (offset : N) (acc : list memory_byte) : EOU (N * list memory_byte) :=
      match elts with
      | [] => ret (accumulate_padding offset pad_to acc)
      | e::es =>
          '(offset', bs) <- acc_dvalue_to_memory_bytes_h elt_t e offset
                              (Some (pad_amount (preferred_alignment (dtyp_alignment elt_t)) offset)) acc ;;
          loop es offset' bs
      end.

  Lemma ser_Base_eq : forall dtb dv offset pad_to acc,
      acc_dvalue_to_memory_bytes_h (DTYPE_Base dtb) (DVALUE_Base dv) offset pad_to acc =
        let '(offset', bs) := acc_memory_bytes_of_dvalue_base dtb dv offset acc in
        ret (accumulate_padding offset' pad_to bs).
  Proof. reflexivity. Qed.

  Lemma ser_Struct_eq : forall packed dts b fields offset pad_to acc,
      acc_dvalue_to_memory_bytes_h (DTYPE_Struct packed dts) (DVALUE_Struct b fields) offset pad_to acc =
        accumulate_struct_bytes pad_to
          (if packed then None else Some (max_preferred_dtyp_alignment dts))
          fields dts offset acc.
  Proof. reflexivity. Qed.

  Lemma ser_Array_eq : forall p sz elt_t b elts offset pad_to acc,
      acc_dvalue_to_memory_bytes_h (DTYPE_Array p sz elt_t) (DVALUE_Array b elts) offset pad_to acc =
        accumulate_array_bytes pad_to elt_t elts offset acc.
  Proof. reflexivity. Qed.

  Lemma acc_struct_nil : forall pad_to pad offset acc,
      accumulate_struct_bytes pad_to pad [] [] offset acc =
        ret (accumulate_padding offset pad_to acc).
  Proof. reflexivity. Qed.

  Lemma acc_struct_nil_cons : forall pad_to pad dt dts offset acc,
      accumulate_struct_bytes pad_to pad [] (dt::dts) offset acc =
        raise_error "type-mismatch: structs / fields have different lengths".
  Proof. reflexivity. Qed.

  Lemma acc_struct_cons_nil : forall pad_to pad f fs offset acc,
      accumulate_struct_bytes pad_to pad (f::fs) [] offset acc =
        raise_error "type-mismatch: structs / fields have different lengths".
  Proof. reflexivity. Qed.

  Lemma acc_struct_cons : forall pad_to pad f fs dt dts offset acc,
      accumulate_struct_bytes pad_to pad (f::fs) (dt::dts) offset acc =
        '(offset', bs) <- acc_dvalue_to_memory_bytes_h dt f offset
                            (if pad
                             then Some (pad_amount (preferred_alignment (dtyp_alignment dt)) offset)
                             else None) acc ;;
        accumulate_struct_bytes pad_to pad fs dts offset' bs.
  Proof. reflexivity. Qed.

  Lemma acc_array_nil : forall pad_to elt_t offset acc,
      accumulate_array_bytes pad_to elt_t [] offset acc =
        ret (accumulate_padding offset pad_to acc).
  Proof. reflexivity. Qed.

  Lemma acc_array_cons : forall pad_to elt_t e es offset acc,
      accumulate_array_bytes pad_to elt_t (e::es) offset acc =
        '(offset', bs) <- acc_dvalue_to_memory_bytes_h elt_t e offset
                            (Some (pad_amount (preferred_alignment (dtyp_alignment elt_t)) offset)) acc ;;
        accumulate_array_bytes pad_to elt_t es offset' bs.
  Proof. reflexivity. Qed.

End SerUnfold.

(** ** Refinement

    [I2F_ser_state] is the invariant threaded through the accumulator
    loops: the two sides agree on the running byte offset (so they make
    the same padding decisions) and their accumulated byte lists are
    related. *)

Definition I2F_ser_state
  (x : N * list (@memory_byte PInf)) (y : N * list (@memory_byte PFin)) : Prop :=
  fst x = fst y /\ Forall2 I2F_memory_byte (snd x) (snd y).

Lemma I2F_accumulate_poison_bytes : forall n acc acc',
    Forall2 I2F_memory_byte acc acc' ->
    Forall2 I2F_memory_byte
      (@accumulate_poison_bytes PInf n acc) (@accumulate_poison_bytes PFin n acc').
Proof.
  intros n acc acc' HA; unfold accumulate_poison_bytes, accumulate_memory_bytes.
  apply Forall2_rev_loop_acc; auto.
  intros; apply I2F_poison_memory_byte.
Qed.

Lemma I2F_accumulate_padding : forall offset pad_to acc acc',
    Forall2 I2F_memory_byte acc acc' ->
    I2F_ser_state (@accumulate_padding PInf offset pad_to acc)
                  (@accumulate_padding PFin offset pad_to acc').
Proof.
  intros offset [align |] acc acc' HA; cbn; split; cbn; auto.
  now apply I2F_accumulate_poison_bytes.
Qed.

Lemma I2F_acc_memory_bytes_of_dvalue_base : forall dtb dv dv',
    I2F_dvalue_base dv dv' ->
    forall offset acc acc',
      Forall2 I2F_memory_byte acc acc' ->
      I2F_ser_state (@acc_memory_bytes_of_dvalue_base PInf dtb dv offset acc)
                    (@acc_memory_bytes_of_dvalue_base PFin dtb dv' offset acc').
Proof.
  intros dtb dv dv' H offset acc acc' HA.
  unfold acc_memory_bytes_of_dvalue_base; split; cbn; [reflexivity |].
  apply Forall2_rev_loop_acc; auto.
  intros i; inversion H; subst.
  - (* Pointer *) now constructor.
  - (* I *) apply I2F_memory_byte_of_dvalue_bv; constructor.
  - (* Iptr *) red in H0; subst; cbn; constructor.
  - (* Double *) constructor.
  - (* Float *) constructor.
  - (* Poison *) apply I2F_poison_memory_byte.
  - (* None *) apply I2F_poison_memory_byte.
  - (* B *) now apply I2F_memory_byte_of_dvalue_bv.
Qed.

Local Notation SER :=
  (fun (a : @dvalue PInf) (b : @dvalue PFin) =>
     forall dt offset pad_to acc acc',
       Forall2 I2F_memory_byte acc acc' ->
       I2F_EOU I2F_ser_state
         (@acc_dvalue_to_memory_bytes_h PInf dt a offset pad_to acc)
         (@acc_dvalue_to_memory_bytes_h PFin dt b offset pad_to acc')).

Lemma I2F_accumulate_struct_bytes : forall fields fields',
    Forall2 SER fields fields' ->
    forall dts pad_to pad offset acc acc',
      Forall2 I2F_memory_byte acc acc' ->
      I2F_EOU I2F_ser_state
        (@accumulate_struct_bytes PInf pad_to pad fields dts offset acc)
        (@accumulate_struct_bytes PFin pad_to pad fields' dts offset acc').
Proof.
  intros fields fields' HF; induction HF as [| f f' fs fs' Hf HF IH];
    intros [| dt dts] pad_to pad offset acc acc' HA.
  - rewrite 2 acc_struct_nil; constructor; now apply I2F_accumulate_padding.
  - rewrite 2 acc_struct_nil_cons; constructor.
  - rewrite 2 acc_struct_cons_nil; constructor.
  - rewrite 2 acc_struct_cons.
    eapply I2F_EOU_bind; [now apply Hf |].
    intros [o1 b1] [o2 b2] [E F]; cbn in E, F; subst.
    now apply IH.
Qed.

Lemma I2F_accumulate_array_bytes : forall elts elts',
    Forall2 SER elts elts' ->
    forall elt_t pad_to offset acc acc',
      Forall2 I2F_memory_byte acc acc' ->
      I2F_EOU I2F_ser_state
        (@accumulate_array_bytes PInf pad_to elt_t elts offset acc)
        (@accumulate_array_bytes PFin pad_to elt_t elts' offset acc').
Proof.
  intros elts elts' HF; induction HF as [| e e' es es' He HF IH];
    intros elt_t pad_to offset acc acc' HA.
  - rewrite 2 acc_array_nil; constructor; now apply I2F_accumulate_padding.
  - rewrite 2 acc_array_cons.
    eapply I2F_EOU_bind; [now apply He |].
    intros [o1 b1] [o2 b2] [E F]; cbn in E, F; subst.
    now apply IH.
Qed.

Lemma I2F_acc_dvalue_to_memory_bytes_h : forall v v', I2F_dvalue v v' -> SER v v'.
Proof.
  intros v v' HDV; induction HDV as [b b' HB | p s1 s2 HF IH | vf s1 s2 HF IH];
    intros dt offset pad_to acc acc' HA;
    destruct dt as [dtb | p' dts | p' sz elt_t].
  - rewrite 2 ser_Base_eq.
    pose proof (I2F_acc_memory_bytes_of_dvalue_base dtb HB offset HA) as HB2.
    destruct (@acc_memory_bytes_of_dvalue_base PInf dtb b offset acc) as [o1 b1].
    destruct (@acc_memory_bytes_of_dvalue_base PFin dtb b' offset acc') as [o2 b2].
    destruct HB2 as [E F]; cbn in E, F; subst.
    constructor; now apply I2F_accumulate_padding.
  - cbn; constructor.
  - cbn; constructor.
  - cbn; constructor.
  - rewrite 2 ser_Struct_eq; now apply I2F_accumulate_struct_bytes.
  - cbn; constructor.
  - cbn; constructor.
  - cbn; constructor.
  - rewrite 2 ser_Array_eq; now apply I2F_accumulate_array_bytes.
Qed.

Lemma I2F_memory_dvalue_to_memory_bytes : forall dt v v',
    I2F_dvalue v v' ->
    forall pad_to,
      I2F_EOU (Forall2 I2F_memory_byte) (@dvalue_to_memory_bytes PInf dt v pad_to ) (@dvalue_to_memory_bytes PFin dt v' pad_to).
Proof.
  intros dt v v' HDV pad_to; unfold dvalue_to_memory_bytes.
  eapply I2F_EOU_bind; [now apply I2F_acc_dvalue_to_memory_bytes_h |].
  intros [o1 b1] [o2 b2] [E F]; cbn in E, F; subst.
  constructor; apply Forall2_rev_append; auto; constructor.
Qed.


(** Bitcast round-trips a value through its byte representation. *)
Lemma I2F_bitcast_bytes : forall v v' t_from t_to,
    I2F_dvalue v v' ->
    I2F_EOU I2F_dvalue
      (dv <- (@dvalue_to_memory_bytes PInf t_from v None) ;;
       @memory_bytes_to_dvalue PInf dv t_to)
      (dv <- (@dvalue_to_memory_bytes PFin t_from v' None) ;;
       @memory_bytes_to_dvalue PFin dv t_to).
Proof.
  intros.
  eapply I2F_EOU_bind with (RA:=Forall2 I2F_memory_byte).
  apply I2F_memory_dvalue_to_memory_bytes; auto.
  apply I2F_memory_bytes_to_dvalue.
Qed.

(* Related base values have equal integer interpretations: the
     convertible shapes carry shared payloads ([DVALUE_I]) or
     [to_Z]-equal ones ([DVALUE_Iptr]); everything else is interpreted
     as [0]. *)
Lemma I2F_dvalue_base_int_unsigned : forall v v',
    I2F_dvalue_base v v' ->
    @dvalue_base_int_unsigned PInf v = @dvalue_base_int_unsigned PFin v'.
Proof.
  intros * H; inversion H; subst; cbn; auto.
Qed.

(** Scalar conversions, by a single destruct of the related conversion
      cases: [Conv_Pure] payloads are related outright, [Conv_ItoP] and
      [Conv_PtoI] go through equal integers ([dvalue_base_int_unsigned]
      and [ptr_to_int] agree on related values) followed by the finite
      [from_Z] in-range analysis, and the failure cases are diagonal. *)
Lemma I2F_convert_pure_base : forall conv t_from t_to v v',
    I2F_dvalue_base v v' ->
    I2F_EOU I2F_dvalue_base
      (@convert_pure_base PInf conv t_from v t_to)
      (@convert_pure_base PFin conv t_from v' t_to).
Proof.
  intros * R.
  unfold convert_pure_base.
  destruct conv; try congruence; cbn; auto.
  all: destruct t_from; auto.
  all: induction R; auto.
  all: destruct t_to; auto.
  all: repeat (break_fast; cbn); eauto.
Qed.

(* OLD Version - needed for impure casts: retaining here, but will be neede
   in the handlder.
 *)
(*
  destruct (@get_conv_case PInf conv t_from v t_to),
    (@get_conv_case PFin conv t_from v' t_to);
    intros CC; cbn in CC; try contradiction; auto.
  (* [Conv_Pure], [Conv_Oom] and [Conv_Illegal] are closed by [auto] *)
  - (* Conv_ItoP: equal integers into [int_to_ptr] *)
    rewrite (I2F_dvalue_base_int_unsigned CC); cbn.
    unfold from_Z_bits.
    repeat (break_match_goal_safe; cbn); auto.
    i2f_in_range_case.
  - (* Conv_PtoI: related pointers expose the same integer *)
    inversion CC; subst; cbn;
      repeat match goal with
        | HA : I2F_Addr ?a ?b |- _ =>
            destruct a, b; destruct HA as [HI ->]; red in HI; subst
        end;
      destruct t_to; cbn; try (repeat constructor);
      unfold from_Z_bits;
      repeat (break_match_goal_safe; cbn); auto;
      i2f_in_range_case.
*)

Lemma I2F_convert_pure cv t_from t_to a b :
  I2F_dvalue a b ->
  I2F_EOU I2F_dvalue (convert_pure cv t_from a t_to) (convert_pure cv t_from b t_to).
Proof.
  intros R.
  inversion R; subst; cbn; auto.
  - destruct (get_base_conversion_type t_from t_to) as [[? ?]|]; cbn; auto.
    specialize (@I2F_convert_pure_base cv d d0 b0 b' H) as HV.
    inversion HV; subst; auto.
  - (* The vector flavour: [i2f_vec_flags] discharges the scalar-array
       flag (a non-vector array is a diagonal error), leaving the
       [get_vector_conversion_type] guard. *)
    i2f_vec_flags; auto.
    destruct (get_vector_conversion_type t_from t_to) as [[? ?]|]; cbn; auto.
    (eapply I2F_EOU_bind;
        [ eapply I2F_EOU_map_monad2;
          [ eauto | intros; apply I2F_dvalue_to_dvalue_base; eauto ] |]).
    intros ? ? ?.
    eapply I2F_EOU_bind;
      [ eapply I2F_EOU_map_monad2 with (RB := I2F_dvalue_base); eauto |].
    intros. apply I2F_convert_pure_base; auto.
    intros. constructor. constructor.
    apply Forall2_map_Base; auto.
Qed.

Lemma I2F_convert ct t_from t_to a b :
  I2F_dvalue a b ->
  I2F_refine (convert ct t_from a t_to) (convert ct t_from b t_to).
Proof.
  intros R.
  destruct ct.
  - cbn.
    destruct (dtyp_eqb t_from t_to); auto.
    break_match_goal_safe.
    apply I2F_refine_lift.
    apply I2F_bitcast_bytes; auto.
    rstep. constructor.
  - cbn.
    apply I2F_refine_lift.
    apply I2F_convert_pure; auto.
  - cbn.
    rstep.
Qed.      


(** * eval_gep *)
(** GEP. The offset computation [handle_gep_h] lives in [EOU Z], a
      parameter-free type: on related indices the two sides are literally
      equal ([to_Z] agrees on related intptrs). *)
Lemma I2F_handle_gep_h : forall vs vs',
    Forall2 I2F_dvalue vs vs' ->
    forall t off,
      @handle_gep_h PInf t off vs = @handle_gep_h PFin t off vs'.
Proof.
  intros vs vs' F; induction F; intros t off; cbn; auto.
  match goal with
  | HC : I2F_dvalue ?c ?c' |- _ =>
      induction HC; cbn; auto
  end;
  try (match goal with
       | HB : I2F_dvalue_base _ _ |- _ =>
           induction HB; cbn; auto
       end);
  try (match goal with
       | HI : I2F_Iptr _ _ |- _ => red in HI; subst
       end);
  repeat (break_goal_fast; cbn); auto.
Qed.

Lemma I2F_handle_gep_ptr : forall t a a' vs vs',
    I2F_Addr a a' ->
    Forall2 I2F_dvalue vs vs' ->
    I2F_EOU I2F_Addr
      (@handle_gep_ptr PInf t a vs)
      (@handle_gep_ptr PFin t a' vs').
Proof.
  intros * HA F.
  destruct a, a'; destruct HA as [HI ->]; red in HI; subst.
  inversion F; subst; cbn; [repeat constructor|].
  match goal with
  | HC : I2F_dvalue ?c ?c' |- _ =>
      inversion HC; subst; cbn; try (repeat constructor)
  end;
  try (match goal with
       | HB : I2F_dvalue_base _ _ |- _ =>
           inversion HB; subst; cbn; try (repeat constructor)
       end);
  try (match goal with
       | HI : I2F_Iptr _ _ |- _ => red in HI; subst
       end);
  unfold from_Z_bits;
  (* bitwidth-literal dispatch first; the [EOU]-typed scrutinees are
         skipped, exposing the offset computations at the top *)
  repeat (break_match_goal_safe; cbn); auto;
  (* align the two offset computations, then reduce them in lockstep *)
  try (erewrite I2F_handle_gep_h by eauto;
       match goal with
       | |- context [match @handle_gep_h ?pa ?u ?o ?ws with _ => _ end] =>
           destruct (@handle_gep_h pa u o ws); cbn; auto
       end);
  repeat (break_match_goal_safe; cbn); repeat constructor; auto; 
  i2f_in_range_case; unfold I2F_Iptr; apply in_bounds_case; auto.
Qed.

Lemma I2F_eval_gep t a1 a2 b1 b2 :
  I2F_dvalue a1 b1 ->
  Forall2 I2F_dvalue a2 b2 ->
  I2F_EOU I2F_dvalue (eval_gep t a1 a2) (eval_gep t b1 b2).
Proof.
  intros R F.
  inversion R; subst; cbn; try (repeat constructor).
  match goal with
  | HB : I2F_dvalue_base _ _ |- _ =>
      inversion HB; subst; cbn; try (repeat constructor)
  end.
  (* Pointer *)
  eapply I2F_EOU_bind; [now apply I2F_handle_gep_ptr|].
  intros; do 3 constructor; auto.
Qed.

(** * extract_element *)
(** Related aggregates split synchronously: either both indexings are out
      of bounds (the shared UB guard), or the parts are pointwise
      related. *)
(* Split the two related aggregates of the goal synchronously: the
     out-of-bounds UB is shared, the mixed cases are contradictory, and
     [tac] finishes the successful case from the pointwise relations. *)
Ltac i2f_split_case i tac :=
  match goal with
  | F : Forall2 I2F_dvalue ?u ?v |- _ =>
      let SP := fresh "SP" in
      pose proof (Forall2_split i F) as SP; revert SP;
      destruct (split [] i u) as [[[? ?] ?] |],
          (split [] i v) as [[[? ?] ?] |];
      intros SP; cbn; try contradiction; auto;
      destruct SP as (? & ? & ?); tac
  end.

(* Related values have equal integer interpretations as indices: the
     only convertible shape is [DVALUE_I], whose payload is shared. *)
Lemma I2F_dvalue_to_Z : forall v v',
    I2F_dvalue v v' ->
    @dvalue_to_Z PInf v = @dvalue_to_Z PFin v'.
Proof.
  intros * H; inversion H; subst; cbn; auto.
  match goal with
  | HB : I2F_dvalue_base _ _ |- _ => inversion HB; subst; cbn; auto
  end.
Qed.

Lemma I2F_extract_element a1 a2 b1 b2 :
  I2F_dvalue a1 b1 ->
  I2F_dvalue a2 b2 ->
  I2F_EOU I2F_dvalue (extract_element a1 a2) (extract_element b1 b2).
Proof.
  intros R1 R2.
  inversion R1; subst; cbn; try (repeat constructor).
  - (* Base. [extract_element] now dispatches on the value rather than on
       a vector type, so this case no longer vanishes: [DVALUE_Poison] is
       the one base value it accepts, every other shape being a diagonal
       error. *)
    match goal with
    | HB : I2F_dvalue_base _ _ |- _ => inversion HB; subst; cbn; repeat constructor
    end.
  - (* Vector *)
    match goal with v : bool |- _ => destruct v end; cbn;
      try (repeat constructor).
    (* The empty vector is its own arm of the match, so split the element
       lists --- by [destruct], not by inverting the [Forall2]: the whole
       [Forall2] has to survive for [i2f_split_case] to pick it up. The
       ragged combinations contradict it. *)
    destruct s1 as [| x xs], s2 as [| y ys]; cbn;
      try (repeat constructor);
      try (match goal with F : Forall2 I2F_dvalue _ _ |- _ => now inversion F end).
    rewrite (I2F_dvalue_to_Z R2).
    destruct (dvalue_to_Z b2) as [i |]; cbn; try (repeat constructor).
    rewrite !split_acc_eq.
    i2f_split_case i ltac:(auto).
Qed.

(** * insert_element *)
Lemma I2F_insert_element dt a1 a2 a3 b1 b2 b3 :
  I2F_dvalue a1 b1 ->
  I2F_dvalue a2 b2 ->
  I2F_dvalue a3 b3 ->
  I2F_EOU I2F_dvalue (insert_element dt a1 a2 a3) (insert_element dt b1 b2 b3).
Proof.
  intros R1 R2 R3.
  (* The vector type is now an explicit argument, so the dispatch on it
     comes first; every non-vector type is a diagonal error. *)
  destruct dt as [ ? | ? ? | [|] sz t ]; cbn; try (repeat constructor).
  inversion R1; subst; cbn; try (repeat constructor).
  - (* Base: poison at vector type stands for a vector of poisons, whose
       length comes from the type's [sz]. *)
    match goal with
    | HB : I2F_dvalue_base _ _ |- _ =>
        inversion HB; subst; cbn; try (repeat constructor)
    end.
    rewrite (I2F_dvalue_to_Z R3).
    destruct (dvalue_to_Z b3) as [i |]; cbn; try (repeat constructor).
    (* [i2f_split_case] splits the two lists against a [Forall2] it finds
       in the context; here the lists are implicit, so supply it. *)
    assert (F : Forall2 I2F_dvalue
                  (repeat (@DVALUE_Base PInf DVALUE_Poison) (N.to_nat sz))
                  (repeat (@DVALUE_Base PFin DVALUE_Poison) (N.to_nat sz)))
      by (apply Forall2_repeat; repeat constructor).
    rewrite !split_acc_eq.
    i2f_split_case i
      ltac:(do 2 constructor; apply Forall2_app; [auto | constructor; auto]).
  - (* Vector *)
    match goal with v : bool |- _ => destruct v end; cbn;
      try (repeat constructor).
    rewrite (I2F_dvalue_to_Z R3).
    destruct (dvalue_to_Z b3) as [i |]; cbn; try (repeat constructor).
    rewrite !split_acc_eq.
    i2f_split_case i
      ltac:(do 2 constructor; apply Forall2_app; [auto | constructor; auto]).
Qed.

(** * shufflevector *)

(* [vector_elts] normalizes a vector operand (a concrete array, or the
   scalar poison encoding padded to the type's length) to its element
   list; related dvalues normalize to related lists, or both fail. *)
Lemma I2F_vector_elts : forall sz v1 v2,
    I2F_dvalue v1 v2 ->
    match vector_elts sz v1, vector_elts sz v2 with
    | Some elts1, Some elts2 => Forall2 I2F_dvalue elts1 elts2
    | None, None => True
    | _, _ => False
    end.
Proof.
  intros sz v1 v2 H; inversion H; subst; cbn.
  - match goal with
    | HB : I2F_dvalue_base _ _ |- _ => inversion HB; subst; cbn; auto
    end.
  - auto.
  - match goal with v : bool |- _ => destruct v end; cbn; auto.
Qed.

Lemma I2F_shuffle_vector dt a1 a2 a3 b1 b2 b3 :
  I2F_dvalue a1 b1 ->
  I2F_dvalue a2 b2 ->
  I2F_dvalue a3 b3 ->
  I2F_EOU I2F_dvalue (shuffle_vector dt a1 a2 a3) (shuffle_vector dt b1 b2 b3).
Proof.
  intros R1 R2 R3.
  destruct dt as [ ? | ? ? | [|] sz t ]; cbn; try (repeat constructor).
  pose proof (I2F_vector_elts sz R1) as V1.
  pose proof (I2F_vector_elts sz R2) as V2.
  destruct (vector_elts sz a1) as [elts1|], (vector_elts sz b1) as [elts1'|];
    try contradiction.
  all: destruct (vector_elts sz a2) as [elts2|], (vector_elts sz b2) as [elts2'|];
    try contradiction.
  all: inversion R3; subst; cbn; try (repeat constructor).
  all: try (match goal with
            | HB : I2F_dvalue_base _ _ |- _ => inversion HB; subst; cbn; repeat constructor
            end).
  all: match goal with v : bool |- _ => destruct v end; cbn; try (repeat constructor).
  eapply Forall2_map_rel; eauto.
  intros idxv idxv' Ridx.
  rewrite (I2F_dvalue_to_Z Ridx).
  destruct (dvalue_to_Z idxv') as [i |]; [| repeat constructor].
  destruct (i <? 0)%Z; [repeat constructor |].
  pose proof (Forall2_nth_error (Forall2_app V1 V2) (Z.to_nat i)) as N.
  destruct (nth_error (elts1 ++ elts2) (Z.to_nat i)) as [?v|],
      (nth_error (elts1' ++ elts2') (Z.to_nat i)) as [v'|];
    try contradiction; [assumption | repeat constructor].
Qed.

(** * extract_value *)
Lemma I2F_extract_value dt a b idxs :
  I2F_dvalue a b ->
  I2F_EOU I2F_dvalue (extract_value dt a (map denote_int_syntax idxs))
    (extract_value dt b (map denote_int_syntax idxs)).
Proof.
  revert dt a b.
  generalize (map denote_int_syntax idxs) as l; clear idxs.
  induction l as [| i l IH]; intros dt a b R; cbn; auto.
  destruct dt as [ dtb | p ts | [|] sz t ]; cbn; try (repeat constructor).
  - (* struct type *)
    destruct (split [] i ts) as [[[pre_t sub_t] post_t] |]; cbn;
      try (repeat constructor).
    inversion R; subst; cbn; try (repeat constructor).
    + match goal with
      | HB : I2F_dvalue_base _ _ |- _ =>
          inversion HB; subst; cbn; try (repeat constructor)
      end.
      apply IH; repeat constructor.
    + i2f_split_case i ltac:(apply IH; auto).
  - (* array type *)
    inversion R; subst; cbn; try (repeat constructor).
    + match goal with
      | HB : I2F_dvalue_base _ _ |- _ =>
          inversion HB; subst; cbn; try (repeat constructor)
      end.
      apply IH; repeat constructor.
    + match goal with v : bool |- _ => destruct v end; cbn;
        try (repeat constructor).
      i2f_split_case i ltac:(apply IH; auto).
Qed.
  
(** * insert_value *)

Lemma I2F_insert_value idxs :
  forall dt a1 a2 b1 b2,
    I2F_dvalue a1 b1 ->
    I2F_dvalue a2 b2 ->
    I2F_EOU I2F_dvalue (insert_value dt a1 a2 (map denote_int_syntax idxs))
      (insert_value dt b1 b2 (map denote_int_syntax idxs)).
Proof.
  generalize (map denote_int_syntax idxs) as l; clear idxs.
  induction l as [| i l IH]; intros dt a1 a2 b1 b2 R1 R2; cbn; auto.
  destruct dt as [ dtb | p ts | [|] sz t ]; cbn; try (repeat constructor).
  - (* struct type *)
    destruct (split [] i ts) as [[[pre_t sub_t] post_t] |]; cbn;
      try (repeat constructor).
    inversion R1; subst; cbn; try (repeat constructor).
    + match goal with
      | HB : I2F_dvalue_base _ _ |- _ =>
          inversion HB; subst; cbn; try (repeat constructor)
      end.
      eapply I2F_EOU_bind; [apply IH; [repeat constructor | auto] |].
      intros; do 2 constructor.
      apply Forall2_app; [apply Forall2_map2; intros; repeat constructor |].
      constructor; [auto | apply Forall2_map2; intros; repeat constructor].
    + i2f_split_case i
        ltac:(eapply I2F_EOU_bind; [apply IH; auto|];
              intros; do 2 constructor;
              apply Forall2_app; [auto | constructor; auto]).
  - (* array type *)
    inversion R1; subst; cbn; try (repeat constructor).
    + match goal with
      | HB : I2F_dvalue_base _ _ |- _ =>
          inversion HB; subst; cbn; try (repeat constructor)
      end.
      destruct (split_indices i sz) as [[pre post] |]; cbn;
        try (repeat constructor).
      eapply I2F_EOU_bind; [apply IH; [repeat constructor | auto] |].
      intros; do 2 constructor.
      apply Forall2_app; [apply Forall2_repeatN; repeat constructor |].
      constructor; [auto | apply Forall2_repeatN; repeat constructor].
    + match goal with v : bool |- _ => destruct v end; cbn;
        try (repeat constructor).
      i2f_split_case i
        ltac:(eapply I2F_EOU_bind; [apply IH; auto|];
              intros; do 2 constructor;
              apply Forall2_app; [auto | constructor; auto]).
Qed.
  
(** * eval_select *)
(** The scalar select: the shared [i1] test picks a side; the poison
      condition computes the (equal) result type of the first operand. *)

(** [dtyp_of_dvalue] computes in the parameter-free [EOU dtyp]: on
      related values the two sides are literally equal (related scalars
      carry equal payloads, and aggregates share their annotations). *)
Lemma I2F_dtyp_of_dvalue_base_eq : forall v v',
    I2F_dvalue_base v v' ->
    @dtyp_of_dvalue_base PInf v = @dtyp_of_dvalue_base PFin v'.
Proof.
  intros * H; inversion H; subst; cbn; auto.
Qed.

Lemma I2F_dtyp_of_dvalue_eq : forall v v',
    I2F_dvalue v v' ->
    @dtyp_of_dvalue PInf v = @dtyp_of_dvalue PFin v'.
Proof.
  induction v using dvalue_ind; intros v' R; inversion R; subst;
    clear R; cbn; auto.
  - (* Base *)
    match goal with
    | HB : I2F_dvalue_base _ _ |- _ =>
        now rewrite (I2F_dtyp_of_dvalue_base_eq HB)
    end.
  - (* Struct: the two [map_monad]s are equal *)
    match goal with
    | F2 : Forall2 I2F_dvalue ?l1 ?l2 |- _ =>
        assert (MM : map_monad (@dtyp_of_dvalue PInf) l1
                     = map_monad (@dtyp_of_dvalue PFin) l2);
        [| rewrite MM; reflexivity ]
    end.
    match goal with
    | F2 : Forall2 I2F_dvalue _ _, IH : Forall _ _ |- _ =>
        revert IH; induction F2 as [| u u' us us' HU HUS IHUS]
    end; intros FIH; cbn; auto.
    inversion FIH; subst.
    match goal with
    | HP : forall _, I2F_dvalue u _ -> _ |- _ => rewrite (HP _ HU)
    end.
    rewrite IHUS by assumption; reflexivity.
  - (* Array *)
    match goal with
    | F2 : Forall2 I2F_dvalue _ _ |- _ =>
        inversion F2 as [| u u' us us' HU HUS]; subst
    end; cbn; auto.
    match goal with
    | IHl : Forall _ (_ :: _) |- _ => inversion IHl as [| ? ? HP HPS]; subst
    end.
    rewrite (HP _ HU).
    destruct (@dtyp_of_dvalue PFin u') as [ ? | ? | ? | t ]; cbn; auto.
    destruct (@NO_VOID_dec t); cbn; auto.
    assert (EQF : forallb (fun e => match @dtyp_of_dvalue PInf e with
                                 | raise_ret t' => dtyp_eqb t t' | _ => false end) us
                  = forallb (fun e => match @dtyp_of_dvalue PFin e with
                                   | raise_ret t' => dtyp_eqb t t' | _ => false end) us').
    { clear - HUS HPS.
      induction HUS; cbn; auto.
      inversion HPS; subst.
      match goal with
      | HQ : forall _, I2F_dvalue _ _ -> _ |- _ => rewrite (HQ _ ltac:(eassumption))
      end.
      rewrite IHHUS by assumption; reflexivity. }
    rewrite EQF.
    assert (LEN : Datatypes.length us = Datatypes.length us')
      by (eapply Forall2_length; eauto).
    cbn; rewrite LEN; reflexivity.
Qed.

Lemma I2F_eval_select_base_dvalue : forall c c' v1 v2 v1' v2',
    I2F_dvalue_base c c' ->
    I2F_dvalue v1 v1' ->
    I2F_dvalue v2 v2' ->
    I2F_EOU I2F_dvalue
      (@eval_select_base_dvalue PInf c v1 v2)
      (@eval_select_base_dvalue PFin c' v1' v2').
Proof.
  intros * RC R1 R2.
  inversion RC; subst; cbn; try (repeat constructor).
  - (* I sz: the width test then the shared i1 test *)
    repeat (break_goal_fast; cbn); auto.
Qed.

Lemma I2F_eval_select dt a1 a2 a3 b1 b2 b3 :
  I2F_dvalue a1 b1 ->
  I2F_dvalue a2 b2 ->
  I2F_dvalue a3 b3 ->
  I2F_EOU I2F_dvalue (eval_select a1 dt a2 a3) (eval_select b1 dt b2 b3).
Proof.
  intros R1 R2 R3.
  inversion R1; subst; cbn; try ((repeat constructor); eauto; fail).
  - (* Base condition *)
    now apply I2F_eval_select_base_dvalue.
  - (* Vector of conditions *)
    match goal with v : bool |- _ => destruct v end; cbn;
      [| repeat constructor; eauto].
    destruct dt as [ ? | ? ? | [|] sz t ]; cbn; try (repeat constructor).
    eapply I2F_EOU_bind;
      [eapply I2F_EOU_map_monad2;
       [eauto | intros; apply I2F_dvalue_to_dvalue_base; auto]|].
    intros cs cs' FCS.
    inversion R2; subst; cbn; try (repeat constructor).
    + (* v1 base *)
      match goal with
      | HB : I2F_dvalue_base _ _ |- _ =>
          inversion HB; subst; cbn; try (repeat constructor)
      end.
      inversion R3; subst; cbn; try (repeat constructor).
      * match goal with
        | HB : I2F_dvalue_base _ _ |- _ =>
            inversion HB; subst; cbn; repeat constructor
        end.
      * match goal with v : bool |- _ => destruct v end; cbn;
          [| repeat constructor].
        eapply I2F_EOU_bind.
        { eapply I2F_EOU_vec_loop with (RB := prod_rel I2F_dvalue I2F_dvalue).
          - eapply Forall2_combine; [eassumption|].
            eapply Forall2_combine; [apply Forall2_repeat; auto | eassumption].
          - intros c p c' p' HC HP;
              destruct p as [x y], p' as [x' y'], HP as [HX HY]; cbn.
            apply I2F_eval_select_base_dvalue; auto. }
        intros; do 2 constructor; auto.
    + (* v1 vector *)
      match goal with v : bool |- _ => destruct v end; cbn;
        [| repeat constructor].
      inversion R3; subst; cbn; try (repeat constructor).
      * match goal with
        | HB : I2F_dvalue_base _ _ |- _ =>
            inversion HB; subst; cbn; try (repeat constructor)
        end.
        eapply I2F_EOU_bind.
        { eapply I2F_EOU_vec_loop with (RB := prod_rel I2F_dvalue I2F_dvalue).
          - eapply Forall2_combine; [eassumption|].
            eapply Forall2_combine; [eassumption | apply Forall2_repeat; auto].
          - intros c p c' p' HC HP;
              destruct p as [x y], p' as [x' y'], HP as [HX HY]; cbn.
            apply I2F_eval_select_base_dvalue; auto. }
        intros; do 2 constructor; auto.
      * match goal with v : bool |- _ => destruct v end; cbn;
          [| repeat constructor].
        eapply I2F_EOU_bind.
        { eapply I2F_EOU_vec_loop with (RB := prod_rel I2F_dvalue I2F_dvalue).
          - eapply Forall2_combine; [eassumption|].
            eapply Forall2_combine; eassumption.
          - intros c p c' p' HC HP;
              destruct p as [x y], p' as [x' y'], HP as [HX HY]; cbn.
            apply I2F_eval_select_base_dvalue; auto. }
        intros; do 2 constructor; auto.
Qed.
    
Lemma I2F_denote_exp :
  forall (e : exp dtyp) τ, I2F_refine (@denote_exp PInf τ e) (@denote_exp PFin τ e).
Proof with try (rstep || cbnn; simp I2FE_Failure; reflexivity).
  induction e.
  - destruct id; intros; cbn...
  - intros [d|]; cbn...
    apply I2F_refine_lift, I2F_denote_int_syntax_as_int.
  - intros [d|]; cbn...
    apply I2F_refine_lift, I2F_denote_float_syntax_as_float.
  - destruct b; intros ?; cbn...
  - intros; cbn...
  - (* initializer *)
    intros [d|]; cbn...
    apply I2F_refine_lift, I2F_default_dvalue_of_dtyp.
  - cbn; intros.
    erbind.
    + apply ruttc_map_monad.
      intros [d e] HIN; now apply (H (d,e)).
    + intros * HF...
  - cbn; intros []...
  - cbn; intros []...
  - cbn; intros. 
    erbind.
    + apply ruttc_map_monad.
      intros [d e] HIN; now apply (H (d,e)).
    + intros * HF...
  - (* EXP_Packed_struct: the [dtyp] guard is a pure, parameter-free
         computation, related to itself by reflexivity of [I2F_EOU] ---
         no case analysis on the type. *)
    cbn; intros.
    erbind.
    + apply I2F_refine_lift, I2F_EOU_refl.
    + intros [] [] _.
      erbind.
      * apply ruttc_map_monad.
        intros [d e] HIN; now apply (H (d,e)).
      * intros * HF...
  - cbn; intros.
    erbind.
    + apply ruttc_map_monad.
      intros [d e] HIN; now apply (H (d,e)).
    + intros * HF...
  - cbn; intros.
    erbind.
    + apply ruttc_map_monad.
      intros [d e] HIN; now apply (H (d,e)).
    + intros * HF...
  - cbn; intros.
    erbind; [apply IHe1 | intros].
    erbind; [apply IHe2 | intros].
    apply I2F_refine_lift, I2F_eval_iop...
  - destruct v; cbn; intros.
    erbind; [apply IHe | intros].
    apply I2F_refine_lift, I2F_eval_fneg...
  - cbn; intros.
    erbind; [apply IHe1 | intros].
    erbind; [apply IHe2 | intros].
    apply I2F_refine_lift, I2F_eval_icmp; eauto.
  - cbn; intros.
    erbind; [apply IHe1 | intros].
    erbind; [apply IHe2 | intros].
    apply I2F_refine_lift, I2F_eval_fop; eauto.
  - cbn; intros.
    erbind; [apply IHe1 | intros].
    erbind; [apply IHe2 | intros].
    apply I2F_refine_lift, I2F_eval_fcmp; eauto.
  - cbn; intros _.
    erbind; [apply IHe | intros].
    apply I2F_convert; eauto.
  - destruct ptrval; cbn; intros _.
    erbind; [apply IHe | intros].
    erbind.
    + apply ruttc_map_monad.
      intros [x y] HIN; now apply (H (x,y)).
    + intros; apply I2F_refine_lift, I2F_eval_gep; eauto.
  - destruct vec, idx; cbn; intros _.
    erbind; [apply IHe | intros].
    erbind; [apply IHe0 | intros].
    apply I2F_refine_lift, I2F_extract_element; eauto.
  - destruct vec, elt, idx; cbn; intros _.
    erbind; [apply IHe | intros].
    erbind; [erbind; [apply IHe0 | intros] | intros].
    apply I2F_refine_lift,I2F_dvalue_to_dvalue_base; auto.
    erbind; [apply IHe1 | intros].
    apply I2F_refine_lift, I2F_insert_element; auto.
  - destruct vec1,vec2,idxmask; cbn; intros _.
    erbind; [apply IHe | intros].
    erbind; [apply IHe0 | intros].
    erbind; [apply IHe1 | intros].
    apply I2F_refine_lift, I2F_shuffle_vector; auto.
  - destruct vec; cbn; intros _.
    erbind; [apply IHe | intros].
    apply I2F_refine_lift, I2F_extract_value; eauto.
  - destruct vec, elt; cbn; intros _.
    erbind; [apply IHe | intros].
    erbind; [apply IHe0 | intros].
    apply I2F_refine_lift, I2F_insert_value; eauto.
  - destruct cnd,v1,v2; cbn; intros _.
    erbind; [apply IHe | intros].
    erbind; [apply IHe0 | intros].
    erbind; [apply IHe1 | intros].
    apply I2F_refine_lift, I2F_eval_select; auto.
  - destruct v; cbn; intros _.
    erbind; [apply IHe | intros].
    apply I2F_freeze; auto.
  - cbn; intros _...
  - cbn; intros _; destruct m...
    all: try now rstep; constructor; eauto.
    destruct tv; cbn.
    eapply H; eauto.
  - (* EXP_Splat: the vector-type accessor is a pure, parameter-free
         computation, related to itself by reflexivity of [I2F_EOU] ---
         no case analysis on the type. *)
    destruct elt; cbn; intros.
    erbind.
    + apply I2F_refine_lift, I2F_EOU_refl.
    + intros [sz t'] ? <-; cbn.
      erbind; [apply IHe |].
      intros...
Qed.

Lemma I2F_denote_exp' :
  forall e τ,
    I2F_refine_CFG I2F_dvalue (@denote_exp' PInf τ e) (@denote_exp' PFin τ e).
Proof. 
  unfold denote_exp', withCall.
  intros.
  unfold I2F_refine_CFG.
  eapply ruttc_translate_inr'; cycle -1.
  apply I2F_denote_exp.
  all:clear.
  - exact I2F_cutUB_CFG.
  - exact I2F_cutOOM_CFG.
  (* [rutt_cutoff.inr_prerel] of the (computing) sum is definitionally
       its right component *)
  - intros A B; split; intros e1 e2 HR.
    + now destruct HR.
    + now constructor.
  - intros A B; split; intros [e1 a] [e2 b] HR.
    + now destruct HR.
    + now constructor.
Qed.

