  (* [denote_exp] only ever applies [EOU_to_itree] to pure computations we
     relate through [I2F_refine_lift]; prevent [cbn] from unfolding it into
     a stuck match that would obstruct applying the lemma. *)
  #[local] Arguments EOU_to_itree : simpl never. 
  
  Tactic Notation "simp_id" := cbn; cbv[resum ReSum_id id_ Id_IFun].
  Tactic Notation "simp_id" "in" ident(H) := cbn in H; cbv[resum ReSum_id id_ Id_IFun] in H.

  Tactic Notation "simp!" :=
    simp I2FE_Call I2FE_ExternalCall I2FE_Intrinsic I2FE_Global I2FE_Local I2FE_Stack I2FE_Memory I2FE_Draw
         in *.

  Ltac rew H :=
    autorewrite with
      I2FE_Call I2FE_ExternalCall I2FE_Intrinsic
      I2FE_Global I2FE_Local
      I2FE_Stack I2FE_Memory I2FE_Draw
      I2FE_Failure I2FE_OOM I2FE_UB
      (* I2FA_Call I2FA_AxternalCall I2FA_Intrinsic I2FA_Global I2FA_Local I2FA_Stack I2FA_Memory I2FA_Draw *)
      in H.
  
  (** The pure content of the [EXP_Integer] case, and the one place where
      the 14-way case analysis on [dtyp] happens. *)
  Lemma I2F_denote_int_syntax_as_int : forall τ x,
      I2F_EOU I2F_dvalue
        (@denote_int_syntax_as_int PInf τ x)
        (@denote_int_syntax_as_int PFin τ x).
  Proof.
    intros; destruct τ as [dt| |]; cbn; try (repeat constructor).
    destruct dt; cbn; try (repeat constructor).
    (* [DTYPE_Iptr]: the finite side either OOMs ([I2F_EOU_oom]) or
       returns [repr x] with [x] in range, so that [unsigned (repr x) = x]. *)
    unfold from_Z_bits.
    destruct ((denote_int_syntax x <=? @Integers.max_unsigned 64)%Z
                && (denote_int_syntax x >=? 0)%Z) eqn:EQ; cbn.
    - apply andb_prop in EQ as [LE GE].
      apply Z.leb_le in LE; apply Z.geb_le in GE.
      do 3 constructor.
      red; rewrite Integers.unsigned_repr; [reflexivity | lia].
    - constructor.
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

  (* The zero intptr and the null address of the two models are related. *)
  Lemma I2F_Iptr_zero : I2F_Iptr zero_iptr zero_iptr.
  Proof.
    red; cbn; rewrite ?Integers.unsigned_zero; easy.
  Qed.

  Lemma I2F_Addr_null : I2F_Addr null null.
  Proof.
    cbn; split; [apply I2F_Iptr_zero | reflexivity].
  Qed.

  (* [Extern]/[apply] rather than [Resolve]/[simple apply]: the goals show
     the instance-reduced forms of [zero_iptr]/[null], which only match the
     lemmas up to conversion. *)
  #[local] Hint Extern 1 (I2F_Iptr _ _) => apply I2F_Iptr_zero : core.
  #[local] Hint Extern 1 (I2F_Addr _ _) => apply I2F_Addr_null : core.
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
        try (destruct fp; cbn); auto 7.
    - (* DTYPE_Struct *)
      eapply I2F_EOU_bind; [apply I2F_EOU_map_monad; auto|].
      intros; do 2 constructor; auto.
    - (* DTYPE_Array *)
      eapply I2F_EOU_bind; [eassumption|].
      intros; do 2 constructor; auto.
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

  End ArithBridge.

  Lemma Z_gtb_irrefl : forall z : Z, (z >? z)%Z = false.
  Proof.
    intros; rewrite Z.gtb_ltb; apply Z.ltb_irrefl.
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

  (* Keep the overflow bounds abstract in goals rather than computed to
     20-digit literals, and keep [unsigned (repr z)] from reducing to
     [Z_mod_modulus z], so that explicit [destruct ... eqn:] and the
     [ArithBridge] lemmas apply syntactically. *)
  #[local] Arguments Integers.max_unsigned : simpl never.
  #[local] Arguments Integers.repr : simpl never.
  #[local] Arguments msamesign_Z : simpl never.

  (** Layer 2: on [bit_int sz] arguments both sides run the very same
      computation; only the [dvalue] wrapper differs. *)
  Lemma I2F_eval_int_op_bit_int : forall (sz : positive) iop (x y : @bit_int sz),
      I2F_EOU I2F_dvalue_base
        (@eval_int_op PInf _ _ _ iop x y)
        (@eval_int_op PFin _ _ _ iop x y).
  Proof.
    intros; destruct iop; cbn;
      repeat (break_match_goal; cbn); auto.
  Qed.

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
      + destruct ((unsigned x' mod unsigned y' =? 0)%Z) eqn:EX; cbn; auto.
        do 2 constructor; red; rewrite unsigned_divu; auto.
      + do 2 constructor; red; rewrite unsigned_divu; auto.
    - (* SDiv: unsupported at iptr type on both sides *)
      repeat constructor.
    - (* LShr *)
      rewrite Bool.andb_false_r; cbn.
      destruct exact; cbn.
      + destruct ((unsigned x' mod 2 ^ unsigned y' =? 0)%Z) eqn:EX; cbn; auto.
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
    inversion H1; subst; inversion H2; subst; cbn;
      try (repeat constructor).
    (* Iptr × Iptr: layer 1 *)
    all: try (now (apply I2F_eval_int_op_iptr; auto)).
    (* I sz × I sz0: the bitwidth test is shared, then layer 2 *)
    all: try (break_match_goal;
              [ match goal with e : _ = _ |- _ => destruct e end; cbn;
                apply I2F_eval_int_op_bit_int
              | repeat constructor ]).
    (* Poison rows: the guards are shared, up to [I2F_Iptr] on the payload *)
    all: destruct iop; cbn; auto;
      try (match goal with H : I2F_Iptr _ _ |- _ => red in H; subst end);
      try (repeat (break_match_goal; cbn); now auto).
  Qed.

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

  (* Destruct the (variable) vector flags blocking the [eval_*] wrapper
     dispatches; the mismatched flavours are diagonal errors. *)
  Ltac i2f_vec_flags :=
    repeat match goal with
           | |- context [if ?v then _ else _] => is_var v; destruct v; cbn
           end.

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
    inversion H1; subst; inversion H2; subst; cbn;
      try (repeat constructor).
    all: try (i2f_vec_flags; repeat constructor).
    - (* Base × Base *)
      eapply I2F_EOU_bind; [apply I2F_eval_iop_integer_base; auto|].
      intros; do 2 constructor; auto.
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
    inversion H; subst; cbn; try (repeat constructor).
    - (* Base *)
      eapply I2F_EOU_bind; [apply I2F_eval_fneg_base; auto|].
      intros; do 2 constructor; auto.
    - (* Array: only the vector flavour computes *)
      match goal with v : bool |- _ => destruct v end; cbn;
        [| repeat constructor].
      eapply I2F_EOU_bind;
        [eapply I2F_EOU_map_monad2;
         [eauto | intros; apply I2F_dvalue_to_dvalue_base; auto]|].
      intros ? ? ?.
      eapply I2F_EOU_bind;
        [eapply I2F_EOU_map_monad2;
         [eauto | intros; apply I2F_eval_fneg_base; auto]|].
      intros; do 2 constructor; apply Forall2_map_Base; auto.
  Qed.

  (** Same-instance [eval_int_icmp]: no [ToDvalue] is involved and all
      outputs are parameter-independent constructors, so one lemma covers
      both the [bit_int sz] case and the [Z] case used for address
      comparisons. *)
  Lemma I2F_eval_int_icmp_refl : forall Int (VMI : VMemInt Int) samesign icmp (x y : Int),
      I2F_EOU I2F_dvalue_base
        (@eval_int_icmp PInf Int VMI samesign icmp x y)
        (@eval_int_icmp PFin Int VMI samesign icmp x y).
  Proof.
    intros; destruct icmp; cbn;
      repeat (break_match_goal; cbn); auto.
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
    destruct icmp; cbn; try (repeat constructor);
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
    inversion H1; subst; inversion H2; subst; cbn;
      try (repeat constructor).
    (* Iptr × Iptr *)
    all: try (now (apply I2F_eval_int_icmp_iptr; auto)).
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
      destruct icmp; cbn;
      repeat (break_match_goal; cbn); repeat constructor.
  Qed.

  Lemma I2F_eval_icmp a1 a2 b1 b2 samesign cmp :
    I2F_dvalue a1 b1 ->
    I2F_dvalue a2 b2 ->
    I2F_EOU I2F_dvalue (eval_icmp samesign cmp a1 a2)
      (eval_icmp samesign cmp b1 b2).
  Proof.
    intros H1 H2.
    inversion H1; subst; inversion H2; subst; cbn;
      try (repeat constructor).
    all: try (i2f_vec_flags; repeat constructor).
    - (* Base × Base *)
      eapply I2F_EOU_bind; [apply I2F_eval_icmp_base; auto|].
      intros; do 2 constructor; auto.
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
    inversion H1; subst; inversion H2; subst; cbn;
      try (repeat constructor);
      destruct c; cbn;
      try (break_match_goal; cbn); repeat constructor.
  Qed.

  Lemma I2F_eval_fop a1 a2 b1 b2 fop :
    I2F_dvalue a1 b1 ->
    I2F_dvalue a2 b2 ->
    I2F_EOU I2F_dvalue (eval_fop fop a1 a2) (eval_fop fop b1 b2).
  Proof.
    intros H1 H2.
    inversion H1; subst; inversion H2; subst; cbn;
      try (repeat constructor).
    all: try (i2f_vec_flags; repeat constructor).
    - (* Base × Base *)
      eapply I2F_EOU_bind; [apply I2F_eval_fop_base; auto|].
      intros; do 2 constructor; auto.
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
    inversion H1; subst; inversion H2; subst; cbn;
      try (repeat constructor);
      unfold float_cmp, double_cmp; destruct c; cbn;
      repeat (break_match_goal; cbn); repeat constructor.
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

  (* Close an in-range [from_Z_bits] success branch: extract the bounds
     from the guard, then relate [z] with [repr z] through
     [unsigned_repr], wrapped either as an intptr value or as an
     address. *)
  Ltac i2f_in_range_case :=
    match goal with
    | B : ((_ <=? _)%Z && (_ >=? _)%Z)%bool = true |- _ =>
        apply andb_prop in B as [LE GE];
        apply Z.leb_le in LE; apply Z.geb_le in GE;
        first
          [ (* an intptr value *)
            do 2 constructor; red;
            rewrite Integers.unsigned_repr; [reflexivity | now split]
          | (* an address value *)
            do 2 constructor; split;
            [ red; rewrite Integers.unsigned_repr; [reflexivity | now split]
            | reflexivity ]
          | (* a bare address pair *)
            do 2 constructor;
            [ red; rewrite Integers.unsigned_repr; [reflexivity | now split]
            | reflexivity ] ]
    end.

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

  (** * Bitcast: relating the byte-serialization round-trip.

      The byte-extraction side is parameter-free-valued
      ([EOU (MaybePoison Z)]): related values expose *equal* bytes, since
      the payloads are shared ([DVALUE_I], floats) or [to_Z]-equal
      (intptrs, addresses --- provenance is discarded by design), and the
      offset/padding arithmetic only reads the shared [dtyp]. *)

  (* The two models share their [Sizeof] instance, but its uses appear
     behind distinct [Params] projections; align them syntactically. *)
  Lemma I2F_sizeof_dtyp : forall t,
      @sizeof_dtyp (@SIZE PInf) t = @sizeof_dtyp (@SIZE PFin) t.
  Proof. reflexivity. Qed.

  Lemma I2F_max_alignment : forall ts,
      @max_preferred_dtyp_alignment (@SIZE PInf) ts
      = @max_preferred_dtyp_alignment (@SIZE PFin) ts.
  Proof. reflexivity. Qed.

  Lemma I2F_dvalue_extract_byte : forall v v',
      I2F_dvalue v v' ->
      forall dt idx,
        @dvalue_extract_byte PInf v dt idx = @dvalue_extract_byte PFin v' dt idx.
  Proof.
    induction v using dvalue_ind; intros v' R; inversion R; subst;
      clear R; intros dt idx; cbn; auto.
    - (* Base *)
      match goal with HB : I2F_dvalue_base _ _ |- _ => inversion HB; subst end;
        cbn; auto.
      + (* Pointer *)
        repeat match goal with
          | HA : I2F_Addr ?a ?b |- _ =>
              destruct a, b; destruct HA as [HI ->]; red in HI; subst
               end; reflexivity.
      + (* Iptr *)
        match goal with HI : I2F_Iptr _ _ |- _ => red in HI; subst end;
        reflexivity.
    - (* Struct: the packed flavour has no padding (capture the loops so
         only the applied offset gets generalized); the aligned one first
         aligns and generalizes the baked-in padding bound (freeing the
         type list). Then induct on the related fields with the type list
         universal; each step unfolds one iteration of both loops in
         lockstep on shared scrutinees. *)
      match goal with p : bool |- _ => destruct p end;
        destruct dt as [ ? | p' ? | ? ? ? ]; cbn; auto;
        destruct p'; cbn; auto.
      + (* packed × packed *)
        match goal with
        | |- ?L _ _ _ _ = ?R _ _ _ _ => set (loopL := L); set (loopR := R)
        end.
        match goal with
        | F : Forall2 I2F_dvalue _ _, IH : Forall _ _ |- _ _ ?ts _ _ = _ =>
            generalize 0%N as offset; intros offset;
            revert offset; revert idx; revert IH; revert ts;
            induction F
        end;
          intros ts IH idx offset.
        * unfold loopL, loopR; cbn;
            destruct ts; cbn; auto;
            repeat (break_match_goal; cbn); auto.
        * unfold loopL, loopR; cbn; fold loopL; fold loopR;
            inversion IH; subst;
            destruct ts; cbn; auto;
            repeat (break_match_goal; cbn); auto.
      + (* aligned × aligned *)
        rewrite I2F_max_alignment.
        match goal with
        | |- context [@max_preferred_dtyp_alignment ?S ?ts] =>
            generalize (@max_preferred_dtyp_alignment S ts) as mpad; intros mpad
        end.
        match goal with
        | F : Forall2 I2F_dvalue _ _, IH : Forall _ _ |- _ _ ?ts _ _ = _ =>
            generalize 0%N as offset; intros offset;
            revert offset; revert idx; revert IH; revert ts;
            induction F
        end;
          intros ts IH idx offset; cbn.
        * destruct ts; cbn; auto;
            repeat (break_match_goal; cbn); auto.
        * inversion IH; subst;
            destruct ts; cbn; auto;
            repeat (break_match_goal; cbn); auto.
    - (* Array *)
      destruct dt; cbn; auto.
      match goal with
      | F : Forall2 I2F_dvalue _ _, IH : Forall _ _ |- _ =>
          revert idx; revert IH; induction F
      end;
        intros FIH fidx; cbn; auto;
        inversion FIH; subst;
        break_match_goal; cbn; auto.
  Qed.

  (** The semantic relation on lazy memory bytes: equal byte values. *)
  Definition I2F_mbyte (b : @memory_byte PInf) (b' : @memory_byte PFin) : Prop :=
    @memory_byte_value PInf b = @memory_byte_value PFin b'.

  Lemma I2F_dvalue_to_memory_bytes : forall v v' t,
      I2F_dvalue v v' ->
      Forall2 I2F_mbyte
        (@dvalue_to_memory_bytes PInf v t)
        (@dvalue_to_memory_bytes PFin v' t).
  Proof.
    intros; unfold dvalue_to_memory_bytes.
    rewrite I2F_sizeof_dtyp.
    apply Forall2_map2; intros b _.
    red; cbn.
    now apply I2F_dvalue_extract_byte.
  Qed.

  (* [EOUP]'s monad instance is local to [MemoryBytes.v]; re-register it
     so that [map_monad] at [EOUP] can be spoken about here. *)
  #[local] Existing Instance EOUP_Monad.

  (** Related bytes give literally equal byte-value streams. *)
  Lemma I2F_map_monad_memory_byte_value : forall dbs dbs',
      Forall2 I2F_mbyte dbs dbs' ->
      map_monad (m := EOUP) (@memory_byte_value PInf) dbs
      = map_monad (@memory_byte_value PFin) dbs'.
  Proof.
    intros dbs dbs' F; induction F; cbn; auto.
    red in H; rewrite H, IHF; reflexivity.
  Qed.

  Lemma Forall2_split_every_pos {A B} (R : A -> B -> Prop) (n : positive) :
    forall k l l',
      (length l <= k)%nat ->
      Forall2 R l l' ->
      Forall2 (Forall2 R) (split_every_pos n l) (split_every_pos n l').
  Proof.
    induction k; intros l l' LEN F; inversion F; subst.
    - rewrite !split_every_pos_equation; constructor.
    - cbn in LEN; lia.
    - rewrite !split_every_pos_equation; constructor.
    - (* [!]-rewriting would loop: the unfolding reintroduces a redex on
         the dropped tail; pin each rewrite to its argument instead *)
      match goal with
      | |- Forall2 _ (split_every_pos _ ?u) (split_every_pos _ ?v) =>
          rewrite (split_every_pos_equation _ u),
                  (split_every_pos_equation _ v)
      end.
      constructor.
      + apply Forall2_take; constructor; auto.
      + apply IHk.
        * match goal with
          | |- (length (drop _ (?x :: ?xs)) <= _)%nat =>
              pose proof (@drop_length_lt _ (x :: xs) (Npos n))
          end;
          cbn in *.
          forward H1; [lia|].
          forward H1; [easy|].
          lia.
        * apply Forall2_drop; constructor; auto.
  Qed.
  
  Lemma Forall2_split_every_nil {A B} (R : A -> B -> Prop) :
    forall n l l',
      Forall2 R l l' ->
      Forall2 (Forall2 R) (split_every_nil n l) (split_every_nil n l').
  Proof.
    intros [|p] l l' F; cbn; [constructor|].
    apply Forall2_split_every_pos with (k := length l); eauto.
  Qed.
  
  #[local] Arguments absorb_pois : simpl never.

  (** Once the byte streams are aligned (they are parameter-free), the
      two sides of [absorb_pois] share their scrutinee: the poison
      short-circuit is diagonal and only the continuations differ. *)
  Lemma I2F_absorb_pois {A} (dt : dtyp) (c : EOUP A)
        (k1 : A -> EOU (@dvalue_base PInf)) (k2 : A -> EOU (@dvalue_base PFin)) :
    (forall a, I2F_EOU I2F_dvalue_base (k1 a) (k2 a)) ->
    I2F_EOU I2F_dvalue_base (@absorb_pois PInf A dt c k1) (@absorb_pois PFin A dt c k2).
  Proof.
    intros K; unfold absorb_pois.
    eapply I2F_EOU_bind with (RA := Logic.eq); [apply I2F_EOU_refl|].
    intros a ? <-; destruct a; cbn; [repeat constructor | apply K].
  Qed.

  (** Deserialization at base types: every arm funnels through the shared
      [EOUP] stream of [memory_byte_value]s (equal by [I2F_mbyte]);
      [DTYPE_Iptr] and [DTYPE_Pointer] then run the finite in-range
      analysis. *)
  Lemma I2F_memory_bytes_to_dvalue_base : forall t dbs dbs',
      Forall2 I2F_mbyte dbs dbs' ->
      I2F_EOU I2F_dvalue_base
        (@memory_bytes_to_dvalue_base PInf dbs t)
        (@memory_bytes_to_dvalue_base PFin dbs' t).
  Proof.
    intros t dbs dbs' F; destruct t; cbn; auto.
    - (* DTYPE_I *)
      rewrite (I2F_map_monad_memory_byte_value F).
      apply I2F_absorb_pois; intros v; repeat constructor.
    - (* DTYPE_Iptr *)
      rewrite (I2F_map_monad_memory_byte_value F).
      apply I2F_absorb_pois; intros v; cbn.
      unfold from_Z_bits;
        repeat (break_match_goal_safe; cbn); auto;
        i2f_in_range_case.
    - (* DTYPE_Pointer *)
      rewrite (I2F_map_monad_memory_byte_value F).
      apply I2F_absorb_pois; intros v; cbn.
      unfold from_Z_bits;
        repeat (break_match_goal_safe; cbn); auto;
        i2f_in_range_case.
    - (* DTYPE_FP *)
      destruct fp; cbn; auto;
        rewrite (I2F_map_monad_memory_byte_value F);
        apply I2F_absorb_pois; intros v; repeat constructor.
  Qed.

  (** Deserialization: related byte lists deserialize to related values;
      aggregates recurse through the [Forall2] list combinators. *)
  Lemma I2F_memory_bytes_to_dvalue : forall t dbs dbs',
      Forall2 I2F_mbyte dbs dbs' ->
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
                   Forall2 I2F_mbyte xs ys ->
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
                   Forall2 I2F_mbyte xs ys ->
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
          [ eapply I2F_EOU_map_monad2 with (RA := Forall2 I2F_mbyte);
            [ apply Forall2_repeatN; constructor
            | intros ? ? ?; auto ]
          | intros ? ? ?; do 2 constructor; auto ].
      + eapply I2F_EOU_bind;
          [ eapply I2F_EOU_map_monad2 with (RA := Forall2 I2F_mbyte);
            [ apply Forall2_split_every_nil; auto
            | intros ? ? ?; auto ]
          | intros ? ? ?; do 2 constructor; auto ].
  Qed.

  (** Bitcast round-trips a value through its byte representation. *)
  Lemma I2F_bitcast_bytes : forall v v' t_from t_to,
      I2F_dvalue v v' ->
      I2F_EOU I2F_dvalue
        (@memory_bytes_to_dvalue PInf (@dvalue_to_memory_bytes PInf v t_from) t_to)
        (@memory_bytes_to_dvalue PFin (@dvalue_to_memory_bytes PFin v' t_from) t_to).
  Proof.
    intros; apply I2F_memory_bytes_to_dvalue, I2F_dvalue_to_memory_bytes; auto.
  Qed.

  (** Related conversion cases: same constructor, related payloads.
      A computing definition, so that the synchronized destruct in
      [I2F_convert_h] reduces it by [cbn]. *)
  Definition I2F_conv_case (c1 : @conv_case PInf) (c2 : @conv_case PFin) : Prop :=
    match c1, c2 with
    | Conv_Pure x1, Conv_Pure x2 => I2F_dvalue_base x1 x2
    | Conv_ItoP x1, Conv_ItoP x2 => I2F_dvalue_base x1 x2
    | Conv_PtoI x1, Conv_PtoI x2 => I2F_dvalue_base x1 x2
    | Conv_Oom s1, Conv_Oom s2 => True
    | Conv_Illegal s1, Conv_Illegal s2 => True
    | _, _ => False
    end.

  (** The single case analysis of the conversion pipeline: related inputs
      classify into related conversion cases. The goals here are pure and
      small (no [convert_base] body in sight), which keeps the case
      product tractable. Bitcast is excluded: its classification runs the
      byte round-trip, and [convert] intercepts it before [convert_base]
      anyway. *)
  Lemma I2F_get_conv_case : forall conv t_from t_to v v',
      conv <> Bitcast ->
      I2F_dvalue_base v v' ->
      I2F_conv_case
        (@get_conv_case PInf conv t_from v t_to)
        (@get_conv_case PFin conv t_from v' t_to).
  Proof.
    intros * NB R.
    destruct conv; try congruence; clear NB; cbn; auto.
    all: destruct t_from; try constructor.
    all: induction R; try constructor.
    all: destruct t_to; try constructor.
    all: repeat (break_fast; cbn); auto.
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
  Lemma I2F_convert_base : forall conv t_from t_to v v',
      conv <> Bitcast ->
      I2F_dvalue_base v v' ->
      I2F_EOU I2F_dvalue_base
        (@convert_base PInf conv t_from v t_to)
        (@convert_base PFin conv t_from v' t_to).
  Proof.
    intros * NB R.
    pose proof (I2F_get_conv_case t_from t_to NB R) as CC; revert CC.
    unfold convert_base.
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
  Qed.

  Lemma I2F_convert conv t_from t_to a b :
    I2F_dvalue a b ->
    I2F_EOU I2F_dvalue (convert conv t_from a t_to) (convert conv t_from b t_to).
  Proof.
    intros R.
    destruct conv.
    (* Bitcast: shared guards, then the byte-level round-trip *)
    12: { cbn.
          break_match_goal; cbn; auto.
          break_match_goal; cbn; auto.
          now apply I2F_bitcast_bytes. }
    (* all others: the type classification is shared and pure; scalars go
       through [convert_base], vectors pointwise so *)
    all: inversion R; subst; cbn; try (repeat constructor).
    (* scalar ([Fptrunc]/[Addrspacecast] reduce to diagonal errors before
       [I2F_convert_base] can be re-folded) *)
    all: try (destruct (get_conversion_type t_from t_to) as [[? ?]|]; cbn;
              [ first
                  [ (eapply I2F_EOU_bind;
                     [ apply I2F_convert_base; [congruence | auto] |]);
                    intros; do 2 constructor; auto
                  | repeat constructor ]
              | repeat constructor ]).
    (* vector: the flags and the (shared) annotation dispatch first *)
    all: i2f_vec_flags; cbn; try (repeat constructor).
    all: break_match_goal; cbn; try (repeat constructor).
    all: i2f_vec_flags; cbn; try (repeat constructor).
    all: destruct (get_conversion_type t_from t_to) as [[? ?]|]; cbn;
      [| repeat constructor].
    all: (eapply I2F_EOU_bind;
          [ eapply I2F_EOU_map_monad2;
            [ eauto | intros; apply I2F_dvalue_to_dvalue_base; auto ] |]);
      intros ? ? ?;
      (eapply I2F_EOU_bind;
       [ eapply I2F_EOU_map_monad2 with (RB := I2F_dvalue_base);
         [ eauto
         | intros;
           first [ apply I2F_convert_base; [congruence | auto]
                 | repeat constructor ] ] |]);
      intros; do 2 constructor; apply Forall2_map_Base; auto.
  Qed.

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
        inversion HC; subst; cbn; auto
    end;
      try (match goal with
           | HB : I2F_dvalue_base _ _ |- _ =>
               inversion HB; subst; cbn; auto
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
      repeat (break_match_goal_safe; cbn); auto;
      i2f_in_range_case.
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

  (* Keep [split] applications abstract in goals so they can be destructed
     with occurrence abstraction. *)
  #[local] Arguments split : simpl never.

  (** Related aggregates split synchronously: either both indexings are out
      of bounds (the shared UB guard), or the parts are pointwise
      related. *)
  Lemma Forall2_split_h {A B} (R : A -> B -> Prop) :
    forall i (l1 : list A) (l2 : list B),
      Forall2 R l1 l2 ->
      forall pre1 pre2, Forall2 R pre1 pre2 ->
      match split_h pre1 i l1, split_h pre2 i l2 with
      | Some (p1, x1, q1), Some (p2, x2, q2) =>
          Forall2 R p1 p2 /\ R x1 x2 /\ Forall2 R q1 q2
      | None, None => True
      | _, _ => False
      end.
  Proof.
    intros i l1 l2 F; revert i; induction F; intros i pre1 pre2 FP; cbn; auto.
    destruct (i =? 0)%Z; cbn.
    - repeat split; auto.
    - apply IHF, Forall2_app; auto.
  Qed.

  Lemma Forall2_split {A B} (R : A -> B -> Prop) :
    forall i (l1 : list A) (l2 : list B),
      Forall2 R l1 l2 ->
      match split [] i l1, split [] i l2 with
      | Some (p1, x1, q1), Some (p2, x2, q2) =>
          Forall2 R p1 p2 /\ R x1 x2 /\ Forall2 R q1 q2
      | None, None => True
      | _, _ => False
      end.
  Proof.
    intros i l1 l2 F; unfold split.
    destruct (i <? 0)%Z; cbn; auto.
    apply Forall2_split_h; auto.
  Qed.

  Lemma Forall2_map_Poison : forall ts,
      Forall2 I2F_dvalue
        (map (fun t => @DVALUE_Base PInf (DVALUE_Poison t)) ts)
        (map (fun t => @DVALUE_Base PFin (DVALUE_Poison t)) ts).
  Proof.
    induction ts; cbn; auto.
  Qed.

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

  Lemma I2F_extract_value a b idxs :
    I2F_dvalue a b ->
    I2F_EOU I2F_dvalue (extract_value a (map denote_int_syntax idxs))
      (extract_value b (map denote_int_syntax idxs)).
  Proof.
    intros R; revert a b R.
    generalize (map denote_int_syntax idxs) as l; clear idxs.
    induction l as [| i l IH]; intros a b R; cbn; auto.
    inversion R; subst; cbn; try (repeat constructor).
    - (* Base: only poison at struct type computes, splitting the shared
         type list *)
      match goal with
      | HB : I2F_dvalue_base _ _ |- _ =>
          inversion HB; subst; cbn; try (repeat constructor)
      end.
      match goal with
      | t : dtyp |- _ => destruct t
      end; cbn; try (repeat constructor).
      match goal with
      | |- context [split [] i ?ts] =>
          destruct (split [] i ts) as [[[? ?] ?] |]
      end; cbn; auto.
    - (* Struct *)
      i2f_split_case i ltac:(apply IH; auto).
    - (* Array: only the non-vector flavour computes *)
      match goal with v : bool |- _ => destruct v end; cbn;
        [repeat constructor|].
      i2f_split_case i ltac:(apply IH; auto).
  Qed.

  Lemma I2F_insert_value idxs :
    forall a1 a2 b1 b2,
    I2F_dvalue a1 b1 ->
    I2F_dvalue a2 b2 ->
    I2F_EOU I2F_dvalue (insert_value a1 a2 (map denote_int_syntax idxs))
      (insert_value b1 b2 (map denote_int_syntax idxs)).
  Proof.
    generalize (map denote_int_syntax idxs) as l; clear idxs.
    induction l as [| i l IH]; intros a1 a2 b1 b2 R1 R2; cbn; auto.
    inversion R1; subst; cbn; try (repeat constructor).
    - (* Base: poison at struct type splits the shared type list and
         rebuilds with poisons *)
      match goal with
      | HB : I2F_dvalue_base _ _ |- _ =>
          inversion HB; subst; cbn; try (repeat constructor)
      end.
      match goal with
      | t : dtyp |- _ => destruct t
      end; cbn; try (repeat constructor).
      match goal with
      | |- context [split [] i ?ts] =>
          destruct (split [] i ts) as [[[? ?] ?] |]
      end; cbn; auto.
      eapply I2F_EOU_bind; [apply IH; auto|].
      intros; do 2 constructor.
      apply Forall2_app; [apply Forall2_map_Poison |].
      constructor; [auto | apply Forall2_map_Poison].
    - (* Struct: split, modify the subfield recursively, reassemble *)
      i2f_split_case i
        ltac:(eapply I2F_EOU_bind; [apply IH; auto|];
              intros; do 2 constructor;
              apply Forall2_app; [auto | constructor; auto]).
    - (* Array: only the non-vector flavour computes *)
      match goal with v : bool |- _ => destruct v end; cbn;
        [repeat constructor|].
      i2f_split_case i
        ltac:(eapply I2F_EOU_bind; [apply IH; auto|];
              intros; do 2 constructor;
              apply Forall2_app; [auto | constructor; auto]).
  Qed.

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
    (* Vector *)
    match goal with v : bool |- _ => destruct v end; cbn;
      try (repeat constructor).
    match goal with
    | τ : dtyp |- _ => destruct τ as [ ? | ? ? | [|] ? ? ]
    end; cbn; try (repeat constructor).
    rewrite (I2F_dvalue_to_Z R2).
    destruct (dvalue_to_Z b2) as [i |]; cbn; try (repeat constructor).
    i2f_split_case i ltac:(auto).
  Qed.

  Lemma I2F_insert_element a1 a2 a3 b1 b2 b3 :
    I2F_dvalue a1 b1 ->
    I2F_dvalue a2 b2 ->
    I2F_dvalue a3 b3 ->
    I2F_EOU I2F_dvalue (insert_element a1 a2 a3) (insert_element b1 b2 b3).
  Proof.
    intros R1 R2 R3.
    inversion R1; subst; cbn; try (repeat constructor).
    - (* Base: poison at vector type splits a vector of poisons *)
      match goal with
      | HB : I2F_dvalue_base _ _ |- _ =>
          inversion HB; subst; cbn; try (repeat constructor)
      end.
      match goal with
      | t : dtyp |- _ => destruct t as [ ? | ? ? | [|] ? ? ]
      end; cbn; try (repeat constructor).
      rewrite (I2F_dvalue_to_Z R3).
      destruct (dvalue_to_Z b3) as [i |]; cbn; try (repeat constructor).
      match goal with
      | |- context [repeat (DVALUE_Base (DVALUE_Poison ?dt)) ?n] =>
          pose proof (Forall2_repeat _ _ _ n
                        (I2F_dvalue_Base (I2F_dvalue_Poison dt))) as F
      end.
      i2f_split_case i
        ltac:(do 2 constructor; apply Forall2_app; [auto | constructor; auto]).
    - (* Vector *)
      match goal with v : bool |- _ => destruct v end; cbn;
        try (repeat constructor).
      match goal with
      | τ : dtyp |- _ => destruct τ as [ ? | ? ? | [|] ? ? ]
      end; cbn; try (repeat constructor).
      rewrite (I2F_dvalue_to_Z R3).
      destruct (dvalue_to_Z b3) as [i |]; cbn; try (repeat constructor).
      i2f_split_case i
        ltac:(do 2 constructor; apply Forall2_app; [auto | constructor; auto]).
  Qed.

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
      | τ : dtyp |- _ => destruct τ as [ ? | ? ? | ? ? ? ]
      end; cbn; auto.
      break_match_goal; cbn; auto.
      match goal with
      | F2 : Forall2 I2F_dvalue ?l1 ?l2 |- _ =>
          match goal with
          | |- context [forallb ?f l1] =>
              match goal with
              | |- context [forallb ?g l2] =>
                  assert (FB : forallb f l1 = forallb g l2);
                  [| assert (LEN : length l1 = length l2)
                       by (eapply Forall2_length; eauto);
                     rewrite FB, LEN; reflexivity ]
              end
          end
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
  Qed.

  (** The scalar select: the shared [i1] test picks a side; the poison
      condition computes the (equal) result type of the first operand. *)
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
    - (* Poison: align the (equal) result types, then reduce the shared
         scrutinees in lockstep *)
      rewrite (I2F_dtyp_of_dvalue_eq R1).
      repeat (break_goal_fast; cbn); auto.
  Qed.

  Lemma I2F_eval_select a1 a2 a3 b1 b2 b3 :
    I2F_dvalue a1 b1 ->
    I2F_dvalue a2 b2 ->
    I2F_dvalue a3 b3 ->
    I2F_EOU I2F_dvalue (eval_select a1 a2 a3) (eval_select b1 b2 b3).
  Proof.
    intros R1 R2 R3.
    inversion R1; subst; cbn; try ((repeat constructor); eauto; fail).
    - (* Base condition *)
      now apply I2F_eval_select_base_dvalue.
    - (* Vector of conditions *)
      match goal with v : bool |- _ => destruct v end; cbn;
        [| repeat constructor; eauto].
      eapply I2F_EOU_bind;
        [eapply I2F_EOU_map_monad2;
         [eauto | intros; apply I2F_dvalue_to_dvalue_base; auto]|].
      intros cs cs' FCS.
      inversion R2; subst; cbn; try (repeat constructor).
      + (* v1 base: only poison at vector type computes *)
        match goal with
        | HB : I2F_dvalue_base _ _ |- _ =>
            inversion HB; subst; cbn; try (repeat constructor)
        end.
        match goal with
        | t : dtyp |- _ => destruct t as [ ? | ? ? | [|] ? ? ]
        end; cbn; try (repeat constructor).
        inversion R3; subst; cbn; try (repeat constructor).
        * (* poison / base: only poison at vector type computes,
             diagonally *)
          match goal with
          | HB : I2F_dvalue_base _ _ |- _ =>
              inversion HB; subst; cbn; try (repeat constructor)
          end.
          match goal with
          | t : dtyp |- _ => destruct t as [ ? | ? ? | [|] ? ? ]
          end; cbn; repeat constructor.
        * (* poison / vector *)
          match goal with v : bool |- _ => destruct v end; cbn;
            [| repeat constructor].
          eapply I2F_EOU_bind.
          { eapply I2F_EOU_vec_loop with (RB := prod_rel I2F_dvalue I2F_dvalue).
            - eapply Forall2_combine; [eassumption|].
              eapply Forall2_combine;
                [apply Forall2_repeat; auto | eassumption].
            - intros c p c' p' HC HP;
                destruct p as [x y], p' as [x' y'], HP as [HX HY]; cbn.
              apply I2F_eval_select_base_dvalue; auto. }
          intros; do 2 constructor; auto.
      + (* v1 vector *)
        inversion R3; subst; cbn; try (repeat constructor).
        * (* vector / base: only poison at vector type computes *)
          match goal with v : bool |- _ => destruct v end; cbn;
            [| repeat constructor].
          match goal with
          | HB : I2F_dvalue_base _ _ |- _ =>
              inversion HB; subst; cbn; try (repeat constructor)
          end.
          match goal with
          | t : dtyp |- _ => destruct t as [ ? | ? ? | [|] ? ? ]
          end; cbn; try (repeat constructor).
          eapply I2F_EOU_bind.
          { eapply I2F_EOU_vec_loop with (RB := prod_rel I2F_dvalue I2F_dvalue).
            - eapply Forall2_combine; [eassumption|].
              eapply Forall2_combine;
                [eassumption | apply Forall2_repeat; auto].
            - intros c p c' p' HC HP;
                destruct p as [x y], p' as [x' y'], HP as [HX HY]; cbn.
              apply I2F_eval_select_base_dvalue; auto. }
          intros; do 2 constructor; auto.
        * (* vector / vector *)
          i2f_vec_flags.
          all: try (repeat constructor).
          all: eapply I2F_EOU_bind;
            [ eapply I2F_EOU_vec_loop with (RB := prod_rel I2F_dvalue I2F_dvalue);
              [ eapply Forall2_combine; [eassumption|];
                eapply Forall2_combine; eassumption
              | intros c p c' p' HC HP;
                destruct p as [x y], p' as [x' y'], HP as [HX HY]; cbn;
                apply I2F_eval_select_base_dvalue; auto ]
            | intros; do 2 constructor; auto ].
        * (* vector / vector *)
          i2f_vec_flags.
          all: try (repeat constructor).
          all: eapply I2F_EOU_bind;
            [ eapply I2F_EOU_vec_loop with (RB := prod_rel I2F_dvalue I2F_dvalue);
              [ eapply Forall2_combine; [eassumption|];
                eapply Forall2_combine; eassumption
              | intros c p c' p' HC HP;
                destruct p as [x y], p' as [x' y'], HP as [HX HY]; cbn;
                apply I2F_eval_select_base_dvalue; auto ]
            | intros; do 2 constructor; auto ].
   Qed.

  Tactic Notation "rbind" uconstr(x) := eapply ruttc_bind with (RR := x).

 
End Refinement.
