Require Import ZArith Lia Basics RelationClasses Program.
Require Import SpecFloat.
Require Import Flocq.IEEE754.Binary Flocq.Core.Defs Flocq.Core.Zaux.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.OptionMonad.
Require Import Floats.

Open Scope Z.

(* a basic float - a pair of two integers - mantissa and exponent *)
Definition bfloat := Flocq.Core.Defs.float radix2.
Definition BFloat := Flocq.Core.Defs.Float radix2.

(** * converting between floats in the same cohort *)

(* increase a given float's exponent by [de] *)
Definition inc_e (f : bfloat) (de : positive) : option bfloat :=
  let '(m, e) := (Fnum f, Fexp f) in
  let rm := two_power_pos de in
  if (BinIntDef.Z.modulo m rm =? 0)
  then Some (BFloat (m / two_power_pos de) (e + Z.pos de))
  else None.

(* decrese a given float's exponent by [de] *)
Definition dec_e (f : bfloat) (de : positive) : bfloat :=
  let '(m, e) := (Fnum f, Fexp f) in
  let rm := two_power_pos de in
  BFloat (m * two_power_pos de) (e - Z.pos de).

(* shift (up or down) the exponent by [de] *)
Definition shift_e (f : bfloat) (de : Z) : option bfloat :=
  match de with
  | Z0 => Some f
  | Z.pos pde => inc_e f pde
  | Z.neg nde => Some (dec_e f nde)
  end.

(* set exponent to a given one *)
Definition set_e (f : bfloat) (e : Z) : option bfloat :=
  shift_e f (e - Fexp f).

(* binary length of a number *)
Definition Zdigits (m : Z) := Z.log2 (Z.abs m) + 1.

(* shifting the binary length of the mantissa - *)
Definition inc_digits_m := dec_e.
Definition dec_digits_m := inc_e.
Definition shift_digits_m (f : bfloat) (ddm : Z) := shift_e f (- ddm).
Definition set_digits_m (f : bfloat) (dm : Z) := shift_digits_m f (dm - Zdigits (Fnum f)).

(* Deprecated stuff from Coq.ZArith.Zlogarithm *)
Fixpoint log_inf (p:positive) : Z :=
  match p with
  | xH => 0
  | xO q => Z.succ (log_inf q)
  | xI q => Z.succ (log_inf q)
  end.

Axiom Zlog2_log_inf : forall p, Z.log2 (Zpos p) = log_inf p.

(** * normalization *)
Definition normalize_float (prec emax : Z) (f : bfloat)
  : option bfloat :=
  let emin := 3 - emax - prec in
  match set_e f emin with
    | None => None
    | Some f1 => if Zdigits (Fnum f1) <=? prec
                 then Some f1
                 else match set_digits_m f prec with
                     | None => None
                     | Some f2 => if andb
                                       (emin <=? Fexp f2)
                                       (Fexp f2 <=? emax - prec)
                                  then Some f2
                                  else None
                     end
  end.

(* check if a mantissa-exponent pair is represntable in a format given by prec, emax *)
Definition can_convert_exactly (prec__target emax__target : Z) (m : positive) (e : Z) : bool :=
  let f := BFloat (Z.pos m) e in
  match normalize_float prec__target emax__target f with
  | Some _ => true
  | None => false
  end.

Definition can_convert_float_to_float32 (v : float) : bool :=
  match v with
  | B754_finite _ m e _ => can_convert_exactly 24 128 m e
  | _ => true
  end.

Definition can_convert_float_to_float64 (v : float) : bool :=
  match v with
  | B754_finite _ m e _ => can_convert_exactly 53 1024 m e
  | _ => true
  end.

Section Correctness.

  (*
   * Inspired by StructTact
   * Source: github.com/uwplse/StructTact
   *
   * [break_match] looks for a [match] construct in the goal or some hypothesis,
   * and destructs the discriminee, while retaining the information about
   * the discriminee's value leading to the branch being taken.
   *)
  Ltac break_match :=
    match goal with
      | [ |- context [ match ?X with _ => _ end ] ] =>
        match type of X with
          | sumbool _ _ => destruct X
          | _ => destruct X eqn:?
        end
      | [ H : context [ match ?X with _ => _ end ] |- _] =>
        match type of X with
          | sumbool _ _ => destruct X
          | _ => destruct X eqn:?
        end
    end.

  (* binary length of a positive number *)
  Let digits (p: positive) := Z.succ (Z.log2 (Zpos p)).

  (* closed form for Flocq's [digits2_pos] *)
  Lemma digits2_pos_digits (m : positive) :
    Z.pos (Digits.digits2_pos m) = digits m.
  Proof using.
    induction m; simpl.
    1,2:
      rewrite Pos2Z.inj_succ, IHm;
      unfold digits;
      rewrite <- Z.log2_double by lia;
      reflexivity.
    auto.
  Qed.

  (** ** Flocq's Binary.bounded rewritten in a form close to IEEE-754 *)
  Lemma bounded_closed_form (prec emax : Z)
        (prec_gt_0 : Flocq.Core.FLX.Prec_gt_0 prec) (Hmax : (prec < emax)%Z)
        (m : positive) (e : Z) :
    bounded prec emax m e = true
    <->
    or
      (digits m < prec /\ e = 3 - emax - prec)
      (digits m = prec /\ 3 - emax - prec <= e <= emax - prec).
  Proof using.
    unfold FLX.Prec_gt_0, bounded, canonical_mantissa, fexp, emin in *.
    rewrite Bool.andb_true_iff, Z.leb_le, <-Zeq_is_eq_bool, digits2_pos_digits.
    unfold FLT.FLT_exp.
    remember (3 - emax - prec) as emin.
    split; intro.
    all: destruct (Z_lt_le_dec (digits m + e - prec) emin).
    all: try rewrite Z.max_r in * by lia.
    all: try rewrite Z.max_l in * by lia.
    all: lia.
  Qed.

  Definition valid_float (prec emax : Z) (f : bfloat) :=
    match (Fnum f) with
    | Z0 => true
    | Z.pos m => bounded prec emax m (Fexp f)
    | Z.neg m => bounded prec emax m (Fexp f)
    end.

  (** ** equality on floats with no jumps to Real *)
  Definition float_eq (f1 : bfloat) (f2 : bfloat) : Prop :=
    let '(m1, e1) := (Fnum f1, Fexp f1) in
    let '(m2, e2) := (Fnum f2, Fexp f2) in
    or
      (e2 <= e1 /\ m2 = m1 * 2 ^ (e1 - e2))
      (e1 <= e2 /\ m1 = m2 * 2 ^ (e2 - e1)).

  Lemma float_eq_refl : Reflexive float_eq.
  Proof using.
    unfold Reflexive; intro f.
    unfold float_eq; left.
    replace (Fexp f - Fexp f) with 0.
    all: lia.
  Qed.

  Lemma float_eq_sym : Symmetric float_eq.
  Proof using.
    unfold Symmetric, float_eq.
    intros; destruct H; auto.
  Qed.

  Lemma Zpow_divide (b p1 p2 : Z) :
    0 < b ->
    0 <= p1 <= p2 ->
    (b ^ p1 | b ^ p2).
  Proof using.
    intros B P.
    rewrite <-Z.mod_divide by (apply Z.pow_nonzero; lia).
    replace p2 with ((p2 - p1) + p1) by lia.
    rewrite Z.pow_add_r by lia.
    apply Z_mod_mult.
  Qed.

  Lemma float_eq_trans : Transitive float_eq.
  Proof using.
    unfold Transitive.
    destruct x as [mx ex], y as [my ey], z as [mz ez].
    unfold float_eq.
    simpl.
    intros XY YZ.
    destruct XY as [XY | XY]; destruct YZ as [YZ | YZ].
    all: destruct XY as [EXY MXY]; destruct YZ as [EYZ MYZ]; subst.
    - left; split; [lia |].
      rewrite <-Z.mul_assoc.
      rewrite <-Z.pow_add_r; try lia.
      replace (ex - ey + (ey - ez)) with (ex - ez) by lia.
      reflexivity.
    - destruct (Z.eq_dec ex ez); subst.
      + (* ex = ez *)
        apply Z.mul_reg_r in MYZ.
        subst; left; split; [lia |].
        rewrite Z.sub_diag; lia.
        generalize (Z.pow_pos_nonneg 2 (ez - ey)); lia.
      + destruct (Z_lt_le_dec ex ez).
        * (* ex < ez *)
          rename MYZ into H.
          assert (H1 : ey <= ex < ez) by lia; clear EXY EYZ n l.
          right; split; [lia |].
          apply f_equal with (f := fun x => Z.div x (2 ^ (ex - ey))) in H.
          rewrite Z_div_mult in H;
            [| generalize (Z.pow_pos_nonneg 2 (ex - ey)); lia].
          subst.
          rewrite Z.divide_div_mul_exact;
            [| apply Z.pow_nonzero; lia | apply Zpow_divide; lia].
          replace (ez - ey) with ((ez - ex) + (ex - ey)) by lia.
          rewrite Z.pow_add_r by lia.
          rewrite Z.div_mul by (apply Z.pow_nonzero; lia).
          reflexivity.
        * (* ez < ex *)
          rename MYZ into H.
          assert (H1: ey <= ez < ex) by lia; clear EXY EYZ n l.
          left; split; [lia |].
          apply f_equal with (f := fun x => Z.div x (2 ^ (ez - ey))) in H.
          rewrite Z_div_mult in H;
            [| generalize (Z.pow_pos_nonneg 2 (ez - ey)); lia].
          subst.
          rewrite Z.divide_div_mul_exact;
            [| apply Z.pow_nonzero; lia | apply Zpow_divide; lia].
          replace (ex - ey) with ((ex - ez) + (ez - ey)) by lia.
          rewrite Z.pow_add_r by lia.
          rewrite Z.div_mul by (apply Z.pow_nonzero; lia).
          reflexivity.
    - destruct (Z.eq_dec ex ez); subst.
      + (* ex = ez *)
        left; split; [lia |].
        rewrite Z.sub_diag; lia.
      + destruct (Z_lt_le_dec ex ez).
        * (* ex < ez *)
          assert (H : ex < ez <= ey) by lia; clear EXY EYZ n l.
          right; split; [lia |].
          rewrite <-Z.mul_assoc.
          rewrite <-Z.pow_add_r by lia.
          replace (ey - ez + (ez - ex)) with (ey - ex) by lia.
          reflexivity.
        * (* ez < ex *)
          assert (H: ez < ex <= ey) by lia; clear EXY EYZ n l.
          left; split; [lia |].
          rewrite <-Z.mul_assoc.
          rewrite <-Z.pow_add_r by lia.
          replace (ey - ex + (ex - ez)) with (ey - ez) by lia.
          reflexivity.
    - right; split; [lia |].
      rewrite <-Z.mul_assoc.
      rewrite <-Z.pow_add_r; try lia.
      replace (ez - ey + (ey - ex)) with (ez - ex) by lia.
      reflexivity.
  Qed.

  Definition float_eq_equivalence :=
    Build_Equivalence float_eq float_eq_refl float_eq_sym float_eq_trans.

  Definition not_zero (f : bfloat) := (Fnum f) <> 0.

  Lemma not_zero_Zpos (m : positive) (e : Z) :
    not_zero (BFloat (Z.pos m) e).
  Proof using. unfold not_zero. simpl. discriminate. Qed.

  Lemma not_zero_eq (f1 f2 : bfloat) :
    not_zero f1 ->
    float_eq f1 f2 ->
    not_zero f2.
  Proof using.
    unfold not_zero, float_eq.
    destruct f1 as [m1 e1], f2 as [m2 e2]; simpl.
    intros NZ1 H.
    destruct H; destruct H as [H1 H2]; subst.
    - assert (0 < 2 ^ (e1 - e2)) by (apply Z.pow_pos_nonneg; lia).
      apply Z.neq_mul_0.
      lia.
    - intros H; contradict NZ1.
      subst; reflexivity.
  Qed.

  (** shifting the exponent results in a shifted exponent as expected *)
  Lemma inc_e_correct (f1 : bfloat) (de : positive) {f2 : bfloat} :
    inc_e f1 de = Some f2 ->
    Fexp f2 = Fexp f1 + Z.pos de.
  Proof using.
    unfold inc_e.
    intro; break_match; inversion H; clear H.
    reflexivity.
  Qed.

  Lemma dec_e_correct (f : bfloat) (de : positive) :
    Fexp (dec_e f de) = Fexp f - Z.pos de.
  Proof using. reflexivity. Qed.

  Lemma shift_e_correct (f1 : bfloat) (de : Z) {f2 : bfloat} :
    shift_e f1 de = Some f2 ->
    Fexp f2 = Fexp f1 + de.
  Proof using.
    unfold shift_e; intro; break_match; inversion H; clear H.
    lia.
    apply inc_e_correct; assumption.
    apply dec_e_correct.
  Qed.

  Lemma set_e_correct (f1 : bfloat) (e : Z) {f2 : bfloat} :
    set_e f1 e = Some f2 ->
    Fexp f2 = e.
  Proof using.
    unfold set_e.
    intro H.
    apply shift_e_correct in H.
    lia.
  Qed.

  (** shifting the exponent preserves the float's value *)
  Lemma inc_e_eq (f1 : bfloat) (de : positive) {f2 : bfloat} :
    inc_e f1 de = Some f2 ->
    float_eq f1 f2.
  Proof using.
    intros.
    destruct f1 as [m1 e1], f2 as [m2 e2].
    unfold inc_e in H; break_match; inversion H; clear H.
    unfold float_eq.
    simpl in *.
    right.
    replace (e1 + Z.pos de - e1) with (Z.pos de) by lia.
    rewrite <-two_power_pos_equiv.
    remember (two_power_pos de) as rm.
    rewrite Z.eqb_eq in Heqb.
    rewrite Z.mul_comm.
    rewrite <-Z_div_exact_2 with (b := rm); try auto.
    rewrite two_power_pos_equiv in Heqrm.
    assert (0 < 2 ^ Z.pos de).
    apply Z.pow_pos_nonneg.
    all: try lia.
    subst rm.
    rewrite two_power_pos_equiv.
    generalize (Z.pow_pos_nonneg 2 (Z.pos de)).
    lia.
  Qed.

  Lemma dec_e_eq (f : bfloat) (de : positive) :
    float_eq f (dec_e f de).
  Proof using.
    destruct f as [m e].
    unfold dec_e, float_eq.
    simpl.
    left.
    replace (e - (e - Z.pos de)) with (Z.pos de) by lia.
    rewrite two_power_pos_equiv.
    split.
    lia.
    reflexivity.
  Qed.

  Lemma shift_e_eq (f1 : bfloat) (de : Z) {f2 : bfloat} :
    shift_e f1 de = Some f2 ->
    float_eq f1 f2.
  Proof using.
    destruct de; simpl.
    - intro H; inversion H; apply float_eq_refl.
    - apply inc_e_eq.
    - intro H; inversion H; apply dec_e_eq.
  Qed.

  Lemma set_e_eq (f1 : bfloat) (e : Z) {f2 : bfloat} :
    set_e f1 e = Some f2 ->
    float_eq f1 f2.
  Proof using.
    unfold set_e.
    apply shift_e_eq.
  Qed.

  Lemma Zdigits_mul_pow2 (m : Z) (d : positive) :
    m <> 0 -> Zdigits (m * two_power_pos d) = Zdigits m + Z.pos d.
  Proof using.
    intro.
    rewrite two_power_pos_equiv.
    unfold Zdigits.
    rewrite Z.abs_mul, Z.abs_pow.
    replace (Z.abs 2) with 2 by reflexivity.
    remember (Z.abs m) as pm; remember (Z.pos d) as pd.
    rewrite Z.log2_mul_pow2.
    all: lia.
  Qed.

  Lemma Zabs_div_exact (a b : Z) :
    b <> 0 ->
    a mod b = 0 ->
    Z.abs (a / b) = Z.abs a / Z.abs b.
  Proof using.
    intros B AMB.
    apply Zmod_divides in AMB; [| assumption ].
    destruct AMB as [c AMB].
    rewrite AMB at 1.
    apply f_equal with (f := Z.abs) in AMB.
    rewrite Z.abs_mul in AMB.
    rewrite AMB.
    rewrite Z.mul_comm. rewrite Z.div_mul.
    rewrite Z.mul_comm. rewrite Z.div_mul.
    all: lia.
  Qed.

  Lemma Zdigits_div_pow2 (m : Z) (d : positive) :
    m <> 0 ->
    m mod two_power_pos d = 0 ->
    Zdigits (m / two_power_pos d) = Zdigits m - Z.pos d.
  Proof using.
    intros M H.
    unfold Zdigits.
    rewrite Zabs_div_exact.
    rewrite two_power_pos_equiv in *.
    rewrite Z.abs_pow.
    remember (Z.abs m) as pm; remember (Z.pos d) as pd.
    apply Zmod_divides in H; destruct H.
    subst m.
    rewrite Z.abs_mul, Z.abs_pow in Heqpm.
    replace (Z.abs 2) with 2 in * by reflexivity.
    subst pm.
    remember (Z.abs x) as px.
    rewrite Z.mul_comm.
    rewrite Z.div_mul.
    rewrite Z.log2_mul_pow2.
    all: subst.
    all: try lia.
    assert (m mod 2 ^ Z.pos d < 2 ^ Z.pos d); try lia.
    apply BinInt.Z.mod_pos_bound.
    apply Z.pow_pos_nonneg; lia.
    rewrite two_power_pos_equiv; generalize (Z.pow_pos_nonneg 2 (Z.pos d)); lia.
  Qed.

  (** changing the mantissa's binary length results in an expected number of digits *)
  Lemma inc_digits_m_correct (f : bfloat) (ddm : positive) :
    not_zero f ->
    Zdigits (Fnum (inc_digits_m f ddm)) = Zdigits (Fnum f) + Z.pos ddm.
  Proof using.
    unfold inc_digits_m, dec_e; simpl.
    apply Zdigits_mul_pow2.
  Qed.

  Lemma dec_digits_m_correct (f1 : bfloat) (ddm : positive) {f2 : bfloat} :
    not_zero f1 ->
    dec_digits_m f1 ddm = Some f2 ->
    Zdigits (Fnum f2) = Zdigits (Fnum f1) - Z.pos ddm.
  Proof using.
    destruct f1 as [m1 e1], f2 as [m2 e2].
    unfold dec_digits_m, inc_e.
    simpl; intros M H.
    break_match; inversion H; clear H.
    rewrite Z.eqb_eq in Heqb.
    apply Zdigits_div_pow2; assumption.
  Qed.

  Lemma shift_digits_m_correct (f1 : bfloat) (ddm : Z) {f2 : bfloat} :
    Fnum f1 <> 0 ->
    shift_digits_m f1 ddm = Some f2 ->
    Zdigits (Fnum f2) = Zdigits (Fnum f1) + ddm.
  Proof using.
    unfold shift_digits_m, shift_e.
    simpl; intros M H.
    break_match; inversion H; clear H; subst.
    - lia.
    - replace inc_e with dec_digits_m in H1 by reflexivity.
      replace ddm with (Z.neg p) by lia.
      apply dec_digits_m_correct; assumption.
    - replace dec_e with inc_digits_m in Heqz by reflexivity.
      replace ddm with (Z.pos p) by lia.
      apply inc_digits_m_correct; assumption.
  Qed.

  Lemma set_digits_m_correct (f1 : bfloat) (dm : Z) {f2 : bfloat} :
    not_zero f1 ->
    set_digits_m f1 dm = Some f2 ->
    Zdigits (Fnum f2) = dm.
  Proof using.
    intros M H.
    unfold set_digits_m in H.
    apply shift_digits_m_correct in H; [| assumption].
    rewrite H.
    lia.
  Qed.

  (** changing the binary length of the mantissa preserves the float's value *)
  Lemma inc_digits_m_eq (f : bfloat) (ddm : positive) :
    float_eq f (inc_digits_m f ddm).
  Proof using.
    unfold inc_digits_m.
    apply dec_e_eq.
  Qed.

  Lemma dec_digits_m_eq (f1 : bfloat) (ddm : positive) {f2 : bfloat} :
    dec_digits_m f1 ddm = Some f2 ->
    float_eq f1 f2.
  Proof using.
    unfold dec_digits_m.
    apply inc_e_eq.
  Qed.

  Lemma shift_digits_m_eq (f1 : bfloat) (ddm : Z) {f2 : bfloat} :
    shift_digits_m f1 ddm = Some f2 ->
    float_eq f1 f2.
  Proof using.
    unfold shift_digits_m.
    apply shift_e_eq.
  Qed.

  Lemma set_digits_m_eq (f1 : bfloat) (dm : Z) {f2 : bfloat} :
    set_digits_m f1 dm = Some f2 ->
    float_eq f1 f2.
  Proof using.
    unfold set_digits_m.
    apply shift_digits_m_eq.
  Qed.

  (** two equal floats with the same exponent are exactly the same *)
  Lemma exponent_unique_fnum (f1 f2 : bfloat) :
    float_eq f1 f2 ->
    Fexp f1 = Fexp f2 ->
    Fnum f1 = Fnum f2.
  Proof using.
    unfold float_eq.
    destruct f1 as [m1 e1], f2 as [m2 e2].
    simpl; intros H E; destruct H; destruct H as [T H]; clear T; subst.
    all: rewrite Z.sub_diag; simpl; lia.
  Qed.

  Lemma exponent_unique (f1 f2 : bfloat) :
    float_eq f1 f2 ->
    Fexp f1 = Fexp f2 ->
    f1 = f2.
  Proof using.
    intros.
    pose proof exponent_unique_fnum f1 f2 H H0.
    destruct f1, f2; simpl in *.
    subst; reflexivity.
  Qed.

  (** two equal floats with the same mantissa length are exactly the same *)
  Lemma Zdigits_m_unique_fexp (f1 f2 : bfloat) :
    not_zero f1 ->
    float_eq f1 f2 ->
    Zdigits (Fnum f1) = Zdigits (Fnum f2) ->
    Fexp f1 = Fexp f2.
  Proof using.
    intros NZ1 H.
    assert (NZ2 : not_zero f2) by apply (not_zero_eq f1 f2 NZ1 H).
    unfold float_eq in *.
    destruct f1 as [m1 e1], f2 as [m2 e2].
    simpl in *; intro DM; destruct H; destruct H as [H1 H2]; subst.
    all: destruct (Z.eq_dec e1 e2); try assumption.
    - assert (e2 < e1) by lia; clear H1 n.
      apply Zcompare_Gt in H.
      apply Zcompare_Gt_spec in H; destruct H as [de H].
      replace (e1 - e2) with (Z.pos de) in DM by lia.
      rewrite <-two_power_pos_equiv in DM.
      rewrite Zdigits_mul_pow2 in DM by assumption.
      contradict DM; lia.
    - assert (e1 < e2) by lia; clear H1 n.
      apply Zcompare_Gt in H.
      apply Zcompare_Gt_spec in H; destruct H as [de H].
      replace (e2 - e1) with (Z.pos de) in DM by lia.
      rewrite <-two_power_pos_equiv in DM.
      rewrite Zdigits_mul_pow2 in DM by assumption.
      contradict DM; lia.
  Qed.

  Lemma Zdigits_m_unique (f1 f2 : bfloat) :
    not_zero f1 ->
    float_eq f1 f2 ->
    Zdigits (Fnum f1) = Zdigits (Fnum f2) ->
    f1 = f2.
  Proof using.
    intros.
    pose proof Zdigits_m_unique_fexp f1 f2 H H0 H1.
    apply exponent_unique; assumption.
  Qed.

  Fact Zdigits_Zpos_log_inf (p : positive) :
  Zdigits (Z.pos p) = Z.succ (Z.log2 (Zpos p)).
  Proof using.
    unfold Zdigits, Z.abs.
    reflexivity.
  Qed.

  Fact Zdigits_Zneg_log_inf (p : positive) :
  Zdigits (Z.neg p) = Z.succ (Z.log2 (Zpos p)).
  Proof using.
    unfold Zdigits, Z.abs.
    reflexivity.
  Qed.

  (* similar to [bounded_closed_form] *)
  Lemma valid_float_closed_form (prec emax : Z) (f : bfloat) (NZ : not_zero f)
        (prec_gt_0 : FLX.Prec_gt_0 prec) (Hmax : prec < emax) :
    let emin := 3 - emax - prec in
    let '(m, e) := (Fnum f, Fexp f) in
      valid_float prec emax f = true
      <->
      or
        (Zdigits m < prec /\ e = emin)
        (Zdigits m = prec /\ emin <= e <= emax - prec).
  Proof using.
    destruct f as [m e].
    intro.
    unfold FLX.Prec_gt_0 in prec_gt_0.
    unfold valid_float.
    simpl.
    destruct m.
    - (* Z0 *)
      unfold not_zero in NZ; simpl in NZ.
      contradict NZ.
      reflexivity.
    - (* Zpos *)
      rewrite bounded_closed_form by assumption;
        rewrite Zdigits_Zpos_log_inf;
        unfold compose.
      split; intros H; destruct H; auto.
    - (* Zneg *)
      rewrite bounded_closed_form by assumption.
        rewrite Zdigits_Zneg_log_inf;
        unfold compose.
      split; intros H; destruct H; auto.
  Qed.

  Lemma not_None_iff_exists_Some {A : Type} {x : option A} :
    x <> None <-> exists y, x = Some y.
  Proof using.
    split; intro.
    - destruct x.
      + exists a; reflexivity.
      + contradict H; reflexivity.
    - destruct H; subst; discriminate.
  Qed.

  Lemma float_eq_trans_l (f1 f2 f3 : bfloat) :
    float_eq f1 f2 ->
    float_eq f1 f3 ->
    float_eq f2 f3.
  Proof using.
    intros EQ12 EQ13.
    apply float_eq_sym in EQ12.
    apply float_eq_trans with (y := f1);
      assumption.
  Qed.

  Lemma float_eq_set_e (f1 f2 : bfloat) :
    float_eq f1 f2 ->
    set_e f1 (Fexp f2) = Some f2.
  Proof using.
    intro.
    destruct set_e as [f |] eqn:SE.
    - (* if successful, then equal *)
      pose proof set_e_eq f1 (Fexp f2) SE; rename H0 into H1.
      apply set_e_correct in SE.
      apply (float_eq_trans_l f1 f f2 H1) in H.
      apply (exponent_unique f f2 H) in SE.
      subst; reflexivity.
    - (* always successful *)
      exfalso.
      unfold float_eq, set_e, shift_e, inc_e, dec_e in *.
      destruct f1 as [m1 e1], f2 as [m2 e2]; simpl in *.
      repeat break_match; try discriminate.
      clear SE; rename Heqb into H1.
      apply Z.eqb_neq in H1.
      destruct H; destruct H as [E M]; [lia |]; subst.
      rewrite two_power_pos_equiv in H1.
      rewrite Z.mod_mul in H1; auto.
      generalize (Z.pow_pos_nonneg 2 (Z.pos p)); lia.
  Qed.

  Lemma float_eq_set_digits_m (f1 f2 : bfloat) :
    not_zero f1 ->
    float_eq f1 f2 ->
    set_digits_m f1 (Zdigits (Fnum f2)) = Some f2.
  Proof using.
    intros NZ1 H.
    assert (NZ2 : not_zero f2) by apply (not_zero_eq f1 f2 NZ1 H).
    destruct set_digits_m as [f |] eqn:SDM.
    - (* if successful, then equal *)
      pose proof set_digits_m_eq f1 (Zdigits (Fnum f2)) SDM; rename H0 into H1.
      apply set_digits_m_correct in SDM; auto.
      apply (float_eq_trans_l f1 f f2 H1) in H.
      assert (NZ: not_zero f) by (apply not_zero_eq with (f1 := f1); assumption).
      apply (Zdigits_m_unique f f2 NZ H) in SDM.
      subst; reflexivity.
    - (* always successful *)
      exfalso.
      unfold float_eq, set_digits_m, shift_digits_m, shift_e, inc_e, dec_e in *.
      destruct f1 as [m1 e1], f2 as [m2 e2]; simpl in *.
      repeat break_match; try discriminate.
      clear SDM; rename Heqb into H1.
      apply Z.eqb_neq in H1.
      destruct H; destruct H as [E M]; subst.
      + destruct (Z.eq_dec e1 e2).
        replace (e1 - e2) with 0 in Heqz by lia;
          rewrite Z.mul_1_r in Heqz; lia.
        assert (e2 < e1) by lia; clear E n.
        apply Zcompare_Gt in H.
        apply Zcompare_Gt_spec in H; destruct H.
        replace (e1 - e2) with (Z.pos x) in *.
        rewrite <-two_power_pos_equiv in *.
        rewrite Zdigits_mul_pow2 in Heqz.
        lia.
        auto.
      + destruct (Z.eq_dec e1 e2).
        replace (e2 - e1) with 0 in Heqz by lia;
          rewrite Z.mul_1_r in Heqz; lia.
        assert (e1 < e2) by lia; clear E n.
        apply Zcompare_Gt in H.
        apply Zcompare_Gt_spec in H; destruct H.
        replace (e2 - e1) with (Z.pos x) in *.
        rewrite <-two_power_pos_equiv in *.
        rewrite Zdigits_mul_pow2 in Heqz.
        assert (x = p) by lia; subst.
        rewrite two_power_pos_equiv in H1.
        rewrite Z.mod_mul in H1; auto.
        generalize (Z.pow_pos_nonneg 2 (Z.pos p)); lia.
        auto.
  Qed.

  (** ** declarative definition of `set_e` *)
  Lemma set_e_definition (f1 : bfloat) (e : Z) {f2 : bfloat} :
    set_e f1 e = Some f2 <->
    float_eq f1 f2 /\ Fexp f2 = e.
  Proof using.
    split; intro.
    - split.
      apply (set_e_eq f1 e H). apply (set_e_correct f1 e H).
    - destruct H as [EQ FEXP].
      subst.
      apply (float_eq_set_e f1 f2 EQ).
  Qed.

  (** ** declarative definition of `set_digits_m` *)
  Lemma set_digits_m_definition (f1 : bfloat) (dm : Z) {f2 : bfloat} :
    not_zero f1 ->
    set_digits_m f1 dm = Some f2 <->
    float_eq f1 f2 /\ Zdigits (Fnum f2) = dm.
  Proof using.
    intros NZ1.
    split; intro.
    - split.
      apply (set_digits_m_eq f1 dm H).
      apply (set_digits_m_correct f1 dm NZ1 H).
    - destruct H as [EQ FEXP].
      subst.
      apply (float_eq_set_digits_m f1 f2 NZ1 EQ).
  Qed.

  Lemma normalize_correct' (prec emax : Z) (f : bfloat) (NZ : not_zero f)
        (prec_gt_0 : FLX.Prec_gt_0 prec) (Hmax : prec < emax) :
    match (normalize_float prec emax f) with
    | Some nf => (float_eq f nf) /\ (valid_float prec emax nf = true)
    | None => forall (xf : bfloat),
        float_eq f xf -> valid_float prec emax xf = false
    end.
  Proof using.
    unfold FLX.Prec_gt_0 in prec_gt_0.
    break_match. rename b into nf.
    - (* successful normalization - equal and valid? *)
      unfold normalize_float in Heqo.
      repeat break_match; inversion Heqo; subst.
      + (* subnormal *)
        split.
        * (* same float? *)
          apply set_e_eq with (e := 3 - emax - prec).
          assumption.
        * (* valid float? *)
          apply Z.leb_le in Heqb0.
          rewrite valid_float_closed_form.
          apply set_e_correct in Heqo0.
          lia.
          apply not_zero_eq with (f1 := f). assumption.
          apply set_e_eq in Heqo0. assumption.
          unfold FLX.Prec_gt_0; lia.
          assumption.
      + (* normal *)
        split.
        * (* same float? *)
          apply set_digits_m_eq with (dm := prec).
          assumption.
        * (* valid float? *)
          apply andb_prop in Heqb1; destruct Heqb1 as [H1 H2].
          apply Z.leb_le in H1; apply Z.leb_le in H2.
          rewrite valid_float_closed_form.
          right.
          apply set_e_correct in Heqo0.
          apply set_digits_m_correct in Heqo1.
          lia.
          assumption.
          apply not_zero_eq with (f1 := f). assumption.
          apply set_digits_m_eq in Heqo1. assumption.
          unfold FLX.Prec_gt_0; lia.
          assumption.
    - (* unsuccessful normalization - impossible to normalize? *)
      intros xf H.
      apply Bool.not_true_is_false.
      intros V.
      assert (XNZ: not_zero xf) by apply (not_zero_eq f xf NZ H).
      rewrite valid_float_closed_form in V by assumption.
      destruct V as [V | V]; destruct V as [D E].
      + (* xf is subnormal *)
        unfold normalize_float in Heqo.
        repeat break_match; try discriminate; clear Heqo.
        all: rewrite <-E in Heqo0.
        all: rewrite float_eq_set_e in Heqo0 by assumption.
        all: inversion Heqo0; subst.
        all: rewrite Z.leb_gt in Heqb0; lia.
      + (* xf is normal *)
        unfold normalize_float in Heqo.
        repeat break_match; try discriminate; clear Heqo.
        * rewrite <-D in Heqo1.
          rewrite float_eq_set_digits_m in Heqo1 by assumption.
          inversion Heqo1; subst; clear Heqo1.
          apply Bool.andb_false_elim in Heqb1; destruct Heqb1.
          all: rewrite Z.leb_gt in e; lia.
        * rewrite <-D in Heqo1.
          rewrite float_eq_set_digits_m in Heqo1 by assumption.
          inversion Heqo1.
        * unfold set_e, shift_e, inc_e, dec_e in Heqo0.
          repeat break_match; try discriminate; clear Heqo0.
          remember (3 - emax - prec) as emin.
          rewrite Z.eqb_neq in Heqb.
          destruct f as [m e], xf as [xm xe].
          unfold float_eq, not_zero in *.
          simpl in *.
          destruct H; destruct H as [EXP NUM].
          -- lia.
          -- subst m.
             replace (xe - e) with ((xe - emin) + Z.pos p) in Heqb by lia.
             rewrite Z.pow_add_r in Heqb by lia.
             rewrite Z.mul_assoc in Heqb.
             rewrite two_power_pos_equiv in Heqb.
             rewrite Z.mod_mul in Heqb.
             contradict Heqb; reflexivity.
             pose proof Z.add_assoc.
             generalize (Z.pow_pos_nonneg 2 (Z.pos p)); lia.
  Qed.

  Theorem normalize_correct (prec emax : Z) (f : bfloat) (NZ : not_zero f)
        (prec_gt_0 : FLX.Prec_gt_0 prec) (Hmax : prec < emax) {nf : bfloat} :
    normalize_float prec emax f = Some nf
    <->
    (float_eq f nf) /\ (valid_float prec emax nf = true).
  Proof using.
    pose proof normalize_correct' prec emax f NZ prec_gt_0 Hmax.
    split; intro.
    - rewrite H0 in H; clear H0; assumption.
    - break_match; try discriminate.
      + destruct H, H0.
        rename b into f1, nf into f2.
        pose proof float_eq_trans_l f f1 f2 H H0 as EQ.
        pose proof not_zero_eq f f1 NZ H as NZ1.
        pose proof not_zero_eq f f2 NZ H0 as NZ2.
        clear H H0 NZ f Heqo.
        apply valid_float_closed_form in H1; try assumption.
        apply valid_float_closed_form in H2; try assumption.
        f_equal.
        destruct H1 as [H1 | H1], H2 as [H2 | H2];
          destruct H1 as [M1 E1], H2 as [M2 E2].
        * apply exponent_unique; try assumption.
          rewrite E1, E2; reflexivity.
        * exfalso. unfold float_eq in EQ.
          destruct EQ as [EQ | EQ]; destruct EQ as [E M].
          -- rewrite M in M2.
             replace (Fexp f1 - Fexp f2) with 0 in M2 by lia.
             simpl in M2; rewrite Z.mul_1_r in M2.
             rewrite M2 in M1.
             lia.
          -- rewrite M in M1.
             destruct (Fexp f2 - Fexp f1) eqn:T; try lia.
             simpl in M1; rewrite Z.mul_1_r in M1.
             rewrite M2 in M1.
             lia.
             rewrite <-two_power_pos_equiv in M1.
             rewrite Zdigits_mul_pow2 in M1.
             lia.
             unfold not_zero in NZ2; assumption.
        * exfalso. unfold float_eq in EQ.
          destruct EQ as [EQ | EQ]; destruct EQ as [E M].
          -- rewrite M in M2.
             destruct (Fexp f1 - Fexp f2) eqn:T; try lia.
             simpl in M2; rewrite Z.mul_1_r in M2.
             rewrite M1 in M2.
             lia.
             rewrite <-two_power_pos_equiv in M2.
             rewrite Zdigits_mul_pow2 in M2.
             lia.
             unfold not_zero in NZ2; assumption.
          -- rewrite M in M1.
             replace (Fexp f2 - Fexp f1) with 0 in M1 by lia.
             simpl in M1; rewrite Z.mul_1_r in M1.
             rewrite M1 in M2.
             lia.
        * apply Zdigits_m_unique; try assumption.
          rewrite M1, M2; reflexivity.
      + destruct H0;
        apply H in H0.
        rewrite H0 in H1.
        inversion H1.
  Qed.

End Correctness.
