Require Import ZArith PArith Lia List String.
Require Import Flocq.IEEE754.Binary Flocq.Core.Zaux Flocq.IEEE754.Bits.
Require Import Basics RelationClasses.
Require Import BinIntDef.
Import ListNotations.

(* From QuickChick Require Import QuickChick. *)
From QuickChick Require Import Generators Producer Show Sets.
Set Warnings "-extraction-opaque-accessed,-extraction".

(** [subst_max] performs as many [subst] as possible, clearing all
    trivial equalities from the context. *)
Ltac subst_max :=
  repeat match goal with
           | [H : ?X = _ |- _ ]  => subst X
           | [H : _ = ?X |- _] => subst X
         end.

(** The Coq [inversion] tries to preserve your context by only adding
    new equalities, and keeping the inverted hypothesis.  Often, you
    want the resulting equalities to be substituted everywhere.  [inv]
    performs this post-substitution.  Often, you don't need the
    original hypothesis anymore.  [invc] extends [inv] and removes the
    inverted hypothesis.  Sometimes, you also want to perform
    post-simplification.  [invcs] extends [invc] and tries to simplify
    what it can. *)
Ltac inv H := inversion H; subst_max.
Ltac invc H := inv H; clear H.
Ltac invcs H := invc H; simpl in *.

(** [tuple_inversion] inverses an equality of tuple into 
    equalities for each component. *)
Ltac tuple_inversion :=
  match goal with
    | [ H : (_, _, _, _) = (_, _, _, _) |- _ ] => invc H
    | [ H : (_, _, _) = (_, _, _) |- _ ] => invc H
    | [ H : (_, _) = (_, _) |- _ ] => invc H
  end.

Open Scope string.
(* Locate B754_zero. *)
Instance show_binary : forall (prec emax : Z), Show (binary_float prec emax) := {
  show c := match c with
              | @B754_zero _ _ false => "+0"
              | @B754_zero _ _ true => "-0"
              | @B754_infinity _ _ false => "+inf"
              | @B754_infinity _ _ true => "-inf"
              | @B754_nan _ _ false _ _ => "+NaN"
              | @B754_nan _ _ true _ _ => "-NaN"
              | @B754_finite _ _ s m e _ => (if s then "" else "-")
                                        ++ (show_Z (Z.pos m * 2 ^ e))
            end
}.

Close Scope string.
Open Scope Z.

#[local] Definition log2 := Z.log2.
#[local] Definition digits := compose Z.succ log2.

Lemma digits2_pos_log2 (m : positive) :
  Z.pos (Digits.digits2_pos m) = Z.succ (log2 (Zpos m)).
Proof.
  induction m; simpl.

  { rewrite Pos2Z.inj_succ. rewrite IHm.
    unfold log2, Z.log2.
    destruct m; cbn; lia.
  }

  { rewrite Pos2Z.inj_succ. rewrite IHm.
    unfold log2, Z.log2.
    destruct m; cbn; lia.
  }

  reflexivity.
Qed.

Lemma digits2_pos_digits (m : positive) :
  Z.pos (Digits.digits2_pos m) = digits (Zpos m).
Proof.
  unfold digits, compose.
  apply digits2_pos_log2.
Qed.

(** ** Flocq's Binary.bounded rewritten in a form close to IEEE-754 *)
Lemma bounded_unfolded (prec emax : Z)
    (prec_gt_0 : Flocq.Core.FLX.Prec_gt_0 prec) (Hmax : (prec < emax)%Z)
    (m : positive) (e : Z) :
  SpecFloat.bounded prec emax m e = true
  <->
  (digits (Zpos m) < prec /\ e = 3 - emax - prec) \/
  (digits (Zpos m) = prec /\ 3 - emax - prec <= e <= emax - prec).
Proof.
  unfold FLX.Prec_gt_0, SpecFloat.bounded, SpecFloat.canonical_mantissa, SpecFloat.fexp, SpecFloat.emin, FLT.FLT_exp in *.
  rewrite Bool.andb_true_iff, Z.leb_le, <-Zeq_is_eq_bool, digits2_pos_digits.
  remember (3 - emax - prec) as emin.
  split; intro.
  all: destruct (Z_lt_le_dec (digits (Zpos m) + e - prec) emin).
  all: try rewrite Z.max_r in * by lia.
  all: try rewrite Z.max_l in * by lia.
  all: lia.
Qed.

Definition binary32 := binary_float 24 128.
Definition binary64 := binary_float 53 1024.

Definition bool_gen : G bool :=
  oneof (ret true) [ret true; ret false].

(* Generates B754_zero values *)
Definition zerg (prec emax : Z) : G (binary_float prec emax) := 
  (liftGen (fun (s : bool) => B754_zero prec emax s)) 
    bool_gen.

(* Generates B754_infinity values *)
Definition infg (prec emax : Z) := 
  (liftGen (fun (s : bool) => B754_infinity prec emax s))
    bool_gen.

(* Generates B754_nan values. Needs payload and nan_pl proof *)
Definition nang (prec emax : Z) 
        (pl : positive) 
        (np : nan_pl prec pl = true) := 
  (liftGen (fun b => B754_nan prec emax b pl np))
    bool_gen.

Definition boundaries (prec emax : Z) (t : bool) :=
      if t 
      then (1, 2^prec - 1, 3 - emax - prec, 3 - emax - prec)%Z 
      else (2^(prec - 1), 2^prec - 1, 3 - emax - prec, emax - prec)%Z.

(* Generates B754_finite values. Needs prec_gt_0 Hmax proof *)
Definition bindGen' := @bindPf G ProducerGen.
Program Definition fing (prec emax : Z) 
        (prec_gt_0 : Flocq.Core.FLX.Prec_gt_0 prec)
        (Hmax : (prec < emax)%Z) : G (binary_float prec emax) :=
  bindGen' _ _ bool_gen (fun t => fun b0 => 
    bindGen' _ _ (returnGen (boundaries prec emax t)) 
    (fun '(m_min, m_max, e_min, e_max) => fun b1 =>
      bindGen' _ _ bool_gen (fun (s : bool) => fun b2 =>
        bindGen' _ _ (choose (m_min, m_max)) (fun (m : Z) => fun b3 =>
          bindGen' _ _ (choose (e_min, e_max)) (fun (e : Z) => fun b4 =>
            returnGen (B754_finite prec emax s (Z.to_pos m) e _)))))).
Next Obligation.
  (* get rid of technical junk *)
  clear s b0 b2; rename b3 into b2, b4 into b3.
  apply @semReturn in b1; try typeclasses eauto.
  apply @semChoose in b2; try typeclasses eauto.
  apply @semChoose in b3; try typeclasses eauto.
  all: unfold is_true, set1, boundaries in *.

  (* simplify *)
  destruct b2 as [B11 B12].
  destruct b3 as [B21 B22].
  all: destruct t; try rewrite Z.leb_le in *.
  Opaque Z.sub.
  all: tuple_inversion.
  all: try unfold FLX.Prec_gt_0 in *.

  (* main goals *)
  (* first main goal *)
  1,2: rewrite bounded_unfolded.
  all: unfold digits, Basics.compose, Z.succ, FLX.Prec_gt_0.
  all: try lia.
  1,2: rewrite Z2Pos.id.
  2: lia.
  assert (m < 2 ^ prec) by lia; clear B12; rename H into B12.
  rewrite Z.log2_lt_pow2 in B12.
  change BinInt.Z.log2 with log2 in B12.
  lia.
  lia.
  (* second main goal *)
  assert (m < 2 ^ prec) by lia; clear B12; rename H into B12.
  rewrite Z.log2_lt_pow2 in B12.
  rewrite Z.log2_le_pow2 in B11.
  right.
  change BinInt.Z.log2 with log2 in B12, B11.
  lia.
  (* subgoals *)
  1,2,3: clear Hmax e B21 B22 B12.
  1,2,3: assert (0 <= prec - 1) by lia.
  1,2,3: assert (0 < 2 ^ (prec - 1)).
  1,3,5: apply Z.pow_pos_nonneg.
  1,3,5: reflexivity.
  1,2,3: auto.
  1,2,3: lia.
  - 
    assert (T : (1) = (2 - 1)) by lia; rewrite T; clear T.
    rewrite <-Z.sub_le_mono_r.
    assert (T : (2) = (2 ^ 1)) by lia; rewrite T; clear T.
    apply Z.pow_le_mono_r; lia; lia.
  -
    clear m b2 e b3 H Hmax emax.
    assert (2 ^ (prec - 1) < 2 ^ prec); [| lia].
    apply Z.pow_lt_mono_r; lia.
Qed.

Theorem fing32_prec : FLX.Prec_gt_0 24.
Proof. unfold FLX.Prec_gt_0; reflexivity. Qed.

Theorem fing32_prec_emax : 24 < 128.
Proof. reflexivity. Qed.

(* Set of binary32 sub-generators *)
Definition zerg32 := zerg 24 128.
Definition infg32 := infg 24 128.
Definition nang32 (pl : positive) (np : nan_pl 24 pl = true) 
  := nang 24 128 pl np.
Definition fing32 := fing 24 128 fing32_prec fing32_prec_emax.

(* Full binary32 generator *)
Definition binary32_gen (pl : positive) (np : nan_pl 24 pl = true) 
  : G (binary32) :=
  freq_ zerg32 [(1, zerg32)%nat ; (1, infg32)%nat ;
                (1, nang32 pl np)%nat ; (7, fing32)%nat].

Theorem fing64_prec : FLX.Prec_gt_0 53.
Proof. unfold FLX.Prec_gt_0; reflexivity. Qed.

Theorem fing64_prec_emax : 53 < 1024.
Proof. reflexivity. Qed.

(* Set of binary64 sub-generators *)
Definition zerg64 := zerg 53 1024.
Definition infg64 := infg 53 1024.
Definition nang64 (pl : positive) (np : nan_pl 53 pl = true) 
  := nang 53 1024 pl np.
Definition fing64 := fing 53 1024 fing64_prec fing64_prec_emax.

(* Full binary64 generator *)
Definition binary64_gen (pl : positive) (np : nan_pl 53 pl = true)
  : G (binary64) :=
  freq_ zerg64 [(1, zerg64)%nat ; (1, infg64)%nat ;
                (1, nang64 pl np)%nat ; (7, fing64)%nat].
