(** * Generic facts about [Z] *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.

Open Scope Z_scope.

Lemma two_power_pos_eq : forall p, two_power_pos p = (2 ^ Z.pos p)%Z.
Proof. intros p; rewrite two_power_pos_equiv; reflexivity. Qed.

Lemma Z_gtb_irrefl : forall z : Z, (z >? z)%Z = false.
Proof.
  intros; rewrite Z.gtb_ltb; apply Z.ltb_irrefl.
Qed.

(** ** Little-endian concatenation of [w]-bit digits

    [concat_digits w [d0; d1; ...] = d0 + 2^w * d1 + ...].  When every digit
    fits in [w] bits, digit [i] can be read back off the result. *)
Fixpoint concat_digits (w : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | z :: l => z + Z.shiftl (concat_digits w l) w
  end.

Lemma concat_digits_range : forall w l,
    (0 < w)%Z -> Forall (fun z => 0 <= z < 2 ^ w)%Z l ->
    (0 <= concat_digits w l < 2 ^ (w * Z.of_nat (List.length l)))%Z.
Proof.
  intros w l Hw; induction l as [| z l IH]; intros HF; cbn [concat_digits List.length].
  - replace (w * Z.of_nat 0)%Z with 0%Z by lia; cbn; lia.
  - inversion HF as [| ? ? Hz Hl]; subst; specialize (IH Hl).
    assert (Hp : (0 < 2 ^ w)%Z) by (apply Z.pow_pos_nonneg; lia).
    rewrite Z.shiftl_mul_pow2 by lia.
    replace (w * Z.of_nat (S (List.length l)))%Z
      with (w + w * Z.of_nat (List.length l))%Z by lia.
    rewrite Z.pow_add_r by lia.
    nia.
Qed.

Lemma concat_digits_nth : forall w l i,
    (0 < w)%Z -> Forall (fun z => 0 <= z < 2 ^ w)%Z l -> (i < List.length l)%nat ->
    ((concat_digits w l / 2 ^ (w * Z.of_nat i)) mod 2 ^ w)%Z = nth i l 0%Z.
Proof.
  intros w l; induction l as [| z l IH]; intros i Hw HF Hi; cbn [List.length] in Hi;
    [lia |].
  inversion HF as [| ? ? Hz Hl]; subst.
  assert (Hp : (0 < 2 ^ w)%Z) by (apply Z.pow_pos_nonneg; lia).
  cbn [concat_digits]; rewrite Z.shiftl_mul_pow2 by lia.
  destruct i as [| i].
  - cbn [nth]; replace (w * Z.of_nat 0)%Z with 0%Z by lia.
    rewrite Z.pow_0_r, Z.div_1_r, Z_mod_plus_full.
    apply Z.mod_small; lia.
  - cbn [nth].
    replace (w * Z.of_nat (S i))%Z with (w + w * Z.of_nat i)%Z by lia.
    rewrite Z.pow_add_r by lia.
    rewrite <- Z.div_div by (try lia; apply Z.pow_pos_nonneg; lia).
    replace ((z + concat_digits w l * 2 ^ w) / 2 ^ w)%Z with (concat_digits w l).
    + apply IH; auto; lia.
    + rewrite Z.add_comm, Z.div_add_l by lia.
      rewrite (Z.div_small z) by lia; lia.
Qed.
