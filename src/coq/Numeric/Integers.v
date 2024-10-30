(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Formalizations of machine integers modulo $2^N$ #2<sup>N</sup>#. *)

Require Import Eqdep_dec Zquot.

Require Import Coqlib.

Require Import Coq.micromega.Lia.

Require Archi.

(** * Comparisons *)

Inductive comparison : Type :=
  | Ceq : comparison               (**r same *)
  | Cne : comparison               (**r different *)
  | Clt : comparison               (**r less than *)
  | Cle : comparison               (**r less than or equal *)
  | Cgt : comparison               (**r greater than *)
  | Cge : comparison.              (**r greater than or equal *)

Definition negate_comparison (c: comparison): comparison :=
  match c with
  | Ceq => Cne
  | Cne => Ceq
  | Clt => Cge
  | Cle => Cgt
  | Cgt => Cle
  | Cge => Clt
  end.

Definition swap_comparison (c: comparison): comparison :=
  match c with
  | Ceq => Ceq
  | Cne => Cne
  | Clt => Cgt
  | Cle => Cge
  | Cgt => Clt
  | Cge => Cle
  end.

(** * Parameterization by the word size, in bits. *)

Module Type WORDSIZE.
  Parameter wordsize: nat.
  Axiom wordsize_not_zero: wordsize <> 0%nat.
End WORDSIZE.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Section MakeInt.

Context {wordsize: positive}.
Definition zwordsize: Z := Zpos wordsize.
Definition natwordsize: nat := Pos.to_nat wordsize.
Definition modulus : Z := two_power_pos wordsize.
Definition half_modulus : Z := modulus / 2.
Definition max_unsigned : Z := modulus - 1.
Definition max_signed : Z := half_modulus - 1.
Definition min_signed : Z := - half_modulus.

Remark wordsize_pos: zwordsize > 0.
Proof.
  unfold zwordsize. lia.
Qed.

Remark modulus_power: modulus = two_p zwordsize.
Proof.
  unfold modulus. rewrite two_power_pos_nat, two_power_nat_two_p.
  rewrite positive_nat_Z.
  reflexivity.
Qed.

Remark modulus_pos: modulus > 0.
Proof.
  rewrite modulus_power. apply two_p_gt_ZERO. generalize wordsize_pos; lia.
Qed.

(** * Representation of machine integers *)

(** A machine integer (type [int]) is represented as a Coq arbitrary-precision
  integer (type [Z]) plus a proof that it is in the range 0 (included) to
  [modulus] (excluded). *)

Record bit_int: Type := mkint { intval: Z; intrange: -1 < intval < modulus }.

(** Fast normalization modulo [2^wordsize] *)

Fixpoint P_mod_two_p (p: positive) (n: nat) {struct n} : Z :=
  match n with
  | O => 0
  | S m =>
      match p with
      | xH => 1
      | xO q => Z.double (P_mod_two_p q m)
      | xI q => Z.succ_double (P_mod_two_p q m)
      end
  end.

Definition Z_mod_modulus (x: Z) : Z :=
  match x with
  | Z0 => 0
  | Zpos p => P_mod_two_p p natwordsize
  | Zneg p => let r := P_mod_two_p p natwordsize in if zeq r 0 then 0 else modulus - r
  end.

Lemma P_mod_two_p_range:
  forall n p, 0 <= P_mod_two_p p n < two_power_nat n.
Proof.
  induction n; simpl; intros.
  - rewrite two_power_nat_O. lia.
  - rewrite two_power_nat_S. destruct p.
    + generalize (IHn p). rewrite Z.succ_double_spec. lia.
    + generalize (IHn p). rewrite Z.double_spec. lia.
    + generalize (two_power_nat_pos n). lia.
Qed.

Lemma P_mod_two_p_eq:
  forall n p, P_mod_two_p p n = (Zpos p) mod (two_power_nat n).
Proof.
  assert (forall n p, exists y, Zpos p = y * two_power_nat n + P_mod_two_p p n).
  {
    induction n; simpl; intros.
    - rewrite two_power_nat_O. exists (Zpos p). ring.
    - rewrite two_power_nat_S. destruct p.
      + destruct (IHn p) as [y EQ]. exists y.
        change (Zpos p~1) with (2 * Zpos p + 1). rewrite EQ.
        rewrite Z.succ_double_spec. ring.
      + destruct (IHn p) as [y EQ]. exists y.
        change (Zpos p~0) with (2 * Zpos p). rewrite EQ.
        rewrite (Z.double_spec (P_mod_two_p p n)). ring.
      + exists 0; lia.
  }
  intros.
  destruct (H n p) as [y EQ].
  symmetry. apply Zmod_unique with y. auto. apply P_mod_two_p_range.
Qed.

Lemma Z_mod_modulus_range:
  forall x, 0 <= Z_mod_modulus x < modulus.
Proof.
  intros; unfold Z_mod_modulus.
  destruct x.
  - generalize modulus_pos; lia.
  - setoid_rewrite two_power_pos_nat.
    apply P_mod_two_p_range.
  - set (r := P_mod_two_p p natwordsize).
    assert (0 <= r < modulus) by (setoid_rewrite two_power_pos_nat; apply P_mod_two_p_range).
    destruct (zeq r 0).
    + generalize modulus_pos; lia.
    + lia.
Qed.

Lemma Z_mod_modulus_range':
  forall x, -1 < Z_mod_modulus x < modulus.
Proof.
  intros. generalize (Z_mod_modulus_range x); lia.
Qed.

Lemma Z_mod_modulus_eq:
  forall x, Z_mod_modulus x = x mod modulus.
Proof.
  intros. unfold Z_mod_modulus. destruct x.
  - rewrite Zmod_0_l. auto.
  - setoid_rewrite two_power_pos_nat; apply P_mod_two_p_eq.
  - generalize (P_mod_two_p_range natwordsize p) (P_mod_two_p_eq natwordsize p).
    fold modulus. intros A B.
    pose proof (Z_div_mod_eq_full (Zpos p) modulus) as C.
    set (q := Zpos p / modulus) in *.
    set (r := P_mod_two_p p natwordsize) in *.
    setoid_rewrite two_power_pos_nat in C.
    setoid_rewrite two_power_pos_nat.
    unfold natwordsize in *.
    rewrite <- B in C.
    change (Z.neg p) with (- (Z.pos p)). destruct (zeq r 0).
    + symmetry. apply Zmod_unique with (-q). rewrite C; rewrite e. ring.
      generalize modulus_pos; lia.
    + setoid_rewrite two_power_pos_nat.
      symmetry. apply Zmod_unique with (-q - 1). rewrite C. ring.
      lia.
Qed.

(** The [unsigned] and [signed] functions return the Coq integer corresponding
  to the given machine integer, interpreted as unsigned or signed
  respectively. *)

Definition unsigned (n: bit_int) : Z := intval n.

Definition signed (n: bit_int) : Z :=
  let x := unsigned n in
  if zlt x half_modulus then x else x - modulus.

(** Conversely, [repr] takes a Coq integer and returns the corresponding
  machine integer.  The argument is treated modulo [modulus]. *)

Definition repr (x: Z) : bit_int :=
  mkint (Z_mod_modulus x) (Z_mod_modulus_range' x).

Definition zero := repr 0.
Definition one  := repr 1.
Definition mone := repr (-1).
Definition iwordsize := repr zwordsize.

Lemma mkint_eq:
  forall x y Px Py, x = y -> mkint x Px = mkint y Py.
Proof.
  intros. subst y.
  assert (forall (n m: Z) (P1 P2: n < m), P1 = P2).
  {
    unfold Z.lt; intros.
    apply eq_proofs_unicity.
    intros c1 c2. destruct c1; destruct c2; (left; reflexivity) || (right; congruence).
  }
  destruct Px as [Px1 Px2]. destruct Py as [Py1 Py2].
  rewrite (H _ _ Px1 Py1).
  rewrite (H _ _ Px2 Py2).
  reflexivity.
Qed.

Lemma eq_dec: forall (x y: bit_int), {x = y} + {x <> y}.
Proof.
  intros. destruct x; destruct y. destruct (zeq intval0 intval1).
  left. apply mkint_eq. auto.
  right. red; intro. injection H. exact n.
Defined.

(** * Arithmetic and logical operations over machine integers *)

Definition eq (x y: bit_int) : bool :=
  if zeq (unsigned x) (unsigned y) then true else false.
Definition lt (x y: bit_int) : bool :=
  if zlt (signed x) (signed y) then true else false.
Definition ltu (x y: bit_int) : bool :=
  if zlt (unsigned x) (unsigned y) then true else false.

Definition neg (x: bit_int) : bit_int := repr (- unsigned x).

Definition add (x y: bit_int) : bit_int :=
  repr (unsigned x + unsigned y).
Definition sub (x y: bit_int) : bit_int :=
  repr (unsigned x - unsigned y).
Definition mul (x y: bit_int) : bit_int :=
  repr (unsigned x * unsigned y).

Definition divs (x y: bit_int) : bit_int :=
  repr (Z.quot (signed x) (signed y)).
Definition mods (x y: bit_int) : bit_int :=
  repr (Z.rem (signed x) (signed y)).

Definition divu (x y: bit_int) : bit_int :=
  repr (unsigned x / unsigned y).
Definition modu (x y: bit_int) : bit_int :=
  repr ((unsigned x) mod (unsigned y)).

(** Bitwise boolean operations. *)

Definition and (x y: bit_int): bit_int := repr (Z.land (unsigned x) (unsigned y)).
Definition or (x y: bit_int): bit_int := repr (Z.lor (unsigned x) (unsigned y)).
Definition xor (x y: bit_int) : bit_int := repr (Z.lxor (unsigned x) (unsigned y)).

Definition not (x: bit_int) : bit_int := xor x mone.

(** Shifts and rotates. *)

Definition shl (x y: bit_int): bit_int := repr (Z.shiftl (unsigned x) (unsigned y)).
Definition shru (x y: bit_int): bit_int := repr (Z.shiftr (unsigned x) (unsigned y)).
Definition shr (x y: bit_int): bit_int := repr (Z.shiftr (signed x) (unsigned y)).

Definition rol (x y: bit_int) : bit_int :=
  let n := (unsigned y) mod zwordsize in
  repr (Z.lor (Z.shiftl (unsigned x) n) (Z.shiftr (unsigned x) (zwordsize - n))).
Definition ror (x y: bit_int) : bit_int :=
  let n := (unsigned y) mod zwordsize in
  repr (Z.lor (Z.shiftr (unsigned x) n) (Z.shiftl (unsigned x) (zwordsize - n))).

Definition rolm (x a m: bit_int): bit_int := and (rol x a) m.

(** Viewed as signed divisions by powers of two, [shrx] rounds towards
  zero, while [shr] rounds towards minus infinity. *)

Definition shrx (x y: bit_int): bit_int :=
  divs x (shl one y).

(** High half of full multiply. *)

Definition mulhu (x y: bit_int): bit_int := repr ((unsigned x * unsigned y) / modulus).
Definition mulhs (x y: bit_int): bit_int := repr ((signed x * signed y) / modulus).

(** Condition flags *)

Definition negative (x: bit_int): bit_int :=
  if lt x zero then one else zero.

Definition add_carry (x y cin: bit_int): bit_int :=
  if zlt (unsigned x + unsigned y + unsigned cin) modulus then zero else one.

Definition add_overflow (x y cin: bit_int): bit_int :=
  let s := signed x + signed y + signed cin in
  if zle min_signed s && zle s max_signed then zero else one.

Definition sub_borrow (x y bin: bit_int): bit_int :=
  if zlt (unsigned x - unsigned y - unsigned bin) 0 then one else zero.

Definition sub_overflow (x y bin: bit_int): bit_int :=
  let s := signed x - signed y - signed bin in
  if zle min_signed s && zle s max_signed then zero else one.

(** [shr_carry x y] is 1 if [x] is negative and at least one 1 bit is shifted away. *)

Definition shr_carry (x y: bit_int) : bit_int :=
  if lt x zero && negb (eq (and x (sub (shl one y) one)) zero)
  then one else zero.

(** Zero and sign extensions *)

Definition Zshiftin (b: bool) (x: Z) : Z :=
  if b then Z.succ_double x else Z.double x.

(** In pseudo-code:
<<
    Fixpoint Zzero_ext (n: Z) (x: Z) : Z :=
      if zle n 0 then
        0
      else
        Zshiftin (Z.odd x) (Zzero_ext (Z.pred n) (Z.div2 x)).
    Fixpoint Zsign_ext (n: Z) (x: Z) : Z :=
      if zle n 1 then
        if Z.odd x then -1 else 0
      else
        Zshiftin (Z.odd x) (Zzero_ext (Z.pred n) (Z.div2 x)).
>>
  We encode this [nat]-like recursion using the [Z.iter] iteration
  function, in order to make the [Zzero_ext] and [Zsign_ext]
  functions efficiently executable within Coq.
*)

Definition Zzero_ext (n: Z) (x: Z) : Z :=
  Z.iter n
    (fun rec x => Zshiftin (Z.odd x) (rec (Z.div2 x)))
    (fun x => 0)
    x.

Definition Zsign_ext (n: Z) (x: Z) : Z :=
  Z.iter (Z.pred n)
    (fun rec x => Zshiftin (Z.odd x) (rec (Z.div2 x)))
    (fun x => if Z.odd x then -1 else 0)
    x.

Definition zero_ext (n: Z) (x: bit_int) : bit_int := repr (Zzero_ext n (unsigned x)).

Definition sign_ext (n: Z) (x: bit_int) : bit_int := repr (Zsign_ext n (unsigned x)).

(** Decomposition of a number as a sum of powers of two. *)

Fixpoint Z_one_bits (n: nat) (x: Z) (i: Z) {struct n}: list Z :=
  match n with
  | O => nil
  | S m =>
      if Z.odd x
      then i :: Z_one_bits m (Z.div2 x) (i+1)
      else Z_one_bits m (Z.div2 x) (i+1)
  end.

Definition one_bits (x: bit_int) : list bit_int :=
  List.map repr (Z_one_bits natwordsize (unsigned x) 0).

(** Recognition of powers of two. *)

Definition is_power2 (x: bit_int) : option bit_int :=
  match Z_one_bits natwordsize (unsigned x) 0 with
  | i :: nil => Some (repr i)
  | _ => None
  end.

(** Comparisons. *)

Definition cmp (c: comparison) (x y: bit_int) : bool :=
  match c with
  | Ceq => eq x y
  | Cne => negb (eq x y)
  | Clt => lt x y
  | Cle => negb (lt y x)
  | Cgt => lt y x
  | Cge => negb (lt x y)
  end.

Definition cmpu (c: comparison) (x y: bit_int) : bool :=
  match c with
  | Ceq => eq x y
  | Cne => negb (eq x y)
  | Clt => ltu x y
  | Cle => negb (ltu y x)
  | Cgt => ltu y x
  | Cge => negb (ltu x y)
  end.

Definition is_false (x: bit_int) : Prop := x = zero.
Definition is_true  (x: bit_int) : Prop := x <> zero.
Definition notbool  (x: bit_int) : bit_int  := if eq x zero then one else zero.

(** x86-style extended division and modulus *)

Definition divmodu2 (nhi nlo: bit_int) (d: bit_int) : option (bit_int * bit_int) :=
  if eq_dec d zero then None else
   (let (q, r) := Z.div_eucl (unsigned nhi * modulus + unsigned nlo) (unsigned d) in
    if zle q max_unsigned then Some(repr q, repr r) else None).

Definition divmods2 (nhi nlo: bit_int) (d: bit_int) : option (bit_int * bit_int) :=
  if eq_dec d zero then None else
   (let (q, r) := Z.quotrem (signed nhi * modulus + unsigned nlo) (signed d) in
    if zle min_signed q && zle q max_signed then Some(repr q, repr r) else None).

(** * Properties of integers and integer arithmetic *)

(** ** Properties of [modulus], [max_unsigned], etc. *)

Remark half_modulus_power:
  half_modulus = two_p (zwordsize - 1).
Proof.
  unfold half_modulus. rewrite modulus_power.
  set (ws1 := zwordsize - 1).
  replace (zwordsize) with (Z.succ ws1).
  rewrite two_p_S. rewrite Z.mul_comm. apply Z_div_mult. lia.
  unfold ws1. generalize wordsize_pos; lia.
  unfold ws1. lia.
Qed.

Remark half_modulus_modulus: modulus = 2 * half_modulus.
Proof.
  rewrite half_modulus_power. rewrite modulus_power.
  rewrite <- two_p_S. apply f_equal. lia.
  generalize wordsize_pos; lia.
Qed.

(** Relative positions, from greatest to smallest:
<<
      max_unsigned
      max_signed
      2*wordsize-1
      wordsize
      0
      min_signed
>>
*)

Remark half_modulus_pos: half_modulus > 0.
Proof.
  rewrite half_modulus_power. apply two_p_gt_ZERO. generalize wordsize_pos; lia.
Qed.

Remark min_signed_neg: min_signed < 0.
Proof.
  unfold min_signed. generalize half_modulus_pos. lia.
Qed.

Remark max_signed_pos: max_signed >= 0.
Proof.
  unfold max_signed. generalize half_modulus_pos. lia.
Qed.

Remark wordsize_max_unsigned: zwordsize <= max_unsigned.
Proof.
  assert (zwordsize < modulus).
    rewrite modulus_power. apply two_p_strict.
    generalize wordsize_pos. lia.
  unfold max_unsigned. lia.
Qed.

Remark two_wordsize_max_unsigned: 2 * zwordsize - 1 <= max_unsigned.
Proof.
  assert (2 * zwordsize - 1 < modulus).
    rewrite modulus_power. apply two_p_strict_2. generalize wordsize_pos; lia.
  unfold max_unsigned; lia.
Qed.

Remark max_signed_unsigned: max_signed < max_unsigned.
Proof.
  unfold max_signed, max_unsigned. rewrite half_modulus_modulus.
  generalize half_modulus_pos. lia.
Qed.

Lemma unsigned_repr_eq:
  forall x, unsigned (repr x) = Z.modulo x modulus.
Proof.
  intros. simpl. apply Z_mod_modulus_eq.
Qed.

Lemma signed_repr_eq:
  forall x, signed (repr x) = if zlt (Z.modulo x modulus) half_modulus then Z.modulo x modulus else Z.modulo x modulus - modulus.
Proof.
  intros. unfold signed. rewrite unsigned_repr_eq. auto.
Qed.

(** ** Modulo arithmetic *)

(** We define and state properties of equality and arithmetic modulo a
  positive integer. *)

Section EQ_MODULO.

Variable modul: Z.
Hypothesis modul_pos: modul > 0.

Definition eqmod (x y: Z) : Prop := exists k, x = k * modul + y.

Lemma eqmod_refl: forall x, eqmod x x.
Proof using Type.
  intros; red. exists 0. lia.
Qed.

Lemma eqmod_refl2: forall x y, x = y -> eqmod x y.
Proof using Type.
  intros. subst y. apply eqmod_refl.
Qed.

Lemma eqmod_sym: forall x y, eqmod x y -> eqmod y x.
Proof using Type.
  intros x y [k EQ]; red. exists (-k). subst x. ring.
Qed.

Lemma eqmod_trans: forall x y z, eqmod x y -> eqmod y z -> eqmod x z.
Proof using Type.
  intros x y z [k1 EQ1] [k2 EQ2]; red.
  exists (k1 + k2). subst x; subst y. ring.
Qed.

Lemma eqmod_small_eq:
  forall x y, eqmod x y -> 0 <= x < modul -> 0 <= y < modul -> x = y.
Proof using Type.
  intros x y [k EQ] I1 I2.
  generalize (Zdiv_unique _ _ _ _ EQ I2). intro.
  rewrite (Zdiv_small x modul I1) in H. subst k. lia.
Qed.

Lemma eqmod_mod_eq:
  forall x y, eqmod x y -> x mod modul = y mod modul.
Proof using modul_pos.
  intros x y [k EQ]. subst x.
  rewrite Z.add_comm. apply Z_mod_plus. auto.
Qed.

Lemma eqmod_mod:
  forall x, eqmod x (x mod modul).
Proof using Type.
  intros; red. exists (x / modul).
  rewrite Z.mul_comm. apply Z_div_mod_eq_full.
Qed.

Lemma eqmod_add:
  forall a b c d, eqmod a b -> eqmod c d -> eqmod (a + c) (b + d).
Proof using Type.
  intros a b c d [k1 EQ1] [k2 EQ2]; red.
  subst a; subst c. exists (k1 + k2). ring.
Qed.

Lemma eqmod_neg:
  forall x y, eqmod x y -> eqmod (-x) (-y).
Proof using Type.
  intros x y [k EQ]; red. exists (-k). rewrite EQ. ring.
Qed.

Lemma eqmod_sub:
  forall a b c d, eqmod a b -> eqmod c d -> eqmod (a - c) (b - d).
Proof using Type.
  intros a b c d [k1 EQ1] [k2 EQ2]; red.
  subst a; subst c. exists (k1 - k2). ring.
Qed.

Lemma eqmod_mult:
  forall a b c d, eqmod a c -> eqmod b d -> eqmod (a * b) (c * d).
Proof using Type.
  intros a b c d [k1 EQ1] [k2 EQ2]; red.
  subst a; subst b.
  exists (k1 * k2 * modul + c * k2 + k1 * d).
  ring.
Qed.

End EQ_MODULO.

Lemma eqmod_divides:
  forall n m x y, eqmod n x y -> Z.divide m n -> eqmod m x y.
Proof.
  intros. destruct H as [k1 EQ1]. destruct H0 as [k2 EQ2].
  exists (k1*k2). rewrite <- Z.mul_assoc. rewrite <- EQ2. auto.
Qed.

(** We then specialize these definitions to equality modulo
  $2^{wordsize}$ #2<sup>wordsize</sup>#. *)

Hint Resolve modulus_pos: bit_ints.

Definition eqm := eqmod modulus.

Lemma eqm_refl: forall x, eqm x x.
Proof (eqmod_refl modulus).
Hint Resolve eqm_refl: bit_ints.

Lemma eqm_refl2:
  forall x y, x = y -> eqm x y.
Proof (eqmod_refl2 modulus).
Hint Resolve eqm_refl2: bit_ints.

Lemma eqm_sym: forall x y, eqm x y -> eqm y x.
Proof (eqmod_sym modulus).
Hint Resolve eqm_sym: bit_ints.

Lemma eqm_trans: forall x y z, eqm x y -> eqm y z -> eqm x z.
Proof (eqmod_trans modulus).
Hint Resolve eqm_trans: bit_ints.

Lemma eqm_small_eq:
  forall x y, eqm x y -> 0 <= x < modulus -> 0 <= y < modulus -> x = y.
Proof (eqmod_small_eq modulus).
Hint Resolve eqm_small_eq: bit_ints.

Lemma eqm_add:
  forall a b c d, eqm a b -> eqm c d -> eqm (a + c) (b + d).
Proof (eqmod_add modulus).
Hint Resolve eqm_add: bit_ints.

Lemma eqm_neg:
  forall x y, eqm x y -> eqm (-x) (-y).
Proof (eqmod_neg modulus).
Hint Resolve eqm_neg: bit_ints.

Lemma eqm_sub:
  forall a b c d, eqm a b -> eqm c d -> eqm (a - c) (b - d).
Proof (eqmod_sub modulus).
Hint Resolve eqm_sub: bit_ints.

Lemma eqm_mult:
  forall a b c d, eqm a c -> eqm b d -> eqm (a * b) (c * d).
Proof (eqmod_mult modulus).
Hint Resolve eqm_mult: bit_ints.

(** ** Properties of the coercions between [Z] and [int] *)

Lemma eqm_samerepr: forall x y, eqm x y -> repr x = repr y.
Proof.
  intros. unfold repr. apply mkint_eq.
  rewrite !Z_mod_modulus_eq. apply eqmod_mod_eq. auto with bit_ints. exact H.
Qed.

Lemma eqm_unsigned_repr:
  forall z, eqm z (unsigned (repr z)).
Proof.
  unfold eqm; intros. rewrite unsigned_repr_eq. apply eqmod_mod.
Qed.
Hint Resolve eqm_unsigned_repr: bit_ints.

Lemma eqm_unsigned_repr_l:
  forall a b, eqm a b -> eqm (unsigned (repr a)) b.
Proof.
  intros. apply eqm_trans with a.
  apply eqm_sym. apply eqm_unsigned_repr. auto.
Qed.
Hint Resolve eqm_unsigned_repr_l: bit_ints.

Lemma eqm_unsigned_repr_r:
  forall a b, eqm a b -> eqm a (unsigned (repr b)).
Proof.
  intros. apply eqm_trans with b. auto.
  apply eqm_unsigned_repr.
Qed.
Hint Resolve eqm_unsigned_repr_r: bit_ints.

Lemma eqm_signed_unsigned:
  forall x, eqm (signed x) (unsigned x).
Proof.
  intros; red. unfold signed. set (y := unsigned x).
  case (zlt y half_modulus); intro.
  apply eqmod_refl. red; exists (-1); ring.
Qed.

Theorem unsigned_range:
  forall i, 0 <= unsigned i < modulus.
Proof.
  destruct i. simpl. lia.
Qed.
Hint Resolve unsigned_range: bit_ints.

Theorem unsigned_range_2:
  forall i, 0 <= unsigned i <= max_unsigned.
Proof.
  intro; unfold max_unsigned.
  generalize (unsigned_range i). lia.
Qed.
Hint Resolve unsigned_range_2: bit_ints.

Theorem signed_range:
  forall i, min_signed <= signed i <= max_signed.
Proof.
  intros. unfold signed.
  generalize (unsigned_range i). set (n := unsigned i). intros.
  case (zlt n half_modulus); intro.
  unfold max_signed. generalize min_signed_neg. lia.
  unfold min_signed, max_signed.
  rewrite half_modulus_modulus in *. lia.
Qed.

Theorem repr_unsigned:
  forall i, repr (unsigned i) = i.
Proof.
  destruct i; simpl. unfold repr. apply mkint_eq.
  rewrite Z_mod_modulus_eq. apply Zmod_small; lia.
Qed.
Hint Resolve repr_unsigned: bit_ints.

Lemma repr_signed:
  forall i, repr (signed i) = i.
Proof.
  intros. transitivity (repr (unsigned i)).
  apply eqm_samerepr. apply eqm_signed_unsigned. auto with bit_ints.
Qed.
Hint Resolve repr_signed: bit_ints.

Opaque repr.

Lemma eqm_repr_eq: forall x y, eqm x (unsigned y) -> repr x = y.
Proof.
  intros. rewrite <- (repr_unsigned y). apply eqm_samerepr; auto.
Qed.

Theorem unsigned_repr:
  forall z, 0 <= z <= max_unsigned -> unsigned (repr z) = z.
Proof.
  intros. rewrite unsigned_repr_eq.
  apply Zmod_small. unfold max_unsigned in H. lia.
Qed.
Hint Resolve unsigned_repr: bit_ints.

Theorem signed_repr:
  forall z, min_signed <= z <= max_signed -> signed (repr z) = z.
Proof.
  intros. unfold signed. destruct (zle 0 z).
  replace (unsigned (repr z)) with z.
  rewrite zlt_true. auto. unfold max_signed in H. lia.
  symmetry. apply unsigned_repr. generalize max_signed_unsigned. lia.
  pose (z' := z + modulus).
  replace (repr z) with (repr z').
  replace (unsigned (repr z')) with z'.
  rewrite zlt_false. unfold z'. lia.
  unfold z'. unfold min_signed in H.
  rewrite half_modulus_modulus. lia.
  symmetry. apply unsigned_repr.
  unfold z', max_unsigned. unfold min_signed, max_signed in H.
  rewrite half_modulus_modulus. lia.
  apply eqm_samerepr. unfold z'; red. exists 1. lia.
Qed.

Theorem signed_eq_unsigned:
  forall x, unsigned x <= max_signed -> signed x = unsigned x.
Proof.
  intros. unfold signed. destruct (zlt (unsigned x) half_modulus).
  auto. unfold max_signed in H. lia.
Qed.

Theorem signed_positive:
  forall x, signed x >= 0 <-> unsigned x <= max_signed.
Proof.
  intros. unfold signed, max_signed.
  generalize (unsigned_range x) half_modulus_modulus half_modulus_pos; intros.
  destruct (zlt (unsigned x) half_modulus); lia.
Qed.

(** ** Properties of zero, one, minus one *)

Theorem unsigned_zero: unsigned zero = 0.
Proof.
  unfold zero; rewrite unsigned_repr_eq. apply Zmod_0_l.
Qed.

Theorem unsigned_one: unsigned one = 1.
Proof.
  unfold one; rewrite unsigned_repr_eq. apply Zmod_small. split. lia.
  setoid_rewrite two_power_pos_nat.
  replace (Pos.to_nat wordsize) with (S(Init.Nat.pred (Pos.to_nat wordsize))).
  rewrite two_power_nat_S. generalize (two_power_nat_pos (Init.Nat.pred (Pos.to_nat wordsize))).
  lia.
  generalize wordsize_pos. unfold zwordsize. lia.
Qed.

Theorem unsigned_mone: unsigned mone = modulus - 1.
Proof.
  unfold mone; rewrite unsigned_repr_eq.
  replace (-1) with ((modulus - 1) + (-1) * modulus).
  rewrite Z_mod_plus_full. apply Zmod_small.
  generalize modulus_pos. lia. lia.
Qed.

Theorem signed_zero: signed zero = 0.
Proof.
  unfold signed. rewrite unsigned_zero. apply zlt_true. generalize half_modulus_pos; lia.
Qed.

Theorem signed_one: zwordsize > 1 -> signed one = 1.
Proof.
  intros. unfold signed. rewrite unsigned_one. apply zlt_true.
  change 1 with (two_p 0). rewrite half_modulus_power. apply two_p_monotone_strict. lia.
Qed.

Theorem signed_mone: signed mone = -1.
Proof.
  unfold signed. rewrite unsigned_mone.
  rewrite zlt_false. lia.
  rewrite half_modulus_modulus. generalize half_modulus_pos. lia.
Qed.

Theorem one_not_zero: one <> zero.
Proof.
  assert (unsigned one <> unsigned zero).
  rewrite unsigned_one; rewrite unsigned_zero; congruence.
  congruence.
Qed.

Theorem unsigned_repr_wordsize:
  unsigned iwordsize = zwordsize.
Proof.
  unfold iwordsize; rewrite unsigned_repr_eq. apply Zmod_small.
  generalize wordsize_pos wordsize_max_unsigned; unfold max_unsigned; lia.
Qed.

(** ** Properties of equality *)

Theorem eq_sym:
  forall x y, eq x y = eq y x.
Proof.
  intros; unfold eq. case (zeq (unsigned x) (unsigned y)); intro.
  rewrite e. rewrite zeq_true. auto.
  rewrite zeq_false. auto. auto.
Qed.

Theorem eq_spec: forall (x y: bit_int), if eq x y then x = y else x <> y.
Proof.
  intros; unfold eq. case (eq_dec x y); intro.
  subst y. rewrite zeq_true. auto.
  rewrite zeq_false. auto.
  destruct x; destruct y.
  simpl. red; intro. elim n. apply mkint_eq. auto.
Qed.

Theorem eq_true: forall x, eq x x = true.
Proof.
  intros. generalize (eq_spec x x); case (eq x x); intros; congruence.
Qed.

Theorem eq_false: forall x y, x <> y -> eq x y = false.
Proof.
  intros. generalize (eq_spec x y); case (eq x y); intros; congruence.
Qed.

Theorem eq_signed:
  forall x y, eq x y = if zeq (signed x) (signed y) then true else false.
Proof.
  intros. predSpec eq eq_spec x y.
  subst x. rewrite zeq_true; auto.
  destruct (zeq (signed x) (signed y)); auto.
  elim H. rewrite <- (repr_signed x). rewrite <- (repr_signed y). congruence.
Qed.

(** ** Properties of addition *)

Theorem add_unsigned: forall x y, add x y = repr (unsigned x + unsigned y).
Proof. intros; reflexivity.
Qed.

Theorem add_signed: forall x y, add x y = repr (signed x + signed y).
Proof.
  intros. rewrite add_unsigned. apply eqm_samerepr.
  apply eqm_add; apply eqm_sym; apply eqm_signed_unsigned.
Qed.

Theorem add_commut: forall x y, add x y = add y x.
Proof. intros; unfold add. decEq. lia. Qed.

Theorem add_zero: forall x, add x zero = x.
Proof.
  intros. unfold add. rewrite unsigned_zero.
  rewrite Z.add_0_r. apply repr_unsigned.
Qed.

Theorem add_zero_l: forall x, add zero x = x.
Proof.
  intros. rewrite add_commut. apply add_zero.
Qed.

Theorem add_assoc: forall x y z, add (add x y) z = add x (add y z).
Proof.
  intros; unfold add.
  set (x' := unsigned x).
  set (y' := unsigned y).
  set (z' := unsigned z).
  apply eqm_samerepr.
  apply eqm_trans with ((x' + y') + z').
  auto with bit_ints.
  rewrite <- Z.add_assoc. auto with bit_ints.
Qed.

Theorem add_permut: forall x y z, add x (add y z) = add y (add x z).
Proof.
  intros. rewrite (add_commut y z). rewrite <- add_assoc. apply add_commut.
Qed.

Theorem add_neg_zero: forall x, add x (neg x) = zero.
Proof.
  intros; unfold add, neg, zero. apply eqm_samerepr.
  replace 0 with (unsigned x + (- (unsigned x))).
  auto with bit_ints. lia.
Qed.

Theorem unsigned_add_carry:
  forall x y,
  unsigned (add x y) = unsigned x + unsigned y - unsigned (add_carry x y zero) * modulus.
Proof.
  intros.
  unfold add, add_carry. rewrite unsigned_zero. rewrite Z.add_0_r.
  rewrite unsigned_repr_eq.
  generalize (unsigned_range x) (unsigned_range y). intros.
  destruct (zlt (unsigned x + unsigned y) modulus).
  rewrite unsigned_zero. apply Zmod_unique with 0. lia. lia.
  rewrite unsigned_one. apply Zmod_unique with 1. lia. lia.
Qed.

Corollary unsigned_add_either:
  forall x y,
  unsigned (add x y) = unsigned x + unsigned y
  \/ unsigned (add x y) = unsigned x + unsigned y - modulus.
Proof.
  intros. rewrite unsigned_add_carry. unfold add_carry.
  rewrite unsigned_zero. rewrite Z.add_0_r.
  destruct (zlt (unsigned x + unsigned y) modulus).
  rewrite unsigned_zero. left; lia.
  rewrite unsigned_one. right; lia.
Qed.

(** ** Properties of negation *)

Theorem neg_repr: forall z, neg (repr z) = repr (-z).
Proof.
  intros; unfold neg. apply eqm_samerepr. auto with bit_ints.
Qed.

Theorem neg_zero: neg zero = zero.
Proof.
  unfold neg. rewrite unsigned_zero. auto.
Qed.

Theorem neg_involutive: forall x, neg (neg x) = x.
Proof.
  intros; unfold neg.
  apply eqm_repr_eq. eapply eqm_trans. apply eqm_neg.
  apply eqm_unsigned_repr_l. apply eqm_refl. apply eqm_refl2. lia.
Qed.

Theorem neg_add_distr: forall x y, neg(add x y) = add (neg x) (neg y).
Proof.
  intros; unfold neg, add. apply eqm_samerepr.
  apply eqm_trans with (- (unsigned x + unsigned y)).
  auto with bit_ints.
  replace (- (unsigned x + unsigned y))
     with ((- unsigned x) + (- unsigned y)).
  auto with bit_ints. lia.
Qed.

(** ** Properties of subtraction *)

Theorem sub_zero_l: forall x, sub x zero = x.
Proof.
  intros; unfold sub. rewrite unsigned_zero.
  replace (unsigned x - 0) with (unsigned x) by lia. apply repr_unsigned.
Qed.

Theorem sub_zero_r: forall x, sub zero x = neg x.
Proof.
  intros; unfold sub, neg. rewrite unsigned_zero. auto.
Qed.

Theorem sub_add_opp: forall x y, sub x y = add x (neg y).
Proof.
  intros; unfold sub, add, neg. apply eqm_samerepr.
  apply eqm_add; auto with bit_ints.
Qed.

Theorem sub_idem: forall x, sub x x = zero.
Proof.
  intros; unfold sub. unfold zero. decEq. lia.
Qed.

Theorem sub_add_l: forall x y z, sub (add x y) z = add (sub x z) y.
Proof.
  intros. repeat rewrite sub_add_opp.
  repeat rewrite add_assoc. decEq. apply add_commut.
Qed.

Theorem sub_add_r: forall x y z, sub x (add y z) = add (sub x z) (neg y).
Proof.
  intros. repeat rewrite sub_add_opp.
  rewrite neg_add_distr. rewrite add_permut. apply add_commut.
Qed.

Theorem sub_shifted:
  forall x y z,
  sub (add x z) (add y z) = sub x y.
Proof.
  intros. rewrite sub_add_opp. rewrite neg_add_distr.
  rewrite add_assoc.
  rewrite (add_commut (neg y) (neg z)).
  rewrite <- (add_assoc z). rewrite add_neg_zero.
  rewrite (add_commut zero). rewrite add_zero.
  symmetry. apply sub_add_opp.
Qed.

Theorem sub_signed:
  forall x y, sub x y = repr (signed x - signed y).
Proof.
  intros. unfold sub. apply eqm_samerepr.
  apply eqm_sub; apply eqm_sym; apply eqm_signed_unsigned.
Qed.

Theorem unsigned_sub_borrow:
  forall x y,
  unsigned (sub x y) = unsigned x - unsigned y + unsigned (sub_borrow x y zero) * modulus.
Proof.
  intros.
  unfold sub, sub_borrow. rewrite unsigned_zero. rewrite Z.sub_0_r.
  rewrite unsigned_repr_eq.
  generalize (unsigned_range x) (unsigned_range y). intros.
  destruct (zlt (unsigned x - unsigned y) 0).
  rewrite unsigned_one. apply Zmod_unique with (-1). lia. lia.
  rewrite unsigned_zero. apply Zmod_unique with 0. lia. lia.
Qed.

(** ** Properties of multiplication *)

Theorem mul_commut: forall x y, mul x y = mul y x.
Proof.
  intros; unfold mul. decEq. ring.
Qed.

Theorem mul_zero: forall x, mul x zero = zero.
Proof.
  intros; unfold mul. rewrite unsigned_zero.
  unfold zero. decEq. ring.
Qed.

Theorem mul_one: forall x, mul x one = x.
Proof.
  intros; unfold mul. rewrite unsigned_one.
  transitivity (repr (unsigned x)). decEq. ring.
  apply repr_unsigned.
Qed.

Theorem mul_mone: forall x, mul x mone = neg x.
Proof.
  intros; unfold mul, neg. rewrite unsigned_mone.
  apply eqm_samerepr.
  replace (-unsigned x) with (0 - unsigned x) by lia.
  replace (unsigned x * (modulus - 1)) with (unsigned x * modulus - unsigned x) by ring.
  apply eqm_sub. exists (unsigned x). lia. apply eqm_refl.
Qed.

Theorem mul_assoc: forall x y z, mul (mul x y) z = mul x (mul y z).
Proof.
  intros; unfold mul.
  set (x' := unsigned x).
  set (y' := unsigned y).
  set (z' := unsigned z).
  apply eqm_samerepr. apply eqm_trans with ((x' * y') * z').
  auto with bit_ints.
  rewrite <- Z.mul_assoc. auto with bit_ints.
Qed.

Theorem mul_add_distr_l:
  forall x y z, mul (add x y) z = add (mul x z) (mul y z).
Proof.
  intros; unfold mul, add.
  apply eqm_samerepr.
  set (x' := unsigned x).
  set (y' := unsigned y).
  set (z' := unsigned z).
  apply eqm_trans with ((x' + y') * z').
  auto with bit_ints.
  replace ((x' + y') * z') with (x' * z' + y' * z').
  auto with bit_ints.
  ring.
Qed.

Theorem mul_add_distr_r:
  forall x y z, mul x (add y z) = add (mul x y) (mul x z).
Proof.
  intros. rewrite mul_commut. rewrite mul_add_distr_l.
  decEq; apply mul_commut.
Qed.

Theorem neg_mul_distr_l:
  forall x y, neg(mul x y) = mul (neg x) y.
Proof.
  intros. unfold mul, neg.
  set (x' := unsigned x).  set (y' := unsigned y).
  apply eqm_samerepr. apply eqm_trans with (- (x' * y')).
  auto with bit_ints.
  replace (- (x' * y')) with ((-x') * y') by ring.
  auto with bit_ints.
Qed.

Theorem neg_mul_distr_r:
   forall x y, neg(mul x y) = mul x (neg y).
Proof.
  intros. rewrite (mul_commut x y). rewrite (mul_commut x (neg y)).
  apply neg_mul_distr_l.
Qed.

Theorem mul_signed:
  forall x y, mul x y = repr (signed x * signed y).
Proof.
  intros; unfold mul. apply eqm_samerepr.
  apply eqm_mult; apply eqm_sym; apply eqm_signed_unsigned.
Qed.

(** ** Properties of division and modulus *)

Lemma modu_divu_Euclid:
  forall x y, y <> zero -> x = add (mul (divu x y) y) (modu x y).
Proof.
  intros. unfold add, mul, divu, modu.
  transitivity (repr (unsigned x)). auto with bit_ints.
  apply eqm_samerepr.
  set (x' := unsigned x). set (y' := unsigned y).
  apply eqm_trans with ((x' / y') * y' + x' mod y').
  apply eqm_refl2. rewrite Z.mul_comm. apply Z_div_mod_eq_full.
  generalize (unsigned_range y); intro.
  assert (unsigned y <> 0). red; intro.
  elim H. rewrite <- (repr_unsigned y). unfold zero. congruence.
  unfold y'.
  auto with bit_ints.
Qed.

Theorem modu_divu:
  forall x y, y <> zero -> modu x y = sub x (mul (divu x y) y).
Proof.
  intros.
  assert (forall a b c, a = add b c -> c = sub a b).
  intros. subst a. rewrite sub_add_l. rewrite sub_idem.
  rewrite add_commut. rewrite add_zero. auto.
  apply H0. apply modu_divu_Euclid. auto.
Qed.

Lemma mods_divs_Euclid:
  forall x y, x = add (mul (divs x y) y) (mods x y).
Proof.
  intros. unfold add, mul, divs, mods.
  transitivity (repr (signed x)). auto with bit_ints.
  apply eqm_samerepr.
  set (x' := signed x). set (y' := signed y).
  apply eqm_trans with ((Z.quot x' y') * y' + Z.rem x' y').
  apply eqm_refl2. rewrite Z.mul_comm. apply Z.quot_rem'.
  apply eqm_add; auto with bit_ints.
  apply eqm_unsigned_repr_r. apply eqm_mult; auto with bit_ints.
  unfold y'. apply eqm_signed_unsigned.
Qed.

Theorem mods_divs:
  forall x y, mods x y = sub x (mul (divs x y) y).
Proof.
  intros.
  assert (forall a b c, a = add b c -> c = sub a b).
  intros. subst a. rewrite sub_add_l. rewrite sub_idem.
  rewrite add_commut. rewrite add_zero. auto.
  apply H. apply mods_divs_Euclid.
Qed.

Theorem divu_one:
  forall x, divu x one = x.
Proof.
  unfold divu; intros. rewrite unsigned_one. rewrite Zdiv_1_r. apply repr_unsigned.
Qed.

Theorem divs_one:
  forall x, zwordsize > 1 -> divs x one = x.
Proof.
  unfold divs; intros. rewrite signed_one. rewrite Z.quot_1_r. apply repr_signed. auto.
Qed.

Theorem modu_one:
  forall x, modu x one = zero.
Proof.
  intros. rewrite modu_divu. rewrite divu_one. rewrite mul_one. apply sub_idem.
  apply one_not_zero.
Qed.

Theorem divs_mone:
  forall x, divs x mone = neg x.
Proof.
  unfold divs, neg; intros.
  rewrite signed_mone.
  replace (Z.quot (signed x) (-1)) with (- (signed x)).
  apply eqm_samerepr. apply eqm_neg. apply eqm_signed_unsigned.
  set (x' := signed x).
  set (one := 1).
  change (-1) with (- one). rewrite Zquot_opp_r.
  assert (Z.quot x' one = x').
  symmetry. apply Zquot_unique_full with 0. red.
  change (Z.abs one) with 1.
  destruct (zle 0 x'). left. lia. right. lia.
  unfold one; ring.
  congruence.
Qed.

Theorem mods_mone:
  forall x, mods x mone = zero.
Proof.
  intros. rewrite mods_divs. rewrite divs_mone.
  rewrite <- neg_mul_distr_l. rewrite mul_mone. rewrite neg_involutive. apply sub_idem.
Qed.

Theorem divmodu2_divu_modu:
  forall n d,
  d <> zero -> divmodu2 zero n d = Some (divu n d, modu n d).
Proof.
  unfold divmodu2, divu, modu; intros.
  rewrite dec_eq_false by auto.
  set (N := unsigned zero * modulus + unsigned n).
  assert (E1: unsigned n = N) by (unfold N; rewrite unsigned_zero; ring). rewrite ! E1.
  set (D := unsigned d).
  set (Q := N / D); set (R := N mod D).
  assert (E2: Z.div_eucl N D = (Q, R)).
  { unfold Q, R, Z.div, Z.modulo. destruct (Z.div_eucl N D); auto. }
  rewrite E2. rewrite zle_true. auto.
  assert (unsigned d <> 0).
  { red; intros. elim H. rewrite <- (repr_unsigned d). rewrite H0; auto. }
  assert (0 < D).
  { unfold D. generalize (unsigned_range d); intros. lia. }
  assert (0 <= Q <= max_unsigned).
  { unfold Q. apply Zdiv_interval_2.
    rewrite <- E1; apply unsigned_range_2.
    lia. unfold max_unsigned; generalize modulus_pos; lia. lia. }
  lia.
Qed.

Lemma unsigned_signed:
  forall n, unsigned n = if lt n zero then signed n + modulus else signed n.
Proof.
  intros. unfold lt. rewrite signed_zero. unfold signed.
  generalize (unsigned_range n). rewrite half_modulus_modulus. intros.
  destruct (zlt (unsigned n) half_modulus).
- rewrite zlt_false by lia. auto.
- rewrite zlt_true by lia. ring.
Qed.

Theorem divmods2_divs_mods:
  forall n d,
  d <> zero -> n <> repr min_signed \/ d <> mone ->
  divmods2 (if lt n zero then mone else zero) n d = Some (divs n d, mods n d).
Proof.
  unfold divmods2, divs, mods; intros.
  rewrite dec_eq_false by auto.
  set (N := signed (if lt n zero then mone else zero) * modulus + unsigned n).
  set (D := signed d).
  assert (D <> 0).
  { unfold D; red; intros. elim H. rewrite <- (repr_signed d). rewrite H1; auto. }
  assert (N = signed n).
  { unfold N. rewrite unsigned_signed. destruct (lt n zero).
    rewrite signed_mone. ring.
    rewrite signed_zero. ring. }
  set (Q := Z.quot N D); set (R := Z.rem N D).
  assert (E2: Z.quotrem N D = (Q, R)).
  { unfold Q, R, Z.quot, Z.rem. destruct (Z.quotrem N D); auto. }
  rewrite E2.
  assert (min_signed <= N <= max_signed) by (rewrite H2; apply signed_range).
  assert (min_signed <= Q <= max_signed).
  { unfold Q. destruct (zeq D 1); [ | destruct (zeq D (-1))].
  - (* D = 1 *)
    rewrite e. rewrite Z.quot_1_r; auto.
  - (* D = -1 *)
    rewrite e. change (-1) with (Z.opp 1). rewrite Z.quot_opp_r by lia.
    rewrite Z.quot_1_r.
    assert (N <> min_signed).
    { red; intros; destruct H0.
    + elim H0. rewrite <- (repr_signed n). rewrite <- H2. rewrite H4. auto.
    + elim H0. rewrite <- (repr_signed d). unfold D in e; rewrite e; auto. }
    unfold min_signed, max_signed in *. lia.
  - (* |D| > 1 *)
    assert (Z.abs (Z.quot N D) < half_modulus).
    { rewrite <- Z.quot_abs by lia. apply Zquot_lt_upper_bound.
      lia. lia.
      apply Z.le_lt_trans with (half_modulus * 1).
      rewrite Z.mul_1_r. unfold min_signed, max_signed in H3; lia.
      apply Zmult_lt_compat_l. generalize half_modulus_pos; lia. lia. }
    rewrite Z.abs_lt in H4.
    unfold min_signed, max_signed; lia.
  }
  unfold proj_sumbool; rewrite ! zle_true by lia; simpl.
  unfold Q, R; rewrite H2; auto.
Qed.

(** ** Bit-level properties *)

(** ** Properties of bit-level operations over [Z] *)

Remark Ztestbit_0: forall n, Z.testbit 0 n = false.
Proof Z.testbit_0_l.

Remark Ztestbit_1: forall n, Z.testbit 1 n = zeq n 0.
Proof.
  intros. destruct n; simpl; auto.
Qed.

Remark Ztestbit_m1: forall n, 0 <= n -> Z.testbit (-1) n = true.
Proof.
  intros. destruct n; simpl; auto.
Qed.

Remark Zshiftin_spec:
  forall b x, Zshiftin b x = 2 * x + (if b then 1 else 0).
Proof.
  unfold Zshiftin; intros. destruct b.
  - rewrite Z.succ_double_spec. lia.
  - rewrite Z.double_spec. lia.
Qed.

Remark Zshiftin_inj:
  forall b1 x1 b2 x2,
  Zshiftin b1 x1 = Zshiftin b2 x2 -> b1 = b2 /\ x1 = x2.
Proof.
  intros. rewrite !Zshiftin_spec in H.
  destruct b1; destruct b2.
  split; [auto|lia].
  lia.
  lia.
  split; [auto|lia].
Qed.

Remark Zdecomp:
  forall x, x = Zshiftin (Z.odd x) (Z.div2 x).
Proof.
  intros. destruct x; simpl.
  - auto.
  - destruct p; auto.
  - destruct p; auto. simpl. rewrite Pos.pred_double_succ. auto.
Qed.

Remark Ztestbit_shiftin:
  forall b x n,
  0 <= n ->
  Z.testbit (Zshiftin b x) n = if zeq n 0 then b else Z.testbit x (Z.pred n).
Proof.
  intros. rewrite Zshiftin_spec. destruct (zeq n 0).
  - subst n. destruct b.
    + apply Z.testbit_odd_0.
    + rewrite Z.add_0_r. apply Z.testbit_even_0.
  - assert (0 <= Z.pred n) by lia.
    set (n' := Z.pred n) in *.
    replace n with (Z.succ n') by (unfold n'; lia).
    destruct b.
    + apply Z.testbit_odd_succ; auto.
    + rewrite Z.add_0_r. apply Z.testbit_even_succ; auto.
Qed.

Remark Ztestbit_shiftin_base:
  forall b x, Z.testbit (Zshiftin b x) 0 = b.
Proof.
  intros. rewrite Ztestbit_shiftin. apply zeq_true. lia.
Qed.

Remark Ztestbit_shiftin_succ:
  forall b x n, 0 <= n -> Z.testbit (Zshiftin b x) (Z.succ n) = Z.testbit x n.
Proof.
  intros. rewrite Ztestbit_shiftin. rewrite zeq_false. rewrite Z.pred_succ. auto.
  lia. lia.
Qed.

Remark Ztestbit_eq:
  forall n x, 0 <= n ->
  Z.testbit x n = if zeq n 0 then Z.odd x else Z.testbit (Z.div2 x) (Z.pred n).
Proof.
  intros. rewrite (Zdecomp x) at 1. apply Ztestbit_shiftin; auto.
Qed.

Remark Ztestbit_base:
  forall x, Z.testbit x 0 = Z.odd x.
Proof.
  intros. rewrite Ztestbit_eq. apply zeq_true. lia.
Qed.

Remark Ztestbit_succ:
  forall n x, 0 <= n -> Z.testbit x (Z.succ n) = Z.testbit (Z.div2 x) n.
Proof.
  intros. rewrite Ztestbit_eq. rewrite zeq_false. rewrite Z.pred_succ. auto.
  lia. lia.
Qed.

Lemma eqmod_same_bits:
  forall n x y,
  (forall i, 0 <= i < Z.of_nat n -> Z.testbit x i = Z.testbit y i) ->
  eqmod (two_power_nat n) x y.
Proof.
  induction n; intros.
  - change (two_power_nat 0) with 1. exists (x-y); ring.
  - rewrite two_power_nat_S.
    assert (eqmod (two_power_nat n) (Z.div2 x) (Z.div2 y)).
      apply IHn. intros. rewrite <- !Ztestbit_succ. apply H. rewrite Nat2Z.inj_succ; lia.
      lia. lia.
  destruct H0 as [k EQ].
  exists k. rewrite (Zdecomp x). rewrite (Zdecomp y).
  replace (Z.odd y) with (Z.odd x).
  rewrite EQ. rewrite !Zshiftin_spec. ring.
  exploit (H 0). rewrite Nat2Z.inj_succ; lia.
  rewrite !Ztestbit_base. auto.
Qed.

Lemma eqm_same_bits:
  forall x y,
  (forall i, 0 <= i < zwordsize -> Z.testbit x i = Z.testbit y i) ->
  eqm x y.
Proof.
  unfold eqm.
  setoid_rewrite two_power_pos_nat.
  intros x y H.
  eapply eqmod_same_bits.
  unfold zwordsize in *.
  rewrite positive_nat_Z.
  auto.
Qed.

Lemma same_bits_eqmod:
  forall n x y i,
  eqmod (two_power_nat n) x y -> 0 <= i < Z.of_nat n ->
  Z.testbit x i = Z.testbit y i.
Proof.
  induction n; intros.
  - simpl in H0. lia.
  - rewrite Nat2Z.inj_succ in H0. rewrite two_power_nat_S in H.
    rewrite !(Ztestbit_eq i); intuition.
    destruct H as [k EQ].
    assert (EQ': Zshiftin (Z.odd x) (Z.div2 x) =
                 Zshiftin (Z.odd y) (k * two_power_nat n + Z.div2 y)).
    {
      rewrite (Zdecomp x) in EQ. rewrite (Zdecomp y) in EQ.
      rewrite EQ. rewrite !Zshiftin_spec. ring.
    }
    exploit Zshiftin_inj; eauto. intros [A B].
    destruct (zeq i 0).
    + auto.
    + apply IHn. exists k; auto. lia.
Qed.

Lemma same_bits_eqm:
  forall x y i,
  eqm x y ->
  0 <= i < zwordsize ->
  Z.testbit x i = Z.testbit y i.
Proof.
  unfold eqm.
  setoid_rewrite two_power_pos_nat.
  intros x y i H1 H2.
  eapply same_bits_eqmod; eauto.
  unfold zwordsize in H2.
  rewrite positive_nat_Z; auto.
Qed.

Remark two_power_nat_infinity:
  forall x, 0 <= x -> exists n, x < two_power_nat n.
Proof.
  intros x0 POS0; pattern x0; apply natlike_ind; auto.
  exists O. compute; auto.
  intros. destruct H0 as [n LT]. exists (S n). rewrite two_power_nat_S.
  generalize (two_power_nat_pos n). lia.
Qed.

Lemma equal_same_bits:
  forall x y,
  (forall i, 0 <= i -> Z.testbit x i = Z.testbit y i) ->
  x = y.
Proof.
  intros.
  set (z := if zlt x y then y - x else x - y).
  assert (0 <= z).
    unfold z; destruct (zlt x y); lia.
  exploit (two_power_nat_infinity z); auto. intros [n LT].
  assert (eqmod (two_power_nat n) x y).
    apply eqmod_same_bits. intros. apply H. tauto.
  assert (eqmod (two_power_nat n) z 0).
    unfold z. destruct (zlt x y).
    replace 0 with (y - y) by lia. apply eqmod_sub. apply eqmod_refl. auto.
    replace 0 with (x - x) by lia. apply eqmod_sub. apply eqmod_refl. apply eqmod_sym; auto.
  assert (z = 0).
    apply eqmod_small_eq with (two_power_nat n). auto. lia. generalize (two_power_nat_pos n); lia.
  unfold z in H3. destruct (zlt x y); lia.
Qed.

Lemma Z_one_complement:
  forall i, 0 <= i ->
  forall x, Z.testbit (-x-1) i = negb (Z.testbit x i).
Proof.
  intros i0 POS0. pattern i0. apply Zlt_0_ind; auto.
  intros i IND POS x.
  rewrite (Zdecomp x). set (y := Z.div2 x).
  replace (- Zshiftin (Z.odd x) y - 1)
     with (Zshiftin (negb (Z.odd x)) (- y - 1)).
  rewrite !Ztestbit_shiftin; auto.
  destruct (zeq i 0). auto. apply IND. lia.
  rewrite !Zshiftin_spec. destruct (Z.odd x); simpl negb; ring.
Qed.

Lemma Ztestbit_above:
  forall n x i,
  0 <= x < two_power_nat n ->
  i >= Z.of_nat n ->
  Z.testbit x i = false.
Proof.
  induction n; intros.
  - change (two_power_nat 0) with 1 in H.
    replace x with 0 by lia.
    apply Z.testbit_0_l.
  - rewrite Nat2Z.inj_succ in H0. rewrite Ztestbit_eq. rewrite zeq_false.
    apply IHn. rewrite two_power_nat_S in H. rewrite (Zdecomp x) in H.
    rewrite Zshiftin_spec in H. destruct (Z.odd x); lia.
    lia. lia. lia.
Qed.

Lemma Ztestbit_above_neg:
  forall n x i,
  -two_power_nat n <= x < 0 ->
  i >= Z.of_nat n ->
  Z.testbit x i = true.
Proof.
  intros. set (y := -x-1).
  assert (Z.testbit y i = false).
    apply Ztestbit_above with n.
    unfold y; lia. auto.
  unfold y in H1. rewrite Z_one_complement in H1.
  change true with (negb false). rewrite <- H1. rewrite negb_involutive; auto.
  lia.
Qed.

Lemma Zsign_bit:
  forall n x,
  0 <= x < two_power_nat (S n) ->
  Z.testbit x (Z.of_nat n) = if zlt x (two_power_nat n) then false else true.
Proof.
  induction n; intros.
  - change (two_power_nat 1) with 2 in H.
    assert (x = 0 \/ x = 1) by lia.
    destruct H0; subst x; reflexivity.
  - rewrite Nat2Z.inj_succ. rewrite Ztestbit_eq. rewrite zeq_false. rewrite Z.pred_succ.
    rewrite IHn. rewrite two_power_nat_S.
    destruct (zlt (Z.div2 x) (two_power_nat n)); rewrite (Zdecomp x); rewrite Zshiftin_spec.
    rewrite zlt_true. auto. destruct (Z.odd x); lia.
    rewrite zlt_false. auto. destruct (Z.odd x); lia.
    rewrite (Zdecomp x) in H; rewrite Zshiftin_spec in H.
    rewrite two_power_nat_S in H. destruct (Z.odd x); lia.
    lia. lia.
Qed.

Lemma Zshiftin_ind:
  forall (P: Z -> Prop),
  P 0 ->
  (forall b x, 0 <= x -> P x -> P (Zshiftin b x)) ->
  forall x, 0 <= x -> P x.
Proof.
  intros. destruct x.
  - auto.
  - induction p.
    + change (P (Zshiftin true (Z.pos p))). auto.
    + change (P (Zshiftin false (Z.pos p))). auto.
    + change (P (Zshiftin true 0)). apply H0. lia. auto.
  - compute in H1. intuition congruence.
Qed.

Lemma Zshiftin_pos_ind:
  forall (P: Z -> Prop),
  P 1 ->
  (forall b x, 0 < x -> P x -> P (Zshiftin b x)) ->
  forall x, 0 < x -> P x.
Proof.
  intros. destruct x; simpl in H1; try discriminate.
  induction p.
    + change (P (Zshiftin true (Z.pos p))). auto.
    + change (P (Zshiftin false (Z.pos p))). auto.
    + auto.
Qed.

Lemma Ztestbit_le:
  forall x y,
  0 <= y ->
  (forall i, 0 <= i -> Z.testbit x i = true -> Z.testbit y i = true) ->
  x <= y.
Proof.
  intros x y0 POS0; revert x; pattern y0; apply Zshiftin_ind; auto; intros.
  - replace x with 0. lia. apply equal_same_bits; intros.
    rewrite Ztestbit_0. destruct (Z.testbit x i) as [] eqn:E; auto.
    exploit H; eauto. rewrite Ztestbit_0. auto.
  - assert (Z.div2 x0 <= x).
    { apply H0. intros. exploit (H1 (Z.succ i)).
        lia. rewrite Ztestbit_succ; auto. rewrite Ztestbit_shiftin_succ; auto.
    }
    rewrite (Zdecomp x0). rewrite !Zshiftin_spec.
    destruct (Z.odd x0) as [] eqn:E1; destruct b as [] eqn:E2; try lia.
    exploit (H1 0). lia. rewrite Ztestbit_base; auto.
    rewrite Ztestbit_shiftin_base. congruence.
Qed.

(** ** Bit-level reasoning over type [int] *)

Definition testbit (x: bit_int) (i: Z) : bool := Z.testbit (unsigned x) i.

Lemma testbit_repr:
  forall x i,
  0 <= i < zwordsize ->
  testbit (repr x) i = Z.testbit x i.
Proof.
  intros. unfold testbit. apply same_bits_eqm; auto with bit_ints.
Qed.

Lemma same_bits_eq:
  forall x y,
  (forall i, 0 <= i < zwordsize -> testbit x i = testbit y i) ->
  x = y.
Proof.
  intros. rewrite <- (repr_unsigned x). rewrite <- (repr_unsigned y).
  apply eqm_samerepr. apply eqm_same_bits. auto.
Qed.

Lemma bits_above:
  forall x i, i >= zwordsize -> testbit x i = false.
Proof.
  intros.
  apply Ztestbit_above with natwordsize; auto.
  unfold natwordsize.
  rewrite <- two_power_pos_nat.
  apply unsigned_range.
  unfold natwordsize.
  rewrite positive_nat_Z; auto.
Qed.

Lemma bits_zero:
  forall i, testbit zero i = false.
Proof.
  intros. unfold testbit. rewrite unsigned_zero. apply Ztestbit_0.
Qed.

Remark bits_one: forall n, testbit one n = zeq n 0.
Proof.
  unfold testbit; intros. rewrite unsigned_one. apply Ztestbit_1.
Qed.

Lemma bits_mone:
  forall i, 0 <= i < zwordsize -> testbit mone i = true.
Proof.
  intros. unfold mone. rewrite testbit_repr; auto. apply Ztestbit_m1. lia.
Qed.

Hint Rewrite bits_zero bits_mone : bit_ints.

Ltac bit_solve :=
  intros; apply same_bits_eq; intros; autorewrite with bit_ints; auto with bool.

Lemma sign_bit_of_unsigned:
  forall x, testbit x (zwordsize - 1) = if zlt (unsigned x) half_modulus then false else true.
Proof.
  intros. unfold testbit.
  set (ws1 := Init.Nat.pred natwordsize).
  assert (zwordsize - 1 = Z.of_nat ws1).
  unfold zwordsize, ws1, natwordsize.
  lia.
  assert (half_modulus = two_power_nat ws1).
    rewrite two_power_nat_two_p. rewrite <- H. apply half_modulus_power.
  rewrite H; rewrite H0.
  apply Zsign_bit. rewrite two_power_nat_S. rewrite <- H0.
  rewrite <- half_modulus_modulus. apply unsigned_range.
Qed.

Lemma bits_signed:
  forall x i, 0 <= i ->
  Z.testbit (signed x) i = testbit x (if zlt i zwordsize then i else zwordsize - 1).
Proof.
  intros.
  destruct (zlt i zwordsize).
  - apply same_bits_eqm. apply eqm_signed_unsigned. lia.
  - unfold signed. rewrite sign_bit_of_unsigned. destruct (zlt (unsigned x) half_modulus).
    + apply Ztestbit_above with natwordsize. unfold half_modulus in *.
      unfold modulus in l.
      rewrite two_power_pos_nat in l.
      unfold natwordsize.
      rewrite <- two_power_pos_nat.
      apply unsigned_range.
      unfold natwordsize.
      rewrite positive_nat_Z; auto.
    + apply Ztestbit_above_neg with natwordsize.
      fold modulus. generalize (unsigned_range x).
      intros H0.
      unfold modulus, half_modulus in *.
      setoid_rewrite <- two_power_pos_nat.
      lia.
      setoid_rewrite positive_nat_Z; auto.
Qed.

Lemma bits_le:
  forall x y,
  (forall i, 0 <= i < zwordsize -> testbit x i = true -> testbit y i = true) ->
  unsigned x <= unsigned y.
Proof.
  intros. apply Ztestbit_le. generalize (unsigned_range y); lia.
  intros. fold (testbit y i). destruct (zlt i zwordsize).
  apply H. lia. auto.
  fold (testbit x i) in H1. rewrite bits_above in H1; auto. congruence.
Qed.

(** ** Properties of bitwise and, or, xor *)

Lemma bits_and:
  forall x y i, 0 <= i < zwordsize ->
  testbit (and x y) i = testbit x i && testbit y i.
Proof.
  intros. unfold and. rewrite testbit_repr; auto. rewrite Z.land_spec; intuition.
Qed.

Lemma bits_or:
  forall x y i, 0 <= i < zwordsize ->
  testbit (or x y) i = testbit x i || testbit y i.
Proof.
  intros. unfold or. rewrite testbit_repr; auto. rewrite Z.lor_spec; intuition.
Qed.

Lemma bits_xor:
  forall x y i, 0 <= i < zwordsize ->
  testbit (xor x y) i = xorb (testbit x i) (testbit y i).
Proof.
  intros. unfold xor. rewrite testbit_repr; auto. rewrite Z.lxor_spec; intuition.
Qed.

Lemma bits_not:
  forall x i, 0 <= i < zwordsize ->
  testbit (not x) i = negb (testbit x i).
Proof.
  intros. unfold not. rewrite bits_xor; auto. rewrite bits_mone; auto.
Qed.

Hint Rewrite bits_and bits_or bits_xor bits_not: bit_ints.

Theorem and_commut: forall x y, and x y = and y x.
Proof.
  bit_solve.
Qed.

Theorem and_assoc: forall x y z, and (and x y) z = and x (and y z).
Proof.
  bit_solve.
Qed.

Theorem and_zero: forall x, and x zero = zero.
Proof.
  bit_solve.
Qed.

Corollary and_zero_l: forall x, and zero x = zero.
Proof.
  intros. rewrite and_commut. apply and_zero.
Qed.

Theorem and_mone: forall x, and x mone = x.
Proof.
  bit_solve.
Qed.

Corollary and_mone_l: forall x, and mone x = x.
Proof.
  intros. rewrite and_commut. apply and_mone.
Qed.

Theorem and_idem: forall x, and x x = x.
Proof.
  bit_solve. destruct (testbit x i); auto.
Qed.

Theorem or_commut: forall x y, or x y = or y x.
Proof.
  bit_solve.
Qed.

Theorem or_assoc: forall x y z, or (or x y) z = or x (or y z).
Proof.
  bit_solve.
Qed.

Theorem or_zero: forall x, or x zero = x.
Proof.
  bit_solve.
Qed.

Corollary or_zero_l: forall x, or zero x = x.
Proof.
  intros. rewrite or_commut. apply or_zero.
Qed.

Theorem or_mone: forall x, or x mone = mone.
Proof.
  bit_solve.
Qed.

Theorem or_idem: forall x, or x x = x.
Proof.
  bit_solve. destruct (testbit x i); auto.
Qed.

Theorem and_or_distrib:
  forall x y z,
  and x (or y z) = or (and x y) (and x z).
Proof.
  bit_solve. apply demorgan1.
Qed.

Corollary and_or_distrib_l:
  forall x y z,
  and (or x y) z = or (and x z) (and y z).
Proof.
  intros. rewrite (and_commut (or x y)). rewrite and_or_distrib. f_equal; apply and_commut.
Qed.

Theorem or_and_distrib:
  forall x y z,
  or x (and y z) = and (or x y) (or x z).
Proof.
  bit_solve. apply orb_andb_distrib_r.
Qed.

Corollary or_and_distrib_l:
  forall x y z,
  or (and x y) z = and (or x z) (or y z).
Proof.
  intros. rewrite (or_commut (and x y)). rewrite or_and_distrib. f_equal; apply or_commut.
Qed.

Theorem and_or_absorb: forall x y, and x (or x y) = x.
Proof.
  bit_solve.
  assert (forall a b, a && (a || b) = a) by destr_bool.
  auto.
Qed.

Theorem or_and_absorb: forall x y, or x (and x y) = x.
Proof.
  bit_solve.
  assert (forall a b, a || (a && b) = a) by destr_bool.
  auto.
Qed.

Theorem xor_commut: forall x y, xor x y = xor y x.
Proof.
  bit_solve. apply xorb_comm.
Qed.

Theorem xor_assoc: forall x y z, xor (xor x y) z = xor x (xor y z).
Proof.
  bit_solve. apply xorb_assoc.
Qed.

Theorem xor_zero: forall x, xor x zero = x.
Proof.
  bit_solve. apply xorb_false.
Qed.

Corollary xor_zero_l: forall x, xor zero x = x.
Proof.
  intros. rewrite xor_commut. apply xor_zero.
Qed.

Theorem xor_idem: forall x, xor x x = zero.
Proof.
  bit_solve. apply xorb_nilpotent.
Qed.

Theorem xor_zero_one: xor zero one = one.
Proof. rewrite xor_commut. apply xor_zero. Qed.

Theorem xor_one_one: xor one one = zero.
Proof. apply xor_idem. Qed.

Theorem xor_zero_equal: forall x y, xor x y = zero -> x = y.
Proof.
  intros. apply same_bits_eq; intros.
  assert (xorb (testbit x i) (testbit y i) = false).
    rewrite <- bits_xor; auto. rewrite H. apply bits_zero.
  destruct (testbit x i); destruct (testbit y i); reflexivity || discriminate.
Qed.

Theorem xor_is_zero: forall x y, eq (xor x y) zero = eq x y.
Proof.
  intros. predSpec eq eq_spec (xor x y) zero.
- apply xor_zero_equal in H. subst y. rewrite eq_true; auto.
- predSpec eq eq_spec x y.
+ elim H; subst y; apply xor_idem.
+ auto.
Qed.

Theorem and_xor_distrib:
  forall x y z,
  and x (xor y z) = xor (and x y) (and x z).
Proof.
  bit_solve.
  assert (forall a b c, a && (xorb b c) = xorb (a && b) (a && c)) by destr_bool.
  auto.
Qed.

Theorem and_le:
  forall x y, unsigned (and x y) <= unsigned x.
Proof.
  intros. apply bits_le; intros.
  rewrite bits_and in H0; auto. rewrite andb_true_iff in H0. tauto.
Qed.

Theorem or_le:
  forall x y, unsigned x <= unsigned (or x y).
Proof.
  intros. apply bits_le; intros.
  rewrite bits_or; auto. rewrite H0; auto.
Qed.

(** Properties of bitwise complement.*)

Theorem not_involutive:
  forall (x: bit_int), not (not x) = x.
Proof.
  intros. unfold not. rewrite xor_assoc. rewrite xor_idem. apply xor_zero.
Qed.

Theorem not_zero:
  not zero = mone.
Proof.
  unfold not. rewrite xor_commut. apply xor_zero.
Qed.

Theorem not_mone:
  not mone = zero.
Proof.
  rewrite <- (not_involutive zero). symmetry. decEq. apply not_zero.
Qed.

Theorem not_or_and_not:
  forall x y, not (or x y) = and (not x) (not y).
Proof.
  bit_solve. apply negb_orb.
Qed.

Theorem not_and_or_not:
  forall x y, not (and x y) = or (not x) (not y).
Proof.
  bit_solve. apply negb_andb.
Qed.

Theorem and_not_self:
  forall x, and x (not x) = zero.
Proof.
  bit_solve.
Qed.

Theorem or_not_self:
  forall x, or x (not x) = mone.
Proof.
  bit_solve.
Qed.

Theorem xor_not_self:
  forall x, xor x (not x) = mone.
Proof.
  bit_solve. destruct (testbit x i); auto.
Qed.

Lemma unsigned_not:
  forall x, unsigned (not x) = max_unsigned - unsigned x.
Proof.
  intros. transitivity (unsigned (repr(-unsigned x - 1))).
  f_equal. bit_solve. rewrite testbit_repr; auto. symmetry. apply Z_one_complement. lia.
  rewrite unsigned_repr_eq. apply Zmod_unique with (-1).
  unfold max_unsigned. lia.
  generalize (unsigned_range x). unfold max_unsigned. lia.
Qed.

Theorem not_neg:
  forall x, not x = add (neg x) mone.
Proof.
  bit_solve.
  rewrite <- (repr_unsigned x) at 1. unfold add.
  rewrite !testbit_repr; auto.
  transitivity (Z.testbit (-unsigned x - 1) i).
  symmetry. apply Z_one_complement. lia.
  apply same_bits_eqm; auto.
  replace (-unsigned x - 1) with (-unsigned x + (-1)) by lia.
  apply eqm_add.
  unfold neg. apply eqm_unsigned_repr.
  rewrite unsigned_mone. exists (-1). ring.
Qed.

Theorem neg_not:
  forall x, neg x = add (not x) one.
Proof.
  intros. rewrite not_neg. rewrite add_assoc.
  replace (add mone one) with zero. rewrite add_zero. auto.
  apply eqm_samerepr. rewrite unsigned_mone. rewrite unsigned_one.
  exists (-1). ring.
Qed.

Theorem sub_add_not:
  forall x y, sub x y = add (add x (not y)) one.
Proof.
  intros. rewrite sub_add_opp. rewrite neg_not.
  rewrite ! add_assoc. auto.
Qed.

Theorem sub_add_not_3:
  forall x y b,
  b = zero \/ b = one ->
  sub (sub x y) b = add (add x (not y)) (xor b one).
Proof.
  intros. rewrite ! sub_add_not. rewrite ! add_assoc. f_equal. f_equal.
  rewrite <- neg_not. rewrite <- sub_add_opp. destruct H; subst b.
  rewrite xor_zero_l. rewrite sub_zero_l. auto.
  rewrite xor_idem. rewrite sub_idem. auto.
Qed.

Theorem sub_borrow_add_carry:
  forall x y b,
  b = zero \/ b = one ->
  sub_borrow x y b = xor (add_carry x (not y) (xor b one)) one.
Proof.
  intros. unfold sub_borrow, add_carry. rewrite unsigned_not.
  replace (unsigned (xor b one)) with (1 - unsigned b).
  destruct (zlt (unsigned x - unsigned y - unsigned b)).
  rewrite zlt_true. rewrite xor_zero_l; auto.
  unfold max_unsigned; lia.
  rewrite zlt_false. rewrite xor_idem; auto.
  unfold max_unsigned; lia.
  destruct H; subst b.
  rewrite xor_zero_l. rewrite unsigned_one, unsigned_zero; auto.
  rewrite xor_idem. rewrite unsigned_one, unsigned_zero; auto.
Qed.

(** Connections between [add] and bitwise logical operations. *)

Lemma Z_add_is_or:
  forall i, 0 <= i ->
  forall x y,
  (forall j, 0 <= j <= i -> Z.testbit x j && Z.testbit y j = false) ->
  Z.testbit (x + y) i = Z.testbit x i || Z.testbit y i.
Proof.
  intros i0 POS0. pattern i0. apply Zlt_0_ind; auto.
  intros i IND POS x y EXCL.
  rewrite (Zdecomp x) in *. rewrite (Zdecomp y) in *.
  transitivity (Z.testbit (Zshiftin (Z.odd x || Z.odd y) (Z.div2 x + Z.div2 y)) i).
  - f_equal. rewrite !Zshiftin_spec.
    exploit (EXCL 0). lia. rewrite !Ztestbit_shiftin_base. intros.
Opaque Z.mul.
    destruct (Z.odd x); destruct (Z.odd y); simpl in *; discriminate || ring.
  - rewrite !Ztestbit_shiftin; auto.
    destruct (zeq i 0).
    + auto.
    + apply IND. lia. intros.
      exploit (EXCL (Z.succ j)). lia.
      rewrite !Ztestbit_shiftin_succ. auto.
      lia. lia.
Qed.

Theorem add_is_or:
  forall x y,
  and x y = zero ->
  add x y = or x y.
Proof.
  bit_solve. unfold add. rewrite testbit_repr; auto.
  apply Z_add_is_or. lia.
  intros.
  assert (testbit (and x y) j = testbit zero j) by congruence.
  autorewrite with bit_ints in H2. assumption. lia.
Qed.

Theorem xor_is_or:
  forall x y, and x y = zero -> xor x y = or x y.
Proof.
  bit_solve.
  assert (testbit (and x y) i = testbit zero i) by congruence.
  autorewrite with bit_ints in H1; auto.
  destruct (testbit x i); destruct (testbit y i); simpl in *; congruence.
Qed.

Theorem add_is_xor:
  forall x y,
  and x y = zero ->
  add x y = xor x y.
Proof.
  intros. rewrite xor_is_or; auto. apply add_is_or; auto.
Qed.

Theorem add_and:
  forall x y z,
  and y z = zero ->
  add (and x y) (and x z) = and x (or y z).
Proof.
  intros. rewrite add_is_or.
  rewrite and_or_distrib; auto.
  rewrite (and_commut x y).
  rewrite and_assoc.
  repeat rewrite <- (and_assoc x).
  rewrite (and_commut (and x x)).
  rewrite <- and_assoc.
  rewrite H. rewrite and_commut. apply and_zero.
Qed.

(** ** Properties of shifts *)

Lemma bits_shl:
  forall x y i,
  0 <= i < zwordsize ->
  testbit (shl x y) i =
  if zlt i (unsigned y) then false else testbit x (i - unsigned y).
Proof.
  intros. unfold shl. rewrite testbit_repr; auto.
  destruct (zlt i (unsigned y)).
  apply Z.shiftl_spec_low. auto.
  apply Z.shiftl_spec_high. lia. lia.
Qed.

Lemma bits_shru:
  forall x y i,
  0 <= i < zwordsize ->
  testbit (shru x y) i =
  if zlt (i + unsigned y) zwordsize then testbit x (i + unsigned y) else false.
Proof.
  intros. unfold shru. rewrite testbit_repr; auto.
  rewrite Z.shiftr_spec. fold (testbit x (i + unsigned y)).
  destruct (zlt (i + unsigned y) zwordsize).
  auto.
  apply bits_above; auto.
  lia.
Qed.

Lemma bits_shr:
  forall x y i,
  0 <= i < zwordsize ->
  testbit (shr x y) i =
  testbit x (if zlt (i + unsigned y) zwordsize then i + unsigned y else zwordsize - 1).
Proof.
  intros. unfold shr. rewrite testbit_repr; auto.
  rewrite Z.shiftr_spec. apply bits_signed.
  generalize (unsigned_range y); lia.
  lia.
Qed.

Hint Rewrite bits_shl bits_shru bits_shr: bit_ints.

Theorem shl_zero: forall x, shl x zero = x.
Proof.
  bit_solve. rewrite unsigned_zero. rewrite zlt_false. f_equal; lia. lia.
Qed.

Lemma bitwise_binop_shl:
  forall f f' x y n,
  (forall x y i, 0 <= i < zwordsize -> testbit (f x y) i = f' (testbit x i) (testbit y i)) ->
  f' false false = false ->
  f (shl x n) (shl y n) = shl (f x y) n.
Proof.
  intros. apply same_bits_eq; intros.
  rewrite H; auto. rewrite !bits_shl; auto.
  destruct (zlt i (unsigned n)); auto.
  rewrite H; auto. generalize (unsigned_range n); lia.
Qed.

Theorem and_shl:
  forall x y n,
  and (shl x n) (shl y n) = shl (and x y) n.
Proof.
  intros. apply bitwise_binop_shl with andb. exact bits_and. auto.
Qed.

Theorem or_shl:
  forall x y n,
  or (shl x n) (shl y n) = shl (or x y) n.
Proof.
  intros. apply bitwise_binop_shl with orb. exact bits_or. auto.
Qed.

Theorem xor_shl:
  forall x y n,
  xor (shl x n) (shl y n) = shl (xor x y) n.
Proof.
  intros. apply bitwise_binop_shl with xorb. exact bits_xor. auto.
Qed.

Lemma ltu_inv:
  forall x y, ltu x y = true -> 0 <= unsigned x < unsigned y.
Proof.
  unfold ltu; intros. destruct (zlt (unsigned x) (unsigned y)).
  split; auto. generalize (unsigned_range x); lia.
  discriminate.
Qed.

Lemma ltu_iwordsize_inv:
  forall x, ltu x iwordsize = true -> 0 <= unsigned x < zwordsize.
Proof.
  intros. generalize (ltu_inv _ _ H). rewrite unsigned_repr_wordsize. auto.
Qed.

Theorem shl_shl:
  forall x y z,
  ltu y iwordsize = true ->
  ltu z iwordsize = true ->
  ltu (add y z) iwordsize = true ->
  shl (shl x y) z = shl x (add y z).
Proof.
  intros.
  generalize (ltu_iwordsize_inv _ H) (ltu_iwordsize_inv _ H0); intros.
  assert (unsigned (add y z) = unsigned y + unsigned z).
    unfold add. apply unsigned_repr.
    generalize two_wordsize_max_unsigned; lia.
  apply same_bits_eq; intros.
  rewrite bits_shl; auto.
  destruct (zlt i (unsigned z)).
  - rewrite bits_shl; auto. rewrite zlt_true. auto. lia.
  - rewrite bits_shl. destruct (zlt (i - unsigned z) (unsigned y)).
    + rewrite bits_shl; auto. rewrite zlt_true. auto. lia.
    + rewrite bits_shl; auto. rewrite zlt_false. f_equal. lia. lia.
    + lia.
Qed.

Theorem sub_ltu:
  forall x y,
    ltu x y = true ->
    0 <= unsigned y - unsigned x <= unsigned y.
Proof.
  intros.
  generalize (ltu_inv x y H). intros .
  split. lia. lia.
Qed.

Theorem shru_zero: forall x, shru x zero = x.
Proof.
  bit_solve. rewrite unsigned_zero. rewrite zlt_true. f_equal; lia. lia.
Qed.

Lemma bitwise_binop_shru:
  forall f f' x y n,
  (forall x y i, 0 <= i < zwordsize -> testbit (f x y) i = f' (testbit x i) (testbit y i)) ->
  f' false false = false ->
  f (shru x n) (shru y n) = shru (f x y) n.
Proof.
  intros. apply same_bits_eq; intros.
  rewrite H; auto. rewrite !bits_shru; auto.
  destruct (zlt (i + unsigned n) zwordsize); auto.
  rewrite H; auto. generalize (unsigned_range n); lia.
Qed.

Theorem and_shru:
  forall x y n,
  and (shru x n) (shru y n) = shru (and x y) n.
Proof.
  intros. apply bitwise_binop_shru with andb; auto. exact bits_and.
Qed.

Theorem or_shru:
  forall x y n,
  or (shru x n) (shru y n) = shru (or x y) n.
Proof.
  intros. apply bitwise_binop_shru with orb; auto. exact bits_or.
Qed.

Theorem xor_shru:
  forall x y n,
  xor (shru x n) (shru y n) = shru (xor x y) n.
Proof.
  intros. apply bitwise_binop_shru with xorb; auto. exact bits_xor.
Qed.

Theorem shru_shru:
  forall x y z,
  ltu y iwordsize = true ->
  ltu z iwordsize = true ->
  ltu (add y z) iwordsize = true ->
  shru (shru x y) z = shru x (add y z).
Proof.
  intros.
  generalize (ltu_iwordsize_inv _ H) (ltu_iwordsize_inv _ H0); intros.
  assert (unsigned (add y z) = unsigned y + unsigned z).
    unfold add. apply unsigned_repr.
    generalize two_wordsize_max_unsigned; lia.
  apply same_bits_eq; intros.
  rewrite bits_shru; auto.
  destruct (zlt (i + unsigned z) zwordsize).
  - rewrite bits_shru. destruct (zlt (i + unsigned z + unsigned y) zwordsize).
    + rewrite bits_shru; auto. rewrite zlt_true. f_equal. lia. lia.
    + rewrite bits_shru; auto. rewrite zlt_false. auto. lia.
    + lia.
  - rewrite bits_shru; auto. rewrite zlt_false. auto. lia.
Qed.

Theorem shr_zero: forall x, shr x zero = x.
Proof.
  bit_solve. rewrite unsigned_zero. rewrite zlt_true. f_equal; lia. lia.
Qed.

Lemma bitwise_binop_shr:
  forall f f' x y n,
  (forall x y i, 0 <= i < zwordsize -> testbit (f x y) i = f' (testbit x i) (testbit y i)) ->
  f (shr x n) (shr y n) = shr (f x y) n.
Proof.
  intros. apply same_bits_eq; intros.
  rewrite H; auto. rewrite !bits_shr; auto.
  rewrite H; auto.
  destruct (zlt (i + unsigned n) zwordsize).
  generalize (unsigned_range n); lia.
  lia.
Qed.

Theorem and_shr:
  forall x y n,
  and (shr x n) (shr y n) = shr (and x y) n.
Proof.
  intros. apply bitwise_binop_shr with andb. exact bits_and.
Qed.

Theorem or_shr:
  forall x y n,
  or (shr x n) (shr y n) = shr (or x y) n.
Proof.
  intros. apply bitwise_binop_shr with orb. exact bits_or.
Qed.

Theorem xor_shr:
  forall x y n,
  xor (shr x n) (shr y n) = shr (xor x y) n.
Proof.
  intros. apply bitwise_binop_shr with xorb. exact bits_xor.
Qed.

Theorem shr_shr:
  forall x y z,
  ltu y iwordsize = true ->
  ltu z iwordsize = true ->
  ltu (add y z) iwordsize = true ->
  shr (shr x y) z = shr x (add y z).
Proof.
  intros.
  generalize (ltu_iwordsize_inv _ H) (ltu_iwordsize_inv _ H0); intros.
  assert (unsigned (add y z) = unsigned y + unsigned z).
    unfold add. apply unsigned_repr.
    generalize two_wordsize_max_unsigned; lia.
  apply same_bits_eq; intros.
  rewrite !bits_shr; auto. f_equal.
  destruct (zlt (i + unsigned z) zwordsize).
  rewrite H4. replace (i + (unsigned y + unsigned z)) with (i + unsigned z + unsigned y) by lia. auto.
  rewrite (zlt_false _ (i + unsigned (add y z))).
  destruct (zlt (zwordsize - 1 + unsigned y) zwordsize); lia.
  lia.
  destruct (zlt (i + unsigned z) zwordsize); lia.
Qed.

Theorem and_shr_shru:
  forall x y z,
  and (shr x z) (shru y z) = shru (and x y) z.
Proof.
  intros. apply same_bits_eq; intros.
  rewrite bits_and; auto. rewrite bits_shr; auto. rewrite !bits_shru; auto.
  destruct (zlt (i + unsigned z) zwordsize).
  - rewrite bits_and; auto. generalize (unsigned_range z); lia.
  - apply andb_false_r.
Qed.

Theorem shr_and_shru_and:
  forall x y z,
  shru (shl z y) y = z ->
  and (shr x y) z = and (shru x y) z.
Proof.
  intros.
  rewrite <- H.
  rewrite and_shru. rewrite and_shr_shru. auto.
Qed.

Theorem shru_lt_zero:
  forall x,
  shru x (repr (zwordsize - 1)) = if lt x zero then one else zero.
Proof.
  intros. apply same_bits_eq; intros.
  rewrite bits_shru; auto.
  rewrite unsigned_repr.
  destruct (zeq i 0).
  subst i. rewrite Z.add_0_l. rewrite zlt_true.
  rewrite sign_bit_of_unsigned.
  unfold lt. rewrite signed_zero. unfold signed.
  destruct (zlt (unsigned x) half_modulus).
  rewrite zlt_false. auto. generalize (unsigned_range x); lia.
  rewrite zlt_true. unfold one; rewrite testbit_repr; auto.
  generalize (unsigned_range x); lia.
  lia.
  rewrite zlt_false.
  unfold testbit. rewrite Ztestbit_eq. rewrite zeq_false.
  destruct (lt x zero).
  rewrite unsigned_one. simpl Z.div2. rewrite Z.testbit_0_l; auto.
  rewrite unsigned_zero. simpl Z.div2. rewrite Z.testbit_0_l; auto.
  auto. lia. lia.
  generalize wordsize_max_unsigned; lia.
Qed.

Theorem shr_lt_zero:
  forall x,
  shr x (repr (zwordsize - 1)) = if lt x zero then mone else zero.
Proof.
  intros. apply same_bits_eq; intros.
  rewrite bits_shr; auto.
  rewrite unsigned_repr.
  transitivity (testbit x (zwordsize - 1)).
  f_equal. destruct (zlt (i + (zwordsize - 1)) zwordsize); lia.
  rewrite sign_bit_of_unsigned.
  unfold lt. rewrite signed_zero. unfold signed.
  destruct (zlt (unsigned x) half_modulus).
  rewrite zlt_false. rewrite bits_zero; auto. generalize (unsigned_range x); lia.
  rewrite zlt_true. rewrite bits_mone; auto. generalize (unsigned_range x); lia.
  generalize wordsize_max_unsigned; lia.
Qed.

(** ** Properties of rotations *)

Lemma bits_rol:
  forall x y i,
  0 <= i < zwordsize ->
  testbit (rol x y) i = testbit x ((i - unsigned y) mod zwordsize).
Proof.
  intros. unfold rol.
  pose proof (Z_div_mod_eq_full (unsigned y) zwordsize) as EQ.
  set (j := unsigned y mod zwordsize). set (k := unsigned y / zwordsize).
  exploit (Z_mod_lt (unsigned y) zwordsize). apply wordsize_pos.
  fold j. intros RANGE.
  rewrite testbit_repr; auto.
  rewrite Z.lor_spec. rewrite Z.shiftr_spec. 2: lia.
  destruct (zlt i j).
  - rewrite Z.shiftl_spec_low; auto.
    Opaque zwordsize.
    simpl.
    Transparent zwordsize.
    unfold testbit. f_equal.
    symmetry. apply Zmod_unique with (-k - 1).
    rewrite EQ.
    lia.
    lia.
  - rewrite Z.shiftl_spec_high.
    fold (testbit x (i + (zwordsize - j))).
    rewrite bits_above. rewrite orb_false_r.
    fold (testbit x (i - j)).
    f_equal. symmetry. apply Zmod_unique with (-k).
    rewrite EQ.
    lia. lia. lia. lia.
    lia.
Qed.

Lemma bits_ror:
  forall x y i,
  0 <= i < zwordsize ->
  testbit (ror x y) i = testbit x ((i + unsigned y) mod zwordsize).
Proof.
  intros. unfold ror.
  pose proof (Z_div_mod_eq_full (unsigned y) zwordsize) as EQ.
  set (j := unsigned y mod zwordsize). set (k := unsigned y / zwordsize).
  exploit (Z_mod_lt (unsigned y) zwordsize). apply wordsize_pos.
  fold j. intros RANGE.
  rewrite testbit_repr; auto.
  rewrite Z.lor_spec. rewrite Z.shiftr_spec. 2: lia.
  destruct (zlt (i + j) zwordsize).
  - rewrite Z.shiftl_spec_low; auto. rewrite orb_false_r.
    unfold testbit. f_equal.
    symmetry. apply Zmod_unique with k.
    rewrite EQ.
    lia. lia. lia.
  - Opaque zwordsize.
    rewrite Z.shiftl_spec_high.
    fold (testbit x (i + j)).
    rewrite bits_above. simpl.
    unfold testbit. f_equal.
    symmetry. apply Zmod_unique with (k + 1).
    rewrite EQ. lia.
    lia. lia. lia. lia.
    Transparent zwordsize.
Qed.

Hint Rewrite bits_rol bits_ror: bit_ints.

Theorem shl_rolm:
  forall x n,
  ltu n iwordsize = true ->
  shl x n = rolm x n (shl mone n).
Proof.
  intros. generalize (ltu_inv _ _ H). rewrite unsigned_repr_wordsize; intros.
  unfold rolm. apply same_bits_eq; intros.
  rewrite bits_and; auto. rewrite !bits_shl; auto. rewrite bits_rol; auto.
  destruct (zlt i (unsigned n)).
  - rewrite andb_false_r; auto.
  - generalize (unsigned_range n); intros.
    rewrite bits_mone. rewrite andb_true_r. f_equal.
    symmetry. apply Zmod_small. lia.
    lia.
Qed.

Theorem shru_rolm:
  forall x n,
  ltu n iwordsize = true ->
  shru x n = rolm x (sub iwordsize n) (shru mone n).
Proof.
  intros. generalize (ltu_inv _ _ H). rewrite unsigned_repr_wordsize; intros.
  unfold rolm. apply same_bits_eq; intros.
  rewrite bits_and; auto. rewrite !bits_shru; auto. rewrite bits_rol; auto.
  destruct (zlt (i + unsigned n) zwordsize).
  - generalize (unsigned_range n); intros.
    rewrite bits_mone. rewrite andb_true_r. f_equal.
    unfold sub. rewrite unsigned_repr. rewrite unsigned_repr_wordsize.
    symmetry. apply Zmod_unique with (-1). ring. lia.
    rewrite unsigned_repr_wordsize. generalize wordsize_max_unsigned. lia.
    lia.
  - rewrite andb_false_r; auto.
Qed.

Theorem rol_zero:
  forall x,
  rol x zero = x.
Proof.
  bit_solve. f_equal. rewrite unsigned_zero. rewrite Z.sub_0_r.
  apply Zmod_small; auto.
Qed.

Lemma bitwise_binop_rol:
  forall f f' x y n,
  (forall x y i, 0 <= i < zwordsize -> testbit (f x y) i = f' (testbit x i) (testbit y i)) ->
  rol (f x y) n = f (rol x n) (rol y n).
Proof.
  intros. apply same_bits_eq; intros.
  rewrite H; auto. rewrite !bits_rol; auto. rewrite H; auto.
  apply Z_mod_lt. apply wordsize_pos.
Qed.

Theorem rol_and:
  forall x y n,
  rol (and x y) n = and (rol x n) (rol y n).
Proof.
  intros. apply bitwise_binop_rol with andb. exact bits_and.
Qed.

Theorem rol_or:
  forall x y n,
  rol (or x y) n = or (rol x n) (rol y n).
Proof.
  intros. apply bitwise_binop_rol with orb. exact bits_or.
Qed.

Theorem rol_xor:
  forall x y n,
  rol (xor x y) n = xor (rol x n) (rol y n).
Proof.
  intros. apply bitwise_binop_rol with xorb. exact bits_xor.
Qed.

Theorem rol_rol:
  forall x n m,
  Z.divide zwordsize modulus ->
  rol (rol x n) m = rol x (modu (add n m) iwordsize).
Proof.
  bit_solve. f_equal. apply eqmod_mod_eq. apply wordsize_pos.
  set (M := unsigned m); set (N := unsigned n).
  apply eqmod_trans with (i - M - N).
  apply eqmod_sub.
  apply eqmod_sym. apply eqmod_mod.
  apply eqmod_refl.
  replace (i - M - N) with (i - (M + N)) by lia.
  apply eqmod_sub.
  apply eqmod_refl.
  apply eqmod_trans with (Z.modulo (unsigned n + unsigned m) zwordsize).
  replace (M + N) with (N + M) by lia. apply eqmod_mod.
  unfold modu, add. fold M; fold N. rewrite unsigned_repr_wordsize.
  assert (forall a, eqmod zwordsize a (unsigned (repr a))).
    intros. eapply eqmod_divides. apply eqm_unsigned_repr. assumption.
  eapply eqmod_trans. 2: apply H1.
  apply eqmod_refl2. apply eqmod_mod_eq. apply wordsize_pos. auto.
  apply Z_mod_lt. apply wordsize_pos.
Qed.

Theorem rolm_zero:
  forall x m,
  rolm x zero m = and x m.
Proof.
  intros. unfold rolm. rewrite rol_zero. auto.
Qed.

Theorem rolm_rolm:
  forall x n1 m1 n2 m2,
  Z.divide zwordsize modulus ->
  rolm (rolm x n1 m1) n2 m2 =
    rolm x (modu (add n1 n2) iwordsize)
           (and (rol m1 n2) m2).
Proof.
  intros.
  unfold rolm. rewrite rol_and. rewrite and_assoc.
  rewrite rol_rol. reflexivity. auto.
Qed.

Theorem or_rolm:
  forall x n m1 m2,
  or (rolm x n m1) (rolm x n m2) = rolm x n (or m1 m2).
Proof.
  intros; unfold rolm. symmetry. apply and_or_distrib.
Qed.

Theorem ror_rol:
  forall x y,
  ltu y iwordsize = true ->
  ror x y = rol x (sub iwordsize y).
Proof.
  intros.
  generalize (ltu_iwordsize_inv _ H); intros.
  apply same_bits_eq; intros.
  rewrite bits_ror; auto. rewrite bits_rol; auto. f_equal.
  unfold sub. rewrite unsigned_repr. rewrite unsigned_repr_wordsize.
  apply eqmod_mod_eq. apply wordsize_pos. exists 1. ring.
  rewrite unsigned_repr_wordsize.
  generalize wordsize_pos; generalize wordsize_max_unsigned; lia.
Qed.

Theorem ror_rol_neg:
  forall x y, (zwordsize | modulus) -> ror x y = rol x (neg y).
Proof.
  intros. apply same_bits_eq; intros.
  rewrite bits_ror by auto. rewrite bits_rol by auto.
  f_equal. apply eqmod_mod_eq. lia.
  apply eqmod_trans with (i - (- unsigned y)).
  apply eqmod_refl2; lia.
  apply eqmod_sub. apply eqmod_refl.
  apply eqmod_divides with modulus.
  apply eqm_unsigned_repr. auto.
Qed.

Theorem or_ror:
  forall x y z,
  ltu y iwordsize = true ->
  ltu z iwordsize = true ->
  add y z = iwordsize ->
  ror x z = or (shl x y) (shru x z).
Proof.
  intros.
  generalize (ltu_iwordsize_inv _ H) (ltu_iwordsize_inv _ H0); intros.
  unfold ror, or, shl, shru. apply same_bits_eq; intros.
  rewrite !testbit_repr; auto.
  rewrite !Z.lor_spec. rewrite orb_comm. f_equal; apply same_bits_eqm; auto.
  - apply eqm_unsigned_repr_r. apply eqm_refl2. f_equal.
    rewrite Zmod_small; auto.
    assert (unsigned (add y z) = zwordsize).
      rewrite H1. apply unsigned_repr_wordsize.
    unfold add in H5. rewrite unsigned_repr in H5.
    lia.
    generalize two_wordsize_max_unsigned; lia.
  - apply eqm_unsigned_repr_r. apply eqm_refl2. f_equal.
    apply Zmod_small; auto.
Qed.

(** ** Properties of [Z_one_bits] and [is_power2]. *)

Fixpoint powerserie (l: list Z): Z :=
  match l with
  | nil => 0
  | x :: xs => two_p x + powerserie xs
  end.

Lemma Z_one_bits_powerserie:
  forall x, 0 <= x < modulus -> x = powerserie (Z_one_bits natwordsize x 0).
Proof.
  assert (forall n x i,
    0 <= i ->
    0 <= x < two_power_nat n ->
    x * two_p i = powerserie (Z_one_bits n x i)).
  {
  induction n; intros.
  simpl. rewrite two_power_nat_O in H0.
  assert (x = 0) by lia. subst x. lia.
  rewrite two_power_nat_S in H0. simpl Z_one_bits.
  rewrite (Zdecomp x) in H0. rewrite Zshiftin_spec in H0.
  assert (EQ: Z.div2 x * two_p (i + 1) = powerserie (Z_one_bits n (Z.div2 x) (i + 1))).
    apply IHn. lia.
    destruct (Z.odd x); lia.
  rewrite two_p_is_exp in EQ. change (two_p 1) with 2 in EQ.
  rewrite (Zdecomp x) at 1. rewrite Zshiftin_spec.
  destruct (Z.odd x); simpl powerserie; rewrite <- EQ; ring.
  lia. lia.
  }
  intros. rewrite <- H. change (two_p 0) with 1. lia.
  lia.
  setoid_rewrite <- two_power_pos_nat.
  exact H0.
Qed.

Lemma Z_one_bits_range:
  forall x i, In i (Z_one_bits natwordsize x 0) -> 0 <= i < zwordsize.
Proof.
  assert (forall n x i j,
    In j (Z_one_bits n x i) -> i <= j < i + Z.of_nat n).
  {
  induction n; simpl In.
  tauto.
  intros x i j. rewrite Nat2Z.inj_succ.
  assert (In j (Z_one_bits n (Z.div2 x) (i + 1)) -> i <= j < i + Z.succ (Z.of_nat n)).
    intros. exploit IHn; eauto. lia.
  destruct (Z.odd x); simpl.
  intros [A|B]. subst j. lia. auto.
  auto.
  }
  intros. generalize (H natwordsize x 0 i H0).
  setoid_rewrite positive_nat_Z; auto.
Qed.

Lemma is_power2_rng:
  forall n logn,
  is_power2 n = Some logn ->
  0 <= unsigned logn < zwordsize.
Proof.
  intros n logn. unfold is_power2.
  generalize (Z_one_bits_range (unsigned n)).
  destruct (Z_one_bits natwordsize (unsigned n) 0).
  intros; discriminate.
  destruct l.
  intros. injection H0; intro; subst logn; clear H0.
  assert (0 <= z < zwordsize).
  apply H. auto with coqlib.
  rewrite unsigned_repr. auto. generalize wordsize_max_unsigned; lia.
  intros; discriminate.
Qed.

Theorem is_power2_range:
  forall n logn,
  is_power2 n = Some logn -> ltu logn iwordsize = true.
Proof.
  intros. unfold ltu. rewrite unsigned_repr_wordsize.
  apply zlt_true. generalize (is_power2_rng _ _ H). tauto.
Qed.

Lemma is_power2_correct:
  forall n logn,
  is_power2 n = Some logn ->
  unsigned n = two_p (unsigned logn).
Proof.
  intros n logn. unfold is_power2.
  generalize (Z_one_bits_powerserie (unsigned n) (unsigned_range n)).
  generalize (Z_one_bits_range (unsigned n)).
  destruct (Z_one_bits natwordsize (unsigned n) 0).
  intros; discriminate.
  destruct l.
  intros. simpl in H0. injection H1; intros; subst logn; clear H1.
  rewrite unsigned_repr. replace (two_p z) with (two_p z + 0).
  auto. lia. elim (H z); intros.
  generalize wordsize_max_unsigned; lia.
  auto with coqlib.
  intros; discriminate.
Qed.

Remark two_p_range:
  forall n,
  0 <= n < zwordsize ->
  0 <= two_p n <= max_unsigned.
Proof.
  intros. split.
  assert (two_p n > 0). apply two_p_gt_ZERO. lia. lia.
  generalize (two_p_monotone_strict _ _ H).
  unfold zwordsize in *.
  rewrite <- positive_nat_Z; auto.
  unfold max_unsigned, modulus.
  setoid_rewrite <- two_power_nat_two_p.
  rewrite <- positive_nat_Z in H.
  rewrite <- two_power_pos_nat.
  lia.
Qed.

Remark Z_one_bits_zero:
  forall n i, Z_one_bits n 0 i = nil.
Proof.
  induction n; intros; simpl; auto.
Qed.

Remark Z_one_bits_two_p:
  forall n x i,
  0 <= x < Z.of_nat n ->
  Z_one_bits n (two_p x) i = (i + x) :: nil.
Proof.
  induction n; intros; simpl. simpl in H. lia.
  rewrite Nat2Z.inj_succ in H.
  assert (x = 0 \/ 0 < x) by lia. destruct H0.
  subst x; simpl. decEq. lia. apply Z_one_bits_zero.
  assert (Z.odd (two_p x) = false /\ Z.div2 (two_p x) = two_p (x-1)).
    apply Zshiftin_inj. rewrite <- Zdecomp. rewrite !Zshiftin_spec.
    rewrite <- two_p_S. rewrite Z.add_0_r. f_equal; lia. lia.
  destruct H1 as [A B]; rewrite A; rewrite B.
  rewrite IHn. f_equal; lia. lia.
Qed.

Lemma is_power2_two_p:
  forall n, 0 <= n < zwordsize ->
  is_power2 (repr (two_p n)) = Some (repr n).
Proof.
  intros. unfold is_power2. rewrite unsigned_repr.
  rewrite Z_one_bits_two_p. auto.
  setoid_rewrite positive_nat_Z.
  auto.
  apply two_p_range; auto.
Qed.

(** ** Relation between bitwise operations and multiplications / divisions by powers of 2 *)

(** Left shifts and multiplications by powers of 2. *)

Lemma Zshiftl_mul_two_p:
  forall x n, 0 <= n -> Z.shiftl x n = x * two_p n.
Proof.
  intros. destruct n; simpl.
  - lia.
  - pattern p. apply Pos.peano_ind.
    + change (two_power_pos 1) with 2. simpl. ring.
    + intros. rewrite Pos.iter_succ. rewrite H0.
      rewrite Pplus_one_succ_l. rewrite two_power_pos_is_exp.
      change (two_power_pos 1) with 2. ring.
  - compute in H. congruence.
Qed.

Lemma shl_mul_two_p:
  forall x y,
  shl x y = mul x (repr (two_p (unsigned y))).
Proof.
  intros. unfold shl, mul. apply eqm_samerepr.
  rewrite Zshiftl_mul_two_p. auto with bit_ints.
  generalize (unsigned_range y); lia.
Qed.

Theorem shl_mul:
  forall x y,
  shl x y = mul x (shl one y).
Proof.
  intros.
  assert (shl one y = repr (two_p (unsigned y))).
  {
    rewrite shl_mul_two_p. rewrite mul_commut. rewrite mul_one. auto.
  }
  rewrite H. apply shl_mul_two_p.
Qed.

Theorem mul_pow2:
  forall x n logn,
  is_power2 n = Some logn ->
  mul x n = shl x logn.
Proof.
  intros. generalize (is_power2_correct n logn H); intro.
  rewrite shl_mul_two_p. rewrite <- H0. rewrite repr_unsigned.
  auto.
Qed.

Theorem shifted_or_is_add:
  forall x y n,
  0 <= n < zwordsize ->
  unsigned y < two_p n ->
  or (shl x (repr n)) y = repr(unsigned x * two_p n + unsigned y).
Proof.
  intros. rewrite <- add_is_or.
  - unfold add. apply eqm_samerepr. apply eqm_add; auto with bit_ints.
    rewrite shl_mul_two_p. unfold mul. apply eqm_unsigned_repr_l.
    apply eqm_mult; auto with bit_ints. apply eqm_unsigned_repr_l.
    apply eqm_refl2. rewrite unsigned_repr. auto.
    generalize wordsize_max_unsigned; lia.
  - bit_solve.
    rewrite unsigned_repr.
    destruct (zlt i n).
    + auto.
    + replace (testbit y i) with false. apply andb_false_r.
      symmetry. unfold testbit.
      assert (EQ: Z.of_nat (Z.to_nat n) = n) by (apply Z2Nat.id; lia).
      apply Ztestbit_above with (Z.to_nat n).
      rewrite <- EQ in H0. rewrite <- two_power_nat_two_p in H0.
      generalize (unsigned_range y); lia.
      rewrite EQ; auto.
    + generalize wordsize_max_unsigned; lia.
Qed.

(** Unsigned right shifts and unsigned divisions by powers of 2. *)

Lemma Zshiftr_div_two_p:
  forall x n, 0 <= n -> Z.shiftr x n = x / two_p n.
Proof.
  intros. destruct n; unfold Z.shiftr; simpl.
  - rewrite Zdiv_1_r. auto.
  - pattern p. apply Pos.peano_ind.
    + change (two_power_pos 1) with 2. simpl. apply Zdiv2_div.
    + intros. rewrite Pos.iter_succ. rewrite H0.
      rewrite Pplus_one_succ_l. rewrite two_power_pos_is_exp.
      change (two_power_pos 1) with 2.
      rewrite Zdiv2_div. rewrite Z.mul_comm. apply Zdiv_Zdiv.
      rewrite two_power_pos_nat. apply two_power_nat_pos. lia.
  - compute in H. congruence.
Qed.

Lemma shru_div_two_p:
  forall x y,
  shru x y = repr (unsigned x / two_p (unsigned y)).
Proof.
  intros. unfold shru.
  rewrite Zshiftr_div_two_p. auto.
  generalize (unsigned_range y); lia.
Qed.

Theorem divu_pow2:
  forall x n logn,
  is_power2 n = Some logn ->
  divu x n = shru x logn.
Proof.
  intros. generalize (is_power2_correct n logn H). intro.
  symmetry. unfold divu. rewrite H0. apply shru_div_two_p.
Qed.

(** Signed right shifts and signed divisions by powers of 2. *)

Lemma shr_div_two_p:
  forall x y,
  shr x y = repr (signed x / two_p (unsigned y)).
Proof.
  intros. unfold shr.
  rewrite Zshiftr_div_two_p. auto.
  generalize (unsigned_range y); lia.
Qed.

Theorem divs_pow2:
  forall x n logn,
  is_power2 n = Some logn ->
  divs x n = shrx x logn.
Proof.
  intros. generalize (is_power2_correct _ _ H); intro.
  unfold shrx. rewrite shl_mul_two_p.
  rewrite mul_commut. rewrite mul_one.
  rewrite <- H0. rewrite repr_unsigned. auto.
Qed.

(** Unsigned modulus over [2^n] is masking with [2^n-1]. *)

Lemma Ztestbit_mod_two_p:
  forall n x i,
  0 <= n -> 0 <= i ->
  Z.testbit (x mod (two_p n)) i = if zlt i n then Z.testbit x i else false.
Proof.
  intros n0 x i N0POS. revert x i; pattern n0; apply natlike_ind; auto.
  - intros. change (two_p 0) with 1. rewrite Zmod_1_r. rewrite Z.testbit_0_l.
    rewrite zlt_false; auto. lia.
  - intros. rewrite two_p_S; auto.
    replace (x0 mod (2 * two_p x))
       with (Zshiftin (Z.odd x0) (Z.div2 x0 mod two_p x)).
    rewrite Ztestbit_shiftin; auto. rewrite (Ztestbit_eq i x0); auto. destruct (zeq i 0).
    + rewrite zlt_true; auto. lia.
    + rewrite H0. destruct (zlt (Z.pred i) x).
      * rewrite zlt_true; auto. lia.
      * rewrite zlt_false; auto. lia.
      * lia.
    + rewrite (Zdecomp x0) at 3. set (x1 := Z.div2 x0). symmetry.
      apply Zmod_unique with (x1 / two_p x).
      rewrite !Zshiftin_spec. rewrite Z.add_assoc. f_equal.
      transitivity (2 * (two_p x * (x1 / two_p x) + x1 mod two_p x)).
      f_equal. apply Z_div_mod_eq_full.
      ring.
      rewrite Zshiftin_spec. exploit (Z_mod_lt x1 (two_p x)). apply two_p_gt_ZERO; auto.
      destruct (Z.odd x0); lia.
Qed.

Corollary Ztestbit_two_p_m1:
  forall n i, 0 <= n -> 0 <= i ->
  Z.testbit (two_p n - 1) i = if zlt i n then true else false.
Proof.
  intros. replace (two_p n - 1) with ((-1) mod (two_p n)).
  rewrite Ztestbit_mod_two_p; auto. destruct (zlt i n); auto. apply Ztestbit_m1; auto.
  apply Zmod_unique with (-1). ring.
  exploit (two_p_gt_ZERO n). auto. lia.
Qed.

Theorem modu_and:
  forall x n logn,
  is_power2 n = Some logn ->
  modu x n = and x (sub n one).
Proof.
  intros. generalize (is_power2_correct _ _ H); intro.
  generalize (is_power2_rng _ _ H); intro.
  apply same_bits_eq; intros.
  rewrite bits_and; auto.
  unfold sub. rewrite testbit_repr; auto.
  rewrite H0. rewrite unsigned_one.
  unfold modu. rewrite testbit_repr; auto. rewrite H0.
  rewrite Ztestbit_mod_two_p. rewrite Ztestbit_two_p_m1.
  destruct (zlt i (unsigned logn)).
  rewrite andb_true_r; auto.
  rewrite andb_false_r; auto.
  tauto. tauto. tauto. tauto.
Qed.

(** ** Properties of [shrx] (signed division by a power of 2) *)

Lemma Zquot_Zdiv:
  forall x y,
  y > 0 ->
  Z.quot x y = if zlt x 0 then (x + y - 1) / y else x / y.
Proof.
  intros. destruct (zlt x 0).
  - symmetry. apply Zquot_unique_full with ((x + y - 1) mod y - (y - 1)).
     + red. right; split. lia.
       exploit (Z_mod_lt (x + y - 1) y); auto.
       rewrite Z.abs_eq. lia. lia.
     + transitivity ((y * ((x + y - 1) / y) + (x + y - 1) mod y) - (y-1)).
       rewrite <- Z_div_mod_eq_full. ring. ring.
  - apply Zquot_Zdiv_pos; lia.
Qed.

Theorem shrx_zero:
  forall x, zwordsize > 1 -> shrx x zero = x.
Proof.
  intros. unfold shrx. rewrite shl_zero. unfold divs. rewrite signed_one by auto.
  rewrite Z.quot_1_r. apply repr_signed.
Qed.

Theorem shrx_shr:
  forall x y,
  ltu y (repr (zwordsize - 1)) = true ->
  shrx x y = shr (if lt x zero then add x (sub (shl one y) one) else x) y.
Proof.
  intros.
  set (uy := unsigned y).
  assert (0 <= uy < zwordsize - 1).
    generalize (ltu_inv _ _ H). rewrite unsigned_repr. auto.
    generalize wordsize_pos wordsize_max_unsigned; lia.
  rewrite shr_div_two_p. unfold shrx. unfold divs.
  assert (shl one y = repr (two_p uy)).
    transitivity (mul one (repr (two_p uy))).
    symmetry. apply mul_pow2. replace y with (repr uy).
    apply is_power2_two_p. lia. apply repr_unsigned.
    rewrite mul_commut. apply mul_one.
  assert (two_p uy > 0). apply two_p_gt_ZERO. lia.
  assert (two_p uy < half_modulus).
    rewrite half_modulus_power.
    apply two_p_monotone_strict. auto.
  assert (two_p uy < modulus).
    rewrite modulus_power. apply two_p_monotone_strict. lia.
  assert (unsigned (shl one y) = two_p uy).
    rewrite H1. apply unsigned_repr. unfold max_unsigned. lia.
  assert (signed (shl one y) = two_p uy).
    rewrite H1. apply signed_repr.
    unfold max_signed. generalize min_signed_neg. lia.
  rewrite H6.
  rewrite Zquot_Zdiv; auto.
  unfold lt. rewrite signed_zero.
  destruct (zlt (signed x) 0); auto.
  rewrite add_signed.
  assert (signed (sub (shl one y) one) = two_p uy - 1).
    unfold sub. rewrite H5. rewrite unsigned_one.
    apply signed_repr.
    generalize min_signed_neg. unfold max_signed. lia.
  rewrite H7. rewrite signed_repr. f_equal. f_equal. lia.
  generalize (signed_range x). intros.
  assert (two_p uy - 1 <= max_signed). unfold max_signed. lia. lia.
Qed.

Theorem shrx_shr_2:
  forall x y,
  ltu y (repr (zwordsize - 1)) = true ->
  shrx x y = shr (add x (shru (shr x (repr (zwordsize - 1))) (sub iwordsize y))) y.
Proof.
  intros.
  rewrite shrx_shr by auto. f_equal.
  rewrite shr_lt_zero. destruct (lt x zero).
- set (uy := unsigned y).
  generalize (unsigned_range y); fold uy; intros.
  assert (0 <= uy < zwordsize - 1).
    generalize (ltu_inv _ _ H). rewrite unsigned_repr. auto.
    generalize wordsize_pos wordsize_max_unsigned; lia.
  assert (two_p uy < modulus).
    rewrite modulus_power. apply two_p_monotone_strict. lia.
  f_equal. rewrite shl_mul_two_p. fold uy. rewrite mul_commut. rewrite mul_one.
  unfold sub. rewrite unsigned_one. rewrite unsigned_repr.
  rewrite unsigned_repr_wordsize. fold uy.
  apply same_bits_eq; intros. rewrite bits_shru by auto.
  rewrite testbit_repr by auto. rewrite Ztestbit_two_p_m1 by lia.
  rewrite unsigned_repr by (generalize wordsize_max_unsigned; lia).
  destruct (zlt i uy).
  rewrite zlt_true by lia. rewrite bits_mone by lia. auto.
  rewrite zlt_false by lia. auto.
  assert (two_p uy > 0) by (apply two_p_gt_ZERO; lia). unfold max_unsigned; lia.
- replace (shru zero (sub iwordsize y)) with zero.
  rewrite add_zero; auto.
  bit_solve. destruct (zlt (i + unsigned (sub iwordsize y)) zwordsize); auto.
Qed.

Lemma Zdiv_shift:
  forall x y, y > 0 ->
  (x + (y - 1)) / y = x / y + if zeq (Z.modulo x y) 0 then 0 else 1.
Proof.
  intros. generalize (Z_div_mod_eq_full x y). generalize (Z_mod_lt x y H).
  set (q := x / y). set (r := x mod y). intros.
  destruct (zeq r 0).
  apply Zdiv_unique with (y - 1). rewrite H1. rewrite e. ring. lia.
  apply Zdiv_unique with (r - 1). rewrite H1. ring. lia.
Qed.

Theorem shrx_carry:
  forall x y,
  ltu y (repr (zwordsize - 1)) = true ->
  shrx x y = add (shr x y) (shr_carry x y).
Proof.
  intros. rewrite shrx_shr; auto. unfold shr_carry.
  unfold lt. set (sx := signed x). rewrite signed_zero.
  destruct (zlt sx 0); simpl.
  2: rewrite add_zero; auto.
  set (uy := unsigned y).
  assert (0 <= uy < zwordsize - 1).
    generalize (ltu_inv _ _ H). rewrite unsigned_repr. auto.
    generalize wordsize_pos wordsize_max_unsigned; lia.
  assert (shl one y = repr (two_p uy)).
    rewrite shl_mul_two_p. rewrite mul_commut. apply mul_one.
  assert (and x (sub (shl one y) one) = modu x (repr (two_p uy))).
    symmetry. rewrite H1. apply modu_and with (logn := y).
    rewrite is_power2_two_p. unfold uy. rewrite repr_unsigned. auto.
    lia.
  rewrite H2. rewrite H1.
  repeat rewrite shr_div_two_p. fold sx. fold uy.
  assert (two_p uy > 0). apply two_p_gt_ZERO. lia.
  assert (two_p uy < modulus).
    rewrite modulus_power. apply two_p_monotone_strict. lia.
  assert (two_p uy < half_modulus).
    rewrite half_modulus_power.
    apply two_p_monotone_strict. auto.
  assert (two_p uy < modulus).
    rewrite modulus_power. apply two_p_monotone_strict. lia.
  assert (sub (repr (two_p uy)) one = repr (two_p uy - 1)).
    unfold sub. apply eqm_samerepr. apply eqm_sub. apply eqm_sym; apply eqm_unsigned_repr.
    rewrite unsigned_one. apply eqm_refl.
  rewrite H7. rewrite add_signed. fold sx.
  rewrite (signed_repr (two_p uy - 1)). rewrite signed_repr.
  unfold modu. rewrite unsigned_repr.
  unfold eq. rewrite unsigned_zero. rewrite unsigned_repr.
  assert (unsigned x mod two_p uy = sx mod two_p uy).
    apply eqmod_mod_eq; auto. apply eqmod_divides with modulus.
    fold eqm. unfold sx. apply eqm_sym. apply eqm_signed_unsigned.
    unfold modulus. rewrite two_power_pos_two_p.
    exists (two_p (zwordsize - uy)). rewrite <- two_p_is_exp.
    f_equal. fold zwordsize; lia. lia. lia.
  rewrite H8. rewrite Zdiv_shift; auto.
  unfold add. apply eqm_samerepr. apply eqm_add.
  apply eqm_unsigned_repr.
  destruct (zeq (sx mod two_p uy) 0); simpl.
  rewrite unsigned_zero. apply eqm_refl.
  rewrite unsigned_one. apply eqm_refl.
  generalize (Z_mod_lt (unsigned x) (two_p uy) H3). unfold max_unsigned. lia.
  unfold max_unsigned; lia.
  generalize (signed_range x). fold sx. intros. split. lia. unfold max_signed. lia.
  generalize min_signed_neg. unfold max_signed. lia.
Qed.

(** Connections between [shr] and [shru]. *)

Lemma shr_shru_positive:
  forall x y,
  signed x >= 0 ->
  shr x y = shru x y.
Proof.
  intros.
  rewrite shr_div_two_p. rewrite shru_div_two_p.
  rewrite signed_eq_unsigned. auto. apply signed_positive. auto.
Qed.

Lemma and_positive:
  forall x y, signed y >= 0 -> signed (and x y) >= 0.
Proof.
  intros.
  assert (unsigned y < half_modulus). rewrite signed_positive in H. unfold max_signed in H; lia.
  generalize (sign_bit_of_unsigned y). rewrite zlt_true; auto. intros A.
  generalize (sign_bit_of_unsigned (and x y)). rewrite bits_and. rewrite A.
  rewrite andb_false_r. unfold signed.
  destruct (zlt (unsigned (and x y)) half_modulus).
  intros. generalize (unsigned_range (and x y)); lia.
  congruence.
  generalize wordsize_pos; lia.
Qed.

Theorem shr_and_is_shru_and:
  forall x y z,
  lt y zero = false -> shr (and x y) z = shru (and x y) z.
Proof.
  intros. apply shr_shru_positive. apply and_positive.
  unfold lt in H. rewrite signed_zero in H. destruct (zlt (signed y) 0). congruence. auto.
Qed.

(** ** Properties of integer zero extension and sign extension. *)

Lemma Ziter_base:
  forall (A: Type) n (f: A -> A) x, n <= 0 -> Z.iter n f x = x.
Proof.
  intros. unfold Z.iter. destruct n; auto. compute in H. elim H; auto.
Qed.

Lemma Ziter_succ:
  forall (A: Type) n (f: A -> A) x,
  0 <= n -> Z.iter (Z.succ n) f x = f (Z.iter n f x).
Proof.
  intros. destruct n; simpl.
  - auto.
  - rewrite Pos.add_1_r. apply Pos.iter_succ.
  - compute in H. elim H; auto.
Qed.

Lemma Znatlike_ind:
  forall (P: Z -> Prop),
  (forall n, n <= 0 -> P n) ->
  (forall n, 0 <= n -> P n -> P (Z.succ n)) ->
  forall n, P n.
Proof.
  intros. destruct (zle 0 n).
  apply natlike_ind; auto. apply H; lia.
  apply H. lia.
Qed.

Lemma Zzero_ext_spec:
  forall n x i, 0 <= i ->
  Z.testbit (Zzero_ext n x) i = if zlt i n then Z.testbit x i else false.
Proof.
  unfold Zzero_ext. induction n using Znatlike_ind.
  - intros. rewrite Ziter_base; auto.
    rewrite zlt_false. rewrite Ztestbit_0; auto. lia.
  - intros. rewrite Ziter_succ; auto.
    rewrite Ztestbit_shiftin; auto.
    rewrite (Ztestbit_eq i x); auto.
    destruct (zeq i 0).
    + subst i. rewrite zlt_true; auto. lia.
    + rewrite IHn. destruct (zlt (Z.pred i) n).
      rewrite zlt_true; auto. lia.
      rewrite zlt_false; auto. lia.
      lia.
Qed.

Lemma bits_zero_ext:
  forall n x i, 0 <= i ->
  testbit (zero_ext n x) i = if zlt i n then testbit x i else false.
Proof.
  intros. unfold zero_ext. destruct (zlt i zwordsize).
  rewrite testbit_repr; auto. rewrite Zzero_ext_spec. auto. auto.
  rewrite !bits_above; auto. destruct (zlt i n); auto.
Qed.

Lemma Zsign_ext_spec:
  forall n x i, 0 <= i -> 0 < n ->
  Z.testbit (Zsign_ext n x) i = Z.testbit x (if zlt i n then i else n - 1).
Proof.
  intros n0 x i I0 N0.
  revert x i I0. pattern n0. apply Zlt_lower_bound_ind with (z := 1).
  - unfold Zsign_ext. intros.
    destruct (zeq x 1).
    + subst x; simpl.
      replace (if zlt i 1 then i else 0) with 0.
      rewrite Ztestbit_base.
      destruct (Z.odd x0).
      apply Ztestbit_m1; auto.
      apply Ztestbit_0.
      destruct (zlt i 1); lia.
    + set (x1 := Z.pred x). replace x1 with (Z.succ (Z.pred x1)).
      rewrite Ziter_succ. rewrite Ztestbit_shiftin.
      destruct (zeq i 0).
      * subst i. rewrite zlt_true. rewrite Ztestbit_base; auto. lia.
      * rewrite H. unfold x1. destruct (zlt (Z.pred i) (Z.pred x)).
        rewrite zlt_true. rewrite (Ztestbit_eq i x0); auto. rewrite zeq_false; auto. lia.
        rewrite zlt_false. rewrite (Ztestbit_eq (x - 1) x0). rewrite zeq_false; auto.
        lia. lia. lia. unfold x1; lia. lia.
      * lia.
      * unfold x1; lia.
      * lia.
  - lia.
Qed.

Lemma bits_sign_ext:
  forall n x i, 0 <= i < zwordsize -> 0 < n ->
  testbit (sign_ext n x) i = testbit x (if zlt i n then i else n - 1).
Proof.
  intros. unfold sign_ext.
  rewrite testbit_repr; auto. rewrite Zsign_ext_spec. destruct (zlt i n); auto.
  lia. auto.
Qed.

Hint Rewrite bits_zero_ext bits_sign_ext: bit_ints.

Theorem zero_ext_above:
  forall n x, n >= zwordsize -> zero_ext n x = x.
Proof.
  intros. apply same_bits_eq; intros.
  rewrite bits_zero_ext. apply zlt_true. lia. lia.
Qed.

Theorem sign_ext_above:
  forall n x, n >= zwordsize -> sign_ext n x = x.
Proof.
  intros. apply same_bits_eq; intros.
  unfold sign_ext; rewrite testbit_repr; auto.
  rewrite Zsign_ext_spec. rewrite zlt_true. auto. lia. lia. lia.
Qed.

Theorem zero_ext_and:
  forall n x, 0 <= n -> zero_ext n x = and x (repr (two_p n - 1)).
Proof.
  bit_solve. rewrite testbit_repr; auto. rewrite Ztestbit_two_p_m1; intuition.
  destruct (zlt i n).
  rewrite andb_true_r; auto.
  rewrite andb_false_r; auto.
  tauto.
Qed.

Theorem zero_ext_mod:
  forall n x, 0 <= n < zwordsize ->
  unsigned (zero_ext n x) = Z.modulo (unsigned x) (two_p n).
Proof.
  intros. apply equal_same_bits. intros.
  rewrite Ztestbit_mod_two_p; auto.
  fold (testbit (zero_ext n x) i).
  destruct (zlt i zwordsize).
  rewrite bits_zero_ext; auto.
  rewrite bits_above. rewrite zlt_false; auto. lia. lia.
  lia.
Qed.

Theorem zero_ext_widen:
  forall x n n', 0 <= n <= n' ->
  zero_ext n' (zero_ext n x) = zero_ext n x.
Proof.
  bit_solve. destruct (zlt i n).
  apply zlt_true. lia.
  destruct (zlt i n'); auto.
  tauto. tauto.
Qed.

Theorem sign_ext_widen:
  forall x n n', 0 < n  <= n' ->
  sign_ext n' (sign_ext n x) = sign_ext n x.
Proof.
  intros. destruct (zlt n' zwordsize).
  bit_solve. destruct (zlt i n').
  auto.
  rewrite (zlt_false _ i n).
  destruct (zlt (n' - 1) n); f_equal; lia.
  lia. lia.
  destruct (zlt i n'); lia.
  lia. lia.
  apply sign_ext_above; auto.
Qed.

Theorem sign_zero_ext_widen:
  forall x n n', 0 <= n < n' ->
  sign_ext n' (zero_ext n x) = zero_ext n x.
Proof.
  intros. destruct (zlt n' zwordsize).
  bit_solve.
  destruct (zlt i n').
  auto.
  rewrite !zlt_false. auto. lia. lia. lia.
  destruct (zlt i n'); lia.
  lia.
  apply sign_ext_above; auto.
Qed.

Theorem zero_ext_narrow:
  forall x n n', 0 <= n <= n' ->
  zero_ext n (zero_ext n' x) = zero_ext n x.
Proof.
  bit_solve. destruct (zlt i n).
  apply zlt_true. lia.
  auto.
  lia. lia. lia.
Qed.

Theorem sign_ext_narrow:
  forall x n n', 0 < n <= n' ->
  sign_ext n (sign_ext n' x) = sign_ext n x.
Proof.
  intros. destruct (zlt n zwordsize).
  bit_solve. destruct (zlt i n); f_equal; apply zlt_true; lia.
  lia.
  destruct (zlt i n); lia.
  lia. lia.
  rewrite (sign_ext_above n'). auto. lia.
Qed.

Theorem zero_sign_ext_narrow:
  forall x n n', 0 < n <= n' ->
  zero_ext n (sign_ext n' x) = zero_ext n x.
Proof.
  intros. destruct (zlt n' zwordsize).
  bit_solve.
  destruct (zlt i n); auto.
  rewrite zlt_true; auto. lia.
  lia. lia. lia.
  rewrite sign_ext_above; auto.
Qed.

Theorem zero_ext_idem:
  forall n x, 0 <= n -> zero_ext n (zero_ext n x) = zero_ext n x.
Proof.
  intros. apply zero_ext_widen. lia.
Qed.

Theorem sign_ext_idem:
  forall n x, 0 < n -> sign_ext n (sign_ext n x) = sign_ext n x.
Proof.
  intros. apply sign_ext_widen. lia.
Qed.

Theorem sign_ext_zero_ext:
  forall n x, 0 < n -> sign_ext n (zero_ext n x) = sign_ext n x.
Proof.
  intros. destruct (zlt n zwordsize).
  bit_solve.
  destruct (zlt i n).
  rewrite zlt_true; auto.
  rewrite zlt_true; auto. lia.
  destruct (zlt i n); lia.
  rewrite zero_ext_above; auto.
Qed.

Theorem zero_ext_sign_ext:
  forall n x, 0 < n -> zero_ext n (sign_ext n x) = zero_ext n x.
Proof.
  intros. apply zero_sign_ext_narrow. lia.
Qed.

Theorem sign_ext_equal_if_zero_equal:
  forall n x y, 0 < n ->
  zero_ext n x = zero_ext n y ->
  sign_ext n x = sign_ext n y.
Proof.
  intros. rewrite <- (sign_ext_zero_ext n x H).
  rewrite <- (sign_ext_zero_ext n y H). congruence.
Qed.

Theorem zero_ext_shru_shl:
  forall n x,
  0 < n < zwordsize ->
  let y := repr (zwordsize - n) in
  zero_ext n x = shru (shl x y) y.
Proof.
  intros.
  assert (unsigned y = zwordsize - n).
    unfold y. apply unsigned_repr. generalize wordsize_max_unsigned. lia.
  apply same_bits_eq; intros.
  rewrite bits_zero_ext.
  rewrite bits_shru; auto.
  destruct (zlt i n).
  rewrite zlt_true. rewrite bits_shl. rewrite zlt_false. f_equal. lia.
  lia. lia. lia.
  rewrite zlt_false. auto. lia.
  lia.
Qed.

Theorem sign_ext_shr_shl:
  forall n x,
  0 < n < zwordsize ->
  let y := repr (zwordsize - n) in
  sign_ext n x = shr (shl x y) y.
Proof.
  intros.
  assert (unsigned y = zwordsize - n).
    unfold y. apply unsigned_repr. generalize wordsize_max_unsigned. lia.
  apply same_bits_eq; intros.
  rewrite bits_sign_ext.
  rewrite bits_shr; auto.
  destruct (zlt i n).
  rewrite zlt_true. rewrite bits_shl. rewrite zlt_false. f_equal. lia.
  lia. lia. lia.
  rewrite zlt_false. rewrite bits_shl. rewrite zlt_false. f_equal. lia.
  lia. lia. lia. lia. lia.
Qed.

(** [zero_ext n x] is the unique integer congruent to [x] modulo [2^n]
    in the range [0...2^n-1]. *)

Lemma zero_ext_range:
  forall n x, 0 <= n < zwordsize -> 0 <= unsigned (zero_ext n x) < two_p n.
Proof.
  intros. rewrite zero_ext_mod; auto. apply Z_mod_lt. apply two_p_gt_ZERO. lia.
Qed.

Lemma eqmod_zero_ext:
  forall n x, 0 <= n < zwordsize -> eqmod (two_p n) (unsigned (zero_ext n x)) (unsigned x).
Proof.
  intros. rewrite zero_ext_mod; auto. apply eqmod_sym. apply eqmod_mod.
Qed.

(** [sign_ext n x] is the unique integer congruent to [x] modulo [2^n]
    in the range [-2^(n-1)...2^(n-1) - 1]. *)

Lemma sign_ext_range:
  forall n x, 0 < n < zwordsize -> -two_p (n-1) <= signed (sign_ext n x) < two_p (n-1).
Proof.
  intros. rewrite sign_ext_shr_shl; auto.
  set (X := shl x (repr (zwordsize - n))).
  assert (two_p (n - 1) > 0) by (apply two_p_gt_ZERO; lia).
  assert (unsigned (repr (zwordsize - n)) = zwordsize - n).
    apply unsigned_repr.
    split. lia. generalize wordsize_max_unsigned; lia.
  rewrite shr_div_two_p.
  rewrite signed_repr.
  rewrite H1.
  apply Zdiv_interval_1.
  lia. lia. apply two_p_gt_ZERO; lia.
  replace (- two_p (n - 1) * two_p (zwordsize - n))
     with (- (two_p (n - 1) * two_p (zwordsize - n))) by ring.
  rewrite <- two_p_is_exp.
  replace (n - 1 + (zwordsize - n)) with (zwordsize - 1) by lia.
  rewrite <- half_modulus_power.
  generalize (signed_range X). unfold min_signed, max_signed. lia.
  lia. lia.
  apply Zdiv_interval_2. apply signed_range.
  generalize min_signed_neg; lia.
  generalize max_signed_pos; lia.
  rewrite H1. apply two_p_gt_ZERO. lia.
Qed.

Lemma eqmod_sign_ext':
  forall n x, 0 < n < zwordsize ->
  eqmod (two_p n) (unsigned (sign_ext n x)) (unsigned x).
Proof.
  intros.
  set (N := Z.to_nat n).
  assert (Z.of_nat N = n) by (apply Z2Nat.id; lia).
  rewrite <- H0. rewrite <- two_power_nat_two_p.
  apply eqmod_same_bits; intros.
  rewrite H0 in H1. rewrite H0.
  fold (testbit (sign_ext n x) i). rewrite bits_sign_ext.
  rewrite zlt_true. auto. lia. lia. lia.
Qed.

Lemma eqmod_sign_ext:
  forall n x, 0 < n < zwordsize ->
  eqmod (two_p n) (signed (sign_ext n x)) (unsigned x).
Proof.
  intros. apply eqmod_trans with (unsigned (sign_ext n x)).
  apply eqmod_divides with modulus. apply eqm_signed_unsigned.
  exists (two_p (zwordsize - n)).
  unfold modulus. rewrite two_power_pos_two_p. fold zwordsize.
  rewrite <- two_p_is_exp. f_equal. lia. lia. lia.
  apply eqmod_sign_ext'; auto.
Qed.

(** ** Properties of [one_bits] (decomposition in sum of powers of two) *)

Theorem one_bits_range:
  forall x i, In i (one_bits x) -> ltu i iwordsize = true.
Proof.
  assert (A: forall p, 0 <= p < zwordsize -> ltu (repr p) iwordsize = true).
    intros. unfold ltu, iwordsize. apply zlt_true.
    repeat rewrite unsigned_repr. tauto.
    generalize wordsize_max_unsigned; lia.
    generalize wordsize_max_unsigned; lia.
  unfold one_bits. intros.
  destruct (list_in_map_inv _ _ _ H) as [i0 [EQ IN]].
  subst i. apply A. apply Z_one_bits_range with (unsigned x); auto.
Qed.

Fixpoint int_of_one_bits (l: list bit_int) : bit_int :=
  match l with
  | nil => zero
  | a :: b => add (shl one a) (int_of_one_bits b)
  end.

Theorem one_bits_decomp:
  forall x, x = int_of_one_bits (one_bits x).
Proof.
  intros.
  transitivity (repr (powerserie (Z_one_bits natwordsize (unsigned x) 0))).
  transitivity (repr (unsigned x)).
  auto with bit_ints. decEq. apply Z_one_bits_powerserie.
  auto with bit_ints.
  unfold one_bits.
  generalize (Z_one_bits_range (unsigned x)).
  generalize (Z_one_bits natwordsize (unsigned x) 0).
  induction l.
  intros; reflexivity.
  intros; simpl. rewrite <- IHl. unfold add. apply eqm_samerepr.
  apply eqm_add. rewrite shl_mul_two_p. rewrite mul_commut.
  rewrite mul_one. apply eqm_unsigned_repr_r.
  rewrite unsigned_repr. auto with bit_ints.
  generalize (H a (in_eq _ _)). generalize wordsize_max_unsigned. lia.
  auto with bit_ints.
  intros; apply H; auto with coqlib.
Qed.

(** ** Properties of comparisons *)

Theorem negate_cmp:
  forall c x y, cmp (negate_comparison c) x y = negb (cmp c x y).
Proof.
  intros. destruct c; simpl; try rewrite negb_elim; auto.
Qed.

Theorem negate_cmpu:
  forall c x y, cmpu (negate_comparison c) x y = negb (cmpu c x y).
Proof.
  intros. destruct c; simpl; try rewrite negb_elim; auto.
Qed.

Theorem swap_cmp:
  forall c x y, cmp (swap_comparison c) x y = cmp c y x.
Proof.
  intros. destruct c; simpl; auto. apply eq_sym. decEq. apply eq_sym.
Qed.

Theorem swap_cmpu:
  forall c x y, cmpu (swap_comparison c) x y = cmpu c y x.
Proof.
  intros. destruct c; simpl; auto. apply eq_sym. decEq. apply eq_sym.
Qed.

Lemma translate_eq:
  forall x y d,
  eq (add x d) (add y d) = eq x y.
Proof.
  intros. unfold eq. case (zeq (unsigned x) (unsigned y)); intro.
  unfold add. rewrite e. apply zeq_true.
  apply zeq_false. unfold add. red; intro. apply n.
  apply eqm_small_eq; auto with bit_ints.
  replace (unsigned x) with ((unsigned x + unsigned d) - unsigned d).
  replace (unsigned y) with ((unsigned y + unsigned d) - unsigned d).
  apply eqm_sub. apply eqm_trans with (unsigned (repr (unsigned x + unsigned d))).
  eauto with bit_ints. apply eqm_trans with (unsigned (repr (unsigned y + unsigned d))).
  eauto with bit_ints. eauto with bit_ints. eauto with bit_ints.
  lia. lia.
Qed.

Lemma translate_ltu:
  forall x y d,
  0 <= unsigned x + unsigned d <= max_unsigned ->
  0 <= unsigned y + unsigned d <= max_unsigned ->
  ltu (add x d) (add y d) = ltu x y.
Proof.
  intros. unfold add. unfold ltu.
  repeat rewrite unsigned_repr; auto. case (zlt (unsigned x) (unsigned y)); intro.
  apply zlt_true. lia.
  apply zlt_false. lia.
Qed.

Theorem translate_cmpu:
  forall c x y d,
  0 <= unsigned x + unsigned d <= max_unsigned ->
  0 <= unsigned y + unsigned d <= max_unsigned ->
  cmpu c (add x d) (add y d) = cmpu c x y.
Proof.
  intros. unfold cmpu.
  rewrite translate_eq. repeat rewrite translate_ltu; auto.
Qed.

Lemma translate_lt:
  forall x y d,
  min_signed <= signed x + signed d <= max_signed ->
  min_signed <= signed y + signed d <= max_signed ->
  lt (add x d) (add y d) = lt x y.
Proof.
  intros. repeat rewrite add_signed. unfold lt.
  repeat rewrite signed_repr; auto. case (zlt (signed x) (signed y)); intro.
  apply zlt_true. lia.
  apply zlt_false. lia.
Qed.

Theorem translate_cmp:
  forall c x y d,
  min_signed <= signed x + signed d <= max_signed ->
  min_signed <= signed y + signed d <= max_signed ->
  cmp c (add x d) (add y d) = cmp c x y.
Proof.
  intros. unfold cmp.
  rewrite translate_eq. repeat rewrite translate_lt; auto.
Qed.

Theorem notbool_isfalse_istrue:
  forall x, is_false x -> is_true (notbool x).
Proof.
  unfold is_false, is_true, notbool; intros; subst x.
  rewrite eq_true. apply one_not_zero.
Qed.

Theorem notbool_istrue_isfalse:
  forall x, is_true x -> is_false (notbool x).
Proof.
  unfold is_false, is_true, notbool; intros.
  generalize (eq_spec x zero). case (eq x zero); intro.
  contradiction. auto.
Qed.

Theorem ltu_range_test:
  forall x y,
  ltu x y = true -> unsigned y <= max_signed ->
  0 <= signed x < unsigned y.
Proof.
  intros.
  unfold ltu in H. destruct (zlt (unsigned x) (unsigned y)); try discriminate.
  rewrite signed_eq_unsigned.
  generalize (unsigned_range x). lia. lia.
Qed.

Theorem lt_sub_overflow:
  forall x y,
  xor (sub_overflow x y zero) (negative (sub x y)) = if lt x y then one else zero.
Proof.
  intros. unfold negative, sub_overflow, lt. rewrite sub_signed.
  rewrite signed_zero. rewrite Z.sub_0_r.
  generalize (signed_range x) (signed_range y).
  set (X := signed x); set (Y := signed y). intros RX RY.
  unfold min_signed, max_signed in *.
  generalize half_modulus_pos half_modulus_modulus; intros HM MM.
  destruct (zle 0 (X - Y)).
- unfold proj_sumbool at 1; rewrite zle_true at 1 by lia. simpl.
  rewrite (zlt_false _ X) by lia.
  destruct (zlt (X - Y) half_modulus).
  + unfold proj_sumbool; rewrite zle_true by lia.
    rewrite signed_repr. rewrite zlt_false by lia. apply xor_idem.
    unfold min_signed, max_signed; lia.
  + unfold proj_sumbool; rewrite zle_false by lia.
    replace (signed (repr (X - Y))) with (X - Y - modulus).
    rewrite zlt_true by lia. apply xor_idem.
    rewrite signed_repr_eq. replace ((X - Y) mod modulus) with (X - Y).
    rewrite zlt_false; auto.
    symmetry. apply Zmod_unique with 0; lia.
- unfold proj_sumbool at 2. rewrite zle_true at 1 by lia. rewrite andb_true_r.
  rewrite (zlt_true _ X) by lia.
  destruct (zlt (X - Y) (-half_modulus)).
  + unfold proj_sumbool; rewrite zle_false by lia.
    replace (signed (repr (X - Y))) with (X - Y + modulus).
    rewrite zlt_false by lia. apply xor_zero.
    rewrite signed_repr_eq. replace ((X - Y) mod modulus) with (X - Y + modulus).
    rewrite zlt_true by lia; auto.
    symmetry. apply Zmod_unique with (-1); lia.
  + unfold proj_sumbool; rewrite zle_true by lia.
    rewrite signed_repr. rewrite zlt_true by lia. apply xor_zero_l.
    unfold min_signed, max_signed; lia.
Qed.

Lemma signed_eq:
  forall x y, eq x y = zeq (signed x) (signed y).
Proof.
  intros. unfold eq. unfold proj_sumbool.
  destruct (zeq (unsigned x) (unsigned y));
  destruct (zeq (signed x) (signed y)); auto.
  elim n. unfold signed. rewrite e; auto.
  elim n. apply eqm_small_eq; auto with bit_ints.
  eapply eqm_trans. apply eqm_sym. apply eqm_signed_unsigned.
  rewrite e. apply eqm_signed_unsigned.
Qed.

Lemma not_lt:
  forall x y, negb (lt y x) = (lt x y || eq x y).
Proof.
  intros. unfold lt. rewrite signed_eq. unfold proj_sumbool.
  destruct (zlt (signed y) (signed x)).
  rewrite zlt_false. rewrite zeq_false. auto. lia. lia.
  destruct (zeq (signed x) (signed y)).
  rewrite zlt_false. auto. lia.
  rewrite zlt_true. auto. lia.
Qed.

Lemma lt_not:
  forall x y, lt y x = negb (lt x y) && negb (eq x y).
Proof.
  intros. rewrite <- negb_orb. rewrite <- not_lt. rewrite negb_involutive. auto.
Qed.

Lemma not_ltu:
  forall x y, negb (ltu y x) = (ltu x y || eq x y).
Proof.
  intros. unfold ltu, eq.
  destruct (zlt (unsigned y) (unsigned x)).
  rewrite zlt_false. rewrite zeq_false. auto. lia. lia.
  destruct (zeq (unsigned x) (unsigned y)).
  rewrite zlt_false. auto. lia.
  rewrite zlt_true. auto. lia.
Qed.

Lemma ltu_not:
  forall x y, ltu y x = negb (ltu x y) && negb (eq x y).
Proof.
  intros. rewrite <- negb_orb. rewrite <- not_ltu. rewrite negb_involutive. auto.
Qed.


(** Non-overlapping test *)

Definition no_overlap (ofs1: bit_int) (sz1: Z) (ofs2: bit_int) (sz2: Z) : bool :=
  let x1 := unsigned ofs1 in let x2 := unsigned ofs2 in
     zlt (x1 + sz1) modulus && zlt (x2 + sz2) modulus
  && (zle (x1 + sz1) x2 || zle (x2 + sz2) x1).

Lemma no_overlap_sound:
  forall ofs1 sz1 ofs2 sz2 base,
  sz1 > 0 -> sz2 > 0 -> no_overlap ofs1 sz1 ofs2 sz2 = true ->
  unsigned (add base ofs1) + sz1 <= unsigned (add base ofs2)
  \/ unsigned (add base ofs2) + sz2 <= unsigned (add base ofs1).
Proof.
  intros.
  destruct (andb_prop _ _ H1). clear H1.
  destruct (andb_prop _ _ H2). clear H2.
  apply proj_sumbool_true in H1.
  apply proj_sumbool_true in H4.
  assert (unsigned ofs1 + sz1 <= unsigned ofs2 \/ unsigned ofs2 + sz2 <= unsigned ofs1).
  destruct (orb_prop _ _ H3). left. eapply proj_sumbool_true; eauto. right. eapply proj_sumbool_true; eauto.
  clear H3.
  generalize (unsigned_range ofs1) (unsigned_range ofs2). intros P Q.
  generalize (unsigned_add_either base ofs1) (unsigned_add_either base ofs2).
  intros [C|C] [D|D]; lia.
Qed.

(** Size of integers, in bits. *)

Definition Zsize (x: Z) : Z :=
  match x with
  | Zpos p => Zpos (Pos.size p)
  | _ => 0
  end.

Definition size (x: bit_int) : Z := Zsize (unsigned x).

Remark Zsize_pos: forall x, 0 <= Zsize x.
Proof.
  destruct x; simpl. lia. compute; intuition congruence. lia.
Qed.

Remark Zsize_pos': forall x, 0 < x -> 0 < Zsize x.
Proof.
  destruct x; simpl; intros; try discriminate. compute; auto.
Qed.

Lemma Zsize_shiftin:
  forall b x, 0 < x -> Zsize (Zshiftin b x) = Z.succ (Zsize x).
Proof.
  intros. destruct x; compute in H; try discriminate.
  destruct b.
  change (Zshiftin true (Zpos p)) with (Zpos (p~1)).
  simpl. f_equal. rewrite Pos.add_1_r; auto.
  change (Zshiftin false (Zpos p)) with (Zpos (p~0)).
  simpl. f_equal. rewrite Pos.add_1_r; auto.
Qed.

Lemma Ztestbit_size_1:
  forall x, 0 < x -> Z.testbit x (Z.pred (Zsize x)) = true.
Proof.
  intros x0 POS0; pattern x0; apply Zshiftin_pos_ind; auto.
  intros. rewrite Zsize_shiftin; auto.
  replace (Z.pred (Z.succ (Zsize x))) with (Z.succ (Z.pred (Zsize x))) by lia.
  rewrite Ztestbit_shiftin_succ. auto. generalize (Zsize_pos' x H); lia.
Qed.

Lemma Ztestbit_size_2:
  forall x, 0 <= x -> forall i, i >= Zsize x -> Z.testbit x i = false.
Proof.
  intros x0 POS0. destruct (zeq x0 0).
  - subst x0; intros. apply Ztestbit_0.
  - pattern x0; apply Zshiftin_pos_ind.
    + simpl. intros. change 1 with (Zshiftin true 0). rewrite Ztestbit_shiftin.
      rewrite zeq_false. apply Ztestbit_0. lia. lia.
    + intros. rewrite Zsize_shiftin in H1; auto.
      generalize (Zsize_pos' _ H); intros.
      rewrite Ztestbit_shiftin. rewrite zeq_false. apply H0. lia.
      lia. lia.
    + lia.
Qed.

Lemma Zsize_interval_1:
  forall x, 0 <= x -> 0 <= x < two_p (Zsize x).
Proof.
  intros.
  assert (x = x mod (two_p (Zsize x))).
    apply equal_same_bits; intros.
    rewrite Ztestbit_mod_two_p; auto.
    destruct (zlt i (Zsize x)). auto. apply Ztestbit_size_2; auto.
    apply Zsize_pos; auto.
  rewrite H0 at 1. rewrite H0 at 3. apply Z_mod_lt. apply two_p_gt_ZERO. apply Zsize_pos; auto.
Qed.

Lemma Zsize_interval_2:
  forall x n, 0 <= n -> 0 <= x < two_p n -> n >= Zsize x.
Proof.
  intros. set (N := Z.to_nat n).
  assert (Z.of_nat N = n) by (apply Z2Nat.id; auto).
  rewrite <- H1 in H0. rewrite <- two_power_nat_two_p in H0.
  destruct (zeq x 0).
  subst x; simpl; lia.
  destruct (zlt n (Zsize x)); auto.
  exploit (Ztestbit_above N x (Z.pred (Zsize x))). auto. lia.
  rewrite Ztestbit_size_1. congruence. lia.
Qed.

Lemma Zsize_monotone:
  forall x y, 0 <= x <= y -> Zsize x <= Zsize y.
Proof.
  intros. apply Z.ge_le. apply Zsize_interval_2. apply Zsize_pos.
  exploit (Zsize_interval_1 y). lia.
  lia.
Qed.

Theorem size_zero: size zero = 0.
Proof.
  unfold size; rewrite unsigned_zero; auto.
Qed.

Theorem bits_size_1:
  forall x, x = zero \/ testbit x (Z.pred (size x)) = true.
Proof.
  intros. destruct (zeq (unsigned x) 0).
  left. rewrite <- (repr_unsigned x). rewrite e; auto.
  right. apply Ztestbit_size_1. generalize (unsigned_range x); lia.
Qed.

Theorem bits_size_2:
  forall x i, size x <= i -> testbit x i = false.
Proof.
  intros. apply Ztestbit_size_2. generalize (unsigned_range x); lia.
  fold (size x); lia.
Qed.

Theorem size_range:
  forall x, 0 <= size x <= zwordsize.
Proof.
  intros; split. apply Zsize_pos.
  destruct (bits_size_1 x).
  subst x; unfold size; rewrite unsigned_zero; simpl. generalize wordsize_pos; lia.
  destruct (zle (size x) zwordsize); auto.
  rewrite bits_above in H. congruence. lia.
Qed.

Theorem bits_size_3:
  forall x n,
  0 <= n ->
  (forall i, n <= i < zwordsize -> testbit x i = false) ->
  size x <= n.
Proof.
  intros. destruct (zle (size x) n). auto.
  destruct (bits_size_1 x).
  subst x. unfold size; rewrite unsigned_zero; assumption.
  rewrite (H0 (Z.pred (size x))) in H1. congruence.
  generalize (size_range x); lia.
Qed.

Theorem bits_size_4:
  forall x n,
  0 <= n ->
  testbit x (Z.pred n) = true ->
  (forall i, n <= i < zwordsize -> testbit x i = false) ->
  size x = n.
Proof.
  intros.
  assert (size x <= n).
    apply bits_size_3; auto.
  destruct (zlt (size x) n).
  rewrite bits_size_2 in H0. congruence. lia.
  lia.
Qed.

Theorem size_interval_1:
  forall x, 0 <= unsigned x < two_p (size x).
Proof.
  intros; apply Zsize_interval_1. generalize (unsigned_range x); lia.
Qed.

Theorem size_interval_2:
  forall x n, 0 <= n -> 0 <= unsigned x < two_p n -> n >= size x.
Proof.
  intros. apply Zsize_interval_2; auto.
Qed.

Theorem size_and:
  forall a b, size (and a b) <= Z.min (size a) (size b).
Proof.
  intros.
  assert (0 <= Z.min (size a) (size b)).
    generalize (size_range a) (size_range b). zify; lia.
  apply bits_size_3. auto. intros.
  rewrite bits_and. zify. subst. destruct H1.
  rewrite (bits_size_2 a). auto. lia.
  rewrite (bits_size_2 b). apply andb_false_r. lia.
  lia.
Qed.

Corollary and_interval:
  forall a b, 0 <= unsigned (and a b) < two_p (Z.min (size a) (size b)).
Proof.
  intros.
  generalize (size_interval_1 (and a b)); intros.
  assert (two_p (size (and a b)) <= two_p (Z.min (size a) (size b))).
  apply two_p_monotone. split. generalize (size_range (and a b)); lia.
  apply size_and.
  lia.
Qed.

Theorem size_or:
  forall a b, size (or a b) = Z.max (size a) (size b).
Proof.
  intros. generalize (size_range a) (size_range b); intros.
  destruct (bits_size_1 a).
  subst a. rewrite size_zero. rewrite or_zero_l. zify; lia.
  destruct (bits_size_1 b).
  subst b. rewrite size_zero. rewrite or_zero. zify; lia.
  zify. destruct H3 as [[P Q] | [P Q]]; subst.
  apply bits_size_4. tauto. rewrite bits_or. rewrite H2. apply orb_true_r.
  lia.
  intros. rewrite bits_or. rewrite !bits_size_2. auto. lia. lia. lia.
  apply bits_size_4. tauto. rewrite bits_or. rewrite H1. apply orb_true_l.
  destruct (zeq (size a) 0). unfold testbit in H1. rewrite Z.testbit_neg_r in H1.
  congruence. lia. lia.
  intros. rewrite bits_or. rewrite !bits_size_2. auto. lia. lia. lia.
Qed.

Corollary or_interval:
  forall a b, 0 <= unsigned (or a b) < two_p (Z.max (size a) (size b)).
Proof.
  intros. rewrite <- size_or. apply size_interval_1.
Qed.

Theorem size_xor:
  forall a b, size (xor a b) <= Z.max (size a) (size b).
Proof.
  intros.
  assert (0 <= Z.max (size a) (size b)).
    generalize (size_range a) (size_range b). zify; lia.
  apply bits_size_3. auto. intros.
  rewrite bits_xor. rewrite !bits_size_2. auto.
  zify; lia.
  zify; lia.
  lia.
Qed.

Corollary xor_interval:
  forall a b, 0 <= unsigned (xor a b) < two_p (Z.max (size a) (size b)).
Proof.
  intros.
  generalize (size_interval_1 (xor a b)); intros.
  assert (two_p (size (xor a b)) <= two_p (Z.max (size a) (size b))).
  apply two_p_monotone. split. generalize (size_range (xor a b)); lia.
  apply size_xor.
  lia.
Qed.
End MakeInt.

(** Decomposing 64-bit ints as pairs of 32-bit ints *)

Definition loword (n: @bit_int 64) : @bit_int 32 := repr (unsigned n).

Definition hiword (n: @bit_int 64) : @bit_int 32 := repr (unsigned (shru n (repr 32))).

Definition ofwords (hi lo: @bit_int 32) : @bit_int 64 :=
  or (shl (repr (unsigned hi)) (repr 32)) (repr (unsigned lo)).

Lemma bits_loword:
  forall n i, 0 <= i < 32 -> @testbit 32 (loword n) i = @testbit 64 n i.
Proof.
  intros. unfold loword. rewrite testbit_repr; auto.
Qed.

Lemma bits_hiword:
  forall n i, 0 <= i < 32 -> @testbit 32 (hiword n) i = @testbit 64 n (i + 32).
Proof.
  intros. unfold hiword. rewrite testbit_repr; auto.
  assert (64 = 2 * 32) by reflexivity.
  fold (@testbit 64 (@shru 64 n (@repr 64 32)) i). rewrite bits_shru;
  unfold zwordsize.
  change (unsigned (@repr 64 32)) with 32.
  apply zlt_true. lia. lia.
Qed.

Lemma bits_ofwords:
  forall hi lo i,
    0 <= i < 64 ->
    @testbit 64 (ofwords hi lo) i =
      if zlt i 32 then @testbit 32 lo i else @testbit 32 hi (i - 32).
Proof.
  intros. unfold ofwords. rewrite bits_or; auto. rewrite bits_shl; auto.
  change (unsigned (@repr 64 32)) with 32.
  assert (64 = 2 * 32) by reflexivity.
  destruct (zlt i 32).
  rewrite testbit_repr; auto.
  rewrite !testbit_repr; auto.
  fold (@testbit 32 lo i). rewrite bits_above. apply orb_false_r. auto.
  unfold zwordsize.
  lia.
Qed.

Lemma lo_ofwords:
  forall hi lo, loword (ofwords hi lo) = lo.
Proof.
  intros. apply same_bits_eq; intros.
  unfold zwordsize in H.
  rewrite bits_loword; auto. rewrite bits_ofwords. apply zlt_true. lia.
  lia.
Qed.

Lemma hi_ofwords:
  forall hi lo, hiword (ofwords hi lo) = hi.
Proof.
  intros. apply same_bits_eq; intros.
  rewrite bits_hiword; auto. rewrite bits_ofwords.
  rewrite zlt_false. f_equal. lia. lia.
  unfold zwordsize in *; lia.
Qed.

Lemma ofwords_recompose:
  forall n, ofwords (hiword n) (loword n) = n.
Proof.
  intros. apply same_bits_eq; intros. rewrite bits_ofwords; auto.
  destruct (zlt i 32).
  apply bits_loword. lia.
  rewrite bits_hiword. f_equal. lia.
  unfold zwordsize in *. lia.
Qed.

Lemma ofwords_add:
  forall lo hi, ofwords hi lo = @repr 64 (@unsigned 32 hi * two_p 32 + @unsigned 32 lo).
Proof.
  intros. unfold ofwords. rewrite shifted_or_is_add.
  apply eqm_samerepr. apply eqm_add. apply eqm_mult.
  apply eqm_sym; apply eqm_unsigned_repr.
  apply eqm_refl.
  apply eqm_sym; apply eqm_unsigned_repr.
  unfold zwordsize. lia.
  rewrite unsigned_repr. generalize (@unsigned_range 32 lo). intros [A B]. exact B.
  assert (@max_unsigned 32 < @max_unsigned 64) by (compute; auto).
  generalize (@unsigned_range_2 32 lo); lia.
Qed.

Lemma ofwords_add':
  forall lo hi, unsigned (ofwords hi lo) = unsigned hi * two_p 32 + unsigned lo.
Proof.
  intros. rewrite ofwords_add. apply unsigned_repr.
  generalize (@unsigned_range 32 hi) (@unsigned_range 32 lo).
  change (two_p 32) with (@modulus 32).
  change (@modulus 32) with 4294967296.
  change (max_unsigned) with 18446744073709551615.
  lia.
Qed.

Remark eqm_mul_2p32:
  forall x y, @eqm 32 x y -> @eqm 64 (x * two_p 32) (y * two_p 32).
Proof.
  intros. destruct H as [k EQ]. exists k. rewrite EQ.
  change (@modulus 32) with (two_p 32) in *.
  change (@modulus 64) with (two_p 32 * two_p 32).
  ring.
Qed.

Lemma ofwords_add'':
  forall lo hi, @signed 64 (ofwords hi lo) = @signed 32 hi * two_p 32 + @unsigned 32 lo.
Proof.
  intros. rewrite ofwords_add.
  replace (@repr 64 (unsigned hi * two_p 32 + unsigned lo))
     with (@repr 64 (signed hi * two_p 32 + unsigned lo)).
  apply signed_repr.
  generalize (@signed_range 32 hi) (@unsigned_range 32 lo).
  change (two_p 32) with (@modulus 32).
  change (@min_signed 64) with (@min_signed 32 * @modulus 32).
  change (@max_signed 64) with (@max_signed 32 * @modulus 32 + @modulus 32 - 1).
  change (@modulus 32) with 4294967296.
  lia.
  apply eqm_samerepr. apply eqm_add. apply eqm_mul_2p32. apply eqm_signed_unsigned. apply eqm_refl.
Qed.

#[global] Hint Resolve modulus_pos: bit_ints.
#[global] Hint Resolve eqm_refl: bit_ints.
#[global] Hint Resolve eqm_refl2: bit_ints.
#[global] Hint Resolve eqm_sym: bit_ints.
#[global] Hint Resolve eqm_trans: bit_ints.
#[global] Hint Resolve eqm_small_eq: bit_ints.
#[global] Hint Resolve eqm_add: bit_ints.
#[global] Hint Resolve eqm_neg: bit_ints.
#[global] Hint Resolve eqm_sub: bit_ints.
#[global] Hint Resolve eqm_mult: bit_ints.
#[global] Hint Resolve eqm_unsigned_repr: bit_ints.
#[global] Hint Resolve eqm_unsigned_repr_l: bit_ints.
#[global] Hint Resolve eqm_unsigned_repr_r: bit_ints.
#[global] Hint Resolve unsigned_range: bit_ints.
#[global] Hint Resolve unsigned_range_2: bit_ints.
#[global] Hint Resolve repr_unsigned: bit_ints.
#[global] Hint Resolve repr_signed: bit_ints.
#[global] Hint Resolve unsigned_repr: bit_ints.
#[global] Hint Rewrite @bits_zero @bits_mone : bit_ints.
#[global] Hint Rewrite @bits_and @bits_or @bits_xor @bits_not: bit_ints.
#[global] Hint Rewrite @bits_shl @bits_shru @bits_shr: bit_ints.
#[global] Hint Rewrite @bits_rol @bits_ror: bit_ints.
#[global] Hint Rewrite @bits_zero_ext @bits_sign_ext: bit_ints.

Ltac bit_solve :=
  intros; apply same_bits_eq; intros; autorewrite with bit_ints; auto with bool.
