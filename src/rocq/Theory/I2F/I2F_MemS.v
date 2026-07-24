From Vellvm Require Import
  Utils
  Semantics.EOU
  Semantics.Interfaces.Memory.

From Vellvm Require Import
  Theory.I2F.Refinement.

(** * Relating computations in the [memS] free monad

    [memS S A P X] (see [Semantics/Interfaces/Memory.v]) is the free monad
    underlying [memM]: a finite tree of [Mret]/[Merr]/[Mub]/[Moom] leaves,
    [Mget]/[Mput] state-access nodes, and [Mchoose] non-deterministic
    oracle nodes. [I2F_memS] relates such trees between two
    instantiations sharing the same choice/provenance type [P] (the two
    memory models always do: [P] is the single, IPtr-independent
    [provenance] type), generalizing [I2F_EOU] (see [Refinement.v]) with
    the extra constructors:
    - [Mget]/[Mput] thread a state relation [RS] pointwise;
    - [Mchoose] keeps the SAME choice [c] on both sides and demands the
      continuations be related at every possible answer. This is sound
      here because the two sides always run the same generic code
      ([Implementations/Memory.v]), so [Mchoose] nodes occur in lockstep;
      and because any two [I2F_State]-related states force equal
      resolutions of a given choice (see [I2F_memory.v]), relating
      continuations pointwise at ALL answers is not stronger than
      relating them only at the answers that could actually arise.
*)

Section I2F_MemS.
  Context {S1 S2 A1 A2 P : Type}.

  Inductive I2F_memS {X1 X2} (RS : S1 -> S2 -> Prop) (RR : X1 -> X2 -> Prop)
    : memS S1 A1 P X1 -> memS S2 A2 P X2 -> Prop :=
  | I2F_Mret  x1 x2 : RR x1 x2 -> I2F_memS RS RR (Mret x1) (Mret x2)
  | I2F_Merr  s1 s2 : I2F_memS RS RR (Merr s1) (Merr s2)
  | I2F_Mub_l s m2  : I2F_memS RS RR (Mub s) m2
  | I2F_Moom_r m1 s : I2F_memS RS RR m1 (Moom s)
  | I2F_Mget  k1 k2 :
      (forall σ1 σ2, RS σ1 σ2 -> I2F_memS RS RR (k1 σ1) (k2 σ2)) ->
      I2F_memS RS RR (Mget k1) (Mget k2)
  | I2F_Mput  σ1 σ2 k1 k2 :
      RS σ1 σ2 ->
      I2F_memS RS RR k1 k2 ->
      I2F_memS RS RR (Mput σ1 k1) (Mput σ2 k2)
  | I2F_Mchoose c k1 k2 :
      (forall a : @memCType P c, I2F_memS RS RR (k1 a) (k2 a)) ->
      I2F_memS RS RR (Mchoose c k1) (Mchoose c k2)
  .

  (** [I2F_memS] is monotone in its result relation. *)
  Lemma I2F_memS_mono {X1 X2} (RS : S1 -> S2 -> Prop) (RR RR' : X1 -> X2 -> Prop)
    (m1 : memS S1 A1 P X1) (m2 : memS S2 A2 P X2) :
    (forall x1 x2, RR x1 x2 -> RR' x1 x2) ->
    I2F_memS RS RR m1 m2 -> I2F_memS RS RR' m1 m2.
  Proof.
    intros SUB H; induction H; try solve [constructor; auto].
  Qed.

  (** Pure [EOU] computations lift into [memS] uniformly in the state
      relation: [lift] never touches the state or the choice oracle. *)
  Lemma I2F_memS_lift {X1 X2} (RS : S1 -> S2 -> Prop) (RR : X1 -> X2 -> Prop)
    (m1 : EOU X1) (m2 : EOU X2) :
    I2F_EOU RR m1 m2 -> I2F_memS RS RR (lift m1) (lift m2).
  Proof.
    intros H; destruct H; cbn; constructor; auto.
  Qed.

  (** Compatibility of [I2F_memS] with the monadic structure of [memS]. *)
  Lemma I2F_memS_bind {X1 X2 Y1 Y2} (RS : S1 -> S2 -> Prop)
    (RX : X1 -> X2 -> Prop) (RY : Y1 -> Y2 -> Prop)
    (m1 : memS S1 A1 P X1) (m2 : memS S2 A2 P X2)
    (k1 : X1 -> memS S1 A1 P Y1) (k2 : X2 -> memS S2 A2 P Y2) :
    I2F_memS RS RX m1 m2 ->
    (forall x1 x2, RX x1 x2 -> I2F_memS RS RY (k1 x1) (k2 x2)) ->
    I2F_memS RS RY (memS_bind m1 k1) (memS_bind m2 k2).
  Proof.
    intros H HK; induction H; cbn.
    - apply HK; auto.
    - constructor.
    - constructor.
    - constructor.
    - constructor; intros σ1 σ2 Hσ; eauto.
    - constructor; auto.
    - constructor; intros a; eauto.
  Qed.

  Lemma I2F_memS_get (RS : S1 -> S2 -> Prop) :
    I2F_memS RS RS get get.
  Proof.
    unfold get.
    constructor; intros σ1 σ2 Hσ; constructor; auto.
  Qed.

  Lemma I2F_memS_put (RS : S1 -> S2 -> Prop) (σ1 : S1) (σ2 : S2) :
    RS σ1 σ2 ->
    I2F_memS RS (fun (_ _ : unit) => True) (put σ1) (put σ2).
  Proof.
    intros Hσ; unfold put; constructor; auto; constructor; auto.
  Qed.

  Lemma I2F_memS_next_key (RS : S1 -> S2 -> Prop) (size align : N) :
    I2F_memS RS (@Logic.eq Z) (next_key size align) (next_key size align).
  Proof.
    unfold next_key, Mnext_key.
    constructor; intros a; constructor; auto.
  Qed.

  Lemma I2F_memS_fresh_prov (RS : S1 -> S2 -> Prop) :
    I2F_memS RS (@Logic.eq P) (fresh_prov tt) (fresh_prov tt).
  Proof.
    unfold fresh_prov, Mfresh_prov.
    constructor; intros p; constructor; auto.
  Qed.

  Lemma I2F_memS_exposed_prov (RS : S1 -> S2 -> Prop) :
    I2F_memS RS (@Logic.eq (option P)) (exposed_prov tt) (exposed_prov tt).
  Proof.
    unfold exposed_prov, Mexposed_prov.
    constructor; intros p; constructor; auto.
  Qed.

  (** [I2F_memS_bind] generalized to two [Forall2]-related lists
      (the [memS] analogue of [I2F_EOU_map_monad2]). *)
  Lemma I2F_memS_map_monad2 {X1 X2 Y1 Y2} (RS : S1 -> S2 -> Prop)
    (RX : X1 -> X2 -> Prop) (RY : Y1 -> Y2 -> Prop)
    (f1 : X1 -> memS S1 A1 P Y1) (f2 : X2 -> memS S2 A2 P Y2) :
    forall l1 l2,
      Forall2 RX l1 l2 ->
      (forall x1 x2, RX x1 x2 -> I2F_memS RS RY (f1 x1) (f2 x2)) ->
      I2F_memS RS (Forall2 RY) (map_monad f1 l1) (map_monad f2 l2).
  Proof.
    intros l1 l2 F HF; induction F; cbn.
    - do 2 constructor.
    - eapply I2F_memS_bind; [now apply HF |].
      intros y1 y2 HY.
      eapply I2F_memS_bind; [apply IHF |].
      intros ys1 ys2 HYS.
      do 2 constructor; auto.
  Qed.

  (** The tail-recursive, accumulator-passing sibling of [map_monad]
      (used by [get_consecutive_ptrs]/[read_bytes]); see
      [I2F_EOU_map_monad_acc2] for the accumulator-invariant idiom this
      mirrors. *)
  Lemma I2F_memS_map_monad_acc2 {X1 X2 Y1 Y2} (RS : S1 -> S2 -> Prop)
    (RX : X1 -> X2 -> Prop) (RY : Y1 -> Y2 -> Prop)
    (f1 : X1 -> memS S1 A1 P Y1) (f2 : X2 -> memS S2 A2 P Y2) :
    forall l1 l2,
      Forall2 RX l1 l2 ->
      (forall x1 x2, RX x1 x2 -> I2F_memS RS RY (f1 x1) (f2 x2)) ->
      I2F_memS RS (Forall2 RY) (map_monad_acc f1 l1) (map_monad_acc f2 l2).
  Proof.
    intros l1 l2 F HF.
    unfold map_monad_acc.
    assert (H : forall xs1 xs2, Forall2 RX xs1 xs2 -> forall acc1 acc2,
               I2F_memS RS
                 (fun r1 r2 =>
                    exists bs1 bs2,
                      r1 = rev_append acc1 bs1 /\
                      r2 = rev_append acc2 bs2 /\
                      Forall2 RY bs1 bs2)
                 ((fix loop acc l :=
                     match l with
                     | [] => ret (rev_append acc [])
                     | a::l' => b <- f1 a;; loop (b::acc) l'
                     end) acc1 xs1)
                 ((fix loop acc l :=
                     match l with
                     | [] => ret (rev_append acc [])
                     | a::l' => b <- f2 a;; loop (b::acc) l'
                     end) acc2 xs2)).
    { intros xs1 xs2 FA; induction FA as [| x1 x2 xs1 xs2 Rx FA' IH]; intros acc1 acc2; cbn.
      - constructor.
        exists [], []; auto.
      - eapply I2F_memS_bind; [now apply HF |].
        intros b1 b2 HB.
        eapply I2F_memS_mono; [| apply (IH (b1::acc1) (b2::acc2))].
        intros r1 r2 (bs1 & bs2 & -> & -> & HBS).
        exists (b1::bs1), (b2::bs2); auto.
    }
    eapply I2F_memS_mono; [| apply (H l1 l2 F [] [])].
    intros r1 r2 (bs1 & bs2 & -> & -> & HBS); auto.
  Qed.

  (** The value-discarding analogue of [map_monad2], for [write_bytes]'s
      use of [loop_monad]. *)
  Lemma I2F_memS_loop_monad2 {X1 X2} (RS : S1 -> S2 -> Prop) (RX : X1 -> X2 -> Prop)
    (f1 : X1 -> memS S1 A1 P unit) (f2 : X2 -> memS S2 A2 P unit) :
    forall l1 l2,
      Forall2 RX l1 l2 ->
      (forall x1 x2, RX x1 x2 -> I2F_memS RS (fun (_ _ : unit) => True) (f1 x1) (f2 x2)) ->
      I2F_memS RS (fun (_ _ : unit) => True) (loop_monad f1 l1) (loop_monad f2 l2).
  Proof.
    intros l1 l2 F HF; induction F; cbn.
    - do 2 constructor.
    - eapply I2F_memS_bind; [now apply HF |].
      intros _ _ _; auto.
  Qed.

End I2F_MemS.

#[export] Hint Constructors I2F_memS : core.
