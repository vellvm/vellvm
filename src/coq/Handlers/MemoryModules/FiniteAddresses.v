From Coq Require Import
  Lia
  Morphisms.

From Vellvm Require Import
  Numeric.Coqlib
  Utils.Error.

From Vellvm.Semantics Require Import
  MemoryAddress
  Memory.FiniteProvenance
  VellvmIntegers.

From QuickChick Require Import Show.

From ExtLib Require Import
  Structures.Functor
  Structures.Monads.

Import ListNotations.

(** ** Type of pointers
    Implementation of the notion of pointer used: an address and an offset.
 *)
Definition Iptr := int64. (* Integer pointer type (physical addresses) *)

(* TODO: Should probably make this an NSet, but it gives universe inconsistency with Module addr *)
Definition Prov := option (list Provenance). (* Provenance *)

Definition wildcard_prov : Prov := None.
Definition nil_prov : Prov := Some [].

(* TODO: If Prov is an NSet, I get a universe inconsistency here... *)
Module FinAddr : MemoryAddress.ADDRESS
with Definition addr := (Iptr * Prov) % type
with Definition null := (@Integers.zero 64, nil_prov)%Z.
  Definition addr := (Iptr * Prov) % type.
  Definition null : addr := (@Integers.zero 64, nil_prov)%Z.

  (* TODO: is this what we should be using for equality on pointers? Probably *NOT* because of provenance. *)
  Lemma eq_dec : forall (a b : addr), {a = b} + {a <> b}.
  Proof.
    intros [a1 a2] [b1 b2].

    destruct (Integers.eq_dec a1 b1);
      destruct (option_eq (fun x y => list_eq_dec N.eq_dec x y) a2 b2); subst.
    - left; reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
  Qed.

  Lemma different_addrs :
    forall (a : addr), exists (b : addr), a <> b.
  Proof.
    intros a.
    destruct a.
    destruct i.
    destruct intval.
    - exists (@Integers.one 64, p).
      intros CONTRA; inversion CONTRA.
    - exists (@Integers.zero 64, p).
      intros CONTRA; inversion CONTRA.
    - exists (@Integers.one 64, p).
      intros CONTRA; inversion CONTRA.
  Qed.

  Definition show_addr (a : addr) :=
    match a with
    | (i, p) =>
        Show.show (unsigned i, p)
    end.
End FinAddr.

Module FinPTOI : PTOI(FinAddr)
with Definition ptr_to_int := fun (ptr : FinAddr.addr) => Integers.unsigned (fst ptr).
  Definition ptr_to_int := fun (ptr : FinAddr.addr) => Integers.unsigned (fst ptr).
End FinPTOI.

Module FinPROV <: PROVENANCE(FinAddr)
with Definition Prov := Prov
with Definition address_provenance
    := fun (a : FinAddr.addr) => snd a
with Definition Provenance := Provenance
with Definition AllocationId := AllocationId
with Definition wildcard_prov := wildcard_prov
with Definition nil_prov := nil_prov
with Definition initial_provenance := 0%N
with Definition provenance_to_prov := fun (pr : Provenance) => Some [pr]
with Definition access_allowed := fun (pr : Prov) (aid : AllocationId)
    => match pr with
       | None => true (* Wildcard can access anything. *)
       | Some prset =>
         match aid with
         | None => true (* Wildcard, can be accessed by anything. *)
         | Some aid =>
           existsb (N.eqb aid) prset
         end
       end.  

  Definition Provenance := Provenance.
  Definition AllocationId := AllocationId.
  Definition Prov := Prov.
  Definition wildcard_prov : Prov := wildcard_prov.
  Definition nil_prov : Prov := nil_prov.
  Definition address_provenance (a : FinAddr.addr) : Prov
    := snd a.

  (* Does the provenance set pr allow for access to aid? *)
  Definition access_allowed (pr : Prov) (aid : AllocationId) : bool
    := match pr with
       | None => true (* Wildcard can access anything. *)
       | Some prset =>
         match aid with
         | None => true (* Wildcard, can be accessed by anything. *)
         | Some aid =>
           existsb (N.eqb aid) prset
         end
       end.

  Definition aid_access_allowed (pr : AllocationId) (aid : AllocationId) : bool
    := match pr with
       | None => true
       | Some pr =>
         match aid with
         | None => true
         | Some aid =>
           N.eqb pr aid
         end
       end.

  Definition allocation_id_to_prov (aid : AllocationId) : Prov
    := fmap (fun x => [x]) aid.

  Definition provenance_to_allocation_id (pr : Provenance) : AllocationId
    := Some pr.

  Definition provenance_to_prov (pr : Provenance) : Prov
    := Some [pr].

  Definition next_provenance (pr : Provenance) : Provenance
    := N.succ pr.

  Definition initial_provenance : Provenance
    := 0%N.

  Definition provenance_lt (p1 p2 : Provenance) : Prop
    := N.lt p1 p2.

  Lemma aid_access_allowed_refl :
    forall aid, aid_access_allowed aid aid = true.
  Proof.
    intros aid.
    unfold aid_access_allowed.
    destruct aid; auto.
    rewrite N.eqb_refl.
    auto.
  Qed.

  Lemma access_allowed_refl :
    forall aid,
      access_allowed (allocation_id_to_prov aid) aid = true.
  Proof.
    intros aid.
    unfold access_allowed.
    cbn.
    destruct aid; auto.
    cbn.
    rewrite N.eqb_refl.
    cbn.
    auto.
  Qed.

  Lemma allocation_id_to_prov_inv:
    forall aid aid',
      allocation_id_to_prov aid = allocation_id_to_prov aid' ->
      aid = aid'.
  Proof.
    intros aid aid' H.
    unfold allocation_id_to_prov in *.
    cbn in *.
    destruct aid, aid'; inv H; auto.
  Qed.

  Lemma provenance_to_allocation_id_inv :
    forall pr pr',
      provenance_to_allocation_id pr = provenance_to_allocation_id pr' ->
      pr = pr'.
  Proof.
    intros pr pr' H.
    unfold provenance_to_allocation_id in *.
    inv H; auto.
  Qed.

  Lemma allocation_id_to_prov_provenance_to_allocation_id :
    forall pr,
      allocation_id_to_prov (provenance_to_allocation_id pr) = provenance_to_prov pr.
  Proof.
    intros pr.
    cbn.
    auto.
  Qed.

  Lemma provenance_eq_dec :
    forall (pr pr' : Provenance),
      {pr = pr'} + {pr <> pr'}.
  Proof.
    unfold Provenance.
    unfold FiniteProvenance.Provenance.
    intros pr pr'.
    apply N.eq_dec.
  Defined.

  Lemma provenance_eq_dec_refl :
    forall (pr : Provenance),
      true = provenance_eq_dec pr pr.
  Proof.
    intros pr.
    destruct provenance_eq_dec; cbn; auto.
    exfalso; auto.
  Qed.

  Lemma aid_eq_dec :
    forall (aid aid' : AllocationId),
      {aid = aid'} + {aid <> aid'}.
  Proof.
    intros aid aid'.
    destruct aid, aid'; auto.
    pose proof provenance_eq_dec p p0.
    destruct H; subst; auto.
    right.
    intros CONTRA. inv CONTRA; contradiction.
    right; intros CONTRA; inv CONTRA.
    right; intros CONTRA; inv CONTRA.
  Qed.

  Lemma aid_eq_dec_refl :
    forall (aid : AllocationId),
      true = aid_eq_dec aid aid.
  Proof.
    intros aid.
    destruct (aid_eq_dec aid aid); cbn; auto.
    exfalso; auto.
  Qed.

  #[global] Instance access_allowed_Proper :
    Proper (eq ==> (fun aid aid' => true = (aid_eq_dec aid aid')) ==> eq) access_allowed.
  Proof.
    unfold Proper, respectful.
    intros x y H x0 y0 H0.
    subst.
    unfold access_allowed.
    symmetry in H0.
    eapply proj_sumbool_true in H0.
    subst.
    reflexivity.
  Defined.

  #[global] Instance provenance_lt_trans : Transitive provenance_lt.
  Proof.
    unfold Transitive.
    intros x y z XY YZ.
    unfold provenance_lt in *.
    lia.
  Defined.

  Lemma provenance_lt_next_provenance :
    forall pr,
      provenance_lt pr (next_provenance pr).
  Proof.
    unfold provenance_lt, next_provenance.
    lia.
  Qed.

  Lemma provenance_lt_nrefl :
    forall pr,
      ~ provenance_lt pr pr.
  Proof.
    intros pr.
    unfold provenance_lt.
    lia.
  Qed.

  #[global] Instance provenance_lt_antisym : Antisymmetric Provenance eq provenance_lt.
  Proof.
    unfold Antisymmetric.
    intros x y XY YX.
    unfold provenance_lt in *.
    lia.
  Defined.

  Lemma next_provenance_neq :
    forall pr,
      pr <> next_provenance pr.
  Proof.
    intros pr.
    unfold next_provenance.
    lia.
  Qed.

  Lemma access_allowed_aid_neq :
    forall aid1 aid2,
      aid1 <> aid2 ->
      access_allowed
        (allocation_id_to_prov (Some aid1)) (Some aid2) = false.
  Proof.
    intros aid1 aid2 NEQ.
    unfold access_allowed.
    unfold allocation_id_to_prov.
    cbn.
    rewrite orb_false_r.
    eapply N.eqb_neq.
    eauto.
  Qed.

  Lemma access_allowed_aid_eq :
    forall aid1 aid2,
      access_allowed
        (allocation_id_to_prov (Some aid1)) (Some aid2) = true ->
      aid1 = aid2.
  Proof.
    intros aid1 aid2 ACCESS.
    unfold access_allowed, allocation_id_to_prov in *.
    cbn in ACCESS.
    rewrite orb_false_r in ACCESS.
    eapply N.eqb_eq in ACCESS.
    auto.
  Qed.

  (* Debug *)
  Definition show_prov (pr : Prov) := Show.show pr.
  Definition show_provenance (pr : Provenance) := Show.show pr.
  Definition show_allocation_id (aid : AllocationId) := Show.show aid.
End FinPROV.

Module FinITOP : ITOP(FinAddr)(FinPROV)(FinPTOI)
with Definition int_to_ptr :=
  fun (i : Z) (pr : Prov) =>
    if (i <? 0)%Z || (i >=? @Integers.modulus 64)%Z
    then Oom ("FinITOP.int_to_ptr: out of range (" ++ show i ++ ").")
    else NoOom (@Integers.repr 64 i, pr).

  Import FinAddr.
  Import FinPROV.
  Import FinPTOI.

  Definition int_to_ptr (i : Z) (pr : Prov) : OOM addr
    := if (i <? 0)%Z || (i >=? @Integers.modulus 64)%Z
       then Oom ("FinITOP.int_to_ptr: out of range (" ++ show i ++ ").")
       else NoOom (Integers.repr i, pr).

  Lemma int_to_ptr_provenance :
    forall (x : Z) (p : Prov) (a : addr),
      int_to_ptr x p = ret a ->
      FinPROV.address_provenance a = p.
  Proof.
    intros x p a IP.
    unfold int_to_ptr in *.
    destruct ((x <? 0)%Z || (x >=? @Integers.modulus 64)); inv IP; auto.
  Qed.

  Lemma int_to_ptr_ptr_to_int :
    forall (a : addr) (p : Prov),
      address_provenance a = p ->
      int_to_ptr (ptr_to_int a) p = ret a.
  Proof.
    intros a p PROV.
    unfold int_to_ptr.
    unfold ptr_to_int.
    destruct a; cbn.
    pose proof (@Integers.unsigned_range 64 i) as R.
    destruct ((@Integers.unsigned 64 i <? 0)%Z || (@Integers.unsigned 64 i >=? @Integers.modulus 64)) eqn:RANGE; [lia|].
    rewrite Integers.repr_unsigned.
    inv PROV; cbn; auto.
  Qed.

  Lemma int_to_ptr_ptr_to_int_exists :
    forall (a : addr) (p : Prov),
    exists a',
      int_to_ptr (ptr_to_int a) p = ret a' /\
        ptr_to_int a' = ptr_to_int a /\
        address_provenance a' = p.
  Proof.
    intros [a prov] p.
    exists (a, p).
    split; auto.
    unfold int_to_ptr, ptr_to_int.
    cbn in *.
    destruct ((Integers.unsigned a <? 0)%Z || (Integers.unsigned a >=? Integers.modulus)) eqn:BOUNDS.
    - (* Out of bounds *)
      exfalso.
      destruct a.
      cbn in *.
      lia.
    - rewrite Integers.repr_unsigned.
      reflexivity.
  Qed.

  Lemma ptr_to_int_int_to_ptr :
    forall (x : Z) (p : Prov) (a : addr),
      int_to_ptr x p = ret a ->
      ptr_to_int a = x.
  Proof.
    intros x p a IP.
    unfold int_to_ptr in *.
    destruct ((x <? 0)%Z || (x >=? @Integers.modulus 64)) eqn:RANGE; inv IP; auto.
    unfold ptr_to_int, fst.
    rewrite (@Integers.unsigned_repr 64); auto.
    unfold Integers.max_unsigned.
    lia.
  Qed.
End FinITOP.
