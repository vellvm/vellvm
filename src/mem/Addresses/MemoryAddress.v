(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

(* begin hide *)
From Stdlib Require Import String.
From Stdlib Require Import OrderedType OrderedTypeEx.
From Stdlib Require Import ZArith.
Require Import Rocqlib.
From Stdlib Require Import List.

From Vellvm Require Import
  Utils.Error
  Utils.Monads
  MapMonadExtra.

From ExtLib Require Import
  Structures.Monads.

From Stdlib Require Import
  Lia
  Structures.Equalities.

From Mem Require Import
  Tactics
  Addresses.Provenance.

Import MonadNotation.
Import ListNotations.
Open Scope monad_scope.
(* end hide *)

(*** Abstract address modules *)
Module ADDRESS_TYPE_NOTATION (Import T:Typ).
  Notation addr := t.
End ADDRESS_TYPE_NOTATION.

(** The core abstract address type, which essentially just has
    decidable equality.
 *)
Module Type CORE_ADDRESS := UsualDecidableType <+ ADDRESS_TYPE_NOTATION.

(*** Address functors *)

(** Addresses which have null pointers *)
Module Type HAS_NULL (Import Addr:CORE_ADDRESS).
  Parameter null : addr.

  (** Check if a pointer is null. The `null` value above is guaranteed
      to be "null", but there may be pointers that don't equal the above
      value that count as "null" in certain memory models. For instance,
      there may be null pointers with different provenances associated
      with them.
   *)
  Parameter is_null : addr -> bool.

  Parameter null_is_null :
    is_null null = true.
End HAS_NULL.

(** Address types which can be converted to integers *)
Module Type HAS_PTOI (Import Addr:CORE_ADDRESS).
  Parameter ptr_to_int : addr -> Z.
End HAS_PTOI.

Module Type HAS_NULL_PTOI (Import Addr:CORE_ADDRESS) (Import Null : HAS_NULL Addr) (Import PTOI : HAS_PTOI Addr).
  Parameter is_null_is_zero :
    forall ptr,
      is_null ptr = true <-> ptr_to_int ptr = 0.

  #[global] Hint Resolve is_null_is_zero : MEM.
End HAS_NULL_PTOI.

Module Type HAS_POINTER_ARITHMETIC_CORE (Import Addr:CORE_ADDRESS).
  (** Pointer addition. May error if the result cannot be represented
      as a pointer, e.g., if it would be out of bounds.
   *)
  Parameter ptr_add : addr -> Z -> err addr.

  Parameter ptr_add_0 :
    forall ptr,
      ptr_add ptr 0 = inr ptr.

  Parameter ptr_add_hom :
    forall ptr x y,
      x >= 0 ->
      y >= 0 ->
      p <- ptr_add ptr x;;
      ptr_add p y = ptr_add ptr (x + y).
End HAS_POINTER_ARITHMETIC_CORE.

Module Type HAS_POINTER_ARITHMETIC_HELPERS
  (Import Addr:CORE_ADDRESS)
  (Import ARITH:HAS_POINTER_ARITHMETIC_CORE Addr).

  (* Slightly more general to help with induction *)
  Definition get_consecutive_ptrs_h (ptr : addr) (start len : nat) : err (list addr) :=
    let ixs := seq start len in
    map_monad
      (fun ix => ptr_add ptr (Z.of_nat ix))
      ixs (m:=err).

  Definition get_consecutive_ptrs (ptr : addr) (len : nat) : err (list addr) :=
    get_consecutive_ptrs_h ptr 0 len.

  Fixpoint consecutive_ptrs_h (start : addr) (ptrs : list addr) : bool :=
    match ptrs with
    | nil => true
    | cons ptr ptrs =>
        match (ptr_add start 1) with
        | inl _ => false
        | inr ptr' =>
            proj_sumbool (eq_dec ptr ptr') &&
              consecutive_ptrs_h ptr ptrs
        end
    end.

  Definition consecutive_ptrs (ptrs : list addr) : bool :=
    match ptrs with
    | nil => true
    | cons ptr ptrs => consecutive_ptrs_h ptr ptrs
    end.

  (*** Lemmas about get_consecutive_ptrs *)
  Lemma get_consecutive_ptrs_head :
    forall len (ptr ptr' : addr) (ptrs : list addr),
      get_consecutive_ptrs ptr len = ret (ptr' :: ptrs) ->
      ptr = ptr'.
  Proof.
    destruct len;
      intros ptr ptr' ptrs CONSEC;
      inv CONSEC.
    cbn in *.
    repeat break_match_hyp_inv.
    rewrite ptr_add_0 in Heqs.
    inv Heqs; auto.
  Qed.

  #[global] Hint Resolve get_consecutive_ptrs_head : MEM.

  Lemma get_consecutive_ptrs_length :
    forall (ptr : addr) (len : nat) (ptrs : list addr),
      get_consecutive_ptrs ptr len = ret ptrs ->
      len = length ptrs.
  Proof.
    intros ptr len ptrs CONSEC.
    unfold get_consecutive_ptrs in CONSEC.
    apply map_monad_err_length in CONSEC.
    rewrite length_seq in CONSEC.
    auto.
  Qed.

  (* Add symmetric version for better automation *)
  Lemma get_consecutive_ptrs_length' :
    forall (ptr : addr) (len : nat) (ptrs : list addr),
      get_consecutive_ptrs ptr len = ret ptrs ->
      length ptrs = len.
  Proof.
    intros *; symmetry; eapply get_consecutive_ptrs_length; eauto.
  Qed.

  Lemma consecutive_ptrs_nil :
    consecutive_ptrs [] = true.
  Proof.
    auto.
  Qed.

  #[global] Hint Resolve consecutive_ptrs_nil : MEM.

  Lemma consecutive_ptrs_cons :
    forall (ptrs : list addr) (ptr : addr),
      consecutive_ptrs (ptr :: ptrs) = true ->
      consecutive_ptrs ptrs = true.
  Proof.
    induction ptrs; intros ptr CONSEC;
      auto.

    cbn in *.
    break_match_hyp_inv.
    apply andb_true_iff in H0.
    destruct H0.
    rewrite H, H0.
    auto.
  Qed.

  Lemma consecutive_ptrs_cons' :
    forall (ptrs : list addr) (ptr : addr),
      consecutive_ptrs (ptr :: ptrs) = true ->
      match head ptrs with
      | None => True
      | Some p =>
          match ptr_add ptr 1 with
          | inl _ => False
          | inr p' => p = p'
          end
      end.
  Proof.
    intros ptrs ptr H.
    cbn in *.
    induction ptrs; cbn in *; auto.
    repeat break_match_hyp_inv.
    apply andb_true_iff in H1.
    destruct H1.
    auto.
    destruct (eq_dec a t0); auto.
    inv H.
  Qed.

  #[global] Hint Resolve
    consecutive_ptrs_cons
    consecutive_ptrs_cons' : MEM.

  Lemma consecutive_ptrs_h_consecutive_ptrs :
    forall ptr ptrs,
      consecutive_ptrs_h ptr ptrs = consecutive_ptrs (ptr :: ptrs).
  Proof.
    intros ptr ptrs.
    cbn; auto.
  Qed.

  #[global] Hint Rewrite consecutive_ptrs_h_consecutive_ptrs : MEM.

  Lemma consecutive_ptrs_app_r :
    forall (ptrs1 ptrs2 : list addr),
      consecutive_ptrs (ptrs1 ++ ptrs2) = true ->
      consecutive_ptrs ptrs2 = true.
  Proof.
    induction ptrs1;
      intros ptrs2 CONSEC;
      cbn in *; auto with MEM.


    autorewrite with MEM in *.
    apply consecutive_ptrs_cons in CONSEC as CONSEC'.
    apply IHptrs1 in CONSEC' as CONSEC2; auto.
  Qed.

  #[global] Hint Resolve consecutive_ptrs_app_r : MEM.

  Lemma consecutive_ptrs_app_l :
    forall (ptrs1 ptrs2 : list addr),
      consecutive_ptrs (ptrs1 ++ ptrs2) = true ->
      consecutive_ptrs ptrs1 = true.
  Proof.
    induction ptrs1;
      intros ptrs2 CONSEC;
      cbn in *; auto with MEM.
    autorewrite with MEM in *.

    apply consecutive_ptrs_cons in CONSEC as CONSEC'.
    apply consecutive_ptrs_cons' in CONSEC.

    apply IHptrs1 in CONSEC'.
    cbn.
    destruct (hd_error (ptrs1 ++ ptrs2)) eqn:PTRS;
      try break_match_hyp_inv.
    - destruct (ptrs1 ++ ptrs2) eqn:PTRS'; inv PTRS.
      destruct ptrs1; auto.
      rewrite <- app_comm_cons in PTRS'.
      inv PTRS'.
      cbn.
      rewrite Heqs; auto.
      apply andb_true_iff.
      split; auto.
      destruct eq_dec; auto.
    - destruct (ptrs1 ++ ptrs2) eqn:PTRS'; inv PTRS.
      apply app_eq_nil in PTRS' as [PTRS1 PTRS2]; subst.
      auto.
  Qed.

  #[global] Hint Resolve consecutive_ptrs_app_l : MEM.

  Lemma consecutive_ptrs_app :
    forall (ptrs1 ptrs2 : list addr),
      consecutive_ptrs (ptrs1 ++ ptrs2) = true ->
      consecutive_ptrs ptrs1 = true /\ consecutive_ptrs ptrs2 = true.
  Proof.
    eauto with MEM.
  Qed.

  #[global] Hint Resolve consecutive_ptrs_app : MEM.

  Lemma get_consecutive_ptrs_h_consecutive :
    forall (len start : nat) (ptr : addr) (ptrs : list addr),
      get_consecutive_ptrs_h ptr start len = ret ptrs ->
      consecutive_ptrs ptrs = true.
  Proof.
    unfold get_consecutive_ptrs, get_consecutive_ptrs_h, consecutive_ptrs.
    induction len; intros start ptr ptrs CONSEC.
    - inv CONSEC; auto.
    - cbn in CONSEC.
      repeat break_match_hyp_inv.
      apply IHlen in Heqs0 as CONSEC.
      destruct l; auto.
      cbn.
      pose proof Heqs0 as L.
      apply map_monad_err_cons_inv in L as (?&?&?).
      rewrite H in Heqs0.
      cbn in Heqs0.
      assert (x = S start).
      { destruct len; inv H; auto.
      }
      subst.
      repeat break_match_hyp_inv.
      pose proof (ptr_add_hom ptr (Z.of_nat start) 1) as PTR.
      do 2 (forward PTR; [lia|]).
      cbn in PTR.
      rewrite Heqs in PTR.
      replace (Z.of_nat start + 1) with (Z.of_nat (S start)) in PTR by lia.
      rewrite Heqs1 in PTR.
      rewrite PTR.
      apply andb_true_iff.
      split; auto.
      destruct eq_dec; auto.
  Qed.

  Lemma get_consecutive_ptrs_consecutive :
    forall (len start : nat) (ptr : addr) (ptrs : list addr),
      get_consecutive_ptrs_h ptr start len = ret ptrs ->
      consecutive_ptrs ptrs = true.
  Proof.
    intros len start ptr ptrs H.
    eapply get_consecutive_ptrs_h_consecutive; eauto.
  Qed.

  #[global] Hint Resolve
    get_consecutive_ptrs_length
    get_consecutive_ptrs_length'
    get_consecutive_ptrs_consecutive : MEM.
End HAS_POINTER_ARITHMETIC_HELPERS.

Module Type HAS_POINTER_ARITHMETIC (ADDR : CORE_ADDRESS)
  := HAS_POINTER_ARITHMETIC_CORE ADDR <+ HAS_POINTER_ARITHMETIC_HELPERS ADDR.

Module Type PTOI_ARITH_EXTRAS_CORE (Import Addr:CORE_ADDRESS) (Import PTOI : HAS_PTOI Addr) (Import HPA : HAS_POINTER_ARITHMETIC Addr).
  Parameter ptr_to_int_ptr_add :
    forall (ptr ptr' : addr) (x : Z),
      ptr_add ptr x = inr ptr' ->
      ptr_to_int ptr' = ptr_to_int ptr + x.

  #[global] Hint Resolve ptr_to_int_ptr_add : MEM.
End PTOI_ARITH_EXTRAS_CORE.

Module Type PTOI_ARITH_EXTRAS_HELPERS (Import Addr:CORE_ADDRESS) (Import PTOI : HAS_PTOI Addr) (Import HPA : HAS_POINTER_ARITHMETIC Addr) (Import CORE : PTOI_ARITH_EXTRAS_CORE Addr PTOI HPA).

  Lemma consecutive_ptrs_gt :
    forall ptrs ptr,
      consecutive_ptrs (ptr :: ptrs) = true ->
      forall p, In p ptrs -> ptr_to_int p > ptr_to_int ptr.
  Proof.
    induction ptrs;
      intros ptr CONSEC p IN;
      [inv IN|].    
    cbn in *.
    break_match_hyp_inv.
    apply ptr_to_int_ptr_add in Heqs.
    apply andb_true_iff in H0 as (?&?).
    destruct eq_dec in H; try discriminate; subst.
    clear H.
    destruct IN; subst; try lia.
    eapply Zgt_trans.
    eapply IHptrs; eauto with MEM.
    lia.
  Qed.

  Lemma get_consecutive_ptrs_h_gt :
    forall len start ptr ptrs,
      get_consecutive_ptrs_h ptr start len = inr ptrs ->
      forall p, In p ptrs -> ptr_to_int p >= ptr_to_int ptr.
  Proof.
    induction len;
      intros start ptr ptrs GCP p IN.
    - cbn in *; inv GCP; inv IN.
    - cbn in *.
      repeat break_match_hyp_inv.
      destruct IN; subst.
      + apply ptr_to_int_ptr_add in Heqs. lia.
      + eapply IHlen in Heqs0; eauto.
  Qed.

  Lemma get_consecutive_ptrs_gt :
    forall len ptr ptrs,
      get_consecutive_ptrs ptr len = inr ptrs ->
      forall p, In p ptrs -> ptr_to_int p >= ptr_to_int ptr.
  Proof.
    intros *;
      eapply get_consecutive_ptrs_h_gt; eauto.
  Qed.

  #[global] Hint Resolve
    consecutive_ptrs_gt
    get_consecutive_ptrs_h_gt
    get_consecutive_ptrs_gt : MEM.
End PTOI_ARITH_EXTRAS_HELPERS.

Module Type PTOI_ARITH_EXTRAS (ADDR : CORE_ADDRESS) (PTOI : HAS_PTOI ADDR) (HPA : HAS_POINTER_ARITHMETIC ADDR)
  := PTOI_ARITH_EXTRAS_CORE ADDR PTOI HPA <+ PTOI_ARITH_EXTRAS_HELPERS ADDR PTOI HPA.

(* TODO: Should this be moved to a utility file? *)
(** Types with additional metadata associated with them *)
Module Type HAS_METADATA (METADATA : Typ) (Import T:Typ).
  Parameter extract_metadata : t -> METADATA.t.
  Parameter default_metadata : METADATA.t.
End HAS_METADATA.

(** Metadata types with provenance *)
Module Type METADATA_PROVENANCE (Import PS : PROV_SET) (METADATA : Typ).
  (** Modify the provenance in the metadata, returning the new provenance and metadata values *)
  Parameter metadata_modify_provenance : METADATA.t -> (ProvSet -> ProvSet) -> (ProvSet * METADATA.t).

  (** Access the provenance for an address *)
  Definition metadata_provenance (md : METADATA.t) : ProvSet
    := fst (metadata_modify_provenance md id).

  Definition metadata_set_provenance (md : METADATA.t) (p : ProvSet) : METADATA.t
    := snd (metadata_modify_provenance md (const p)).
End METADATA_PROVENANCE.

Module Type METADATA_WITH_PROVENANCE (PS : PROV_SET) := Typ <+ METADATA_PROVENANCE PS.

(** Address types which support casts from integers

    METADATA is a type representing any extra metadata that might be
    needed when constructing a pointer from an integer type. Usually
    this metadata is something like a provenance.
 *)
Module Type HAS_ITOP (METADATA : Typ) (Import Addr:CORE_ADDRESS) (Import HMD : HAS_METADATA METADATA Addr).
  (** Convert an integer to a pointer.

      Parameters:
      - The integer to convert to a pointer value.
      - Metadata associated with the pointer (often this is a provenance).

      Return value:
      The resulting address. May OOM if the integer value doesn't fit
      in the address space.
   *)
  Parameter int_to_ptr : Z -> METADATA.t -> OOM addr.
  Parameter int_to_ptr_metadata :
    forall (x : Z) (p : METADATA.t) (a : addr),
      int_to_ptr x p = ret a ->
      extract_metadata a = p.
End HAS_ITOP.

(** Addresses that integers can safely be converted to (infinite
    address space)
 *)
Module Type ITOP_BIG (METADATA : Typ) (Import Addr:CORE_ADDRESS) (Import HMD : HAS_METADATA METADATA Addr) (Import ITOP : HAS_ITOP METADATA Addr HMD).
  Parameter int_to_ptr_safe :
    forall z pr,
      match int_to_ptr z pr with
      | NoOom _ => True
      | Oom _ => False
      end.
End ITOP_BIG.

(** Extra properties for addresses that support both ptoi and itop casts *)
Module Type PTOI_ITOP_EXTRA (METADATA : Typ) (Import Addr:CORE_ADDRESS) (Import HMD : HAS_METADATA METADATA Addr) (Import ITOP : HAS_ITOP METADATA Addr HMD) (Import PTOI : HAS_PTOI Addr).
  Parameter int_to_ptr_ptr_to_int :
    forall (a : addr) (p : METADATA.t),
      extract_metadata a = p ->
      int_to_ptr (ptr_to_int a) p = ret a.

  Parameter int_to_ptr_ptr_to_int_exists :
    forall (a : addr) (p : METADATA.t),
    exists a',
      int_to_ptr (ptr_to_int a) p = ret a' /\
        ptr_to_int a' = ptr_to_int a /\
        extract_metadata a' = p.

  Parameter ptr_to_int_int_to_ptr :
    forall (x : Z) (p : METADATA.t) (a : addr),
      int_to_ptr x p = ret a ->
      ptr_to_int a = x.
End PTOI_ITOP_EXTRA.

(*** Address module types *)
(** Addresses that can be null *)
Module Type NULLABLE_ADDRESS := CORE_ADDRESS <+ HAS_NULL.

(** Addresses with pointer to integer casts and pointer arithmetic *)
Module Type PTOI_ADDRESS :=
  CORE_ADDRESS <+ HAS_POINTER_ARITHMETIC <+ HAS_PTOI <+ PTOI_ARITH_EXTRAS.

(** Addresses without metadata *)
Module Type BASIC_ADDRESS :=
  PTOI_ADDRESS <+ HAS_NULL <+ HAS_NULL_PTOI.

(** Addresses with metadata *)
Module Type METADATA_ADDRESS (MD : Typ) :=
  BASIC_ADDRESS <+ HAS_METADATA MD.

(** Addresses with provenance metadata *)
Module Type BASE_PROVENANCE_ADDRESS (MD : Typ) (PS : PROV_SET) :=
  METADATA_ADDRESS MD <+ METADATA_PROVENANCE PS MD.

Module HAS_PROVENANCE (MD : Typ) (PS : PROV_SET) (Import Addr:BASE_PROVENANCE_ADDRESS MD PS).
    Definition address_provenance (a : Addr.t) : PS.ProvSet :=
      metadata_provenance (extract_metadata a).
End HAS_PROVENANCE.

Module Type PROVENANCE_ADDRESS (MD : Typ) (PS : PROV_SET) :=
  BASE_PROVENANCE_ADDRESS MD PS <+ HAS_PROVENANCE MD PS.

(** Basic addresses with the batteries and metadata included *)
Module Type ADDRESS (MD : Typ) (PS : PROV_SET) :=
  PROVENANCE_ADDRESS MD PS <+ HAS_ITOP MD <+ PTOI_ITOP_EXTRA MD.

(** Infinite addresses with the batteries included *)
Module Type INFINITE_ADDRESS (MD : Typ) (PS : PROV_SET) :=
  ADDRESS MD PS <+ ITOP_BIG MD.

(* TODO: Move this to a show utility file? *)
Module Type SHOWABLE (Import T:Typ).
  Parameter show_t : t -> string.
End SHOWABLE.
