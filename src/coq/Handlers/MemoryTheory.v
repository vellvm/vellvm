From Coq Require Import
     Morphisms ZArith List String Lia
     FSets.FMapAVL
     Structures.OrderedTypeEx
     micromega.Lia
     Psatz.

From ITree Require Import
     ITree
     Basics.Basics
     Events.Exception
     Eq.Eqit
     Events.StateFacts
     Events.State.

Import Basics.Basics.Monads.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Programming.Eqv
     Data.String.

From Vellvm Require Import
     Numeric.Coqlib
     Numeric.Integers
     Numeric.Floats
     Utils.Tactics
     Utils.Util
     Utils.Error
     Syntax.LLVMAst
     Syntax.DynamicTypes
     Semantics.DynamicValues
     Semantics.Denotation
     Semantics.MemoryAddress
     Semantics.LLVMEvents
     Handlers.Memory.

From stdpp Require Import gmap.
Require Import Ceres.Ceres.

Import EqvNotation.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

#[local] Open Scope Z_scope.

(** * Memory Model: Theory
    Reasoning principles for VIR's main memory model.
*)

Module Type MEMORY_THEORY (LLVMEvents : LLVM_INTERACTIONS(Addr)).
  (** ** Theory of the general operations over the finite maps we manipulate *)
  Import LLVMEvents.
  Import DV.
  Open Scope list.

  Module Mem := Memory.Make(LLVMEvents).
  Export Mem.

(** ** Theory of the general operations over the finite maps we manipulate
 *)
Section Map_Theory.

  (** ** Utility lemmas  *)
  Lemma Zseq_succ : forall off (n : N),
      Zseq off (N.to_nat (N.succ n)) = off :: Zseq (Z.succ off) (N.to_nat n).
  Proof.
    intros off n.
    rewrite Nnat.N2Nat.inj_succ; auto.
  Qed.

  Lemma Zseq_succ_nat : forall off (n : nat),
      Zseq off (S n) = off :: Zseq (Z.succ off) n.
  Proof.
    intros off n.
    auto.
  Qed.

  Lemma Zseq_length :
    forall len off,
      Datatypes.length (Zseq off len) = len.
  Proof.
    induction len; intros; auto.
    cbn.
    congruence.
  Qed.

  Lemma key_in_range_or_not_aux {a} : forall (k z : Z) (l : list a),
      {z <= k <= z + Zlength l - 1} + {k < z} + {k >= z + Zlength l}.
  Proof.
    induction l as [| x l IH]; intros.
    - cbn; rewrite Z.add_0_r.
      destruct (@RelDec.rel_dec_p _ Z.lt _ _ k z); [left; right; auto | right; lia].
    - rewrite Zlength_cons, <- Z.add_1_r.
      destruct IH as [[IH | IH] | IH].
      + left; left; lia.
      + left; right; lia.
      + destruct (RelDec.rel_dec_p k (z + Zlength l)).
        * subst; left; left; rewrite Zlength_correct; lia.
        * right; lia.
  Qed.

  Lemma key_in_range_or_not {a} : forall (k z : Z) (l : list a),
      {z <= k <= z + Zlength l - 1} + {k < z \/ k >= z + Zlength l}.
  Proof.
    intros; destruct (@key_in_range_or_not_aux _ k z l) as [[? | ?] | ?]; [left; auto | right; auto | right; auto].
  Qed.

  Lemma range_list_nth_z : forall {a} (l : list a) k,
      0 <= k < Zlength l ->
      exists v, list_nth_z l k = Some v.
  Proof.
    induction l as [| x l IH]; intros k INEQ; [cbn in *; lia |].
    cbn; flatten_goal; [eexists; reflexivity |].
    destruct (IH (Z.pred k)) as [v LU]; eauto.
    rewrite Zlength_cons in INEQ; lia.
  Qed.

  Lemma in_range_is_in {a} :  forall (k z : Z) (l : list a),
      z <= k <= z + Zlength l - 1 ->
      exists v, list_nth_z l (k - z) = Some v.
  Proof.
    intros.
    apply range_list_nth_z; lia.
  Qed.

  (** ** Behavior of [lookup_all_index]
   *)

  Lemma lookup_all_index_cons {a} : forall k (n : N) (m : IntMap a) def,
      lookup_all_index k (N.succ n) m def =
      match m !! k with
      | Some val => val
      | None => def
      end :: lookup_all_index (Z.succ k) n m def.
  Proof.
    intros.
    unfold lookup_all_index.
    rewrite Zseq_succ; try lia.
    auto.
  Qed.

  Lemma lookup_all_index_add_out_aux {a} : forall l k (n : N) (m : IntMap a) key x def,
      l = Zseq k (N.to_nat n) ->
      (key < k \/ key >= k + Z.of_N n) ->
      lookup_all_index k n (<[ key := x ]> m) def =
      lookup_all_index k n m def.
  Proof.
    induction l as [| x l IH]; simpl.
    - intros * EQ LT.
      unfold lookup_all_index; rewrite <- EQ; reflexivity.
    - intros * EQ RANGE.
      destruct (N.to_nat n) eqn:EQn; [inv EQ |].
      cbn in EQ; inv EQ.
      assert (n = N.succ (N.of_nat n0)) by lia.
      subst; rewrite lookup_all_index_cons; auto; try lia.
      subst; rewrite lookup_all_index_cons; auto; try lia.
      rewrite lookup_insert_ne; [ | lia].
      f_equal.
      apply IH; try lia.
      rewrite Nnat.Nat2N.id.
      reflexivity.
  Qed.

  (* Generalization of [lookup_add_ineq]: adding outside of the range of the lookup is inconsequential *)
  Lemma lookup_all_index_add_out {a} : forall k (n : N) (m : IntMap a) key x def,
      (key < k \/ key >= k + Z.of_N n) ->
      lookup_all_index k n (<[ key := x ]> m) def =
      lookup_all_index k n m def.
  Proof.
    intros; eapply lookup_all_index_add_out_aux; eauto.
  Qed.

  Lemma lookup_all_index_add {a} : forall k (size : N) x (m : IntMap a) def,
      lookup_all_index k (N.succ size) (<[ k := x ]> m) def =
      x :: lookup_all_index (Z.succ k) size m def.
  Proof.
    intros *.
    rewrite lookup_all_index_cons; auto; try lia.
    rewrite lookup_insert.
    f_equal.
    rewrite lookup_all_index_add_out; auto; try lia.
  Qed.

  Lemma lookup_all_index_add_all_index_same_length :
    forall serialized_bytes off len mem,
      len = Datatypes.length serialized_bytes ->
      lookup_all_index off (N.of_nat len) (add_all_index serialized_bytes off mem) SUndef = serialized_bytes.
  Proof.
    induction serialized_bytes;
      intros off len mem LEN.
    - cbn in *; subst; reflexivity.
    - cbn in LEN; subst.
      unfold add_all_index.
      rewrite Nnat.Nat2N.inj_succ.
      rewrite lookup_all_index_add.

      rewrite IHserialized_bytes; auto.
  Qed.

  Lemma pred_succ_of_nat :
    forall n,
      Pos.pred_N (Pos.of_succ_nat n) = N.of_nat n.
  Proof.
    induction n; auto.
    cbn.
    rewrite Pos.pred_N_succ.
    auto.
  Qed.


  Lemma lookup_all_index_append:
    forall serialized_bytes serialized_length rest_bytes rest_length off bytes ,
      N.of_nat (Datatypes.length serialized_bytes) = serialized_length ->
      (lookup_all_index off
                        (serialized_length + rest_length)
                        (add_all_index
                           (serialized_bytes ++ rest_bytes)
                           off bytes) SUndef) =
      (lookup_all_index off serialized_length
                        (add_all_index
                           (serialized_bytes)
                           off bytes) SUndef) ++
                                              (lookup_all_index (off + Z.of_N serialized_length) rest_length
                                                                (add_all_index
                                                                   (rest_bytes)
                                                                   (off + Z.of_N serialized_length) bytes) SUndef).
  Proof.
    induction serialized_bytes;
      intros serialized_length rest_bytes rest_length off bytes LEN.
    - cbn in *.
      subst.
      cbn in *.
      replace (off + 0) with off by lia.
      reflexivity.
    - cbn in LEN.
      subst.

      rewrite <- N.succ_pos_pred.
      rewrite <- app_comm_cons.
      cbn.

      rewrite lookup_all_index_add.
      replace (N.succ (Pos.pred_N (Pos.of_succ_nat (Datatypes.length serialized_bytes))) + rest_length)%N with (N.succ ((Pos.pred_N (Pos.of_succ_nat (Datatypes.length serialized_bytes))) + rest_length)) by lia.
      rewrite lookup_all_index_add.

      pose proof (IHserialized_bytes (N.of_nat (Datatypes.length serialized_bytes)) rest_bytes rest_length off bytes).
      forward H; [reflexivity|].

      rewrite pred_succ_of_nat.

      rewrite IHserialized_bytes; auto.
      replace (off + 1) with (Z.succ off) by lia.
      replace (off + Z.of_N (N.succ (N.of_nat (Datatypes.length serialized_bytes)))) with ((Z.succ off + Z.of_N (N.of_nat (Datatypes.length serialized_bytes)))) by lia.
      reflexivity.
  Qed.

  Lemma lookup_all_index_length :
    forall {A} len off bytes (def : A),
      Datatypes.length (lookup_all_index off len bytes def) = N.to_nat len.
  Proof.
    intros A len.
    remember (N.to_nat len) as n.
    assert (len = N.of_nat (N.to_nat len)) by lia.
    rewrite H. clear H.
    rewrite <- Heqn.
    clear Heqn len.

    induction n;
      intros off bytes def; auto.

    cbn.
    rewrite map_length.

    rewrite <- (IHn off bytes def).
    rewrite Zseq_length.
    lia.
  Qed.

  (** ** Behavior of [add_all_index]
   *)
  (* Generalization of [lookup_add_eq]: looking in range of the additions is fully defined *)
  Lemma lookup_add_all_index_in {a} : forall l k z (m : IntMap a) v,
      z <= k <= z + Zlength l - 1 ->
      list_nth_z l (k - z) = Some v ->
      lookup k (add_all_index l z m) = Some v.
  Proof.
    induction l as [| x l IH]; simpl; intros * INEQ LU.
    inv LU.
    destruct (RelDec.rel_dec_p k z).
    - subst.
      rewrite Z.sub_diag in LU; cbn in LU; inv LU.
      rewrite lookup_insert;  reflexivity.
    - rewrite lookup_insert_ne; auto.
      apply IH.
      rewrite Zlength_cons in INEQ; lia.
      destruct (zeq (k - z)) eqn:INEQ'; [lia |].
      replace (k - (z + 1)) with (Z.pred (k-z)) by lia; auto.
  Qed.

  (* (Different from [lookup_all_index_add_out]) Generalization of [lookup_add_eq]: looking out of range of the additions can ignore the additions *)
  Lemma lookup_add_all_index_out {a} : forall l k z (m : IntMap a),
      (k < z \/ k >= z + Zlength l) ->
      lookup k (add_all_index l z m) = lookup k m.
  Proof.
    induction l as [| x l IH]; simpl; intros * INEQ; auto.
    destruct (RelDec.rel_dec_p k z).
    - subst. exfalso; destruct INEQ as [INEQ | INEQ]; try lia.
      rewrite Zlength_cons, Zlength_correct in INEQ; lia.
    - rewrite lookup_insert_ne; auto.
      apply IH.
      destruct INEQ as [INEQ | INEQ]; [left; lia | ].
      right.
      rewrite Zlength_cons, Zlength_correct in INEQ.
      rewrite Zlength_correct.
      lia.
  Qed.

  (* Generalization of [add_ad], with the added constraint on the size of the lists *)
  Lemma add_all_index_twice {A} `{Equiv A, !Reflexive (≡@{A})}:
    forall (l1 l2 : list A) z m,
      Zlength l1 = Zlength l2 ->
      (add_all_index l2 z (add_all_index l1 z m)) ≡ (add_all_index l2 z m).
  Proof.
    repeat intro.
    destruct (@key_in_range_or_not _ i z l2) as [IN | OUT].
    - destruct (in_range_is_in _ IN) as [? LU].
      erewrite 2 lookup_add_all_index_in; eauto. f_equiv.
    - rewrite 3 lookup_add_all_index_out; eauto.
      { destruct (m !! i); try f_equiv. repeat red.
        constructor. }
      lia.
  Qed.

End Map_Theory.

Section Serialization_Theory.

  (** Length properties *)

  Lemma length_bytes_of_int:
    forall n x, List.length (bytes_of_int n x) = n.
  Proof.
    induction n; simpl; intros. auto. decEq. auto.
  Qed.

  Lemma int_of_bytes_of_int:
    forall n x,
      int_of_bytes (bytes_of_int n x) = x mod (two_p (Z.of_nat n * 8)).
  Proof.
    induction n; intros.
    simpl. rewrite Zmod_1_r. auto.
    Opaque Byte.wordsize.
    rewrite Nat2Z.inj_succ. simpl.
    replace (Z.succ (Z.of_nat n) * 8) with (Z.of_nat n * 8 + 8) by lia.
    rewrite two_p_is_exp; try lia.
    rewrite Zmod_recombine. rewrite IHn. rewrite Z.add_comm.
    change (Byte.unsigned (Byte.repr x)) with (Byte.Z_mod_modulus x).
    rewrite Byte.Z_mod_modulus_eq. reflexivity.
    apply two_p_gt_ZERO. lia. apply two_p_gt_ZERO. lia.
  Qed.

  (* The relation defining serializable dvalues. *)
  Inductive serialize_defined : dvalue -> Prop :=
  | d_addr: forall addr,
      serialize_defined (DVALUE_Addr addr)
  | d_i1: forall i1,
      serialize_defined (DVALUE_I1 i1)
  | d_i8: forall i1,
      serialize_defined (DVALUE_I8 i1)
  | d_i32: forall i32,
      serialize_defined (DVALUE_I32 i32)
  | d_i64: forall i64,
      serialize_defined (DVALUE_I64 i64)
  | d_struct_empty:
      serialize_defined (DVALUE_Struct [])
  | d_struct_nonempty: forall dval fields_list,
      serialize_defined dval ->
      serialize_defined (DVALUE_Struct fields_list) ->
      serialize_defined (DVALUE_Struct (dval :: fields_list))
  | d_array_empty:
      serialize_defined (DVALUE_Array [])
  | d_array_nonempty: forall dval fields_list,
      serialize_defined dval ->
      serialize_defined (DVALUE_Array fields_list) ->
      serialize_defined (DVALUE_Array (dval :: fields_list)).

  (* Lemma assumes all integers encoded with 8 bytes. *)

  Inductive sbyte_list_wf : list SByte -> Prop :=
  | wf_nil : sbyte_list_wf []
  | wf_cons : forall b l, sbyte_list_wf l -> sbyte_list_wf (Byte b :: l)
  .

  Lemma fold_sizeof :
    forall (dts : list dtyp) n,
      (fold_left (fun (acc : N) (x : dtyp) => acc + sizeof_dtyp x) dts n =
      n + fold_left (fun (acc : N) (x : dtyp) => acc + sizeof_dtyp x) dts 0)%N.
  Proof.
    induction dts; intros n.
    - cbn. rewrite N.add_0_r. reflexivity.
    - cbn. rewrite IHdts at 1. specialize (IHdts (sizeof_dtyp a)).
      setoid_rewrite IHdts.
      rewrite N.add_assoc.
      reflexivity.
  Qed.

  Lemma sizeof_struct_cons :
    forall dt dts,
      (sizeof_dtyp (DTYPE_Struct (dt :: dts)) = sizeof_dtyp dt + sizeof_dtyp (DTYPE_Struct dts))%N.
  Proof.
    cbn.
    intros dt dts.
    rewrite fold_sizeof. reflexivity.
  Qed.

  Lemma sizeof_dvalue_pos :
    forall dt,
      (0 <= sizeof_dtyp dt)%N.
  Proof.
    intros dt.
    lia.
  Qed.

  Lemma sizeof_serialized :
    forall dv dt,
      dvalue_has_dtyp dv dt ->
      N.of_nat (List.length (serialize_dvalue dv)) = sizeof_dtyp dt.
  Proof.
    intros dv dt TYP.
    induction TYP; try solve [cbn; auto].
    - cbn. rewrite DynamicValues.unsupported_cases_match; auto.
    - cbn.
      rewrite app_length.
      rewrite Nnat.Nat2N.inj_add.
      rewrite IHTYP1.
      cbn in IHTYP2. rewrite IHTYP2.
      symmetry.
      apply fold_sizeof.
    - generalize dependent sz.
      induction xs; intros sz H; cbn.
      + subst; auto.
      + cbn in *. rewrite <- H. rewrite app_length.
        replace (N.of_nat (S (Datatypes.length xs)) * sizeof_dtyp dt)%N
          with (sizeof_dtyp dt + N.of_nat (Datatypes.length xs) * sizeof_dtyp dt)%N.
        * rewrite Nnat.Nat2N.inj_add. rewrite IHxs with (sz:=Datatypes.length xs); auto.
          apply N.add_cancel_r; auto.
        * rewrite Nnat.Nat2N.inj_succ. rewrite N.mul_succ_l. lia.
  Qed.

  (* TODO: does this exist somewhere else? *)
  Lemma app_prefix :
    forall {A} (a b c : list A),
      b = c -> a ++ b = a ++ c.
  Proof.
    intros A a b c H.
    induction a.
    - cbn; auto.
    - cbn. rewrite IHa.
      reflexivity.
  Qed.

  Lemma firstn_sizeof_dtyp :
    forall dv dt,
      dvalue_has_dtyp dv dt ->
      (firstn (N.to_nat (sizeof_dtyp dt)) (serialize_dvalue dv)) = serialize_dvalue dv.
  Proof.
    intros dv dt TYP.
    induction TYP; auto.
    - cbn. rewrite DynamicValues.unsupported_cases_match. reflexivity. auto.
    - (* Structs *)
      rewrite sizeof_struct_cons.
      cbn.
      rewrite <- sizeof_serialized with (dv:=f); auto.

      replace (N.to_nat
                 (N.of_nat (Datatypes.length (serialize_dvalue f)) +
                  fold_left (fun (x : N) (acc : dtyp) => x + sizeof_dtyp acc) dts 0))%N with
          (Datatypes.length (serialize_dvalue f) +
           N.to_nat (fold_left (fun (x : N) (acc : dtyp) => (x + sizeof_dtyp acc)%N) dts 0%N))%nat.
      + rewrite firstn_app_2.
        cbn in *.
        rewrite IHTYP2.
        reflexivity.
      + rewrite Nnat.N2Nat.inj_add; try lia.
    - (* Arrays *)
      generalize dependent sz.
      induction xs; intros sz H.
      + cbn. apply firstn_nil.
      + cbn in *. inversion H.
        replace (N.of_nat (S (Datatypes.length xs)) * sizeof_dtyp dt)%N with
            (sizeof_dtyp dt + N.of_nat (Datatypes.length xs) * sizeof_dtyp dt)%N.
        * rewrite Nnat.N2Nat.inj_add.
          -- cbn. rewrite <- sizeof_serialized with (dv:=a).
             rewrite Nnat.Nat2N.id.
             rewrite firstn_app_2.
             rewrite sizeof_serialized with (dt:=dt).
             apply app_prefix.
             apply IHxs.
             intros x Hin.
             apply IH; intuition.
             intros x Hin; auto.
             auto.
             auto.
             auto.
        * rewrite Nnat.Nat2N.inj_succ. rewrite N.mul_succ_l. lia.
  Qed.

  Lemma skipn_length_app :
    forall {A} (xs ys : list A),
      skipn (Datatypes.length xs) (xs ++ ys) = ys.
  Proof.
    intros A xs ys.
    induction xs; cbn; auto.
  Qed.

  Lemma all_not_sundef_cons :
    forall b bs,
      all_not_sundef (b :: bs) = true ->
      all_not_sundef bs = true.
  Proof.
    intros b bs H.
    cbn in H.
    unfold all_not_sundef.
    apply andb_prop in H as [Hid Hall].
    auto.
  Qed.

  Lemma all_not_sundef_app :
    forall xs ys,
      all_not_sundef xs ->
      all_not_sundef ys ->
      all_not_sundef (xs ++ ys).
  Proof.
    induction xs; intros ys Hxs Hys; auto.
    cbn in *.
    apply andb_prop in Hxs.
    apply andb_true_iff.
    intuition.
    apply IHxs; auto.
  Qed.

  Hint Resolve all_not_sundef_app: core.

  Lemma byte_defined :
    forall b bs,
      all_not_sundef bs ->
      In b bs ->
      Sbyte_defined b.
  Proof.
    intros b bs Hundef Hin.
    induction bs.
    - inversion Hin.
    - apply andb_prop in Hundef as [Hid Hall].
      inversion Hin; subst.
      + apply Hid.
      + apply IHbs; auto.
  Qed.

  Lemma dvalue_serialized_not_sundef :
    forall dv,
      all_not_sundef (serialize_dvalue dv) = true.
  Proof.
    intros dv.
    induction dv; auto.
    - induction fields.
      + reflexivity.
      + cbn. apply forallb_forall.
        intros x Hin.
        apply in_app_or in Hin as [Hin | Hin].
        * assert (In a (a :: fields)) as Hina.
          { intuition; apply in_eq. }
          specialize (H a Hina).
          eapply byte_defined; eauto.
        * assert (forall u : dvalue, In u fields -> all_not_sundef (serialize_dvalue u) = true) as Hu.
          intros u Hinu.
          apply H. cbn. auto.

          specialize (IHfields Hu).
          eapply byte_defined. apply IHfields.
          apply Hin.
    - induction elts.
      + reflexivity.
      + cbn in *.
        rewrite forallb_app.
        apply andb_true_iff.
        split.
        * apply H; auto.
        * apply IHelts. intros e H0.
          apply H; auto.
  Qed.

  Hint Resolve dvalue_serialized_not_sundef: core.

  Lemma all_not_sundef_fold_right_serialize :
    forall xs,
      all_not_sundef (fold_right (fun (dv : dvalue) (acc : list SByte) => serialize_dvalue dv ++ acc) [ ] xs).
  Proof.
    induction xs; auto.
    - cbn. apply all_not_sundef_app; auto.
  Qed.

  Hint Resolve all_not_sundef_fold_right_serialize: core.

  Lemma all_not_sundef_deserialized :
    forall bs t,
      all_not_sundef bs ->
      deserialize_sbytes_defined bs t = deserialize_sbytes bs t.
  Proof.
    intros bs t H.
    unfold deserialize_sbytes.
    rewrite H.
    auto.
  Qed.

  Lemma deserialize_sbytes_defined_dvalue :
    forall dv t,
      deserialize_sbytes_defined (serialize_dvalue dv) t = deserialize_sbytes (serialize_dvalue dv) t.
  Proof.
    intros dv t.
    apply all_not_sundef_deserialized.
    apply dvalue_serialized_not_sundef.
  Qed.

  Hint Resolve deserialize_sbytes_defined: core.

  Lemma serialize_firstn_app :
    forall dv dt rest,
      dvalue_has_dtyp dv dt ->
      firstn (N.to_nat (sizeof_dtyp dt))
             (serialize_dvalue dv ++ rest) = serialize_dvalue dv.
  Proof.
    intros dv dt rest H.
    erewrite <- sizeof_serialized; eauto.
    rewrite Nnat.Nat2N.id.
    rewrite firstn_app.
    rewrite Nat.sub_diag.
    cbn.
    rewrite app_nil_r.
    rewrite <- (Nnat.Nat2N.id (Datatypes.length (serialize_dvalue dv))).
    erewrite sizeof_serialized; eauto.
    rewrite firstn_sizeof_dtyp; eauto.
  Qed.

  Lemma serialize_skipn_app :
    forall dv dt rest,
      dvalue_has_dtyp dv dt ->
      skipn (N.to_nat (sizeof_dtyp dt))
            (serialize_dvalue dv ++ rest) = rest.
  Proof.
    intros dv dt rest H.
    erewrite <- sizeof_serialized; eauto.
    rewrite Nnat.Nat2N.id.
    apply skipn_length_app.
  Qed.

  Lemma serialize_fold_length :
    forall xs dt,
      (forall x, In x xs -> dvalue_has_dtyp x dt) ->
      N.to_nat (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt) =
      Datatypes.length
        (fold_right (fun (dv : dvalue) (acc : list SByte) => serialize_dvalue dv ++ acc) [] xs).
  Proof.
    induction xs; intros dt H; auto.

    cbn.
    rewrite app_length.
    apply Nnat.Nat2N.inj.
    rewrite Nnat.N2Nat.id.
    rewrite Nnat.Nat2N.inj_add.

    break_match.
    - erewrite sizeof_serialized; cycle 1.
      { apply H; apply in_eq. }

      rewrite !Heqn. cbn.
      erewrite <- IHxs; cycle 1.
      { intros; apply H; by apply in_cons. }
      rewrite Heqn. lia.
    - erewrite sizeof_serialized; cycle 1.
      { apply H; apply in_eq. }

      rewrite Heqn.
      erewrite <- IHxs; cycle 1.
      { intros; apply H; by apply in_cons. }
      rewrite Nnat.N2Nat.id.
      lia.
  Qed.


End Serialization_Theory.

Section Memory_Stack_Theory.

  Lemma not_overlaps__no_overlap :
    forall a1 τ1 a2 τ2,
      ~ overlaps_dtyp a1 τ1 a2 τ2 ->
      no_overlap_dtyp a1 τ1 a2 τ2.
  Proof.
    intros [a1_r a1_o] τ1 [a2_r a2_o] τ2 H.
    unfold overlaps_dtyp, overlaps in H.
    unfold no_overlap_dtyp, no_overlap.
    lia.
  Qed.

  Lemma no_overlap__not_overlaps :
    forall a1 τ1 a2 τ2,
      no_overlap_dtyp a1 τ1 a2 τ2 ->
      ~ overlaps_dtyp a1 τ1 a2 τ2.
  Proof.
    intros [a1_r a1_o] τ1 [a2_r a2_o] τ2 H.
    unfold no_overlap_dtyp, no_overlap in H.
    unfold overlaps_dtyp, overlaps.
    lia.
  Qed.

  Lemma no_overlap_dec :
    forall ptr1 ptr2 s1 s2,
      {no_overlap ptr1 s1 ptr2 s2} + {~ (no_overlap ptr1 s1 ptr2 s2)}.
  Proof.
    intros [b1 o1] [b2 o2] s1 s2.
    unfold no_overlap.
    cbn.

    destruct (Z.eq_dec b1 b2) as [B | B].
    2: { left. auto. }

    destruct (Int.Z_as_Int.gt_le_dec (o1) (o2 + s2 - 1)).
    { left. auto. }

    destruct (Int.Z_as_Int.gt_le_dec (o2) (o1 + s1 - 1)).
    { left. auto. }

    right. intuition.
  Qed.

  Lemma no_overlap_dtyp_dec :
    forall ptr1 ptr2 τ1 τ2,
      {no_overlap_dtyp ptr1 τ1 ptr2 τ2} + {~ (no_overlap_dtyp ptr1 τ1 ptr2 τ2)}.
  Proof.
    intros ptr1 ptr2 τ1 τ2.
    apply no_overlap_dec.
  Qed.

  Lemma gep_array_ptr_overlap_dtyp :
    forall ptr ix (sz : N) τ elem_ptr,
      DynamicValues.Int64.unsigned ix < Z.of_N sz -> (* Not super happy about this *)
      (0 < sizeof_dtyp τ)%N ->
      handle_gep_addr (DTYPE_Array sz τ) ptr
                      [DVALUE_I64 (repr 0); DVALUE_I64 ix] = inr elem_ptr ->
      ~(no_overlap_dtyp elem_ptr τ ptr (DTYPE_Array sz τ)).
  Proof.
    intros ptr ix sz τ elem_ptr BOUNDS SIZE GEP.
    intros NO_OVER.
    unfold no_overlap_dtyp, no_overlap in NO_OVER.

    destruct ptr as [ptr_b ptr_i].
    destruct elem_ptr as [elem_ptr_b elem_ptr_i].

    unfold handle_gep_addr in GEP.
    cbn in *.
    inversion GEP; subst.

    destruct NO_OVER as [NO_OVER | [NO_OVER | NO_OVER]].
    - auto.
    - rewrite Integers.Int64.unsigned_repr in NO_OVER; cycle 1.
      { pose proof Int64.unsigned_range_2.
        specialize (H Int64.zero). lia. }
      replace (ptr_i + Z.of_N (sz * sizeof_dtyp τ) * 0 + DynamicValues.Int64.unsigned ix * Z.of_N (sizeof_dtyp τ)) with (ptr_i + DynamicValues.Int64.unsigned ix * Z.of_N (sizeof_dtyp τ)) in NO_OVER by lia.
      pose proof (Int64.unsigned_range ix) as [? ?].
      assert (Z.of_N sz > 0). lia.
      rewrite N2Z.inj_mul in NO_OVER.
      replace (ptr_i + Z.of_N sz * Z.of_N (sizeof_dtyp τ) - 1) with (ptr_i + (Z.of_N sz * Z.of_N (sizeof_dtyp τ) - 1)) in NO_OVER by lia.
      apply Zorder.Zplus_gt_reg_l in NO_OVER.

      assert (Z.of_N sz * Z.of_N (sizeof_dtyp τ) - Z.of_N (sizeof_dtyp τ) <= Z.of_N sz * Z.of_N (sizeof_dtyp τ) - 1).
      lia.
      assert (Int64.unsigned ix * Z.of_N (sizeof_dtyp τ) <= (Z.of_N sz - 1) * Z.of_N (sizeof_dtyp τ)).
      { apply Zmult_le_compat_r; lia. }
      lia.
    - rewrite Integers.Int64.unsigned_repr in NO_OVER; cycle 1.
      { pose proof Int64.unsigned_range_2.
        specialize (H Int64.zero). lia. }
      replace (ptr_i + Z.of_N (sz * sizeof_dtyp τ) * 0 + DynamicValues.Int64.unsigned ix * Z.of_N (sizeof_dtyp τ)) with (ptr_i + DynamicValues.Int64.unsigned ix * Z.of_N (sizeof_dtyp τ)) in NO_OVER by lia.
      pose proof (Int64.unsigned_range ix) as [? ?].
      lia.
  Qed.

  Definition non_void (τ : dtyp) : Prop :=
    τ <> DTYPE_Void.

  Lemma allocate_inv : forall m τ m' a,
      allocate m τ = inr (m', a) ->
      non_void τ /\
      let new_block := make_empty_logical_block τ in
      let key       := next_logical_key m in
      let m         := add_logical_block key new_block m in
      m' = add_to_frame m key /\ a = (key,0).
  Proof.
    intros m τ m' a ALLOC.
    split.
    - intros NV. destruct τ; inversion NV; inversion ALLOC.
    - split;
        destruct τ;
        cbn in ALLOC; inversion ALLOC; subst; cbn; auto.
  Qed.

  (** ** Block level lemmas *)

  Lemma get_logical_block_of_add_logical_block :
    forall (m : memory_stack) (key : Z) (lb : logical_block),
      get_logical_block (add_logical_block key lb m) key = Some lb.
  Proof.
    intros [lm s] b lb.
    cbn. setoid_rewrite lookup_insert. reflexivity.
  Qed.

  Lemma get_logical_block_of_add_logical_block_mem :
    forall (m : memory) (s : frame_stack) (key : Z) (lb : logical_block),
      get_logical_block (add_logical_block_mem key lb m, s) key = Some lb.
  Proof.
    intros. erewrite <- get_logical_block_of_add_logical_block.
    unfold add_logical_block.
    Unshelve. 3 : exact key. 2 : exact (m, s). cbn. reflexivity.
  Qed.

  (* TODO: looks like this might be duplicated now *)
  Lemma get_logical_block_of_add_logical_block_neq :
    forall (m : memory_stack) (key key' : Z) (lb : logical_block),
      key <> key' ->
      get_logical_block (add_logical_block key lb m) key' = get_logical_block m key'.
  Proof.
    intros [lm s] b b' lb NEQ.
    cbn. by setoid_rewrite lookup_insert_ne.
  Qed.

  Lemma get_logical_block_of_add_logical_block_mem_neq :
    forall (m : memory) (s : frame_stack) (key key' : Z) (lb : logical_block),
      key <> key' ->
      get_logical_block (add_logical_block_mem key lb m, s) key' = get_logical_block (m, s) key'.
  Proof.
    intros m s key key' lb H.
    change (add_logical_block_mem key lb m, s) with (add_logical_block key lb (m, s)).
    eapply get_logical_block_of_add_logical_block_neq; eauto.
  Qed.

  Lemma get_logical_block_of_add_to_frame :
    forall (m : memory_stack) k x, get_logical_block (add_to_frame m k) x = get_logical_block m x.
  Proof.
    intros. destruct m. cbn. destruct m.
    destruct f; unfold get_logical_block; cbn; reflexivity.
  Qed.

  Lemma get_logical_block_of_add_logical_frame_ineq :
    forall x m k mv, m <> x ->
                     get_logical_block (add_logical_block m k mv) x = get_logical_block mv x.
  Proof.
    intros.
    cbn in *.
    unfold get_logical_block, get_logical_block_mem in *.
    unfold add_logical_block. destruct mv. cbn.
    unfold add_logical_block_mem.
    cbn in *.
    setoid_rewrite lookup_insert_ne; auto.
  Qed.

  Lemma unsigned_I1_in_range : forall (x : DynamicValues.int1),
      0 <= DynamicValues.Int1.unsigned x <= 1.
  Proof.
    destruct x as [x [? ?]].
    cbn in *.
    unfold DynamicValues.Int1.modulus,DynamicValues.Int1.wordsize, DynamicValues.Wordsize1.wordsize, two_power_nat in *.
    cbn in *; lia.
  Qed.

  Lemma unsigned_I8_in_range : forall (x : DynamicValues.int8),
      0 <= DynamicValues.Int8.unsigned x <= 255.
  Proof.
    destruct x as [x [? ?]].
    cbn in *.
    unfold DynamicValues.Int8.modulus,DynamicValues.Int8.wordsize, DynamicValues.Wordsize8.wordsize, two_power_nat in *.
    cbn in *; lia.
  Qed.

  Lemma unsigned_I32_in_range : forall (x : DynamicValues.int32),
      0 <= DynamicValues.Int32.unsigned x <= 4294967295.
  Proof.
    destruct x as [x [? ?]].
    cbn in *.
    unfold DynamicValues.Int32.modulus,DynamicValues.Int8.wordsize, DynamicValues.Wordsize8.wordsize, two_power_nat in *.
    cbn in *; lia.
  Qed.

  Lemma unsigned_I64_in_range : forall (x : DynamicValues.int64),
      0 <= DynamicValues.Int64.unsigned x <= 18446744073709551615.
  Proof.
    destruct x as [x [? ?]].
    cbn in *.
    unfold DynamicValues.Int32.modulus,DynamicValues.Int8.wordsize, Int64.modulus, DynamicValues.Wordsize8.wordsize, two_power_nat in *.
    cbn in *;lia.
  Qed.

  Lemma Z_div_mod' :
    forall a b q r : Z, b > 0 -> Z.div_eucl a b = (q, r) -> a = b * q + r /\ 0 <= r < b.
  Proof.
    intros.
    pose proof (Z_div_mod a b H).
    break_let.
    congruence.
  Qed.

    Definition not_pointer (τ : dtyp) : Prop
      := τ <> DTYPE_Pointer.

    Definition not_undef (v : uvalue) : Prop
      := forall τ, v <> UVALUE_Undef τ.

    Lemma div_add_lemma :
      forall (x y d : Z),
        0 <= y < d ->
        (d * x + y) / d = x.
    Proof.
      intros x y d H.
      rewrite Z.add_comm.
      rewrite Z.mul_comm.
      rewrite Z_div_plus.
      rewrite Zdiv_small with (a:=y) by lia.
      all: lia.
    Qed.

    Ltac destruct_div_eucls :=
      repeat
        match goal with
        | H: Z.div_eucl _ _ = _ |- _ =>
          apply Z_div_mod' in H; [destruct H|lia]
        end.

    Ltac rewrite_div_adds :=
      repeat
        match goal with
        | H: context [(?d * ?x + ?z) / ?d] |- _ =>
          rewrite div_add_lemma in H; [|lia]; subst
        end.

    Ltac unfold_lookup_all_index :=
      rewrite <- N.succ_pos_pred;
      match goal with
      | |- context [N.succ (Pos.pred_N ?x)] =>
        let var := fresh "var" in
        set (var := Pos.pred_N x); cbn in var; subst var
      end;
      rewrite lookup_all_index_add.

    Ltac unroll_lookup_all_index :=
      simpl add_all_index; simpl sizeof_dtyp;
      repeat unfold_lookup_all_index.

    Ltac solve_integer_deserialize :=
      unroll_lookup_all_index; cbn; f_equal;
      match goal with
      | |- _ = ?x =>
        first [ pose proof (unsigned_I8_in_range x)
              | pose proof (unsigned_I32_in_range x)
              | pose proof (unsigned_I64_in_range x)
              ];

        repeat rewrite Byte.unsigned_repr_eq;
        unfold Byte.max_unsigned, Byte.modulus, Byte.wordsize, Wordsize_8.wordsize;
        cbn;
        change (two_power_nat 8) with 256;
        let xv := fresh "xv" in
        let Hxv := fresh "Hxv" in
        first [ remember (Int8.unsigned x) as xv eqn:Hxv
              | remember (Int32.unsigned x) as xv eqn:Hxv
              | remember (Int64.unsigned x) as xv eqn:Hxv
              ];
        match goal with
        | [|- context[Int8.repr ?zv]] => replace zv with xv
        | [|- context[Int32.repr ?zv]] => replace zv with xv
        | [|- context[Int64.repr ?zv]] => replace zv with xv
        end;
        [subst xv;
         try solve [ apply Int1.repr_unsigned
                   | apply Int8.repr_unsigned
                   | apply Int32.repr_unsigned
                   | apply Int64.repr_unsigned
                   ]
        |];
        clear Hxv;
        unfold Z.modulo;
        repeat break_let;
        destruct_div_eucls;
        subst;
        rewrite_div_adds;
        lia
      end.

    Lemma deserialize_sbytes_dvalue_all_not_sundef :
      forall dv dt bytes,
        deserialize_sbytes bytes dt = dvalue_to_uvalue dv ->
        all_not_sundef bytes = true.
    Proof.
      intros dv dt bytes DES.
      unfold deserialize_sbytes in DES.
      break_match_hyp; auto.

      destruct dv; inversion DES.
    Qed.

    Lemma deserialize_struct_element :
      forall f fields ft fts f_bytes fields_bytes,
        is_supported (DTYPE_Struct (ft :: fts)) ->
        all_not_sundef f_bytes = true ->
        all_not_sundef fields_bytes = true ->
        N.to_nat (sizeof_dtyp ft) = Datatypes.length f_bytes ->
        deserialize_sbytes f_bytes ft = f ->
        deserialize_sbytes fields_bytes (DTYPE_Struct fts) = UVALUE_Struct fields ->
        deserialize_sbytes (f_bytes ++ fields_bytes) (DTYPE_Struct (ft :: fts)) =
        UVALUE_Struct (f :: fields).
    Proof.
      intros f fields ft fts.
      generalize dependent ft.
      generalize dependent fields.
      generalize dependent f.
      induction fts; intros f fields ft f_bytes fields_bytes SUP UNDEF_BYTES UNDEF_FIELDS SIZE FIELD FIELDS.

      - rewrite <- all_not_sundef_deserialized in FIELD; auto.
        rewrite <- all_not_sundef_deserialized in FIELDS; auto.
        rewrite <- all_not_sundef_deserialized; auto using all_not_sundef_app.

        cbn in FIELDS; inversion FIELDS; subst; cbn.

        replace (N.to_nat (sizeof_dtyp ft)) with (Datatypes.length f_bytes + 0)%nat by lia.
        rewrite firstn_app_2; cbn.
        rewrite app_nil_r.

        congruence.
      - rewrite <- all_not_sundef_deserialized in FIELD; auto.
        rewrite <- all_not_sundef_deserialized in FIELDS; auto.
        rewrite <- all_not_sundef_deserialized; auto using all_not_sundef_app.

        cbn in FIELDS; inversion FIELDS; subst; cbn.

        replace (N.to_nat (sizeof_dtyp ft)) with (Datatypes.length f_bytes + 0)%nat by lia.
        rewrite firstn_app_2; cbn.
        rewrite app_nil_r.

        do 2 f_equal.

        replace (Datatypes.length f_bytes + 0)%nat with (Datatypes.length f_bytes) by lia.
        rewrite skipn_length_app.
        congruence.
    Qed.

    Lemma deserialize_array_element :
      forall sz elt elts ft elt_bytes elts_bytes,
        is_supported (DTYPE_Array sz ft) ->
        all_not_sundef elt_bytes = true ->
        all_not_sundef elts_bytes = true ->
        N.to_nat (sizeof_dtyp ft) = Datatypes.length elt_bytes ->
        deserialize_sbytes elt_bytes ft = elt ->
        deserialize_sbytes elts_bytes (DTYPE_Array sz ft) = UVALUE_Array elts ->
        deserialize_sbytes (elt_bytes ++ elts_bytes) (DTYPE_Array (N.succ sz) ft) =
        UVALUE_Array (elt :: elts).
    Proof.
      induction sz;
        intros elt elts ft elt_bytes elts_bytes SUP UNDEF_BYTES UNDEF_ELTS SIZE ELT ELTS.

      - rewrite <- all_not_sundef_deserialized in ELT; auto.
        rewrite <- all_not_sundef_deserialized in ELTS; auto.
        rewrite <- all_not_sundef_deserialized; auto using all_not_sundef_app.

        cbn in ELTS; inversion ELTS; subst; cbn.

        replace (N.to_nat (sizeof_dtyp ft)) with (Datatypes.length elt_bytes + 0)%nat by lia.
        rewrite Pos2Nat.inj_1.
        rewrite firstn_app_2; cbn.
        rewrite app_nil_r.

        congruence.
      - rewrite <- all_not_sundef_deserialized in ELT; auto.
        rewrite <- all_not_sundef_deserialized in ELTS; auto.
        rewrite <- all_not_sundef_deserialized; auto using all_not_sundef_app.

        cbn in ELTS; inversion ELTS; subst; cbn.

        replace (N.to_nat (sizeof_dtyp ft)) with (Datatypes.length elt_bytes + 0)%nat by lia.
        rewrite Pos2Nat.inj_succ.
        rewrite firstn_app_2; cbn.
        rewrite app_nil_r.

        do 2 f_equal.

        replace (Datatypes.length elt_bytes + 0)%nat with (Datatypes.length elt_bytes) by lia.
        rewrite skipn_length_app.
        congruence.
    Qed.

    Lemma int64_modulus_range :
      0 ≤ Int64.modulus - 1.
    Proof.
      pose proof (@Int64.unsigned_range Int64.zero).
      assert (0 < Int64.modulus) by lia.
      lia.
    Qed.

    (** ** Deserialize - Serialize *)
(*         Starting from a dvalue [val] whose [dtyp] is [t], if: *)
(*         1. we serialize [val], getting a [list SByte] *)
(*         2. we add all these bytes to the memory block, starting from the position [off], getting back a new [mem_block] m' *)
(*         3. we lookup in this new memory [m'] the indices starting from [off] for the size of [t], getting back a [list SByte] *)
(*         4. we deserialize this final list of bytes *)
(*         then we should get back the initial value [val], albeit injected into [uvalue]. *)

(*         The proof should go by induction over [TYP] I think, and rely on [lookup_all_index_add] notably. *)
(*      *)
    Lemma deserialize_serialize : forall val t (TYP : dvalue_has_dtyp val t),
        forall off (bytes : mem_block) (SUP : is_supported t),
          deserialize_sbytes (lookup_all_index off (sizeof_dtyp t) (add_all_index (serialize_dvalue val) off bytes) SUndef) t = dvalue_to_uvalue val.
    Proof.
      induction 1; try auto; intros;
        match goal with
        | H: is_supported ?t |- _ =>
          try solve [inversion H]
        end.
      - unroll_lookup_all_index; cbn; f_equal.
      - unroll_lookup_all_index; cbn; f_equal.
        pose proof (unsigned_I1_in_range x).
        assert (EQ :DynamicValues.Int1.unsigned x / 256 = 0).
        apply Z.div_small; lia.
        rewrite EQ.
        repeat rewrite Zdiv_0_l.
        pose proof Byte.modulus_pos.
        repeat rewrite Byte.unsigned_repr; cycle 1.
        all: try solve [unfold Byte.max_unsigned; try lia].
        { split; try lia.
          pose proof (@Int1.unsigned_range x).
          destruct H1.
          apply Z.lt_le_incl.
          eapply Z.lt_le_trans; eauto.
          unfold Int1.modulus, Byte.max_unsigned, Byte.modulus.
          unfold Int1.wordsize, Wordsize1.wordsize.
          unfold Byte.wordsize, Wordsize_8.wordsize.

          unfold two_power_nat. unfold shift_nat; cbn.
          lia. }
        rewrite Z.add_0_r.
        apply DynamicValues.Int1.repr_unsigned.
      - solve_integer_deserialize.
      - solve_integer_deserialize.
      - solve_integer_deserialize.
      - inversion SUP; subst;
        exfalso; apply H; constructor.
      - unroll_lookup_all_index; cbn; f_equal.
        clear bytes off.
        remember (Float.to_bits x) as xb.
        pose proof (unsigned_I64_in_range xb).
        repeat rewrite Byte.unsigned_repr_eq.
        unfold Byte.modulus, Byte.wordsize, Wordsize_8.wordsize; cbn.
        replace (two_power_nat 8) with 256 by reflexivity.
        remember (Int64.unsigned xb) as xbv.
        match goal with
        | [|- context[Int64.repr ?zv]] => replace zv with xbv
        end.
        +
          subst.
          rewrite Int64.repr_unsigned.
          apply Float.of_to_bits.
        +
          (* this is the same goal as I64 branch! *)
          clear -H.
          rewrite Z.add_0_r.
          unfold Z.modulo.
          repeat break_let.
          repeat match goal with
                 | [H : Z.div_eucl _ _ = _ |- _] => apply Z_div_mod' in H; [destruct H | lia]
                 end.
          subst.
          repeat
            match goal with
            | H: context [(?d * ?x + ?z) / ?d] |- _ =>
              rewrite div_add_lemma in H; [|lia]; subst
            end.
          lia.
      - unroll_lookup_all_index; cbn; f_equal.
        clear bytes off.
        remember (Float32.to_bits x) as xb.
        pose proof (unsigned_I32_in_range xb).
        repeat rewrite Byte.unsigned_repr_eq.
        unfold Byte.modulus, Byte.wordsize, Wordsize_8.wordsize; cbn.
        replace (two_power_nat 8) with 256 by reflexivity.
        remember (Int32.unsigned xb) as xbv.
        match goal with
        | [|- context[Int32.repr ?zv]] => replace zv with xbv
        end.
        +
          subst.
          rewrite Int32.repr_unsigned.
          apply Float32.of_to_bits.
        +
          clear -H.

          rewrite Z.add_0_r.
          unfold Z.modulo.
          repeat break_let.
          repeat match goal with
                 | [H : Z.div_eucl _ _ = _ |- _] => apply Z_div_mod' in H; [destruct H | lia]
                 end.
          subst.
          rewrite Z.add_comm, Z.mul_comm, Z_div_plus in * by lia.
          rewrite Zdiv_small with (a:=z0) in * by lia.
          rewrite Z.add_0_l in *.
          subst.
          rewrite Z.add_comm, Z.mul_comm, Z_div_plus in * by lia.
          rewrite Zdiv_small with (a:=z2) in * by lia.
          rewrite Z.add_0_l in *.
          subst.
          rewrite Z.add_comm, Z.mul_comm, Z_div_plus in * by lia.
          rewrite Zdiv_small with (a:=z4) in * by lia.
          rewrite Z.add_0_l in *.
          subst.
          lia.
      - (* Structs *)
        rewrite sizeof_struct_cons.

        inversion SUP.
        subst.
        rename H0 into FIELD_SUP.
        apply List.Forall_cons_iff in FIELD_SUP.
        destruct FIELD_SUP as [dt_SUP dts_SUP].
        assert (is_supported (DTYPE_Struct dts)) as SUP_STRUCT by (constructor; auto).

        cbn.
        rewrite lookup_all_index_append; [|apply sizeof_serialized; auto].

        erewrite deserialize_struct_element; auto.
        +  erewrite <- sizeof_serialized; eauto.
          rewrite lookup_all_index_add_all_index_same_length; eauto.

          apply dvalue_serialized_not_sundef.
        + pose proof deserialize_sbytes_dvalue_all_not_sundef (DVALUE_Struct fields) (DTYPE_Struct dts) (lookup_all_index (off + Z.of_N (sizeof_dtyp dt)) (sizeof_dtyp (DTYPE_Struct dts))
                                                                                                                          (add_all_index (serialize_dvalue (DVALUE_Struct fields)) (off + Z.of_N (sizeof_dtyp dt)) bytes) SUndef).
          cbn in H.
          forward H; auto.
        + rewrite lookup_all_index_length.
          reflexivity.
      - (* Arrays *)
        rename H into SZ.
        generalize dependent sz.
        generalize dependent xs.
        induction xs;
          intros IH IHdtyp sz SZ SUP.
        + cbn in *.
          subst.
          reflexivity.
        + cbn in SZ.
          subst.
          rewrite Nnat.Nat2N.inj_succ.
          cbn.

          assert (dvalue_has_dtyp a dt) as DTa.
          {
            apply IHdtyp.
            cbn. auto.
          }

          rewrite Nmult_Sn_m.
          rewrite lookup_all_index_append; [|apply sizeof_serialized; auto].

          erewrite deserialize_array_element; auto.
          * inversion SUP; constructor; auto.
          * erewrite <- sizeof_serialized; eauto.
            rewrite lookup_all_index_add_all_index_same_length; eauto.

            apply dvalue_serialized_not_sundef.
          * (* Should be serialization of DVALUE_array xs *)
            replace (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt)%N
              with (N.of_nat (N.to_nat (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt))) by lia.
            rewrite lookup_all_index_add_all_index_same_length.

            apply all_not_sundef_fold_right_serialize.

            apply serialize_fold_length; intuition. apply IHdtyp; eauto.
            by apply in_cons.
          * replace (sizeof_dtyp dt) with (N.of_nat (N.to_nat (sizeof_dtyp dt))) by lia.
            rewrite lookup_all_index_add_all_index_same_length; cycle 1.
            { erewrite <- sizeof_serialized; intuition.
              by rewrite Nat2N.id. done. }
            erewrite <- sizeof_serialized; intuition; eauto.
            by do 2 rewrite Nat2N.id.
          * rewrite IH; intuition.
            inversion SUP; auto. by apply in_eq.
            inversion SUP; eauto.
          * cbn.

            unfold deserialize_sbytes.
            break_match.

            2: {
              assert (all_not_sundef
                        (lookup_all_index (off + Z.of_N (sizeof_dtyp dt))
                                          (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt)
                                          (add_all_index
                                             (fold_right (fun (dv : dvalue) (acc : list SByte) => serialize_dvalue dv ++ acc) []
                                                         xs) (off + Z.of_N (sizeof_dtyp dt)) bytes) SUndef) = true) as CONTRA.
              replace (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt)%N
                with (N.of_nat (N.to_nat (N.of_nat (Datatypes.length xs) * sizeof_dtyp dt))) by lia.
              rewrite lookup_all_index_add_all_index_same_length.

              apply all_not_sundef_fold_right_serialize.

              apply serialize_fold_length; intuition.
              { apply IHdtyp; by apply in_cons. }

              rewrite Heqb in CONTRA.
              inversion CONTRA.
            }

            forward IHxs; intuition.
            { eapply IH; eauto; by apply in_cons. }


            forward IHxs; intuition.
            { by apply IHdtyp, in_cons. }

            specialize (IHxs (Datatypes.length xs) eq_refl).
            forward IHxs.
            { inversion SUP; constructor; eauto. }

            cbn in IHxs.
            rewrite <- IHxs.

            rewrite all_not_sundef_deserialized; auto.
            erewrite <- sizeof_serialized.

            f_equal.

            repeat rewrite <- Nnat.Nat2N.inj_mul.
            rewrite lookup_all_index_add_all_index_same_length.
            rewrite lookup_all_index_add_all_index_same_length.
            reflexivity.

            { erewrite <- serialize_fold_length.
              erewrite <- sizeof_serialized.

              repeat rewrite <- Nnat.Nat2N.inj_mul.
              rewrite Nnat.Nat2N.id.
              reflexivity.

              eauto.
              intuition; by apply IHdtyp, in_cons.
            }

            { erewrite <- serialize_fold_length.
              erewrite <- sizeof_serialized.

              repeat rewrite <- Nnat.Nat2N.inj_mul.
              rewrite Nnat.Nat2N.id.
              reflexivity.

              eauto.
              intuition; by apply IHdtyp, in_cons.
            }

            eauto.
    Qed.

    (** ** Write - Read *)
(*         The expected law: reading the key that has just been written to returns the written value. *)
(*         The only subtlety comes from the fact that it holds _if_ the read is performed at the type of *)
(*         the written value. *)
(*      *)
    Lemma write_read :
      forall (m m' : memory_stack) (t : dtyp) (val : dvalue) (a : addr),
        is_supported t ->
        write m a val = inr m' ->
        dvalue_has_dtyp val t ->
        read m' a t = inr (dvalue_to_uvalue val).
    Proof.
      unfold write, read; cbn.
      intros * SUP WR TYP.
      flatten_hyp WR; try inv_sum.
      destruct l,a as [id off]; inv_sum.
      rewrite get_logical_block_of_add_logical_block.
      cbn.
      unfold read_in_mem_block.
      rewrite deserialize_serialize; auto.
    Qed.

    Arguments add : simpl never.
    Arguments lookup : simpl never.
    Arguments logical_next_key : simpl never.

    Lemma write_allocated : forall m a val m',
        write m a val = inr m' ->
        allocated a m.
    Proof.
      unfold write; intros (m,s) * WR; cbn in *.
      flatten_hyp WR; [| inv_sum].
      destruct l,a; inv WR.
      cbn in *. unfold allocated.
      cbn.
      unfold get_logical_block, get_logical_block_mem in Heq.
      cbn in Heq.
      by eapply elem_of_dom_2.
    Qed.

    Lemma lookup_all_index_add_all_index_no_overlap :
      forall {A} bs off off' m (def : A) (sz : N),
        off' + Z.of_N sz <= off \/ off + (Z.of_nat (length bs)) <= off' ->
        lookup_all_index off' sz (add_all_index bs off m) def =
        lookup_all_index off' sz m def.
    Proof.
      intros A; induction bs; intros off off' m def sz Hrange; auto.
      cbn.
      rewrite lookup_all_index_add_out; auto; try lia.
      apply IHbs; auto.
      destruct Hrange as [Hleft | Hright]; cbn in *; lia.
      destruct Hrange; cbn in *; lia.
    Qed.

    Lemma write_untouched:
      forall (m1 : memory_stack) (a : addr) (v : dvalue) (τ : dtyp) (m2 : memory_stack),
        dvalue_has_dtyp v τ ->
        write m1 a v = inr m2 ->
        forall (a' : addr) (τ' : dtyp),
          no_overlap_dtyp a τ a' τ' ->
          read m2 a' τ' = read m1 a' τ'.
    Proof.
      intros (m,s) [a off] v τ (m',s') TYP WR [a' off'] τ' INEQ.
      unfold read,write in *.
      cbn in *.
      flatten_hyp WR; try inv_sum.
      destruct l; inv_sum.
      apply no_overlap__not_overlaps in INEQ;
        unfold overlaps_dtyp, overlaps in INEQ; cbn in INEQ.
      unfold get_logical_block, get_logical_block_mem; cbn.
      destruct (Z.eq_dec a a') eqn:Haa'.
      - subst. setoid_rewrite lookup_insert.
        unfold get_logical_block,get_logical_block_mem in Heq. cbn in Heq.
        rewrite Heq.
        destruct (Z.le_gt_cases off (off' + (Z.of_N (sizeof_dtyp τ') - 1))) as [Hle | Hnle].
        + destruct (Z.le_gt_cases off' (off + (Z.of_N (sizeof_dtyp τ) - 1))) as [Hle' | Hnle'].
          * exfalso. apply INEQ. lia.
          * (* Overlap because off + sizeof_dtyp τ < off', so second memory region is "to the right" *)
            unfold read_in_mem_block.
            rewrite lookup_all_index_add_all_index_no_overlap; auto.
            rewrite <- nat_N_Z.
            rewrite sizeof_serialized with (dt:=τ); auto; lia.
        + (* off' + sizeof_dtyp τ' < off, so second memory region is "to the left" *)
          unfold read_in_mem_block.
          rewrite lookup_all_index_add_all_index_no_overlap; auto.
          lia.
      - setoid_rewrite lookup_insert_ne; auto.
    Qed.

    Lemma write_succeeds : forall m1 v τ a,
        dvalue_has_dtyp v τ ->
        dtyp_fits m1 a τ ->
        exists m2, write m1 a v = inr m2.
    Proof.
      intros m1 v τ a TYP CAN.
      destruct CAN as (sz & bytes & cid & BLOCK & SIZE).
      exists (add_logical_block (fst a) (LBlock sz (add_all_index (serialize_dvalue v) (snd a) bytes) cid) m1).
      unfold write.
      rewrite BLOCK.
      cbn. destruct a. reflexivity.
    Qed.

    Lemma read_write_succeeds :
      forall m ptr τ val v,
        read m ptr τ = inr val ->
        dvalue_has_dtyp v τ ->
        exists m2, write m ptr v = inr m2.
    Proof.
      intros m ptr τ val v READ TYP.
      unfold read in *.
      destruct (get_logical_block m (fst ptr)) eqn:LBLOCK; inversion READ.
      clear H0.

      destruct l as [sz bytes cid].
      exists (add_logical_block (fst ptr) (LBlock sz (add_all_index (serialize_dvalue v) (snd ptr) bytes) cid) m).
      unfold write.
      rewrite LBLOCK.
      cbn. destruct ptr. reflexivity.
    Qed.

    Lemma write_correct : forall m1 a v m2,
        write m1 a v = inr m2 ->
        write_spec m1 a v m2.
    Proof.
      intros; split; [| split]; eauto using write_allocated, write_read, write_untouched.
    Qed.

    Lemma write_block_preserves :
      forall m1 m2 (a a' : addr) v sz bytes cid,
        write m1 a v = inr m2 ->
        get_logical_block m1 (fst a') = Some (LBlock sz bytes cid) ->
        exists bytes', get_logical_block m2 (fst a') = Some (LBlock sz bytes' cid).
    Proof.
      intros m1 m2 a a' v sz bytes cid WRITE GET.
      destruct m1, m2; cbn in *.
      unfold write in WRITE.
      cbn in WRITE.
      break_match_hyp; inv WRITE.
      destruct l.
      destruct a, a'. cbn in *.
      inv H0.

      destruct (Z.eq_dec z z1) as [EQ | NEQ].
      - subst.
        rewrite GET in Heqo. inv Heqo.
        rewrite get_logical_block_of_add_logical_block_mem.
        eexists.
        reflexivity.
      - exists bytes.
        erewrite get_logical_block_of_add_logical_block_mem_neq; eauto.
    Qed.

    Lemma dtyp_fits_after_write :
      forall m m' ptr ptr' τ τ',
        dtyp_fits m ptr τ ->
        write m ptr' τ' = inr m' ->
        dtyp_fits m' ptr τ.
    Proof.
      intros m m' ptr ptr' τ τ' FITS WRITE.
      unfold dtyp_fits in *.
      destruct FITS as (sz & bytes & cid & GET & BOUNDS).
      eapply write_block_preserves in WRITE; eauto. destruct WRITE as (bytes' & WRITE).
      exists sz. exists bytes'. exists cid.
      split; eauto.
    Qed.

    Lemma read_in_mem_block_write_to_mem_block :
      forall bytes offset val τ,
        is_supported τ ->
        dvalue_has_dtyp val τ ->
        read_in_mem_block (write_to_mem_block bytes offset val) offset τ = dvalue_to_uvalue val.
    Proof.
      intros bytes offset val τ SUP H.
      unfold read_in_mem_block, write_to_mem_block.
      rewrite deserialize_serialize; eauto.
    Qed.

    Lemma write_array_cell_get_array_cell :
      forall (m m' : memory_stack) (t : dtyp) (val : dvalue) (a : addr) (i : nat),
        write_array_cell m a i t val = inr m' ->
        is_supported t ->
        dvalue_has_dtyp val t ->
        get_array_cell m' a i t = inr (dvalue_to_uvalue val).
    Proof.
      intros m m' t val a i WRITE SUP TYP.
      destruct a; cbn in *.
      break_match_hyp; inv WRITE.
      destruct l.
      inversion H0; subst.
      rewrite get_logical_block_of_add_logical_block.
      rewrite read_in_mem_block_write_to_mem_block; eauto.
    Qed.

    (* TODO: make this more general? I.e. write / read different types? *)
    Lemma read_in_mem_block_write_to_mem_block_untouched :
      forall offset offset' bytes val τ,
        dvalue_has_dtyp val τ ->
        offset' + Z.of_N (sizeof_dtyp τ) <= offset \/ offset + Z.of_N (sizeof_dtyp τ) <= offset' ->
        read_in_mem_block (write_to_mem_block bytes offset val) offset' τ = read_in_mem_block bytes offset' τ.
    Proof.
      intros offset offset' bytes val τ TYP OUT.
      unfold read_in_mem_block, write_to_mem_block.
      rewrite lookup_all_index_add_all_index_no_overlap; eauto.
      destruct OUT.
      - left. auto.
      - right. rewrite <- nat_N_Z. erewrite sizeof_serialized; eauto.
    Qed.

    Lemma write_array_cell_untouched :
      forall (m m' : memory_stack) (t : dtyp) (val : dvalue) (a : addr) (i : nat) (i' : nat),
        write_array_cell m a i t val = inr m' ->
        dvalue_has_dtyp val t ->
        DynamicValues.Int64.unsigned (DynamicValues.Int64.repr (Z.of_nat i)) <> DynamicValues.Int64.unsigned (DynamicValues.Int64.repr (Z.of_nat i')) ->
        get_array_cell m' a i' t = get_array_cell m a i' t.
    Proof.
      intros m m' t val a i i' WRITE TYP NEQ.
      destruct a; cbn in *.
      break_match_hyp; inv WRITE.
      destruct l.
      inversion H0; subst.
      rewrite get_logical_block_of_add_logical_block.
      rewrite read_in_mem_block_write_to_mem_block_untouched; eauto.

      destruct (Z_lt_ge_dec (DynamicValues.Int64.unsigned (DynamicValues.Int64.repr (Z.of_nat i'))) (DynamicValues.Int64.unsigned (DynamicValues.Int64.repr (Z.of_nat i)))) as [LT | GE].
      - left.
        rewrite <- Z.add_assoc.
        apply Z.add_le_mono_l.
        replace (DynamicValues.Int64.unsigned (DynamicValues.Int64.repr (Z.of_nat i')) * Z.of_N (sizeof_dtyp t) + Z.of_N (sizeof_dtyp t)) with ((1 + DynamicValues.Int64.unsigned (DynamicValues.Int64.repr (Z.of_nat i'))) * Z.of_N (sizeof_dtyp t)) by lia.
        apply Zmult_le_compat_r; eauto; lia.
      - right.
        rewrite <- Z.add_assoc.
        apply Z.add_le_mono_l.

        (* if i <> i' then the conversions shouldn't overlap either *)
        assert (DynamicValues.Int64.unsigned (DynamicValues.Int64.repr (Z.of_nat i')) >
                DynamicValues.Int64.unsigned (DynamicValues.Int64.repr (Z.of_nat i))) by lia.

        replace (DynamicValues.Int64.unsigned (DynamicValues.Int64.repr (Z.of_nat i)) * Z.of_N (sizeof_dtyp t) + Z.of_N (sizeof_dtyp t)) with ((1 + DynamicValues.Int64.unsigned (DynamicValues.Int64.repr (Z.of_nat i))) * Z.of_N (sizeof_dtyp t)) by lia.
        apply Zmult_le_compat_r; eauto; lia.
    Qed.

    Lemma write_array_cell_untouched_ptr_block :
      forall (m m' : memory_stack) (t : dtyp) (val : dvalue) (a a' : addr) (i i' : nat),
        write_array_cell m a i t val = inr m' ->
        dvalue_has_dtyp val t ->
        fst a' <> fst a ->
        get_array_cell m' a' i' t = get_array_cell m a' i' t.
    Proof.
      intros m m' t val a a' i i' WRITE TYP BLOCK_NEQ.
      destruct a as [b1 o1].
      destruct a' as [b2 o2].
      unfold get_array_cell.
      cbn in WRITE.
      break_match_hyp; inv WRITE.
      destruct l.
      inv H0.
      rewrite get_logical_block_of_add_logical_block_neq; eauto.
    Qed.

    Lemma all_neq_not_in:
      forall {A} (m : A) l,
        Forall (fun a => a <> m) l -> ~ In m l.
    Proof.
      intros A m l ALL.
      induction ALL; intros IN; inversion IN.
      - subst; contradiction.
      - contradiction.
    Qed.

    Instance logical_block_inhabited : Inhabited logical_block.
    Proof.
      constructor; eauto.
      constructor.
      - exact 0%N.
      - exact empty.
      - exact None.
    Qed.

    Lemma next_logical_key_fresh : forall lm,
        (logical_next_key lm) ∉ dom lm.
    Proof.
      intros lm MEM.

      assert (In (logical_next_key lm) (map fst (map_to_list lm))).
      { apply elem_of_list_In.
        setoid_rewrite dom_alt in MEM.
        by eapply elem_of_list_to_set. Unshelve.
        typeclasses eauto. }
      apply (maximumBy_Z_correct (-1)) in H.
      apply Zle_bool_imp_le in H.
      unfold logical_next_key in H.
      remember (map fst (map_to_list lm)) in H. lia.
    Qed.

    Lemma lookup_init_block_undef :
      forall n,
        lookup 0 (init_block_undef n empty) = Some SUndef.
    Proof.
      induction n; auto.
      cbn.
      setoid_rewrite lookup_insert_ne; [|lia].
      auto.
    Qed.

    Lemma lookup_init_block :
      forall n,
        (n > 0)%N ->
        lookup 0 (init_block n) = Some SUndef.
    Proof.
      intros n SZ.
      pose proof Nnat.N2Nat.id n.
      induction (N.of_nat (N.to_nat n)); [lia|].
      subst.
      cbn.
      apply lookup_init_block_undef.
    Qed.

    Lemma all_not_sundef_init :
      forall n,
        (n > 0)%N ->
        all_not_sundef (lookup_all_index 0 n (init_block n) SUndef) = false.
    Proof.
      destruct n; intros SZ.
      inv SZ.
      cbn.

      pose proof Pos2Nat.is_succ p as [n PN].
      rewrite PN.
      cbn.

      rewrite lookup_init_block_undef.
      reflexivity.
    Qed.

    (* This is false for VOID, and 0 length arrays *)
    Lemma read_empty_block : forall τ,
        (sizeof_dtyp τ > 0)%N ->
        read_in_mem_block (make_empty_mem_block τ) 0 τ = UVALUE_Undef τ.
    Proof.
      unfold read_in_mem_block.
      unfold make_empty_mem_block.
      unfold deserialize_sbytes.
      intros τ. induction τ; intros SZ; try solve [reflexivity | cbn in SZ; inv SZ | rewrite all_not_sundef_init; auto].
    Qed.

    (* TODO: finish a less specialized version of this *)
    Lemma read_array_not_pointer : forall mem a τ sz v dv,
        not_undef v ->
        read mem a (DTYPE_Array sz τ) = inr v ->
        uvalue_to_dvalue v = inr dv ->
        ~ dvalue_has_dtyp dv DTYPE_Pointer.
    Proof.
      intros mem a τ sz v dv NU READ CONVERT.
      intros TYP.
      inversion TYP.
      subst.
      unfold read in READ.
      break_match; try discriminate READ.
      break_match; subst.
      unfold read_in_mem_block in READ.
      unfold deserialize_sbytes in READ.
      break_match.
      - (* Fully defined *)
        inversion READ; subst.
        cbn in CONVERT.
        break_match; inversion CONVERT.
      - (* Undefined *)
        inversion READ; subst;
          eapply NU; eauto.
    Qed.

    Lemma allocate_succeeds : forall m1 τ,
        non_void τ ->
        exists m2 a, allocate m1 τ = inr (m2, a).
    Proof.
      intros m1 τ NV.
      destruct m1 as [m fs].
      destruct fs as [|f fs].
      - destruct τ eqn:Hτ; cbn; repeat rewrite <- Hτ;
          exists (add_logical_block_mem (next_logical_key (m, Singleton f)) (make_empty_logical_block τ) m,
                  Singleton (next_logical_key (m, Singleton f) :: f));
          exists (next_logical_key (m, Singleton f), 0);
          auto; exfalso; auto.
      - destruct τ eqn:Hτ; cbn; repeat rewrite <- Hτ;
          exists (add_logical_block_mem (next_logical_key (m, Snoc f fs)) (make_empty_logical_block τ) m,
                  Snoc f (next_logical_key (m, Snoc f fs) :: fs));
          exists (next_logical_key (m, Snoc f fs), 0);
          auto; exfalso; auto.
    Qed.

    Lemma allocate_non_void : forall m τ x,
        allocate m τ = inr x ->
        non_void τ.
    Proof.
      intros m τ x H.
      destruct τ; inversion H; intros NV; inversion NV.
    Qed.

    Lemma allocate_correct : forall m1 τ m2 a,
        allocate m1 τ = inr (m2,a) ->
        allocate_spec m1 τ m2 a.
    Proof.
      intros (m,s) * EQ;
        destruct s as [|f s]; apply allocate_inv in EQ as [NV [EQm2 EQa]]; subst; cbn.
      - split.
        + cbn. apply next_logical_key_fresh.
        + { split.
            + intros SIZE.
              unfold read; cbn.
              unfold get_logical_block, get_logical_block_mem; cbn.
              setoid_rewrite lookup_insert; cbn.
              unfold non_void in NV.
              f_equal; apply read_empty_block.
              lia.
            + intros * ALLOC NOVER.
              unfold read; cbn.
              unfold get_logical_block, get_logical_block_mem; cbn.

              cbn in ALLOC.

              apply no_overlap__not_overlaps in NOVER.
              unfold next_logical_key, next_logical_key_mem, overlaps in *.
              cbn in *.
              destruct (Z.eq_dec (logical_next_key m) (fst a')) as [Ha' | Ha'].
              -- (* Bogus branch where a' is the freshly allocated block *)
                exfalso. eapply next_logical_key_fresh; erewrite Ha'; eauto.
              -- (* Good branch *)
                setoid_rewrite lookup_insert_ne; auto.
          }
      - split.
        + cbn. apply next_logical_key_fresh.
        + { split.
            + intros SIZE.
              unfold read; cbn.
              unfold get_logical_block, get_logical_block_mem; cbn.
              setoid_rewrite lookup_insert; cbn.
              f_equal; apply read_empty_block.
              lia.
            + intros * ALLOC NOVER.
              unfold read; cbn.
              unfold get_logical_block, get_logical_block_mem; cbn.

              cbn in ALLOC.

              apply no_overlap__not_overlaps in NOVER.
              unfold next_logical_key, next_logical_key_mem, overlaps in *.
              cbn in *.
              destruct (Z.eq_dec (logical_next_key m) (fst a')) as [Ha' | Ha'].
              -- (* Bogus branch where a' is the freshly allocated block *)
                exfalso. eapply next_logical_key_fresh; erewrite Ha'; eauto.
              -- (* Good branch *)
                setoid_rewrite lookup_insert_ne; auto.
          }
    Qed.

    Lemma allocated_get_logical_block :
      forall a m,
        allocated a m ->
        exists b, get_logical_block m (fst a) = Some b.
    Proof.
      intros a m H.
      unfold allocated in H.
      destruct m as [m fs].
      cbn in H.

      apply elem_of_dom in H; eauto.
    Qed.

    Lemma read_array: forall m size τ i a elem_addr,
        allocated a m ->
        handle_gep_addr (DTYPE_Array size τ) a [DVALUE_I64 (repr 0); DVALUE_I64 (repr (Z.of_nat i))] = inr elem_addr ->
        read m elem_addr τ = get_array_cell m a i τ.
    Proof.
      intros m size τ i a elem_addr ALLOC GEP.
      unfold get_array_cell.
      destruct a.
      unfold read.
      cbn in GEP.
      inversion GEP. subst.
      cbn.
      destruct (get_logical_block m z) eqn:GET.
      - destruct l.
        cbn.
        rewrite Int64.unsigned_repr.
        + replace (z0 + Z.of_N (size * sizeof_dtyp τ) * 0 +
                   DynamicValues.Int64.unsigned (DynamicValues.Int64.repr (Z.of_nat i)) * Z.of_N (sizeof_dtyp τ))
            with  (z0 + DynamicValues.Int64.unsigned (DynamicValues.Int64.repr (Z.of_nat i)) * Z.of_N (sizeof_dtyp τ))
            by lia.
          reflexivity.
        + pose proof Int64.unsigned_range_2.
          specialize (H Int64.zero). lia.
      - pose proof (@allocated_get_logical_block (z, z0) m ALLOC) as [b GETSOME].
        cbn in GETSOME.
        rewrite GET in GETSOME.
        inversion GETSOME.
    Qed.

    Lemma can_read_allocated :
      forall ptr τ v m,
        read m ptr τ = inr v ->
        allocated ptr m.
    Proof.
      intros ptr τ v m READ.
      unfold read in READ.
      destruct (get_logical_block m (fst ptr)) eqn:LBLOCK.
      - destruct l.
        red. unfold get_logical_block, get_logical_block_mem in LBLOCK.
        destruct m, ptr; cbn in LBLOCK; cbn.
        apply elem_of_dom; eauto.
      - inversion READ.
    Qed.

    Lemma allocated_can_read :
      forall a m τ,
        allocated a m ->
        exists v, read m a τ = inr v.
    Proof.
      intros a [[cm lm] fs] τ ALLOC.
      apply allocated_get_logical_block in ALLOC.
      destruct ALLOC as [b GET].
      unfold read.
      rewrite GET.
      destruct b.
      cbn.
      exists (read_in_mem_block bytes (snd a) τ). reflexivity.
    Qed.

    Lemma freshly_allocated_different_blocks :
      forall ptr1 ptr2 τ m1 m2,
        allocate m1 τ = inr (m2, ptr2) ->
        allocated ptr1 m1 ->
        fst ptr2 <> fst ptr1.
    Proof.
      intros ptr1 ptr2 τ m1 m2 ALLOC INM1 EQ.
      pose proof (allocate_correct ALLOC) as (ALLOC_FRESH & ALLOC_NEW & ALLOC_OLD).
      apply ALLOC_FRESH.
      unfold allocated in *.
      destruct m1 as [[cm1 lm1] fs1].
      rewrite EQ.
      auto.
    Qed.

    Lemma freshly_allocated_no_overlap_dtyp :
      forall ptr1 ptr2 τ τ' m1 m2,
        allocate m1 τ' = inr (m2, ptr2) ->
        allocated ptr1 m1 ->
        no_overlap_dtyp ptr2 τ' ptr1 τ.
    Proof.
      intros ptr1 ptr2 τ τ' m1 m2 ALLOC INM1.
      repeat red.
      left.
      eapply freshly_allocated_different_blocks; eauto.
    Qed.

    Lemma no_overlap_dtyp_different_blocks :
      forall a b τ τ',
        fst a <> fst b ->
        no_overlap_dtyp a τ b τ'.
    Proof.
      intros a b τ τ' H.
      unfold no_overlap_dtyp, no_overlap.
      auto.
    Qed.

    Lemma read_array_exists : forall m size τ i a,
        allocated a m ->
        exists elem_addr,
          handle_gep_addr (DTYPE_Array size τ) a [DVALUE_I64 (repr 0); DVALUE_I64 (repr (Z.of_nat i))] = inr elem_addr /\ read m elem_addr τ = get_array_cell m a i τ.
    Proof.
      intros m size τ i a ALLOC.
      destruct a.
      exists (z,
              z0 + Z.of_N size * Z.of_N (sizeof_dtyp τ) * DynamicValues.Int64.unsigned (DynamicValues.Int64.repr 0) +
              DynamicValues.Int64.unsigned (DynamicValues.Int64.repr (Z.of_nat i)) * Z.of_N (sizeof_dtyp τ)).
      split.
      - cbn.
        rewrite Int64.unsigned_repr.
        replace (z0 + Z.of_N (size * sizeof_dtyp τ) * 0 +
                 DynamicValues.Int64.unsigned (DynamicValues.Int64.repr (Z.of_nat i)) * Z.of_N (sizeof_dtyp τ))
          with (z0 + DynamicValues.Int64.unsigned (DynamicValues.Int64.repr (Z.of_nat i)) * Z.of_N (sizeof_dtyp τ))
          by lia.
        replace (z0 + Z.of_N size * Z.of_N (sizeof_dtyp τ) * 0 +
                 Int64.unsigned (Int64.repr (Z.of_nat i)) * Z.of_N (sizeof_dtyp τ))
          with (z0 + DynamicValues.Int64.unsigned (DynamicValues.Int64.repr (Z.of_nat i)) * Z.of_N (sizeof_dtyp τ)) by lia.
        reflexivity.
        unfold Int64.max_unsigned. cbn.
        split; [ lia | ]; apply int64_modulus_range.

      - eapply read_array; cbn; eauto.
        rewrite N2Z.inj_mul.
        reflexivity.
    Qed.

    Lemma write_array_lemma : forall m size τ i a elem_addr v,
        allocated a m ->
        handle_gep_addr (DTYPE_Array size τ) a [DVALUE_I64 (repr 0); DVALUE_I64 (repr (Z.of_nat i))] = inr elem_addr ->
        write m elem_addr v = write_array_cell m a i τ v.
    Proof.
      intros m size τ i a elem_addr v ALLOC GEP.
      unfold write_array_cell.
      destruct a.
      unfold write.
      cbn in GEP.
      inversion GEP. subst.
      cbn.
      destruct (get_logical_block m z) eqn:GET.
      - destruct l.
        cbn.
        rewrite Int64.unsigned_repr.
        + replace (z0 + Z.of_N (size * sizeof_dtyp τ) * 0 +
                   DynamicValues.Int64.unsigned (DynamicValues.Int64.repr (Z.of_nat i)) * Z.of_N (sizeof_dtyp τ))
            with  (z0 + DynamicValues.Int64.unsigned (DynamicValues.Int64.repr (Z.of_nat i)) * Z.of_N (sizeof_dtyp τ))
            by lia.

          reflexivity.
        + unfold Int64.max_unsigned. cbn.

          split; [ lia | ]; apply int64_modulus_range.
      - pose proof @allocated_get_logical_block (z, z0) m ALLOC as [b GETSOME].
        cbn in GETSOME.
        rewrite GET in GETSOME.
        inversion GETSOME.
    Qed.

    Lemma write_array_exists : forall m size τ i a v,
        allocated a m ->
        exists elem_addr,
          handle_gep_addr (DTYPE_Array size τ) a [DVALUE_I64 (repr 0); DVALUE_I64 (repr (Z.of_nat i))] = inr elem_addr /\ write m elem_addr v = write_array_cell m a i τ v.
    Proof.
      intros m size τ i a v ALLOC.
      destruct a.
      exists (z,
              z0 + Z.of_N (size * sizeof_dtyp τ) * DynamicValues.Int64.unsigned (DynamicValues.Int64.repr 0) +
              DynamicValues.Int64.unsigned (DynamicValues.Int64.repr (Z.of_nat i)) * Z.of_N (sizeof_dtyp τ)).
      split.
      - cbn.
        rewrite Int64.unsigned_repr.
        replace (z0 + Z.of_N (size * sizeof_dtyp τ) * 0 +
                 DynamicValues.Int64.unsigned (DynamicValues.Int64.repr (Z.of_nat i)) * Z.of_N (sizeof_dtyp τ))
          with  (z0 + DynamicValues.Int64.unsigned (DynamicValues.Int64.repr (Z.of_nat i)) * Z.of_N (sizeof_dtyp τ))
          by lia.
        reflexivity.
        unfold Int64.max_unsigned.
        split; [ lia | ]; apply int64_modulus_range.
      - eapply write_array_lemma; cbn; eauto.
    Qed.

    Lemma write_preserves_allocated :
      forall {m1 m2 ptr ptr' v},
        allocated ptr' m1 ->
        write m1 ptr v = inr m2 ->
        allocated ptr' m2.
    Proof.
      intros m1 m2 ptr ptr' v ALLOC WRITE.
      unfold allocated in *.
      destruct m1 as [m1 f1].
      destruct m2 as [m2 f2].

      unfold write in WRITE.
      destruct (get_logical_block (m1, f1) (fst ptr)) eqn:LB.
      - destruct l. destruct ptr, ptr'; cbn in *.
        inversion WRITE; subst.
        unfold add_logical_block_mem.
        unfold get_logical_block, get_logical_block_mem in LB.
        cbn in *.
        apply dom_insert. set_solver.
      - inversion WRITE.
    Qed.

    Lemma dtyp_fits_allocated :
      forall m a τ,
        dtyp_fits m a τ ->
        allocated a m.
    Proof.
      intros m a τ FITS.
      unfold allocated.

      unfold dtyp_fits in FITS.
      destruct FITS as (sz & bytes & cid & LB & SIZE).

      (* TODO: Make this part of the allocated / get_logical_block lemma *)
      unfold get_logical_block, get_logical_block_mem in LB.
      destruct m as [m f]; cbn in *.
      apply elem_of_dom; eauto.
    Qed.

    Lemma allocated_next_key_diff :
      forall m ptr,
        allocated ptr m ->
        next_logical_key m <> fst ptr.
    Proof.
      intros [m fs] [ptr_a ptr_o] H.
      Transparent next_logical_key.
      unfold next_logical_key, next_logical_key_mem, logical_next_key.
      cbn.
      unfold allocated in H.
      epose proof maximumBy_Z_correct.
      cbn in *.
      pose proof (next_logical_key_fresh m).
      intro; apply H1. set_solver.
    Qed.

    Lemma get_logical_block_frames :
      forall m f1 f2,
        get_logical_block (m, f1) = get_logical_block (m, f2).
    Proof.
      intros m f1 f2.
      unfold get_logical_block.
      cbn.
      reflexivity.
    Qed.

    Lemma get_logical_block_add_to_frame :
      forall m key ptr,
        get_logical_block (add_to_frame m key) ptr = get_logical_block m ptr.
    Proof.
      intros [[cm lm] fs] key ptr.
      cbn.
      destruct fs;
        erewrite get_logical_block_frames; reflexivity.
    Qed.

    Lemma get_logical_block_allocated:
      forall m1 m2 τ ptr ptr_allocated,
        allocate m1 τ = inr (m2, ptr_allocated) ->
        allocated ptr m1 ->
        get_logical_block m2 (fst ptr) = get_logical_block m1 (fst ptr).
    Proof.
      Opaque add_logical_block next_logical_key.
      intros [[cm1 lm1] fs1] [[cm2 lm2] fs2] τ ptr ptr_allocated ALLOC INm1.
      pose proof (allocate_correct ALLOC) as (ALLOC_FRESH & ALLOC_NEW & ALLOC_OLD).
      unfold allocate in ALLOC.
      destruct τ; inversion ALLOC.
      all :
        rewrite get_logical_block_add_to_frame;
        rewrite get_logical_block_of_add_logical_block_neq;
        [auto | apply allocated_next_key_diff; auto].
      Transparent add_logical_block next_logical_key.
    Qed.

    Lemma dtyp_fits_after_allocated:
      forall m1 m2 τ ptr τ' ptr_allocated,
        allocate m1 τ = inr (m2, ptr_allocated) ->
        dtyp_fits m1 ptr τ' ->
        dtyp_fits m2 ptr τ'.
    Proof.
      intros m1 m2 τ ptr τ' ptr_allocated ALLOC FITS.
      pose proof FITS as ALLOCATED.
      apply dtyp_fits_allocated in ALLOCATED.
      pose proof (freshly_allocated_different_blocks _
                    ALLOC ALLOCATED) as DIFF.

      unfold dtyp_fits in *.
      erewrite get_logical_block_allocated; eauto.
    Qed.

    Lemma handle_gep_addr_allocated :
      forall idxs sz τ ptr m elem_addr,
        allocated ptr m ->
        handle_gep_addr (DTYPE_Array sz τ) ptr idxs = inr elem_addr ->
        allocated elem_addr m.
    Proof.
      induction idxs;
        intros sz τ [b i] m [eb ei] ALLOC GEP.
      - discriminate GEP.
      - cbn in *. destruct a; inversion GEP.
        + destruct (handle_gep_h (DTYPE_Array sz τ) (i + Z.of_N (sz * sizeof_dtyp τ) * DynamicValues.Int32.unsigned x) idxs); inversion GEP; subst.
          apply ALLOC.
        + destruct (handle_gep_h (DTYPE_Array sz τ) (i + Z.of_N (sz * sizeof_dtyp τ) * DynamicValues.Int64.unsigned x) idxs); inversion GEP; subst.
          apply ALLOC.
    Qed.

    (* ext_memory only talks in terms of reads... Does not *)
(*        necessarily preserved what's allocated, because you might *)
(*        not be able to read from an allocated block *)
    Lemma ext_memory_trans :
      forall m1 m2 m3 τ v1 v2 dst,
        ext_memory m1 dst τ v1 m2 ->
        ext_memory m2 dst τ v2 m3 ->
        ext_memory m1 dst τ v2 m3.
    Proof.
      intros m1 m2 m3 τ v1 v2 dst [NEW1 OLD1] [NEW2 OLD2].
      split; auto.
      intros a' τ' ALLOC DISJOINT.
      rewrite <- OLD1; eauto.
      pose proof (allocated_can_read τ' ALLOC) as [v READ].
      rewrite <- OLD1 in READ; eauto.
      apply can_read_allocated in READ.
      rewrite <- OLD2; eauto.
    Qed.

    (* If I write to a different area, it doesn't affect the allocation of other addresses *)
    Lemma write_untouched_allocated:
      forall m1 m2 a τa v,
        dvalue_has_dtyp v τa ->
        write m1 a v = inr m2 ->
        forall b τb, no_overlap_dtyp a τa b τb ->
                allocated b m2 ->
                allocated b m1.
    Proof.
      intros m1 m2 a τa v TYP WRITE b τb OVERLAP ALLOC.

      eapply allocated_can_read in ALLOC as [v' READ].
      eapply can_read_allocated.

      erewrite write_untouched in READ; eauto.
    Qed.

    Lemma write_get_logical_block_neq :
      forall (m m' : memory_stack) (t : dtyp) (val : dvalue) (a a' : addr) (i i' : nat),
        write m a val = inr m' ->
        fst a' <> fst a ->
        get_logical_block m (fst a') = get_logical_block m' (fst a').
    Proof.
      intros m m' t val a a' i i' WRITE NEQ.
      unfold write in WRITE.
      break_match_hyp.
      - destruct l, a.
        cbn in WRITE; inv WRITE.
        symmetry.
        apply get_logical_block_of_add_logical_frame_ineq.
        eauto.
      - inv WRITE.
    Qed.

    Lemma write_untouched_ptr_block_get_array_cell :
      forall (m m' : memory_stack) (t : dtyp) (val : dvalue) (a a' : addr) (i i' : nat),
        write m a val = inr m' ->
        fst a' <> fst a ->
        get_array_cell m' a' i' t = get_array_cell m a' i' t.
    Proof.
      intros m m' t val a a' i i' WRITE NEQ.

      destruct a as [b1 o1].
      destruct a' as [b2 o2].
      unfold get_array_cell.

      assert (get_logical_block m b2 = get_logical_block m' b2).
      { change b2 with (fst (b2, o2)).
        eapply write_get_logical_block_neq; eauto.
      }

      rewrite H.
      reflexivity.
    Qed.

    Lemma no_overlap_dtyp_array_different_indices:
      forall ix i ptrll elem_addr1 elem_addr2 sz τ,
        handle_gep_addr (DTYPE_Array sz τ) ptrll [DVALUE_I64 (repr 0); DVALUE_I64 ix] = inr elem_addr1 ->
        Int64.unsigned i <> Int64.unsigned ix ->
        handle_gep_addr (DTYPE_Array sz τ) ptrll [DVALUE_I64 (repr 0); DVALUE_I64 i] = inr elem_addr2 ->
        no_overlap_dtyp elem_addr1 τ elem_addr2 τ.
    Proof.
      intros ix i [ptr_b ptr_o] elem_addr1 elem_addr2 sz τ GEP1 NEQ GEP2.
      unfold handle_gep_addr in *.
      cbn in *; inv GEP1; inv GEP2.
      unfold no_overlap_dtyp. red.
      cbn.
      right.

      rewrite Integers.Int64.unsigned_repr; cycle 1.
      { split; [ lia | ]; apply int64_modulus_range. }


      replace (ptr_o + Z.of_N (sz * sizeof_dtyp τ) * 0 + Int64.unsigned ix * Z.of_N (sizeof_dtyp τ))
        with
          (ptr_o + Int64.unsigned ix * Z.of_N (sizeof_dtyp τ)) by lia.
      replace (ptr_o + Z.of_N (sz * sizeof_dtyp τ) * 0 + Int64.unsigned i * Z.of_N (sizeof_dtyp τ) + Z.of_N (sizeof_dtyp τ) - 1)
        with
          (ptr_o + Int64.unsigned i * Z.of_N (sizeof_dtyp τ) + Z.of_N (sizeof_dtyp τ) - 1) by lia.

      pose proof (ZArith_dec.Z_lt_le_dec (DynamicValues.Int64.unsigned i) (DynamicValues.Int64.unsigned ix)) as [LT | LE].
      - left.
        assert (Int64.unsigned i * Z.of_N (sizeof_dtyp τ) <= (Int64.unsigned ix * Z.of_N (sizeof_dtyp τ) - Z.of_N (sizeof_dtyp τ))).
        { replace (Int64.unsigned ix * Z.of_N (sizeof_dtyp τ) - Z.of_N (sizeof_dtyp τ)) with (Int64.unsigned ix * Z.of_N (sizeof_dtyp τ) - (1 * Z.of_N (sizeof_dtyp τ))) by lia.
          rewrite <- Z.mul_sub_distr_r.
          apply Zmult_le_compat_r; lia.
        }

        lia.
      - right.
        assert (Int64.unsigned ix * Z.of_N (sizeof_dtyp τ) <= (Int64.unsigned i * Z.of_N (sizeof_dtyp τ) - Z.of_N (sizeof_dtyp τ))).
        { replace (Int64.unsigned i * Z.of_N (sizeof_dtyp τ) - Z.of_N (sizeof_dtyp τ)) with (Int64.unsigned i * Z.of_N (sizeof_dtyp τ) - (1 * Z.of_N (sizeof_dtyp τ))) by lia.
          rewrite <- Z.mul_sub_distr_r.
          apply Zmult_le_compat_r; lia.
        }

        lia.
    Qed.

    Lemma add_logical_block_add_logical_block :
      forall off b1 b2 m,
        add_logical_block off b2 (add_logical_block off b1 m) =
        add_logical_block off b2 m.
    Proof.
      intros ? ? ? (m,s).
      unfold add_logical_block, add_logical_block_mem.
      setoid_rewrite insert_insert; done.
    Qed.


    Definition equiv_sum {A : Type} (R : A -> A -> Prop) : err A -> err A -> Prop :=
      fun ma ma' => match ma,ma' with
                    | inr a, inr a' => R a a'
                    | inl _, inl _ => True
                    | _, _ => False
                    end.

    Lemma write_write :
      forall (m : memory_stack) (v1 v2 : dvalue) (a : addr) τ,
        dvalue_has_dtyp v1 τ ->
        dvalue_has_dtyp v2 τ ->
        equiv_sum eq
          (bind (write m a v1) (fun m1 => write m1 a v2))
          (write m a v2).
    Proof.
      intros * T1 T2.
      unfold write; cbn.
      flatten_goal; repeat flatten_hyp Heq; try inv_sum.
      reflexivity.
      cbn in *.
      rewrite get_logical_block_of_add_logical_block.
      cbn. destruct m; cbn. unfold add_logical_block_mem.
      setoid_rewrite insert_insert. do 2 f_equiv.
      f_equiv. eapply map_leibniz.
      apply add_all_index_twice.
      erewrite 2 Zlength_correct.
      do 2 rewrite <- nat_N_Z.
      erewrite 2 sizeof_serialized; eauto.
    Qed.

    Lemma write_different_blocks :
      forall m m2 p p' v v2 dv2 τ τ',
        write m p v = inr m2 ->
        read m p' τ = inr v2 ->
        fst p <> fst p' ->
        uvalue_to_dvalue v2 = inr dv2 ->
        dvalue_has_dtyp dv2 τ ->
        dvalue_has_dtyp v τ' ->
        read m2 p' τ = inr v2.
    Proof.
      intros m m2 p p' v v2 dv2 τ τ' WRITE READ NEQ UVDV TYP1 TYP2.
      erewrite write_untouched; eauto.
      unfold no_overlap_dtyp.
      unfold no_overlap.
      left. auto.
    Qed.

End Memory_Stack_Theory.

Section PARAMS.
  Variable (E F G : Type -> Type).
  Context `{FailureE -< F} `{UBE -< F} `{PickE -< F}.
  Notation Effin := (E +' IntrinsicE +' MemoryE +' F).
  Notation Effout := (E +' F).
  Notation interp_memory := (@interp_memory E F _ _ _).

  Section Structural_Lemmas.

    Lemma interp_memory_bind :
      forall (R S : Type) (t : itree Effin R) (k : R -> itree Effin S) m,
        interp_memory (ITree.bind t k) m ≅
                      ITree.bind (interp_memory t m) (fun '(m',r) => interp_memory (k r) m').
    Proof.
      intros.
      unfold interp_memory.
      setoid_rewrite interp_state_bind.
      apply eq_itree_clo_bind with (UU := Logic.eq).
      reflexivity.
      intros [] [] EQ; inv EQ; reflexivity.
    Qed.

    Lemma interp_memory_ret :
      forall (R : Type) m (x: R),
        interp_memory (Ret x: itree Effin R) m ≅ Ret (m,x).
    Proof.
      intros; apply interp_state_ret.
    Qed.

    Lemma interp_memory_Tau :
      forall {R} (t: itree Effin R) m,
        interp_memory (Tau t) m ≅ Tau (interp_memory t m).
    Proof.
      intros.
      unfold interp_memory; rewrite interp_state_tau; reflexivity.
    Qed.

    Lemma interp_memory_vis_eqit:
      forall S X (kk : X -> itree Effin S) m
             (e : Effin X),
        interp_memory (Vis e kk) m ≅ ITree.bind (interp_memory_h e m) (fun sx => Tau (interp_memory (kk (snd sx)) (fst sx))).
    Proof.
      intros.
      unfold interp_memory.
      setoid_rewrite interp_state_vis.
      reflexivity.
    Qed.

    Lemma interp_memory_vis:
      forall m S X (kk : X -> itree Effin S) (e : Effin X),
        interp_memory (Vis e kk) m ≈ ITree.bind (interp_memory_h e m) (fun sx => interp_memory (kk (snd sx)) (fst sx)).
    Proof.
      intros.
      rewrite interp_memory_vis_eqit.
      apply eutt_eq_bind.
      intros ?; tau_steps; reflexivity.
    Qed.

    Lemma interp_memory_trigger:
      forall (m : memory_stack) X (e : Effin X),
        interp_memory (ITree.trigger e) m ≈ interp_memory_h e m.
    Proof.
      intros.
      unfold interp_memory.
      rewrite interp_state_trigger.
      reflexivity.
    Qed.

    Lemma interp_memory_bind_trigger_eqit:
      forall m S X (kk : X -> itree Effin S) (e : Effin X),
        interp_memory (ITree.bind (trigger e) kk) m ≅ ITree.bind (interp_memory_h e m) (fun sx => Tau (interp_memory (kk (snd sx)) (fst sx))).
    Proof.
      intros.
      unfold interp_memory.
      rewrite bind_trigger.
      setoid_rewrite interp_state_vis.
      reflexivity.
    Qed.

    Lemma interp_memory_bind_trigger:
      forall m S X
             (kk : X -> itree Effin S)
             (e : Effin X),
        interp_memory (ITree.bind (trigger e) kk) m ≈ ITree.bind (interp_memory_h e m) (fun sx => interp_memory (kk (snd sx)) (fst sx)).
    Proof.
      intros.
      rewrite interp_memory_bind_trigger_eqit.
      apply eutt_eq_bind.
      intros ?; tau_steps; reflexivity.
    Qed.

    #[global] Instance eutt_interp_memory {R}:
      Proper (eutt (R2 := R) Logic.eq ==> Logic.eq ==> eutt Logic.eq) interp_memory.
    Proof.
      repeat intro.
      unfold interp_memory.
      subst; rewrite H2.
      reflexivity.
    Qed.

    Lemma interp_memory_load :
      forall (m : memory_stack) (t : dtyp) (val : uvalue) (a : addr),
        read m a t = inr val ->
        interp_memory (trigger (Load t (DVALUE_Addr a))) m ≈ Ret (m, val).
    Proof.
      intros m t val a Hval.
      rewrite interp_memory_trigger.
      cbn. rewrite Hval.
      reflexivity.
    Qed.

    Lemma interp_memory_store :
      forall (m m' : memory_stack) (val : dvalue) (a : addr),
        write m a val = inr m' ->
        interp_memory (trigger (Store (DVALUE_Addr a) val)) m ≈ Ret (m', tt).
    Proof.
      intros m m' val a Hwrite.
      rewrite interp_memory_trigger.
      cbn. rewrite Hwrite.
      cbn. rewrite bind_ret_l.
      reflexivity.
    Qed.

    Lemma interp_memory_store_exists :
      forall (m : memory_stack) (t : dtyp) (val : dvalue) (a : addr),
        dvalue_has_dtyp val t ->
        dtyp_fits m a t ->
        exists m',
          write m a val = inr m' /\
          interp_memory (trigger (Store (DVALUE_Addr a) val)) m ≈ Ret (m', tt).
    Proof.
      intros m t val a TYP CAN.
      apply write_succeeds with (v:=val) in CAN as [m2 WRITE]; auto.
      exists m2. split; auto.

      eapply interp_memory_store; eauto.
    Qed.

    Lemma interp_memory_alloca :
      forall (m m' : memory_stack) (t : dtyp) (a : addr),
        allocate m t = inr (m', a) ->
        interp_memory (trigger (Alloca t)) m ≈ Ret (m', DVALUE_Addr a).
    Proof.
      intros m m' t a ALLOC.
      rewrite interp_memory_trigger.
      cbn in *. rewrite ALLOC. cbn.
      rewrite bind_ret_l.
      reflexivity.
    Qed.

    Lemma interp_memory_alloca_exists :
      forall (m : memory_stack) (t : dtyp),
        non_void t ->
        exists m' a', allocate m t = inr (m', a') /\
                      interp_memory (trigger (Alloca t)) m ≈ Ret (m', DVALUE_Addr a').
    Proof.
      intros m t NV.
      apply allocate_succeeds with (τ:=t) (m1:=m) in NV as [m' [a' ALLOC]].
      exists m'. exists a'.
      auto using interp_memory_alloca.
    Qed.

    Lemma get_array_succeeds_allocated : forall m a i t val,
        get_array_cell m a i t = inr val ->
        allocated a m.
    Proof.
      intros m [b o] i t val GET.
      cbn in GET.
      unfold get_logical_block in GET.
      unfold get_logical_block_mem in GET.
      break_match; inv GET.
      destruct l; cbn in *; inversion H3.
      red; cbn. destruct m; cbn in *.
      apply elem_of_dom; eauto.
    Qed.

    Lemma interp_memory_GEP_array_addr : forall t a (size :N) m val i ptr,
        get_array_cell m a i t = inr val ->
          handle_gep_addr (DTYPE_Array size t) a [DVALUE_I64 (Int64.repr 0); DVALUE_I64 (Int64.repr (Z.of_nat i))] = inr ptr ->
          interp_memory (trigger (GEP
                                    (DTYPE_Array size t)
                                    (DVALUE_Addr a)
                                    [DVALUE_I64 (repr 0); DVALUE_I64 (repr (Z.of_nat i))])) m
                        ≈ Ret (m, DVALUE_Addr ptr) /\
          read m ptr t = inr val.
    Proof.
      intros * GET. intros.
      pose proof get_array_succeeds_allocated _ _ _ _ GET as ALLOC.
      pose proof @read_array m size t i a ptr ALLOC as RARRAY.
      split.
      - rewrite interp_memory_trigger. cbn.
        cbn in RARRAY. destruct RARRAY. auto.
        rewrite H2. cbn.
        rewrite bind_ret_l. cbn. reflexivity.
      - destruct RARRAY. eauto.
        auto.
    Qed.

    Lemma interp_memory_GEP_array' : forall t a size m val i,
        get_array_cell m a i t = inr val ->
        exists ptr,
          interp_memory (trigger (GEP
                                    (DTYPE_Array size t)
                                    (DVALUE_Addr a)
                                    [DVALUE_I64 (Int64.repr 0); DVALUE_I64 (Int64.repr (Z.of_nat i))])) m
                        ≈ Ret (m, DVALUE_Addr ptr) /\
          handle_gep_addr (DTYPE_Array size t) a [DVALUE_I64 (repr 0); DVALUE_I64 (repr (Z.of_nat i))] = inr ptr /\
          read m ptr t = inr val.
    Proof.
      intros t a size m val i GET.
      pose proof get_array_succeeds_allocated _ _ _ _ GET as ALLOC.
      pose proof @read_array_exists m size t i a ALLOC as RARRAY.
      destruct RARRAY as (ptr & GEP & READ).
      exists ptr.
      split.
      - rewrite interp_memory_trigger. cbn.
        cbn in GEP.
        rewrite GEP.
        cbn.
        rewrite bind_ret_l.
        reflexivity.
      - rewrite <- GET. auto.
    Qed.

    Lemma interp_memory_GEP_array : forall t a size m val i,
        get_array_cell m a i t = inr val ->
        exists ptr,
          interp_memory (trigger (GEP
                                    (DTYPE_Array size t)
                                    (DVALUE_Addr a)
                                    [DVALUE_I64 (Int64.repr 0); DVALUE_I64 (Int64.repr (Z.of_nat i))])) m
                        ≈ Ret (m,DVALUE_Addr ptr) /\
          read m ptr t = inr val.
    Proof.
      intros t a size m val i GET.
      epose proof (@interp_memory_GEP_array' t a size m val i GET) as [ptr GEP].
      exists ptr. intuition.
    Qed.

    Lemma interp_memory_GEP_array_no_read_addr : forall t a size m i ptr,
      dtyp_fits m a (DTYPE_Array size t) ->
        handle_gep_addr (DTYPE_Array size t) a [DVALUE_I64 (Int64.repr 0); DVALUE_I64 (Int64.repr (Z.of_nat i))] = inr ptr ->
        interp_memory (trigger (GEP
                                  (DTYPE_Array size t)
                                  (DVALUE_Addr a)
                                  [DVALUE_I64 (Int64.repr 0); DVALUE_I64 (Int64.repr (Z.of_nat i))])) m
                      ≈ Ret (m, DVALUE_Addr ptr).
    Proof.
      intros * FITS HGEP.
      pose proof (dtyp_fits_allocated FITS) as ALLOC.
      pose proof @read_array m size t i a ptr ALLOC as RARRAY.
      destruct RARRAY. eauto.
      rewrite interp_memory_trigger. cbn.
      rewrite HGEP. cbn.
      rewrite bind_ret_l.
      reflexivity.
    Qed.

    Lemma interp_memory_GEP_array_no_read : forall t a size m i,
        dtyp_fits m a (DTYPE_Array size t) ->
        exists ptr,
          interp_memory (trigger (GEP
                                    (DTYPE_Array size t)
                                    (DVALUE_Addr a)
                                    [DVALUE_I64 (Int64.repr 0); DVALUE_I64 (Int64.repr (Z.of_nat i))])) m
                        ≈ Ret (m, DVALUE_Addr ptr) /\
          handle_gep_addr (DTYPE_Array size t) a [DVALUE_I64 (repr 0); DVALUE_I64 (repr (Z.of_nat i))] = inr ptr.
    Proof.
      intros t a size m i FITS.
      pose proof (dtyp_fits_allocated FITS) as ALLOC.
      pose proof @read_array_exists m size t i a ALLOC as RARRAY.
      destruct RARRAY as (ptr & GEP & READ).
      exists ptr.
      split.
      - rewrite interp_memory_trigger. cbn.
        cbn in GEP.
        rewrite GEP.
        cbn.
        rewrite bind_ret_l.
        reflexivity.
      - auto.
    Qed.

    Lemma no_overlap_reflect :
      forall x y s, reflect (no_overlap x s y s) (no_overlap_b x s y s).
    Proof.
      intros.
      destruct x as (x1 & x2).
      destruct y as (y1 & y2).
      match goal with
      | |- reflect ?L ?R => remember L as LHS; remember R as RHS
      end.
      destruct RHS; subst; constructor.
      - unfold no_overlap.
        unfold no_overlap_b in HeqRHS.
        cbn in *.
        destruct (x2 >? (y2 + s) - 1) eqn: EQ2.
        + rewrite Z.gtb_lt in EQ2. right. left.
          rewrite Z.gt_lt_iff. auto.
        + destruct (y2 >? (x2 + s) - 1) eqn: EQ3.
          * rewrite Z.gtb_lt in EQ3. right. right.
            rewrite Z.gt_lt_iff. auto.
          * destruct (x1 /~=? y1) eqn: EQ1.
            -- left. auto.
            -- cbn in HeqRHS. inversion HeqRHS.
      - unfold no_overlap.
        unfold no_overlap_b in HeqRHS.
        cbn in *.
        destruct (x1 /~=? y1) eqn: EQ1; try inversion HeqRHS.
        destruct (x2 >? (y2 + s) - 1) eqn: EQ2; try inversion HeqRHS.
        destruct (y2 >? (x2 + s) - 1) eqn: EQ3; try inversion HeqRHS.
        intuition;
          try first [rewrite Z.gt_lt_iff,<- Z.gtb_lt in H2;
                     rewrite H2 in EQ2; inversion EQ2 |
                     rewrite Z.gt_lt_iff,<- Z.gtb_lt in H2;
                     rewrite H2 in EQ3; inversion EQ3].
        (* TODO: Write symmetric variants of Z.gtb_lt lemmas. *)
    Qed.

    Lemma app_prefix_eq :
      forall (A : Type) (a b c: list A),
        a = b -> a ++ c = b ++ c.
    Proof.
      intros.
      rewrite H2. reflexivity.
    Qed.

    Lemma Zseq_app : forall (off : Z) (n : N),
        Zseq off (N.to_nat (N.succ n)) =
        Zseq off (N.to_nat n) ++ [off + Z.of_N n].
    Proof.
      intros.
      rewrite <- N.add_1_r.
      setoid_rewrite Nnat.N2Nat.inj_add; auto.
      unfold N.to_nat at 2. unfold Pos.to_nat. cbn.
      remember (N.to_nat n) as sz.
      assert (off_H: off + Z.of_N n = off + (Z.of_nat sz)). {
        rewrite Heqsz. rewrite N_nat_Z. reflexivity.
      }
      rewrite off_H.
      clear Heqsz off_H.
      revert off.
      induction sz.
      - intros. cbn. f_equiv.
        rewrite Zred_factor6 at 1.
        reflexivity.
      - intros.
        rewrite Nat.add_1_r in *.
        cbn in *.
        specialize (IHsz (Z.succ off)).
        rewrite IHsz.
        assert (Z.succ off + Z.of_nat sz = off + Z.pos (Pos.of_succ_nat sz)) as END by lia.
        rewrite END. reflexivity.
    Qed.

    Lemma Zseq_app_Z : forall off n : Z,
        0 <= n ->
        Zseq off (Z.to_nat (Z.succ n)) =
        Zseq off (Z.to_nat n) ++ [off + n].
    Proof.
      intros.
      unfold Z.succ.
      setoid_rewrite Z2Nat.inj_add; auto.
      unfold Z.to_nat at 2. unfold Pos.to_nat. cbn.
      remember (Z.to_nat n) as sz.
      assert (off_H: off + n = off + (Z.of_nat sz)). {
        rewrite Heqsz. rewrite Z2Nat.id. reflexivity. auto.
      }
      rewrite off_H.
      clear Heqsz off_H.
      revert off.
      induction sz.
      - intros. cbn. f_equiv.
        setoid_rewrite Zred_factor6 at 1.
        reflexivity.
      - intros.
        rewrite Nat.add_1_r in *.
        cbn in *.
        specialize (IHsz (Z.succ off)).
        rewrite IHsz.
        assert (Z.succ off + Z.of_nat sz = off + Z.pos (Pos.of_succ_nat sz)) by lia.
        rewrite H3. reflexivity.
      - lia.
    Qed.

    Lemma list_nth_z_length:
      forall A (l : list A) (a : A),
        list_nth_z (l ++ [a]) (Z.of_nat (length l)) = Some a.
    Proof.
      intros. revert a.
      remember (Datatypes.length l) as LEN. revert LEN HeqLEN.
      induction l.
      - intros; subst; auto.
      - intros; cbn.
        assert ((Datatypes.length (a :: l) <> 0)%nat).
        { cbn. lia. }
        rewrite <- HeqLEN in H2.
        destruct (zeq (Z.of_nat LEN) 0) eqn: LENZERO.
        + intuition. lia.
        + rewrite <- Nat2Z.inj_pred. 2 : lia.
          apply IHl. cbn in HeqLEN. lia.
    Qed.

    Lemma list_singleton_eq:
      forall A (a b: A), a = b -> [a] = [b].
    Proof.
      intros. rewrite H2. reflexivity.
    Qed.

    Lemma lookup_all_index_add_all_length_app:
      forall a sz l l' offset bytes (def : a),
        length l = sz ->
        lookup_all_index offset (N.of_nat sz)
                         (add_all_index (l ++ l') offset bytes) def =
        lookup_all_index offset (N.of_nat sz)
                         (add_all_index l offset bytes) def.
    Proof.
      intros*. revert def bytes offset sz.
      induction l.
      - intros; cbn. cbn in H2. subst. auto.
      - intros; cbn in *. subst.
        rewrite Nnat.Nat2N.inj_succ.
        rewrite 2 lookup_all_index_add.
        rewrite IHl. reflexivity. reflexivity.
    Qed.


    (* TODO: move *)
    Lemma Zlength_map:
      forall {A B} (f : A -> B) (l : list A),
        Zlength (map f l) = Zlength l.
    Proof.
      intros A B f l.
      induction l.
      - reflexivity.
      - rewrite map_cons.
        rewrite 2 Zlength_cons.
        rewrite IHl.
        reflexivity.
    Qed.

    (* TODO: move *)
    Lemma Zlength_app:
      forall {A} (l1 l2 : list A),
        Zlength (l1 ++ l2) = Zlength l1 + Zlength l2.
    Proof.
      intros A; induction l1; intros l2.
      - reflexivity.
      - (* TODO: avoid this... *)
        Opaque Zlength.
        cbn.
        rewrite 2 Zlength_cons.
        Transparent Zlength.
        rewrite Z.add_succ_l.
        rewrite IHl1.
        reflexivity.
    Qed.

    Lemma Zlength_Zseq:
      forall sz start,
        Zlength (Zseq start sz) = Z.of_nat sz.
    Proof.
      induction sz; intros start.
      - reflexivity.
      - (* TODO: avoid this... *)
        Opaque Zlength.
        cbn.
        rewrite Zlength_cons.
        Transparent Zlength.
        rewrite IHsz.
        lia.
    Qed.

    Lemma lookup_all_index_add_all_index :
      forall (sz : nat) src_bytes src_offset dst_bytes dst_offset def,
        (lookup_all_index dst_offset (N.of_nat sz)
                          (add_all_index
                             (lookup_all_index src_offset (N.of_nat sz) src_bytes def)
                             dst_offset dst_bytes) SUndef) =
        (lookup_all_index src_offset (N.of_nat sz) src_bytes def).
    Proof.
      intros sz src_bytes src_offset dst_bytes dst_offset def.
      induction sz.
      - cbn; reflexivity.
      - assert (N.of_nat (S sz) = N.succ (N.of_nat sz)). cbn.
        lia.
        rewrite H2.
        unfold lookup_all_index in *.
        remember (fun x0 =>
                    match src_bytes !! x0 with
                    | Some val => val
                    | None => def
                    end).
        rewrite 2 Zseq_app.
        unfold lookup_all_index in IHsz.
        + assert (match
                     lookup (dst_offset + Z.of_nat sz)
                            (add_all_index
                               (map s (Zseq src_offset (N.to_nat (N.of_nat sz)) ++
                                            [src_offset + Z.of_nat sz]))
                               dst_offset dst_bytes)
                   with
                   | Some val => val
                   | None => SUndef
                   end = s (src_offset + Z.of_nat sz)). {
            erewrite lookup_add_all_index_in. Unshelve.
            3 : {
              rewrite Z.add_simpl_l. rewrite list_nth_z_map.
              unfold option_map.
              rewrite <- (@Zseq_length sz src_offset) at 3.
              rewrite Nnat.Nat2N.id.
              rewrite list_nth_z_length. reflexivity.
            }
            reflexivity.
            - split.
              + rewrite <- Z.add_0_r at 1.
                rewrite <- Z.add_le_mono_l.
                apply Zle_0_nat.
              + rewrite <- Z.add_sub_assoc.
                rewrite <- Z.add_le_mono_l.
                rewrite Zlength_correct.
                rewrite map_length.
                rewrite app_length. cbn.
                rewrite Nnat.Nat2N.id.
                rewrite <- Zseq_length at 1.
                rewrite Nat2Z.inj_add. cbn.
                rewrite Z.add_simpl_r.
                apply Z.le_refl.
          }
          rewrite 2 map_app. cbn. rewrite map_app in H3.
          cbn in H3.
          apply list_singleton_eq in H3.
          rewrite nat_N_Z.
          rewrite H3. clear H3.
          eapply app_prefix_eq.
          remember (add_all_index
                      (map s (Zseq src_offset (N.to_nat (N.of_nat sz))) ++
                           [s (src_offset + Z.of_nat sz)]) dst_offset dst_bytes) as m.
          remember (add_all_index
                      (map s (Zseq src_offset (N.to_nat (N.of_nat sz))))
                      dst_offset dst_bytes) as m'.
          setoid_rewrite <- IHsz.
          match goal with
          | |- ?L = ?R => remember L as LHS; remember R as RHS
          end.
          assert (LHS = lookup_all_index dst_offset (N.of_nat sz) m SUndef).
          {
            rewrite HeqLHS. unfold lookup_all_index. subst.
            reflexivity.
          }
          assert (RHS = lookup_all_index dst_offset (N.of_nat sz) m' SUndef).
          {
            rewrite HeqRHS. unfold lookup_all_index. reflexivity.
          }
          rewrite H3, H4.
          rewrite Heqm, Heqm'.
          apply lookup_all_index_add_all_length_app.
          pose proof Zseq_length as Zseq_length_H.
          specialize (Zseq_length_H sz src_offset).
          rewrite Nnat.Nat2N.id.
          symmetry.
          rewrite map_length. auto.
    Qed.

    (* (* Note : For the current version of subevents, [interp_memory] must *) *)
(*     (*     have subevent clauses assumed in Context, or else the *) *)
(*     (*     [handle_intrinsic] handler will not get properly invoked. *) *)
    (* (* This is specialized to DTYPE_Array for practical *) *)
(*     (*    purposes. We could conjure a more complete definition later. *) *)
    (* Lemma interp_memory_intrinsic_memcpy : *)
    (*   forall (m : memory_stack) (dst src : Addr.addr) (sz : N) *)
    (*     (dst_val src_val : uvalue) (dτ : dtyp) volatile align, *)
    (*     0 <= Z.of_N (sz * sizeof_dtyp dτ) <= Int32.max_unsigned -> *)
    (*     read m dst (DTYPE_Array sz dτ) = inr dst_val -> *)
    (*     read m src (DTYPE_Array sz dτ) = inr src_val -> *)
    (*     no_overlap dst (Int32.unsigned (Int32.repr (Z.of_N (sz * sizeof_dtyp dτ)))) src *)
    (*                (Int32.unsigned (Int32.repr (Z.of_N (sz * sizeof_dtyp dτ)))) -> *)
    (*     exists m' s, *)
    (*       (interp_memory (trigger (Intrinsic DTYPE_Void *)
    (*                                          "llvm.memcpy.p0i8.p0i8.i32" *)
    (*                                          [DVALUE_Addr dst; DVALUE_Addr src; *)
    (*                                          DVALUE_I32 (Int32.repr (Z.of_N (sizeof_dtyp (DTYPE_Array sz dτ)))); *)
    (*                                          DVALUE_I32 align ; *)
    (*                                          DVALUE_I1 volatile])) m ≈ *)
    (*                      ret (m', s, DVALUE_None)) /\ *)
    (*       read (m', s) dst (DTYPE_Array sz dτ) = inr src_val. *)
    (* Proof. *)
    (*   intros m dst src i dst_val src_val dτ volatile align. *)
    (*   intros size_H  MEM_dst MEM_src NO_OVERLAP. *)
    (*   unfold read in MEM_dst, MEM_src. *)
    (*   destruct (get_logical_block m (fst dst)) eqn: HM_dst. cbn in MEM_dst. *)
    (*   destruct l. 2 : { inversion MEM_dst. } *)
    (*   destruct (get_logical_block m (fst src)) eqn: HM_src. cbn in MEM_src. *)
    (*   destruct l. 2 : { inversion MEM_src. } *)
    (*   setoid_rewrite interp_memory_trigger. *)
    (*   unfold interp_memory_h. cbn. *)
    (*   unfold resum, ReSum_id, id_, Id_IFun. *)
    (*   unfold handle_intrinsic. cbn. *)
    (*   destruct m. *)
    (*   destruct dst as (dst_base & dst_offset). *)
    (*   destruct src as (src_base & src_offset). *)
    (*   epose proof no_overlap_reflect as reflect_H. *)
    (*   eapply reflect_iff in reflect_H. *)
    (*   rewrite reflect_iff in NO_OVERLAP. clear reflect_H. *)
    (*   setoid_rewrite NO_OVERLAP. cbn in *. *)
    (*   setoid_rewrite HM_src. cbn. setoid_rewrite HM_dst. cbn. *)
    (*   eexists. exists f. *)
    (*   split; try reflexivity. *)
    (*   rewrite <- MEM_src. unfold read. cbn. *)
    (*   unfold read_in_mem_block. cbn. *)
    (*   rewrite Int32.unsigned_repr. 2 : apply size_H. *)
    (*   rewrite get_logical_block_of_add_logical_block_mem. *)
    (*   pose proof lookup_all_index_add_all_index. *)
    (*   specialize (H2 (N.to_nat (i * sizeof_dtyp dτ))). *)
    (*   rewrite Nnat.N2Nat.id in H2. *)
    (*   rewrite N2Z.id. *)
    (*   rewrite H2. reflexivity. *)
    (*   apply no_overlap_reflect. Unshelve. unfold addr, Addr.addr. *)
    (*   exact (0, 0). exact (0, 0). eauto. *)
    (* Qed. *)

  End Structural_Lemmas.

  (* TODO: move to appropriate place in this file *)
  Lemma handle_gep_addr_array_same_block :
    forall ptr ptr_elem ix sz τ,
      handle_gep_addr (DTYPE_Array sz τ) ptr
                      [DVALUE_I64 (repr 0); DVALUE_I64 ix] = inr ptr_elem ->
      fst ptr = fst ptr_elem.
  Proof.
    intros [ptrb ptro] [ptr_elemb ptr_elemo] ix sz τ GEP.
    cbn in GEP.
    inversion GEP; subst.
    reflexivity.
  Qed.

  Lemma unsigned_repr_0_i64 :
    DynamicValues.Int64.unsigned (DynamicValues.Int64.repr 0) = 0.
  Proof.
    apply Integers.Int64.unsigned_zero.
  Qed.


  Lemma handle_gep_addr_array_offset :
    forall ptr ptr_elem ix sz τ,
      handle_gep_addr (DTYPE_Array sz τ) ptr
                      [DVALUE_I64 (repr 0); DVALUE_I64 ix] = inr ptr_elem ->
      snd ptr + DynamicValues.Int64.unsigned ix * Z.of_N (sizeof_dtyp τ) = snd ptr_elem.
  Proof.
    intros [ptrb ptro] [ptr_elemb ptr_elemo] ix sz τ GEP.
    cbn in GEP.
    inversion GEP; subst.
    cbn.
    rewrite unsigned_repr_0_i64.
    lia.
  Qed.

 Lemma dtyp_fits_array_elem :
    forall m ptr ptr_elem ix (sz : N) τ,
      dtyp_fits m ptr (DTYPE_Array sz τ) ->
      handle_gep_addr (DTYPE_Array sz τ) ptr
                      [DVALUE_I64 (repr 0); DVALUE_I64 ix] = inr ptr_elem ->
      Int64.intval ix < Z.of_N sz ->
      dtyp_fits m ptr_elem τ.
  Proof.
    intros m ptr ptr_elem ix sz τ FITS GEP SZ.
    cbn in GEP.
    unfold dtyp_fits in *.
    destruct FITS as (sz' & bytes & cid & BLOCK & BOUND).
    exists sz'. exists bytes. exists cid.
    split.
    erewrite <- handle_gep_addr_array_same_block; eauto.
    erewrite <- handle_gep_addr_array_offset; eauto.
    cbn in BOUND.
    assert (Int64.unsigned ix = Int64.intval ix) by reflexivity.
    rewrite H2.
    assert (1 + Int64.intval ix <= Z.of_N sz) by lia.
    rewrite <- Z.add_assoc.
    assert (snd ptr + (Int64.intval ix * Z.of_N (sizeof_dtyp τ) + Z.of_N (sizeof_dtyp τ)) <= snd ptr + Z.of_N (sz * sizeof_dtyp τ)).
    { eapply Zorder.Zplus_le_compat_l.
      replace (Int64.intval ix * Z.of_N (sizeof_dtyp τ) + Z.of_N (sizeof_dtyp τ)) with ((1 + Int64.intval ix) * Z.of_N (sizeof_dtyp τ)).
      rewrite N2Z.inj_mul.
      eapply Z.mul_le_mono_nonneg_r; lia.
      lia.
    }
    lia.
  Qed.

End PARAMS.
End MEMORY_THEORY.

Module Make(LLVMEvents : LLVM_INTERACTIONS(Addr)) <: MEMORY_THEORY(LLVMEvents).
Include MEMORY_THEORY(LLVMEvents).
End Make.
