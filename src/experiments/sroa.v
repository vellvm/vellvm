Require Import minillvm_bitwise.
Require Import List.
Require Import Util.
Require Import ZArith.
Require Import Coqlib.
Require Import CoqEqDec.
Require Import block_model.
Import ListNotations.

(* Replacement of aggregates (structs and arrays) by scalars. *)

Section SROA.
  Variable (block : Type).
  Variable (do_op : op -> list trit -> list trit -> option (list trit)).
  Variable (TGT : Target).

  (* We're already using lower_val to break aggregate loads and stores down.
     So, what can we prove? Replacement of a complex load/store by a series of
     simpler ones shouldn't be *too* bad, but what's the analysis involved? *)

  Definition pad_and_add o a n :=
    match pad_offset do_op o a with
    | Some o' => do_op Add o' (encode_nat n (8 * ptr_size))
    | None => None
    end.

  Hypothesis (add_normal : forall v1 v2 i1 i2, decode_trits v1 = Some i1 ->
    decode_trits v2 = Some i2 -> exists v3, do_op Add v1 v2 = Some v3 /\
    decode_trits v3 = Some (i1 + i2)).
  Hypothesis (pad_normal : forall v1 v2 i1 i2, decode_trits v1 = Some i1 ->
    decode_trits v2 = Some i2 -> i2 > 0 -> exists v3, do_op Pad v1 v2 = Some v3 
    /\ decode_trits v3 = Some (let n := i1 mod i2 in if eq_dec n 0 then i1
                               else i1 + (i2 - n))).

  Lemma pad_and_add_normal : forall v a n o
    (Ha_lt : Z.of_nat a < two_power_nat (8 * ptr_size - 1))
    (Hn_lt : Z.of_nat n < two_power_nat (8 * ptr_size - 1))
    (Ha_nz : a <> O)
    (Ho : decode_trits v = Some (Z.of_nat o)),
    exists v', pad_and_add v a n = Some v' /\ 
               decode_trits v' = Some (Z.of_nat (padn o a + n)).
  Proof.
    unfold pad_and_add, pad_offset; intros.
    exploit (@encode_decode (8 * ptr_size) (Z_of_nat a)).
    { generalize ptr_size_pos; omega. }
    { split; auto; transitivity 0; [apply Pos2Z.neg_is_nonpos | omega]. }
    intro Ha; specialize (pad_normal _ _ _ _ Ho Ha); use pad_normal; [|omega].
    destruct pad_normal as [v3 [Hpad Hv3]]; setoid_rewrite Hpad.
    exploit (@encode_decode (8 * ptr_size) (Z_of_nat n)).
    { generalize ptr_size_pos; omega. }
    { split; auto; transitivity 0; [apply Pos2Z.neg_is_nonpos | omega]. }
    intro Hn; specialize (add_normal _ _ _ _ Hv3 Hn).
    destruct add_normal as [v4 [Hadd Hv4]]; setoid_rewrite Hadd.
    repeat eexists. rewrite Hv4; unfold padn; simpl.
    rewrite <- mod_Zmod; auto.
    rewrite <- Nat2Z.inj_sub.
    destruct (NPeano.modulo o a); clear; clarify;
      repeat rewrite Nat2Z.inj_add; auto.
    generalize (NPeano.mod_bound_pos o a); omega.
  Qed.

  Fixpoint emit_split_loads (o : list trit) (ty : type) :=
    match ty with
    | Array_ty n t => fold_right (fun x ol => 
        match (pad_and_add o (first_align t) (x * size_of t), ol) with
        | (Some o', Some l) =>
            match emit_split_loads o' t with
            | Some l' => Some (l' ++ l)
            | None => None
            end
        | _ => None
        end) (Some []) (interval 0 n)
    | Struct_ty ts =>
        (fix emit_aux o ts :=
           match ts with
           | [] => Some []
           | t :: rest =>
               match (emit_split_loads o t,
                      pad_and_add o (first_align t) (size_of t)) with
               | (Some l, Some o') =>
                   match emit_aux o' rest with
                   | Some l' => Some (l ++ l')
                   | None => None
                   end
               | _ => None
               end
           end) o ts
    | _ => Some [(ty, o)]
    end.

  Fixpoint emit_split_stores (o : list trit) (ty : type) (v : const block) :=
    let emit_aux := (fix emit_aux o ts vs {struct vs} :=
           match (ts, vs) with
           | ([], []) => Some []
           | (t :: trest, v :: vrest) =>
               match (emit_split_stores o t v,
                      pad_and_add o (first_align t) (size_of t)) with
               | (Some l, Some o') =>
                   match emit_aux o' trest vrest with
                   | Some l' => Some (l ++ l')
                   | None => None
                   end
               | _ => None
               end
           | _ => None
           end) in
    match (ty, v) with
    | (Array_ty n t, Complex_c vs) => emit_aux o (replicate t n) vs
    | (Struct_ty ts, Complex_c vs) => emit_aux o ts vs
    | (Int_ty _, Int_c _) => Some [(ty, o, v)]
    | (Pointer_ty _, Pointer_c _) => Some [(ty, o, v)]
    | _ => None
    end.

  Fixpoint emit_split_list_stores o ts vs {struct vs} :=
    match (ts, vs) with
    | ([], []) => Some []
    | (t :: trest, v :: vrest) =>
        match (emit_split_stores o t v, 
               pad_and_add o (first_align t) (size_of t)) with
        | (Some l, Some o') =>
            match emit_split_list_stores o' trest vrest with
            | Some l' => Some (l ++ l')
            | None => None
            end
        | _ => None
        end
    | _ => None
    end.

  Print lower_val.

  Fixpoint make_lower (l : list (type * list trit * const block)):=
    match l with
    | [] => Some []
    | (ty, o, v) :: rest =>
        match (lower_val ty (Z.to_nat (decode_0_trits o)) v, make_lower rest)
        with
        | (Some l, Some l') => Some (l ++ l')
        | _ => None
        end
    end.

  Lemma make_lower_app : forall l1 l2 r, make_lower (l1 ++ l2) = Some r <->
    exists r1 r2, make_lower l1 = Some r1 /\ make_lower l2 = Some r2 /\
      r = r1 ++ r2.
  Proof.
    induction l1; clarify.
    - split; clarify; eauto.
    - destruct a as ((ty, o), v); clarify.
      destruct (lower_val ty (Z.to_nat (decode_0_trits o)) v);
        [|split; clarify].
      destruct (make_lower (l1 ++ l2)) eqn: Hmake.
      + rewrite IHl1 in Hmake; split; clarsimp.
        repeat eexists; clarsimp.
      + split; clarify.
        specialize (IHl1 l2 (x1 ++ x0)); destruct IHl1 as [_ IHl1];
          rewrite IHl1 in Hmake; clarify; eauto.
  Qed.

  Lemma emit_val : forall v o ty l (Hpos : 0 <= decode_0_trits o)
    (Hl : emit_split_stores o ty v = Some l) (Ho : decode_trits o <> None)
    (Hsane_size : (size_of ty < NPeano.pow 2 (8 * ptr_size - 1))%nat),
    lower_val ty (Z.to_nat (decode_0_trits o)) v = make_lower l.
  Proof.
    einduction v using const_ind'; intros.
    - destruct ty; clarsimp.
    - destruct ty; clarsimp.
    - instantiate (1 := fun vs => forall o ts l (Hpos : 0 <= decode_0_trits o)
        (Hl : emit_split_list_stores o ts vs = Some l)
        (Ho : decode_trits o <> None) (Hsane_size : Forall (fun t => 
          (size_of t < NPeano.pow 2 (8 * ptr_size - 1))%nat) ts),
        lower_vals ts (Z.to_nat (decode_0_trits o)) vs = make_lower l);
      clarify.
    - clarify.
      destruct ts; clarify.
      inversion Hsane_size; clarify.
      exploit IHc; eauto; clarify.
      rewrite lower_pad; destruct (lower_val t (Z.to_nat (decode_0_trits o)) c)
        eqn: Hlower.
      generalize (pad_and_add_normal o (first_align t) (size_of t)
        (Z.to_nat (decode_0_trits o))); intro Hx0; clarify.
      use Hx0. use Hx0. use Hx0.
      rewrite Z2Nat.id in Hx0; auto.
      use Hx0.
      clarsimp.
      exploit decode_0_decode; eauto; intro Hdec.
      exploit IHc0; try (apply Hl221); eauto.
      { rewrite <- Hdec; omega. }
      { clarsimp. }
      rewrite <- Hdec, Nat2Z.id in *.
      destruct (lower_vals ts
        (padn (Z.to_nat (decode_0_trits o)) (first_align t) + size_of t) rest);
        clarify.
      symmetry; rewrite make_lower_app.
      repeat eexists; eauto.
      { destruct (make_lower (x ++ x1)) eqn: Hmake; auto.
        rewrite make_lower_app in Hmake; clarsimp. }
      { destruct (decode_trits o) eqn: Hdec; clarify.
        exploit decode_0_decode; eauto; clarify. }
      { generalize (first_align_pos t); omega. }
      { rewrite <- two_power_pow; apply inj_lt; auto. }
      { rewrite <- two_power_pow; apply inj_lt, first_align_sane. }
      { destruct (make_lower (x ++ x1)) eqn: Hmake; auto.
        rewrite make_lower_app in Hmake; clarsimp. }
    - destruct ty; clarify; exploit IHc; eauto.
      + rewrite Forall_forall; intros.
        exploit (@in_replicate); eauto; clarify.
        eapply le_lt_trans; [|apply Hsane_size].
        destruct n; clarify.
        etransitivity; [apply padn_ge|].
        instantiate (1 := first_align ty).
        generalize (mult_O_le (padn (size_of ty) (first_align ty)) (S n));
          clarify.
      + rewrite Forall_forall; intros.
        eapply le_lt_trans; [|apply Hsane_size].
        generalize (struct_size x l0); clarify.
  Qed.
    
  Corollary emit_load : forall v o ty l (Hpos : 0 <= decode_0_trits o)
    (Hl : emit_split_stores o ty v = Some l) (Ho : decode_trits o <> None)
    (Hsane_size : (size_of ty < NPeano.pow 2 (8 * ptr_size - 1))%nat)
    b, mk_read ty b (Z.to_nat (decode_0_trits o)) v =
      match make_lower l with Some m => Some (map
        (fun (x : nat * mem_data _) => let (o, v) := x in MRead (b, o) v) m)
      | None => None end.
  Proof. unfold mk_read; intros; erewrite emit_val; eauto. Qed.
    
  Corollary emit_store : forall v o ty l (Hpos : 0 <= decode_0_trits o)
    (Hl : emit_split_stores o ty v = Some l) (Ho : decode_trits o <> None)
    (Hsane_size : (size_of ty < NPeano.pow 2 (8 * ptr_size - 1))%nat)
    b, mk_write ty b (Z.to_nat (decode_0_trits o)) v =
      match make_lower l with Some m => Some (map
        (fun (x : nat * mem_data _) => let (o, v) := x in MWrite (b, o) v) m)
      | None => None end.
  Proof. unfold mk_write; intros; erewrite emit_val; eauto. Qed.

End SROA.