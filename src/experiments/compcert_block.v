Require Import Memory.
Require Import block_model.
Require Import Values.
Require Import ZArith.
Require Import CoqEqDec.
Require Import Coq.Classes.EquivDec.
Require Import AST.
Require Import Integers.
Require Import Equalities.
Require Import Util.
Require Import SetsAndMaps.
Require Import List.
Import ListNotations.
Require Import Coqlib.
Require Import Memdata.

Set Implicit Arguments.

Instance memval_eq : @EqDec memval eq eq_equivalence.
Proof. 
  eq_dec_inst.
  apply Byte.eq_dec.
  apply Int.eq_dec.
Qed.

Instance block_eq : @EqDec block eq eq_equivalence.
Proof. eq_dec_inst. Qed.

Instance Z_eq : @EqDec Z eq eq_equivalence.
Proof. eq_dec_inst. Qed.

Instance bo_eq : @EqDec (block * Z)%type eq eq_equivalence.
Proof. eq_dec_inst. Qed.

Module CC_BlockInstance (MBlock : UsualDecidableType).
  Import Mem.

  Definition mblock := MBlock.t.
  Instance mblock_eq : @EqDec mblock eq eq_equivalence.
  Proof. eq_dec_inst; apply MBlock.eq_dec. Qed.

  Lemma range_perm_storebytes_1 : forall m1 b ofs v m2
    (Hstore : storebytes m1 b ofs v = Some m2) b' lo hi k p
    (Hrange_perm : range_perm m1 b' lo hi k p), 
    range_perm m2 b' lo hi k p.
  Proof.
    repeat intro.
    exploit Hrange_perm; eauto; intro Hperm.
    eapply perm_storebytes_1; eauto.
  Qed.

  Lemma range_perm_storebytes_2 : forall m1 b ofs v m2
    (Hstore : storebytes m1 b ofs v = Some m2) b' lo hi k p
    (Hrange_perm : range_perm m2 b' lo hi k p), 
    range_perm m1 b' lo hi k p.
  Proof.
    repeat intro.
    exploit Hrange_perm; eauto; intro Hperm.
    eapply perm_storebytes_2; eauto.
  Qed.

  Lemma range_perm_storebytes_iff : forall m1 b ofs v m2
    (Hstore : storebytes m1 b ofs v = Some m2) b' lo hi k p,
    range_perm m1 b' lo hi k p <-> 
    range_perm m2 b' lo hi k p.
  Proof.
    intros; split; [eapply range_perm_storebytes_1 | 
      eapply range_perm_storebytes_2]; eauto.
  Qed.

  Lemma perm_storebytes_iff : forall m1 b ofs v m2
    (Hstore : storebytes m1 b ofs v = Some m2) b' o k p,
    perm m1 b' o k p <-> perm m2 b' o k p.
  Proof.
    intros; split; [eapply perm_storebytes_1 | eapply perm_storebytes_2]; eauto.
  Qed.

  Lemma range_perm_alloc_1 : forall m1 b lo hi m2
    (Halloc : alloc m1 lo hi = (m2, b)) b' lo hi k p
    (Hrange_perm : range_perm m1 b' lo hi k p), range_perm m2 b' lo hi k p.
  Proof.
    repeat intro.
    exploit Hrange_perm; eauto; intro Hperm.
    eapply perm_alloc_1; eauto.
  Qed.

  Lemma range_perm_alloc_2 : forall m1 b lo hi m2
    (Halloc : alloc m1 lo hi = (m2, b)) b' (Hdiff : b <> b') lo hi k p
    (Hrange_perm : range_perm m2 b' lo hi k p), range_perm m1 b' lo hi k p.
  Proof.
    repeat intro.
    exploit Hrange_perm; eauto; intro Hperm.
    eapply perm_alloc_4; eauto.
  Qed.

  Lemma range_perm_alloc_iff : forall m1 b lo hi m2
    (Halloc : alloc m1 lo hi = (m2, b)) b' (Hdiff : b <> b') lo hi k p,
    range_perm m1 b' lo hi k p <-> range_perm m2 b' lo hi k p.
  Proof.
    intros; split; [eapply range_perm_alloc_1 | eapply range_perm_alloc_2]; 
      eauto.
  Qed.

  Lemma perm_alloc_iff : forall m1 b lo hi m2
    (Halloc : alloc m1 lo hi = (m2, b)) b' (Hdiff : b <> b') o k p,
    perm m1 b' o k p <-> perm m2 b' o k p.
  Proof.
    intros; split; intro; [eapply perm_alloc_1 | eapply perm_alloc_4]; eauto.
  Qed.

  Lemma range_perm_free_1 : forall m1 b lo hi m2
    (Hfree : free m1 b lo hi = Some m2) b' (Hdiff : b <> b') lo hi k p
    (Hrange_perm : range_perm m1 b' lo hi k p), range_perm m2 b' lo hi k p.
  Proof.
    repeat intro.
    exploit Hrange_perm; eauto; intro Hperm.
    eapply perm_free_1; eauto.
  Qed.

  Lemma range_perm_free_2 : forall m1 b lo hi m2
    (Hfree : free m1 b lo hi = Some m2) b' lo hi k p
    (Hrange_perm : range_perm m2 b' lo hi k p), range_perm m1 b' lo hi k p.
  Proof.
    repeat intro.
    exploit Hrange_perm; eauto; intro Hperm.
    eapply perm_free_3; eauto.
  Qed.

  Lemma range_perm_free_iff : forall m1 b lo hi m2
    (Hfree : free m1 b lo hi = Some m2) b' (Hdiff : b <> b') lo hi k p,
    range_perm m1 b' lo hi k p <-> range_perm m2 b' lo hi k p.
  Proof.
    intros; split; [eapply range_perm_free_1 | eapply range_perm_free_2]; eauto.
  Qed.

  Lemma perm_free_iff : forall m1 b lo hi m2
    (Hfree : free m1 b lo hi = Some m2) b' (Hdiff : b <> b') o k p,
    perm m1 b' o k p <-> perm m2 b' o k p.
  Proof.
    intros; split; [eapply perm_free_1 | eapply perm_free_3]; eauto.
  Qed.
  
  (* These axioms are absent in Memtype. We can translate between byte and chunk
     operations only when we operate at the chunk size of the block. *)
  Lemma loadbytes_alloc_other:
    forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
    forall b' ofs n v,
    loadbytes m1 b' ofs n = Some v ->
    loadbytes m2 b' ofs n = Some v.
  Proof.
    intros.
    eapply loadbytes_unchanged_on; eauto.
    - eapply alloc_unchanged_on; eauto.
    - instantiate (1 := fun _ _ => True); clarify.
  Qed.

  Lemma loadbytes_alloc_unchanged:
    forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
    forall b' ofs n (Hvalid : valid_block m1 b'),
    loadbytes m1 b' ofs n = loadbytes m2 b' ofs n.
  Proof.
    intros.
    destruct (loadbytes m1 b' ofs n) eqn: Hload1.
    - symmetry; eapply loadbytes_alloc_other; eauto.
    - destruct (loadbytes m2 b' ofs n) eqn: Hload2; auto.
      generalize (loadbytes_range_perm _ _ _ _ _ Hload2); intro perm.
      rewrite <- range_perm_alloc_iff in perm; eauto.
      exploit range_perm_loadbytes; eauto; clarify.
      { intro; clarify.
        exploit alloc_result; eauto 2; clarify.
        exploit Plt_strict; eauto. }
  Qed.

  Lemma get_init : forall n v ofs, getN n ofs (Maps.ZMap.init v) = 
    replicate v n.
  Proof.
    induction n; clarify.
    rewrite Maps.ZMap.gi, IHn; auto.
  Qed.
  Hint Resolve get_init.

  Transparent alloc loadbytes.

  Lemma loadbytes_alloc_same:
    forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
    forall ofs v n,
    loadbytes m2 b ofs n = Some v ->
    v = replicate Undef (nat_of_Z n).
  Proof.
    unfold alloc, loadbytes; clarify.
    rewrite Maps.PMap.gss; auto.
  Qed.

  Lemma loadbytes_free:
    forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
    forall b ofs n,
    b <> bf \/ lo >= hi \/ ofs + n <= lo \/ hi <= ofs ->
    loadbytes m2 b ofs n = loadbytes m1 b ofs n.
  Proof.
    intros.
    exploit (free_unchanged_on (fun bf i => b = bf /\ i >= ofs /\ i < ofs + n));
      eauto.
    { repeat intro; clarify; omega. }
    intro Hunchanged.
    destruct (loadbytes m1 b ofs n) eqn: Hload1.
    - eapply loadbytes_unchanged_on; eauto; clarify; omega.
    - destruct (loadbytes m2 b ofs n) eqn: Hload2; auto.
      exploit loadbytes_unchanged_on; try (apply Hload2).
      + inversion Hunchanged.
        constructor; intros.
        * rewrite unchanged_on_perm0; try reflexivity.
          apply H1.
          eauto 3 with mem.
        * rewrite unchanged_on_contents0; auto.
          rewrite unchanged_on_perm0; auto.
          eauto 3 with mem.
      + clarify; omega.
      + intro Hload1'; rewrite Hload1' in Hload1; clarify.
  Qed.

  Lemma loadbytes_valid_block : forall m b o n v (Hpos : n > 0)
    (Hload : loadbytes m b o n = Some v), valid_block m b.
  Proof.
    intros; eapply perm_valid_block.
    eapply loadbytes_range_perm; eauto.
    instantiate (1 := o); omega.
  Qed.

  Opaque alloc loadbytes.

  (* memory model instance *)
  Module Map := FMap' MBlock.

  Record mem_rec := { m : mem; map : Map.t (block * nat) }.
  Definition empty_rec := {| m := empty; map := Map.empty _ |}.

  Definition CC_do_op mrec op := match op with
  | MRead (b, o) v => 
      match Map.find b (map mrec) with
      | Some (b, _) => 
          match loadbytes (m mrec) b (Z.of_nat o) 1 with
          | Some [v'] => if eq_dec v v' then Some mrec else None
          | _ => None
          end
      | None => None
      end
  | MWrite (b, o) v => 
      match Map.find b (map mrec) with None => None
      | Some (b, _) => 
          match storebytes (m mrec) b (Z.of_nat o) [v] with 
          | Some m' => Some {| m := m'; map := map mrec |} 
          | None => None
          end
      end
  | MAlloc b n => 
      match Map.find b (map mrec) with 
      | Some _ => None
      | None => let (m, b') := alloc (m mrec) 0 (Z.of_nat n) in 
                   Some {| m := m; map := Map.add b (b', n) (map mrec) |}
      end
  | MFree b => 
      match Map.find b (map mrec) with None => None
      | Some (b', n) => 
          match free (m mrec) b' 0 (Z.of_nat n) with
          | Some m' => Some {| m := m'; map := Map.remove b (map mrec) |}
          | None => None
          end
      end
  end.

  Fixpoint CC_do_ops mrec ops := match ops with
  | [] => Some mrec
  | op :: rest => match CC_do_op mrec op with 
                  | Some mrec' => CC_do_ops mrec' rest
                  | None => None
                  end
  end.

  Definition CC_can_do ops op := 
    match CC_do_ops empty_rec (rev ops ++ [op]) with
    | Some _ => true | None => false end.

  Definition CC_consistent ops := 
    match CC_do_ops empty_rec ops with
    | Some _ => True | None => False end.

  Lemma CC_ops_app : forall ops1 ops2 m, CC_do_ops m (ops1 ++ ops2) =
    match CC_do_ops m ops1 with Some m' => CC_do_ops m' ops2 | None => None end.
  Proof. 
    induction ops1; clarify; eauto.
    destruct (CC_do_op m0 a); clarify.
  Qed.

  Definition valid_mem mr := forall x b n, Map.find x (map mr) = Some (b, n) ->
    valid_block (m mr) b.
  Definition inj_mem mr := forall x y b n n', 
    Map.find x (map mr) = Some (b, n) -> Map.find y (map mr) = Some (b, n') -> 
    x = y.

  Lemma do_op_valid : forall m1 op m2 (Hop : CC_do_op m1 op = Some m2)
    (Hvalid : valid_mem m1), valid_mem m2.
  Proof.
    repeat intro.
    specialize (Hvalid x b); unfold valid_block in *; destruct op; clarify.
    - destruct p; clarify.
      destruct x0; clarify.
      destruct x0; clarify; eauto.
    - destruct p; clarify.
      destruct x0; clarify.
      erewrite nextblock_storebytes; eauto.
    - destruct (alloc (m m1) 0 (Z.of_nat n0)) eqn: alloc1; 
        inversion Hop; clarify.
      erewrite nextblock_alloc; eauto.
      rewrite Map.F.F.add_o in *; clarify.
      destruct (Map.Map.E.eq_dec k x); clarify.
      + exploit alloc_result; eauto; clarify.
        apply Pos.lt_succ_diag_r.      
      + apply Pos.lt_lt_succ; eapply Hvalid; eauto.
    - destruct x0; clarify.
      rewrite Map.F.F.remove_o in *; clarify.
      erewrite nextblock_free; eauto.
  Qed.

  Lemma do_ops_valid : forall ops m1 m2 (Hops : CC_do_ops m1 ops = Some m2)
    (Hvalid : valid_mem m1), valid_mem m2.
  Proof.
    induction ops; clarify.
    eapply IHops; eauto.
    eapply do_op_valid; eauto.
  Qed.

  Lemma can_do_valid : forall ops m'
    (Hops : CC_do_ops empty_rec ops = Some m'),
    valid_mem m'.
  Proof. intros; eapply do_ops_valid; eauto; clarify. Qed.

  Lemma do_op_inj : forall m1 op m2 (Hop : CC_do_op m1 op = Some m2)
    (Hvalid : valid_mem m1) (Hinj : inj_mem m1), inj_mem m2.
  Proof.
    repeat intro.
    specialize (Hinj x y b); destruct op; clarify.
    - destruct p; clarify.
      destruct x0; clarify.
      destruct x0; clarify; eauto.
    - destruct p; clarify.
      destruct x0; clarify; eauto.
    - destruct (alloc (m m1) 0 (Z.of_nat n0)) eqn: alloc1; inversion Hop; 
       clarify.
      exploit alloc_result; eauto 1; clarify.
      rewrite Map.F.F.add_o in *; destruct (Map.Map.E.eq_dec k x); 
        destruct (Map.Map.E.eq_dec k y); clarify.
      + specialize (Hvalid _ _ _ H0); exploit Pos.lt_irrefl; eauto 1; clarify.
      + specialize (Hvalid _ _ _ H); exploit Pos.lt_irrefl; eauto 1; clarify.
      + eauto.
    - destruct x0; clarify.
      rewrite Map.F.F.remove_o in *; clarify; eauto.
  Qed.

  Lemma do_ops_inj : forall ops m1 m2 (Hops : CC_do_ops m1 ops = Some m2)
    (Hvalid : valid_mem m1) (Hinj : inj_mem m1), inj_mem m2.
  Proof.
    induction ops; clarify.
    eapply IHops; eauto.
    eapply do_op_valid; eauto.
    eapply do_op_inj; eauto.
  Qed.

  Lemma can_do_inj : forall ops m'
    (Hops : CC_do_ops empty_rec ops = Some m'),
    inj_mem m'.
  Proof. intros; eapply do_ops_inj; eauto; clarify. Qed.

  (* The relationship between two equivalent memories. *)
  Definition matching mrec1 mrec2 := forall mb,
    match Map.find mb (map mrec1) with
    | Some (b1, n) => exists b2, Map.find mb (map mrec2) = Some (b2, n) /\
        (forall o, Maps.ZMap.get o (Maps.PMap.get b1 (mem_contents (m mrec1))) =
                   Maps.ZMap.get o (Maps.PMap.get b2 (mem_contents (m mrec2))))
     /\ (forall o k, Maps.PMap.get b1 (mem_access (m mrec1)) o k =
                     Maps.PMap.get b2 (mem_access (m mrec2)) o k)
    | None => Map.find mb (map mrec2) = None
    end.

  Transparent loadbytes storebytes alloc free.

  Ltac dec_perm := match goal with 
    | H: context[if range_perm_dec ?m ?b ?lo ?hi ?k ?p then _ else _] |- _ =>
      destruct (range_perm_dec m b lo hi k p); clarify
    | H: context[match range_perm_dec ?m ?b ?lo ?hi ?k ?p with 
                     left _ => _ | right _ => _ end] |- _ =>
      destruct (range_perm_dec m b lo hi k p); clarify
    | |-context[if range_perm_dec ?m ?b ?lo ?hi ?k ?p then _ else _] =>
      destruct (range_perm_dec m b lo hi k p); clarify
    | |-context[match range_perm_dec ?m ?b ?lo ?hi ?k ?p with 
                     left _ => _ | right _ => _ end] =>
      destruct (range_perm_dec m b lo hi k p); clarify end.

  Lemma matching_do_op : forall mr1 mr2 
    (Hinj1 : inj_mem mr1) (Hinj2 : inj_mem mr2) 
    (Hvalid1 : valid_mem mr1) (Hvalid2 : valid_mem mr2)
    (Hmatch : matching mr1 mr2) op mr1' (Hdo : CC_do_op mr1 op = Some mr1'),
    exists mr2', CC_do_op mr2 op = Some mr2' /\ matching mr1' mr2'.
  Proof.
    destruct op; clarify.
    - destruct p; clarify.
      destruct x; clarify.
      destruct x; clarify.
      generalize (Hmatch k); clarsimp.
      unfold loadbytes in *; clarify.
      dec_perm.
      rewrite H21; clarify; eauto.
      { unfold range_perm, perm in *.
        contradiction n1; intros.
        clear cond.
        specialize (r ofs); clarify.
        rewrite H22 in r; auto. }
    - destruct p; clarify.
      destruct x; clarify.
      destruct x; clarify.
      generalize (Hmatch k); clarsimp.
      unfold storebytes in *; repeat dec_perm.
      eexists; split; eauto; intro; clarify.
      specialize (Hmatch mb).
      destruct (Map.find mb (map mr1)) eqn: Hfind1; clarify.
      destruct p; clarify.
      eexists; split; eauto.
      destruct (eq_dec b0 b); clarify.
      + specialize (Hinj1 _ _ _ _ _ Hdo1 Hfind1); clarsimp.
        repeat rewrite Maps.PMap.gss.
        destruct (eq_dec o (Z.of_nat n)); clarify; 
          [repeat rewrite Maps.ZMap.gss | repeat rewrite Maps.ZMap.gso]; auto.
      + destruct (eq_dec x0 x); clarify.
        { specialize (Hinj2 _ _ _ _ _ Hmatch1 H1); clarsimp. }
        repeat rewrite Maps.PMap.gso; auto.
      + unfold range_perm, perm in *.
        contradiction n1; intros.
        specialize (r ofs); clarify.
        rewrite H22 in r; auto.
    - generalize (Hmatch k); clarsimp.
      eexists; split; eauto; intro; clarify.
      repeat rewrite Map.F.F.add_o; destruct (Map.E.eq_dec k mb); clarify.
      + eexists; split; eauto.
        repeat rewrite Maps.PMap.gss; auto.
      + specialize (Hmatch mb).
        destruct (Map.find mb (map mr1)) as [(b, n')|] eqn: Hfind1; clarsimp.
        eexists; split; eauto.
        specialize (Hvalid1 _ _ _ Hfind1); specialize (Hvalid2 _ _ _ Hmatch1).
        unfold valid_block in *.
        generalize (Plt_ne _ _ Hvalid1), (Plt_ne _ _ Hvalid2); intros.
        repeat rewrite Maps.PMap.gso; auto.
    - destruct x; clarify.
      generalize (Hmatch k); clarsimp.
      unfold free in *; repeat dec_perm.
      eexists; split; eauto; intro; clarify.
      repeat rewrite Map.F.F.remove_o; destruct (Map.E.eq_dec k mb); auto.
      specialize (Hmatch mb).
      destruct (Map.find mb (map mr1)) as [(b', n')|] eqn: Hfind1; clarsimp.
      eexists; split; eauto; clarify.
      destruct (eq_dec b' b); clarify.
      + specialize (Hinj1 _ _ _ _ _ Hdo1 Hfind1); clarsimp.
      + destruct (eq_dec x0 x); clarify.
        { specialize (Hinj2 _ _ _ _ _ Hmatch1 H1); clarsimp. }
        repeat rewrite Maps.PMap.gso; auto.
      + unfold range_perm, perm in *.
        contradiction n0; intros.
        specialize (r ofs); clarify.
        rewrite H22 in r; auto.
  Qed.        

  Corollary matching_do_ops : forall ops mr1 mr2 
    (Hinj1 : inj_mem mr1) (Hinj2 : inj_mem mr2) 
    (Hvalid1 : valid_mem mr1) (Hvalid2 : valid_mem mr2)
    (Hmatch : matching mr1 mr2) mr1' (Hdo : CC_do_ops mr1 ops = Some mr1'),
    exists mr2', CC_do_ops mr2 ops = Some mr2' /\ matching mr1' mr2'.
  Proof.
    induction ops; clarify; eauto.
    exploit matching_do_op; try (apply Hmatch); eauto; clarify.
    eapply IHops; try (apply Hdo2); auto.
    - eapply do_op_inj; eauto.
    - eapply do_op_inj; eauto.
    - eapply do_op_valid; eauto.
    - eapply do_op_valid; eauto.
  Qed.

  Lemma matching_refl : forall m, matching m m.
  Proof.
    repeat intro.
    destruct (Map.find mb (map m0)) as [(?, ?)|]; eauto.
  Qed.
  Hint Resolve matching_refl.

  Instance matching_sym : Symmetric matching.
  Proof.
    repeat intro.
    specialize (H mb); clarify.
    destruct (Map.find mb (map x)), (Map.find mb (map y)); clarify;
      destruct p; clarify; eauto.
  Qed.

  Lemma ZMap_gsi : forall {A} m k1 (v1 : A) k2 v2 k, k1 <> k2 ->
    Maps.ZMap.get k (Maps.ZMap.set k1 v1 (Maps.ZMap.set k2 v2 m)) =
    Maps.ZMap.get k (Maps.ZMap.set k2 v2 (Maps.ZMap.set k1 v1 m)).
  Proof.
    intros.
    destruct (eq_dec k k1); destruct (eq_dec k k2); clarify;
      repeat (repeat rewrite Maps.ZMap.gss; try rewrite Maps.ZMap.gso; auto).
  Qed.

  Lemma PMap_gsi : forall {A} m k1 (v1 : A) k2 v2 k, k1 <> k2 ->
    Maps.PMap.get k (Maps.PMap.set k1 v1 (Maps.PMap.set k2 v2 m)) =
    Maps.PMap.get k (Maps.PMap.set k2 v2 (Maps.PMap.set k1 v1 m)).
  Proof.
    intros.
    destruct (eq_dec k k1); destruct (eq_dec k k2); clarify;
      repeat (repeat rewrite Maps.PMap.gss; try rewrite Maps.PMap.gso; auto).
  Qed.

  Lemma CC_ops_comm : forall op1 op2 mr mr1
    (Hvalid : valid_mem mr) (Hinj : inj_mem mr)
    (Hdiff_loc : independent (loc_of op1) (loc_of op2))
    (Hops1 : CC_do_ops mr [op1; op2] = Some mr1),
    exists mr2, CC_do_ops mr [op2; op1] = Some mr2 /\ matching mr1 mr2.
  Proof.
    intros; clarify.
    generalize (do_op_valid _ Hops11); intro Hvalid'; clarify.
    generalize (do_op_inj _ Hops11); intro Hinj'; clarify.
    destruct op1; clarify.
    - destruct p as (b1, o1); clarify.
      destruct x0; clarify.
      destruct x0; clarify.
      destruct op2; clarify.
      + destruct p as (b2, o2); clarsimp.
        destruct x0; clarify.
        destruct x0; clarsimp; eauto.
      + destruct p as (b2, o2); clarsimp.
        destruct x0; clarsimp.
        erewrite loadbytes_storebytes_other; eauto; clarsimp.
        eexists; split; eauto.
        { destruct (eq_dec b b0); clarify.
          specialize (Hinj' _ _ _ _ _ Hops1211 Hops111); clarify.
          destruct (eq_dec o1 o2); clarify; right; omega. }
      + rewrite Map.F.F.add_neq_o in *; clarsimp.
        erewrite loadbytes_alloc_other; eauto; clarify; eauto.
        unfold alloc; clarify.
      + destruct x0; clarsimp.
        rewrite Map.F.F.remove_neq_o in *; clarsimp.
        erewrite loadbytes_free; eauto; clarsimp; eauto.
        { left; intro; subst; contradiction Hdiff_loc; eapply Hinj'; eauto. }
    - destruct p as (b1, o1); clarify.
      destruct x0; clarify.
      destruct op2; clarify.
      + destruct p as (b2, o2); clarsimp.
        destruct x; clarify.
        erewrite <- loadbytes_storebytes_other; eauto; clarsimp; eauto.
        destruct x; clarsimp; eauto.
        { destruct (eq_dec b b0); clarify.
          specialize (Hinj _ _ _ _ _ Hops1211 Hops111); clarify.
          destruct (eq_dec o1 o2); clarify; right; omega. }
      + destruct p as (b2, o2); clarsimp.
        destruct x; clarify.
        unfold storebytes in *; repeat dec_perm.
        eexists; split; eauto; intro; clarify.
        destruct (Map.find mb (map mr)) as [(b', n')|] eqn: Hfind; clarify.
        eexists; split; eauto; split; auto; intro.
        destruct (eq_dec b b0); clarify.
        * specialize (Hinj _ _ _ _ _ Hops1211 Hops111); clarify.
          repeat rewrite Maps.PMap.set2.
          destruct (eq_dec o1 o2); clarify.
          generalize (inj_neq o1 o2); clarify.
          destruct (eq_dec b' b0); clarify.
          { repeat rewrite Maps.PMap.gss; auto.
            rewrite ZMap_gsi; auto. }
          repeat rewrite Maps.PMap.gso; auto.
        * rewrite PMap_gsi; auto.
          rewrite (Maps.PMap.gso _ _ n1).
          assert (b0 <> b) as Hneq by auto; rewrite (Maps.PMap.gso _ _ Hneq);
            auto.
      + rewrite Map.F.F.add_neq_o; clarify.
        unfold storebytes in *; dec_perm.
        generalize (range_perm_alloc_1(b := nextblock (m mr))(m1 := m mr)
          (lo := 0)(hi := Z.of_nat n0)); intro Hperm; clarify.
        specialize (Hperm _ _ _ _ _ r).
        dec_perm.
        eexists; split; [eauto|]; intro; clarify.
        repeat rewrite Map.F.F.add_o; destruct (Map.E.eq_dec k mb); clarify.
        * eexists; split; eauto; clarify.
          generalize (Plt_ne _ _ (Hvalid _ _ _ Hops111)); intro Hneq.
          rewrite (Maps.PMap.gso _ _ Hneq).
          assert (nextblock (m mr) <> b) as Hneq' by auto;
            rewrite (Maps.PMap.gso _ _ Hneq').
          repeat rewrite Maps.PMap.gss; auto.
        * destruct (Map.find mb (map mr)) as [(?, ?)|] eqn: Hfind1; clarify.
          eexists; split; eauto; clarify.
          generalize (Plt_ne _ _ (Hvalid _ _ _ Hfind1)); intro Hneq.
          rewrite (Maps.PMap.gso _ _ Hneq).
          generalize (Plt_ne _ _ (Hvalid _ _ _ Hops111)); intro Hneq'.
          rewrite (Maps.PMap.gso _ _ Hneq').          
          destruct (eq_dec b0 b); clarify.
          { specialize (Hinj _ _ _ _ _ Hfind1 Hops111); clarify.
            repeat rewrite Maps.PMap.gss; auto. }
          repeat rewrite Maps.PMap.gso; auto.
      + destruct x; clarify.
        unfold free in *; clarify.
        clear cond.
        rewrite <- range_perm_storebytes_iff in r; eauto.
        clarify.
        rewrite Map.F.F.remove_neq_o; clarify.
        unfold storebytes in *; repeat dec_perm.
        eexists; split; eauto; intro; clarify.
        repeat rewrite Map.F.F.remove_o; clarify.
        destruct (Map.find mb (map mr)) as [(?, ?)|] eqn: Hfind1; clarify.
        eexists; split; eauto; clarify.
        { contradiction n1; eapply range_perm_free_1; eauto; unfold free;
            clarify.
          intro; subst; contradiction Hdiff_loc; eapply Hinj; eauto. }
    - destruct op2; clarify.
      + destruct p; clarify.
        rewrite Map.F.F.add_neq_o in *; clarify.
        destruct x; clarify.
        destruct x; clarify.
        erewrite loadbytes_alloc_unchanged; unfold alloc; eauto.
        setoid_rewrite Hops12121; clarify; eauto.
      + destruct p; clarify.
        rewrite Map.F.F.add_neq_o in *; clarify.
        destruct x; clarify.
        unfold storebytes in *; dec_perm.
        generalize (range_perm_alloc_2(b := nextblock (m mr))(m1 := m mr)
          (lo := 0)(hi := Z.of_nat n)); intro Hperm; clarify.
        generalize (Plt_ne _ _ (Hvalid _ _ _ Hops1211)); intro Hneq.
        specialize (Hperm b); clarify.
        specialize (Hperm _ _ _ _ r).
        dec_perm.
        eexists; split; eauto; intro; clarify.
        repeat rewrite Map.F.F.add_o; destruct (Map.E.eq_dec k mb); clarify.
        * eexists; split; eauto; clarify.
          generalize (Plt_ne _ _ (Hvalid _ _ _ Hops1211)); intro Hneq'.
          rewrite (Maps.PMap.gso _ _ Hneq').
          assert (nextblock (m mr) <> b) as Hneq'' by auto;
            rewrite (Maps.PMap.gso _ _ Hneq'').
          repeat rewrite Maps.PMap.gss; auto.
        * destruct (Map.find mb (map mr)) as [(?, ?)|] eqn: Hfind1; clarify.
          eexists; split; eauto; clarify.
          generalize (Plt_ne _ _ (Hvalid _ _ _ Hfind1)); intro Hneq'.
          rewrite (Maps.PMap.gso _ _ Hneq').
          generalize (Plt_ne _ _ (Hvalid _ _ _ Hops1211)); intro Hneq''.
          rewrite (Maps.PMap.gso _ _ Hneq'').          
          destruct (eq_dec b0 b); clarify.
          { specialize (Hinj _ _ _ _ _ Hfind1 Hops1211); clarify.
            repeat rewrite Maps.PMap.gss; auto. }
          repeat rewrite Maps.PMap.gso; auto.
      + rewrite Map.F.F.add_neq_o in *; clarify.
        rewrite Map.F.F.add_neq_o; clarify.
        eexists; split; eauto; intro; simpl.
        repeat rewrite Map.F.F.add_o.
        generalize (Plt_ne _ _ (Plt_succ (nextblock (m mr)))); intro Hneq.
        destruct (Map.E.eq_dec k0 mb); destruct (Map.E.eq_dec k mb); clarify.
        * eexists; split; eauto; split; clarify; 
            rewrite (Maps.PMap.gso _ _ Hneq); repeat rewrite Maps.PMap.gss; 
            auto.
        * eexists; split; eauto; split; clarify; 
            rewrite (Maps.PMap.gso _ _ Hneq); repeat rewrite Maps.PMap.gss; 
            auto.
        * destruct (Map.find mb (map mr)) as [(?, ?)|] eqn: Hfind1; clarify.
          eexists; split; eauto; clarify.
          specialize (Hvalid _ _ _ Hfind1).
          exploit Plt_trans_succ; eauto; intro Hlt.
          generalize (Plt_ne _ _ Hvalid); generalize (Plt_ne _ _ Hlt); intros.
          repeat rewrite Maps.PMap.gso; auto.
      + rewrite Map.F.F.add_neq_o in *; clarify.
        destruct x; clarify.
        unfold free in *; clarify.
        generalize (Plt_ne _ _ (Hvalid _ _ _ Hops1211)); intro Hneq.
        clear cond0; rewrite <- range_perm_alloc_iff in r; unfold alloc; eauto.
        clarify.
        repeat rewrite Map.F.F.remove_o.
        destruct (Map.E.eq_dec k0 k); clarify.
        eexists; split; eauto; intro; clarify.
        destruct (eq_dec mb k0); [rewrite Map.F.F.remove_eq_o |
          rewrite Map.F.F.remove_neq_o]; clarify.
        { rewrite Map.F.F.add_neq_o; auto; apply Map.F.F.remove_eq_o; auto. }
        repeat rewrite Map.F.F.add_o; destruct (Map.E.eq_dec k mb); clarify.
        * eexists; split; eauto; clarify.
          rewrite (Maps.PMap.gso _ _ Hneq); rewrite Maps.PMap.gss.
          assert (nextblock (m mr) <> b) as Hneq' by auto;
            rewrite (Maps.PMap.gso _ _ Hneq'); rewrite Maps.PMap.gss; auto.
        * destruct (Map.find mb (map mr)) as [(?, ?)|] eqn: Hfind1;
            rewrite Map.F.F.remove_neq_o; clarify.
          eexists; split; eauto; clarify.
          destruct (eq_dec b b0); clarify.
          { repeat rewrite (Maps.PMap.gso _ _ Hneq);
              repeat rewrite Maps.PMap.gss; auto. }
          generalize (Plt_ne _ _ (Hvalid _ _ _ Hfind1)); intro.
          repeat rewrite Maps.PMap.gso; auto.
    - destruct x0; clarify.
      destruct op2; clarify.
      + destruct p; clarify.
        rewrite Map.F.F.remove_neq_o in *; clarify.
        destruct x; clarify.
        destruct x; clarify.
        erewrite <- loadbytes_free; eauto; clarify; eauto.
        { left; intro; subst; contradiction Hdiff_loc; eapply Hinj; eauto. }
      + destruct p; clarify.
        rewrite Map.F.F.remove_neq_o in *; clarify.
        destruct x; clarify.
        unfold storebytes in *; dec_perm.
        generalize (range_perm_free_2 _ _ _ _ Hops1121 r); intro Hperm.
        dec_perm.
        unfold free in *; clarify.
        eexists; split; eauto; intro; clarify.
        repeat rewrite Map.F.F.remove_o; destruct (Map.E.eq_dec k mb);
          clarify.
        destruct (Map.find mb (map mr)) as [(?, ?)|]; clarify; eauto.
      + rewrite Map.F.F.remove_neq_o in *; clarify.
        rewrite Map.F.F.add_neq_o in *; clarify.
        unfold free in *; clarify.
        generalize (range_perm_alloc_1(b := nextblock (m mr))(m1 := m mr)
          (lo := 0)(hi := Z.of_nat n0)); intro Hperm; clarify.
        specialize (Hperm _ _ _ _ _ r).
        dec_perm.
        eexists; split; [eauto|]; intro; clarify.
        repeat rewrite Map.F.F.remove_o, Map.F.F.add_o;
          destruct (Map.E.eq_dec k mb); clarify;
          destruct (Map.Map.E.eq_dec k0 mb); clarify.
        * eexists; split; eauto; clarify.
          generalize (Plt_ne _ _ (Hvalid _ _ _ Hops111)); intro Hneq.
          assert (nextblock (m mr) <> b) as Hneq' by auto;
            rewrite (Maps.PMap.gso _ _ Hneq'); repeat rewrite Maps.PMap.gss;
            auto.
        * destruct (Map.find mb (map mr)) as [(?, ?)|] eqn: Hfind1; clarify.
          eexists; split; eauto; clarify.
          generalize (Plt_ne _ _ (Hvalid _ _ _ Hfind1)); intro Hneq.
          rewrite (Maps.PMap.gso _ _ Hneq).
          destruct (eq_dec b b0); clarify.
          { repeat rewrite Maps.PMap.gss; rewrite (Maps.PMap.gso _ _ Hneq);
              auto. }
          repeat rewrite Maps.PMap.gso; auto.
      + rewrite Map.F.F.remove_neq_o in *; clarify.
        destruct x; clarify.
        unfold free in *; clarify.
        destruct (eq_dec b0 b); clarify.
        { contradiction Hdiff_loc; eapply Hinj; eauto. }
        dec_perm.
        rewrite Map.F.F.remove_neq_o; clarify.
        dec_perm.
        eexists; split; eauto; intro; clarify.
        repeat rewrite Map.F.F.remove_o; destruct (Map.E.eq_dec k0 mb);
          clarify; destruct (Map.E.eq_dec k mb); clarify.
        destruct (Map.find mb (map mr)) as [(?, ?)|] eqn: Hfind1; clarify.
        eexists; split; eauto; clarify.
        destruct (eq_dec b1 b0); destruct (eq_dec b1 b); clarify.
        * rewrite Maps.PMap.gss; repeat rewrite (Maps.PMap.gso _ _ n1);
            rewrite Maps.PMap.gss; auto.
        * rewrite Maps.PMap.gss; repeat rewrite (Maps.PMap.gso _ _ n6);
            rewrite Maps.PMap.gss; auto.
        * repeat rewrite Maps.PMap.gso; auto.
        * contradiction n2; eapply range_perm_free_1; unfold free; clarify.
        * contradiction n2; eapply range_perm_free_2; unfold free; eauto; 
            clarify.
  Qed.

  Lemma double_write_matching : forall m p v v' m'
    (Hwrite : CC_do_op m (MWrite p v') = Some m'),
    exists m'', CC_do_ops m [MWrite p v; MWrite p v'] = Some m'' /\
                matching m' m''.
  Proof.
    clarify.
    destruct p; clarify.
    destruct x; clarify.
    unfold storebytes in *; repeat dec_perm.
    eexists; split; eauto; intro; clarify.
    destruct (Map.find mb (map m0)) eqn: Hfind; clarify.
    destruct p; clarify.
    eexists; split; eauto; clarify.
    destruct (eq_dec b0 b); clarify.
    - repeat rewrite Maps.PMap.gss.
      rewrite Maps.ZMap.set2; auto.
    - repeat rewrite Maps.PMap.gso; auto.
  Qed.      

  Lemma write_free_matching : forall m b o v (Hinj : inj_mem m)
    mw (Hwrite : CC_do_op m (MWrite (b, o) v) = Some mw)
    m' (Hfree : CC_do_op m (MFree b) = Some m'),
    exists m'', CC_do_ops m [MWrite (b, o) v; MFree b] = Some m'' /\
                matching m' m''.
  Proof.
    clarify.
    destruct x; clarsimp.
    unfold storebytes, free in *; repeat dec_perm.
    eexists; split; eauto; intro; clarify.
    rewrite (Map.F.F.remove_o); destruct (Map.Map.E.eq_dec b mb); clarify.
    destruct (Map.find mb (map m0)) eqn: Hfind; clarify.
    destruct p; clarify.
    eexists; split; eauto; clarify.
    destruct (eq_dec b1 b0); clarify.
    - specialize (Hinj _ _ _ _ _ Hfind Hwrite1); clarify.
    - repeat rewrite Maps.PMap.gso; auto.
  Qed.      

  Opaque loadbytes storebytes alloc free.

  Lemma CC_loc_comm : forall op1 op2 mr mr' 
    (Hdiff_loc : independent (loc_of op1) (loc_of op2))
    (Hcon : CC_consistent (mr ++ op1 :: op2 :: mr')),
    CC_consistent (mr ++ op2 :: op1 :: mr').
  Proof.
    unfold CC_consistent; clarify.
    rewrite CC_ops_app in *; clarsimp.
    generalize (do_ops_valid _ cond1); intro Hvalid; use Hvalid.
    generalize (do_ops_inj _ cond1); intro Hinj; use Hinj; use Hinj.
    exploit CC_ops_comm; eauto; clarsimp.
    generalize (do_op_valid _ cond21); intro Hvalid1; clarify.
    generalize (do_op_valid _ H11); intro Hvalid2; clarify.
    exploit matching_do_ops; try (apply H2); eauto; clarify.
    - eapply do_op_inj; eauto.
      eapply do_op_inj; eauto.
    - eapply do_op_inj; eauto.
      eapply do_op_inj; eauto.
    - eapply do_op_valid; eauto.
    - eapply do_op_valid; eauto.
  Qed.

  Lemma CC_loc_valid : forall m op1 op2 
      (Hdiff_loc : independent (loc_of op1) (loc_of op2))
      (Hop1 : CC_consistent (m ++ [op1])) (Hop2 : CC_consistent (m ++ [op2])),
      CC_consistent (m ++ [op1; op2]).
  Proof.
    unfold CC_consistent; clarsimp; repeat rewrite CC_ops_app in *; clarsimp.
    rename x into mbase, m1 into m3, m2 into m1; rename m3 into m2.
    generalize (do_ops_valid _ cond01); intro Hvalid; use Hvalid.
    generalize (do_ops_inj _ cond01); intro Hinj; use Hinj; use Hinj.
    generalize (do_op_valid _ cond31), (do_op_inj _ cond31); 
      intros Hvalid2 Hinj2; clarify.
    destruct op1; clarify.
    - destruct p; clarify.
      destruct x; clarify.
      destruct x; clarify.
    - destruct p as (b1, o1); clarify.
      destruct x; clarify.
      destruct op2; clarify.
      + destruct p as (b2, o2); clarify.
        destruct x0; clarsimp.
        destruct x0; clarify.
        erewrite loadbytes_storebytes_other in cond11; eauto 2; clarsimp.
        { destruct (eq_dec b b0); clarify.
          specialize (Hinj2 _ _ _ _ _ cond311 cond0211); clarify.
          destruct (eq_dec o1 o2); clarify; right; omega. }
      + destruct p as (b2, o2); clarsimp.
        destruct x0; clarify.
        generalize (storebytes_range_perm _ _ _ _ _ cond3121); intro Hperm.
        rewrite range_perm_storebytes_iff in Hperm; eauto 2.
        generalize (range_perm_storebytes _ _ _ _ Hperm); intros [? ?];
          clarsimp.
      + destruct x0; clarsimp.
        generalize (free_range_perm _ _ _ _ _ cond3121); intro Hperm.
        rewrite range_perm_storebytes_iff in Hperm; eauto 2.
        generalize (range_perm_free _ _ _ _ Hperm); intros [? ?]; clarsimp.
    - destruct (alloc (m mbase) 0 (Z.of_nat n)) eqn: Halloc; clarify.
      exploit alloc_result; eauto 2; clarify.
      destruct op2; clarify.
      + destruct p; clarify.
        rewrite Map.F.F.add_neq_o in *; clarsimp.
        destruct x; clarify.
        destruct x; clarify.
        erewrite <- loadbytes_alloc_unchanged in cond11; eauto 2; clarsimp.
      + destruct p; clarify.
        rewrite Map.F.F.add_neq_o in *; clarsimp.
        destruct x; clarify.
        generalize (storebytes_range_perm _ _ _ _ _ cond3121); intro Hperm.
        rewrite range_perm_alloc_iff in Hperm; eauto 2.
        generalize (range_perm_storebytes _ _ _ _ Hperm); intros [? ?];
          clarsimp.
        { generalize (Plt_ne _ _ (Hvalid _ _ _ cond311)); clarify. }
      + rewrite Map.F.F.add_neq_o in *; clarify.
      + rewrite Map.F.F.add_neq_o in *; clarsimp.
        destruct x; clarify.
        generalize (free_range_perm _ _ _ _ _ cond3121); intro Hperm.
        rewrite range_perm_alloc_iff in Hperm; eauto 2.
        generalize (range_perm_free _ _ _ _ Hperm); intros [? ?]; clarsimp.
        { generalize (Plt_ne _ _ (Hvalid _ _ _ cond311)); clarify. }
    - destruct x; clarify.
      destruct op2; clarify.
      + destruct p; clarify.
        rewrite Map.F.F.remove_neq_o in *; clarsimp.
        destruct x0; clarify.
        destruct x0; clarify.
        erewrite loadbytes_free in cond11; eauto 2; clarsimp.
        { left; intro; subst; contradiction Hdiff_loc; eapply Hinj2; eauto. }
      + destruct p; clarify.
        rewrite Map.F.F.remove_neq_o in *; clarsimp.
        destruct x0; clarify.
        generalize (storebytes_range_perm _ _ _ _ _ cond3121); intro Hperm.
        rewrite range_perm_free_iff in Hperm; eauto 2.
        generalize (range_perm_storebytes _ _ _ _ Hperm); intros [? ?];
          clarsimp.
        { intro; subst; contradiction Hdiff_loc; eapply Hinj; eauto. }
      + rewrite Map.F.F.remove_neq_o in *; clarify.
      + rewrite Map.F.F.remove_neq_o in *; clarsimp.
        destruct x0; clarify.
        generalize (free_range_perm _ _ _ _ _ cond3121); intro Hperm.
        rewrite range_perm_free_iff in Hperm; eauto 2.
        generalize (range_perm_free _ _ _ _ Hperm); intros [? ?]; clarsimp.
        { intro; subst; contradiction Hdiff_loc; eapply Hinj; eauto. }
  Qed.

(*  Convoy pattern
  Definition lift_g (b : {x : A | P x}) : option {x : A | P x} :=
    match b with exist a p =>
      match g a as oa return g a = oa -> option {x : A | P x} with
      | Some c => fun Pc => Some (exist P c (g_P a c Pc p))
      | None => fun _ => None
      end eq_refl
    end.

  Definition CC_do_op (m:mem_rec') (op:mem_op Map.key val positive) :=
    match CC_do_op0 (mrec m) op with
    | Some m' => fun P => Some {| mrec := m'; 
        mvalid := (op_valid (mrec m) op m' P (mvalid m));
        minj := (op_inj (mrec m) op m' P (mvalid m) (minj m)) |}
    | None => fun _ => None
    end eq_refl.*)

  Lemma CC_loc_comm_iff : forall op1 op2 mr mr' 
    (Hdiff_loc : independent (loc_of op1) (loc_of op2)),
    CC_consistent (mr ++ op1 :: op2 :: mr') <->
    CC_consistent (mr ++ op2 :: op1 :: mr').
  Proof.
    intros; split; intro; apply CC_loc_comm; auto; apply indep_sym; auto.
  Qed.

  Lemma CC_loc_valid_iff : forall m op1 op2 
    (Hdiff_loc : independent (loc_of op1) (loc_of op2)),
    CC_consistent (m ++ [op1; op2]) <->
    (CC_consistent (m ++ [op1]) /\ CC_consistent (m ++ [op2])).
  Proof.
    intros; split; clarify; [|apply CC_loc_valid; auto].
    exploit CC_loc_comm; eauto; intro.
    unfold CC_consistent in *; repeat rewrite CC_ops_app in *; clarsimp.
  Qed.

  Lemma CC_write_not_read : forall p v ops m
    (Hnot_read : Forall (fun op => forall v' : memval, op <> MRead p v') ops),
    CC_consistent (m ++ MWrite p v :: ops) <->
    (CC_consistent (m ++ [MWrite p v]) /\ CC_consistent (m ++ ops)).
  Proof.
    induction ops; clarify.
    - unfold CC_consistent; split; clarsimp.
      rewrite CC_ops_app in *; clarify.
    - inversion Hnot_read; clarify.
      destruct (indep_dec _ (Ptr p) (loc_of a)).
      { rewrite CC_loc_comm_iff; auto.
        specialize (IHops (m0 ++ [a])); repeat rewrite <- app_assoc in *;
          clarify; rewrite IHops.
        rewrite CC_loc_valid_iff; clarify; [|apply indep_sym; auto].
        split; clarify.
        unfold CC_consistent in *; rewrite CC_ops_app in *; clarify. }
      unfold CC_consistent; repeat rewrite CC_ops_app.
      destruct (CC_do_ops empty_rec m0) as [mbase|] eqn: Hbase; [|split];
        clarify.
      generalize (do_ops_valid _ Hbase); intro Hvalid; use Hvalid.
      generalize (do_ops_inj _ Hbase); intro Hinj; use Hinj; use Hinj.
      destruct p; clarify.
      destruct (Map.find k (map mbase)) eqn: Hfind; [|split]; clarify.
      destruct p; clarify.
      destruct (storebytes (m mbase) b (Z.of_nat n0) [v]) eqn: Hstore; [|split];
        clarify.
      generalize (do_op_valid(m1 := mbase) (MWrite (k, n0) v)); intro Hvalid1;
        clarsimp.
      destruct a; clarify.
      + destruct (eq_dec (k, n0) p); clarify.
        exploit H1; eauto; clarify.
      + destruct (eq_dec (k, n0) p); clarify.
        generalize (storebytes_range_perm _ _ _ _ _ Hstore); intro Hperm.
        assert (length [v] = length [m2]) as Hlen by auto;
          rewrite Hlen in Hperm.
        generalize (range_perm_storebytes _ _ _ _ Hperm); intros [? ?];
          clarsimp.
        generalize (double_write_matching mbase (k, n0) v m2); intro Hmatch;
          clarsimp.
        generalize (do_op_valid(m1 := mbase) (MWrite (k, n0) m2));
          intro Hvalid2; clarsimp.
        generalize (do_op_valid(m1 := {| m := m1; map := map mbase |}) 
          (MWrite (k, n0) m2)); intro Hvalid3; clarsimp.
        split; clarify.
        * symmetry in Hmatch2.
          exploit matching_do_ops; try (apply Hmatch2); eauto; clarify.
        * exploit matching_do_ops; try (apply Hmatch2); eauto; clarify.
      + destruct (eq_dec k0 k); clarify; split; clarify.
      + destruct (eq_dec k k0); clarify.
        destruct (free (m mbase) b 0 (Z.of_nat n1)) eqn: Hfree1; clarify.
        generalize (do_op_valid(m1 := mbase) (MFree k0)); intro Hvalid2;
          clarsimp.
        generalize (do_op_inj(m1 := mbase) (MFree k0)); intro Hinj2;
          clarsimp.
        generalize (write_free_matching(m := mbase) k0 n0 v); intro Hmatch;
          clarsimp.
        generalize (do_op_valid(m1 := {| m := m1; map := map mbase |})
          (MFree k0)); intro Hvalid3; clarsimp.
        split; clarify.
        * symmetry in Hmatch2.
          exploit matching_do_ops; try (apply Hmatch2); eauto; clarify.
        * exploit matching_do_ops; try (apply Hmatch2); eauto; clarify.
        * destruct (free m1 b 0 (Z.of_nat n1)) eqn: Hfree2; split; clarify.
          generalize (free_range_perm _ _ _ _ _ Hfree2); intro Hperm.
          erewrite <- range_perm_storebytes_iff in Hperm; eauto.
          generalize (range_perm_free _ _ _ _ Hperm); intros [? ?]; clarify.
  Qed.

  Instance CompCertMem : Memory_Layout _ mblock_eq :=
    {| consistent := CC_consistent |}.
  Proof.
    - unfold CC_consistent; simpl; auto.
    - unfold CC_consistent; clarify.
      rewrite CC_ops_app in cond; clarify.
    - intros; split; apply CC_loc_comm; [|apply indep_sym]; auto.
    - apply CC_loc_valid.
    - unfold CC_consistent; clarify; repeat rewrite CC_ops_app in *; clarify.
      destruct p; clarify.
      destruct x0; clarify.
      destruct x0; clarify; reflexivity.
    - unfold CC_consistent; clarify; repeat rewrite CC_ops_app in *; clarify.
      destruct p; clarify.
      destruct x0; clarify.
      exploit loadbytes_storebytes_same; eauto 2; intro Hload; clarify.
      split; clarify.
    - intros; apply CC_write_not_read; auto.
    - intros; destruct (indep_dec _ (loc_of op) (Ptr p)).
      { rewrite CC_loc_valid_iff; [split|]; clarify. }
      destruct op; clarify; destruct (eq_dec p0 p); clarify.
      unfold CC_consistent in *; clarify; repeat rewrite CC_ops_app in *;
        clarify.
      destruct p; clarify.
      destruct x0; clarify.
      destruct x0; clarify; reflexivity.
    - unfold CC_consistent; clarify; repeat rewrite CC_ops_app in *; clarify.
      destruct (alloc (m x) 0 (Z.of_nat n)) eqn: Halloc; clarify.
      rewrite Map.F.F.add_eq_o; auto.
      repeat split; intros; repeat rewrite CC_ops_app in *; clarsimp.
      + rewrite Map.F.F.add_eq_o in *; clarify.
        generalize (range_perm_storebytes m2 b0 (Z.of_nat o) [v]);
          intro X; use X; [destruct X; clarsimp|].
        repeat intro.
        eapply perm_implies; [eapply perm_alloc_2 | apply perm_F_any]; eauto;
          omega.
      + generalize (range_perm_free m2 b0 0 (Z.of_nat n)); intro X; use X;
          [destruct X; clarsimp|].
        repeat intro; exploit perm_alloc_2; eauto.
      + rewrite Map.F.F.add_eq_o in *; clarify.
    - unfold CC_consistent; clarify; repeat rewrite CC_ops_app in *; clarify.
      destruct x1; clarify.
      rewrite Map.F.F.remove_eq_o; auto.
      split; clarify; rewrite CC_ops_app in *; clarsimp.
      + rewrite Map.F.F.remove_eq_o in *; clarify.
      + rewrite Map.F.F.remove_eq_o in *; clarify.
    - unfold CC_consistent; clarify; repeat split; clarify.
      destruct p; clarify.
    - unfold CC_consistent; clarify; repeat rewrite CC_ops_app in *; clarsimp.
      destruct (CC_do_ops empty_rec m0) as [mbase|] eqn: Hbase; [|split];
        clarsimp.
      destruct p; clarify.
      destruct (Map.find m1 (map mbase)) eqn: Hfind; [|split]; clarify.
      destruct p; clarify.
      destruct (storebytes (m mbase) b (Z.of_nat n) [v]) eqn: Hstore;
        split; clarsimp.
      + generalize (storebytes_range_perm _ _ _ _ _ Hstore), 
        (range_perm_storebytes (m mbase) b (Z.of_nat n) [v']); clarify;
        destruct X; clarify.
      + generalize (storebytes_range_perm _ _ _ _ _ cond1), 
        (range_perm_storebytes (m mbase) b (Z.of_nat n) [v]); clarify;
        destruct X; clarify.
  Defined.
      
End CC_BlockInstance.