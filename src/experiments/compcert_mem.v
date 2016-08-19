Require Import Memtype.
Require Import memory_model.
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

Set Implicit Arguments.

(* What does it mean for CompCert's memory model to be an instance of
   the memory model interface? It can certainly support all the operations of
   the interface, but should the interface be expanded to include more of its
   operations? *)

Instance block_Z_eq : @EqDec (block * int) eq eq_equivalence.
Proof. eq_dec_inst. apply Int.eq_dec. Qed.

Instance val_eq : @EqDec val eq eq_equivalence.
Proof. 
  eq_dec_inst.
  apply Int.eq_dec.
  apply Int64.eq_dec.
  apply Floats.Float.eq_dec.
  try (apply Floats.Float32.eq_dec).
  apply Int.eq_dec.
Qed.

(* 32-bit values *)
Inductive val32 := Wint (i : int) | Wptr (b : block) (o : int) | Wundef.
Instance val32_eq : @EqDec val32 eq eq_equivalence.
Proof. eq_dec_inst; apply Int.eq_dec. Qed.

Definition to_val v := match v with
| Wint i => Vint i
| Wptr b o => Vptr b o
| Wundef => Vundef
end.

Definition to_val32 v := match v with
| Vint i => Wint i
| Vptr b o => Wptr b o
| _ => Wundef
end.

(* At present, this uses CompCert's model to implement a separate block for
   each location. *)
Module CC_MemInstance (Import M : MEM) (Loc : UsualDecidableType).
  Definition loc := Loc.t.
  Instance loc_eq : @EqDec loc eq eq_equivalence.
  Proof. eq_dec_inst; apply Loc.eq_dec. Qed.
  
  Module Map := FMap' Loc.

  (* This would be much richer with types. *)
  Record mem_rec := { m : mem; map : Map.t block }.
  Definition empty_rec := {| m := empty; map := Map.empty _ |}.

  Definition CC_do_op mrec op := match op with
  | MRead l v => match Map.find l (map mrec) with None => None
                 | Some b => match load Mint32 (m mrec) b 0 with None => None
                             | Some v' => if eq_dec v (to_val32 v') then Some mrec else None
                             end
                 end
  | MWrite l v => match Map.find l (map mrec) with None => None
                  | Some b => match store Mint32 (m mrec) b 0 (to_val v) with None => None
                              | Some m' => Some {| m := m'; map := map mrec |}
                              end
                  end
  | MAlloc l => match Map.find l (map mrec) with Some _ => None
                | None => let (m, b) := alloc (m mrec) 0 4 in 
                   Some {| m := m; map := Map.add l b (map mrec) |}
                end
  | MFree l => match Map.find l (map mrec) with None => None
               | Some b => match free (m mrec) b 0 4 with
                           | Some m' => Some {| m := m'; map := Map.remove l (map mrec) |}
                           | None => None
                           end
               end
  | MCast l b => match Map.find l (map mrec) with None => None
                 | Some b' => if eq_block b b' then Some mrec else None
                 end
  end.

  Fixpoint CC_do_ops mrec ops := match ops with
  | [] => Some mrec
  | op :: rest => match CC_do_op mrec op with 
                  | Some mrec' => CC_do_ops mrec' rest
                  | None => None
                  end
  end.

  (* How should we handle inconsistent memories? *)
  Definition CC_can_do ops op := 
    match CC_do_ops empty_rec (rev ops ++ [op]) with
    | Some _ => true | None => false end.

  Lemma CC_ops_app : forall ops1 ops2 m, CC_do_ops m (ops1 ++ ops2) =
    match CC_do_ops m ops1 with Some m' => CC_do_ops m' ops2 | None => None end.
  Proof. 
    induction ops1; clarify; eauto.
    destruct (CC_do_op m0 a); clarify.
  Qed.

  Definition valid_mem mr := forall x b, Map.find x (map mr) = Some b -> 
    valid_block (m mr) b.
  Definition inj_mem mr := forall x y b, Map.find x (map mr) = Some b -> 
    Map.find y (map mr) = Some b -> x = y.

  Lemma do_op_valid : forall m1 op m2 (Hop : CC_do_op m1 op = Some m2)
    (Hvalid : valid_mem m1), valid_mem m2.
  Proof.
    repeat intro.
    specialize (Hvalid x b); unfold valid_block in *; destruct op; clarify.
    - erewrite nextblock_store; eauto.
    - destruct (alloc (m m1) 0 4) eqn: alloc1; inversion Hop; clarify.
      erewrite nextblock_alloc; eauto.
      rewrite Map.F.F.add_o in *; clarify.
      destruct (Map.Map.E.eq_dec k x); clarify.
      + exploit alloc_result; eauto; clarify.
        apply Pos.lt_succ_diag_r.      
      + apply Pos.lt_lt_succ; auto.
    - rewrite Map.F.F.remove_o in *; clarify.
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
    - destruct (alloc (m m1) 0 4) eqn: alloc1; inversion Hop; clarify.
      exploit alloc_result; eauto 1; clarify.
      rewrite Map.F.F.add_o in *; destruct (Map.Map.E.eq_dec k x); 
        destruct (Map.Map.E.eq_dec k y); clarify.
      + specialize (Hvalid _ _ H0); exploit Pos.lt_irrefl; eauto 1; clarify.
      + specialize (Hvalid _ _ H); exploit Pos.lt_irrefl; eauto 1; clarify.
    - rewrite Map.F.F.remove_o in *; clarify.
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
    
  Lemma range_perm_store_1 : forall chunk m1 b ofs v m2
    (Hstore : store chunk m1 b ofs v = Some m2) b' lo hi k p
    (Hrange_perm : range_perm m1 b' lo hi k p), range_perm m2 b' lo hi k p.
  Proof.
    repeat intro.
    exploit Hrange_perm; eauto; intro Hperm.
    eapply perm_store_1; eauto.
  Qed.

  Lemma range_perm_store_2 : forall chunk m1 b ofs v m2
    (Hstore : store chunk m1 b ofs v = Some m2) b' lo hi k p
    (Hrange_perm : range_perm m2 b' lo hi k p), range_perm m1 b' lo hi k p.
  Proof.
    repeat intro.
    exploit Hrange_perm; eauto; intro Hperm.
    eapply perm_store_2; eauto.
  Qed.

  Lemma range_perm_store_iff : forall chunk m1 b ofs v m2
    (Hstore : store chunk m1 b ofs v = Some m2) b' lo hi k p,
    range_perm m1 b' lo hi k p <-> range_perm m2 b' lo hi k p.
  Proof.
    intros; split; [eapply range_perm_store_1 | eapply range_perm_store_2]; eauto.
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
    (Hfree : free m1 b lo hi = Some m2) b' (Hdiff : b <> b') lo hi k p
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

  Lemma range_perm_op_iff : forall m1 op m2
    (Hop : CC_do_op m1 op = Some m2) op' (Hdiff_loc : loc_of op1 <> loc_of op2) lo hi k p,
    range_perm m1 b' lo hi k p <-> range_perm m2 b' lo hi k p.
  Proof.
  

  Lemma CC_loc_comm : forall op1 op2 mr mr' 
    (Hdiff_loc : loc_of op1 <> loc_of op2)
    (Hvalid : forall x b, Map.find x (map mr) = Some b -> valid_block (m mr) b)
    (Hinj : forall x y b, Map.find x (map mr) = Some b -> 
                          Map.find y (map mr) = Some b -> x = y),
    CC_do_ops mr [op1; op2] = Some mr' ->
      exists mr2', CC_do_ops mr [op2; op1] = Some mr2'.
  Proof.
    intros; destruct op1; destruct op2; clarify; eauto 2.
    - erewrite load_store_other; eauto.
      rewrite H121; clarify; eauto.
      left; intro; subst; contradiction Hdiff_loc; eapply Hinj; eauto.
    - destruct (alloc (m x) 0 4) eqn: alloc1; inversion H21; clarify.
      rewrite Map.F.F.add_neq_o; clarify.
      erewrite load_alloc_other; eauto; clarify; eauto.
    - rewrite Map.F.F.remove_neq_o; clarify.
      erewrite load_free; eauto; clarify; eauto.
      left; intro; subst; contradiction Hdiff_loc; eapply Hinj; eauto.
    - erewrite <- load_store_other; eauto; clarify; eauto.
      left; intro; subst; contradiction Hdiff_loc; eapply Hinj; eauto.
    - generalize (store_valid_access_3 _ _ _ _ _ _ H2121);
        generalize (store_valid_access_3 _ _ _ _ _ _ H121); intros valid1 valid2.
      exploit (store_valid_access_2 _ _ _ _ _ _ H121); eauto; intro valid2'.
      generalize (valid_access_store _ _ _ _ (to_val v0) valid2'); intros [m2 store2];
        rewrite store2; clarify.
      exploit (store_valid_access_1 _ _ _ _ _ _ store2 Mint32 x3); eauto; 
        intro valid1'.
      generalize (valid_access_store _ _ _ _ (to_val v) valid1'); 
        intros [? store1]; rewrite store1; eauto.
    - destruct (alloc (m mr) 0 4) eqn: alloc1; clarify.
      rewrite Map.F.F.add_neq_o; clarify.
      exploit store_valid_access_3; eauto; intro valid.
      exploit valid_access_alloc_other; eauto; intro valid'.
      generalize (valid_access_store _ _ _ _ (to_val v) valid'); intros [? store];
        rewrite store; eauto.
    - generalize (free_range_perm _ _ _ _ _ H2121); intro freeable.
      rewrite <- range_perm_store_iff in freeable; eauto.
      generalize (range_perm_free _ _ _ _ freeable); intros [? free];
        rewrite free; clarify.
      rewrite Map.F.F.remove_neq_o; clarify.
      exploit store_valid_access_3; eauto; intro valid.
      exploit valid_access_free_1; eauto.
      { left; intro; subst; contradiction Hdiff_loc; eapply Hinj; eauto. }
      intro valid'; generalize (valid_access_store _ _ _ _ (to_val v) valid'); 
        intros [? store]; rewrite store; eauto.
    - destruct (alloc (m mr) 0 4) eqn: alloc1; inversion H1; clarify.
      rewrite Map.F.F.add_neq_o in *; clarify.
      erewrite load_alloc_unchanged in H2121; eauto; clarify.
      rewrite alloc1; eauto.
    - destruct (alloc (m mr) 0 4) eqn: alloc1; inversion H1; clarify.
      rewrite Map.F.F.add_neq_o in *; clarify.
      exploit store_valid_access_3; eauto; intro valid.
      exploit valid_access_alloc_inv; eauto; intro valid'.
      destruct (eq_block x1 b); clarify.
      + exploit alloc_result; eauto; clarify.
        specialize (Hvalid _ _ H211); unfold valid_block in Hvalid.
        generalize (Pos.lt_irrefl (nextblock (m mr))); clarify.
      + generalize (valid_access_store _ _ _ _ (to_val v) valid'); intros [? store];
        rewrite store; clarify.
        destruct (alloc x 0 4); eauto.
    - destruct (alloc (m mr) 0 4) eqn: alloc1; inversion H1; clarify.
      rewrite Map.F.F.add_neq_o in *; clarify.
      rewrite Map.F.F.add_neq_o; clarify.
      destruct (alloc m0 0 4); eauto.
    - destruct (alloc (m mr) 0 4) eqn: alloc1; inversion H1; clarify.
      rewrite Map.F.F.add_neq_o in *; clarify.
      generalize (free_range_perm _ _ _ _ _ H2121); intro valid.
      generalize (range_perm_free (m mr) x1 0 4); intro X; use X.
      + destruct X as [? free]; rewrite free; clarify.
        rewrite Map.F.F.remove_neq_o; clarify.
        destruct (alloc x 0 4); eauto.
      + repeat intro.
        eapply perm_alloc_4; eauto.
        intro; exploit alloc_result; eauto; clarify.
        specialize (Hvalid _ _ H211); unfold valid_block in Hvalid; clarify.
        generalize (Pos.lt_irrefl _ Hvalid); auto.
    - destruct (alloc (m mr) 0 4) eqn: alloc1; inversion H1; clarify.
      rewrite Map.F.F.add_neq_o in *; clarify.
      rewrite alloc1; eauto.
    - rewrite Map.F.F.remove_neq_o in *; clarify.
      erewrite <- load_free; eauto; clarify; eauto.
      left; intro; subst; contradiction Hdiff_loc; eapply Hinj; eauto.
    - rewrite Map.F.F.remove_neq_o in *; clarify.
      exploit store_valid_access_3; eauto; intro valid.
      exploit valid_access_free_inv_1; eauto; intro valid'.
      generalize (valid_access_store _ _ _ _ (to_val v) valid'); intros [? store];
        rewrite store; clarify.
      generalize (free_range_perm _ _ _ _ _ H121); intro freeable.
      rewrite range_perm_store_iff in freeable; eauto.
      generalize (range_perm_free _ _ _ _ freeable); intros [? free];
        rewrite free; eauto.
    - destruct (alloc x2 0 4) eqn: alloc1; inversion H21; clarify.
      rewrite Map.F.F.remove_neq_o in *; clarify.
      destruct (alloc (m mr) 0 4) eqn: alloc2; clarify.
      rewrite Map.F.F.add_neq_o in *; clarify.
      generalize (free_range_perm _ _ _ _ _ H121); intro valid.
      generalize (range_perm_free m1 x1 0 4); intro X; use X.
      + destruct X; clarify; eauto.
      + repeat intro; eapply perm_alloc_1; eauto.
    - rewrite Map.F.F.remove_neq_o in *; clarify.
      generalize (free_range_perm _ _ _ _ _ H2121); 
        generalize (free_range_perm _ _ _ _ _ H121); intros freeable1 freeable2.
      rewrite <- range_perm_free_iff in freeable2; eauto.
      generalize (range_perm_free _ _ _ _ freeable2); 
        intros [? free1]; rewrite free1; clarify.
      rewrite Map.F.F.remove_neq_o; clarify.
      rewrite range_perm_free_iff in freeable1; eauto.
      generalize (range_perm_free _ _ _ _ freeable1); 
        intros [? free2]; rewrite free2; eauto.
      intro; subst; contradiction Hdiff_loc; eapply Hinj; eauto.
      intro; subst; contradiction Hdiff_loc; eapply Hinj; eauto.
    - rewrite Map.F.F.remove_neq_o in *; clarify; eauto.
    - destruct (alloc (m x) 0 4) eqn: alloc1; inversion H21; clarify.
      rewrite Map.F.F.add_neq_o; clarify; eauto.
    - rewrite Map.F.F.remove_neq_o in *; clarify; eauto.
  Qed.
      
  Lemma CC_loc_valid : forall op1 op2 mr mr1
    (Hdiff_loc : loc_of op1 <> loc_of op2)
    (Hvalid : forall x b, Map.find x (map mr) = Some b -> valid_block (m mr) b)
    (Hinj : forall x y b, Map.find x (map mr) = Some b -> 
                          Map.find y (map mr) = Some b -> x = y)
    (Hcan : CC_do_op mr op1 = Some mr1),
    CC_do_op mr1 op2 = None <-> CC_do_op mr op2 = None.
  Proof. 
    intros; destruct op1; clarify; try reflexivity.
    - destruct op2; clarify; destruct (Map.find k0 (map mr)) eqn: find; 
        try reflexivity.
      + erewrite load_store_other; eauto.
        destruct (load Mint32 (m mr) b 0); split; clarify.
        left; intro; subst; contradiction Hdiff_loc; eapply Hinj; eauto.
      + destruct (store Mint32 (m mr) b 0 (to_val v0)) eqn: store1; split; clarify.
        * generalize (store_valid_access_3 _ _ _ _ _ _ store1); intro valid1.
          exploit (store_valid_access_1 _ _ _ _ _ _ Hcan21); eauto; intro valid2.
          generalize (valid_access_store _ _ _ _ (to_val v0) valid2);
            intros [? ?]; clarsimp.
        * destruct (store Mint32 x0 b 0 (to_val v0)) eqn: store2; clarify.
          generalize (store_valid_access_3 _ _ _ _ _ _ store2); intro valid2.
          exploit (store_valid_access_2 _ _ _ _ _ _ Hcan21); eauto; intro valid1.
          generalize (valid_access_store _ _ _ _ (to_val v0) valid1); intros [? ?];
            clarify.
      + destruct (alloc x0 0 4); destruct (alloc (m mr) 0 4); split; clarify.
      + destruct (free (m mr) b 0 4) eqn: free1; split; clarify.
        * generalize (free_range_perm _ _ _ _ _ free1); intro freeable.
          rewrite range_perm_store_iff in freeable; eauto.
          generalize (range_perm_free _ _ _ _ freeable); intros [? ?]; clarsimp.
        * destruct (free x0 b 0 4) eqn: free2; clarify.
          generalize (free_range_perm _ _ _ _ _ free2); intro freeable.
          rewrite <- range_perm_store_iff in freeable; eauto.
          generalize (range_perm_free _ _ _ _ freeable); intros [? ?]; clarsimp.
      + split; clarify.
    - destruct (alloc (m mr) 0 4) eqn: alloc1; clarify.
      destruct op2; clarify; rewrite Map.F.F.add_neq_o in *; clarify; 
        destruct (Map.find k0 (map mr)) eqn: find; try reflexivity.
      + erewrite load_alloc_unchanged; eauto.
        destruct (load Mint32 (m mr) b0 0); clarify; split; clarify.
      + destruct (store Mint32 (m mr) b0 0 (to_val v)) eqn: store1; split; clarify.
        * exploit store_valid_access_3; eauto; intro valid1.
          exploit valid_access_alloc_other; eauto; intro valid2.
          generalize (valid_access_store _ _ _ _ (to_val v) valid2);
            intros [? ?]; clarsimp.
        * destruct (store Mint32 m0 b0 0 (to_val v)) eqn: store2; clarify.
          exploit store_valid_access_3; eauto; intro valid2.
          exploit valid_access_alloc_inv; eauto; intro valid1.
          destruct (eq_block b0 b); clarify.
          { exploit alloc_result; eauto; clarify.
            specialize (Hvalid _ _ find); unfold valid_block in Hvalid.
            generalize (Pos.lt_irrefl (nextblock (m mr))); clarify. }
          generalize (valid_access_store _ _ _ _ (to_val v) valid1);
            intros [? ?]; clarsimp.
      + destruct (alloc (m mr) 0 4); destruct (alloc m0 0 4); split; clarify.
      + destruct (free (m mr) b0 0 4) eqn: free1; split; clarify.
        * generalize (free_range_perm _ _ _ _ _ free1); intro valid1.
          generalize (range_perm_free m0 b0 0 4); intro X; use X.
          destruct X as [? ?]; clarsimp.
          repeat intro; eapply perm_alloc_1; eauto.
        * destruct (free m0 b0 0 4) eqn: free2; clarify.
          generalize (free_range_perm _ _ _ _ _ free2); intro valid2.
          generalize (range_perm_free (m mr) b0 0 4); intro X; use X.
          destruct X as [? ?]; clarsimp.
          repeat intro; eapply perm_alloc_4; eauto.
          intro; exploit alloc_result; eauto; clarify.
          specialize (Hvalid _ _ find); unfold valid_block in Hvalid; clarify.
          generalize (Pos.lt_irrefl _ Hvalid); auto.
      + split; clarify.
    - destruct op2; clarify; rewrite Map.F.F.remove_neq_o in *; clarify; 
        destruct (Map.find k0 (map mr)) eqn: find; try reflexivity.
      + erewrite load_free; eauto.
        destruct (load Mint32 (m mr) b 0); split; clarify.
        left; intro; subst; contradiction Hdiff_loc; eapply Hinj; eauto.
      + destruct (store Mint32 (m mr) b 0 (to_val v)) eqn: store1; split; clarify.
        * exploit store_valid_access_3; eauto; intro valid1.
          exploit valid_access_free_1; eauto.
          { left; intro; subst; contradiction Hdiff_loc; eapply Hinj; eauto. }
          intro valid2; generalize (valid_access_store _ _ _ _ (to_val v) 
            valid2); intros [? ?]; clarsimp.
        * destruct (store Mint32 x0 b 0 (to_val v)) eqn: store2; clarify.
          exploit store_valid_access_3; eauto; intro valid2.
          exploit valid_access_free_inv_1; eauto.
          intro valid1; generalize (valid_access_store _ _ _ _ (to_val v) 
            valid1); intros [? ?]; clarsimp.
      + destruct (alloc (m mr) 0 4); destruct (alloc x0 0 4); split; clarify.
      + destruct (free (m mr) b 0 4) eqn: free1; split; clarify.
        * generalize (free_range_perm _ _ _ _ _ free1); intro freeable.
          rewrite (range_perm_free_iff Hcan21) in freeable; eauto.
          generalize (range_perm_free _ _ _ _ freeable); intros [? ?]; clarsimp.
          { intro; subst; contradiction Hdiff_loc; eapply Hinj; eauto. }
        * destruct (free x0 b 0 4) eqn: free2; clarify.
          generalize (free_range_perm _ _ _ _ _ free2); intro freeable.
          rewrite <- range_perm_free_iff in freeable; eauto.
          generalize (range_perm_free _ _ _ _ freeable); intros [? ?]; clarsimp.
          { intro; subst; contradiction Hdiff_loc; eapply Hinj; eauto. }
      + split; clarify.
  Qed.    

  Lemma CC_loc_valid' : forall m op1 op2 (Hdiff_loc : loc_of op1 <> loc_of op2)
      (Hnot_cast : is_mcast op2 = false) (Hcan : CC_can_do m op1 = true),
      CC_can_do (op1 :: m) op2 = CC_can_do m op2.
  Proof.
    unfold CC_can_do; clarsimp; repeat rewrite CC_ops_app in *; clarify.
    generalize (can_do_valid _ cond1); intro valid.
    generalize (can_do_inj _ cond1); intro inj.
    destruct (CC_do_op m1 op2) eqn: Hop2; clarify.
    - exploit CC_loc_comm; eauto 1; clarify.
    - rewrite CC_loc_valid in Hop2; eauto 1; clarify.
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

  Instance CompCertMem : Memory_Layout block Loc.eq_dec val32_eq :=
    {| can_do_op := CC_can_do |}.
  Proof.
    - unfold CC_can_do; clarify; repeat rewrite CC_ops_app in *; clarify.
      destruct (CC_do_ops empty_rec (rev m0)) eqn: Hm'; clarsimp.
      destruct (CC_do_ops m1 [op1; op2]) eqn: Hops.
      + generalize (CC_loc_comm(mr' := m2) _ _ _ Hdiff_loc (can_do_valid _ Hm') 
          (can_do_inj _ Hm')); clarify.
      + destruct (CC_do_ops m1 [op2; op1]) eqn: Hops'; [|clarify].
        assert (loc_of op2 <> loc_of op1) as Hdiff_loc' by clarify.
        generalize (CC_loc_comm(mr' := m2) _ _ _ Hdiff_loc' (can_do_valid _ Hm')
          (can_do_inj _ Hm')); clarify.
    - apply CC_loc_valid'.
    - unfold CC_can_do; clarify; repeat rewrite CC_ops_app in *; clarify.
    - unfold CC_can_do; clarify; repeat rewrite CC_ops_app in *; clarify.
    - unfold CC_can_do; clarify; repeat rewrite CC_ops_app in *; clarsimp.
      exploit load_store_same; eauto 2; intro Hload; rewrite Hload.
      destruct v; match goal with |-context[eq_dec v' ?v] => 
        destruct (eq_dec v' v) end; clarify.
    - intros; destruct (eq_dec l (loc_of op)).
      unfold CC_can_do in *; clarify; repeat rewrite CC_ops_app in *; clarify.
      + destruct op; clarsimp.
        * specialize (Hnot_read v0); clarify.
        * generalize (store_valid_access_3 _ _ _ _ _ _ cond2121); intro valid.
          exploit store_valid_access_1; eauto 2; intro valid2.
          generalize (valid_access_store _ _ _ _ (to_val v0) valid);
          generalize (valid_access_store _ _ _ _ (to_val v0) valid2);
            intros [? ?] [? ?]; clarsimp.
        * destruct (free x2 x1 0 4) eqn: Hfree; clarsimp.
          generalize (free_range_perm _ _ _ _ _ Hfree); intro valid.
          rewrite <- range_perm_store_iff in valid; eauto.
          generalize (range_perm_free _ _ _ _ valid); intros [? ?]; clarify.
          generalize (free_range_perm _ _ _ _ _ cond0); intro valid.
          rewrite range_perm_store_iff in valid; eauto.
          generalize (range_perm_free _ _ _ _ valid); intros [? ?]; clarify.
      + unfold CC_can_do in *; clarify; repeat rewrite CC_ops_app in *; 
          clarsimp.
        generalize (can_do_valid _ cond1); intro valid.
        generalize (can_do_inj _ cond1); intro inj.
        destruct (CC_do_op x op) eqn: Hop; clarify.
        * rewrite (CC_loc_valid (MWrite l v) _ x) in cond; clarify; eauto.
        * rewrite <- (CC_loc_valid (MWrite l v) _ x) in Hop; clarify; eauto.
          rewrite Hop in cond; clarify.
    - intros; destruct (eq_dec l (loc_of op)).
      unfold CC_can_do in *; clarify; repeat rewrite CC_ops_app in *; clarsimp.
      + destruct op; clarify.
      + apply CC_loc_valid'; clarify.
    - unfold CC_can_do; clarify; repeat rewrite CC_ops_app in *; clarify.
      destruct (alloc (m x) 0 4) eqn: alloc1; clarify.
      rewrite Map.F.F.add_eq_o; auto.
      split; intros; clarsimp.
      + repeat rewrite CC_ops_app in *; clarsimp.
        rewrite Map.F.F.add_eq_o in *; clarify.
        generalize (valid_access_store m2 Mint32 b 0 (to_val v)); intro X;
          use X.
        * destruct X; clarsimp.
        * unfold valid_access; clarify.
          split; [repeat intro | apply Z.divide_0_r].
          eapply perm_implies; [eapply perm_alloc_2 | apply perm_F_any]; eauto.
      + generalize (range_perm_free m2 b 0 4); intro X; use X.
        * destruct X; clarify.
        * repeat intro; exploit perm_alloc_2; eauto.
    - unfold CC_can_do; clarify; repeat rewrite CC_ops_app in *; clarify.
      rewrite Map.F.F.remove_eq_o; auto.
      destruct (alloc x2 0 4) eqn: alloc1; clarify.
      repeat rewrite CC_ops_app in *; clarsimp.
      rewrite Map.F.F.remove_eq_o in *; clarify.
    - unfold CC_can_do; clarify; repeat split.
      destruct (alloc empty 0 4); clarify.
    - unfold CC_can_do; clarify; repeat rewrite CC_ops_app in *; clarsimp.
      destruct (CC_do_ops empty_rec (rev m0)) eqn: Hm'; clarsimp.
      destruct (Map.find l (map m1)) eqn: Hfind; clarify.
      destruct (store Mint32 (m m1) b 0 (to_val v)) eqn: store1; clarsimp.
      + exploit store_valid_access_3; eauto; intro valid.
        generalize (valid_access_store _ _ _ _ (to_val v') valid); intros [? ?];
          clarify.
      + exploit store_valid_access_3; eauto; intro valid.
        generalize (valid_access_store _ _ _ _ (to_val v) valid); intros [? ?];
          clarify.
  Defined.
      
End CC_MemInstance.