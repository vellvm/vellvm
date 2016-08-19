Require Import MSets.
Require Import OrdersEx.
Require Import FMaps.
Require Import Util.

(* The grand unified theory of MSets and FMaps. *)
Module MSet' (T : Equalities.DecidableType).
  
  Module MSet := MSetWeakList.Make T.
  Include MSet.
  Include WPropertiesOn T MSet.
  Include Decide MSet.

End MSet'.

Module FMap' (T : Equalities.DecidableType).

  Module Old_T := Backport_DT T.
  Module Map := FMapWeakList.Make Old_T.
  Include Map.
  Module Import F := FMapFacts.Properties Map.
  Module MSet := MSet' T.

  (* Decidable equality for maps *)
  Lemma map_not_in_empty: forall (A: Set) (m : t A), Empty m -> forall x, ~In x m.
  Proof.
    intros ? ? Hempty x Hin.
    rewrite F.elements_in_iff in *; rewrite elements_Empty in *; clarify.
    rewrite Hempty in Hin; rewrite InA_nil in *; contradiction.
  Qed.
  Hint Resolve map_not_in_empty.

  Definition keys {A : Set} (m : t A) := fold (fun k _ s => MSet.add k s) m MSet.empty.
  Lemma keys_spec: forall (A : Set) (m : t A) x, In x m <-> MSet.In x (keys m).
  Proof.
    intros A m x; unfold keys; apply fold_rec; clarify.
    - specialize (map_not_in_empty _ _ H); intro not; split; intro H1.
      + specialize (not _ H1); contradiction.
      + rewrite MSet.F.empty_iff in *; contradiction.
    - destruct (T.eq_dec x k); subst; unfold Add in *; rewrite MSet.add_spec.
      + split; clarify.
        rewrite F.in_find_iff; rewrite H1; rewrite F.add_eq_o; clarify.
      + rewrite F.in_find_iff in *; rewrite H1; rewrite F.add_neq_o; auto.
        rewrite H2; split; clarify.
  Qed.    
  
  Instance proper_check_eq: forall A m' (eq_dec : forall (a b : A), ({a = b} + {a <> b})), Proper (T.eq ==> eq ==> eq)
  (fun (k : key) (v : A) =>
   match find (elt:=A) k m' with
   | Some v' => if eq_dec v v' then true else false
   | None => false
   end).
  Proof.
    unfold Proper; unfold respectful; intros.
    rewrite H; subst; auto.
  Qed.
  Local Hint Immediate proper_check_eq.

  Lemma map_keys_equiv: forall (A : Set) (eq_dec : forall (a b : A), ({a = b} + {a <> b})) (m m' : t A), Equal m m' <->
    MSet.Equal (keys m) (keys m') /\ for_all (fun k v => match find k m' with Some v' => if eq_dec v v' then true else false | _ => false end) m = true.
  Proof.
    intros A eq_dec; apply (map_induction(P := fun m => forall (m' : t A), Equal m m' <->
      MSet.Equal (keys m) (keys m') /\ for_all (fun (k : key) (v : A) => match find k m' with Some v' => if eq_dec v v' then true else false
      | None => false end) m = true)); intros; rewrite for_all_iff in *; clarify.
    - split; unfold Equal, MSet.Equal; clarify.
      + split; clarify.
        * repeat rewrite <- keys_spec; repeat rewrite F.in_find_iff; rewrite H0;
            reflexivity.
        * rewrite F.elements_mapsto_iff in *; specialize (H _ _ H1);
            contradiction.
      + setoid_rewrite <- keys_spec in H01.
        generalize (F.in_find_iff m y); intro Hin.
        destruct (find y m) eqn: Hfind; clarify.
        * destruct Hin as [_ Hin]; use Hin.
          generalize (map_not_in_empty _ _ H _ Hin); contradiction.
        * rewrite H01 in Hin; rewrite F.in_find_iff in *; 
            destruct Hin as [Hin _].
          destruct (find y m'); clarify; use Hin; clarify.
    - unfold Add in *; specialize (H (remove x m'0)); split; 
        intro Heq.
      + assert (Equal m (remove (elt:=A) x m'0)) as eql; [|rewrite H in eql].
        { unfold Equal in *; intro.
          destruct (E.eq_dec x y); clarify.
          * rewrite e0 in *; rewrite F.remove_eq_o; auto.
            rewrite F.in_find_iff in *; destruct (find y m); clarify.
            contradiction H0; clarify.
          * rewrite F.remove_neq_o; auto.
            rewrite <- Heq; rewrite H1; rewrite F.add_neq_o; auto. }
        split.
        * unfold MSet.Equal; intro.
          repeat (rewrite <- keys_spec in *; rewrite F.in_find_iff in *).
          rewrite Heq; reflexivity.
        * destruct eql as [_ eql]; rewrite for_all_iff in eql; 
            intros k el Hmaps.
          rewrite <- Heq.
          rewrite F.find_mapsto_iff in *; clarsimp.
          { repeat intro; clarify.
            rewrite Hmaps; reflexivity. }
      + assert (Equal m (remove x m'0)); [rewrite H | unfold Equal in *].
        { split.
          * unfold MSet.Equal in *; intro.
            destruct Heq as [Heq _].
            specialize (Heq a); specialize (H1 a); 
              repeat rewrite <- keys_spec in *.
            repeat rewrite F.in_find_iff in *; destruct (T.eq_dec x a).
            rewrite e0 in *; split; clarify.
            rewrite F.remove_eq_o in *; clarify.
            rewrite F.remove_neq_o; auto.
            rewrite <- Heq; rewrite H1; rewrite F.add_neq_o; auto; reflexivity.
          * rewrite for_all_iff; intros.
            rewrite F.not_find_in_iff in *; rewrite F.find_mapsto_iff in *.
            specialize (H1 k); destruct (T.eq_dec x k); clarify.
            { rewrite e1 in H0; clarsimp. }
            rewrite F.remove_neq_o; rewrite F.add_neq_o in *; auto.
            rewrite Heq2; auto.
            rewrite F.find_mapsto_iff; rewrite H1; auto.
            { repeat intro; clarify.
              rewrite H2; auto. } }
        destruct Heq as [_ Heq].
        intro; specialize (H1 y); specialize (Heq y); destruct (T.eq_dec x y).
        * setoid_rewrite F.find_mapsto_iff in Heq.
          rewrite e0 in *; rewrite H1; rewrite F.add_eq_o in *; auto.
          specialize (Heq _ H1).
          destruct (find y m'0); clarify.
        * specialize (H2 y); rewrite F.remove_neq_o in H2; auto.
          rewrite <- H2; rewrite H1; rewrite F.add_neq_o; auto.
  Qed.

  Lemma map_eq_dec: forall (A : Set) (eq_dec : forall (a b : A), ({a = b} + {a <> b})) (m m' : t A), 
    {Equal m m'} + {~Equal m m'}.
  Proof.
    intros; generalize (map_keys_equiv _ eq_dec m m'); intro.
    destruct (MSet.eq_dec (keys m) (keys m')).
    - destruct (for_all (fun k v => match find k m' with Some v' => 
        if eq_dec v v' then true else false | _ => false end) m) eqn: all_same; 
        [left; rewrite H | right]; clarify.
      rewrite H; intro; clarify.
    - right; rewrite H; intro; clarify.
  Qed.

End FMap'.

Module NatSet := MSet' OrdersEx.Nat_as_OT.
Definition nat_set := NatSet.t.

Module NatMap := FMap' OrdersEx.Nat_as_OT.
Definition nat_map := NatMap.t.