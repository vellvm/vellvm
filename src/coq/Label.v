From ITree Require Import
     Basics.Basics
     Basics.Function
     ITree
     Basics.Category
     KTree
     KTreeFacts.

From Coq Require Import
     Psatz
     List.

From Vellvm Require Import 
     LLVMAst.

Require Import Program.Equality.

Section FinSets.

  Definition FinSet (l: list block_id): Type := {bid: block_id | In bid l}.

  Definition FinC (l l': list block_id) := FinSet l -> FinSet l'.

  Global Instance Eq_FinC : Eq2 FinC :=
    fun n m f g => forall (k: FinSet n), proj1_sig (f k) = proj1_sig (g k).

  Global Instance Id_FinC : Id_ FinC :=
    fun n k => k.

  Definition hom a b := (FinSet a -> FinSet b).

  Global Instance Cat_FinC : Cat FinC :=
    fun n m p (f: FinSet n -> FinSet m) (g: FinSet m -> FinSet p) => cat f g: FinSet n -> FinSet p.

  (** ** The [sum] coproduct. *)

  (** Coproduct elimination *)

  Global Instance Case_FinC : CoprodCase FinC app :=
    fun {n m p} (k : FinC n p) (k' : FinC m p) (x : FinSet (n ++ m)) =>
      match n with
      | [] => 
      match split_fin_sum x with
      | inl x => k x
      | inr x => k' x
      end.

  (** Injections *)
  Global Instance Inl_FinC : CoprodInl FinC plus :=
    fun n m x => L _ x.
  Global Instance Inr_FinC : CoprodInr FinC plus :=
    fun n m x => R _ x.

  Definition lift_eq {A B: nat} (f: A = B): Fin A -> Fin B :=
    fun a => eq_rect A Fin a B f.

  Global Instance Initial_FinC : Initial FinC 0 :=
    fun _ v => match v with end.


  Lemma to_nat'_FS {n} (k: Fin n):
    to_nat' (FS k) = S (to_nat' k).
  Proof.
    unfold to_nat'; simpl; destruct (to_nat k); reflexivity. 
  Qed.

  Definition split_fin_S (n: nat) (k: Fin (S n)) : (Fin 1) + (Fin n) :=
    match k with
    | F1 => inl F1
    | FS k => inr k
    end.

  Definition split_fin_sum (m: nat) :=
    nat_rec (fun n => Fin (n + m) -> Fin n + Fin m)
            (fun k => inr k)
            (fun n IH (k: Fin (S n + m)) =>
               match split_fin_S (n + m) k with
               | inl _ => inl F1
               | inr k => match IH k with
                         | inl k => inl (FS k)
                         | inr k => inr k
                         end
               end
            ).

  Arguments split_fin_sum {m n}.

  Lemma split_fin_S_left:
    forall (n: nat) (k : Fin (S n)) t,
      split_fin_S n k = inl t -> k = F1. 
  Proof.
    unfold split_fin_S.
    intros; dependent destruction k; [reflexivity | inversion H].
  Qed.

  Lemma split_fin_S_right:
    forall (n: nat) (k : Fin (S n)) t,
      split_fin_S n k = inr t -> to_nat' k = S (to_nat' t). 
  Proof.
    unfold split_fin_S.
    intros; dependent destruction k.
    - inv H.
    - inv H; apply to_nat'_FS. 
  Qed.

  Lemma split_fin_sum_left:
    forall {n m} (k: Fin (n + m)) k',
      split_fin_sum k = inl k' ->
      to_nat' k = to_nat' k'.
  Proof.
    induction n as [| n IH]; simpl; intros.
    - inv H.
    - destruct (split_fin_S (n + m) k) eqn:EQ.
      + apply split_fin_S_left in EQ; subst.
        inv H; reflexivity.
      + destruct (split_fin_sum t) eqn: EQ'.
        * inv H.
          apply IH in EQ'.
          rewrite to_nat'_FS.
          apply split_fin_S_right in EQ.
          rewrite EQ, <- EQ'; reflexivity.
        * inv H.
  Qed.


  (* Fact __arith_fact: *)
  (*   forall p n m,  *)
  (*     p < n + m -> *)
  (*     n <= p -> *)
  (*     p - n < m. *)
  (* Proof. *)
  (*   intros; lia. *)
  (* Qed. *)
 
  (* Fixpoint foo (n m: nat) (k: Fin (n + m)) : (Fin n) + (Fin m) := *)
  (*   match n with *)
  (*   | O => inr k *)
  (*   | S n => match k with *)
  (*           | F1 => inl F1 *)
  (*           | FS k => foo n m k *)
  (*           end *)
  (*   end. *)
  (*   refine (let (p, LT) := to_nat k in _). *)
  (*   destruct (Nat.ltb p n) eqn:H. *)
  (*   - refine (inl (of_nat_lt (proj1 (PeanoNat.Nat.ltb_lt _ _) H))). *)
  (*   - refine (inr (of_nat_lt (p := p - n) _)). *)
  (*     refine (__arith_fact _ _ _ LT (proj1 (PeanoNat.Nat.ltb_ge _ _) H)). *)
  (* Defined. *)


  (* Definition split_fin_sum {n m: nat} (k: Fin (n + m)): (Fin n) + (Fin m). *)
  (*   refine (let (p, LT) := to_nat k in _). *)
  (*   destruct (Nat.ltb p n) eqn:H. *)
  (*   - refine (inl (of_nat_lt (proj1 (PeanoNat.Nat.ltb_lt _ _) H))). *)
  (*   - refine (inr (of_nat_lt (p := p - n) _)). *)
  (*     refine (__arith_fact _ _ _ LT (proj1 (PeanoNat.Nat.ltb_ge _ _) H)). *)
  (* Defined. *)

  (* Lemma split_fin_sum_left: *)
  (*   forall {n m} (k: Fin (n + m)) k', *)
  (*     split_fin_sum k = inl k' -> *)
  (*     proj1_sig (to_nat k) = proj1_sig (to_nat k'). *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold split_fin_sum in H. *)
  (*   destruct (to_nat k) as [p LT]; simpl. *)
  (*   dep_destruct (Nat.ltb p n). *)

  (*   destruct (Nat.ltb p n) eqn:EQb. *)
  (*   -  *)
  (*     rewrite EQ in H. *)
  (*     rewrite EQb in H. *)
  (*     dependent destruction b. *)
  (*   revert H. *)
    
    

  (* Lemma foo: *)
  (*   forall {m n: nat} (k: Fin.t (m + n)) k', *)
  (*     split_fin_sum k = inr k' -> k = R _ k'. *)
  (* Proof. *)
  (*   intros. *)


End Fin.

Arguments split_fin_sum {m n}.

Section Label.

  Context {E: Type -> Type}.
  Notation Fin := Fin.t.

  Definition Label (n: nat) (m: nat) := ktree E (Fin n) (Fin m).

  (* Actually probably need eutt (fun k k' => to_nat' k = to_nat' k') rather than eutt eq *)
  Global Instance Eq_Label : Eq2 Label :=
    fun n m k k' => forall l, k l ≈ k' l.

  Global Instance Id_Label : Id_ Label :=
    fun n k => Ret k.

  Global Instance Cat_Label : Cat Label :=
    fun n m p (k: ktree E (Fin n) (Fin m)) (k': ktree E (Fin m) (Fin p)) => cat k k': ktree E _ _.

  Global Instance Initial_Label : Initial Label 0 :=
    fun _ v => match v with end.

  (** ** The [sum] coproduct. *)

  (** Coproduct elimination *)

  Global Instance Case_Label : CoprodCase Label plus :=
    fun {n m p} (k : Label n p) (k' : Label m p) (x : Fin (n + m)) =>
      match split_fin_sum x with
      | inl x => k x
      | inr x => k' x
      end.

  (** Injections *)
  Global Instance Inl_Label : CoprodInl Label plus :=
    fun n m x => Ret (L _ x).
  Global Instance Inr_Label : CoprodInr Label plus :=
    fun n m x => Ret (R _ x).

  Definition loop_Label {A B C : nat}: Label (C + A) (C + B) -> Label A B :=
    fun body =>
      loop 
        (fun l => match l with
               | inl l => ITree.map split_fin_sum (body (L _ l))
               | inr l => ITree.map split_fin_sum (body (R _ l))
               end).

  Definition lift_Label {A B} (f : FinC A B) : Label A B := fun a => Ret (f a).

End Label.

